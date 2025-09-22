/*
 * Copyright 2023 The OpenSSL Project Authors. All Rights Reserved.
 *
 * Licensed under the Apache License 2.0 (the "License").  You may not use
 * this file except in compliance with the License.  You can obtain a copy
 * in the file LICENSE in the source distribution or at
 * https://www.openssl.org/source/license.html
 */

#include <dirent.h>
#include <errno.h>
#include <math.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#ifndef _WIN32
# include <libgen.h>
# include <unistd.h>
#else
# include <windows.h>
# include "perflib/getopt.h"
# include "perflib/basename.h"
#endif    /* _WIN32 */
#include <openssl/bio.h>
#include <openssl/core_names.h>
#include <openssl/evp.h>
#include <openssl/x509.h>
#include "perflib/err.h"
#include "perflib/perflib.h"

#define NUM_CERTS 1024
#define NUM_LOAD_CERTS 128
#define NUM_KEYS 16
#define KEY_ALGO "rsa:2048"
#define W_PROBABILITY 50
#define MAX_WRITERS 0
#define RUN_TIME 5
#define QUANTILES 5
#define NONCE_CFG "file:servercert.pem"
#define CTX_SHARE_THREADS 1

#define RAND_CYCLE 65536

static size_t num_gen_certs = NUM_CERTS;
static size_t num_gen_load_certs = NUM_LOAD_CERTS;
static size_t num_gen_keys = NUM_KEYS;
static const char *gen_key_algo = KEY_ALGO;
static size_t timeout_us = RUN_TIME * 1000000;
static size_t quantiles = QUANTILES;
static size_t max_writers = MAX_WRITERS;
static size_t w_probability = W_PROBABILITY * 65536 / 100;

enum verbosity {
    VERBOSITY_TERSE,
    VERBOSITY_DEFAULT,
    VERBOSITY_VERBOSE,
    VERBOSITY_DEBUG_STATS,
    VERBOSITY_DEBUG,

    VERBOSITY_MAX__
};

static enum mode {
    MODE_R,
    MODE_RW, /* "MODE_W" is just MODE_RW with 100% write probability */
} mode = MODE_R;

enum nonce_type {
    NONCE_GENERATED,
    NONCE_PATH,
};

struct call_times {
    uint64_t duration;
    uint64_t total_count;
    uint64_t total_found;
    uint64_t total_added;
    uint64_t min_count;
    uint64_t max_count;
    double avg;
    double min;
    double max;
    double stddev;
    double median;
    size_t min_idx;
    size_t max_idx;
};

struct nonce_cfg {
    enum nonce_type type;
    const char *path;
    char **dirs;
    size_t num_dirs;
};

struct affinity_cfg {
    uint32_t stride;
    uint32_t stripe_step;
    uint32_t stripe_size;
};

struct thread_data {
    //unsigned long rw_cycle[RAND_CYCLE / CHAR_BIT / sizeof(unsigned long)];
    OSSL_TIME start_time;
    struct {
        uint64_t count;
        uint64_t found;
        uint64_t added_certs;
        OSSL_TIME end_time;
    } *q_data;
    X509_STORE_CTX *ctx;
} *thread_data;

static int error = 0;
static int verbosity = VERBOSITY_DEFAULT;
static X509_STORE *store = NULL;
static X509 *x509_nonce = NULL;
static X509_NAME *x509_name_nonce = NULL;
static EVP_PKEY **gen_keys = NULL;
static EVP_PKEY **gen_pubkeys = NULL;
static X509 **gen_certs = NULL;

static size_t threadcount;

OSSL_TIME max_time;

#define OSSL_MIN(p, q) ((p) < (q) ? (p) : (q))
#define OSSL_MAX(p, q) ((p) > (q) ? (p) : (q))

static int stride_stripe_affinity(affinity_t *cpu_set_bits, size_t cpu_set_size,
                                  size_t num, size_t cnt, void *arg)
{
    enum { BITS_PER_ELEM = sizeof(cpu_set_bits[0]) * CHAR_BIT };
    struct affinity_cfg *cfg = (struct affinity_cfg *)arg;
    size_t set_cnt = 0;
    uint32_t num_bit;
    size_t i;

    /* We run everything through "% cnt" to avoid integer overflow */
    num_bit = (((num % cfg->stripe_size) % cnt) * (cfg->stride % cnt) +
               ((num / cfg->stripe_size) % cnt) * (cfg->stripe_step % cnt))
              % cnt;

    /* Finding (num % cnt)th set bit in the provided mask */
    for (i = 0; i < cpu_set_size; i++) {
        if (cpu_set_bits[i / BITS_PER_ELEM] & (1UL << (i % BITS_PER_ELEM)))
            set_cnt++;

        if (set_cnt == (num_bit + 1))
            break;
    }

    if (set_cnt != (num_bit + 1)) {
        WARNX("Only %zu bits are set in the affinity mask, %zu expected",
              set_cnt, num % cnt + 1);

        return 0;
    }

    if (verbosity >= VERBOSITY_DEBUG)
        fprintf(stderr, "Mapping thread %3" PRIu32 " to CPU %zu\n", num, i);

    memset(cpu_set_bits, 0, cpu_set_size / CHAR_BIT);

    cpu_set_bits[i / BITS_PER_ELEM] = 1 << (i % BITS_PER_ELEM);

    return 1;
}

static EVP_PKEY_CTX *
make_pkey_ctx(const char *algstr, char **alg_storage)
{
    EVP_PKEY_CTX *ctx = NULL;
    const char *alg;
    const char *p = strchr(algstr, ':');

    alg = p ? *alg_storage = OPENSSL_strndup(algstr, p - algstr) : algstr;
    if (alg == NULL) {
        warnx("Error getting algorithm name from \"%s\"", algstr);
        goto err;
    }

    ctx = EVP_PKEY_CTX_new_from_name(NULL, alg, NULL);
    if (ctx == NULL) {
        warnx("Error allocating keygen context");
        goto err;
    }

    if (EVP_PKEY_keygen_init(ctx) <= 0) {
        warnx("Error initialising keygen contextx");
        goto err;
    }

    /* The bits part */
    if (p && p[1] >= '0' && p[1] <= '9') {
        char *endptr = NULL;
        long bits = strtol(p + 1, &endptr, 0);
        if (!endptr || (*endptr != '\0' && *endptr != ':')) {
            warnx("Error while parsing bits from \"%s\"", p + 1);
            goto err;
        }
        p = endptr;

        if (bits > 0) {
            OSSL_PARAM params[] = { OSSL_PARAM_END, OSSL_PARAM_END };
            size_t val = bits;

            params[0] = OSSL_PARAM_construct_size_t(OSSL_PKEY_PARAM_BITS, &val);

            if (EVP_PKEY_CTX_set_params(ctx, params) <= 0) {
                warnx("Error setting bits value of %zu to algorithm \"%s\"",
                      val, alg);
                goto err;
            }
        }
    }

    /* param=value pairs */
    while (p && p[0] == ':' && p[1] != '\0') {
        const char *param_str = p + 1;
        char *param;
        char *val;
        const char *eq;
        int ret;

        eq = strchr(param_str, '=');
        p = strchr(param_str, ':');

        if (eq == NULL || (p != NULL && eq > p)) {
            warnx("Error while parsing a param=value pair from \"%s\"", param_str);
            goto err;
        }

        param = OPENSSL_strndup(param_str, eq - param_str);
        if (param == NULL) {
            warnx("Error allocating param name string\n");
            goto err;
        }

        if (p)
            val = OPENSSL_strndup(eq + 1, p - eq - 1);
        else
            val = OPENSSL_strdup(eq + 1);
        if (val == NULL) {
            warnx("Error allocating param value string");
            OPENSSL_free(param);
            goto err;
        }

        if ((ret = EVP_PKEY_CTX_ctrl_str(ctx, param, val)) <= 0) {
            warnx("Error setting parameter \"%s\" to value \"%s\" for algorithm"
                  " \"%s\", got %d\n", param, val, alg, ret);
            OPENSSL_free(val);
            OPENSSL_free(param);
            goto err;
        }

        OPENSSL_free(val);
        OPENSSL_free(param);
    }

    return ctx;

err:
    EVP_PKEY_CTX_free(ctx);

    return NULL;
}

static EVP_PKEY *
gen_key(EVP_PKEY_CTX *ctx)
{
    EVP_PKEY *res = NULL;

    if (EVP_PKEY_keygen(ctx, &res) <= 0) {
        warnx("Error generating key");

        return NULL;
    }

    return res;
}

static EVP_PKEY *
get_pubkey(EVP_PKEY *pkey)
{
    BIO *bio = NULL;
    EVP_PKEY *pubkey = NULL;

    bio = BIO_new(BIO_s_mem());
    if (!bio) {
        warnx("Error creating memory BIO");
        goto err;
    }

    if (!PEM_write_bio_PUBKEY(bio, pkey)) {
        warnx("Error writing public key to BIO");
        goto err;
    }

    if (BIO_seek(bio, 0) < 0) {
        warnx("Error resetting BIO cursor");
        goto err;
    }

    pubkey = PEM_read_bio_PUBKEY(bio, NULL, NULL, NULL);
    if (pubkey == NULL) {
        warnx("Error reading pubkey from BIO");
        goto err;
    }

    BIO_free(bio);

    return pubkey;

err:
    EVP_PKEY_free(pubkey);
    BIO_free(bio);

    return NULL;
}

static const unsigned char *
gen_name(void)
{
    static const char chars[] = "0123456789ABCDEFGHIJKLMNOPQRSTUV"
                                "WXYZabcdefghijklmnopqrstuvwxyz  ";
    static unsigned char out[64];
    size_t len;

    len = rand() % (sizeof(out) - 2) + 1;

    for (size_t i = 0; i < len; i++)
        out[i] = chars[rand() % (sizeof(chars) - 1)];

    out[len] = '\0';

    return out;
}

static X509 *
gen_cert(size_t key_id, const unsigned char *sn, const unsigned char *in)
{
    EVP_PKEY *pubkey = gen_pubkeys[key_id];
    EVP_PKEY *pkey = gen_keys[key_id];
    X509 *cert = NULL;
    X509_NAME *issuer = NULL;
    X509_NAME *subject = NULL;
    EVP_MD_CTX *mctx = NULL;
    const unsigned char *in_str;
    const unsigned char *sn_str;
    int error = 1;

    cert = X509_new();
    if (!cert) {
        warnx("Error creating X509 certificate object");
        goto out;
    }

    issuer = X509_NAME_new();
    if (!issuer) {
        warnx("Error creating X509 issuer name object");
        goto out;
    }

    in_str = in ? in : gen_name();
    if (!X509_NAME_add_entry_by_txt(issuer, "CN", MBSTRING_ASC,
                                    in_str, -1, -1, 0)) {
        warnx("Error setting X509 issuer name \"%s\"", (const char *)in_str);
        goto out;
    }

    if (!X509_set_issuer_name(cert, issuer)) {
        warnx("Error setting X509 certificate issuer name:");
        X509_NAME_print_ex_fp(stderr, issuer, 2, 0);
        goto out;
    }

    subject = X509_NAME_new();
    if (!subject) {
        warnx("Error creating X509 subject name object");
        goto out;
    }

    sn_str = sn ? sn : gen_name();
    if (!X509_NAME_add_entry_by_txt(subject, "CN", MBSTRING_ASC,
                                    sn_str, -1, -1, 0)) {
        warnx("Error setting X509 subject name \"%s\"", (const char *)sn_str);
        goto out;
    }

    if (!X509_set_subject_name(cert, subject)) {
        warnx("Error setting X509 certificate subject name");
        goto out;
    }

    if (!X509_set_pubkey(cert, pubkey)) {
        warnx("Error setting public key for X509 certificate");
        goto out;
    }

    mctx = EVP_MD_CTX_new();
    if (!mctx) {
        warnx("Error allocating digest context");
        goto out;
    }

    if (!EVP_DigestSignInit_ex(mctx, NULL, NULL, NULL, NULL, pkey, NULL)) {
        warnx("Error initialising digest context");
        goto out;
    }

    if (!X509_sign_ctx(cert, mctx)) {
        warnx("Error signing certificate");
        goto out;
    }

    error = 0;

out:
    EVP_MD_CTX_free(mctx);
    X509_NAME_free(subject);
    X509_NAME_free(issuer);

    if (error) {
        X509_free(cert);
        cert = NULL;
    }

    return cert;
}

static X509 *
gen_nonce(struct nonce_cfg *cfg)
{
    X509 *x509_nonce = X509_new();

    if (!x509_nonce)
        errx(EXIT_FAILURE, "Error creating X509 nonce object");

    x509_name_nonce = X509_NAME_new();
    if (!x509_name_nonce)
        errx(EXIT_FAILURE, "Error creating X509 name nonce object");

    if (!X509_NAME_add_entry_by_txt(x509_name_nonce, "CN", MBSTRING_ASC,
                                    (unsigned char *) "Test NC CA", -1, -1, 0))
        errx(EXIT_FAILURE, "Error setting X509 name nonce");

    if (!X509_set_issuer_name(x509_nonce, x509_name_nonce))
        errx(EXIT_FAILURE, "Error setting X509 nonce name");

    return x509_nonce;
}

static X509 *
load_nonce_from_file(const char *path)
{
    BIO *bio = BIO_new_file(path, "rb");
    X509 *x509_nonce = NULL;

    if (bio == NULL) {
        warnx("Unable to create BIO for reading \"%s\"", path);
        return NULL;
    }

    x509_nonce = PEM_read_bio_X509(bio, NULL, NULL, NULL);
    if (x509_nonce == NULL)
        warnx("Failed to read certificate \"%s\"", path);

    BIO_free(bio);

    return x509_nonce;
}

static bool
is_abs_path(const char *path)
{
    if (path == NULL)
        return false;

#if defined(_WIN32)
    /*
     * So, we don't try to concatenate the provided path with the directory
     * paths if the path start with the following:
     *  - volume character and a colon ("C:"):  it is either absolute path
     *    (if followed by a backslash), or a relative path to a current
     *    directory of that volume (and we don't want to implement any logic
     *    that handles that);
     *  - backslash ("\"):  it is an "absolute path" on the "current" drive,
     *    or (if there are two backslashes in the beginning) an UNC path.
     */
    return (isalpha(path[0]) && path[1] == ':') || path[0] == '\\';
#else /* !_WIN32 */
    return path[0] == '/';
#endif
}

static X509 *
load_nonce_from_path(struct nonce_cfg *cfg)
{
    if (is_abs_path(cfg->path))
        return load_nonce_from_file(cfg->path);

    for (size_t i = 0; i < cfg->num_dirs; i++) {
        char *cert;
        X509 *ret;

        cert = perflib_mk_file_path(cfg->dirs[i], cfg->path);
        if (cert == NULL) {
            warnx("Failed to allocate file path for directory \"%s\""
                  " and path \"%s\"", cfg->dirs[i], cfg->path);
            continue;
        }

        ret = load_nonce_from_file(cert);
        OPENSSL_free(cert);

        if (ret != NULL)
            return ret;
    }

    return NULL;
}

static X509 *
make_nonce(struct nonce_cfg *cfg)
{
    switch (cfg->type) {
    case NONCE_GENERATED:
        return gen_nonce(cfg);
    case NONCE_PATH:
        return load_nonce_from_path(cfg);
    default:
        errx(EXIT_FAILURE, "Unknown nonce type: %lld", (long long ) cfg->type);
    }
}

static void
do_x509storeissuer(size_t num)
{
    struct thread_data *td = thread_data + num;
    X509 *issuer = NULL;
    OSSL_TIME time;
    OSSL_TIME duration;
    OSSL_TIME q_end;
    size_t q = 0;
    size_t count = 0;
    size_t add = 0;
    size_t found = 0;

    td->start_time = ossl_time_now();
    duration.t = max_time.t - td->start_time.t;
    q_end.t = duration.t / quantiles + td->start_time.t;

    do {
        if (mode == MODE_RW
            && (!max_writers || (num < max_writers))
            && (rand() % 65536 < w_probability)) {
            size_t cert_id = num_gen_load_certs
                             + ((num_gen_certs - num_gen_load_certs)
                                * num / threadcount)
                             + rand() % OSSL_MAX((num_gen_certs
                                                  - num_gen_load_certs)
                                                 / threadcount, 1);

            if (!X509_STORE_add_cert(store, gen_certs[cert_id])) {
                warnx("Failed to add generated certificate %zu to the store",
                      cert_id);
            } else {
                add++;
            }
        } else {
            if (X509_STORE_CTX_get1_issuer(&issuer, td->ctx, x509_nonce) != 0) {
                found++;
                X509_free(issuer);
            }
            issuer = NULL;
        }

        count++;
        if (count % 100 == 0) {
            time = ossl_time_now();
            if (time.t >= q_end.t) {
                td->q_data[q].count = count;
                td->q_data[q].found = found;
                td->q_data[q].added_certs = add;
                td->q_data[q].end_time = time;
                q_end.t = (duration.t * (++q + 1)) / quantiles + td->start_time.t;
            }
        }
    } while (time.t < max_time.t);

    td->q_data[quantiles - 1].count = count;
    td->q_data[quantiles - 1].end_time = time;
}

static void
report_store_size(X509_STORE * const store, const char * const suffix,
                  int verbosity)
{
    if (verbosity >= VERBOSITY_DEBUG_STATS) {
        STACK_OF(X509_OBJECT) *sk = X509_STORE_get1_objects(store);
        fprintf(stderr, "Number of certificates in the store %s: %d\n",
                suffix, sk_X509_OBJECT_num(sk));
    }
}

static int
cmp_double(const void *a_ptr, const void *b_ptr)
{
    const double * const a = a_ptr;
    const double * const b = b_ptr;

    return *a - *b < 0 ? -1 : *a - *b > 0 ? 1 : 0;
}

static void
get_calltimes(struct call_times *times, int verbosity)
{
    double *call_times;

    for (size_t q = 0; q < quantiles; q++) {
        for (size_t i = 0; i < threadcount; i++) {
            uint64_t start_t = q ? thread_data[i].q_data[q - 1].end_time.t
                                 : thread_data[i].start_time.t;
            uint64_t count = thread_data[i].q_data[q].count -
                (q ? thread_data[i].q_data[q - 1].count : 0);
            uint64_t found = thread_data[i].q_data[q].found -
                (q ? thread_data[i].q_data[q - 1].found : 0);
            uint64_t add = thread_data[i].q_data[q].added_certs -
                (q ? thread_data[i].q_data[q - 1].added_certs : 0);

            times[q].duration += thread_data[i].q_data[q].end_time.t - start_t;
            times[q].total_count += count;
            times[q].total_found += found;
            times[q].total_added += add;
        }
    }

    for (size_t q = 0; q < quantiles; q++) {
        times[quantiles].duration += times[q].duration;
        times[quantiles].total_count += times[q].total_count;
        times[quantiles].total_found += times[q].total_found;
        times[quantiles].total_added += times[q].total_added;
    }

    for (size_t q = (quantiles == 1); q <= quantiles; q++)
        times[q].avg = (double) times[q].duration / OSSL_TIME_US / times[q].total_count;

    if (verbosity >= VERBOSITY_VERBOSE) {
        call_times = OPENSSL_zalloc(threadcount * sizeof(*call_times));

        for (size_t q = (quantiles == 1); q <= quantiles; q++) {
            double variance = 0;

            for (size_t i = 0; i < threadcount; i++) {
                uint64_t start_t = q && q != quantiles ? thread_data[i].q_data[q - 1].end_time.t
                                                       : thread_data[i].start_time.t;
                uint64_t duration = thread_data[i].q_data[OSSL_MIN(q, quantiles - 1)].end_time.t - start_t;
                uint64_t count = thread_data[i].q_data[OSSL_MIN(q, quantiles - 1)].count -
                    (q && q != quantiles ? thread_data[i].q_data[q - 1].count : 0);
                call_times[i] = (double) duration / OSSL_TIME_US / count;
            }

            times[q].min = times[q].max = call_times[0];
            times[q].min_idx = times[q].max_idx = 0;

            for (size_t i = 0; i < threadcount; i++) {
                if (call_times[i] < times[q].min) {
                    times[q].min = call_times[i];
                    times[q].min_idx = i;
                }

                if (call_times[i] > times[q].max) {
                    times[q].max = call_times[i];
                    times[q].max_idx = i;
                }
            }

            qsort(call_times, threadcount, sizeof(call_times[0]), cmp_double);
            times[q].median = call_times[threadcount / 2];

            for (size_t i = 0; i < threadcount; i++) {
                double dev = call_times[i] - times[q].avg;

                variance += dev * dev;
            }

            times[q].stddev = sqrt(variance / threadcount);
        }

        OPENSSL_free(call_times);
    }
}

static void
report_result(int verbosity)
{
    struct call_times *times;

    times = OPENSSL_zalloc(sizeof(*times) * (quantiles + 1));

    get_calltimes(times, verbosity);

    switch (verbosity) {
    case VERBOSITY_TERSE:
        printf("%lf\n", times[1].avg);
        break;
    case VERBOSITY_DEFAULT:
        printf("Average time per call: %lfus\n", times[1].avg);
        break;
    case VERBOSITY_VERBOSE:
    default:
        /* if quantiles == 1, we only need to print total runtime info */
        for (size_t i = (quantiles == 1); i <= quantiles; i++) {
            if (i < quantiles)
                printf("Part %8zu", i + 1);
            else
                printf("Total runtime");

            printf(": avg: %9.3lf us, median: %9.3lf us"
                   ", min: %9.3lf us @thread %3zu, max: %9.3lf us @thread %3zu"
                   ", stddev: %9.3lf us (%8.4lf%%)"
                   ", hits %9zu of %9zu (%8.4lf%%)"
                   ", added certs: %zu\n",
                   times[i].avg, times[i].median,
                   times[i].min, times[i].min_idx,
                   times[i].max, times[i].max_idx,
                   times[i].stddev,
                   100.0 * times[i].stddev / times[i].avg,
                   times[i].total_found,
                   (times[i].total_count - times[i].total_added),
                   100.0 * times[i].total_found
                           / (times[i].total_count - times[i].total_added),
                   times[i].total_added);
        }
        break;
    }
}

static void
usage(char * const argv[])
{
    fprintf(stderr,
            "Usage: %s [-t] [-v] [-q N] [-T time] [-G num] [-g num] "
            "[-k num_keys] [-K keyalg[:bits][:param=value...]] "
            "[-n nonce_type:type_args] [-m mode] [-w writer_threads] "
            "[-W percentage] [-C threads] [-s stride] [-r stripe_step] "
            "[-R stripe_size] certsdir [certsdir...] threadcount\n"
            "\t-t\tTerse output\n"
            "\t-v\tVerbose output.  Multiple usage increases verbosity.\n"
            "\t-q\tGather information about temporal N-quantiles.\n"
            "\t\tDone only when the output is verbose.  Default: "
            OPENSSL_MSTR(QUANTILES) "\n"
            "\t-T\tTimeout for the test run in seconds,\n"
            "\t\tcan be fractional.  Default: "
            OPENSSL_MSTR(RUN_TIME) "\n"
            "\t-G\tNumber of generated certificates.  Default: "
            OPENSSL_MSTR(NUM_CERTS) "\n"
            "\t-g\tNumber of initially loaded generated certificates.\n"
            "\t\tDefault: " OPENSSL_MSTR(NUM_LOAD_CERTS) "\n"
            "\t-k\tNumber of different keys to be used\n"
            "\t\tfor the generated certificates.  Default: "
            OPENSSL_MSTR(NUM_KEYS) "\n"
            "\t-K\tAlgorithm and key size of the generated keys.\n"
            "\t\tDefault: " KEY_ALGO "\n"
            "\t-n\tNonce configuration, supported options:\n"
            "\t\t\tgen - generated\n"
            "\t\t\tfile:PATH - load nonce certificate from PATH;\n"
            "\t\t\tif PATH is relative, the provided certsdir's are searched.\n"
            "\t\tDefault: " NONCE_CFG "\n"
            "\t-m\tTest mode, can be one of r, rw.  Default: r\n"
            "\t-w\tMaximum number of threads that attempt addition\n"
            "\t\tof the new certificates to the store in rw mode,\n"
            "\t\t0 is unlimited.  Default: " OPENSSL_MSTR(MAX_WRITERS) "\n"
            "\t-W\tProbability of a certificate being written\n"
            "\t\tto the store, instead of being queried,\n"
            "\t\tin percents.  Default: " OPENSSL_MSTR(W_PROBABILITY) "\n"
            "\t-C\tNumber of threads that share the same X.509\n"
            "\t\tstore context object.  Default: "
            OPENSSL_MSTR(CTX_SHRE_THREADS) "\n"
            "\t-s stride, -r stripe_step, -R stripe_size\n"
            "\t\tMap Nth thread to ((N % R) * s + (N / R) * r)th CPU\n"
            "\t\tin the available process affinity mask (modulus mask size).\n"
            "\t\tWhen all parameters are 0, no CPU thread affinity setting is\n"
            "\t\tperformed.  Supported only on Linux/glibc and Windows.\n"
            "\t\tDefault: 0, 0, 0\n",
            basename(argv[0]));
}

static size_t
parse_timeout(const char * const optarg)
{
    char *endptr = NULL;
    double timeout_s;

    timeout_s = strtod(optarg, &endptr);

    if (endptr == NULL || *endptr != '\0' || timeout_s < 0)
        errx(EXIT_FAILURE, "incorrect timeout value: \"%s\"");

    if (timeout_s > SIZE_MAX / 1000000)
        errx(EXIT_FAILURE, "timeout is too large: %f", timeout_s);

    return timeout_s * 1e6;
}

static double
parse_probability(const char * const optarg)
{
    char *endptr = NULL;
    double prob;

    prob = strtod(optarg, &endptr);

    if (endptr == NULL || *endptr != '\0' || prob < 0 || prob > 100)
        errx(EXIT_FAILURE, "incorrect probability value: \"%s\"", optarg);

    return prob;
}

/**
 * Parse nonce configuration string. Currently supported formats:
 *  * "gen" - generate a nonce certificate
 *  * "file:PATH" - where PATH is either a relative path (that will be then
 *                  checked against the list of directories provided),
 *                  or an absolute one.
 */
static void
parse_nonce_cfg(const char * const optarg, struct nonce_cfg *cfg)
{
    static const char gen[] = "gen";
    static const char file_pfx[] = "file:";

    if (strncmp(optarg, gen, sizeof(gen)) == 0) {
        cfg->type = NONCE_GENERATED;
    } else if (strncmp(optarg, file_pfx, sizeof(file_pfx) - 1) == 0) {
        cfg->type = NONCE_PATH;
        cfg->path = optarg + sizeof(file_pfx) - 1;
    } else {
        errx(EXIT_FAILURE, "incorrect nonce configuration: \"%s\"", optarg);
    }
}

static long long
parse_int(const char * const s, long long min, long long max,
          const char * const what)
{
    char *endptr = NULL;
    long long ret;

    ret = strtoll(s, &endptr, 0);
    if (endptr == NULL || *endptr != '\0')
        errx(EXIT_FAILURE, "failed to parse %s as a number: \"%s\"", what, s);
    if (ret < min || ret > max)
        errx(EXIT_FAILURE, "provided value of %s is out of the expected"
                           " %lld..%lld range: %lld", what, min, max, ret);

    return ret;
}

int
main(int argc, char *argv[])
{
    int i;
    OSSL_TIME duration;
    size_t ctx_share_cnt = CTX_SHARE_THREADS;
    double avcalltime;
    char *alg_name_storage = NULL;
    char *cert = NULL;
    int ret = EXIT_FAILURE;
    EVP_PKEY_CTX *key_ctx;
    BIO *bio = NULL;
    X509 *x509 = NULL;
    int opt;
    int dirs_start;
    size_t num_certs = 0;
    size_t num_store_gen_certs = 0;
    struct nonce_cfg nonce_cfg;
    struct affinity_cfg affinity_cfg = { 0 };
    bool set_affinity = false;

    parse_nonce_cfg(NONCE_CFG, &nonce_cfg);

    while ((opt = getopt(argc, argv, "tvq:T:G:g:k:K:m:n:w:W:S:s:r:R:")) != -1) {
        switch (opt) {
        case 't': /* terse */
            verbosity = VERBOSITY_TERSE;
            break;
        case 'v': /* verbose */
            if (verbosity < VERBOSITY_VERBOSE) {
                verbosity = VERBOSITY_VERBOSE;
            } else {
                if (verbosity < VERBOSITY_MAX__ - 1)
                    verbosity++;
            }
            break;
        case 'q': /* quantiles */
            quantiles = parse_int(optarg, 1, INT_MAX,
                                  "number of quantiles");
            break;
        case 'T': /* timeout */
            timeout_us = parse_timeout(optarg);
            break;
        case 'G': /* number of generated certs */
            num_gen_certs = parse_int(optarg, 0, INT_MAX,
                                      "number of initially loaded generated"
                                      " certificates");
            break;
        case 'g': /* number of initially loaded generated certs */
            num_gen_load_certs = parse_int(optarg, 0, INT_MAX,
                                           "number of initially loaded"
                                           " generated certificates");
            break;
        case 'k': /* number of generated keys */
            num_gen_keys = parse_int(optarg, 0, INT_MAX,
                                     "number of generated keys");
            break;
        case 'K': /* key type */
            gen_key_algo = optarg;
            break;
        case 'm': /* mode */
            if (strcasecmp(optarg, "r") == 0) {
                mode = MODE_R;
            } else if (strcasecmp(optarg, "rw") == 0) {
                mode = MODE_RW;
            } else {
                errx(EXIT_FAILURE, "Unknown mode: \"%s\"", optarg);
            }
            break;
        case 'n': /* nonce */
            parse_nonce_cfg(optarg, &nonce_cfg);
            break;
        case 'w': /* maximum writers */
            max_writers = parse_int(optarg, 0, INT_MAX,
                                    "maximum number of writers");
        case 'W': /* percent of writes */
            w_probability = (size_t) (parse_probability(optarg) * 65536 / 100);
            break;
        case 'S': /* how many threads share X509_STORE_CTX */
            ctx_share_cnt = parse_int(optarg, 1, INT_MAX,
                                      "X509_STORE_CTX share degree");
            break;
        case 's': /* stride, s in ((N % R) * s + (N / R) * r) mod ncpus */
            affinity_cfg.stride = parse_int(optarg, 0, INT_MAX,
                                            "thread affinity stride");
            break;
        case 'r': /* stripe step, r in ((N % R) * s + (N / R) * r) mod ncpus */
            affinity_cfg.stripe_step = parse_int(optarg, 0, INT_MAX,
                                                 "thread affinity stripe step");
            break;
        case 'R': /* stripe size, R in ((N % R) * s + (N / R) * r) mod ncpus */
            affinity_cfg.stripe_size = parse_int(optarg, 0, INT_MAX,
                                                 "thread affinity stripe size");
            break;
        default:
            warnx("Unknown option: \"-%c\"", opt);
            usage(argv);
            return EXIT_FAILURE;
        }
    }

    if (verbosity < VERBOSITY_VERBOSE)
        quantiles = 1;

    if (num_gen_certs > 0 && num_gen_keys == 0)
        errx(EXIT_FAILURE,
             "Cannot generate certificates without generating keys");

    if (num_gen_certs < num_gen_load_certs)
        errx(EXIT_FAILURE, "Cannot load more certificates than generate");

    if (num_gen_certs == num_gen_load_certs && mode == MODE_RW)
        errx(EXIT_FAILURE, "No generated certificates to use after"
                           " the initially loaded ones, please increase"
                           " -G to be more than -g");

    if (argv[optind] == NULL)
        errx(EXIT_FAILURE, "certsdir is missing");

    dirs_start = optind++;

    /*
     * Store the part of argv containing directories to nonce_cfg so
     * load_nonce_from_path can use it later.
     */
    nonce_cfg.dirs = argv + dirs_start;
    nonce_cfg.num_dirs = argc - 1 - dirs_start;

    if (optind >= argc)
        errx(EXIT_FAILURE, "threadcount is missing");

    threadcount = parse_int(argv[argc - 1], 1, INT_MAX, "threadcount");

    thread_data = OPENSSL_zalloc(threadcount * sizeof(*thread_data));
    if (thread_data == NULL)
        errx(EXIT_FAILURE, "Failed to create thread_data array");

    for (size_t i = 0; i < threadcount; i++) {
        thread_data[i].q_data = OPENSSL_zalloc(quantiles *
                                               sizeof(*(thread_data[i].q_data)));
        if (thread_data[i].q_data == NULL)
            errx(EXIT_FAILURE, "Failed to create quantiles array for thread"
                               " %zu", i);
    }

    if (num_gen_keys > 0) {
        key_ctx = make_pkey_ctx(gen_key_algo, &alg_name_storage);
        if (key_ctx == NULL)
            exit(EXIT_FAILURE);

        gen_keys = OPENSSL_zalloc(num_gen_keys * sizeof(*gen_keys));
        if (gen_keys == NULL)
            errx(EXIT_FAILURE, "Error allocating generated keys array");

        gen_pubkeys = OPENSSL_zalloc(num_gen_keys * sizeof(*gen_pubkeys));
        if (gen_pubkeys == NULL)
            errx(EXIT_FAILURE, "Error allocating public keys array");

        for (size_t i = 0; i < num_gen_keys; i++) {
            if (verbosity >= VERBOSITY_DEBUG_STATS) {
                static OSSL_TIME last = { 0 };
                OSSL_TIME cur = ossl_time_now();
                if (cur.t - last.t > OSSL_TIME_SECOND) {
                    fprintf(stderr, "Generating key %zu out of %zu...\n",
                            i + 1, num_gen_keys);
                    last.t = cur.t;
                }
            }
            gen_keys[i] = gen_key(key_ctx);
            if (gen_keys[i] == NULL)
                exit(EXIT_FAILURE);

            gen_pubkeys[i] = get_pubkey(gen_keys[i]);
            if (gen_pubkeys[i] == NULL)
                exit(EXIT_FAILURE);
        }

        if (verbosity >= VERBOSITY_DEBUG_STATS)
            fprintf(stderr, "Generated %zu keys\n", num_gen_keys);
    }

    if (num_gen_certs > 0) {
        gen_certs = OPENSSL_zalloc(num_gen_certs * sizeof(*gen_certs));
        if (gen_certs == NULL)
            errx(EXIT_FAILURE, "Error allocating generated certificates array");

        for (size_t i = 0; i < num_gen_certs; i++) {
            if (verbosity >= VERBOSITY_DEBUG_STATS) {
                static OSSL_TIME last = { 0 };
                OSSL_TIME cur = ossl_time_now();
                if (cur.t - last.t > OSSL_TIME_SECOND) {
                    fprintf(stderr, "Generating certificate %zu out of"
                                    " %zu...\n", i + 1, num_gen_certs);
                    last.t = cur.t;
                }
            }
            gen_certs[i] = gen_cert(i % num_gen_keys, NULL, NULL);
            if (gen_certs[i] == NULL)
                goto err;
        }

        if (verbosity >= VERBOSITY_DEBUG_STATS)
            fprintf(stderr, "Generated %zu certificates\n", num_gen_certs);
    }

    store = X509_STORE_new();
    if (store == NULL || !X509_STORE_set_default_paths(store))
        errx(EXIT_FAILURE, "Failed to create X509_STORE");

    for (int i = dirs_start; i < argc - 1; i++) {
        struct stat st;
        struct dirent *e;
        DIR *d = opendir(argv[i]);

        if (d == NULL)
            err(EXIT_FAILURE, "Could not open \"%s\"", argv[i]);

        while (1) {
            errno = 0;
            e = readdir(d);

            if (e == NULL) {
                if (errno != 0) {
                    err(EXIT_FAILURE, "An error ocurred while reading directory"
                                      " \"%s\"", argv[i]);
                } else {
                    break;
                }
            }

            cert = perflib_mk_file_path(argv[i], e->d_name);
            if (cert == NULL)
                errx(EXIT_FAILURE, "Failed to allocate cert name in directory"
                                   " \"%s\" for entry \"%s\"",
                                   argv[i], e->d_name);

            if (lstat(cert, &st) < 0) {
                warn("Got error on lstat(\"%s\")", cert);
                goto next_file;
            }

            if (st.st_mode & S_IFMT != S_IFREG) {
                if (verbosity >= VERBOSITY_DEBUG)
                    warnx("\"%s\" is not a regular file, skipping", cert);
                goto next_file;
            }

            bio = BIO_new_file(cert, "rb");
            if (bio == NULL)
                errx(EXIT_FAILURE, "Unable to create BIO for \"%s\"", cert);

            x509 = PEM_read_bio_X509(bio, NULL, NULL, NULL);
            if (x509 == NULL) {
                if (verbosity >= VERBOSITY_DEBUG)
                    warnx("Failed to read certificate from \"%s\", skipping",
                          cert);
                goto next_file;
            } else {
                if (!X509_STORE_add_cert(store, x509)) {
                    warnx("Failed to add a certificate from \"%s\""
                          " to the store\n", cert);
                    goto next_file;
                } else {
                    if (verbosity >= VERBOSITY_DEBUG)
                        fprintf(stderr, "Successfully added a certificate from"
                                        " \"%s\" to the store\n", cert);
                    num_certs++;
                }
            }

 next_file:
            X509_free(x509);
            x509 = NULL;

            BIO_free(bio);
            bio = NULL;

            OPENSSL_free(cert);
            cert = NULL;
        }
    }

    if (verbosity >= VERBOSITY_DEBUG_STATS)
        fprintf(stderr, "Added %zu certificates to the store\n", num_certs);

    num_store_gen_certs = 0;
    for (size_t i = 0; i < num_gen_load_certs; i++) {
        if (!X509_STORE_add_cert(store, gen_certs[i])) {
            warnx("Failed to add generated certificate %zu to the store\n", i);
        } else {
            if (verbosity >= VERBOSITY_DEBUG)
                fprintf(stderr, "Successfully added generated certificate"
                                " %zu to the store\n", i);
            num_certs++;
            num_store_gen_certs++;
        }
    }

    if (verbosity >= VERBOSITY_DEBUG_STATS)
        fprintf(stderr, "Added %zu generated certificates to the store,"
                        " %zu total\n", num_store_gen_certs, num_certs);

    report_store_size(store, "before the test run", verbosity);

    x509_nonce = make_nonce(&nonce_cfg);
    if (x509_nonce == NULL)
        errx(EXIT_FAILURE, "Unable to create the nonce X509 object");

    for (size_t i = 0; i < threadcount; i++) {
        if (i % ctx_share_cnt) {
            thread_data[i].ctx = thread_data[i - i % ctx_share_cnt].ctx;
        } else {
            thread_data[i].ctx = X509_STORE_CTX_new();
            if (thread_data[i].ctx == NULL
                || !X509_STORE_CTX_init(thread_data[i].ctx, store, x509, NULL))
                errx(EXIT_FAILURE, "Failed to initialise X509_STORE_CTX"
                     " for thread %zu", i);
        }
    }

    max_time = ossl_time_add(ossl_time_now(), ossl_us2time(timeout_us));

    if (affinity_cfg.stride != 0
        || affinity_cfg.stripe_step != 0
        || affinity_cfg.stripe_size != 0)
        set_affinity = true;

    if (set_affinity && affinity_cfg.stripe_size == 0)
        affinity_cfg.stripe_size = INT_MAX;

    if (!perflib_run_multi_thread_test_ex(do_x509storeissuer, threadcount,
                                          &duration,
                                          set_affinity ? stride_stripe_affinity
                                                       : NULL,
                                          &affinity_cfg))
        errx(EXIT_FAILURE, "Failed to run the test");

    if (error)
        errx(EXIT_FAILURE, "Error during test");

    report_store_size(store, "after the test run", verbosity);

    report_result(verbosity);

    ret = EXIT_SUCCESS;

 err:
    X509_NAME_free(x509_name_nonce);
    X509_free(x509_nonce);
    X509_STORE_free(store);
    if (gen_certs) {
        for (size_t i = 0; i < num_gen_certs; i++)
            X509_free(gen_certs[i]);
    }
    OPENSSL_free(gen_certs);
    if (gen_pubkeys) {
        for (size_t i = 0; i < num_gen_keys; i++)
            EVP_PKEY_free(gen_pubkeys[i]);
    }
    OPENSSL_free(gen_pubkeys);
    if (gen_keys) {
        for (size_t i = 0; i < num_gen_keys; i++)
            EVP_PKEY_free(gen_keys[i]);
    }
    OPENSSL_free(gen_keys);
    EVP_PKEY_CTX_free(key_ctx);
    OPENSSL_free(alg_name_storage);
    if (thread_data != NULL) {
        for (size_t i = 0; i < threadcount; i++) {
            if (!(i % ctx_share_cnt))
                X509_STORE_CTX_free(thread_data[i].ctx);
            OPENSSL_free(thread_data[i].q_data);
        }
    }
    OPENSSL_free(thread_data);
    return ret;
}
