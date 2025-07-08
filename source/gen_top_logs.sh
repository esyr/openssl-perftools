#! /bin/bash -eux

: "${NUM_THREADS:=4 8 12 24 48 96}"
: "${ANALYZER=../../openssl/util/analyze-contention-log.sh}"

[ 0 -lt "$#" ] || {
    echo "Usage: $0 INPUT_FILE" > /dev/stderr
    exit 1
}

[ "x-" != "x$1" ] || $1="/dev/stdin"

args_join() {
    printf -- "%s" "$1"
    shift
    [ 0 -eq "$#" ] || printf -- "-%s" "$@"
}

gen_fn_sfx() {
    bn="$(basename "$1")"
    shift
    args_join "${bn}" "$@" | sed 's/\//_/g'
}

while read -a args; do
    [ "x${args[0]###}" = "x${args[0]}" ] || {
		printf -- "Skipping '%s'...\n" "${args[*]}";
		continue
	}
    printf -- "Processing %s...\n" "${args[*]}" > /dev/stderr
    for i in ${NUM_THREADS}; do
        rm -f lock-contention-log.*.txt
        "${args[@]}" "$i"
        OUTFILE="top-latencies.$(gen_fn_sfx "${args[@]}").$i.txt"
        printf -- "%s\n\n" "${args[*]} $i" > "$OUTFILE"
        "${ANALYZER}" lock-contention-log.*.txt >> "$OUTFILE"
    done
    args=()
done < "$1"

rm -f lock-contention-log.*.txt
