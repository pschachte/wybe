#!/bin/sh
# run each benchmark test 5 times, ignoring output and noting the time in the
# BENCHMARKS file

if [ ! -f "$TESTINPUT" ] ; then
    echo "Assign \$TESTINPUT variable to a large file before benchmarking." >&2
    exit 1
fi

# Configuration:  define the $TESTINPUT environment variable to hold

repeat=5
case $1 in
    *_wc*)
        if [ ! -f "$TESTINPUT" ] ; then
            echo "Assign \$TESTINPUT variable to a large file before benchmarking." >&2
            exit 1
        fi
        input=$TESTINPUT ;;
    *)  input=/dev/null ;;
esac
ulimit -s 65520 -t 300
for exe in $* ; do
    echo "Testing $exe:"
    for i in `seq $repeat` ; do
        echo "  $i"
        printf "$exe" >> BENCHMARKS
        ( /usr/bin/time -a -o BENCHMARKS ./$exe <$input >/dev/null )
    done
done
