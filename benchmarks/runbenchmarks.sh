#!/bin/sh
# run each benchmark test 5 times, ignoring output and noting the time in the
# BENCHMARKS file

repeat=5
ulimit -s 65520
for exe in $* ; do
    echo "Testing $exe:"
    for i in `seq $repeat` ; do
        echo "  $i"
        printf "$exe" >> BENCHMARKS
        ( /usr/bin/time -a -o BENCHMARKS ./$exe >/dev/null )
    done
done
