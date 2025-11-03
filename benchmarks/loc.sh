#!/bin/sh

# find the number of lines of code in each source file on the command line
for file in $* ; do
    case $file in
        *.wybe) comment="#" ;;
        *.c) comment="\/\/" ;;
        *.rs) comment="\/\/" ;;
        *.hs) comment="--" ;;
        *) echo "$file: nrecognised file type" >&2 ; exit 1 ;;
    esac
    printf "$file: "
    sed -e '/^\s*$/d' -e "/^\s*${comment}/d" $file | wc -l
done
