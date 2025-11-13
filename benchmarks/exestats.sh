#!/bin/sh

# present a latex table showing test case, lines of code, exe size, and mean
# execution time for each source file specified on the command line.
printf '\\begin{tabular}{| l | r | r | r |}\n\\hline\n'
printf '\\textbf{Program} & \\textbf{LoC} & \\textbf{Exe Size (b)} & \\textbf{Time (s)} \\\\\n\\hline\n'
for file in $* ; do
    case $file in
        *.c)    comment="\/\/" ; exefile=`basename $file .c` ;;
        *.hs)   comment="--"   ; exefile=`basename $file .hs` ;;
        *.rs)   comment="\/\/" ; exefile=`basename $file .rs` ;;
        *.wybe) comment="#"    ; exefile=`basename $file .wybe` ;;
        *) echo "$file: nrecognised file type" >&2 ; exit 1 ;;
    esac  
    lines=`sed -e '/^\s*$/d' -e "/^\s*${comment}/d" $file | wc -l`
    exesize=`ls -l $exefile | awk '{printf("%s\n", $5);}'`
    exectime=`awk '$1 == "'"$exefile"'" {count++; tot+=$8} END {printf("%7.2f\n", tot/count);}' BENCHMARKS`
    rowname='\texttt{'`echo $exefile | sed 's/_/\\\\_/g'`'}'
    printf "%s & %d & %d & %s \\\\\\\\\n\\hline\n" $rowname $lines $exesize $exectime
done
printf '\\end{tabular}\n'