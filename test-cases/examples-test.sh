#!/bin/bash

LIMIT=30

if [[ `uname` == 'Darwin' ]]; then
	TIMEOUT="gtimeout $LIMIT"
elif [[ `uname` == 'Linux' ]]; then
	TIMEOUT="timeout $LIMIT"
fi
LIBDIR="../wybelibs"

for f in `ls ../samples/*.wybe ../benchmarks/*/*.wybe`
do
	targ=`echo -e "$f" | sed 's/.wybe$//'`
	rm -f $targ $targ.o
	out=$($TIMEOUT ../wybemk --force-all -L $LIBDIR $targ 2>&1)
	if [ $? -eq 0 ] ; then
		printf "."
	else 
		printf "Failed to build $targ\n" >> ../ERRS
		echo $out >> ../ERRS
		printf "[31mX[39m"
		FAILS="$FAILS\n    $targ"
	fi 
done
echo -e
if [ -n "$FAILS" ] ; then
	echo -e "Failed: $FAILS\nSee ERRS for errors."
	exit 1
else
	echo -e "ALL TESTS PASS"
fi
