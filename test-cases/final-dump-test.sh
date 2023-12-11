#!/bin/bash

LIMIT=60

if [[ `uname` == 'Darwin' ]]; then
	TIMEOUT="gtimeout $LIMIT"
elif [[ `uname` == 'Linux' ]]; then
	TIMEOUT="timeout $LIMIT"
fi
LIBDIR="../wybelibs"

# clean up
rm -f final-dump/*.bc
rm -f final-dump/*.o
rm -f final-dump/*.out

for f in `ls final-dump/*.wybe`
do
	out=`echo -e "$f" | sed 's/.wybe$/.out/'`
	exp=`echo -e "$f" | sed 's/.wybe$/.exp/'`
	targ=`echo -e "$f" | sed 's/.wybe$/.o/'`
	$TIMEOUT ../wybemk --log=FinalDump --force-all -L $LIBDIR $targ 2>&1 \
	    | sed -e 's/@\([A-Za-z0-9_]*\):[0-9:]*/@\1:nn:nn/g' \
            -e "s|`pwd`|!ROOT!|g" \
            -e 's/\[[0-9][0-9]* x i8\]/[?? x i8]/g' \
        > $out
	# Add a newline to the end of a file if there isn't to resolve platform differences.
	ed -s $out <<< w > /dev/null 2>&1
	if [ ! -r $exp ] ; then
		printf "[31m?[39m"
		NEW="$NEW\n    $out"
	elif diff -q $exp $out >/dev/null 2>&1 ; then
		printf "."
	else
		printf "\n[34;1m**************** difference building $targ ****************[0m\n" >> ../ERRS
		dwdiff -C1 -c -d '()<>~!@:?.%#' $exp $out >> ../ERRS 2>&1
		printf "[31mX[39m"
		FAILS="$FAILS\n    $out"
	fi
done
echo -e
if [ -n "$FAILS" ] ; then
	echo -e "Failed: $FAILS\nSee ERRS for differences."
	exit 1
else
	echo -e "ALL TESTS PASS"
fi
if [ -n "$NEW" ] ; then
	echo -e "New tests: $NEW\nDo .\update-exp to specify expected output"
fi
