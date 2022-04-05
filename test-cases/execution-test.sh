#!/bin/bash


if [[ `uname` == 'Darwin' ]]; then
	TIMEOUT=gtimeout
elif [[ `uname` == 'Linux' ]]; then
	TIMEOUT=timeout
fi
LIBDIR="../wybelibs"

# clean up
rm -f execution/*.o
rm -f execution/*.out

for f in `ls execution/*.wybe`
do
	in=`echo -e "$f" | sed 's/.wybe$/.in/'`
	out=`echo -e "$f" | sed 's/.wybe$/.out/'`
	cmdline=`echo -e "$f" | sed 's/.wybe$/.cmdline/'`
	exp=`echo -e "$f" | sed 's/.wybe$/.exp/'`
	targ=`echo -e "$f" | sed 's/.wybe$//'`
	rm -f $targ
        cmd="$targ"
        if [ -r $cmdline ] ; then
            cmd="$targ `cat $cmdline`"
        fi
	$TIMEOUT 20 ../wybemk --force-all -L $LIBDIR $targ >/dev/null
    $TIMEOUT 20 $cmd< $in &> $out
	if [ ! -r $exp ] ; then 
		printf "[31m?[39m"
		NEW="$NEW\n    $out"
	elif diff -q $exp $out >/dev/null 2>&1 ; then
		printf "."
	else 
		printf "\n[34;1m**************** difference building $targ ****************[0m\n" >> ../ERRS
		dwdiff -c -d '()<>~!@:?.%#' $exp $out >> ../ERRS 2>&1
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
	exit 1
fi
