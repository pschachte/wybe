#!/bin/bash

exitcode=0

run() {
    echo "--------------------------------------------------------"
    echo "$1 Test"
    echo "--------------------------------------------------------"
    "${@:2}"
    [ $? -ne 0 ] && exitcode=1
    echo "--------------------------------------------------------"
    echo ""
}

run "Final Dump" ./final-dump-test.sh
run "Execution"  ./execution-test.sh
run "Complex"    python3 ./complex-test.py
run "Examples"   ./examples-test.sh

exit $exitcode
