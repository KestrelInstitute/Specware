#Check the number of arguments supplied:
if [ $# -ne 1 ]
then
    echo "test.sh: Error: Argument must be the Specware installation to use."
    exit 1
fi

SPECWARE4=$1
echo "Testing Library/CGen/Deep:"

run-proc.sh ${SPECWARE4} ${SPECWARE4}/Library/CGen/Deep/C
run-proc.sh ${SPECWARE4} ${SPECWARE4}/Library/CGen/Deep/CPrettyPrinter
run-proc.sh ${SPECWARE4} ${SPECWARE4}/Library/CGen/Deep/CPrettyPrinter_Tests
run-proc.sh ${SPECWARE4} ${SPECWARE4}/Library/CGen/Deep/All

#Actually run the tests:
LOG=${SPECWARE4}/Library/CGen/Deep/CPrettyPrinter_Tests.testlog
run-specware-batch.sh ${SPECWARE4} ${LOG} <<EOF
ctext ${SPECWARE4}/Library/CGen/Deep/CPrettyPrinter_Tests
e run_test
quit
EOF


# #Actually run the pretty printer tests and make sure ERROR: is not printed:
# fakenewline="NEWLINE" # this will get replaced by a true newline in the run-specware.sh script.
# (run-specware.sh ${SPECWARE4} ${LOG} "ctext "${SPECWARE4}"/Library/CGen/Deep/CPrettyPrinter_Tests NEWLINE e run_test")


