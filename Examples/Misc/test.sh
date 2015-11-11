#Check the number of arguments supplied:
if [ $# -ne 2 ]
then
    echo "test.sh: Error: Argument must be the Specware installation to test and ISABELLE_2015_ROOT."
    exit 1
fi

SPECWARE4=$1
ISABELLE_2015_ROOT=$2


echo "Running a tiny test of the Transform shell."
LOG=${SPECWARE4}/Examples/Misc/TinyTransformShellTest.swlog
run-specware-batch.sh ${SPECWARE4} ${LOG} <<EOFMARKER
transform TinyTransformShellTest
at f
simplify
quit
EOFMARKER

echo "Testing a small example with two morphisms:"
run-proc.sh ${SPECWARE4} ${SPECWARE4}/Examples/Misc/TwoMorphisms#A
run-proc.sh ${SPECWARE4} ${SPECWARE4}/Examples/Misc/TwoMorphisms#B
run-proc.sh ${SPECWARE4} ${SPECWARE4}/Examples/Misc/TwoMorphisms#CheckRqmtsB
run-proc.sh ${SPECWARE4} ${SPECWARE4}/Examples/Misc/TwoMorphisms#C
run-proc.sh ${SPECWARE4} ${SPECWARE4}/Examples/Misc/TwoMorphisms#CheckRqmtsC
run-gen-obligs.sh ${SPECWARE4} ${SPECWARE4}/Examples/Misc/TwoMorphisms#A
run-gen-obligs.sh ${SPECWARE4} ${SPECWARE4}/Examples/Misc/TwoMorphisms#B
run-gen-obligs.sh ${SPECWARE4} ${SPECWARE4}/Examples/Misc/TwoMorphisms#CheckRqmtsB
run-gen-obligs.sh ${SPECWARE4} ${SPECWARE4}/Examples/Misc/TwoMorphisms#C
run-gen-obligs.sh ${SPECWARE4} ${SPECWARE4}/Examples/Misc/TwoMorphisms#CheckRqmtsC
run-isabelle2015-build.sh ${SPECWARE4}/Examples/Misc/Isa ${ISABELLE_2015_ROOT}

