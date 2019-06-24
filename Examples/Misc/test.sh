#Check the number of arguments supplied:
if [ $# -ne 2 ]
then
    echo "test.sh: Error: Argument must be the Specware installation to test and ISABELLE_ROOT."
    exit 1
fi

SPECWARE4=$1
ISABELLE_ROOT=$2


echo "Running a tiny test of the Transform shell."
LOG=${SPECWARE4}/Examples/Misc/TinyTransformShellTest.swlog
run-specware-batch.sh ${SPECWARE4} ${LOG} <<EOFMARKER
cd ${SPECWARE4}/Examples/Misc
transform TinyTransformShellTest
at f
l
lr plus_0
done
exit
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
run-isabelle-build.sh ${SPECWARE4}/Examples/Misc/Isa ${ISABELLE_ROOT}
