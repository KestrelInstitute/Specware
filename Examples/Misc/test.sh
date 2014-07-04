#Check the number of arguments supplied:
if [ $# -ne 2 ]
then
    echo "test.sh: Error: Argument must be the Specware installation to test and ISABELLE_2013_2_ROOT."
    exit 1
fi

SPECWARE4=$1
ISABELLE_2013_2_ROOT=$2

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
run-isabelle2013-2.sh ${SPECWARE4}/Examples/Misc/Isa/TwoMorphisms_CheckRqmtsC.thy ${ISABELLE_2013_2_ROOT}
