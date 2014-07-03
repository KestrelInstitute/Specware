#Check the number of arguments supplied:
if [ $# -ne 2 ]
then
    echo "test.sh: Error: Argument must be the Specware installation to test and ISABELLE_2013_2_ROOT."
    exit 1
fi

SPECWARE4=$1
ISABELLE_2013_2_ROOT=$2

run-proc.sh ${SPECWARE4} TwoMorphisms#A
run-proc.sh ${SPECWARE4} TwoMorphisms#B
run-proc.sh ${SPECWARE4} TwoMorphisms#CheckRqmtsB
run-proc.sh ${SPECWARE4} TwoMorphisms#C
run-proc.sh ${SPECWARE4} TwoMorphisms#CheckRqmtsC
run-gen-obligs.sh ${SPECWARE4} TwoMorphisms#A
run-gen-obligs.sh ${SPECWARE4} TwoMorphisms#B
run-gen-obligs.sh ${SPECWARE4} TwoMorphisms#CheckRqmtsB
run-gen-obligs.sh ${SPECWARE4} TwoMorphisms#C
run-gen-obligs.sh ${SPECWARE4} TwoMorphisms#CheckRqmtsC
run-isabelle2013-2.sh Isa/TwoMorphisms_CheckRqmtsC.thy ${ISABELLE_2013_2_ROOT}
