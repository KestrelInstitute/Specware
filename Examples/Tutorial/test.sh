#Check the number of arguments supplied:
if [ $# -ne 1 ]
then
    echo "test.sh: Error: Argument must be the Specware installation to test."
    exit 1
fi

SPECWARE4=$1

echo "  Testing Examples/Tutorial:"


run-proc.sh ${SPECWARE4} ${SPECWARE4}/Examples/Tutorial/MatchingSpecs#Symbols
run-proc.sh ${SPECWARE4} ${SPECWARE4}/Examples/Tutorial/MatchingSpecs#Words
run-proc.sh ${SPECWARE4} ${SPECWARE4}/Examples/Tutorial/MatchingSpecs#Messages
run-proc.sh ${SPECWARE4} ${SPECWARE4}/Examples/Tutorial/MatchingSpecs#SymbolMatching
run-proc.sh ${SPECWARE4} ${SPECWARE4}/Examples/Tutorial/MatchingSpecs#WordMatching
run-proc.sh ${SPECWARE4} ${SPECWARE4}/Examples/Tutorial/MatchingSpecs#Matches
run-proc.sh ${SPECWARE4} ${SPECWARE4}/Examples/Tutorial/MatchingSpecs#FindMatches

run-proc.sh ${SPECWARE4} ${SPECWARE4}/Examples/Tutorial/MatchingRefinements#Symbols
run-proc.sh ${SPECWARE4} ${SPECWARE4}/Examples/Tutorial/MatchingRefinements#Symbols_Ref
run-proc.sh ${SPECWARE4} ${SPECWARE4}/Examples/Tutorial/MatchingRefinements#WordMatching0
run-proc.sh ${SPECWARE4} ${SPECWARE4}/Examples/Tutorial/MatchingRefinements#WordMatching_Ref0
run-proc.sh ${SPECWARE4} ${SPECWARE4}/Examples/Tutorial/MatchingRefinements#WordMatching
run-proc.sh ${SPECWARE4} ${SPECWARE4}/Examples/Tutorial/MatchingRefinements#WordMatching_Ref
run-proc.sh ${SPECWARE4} ${SPECWARE4}/Examples/Tutorial/MatchingRefinements#FindMatches0
run-proc.sh ${SPECWARE4} ${SPECWARE4}/Examples/Tutorial/MatchingRefinements#FindMatches_Ref0
run-proc.sh ${SPECWARE4} ${SPECWARE4}/Examples/Tutorial/MatchingRefinements#FindMatches
run-proc.sh ${SPECWARE4} ${SPECWARE4}/Examples/Tutorial/MatchingRefinements#FindMatches_Ref

run-proc.sh ${SPECWARE4} ${SPECWARE4}/Examples/Tutorial/MatchingTest#Test
run-proc.sh ${SPECWARE4} ${SPECWARE4}/Examples/Tutorial/MatchingTest#Data