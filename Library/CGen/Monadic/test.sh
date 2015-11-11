#Check the number of arguments supplied:
if [ $# -ne 1 ]
then
    echo "test.sh: Error: Argument must be the Specware installation to use."
    exit 1
fi

SPECWARE4=$1
echo "Testing Library/CGen/Monadic:"

#TODO: Add CGen.sw?
run-proc.sh ${SPECWARE4} ${SPECWARE4}/Library/CGen/Monadic/C_DSL.sw
#run-proc.sh ${SPECWARE4} ${SPECWARE4}/Library/CGen/Monadic/C_Permissions.sw  #Eddy says this is in flux.  It currently doesn't proc.
run-proc.sh ${SPECWARE4} ${SPECWARE4}/Library/CGen/Monadic/C_Predicates.sw
run-proc.sh ${SPECWARE4} ${SPECWARE4}/Library/CGen/Monadic/CPrettyPrinter.sw
run-proc.sh ${SPECWARE4} ${SPECWARE4}/Library/CGen/Monadic/C.sw
run-proc.sh ${SPECWARE4} ${SPECWARE4}/Library/CGen/Monadic/TraceMonad_Simple.sw
run-proc.sh ${SPECWARE4} ${SPECWARE4}/Library/CGen/Monadic/TraceMonad.sw

run-proc.sh ${SPECWARE4} ${SPECWARE4}/Library/CGen/Monadic/Examples/NegateBytes.sw
run-proc.sh ${SPECWARE4} ${SPECWARE4}/Library/CGen/Monadic/Examples/NegateBytesOrig.sw
run-proc.sh ${SPECWARE4} ${SPECWARE4}/Library/CGen/Monadic/Examples/Examples.sw

