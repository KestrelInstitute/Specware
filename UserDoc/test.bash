#!/bin/bash

#Check the number of arguments supplied:
if [ $# -ne 1 ]
then
    echo "test: ERROR: Must be given exactly one argument (the directory in which this script resides)."
    exit 18 # Just a made-up error code.
fi

THISSCRIPTDIR=$1     #old: `dirname $0`

#TODO Test other documentation formats besides PDF?

pushd ${THISSCRIPTDIR}/sources > /dev/null
make clean &> /dev/null
LOG=${THISSCRIPTDIR}/build-docs-test.log
echo "Building documentation (see ${LOG})."
make &> ${LOG}
popd > /dev/null

#Check to ensure that the files got built:

ls -l ${THISSCRIPTDIR}/sources/xform-manual/_build/latex/SpecwareTransformationManual.pdf
ls -l ${THISSCRIPTDIR}/sources/tutorial/_build/latex/SpecwareTutorial.pdf
ls -l ${THISSCRIPTDIR}/sources/user-manual/_build/latex/SpecwareUserManual.pdf
ls -l ${THISSCRIPTDIR}/sources/isabelle-interface/_build/latex/SpecwareIsabelleInterface.pdf
ls -l ${THISSCRIPTDIR}/sources/language-manual/_build/latex/SpecwareLanguageManual.pdf
ls -l ${THISSCRIPTDIR}/sources/quick-reference/_build/latex/SpecwareQuickReference.pdf
