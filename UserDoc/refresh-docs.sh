#!/bin/bash

THISSCRIPTDIR="$( cd "$( dirname "$0" )" && pwd )" #Simpler commands can just give "." here, which seems bad.

cp -pr ${THISSCRIPTDIR}/sources/xform-manual/_build/latex/SpecwareTransformationManual.pdf ${THISSCRIPTDIR}
cp -pr ${THISSCRIPTDIR}/sources/tutorial/_build/latex/SpecwareTutorial.pdf ${THISSCRIPTDIR}
cp -pr ${THISSCRIPTDIR}/sources/user-manual/_build/latex/SpecwareUserManual.pdf ${THISSCRIPTDIR}
cp -pr ${THISSCRIPTDIR}/sources/isabelle-interface/_build/latex/SpecwareIsabelleInterface.pdf ${THISSCRIPTDIR}
cp -pr ${THISSCRIPTDIR}/sources/language-manual/_build/latex/SpecwareLanguageManual.pdf ${THISSCRIPTDIR}
cp -pr ${THISSCRIPTDIR}/sources/quick-reference/_build/latex/SpecwareQuickReference.pdf ${THISSCRIPTDIR}
