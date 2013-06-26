FORMAT=latexpdf

.PHONY: language-manual user-manual tutorial xform-manual isabelle-interface quick-reference

all: publish

build: language-manual user-manual tutorial xform-manual isabelle-interface quick-reference

publish: build
# cp language-manual/_build/latex/*.pdf ..
# cp user-manual/_build/latex/*.pdf ..
# cp tutorial/_build/latex/*.pdf ..
# cp xform-manual/_build/latex/*.pdf ..
# cp isabelle-interface/_build/latex/*.pdf ..
# cp quick-reference/_build/latex/*.pdf ..


language-manual:
	cd language-manual ; make $(FORMAT)

user-manual:
	cd user-manual ; make $(FORMAT)

tutorial:
	cd tutorial ; make $(FORMAT)

xform-manual:
	cd xform-manual ; make $(FORMAT)

isabelle-interface:
	cd isabelle-interface ; make $(FORMAT)

quick-reference:
	cd quick-reference ; make $(FORMAT)

clean:
	cd language-manual ; make clean ; cd ../user-manual ; make clean ; cd ../xform-manual ; make clean ; cd ../tutorial ; make clean ; cd ../isabelle-interface ; make clean ; cd ../quick-reference ; make clean
