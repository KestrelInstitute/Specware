FORMAT=latexpdf

.PHONY: language-manual user-manual tutorial xform-manual isabelle-interface quickreference

all: publish

build: language-manual user-manual tutorial xform-manual isabelle-interface quickreference

publish: build
	cp language-manual/_build/latex/*.pdf ..
	cp user-manual/_build/latex/*.pdf ..
	cp tutorial/_build/latex/*.pdf ..
	cp xform-manual/_build/latex/*.pdf ..
	cp isabelle-interface/_build/latex/*.pdf .
	cp quickreference/_build/latex/*.pdf ..


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

quickreference:
	cd quickreference ; make $(FORMAT)

clean:
	cd language-manual ; make clean ; cd ../user-manual ; make clean ; cd ../xform-manual ; make clean ; cd ../tutorial ; make clean ; cd ../isabelle-interface ; make clean
