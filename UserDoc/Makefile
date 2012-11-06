FORMAT=latexpdf
all: language-manual user-manual tutorial xform-manual isabelle-interface 

.PHONY: language-manual user-manual tutorial xform-manual isabelle-interface 

#! /bin/bash


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

clean:
	cd language-manual ; make clean ; cd ../user-manual ; make clean ; cd ../xform-manual ; make clean ; cd ../tutorial ; make clean ; cd ../isabelle-interface ; make clean
