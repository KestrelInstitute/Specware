all: language-manual user-manual tutorial xform-manual isabelle-interface dbk2glm

#! /bin/bash

# Compile the converters between GLM and docbook:

glm2dbk: src/glm2dbk.c
	gcc src/glm2dbk.c -o bin/glm2dbk.o

# This one only used for sanity checking?:
dbk2glm:
	gcc src/dbk2glm.c -o bin/dbk2glm.o

language-manual: glm2dbk
	cd language-manual ; make

user-manual: glm2dbk
	cd user-manual ; make

tutorial: glm2dbk
	cd tutorial ; make

xform-manual: glm2dbk
	cd xform-manual ; make

isabelle-interface: glm2dbk
	cd isabelle-interface ; make

clean:
	rm -f bin/glm2dbk.o ; rm -f bin/dbk2glm.o ; cd language-manual ; make clean ; cd ../user-manual ; make clean ; cd ../xform-manual ; make clean ; cd ../tutorial ; make clean ; cd ../isabelle-interface ; make clean

