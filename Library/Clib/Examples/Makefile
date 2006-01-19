# Example Makefile for compiling Accord-generated C code
# See ../README.CCodeGen for additional information.
# This file and the description is tailored for the GNU version of make.

# enable this line, if you want to disable the default garbage collector;
# this must precede the include statement below
#USEGC = no

# also preceding the include statement, you should put here the main
# target of the application, otherwise you have to use the target's
# name on the command line as in "make myapp", because the included
# file defines some rules not intended to be toplevel rules.
all: myapp

# mandatory; this includes the settings needed for the generated
# code to compile; it sets CPPFLAGS and LDLIBS variables
include $(ACCORD)/Sources/Library/Clib/Makerules

# optional: augment the CPPFLAGS
CPPFLAGS := -g $(CPPFLAGS)

# The following assumes that you have the Accord code generated into 
# files QuickSort.[ch]

# Variant 1:

# If you have defined a main operator in Accord (see
# ../README.CCodeGen) then you don't need to specify a rule for the
# main target, because make's implicit rules already take care of
# everything. For instance, if your MetaSlang code defines an (unqualified!)
# operator "main" like this:
#
#   op main: () -> ()
#   def main() = ...
#
# and you generate C code for the spec into files foo.[ch], then a simple
#
#   make foo
#
# should be enough to compile the generated code. In this case you might not
# even need to specify a separate Makefile, because the above included Makerules
# contains all the neccessary variable settings:
#
#   make -f $ACCORD/Sources/Library/Clib/Makerules foo
#
# would be sufficient in that case.



# Variant 2:
# file "main.c" contains the main program that calls the generated code
# no command needs to be supplied in this case, because there is an implicit
# rule that uses the variables defined in the includes Makerules file to build
# main from the file main.c and QuickSort.c. The dependency to $(GCLIB) is added
# to automatically compile the garbage collection library that come with the
# Accord distribution. For that, you must have write permission on the Accord
# distribution tree; otherwise omit the dependency to $(GCLIB) here.
main: QuickSort.o $(GCLIB)

# Variant 3:
# Explicitly call the linker for an application including generated C
# files.  This is the most general case and applicable in those cases,
# where the generated code has to be integrated in some other
# application
myapp: main.o QuickSort.o $(GCLIB)
	$(CC) -o $@ $^ $(LDLIBS)


# If, for instance for using certain optimizer flags, you have to
# supply an explicit rule for compiling a Accord generated C file,
# you have to make sure to include $(CPPFLAGS) on the command line.

queens.o: queens.c queens.h
	$(CC) -O3 $(CPPFLAGS) -o $@ -c $< 

queens: queens.o $(GCLIB)
