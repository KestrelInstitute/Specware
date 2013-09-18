
SPECWARE4=`dirname $0`

#Applications/Specware/bin/linux/Specware4.sbclexe:
bootstrap:
	SPECWARE4=${SPECWARE4} Applications/Specware/bin/linux/bootstrap

clean:
	rm -f Applications/Specware/lisp/*.lisp
	find . -name \*.sfsl -print | xargs rm -f

realclean: clean
	rm Applications/Specware/bin/linux/Specware4.sbclexe
