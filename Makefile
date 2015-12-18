
#Applications/Specware/bin/unix/Specware4.sbclexe:
bootstrap:
	bin/bootstrap

clean:
	rm -f Applications/Specware/lisp/*.lisp
	find . -name \*.sfsl -print | xargs rm -f

realclean: clean
	rm -f Applications/Specware/bin/unix/Specware4.sbclexe
