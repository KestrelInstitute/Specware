(test-directories ".")

(test 

 ("Bug 0025 : Problem with code generation / libraries failing ot include all the defun's needed in .lisp [gen lisp]"
  :swl "S"
  :output '(";;; Elaborating spec at $TESTDIR/S"
	    ";;; Generating lisp file $TESTDIR/lisp/S.lisp"
	    (:optional
	     ";; ensure-directories-exist: creating $TESTDIR/lisp/S.lisp")
	    (:optional
	     ";; Directory $TESTDIR/lisp/ does not exist, will create.")
	    ""))

 ("Bug 0025 : Problem with code generation / libraries failing ot include all the defun's needed in .lisp [test lisp]"
  :lisp "(progn 
            (let ((first-form (with-open-file (s \"lisp/S.lisp\") (read s))))
              (print (list (equalp (car first-form) 'require)
                           (equalp (cadr first-form) \"SpecwareRuntime\")))
              (load \"lisp/S.lisp\") 
              (print (sw-user::foo-2 \"abc\" \"def\"))))"
  :output '(""
	    "(T T) "
	    (:optional
	     "Warning: BOOLEAN-SPE:COMPARE-2, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: BOOLEAN-SPE:COMPARE, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: BOOLEAN-SPE:SHOW, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: INTEGER-SPE:>-2, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: INTEGER-SPE:COMPARE-2, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: CHAR-SPE:COMPARE-2, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: CHAR-SPE:COMPARE, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: CHAR-SPE:SHOW, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: COMPARE::COMPARE-2, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: COMPARE::COMPARE, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: COMPARE::SHOW, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: FUNCTIONS::ID, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: FUNCTIONS::O-1-1, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: FUNCTIONS::O, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: FUNCTIONS::O-2, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: INTEGER-SPE:>=-2, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: INTEGER-SPE:COMPARE, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: LIST-SPE:HD, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: LIST-SPE:TL, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: INTEGER-SPE:INTCONVERTIBLE, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: INTEGER-SPE:MAX-2, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: INTEGER-SPE:MIN-2, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: INTEGER-SPE:PRED, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: INTEGER-SPE:SHOW, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: INTEGER-SPE:!>=, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: INTEGER-SPE:!>, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: INTEGER-SPE:|!abs|, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: INTEGER-SPE:|!max|, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: INTEGER-SPE:|!min|, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: LIST-SPE:CONCAT-2, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: LIST-SPE:++-2, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: LIST-SPE:ALL-1-1, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: LIST-SPE:ALL, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: LIST-SPE:APP-1-1, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: LIST-SPE:APP, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: LIST-SPE:COMPARE-1-1, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: LIST-SPE:COMPARE, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: LIST-SPE:CONCAT, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: LIST-SPE:CONS-2, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: LIST-SPE:MEMBER-2, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: LIST-SPE:DIFF-2, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: LIST-SPE:DIFF, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: LIST-SPE:EXISTS-1-1, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: LIST-SPE:FILTER-1-1, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: LIST-SPE:FILTER, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: LIST-SPE:FIND-1-1, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: LIST-SPE:FIRSTUPTO-1-1, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: LIST-SPE:FIRSTUPTO, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: LIST-SPE:FLATTEN, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: LIST-SPE:FOLDL-1-1-1, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: LIST-SPE:FOLDL, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: LIST-SPE:FOLDR-1-1-1, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: LIST-SPE:FOLDR, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: LIST-SPE:INSERT-2, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: LIST-SPE:INSERT, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: LIST-SPE:LOCATIONOF-2, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: LIST-SPE:LOCATIONOF, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: LIST-SPE:MAP-1-1, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: LIST-SPE:MAPPARTIAL-1-1, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: LIST-SPE:MAPPARTIAL, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: LIST-SPE:NTH-2, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: LIST-SPE:NTHTAIL-2, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: LIST-SPE:NTHTAIL, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: LIST-SPE:REV2-2, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: LIST-SPE:REV, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: LIST-SPE:REV2, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: LIST-SPE:SHOW-1-1, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: LIST-SPE:SHOW, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: LIST-SPE:SPLITLIST-1-1, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: LIST-SPE:SPLITLIST, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: LIST-SPE:SUBLIST-3, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: LIST-SPE:SUBLIST, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: LIST-SPE:TABULATE-2, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: LIST-SPE:TABULATE, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: LIST-SPE:!++, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: LIST-SPE:|!butLast|, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: LIST-SPE:|!cons|, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: LIST-SPE:|!exists|, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: LIST-SPE:|!find|, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: LIST-SPE:|!last|, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: LIST-SPE:|!length|, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: LIST-SPE:|!map|, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: LIST-SPE:|!member|, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: LIST-SPE:|!nil|, :VARIABLE was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: LIST-SPE:|!nth|, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: LIST-SPE:|!null|, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: NAT-SPE:NATCONVERTIBLE, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: NAT-SPE:ONE, :VARIABLE was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: NAT-SPE:POSNAT?, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: NAT-SPE:SHOW, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: NAT-SPE:TWO, :VARIABLE was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: OPTION::COMPARE-1-1, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: OPTION::COMPARE, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: OPTION::MAPOPTION-1-1, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: OPTION::MAPOPTION, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: OPTION::NONE, :VARIABLE was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: OPTION::NONE?, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: OPTION::SHOW-1-1, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: OPTION::SHOW, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: OPTION::SOME?, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: OPTION::|!some|, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: STRING-SPE:>-2, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: STRING-SPE:>=-2, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: STRING-SPE:COMPARE-2, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: STRING-SPE:COMPARE, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: STRING-SPE:!>=, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    (:optional
	     "Warning: STRING-SPE:!>, :OPERATOR was defined in $SPECWARE/Applications/Specware/lisp/Specware4.lisp and is now being defined in"
	     "         $TESTDIR/lisp/S.lisp")
	    ""
	    "T ")
  )
 )
