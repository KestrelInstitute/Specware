
(in-package "PARSER4")

(defvar *lhs-latex*) ; used only for debugging messages

(defparameter *MAX-BNF-WIDTH* 40)

#+allegro				; Fix for other dialects later
(defun cl-user::show-grammar (&optional just-rerun-latex?)
  (let ((parser-ps-file (print-grammar-ps-file just-rerun-latex?)))
    (format t "~&~%--------------------------------------------------------------------------------~%")
    (format t "~&Type QUIT to exit from gs ~2%")
    (let* ((ps-viewer (get-ps-viewer))
	   (cmd (format nil "~A ~A" ps-viewer parser-ps-file)))
      (excl::run-shell-command cmd :wait t)
      (format t "~&~%You might want to run ~A manually from a shell...~%" ps-viewer)
      (format t "~&~A~%" cmd)
      (values))))

#+allegro				; Fix for other dialects later
(defun get-ps-viewer ()
  (dolist (program '("ghostview" "gs")
	    (progn
	      (warn "Could not find a viewer for postscript! -- Defaulting to (non-existant?) ghostview.")
	      "ghostview"))
    (when (equal (excl::shell (format nil "which ~A > /dev/null" program)) 0)
      (return program))))

;; The following is called from Languages/SpecCalculus/Parser/Handwritten/Lisp/system.lisp
;; to print a postscript version of the bnf for the grammar each time the system is built.
#+allegro				; Fix for other dialects later
(defun print-grammar-ps-file (&optional just-rerun-latex?)
  (let* ((parser-lisp-dir (specware::current-directory))
	 (parser-tex-dir  (make-pathname :directory (append (reverse (cdr (reverse (pathname-directory parser-lisp-dir))))
							    '("TeX"))))
	 (*default-pathname-defaults* parser-tex-dir)
	 (tex-file (make-pathname :name "metaslang.tex" :defaults parser-tex-dir)) ; metaslang.tex is the name expected by parser-main.tex
	 (ps-file  (make-pathname :name "grammar.ps"    :defaults parser-tex-dir))
	 (log-file (make-pathname :name "latex.log"     :defaults parser-tex-dir))
	 )
    (unless just-rerun-latex?
      (when (probe-file tex-file)
	(let ((old-tex-file (make-pathname :name "old-metaslang.tex" :defaults parser-tex-dir)))
	  ; (format t "~&;;; Renaming ~A~&;;;       to ~A~%" tex-file old-tex-file)
	  (rename-file tex-file old-tex-file)))
      (when (probe-file ps-file)
	(let ((old-ps-file  (make-pathname :name "old-grammar.ps"    :defaults parser-tex-dir)))
	  ; (format t "~&;;; Renaming ~A~&;;;       to ~A~%" ps-file old-ps-file)
	  (rename-file ps-file old-ps-file)))
      (write-bnf-in-latex-for-grammar tex-file))
    (when (probe-file log-file)
      (delete-file log-file))
    (let ((cmd (format nil "cd ~A ; latex parser-main.tex > latex.log ; dvips -q -f parser-main.dvi > grammar.ps"
		       parser-tex-dir)))
      (excl::run-shell-command cmd :wait t))
    (format t "~&;     See ~Agrammar.ps~%" parser-tex-dir)
    (make-pathname :name "grammar" :type "ps" :defaults parser-tex-dir)))

(defun write-bnf-in-latex-for-grammar (latex-file-or-stream &optional (parser *current-parser*)) 
  (if (not (streamp latex-file-or-stream))
      (with-open-file (ss latex-file-or-stream :direction :output :if-exists :supersede)
	(write-bnf-in-latex-for-grammar ss parser))
    (let ((latex-stream latex-file-or-stream)) 
      (multiple-value-bind (reversed-bnf-expressions atomic-rules)
	  (bnf-for-parser-main-rules (parser-toplevel-rule parser) 
				     parser
				     nil
				     nil)
	#-DEBUG-PARSER (declare (ignore atomic-rules))
        #+DEBUG-PARSER (format t "~&ATOMIC RULES: ~S" atomic-rules)
	(format latex-stream "~&~%")
	(format latex-stream "~&\\newcommand{\\bnf}[1]           {{#1}}~%")
	(format latex-stream "~&\\newcommand{\\bnfoptionalopen}  {{\\bnf{$\\big[$}    }}~%")
	(format latex-stream "~&\\newcommand{\\bnfoptionalclose} {{\\bnf{$\\big]$}    }}~%")
	(format latex-stream "~&\\newcommand{\\bnfrepeatopen}    {{\\bnf{$\\big\\{$}   }}~%")
	(format latex-stream "~&\\newcommand{\\bnfrepeatclose}   {{\\bnf{$\\big\\}^*$} }}~%")
	(format latex-stream "~&\\newcommand{\\bnfalternative}   {{\\bnf{$|$}       }}~%")
	(format latex-stream "~&~%")
	(format latex-stream "~&\\newcommand{\\grnonterminal}[1] {{\\textup{\\textsc {#1}} }}~%")
	(format latex-stream "~&~%")
	(format latex-stream "~&\\newcommand{\\grterminal}[1]    {{\\underline {\\textup {\\texttt {#1}}} }}~%")
	(format latex-stream "~&~%")
	(format latex-stream "~&\\newcommand{\\grcomment}[1]    {{\\textit {\\textrm {#1}}}}~%")
	(format latex-stream "~&~%")
	(format latex-stream "~&{\\em~%\\begin{tabbing}~%")
	(let* ((bnf-expressions (nreverse reversed-bnf-expressions))
	       (max-name-char-length 0))
	  (dolist (x bnf-expressions)
	    (setq max-name-char-length (max max-name-char-length
					    (length (symbol-name (car x))))))
	  (format latex-stream "~&~A \\= $::=$\\=  \\ \\ \\ \\= ~A \\= \\kill"
		  (make-string max-name-char-length :initial-element #\A)
		  (make-string 37 :initial-element #\A))
	  (dolist (bnf-expression bnf-expressions)
	    (let* ((lhs-latex (latex-for-bnf (car bnf-expression)))
		   (rhs-latex 
		    (let ((*lhs-latex* lhs-latex))  ; *lhs-latex* is used only for debugging messages
		      (latex-for-bnf (cdr bnf-expression)))))
	      (format latex-stream "~&\\\\~%\\\\ ~A \\> $::=$ \\> \\> ~A~%"
		      lhs-latex
		      rhs-latex)
	      )))
	(format latex-stream "~&\\end{tabbing}~%}~%")))))

(defun bnf-width (bnf &optional examine-just-head-of-repeats?)
  (cond ((null bnf) 0)
	((symbolp bnf) (length (symbol-name bnf)))
	((stringp bnf) (* (float 5/7) ; font for keywords is smaller, so approximate the difference
			  (length bnf)))
	(t
	 (let ((key   (car bnf))
	       (items (cdr bnf)))
	   (case key
	     (parser-tuple-rule
	      (let ((count -1))
		(dolist (item items)
		  (incf count 
			(+ (length " ")
			   (bnf-width item)
			   (length "")
			   )))
		count))
	     (parser-anyof-rule
	      (let ((count 0))
		(dolist (item items)
		  ;; if we were at top level, but we break those anyway...
		  ;; (setq count (max count (bnf-width item))))
		 (incf count (bnf-width item)))
		count)
	      )
	     (parser-repeat-rule
	      (let ((elt-length (bnf-width (first items))))
		(cond ((null (second items))
		       (+ (length "{ ") elt-length (length "}* ")))
		      (examine-just-head-of-repeats? 
		       elt-length)
		      (t
		       (+ elt-length 
			  (length " { ") 
			  (bnf-width (second items))
			  (length " ") 
			  elt-length 
			  (length "}* "))))))
	     (:optional 
	      (+ (length "[ ")
		 (bnf-width (first items))
		 (length "] ")
		 ))
	     (:doc 
	      (bnf-width (first items))
	      ))))))

(defun latex-for-bnf (bnf &optional (indent 0))
  (cond ((symbolp bnf)
	 (format nil "\\grnonterminal {~A}" 
		 ;; string-upcase, string-downcase, string-capitalize
		 (sanitize-string-for-latex (symbol-name bnf))))
	((stringp bnf)
	 (format nil "\\grterminal {~A}" 
		 (sanitize-string-for-latex bnf)))
	(t
	 (let* ((width (bnf-width bnf))
		(break? (> (+ width indent ) *max-bnf-width*))
		(key   (car bnf))
		(items (cdr bnf)))
	   #+DEBUG-PARSER (when break? (format t "~&Count: ~3S for ~30S ~%" (round (+ 211 (* 7 width))) *lhs-latex*))
	   (case key
	     (parser-tuple-rule 
	      (if break?
		  (let* ((latex "")
			 (width indent)
			 (indent (+ indent
				    (if (stringp (first items)) 
					(+ 4 (length (first items)))
				      0)))
			 (xx nil)
			 (saw-optional-or-repeat? nil))
		    (do ((items items (rest  items)))
			((null items) latex)
		      (let ((item (first items)))
			(incf width (+ 2 (bnf-width item t)))
			(unless (member item '("}" ">" "]" ")") :test 'equalp)
			  (when (or saw-optional-or-repeat?
				    (> width *max-bnf-width*)
				    (and (not (equal latex "")) 
					 (stringp item)
					 (> (+ width (bnf-width (first (rest items)) t)) *max-bnf-width*)
					 ))
			    (let ((filler (let ((spaces ""))
					   (dotimes (i (if (and (stringp item) (> (length item) 1))
							   (max 0 (- indent (+ 4 (length item))))
							 indent)
						      spaces)
					     (setq spaces (concatenate 'string spaces "\\ "))))))
			      (setq latex (concatenate 'string 
					    latex 
					    (format nil "~&\\\\  \\>  \\>  \\>~A" filler))))
			    (setq width indent)))
			(multiple-value-setq (xx saw-optional-or-repeat?)
			  (latex-for-bnf item indent))
			(setq latex (concatenate 'string latex "  " xx)))))
		(format nil "  ~{ ~A~^\\ ~}" 
			(mapcar #'(lambda (x) (latex-for-bnf x)) 
				items))))
	     (parser-anyof-rule 
	      (format nil "  ~A~{ ~&\\\\  \\>  \\>   \\bnfalternative \\>  ~A~}" 
		      (latex-for-bnf (first items))
		      (mapcar #'(lambda (x) (latex-for-bnf x)) 
			      (rest items))))
	     (parser-repeat-rule 
	      (values
	       (let ((x1 (latex-for-bnf (first items))))
		 (if (null (second items))
		     (format nil "\\bnfrepeatopen  ~A \\bnfrepeatclose" x1)
		   (let ((x2 (latex-for-bnf (second items))))
		     (if break?
			 (let ((filler (let ((spaces ""))
					 (dotimes (i (1- indent) spaces)
					   (setq spaces (concatenate 'string spaces "\\ "))))))
			   (format nil "~A ~&\\\\  \\>  \\>  \\> ~A \\bnfrepeatopen ~A ~A \\bnfrepeatclose" x1 filler x2 x1))
		       (format nil "~A \\bnfrepeatopen ~A ~A \\bnfrepeatclose" x1 x2 x1)))))
	       t))
	     (:optional 
	      (values 
	       (format nil "\\bnfoptionalopen ~A \\bnfoptionalclose" (latex-for-bnf (first items))) 
	       t))
	     (:doc      
	      (format nil "~A \\> \\grcomment{~A}" 
		      (latex-for-bnf (first items))
		      (second items)))
	     (t (format nil "?? ~A ??" key)))))))

(defun sanitize-string-for-latex (str)
  (let ((raw-chars (coerce str 'list))
	(new-chars nil)
	(tex-char-command (coerce "\\char" 'list)))
    (dolist (char raw-chars)
      ;; see "A Guide to Latex2e" , 2nd ed.,  page 21
      (cond ((alpha-char-p char) (push char new-chars))
	    ((digit-char-p char) (push char new-chars))
	    ((member char '(#\# #\$ #\_ #\% #\{ #\})) ; #\^ #\~
	     (push #\\ new-chars)
	     (push char new-chars))
	    (t
	     (dolist (cc tex-char-command)
	       (push cc new-chars))
	     (dolist (cc (coerce (format nil "~D" (char-code char)) 
				 'list))
	       (push cc new-chars)))))
    (coerce (nreverse new-chars) 'string)))

(defun bnf-for-parser-main-rules (main-rule 
				  parser 
				  main-expressions 
				  atomic-rules)
  (let ((sub-expressions nil)
	(main-sub-rules  nil))
    (do-parser-rule-items (item main-rule)
      (unless (null item)
	(let* ((sub-rule-name (parser-rule-item-rule item))
	       (sub-rule      (find-parser-rule parser sub-rule-name)))
	  (let ((form
		 (cond ((parser-rule-main-rule? sub-rule) 
			(pushnew sub-rule main-sub-rules)
			(parser-rule-name sub-rule))
		       (t
			(multiple-value-bind (bnf sub-rules)
			    (bnf-for-parser-sub-rule sub-rule parser nil)
			  (dolist (sub-rule sub-rules)
			    (pushnew sub-rule main-sub-rules))
			  bnf)))))
	    (push (if (parser-rule-item-optional? item)
		      (list :OPTIONAL form)
		    form)
		  sub-expressions)))))
    (if (parser-atomic-rule-p main-rule)
	(pushnew main-rule atomic-rules)
      (push (cond ((and (or (parser-tuple-rule-p main-rule)
			    (parser-anyof-rule-p main-rule))
			(null (rest sub-expressions)))
		   (if (symbolp (first sub-expressions))
		       `(,(parser-rule-name main-rule) 
			 parser-tuple-rule 
			 ,@(nreverse sub-expressions))
		     `(,(parser-rule-name main-rule) 
		       ,@(first sub-expressions))))
		  (t
		   `(,(parser-rule-name main-rule) 
		     ,(type-of main-rule) 
		     ,@(nreverse sub-expressions))))
	    main-expressions))
    (dolist (main-sub-rule (nreverse main-sub-rules))
      (unless (assoc (parser-rule-name main-sub-rule) main-expressions)
	(multiple-value-setq (main-expressions atomic-rules)
	  (bnf-for-parser-main-rules main-sub-rule 
				     parser 
				     main-expressions
				     atomic-rules))))
    (values main-expressions atomic-rules)))
      
(defun bnf-for-parser-sub-rule (main-rule parser main-sub-rules)
  (let ((sub-expressions nil))
    (do-parser-rule-items (item main-rule)
      (unless (null item)
	(let* ((sub-rule-name (parser-rule-item-rule item))
	       (sub-rule      (find-parser-rule parser sub-rule-name)))
	  (let ((form
		 (cond ((parser-rule-main-rule? sub-rule) 
			(pushnew sub-rule main-sub-rules)
			(parser-rule-name sub-rule))
		       (t
			(multiple-value-bind (bnf sub-rules)
			    (bnf-for-parser-sub-rule sub-rule 
						     parser 
						     main-sub-rules)
			  (dolist (sub-rule sub-rules)
			    (pushnew sub-rule main-sub-rules))
			  bnf)))))
	    (push (if (parser-rule-item-optional? item)
		      (list :OPTIONAL form)
		    form)
		  sub-expressions)))))
    (let ((xx
	   (cond ((parser-keyword-rule-p main-rule)
		  (parser-keyword-rule-keyword main-rule))
		 ((and (parser-tuple-rule-p main-rule)
		       (null (rest sub-expressions)))
		  (first sub-expressions))
		 (t
		  `(,(type-of main-rule) ,@(nreverse sub-expressions))))))
      (let ((doc (parser-rule-documentation main-rule)))
	(if (null doc)
	    (values xx main-sub-rules)
	  (values `(:doc ,xx ,doc) main-sub-rules))))))
      

;;; informative messages for person building parser....

#+allegro				; Fix for other dialects later
(eval-when (load)
  (format t "~&;     To create grammar.ps and display using ghostview or gs: (cl-user::show-grammar)~%"))


