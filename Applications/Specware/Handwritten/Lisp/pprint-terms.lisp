;;; Extends lisp prettyprinter to print out Metaslang term representations readably

(defpackage "METASLANG")
(in-package "METASLANG")

;(list-all-packages)
;(setq *print-pprint-dispatch* (copy-pprint-dispatch nil))

(defun print_term (strm term)
  (let ((*standard-output* strm))
    (AnnSpecPrinter::printTermToTerminal term)))

(defvar *print-constructors?* t)
(defvar *print-metaslang-terms?* t)
;(setq metaslang::*print-metaslang-terms?* nil)

(defun term_symbol? (s)
  (and *print-constructors?* *print-metaslang-terms?*
       (member s '(:|Apply| :|ApplyN| :|Record| :|Bind| :|Let| :|LetRec| :|Var|
		   :|Fun| :|Lambda| :|IfThenElse| :|Seq| ))))

(deftype term_symbol ()
  `(and symbol (satisfies term_symbol?)))

(set-pprint-dispatch '(cons term_symbol) 'print_term)

(defun print_sort (strm sort)
  (let ((*standard-output* strm))
    (if (and (consp sort))
	(AnnSpecPrinter::printSortToTerminal sort)
      (print_dotted_pair strm sort))))

(defun sort_symbol? (s)
  (and *print-constructors?* *print-metaslang-terms?*
       (member s '(:|Arrow| :|Product| :|CoProduct| :|Quotient| :|Subsort| :|Base|
		   :|TyVar|))))

(deftype sort_symbol ()
  `(and symbol (satisfies sort_symbol?)))

(set-pprint-dispatch '(cons sort_symbol) 'print_sort)


(defun print_dotted_pair (strm l)
  (format strm "~@:<~W ~_. ~W~:>" (car l) (cdr l)))
  
(set-pprint-dispatch '(cons T (and cons (satisfies
					  (lambda (x) (or (term_symbol? (car x))
							  (sort_symbol? (car x)))))))
		     'print_dotted_pair)
