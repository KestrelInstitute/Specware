;;; Extends lisp prettyprinter to print out Metaslang term representations readably

(defpackage :MetaSlang)
(in-package :MetaSlang)

;(list-all-packages)
;(setq *print-pprint-dispatch* (copy-pprint-dispatch nil))

;;; Terms

(defun print_term (strm term)
  (let ((*standard-output* strm)
	(AnnSpecPrinter::useXSymbols? nil))
    (declare (special AnnSpecPrinter::useXSymbols?))
    (AnnSpecPrinter::printTermToTerminal term)))

(defvar *print-constructors?* t)
(defvar *print-metaslang-terms?* t)
;(setq metaslang::*print-metaslang-terms?* nil)

(defun term_symbol? (s)
  (and *print-constructors?* *print-metaslang-terms?*
       (member s '(:|Apply| :|ApplyN| :|Record| :|Bind| :|Let| :|LetRec| :|Var|
		   :|Fun| :|Lambda| :|IfThenElse| :|Seq| :|TypedTerm|))))

(deftype term_symbol ()
  `(and symbol (satisfies term_symbol?)))

(set-pprint-dispatch '(cons term_symbol) #'print_term)

;;; Types

(defun print_type (strm type)
  (let ((*standard-output* strm))
    (if (and (consp type))
	(AnnSpecPrinter::printTypeToTerminal type)
      (print_dotted_pair strm type))))

(defun type_symbol? (s)
  (and *print-constructors?* *print-metaslang-terms?*
       (member s '(:|Arrow| :|Product| :|CoProduct| :|Quotient| :|Subtype| :|Base|
		   :|TyVar|))))

(deftype type_symbol ()
  `(and symbol (satisfies type_symbol?)))

(set-pprint-dispatch '(cons type_symbol) #'print_type)


;;; Elements

(defun print_element (strm el)
  (let ((*standard-output* strm))
    (if (and (consp el))
	(princ (AnnSpec::showQ el))
      (print_dotted_pair strm el))))

(defun element_symbol? (s)
  (and *print-constructors?*
       (member s '(:|Import| :|Type| :|TypeDef| :|Op| :|OpDef| :|Property| :|Comment|
		   :|Pragma|))))

(deftype element_symbol ()
  `(and symbol (satisfies element_symbol?)))

(set-pprint-dispatch '(cons element_symbol) #'print_element)

;;; Dotted pairs

(defun print_dotted_pair (strm l)
  (format strm "~@:<~W ~_. ~W~:>" (car l) (cdr l)))

(defun type_or_term? (x)
  (or (term_symbol? (car x))
      (type_symbol? (car x))
      (element_symbol? (car x))))

(set-pprint-dispatch '(cons T (and cons (satisfies type_or_term?)))
		     #'print_dotted_pair)
