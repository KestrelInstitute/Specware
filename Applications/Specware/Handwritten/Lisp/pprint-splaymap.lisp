;;; Extends lisp prettyprinter to print out Metaslang splaymaps representations readably

(defpackage :MetaSlang)
(in-package :MetaSlang)

;(list-all-packages)
;(setq *print-pprint-dispatch* (copy-pprint-dispatch nil))

(defun print_splay_map (strm m)
  (let ((*standard-output* strm))
    (format strm "Map: ~a" (SplayMap::tolist m))))

(defvar *print-constructors?* t)
(defvar *print-splay-maps?* t)
;(setq MetaSlang::*print-splay-maps?* nil)

(defun splay_map_symbol? (s)
  (and *print-constructors?* *print-splay-maps?* (member s '(:|MAP|))))

(deftype splay_map_symbol ()
  `(and symbol (satisfies splay_map_symbol?)))

(set-pprint-dispatch '(cons splay_map_symbol) #'print_splay_map)


(defun print_dotted_pair (strm l)
  (format strm "~@:<~W ~_. ~W~:>" (car l) (cdr l)))
  
;;;(set-pprint-dispatch '(cons T (and cons (satisfies
;;;					  (lambda (x) (splay_map_symbol? (car x))))))
;;;		     'print_dotted_pair)

(defun print_splay_set (strm m)
  (let ((*standard-output* strm))
    (format strm "Set: ~a" (SplaySet::listItems m))))


(defun splay_set_symbol? (s)
  (and *print-constructors?* *print-splay-maps?* (member s '(:|SET|))))

(deftype splay_set_symbol ()
  `(and symbol (satisfies splay_set_symbol?)))

(set-pprint-dispatch '(cons splay_set_symbol) #'print_splay_set)

(set-pprint-dispatch '(cons T (and cons (satisfies
					  (lambda (x) (or (splay_set_symbol? (car x))
							  (splay_map_symbol? (car x)))))))
		     #'print_dotted_pair)

(defun print_dotted_triple (strm l)
  (format strm "~@:<~W ~W ~_. ~W~:>" (car l) (cadr l)(cddr l)))

(set-pprint-dispatch '(cons T (cons T (and cons
				       (satisfies
					(lambda (x) (or (splay_set_symbol? (car x))
							(splay_map_symbol? (car x))))))))
		     #'print_dotted_triple)