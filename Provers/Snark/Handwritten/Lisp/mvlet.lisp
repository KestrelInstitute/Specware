;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: mes-mvlet -*-
;;; File: mvlet.lisp
;;; Copyright (c) 1999 Mark E. Stickel
;;;
;;; Permission is hereby granted, free of charge, to any person obtaining a
;;; copy of this software and associated documentation files (the "Software"),
;;; to deal in the Software without restriction, including without limitation
;;; the rights to use, copy, modify, merge, publish, distribute, sublicense,
;;; and/or sell copies of the Software, and to permit persons to whom the
;;; Software is furnished to do so, subject to the following conditions:
;;;
;;; The above copyright notice and this permission notice shall be included
;;; in all copies or substantial portions of the Software.
;;;
;;; THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
;;; EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
;;; MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
;;; IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
;;; CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
;;; TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
;;; SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

(in-package :mes-mvlet)

;;; MVLET and MVLET* are extensions of LET and LET*
;;; that add to the list of binding forms
;;; the forms ((:values var1 var2 var*) [init-form])
;;;           ((:list   var1 var2 var*) [init-form])
;;;           ((:list*  var1 var2 var*) [init-form])
;;; that does multiple-value-binding and list destructuring
;;; extra values in init-form are ignored; missing ones are replaced by nil
;;; note that allowing fewer than two variables isn't really useful
;;;
;;; the troublesome part:
;;; declarations at the beginning of the body
;;; are decoded and placed in the proper locations
;;; in the expansion
;;;
;;; stickel@ai.sri.com 1999-08-09

(defmacro mvlet (bindings &body body)
  (mvlet-expansion bindings body nil))

(defmacro mvlet* (bindings &body body)
 (mvlet-expansion bindings body :none))

(defun binding-p (x)
  ;; var
  ;; (var [init-form])
  ;; ((:values var1 var2 var*) [init-form])
  ;; ((:list   var1 var2 var*) [init-form])
  ;; ((:list*  var1 var2 var*) [init-form])
  (or (symbolp x)
      (and (consp x)
           (listp (cdr x))
           (null (cddr x))
           (if (consp (car x))
               (case (caar x)
                 ((:values :list :list*)
                  (do ((l (cdar x) (cdr l))
                       (n 0 (1+ n)))
                      ((atom l)
                       (and (null l) (<= 2 n)))
                    (unless (symbolp (car l))
                      (return nil)))))
               (symbolp (car x))))))

(defun list-binding (vars form &optional list*)
  ;; for a quick implementation of :list and :list* binding forms,
  ;; replace ((:list   a b c d) form)
  ;;      by ((:values a b c d) (let ((v form)) (values (pop v) (pop v) (first v) (second v))))
  ;; replace ((:list*  a b c d) form)
  ;;      by ((:values a b c d) (let ((v form)) (values (pop v) (pop v) (first v) (rest v))))
  (do ((v (gensym))
       (l vars (rest l))
       (l2 nil (cons `(pop ,v) l2)))
      ((null (rest (rest l)))
       `((:values ,@vars) (let ((,v ,form))
                            (values ,@(reverse l2)
                                    (first ,v)
                                    ,(if list* `(rest ,v) `(second ,v))))))))

(defun mvlet-expansion (bindings body subst)
  (cond
   ((null bindings)
    `(let () ,@body))
   (t
    (dolist (b bindings)
      (unless (binding-p b)
        (error "~S is not a proper binding." b)))
    (multiple-value-bind (decl-specs body) (extract-declaration-specifiers body)
      (first (expand-mvlet bindings decl-specs body subst))))))

(defun expand-mvlet (bindings decl-specs body subst)
  (let (v)
    (cond
     ((null bindings)
      (let ((result body))
        (when decl-specs
          (setq result `((declare ,@decl-specs) ,@result)))
        (when (consp subst)
          (setq result `((let ,(reverse subst) ,@result))))
        result))

     ;; var or (var constant)
     ((or (symbolp (setq v (car bindings)))
          (and (symbolp (setq v (caar bindings)))
               (constantp (cadar bindings))))
      (let ((val (if (consp (car bindings)) (cadar bindings) nil)))
        (if (and (listp subst) (rest bindings))
            (expand-mvlet (rest bindings) decl-specs body (cons (list v val) subst))
            `((let ((,v ,val))
                ,@(expand-mvlet1 (rest bindings) decl-specs body subst v))))))

     ;; (var init-form)
     ((symbolp v)
      (when (and (listp subst) (rest bindings))
        (push (list v (setq v (make-symbol (symbol-name v)))) subst))
      `((let ((,v ,(cadar bindings)))
          ,@(expand-mvlet1 (rest bindings) decl-specs body subst v))))

     ;; ((:values var1 var2 var*) [init-form])
     ((eq :values (first (setq v (caar bindings))))
      (setq v (rest v))
      (when (and (listp subst) (rest bindings))
        (setq v (mapcar
                 #'(lambda (v1)
                     (push (list v1 (setq v1 (make-symbol (symbol-name v1)))) subst)
                     v1)
                 v)))
      `((multiple-value-bind ,v ,(cadar bindings)
          ,@(expand-mvlet1 (rest bindings) decl-specs body subst v))))

     ;; ((:list var1 var2 var*) [init-form])
     ;; ((:list* var1 var2 var*) [init-form])
     ((member (first v) '(:list :list*))
      (expand-mvlet
       (cons (list-binding (rest v) (cadar bindings) (eq :list* (first v)))
             (rest bindings))
       decl-specs
       body
       subst)))))

(defun expand-mvlet1 (bindings decl-specs body subst v)
  (multiple-value-bind (l1 l2) (filter-declaration-specifiers decl-specs v subst)
    (if (null l1)
        (expand-mvlet bindings l2 body subst)
        (cons `(declare ,@l1) (expand-mvlet bindings l2 body subst)))))

(defun type-symbol-p (x)
  ;; is X a symbol that names a type?
  (and (symbolp x)
       (handler-case
         (progn (typep nil x) t)	;is there a better way?
         (error () nil))))

(defun extract-declaration-specifiers (body)
  ;; returns declaration-specifiers of declarations at beginning of body
  ;; (declare (fixnum x y)) -> ((type fixnum x) (type fixnum y)) etc.
  ;; declaration-specifier syntax
  ;;   relevant to mvlet
  ;;     (dynamic-extent [[var* | (function fn)*]]) 
  ;;     (ignorable {var | (function fn)}*)  (1)
  ;;     (ignore    {var | (function fn)}*)
  ;;     (special var*)
  ;;     (type typespec var*)
  ;;     (a-symbol-which-is-the-name-of-a-type var*)
  ;;   irrelevant to mvlet?
  ;;     (declaration name*)
  ;;     (ftype type function-name*)
  ;;     (function ???)
  ;;     (inline    function-name*)
  ;;     (notinline function-name*)
  ;;     (optimize ???)
  ;;     (a-symbol-declared-to-be-a-declaration-identifier ???)
  ;; (1) fix CLHS glossary: add IGNORABLE to list of declaration identifiers
  (let ((decl-specs nil) form)
    (loop
      (cond
       ((and body (consp (setq form (first body))) (eq 'declare (first form)))
        (dolist (decl-spec (rest form))
          (let ((decl-id (first decl-spec)))
            (case decl-id
              ((dynamic-extent ignorable ignore special)
               (dolist (v (rest decl-spec))
                 (push `(,decl-id ,v) decl-specs)))
              (type
               (let ((type (second decl-spec)))
                 (dolist (v (rest (rest decl-spec)))
                   (push `(,decl-id ,type ,v) decl-specs))))
              (otherwise
               (if (type-symbol-p decl-id)
                   (dolist (v (rest decl-spec))
                     (push `(type ,decl-id ,v) decl-specs))
                   (push decl-spec decl-specs))))))
        (setq body (rest body)))
       (t
        (return (values (nreverse decl-specs) body)))))))

(defun filter-declaration-specifiers (decl-specs v subst)
  ;; returns (values l1 l2) where
  ;; l1 are declaration specifiers in decl-specs that concern
  ;; variable or variables v and
  ;; l2 are declaration specifiers in decl-specs that don't
  (if (null decl-specs)
      (values nil nil)
      (let ((d (first decl-specs))
            (r (rest decl-specs)))
        (multiple-value-bind (l1 l2) (filter-declaration-specifiers r v subst)
          (if (case (first d)
                ((dynamic-extent ignorable ignore special)
                 (if (consp v) (member (second d) v) (eq (second d) v)))
                (type
                 (if (consp v) (member (third d) v) (eq (third d) v))))
              (setq l1 (if (eq l1 r) decl-specs (cons d l1)))
              (setq l2 (if (eq l2 r) decl-specs (cons d l2))))
          ;; also add to l1 some declarations for temporary variables
          ;; that variable or variables v will be bound to
          (when (consp subst)
            (case (first d)
              (dynamic-extent
               (let ((x (second (assoc (second d) subst))))
                 (when (and x (if (consp v) (member x v) (eq x v)))
                   (push `(,(first d) ,x) l1))))
              (type
               (let ((x (second (assoc (third d) subst))))
                 (when (and x (if (consp v) (member x v) (eq x v)))
                   (push `(,(first d) ,(second d) ,x) l1))))))
          (values l1 l2)))))

(defun mvlet-test1 ()
  (let ((form '(mvlet* ((u (foo))
                        (v 13)
                        ((:values w x) (bar))
                        (y (baz)))
                (declare (fixnum v x) (special y w))
                (declare (dynamic-extent x))
                (list u v w x y)))
        (*print-pretty* t))
    (print (macroexpand-1 (print form)))
    (terpri)
    (print (macroexpand-1 (print (cons 'mvlet (rest form)))))
    nil))

(defun mvlet-test2 ()
  (let ((form '(mvlet (((:values a1 a2 a3) (foo))
                      ((:list   b1 b2 b3) (bar))
                      ((:list*  c1 c2 c3) (baz)))
                 (list a1 a2 a3 b1 b2 b3 c1 c2 c3)))
        (*print-pretty* t))
    (print (macroexpand-1 (print form)))
    nil))

#+(and mcl (not openmcl))
(progn
  (pushnew '(mvlet  . 1) ccl:*fred-special-indent-alist* :test #'equal)
  (pushnew '(mvlet* . 1) ccl:*fred-special-indent-alist* :test #'equal)
  nil)

;;; mvlet.lisp EOF
