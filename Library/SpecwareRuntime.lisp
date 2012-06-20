(defpackage :Specware (:use :cl))
(in-package :Specware)

(unless (boundp '*fasl-type*)
  (defvar *fasl-type*
      #+allegro "fasl"
      #+mcl     "dfsl"
      #+cmu     "x86f"
      #+sbcl    sb-fasl:*fasl-file-type*))

(unless (fboundp 'Specware::getenv)
  (defun Specware::getenv (varname)	; duplicate of definition in load-utilities.lisp
    #+allegro   (system::getenv varname)
    #+mcl       (ccl::getenv varname)
    #+lispworks (hcl::getenv varname)	;?
    #+cmu       (cdr (assoc (intern varname "KEYWORD") ext:*environment-list*))
    #+sbcl      (let ((x (find-symbol "*ENVIRONMENT-SHADOW*")))
                  (or (and x
                           (cdr (assoc (intern varname "KEYWORD") (symbol-value x))))
                      (sb-ext:posix-getenv  varname)))
    #+gcl       (si:getenv varname)
    #+clisp     (ext:getenv varname)
    ))

(defvar *specware4* 
  #-windows (getenv "SPECWARE4")
  #+windows (substitute #\/ #\\ (convert-pathname-from-cygwin (getenv "SPECWARE4"))))

#+sbcl (require "SBCL_PATCH" (format nil "~a/Applications/Handwritten/Lisp/sbcl-patch" *specware4*))

(unless (fboundp 'compile-file-if-needed)
  ;; Conditional because of an app/usr/lib/sbcl/arent Allegro bug in generate-application
  ;; where excl::compile-file-if-needed compiles even if not needed
  (defun compile-file-if-needed (file)
    #+allegro (excl::compile-file-if-needed file)
    #+Lispworks (hcl:compile-file-if-needed file)
    #+(or cmu mcl sbcl)
    (let* ((file-date (if (probe-file file) (file-write-date file) 0))
           (fasl-type (symbol-value (find-symbol "*FASL-TYPE*" "SPECWARE")))
           (fasl-file (make-pathname :defaults file :type fasl-type))
           (fasl-date (if (probe-file fasl-file) (file-write-date file) 0)))
      (when (> file-date fasl-date)
        (compile-file file)))))

(unless (fboundp 'compile-and-load-lisp-file)
  (defun compile-and-load-lisp-file (file)
    (let ((filep (make-pathname :defaults file :type "lisp")))
      (compile-file-if-needed filep)
      (load (make-pathname :defaults filep :type nil)))))


(loop for fil in '("Base/Handwritten/Lisp/meta-slang-runtime" ; equality, etc.
		   "Base/Handwritten/Lisp/Integer"
		   ;"Base/Handwritten/Lisp/Nat"
		   "Base/Handwritten/Lisp/Character"
		   "Base/Handwritten/Lisp/String"
		   "Legacy/Utilities/Handwritten/Lisp/System"
		   "IO/Primitive/Handwritten/Lisp/IO"
		   "Legacy/Utilities/Handwritten/Lisp/State"
		   "Legacy/Utilities/Handwritten/Lisp/IO"
		   "Legacy/Utilities/Handwritten/Lisp/Lisp"
		   "Structures/Data/Monad/Handwritten/Lisp/State"
                   "Algorithms/Handwritten/Lisp/Thread")
  do (compile-and-load-lisp-file (format nil "~a/Library/~a" *specware4* fil)))

(provide "SpecwareRuntime")
