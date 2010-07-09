(defpackage :Specware)
(in-package :Specware)
;(in-package :cl-user) -- *specware4*, *fasl-type*, etc. are in Specware package!

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
    #+sbcl      (or (cdr (assoc (intern varname "KEYWORD") *environment-shadow*))
		    (sb-ext:posix-getenv  varname))
    #+gcl       (si:getenv varname)
    #+clisp     (ext:getenv varname)
    ))

(defvar *specware4* (substitute #\/ #\\ (convert-pathname-from-cygwin (getenv "SPECWARE4"))))

(unless (fboundp 'compile-file-if-needed)
  ;; Conditional because of an app/usr/lib/sbcl/arent Allegro bug in generate-application
  ;; where excl::compile-file-if-needed compiles even if not needed
  (defun compile-file-if-needed (file)
    #+allegro (excl::compile-file-if-needed file)
    #+Lispworks (hcl:compile-file-if-needed file)
    #+(or cmu mcl sbcl)
    (when (> (file-write-date file)
	     (or (file-write-date (make-pathname :defaults file
						 :type *fasl-type*))
		 0)) 
      (compile-file file))))

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
