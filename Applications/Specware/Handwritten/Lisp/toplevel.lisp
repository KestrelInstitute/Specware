(in-package :cl-user)
(defpackage :SpecCalc)

;; Toplevel Lisp aliases for Specware

;; The lisp code supporting the saving/restoring of the Specware state
;; to/from the lisp environment can be found in specware-state.lisp.
;; The latter must be loaded before this and the generated lisp code for
;; Specware.

(defvar *last-uri-loaded* nil)
(defvar *last-swl-args* nil)
(defvar *last-swj-args* nil)

(defun sw0 (x)
   (Specware::runSpecwareURI x)
   (values))
#+allegro(top-level:alias ("sw0" :case-sensitive) (x) (sw0 (string x)))

(defun sw-re-init ()
   (setq *specware-global-context* nil)
   (values))
(defun sw-init ()
   (sw-re-init))
#+allegro(top-level:alias "sw-init" () (sw-re-init))

(defun list-loaded-units ()
   (Specware::listLoadedUnits))
#+allegro(top-level:alias ("list" :case-sensitive) () (list-loaded-units))

(defun sw (x)
   (Specware::evaluateURI_fromLisp x)
   ;; (values) ; breaks bootstrap!  why suppress result?
   )

#+allegro
(top-level:alias ("sw" :case-sensitive) (&optional x)
  (if x
    (sw (setq *last-uri-loaded* (string x)))
    (if *last-uri-loaded*
      (sw *last-uri-loaded*)
      (format t "No previous unit evaluated~%"))))

(defun show (x)
   (Specware::evaluatePrint_fromLisp x)
   (values))
#+allegro
(top-level:alias ("show" :case-sensitive) (&optional x)
  (if x
    (show (setq *last-uri-loaded* (string x)))
    (if *last-uri-loaded*
      (show *last-uri-loaded*)
      (format t "No previous unit evaluated~%"))))

;; Not sure if an optional URI make sense for swl
(defun swl (x &optional y)
   (Specware::evaluateLispCompile_fromLisp x
                         (if y (cons :|Some| y)
                               '(:|None|)))
   (values))
#+allegro
(top-level:alias ("swl" :case-sensitive) (&optional &rest args)
   (let ((r-args (if (not (null args))
		     args
		   *last-swl-args*)))
   (if r-args
       (progn (setq *last-swl-args* args)
	      (funcall 'swl (string (first r-args))
		       (if (not (null (second r-args)))
			   (string (second r-args)) nil)))
     (format t "No previous unit evaluated~%"))))

;; Not sure if an optional URI make sense for swj
(defun swj (x &optional y)
   (Specware::evaluateJavaGen_fromLisp x
                         (if y (cons :|Some| y)
                               '(:|None|)))
   (values))
#+allegro
(top-level:alias ("swj" :case-sensitive) (&optional &rest args)
   (let ((r-args (if (not (null args))
		     args
		   *last-swj-args*)))
   (if r-args
       (progn (setq *last-swj-args* args)
	      (funcall 'swj (string (first r-args))
		       (if (not (null (second r-args)))
			   (string (second r-args)) nil)))
     (format t "No previous unit evaluated~%"))))

#+allegro
(top-level:alias ("wiz" :case-sensitive) (&optional (b nil b?))
   (if b? (princ (setq SpecCalc::specwareWizard? b))
          (princ SpecCalc::specwareWizard?)))

;; When the following boolean is true, then the System.debug function will
;; take the user into the Lisp debugger.
(defvar System-spec::specwareDebug? nil)
(defun swdbg (&optional (b nil b?))
  (if b? (princ (setq System-spec::specwareDebug?
		      (and b (not (equal b "nil")))))
    (princ System-spec::specwareDebug?))
  (values))

#+allegro
(top-level:alias ("swdbg" :case-sensitive) (&optional (b nil b?))
   (if b? (princ (setq System-spec::specwareDebug? b))
          (princ System-spec::specwareDebug?)))

(defun swpath  (&optional str)
  (if (or (null str) (equal str ""))
      (princ (specware::getenv "SWPATH"))
    (let ((str (string str)))
      (speccalc::checkSpecPathsExistence str)
      (princ (specware::setenv "SWPATH" (string str)))))
  (values))

#+allegro
(top-level:alias ("swpath" :case-sensitive) (&optional str)
  (if (null str)
      (princ (sys:getenv "SWPATH"))
    (let ((str (string str)))
      (speccalc::checkSpecPathsExistence str)
      (princ (setf (sys:getenv "SWPATH") (string str))))))

#+cmu
(defun cd (&optional dir)
  (specware::change-directory (or dir (specware::getenv "HOME"))))

(defun strip-extraneous (str)
  (let ((len (length str)))
    (if (> len 0)
	(if (member (elt str 0) '(#\" #\space))
	    (strip-extraneous (subseq str 1 len))
	  (if (member (elt str (- len 1)) '(#\" #\space))
	      (strip-extraneous (subseq str 0 (- len 1)))
	    str))
      str)))

#+cmu
(defun cl::commandp (form)
  (and (symbolp form)
       (eq (symbol-package form) *keyword-package*)))

#+cmu
(defun cl::invoke-command-interactive (command)
  (let ((fn (intern (symbol-name command)))
	(ch (read-char-no-hang)))
    (if ch
	(progn (unread-char ch)
	       (if (fboundp fn)
		   (funcall fn (strip-extraneous (read-line)))
		 (progn (read-line)
			(warn "Unknown command ~s" command))))
      (if (fboundp fn)
	  (funcall fn)
	(warn "Unknown command ~s" command)))))
