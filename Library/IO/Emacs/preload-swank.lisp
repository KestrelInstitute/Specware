(in-package :common-lisp-user)

;;; To avoid loading swank at each startup, load this prior to saving image

(defvar *using-slime-interface?* t)

(when *using-slime-interface?*
  ;; Preload slime lisp support

  ;; per instructions in swank-loader.lisp
  (cl:defpackage :swank-loader
		 (:use :cl)
		 (:export :load-swank 
			  :*source-directory*
			  :*fasl-directory*))
  )

;; Repeat the when test so the defparameter below can 
;; be read after the defpackage above has been evaluted.
(when *using-slime-interface?*
  (eval
   `(defparameter ,(intern "*FASL-DIRECTORY*" "SWANK-LOADER")
     (format nil "~a/Library/IO/Emacs/slime/" (Specware::getenv "SPECWARE4"))))
  (let ((loader (format nil "~a/Library/IO/Emacs/slime/swank-loader.lisp" 
                        (Specware::getenv "SPECWARE4"))))
    (load loader :verbose t)
    (funcall (read-from-string "swank-loader:init") :setup nil :reload t :load-contribs t)))

(setq *using-slime-interface?* nil)	; Gets set to t when initialized
