;; -*- MODE: LISP;  SYNTAX: COMMON-LISP; PACKAGE: USER; -*-
;;  Emacs LISP interaction
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defpackage "EMACS")
(in-package "EMACS")

#|
Notes:

(mp::make-process &key name ...)
(mp::process-run-function name-or-options prset-function &rest
			  preset-arguments)
(mp::process-kil process)


|#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Separation of REFINE functions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defvar *use-emacs-interface?* t)

(defun eval-in-emacs (string)
  (when *use-emacs-interface?*
    #+allegro
    (when lep::*connection*
      (lep::eval-in-emacs string))
    #-allegro (format t "~a" string)))


(defvar *select-term-number-in-spec*)


;;; Relies on select-mspe-object from msp-emacs.el (use M-x find-library)
;;; Extended from /usr/local/kiu/dev4/ki-patches/indep/msp-emacs.re
;;; The REFINE version calls re::mspe-object-selected 
;;; the LISP   version calls emacs::mspe-object-selected

(defun emacs::mspe-object-selected (n)
   (setq *select-term-number-in-spec* n))

  ;;; JUNK to be deleted?
  ;;  (setq ri::*selected-msp-object*
  ;;    (object-for-mspe-number n))
  
(defvar *goto-file-position-store?* nil)
(defvar *goto-file-position-stored* nil)
(defun goto-file-position (file line col)
  (unless (equal file "")
    (if (or *goto-file-position-store?* (not *use-emacs-interface?*))
	(setq *goto-file-position-stored* (list file line col))
      (eval-in-emacs (format nil "(goto-file-position ~s ~a ~a)" file line col)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Term selection

(defun looking-for-mspe-object(string)
  (eval-in-emacs (format nil "(looking-for-mspe-object ~S)" string)))

#+allegro
(defun select-term-in-spec ()
  (setq *select-term-number-in-spec* nil)
  (unwind-protect
      (progn (looking-for-mspe-object "Select term")
	     (mp:process-wait "Select term" #'eval '*select-term-number-in-spec*))
      )
  (if *select-term-number-in-spec*
      *select-term-number-in-spec*
    -1))


;;; (le)(defun open-spec-window ()
;;; (le)   (eval-in-emacs "(set-specware-ui-foci-frame 300 80 800 1000 3 \"Specware Interaction\" \"*Specware*\")")
;;; (le)   (snark::add-snark-menu-options))

(defun update-window-with-spec (specFile pathFile)
   (eval-in-emacs "(sw-erase-buffer *mspe-buffer*)")
   (eval-in-emacs (concatenate 'string "(mspe-insert \"" specFile "\" \"" pathFile "\")")))

(defun update-window-with-spec2 (specString)
   (eval-in-emacs "(sw-erase-buffer *mspe-buffer*)")
   (eval-in-emacs specString))

(defun goto-old-char ()
  (eval-in-emacs "(goto-char *mspe-save-char-position*)"))

(defun send-message-to-emacs (message)
  (let ((msg (format nil "(message ~S)" message)))
    (eval-in-emacs msg)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Display text in a dialog box.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun display-message (message)
  (eval-in-emacs (format nil "(open-output-window ~S)" message)))
  

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Retrieve input term from interface:
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defvar *input-term-from-window*)

#+allegro
(defun open-input-window ()
  (eval-in-emacs "(open-input-window)")
  (setq *input-term-from-window* nil)
   (unwind-protect
      (progn (mp:process-wait "Return string" #'eval '*input-term-from-window*)))
  (if *input-term-from-window*
      *input-term-from-window*
    ""))

(defun parseTerm (buffer) 
  (setq *input-term-from-window* buffer))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Register Spec with the interface
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; The registered spec name is added to the pull down menu for specs
;; When selecting the spec, emacs tells the UI to shift focus to this spec.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;;; (le)(defun add-new-spec (builtIn specName)
;;; (le)  (format t "Adding menu item ~S~%" specName)
;;; (le)  (let ((set-focus-message
;;; (le)	 (format nil "(emacs::set-specification-focus ~S )" specName)))
;;; (le)  (eval-in-emacs 
;;; (le)   (format nil 
;;; (le)  "(progn (select-frame *current-specware-ui-foci-frame*)   (switch-to-buffer *mspe-buffer*)
;;; (le)            (add-menu-item '(\"Specifications\" ~A) ~S '(send-message-to-lisp ~S) t))"
;;; (le)  builtIn specName set-focus-message))
;;; (le)  ))
;;; (le)
;;; (le)(defun set-specification-focus (specName) 
;;; (le)  (SpecwareUI::setFocus specName))
;;; (le)
;;; (le);;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; (le);; Toggle axiom settings
;;; (le);;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; (le)
;;; (le)(defun toggleIndex (number newSetting)
;;; (le)  (SpecwareUI::toggleIndex number newSetting))
;;; (le)
;;; (le)(defun toggleSosIndex (number newSetting)
;;; (le)  (SpecwareUI::toggleSosIndex number newSetting))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Create a multiple choice buffer that returns with the number that is
;; chosen.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defvar *input-choice-from-window*)

#+allegro
(defun open-multiple-choice-window (choices)
  (eval-in-emacs (format nil "(open-choice-window '~S)" choices))
  (setq *input-choice-from-window* nil)
   (unwind-protect
      (progn (mp:process-wait "Return string" #'eval '*input-choice-from-window*)))
  (if *input-choice-from-window*
      *input-choice-from-window*
    -1))

(defun choiceItem (choice) 
  (setq *input-choice-from-window* choice))

;;; (le) ;;;; Meta-point support
;;; (le) #+allegro
;;; (le) (defun get-source-file-info (spec name)
;;; (le)   (let ((pkg (find-package spec)))
;;; (le)     (if (null pkg)
;;; (le) 	"NO-SPEC"
;;; (le)       (let ((lisp-str (specId name)))
;;; (le) 	(let ((sym (find-symbol (if (eq (elt lisp-str 0) #\|)
;;; (le) 				    (string-trim "|" lisp-str)
;;; (le) 				  (string-upcase lisp-str)) pkg)))
;;; (le) 	  (if (null sym)
;;; (le) 	      "NO-SYMBOL"
;;; (le) 	    (let ((path (excl:source-file sym)))
;;; (le) 	      (if (null path)
;;; (le) 		  "NO-FILE"
;;; (le) 		(let ((path (merge-pathnames
;;; (le) 			     path
;;; (le) 			     (make-pathname :directory (sys::getenv "SPECWARE2000")))))
;;; (le) 		  (let ((dirs (pathname-directory path))
;;; (le) 			(ext (pathname-type path)))
;;; (le) 		    (let ((sl-path
;;; (le) 			   (if (and (eql ext "lisp")
;;; (le) 				    (eql (car (last dirs)) "lisp"))
;;; (le) 			       (merge-pathnames (make-pathname :directory (butlast dirs)
;;; (le) 							       :type "sl")
;;; (le) 						path)
;;; (le) 			     path)))
;;; (le) 		      (namestring sl-path))))))))))))
;;; (le) 
;;; (le) 
;;; (le) (defun specId (name)
;;; (le)   (let ((upper (string-upcase name)))
;;; (le)     (if (or (MetaSlangToLisp::isLispString upper)
;;; (le) 	    (eql (elt upper 0) #\!))
;;; (le) 	(concatenate 'string "|!" name "|")
;;; (le)       upper)))
;;; (le) 

