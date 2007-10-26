(in-package "CL-USER")

;;; Any lisp code anywhere within the Specware system should load this
;;; file to get the current version information.

(defparameter *Specware-Name*                 "Specware4")	; Name of dir and startup files
(defparameter *Specware-Major-Version*        4)
(defparameter *Specware-Minor-Version*        2)
(defparameter *Specware-Patch-Level*          4)

(defparameter *Specware-Version*              "4.2.4")
(defparameter *Specware-Version-Name*         "Specware-4-2-4")
(defparameter *Specware-Major-Version-String*  "4-2")           ; Used in patch detection and about-specware command

(format t "~&========================================================~%")
(format t "~&~28A = ~S~%"  '*Specware-Name*                 *Specware-Name*          )
(format t "~&~28A = ~S~%"  '*Specware-Major-Version*        *Specware-Major-Version* )
(format t "~&~28A = ~S~%"  '*Specware-Minor-Version*        *Specware-Minor-Version* )
(format t "~&~28A = ~S~%"  '*Specware-Patch-Level*          *Specware-Patch-Level*   )
(format t "~&~28A = ~S~%"  '*Specware-Version*              *Specware-Version*       )
(format t "~&~28A = ~S~%"  '*Specware-Version-Name*         *Specware-Version-Name*  )
(format t "~&~28A = ~S~%"  '*Specware-Major-Version-String* *Specware-Major-Version-String* )
(format t "~&========================================================~%")


;;;  The following can be used to find and load this file...
;;;
;;;  ;;; Get version information from canonical source...
;;;  (let ((specware4 (specware::getenv "SPECWARE4")))
;;;    (if (equal specware4 nil)
;;;        (error "in xxx.lisp:  SPECWARE4 environment variable not set")
;;;      (let ((specware-dir
;;;  	   (let ((dir (substitute #\/ #\\ specware4)))
;;;  	     (if (eq (schar dir (1- (length dir))) #\/)
;;;  		 dir
;;;  	       (concatenate 'string dir "/")))))
;;;        (let ((version-file (format nil "~AApplications/Specware/Handwritten/Lisp/SpecwareVersion.lisp"
;;;  				  specware-dir)))
;;;  	(if (probe-file version-file)
;;;  	    (load version-file)
;;;  	  (error "in xxx.lisp:  Cannot find ~A" version-file))))))
