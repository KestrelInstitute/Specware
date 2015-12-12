;; This file builds a distribution directory for Window/Allegro Runtime Specware.

(defpackage :Specware)

(defvar Specware4-dir (Specware::getenv "SPECWARE4"))
(defun in-specware-dir (file) (concatenate 'string Specware4-dir "/" file))

;;; Get version information from canonical source...
(let ((version-file (in-specware-dir "Applications/Specware/Handwritten/Lisp/SpecwareVersion.lisp")))
  (if (probe-file version-file)
      (load version-file)
    (error "in BuildDistribution.lisp:  Cannot find ~A" version-file)))

;; dist-dir-name is the sub-directory to receive this particular distribution.
;; In particular, this is where generate-application puts all its stuff.
(defvar dist-dir-name "distribution/")

(defparameter distribution-directory 
  (in-specware-dir  (concatenate 'string dist-dir-name *Specware-Name* "/")))
(defun in-distribution-dir (file) (concatenate 'string distribution-directory file))

;; in-lisp-dir is used to get some emacs files used by allegro runtime
(defun in-lisp-dir (file) (concatenate 'string (sys:getenv "ALLEGRO") "/" file))

;;; For Windows, we use the Allegro Enterprise gen-app facility

;; If the application directory already exists, then we delete it.
;; generate-application complains and dies if the directory exists.
;;  (when (probe-file (make-pathname :directory distribution-directory))
;;    (excl::delete-directory-and-files
;;      (make-pathname :directory distribution-directory)))

(excl:generate-application
 ;; this is the name of the application
 *Specware-Name*

 ;; this is the directory where the application is to go
 ;; (plus accompanying files) 
 distribution-directory

 ;; a list of files to load
 '("BuildPreamble.lisp" "Specware4.lisp")

 ;; a list of files to copy to the distribution directory
 :application-files
 (list (in-specware-dir "Release/Windows/Specware4.cmd")
       (in-specware-dir "Release/Windows/Specware4 Shell.cmd")
       (in-specware-dir "Applications/Specware/Handwritten/Lisp/StartShell.lisp"))

 ;; Possible option instead of excl::delete-directory-and-files call
 :allow-existing-directory t

 ;; the image does not have a compiler neither during the build nor after.
 ;; The application has the interpreter only.
 :include-compiler t

 ;; which runtime? the other option is :dynamic which includes the compiler
 :runtime :dynamic
 )

(load (in-specware-dir "Applications/Specware/Handwritten/Lisp/copy-files-for-distribution.lisp"))

(Specware::copy-directory (in-lisp-dir "xeli/") (in-distribution-dir "Library/IO/Emacs/xeli/"))
