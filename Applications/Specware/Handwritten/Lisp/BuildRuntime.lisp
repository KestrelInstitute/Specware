(defvar Specware-version "4.0 Beta")
(defvar Specware-version-name "Specware-4-0-Beta")

(defvar distribution-directory "Distribution")

;; This is the sub-directory to receive this particular distribution.
;; In particular, this is where generate-application puts all its stuff.
(defvar application-directory 
  (list :relative distribution-directory "Specware4"))

;; If the application directory already exists, then we delete it.
;; generate-application complains and dies if the directory exists.
(when (probe-file (make-pathname :directory application-directory))
  (excl::delete-directory-and-files
    (make-pathname :directory application-directory)))

(generate-application
;; this is the name of the application
  "Specware4"

;; this is the directory where the application is to go
;; (plus accompanying files) 
  (format nil "~A" (make-pathname :directory application-directory))

;; a list of files to load
  '(Specware4.lisp)

;; the image does not have a compiler neither during the build nor after.
;; The application has the interpreter only.
  :include-compiler nil

;; which runtime? the other option is :dynamic which includes the compiler
  :runtime :standard
)