;; These two definitions might not be needed here
;; They are in BuildPreamble.lisp where they are needed
(defvar Accord-version "4.0.11")
(defvar Accord-version-name "Specware-4-0-11")
(defvar Accord-name "Specware-Accord")	; Name of directory and startup files
(defvar Accord-dir (sys:getenv "ACCORD"))
(defvar Specware-dir (sys:getenv "SPECWARE4"))
(defun in-accord-dir (file) (concatenate 'string Accord-dir "/" file))
(defun in-specware-dir (file) (concatenate 'string Specware-dir "/" file))
(defun in-lisp-dir (file) (concatenate 'string (sys:getenv "ALLEGRO") "/" file))

;; This is the sub-directory to receive this particular distribution.
;; In particular, this is where generate-application puts all its stuff.
(defparameter distribution-directory 
  (in-accord-dir  (concatenate 'string "distribution/" Accord-name "/")))
(defun in-distribution-dir (file) (concatenate 'string distribution-directory file))

;; If the application directory already exists, then we delete it.
;; generate-application complains and dies if the directory exists.
(when (probe-file distribution-directory)
  (excl::delete-directory-and-files distribution-directory))

(generate-application
  ;; this is the name of the application
  Accord-name

  ;; this is the directory where the application is to go
  ;; (plus accompanying files) 
  distribution-directory

  ;; a list of files to load
  (mapcar #'(lambda (file) (format nil "~A/Applications/Specware/Handwritten/Lisp/~A.lisp" 
				   Specware-dir
				   file))
	  '("BuildAccordPreamble" "Specware4" "load-accord" "accord-license"))

  ;; a list of files to copy to the distribution directory
  :application-files
  (list ;;; (in-accord-dir "/Library/")
	;;; (in-accord-dir "/Applications/Accord/Courses/")
   (in-specware-dir "Release/Windows/Specware-Accord.cmd"))

  ;; Possible option instead of excl::delete-directory-and-files call
  ;;  :allow-existing-directory t

  ;; the image does not have a compiler neither during the build nor after.
  ;; The application has the interpreter only.
  :include-compiler nil

  ;; which runtime? the other option is :dynamic which includes the compiler
  :runtime :standard
  )

;;; Copy needed directories to distribution
(copy-directory (in-specware-dir "Library/Base/")
		(in-distribution-dir "Library/Base/"))
(copy-directory (in-specware-dir "Library/Accord/")
		(in-distribution-dir "Library/Accord/"))
(specware::copy-file (in-specware-dir "Library/Base.sw")
                     (in-distribution-dir "Library/Base.sw"))
(copy-directory (in-specware-dir "Library/IO/Emacs/")
		(in-distribution-dir "Library/IO/Emacs/"))
(copy-directory (in-specware-dir "UserDoc/tutorial/example/")
		(in-distribution-dir "Examples/Matching/"))
(copy-directory (in-specware-dir "UserDoc/examples/")
		(in-distribution-dir "Examples/"))

(specware::make-directory (in-distribution-dir "Documentation/"))
(specware::copy-file (in-specware-dir "UserDoc/language-manual/SpecwareLanguageManual.pdf")
 	   (in-distribution-dir "Documentation/SpecwareLanguageManual.pdf"))
(specware::copy-file (in-specware-dir "UserDoc/tutorial/SpecwareTutorial.pdf")
 	   (in-distribution-dir "Documentation/SpecwareTutorial.pdf"))
(specware::copy-file (in-specware-dir "UserDoc/user-manual/SpecwareUserManual.pdf")
 	   (in-distribution-dir "Documentation/SpecwareUserManual.pdf"))
(specware::copy-file (in-specware-dir "UserDoc/cheat-sheet/Specware-405-QuickReference.pdf")
 	   (in-distribution-dir "Documentation/Specware-QuickReference.pdf"))
(specware::copy-file (in-accord-dir "UserDoc/ReleaseNotes.txt")
		     (in-distribution-dir "Documentation/AccordReleaseNotes.txt"))
(specware::copy-file (in-accord-dir "UserDoc/Cygwin.txt")
		     (in-distribution-dir "Documentation/Cygwin.txt"))
(specware::copy-file (in-accord-dir "UserDoc/tutorial.pdf")
		     (in-distribution-dir "Documentation/AccordTutorial.pdf"))

(copy-directory (in-accord-dir "Tests/Queens/")
		(in-distribution-dir "Tests/Queens/"))
(copy-directory (in-accord-dir "Tests/Library/")
		(in-distribution-dir "Tests/Library/"))
(copy-directory (in-accord-dir "Tests/GCD/")
		(in-distribution-dir "Tests/GCD/"))
(copy-directory (in-accord-dir "Tests/Cipher/")
		(in-distribution-dir "Tests/Cipher/"))

(copy-directory (in-accord-dir "Sources/Handwritten/")
		(in-distribution-dir "Sources/Handwritten/"))

(copy-directory (in-lisp-dir "xeli/")
		(in-distribution-dir "Library/IO/Emacs/xeli/"))

(specware::make-directory (in-distribution-dir "Patches/"))

(specware::make-directory (in-distribution-dir "Languages/"))
(specware::make-directory (in-distribution-dir "Languages/MetaSlang/"))
(specware::make-directory (in-distribution-dir "Languages/MetaSlang/CodeGen/"))
(specware::make-directory (in-distribution-dir "Languages/MetaSlang/CodeGen/C/"))
(specware::make-directory (in-distribution-dir "Languages/MetaSlang/CodeGen/C/Clib/"))
(specware::make-directory (in-distribution-dir "Languages/MetaSlang/CodeGen/C/Clib/gc6.2/"))
(specware::make-directory (in-distribution-dir "Languages/MetaSlang/CodeGen/C/Clib/gc6.2/include/"))
(specware::make-directory (in-distribution-dir "Languages/MetaSlang/CodeGen/C/Clib/gc6.2/include/private/"))
(specware::make-directory (in-distribution-dir "Languages/MetaSlang/CodeGen/C/Clib/gc6.2/cord"))
(specware::make-directory (in-distribution-dir "Languages/MetaSlang/CodeGen/C/Clib/gc6.2/doc"))
(specware::make-directory (in-distribution-dir "Languages/MetaSlang/CodeGen/C/Clib/gc6.2/Mac_files"))
(specware::make-directory (in-distribution-dir "Languages/MetaSlang/CodeGen/C/Clib/gc6.2/tests"))
(specware::make-directory (in-distribution-dir "Languages/MetaSlang/CodeGen/C/Examples"))

(with-open-file (s (in-specware-dir "Languages/MetaSlang/CodeGen/C/cgen-distribution-files"))
  (let ((eof (cons nil nil)))
    (do ((filename (read-line s nil eof) (read-line s nil eof)))
	((eq filename eof))
      (let ((filename (string-trim '(#\Space #\Tab) filename)))
	(unless (equalp filename "")
	  (specware::copy-file (in-specware-dir filename) (in-distribution-dir filename)))))))

(let ((saw? nil)
      (in-file (in-distribution-dir "Languages/MetaSlang/CodeGen/C/Clib/gc6.2/Makefile"))
      (out-file (in-distribution-dir "temp")))
  (with-open-file (in in-file)
    (with-open-file (out out-file :direction :output)
      (let ((eof (cons nil nil)))
	(do ((line (read-line in nil eof) (read-line in nil eof)))
	    ((eq line eof))
	  (write-line (format nil "~A"
				  (cond ((equalp line "CC=cc $(ABI_FLAG)")
					 (setq saw? t)
					 "CC=gcc -w $(ABI_FLAG)")
					(t
					 line)))
		      out)))))
  (unless saw?
    (warn "Did not see \"CC=cc $(ABI_FLAG)\""))
  (delete-file in-file)
  (rename-file out-file in-file))


