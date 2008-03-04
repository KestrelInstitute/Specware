; for simplicity, use the same package that utilities.lisp uses
(defpackage :Distribution (:use :common-lisp))
(in-package :Distribution)

(cl:defpackage :swank-loader
	       (:use :cl)
	       (:export :load-swank :*source-directory* :*fasl-directory*))

(defvar *VERBOSE* nil)

;;  --------------------------------------------------------------------------------
;;; Since we compile files as part of this process, we assume we are running this
;;; code under the same lisp and OS as that for the distribution being built.
;;;
;;; In particular, we have
;;;   one of:   Linux, Mac, MSWindows 
;;;   one of:   SBCL, Allegro, CMU, OpenMCL
;;;
;;; Current candidates being used are:
;;;   Linux     SBCL      [was Linux Allegro, then Linux CMU]
;;;   MSWIndows Allegro   [soon MSWindows SBCL]
;;;   Mac       SBCL      
;;; --------------------------------------------------------------------------------

(let ((selected-os   (list #+Linux 'Linux #+Mac 'Mac #+MSWindows 'MSWindows))
      (selected-lisp (list #+CMU 'CMU #+SBCL 'SBCL #+Allegro 'Allegro #+OpenMCL 'OpenMCL)))
  (unless (= (length selected-os) 1)
    (error "Need exactly one OS selected, but have: ~S" selected-os))
  (unless (= (length selected-lisp) 1)
    (error "Need exactly one Lisp selected, but have: ~S" selected-lisp))
  (format t "~&;;; =================================================~%")
  (format t "~&;;; Gathering components for ~A under ~A~2%"
	  (car selected-lisp)
	  (car selected-os)))

(defvar *fasl-type*
  #+CMU     "x86f"
  #+SBCL    "sfsl"
  #+Allegro "fasl" 
  #+OpenMCL "???")

#+Allegro 
(eval-when (compile eval load)
  (require "genapp")
  (require "build")
  )

;; sigh -- miserable hack so we can read an emacs file without choking
(defpackage "SW")
(eval-when (compile eval load)
  (export (list (intern "SPECWARE-EMACS-FILES" "SW")) "SW"))

;;; See ../README for a description of the tree of components this code assembles.

;;; #+Allegro
;;; (eval-when (compile eval load)
;;;   (require "dist-utils")
;;;   (require "env-utils")
;;;   (require "dir-utils")
;;;   (require "save-image")
;;;   )
;;; #-Allegro
;;; (eval-when (compile eval load)
;;;   (load "dist-utils")
;;;   (load "env-utils")
;;;   (load "dir-utils")
;;;   (load "save-image")
;;;   )

;;; ================================================================================
;;; Parameters
;;; ================================================================================

;;; Get version information from canonical source...
(let ((specware4 (specware::getenv "SPECWARE4")))
  (if (equal specware4 nil)
      (error "in GatherSpecwareComponents.lisp:  SPECWARE4 environment variable not set")
    (let ((specware-dir
	   (let ((dir (substitute #\/ #\\ specware4)))
	     (if (eq (schar dir (1- (length dir))) #\/)
		 dir
	       (concatenate 'string dir "/")))))
      (let ((version-file (format nil "~AApplications/Specware/Handwritten/Lisp/SpecwareVersion.lisp"
				  specware-dir)))
	(if (probe-file version-file)
	    (load version-file)
	  (error "in GatherSpecwareComponents.lisp:  Cannot find ~A" version-file))))))

(defun print-blank ()
  (format t "~&~%"))

(defun print-blank-comment ()
  (format t "~&;;;~%"))

(defun print-break ()
  (format t "~&;;; ---------------------------------------------------------------------------~%"))

(defun print-major (component)
  (print-break)
  (format t "~&;;; Preparing ~A release ...~%" component))

(defun print-minor (component version)
  (print-blank)
  (format t "~&;;;   ~A ~A ...~%" component version)
  (print-blank-comment))

;;; ================================================================================
;;; Toplevel
;;; ================================================================================

(defun cl-user::prepare_specware_release (specware-dir distribution-dir &optional (*verbose* t))
  (declare (special cl-user::*Specware-Version-Name*))
  (let ((specware-dir     (truename specware-dir))
	(distribution-dir (truename distribution-dir))
	(release-dir      (truename (ensure-subdirs-exist distribution-dir "Releases" 
							  cl-user::*Specware-Version-Name*))))

    (format t "~&;;; Preparing release of ~A~%" cl-user::*Specware-Version-Name*)

    ;; Oops: As written, this is overkill (literally!).
    ;; In addition to deleting old versions of the files we're about to create,
    ;; it will also delete files created on other operating systems.
    ;; (when (probe-file release-dir)
    ;;  (format t "~&Deleting old version of ~A~%" release-dir)
    ;;  (generic-delete-directory release-dir t))
      
    (prepare_Specware_Lib specware-dir release-dir)
    (prepare_XEmacs_Lib   specware-dir release-dir)
    (prepare_C_Lib        specware-dir release-dir)
    (prepare_Specware     specware-dir release-dir distribution-dir)
    (print-blank)
    (print-break)
    (print-blank)
    (format t "~&The new release is at ~A~%" release-dir)
    (format t "~&It is safe to exit now.~%")
    ))

;;; ================================================================================
;;; Specware Library
;;; ================================================================================

(defun prepare_Specware_Lib (specware-dir release-dir)
  (print-major "Specware_Lib")
  (prepare_Specware_Lib_Generic specware-dir release-dir)
  #+Linux     (prepare_Specware_Lib_Linux   specware-dir release-dir)
  #+Mac       (prepare_Specware_Lib_Mac     specware-dir release-dir)
  #+MSWindows (prepare_Specware_Lib_Windows specware-dir release-dir)
  )

(defun prepare_Specware_Lib_Generic (specware-dir release-dir)
  (print-minor "Specware_Lib" "generic")
  (let* ((source-dir       (ensure-subdir-exists specware-dir "Library"))
	 ;;
	 (component-dir    (ensure-subdirs-exist release-dir "Specware_Lib" "Generic")))

    ;; First the standard Specware libaries...

    (copy-dist-file      (merge-pathnames source-dir    "Base.sw")
			 (merge-pathnames component-dir "Base.sw"))

    (copy-dist-file      (merge-pathnames source-dir    "InterpreterBase.sw")
			 (merge-pathnames component-dir "InterpreterBase.sw"))

    (copy-dist-directory (extend-directory source-dir    "Base")
			 (extend-directory component-dir "Base"))

    (copy-dist-directory (extend-directory source-dir    "ProverBase")
			 (extend-directory component-dir "ProverBase"))

    (copy-dist-directory (extend-directory source-dir    "Isa")
			 (extend-directory component-dir "Isa"))

    ;; When the user's Specware application starts, they need to load some 
    ;; handcoded definitions for a few primitive ops declared but not defined
    ;; in the Specware library.
    ;; Those definitions are all gathered into a file named SpecwareRuntime.lisp.

    (let ((source-files
	    (mapcar #'(lambda (entry)
		       (let ((subdirs (first  entry))
			     (name    (second entry)))
			 (make-pathname :directory (append (pathname-directory source-dir) subdirs)
					:name      name
					:type      "lisp"
					:defaults  specware-dir)))
		   '((("Base"                      "Handwritten" "Lisp") "meta-slang-runtime")
		     (("Base"                      "Handwritten" "Lisp") "ProvideSpecwareRuntime")
		     (("Base"                      "Handwritten" "Lisp") "Integer")
		     (("Base"                      "Handwritten" "Lisp") "Nat")
		     (("Base"                      "Handwritten" "Lisp") "Char")
		     (("Base"                      "Handwritten" "Lisp") "String")
		     (("Base"                      "Handwritten" "Lisp") "System")
		     (("IO" "Primitive"            "Handwritten" "Lisp") "IO")
		     (("Legacy" "Utilities"        "Handwritten" "Lisp") "State")
		     (("Legacy" "Utilities"        "Handwritten" "Lisp") "IO")
		     (("Legacy" "Utilities"        "Handwritten" "Lisp") "Lisp")
		     (("Structures" "Data" "Monad" "Handwritten" "Lisp") "State")
		     )))
	  (temp-file 
	   (merge-pathnames (ensure-subdir-exists component-dir "Base") 
			    (multiple-value-bind (sec min hour day month year)
				(decode-universal-time (get-universal-time))
			      (format nil "SpecwareRuntime-~2,'0D~2,'0D~2,'0D-~2,'0D~2,'0D~2,'0D"
				      (mod year 100) month day hour min sec))))
	  (target-file
	   (merge-pathnames (extend-directory component-dir "Base") "SpecwareRuntime.lisp")))
      (concatenate-files source-files temp-file)
      (cond ((and (probe-file target-file) (equivalent-files? temp-file target-file))
	     (format t "~&;;; Ignoring equivalent new ~A.~%" (file-namestring target-file))
	     (delete-file temp-file))
	    (t
	     (format t "~&;;; Creating new ~A~%" target-file)
	     (rename-file temp-file target-file)))
      )))

#+Linux     
(defun prepare_Specware_Lib_Linux   (specware-dir release-dir)
  (declare (ignore specware-dir))
  (print-minor "Specware_Lib" "Linux")
  (let* ((lib-dir          (ensure-subdirs-exist release-dir "Specware_Lib"))
	 (generic-dir      (ensure-subdirs-exist lib-dir "Generic" "Base" "Handwritten" "Lisp"))
	 (linux-dir        (ensure-subdirs-exist lib-dir "Linux"   "Base" "Handwritten" "Lisp")))
    (dolist (file (sorted-directory generic-dir))
      (let* ((pn            (pathname file))
	     (name          (pathname-name pn))
	     (type          (pathname-type pn))
	     (name_and_type (format nil "~A.~A" name type)))
	(when (equal type *fasl-type*)
	  (rename-file (merge-pathnames generic-dir name_and_type)
		       (merge-pathnames linux-dir   name_and_type)))))
    ))

#+Mac
(defun prepare_Specware_Lib_Mac (specware-dir release-dir)
  (declare (ignore specware-dir release-dir))
  (print-minor "Specware_Lib" "Mac")
  )

#+MSWindows
(defun prepare_Specware_Lib_Windows (specware-dir release-dir)
  (declare (ignore specware-dir))
  (print-minor "Specware_Lib" "Windows")
  (let* ((lib-dir          (ensure-subdirs-exist release-dir "Specware_Lib"))
	 (generic-dir      (ensure-subdirs-exist lib-dir "Generic" "Base" "Handwritten" "Lisp"))
	 (windows-dir      (ensure-subdirs-exist lib-dir "Windows" "Base" "Handwritten" "Lisp")))
    (dolist (file (sorted-directory generic-dir))
      (let* ((pn            (pathname file))
	     (name          (pathname-name pn))
	     (type          (pathname-type pn))
	     (name_and_type (format nil "~A.~A" name type)))
	(when (equal type *fasl-type*)
	  (let* ((source-file (merge-pathnames generic-dir name_and_type))
		 (target-file (merge-pathnames windows-dir name_and_type)))
	    (cond ((equivalent-files? source-file target-file)
		   (format t "~&;;; Ignoring equivalent new ~A.~%" (file-namestring target-file))
		   (delete-file source-file))
		  (t
		   (format t "~&;;; Renaming ~A~%" source-file)
		   (format t "~&;;;       to ~A~%" target-file)
		   (rename-file source-file target-file)))))))
    ))

;;; ================================================================================
;;; XEmacs Library
;;; ================================================================================

(defun prepare_XEmacs_Lib (specware-dir release-dir)
  (print-major "XEmacs_Lib")
  (prepare_XEmacs_Lib_Generic specware-dir release-dir)
  #+Linux     (prepare_XEmacs_Lib_Linux   specware-dir release-dir)
  #+Mac       (prepare_XEmacs_Lib_Mac     specware-dir release-dir)
  #+MSWindows (prepare_XEmacs_Lib_Windows specware-dir release-dir)
  )

(defun prepare_XEmacs_Lib_Generic (specware-dir release-dir)
  (print-minor "XEmacs_Lib" "generic")
  ;;
  ;; We use various Emacs/Lisp interfaces:
  ;;   slime/swank is used for SBCL on Linux and Mac (and will be for Windows)
  ;;   xeli        is used for Allegro under Windows
  ;;   ilisp       was used for awhile
  ;;
  ;; At user-installation time, we will merge the appropriate files under Library/IO/Emacs/
  ;;
  (let* ((source-dir       (extend-directory specware-dir "Library" "IO" "Emacs"))
	 ;;
	 (component-dir    (ensure-subdirs-exist release-dir "Emacs_Lib"))
	 ;;
	 (generic-dir      (ensure-subdir-exists component-dir "Generic"))
	 (slime-dir        (ensure-subdir-exists component-dir "slime"))
	 (ilisp-dir        (ensure-subdir-exists component-dir "ilisp"))
	 (xeli-dir         (ensure-subdir-exists component-dir "xeli"))
	 (openmcl-dir      (ensure-subdir-exists component-dir "OpenMCL"))
	 ;;
	 (generic-dirs     '("x-symbol"))
	 (x-files          '(;; "x-symbol-specware.el" is in files.el
			     ))
	 (generic-files    (append '("Preface.el"
				     "files.el" 
				     "compile.el"
				     "hideshow.el"
				     "hideshow.elc"
				     "specware_logo.xpm")
				   x-files
				   (with-open-file (s (merge-pathnames source-dir "files.el"))
				     (let ((form (read s)))
				       (if (and (eq (first  form) 'cl-user::defconst)
						(eq (second form) 'sw::specware-emacs-files))
					   (let ((names (eval (third form))))
					     (mapcan #'(lambda (name)
							 (list (format nil "~A.el"  name)
							       (format nil "~A.elc" name)))
						     names))
					 (error "files.el does seem to contain the form ~A"
						"(defconst sw:specware-emacs-files '(...))"))))))
	 ;;
	 (ilisp-dirs       '("ilisp"))
	 (ilisp-files	   '("load-ilisp.el"
			     "compile-misc-ilisp-files.el"
			     "compile-misc-ilisp-files-for-acl.el"))
	 ;;
	 (slime-dirs       '("slime"))
	 (slime-files      '("load-slime.el" 
			     "load-slime.lisp" 
			     "sw-slime.el" 
			     ))
	 ;;
	 (xeli-dirs        '("xeli"))
	 (xeli-files	   '("load.el"))
	 ;;
	 (openmcl-dirs     '())
	 (openmcl-files    '("load-openmcl.el"))
	 ;;
	 (ignored-dirs     '("CVS"))
	 (ignored-files    '(".cvsignore"
			     "files.elc" 
			     "compile.elc"
			     "compile-misc-ilisp-files.elc"
			     "compile-misc-ilisp-files-for-acl.elc"
			     "load.elc"
			     "load-ilisp.elc"
			     "load-slime.elc"
			     "load-openmcl.elc"
			     "sw-slime.elc" 
			     ))
	 ;;
	 (all-files        (append generic-files slime-files ilisp-files xeli-files openmcl-files ignored-files))
	 (all-dirs         (append generic-dirs  slime-dirs  ilisp-dirs  xeli-dirs  openmcl-dirs  ignored-dirs))
	 )


    ;; Warnings about ignored files

    (dolist (file (sorted-directory source-dir))
      (let ((name (pathname-name file)))
	(if (null name)
	    (unless (member (first (last (pathname-directory file))) all-dirs :test 'equal)
	      (format t "~&;;; Ignoring directory ~A" file))
	  (let ((name-and-type (namestring (make-pathname :name name :type (pathname-type file)))))
	    (unless (member name-and-type all-files :test 'equal)
	      (format t "~&;;; Ignoring file ~A" file))))))
      
    ;; Generic
    (progn 

      (dolist (dir generic-dirs)
	(copy-dist-directory (extend-directory source-dir  dir)
			     (extend-directory generic-dir dir)))

      (dolist (file generic-files)
	(copy-dist-file (merge-pathnames source-dir  file)
			(merge-pathnames generic-dir file)))
      )


    ;; Slime/Swank 
    (let ((slime-source-dir (extend-directory source-dir "slime")))

      ;; Loading swank-loader.lisp will compile all the swank files.
      ;; We need to compile here since the slime loader puts fasls by default under the
      ;; users home directory, not in a location derived from the source directory.

      (load (merge-pathnames slime-source-dir "swank-loader.lisp"))

      ;; (defpackage "SB-BSD-SOCKETS" (:use "COMMON-LISP"))
      ;; ;; loading swank-backend will compile all the swank lisp files...
      ;; (load (merge-pathnames slime-source-dir "swank-backend.lisp"))
      ;; 
      ;; #+allegro (compile-file (merge-pathnames slime-source-dir "swank-allegro.lisp"))
      ;; #+sbcl    (let ((sb-fasl:*fasl-file-type* *fasl-type*)) 
      ;; ;; The default for sbcl is "fasl", but that conflicts with Allegro, 
      ;; ;; so use "sfsl" instead (see binding of *fasl-type* at top of file).
      ;; (compile-file (merge-pathnames slime-source-dir "swank-sbcl.lisp")))
      ;; #+cmu     (compile-file (merge-pathnames slime-source-dir "swank-cmucl.lisp"))
      ;; #+openmcl (compile-file (merge-pathnames slime-source-dir "swank-openmcl.lisp"))
      
      (dolist (dir slime-dirs)
	(copy-dist-directory (extend-directory source-dir dir)
			     (extend-directory slime-dir  dir)))
      
      (dolist (file slime-files)
	(copy-dist-file (merge-pathnames source-dir file)
			(merge-pathnames slime-dir  file)))

      (let ((source-file (make-pathname :name "swank-backend" :type "lisp"))
	    (fasl-file   (make-pathname :name "swank-backend" :type *fasl-type*)))
	(declare (special swank-loader::*fasl-directory* 
			  swank-loader::*source-directory*))
	(copy-dist-file (merge-pathnames swank-loader::*source-directory* source-file)
			(merge-pathnames slime-dir                        source-file))
	(copy-dist-file (merge-pathnames swank-loader::*fasl-directory*   fasl-file)
			(merge-pathnames slime-dir                        fasl-file)))
      )

    ;; Ilisp
    (progn

      (dolist (dir ilisp-dirs)
	(copy-dist-directory (extend-directory source-dir dir)
			     (extend-directory ilisp-dir  dir)))

      (dolist (file ilisp-files)
	(copy-dist-file (merge-pathnames source-dir file)
			(merge-pathnames ilisp-dir  file)))
      )

    ;; xeli
    (progn

      (let* ((specware-xeli-dir (extend-directory source-dir "xeli"))
	     (source-xeli-dir   (if (null (generic-directory specware-xeli-dir))
				    ;; the 6.2 version of xeli is buggy, so use 7.0 version even with 6.2 lisp
				    #+Linux     "/usr/local/acl/acl70/xeli/" ; 6.2 version is buggy
				    #+MSWindows "C:\\Program Files\\acl70\\xeli\\" ; 6.2 version is buggy
				    #-(or Linux MSWindows) "[no idea where xeli lives on non-Linux, non-Windows OS]"
				    specware-xeli-dir)))
	#-MSWindows 
	(format t "~&;;; Ignoring non-Windows sources for xeli at ~A~%" source-xeli-dir)
	#+MSWindows 
	(copy-dist-directory source-xeli-dir
			     (extend-directory xeli-dir  "xeli")
			     t
			     #'(lambda (p) (member (pathname-type p)
						   '("elbak" "elcbak")
						   :test 'equalp))))
    
      (dolist (file xeli-files)
	(copy-dist-file (merge-pathnames source-dir file)
			(merge-pathnames xeli-dir   file)))
      )


    ;; OpenMCL
    (progn
      (dolist (dir openmcl-dirs)
	(copy-dist-directory (extend-directory source-dir  dir)
			     (extend-directory openmcl-dir dir)))
      
      (dolist (file openmcl-files)
	(copy-dist-file (merge-pathnames source-dir  file)
			(merge-pathnames openmcl-dir file)))
      )

    ))

#+Linux     
(defun prepare_XEmacs_Lib_Linux   (specware-dir release-dir)
  (declare (ignore specware-dir release-dir))
  (print-minor "XEmacs_Lib" "Linux")
  )

#+Mac
(defun prepare_XEmacs_Lib_Mac     (specware-dir release-dir)
  (declare (ignore specware-dir release-dir))
  (print-minor "XEmacs_Lib" "Mac")
  )

#+MSWindows
(defun prepare_XEmacs_Lib_Windows (specware-dir release-dir)
  (declare (ignore specware-dir release-dir))
  (print-minor "XEmacs_Lib" "Windows")
  )

;;; ================================================================================
;;; C Library
;;; ================================================================================

(defun prepare_C_Lib (specware-dir release-dir)
  (print-major "C_Lib")
  (prepare_C_Lib_Generic specware-dir release-dir)
  #+Linux     (prepare_C_Lib_Linux   specware-dir release-dir)
  #+Mac       (prepare_C_Lib_Mac     specware-dir release-dir)
  #+MSWindows (prepare_C_Lib_Windows specware-dir release-dir)
  )

#+Linux
(defun prepare_C_Lib_Linux   (specware-dir release-dir)
  (declare (ignore specware-dir release-dir))
  (print-minor "C_Lib" "Linux")
  )

#+Mac
(defun prepare_C_Lib_Mac     (specware-dir release-dir)
  (declare (ignore specware-dir release-dir))
  (print-minor "C_Lib" "Mac")
  )

#+MSWindows
(defun prepare_C_Lib_Windows (specware-dir release-dir)
  (declare (ignore specware-dir release-dir))
  (print-minor "C_Lib" "Windows")
  )

(defun prepare_C_Lib_Generic (specware-dir release-dir)
  ;; We include Clib as its own component, so it can be remerged (or not)
  ;; under the generic Library directory at user installation time.
  ;; This also makes it easier to replace it with alternatives, etc.
  (print-minor "C_Lib" "generic")
  (let* ((source-clib-dir   (extend-directory specware-dir "Library" "Clib"))
	 (source-clib-path  (pathname-directory  source-clib-dir))
	 ;;
	 (gen-dist-file     (make-pathname :name "cgen-distribution-files" :defaults source-clib-dir))
	 (gen-dist-files    (let ((filenames nil))
			      (with-open-file (s gen-dist-file)
				(do ((line (read-line s nil nil) (read-line s nil nil)))
				    ((null line)
				     (sort filenames 'namestring-lessp))
				  (let ((line (string-trim '(#\Space #\Tab) line)))
				    (unless (equal line "")
				      (push line filenames)))))))
	 ;;
	 (target-clib-dir   (ensure-subdirs-exist release-dir "C_Lib" "Generic"))
	 (target-clib-path  (pathname-directory target-clib-dir)))
    
    ;; --------------------
    ;; mention any discrepencies between files listed in cgen-distribution-files vs. files found in directory
    ;;
    (let ((source-files (remove-if #'(lambda (pn)
				       (let ((name (pathname-name pn)))
					 (or (null   name)
					     (ignored-file? pn))))
				   (sorted-directory source-clib-dir :recursive? t))))
      (let ((x gen-dist-files)
	    (y source-files))
	(loop
	  (cond ((null x)
		 (dolist (z y) 
		   (unless (or (equalp (pathname-type z) "a")
			       (equalp (pathname-type z) "o")
			       (member "gc6.2" (pathname-directory z) :test 'equalp))
		     (warn "Ignoring file not mentioned in cgen-distribution-files: ~A" z)))
		 (return nil))
		((null y)
		 (dolist (z x) 
		   (warn "[A]File mentioned in cgen-distribution-files is missing: ~A" z))
		 (return nil))
		(t
		 (let* ((gen-dist-file (make-pathname :directory (append (pathname-directory source-clib-dir) 
									 (cdr (pathname-directory (car x)))) 
						      :device    (pathname-device source-clib-dir)
						      :defaults  (car x)))
			(source-file (car y))
			(xn (substitute #\/ #\\ (enough-namestring gen-dist-file source-clib-dir)))
			(yn (substitute #\/ #\\ (enough-namestring source-file   source-clib-dir))))
		   (cond ((string-equal xn yn)
			  (pop x)
			  (pop y))
			 ((string-lessp xn yn)
			  (warn "[B]File mentioned in cgen-distribution-files is missing: ~A" (pop x)))
			 (t
			  (let ((z (pop y)))
			    (unless (or (equalp (pathname-type z) "a")
					(equalp (pathname-type z) "o")
					(member "gc6.2" (pathname-directory z) :test 'equalp)
					(member (pathname-name z) 
						'("cgen-distribution-files"
						  "cgen-distribution-files-6-2"
						  "base_lib"
						  "gctest"
						  "if_mach"
						  "if_not_there"
						  "threadlibs")
						:test 'equalp))
			      (warn ";;; Ignoring file not mentioned in cgen-distribution-files: ~A" z))))))))))
      ;; (when *verbose* (format t "~&~%"))
      )
    ;;
    ;; --------------------

    (dolist (filename gen-dist-files)
      (let* ((pn          (pathname filename))
	     (name        (pathname-name      pn))
	     (type        (pathname-type      pn)) 
	     (path        (pathname-directory pn))
	     (path        (if (eq (first path) :relative) (rest path) path))
	     (source-path (append source-clib-path path))
	     (target-path (append target-clib-path path)))
	(cond ((and (null name) (null type))
	       (ensure-directories-exist (make-pathname :directory target-path 
							:defaults  target-clib-dir)))
	      ((equalp name "CVS")  ; redundant: copy-dist-file would ignore file
	       nil)
	      (t
	       (let ((source-file (make-pathname :directory source-path
						 :name      name
						 :type      type
						 :defaults  source-clib-dir))
		     (target-file (make-pathname :directory target-path
						 :name      name
						 :type      type
						 :defaults  target-clib-dir)))
		 (ensure-directories-exist target-file)
		 ;; (when (probe-file target-file) (delete-file target-file))
		 (copy-dist-file source-file target-file))))))

    ;; --------------------
    ;; Some obscure hack to tweak Makefile -- TODO: What is this???

    ;; (when *verbose*(format t "~&~%"))
    (let* ((saw-old? nil)
	   (saw-new? nil)
	   (target-file (make-pathname :name     "Makefile" 
				       :defaults (extend-directory target-clib-dir "gc6.6")))
	   (temp-file   (make-pathname :name     "temp"
				       :defaults target-clib-dir)))
      (with-open-file (target target-file)
	(with-open-file (temp temp-file :direction :output :if-exists :supersede)
	  (let ((eof (cons nil nil)))
	    (do ((line (read-line target nil eof) (read-line target nil eof)))
		((eq line eof))
	      (write-line (format nil "~A"
				  (cond ((equalp line "CC=cc $(ABI_FLAG)")
					 (setq saw-old? t)
					 (when *verbose*
					   (format t "~&;;; In ~A~%" target-file)
					   (format t "~&;;;   replacing ~S~%" line)
					   (format t "~&;;;        with ~S~%" "CC=gcc -w $(ABI_FLAG)"))
					 "CC=gcc -w $(ABI_FLAG)")
					((equalp line "CC=gcc -w $(ABI_FLAG)")
					 (setq saw-new? t)
					 (when *verbose*
					   (format t "~&;;; In ~A~%" target-file)
					   (format t "~&;;;   leaving ~S~%" line))
					 line)
					(t
					 line)))
			  temp)))))
      (unless (or saw-old? saw-new?)
	(warn "Did not see ~A or ~A in ~A" 
	      "CC=cc $(ABI_FLAG)"
	      "CC=gcc -w $(ABI_FLAG)"
	      target-file))
      (cond (saw-old?
	     (delete-file target-file)
	     (rename-file temp-file target-file))
	    ((probe-file temp-file)
	     (delete-file temp-file))))
    
    ))

;;; ================================================================================
;;; Specware
;;; ================================================================================

(defun prepare_Specware (specware-dir release-dir distribution-dir)
  (print-major "Specware")
  (let ((lisp-utilities-dir (truename (ensure-subdirs-exist distribution-dir "Lisp_Utilities"))))
    (prepare_Specware_Generic specware-dir release-dir)
    #+Linux     (prepare_Specware_Linux   specware-dir release-dir lisp-utilities-dir)
    #+Mac       (prepare_Specware_Mac     specware-dir release-dir lisp-utilities-dir)
    #+MSWindows (prepare_Specware_Windows specware-dir release-dir lisp-utilities-dir)
    ))

(defun prepare_Specware_Generic (specware-dir release-dir)
  (print-minor "Specware" "generic")
  (let* ((source-dir  (ensure-subdirs-exist specware-dir))
	 (generic-dir (ensure-subdirs-exist source-dir  "Release" "Generic"))
	 (target-dir  (ensure-subdirs-exist release-dir "Specware" "Generic")))

    ;; License file (InstallShield looks for this)
    (copy-dist-file (make-pathname :name "SpecwareClickThruLicense" :type "txt" :defaults generic-dir)
		    (make-pathname :name "SpecwareClickThruLicense" :type "txt" :defaults target-dir))

    ;; Icons
    (copy-dist-file (make-pathname :name "S" :type "ico" :defaults (extend-directory specware-dir "Icons"))
		    (make-pathname :name "S" :type "ico" :defaults target-dir))
    
    (copy-dist-file (make-pathname :name "KestrelBird" :type "xpm" :defaults (extend-directory specware-dir "Icons"))
		    (make-pathname :name "KestrelBird" :type "xpm" :defaults target-dir))
    
    ;; Documentation
    (let ((source-doc-dir (extend-directory     source-dir "UserDoc"))
	  (target-doc-dir (ensure-subdirs-exist target-dir "Documentation")))
      ;; (format t "~&;;;~%")
      (format t "~&;;;   Getting Documentation ...~%")
      (copy-dist-file  (make-pathname :name "SpecwareLanguageManual"    :type "pdf" :defaults (extend-directory source-doc-dir "language-manual")) 
		       (make-pathname :name "SpecwareLanguageManual"    :type "pdf" :defaults target-doc-dir))
      (copy-dist-file  (make-pathname :name "SpecwareTutorial"          :type "pdf" :defaults (extend-directory source-doc-dir "tutorial"))
		       (make-pathname :name "SpecwareTutorial"          :type "pdf" :defaults target-doc-dir))
      (copy-dist-file  (make-pathname :name "SpecwareUserManual"        :type "pdf" :defaults (extend-directory source-doc-dir "user-manual"))
		       (make-pathname :name "SpecwareUserManual"        :type "pdf" :defaults target-doc-dir))
      (copy-dist-file  (make-pathname :name "QuickReference"            :type "pdf" :defaults (extend-directory source-doc-dir "cheat-sheet"))
		       (make-pathname :name "Specware-QuickReference"   :type "pdf" :defaults target-doc-dir))
      (copy-dist-file  (make-pathname :name "SpecwareIsabelleInterface" :type "pdf" :defaults (extend-directory source-doc-dir "isabelle-interface"))
		       (make-pathname :name "SpecwareIsabelleInterface" :type "pdf" :defaults target-doc-dir))

      (let ((notes-file (make-pathname :name "ReleaseNotes" :type "txt" :defaults source-doc-dir)))
	(when (probe-file notes-file)
	  (copy-dist-file notes-file
			  (make-pathname :name "ReleaseNotes" :type "txt" :defaults target-doc-dir))))
      )

    ;; Examples
    (let ((examples-dir    (ensure-subdirs-exist target-dir "Examples")))
      ;; (format t "~&;;;~%")
      (format t "~&;;;   Getting Examples ...~%")

      (copy-dist-directory (extend-directory source-dir   "UserDoc" "tutorial" "example")
			   (extend-directory examples-dir "Matching"))
      
      (let ((matching (extend-directory examples-dir "Matching")))
	(delete-file (make-pathname :name "MatchingRichard"         :type "sw":defaults matching))
	(delete-file (make-pathname :name "MatchingRichardTheorems" :type "sw":defaults matching)))

      (copy-dist-directory (extend-directory source-dir "UserDoc" "examples")
			   (extend-directory target-dir "Examples"))

      (copy-dist-directory (extend-directory source-dir "UserDoc" "isabelle-interface" "example")
			   (extend-directory target-dir "Examples"))

      ;; (let ((snark-dir (extend-directory examples-dir "Matching" "Snark"))
      ;;       (lisp-dir  (extend-directory examples-dir "Matching" "lisp")))
      ;; 
      ;;   (when (probe-file snark-dir) 
      ;;     (generic-delete-directory snark-dir))
      ;;   (when (probe-file lisp-dir)  
      ;;     (generic-delete-directory lisp-dir)))

      (let ((simple1 (extend-directory examples-dir "simple1"))
	    (simple2 (extend-directory examples-dir "simple2"))
	    (simple3 (extend-directory examples-dir "simple3")))
	(delete-file (make-pathname :name "test" :type "lisp":defaults simple1))
	(delete-file (make-pathname :name "test" :type "lisp":defaults simple2))
	(delete-file (make-pathname :name "test" :type "lisp":defaults simple3))))
    ))

#+Linux
(defun prepare_Specware_Linux (specware-dir release-dir lisp-utilities-dir)
  (declare (special cl-user::*Specware-Name*))
  (print-minor "Specware" "Linux")
  (let* ((source-dir              (ensure-subdirs-exist specware-dir))
	 (source-buildscripts-dir (ensure-subdirs-exist source-dir "Release" "BuildScripts"))
	 (source-generic-dir      (ensure-subdirs-exist source-dir "Release" "Generic"))
	 (source-linux-dir        (ensure-subdirs-exist source-dir "Release" "Linux"))
	 #+CMUCL
	 (source-linux-cmucl-dir  (ensure-subdirs-exist source-dir "Release" "Linux" "CMUCL"))
	 #+SBCL
	 (source-linux-sbcl-dir   (ensure-subdirs-exist source-dir "Release" "Linux" "SBCL"))
	 ;;
	 (target-dir              (ensure-subdirs-exist release-dir "Specware" "Linux"))

	 ;; a list of files to load into the new application
	 (files-to-load           (list (merge-pathnames lisp-utilities-dir      "LoadUtilities")
					(merge-pathnames lisp-utilities-dir      "MemoryManagement")
					(merge-pathnames lisp-utilities-dir      "CompactMemory")
					(merge-pathnames source-buildscripts-dir "BuildSpecwarePreamble")
					(merge-pathnames source-buildscripts-dir "LoadSpecware")
					(merge-pathnames source-buildscripts-dir "SpecwareLicense")))

	 ;; a list of files put on the distribution directory
	 (files-to-copy           (append
				    #+CMUCL
				    (list (merge-pathnames source-linux-cmucl-dir "Specware")
					  (merge-pathnames source-linux-cmucl-dir "SpecwareShell")
					  (merge-pathnames source-linux-cmucl-dir "Find_CMUCL")
					  (merge-pathnames source-linux-cmucl-dir "Find_Specware_App_CMUCL")
					  (merge-pathnames source-linux-cmucl-dir "Isabelle_Specware")
					  (merge-pathnames source-linux-cmucl-dir "XEmacs_Specware")
					  )
				    #+SBCL 
				    (list (merge-pathnames source-linux-sbcl-dir "Specware")
					  (merge-pathnames source-linux-sbcl-dir "SpecwareShell")
					  (merge-pathnames source-linux-sbcl-dir "Find_SBCL")
					  (merge-pathnames source-linux-sbcl-dir "Find_Specware_App_SBCL")
					  (merge-pathnames source-linux-sbcl-dir "Isabelle_Specware")
					  (merge-pathnames source-linux-sbcl-dir "XEmacs_Specware")
					  )
				    (list
				     (merge-pathnames source-linux-dir      "install_gnome_desktop_icons_specware")
				     (merge-pathnames source-linux-dir      "Find_XEMACS")
				     (merge-pathnames source-linux-dir      "Find_SPECWARE4")
				     (merge-pathnames source-linux-dir      "Update_Path")
				     (merge-pathnames source-linux-dir      "Update_SWPATH")
				     (merge-pathnames source-generic-dir    "StartSpecwareShell.lisp")
				     ))))

    (dolist (file files-to-load) (specware::compile-file-if-needed file))

    ;; Installation Scripts
    
    ;; Executables/Images
    (generate-new-lisp-application #+CMUCL "/usr/share/cmulisp/bin/lisp" 
				   #+CMUCL (format nil "~A.cmuimage" cl-user::*Specware-Name*)

				   #+SBCL  "/usr/local/bin/sbcl"
				   #+SBCL  (format nil "~A.sbclexe" cl-user::*Specware-Name*)

				   target-dir
				   (mapcar #'(lambda (f) (make-pathname :defaults f :type *fasl-type*)) files-to-load)
				   files-to-copy
				   t
				   :executable? t)

    ;; Patches
    (prepare_patch_dir source-dir target-dir)
    ))

#+Mac
(defun prepare_Specware_Mac (specware-dir release-dir lisp-utilities-dir)
  ;; work in progress...
  (declare (ignore specware-dir release-dir lisp-utilities-dir))
  (print-minor "Specware" "Mac")
  (specware::copy-file (in-specware-dir "Release/Mac/SBCL/Isabelle_Specware")
		       (in-distribution-dir "Isabelle_Specware.terminal"))
  (specware::copy-file (in-specware-dir "Release/Mac/SBCL/XEmacs_Specware")
		       (in-distribution-dir "XEmacs_Specware"))
  )

#+MSWindows
(defun prepare_Specware_Windows (specware-dir release-dir lisp-utilities-dir)
  (declare (special cl-user::*Specware-Name*))
  (print-minor "Specware" "Windows")
  (let* ((source-dir                 (ensure-subdirs-exist specware-dir))
	 (source-buildscripts-dir    (ensure-subdirs-exist source-dir "Release" "BuildScripts"))
	 (source-generic-dir         (ensure-subdirs-exist source-dir "Release" "Generic"))
	 (source-windows-dir         (ensure-subdirs-exist source-dir "Release" "Windows"))
	 (source-windows-allegro-dir (ensure-subdirs-exist source-dir "Release" "Windows" "Allegro"))
	 ;;
	 (target-dir                 (ensure-subdirs-exist release-dir "Specware" "Windows"))
	 (specware-exe-file          (format nil "~A.exe" cl-user::*Specware-Name*))

	 ;; a list of files to load into the new application
	 (files-to-load              (list (merge-pathnames lisp-utilities-dir       "LoadUtilities")
					   (merge-pathnames lisp-utilities-dir       "MemoryManagement")
					   (merge-pathnames lisp-utilities-dir       "CompactMemory")
					   (merge-pathnames source-buildscripts-dir  "BuildSpecwarePreamble")
					   (merge-pathnames source-buildscripts-dir  "LoadSpecware")
					   (merge-pathnames source-buildscripts-dir  "SpecwareLicense")))

	 ;; a list of files to copy to the distribution directory
	 (files-to-copy              (list (merge-pathnames source-windows-allegro-dir "Specware.cmd")
					   (merge-pathnames source-windows-allegro-dir "SpecwareShell.cmd")
					   (merge-pathnames source-windows-allegro-dir "Find_Specware_App_ACL.cmd")
					   (merge-pathnames source-windows-allegro-dir "start-in-xemacs-xeli.cmd")
					   (merge-pathnames source-windows-allegro-dir "start-in-xemacs-ilisp.cmd")
					   (merge-pathnames source-windows-allegro-dir "start-in-xemacs-slime.cmd")

					   (merge-pathnames source-windows-dir         "Find_XEMACS.cmd")
					   (merge-pathnames source-windows-dir         "Find_SPECWARE4.cmd")
					   (merge-pathnames source-windows-dir         "Update_Path.cmd")
					   (merge-pathnames source-windows-dir         "Update_SWPATH.cmd")
					   (merge-pathnames source-generic-dir         "StartSpecwareShell.lisp")))
	 )

    (dolist (file files-to-load) (specware::compile-file-if-needed file))

    ;; Installation Scripts

    ;; Executables/Images
    (dolist (filename (list (format nil "~A.lic" cl-user::*Specware-Name*)
			    (format nil "~A.dxl" cl-user::*Specware-Name*)
			    specware-exe-file
			    "Specware.cmd"
			    "SpecwareShell.cmd"
			    "Find_Specware_App_ACL.cmd"
			    "start-in-xemacs-xeli.cmd"
			    "start-in-xemacs-ilisp.cmd"
			    "start-in-xemacs-slime.cmd"
			    "Find_XEMACS.cmd"
			    "Find_SPECWARE4.cmd"
			    "Update_Path.cmd"
			    "Update_SWPATH.cmd"
			    "StartSpecwareShell.lisp"))
      (let ((filename (format nil "~A~A" target-dir filename)))
	(when (probe-file filename)
	  (format t "~&;;; Deleting old version of ~A~%" filename)
	  (delete-file filename))))
    (generate-new-lisp-application :Allegro 
				   specware-exe-file
				   target-dir

				   (mapcar #'(lambda (f) (make-pathname :defaults f :type *fasl-type*)) files-to-load)
				   files-to-copy
				   t)

    ;; CVS is perversely hardwired to refuse to accept *.exe files.
    ;; They are presumed to be binary files and hence outside it's purview.
    ;; The documented means for overriding the default behavior, putting 
    ;; a ! in the .cvsignore file, doesnt't work.
    ;; I tried to enter the .exe files under aliases, and later rename them 
    ;; back to .exe for the CD.  But no matter what alias is used, CVS will 
    ;; accept the first version and then refuse to update after that.
    ;; So we prepare a zip file to put the related dxl,exe,lic files together
    ;; in a form that can evade CVS's deadly radar.
    ;; (Was I really, really bad in some previous incarnation??)

    (let* ((zip-file (make-pathname :name     cl-user::*Specware-Name*
				    :type     "zip"
				    :defaults target-dir))
	   (zip-cmd (format nil "zip -j -9 ~A ~{ ~A ~}"
			    zip-file
			    (mapcar #'(lambda (type)
					(namestring (make-pathname :name     cl-user::*Specware-Name*
								   :type     type
								   :defaults target-dir)))
				    '("lic" "exe" "dxl")))))
      (when (probe-file zip-file)
	(format t "~&;;; Deleting old zip file ~A~%" zip-file)
	(delete-file zip-file))
      (format t "~&;;; About to run ~A~%" zip-cmd)
      (format t "~&;;;  -j suppresses directories in names~%")
      (format t "~&;;;  -9 is highest compression level~%")
      (excl::run-shell-command zip-cmd))
    ;; Patches
    (prepare_patch_dir source-dir target-dir)
    ))

;;; ================================================================================
;;; Patches (Linux and Windows)
;;; ================================================================================

;;;  TODO: copy highest-numbered patch from "$SPECWARE4"/Release/Linux/CMU/Patches
;;; /bin/cp "$SPECWARE4"/Release/Linux/CMU/Patches/patch-4-0-6.*fasl-type* "$SPECWARE4"/distribution-cmulisp/Patches

(defun prepare_patch_dir (source-dir target-dir)
  (let ((source-patch-dir (extend-directory source-dir "Release" "Windows" "Patches"))
	(target-patch-dir (extend-directory target-dir "Patches"))
	(lisp
	 #+CMU       "CMUCL"
	 #+SBCL      "SBCL"
	 #+Allegro   "Allegro"
	 #+OpenMCL   "OpenMCL")
	(fasl 
	 #+CMU       "x86f"
	 #+SBCL      "sfsl"
	 #+Allegro   "fasl" 
	 #+OpenMCL   "????")
	(os 
	 #+Linux     "Linux"
	 #+MSWindows "Windows" 
	 #+Mac       "Mac OSX"))

    (format t "~&~%;;;   Preparing ~A patches for ~A under ~A...~%" fasl lisp os)
    (when *verbose*
      (format t "~&;;;   Ensuring patch directory exists: ~A~%" target-patch-dir))
    (ensure-directories-exist target-patch-dir)
    (let ((source-patch-lisp (make-pathname :name "empty-patch-template" :type "lisp" :defaults source-patch-dir))
	  (target-patch-lisp (make-pathname :name "empty-patch-template" :type "lisp" :defaults target-patch-dir)))

      (copy-dist-file source-patch-lisp target-patch-lisp)

      (let* ((target-patch-fasl (make-pathname :name     "empty-patch-template" 
					       :type     *fasl-type*
					       :defaults target-patch-dir)))
	(cond ((probe-file target-patch-fasl)
	       (when *verbose*
		 (format t "~&;;;   Fasl for empty patch file already present for ~A under ~A: ~A~%"
			 lisp os
			 (file-namestring target-patch-fasl))
		 (force-output t)))
	      (t
	       (when *verbose*
		 (format t "~&;;;   Compiling empty ~A patch file using ~A under ~A~%" fasl lisp os)
		 (force-output t))
	       (compile-file target-patch-lisp :verbose *verbose*)))))))
	       

