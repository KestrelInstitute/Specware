(in-package :cl-user)

(defun delete-file-if-present (fil)
  (when (probe-file fil)
    (delete-file fil)))

;;; Copy needed directories to distribution
(specware::make-directory (in-distribution-dir "Library/"))
(specware::copy-directory (in-specware-dir "Library/Base/")
			  (in-distribution-dir "Library/Base/"))
(specware::delete-directory (in-distribution-dir "Library/Base/CVS/"))
(specware::delete-directory (in-distribution-dir "Library/Base/Handwritten/CVS/"))
(specware::delete-directory (in-distribution-dir "Library/Base/Handwritten/Lisp/CVS/"))
(delete-file-if-present (in-distribution-dir "Library/Base/Handwritten/Lisp/.cvsignore"))

(specware::copy-directory (in-specware-dir "Library/ProverBase/")
			  (in-distribution-dir "Library/ProverBase/"))
(specware::delete-directory (in-distribution-dir "Library/ProverBase/CVS/"))

(specware::copy-file (in-specware-dir "Library/Base.sw")
                     (in-distribution-dir "Library/Base.sw"))
(specware::copy-file (in-specware-dir "Library/InterpreterBase.sw")
                     (in-distribution-dir "Library/InterpreterBase.sw"))

(specware::make-directory (in-distribution-dir "Library/IO/"))
(specware::copy-directory (in-specware-dir "Library/IO/Emacs/")
			  (in-distribution-dir "Library/IO/Emacs/"))
(specware::delete-directory (in-distribution-dir "Library/IO/Emacs/CVS/"))
(specware::delete-directory (in-distribution-dir "Library/IO/Emacs/ilisp/CVS/"))

(specware::make-directory (in-distribution-dir "Examples/"))
(specware::copy-directory (in-specware-dir "UserDoc/tutorial/example/")
			  (in-distribution-dir "Examples/Matching/"))
(delete-file-if-present (in-distribution-dir "Examples/Matching/.cvsignore"))
(specware::delete-directory (in-distribution-dir "Examples/Matching/CVS"))
;;(specware::delete-directory (in-distribution-dir "Examples/Matching/Snark"))
;;(specware::delete-directory (in-distribution-dir "Examples/Matching/lisp"))

(specware::copy-directory (in-specware-dir "UserDoc/examples/")
			  (in-distribution-dir "Examples/"))
(specware::delete-directory (in-distribution-dir "Examples/CVS"))
(specware::delete-directory (in-distribution-dir "Examples/simple1/CVS"))
(delete-file-if-present (in-distribution-dir "Examples/simple1/test.lisp"))
(specware::delete-directory (in-distribution-dir "Examples/simple2/CVS"))
(delete-file-if-present (in-distribution-dir "Examples/simple2/test.lisp"))
(specware::delete-directory (in-distribution-dir "Examples/simple2/Refs/CVS"))
(specware::delete-directory (in-distribution-dir "Examples/simple2/Specs/CVS"))
(specware::delete-directory (in-distribution-dir "Examples/simple3/CVS"))
(delete-file-if-present (in-distribution-dir "Examples/simple3/test.lisp"))

(specware::make-directory (in-distribution-dir "Examples/Accord/"))

(specware::copy-directory (in-specware-dir "../Accord/Tests/Library/")
			  (in-distribution-dir "Examples/Accord/Library/"))
(delete-file-if-present (in-distribution-dir "Examples/Accord/Library/.cvsignore"))

(specware::copy-directory (in-specware-dir "../Accord/Tests/Cipher/")
			  (in-distribution-dir "Examples/Accord/Cipher/"))
(delete-file-if-present (in-distribution-dir "Examples/Accord/Cipher/.cvsignore"))

(specware::copy-directory (in-specware-dir "../Accord/Tests/F91/")
			  (in-distribution-dir "Examples/Accord/F91/"))
(delete-file-if-present (in-distribution-dir "Examples/Accord/F91/.cvsignore"))

(specware::copy-directory (in-specware-dir "../Accord/Tests/GCD/")
			  (in-distribution-dir "Examples/Accord/GCD/"))
(delete-file-if-present (in-distribution-dir "Examples/Accord/GCD/.cvsignore"))

(specware::copy-directory (in-specware-dir "../Accord/Tests/Queens/")
			  (in-distribution-dir "Examples/Accord/Queens/"))
(delete-file-if-present (in-distribution-dir "Examples/Accord/Queens/.cvsignore"))

(specware::concatenate-files
   (loop for fil in '("Base/Handwritten/Lisp/Integer"
		      "Base/Handwritten/Lisp/Nat"
		      "Base/Handwritten/Lisp/Char"
		      "Base/Handwritten/Lisp/String"
		      "Base/Handwritten/Lisp/System"
		      "IO/Primitive/Handwritten/Lisp/IO"
		      "Legacy/Utilities/Handwritten/Lisp/State"
		      "Legacy/Utilities/Handwritten/Lisp/IO"
		      "Legacy/Utilities/Handwritten/Lisp/Lisp"
		      "Structures/Data/Monad/Handwritten/Lisp/State"
		      "../Applications/Handwritten/Lisp/meta-slang-runtime"
		      "../Applications/Specware/Handwritten/Lisp/ProvideSpecwareRuntime")
      collect (in-specware-dir (format nil "Library/~a.lisp" fil)))
   (in-distribution-dir "Library/SpecwareRuntime.lisp"))

(specware::make-directory (in-distribution-dir "Documentation/"))
(specware::copy-file (in-specware-dir "UserDoc/language-manual/SpecwareLanguageManual.pdf")
		     (in-distribution-dir "Documentation/SpecwareLanguageManual.pdf"))
(specware::copy-file (in-specware-dir "UserDoc/tutorial/SpecwareTutorial.pdf")
		     (in-distribution-dir "Documentation/SpecwareTutorial.pdf"))
(specware::copy-file (in-specware-dir "UserDoc/user-manual/SpecwareUserManual.pdf")
		     (in-distribution-dir "Documentation/SpecwareUserManual.pdf"))
(specware::copy-file (in-specware-dir "UserDoc/cheat-sheet/QuickReference.pdf")
		     (in-distribution-dir "Documentation/Specware-QuickReference.pdf"))
;(specware::copy-file (in-specware-dir "UserDoc/ReleaseNotes.txt")
;		     (in-distribution-dir "Documentation/ReleaseNotes.txt"))

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


