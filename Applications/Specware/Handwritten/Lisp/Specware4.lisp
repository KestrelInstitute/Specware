#+Lispworks
(setq *default-package-use-list* '("CL"))

(defpackage "Specware")
(in-package "Specware")

(terpri) ; purely cosmetic

;;; ---------------
;; The following collection have been adapted from the 2000 load.lisp
;; file. Perhaps they should be factored into a separate file as they
;; are likely to be used for many of the generated lisp applications?

(defun current-directory ()
  #+allegro(excl::current-directory)
  #+Lispworks(hcl:get-working-directory)  ;(current-pathname)
  )

(defun change-directory (directory)
  ;; (lisp::format t "Changing to: ~A~%" directory)
  #+allegro(excl::chdir directory)
  #+Lispworks (hcl:change-directory directory)
  (setq lisp::*default-pathname-defaults* (current-directory)))

#+Lispworks
(defun make-system (new-directory)
  (let ((*default-pathname-defaults*
     (make-pathname :name (concatenate 'string new-directory "/")
            :defaults
            system::*current-working-pathname*))
    (old-directory (current-directory)))
    (change-directory new-directory)
    (unwind-protect (load "system.lisp")
      (change-directory old-directory))))

#-Lispworks
(defun make-system (new-directory)
  (let ((old-directory (current-directory)))
    (change-directory new-directory)
    (unwind-protect (load "system.lisp")
      (change-directory old-directory))))

(defun compile-and-load-lisp-file (file)
   (#+allegro excl::compile-file-if-needed
    #+Lispworks hcl:compile-file-if-needed
    (make-pathname :defaults file :type "lisp"))
   (load (make-pathname :defaults file :type nil)))

;; The following list should be generated automatically!
;; Perhaps setq is the wrong thing to use. defvar?
;; The list is used only in this file.
;;; ---------------
(setq HandwrittenFiles
  '(
    "Library/Base/Handwritten/Lisp/Boolean.lisp"
    "Library/Base/Handwritten/Lisp/Integer.lisp"
    "Library/Base/Handwritten/Lisp/Nat.lisp"
    "Library/Base/Handwritten/Lisp/Char.lisp"
    "Library/Base/Handwritten/Lisp/List.lisp"
    "Library/Base/Handwritten/Lisp/String.lisp"
    "Library/Base/Handwritten/Lisp/Option.lisp"
    "Library/IO/Primitive/Handwritten/Lisp/IO.lisp"
    "Library/Legacy/Utilities/Handwritten/Lisp/State.lisp"
    "Library/Legacy/Utilities/Handwritten/Lisp/IO.lisp"
    "Library/Legacy/Utilities/Handwritten/Lisp/Lisp.lisp"
    "Library/Legacy/DataStructures/Handwritten/Lisp/HashTable.lisp"
  )
)

(setq Specware4 (sys:getenv "SPECWARE4"))

(compile-and-load-lisp-file "runtime")

(map 'list #'(lambda (file)
  (compile-and-load-lisp-file (concatenate 'string Specware4 "/" file)))
  HandwrittenFiles
)

;; Now load the generated lisp code.
(compile-and-load-lisp-file "../../lisp/Specware4.lisp")

;; Stephen's toplevel aliases 
(compile-and-load-lisp-file "toplevel")

;; Might need this?
;;(defun compilelisp::additionaldefinitions ()
;;  (if (boundp 'parser4::*collected-definitions*) 
;;      (symbol-value 'parser4::*collected-definitions*)
;;    nil))

;; This defines the RE package .. this will go away when the bootstrap
;; is complete.
(compile-and-load-lisp-file "re-legacy")

;; The following are temporary until the parser migrates under the Specware4
;; tree. The following are referred to in semantics.lisp but the qualifiers
;; have changed in the move to Specware 4. 
;; Can we remove this dependency? It would be nice if the parser didn't
;; refer to MetaSlang specs.
(defpackage :ATERM)

(defun ATerm::mkQualifiedId (qualifier id) 
  (MetaSlang::mkQualifiedId qualifier id))

(defun ATerm::mkQualifiedId-1 (x) 
  (MetaSlang::mkQualifiedId (car x) (cdr x)))
                                             
(defun ATerm::mkUnQualifiedId (id) 
  (MetaSlang::mkUnQualifiedId id))

;; Does this belong here? Why not in the parser?
(defpackage "PARSER")

;; This is also temporary. The SW4 tokenizer.lisp file refers to
;;   parser::create-tokenizer-parameters
;;   parser::extract-tokens-from file.
;; And yet it has its own version of basic parser library in parser4.
;; So there needs to be a rationalization of the parser.
(make-system (concatenate 'string Specware4 "/../2000/parser1"))

;; We assume for the time being that the SW4 tree is a sibling of
;; the Specware4 tree.
(make-system (concatenate 'string
    Specware4 "/../SW4/Languages/MetaSlang/Parser/Handwritten"))
(make-system (concatenate 'string
    Specware4 "/../SW4/Languages/SpecCalculus/Parser/Handwritten"))

(format t "~2%To test, run (test)~%")
(format t "~%That will run (sw \"/Applications/Specware/Specware4\")~2%")

(defun user::test ()
  (user::sw "/Applications/Specware/Specware4")
)

