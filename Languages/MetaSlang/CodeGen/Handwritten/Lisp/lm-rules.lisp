;;; -*- Mode: LISP; Package: Specware; Base: 10; Syntax: Common-Lisp -*-

(defpackage :LM (:use :COMMON-LISP-USER))
(in-package :Parser4)

;;; This generic file is loaded prior to (or within) a file with more 
;;; language specific rules such as those for MetaSlang, C, etc.

;;; ========================================================================
;;; These are generic parsing rules somewhat independent of the detaila of 
;;; the source and target.  The descriptions of translation rules may refer
;;; to features such as currying, infix, precedence, argument order, etc.
;;;
;;; Assumptions:
;;;
;;;   The source type  in a morphism rule is a (possibly quaflfied) name.
;;;   The source field in a morphism rule is an unstructured name (a string).
;;;   The source op    is a morphism rule is a (possibly quaflfied) name.
;;;
;;;   The target type  in a morphism rule is an unstructured name (a string).
;;;   The target field in a morphism rule is an unstructured name (a string).
;;;   The target term  is a morphism rule is one of
;;;    unstructured name (a string) 
;;;    typed term : ((type)term), where type is a simple string
;;;    parenthesized list of terms : (term* )
;;; ========================================================================

;;; ========================================================================
;;;  Utility functions
;;; ========================================================================

;;; Parser may return :uspecified for (:optional ..)

(defun make-false  () nil)
(defun make-true   () t)
(defun make-option (x) (if (eq x :unspecified) '(:|None|) `(:|Some| . ,x)))
(defun make-bool   (x) (if (eq x :unspecified) (make-false) (make-true)))

;;; ========================================================================
;;;  Primitives
;;; ========================================================================

(define-lm-parser-rule :Symbol    nil nil :documentation "Primitive")
(define-lm-parser-rule :String    nil nil :documentation "Primitive")
(define-lm-parser-rule :Number    nil nil :documentation "Primitive")
(define-lm-parser-rule :Character nil nil :documentation "Primitive")
(define-lm-parser-rule :Pragma    nil nil :documentation "Primitive")

(define-lm-parser-rule :Arrow
    (:anyof "->" "\\_rightarrow"))

;;; ========================================================================
;;;  TOP LEVEL
;;; ========================================================================

(define-lm-parser-rule :Toplevel 	; toplevel needs to be anyof rule
    (:anyof (1 :LanguageMorphism))
  (1))                                  ; semantics must be (1), not 1

;;; ========================================================================
;;;  LanguageMorphism
;;; ========================================================================

(define-lm-parser-rule :LanguageMorphism 
    (:tuple (1 :Language) (2 :Sections))
  (lm::make_LanguageMorphism-3 "MetaSlang" 1 2))

;;; ========================================================================
;;;  Language
;;; ========================================================================

(define-lm-parser-rule :Language
    (:tuple (1 :SimpleName))
  (lm::make_Language 1))

;;; ========================================================================
;;; Sections
;;; ========================================================================

(define-lm-parser-rule :Sections 
    (:tuple (1 (:repeat* :Section)))
  1)

(define-lm-parser-rule :Section 
    (:anyof :Verbatim_Section
            :Imports_Section
            :Morphism_Section
            :Generated_Section 
            :Natives_Section))

;;; ========================================================================
;;;  Verbatim
;;; ========================================================================

(define-lm-parser-rule :Verbatim_Section 
    (:tuple (1 :Pragma)) ; three-element list: prefix, body, postfix
  (LM::make_Verbatim_Section-3 . 1)) 

;;; ========================================================================
;;;  Imports
;;; ========================================================================

(define-lm-parser-rule :Imports_Section 
    (:tuple :KW_Import (1 :Imports))
  (LM::make_Imports_Section 1))  

(define-lm-parser-rule :Imports 
    :Pathnames)

(define-lm-parser-rule :Pathnames
    (:repeat* :Pathname))

(define-lm-parser-rule :Pathname
    (:tuple (:optional (1 :Directory)) (2 :FileName) "." (3 :FileExtension))
  (LM::make_Pathname-3 (make-option 1) 2 3))

(define-lm-parser-rule :Directory
    (:anyof :RootedDir :NonRootedDir))

(define-lm-parser-rule :RootedDir
    (:tuple "/" (1 (:repeat* :DirectoryNode)))
  (LM::make_Directory-2 (make-true) 1))

(define-lm-parser-rule :NonRootedDir
    (:tuple (1 (:repeat+ :DirectoryNode)))
  (LM::make_Directory-2 (make-false) 1))

(define-lm-parser-rule :DirectoryNode
    (:tuple (1 :DirectoryId) "/")
  1)

(define-lm-parser-rule :FileName 
    :SimpleName)

(define-lm-parser-rule :FileExtension
    :SimpleName)
  
(define-lm-parser-rule :DirectoryId 
    :SimpleName)
  
(define-lm-parser-rule :KW_Import
    (:anyof "-import" "-include"))

;;; ========================================================================
;;;  Morphism
;;; ========================================================================

(define-lm-parser-rule :Morphism_Section 
    (:tuple :KW_Morphism (1 :Translations))
  (LM::make_Morphism_Section 1)) 

(define-lm-parser-rule :KW_Morphism
    (:anyof "-morphism" "-translate"))

(define-lm-parser-rule :Translations
    (:repeat* :Translation))

(define-lm-parser-rule :Translation
    (:anyof :TypeTranslation 
            :FieldTranslation
            :OpTranslation))

;;; ========================================================================
;;;  Names
;;;  Simple names are just symbols:  "X", "0", "<=", etc.
;;;  Dotted names are simple names separated by dots: "A.B.f" etc.
;;;  No check for plausiblity is done, so "A.0.<=.X" is legal.
;;; ========================================================================

(define-lm-parser-rule :SimpleName ; corresponds to Symbol in LanguageMorphism.sw
    (:anyof
     ;; keywords in pragma parser are also legal ids
     ((:tuple "struct")    "struct")
     ((:tuple "curry")     "curry")
     ((:tuple "uncurry")   "uncurry")
     ((:tuple "left")      "left")
     ((:tuple "right")     "right")
     ((:tuple "infix")     "infix")
     ((:tuple "prefix")    "prefix")
     ((:tuple "postfix")   "postfix")
     ((:tuple "reversed")  "reversed")
     ((:tuple "primitive") "primitive") 
     ((:tuple "type")      "type")
     ((:tuple "field")     "field")
     ((:tuple "op")        "op")
     ((:tuple "in")        "in")
     ((:tuple (1 :Symbol)) (common-lisp::symbol-name (quote 1)))
     ))

(define-lm-parser-rule :Name 
    (:tuple (1 (:repeat :SimpleName ".")))
  (list . 1))

;;; ========================================================================
;;;  Terms
;;; ========================================================================

(define-lm-parser-rule :Term
    (:anyof :Name_Term :Number_Term :Apply_Term :Vector_Term :Typed_Term))

;;; --------

(define-lm-parser-rule :Name_Term
    (:tuple (1 :Name))
  (LM::make_Name_Term 1))

;;; --------

(define-lm-parser-rule :Number_Term
    (:tuple (1 :Number))
  (LM::make_Number_Term 1))

;;; --------

(define-lm-parser-rule :Apply_Term
    (:tuple (1 :Term) (2 :Arg_Term))
  (LM::make_Apply_Term-2 1 2))

(define-lm-parser-rule :Arg_Term
    (:anyof :List_Term :Vector_Term))

(define-lm-parser-rule :List_Term
    (:anyof :List_Term_Spaces :List_Term_Commas))

(define-lm-parser-rule :List_Term_Spaces
    (:tuple "(" (1 (:repeat* :Term)) ")")
  (LM::make_List_Term_Spaces 1))

(define-lm-parser-rule :List_Term_Commas
    (:tuple "(" (1 :Term) "," (2  (:repeat+ :Term ",")) ")")
  (LM::make_List_Term_Commas (cons 1 2)))

;;; --------

(define-lm-parser-rule :Vector_Term
    (:tuple "[" (1 :Term) "," (2  (:repeat+ :Term ",")) "]")
  (LM::make_Vector_Term (cons 1 2)))

;;; --------

(define-lm-parser-rule :Typed_Term
    (:anyof :Prefix_Typed_Term :Postfix_Typed_Term))

(define-lm-parser-rule :Prefix_Typed_Term   ; C
   (:tuple (:anyof (:tuple "(" "(") "((") (1 :Term) ")" (2 :Term) ")")
  (LM::make_Prefix_Typed_Term-2 1 2))

(define-lm-parser-rule :Postfix_Typed_Term  ; Haskell, Isabelle
    (:tuple (1 :Term) "::" (2 :Term))
  (LM::make_Postfix_Typed_Term-2 2 1))

;;; ========================================================================
;;;  Location
;;; ========================================================================

(define-lm-parser-rule :Location
    (:anyof :PathnameLocation :PrimitiveLocation))

(define-lm-parser-rule :PathnameLocation
    (:tuple "in" (1 :Pathname))
  (LM::make_Pathname_Location 1))

(define-lm-parser-rule :PrimitiveLocation
    (:tuple "primitive")
  (LM::make_Primitive_Location-0))

;;; ========================================================================
;;;  TypeTranslation
;;; ========================================================================

(define-lm-parser-rule :TypeTranslation 
    (:tuple "type"
            (1 :Name)
            :Arrow 
            (:optional (4 "struct"))
            (2 :Term) 
            (:optional (3 :Location)))
  (LM::make_Type_Translation-4 1 2 (make-option 3) (make-bool 4)))

;;; ========================================================================
;;;  FieldTranslation
;;; ========================================================================

(define-lm-parser-rule :FieldTranslation 
    (:tuple "field" (1 :FieldRef) :Arrow  (2 :FieldRef) (:optional (3 :Location)))
  (LM::make_Field_Translation-3 1 2 (make-option 3)))

(define-lm-parser-rule :FieldRef 
    (:tuple (1 :Name) "." (2 :Fieldid))
  (LM::make_FieldRef-2 1 2)) 

(define-lm-parser-rule :FieldId
    :SimpleName)

;;; ========================================================================
;;;  OpTranslation
;;; ========================================================================

(define-lm-parser-rule :OpTranslation 
    (:tuple "op" 
            (1 :Name)
            :Arrow 
            (2 :Term)
            (:optional (3 :ReCurry))
            (:optional (4 :Fixity))
            (:optional (5 :Precedence))
            (:optional (6 :Reversed))
            (:optional (7 :Location)))
  (LM::make_Op_Translation-7 1 2 
                             (make-option 3) 
                             (make-option 4)
                             (make-option 5)
                             (make-bool   6)
                             (make-option 7)))

(define-lm-parser-rule :ReCurry
    (:tuple (1 (:anyof "curried" "uncurried")))
  (LM::make_recurry 1))

(define-lm-parser-rule :Fixity
    (:tuple (1 (:anyof "infix" "right" "left" "prefix" "postfix")))
  (LM::make_LM_Fixity 1))

(define-lm-parser-rule :Precedence
    :Number)

(define-lm-parser-rule :Reversed
    (:tuple "reversed")
  (LM::make_true))

;;; ========================================================================
;;;  Natives
;;; ========================================================================

(define-lm-parser-rule :Natives_Section 
    (:tuple "-native" (1 :Natives))
  (LM::make_Natives_Section 1)) 

(define-lm-parser-rule :Natives 
    (:repeat* :Native))

(define-lm-parser-rule :Native 
    (:anyof :NativeType :NativeOp))

(define-lm-parser-rule :NativeType 
    (:tuple "type" (1 :Name) (:optional (2 :Location)))
  (LM::make_Type_Native-2 1 (make-option 2)))

(define-lm-parser-rule :NativeOp 
    (:tuple "op" (1 :Name) (:optional (2 :Location)))
  (LM::make_Op_Native-2 1 (make-option 2)))

;;; ========================================================================
;;;  Generated
;;; ========================================================================

(define-lm-parser-rule :Generated_Section 
    (:tuple "-generated")
  (LM::make_Generated_Section-0)) 

