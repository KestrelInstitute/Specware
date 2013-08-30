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

(defun make-option  (x) (if (eq x :unspecified) '(:|None|) `(:|Some| . ,x)))
(defun make-boolean (x) (if (eq x :unspecified) nil        x))

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
    (:repeat* :Import))

(define-lm-parser-rule :Import 
    (:tuple (1 :DirectoryPath) (2 :FileName))
  (LM::make_Import-2 1 2)) 

(define-lm-parser-rule :DirectoryPath 
    (:tuple "/" (1 (:repeat* :DirectoryName)))
  1)

(define-lm-parser-rule :DirectoryName 
    (:tuple (1 :FileId) "/")
  1)

(define-lm-parser-rule :FileName 
    (:tuple (1 :FileId) "." (2 :FileId))
  (LM::make_FileName-2 1 2)) 

(define-lm-parser-rule :FileId 
    (:tuple (1 :Symbol))
  (common-lisp::symbol-name (quote 1)))
  
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
     ((:tuple "curry")    "curry")
     ((:tuple "uncurry")  "uncurry")
     ((:tuple "infix")    "infix")
     ((:tuple "right")    "right")
     ((:tuple "left")     "left")
     ((:tuple (1 :Symbol)) (common-lisp::symbol-name (quote 1)))
     ))

(define-lm-parser-rule :Name 
    (:tuple (1 (:repeat :SimpleName ".")))
  (list . 1))

;;; ========================================================================
;;;  Terms
;;; ========================================================================

(define-lm-parser-rule :Term
    (:anyOf :Name_Term :List_Term :Apply_Term :Typed_Term))

;;; --------

(define-lm-parser-rule :Name_Term
    (:tuple (1 :Name))
  (LM::make_Name_Term 1))

;;; --------

(define-lm-parser-rule :List_Term
    (:tuple "(" (1 :Terms) ")")
  (LM::make_List_Term 1))

(define-lm-parser-rule :Terms
    (:anyof :Terms_Spaces :Terms_Commas))

(define-lm-parser-rule :Terms_Spaces
    (:repeat* :Term))

(define-lm-parser-rule :Terms_Commas
    (:repeat* :Term ","))

;;; --------

(define-lm-parser-rule :Apply_Term
    (:tuple (1 :Term) "(" (2 :Term) ")")
  (LM::make_Apply_Term-2 1 2)) 

;;; --------

(define-lm-parser-rule :Typed_Term
    (:anyOf :C_Typed_Term :Isabelle_Typed_Term))

(define-lm-parser-rule :C_Typed_Term
    (:tuple "(" "(" (1 :Term) ")" (2 :Term) ")")
  (LM::make_Typed_Term-2 1 2))

(define-lm-parser-rule :Isabelle_Typed_Term
    (:tuple (1 :Term) "::" (2 :Term))
  (LM::make_Typed_Term-2 2 1))

;;; ========================================================================
;;;  TypeTranslation
;;; ========================================================================

(define-lm-parser-rule :TypeTranslation 
    (:tuple "type" (1 :Name) :Arrow (2 :Term))
  (LM::make_Type_Translation-2 1 2))  


;;; ========================================================================
;;;  FieldTranslation
;;; ========================================================================

(define-lm-parser-rule :FieldTranslation 
    (:tuple "field" (1 :FieldRef) :Arrow (2 :FieldRef))
  (LM::make_Field_Translation-2 1 2)) 

(define-lm-parser-rule :FieldRef 
    (:tuple (1 :Name) "." (2 :Fieldid))
  (LM::make_FieldRef-2 1 2)) 

(define-lm-parser-rule :FieldId
    (:tuple (1 :Symbol))
  (common-lisp::symbol-name (quote 1)))

;;; ========================================================================
;;;  OpTranslation
;;; ========================================================================

(define-lm-parser-rule :OpTranslation 
    (:tuple "op" (1 :Name) :Arrow (2 :Term)
            (:optional (3 :ReCurry))
            (:optional (4 :Fixity))
            (:optional (5 :Precedence))
            (:optional (6 :Reversed)))
  (LM::make_Op_Translation-6 1 2 
                             (make-option  3) 
                             (make-option  4)
                             (make-option  5)
                             (make-boolean 6)))

(define-lm-parser-rule :ReCurry
    (:tuple (1 (:anyof "curried" "uncurried")))
  (LM::make_recurry 1))

(define-lm-parser-rule :Fixity
    (:tuple (1 (:anyof "infix" "right" "left")))
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
    (:tuple "type" (1 :Name))
  (LM::make_Type_Native 1)) 

(define-lm-parser-rule :NativeOp 
    (:tuple "op" (1 :Name))
  (LM::make_Op_Native 1)) 

;;; ========================================================================
;;;  Generated
;;; ========================================================================

(define-lm-parser-rule :Generated_Section 
    (:tuple "-generated")
  (LM::make_Generated_Section-0)) 

