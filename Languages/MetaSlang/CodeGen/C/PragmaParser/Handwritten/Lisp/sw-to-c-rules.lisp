;;; -*- Mode: LISP; Package: Specware; Base: 10; Syntax: Common-Lisp -*-

(defpackage :SpecCalc (:use :COMMON-LISP-USER))
(defpackage :SW_TO_C  (:use :COMMON-LISP-USER))
(in-package :Parser4)

;;; ========================================================================
;;;  Primitives
;;; ========================================================================

(define-sw-parser-rule :Symbol    () nil nil :documentation "Primitive")
(define-sw-parser-rule :String    () nil nil :documentation "Primitive")
(define-sw-parser-rule :Number    () nil nil :documentation "Primitive")
(define-sw-parser-rule :Character () nil nil :documentation "Primitive")
(define-sw-parser-rule :Pragma    () nil nil :documentation "Primitive")

;;; ========================================================================
;;;  Names
;;; ========================================================================

;;; ------------------------------------------------------------------------
;;;  SW Name
;;; ------------------------------------------------------------------------

(define-sw-parser-rule :SW_Id () ;; same as :NAME in specware parser
  (:anyof
   ((:tuple "answerVar")    "answerVar")
   ((:tuple "colimit")      "colimit")
   ((:tuple "diagram")      "diagram")
   ((:tuple "expand")       "expand")
   ((:tuple "export")       "export")
   ((:tuple "extendMorph")  "extendMorph")
   ((:tuple "hide")         "hide")
   ((:tuple "is")           "is")
   ((:tuple "options")      "options")
   ((:tuple "print")        "print")
   ((:tuple "reduce")       "reduce")
   ((:tuple "translate")    "translate")
   ((:tuple "using")        "using")
   ((:tuple "with")         "with")
   ((:tuple "/")            "/")
   ((:tuple "*")            "*")
   ((:tuple "\\_times")     "\\_times")
   ((:tuple "UID")          "UID")
   ((:tuple "at")           "at")
   ((:tuple "repeat")       "repeat")
   ((:tuple "slice")        "slice")
   ((:tuple (1 :Symbol))    (common-lisp::symbol-name (quote 1)))
   ))

(define-sw-parser-rule :SW_Qualifier ()
  :SW_Id)

(define-sw-parser-rule :UnqualifiedName ()
  (:tuple (1 :SW_Id))
  (MetaSlang::mkUnQualifiedId 1))

(define-sw-parser-rule :QualifiedName ()
  (:tuple (1 :SW_Qualifier) "." (2 :SW_Id))
  (MetaSlang::mkQualifiedId-2 1 2))

(define-sw-parser-rule :SW_Name ()
  (:anyof :UnqualifiedName :QualifiedName))

(define-sw-parser-rule :SW_TypeName ()
  :SW_Name)

(define-sw-parser-rule :SW_FieldName ()
  (:tuple (1 :SW_Id))
  (sw_to_C::make_SW_FieldName 1)) ; ok

(define-sw-parser-rule :SW_OpName ()
  :SW_Name)

;;; ------------------------------------------------------------------------
;;;  C Name
;;; ------------------------------------------------------------------------

(define-sw-parser-rule :C_Id () 
  (:tuple (1 :Symbol))
  (common-lisp::symbol-name (quote 1)))

(define-sw-parser-rule :C_TypeName () 
  (:tuple (1 :C_Id))
  (SW_TO_C::make_C_TypeName 1)) ; ok

(define-sw-parser-rule :C_FieldName () 
  (:tuple (1 :C_Id))
  (SW_TO_C::make_C_FieldName 1)) ; ok

(define-sw-parser-rule :C_OpName () 
  (:tuple (1 :C_Id))
  (SW_TO_C::make_C_OpName 1)) ; ok

;;; ========================================================================
;;;  TOP LEVEL
;;; ========================================================================

(define-sw-parser-rule :Toplevel ()	; toplevel needs to be anyof rule
  (:anyof (1 :Sections))
  (1))                                  ; semantics must be (1), not 1

(define-sw-parser-rule :Sections ()
  (:tuple (1 (:repeat* :Section)))
  1)

(define-sw-parser-rule :Section ()
  (:anyof :InclusionSection  :VerbatimSection :TranslateSection :NativeSection))

;;; ========================================================================
;;;  Inclusions
;;; ========================================================================

(define-sw-parser-rule :InclusionSection ()
  (:tuple "-include" (1 :Inclusions))
  (SW_TO_C::make_Inclusion_Section 1))

(define-sw-parser-rule :Inclusions ()
  (:repeat* :Inclusion))

(define-sw-parser-rule :Inclusion ()
  (:tuple (1 :DirectoryPath) (2 :FileName))
  (SW_TO_C::make_Inclusion-2 1 2))

(define-sw-parser-rule :DirectoryPath ()
  (:tuple "/" (1 (:repeat* :DirectoryName)))
  1)

(define-sw-parser-rule :DirectoryName ()
  (:tuple (1 :FileId) "/")
  1)

(define-sw-parser-rule :FileName ()
  (:tuple (1 :FileId) "." (2 :FileId))
  (SW_TO_C::make_FileName-2 1 2))

(define-sw-parser-rule :FileId ()
  (:tuple (1 :Symbol))
  (common-lisp::symbol-name (quote 1)))
  
;;; ========================================================================
;;;  Verbatim
;;; ========================================================================

(define-sw-parser-rule :VerbatimSection ()
  (:tuple (1 :Pragma))
  (SW_TO_C::make_Verbatim_Section-3 . 1))

;;; ========================================================================
;;;  Translations
;;; ========================================================================

(define-sw-parser-rule :TranslateSection ()
  (:tuple "-translate" (1 :Translations))
  (SW_TO_C::make_Translation_Section 1))

(define-sw-parser-rule :Translations ()
  (:repeat* :Translation))

(define-sw-parser-rule :Translation ()
  (:anyof :TypeTranslation 
          :FieldTranslation
          :OpTranslation))

;;; ========================================================================
;;; type rule:   Type -> Type
;;; ========================================================================

(define-sw-parser-rule :TypeTranslation ()
  (:tuple "type" (1 :SW_TypeName) "->" (2 :C_TypeName))
  (SW_TO_C::make_Type_Translation-2 1 2))  ; ok

;;; ========================================================================
;;; field rule:  Type,field -> Type.field
;;; ========================================================================

(define-sw-parser-rule :FieldTranslation ()
  (:tuple "field" (1 :SW_FieldRef) "->" (2 :C_FieldRef))
  (SW_TO_C::make_Field_Translation-2 1 2)) ; ok

(define-sw-parser-rule :SW_FieldRef ()
  (:tuple (1 :SW_TypeName) "." (2 :SW_FieldName))
  (SW_TO_C::make_SW_FieldRef-2 1 2)) ; ok

(define-sw-parser-rule :C_FieldRef ()
  (:tuple (1 :C_TypeName) "." (2 :C_FieldName))
  (SW_TO_C::make_C_FieldRef-2 1 2)) ; ok

;;; ========================================================================
;;; op rule:   Op -> Op
;;; ========================================================================

(define-sw-parser-rule :OpTranslation ()
  (:tuple "op" (1 :SW_OpName) "->" (2 :C_OpName))
  (SW_TO_C::make_Op_Translation-2 1 2)) ; ok

;;; ========================================================================
;;;  Natives
;;; ========================================================================

(define-sw-parser-rule :NativeSection ()
  (:tuple "-native" (1 :Natives))
  (SW_TO_C::make_Native_Section 1))

(define-sw-parser-rule :Natives ()
  (:repeat* :Native))

(define-sw-parser-rule :Native ()
  (:anyof :NativeType :NativeOp))

(define-sw-parser-rule :NativeType ()
  (:tuple "type" (1 :C_TypeName))
  (SW_TO_C::make_Type_Native 1))  ; ok

(define-sw-parser-rule :NativeOp ()
  (:tuple "op" (1 :C_TypeName))
  (SW_TO_C::make_Op_Native 1)) ; ok




