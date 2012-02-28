;;; -*- Mode: LISP; Package: Specware; Base: 10; Syntax: Common-Lisp -*-

(defpackage :SpecCalc (:use :COMMON-LISP-USER))
(defpackage :SCParser (:use :COMMON-LISP-USER))
(in-package :Parser4)

;;; ========================================================================
;;;
;;;  TODO: In doc: still refers to SW3
;;;  TODO: In doc: Change references to modules
;;;  TODO: In doc: Remove reference to spec-definition within a spec
;;;  TODO: In doc: import sc-term, not just spec-name
;;;  TODO: In doc: type-declaration now uses qualified name, not just name
;;;  TODO: In doc: type-definition now uses qualified name, not just name
;;;  TODO: In doc: op-declaration now uses qualified name, not just name
;;;  TODO: In doc: op-definition now uses qualified name, not just name
;;;  TODO: In doc: use "=", not :EQUALS in claim definition
;;;  TODO: In doc: type-quotient relation is expression, but that's ambiguous -- need tight-expression
;;;
;;; ========================================================================
;;;
;;;  TODO: In code: compare op-definition with doc
;;;  TODO: In code: We should add :record* as a parser production.
;;;  TODO: In code: Re-enable field selection
;;;
;;; ========================================================================
;;;
;;;  TODO: In doc and code: The syntax for naming axioms is pretty ugly
;;;
;;; ========================================================================
;;;
;;;  NOTE: :LOCAL-TYPE-VARIABLE as :CLOSED-TYPE       would introduce ambiguities, so we parse as :TYPE-REF          and post-process
;;;  NOTE: :LOCAL-VARIABLE      as :CLOSED-EXPRESSION would introduce ambiguities, so we parse as :ATOMIC-EXPRESSION and post-process
;;;
;;;  NOTE: We use normally use :NAME whereever the doc says :NAME,
;;;        but use :NAME-OR-EQUAL for op refs.
;;;
;;;  NOTE: "{}" is parsed directly as :UNIT-PRODUCT-TYPE,
;;;        but in the documentation, it's viewed as 0 entries in :TYPE-RECORD

;;; ========================================================================
;;;  Primitives
;;; ========================================================================

(define-sw-parser-rule :SYMBOL    () nil nil :documentation "Primitive")
(define-sw-parser-rule :STRING    () nil nil :documentation "Primitive")
(define-sw-parser-rule :NUMBER    () nil nil :documentation "Primitive")
(define-sw-parser-rule :CHARACTER () nil nil :documentation "Primitive")
(define-sw-parser-rule :PRAGMA    () nil nil :documentation "Primitive")

;;; These simplify life...

;;; The rationale for :NAME --
;;;
;;; If we were to use :SYMBOL everywhere in a rule, e.g.
;;;
;;; (define-sw-parser-rule :FOO ()
;;;   (:tuple "foo" (1 :SYMBOL) (2 :SYMBOL) (3 :SYMBOL))
;;;   (foo 1 2 3)
;;;
;;; then after substitutions we'd get lisp forms such as
;;;  (foo x y z)
;;; where the names x y z would be viewed as lisp variables.
;;;
;;; But if we use :NAME instead, e.g.:
;;;
;;; (define-sw-parser-rule :FOO ()
;;;   (:tuple "foo" (1 :NAME) (2 :NAME) (3 :NAME))
;;;   (foo 1 2 3)
;;;
;;; then after substitutions we'd get lisp forms such as
;;;  (foo "x" "y" "z")
;;; where "x", "y" "z" are the symbol-name's of the symbols x y z
;;;
;;; There might be simpler schemes, but this works well enough...

(define-sw-parser-rule :NAME ()
  (:anyof
   ((:tuple "answerVar")    "answerVar")
   ((:tuple "colimit")      "colimit")
   ((:tuple "diagram")      "diagram")
   ((:tuple "expand")       "expand")
   ((:tuple "export")       "export")
   ((:tuple "extendMorph")  "extendMorph")
   ((:tuple "hide")         "hide")
  ;((:tuple "is")           "is")
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
  ;((:tuple "slice")        "slice")
  ;((:tuple "globalize")    "globalize")
   ((:tuple (1 :SYMBOL))    (common-lisp::symbol-name (quote 1)))
   ))

(define-sw-parser-rule :EQUALS ()
  (:anyof "=" "is"))

;;; ========================================================================
;;; The first rules are those for the spec calculus. Such rules are all
;;; prefixed with SC-. It would be nice if the grammar could be factored
;;; but it may not be straightforward. For instance, imports refer to SC terms.
;;; ========================================================================

;;; ========================================================================
;;;  TOPLEVEL
;;; ========================================================================

(define-sw-parser-rule :TOPLEVEL ()	; toplevel needs to be anyof rule
  (:anyof
   (1 :SC-TOPLEVEL-TERM)
   (1 :SC-TOPLEVEL-DECLS))
  (1))

;; (:tuple (1 :FILE-DECLS))
;; (define-sw-parser-rule :FILE-DECLS ()
;;     (1 (:repeat :SC-DECL nil))
;;   1)

(define-sw-parser-rule :SC-TOPLEVEL-TERM ()
  (:tuple (1 :SC-TERM))
  (SCParser::mkToplevelTerm-3 1 ':left-lcb ':right-lcb))

(define-sw-parser-rule :SC-TOPLEVEL-DECLS ()
  (:tuple (1 :SC-DECLS))
  (SCParser::mkToplevelDecls-3 1 ':left-lcb ':right-lcb))

(define-sw-parser-rule :SC-DECLS ()
  (:repeat+ :SC-DECL nil))

(define-sw-parser-rule :SC-DECL ()
  (:tuple  (1 :NAME) :EQUALS (2 :SC-TERM))
  (SpecCalc::mkSCDecl-4 1 2 ':left-lcb ':right-lcb))

;;; ========================================================================
;;;  SC-TERM
;;; ========================================================================

(define-sw-parser-rule :SC-TERM ()
  ;; Factoring SC-TERM this way is a no-op here, but can make it a bit more 
  ;; convenient to describe certain gramamrs (e.g. Accord) that extend SC-TERM.
  (:anyof :SC-UNIT-ID
	  :SC-NON-UNIT-ID))

(define-sw-parser-rule :SC-NON-UNIT-ID ()
  (:anyof :SC-PARENTHESIZED-TERM
	  :SC-PRINT
	  :SC-SPEC ; was SPEC-DEFINITION
	  :SC-LET
	  :SC-WHERE
	  :SC-QUALIFY
	  :SC-TRANSLATE
	  :SC-SPEC-MORPH
	  ;; :SC-SHAPE
	  :SC-DIAG
	  :SC-COLIMIT
	  :SC-SUBSTITUTE
	  :SC-OP-REFINE
	  :SC-OP-TRANSFORM
	  ;; :SC-DIAG-MORPH
	  ;; :SC-DOM
	  ;; :SC-COD
	  ;; :SC-LIMIT
	  ;; :SC-APEX
	  :SC-GENERATE
	  :SC-OBLIGATIONS
	  :SC-PROVE
	  :SC-EXPAND
	  :SC-REDUCE

	  ;; ???
	  :SC-EXTEND
	  :SC-HIDE
	  :SC-EXPORT
	  ))

;;; ========================================================================
;;;  SC-PARENTHESIZED-TERM
;;; ========================================================================

(define-sw-parser-rule :SC-PARENTHESIZED-TERM ()
  (:tuple "(" (1 :SC-TERM) ")")
  1)

;;; ========================================================================
;;;  SC-PRINT
;;; ========================================================================

(define-sw-parser-rule :SC-PRINT ()
  (:tuple "print" (1 :SC-TERM))
  (make-sc-print 1 ':left-lcb ':right-lcb))

;;; ========================================================================
;;;  SC-UNIT-ID
;;; ========================================================================

;; The following does not correspond to URI syntax in RFC 2396. It is
;; not clear that it should. Perhaps, a UNIT-ID below should evaluate
;; to something of the form given in the RFC.

;; Because things come through the tokenizer, the rules below permit
;; white space between path elements and the white space is lost. We treat
;; ".." as a special path element. While it is supported in the RFC for
;; relative paths, it is not part of the standard UNIT-ID grammar.
;; It is used in the Specware source, though.

;; Maybe one day we will want network addresses.

(define-sw-parser-rule :SC-UNIT-ID ()
  (:anyof
   (1 :SC-ABSOLUTE-UNIT-ID)
   (1 :SC-RELATIVE-UNIT-ID))
  1)

(define-sw-parser-rule :SC-ABSOLUTE-UNIT-ID ()
  (:tuple "/" (1 :SC-UNIT-ID-PATH) (:optional (2 :FRAGMENT-ID)))
  (make-sc-absolute-unit-id 1 2 ':left-lcb ':right-lcb))

(define-sw-parser-rule :SC-RELATIVE-UNIT-ID ()
  (:tuple (1 :SC-UNIT-ID-PATH) (:optional (2 :FRAGMENT-ID)))
  (make-sc-relative-unit-id 1 2 ':left-lcb ':right-lcb))

(define-sw-parser-rule :FRAGMENT-ID ()
  (:tuple (1 :CHARACTER) (:optional (2 :NUMBER)) (:optional (3 :NAME)))
  (make-fragment-id 1 2 3 ':left-lcb ':right-lcb))

(define-sw-parser-rule :SC-UNIT-ID-PATH ()
  (:repeat+ :SC-UNIT-ID-ELEMENT "/"))

;; The following is a horrible hack. We want ".." as a path element
;; but the tokenizer treats "." as a special character. The way things
;; are below, one could put white space between successive "."'s.
;; Should really change things in the tokenizer.
(define-sw-parser-rule :SC-UNIT-ID-ELEMENT ()
  (:anyof
   ((:tuple (1 :NAME))             1)
   ((:tuple (1 :NUMBER-AS-STRING)) 1)	; e.g. ../foo/00/abc/..
   ((:tuple "..")                  "..")
   ))

;;; ========================================================================
;;;  SC-SPEC
;;;  http://www.specware.org/manual/html/modules.html
;;;  TODO: In doc: Change references to modules
;;; ========================================================================

(define-sw-parser-rule :SC-SPEC ()
  :SPEC-DEFINITION)

(define-sw-parser-rule :SPEC-DEFINITION () ; deprecate
  (:anyof
   (:tuple "spec" "{" (1 :DECLARATION-SEQUENCE) "}")
   (:tuple "spec"     (1 :DECLARATION-SEQUENCE) :END-SPEC))
  (make-sc-spec 1 ':left-lcb ':right-lcb))

(define-sw-parser-rule :END-SPEC ()
  (:anyof "end" "end-spec" "endspec"))

(define-sw-parser-rule :DECLARATION-SEQUENCE ()
  (:repeat* :DECLARATION nil))

;;; ========================================================================
;;;  DECLARATION
;;;  http://www.specware.org/manual/html/declarations.html
;;; ========================================================================

(define-sw-parser-rule :DECLARATION ()
  (:anyof
   (1 :IMPORT-DECLARATION)
   (1 :TYPE-DECLARATION)
   (1 :OP-DECLARATION)
   (1 :DEFINITION)
   (1 :PRAGMA-DECLARATION))
  1)

;;;  TODO: In doc: Remove reference to spec-definition within a spec
(define-sw-parser-rule :DEFINITION ()
  (:anyof
   (1 :TYPE-DEFINITION)
   (1 :OP-DEFINITION)
   (1 :CLAIM-DEFINITION))
  1)

;;; ------------------------------------------------------------------------
;;;  IMPORT-DECLARATION
;;; ------------------------------------------------------------------------

;;;  TODO: In doc: import sc-term, not just spec-name
(define-sw-parser-rule :IMPORT-DECLARATION ()
  (:tuple "import" (1 (:repeat+ :SC-TERM ",")))
  (make-import-declaration 1 ':left-lcb ':right-lcb))

;;; ------------------------------------------------------------------------
;;;  QUALIFIABLE-TYPE-NAME 
;;; ------------------------------------------------------------------------
(define-sw-parser-rule :QUALIFIABLE-TYPE-NAME ()
  (:anyof :UNQUALIFIED-TYPE-NAME :QUALIFIED-TYPE-NAME))

(define-sw-parser-rule :UNQUALIFIED-TYPE-NAME ()
  (1 :TYPE-NAME)
  (MetaSlang::mkUnQualifiedId 1))

(define-sw-parser-rule :QUALIFIED-TYPE-NAME ()
  (:tuple (1 :QUALIFIER) "." (2 :TYPE-NAME))
  (MetaSlang::mkQualifiedId-2 1 2))

(define-sw-parser-rule :QUALIFIER ()
  :NAME)

(define-sw-parser-rule :TYPE-NAME ()
  :NAME)

;;; ------------------------------------------------------------------------
;;;  QUALIFIABLE-OP-NAME 
;;; ------------------------------------------------------------------------

(define-sw-parser-rule :QUALIFIABLE-OP-NAME ()
  (:anyof :UNQUALIFIED-OP-NAME :QUALIFIED-OP-NAME))

(define-sw-parser-rule :UNQUALIFIED-OP-NAME ()
  (1 :OP-NAME)
  (MetaSlang::mkUnQualifiedId 1))

(define-sw-parser-rule :QUALIFIED-OP-NAME ()
  (:tuple (1 :QUALIFIER) "." (2 :OP-NAME))
  (MetaSlang::mkQualifiedId-2 1 2))

(define-sw-parser-rule :OP-NAME ()
  :NAME)

;;; ------------------------------------------------------------------------
;;;  QUALIFIABLE-CLAIM-NAME 
;;; ------------------------------------------------------------------------

(define-sw-parser-rule :QUALIFIABLE-CLAIM-NAME ()
  (:anyof :UNQUALIFIED-CLAIM-NAME :QUALIFIED-CLAIM-NAME))

(define-sw-parser-rule :UNQUALIFIED-CLAIM-NAME ()
  (:tuple (1 :CLAIM-NAME))
  (MetaSlang::mkUnQualifiedId 1))

(define-sw-parser-rule :QUALIFIED-CLAIM-NAME ()
  (:tuple (1 :QUALIFIER) "." (2 :CLAIM-NAME))
  (MetaSlang::mkQualifiedId-2 1 2))

(define-sw-parser-rule :CLAIM-NAME ()
  :NAME)

;;; ------------------------------------------------------------------------
;;;  TYPE-DECLARATION
;;; ------------------------------------------------------------------------

;;;  TODO: Fix doc: type-declaration now uses qualified name, not just name
(define-sw-parser-rule :TYPE-DECLARATION ()
  (:tuple :KW-TYPE (1 :QUALIFIABLE-TYPE-NAMES) (:optional (2 :FORMAL-TYPE-PARAMETERS)))
  (make-type-declaration 1 2 ':left-lcb ':right-lcb))

(define-sw-parser-rule :KW-TYPE ()
  (:anyof "sort" "type"))

(define-sw-parser-rule :FORMAL-TYPE-PARAMETERS ()
  ;; a little tricky.  Allow "X" "(X)" "(X,Y)" etc. but not "()"
  (:anyof :SINGLE-TYPE-VARIABLE :LOCAL-TYPE-VARIABLE-LIST))

(define-sw-parser-rule :SINGLE-TYPE-VARIABLE ()
  (1 :LOCAL-TYPE-VARIABLE)
  (list 1))				; e.g. "x" => (list "x")

(define-sw-parser-rule :LOCAL-TYPE-VARIABLE-LIST ()
  (:tuple "(" (1 (:repeat+ :LOCAL-TYPE-VARIABLE ",")) ")")
  1)					; e.g. ("x" "y" "z") => (list "x" "y" "z")

(define-sw-parser-rule :LOCAL-TYPE-VARIABLE ()
  :NAME)

;;; ------------------------------------------------------------------------
;;;  TYPE-DEFINITION
;;; ------------------------------------------------------------------------

;;;  TODO: In doc: type-definition now uses qualified name, not just name
(define-sw-parser-rule :TYPE-DEFINITION ()
  (:tuple :KW-TYPE (1 :QUALIFIABLE-TYPE-NAMES) (:optional (2 :FORMAL-TYPE-PARAMETERS)) :EQUALS (3 :TYPE-DEF-RHS))
  (make-type-definition 1 2 3 ':left-lcb ':right-lcb))

;;; ------------------------------------------------------------------------
;;;  OP-DECLARATION
;;; ------------------------------------------------------------------------

;;;  TODO: In doc: op-declaration now uses qualified name, not just name
(define-sw-parser-rule :OP-DECLARATION ()
  (:tuple "op" 
	  (:optional (3 :NEW-TYPE-VARIABLE-BINDER))
	  (1 :QUALIFIABLE-OP-NAMES) 
          (:optional (6 :FORMAL-PARAMETERS))
	  (:optional (2 :FIXITY)) 
	  ":" 
	  (:optional (4 :TYPE-VARIABLE-BINDER)) 
	  (5 :TYPE)
	  (:optional 
	   (:tuple "=" (7 :EXPRESSION))))
  ;; args to make-op-elem are: 
  ;;  1 qualifiable-op-names 
  ;;  2 optional-fixity 
  ;;  3 optional-pre-tvs 
  ;;  4 optional-post-tvs 
  ;;  5 optional-type 
  ;;  6 optional-params 
  ;;  7 optional-def 
  ;;  8 l 
  ;;  9 r
  (make-op-elem 1 2 3 4 5 6 7 :unspecified :unspecified ':left-lcb ':right-lcb))

(define-sw-parser-rule :FIXITY ()
  (:tuple (1 :ASSOCIATIVITY) (2 :PRIORITY))
  (make-fixity 1 2 ':left-lcb ':right-lcb))

#||
If we want the precedence to be optional:
(define-sw-parser-rule :FIXITY ()
  (:anyof
   ((:tuple "infixl" (:optional (1 :NAT-LITERAL))) (make-fixity :|Left| 1 ':left-lcb ':right-lcb))
   ((:tuple "infixr" (:optional (1 :NAT-LITERAL))) (make-fixity :|Left| 1 ':left-lcb ':right-lcb))))
||#

(define-sw-parser-rule :ASSOCIATIVITY ()
  (:anyof
   ((:tuple "infixl")  :|Left|)
   ((:tuple "infixr")  :|Right|)))

(define-sw-parser-rule :PRIORITY ()
  :NUMBER)				; we want a raw number here, not a :NAT-LITERAL

(define-sw-parser-rule :TYPE-VARIABLE-BINDER ()
  (:anyof 
   :OLD-TYPE-VARIABLE-BINDER  
   :NEW-TYPE-VARIABLE-BINDER ))

(define-sw-parser-rule :OLD-TYPE-VARIABLE-BINDER ()
  (:tuple "fa" (1 :LOCAL-TYPE-VARIABLE-LIST))
  1)

(define-sw-parser-rule :NEW-TYPE-VARIABLE-BINDER ()
  (:tuple "["  (1 (:repeat+ :LOCAL-TYPE-VARIABLE ",")) "]")
  1)

;;; ------------------------------------------------------------------------
;;;  OP-DEFINITION
;;; ------------------------------------------------------------------------

;;;  TODO: In doc: op-definition now uses qualified name, not just name
;;;  TODO: In code: compare op-definition with doc
(define-sw-parser-rule :OP-DEFINITION ()
  (:tuple (8 (:optional "refine"))
          "def"
          (:optional (3 :TYPE-VARIABLE-BINDER))
          (1 :QUALIFIABLE-OP-NAMES)
          (6 :FORMAL-PARAMETERS)
          (:optional (:tuple ":" (:optional (4 :TYPE-VARIABLE-BINDER)) (5 :TYPE)))
          (:optional
           (:anyof
            (:tuple "=" (7 :EXPRESSION))
            (:tuple "by" "{" (9 (:repeat* :TRANSFORM-EXPR ",")) "}"))))
  ;; args to make-op-elem are: 
  ;;  1 qualifiable-op-names 
  ;;  2 optional-fixity 
  ;;  3 optional-pre-tvs 
  ;;  4 optional-post-tvs 
  ;;  5 optional-type 
  ;;  6 optional-params 
  ;;  7 optional-def 
  ;;  8 l 
  ;;  9 r
  (make-op-elem 1 :unspecified 3 4 5 6 7 8 9 ':left-lcb ':right-lcb))

(define-sw-parser-rule :FORMAL-PARAMETERS ()
  (:repeat* :FORMAL-PARAMETER))

(define-sw-parser-rule :FORMAL-PARAMETER ()
  (:anyof :CLOSED-PATTERN :RESTRICTED-FORMAL-PATTERN))

(define-sw-parser-rule :RESTRICTED-FORMAL-PATTERN ()
  (:tuple "(" (1 :FORMAL-PATTERN) "|" (2 :EXPRESSION) ")")  
  (make-restricted-formal-pattern 1 2   ':left-lcb ':right-lcb) 
  :documentation "Restricted pattern")

(define-sw-parser-rule :FORMAL-PATTERN ()
  (:anyof
   ((:tuple (1 :PATTERN))                 1                                             :documentation "Single formal parameter")
   ((:tuple (1 (:repeat++ :PATTERN ","))) (make-tuple-pattern 1 ':left-lcb ':right-lcb) :documentation "Multiple formal parameters")
   ))
  

;;; ------------------------------------------------------------------------
;;;  CLAIM-DEFINITION
;;; ------------------------------------------------------------------------

;;;  TODO: In doc: use "=", not :EQUALS in claim definition
(define-sw-parser-rule :CLAIM-DEFINITION ()
  ;; :EQUALS would be too confusing. e.g. "axiom x = y" would mean "axiom named x is defined as y"
  (:tuple (1 :CLAIM-KIND) (2 :QUALIFIABLE-CLAIM-NAME) "is" (3 :CLAIM))
  (make-claim-definition 1 2 3 ':left-lcb ':right-lcb))

(define-sw-parser-rule :CLAIM-KIND ()
  (:anyof ((:tuple "axiom")       :|Axiom|)
          ((:tuple "theorem")     :|Theorem|)
          ((:tuple "conjecture")  :|Conjecture|)))

(define-sw-parser-rule :NUMBER-AS-STRING ()
  (:tuple (1 :NUMBER))
  (format nil "~D" 1))

(define-sw-parser-rule :CLAIM ()
  (:tuple (:optional (1 :TYPE-QUANTIFICATION)) (2 :EXPRESSION-NSWB)) ; "NSWB" means "Not starting with bracket"
  (cons 1 2))

(define-sw-parser-rule :TYPE-QUANTIFICATION ()
  (:anyof 
   :OLD-TYPE-QUANTIFICATION
   :NEW-TYPE-VARIABLE-BINDER))

(define-sw-parser-rule :OLD-TYPE-QUANTIFICATION ()
  (:tuple :KW-TYPE (1 :OLD-TYPE-VARIABLE-BINDER))
  1)

;;; ========================================================================
;;;   TYPE DECLARATION
;;;   http://www.specware.org/manual/html/types.html
;;; ========================================================================

(define-sw-parser-rule :TYPE-DEF-RHS () ; as in rhs of  T x = | A x | B x
  (:anyof
   ;; these are type abbreviations, not 
   (1 :TYPE-ABBREVIATION  :documentation "Type abbreviation") 
   (1 :RAW-SUBTYPE        :documentation "Subtype")         ; Allow unparenthesized subtype at top level: "Foo | q?"
   (1 :TYPE               :documentation "Function type")   ; All other types, including "(Foo | q?)"
   )
  1)

;;; ========================================================================
;;;   TYPE ABBREVIATION
;;;   A type abbreviation is not a true type -- it is syntax for declaring 
;;;   constructors, etc.
;;; ========================================================================

(define-sw-parser-rule :TYPE-ABBREVIATION () 
  ;; these are type abbreviations, not true types
  (:anyof
   (1 :SUM-TYPE          :documentation "Co-product type") ; "(| Foo Nat | Bar String)"
   (1 :RAW-SUM-TYPE      :documentation "Co-product type") ; "| Foo Nat | Bar String"
   (1 :QUOTIENT-TYPE     :documentation "Type quotient")   ; "(Foo / q?)"
   (1 :RAW-QUOTIENT-TYPE :documentation "Type quotient")   ; "Foo / q?"
   )
  1)

;;; ------------------------------------------------------------------------
;;;   SUM-TYPE  (Not a true type!)
;;; ------------------------------------------------------------------------
;;;   NOTE: SUM-TYPE is only an alternative for :TYPE-ABBREVIATION,
;;;         and cannot be used elsewhere.

(define-sw-parser-rule :SUM-TYPE ()
  (:tuple "(" (1 :RAW-SUM-TYPE) ")")
  1)

(define-sw-parser-rule :RAW-SUM-TYPE ()
  (:tuple (1 (:repeat+ :TYPE-SUMMAND nil)))
  (make-type-sum 1 ':left-lcb ':right-lcb))

(define-sw-parser-rule :TYPE-SUMMAND ()
  (:tuple "|" (1 :CONSTRUCTOR) (:optional (2 :SLACK-TYPE)))
  (make-type-summand 1 2 ':left-lcb ':right-lcb))

(define-sw-parser-rule :CONSTRUCTOR ()
  :NAME)

;;; ------------------------------------------------------------------------
;;;   QUOTIENT-TYPE  (Not a true type!)
;;; ------------------------------------------------------------------------
;;;   NOTE: QUOTIENT-TYPE is only an alternative for :TYPE-ABBREVIATION,
;;;         and cannot be used elsewhere.

(define-sw-parser-rule :QUOTIENT-TYPE ()
  (:tuple "(" (1 :RAW-QUOTIENT-TYPE) ")")
  1)

(define-sw-parser-rule :RAW-QUOTIENT-TYPE ()
  ;; TODO: [still relevant given above?] 
  ;;       In doc: type-quotient relation is expression, but that's ambiguous -- need tight-expression 
  (:tuple (1 :CLOSED-TYPE) "/" (2 :TIGHT-EXPRESSION)) ; CLOSED-EXPRESSION?
  (make-type-quotient 1 2 ':left-lcb ':right-lcb) :documentation "Quotient")

;;; ========================================================================
;;;   TYPE
;;;   http://www.specware.org/manual/html/types.html
;;; ========================================================================

(define-sw-parser-rule :TYPE () ; anywhere
  (:anyof
   (1 :TYPE-ARROW              :documentation "Function type")
   (1 :SLACK-TYPE              :documentation "Slack type")
   )
  1)

(define-sw-parser-rule :SLACK-TYPE ()
  (:anyof
   (1 :TYPE-PRODUCT            :documentation "Product type")
   (1 :TIGHT-TYPE              :documentation "Tight type")
   )
  1)

(define-sw-parser-rule :TIGHT-TYPE ()
  (:anyof
   (1 :TYPE-INSTANTIATION      :documentation "Type instantiation")
   (1 :CLOSED-TYPE             :documentation "Closed type -- unambiguous termination")
   )
  1)

(define-sw-parser-rule :CLOSED-TYPE ()
  (:anyof
   (1 :TYPE-REF                :documentation "Qualifiable type name") ; could refer to type or type variable
   (1 :TYPE-RECORD             :documentation "Type record")
   (1 :TYPE-RESTRICTION        :documentation "Type restriction")
   (1 :TYPE-COMPREHENSION      :documentation "Type comprehension")
   (1 :PARENTHESIZED-TYPE      :documentation "Parenthesized Type")
   )
  1)

;;; ------------------------------------------------------------------------
;;;   TYPE-ARROW
;;; ------------------------------------------------------------------------

(define-sw-parser-rule :TYPE-ARROW ()
  (:tuple (1 :ARROW-SOURCE) (:anyof "->" "\\_rightarrow") (2 :TYPE))
  (make-type-arrow 1 2 ':left-lcb ':right-lcb))

(define-sw-parser-rule :ARROW-SOURCE ()
  :SLACK-TYPE)

;;; ------------------------------------------------------------------------
;;;   TYPE-PRODUCT
;;; ------------------------------------------------------------------------

(define-sw-parser-rule :TYPE-PRODUCT ()
  (:tuple (1 (:repeat++ :TIGHT-TYPE (:anyof "*" "\\_times"))))
  (make-type-product 1 ':left-lcb ':right-lcb))

;;; ------------------------------------------------------------------------
;;;   TYPE-INSTANTIATION
;;; ------------------------------------------------------------------------

(define-sw-parser-rule :TYPE-INSTANTIATION ()
  ;; Don't use :TYPE-REF for first arg, since that could
  ;;  refer to type variables as well as types,
  ;;  which we don't want to allow here.
  (:tuple (1 :QUALIFIABLE-TYPE-NAME) (2 :ACTUAL-TYPE-PARAMETERS))
  (make-type-instantiation 1 2 ':left-lcb ':right-lcb))

(define-sw-parser-rule :ACTUAL-TYPE-PARAMETERS ()
  (:anyof
   ((:tuple (1 :CLOSED-TYPE))       (list 1))
   ((:tuple (1 :PROPER-TYPE-LIST))  1)
   ))

(define-sw-parser-rule :PROPER-TYPE-LIST ()
  (:tuple "(" (1 (:repeat++ :TYPE ",")) ")")
  1)

;;; ------------------------------------------------------------------------

(define-sw-parser-rule :QUALIFIABLE-TYPE-NAMES ()
  ;; "S"  "A.S"  "{S, A.X, Y}" etc.
  ;; "{S}" is same as "S"
  (:anyof 
   ((:tuple (1 :QUALIFIABLE-TYPE-NAME))                          (list 1))
   ((:tuple "{" (2 (:repeat+ :QUALIFIABLE-TYPE-NAME ",")) "}")   2)))

;;; ------------------------------------------------------------------------
;;;   TYPE-REF
;;; ------------------------------------------------------------------------

(define-sw-parser-rule :TYPE-REF ()
  (1 :QUALIFIABLE-TYPE-NAME)
  (make-type-ref 1 ':left-lcb ':right-lcb))

;;; ------------------------------------------------------------------------
;;;   TYPE-RECORD
;;; ------------------------------------------------------------------------

(define-sw-parser-rule :TYPE-RECORD ()
  (:anyof
   (1 :UNIT-PRODUCT-TYPE)
   (:tuple "{" (1 :FIELD-TYPE-LIST) "}"))
  1)

;;;  NOTE: "{}" is parsed directly as :UNIT-PRODUCT-TYPE,
;;;        but in the documentation, it's viewed as 0 entries in :TYPE-RECORD
;;;  TODO: In code: We should add :record* as a parser production.
(define-sw-parser-rule :UNIT-PRODUCT-TYPE ()
  (:anyof
   (:tuple "{" "}")
   (:tuple "(" ")"))
  (make-type-record  nil        ':left-lcb ':right-lcb) :documentation "Unit product")

(define-sw-parser-rule :FIELD-TYPE-LIST ()
  (1 (:repeat+ :FIELD-TYPE ","))
  (make-type-record  1 ':left-lcb ':right-lcb) :documentation "Record Type")

(define-sw-parser-rule :FIELD-TYPE ()
  (:tuple (1 :FIELD-NAME) ":" (2 :TYPE))
  (make-field-type 1 2 ':left-lcb ':right-lcb))

(define-sw-parser-rule :FIELD-NAME ()
  :NAME)

;;; ------------------------------------------------------------------------
;;;   TYPE-RESTRICTION
;;; ------------------------------------------------------------------------

(define-sw-parser-rule :TYPE-RESTRICTION ()
  ;; The multiple uses of "|" in the grammar complicates this rule.
  ;; E.g., without parens required here, type comprehension {x : Integer | f x}
  ;; could be parsed as a one-element field type with x of type (Integer | f x).
  ;; But with parens required here, that would need to be {x : (Integer | f x)}
  ;; to get that effect.
  (:tuple "(" (1 :RAW-SUBTYPE) ")")
  1)

(define-sw-parser-rule :RAW-SUBTYPE ()
  ;; This can also be used as a :TYPE-DEF-RHS
  (:tuple (1 :SLACK-TYPE) "|" (2 :EXPRESSION))
  (make-type-restriction 1 2 ':left-lcb ':right-lcb) :documentation "Subtype")

;;; ------------------------------------------------------------------------
;;;   TYPE-COMPREHENSION
;;; ------------------------------------------------------------------------

(define-sw-parser-rule :TYPE-COMPREHENSION ()
  (:tuple "{" (1 :ANNOTATED-PATTERN) "|" (2 :EXPRESSION) "}")
  (make-type-comprehension 1 2 ':left-lcb ':right-lcb) :documentation "Type comprehension")

;;; ------------------------------------------------------------------------
;;;   PARENTHESIZED-TYPE
;;; ------------------------------------------------------------------------

(define-sw-parser-rule :PARENTHESIZED-TYPE ()
  (:tuple "(" (1 :TYPE) ")")
  1)

;;; ========================================================================
;;;   EXPRESSION
;;;   http://www.specware.org/manual/html/expressions.html
;;; ========================================================================


(define-sw-parser-rule :EXPRESSION ()
  (:anyof
   (1 :LAMBDA-FORM          :documentation "Function definition")
   (1 :CASE-EXPRESSION      :documentation "Case")
   (1 :THE-EXPRESSION       :documentation "Iota")
   (1 :LET-EXPRESSION       :documentation "Let")
   (1 :IF-EXPRESSION        :documentation "If-then-else")
   (1 :QUANTIFICATION       :documentation "Quantification (fa/ex/ex1)")
   (1 :ANNOTATED-EXPRESSION :documentation "Annotated (i.e. typed) expression")
   (1 :TIGHT-EXPRESSION     :documentation "Tight expression -- suitable for annotation")
   )
  1)

(define-sw-parser-rule :EXPRESSION-NSWB ()
  (:anyof
   (1 :LAMBDA-FORM          :documentation "Function definition")
   (1 :CASE-EXPRESSION      :documentation "Case")
   (1 :THE-EXPRESSION       :documentation "Iota")
   (1 :LET-EXPRESSION       :documentation "Let")
   (1 :IF-EXPRESSION        :documentation "If-then-else")
   (1 :QUANTIFICATION       :documentation "Quantification (fa/ex/ex1)")
   (1 :ANNOTATED-EXPRESSION :documentation "Annotated (i.e. typed) expression")
   (1 :TIGHT-EXPRESSION-NSWB :documentation "Tight expression -- suitable for annotation -- not starting with '['")
   )
  1)

(define-sw-parser-rule :NON-BRANCH-EXPRESSION ()
  (:anyof
   (1 :NON-BRANCH-THE-EXPRESSION  :documentation "Iota not ending in case or lambda")
   (1 :NON-BRANCH-LET-EXPRESSION  :documentation "Let not ending in case or lambda")
   (1 :NON-BRANCH-IF-EXPRESSION   :documentation "If-then-else not ending in case or lambda")
   (1 :NON-BRANCH-QUANTIFICATION  :documentation "Quantification (fa/ex/ex1) not ending in case or lambda")
   (1 :ANNOTATED-EXPRESSION       :documentation "Annotated (i.e. typed) expression")
   (1 :TIGHT-EXPRESSION           :documentation "Tight expression -- suitable for annotation")
   )
  1)

(define-sw-parser-rule :TIGHT-EXPRESSION ()
  (:anyof
   (1 :APPLICATION          :documentation "Application")
   (1 :CLOSED-EXPRESSION    :documentation "Closed expression -- unambiguous termination")
   )
  1)

(define-sw-parser-rule :TIGHT-EXPRESSION-NSWB ()
  (:anyof
   (1 :APPLICATION-NSWB          :documentation "Application not starting with bracket")
   (1 :CLOSED-EXPRESSION-NSWB    :documentation "Closed expression -- unambiguous termination -- not starting with '['")
   )
  1)

;;;  UNQUALIFIED-OP-REF is outside SELECTABLE-EXPRESSION to avoid ambiguity with "A.B.C"
;;;   being both SELECT (C, TWO-NAME-EXPRESSION (A,B))
;;;          and SELECT (C, SELECT (B, UNQUALIFIED-OP-REF A))
;;;  "X . SELECTOR" will be parsed as TWO-NAME-EXPRESSION and be disambiguated in post-processing
(define-sw-parser-rule :CLOSED-EXPRESSION ()
  (:anyof
   (1 :CLOSED-EXPRESSION-NSWB)
   (1 :LIST-DISPLAY           :documentation "List") ; starts with left bracket
   )
  1)

(define-sw-parser-rule :CLOSED-EXPRESSION-NSWB ()
  (:anyof
   (1 :BUILT-IN-OPERATOR      :documentation "&&, ||, =>, <=>, =, ~=, <<, ::")
   (1 :UNQUALIFIED-OP-REF     :documentation "Op reference or Variable reference")
   (1 :SELECTABLE-EXPRESSION  :documentation "Closed expression -- unambiguous termination, not starting with [")
   )
  1)

;;;  NOTE: An expressions such as A.B is a three-way ambiguous selectable-expression :
;;;         OpRef (Qualified (A,B))
;;;         Select (B, OpRef (Qualified (unqualified, A)))
;;;         Select (B, VarRef A)
;;;        So we parse as TWO-NAME-EXPRESSION and resolve in post-processing.

(define-sw-parser-rule :SELECTABLE-EXPRESSION ()
  (:anyof
   (1 :TWO-NAME-EXPRESSION        :documentation "Reference to op or var, or selection")  ; resolve in post-processing  (name     . name)
   ;; (1 :QUALIFIED-OP-REF        :documentation "Qualified reference to op")             ; see TWO-NAME-EXPRESSION
   (1 :NAT-FIELD-SELECTION        :documentation "Selection from name using Nat")         ; see TWO-NAME-EXPRESSION     (name     . nat)
   (1 :FIELD-SELECTION            :documentation "Selection from non-name")               ; see TWO-NAME-EXPRESSION     (non-name . name)
   ;;
   (1 :LITERAL                    :documentation "Literal: Boolean, Nat, Character, String")
   (1 :TUPLE-DISPLAY              :documentation "Tuple")
   (1 :RECORD-DISPLAY             :documentation "Record")
   (1 :SEQUENTIAL-EXPRESSION      :documentation "Sequence of expressions")
   (1 :STRUCTOR                   :documentation "Project, Embed, etc.")
   (1 :PARENTHESIZED-EXPRESSION   :documentation "Parenthesized expression")
   (1 :MONAD-EXPRESSION           :documentation "Monadic expression")
   )
  1)

;;; ------------------------------------------------------------------------
;;;   BUILT-IN-OPERATOR 
;;; ------------------------------------------------------------------------

;;; Note: If a dot follows, this production will become a dead-end,
;;;       since dot is not legal after a TIGHT-EXPRESSION,
;;;       but the competing TWO-NAME-EXPRESSION may succeed.

(define-sw-parser-rule :BUILT-IN-OPERATOR ()
  (:anyof 
   ;; "~" is treated specially: see semantics.lisp
   ;; "~" refers to the built-in Not, but "foo.~" is just an ordinary operator,
   ;; so we don't make "~" a keyword (which would exclude the latter)
   ((:tuple "&")                 (make-bool-fun '(:|And|)     ':left-lcb ':right-lcb)) ; deprecated
   ((:tuple "&&")                (make-bool-fun '(:|And|)     ':left-lcb ':right-lcb))
   ((:tuple "\\_and")            (make-bool-fun '(:|And|)     ':left-lcb ':right-lcb))
   ((:tuple "||")                (make-bool-fun '(:|Or|)      ':left-lcb ':right-lcb))
   ((:tuple "\\_or")             (make-bool-fun '(:|Or|)      ':left-lcb ':right-lcb))
   ((:tuple "=>")                (make-bool-fun '(:|Implies|) ':left-lcb ':right-lcb))
   ((:tuple "\\_Rightarrow")     (make-bool-fun '(:|Implies|) ':left-lcb ':right-lcb))
   ((:tuple "<=>")               (make-bool-fun '(:|Iff|)     ':left-lcb ':right-lcb))
   ((:tuple "\\_Leftrightarrow") (make-bool-fun '(:|Iff|)     ':left-lcb ':right-lcb))
   ;;
   ;; "=" is treated specially: see semantics.lisp
   ;; "=" refers to the built-in Equals, but can also appear as a keyword in other rules
   ;; ((:tuple "=")              (make-equality-fun '(:|Equals|)    ':left-lcb ':right-lcb))
   ((:tuple "~=")                (make-equality-fun '(:|NotEquals|) ':left-lcb ':right-lcb))
   ((:tuple "\\_noteq")          (make-equality-fun '(:|NotEquals|) ':left-lcb ':right-lcb))
   ((:tuple "<<")                (make-fun          '(:|RecordMerge|) (freshMetaTypeVar ':left-lcb ':right-lcb) ':left-lcb ':right-lcb))
   ((:tuple "\\_guillemotleft")  (make-fun          '(:|RecordMerge|) (freshMetaTypeVar ':left-lcb ':right-lcb) ':left-lcb ':right-lcb))
   ((:tuple "::")                (make-unqualified-op-ref "Cons" ':left-lcb ':right-lcb))
   ))

;;; ------------------------------------------------------------------------
;;;   UNQUALIFIED-OP-REF
;;; ------------------------------------------------------------------------

;;; Note: If a dot follows, this production will become a dead-end,
;;;       since dot is not legal after a TIGHT-EXPRESSION,
;;;       but the competing TWO-NAME-EXPRESSION may succeed.
(define-sw-parser-rule :UNQUALIFIED-OP-REF ()
  (:anyof
   ;; so we can use "="  in expressions, e.g "A = B"
   ((:tuple "=")        (make-equality-fun       '(:|Equals|) ':left-lcb ':right-lcb))
   ((:tuple (1 :NAME))  (make-unqualified-op-ref 1            ':left-lcb ':right-lcb))
   ))

;;; ------------------------------------------------------------------------
;;;   NAME-DOT-NAME
;;; ------------------------------------------------------------------------

;;; Note: Without the dot, this production fails,
;;;       but the competing UNQUALIFIED-OP-REF may succeed.
(define-sw-parser-rule :TWO-NAME-EXPRESSION ()
  (:tuple (1 :NAME) "." (2 :NAME))
  (make-two-name-expression 1 2 ':left-lcb ':right-lcb))

;;; ------------------------------------------------------------------------
;;;   LAMBDA-FORM
;;; ------------------------------------------------------------------------

(define-sw-parser-rule :LAMBDA-FORM ()
  (:tuple (:anyof "fn" "\\_lambda") (1 :MATCH))
  (make-lambda-form 1 ':left-lcb ':right-lcb)
  :documentation "Lambda abstraction")

;;; ------------------------------------------------------------------------
;;;   CASE-EXPRESSION
;;; ------------------------------------------------------------------------

(define-sw-parser-rule :CASE-EXPRESSION ()
  (:tuple "case" (1 :EXPRESSION) "of" (2 :MATCH))
  (make-case-expression 1 2 ':left-lcb ':right-lcb)
  :documentation "Case statement")

;;; ------------------------------------------------------------------------
;;;   LET-EXPRESSION
;;; ------------------------------------------------------------------------

(define-sw-parser-rule :LET-EXPRESSION ()
  (:anyof
   ((:tuple "let" (1 :RECLESS-LET-BINDING)      "in" (2 :EXPRESSION)) (make-let-binding-term     1 2 ':left-lcb ':right-lcb) :documentation "Let Binding")
   ((:tuple "let" (1 :REC-LET-BINDING-SEQUENCE) "in" (2 :EXPRESSION)) (make-rec-let-binding-term 1 2 ':left-lcb ':right-lcb) :documentation "RecLet Binding")
   ))

(define-sw-parser-rule :NON-BRANCH-LET-EXPRESSION () ; as above, but not ending with "| .. -> .."
  (:anyof
   ((:tuple "let" (1 :RECLESS-LET-BINDING)      "in" (2 :NON-BRANCH-EXPRESSION)) (make-let-binding-term     1 2 ':left-lcb ':right-lcb) :documentation "Let Binding")
   ((:tuple "let" (1 :REC-LET-BINDING-SEQUENCE) "in" (2 :NON-BRANCH-EXPRESSION)) (make-rec-let-binding-term 1 2 ':left-lcb ':right-lcb) :documentation "RecLet Binding")
   ))

(define-sw-parser-rule :RECLESS-LET-BINDING ()
  (:tuple (1 :PATTERN) :EQUALS (2 :EXPRESSION))
  (make-recless-let-binding 1 2 ':left-lcb ':right-lcb))

(define-sw-parser-rule :REC-LET-BINDING-SEQUENCE ()
  (:repeat+ :REC-LET-BINDING nil))

(define-sw-parser-rule :REC-LET-BINDING ()
  (:tuple "def" (1 :NAME) (2 :FORMAL-PARAMETER-SEQUENCE) (:optional (:tuple ":" (3 :TYPE))) :EQUALS (4 :EXPRESSION))
  (make-rec-let-binding 1 2 3 4 ':left-lcb ':right-lcb))

(define-sw-parser-rule :FORMAL-PARAMETER-SEQUENCE ()
  (:repeat+ :FORMAL-PARAMETER ""))

;;; ------------------------------------------------------------------------
;;;   IF-EXPRESSION
;;; ------------------------------------------------------------------------

(define-sw-parser-rule :IF-EXPRESSION ()
  (:tuple "if" (1 :EXPRESSION) "then" (2 :EXPRESSION) "else" (3 :EXPRESSION))
  (make-if-expression 1 2 3 ':left-lcb ':right-lcb)  :documentation "If-Then-Else")

(define-sw-parser-rule :NON-BRANCH-IF-EXPRESSION () ; as above, but not ending with "| .. -> .."
  (:tuple "if" (1 :EXPRESSION) "then" (2 :EXPRESSION) "else" (3 :NON-BRANCH-EXPRESSION))
  (make-if-expression 1 2 3 ':left-lcb ':right-lcb)  :documentation "If-Then-Else")

;;; ------------------------------------------------------------------------
;;;   THE-EXPRESSION
;;; ------------------------------------------------------------------------

(define-sw-parser-rule :THE-EXPRESSION ()
  (:tuple "the" "(" (1 :ANNOTATED-VARIABLE) ")" (2 :EXPRESSION))
  (make-the 1 2 ':left-lcb ':right-lcb)
  :documentation "Iota")

(define-sw-parser-rule :NON-BRANCH-THE-EXPRESSION () ; as above, but not ending with "| .. -> .."
  (:tuple "the" "(" (1 :ANNOTATED-VARIABLE) ")" (2 :NON-BRANCH-EXPRESSION))
  (make-the 1 2 ':left-lcb ':right-lcb)
  :documentation "Iota")

;;; ------------------------------------------------------------------------
;;;   QUANTIFICATION
;;; ------------------------------------------------------------------------

(define-sw-parser-rule :QUANTIFICATION ()
  (:tuple (1 :QUANTIFIER) (2 :LOCAL-VARIABLE-LIST) (3 :EXPRESSION))
  (make-quantification 1 2 3 ':left-lcb ':right-lcb)
  :documentation "Quantification")

(define-sw-parser-rule :NON-BRANCH-QUANTIFICATION () ; as above, but not ending with "| .. -> .."
  (:tuple (1 :QUANTIFIER) (2 :LOCAL-VARIABLE-LIST) (3 :NON-BRANCH-EXPRESSION))
  (make-quantification 1 2 3 ':left-lcb ':right-lcb)
  :documentation "Quantification")

(define-sw-parser-rule :QUANTIFIER ()
  (:anyof
   ((:tuple (:anyof "fa" "\\_forall"))  forall-op)
   ((:tuple (:anyof "ex" "\\_exists"))  exists-op)
   ((:tuple "ex1") exists1-op)))

(define-sw-parser-rule :LOCAL-VARIABLE-LIST ()
  (:tuple "(" (1 (:repeat+ :ANNOTATED-VARIABLE ",")) ")")
  (make-local-variable-list 1 ':left-lcb ':right-lcb))

(define-sw-parser-rule :ANNOTATED-VARIABLE ()
  (:tuple (1 :LOCAL-VARIABLE) (:optional (:tuple ":" (2 :TYPE))))
  (make-annotated-variable 1 2 ':left-lcb ':right-lcb))

(define-sw-parser-rule :LOCAL-VARIABLE ()
  :NAME)

;;; ------------------------------------------------------------------------
;;;   ANNOTATED-EXPRESSION
;;; ------------------------------------------------------------------------

(define-sw-parser-rule :ANNOTATED-EXPRESSION ()
  ;;  "P : S1 : S2" is legal,  meaning P is of type S1, which is also of type S2
  (:tuple (1 :TIGHT-EXPRESSION) ":" (2 :TYPE))
  (make-annotated-expression 1 2 ':left-lcb ':right-lcb)
  :documentation "Annotated term")

;;; ------------------------------------------------------------------------

(define-sw-parser-rule :QUALIFIABLE-OP-NAMES ()
  ;; "f"  "A.f"  "{f, A.g, h}" etc.
  ;; "{f}" is same as "f"
  (:anyof 
   ((:tuple (1 :QUALIFIABLE-OP-NAME))
    (list 1))
   ((:tuple "{"
	    (2 (:repeat+ :QUALIFIABLE-OP-NAME ","))
	    "}")
    2)))

;;; ------------------------------------------------------------------------
;;;   APPLICATION
;;; ------------------------------------------------------------------------

;;; Application is greatly complicated by the possibility of infix operators,
;;; overloading, type inference, etc.  See the description of Applications
;;; in http://www.specware.org/manual/html/expressions.html
;;;
;;; :APPLICATION        ::= :PREFIX-APPLICATION | :INFIX-APPLICATION
;;; :PREFIX-APPLICATION ::= :APPLICATION-HEAD :ACTUAL-PARAMETER
;;; :APPLICATION-HEAD   ::= :CLOSED-EXPRESSION | :PREFIX-APPLICATION
;;; :ACTUAL-PARAMETER   ::= :CLOSED-EXPRESSION
;;; :INFIX-APPLICATION  ::= :ACTUAL-PARAMETER :QUALIFIABLE-OP-NAME :ACTUAL-PARAMETER
;;;
;;; Note that if "P N Q" (e.g. "P + Q") reduces to
;;;  :CLOSED-EXPRESSION :QUALIFIABLE-OP-NAME :CLOSED-EXPRESSION
;;; then it can be reduced
;;;  => :INFIX-APPLICATION                                     [ (+ P Q)   ]
;;; or
;;;  => :APPLICATION-HEAD :ACTUAL-PARAMETER :ACTUAL-PARAMETER  [ P + Q     ]
;;;  => :PREFIX-APPLICATION :ACTUAL-PARAMETER                  [ (P +) Q   ]
;;;  => :APPLICATION-HEAD :ACTUAL-PARAMETER                    [ (P +) Q   ]
;;;  => :PREFIX-APPLICATION                                    [ ((P +) Q) ]
;;;
;;; Also, "P M Q N R" might parse as "(P M Q) N R" or "P M (Q N R)",
;;; depending on precedences of M and N.
;;; For now, the parser here does not have access to the necessary information
;;; to resolve such things, so the disambiguation is done in a post-processing
;;; phase.  See <sw>/meta-slang/infix.sl

(define-sw-parser-rule :APPLICATION ()
  (:tuple (1 :CLOSED-EXPRESSION) (2 :CLOSED-EXPRESSIONS)) ;  (:optional (:tuple ":" (3 :TYPE)))
  (make-application 1 2 ':left-lcb ':right-lcb) ; see notes above
  :documentation "Application")

(define-sw-parser-rule :APPLICATION-NSWB  ()
  (:tuple (1 :CLOSED-EXPRESSION-NSWB) (2 :CLOSED-EXPRESSIONS)) ;  (:optional (:tuple ":" (3 :TYPE)))
  (make-application 1 2 ':left-lcb ':right-lcb) ; see notes above
  :documentation "Application")



(define-sw-parser-rule :CLOSED-EXPRESSIONS ()
  (:repeat+ :CLOSED-EXPRESSION))

;;; ------------------------------------------------------------------------
;;;   LITERAL
;;; ------------------------------------------------------------------------

(define-sw-parser-rule :LITERAL ()
  (:anyof
   :BOOLEAN-LITERAL
   :NAT-LITERAL
   :CHAR-LITERAL
   :STRING-LITERAL))

(define-sw-parser-rule :BOOLEAN-LITERAL ()
  (:anyof
   ((:tuple "true")  (make-boolean-literal t   ':left-lcb ':right-lcb))
   ((:tuple "false") (make-boolean-literal nil ':left-lcb ':right-lcb))
   ))

(define-sw-parser-rule :NAT-LITERAL ()
  (1 :NAT)				; A sequence of digits -- see lexer for details
  (make-nat-literal 1 ':left-lcb ':right-lcb))

(define-sw-parser-rule :NAT () :NUMBER)	; more explicit synonym

(define-sw-parser-rule :CHAR-LITERAL ()
  (1 :CHARACTER)			; see lexer for details, should be same as in following comment
  (make-char-literal 1 ':left-lcb ':right-lcb))

;;; :CHAR-LITERAL        ::= #:CHAR-LITERAL-GLYPH
;;; :CHAR-LITERAL-GLYPH  ::= :CHAR-GLYPH | "
;;; :CHAR-GLYPH          ::= :LETTER | :DECIMAL-DIGIT | :OTHER-CHAR-GLYPH
;;; :OTHER-CHAR-GLYPH    ::=  ! | : | @ | # | $ | % | ^ | & | * | ( | ) | _ | - | + | =
;;;                         | | | ~ | ` | . | , | < | > | ? | / | ; | ' | [ | ] | { | }
;;;                         | \\ | \"
;;;                         | \a | \b | \t | \n | \v | \f | \r | \s
;;;                         | \x :HEXADECIMAL-DIGIT :HEXADECIMAL-DIGIT
;;;  :HEXADECIMAL-DIGIT  ::= :DECIMAL-DIGIT | a | b | c | d | e | f | A | B | C | D | E | F

(define-sw-parser-rule :STRING-LITERAL ()
  (1 :STRING)				; see lexer for details, should be same as in following comment
  (make-string-literal 1 ':left-lcb ':right-lcb))

;;; :STRING-LITERAL         ::= " :STRING-BODY "
;;; :STRING-BODY            ::= { :STRING-LITERAL-GLYPH }*
;;; :STRING-LTIERAL-GLYPH   ::= :CHAR-GLYPH | :SIGNIFICANT-WHITESPACE
;;; :SIGNIFICANT-WHITESPACE ::= space | tab | newline

;;; ------------------------------------------------------------------------
;;;   FIELD-SELECTION
;;; ------------------------------------------------------------------------

(define-sw-parser-rule :FIELD-SELECTION ()
  (:tuple (1 :SELECTABLE-EXPRESSION) "." (2 :FIELD-SELECTOR))
  (make-field-selection 2 1 ':left-lcb ':right-lcb))  ;; fix

(define-sw-parser-rule :NAT-FIELD-SELECTION ()
  (:tuple (1 :UNQUALIFIED-OP-REF) "." (2 :NAT-SELECTOR))
  (make-field-selection 2 1 ':left-lcb ':right-lcb))

(define-sw-parser-rule :NAT-SELECTOR ()
  (1 :NAT)
  (make-nat-selector 1 ':left-lcb ':right-lcb))

(define-sw-parser-rule :FIELD-SELECTOR ()
  (:anyof
   ((:tuple (1 :NAT))         (make-nat-selector        1 ':left-lcb ':right-lcb))
   ((:tuple (1 :FIELD-NAME))  (make-field-name-selector 1 ':left-lcb ':right-lcb))
   ))

;;; ------------------------------------------------------------------------
;;;  TUPLE-DISPLAY
;;; ------------------------------------------------------------------------

(define-sw-parser-rule :TUPLE-DISPLAY ()
  (:tuple "(" (:optional (1 :TUPLE-DISPLAY-BODY)) ")")
  (make-tuple-display 1 ':left-lcb ':right-lcb)
  :documentation "Tuple")

(define-sw-parser-rule :TUPLE-DISPLAY-BODY ()
  (:repeat++ :EXPRESSION ","))

;;; ------------------------------------------------------------------------
;;;  RECORD-DISPLAY
;;; ------------------------------------------------------------------------

(define-sw-parser-rule :RECORD-DISPLAY ()
  (:tuple "{" (1 :RECORD-DISPLAY-BODY) "}")
  1
  :documentation "Record")

(define-sw-parser-rule :RECORD-DISPLAY-BODY ()
  (1 (:repeat* :FIELD-FILLER ","))
  (make-record-display 1 ':left-lcb ':right-lcb)
  :documentation "Record")

(define-sw-parser-rule :FIELD-FILLER ()
  (:tuple (1 :FIELD-NAME) "=" (2 :EXPRESSION))
  (make-field-filler 1 2 ':left-lcb ':right-lcb))

;;; ------------------------------------------------------------------------
;;;  SEQUENTIAL-EXPRESSION
;;; ------------------------------------------------------------------------

(define-sw-parser-rule :SEQUENTIAL-EXPRESSION ()
  (:tuple "(" (1 :OPEN-SEQUENTIAL-EXPRESSION) ")")
  1
  :documentation "Sequence")

(define-sw-parser-rule :OPEN-SEQUENTIAL-EXPRESSION ()
  ;;    we collect here as "(void ; void ; void) ; expr"
  ;; but will interpret as "void ; (void ; (void ; expr))"
  (:tuple (1 (:repeat+ :VOID-EXPRESSION ";")) ";" (2 :EXPRESSION))
  (make-sequential-expression 1 2 ':left-lcb ':right-lcb) ; fix semantics
  :documentation "Sequence")

(define-sw-parser-rule :VOID-EXPRESSION ()
  (1 :EXPRESSION)
  1)

;;; ------------------------------------------------------------------------
;;;  LIST-DISPLAY
;;; ------------------------------------------------------------------------

(define-sw-parser-rule :LIST-DISPLAY ()
  (:tuple "[" (1 :LIST-DISPLAY-BODY) "]")
  (make-list-display 1 ':left-lcb ':right-lcb) :documentation "List")

(define-sw-parser-rule :LIST-DISPLAY-BODY ()
  (:repeat* :EXPRESSION ","))

;;; ------------------------------------------------------------------------
;;;  STRUCTOR
;;; ------------------------------------------------------------------------

(define-sw-parser-rule :STRUCTOR ()
  (:anyof
   :PROJECTOR
   :QUOTIENTER
   :CHOOSER
   :EMBEDDER
   :EMEBDDING-TEST))

;;; ------------------------------------------------------------------------

(define-sw-parser-rule :PROJECTOR ()
  (:anyof
   ((:tuple "project" (1 :NAT))        (make-nat-selector        1 ':left-lcb ':right-lcb) :documentation "Projection")
   ((:tuple "project" (1 :FIELD-NAME)) (make-field-name-selector 1 ':left-lcb ':right-lcb) :documentation "Projection")))

(define-sw-parser-rule :QUOTIENTER ()
  (:tuple "quotient" "[" (1 :QUALIFIABLE-TYPE-NAME) "]")
  (make-quotienter 1  ':left-lcb ':right-lcb)
  :documentation "Quotient")

(define-sw-parser-rule :CHOOSER ()
  (:tuple "choose" "[" (1 :QUALIFIABLE-TYPE-NAME) "]")
  (make-chooser 1  ':left-lcb ':right-lcb)
  :documentation "Choice")

(define-sw-parser-rule :EMBEDDER ()
  ;; (:tuple (:optional "embed") (1 :CONSTRUCTOR))
  (:tuple "embed" (1 :CONSTRUCTOR))
  (make-embedder 1 ':left-lcb ':right-lcb)
  :documentation "Embedding")

(define-sw-parser-rule :EMEBDDING-TEST ()
  (:tuple "embed?"  (1 :CONSTRUCTOR))
  (make-embedding-test 1 ':left-lcb ':right-lcb)
  :documentation "Embedding Test")

;;; ------------------------------------------------------------------------

(define-sw-parser-rule :PARENTHESIZED-EXPRESSION ()
  (:tuple "(" (1 :EXPRESSION) ")")
  (make-nonfix 1))

;;; ------------------------------------------------------------------------
;;;   MONAD-EXPRESSION
;;; ------------------------------------------------------------------------

(define-sw-parser-rule :MONAD-EXPRESSION ()
  (:anyof
   :MONAD-TERM-EXPRESSION
   :MONAD-BINDING-EXPRESSION
   ))

(define-sw-parser-rule :MONAD-TERM-EXPRESSION ()
  (:tuple "{" (1 :EXPRESSION) ";" (2 :MONAD-STMT-LIST) "}")
  (make-monad-term-expression 1 2 ':left-lcb ':right-lcb)
  :documentation "Monadic sequence")

(define-sw-parser-rule :LEFT-ARROW ()
  (:anyof "<-" "\\_leftarrow"))

(define-sw-parser-rule :MONAD-BINDING-EXPRESSION ()
  (:tuple "{" (1 :PATTERN) :LEFT-ARROW (2 :EXPRESSION) ";" (3 :MONAD-STMT-LIST) "}")
  (make-monad-binding-expression 1 2 3 ':left-lcb ':right-lcb)
  :documentation "Monadic binding")

(define-sw-parser-rule :MONAD-STMT-LIST ()
  (:anyof
   ((:tuple (1 :EXPRESSION)) 1)
   ((:tuple (1 :EXPRESSION) ";" (2 :MONAD-STMT-LIST))
    (make-monad-term-expression    1 2   ':left-lcb ':right-lcb))
   ((:tuple (1 :PATTERN) :LEFT-ARROW (2 :EXPRESSION) ";" (3 :MONAD-STMT-LIST))
    (make-monad-binding-expression 1 2 3 ':left-lcb ':right-lcb))
   ))

;;; ========================================================================
;;;  MATCH
;;;  http://www.specware.org/manual/html/matchesandpatterns.html
;;; ========================================================================

;;(define-sw-parser-rule :MATCH ()
;;  (:tuple (:optional "|") (1 (:repeat :BRANCH "|")))
;;  (list . 1))

(define-sw-parser-rule :MATCH ()
  (:tuple (:optional "|") (1 :AUX-MATCH))
  1)

(define-sw-parser-rule :AUX-MATCH ()
  (:anyof
   ((:tuple (1 :NON-BRANCH-BRANCH) "|" (2 :AUX-MATCH)) (cons 1 2))
   ((:tuple (1 :BRANCH))                               (cons 1 nil))
   ))

(define-sw-parser-rule :BRANCH ()
  (:tuple (1 :TOP-PATTERN) (:anyof "->" "\\_rightarrow") (2 :EXPRESSION))
  (make-branch 1 2 ':left-lcb ':right-lcb))

(define-sw-parser-rule :NON-BRANCH-BRANCH () ; as above, but not ending with "| .. -> .."
  ;; i.e., a branch that doesn't end in a branch
  (:tuple (1 :TOP-PATTERN) (:anyof "->" "\\_rightarrow") (2 :NON-BRANCH-EXPRESSION))
  (make-branch 1 2 ':left-lcb ':right-lcb))

;;; ========================================================================
;;;  PATTERN
;;;  http://www.specware.org/manual/html/matchesandpatterns.html
;;; ========================================================================

(define-sw-parser-rule :TOP-PATTERN ()
  (:anyof
   :PATTERN
   :RESTRICTED-PATTERN))

(define-sw-parser-rule :PATTERN ()
  (:anyof
   :ANNOTATED-PATTERN
   :TIGHT-PATTERN))

(define-sw-parser-rule :TIGHT-PATTERN ()
  (:anyof
   :ALIASED-PATTERN
   :CONS-PATTERN
   :EMBED-PATTERN
   :QUOTIENT-PATTERN
   :CLOSED-PATTERN))

(define-sw-parser-rule :CLOSED-PATTERN ()
  (:anyof
   :VARIABLE-PATTERN
   :WILDCARD-PATTERN
   :LITERAL-PATTERN
   :LIST-PATTERN
   :TUPLE-PATTERN
   :RECORD-PATTERN
   :PARENTHESIZED-PATTERN))

;;; ------------------------------------------------------------------------

(define-sw-parser-rule :ANNOTATED-PATTERN ()
  (:tuple (1 :PATTERN) ":" (2 :TYPE))                            (make-annotated-pattern  1 2   ':left-lcb ':right-lcb) :documentation "Annotated Pattern")

(define-sw-parser-rule :ALIASED-PATTERN   ()
  (:tuple (1 :VARIABLE-PATTERN) "as" (2 :TIGHT-PATTERN))         (make-aliased-pattern    1 2   ':left-lcb ':right-lcb) :documentation "Aliased pattern")

(define-sw-parser-rule :CONS-PATTERN ()
  (:tuple (1 :CLOSED-PATTERN) "::" (2 :TIGHT-PATTERN))           (make-cons-pattern       1 2   ':left-lcb ':right-lcb) :documentation "CONS pattern")

(define-sw-parser-rule :EMBED-PATTERN ()
  (:tuple (1 :CONSTRUCTOR) (2 :CLOSED-PATTERN))                  (make-embed-pattern      1 2   ':left-lcb ':right-lcb) :documentation "Embed pattern")

(define-sw-parser-rule :QUOTIENT-PATTERN ()
  (:tuple "quotient" "[" (1 :QUALIFIABLE-TYPE-NAME) "]" (2 :TIGHT-PATTERN))  (make-quotient-pattern   1 2   ':left-lcb ':right-lcb) :documentation "Quotient pattern")

(define-sw-parser-rule :RESTRICTED-PATTERN ()
  (:tuple (1 :TIGHT-PATTERN) "|" (2 :EXPRESSION))                (make-restricted-pattern 1 2   ':left-lcb ':right-lcb) :documentation "Restricted pattern")

(define-sw-parser-rule :VARIABLE-PATTERN ()
  (1 :LOCAL-VARIABLE)                                            (make-variable-pattern   1     ':left-lcb ':right-lcb) :documentation "Variable pattern")

(define-sw-parser-rule :WILDCARD-PATTERN ()
  (:tuple "_")                                                   (make-wildcard-pattern         ':left-lcb ':right-lcb) :documentation "Wildcard pattern")

(define-sw-parser-rule :LITERAL-PATTERN ()
  (:anyof
   ((:tuple "true")                                              (make-boolean-pattern    't    ':left-lcb ':right-lcb) :documentation "Boolean Pattern")
   ((:tuple "false")                                             (make-boolean-pattern    'nil  ':left-lcb ':right-lcb) :documentation "Boolean Pattern")
   ((:tuple (1 :NAT))                                            (make-nat-pattern        1     ':left-lcb ':right-lcb) :documentation "Nat Pattern")
   ((:tuple (1 :CHARACTER))                                      (make-char-pattern       1     ':left-lcb ':right-lcb) :documentation "Char Pattern")
   ((:tuple (1 :STRING))                                         (make-string-pattern     1     ':left-lcb ':right-lcb) :documentation "String Pattern")
   ))

(define-sw-parser-rule :LIST-PATTERN ()
  (:tuple "[" (1 (:repeat* :PATTERN ",")) "]")                   (make-list-pattern       1     ':left-lcb ':right-lcb) :documentation "List enumeration")

(define-sw-parser-rule :TUPLE-PATTERN ()
  (:anyof
   ((:tuple "(" ")")                                             (make-tuple-pattern      ()    ':left-lcb ':right-lcb) :documentation "Empty tuple pattern")
   ;; "(X)" not allowed, just "()" "(X,Y)" "(X,Y,Z)" ...
   ((:tuple "(" (1 (:repeat++ :PATTERN ",")) ")")                (make-tuple-pattern      1     ':left-lcb ':right-lcb) :documentation "Tuple pattern")
   ))

(define-sw-parser-rule :RECORD-PATTERN ()
  ;; allow "( }" ??
  (:tuple "{" (1 (:repeat+ :FIELD-PATTERN ",")) "}")             (make-record-pattern     1     ':left-lcb ':right-lcb) :documentation "Record pattern")

(define-sw-parser-rule :FIELD-PATTERN ()
  (:tuple (1 :FIELD-NAME) (:optional (:tuple "=" (2 :PATTERN))))
  (make-field-pattern 1 2 ':left-lcb ':right-lcb)
  :documentation "Unstructured record element")

(define-sw-parser-rule :PARENTHESIZED-PATTERN ()
  (:tuple "(" (1 :PATTERN) ")")                                  1                                                     :documentation "Parenthesized pattern")

;;; ------------------------------------------------------------------------
;;;  PRAGMA-DECLARATION
;;; ------------------------------------------------------------------------

(define-sw-parser-rule :PRAGMA-DECLARATION ()
  (1 :PRAGMA)
  (make-pragma (quote 1) ':left-lcb ':right-lcb))

;;; ========================================================================
;;;  SC-LET
;;;  SC-WHERE
;;;  These refer to names for specs, etc.
;;;  E.g.  let SET = /a/b/c in spec import SET ... end-spec
;;; ========================================================================

(define-sw-parser-rule :SC-LET ()
  (:tuple "let" (1 :SC-DECLS) "in" (2 :SC-TERM))
  (make-sc-let 1 2 ':left-lcb ':right-lcb))

;; The "where" is experimental. The semantics of "t where decls end" is the
;; same as "let decls in t"

(define-sw-parser-rule :SC-WHERE ()
  (:tuple (2 :SC-TERM) "where" "{" (1 :SC-DECLS) "}")
  (make-sc-where 1 2 ':left-lcb ':right-lcb))

;;; ========================================================================
;;;  SC-QUALIFY
;;; ========================================================================

(define-sw-parser-rule :SC-QUALIFY ()
  (:tuple (1 :QUALIFIER) "qualifying" (2 :SC-TERM))
  (make-sc-qualify 1 2 ':left-lcb ':right-lcb))

;;; ------------------------------------------------------------------------
;;;  TYPE REF
;;; ------------------------------------------------------------------------

(define-sw-parser-rule :SC-TYPE-REF ()
  ;; When we know it must be a type ref...
  ;; "[A.]X" "([A.]X)", but X cannot be "="
  (:anyof 
   ((:tuple     (1 :QUALIFIABLE-TYPE-NAME)     )  1) ; "[A.]f"  
   ((:tuple "(" (1 :QUALIFIABLE-TYPE-NAME) ")" )  1) ; "([A.]f)"
   ))

;;; ------------------------------------------------------------------------
;;;  OP REF
;;; ------------------------------------------------------------------------

(define-sw-parser-rule :SC-OP-REF ()
  ;; When we know it must be an op ref...
  ;; "[A,]f", "([A,]f)", "[A.]f : <type>", "([A.]f : <type>)"
  (:anyof 
   ((:tuple     (1 :SC-OP-REF-AUX)     )  1) ; "[A.]f"  
   ((:tuple "(" (1 :SC-OP-REF-AUX) ")" )  1) ; "([A.]f)"
   ))

(define-sw-parser-rule :SC-OP-REF-AUX ()
  ;; "[A,]f", "([A,]f)", "[A.]f : <type>", "([A.]f : <type>)"
  (:anyof 
   :SC-UNANNOTATED-OP-REF
   :SC-ANNOTATED-OP-REF))

(define-sw-parser-rule :SC-UNANNOTATED-OP-REF ()
  ;; When we know it must be an op ref...
  ;; "[A.]f"
  (1 :QUALIFIABLE-OP-NAME) 
  (make-sc-unannotated-op-ref 1 ':left-lcb ':right-lcb))

(define-sw-parser-rule :SC-ANNOTATED-OP-REF ()
  ;; This can only be an op ref...
  ;; "[A.]f : <type>"
  (:tuple (1 :QUALIFIABLE-OP-NAME) ":" (2 :TYPE))
  (make-sc-annotated-op-ref 1 2 ':left-lcb ':right-lcb))

;;; ------------------------------------------------------------------------
;;;  CLAIM REF
;;; ------------------------------------------------------------------------

(define-sw-parser-rule :SC-CLAIM-REF ()
  ;; When we know it must be a claim ref...
  ;; "[A.]X" "([A.]X)", but X cannot be "="
  (:anyof 
   ((:tuple     (1 :QUALIFIABLE-CLAIM-NAME)     )  1) ; "[A.]f"  
   ((:tuple "(" (1 :QUALIFIABLE-CLAIM-NAME) ")" )  1) ; "([A.]f)"
   ))

;;; ------------------------------------------------------------------------
;;;  AMBIGUOUS REF
;;; ------------------------------------------------------------------------

(define-sw-parser-rule :SC-AMBIGUOUS-REF ()
  ;; When we're not sure if its a type/op/axiom ref...
  ;; "X"  "A.X"  "(X)"  "(A.X)"
  ;; We assume that semantic routines will disambiguate as an OP-REF if X is "="
  (:anyof 
   ((:tuple     (1 :QUALIFIABLE-AMBIGUOUS-NAME)     )  1) ; "[A.]f"  
   ((:tuple "(" (1 :QUALIFIABLE-AMBIGUOUS-NAME) ")" )  1) ; "([A.]f)"
   ))

;;; ------------------------------------------------------------------------
;;;  QUALIFIABLE-AMBIGUOUS-NAME (might refer to type/op/axiom)
;;; ------------------------------------------------------------------------

(define-sw-parser-rule :QUALIFIABLE-AMBIGUOUS-NAME ()
  ;; might be type or op name, but will be of the form XXX or QQQ.XXX
  (:anyof :UNQUALIFIED-AMBIGUOUS-NAME :QUALIFIED-AMBIGUOUS-NAME))

(define-sw-parser-rule :UNQUALIFIED-AMBIGUOUS-NAME ()
  (:anyof
   ((:tuple (1 :NAME)) (MetaSlang::mkUnQualifiedId 1))
   ((:tuple "_")       (MetaSlang::mkUnQualifiedId "_"))
   ))

(define-sw-parser-rule :QUALIFIED-AMBIGUOUS-NAME ()
  (:anyof
   ((:tuple (1 :QUALIFIER) "." (2 :NAME)) (MetaSlang::mkQualifiedId-2 1 2))
   ((:tuple (1 :QUALIFIER) "." "_")       (MetaSlang::mkQualifiedId-2 1 "_"))
   ))

;;; ========================================================================
;;;  SC-TRANSLATE
;;; ========================================================================

(define-sw-parser-rule :SC-TRANSLATE ()
  (:tuple "translate" (1 :SC-TERM) "by" (2 :SC-TRANSLATE-EXPR))
  (make-sc-translate 1 2 ':left-lcb ':right-lcb))

(define-sw-parser-rule :SC-TRANSLATE-EXPR ()
  ;; Right now a translation is just a name mapping. Later we may
  ;; provide support for matching patterns
  (:tuple "{" (1 :SC-TRANSLATE-RULES) "}")
  (make-sc-translate-expr 1 ':left-lcb ':right-lcb))

(define-sw-parser-rule :SC-TRANSLATE-RULES ()
  (:repeat* :SC-TRANSLATE-RULE ",")
  ;;   (make-sc-translate-rules 1)
  )

(define-sw-parser-rule :SC-TRANSLATE-RULE ()
  ;; (:tuple (1 :QUALIFIABLE-OP-NAME) :MAPS-TO (2 :QUALIFIABLE-OP-NAME))
  ;; (make-sc-translate-rule 1 2 ':left-lcb ':right-lcb))
  (:anyof 
   ((:tuple :KW-TYPE (1 :SC-TYPE-REF)       :MAPS-TO (2 :SC-TYPE-REF))          (make-sc-type-rule      1 2 ':left-lcb ':right-lcb))
   ((:tuple "op"     (1 :SC-OP-REF)         :MAPS-TO (2 :SC-OP-REF))            (make-sc-op-rule        1 2 ':left-lcb ':right-lcb))
   ;; ?? axiom/thoerem/conjecture ??
   ;; Without an explicit "type" or "op" keyword, 
   ;;  if either side is annotated, this is an op rule:
   ((:tuple        (1 :SC-ANNOTATED-OP-REF) :MAPS-TO (2 :SC-OP-REF))            (make-sc-op-rule        1 2 ':left-lcb ':right-lcb))
   ((:tuple        (1 :SC-ANNOTATED-OP-REF) :MAPS-TO (2 :SC-ANNOTATED-OP-REF))  (make-sc-op-rule        1 2 ':left-lcb ':right-lcb))
   ((:tuple        (1 :SC-OP-REF)           :MAPS-TO (2 :SC-ANNOTATED-OP-REF))  (make-sc-op-rule        1 2 ':left-lcb ':right-lcb))
   ;; Otherwise, it's probably ambiguous (semantic routine will notice that "=" must be an op):
   ((:tuple        (1 :SC-AMBIGUOUS-REF)    :MAPS-TO (2 :SC-AMBIGUOUS-REF))     (make-sc-ambiguous-rule 1 2 ':left-lcb ':right-lcb))
   ))

(define-sw-parser-rule :MAPS-TO ()
  (:tuple (:anyof "+->" "\\_mapsto")))

;;; ========================================================================
;;;  SC-SPEC-MORPH
;;; ========================================================================

(define-sw-parser-rule :SC-SPEC-MORPH ()
  (:tuple "morphism" (1 :SC-TERM) (:anyof "->" "\\_rightarrow") (2 :SC-TERM) "{" (3 :SC-SPEC-MORPH-RULES) "}"
	  (4 (:repeat* :SM-PRAGMA)))
  (make-sc-spec-morph 1 2 3 4 ':left-lcb ':right-lcb)
  )

(define-sw-parser-rule :SM-PRAGMA ()
  (1 :PRAGMA)
  (make-sm-pragma (quote 1) ':left-lcb ':right-lcb))

(define-sw-parser-rule :SC-SPEC-MORPH-RULES ()
  (:repeat* :SC-SPEC-MORPH-RULE ","))

(define-sw-parser-rule :SC-SPEC-MORPH-RULE ()
  ;; (:tuple (1 :QUALIFIABLE-OP-NAME) :MAPS-TO (2 :QUALIFIABLE-OP-NAME))
  ;; (make-sc-spec-morph-rule 1 2 ':left-lcb ':right-lcb))
  (:anyof 
   ((:tuple :KW-TYPE (1 :SC-TYPE-REF)       :MAPS-TO (2 :SC-TYPE-REF))          (make-sm-type-rule      1 2 ':left-lcb ':right-lcb))
   ((:tuple "op"     (1 :SC-OP-REF)         :MAPS-TO (2 :SC-OP-REF))            (make-sm-op-rule        1 2 ':left-lcb ':right-lcb))
   ;; ?? axiom/thoerem/conjecture ??
   ;; Without an explicit "type" or "op" keyword, 
   ;;  if either side is annotated, this is an op rule:
   ((:tuple        (1 :SC-ANNOTATED-OP-REF) :MAPS-TO (2 :SC-OP-REF))            (make-sm-op-rule        1 2 ':left-lcb ':right-lcb))
   ((:tuple        (1 :SC-ANNOTATED-OP-REF) :MAPS-TO (2 :SC-ANNOTATED-OP-REF))  (make-sm-op-rule        1 2 ':left-lcb ':right-lcb))
   ((:tuple        (1 :SC-OP-REF)           :MAPS-TO (2 :SC-ANNOTATED-OP-REF))  (make-sm-op-rule        1 2 ':left-lcb ':right-lcb))
   ;; Otherwise, it's probably ambiguous (semantic routine will notice that "=" must be an op):
   ((:tuple        (1 :SC-AMBIGUOUS-REF)    :MAPS-TO (2 :SC-AMBIGUOUS-REF))     (make-sm-ambiguous-rule 1 2 ':left-lcb ':right-lcb))
   ))

;;; ========================================================================
;;;  SC-SHAPE
;;; ========================================================================

;;; ========================================================================
;;;  SC-DIAG
;;; ========================================================================

(define-sw-parser-rule :SC-DIAG ()
  (:tuple "diagram" "{" (1 (:repeat* :SC-DIAG-ELEM ",")) "}")
  (make-sc-diag 1 ':left-lcb ':right-lcb))

(define-sw-parser-rule :SC-DIAG-ELEM ()
  (:anyof
   (1 :SC-DIAG-NODE)
   (1 :SC-DIAG-EDGE))
  1)

(define-sw-parser-rule :SC-DIAG-NODE ()
  (:tuple (1 :NAME) :MAPS-TO (2 :SC-TERM))
  (make-sc-diag-node 1 2 ':left-lcb ':right-lcb))

(define-sw-parser-rule :SC-DIAG-EDGE ()
  (:tuple (1 :NAME) ":" (2 :NAME) (:anyof "->" "\\_rightarrow") (3 :NAME) :MAPS-TO (4 :SC-TERM))
  (make-sc-diag-edge 1 2 3 4 ':left-lcb ':right-lcb))

;;; ========================================================================
;;;  SC-COLIMIT
;;; ========================================================================

(define-sw-parser-rule :SC-COLIMIT ()
  (:tuple "colimit" (1 :SC-TERM))
  (make-sc-colimit 1 ':left-lcb ':right-lcb))

;;; ========================================================================
;;;  SC-SUBSTITUTE
;;; ========================================================================
(define-sw-parser-rule :SC-SUBSTITUTE ()
  (:tuple (1 :SC-TERM) "[" (2 :SC-TERM) "]")
  (make-sc-substitute 1 2 ':left-lcb ':right-lcb))

;;; ========================================================================
;;;  SC-OP-REFINE
;;; ========================================================================
(define-sw-parser-rule :SC-OP-REFINE ()
  (:tuple "refine" (1 :SC-TERM) "by" "{"
	  (2 (:repeat+ (:anyof :OP-DEFINITION
			       :OP-DECLARATION
                               :TYPE-DECLARATION
                               :TYPE-DEFINITION
                               :CLAIM-DEFINITION
                               :PRAGMA-DECLARATION) nil)) "}")
  (make-sc-op-refine 1 2 ':left-lcb ':right-lcb))

;;; ========================================================================
;;;  SC-OP-TRANSFORM
;;; ========================================================================
(define-sw-parser-rule :SC-OP-TRANSFORM ()
  (:tuple "transform" (1 :SC-TERM) "by" "{"
	  (2 (:repeat* :TRANSFORM-EXPR ",")) "}")
  (make-sc-transform 1 2 ':left-lcb ':right-lcb))

(define-sw-parser-rule :TRANSFORM-EXPR ()
  (:anyof
   ((:tuple (1 :NUMBER))                     (make-transform-number    1   ':left-lcb ':right-lcb))
   ((:tuple (1 :STRING))                     (make-transform-string    1   ':left-lcb ':right-lcb))
   ((:tuple (1 :NAME))                       (make-transform-name      1   ':left-lcb ':right-lcb))
   ((:tuple "true")                          (make-transform-boolean   t   ':left-lcb ':right-lcb))
   ((:tuple "false")                         (make-transform-boolean   nil ':left-lcb ':right-lcb))
   ((:tuple "UID" (1 :SC-UNIT-ID))           (make-transform-scterm    1   ':left-lcb ':right-lcb))
   ((:tuple (1 :NAME) "." (2 :NAME))         (make-transform-qual      1 2 ':left-lcb ':right-lcb))
   ((:tuple (1 :NAME) (2 :TRANSFORM-EXPR))   (make-transform-item      1 2 ':left-lcb ':right-lcb))

   ;; slice (spec, ops, types)
   ((:tuple "slice" 
            (:optional (:tuple "from"
                               (:tuple "{" (1 (:repeat* :QUALIFIABLE-OP-NAME   ",")) "}")
                               (:tuple "{" (2 (:repeat* :QUALIFIABLE-TYPE-NAME ",")) "}")))
            (:optional (:tuple "stopping_at"
                               (:tuple "{" (3 (:repeat* :QUALIFIABLE-OP-NAME   ",")) "}")
                               (:tuple "{" (4 (:repeat* :QUALIFIABLE-TYPE-NAME ",")) "}"))))
    (make-transform-slice 1 2 3 4 ':left-lcb ':right-lcb))

   ;; globalize (type, global-var-name, op-that-initializes-global)
   ((:tuple "globalize" "(" (1 :QUALIFIABLE-OP-NAMES) ","  ; roots
                            (2 :QUALIFIABLE-TYPE-NAME) "," ; global type
                            (3 :QUALIFIABLE-OP-NAME)       ; global var of global type
                            (:optional (:tuple "," (4 :QUALIFIABLE-OP-NAME))) ; possibly named initializer
                        ")")
    (make-transform-globalize 1 2 3 4 ':left-lcb ':right-lcb))

   ((:tuple (1 :TRANSFORM-EXPR)
	    "(" (2 (:repeat* :TRANSFORM-EXPR-ARG ",")) ")")
    (make-transform-apply 1 2 ':left-lcb ':right-lcb))
   ((:tuple (1 :TRANSFORM-EXPR)
	    "[" (2 (:repeat* :TRANSFORM-EXPR-ARG ",")) "]")
    (make-transform-apply-options 1 2 ':left-lcb ':right-lcb))
   ((:tuple (1 :TRANSFORM-EXPR)
	    "{" (2 (:repeat* :TRANSFORM-RECORD-PAIR ",")) "}")
    (make-transform-apply-record 1 2 ':left-lcb ':right-lcb))))

(define-sw-parser-rule :TRANSFORM-EXPR-ARG ()
  (:anyof
   ((:tuple (1 :TRANSFORM-EXPR)) 1)
   ((:tuple "(" (1 (:repeat* :TRANSFORM-EXPR-ARG ",")) ")")
    (make-transform-tuple 1 ':left-lcb ':right-lcb))))

(define-sw-parser-rule :TRANSFORM-RECORD-PAIR ()
  (:tuple (1 :NAME) ":" (2 :TRANSFORM-EXPR-ARG))
  (cons 1 2))

;;; ========================================================================
;;;  SC-DIAG-MORPH
;;; ========================================================================

;;; ========================================================================
;;;  SC-DOM
;;;  SC-COD
;;; ========================================================================

;;; ========================================================================
;;;  SC-LIMIT
;;;  SC-APEX
;;; ========================================================================

;;; ========================================================================
;;;  SC-GENERATE
;;; ========================================================================

(define-sw-parser-rule :SC-GENERATE ()
  (:tuple "generate" (1 :NAME) (2 :SC-TERM) 
	  (:optional 
	   (:anyof
	    (:tuple "in" (3 :STRING))
	    (:tuple "with" (3 :NAME-AS-STRING))
	    )
	   ))
  (make-sc-generate 1 2 3 ':left-lcb ':right-lcb))

(define-sw-parser-rule :NAME-AS-STRING ()
  (:tuple (1 :NAME))
  (string 1))

;;; ========================================================================
;;;  SC-OBLIGATIONS
;;; ========================================================================

(define-sw-parser-rule :SC-OBLIGATIONS ()
  (:tuple "obligations" (1 :SC-TERM))
  (make-sc-obligations 1 ':left-lcb ':right-lcb))

;;; ========================================================================
;;;  SC-PROVE
;;; ========================================================================

(define-sw-parser-rule :SC-PROVE ()
  (:tuple "prove" (1 :PROVER-CLAIM) "in" (2 :SC-TERM)
	  (:optional (:tuple "with"       (3 :PROVER-NAME)))
	  (:optional (:tuple "using"      (4 :PROVER-ASSERTIONS)))
	  (:optional (:tuple "options"    (5 :PROVER-OPTIONS)))
	  (:optional (:tuple "answerVar"  (7 :ANSWER-VARIABLE))))
  (make-sc-prover 1 2 3 4 5 7 ':left-lcb ':right-lcb))

(define-sw-parser-rule :PROVER-CLAIM ()
  ;; WELLFORMED is a :QUALIFIABLE-CLAIM-NAME that will be handled specially by semantics...
  :QUALIFIABLE-CLAIM-NAME)

(define-sw-parser-rule :PROVER-NAME ()
  ;; semantics will check for legal name among "Snark" "PVS" "FourierM" "Checker"
  :STRING)

(define-sw-parser-rule :PROVER-ASSERTIONS ()
  ;; "ALL" is a :QUALIFIABLE-CLAIM-NAME that will be handled specially by semantics
  (:repeat+ :QUALIFIABLE-CLAIM-NAME ","))

(define-sw-parser-rule :PROVER-OPTIONS ()
  (:anyof
   ((:tuple (1 :STRING))               (make-sc-prover-options-from-string 1)) ; returns (:|OptionString| <sexpressions>) or (:|Error| msg string)
   ((:tuple (1 :QUALIFIABLE-OP-NAME))  (cons :|OptionName| 1))
   ))

;;(define-sw-parser-rule :PROVER-BASE-OPTIONS ()
;;  (:anyof "NONE" "BASE")
;;   )

(define-sw-parser-rule :ANSWER-VARIABLE ()
  (:tuple (1 :ANNOTATED-VARIABLE))
  (make-sc-answerVar 1))


;;; ========================================================================
;;;  SC-EXPAND
;;; ========================================================================

(define-sw-parser-rule :SC-EXPAND ()
  (:tuple "expand" (1 :SC-TERM))
  (make-sc-expand 1 ':left-lcb ':right-lcb))

;;; ========================================================================
;;;  SC-REDUCE
;;; ========================================================================

(define-sw-parser-rule :SC-REDUCE ()
  (:tuple "reduce" (1 :TIGHT-EXPRESSION) "in" (2 :SC-TERM))
  (make-sc-reduce 1 2 ':left-lcb ':right-lcb))

;;; ========================================================================
;;;  SC-EXTEND
;;; ========================================================================

(define-sw-parser-rule :SC-EXTEND ()
  (:tuple "extendMorph" (1 :SC-TERM))
  (make-sc-extend 1 ':left-lcb ':right-lcb))

;;; ========================================================================
;;;  SC-HIDE
;;;  SC-EXPORT
;;; ========================================================================

(define-sw-parser-rule :SC-HIDE ()
  (:tuple "hide" "{" (1 :SC-DECL-REFS) "}" "in" (2 :SC-TERM))
  (make-sc-hide 1 2 ':left-lcb ':right-lcb))

(define-sw-parser-rule :SC-EXPORT ()
  (:tuple "export" "{" (1 :SC-DECL-REFS) "}" "from" (2 :SC-TERM))
  (make-sc-export 1 2 ':left-lcb ':right-lcb))

;; Right now we simply list the names to hide or export. Later
;; we might provide some type of expressions or patterns
;; that match sets of identifiers.
;; (define-sw-parser-rule :SC-NAME-EXPR ()
;;   (:tuple "{" (1 (:optional :QUALIFIABLE-AMBIGUOUS-NAME-LIST)) "}")
;; (list . 1))

(define-sw-parser-rule :SC-DECL-REFS ()
  (:repeat* :SC-DECL-REF ","))

(define-sw-parser-rule :SC-DECL-REF ()
  (:anyof 
   ((:tuple :KW-TYPE        (1 :SC-TYPE-REF))          (make-sc-type-ref      1 ':left-lcb ':right-lcb))
   ((:tuple "op"            (1 :SC-OP-REF))            (make-sc-op-ref        1 ':left-lcb ':right-lcb))
   ((:tuple (1 :CLAIM-KIND) (2 :SC-CLAIM-REF))         (make-sc-claim-ref     1 2 ':left-lcb ':right-lcb))
   ;; Without an explicit "type" or "op" keyword, if ref is annotated, its an op ref:
   ((:tuple                 (1 :SC-ANNOTATED-OP-REF))  (make-sc-op-ref        1 ':left-lcb ':right-lcb))
   ;; Otherwise, it's probably ambiguous (semantic routine will notice that "=" must be an op):
   ((:tuple                 (1 :SC-AMBIGUOUS-REF))     (make-sc-ambiguous-ref 1 ':left-lcb ':right-lcb))
   ))

