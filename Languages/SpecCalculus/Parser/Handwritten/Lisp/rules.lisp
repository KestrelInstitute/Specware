;;; -*- Mode: LISP; Package: Specware; Base: 10; Syntax: Common-Lisp -*-

(in-package "PARSER4")

;;; ========================================================================
;;;
;;;  TODO: In doc: still refers to SW3
;;;  TODO: In doc: Change references to modules
;;;  TODO: In doc: Remove reference to spec-definition within a spec
;;;  TODO: In doc: import sc-term, not just spec-name
;;;  TODO: In doc: sort-declaration now uses qualified name, not just name
;;;  TODO: In doc: sort-definition now uses qualified name, not just name
;;;  TODO: In doc: op-declaration now uses qualified name, not just name
;;;  TODO: In doc: op-definition now uses qualified name, not just name
;;;  TODO: In doc: use "=", not :EQUALS in claim definition
;;;  TODO: In doc: sort-quotient relation is expression, but that's ambiguous -- need tight-expression
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
;;;  NOTE: :LOCAL-SORT-VARIABLE as :CLOSED-SORT       would introduce ambiguities, so we parse as :SORT-REF          and post-process
;;;  NOTE: :LOCAL-VARIABLE      as :CLOSED-EXPRESSION would introduce ambiguities, so we parse as :ATOMIC-EXPRESSION and post-process
;;;
;;;  NOTE: We use normally use :NAME whereever the doc says :NAME,
;;;        but use :NON-KEYWORD-NAME instead for :SORT-NAME and :LOCAL-VARIABLE
;;;
;;;  NOTE: "{}" is parsed directly as :UNIT-PRODUCT-SORT,
;;;        but in the documentation, it's viewed as 0 entries in :SORT-RECORD

;;; ========================================================================
;;;  Primitives
;;; ========================================================================

(define-sw-parser-rule :SYMBOL    () nil nil :documentation "Primitive")
(define-sw-parser-rule :STRING    () nil nil :documentation "Primitive")
(define-sw-parser-rule :NUMBER    () nil nil :documentation "Primitive")
(define-sw-parser-rule :CHARACTER () nil nil :documentation "Primitive")

;;; These simplify life...

;;; The rationale for :NON-KEYWORD-NAME --
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
;;; But if we use :NON-KEYWORD-NAME instead, e.g.:
;;;
;;; (define-sw-parser-rule :FOO ()
;;;   (:tuple "foo" (1 :NON-KEYWORD-NAME) (2 :NON-KEYWORD-NAME) (3 :NON-KEYWORD-NAME))
;;;   (foo 1 2 3)
;;;
;;; then after substitutions we'd get lisp forms such as
;;;  (foo "x" "y" "z")
;;; where "x", "y" "z" are the symbol-name's of the symbols x y z
;;;
;;; There might be simpler schemes, but this works well enough...

(define-sw-parser-rule :NON-KEYWORD-NAME ()
  (1 :SYMBOL)
  (common-lisp::symbol-name (quote 1)))

(define-sw-parser-rule :EQUALS ()
  (:anyof "=" "is"))

;;;  NOTE: We use normally use :NAME whereever the doc says :NAME,
;;;        but use :NON-KEYWORD-NAME instead for :SORT-NAME and :LOCAL-VARIABLE
(define-sw-parser-rule :NAME ()
  (:anyof
   ((:tuple "=")           "=")		; so we can use = (and "is" ?) as an op-name
   ((:tuple "*")           "*")		; so we can use * as an op-name
   ((:tuple "/")           "/")		; so we can use / as an op-name
   ((:tuple "translate")   "translate")	; so we can use translate as a op-name
   ((:tuple "colimit")     "colimit")	; so we can use colimit as a op-name
   ((:tuple "diagram")     "diagram")	; so we can use diagram as a op-name
   ((:tuple "print")       "print")	; so we can use print as a op-name
   ((:tuple "with")        "with")	; so we can use with as a op-name
   ((:tuple "Snark")       "Snark")	; so we can use Snark as a unit-identifier
   ((:tuple (1 :NON-KEYWORD-NAME)) 1)
   ))

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
  (make-sc-toplevel-term 1 ':left-lcb ':right-lcb))

(define-sw-parser-rule :SC-TOPLEVEL-DECLS ()
  (:tuple (1 :SC-DECLS))
  (make-sc-toplevel-decls 1 ':left-lcb ':right-lcb))

(define-sw-parser-rule :SC-DECLS ()
  (:repeat+ :SC-DECL nil))

(define-sw-parser-rule :SC-DECL ()
  (:tuple  (1 :NAME) :EQUALS (2 :SC-TERM))
  (make-sc-decl 1 2 ':left-lcb ':right-lcb))

;;; ========================================================================
;;;  SC-TERM
;;; ========================================================================

(define-sw-parser-rule :SC-TERM ()
  (:anyof
   (:tuple "(" (1 :SC-TERM) ")")
   (1 :SC-PRINT)
   (1 :SC-UNIT-ID)
   (1 :SPEC-DEFINITION)
   (1 :SC-LET)
   (1 :SC-WHERE)
   (1 :SC-QUALIFY)
   (1 :SC-HIDE)
   (1 :SC-EXPORT)
   (1 :SC-TRANSLATE)
   (1 :SC-SPEC-MORPH)
   ;; (1 :SC-SHAPE)
   (1 :SC-DIAG)
   (1 :SC-COLIMIT)
   (1 :SC-SUBSTITUTE)
   ;; (1 :SC-DIAG-MORPH)
   ;; (1 :SC-DOM)
   ;; (1 :SC-COD)
   ;; (1 :SC-LIMIT)
   ;; (1 :SC-APEX)
   (1 :SC-GENERATE)
   (1 :SC-OBLIGATIONS)
   (1 :SC-PROVE)
   (1 :SC-EXPAND)
   (1 :SC-REDUCE)
   (1 :SC-EXTEND))
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
  (:tuple "/" (1 :SC-UNIT-ID-PATH) (:optional (:tuple "#" (2 :NAME))))
  (make-sc-absolute-unit-id 1 2 ':left-lcb ':right-lcb))

(define-sw-parser-rule :SC-RELATIVE-UNIT-ID ()
  (:tuple (1 :SC-UNIT-ID-PATH) (:optional (:tuple "#" (2 :NAME))))
  (make-sc-relative-unit-id 1 2 ':left-lcb ':right-lcb))

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
;;;  SPEC-DEFINITION
;;;  http://www.specware.org/manual/html/modules.html
;;;  TODO: In doc: Change references to modules
;;; ========================================================================

(define-sw-parser-rule :SPEC-DEFINITION ()
  (:anyof
   (:tuple "spec" (1 (:optional :QUALIFIER)) "{" (2 :DECLARATION-SEQUENCE) "}")
   (:tuple "spec" (1 (:optional :QUALIFIER))     (2 :DECLARATION-SEQUENCE) :END-SPEC))
  (make-spec-definition 1 2 ':left-lcb ':right-lcb))

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
   (1 :SORT-DECLARATION)
   (1 :OP-DECLARATION)
   (1 :DEFINITION))
  1)

;;;  TODO: In doc: Remove reference to spec-definition within a spec
(define-sw-parser-rule :DEFINITION ()
  (:anyof
   (1 :SORT-DEFINITION)
   (1 :OP-DEFINITION)
   (1 :CLAIM-DEFINITION))
  ;; (1 :SPEC-DEFINITION)  ;; obsolete
  1)

;;; ------------------------------------------------------------------------
;;;  IMPORT-DECLARATION
;;; ------------------------------------------------------------------------

;;;  TODO: In doc: import sc-term, not just spec-name
(define-sw-parser-rule :IMPORT-DECLARATION ()
  (:tuple "import" (1 (:repeat+ :SC-TERM ",")))
  (make-import-declaration 1 ':left-lcb ':right-lcb))

;;; ------------------------------------------------------------------------
;;;  QUALIFIABLE-SORT-NAME 
;;; ------------------------------------------------------------------------
(define-sw-parser-rule :QUALIFIABLE-SORT-NAME ()
  (:anyof :UNQUALIFIED-SORT-NAME :QUALIFIED-SORT-NAME))

(define-sw-parser-rule :UNQUALIFIED-SORT-NAME ()
  (1 :SORT-NAME)
  (MetaSlang::mkUnQualifiedId 1))

(define-sw-parser-rule :QUALIFIED-SORT-NAME ()
  (:tuple (1 :QUALIFIER) "." (2 :SORT-NAME))
  (MetaSlang::mkQualifiedId-2 1 2))

(define-sw-parser-rule :QUALIFIER ()
  (1 :NAME)
  1)

;;;  NOTE: We use normally use :NAME whereever the doc says :NAME,
;;;        but use :NON-KEYWORD-NAME instead for :SORT-NAME and :LOCAL-VARIABLE
(define-sw-parser-rule :SORT-NAME ()
  :NON-KEYWORD-NAME)

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
  (1 :NAME)
  1)

;;; ------------------------------------------------------------------------
;;;  QUALIFIABLE-CLAIM-NAME 
;;; ------------------------------------------------------------------------

(define-sw-parser-rule :QUALIFIABLE-CLAIM-NAME ()
  (:anyof :UNQUALIFIED-CLAIM-NAME :QUALIFIED-CLAIM-NAME))

(define-sw-parser-rule :UNQUALIFIED-CLAIM-NAME ()
  (1 :CLAIM-NAME)
  (MetaSlang::mkUnQualifiedId 1))

(define-sw-parser-rule :QUALIFIED-CLAIM-NAME ()
  (:tuple (1 :QUALIFIER) "." (2 :CLAIM-NAME))
  (MetaSlang::mkQualifiedId-2 1 2))

(define-sw-parser-rule :CLAIM-NAME ()
  (1 :NAME)
  1)

;;; ------------------------------------------------------------------------
;;;  SORT-DECLARATION
;;; ------------------------------------------------------------------------

;;;  TODO: Fix doc: sort-declaration now uses qualified name, not just name
(define-sw-parser-rule :SORT-DECLARATION ()
  (:tuple :KW-TYPE (1 :QUALIFIABLE-SORT-NAMES) (:optional (2 :FORMAL-SORT-PARAMETERS)))
  (make-sort-declaration 1 2 ':left-lcb ':right-lcb))

(define-sw-parser-rule :KW-TYPE ()
  (:anyof "sort" "type"))

(define-sw-parser-rule :FORMAL-SORT-PARAMETERS ()
  ;; a little tricky.  Allow "X" "(X)" "(X,Y)" etc. but not "()"
  (:anyof :SINGLE-SORT-VARIABLE :LOCAL-SORT-VARIABLE-LIST))

(define-sw-parser-rule :SINGLE-SORT-VARIABLE ()
  (1 :LOCAL-SORT-VARIABLE)
  (list 1))				; e.g. "x" => (list "x")

(define-sw-parser-rule :LOCAL-SORT-VARIABLE-LIST ()
  (:tuple "(" (1 (:repeat+ :LOCAL-SORT-VARIABLE ",")) ")")
  1)					; e.g. ("x" "y" "z") => (list "x" "y" "z")

(define-sw-parser-rule :LOCAL-SORT-VARIABLE ()
  (1 :NON-KEYWORD-NAME)			; don't allow "="
  1)

;;; ------------------------------------------------------------------------
;;;  SORT-DEFINITION
;;; ------------------------------------------------------------------------

;;;  TODO: In doc: sort-definition now uses qualified name, not just name
(define-sw-parser-rule :SORT-DEFINITION ()
  (:tuple :KW-TYPE (1 :QUALIFIABLE-SORT-NAMES) (:optional (2 :FORMAL-SORT-PARAMETERS)) :EQUALS (3 :SORT))
  (make-sort-definition 1 2 3 ':left-lcb ':right-lcb))

;;; ------------------------------------------------------------------------
;;;  OP-DECLARATION
;;; ------------------------------------------------------------------------

;;;  TODO: In doc: op-declaration now uses qualified name, not just name
(define-sw-parser-rule :OP-DECLARATION ()
  (:tuple "op" (1 :QUALIFIABLE-OP-NAMES) (:optional (2 :FIXITY)) ":" (3 :SORT-SCHEME))
  (make-op-declaration 1 2 3 ':left-lcb ':right-lcb))

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

(define-sw-parser-rule :SORT-SCHEME ()
  (:tuple (:optional (1 :SORT-VARIABLE-BINDER)) (2 :SORT))
  (make-sort-scheme 1 2 ':left-lcb ':right-lcb))

(define-sw-parser-rule :SORT-VARIABLE-BINDER ()
  (:tuple "fa" (1 :LOCAL-SORT-VARIABLE-LIST))
  1)

;;; ------------------------------------------------------------------------
;;;  OP-DEFINITION
;;; ------------------------------------------------------------------------

;;;  TODO: In doc: op-definition now uses qualified name, not just name
;;;  TODO: In code: compare op-definition with doc
(define-sw-parser-rule :OP-DEFINITION ()
  (:tuple "def"
          (:optional (1 :SORT-VARIABLE-BINDER))
          (2 :QUALIFIABLE-OP-NAMES)
          (3 :FORMAL-PARAMETERS)
          (:optional (:tuple ":" (4 :SORT)))
          :EQUALS
          (5 :EXPRESSION))
  (make-op-definition 1 2 3 4 5 ':left-lcb ':right-lcb))

(define-sw-parser-rule :FORMAL-PARAMETERS ()
  (:repeat* :FORMAL-PARAMETER))

(define-sw-parser-rule :FORMAL-PARAMETER ()
  :CLOSED-PATTERN)

;;; ------------------------------------------------------------------------
;;;  CLAIM-DEFINITION
;;; ------------------------------------------------------------------------

;;;  TODO: In doc: use "=", not :EQUALS in claim definition
(define-sw-parser-rule :CLAIM-DEFINITION ()
  ;; :EQUALS would be too confusing. e.g. "axiom x = y" would mean "axiom named x is defined as y"
  (:tuple (1 :CLAIM-KIND) (2 :LABEL) "is" (3 :CLAIM))
  (make-claim-definition 1 2 3 ':left-lcb ':right-lcb))

(define-sw-parser-rule :CLAIM-KIND ()
  (:anyof ((:tuple "axiom")       :|Axiom|)
          ((:tuple "theorem")     :|Theorem|)
          ((:tuple "conjecture")  :|Conjecture|)))

;;;  TODO: In doc and code: The syntax for naming axioms is pretty ugly
(define-sw-parser-rule :LABEL ()
  :ANY-TEXT-UP-TO-EQUALS)

;;;  TODO: In doc and code: The syntax for naming axioms is pretty ugly
(define-sw-parser-rule :ANY-TEXT-UP-TO-EQUALS ()
  (1 (:repeat+ :DESCRIPTION-ELEMENT nil))
  (make-claim-name 1))

;;;  TODO: In doc and code: The syntax for naming axioms is pretty ugly
(define-sw-parser-rule :DESCRIPTION-ELEMENT ()
  (:anyof
   :NON-KEYWORD-NAME
   :NUMBER-AS-STRING
   :STRING
   :CHARACTER
   "true" "false" "fa" "ex"
   "module" "spec" "import" "sort" "def" "op" "end"
   "fn" "case" "of" "let" "if" "then" "else" "in" "with" "using" "options"
   "project" "relax" "restrict" "quotient" "choose" "embed" "embed?"
   "as" "infixl" "infixr"
   "axiom" "theorem" "conjecture"
   "_" "::" ":" "->" "|" "(" ")" "[" "]" "{" "}" "*" "." "/" ","
   ))

(define-sw-parser-rule :NUMBER-AS-STRING ()
  (:tuple (1 :NUMBER))
  (format nil "~D" 1))

(define-sw-parser-rule :CLAIM ()
  (:tuple (:optional (1 :SORT-QUANTIFICATION)) (2 :EXPRESSION))
  (cons 1 2))

(define-sw-parser-rule :SORT-QUANTIFICATION ()
  (:tuple :KW-TYPE (1 :SORT-VARIABLE-BINDER))
  1)

;;; ========================================================================
;;;   SORT
;;;   http://www.specware.org/manual/html/sorts.html
;;; ========================================================================

(define-sw-parser-rule :SORT ()
  (:anyof
   (1 :SORT-SUM                :documentation "Co-product sort")
   (1 :SORT-ARROW              :documentation "Function sort")
   (1 :SLACK-SORT              :documentation "Slack sort")
   )
  1)

(define-sw-parser-rule :SLACK-SORT ()
  (:anyof
   (1 :SORT-PRODUCT            :documentation "Product sort")
   (1 :TIGHT-SORT              :documentation "Tight sort")
   )
  1)

(define-sw-parser-rule :TIGHT-SORT ()
  (:anyof
   (1 :SORT-INSTANTIATION      :documentation "Sort instantiation")
   (1 :CLOSED-SORT             :documentation "Closed sort -- unambiguous termination")
   )
  1)

(define-sw-parser-rule :CLOSED-SORT ()
  (:anyof
   (1 :SORT-REF                :documentation "Qualifiable sort name") ; could refer to sort or sort variable
   (1 :SORT-RECORD             :documentation "Sort record")
   (1 :SORT-RESTRICTION        :documentation "Sort restriction")
   (1 :SORT-COMPREHENSION      :documentation "Sort comprehension")
   (1 :SORT-QUOTIENT           :documentation "Sort quotient")
   (1 :PARENTHESIZED-SORT      :documentation "Parenthesized Sort")
   )
  1)

;;; ------------------------------------------------------------------------
;;;   SORT-SUM
;;; ------------------------------------------------------------------------

(define-sw-parser-rule :SORT-SUM ()
  (:tuple (1 (:repeat+ :SORT-SUMMAND nil)))
  (make-sort-sum 1 ':left-lcb ':right-lcb))

(define-sw-parser-rule :SORT-SUMMAND ()
  (:tuple "|" (1 :CONSTRUCTOR) (:optional (2 :SLACK-SORT)))
  (make-sort-summand 1 2 ':left-lcb ':right-lcb))

(define-sw-parser-rule :CONSTRUCTOR ()
  :NAME)

;;; ------------------------------------------------------------------------
;;;   SORT-ARROW
;;; ------------------------------------------------------------------------

(define-sw-parser-rule :SORT-ARROW ()
  (:tuple (1 :ARROW-SOURCE) "->" (2 :SORT))
  (make-sort-arrow 1 2 ':left-lcb ':right-lcb))

(define-sw-parser-rule :ARROW-SOURCE ()
  (:anyof :SORT-SUM :SLACK-SORT))

;;; ------------------------------------------------------------------------
;;;   SORT-PRODUCT
;;; ------------------------------------------------------------------------

(define-sw-parser-rule :SORT-PRODUCT ()
  (:tuple (1 (:repeat++ :TIGHT-SORT "*")))
  (make-sort-product 1 ':left-lcb ':right-lcb))

;;; ------------------------------------------------------------------------
;;;   SORT-INSTANTIATION
;;; ------------------------------------------------------------------------

(define-sw-parser-rule :SORT-INSTANTIATION ()
  ;; Don't use :SORT-REF for first arg, since that could
  ;;  refer to sort variables as well as sorts,
  ;;  which we don't want to allow here.
  (:tuple (1 :QUALIFIABLE-SORT-NAME) (2 :ACTUAL-SORT-PARAMETERS))
  (make-sort-instantiation 1 2 ':left-lcb ':right-lcb))

(define-sw-parser-rule :ACTUAL-SORT-PARAMETERS ()
  (:anyof
   ((:tuple (1 :CLOSED-SORT))       (list 1))
   ((:tuple (1 :PROPER-SORT-LIST))  1)
   ))

(define-sw-parser-rule :PROPER-SORT-LIST ()
  (:tuple "(" (1 (:repeat++ :SORT ",")) ")")
  1)

;;; ------------------------------------------------------------------------

(define-sw-parser-rule :QUALIFIABLE-SORT-NAMES ()
  ;; "S"  "A.S"  "{S, A.X, Y}" etc.
  ;; "{S}" is same as "S"
  (:anyof 
   ((:tuple (1 :QUALIFIABLE-SORT-NAME))
    (list 1))
   ((:tuple "{"
	    (2 (:REPEAT+ :QUALIFIABLE-SORT-NAME ","))
	    "}")
    2)))

;;; ------------------------------------------------------------------------
;;;   SORT-REF
;;; ------------------------------------------------------------------------

(define-sw-parser-rule :SORT-REF ()
  (1 :QUALIFIABLE-SORT-NAME)
  (make-sort-ref 1 ':left-lcb ':right-lcb))

;;; ------------------------------------------------------------------------
;;;   SORT-RECORD
;;; ------------------------------------------------------------------------

(define-sw-parser-rule :SORT-RECORD ()
  (:anyof
   (1 :UNIT-PRODUCT-SORT)
   (:tuple "{" (1 :FIELD-SORT-LIST) "}"))
  1)

;;;  NOTE: "{}" is parsed directly as :UNIT-PRODUCT-SORT,
;;;        but in the documentation, it's viewed as 0 entries in :SORT-RECORD
;;;  TODO: In code: We should add :record* as a parser production.
(define-sw-parser-rule :UNIT-PRODUCT-SORT ()
  (:anyof
   (:tuple "{" "}")
   (:tuple "(" ")"))
  (make-sort-record  nil        ':left-lcb ':right-lcb) :documentation "Unit product")

(define-sw-parser-rule :FIELD-SORT-LIST ()
  (1 (:repeat+ :FIELD-SORT ","))
  (make-sort-record  1 ':left-lcb ':right-lcb) :documentation "Record Sort")

(define-sw-parser-rule :FIELD-SORT ()
  (:tuple (1 :FIELD-NAME) ":" (2 :SORT))
  (make-field-sort 1 2 ':left-lcb ':right-lcb))

(define-sw-parser-rule :FIELD-NAME ()
  :NAME)

;;; ------------------------------------------------------------------------
;;;   SORT-RESTRICTION
;;; ------------------------------------------------------------------------

(define-sw-parser-rule :SORT-RESTRICTION ()
  ;; The multiple uses of "|" in the grammar complicates this rule.
  ;; E.g., without parens required here, sort comprehension {x : Integer | f x}
  ;; could be parsed as a one-element field sort with x of type (Integer | f x).
  ;; But with parens required here, that would need to be {x : (Integer | f x)}
  ;; to get that effect.
  (:tuple "(" (1 :SLACK-SORT) "|" (2 :EXPRESSION) ")")
  (make-sort-restriction 1 2 ':left-lcb ':right-lcb) :documentation "Subsort")

;;; ------------------------------------------------------------------------
;;;   SORT-COMPREHENSION
;;; ------------------------------------------------------------------------

(define-sw-parser-rule :SORT-COMPREHENSION ()
  (:tuple "{" (1 :ANNOTATED-PATTERN) "|" (2 :EXPRESSION) "}")
  (make-sort-comprehension 1 2 ':left-lcb ':right-lcb) :documentation "Sort comprehension")

;;; ------------------------------------------------------------------------
;;;   SORT-QUOTIENT
;;; ------------------------------------------------------------------------

;;;  TODO: In doc: sort-quotient relation is expression, but that's ambiguous -- need tight-expression
(define-sw-parser-rule :SORT-QUOTIENT ()
  (:tuple (1 :CLOSED-SORT) "/" (2 :TIGHT-EXPRESSION)) ; CLOSED-EXPRESSION?
  (make-sort-quotient 1 2 ':left-lcb ':right-lcb) :documentation "Quotient")

;;; ------------------------------------------------------------------------
;;;   PARENTHESIZED-SORT
;;; ------------------------------------------------------------------------

(define-sw-parser-rule :PARENTHESIZED-SORT ()
  (:tuple "(" (1 :SORT) ")")
  1)

;;; ========================================================================
;;;   EXPRESSION
;;;   http://www.specware.org/manual/html/expressions.html
;;; ========================================================================


(define-sw-parser-rule :EXPRESSION ()
  (:anyof
   (1 :LAMBDA-FORM          :documentation "Function definition")
   (1 :CASE-EXPRESSION      :documentation "Case")
   (1 :LET-EXPRESSION       :documentation "Let")
   (1 :IF-EXPRESSION        :documentation "If-then-else")
   (1 :QUANTIFICATION       :documentation "Quantification (fa/ex)")
   (1 :ANNOTATED-EXPRESSION :documentation "Annotated (i.e. typed) expression")
   (1 :TIGHT-EXPRESSION     :documentation "Tight expression -- suitable for annotation")
   )
  1)

(define-sw-parser-rule :NON-BRANCH-EXPRESSION ()
  (:anyof
   (1 :NON-BRANCH-LET-EXPRESSION  :documentation "Let not ending in case or lambda")
   (1 :NON-BRANCH-IF-EXPRESSION   :documentation "If-then-else not ending in case or lambda")
   (1 :NON-BRANCH-QUANTIFICATION  :documentation "Quantification (fa/ex) not ending in case or lambda")
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

;;;  UNQUALIFIED-OP-REF is outside SELECTABLE-EXPRESSION to avoid ambiguity with "A.B.C"
;;;   being both SELECT (C, TWO-NAME-EXPRESSION (A,B))
;;;          and SELECT (C, SELECT (B, UNQUALIFIED-OP-REF A))
;;;  "X . SELECTOR" will be parsed as TWO-NAME-EXPRESSION and be disambiguated in post-processing
(define-sw-parser-rule :CLOSED-EXPRESSION ()
  (:anyof
   (1 :UNQUALIFIED-OP-REF     :documentation "Op reference or Variable reference")
   (1 :SELECTABLE-EXPRESSION  :documentation "Closed expression -- unambiguous termination")
   (1 :RESTRICTION            :documentation "restrict p e -or- (restrict p) e") ; new, per task 22
   )
  1)

;;;  NOTE: An expressions such as A.B is a three-way ambiguous selectable-expression :
;;;         OpRef (Qualified (A,B))
;;;         Select (B, OpRef (Qualified (unqualified, A)))
;;;         Select (B, VarRef A)
;;;        So we parse as TWO-NAME-EXPRESSION and resolve in post-processing.
(define-sw-parser-rule :SELECTABLE-EXPRESSION ()
  (:anyof
   ;; 
   (1 :TWO-NAME-EXPRESSION        :documentation "Reference to op or var, or selection")  ; resolve in post-processing  (name     . name)
   ;; (1 :QUALIFIED-OP-REF        :documentation "Qualified reference to op")             ; see TWO-NAME-EXPRESSION
   (1 :NAT-FIELD-SELECTION        :documentation "Selection from name using Nat")         ; see TWO-NAME-EXPRESSION     (name     . nat)
   (1 :FIELD-SELECTION            :documentation "Selection from non-name")               ; see TWO-NAME-EXPRESSION     (non-name . name)
   ;;
   (1 :LITERAL                    :documentation "Literal: Boolean, Nat, Character, String")
   (1 :TUPLE-DISPLAY              :documentation "Tuple")
   (1 :RECORD-DISPLAY             :documentation "Record")
   (1 :SEQUENTIAL-EXPRESSION      :documentation "Sequence of expressions")
   (1 :LIST-DISPLAY               :documentation "List")
   (1 :STRUCTOR                   :documentation "Project, Embed, etc.")
   (1 :PARENTHESIZED-EXPRESSION   :documentation "Parenthesized expression")
   (1 :MONAD-EXPRESSION           :documentation "Monadic expression")
   )
  1)

;;; ------------------------------------------------------------------------
;;;   UNQUALIFIED-OP-REF
;;; ------------------------------------------------------------------------

;;; Note: If a dot follows, this production will become a dead-end,
;;;       since dot is not legal after a TIGHT-EXPRESSION,
;;;       but the competing TWO-NAME-EXPRESSION may succeed.
(define-sw-parser-rule :UNQUALIFIED-OP-REF ()
  (:tuple (1 :NAME))
  (make-unqualified-op-ref 1 ':left-lcb ':right-lcb))

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
  (:tuple "fn" (1 :MATCH))
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
  (:tuple "def" (1 :NAME) (2 :FORMAL-PARAMETER-SEQUENCE) (:optional (:tuple ":" (3 :SORT))) :EQUALS (4 :EXPRESSION))
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
   ((:tuple "fa")  forall-op)
   ((:tuple "ex")  exists-op)))

(define-sw-parser-rule :LOCAL-VARIABLE-LIST ()
  (:tuple "(" (1 (:repeat+ :ANNOTATED-VARIABLE ",")) ")")
  (make-local-variable-list 1 ':left-lcb ':right-lcb))

(define-sw-parser-rule :ANNOTATED-VARIABLE ()
  (:tuple (1 :LOCAL-VARIABLE) (:optional (:tuple ":" (2 :SORT))))
  (make-annotated-variable 1 2 ':left-lcb ':right-lcb))

;;;  NOTE: We use normally use :NAME whereever the doc says :NAME,
;;;        but use :NON-KEYWORD-NAME instead for :SORT-NAME and :LOCAL-VARIABLE
(define-sw-parser-rule :LOCAL-VARIABLE ()
  :NON-KEYWORD-NAME)

;;; ------------------------------------------------------------------------
;;;   ANNOTATED-EXPRESSION
;;; ------------------------------------------------------------------------

(define-sw-parser-rule :ANNOTATED-EXPRESSION ()
  ;;  "P : S1 : S2" is legal,  meaning P is of type S1, which is also of type S2
  (:tuple (1 :TIGHT-EXPRESSION) ":" (2 :SORT))
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
	    (2 (:REPEAT+ :QUALIFIABLE-OP-NAME ","))
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
  (:tuple (1 :CLOSED-EXPRESSION) (2 :CLOSED-EXPRESSIONS)) ;  (:optional (:tuple ":" (3 :SORT)))
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
   :RELAXATOR
   ;;  removed :RESTRICTOR, per task 22: 
   ;;  restrict p must no longer be a function but part of a construct, 
   ;;  i.e. it must be always followed by an expression, i.e. restrict p e
   ;; :RESTRICTOR 
   :QUOTIENTER
   :CHOOSER
   :EMBEDDER
   :EMEBDDING-TEST))

;;; ------------------------------------------------------------------------

(define-sw-parser-rule :PROJECTOR ()
  (:anyof
   ((:tuple "project" (1 :NAT))        (make-nat-selector        1 ':left-lcb ':right-lcb) :documentation "Projection")
   ((:tuple "project" (1 :FIELD-NAME)) (make-field-name-selector 1 ':left-lcb ':right-lcb) :documentation "Projection")))

(define-sw-parser-rule :RELAXATOR ()
  (:tuple "relax"    (1 :CLOSED-EXPRESSION))
  (make-relaxator 1 ':left-lcb ':right-lcb)
  :documentation "Relaxation")

;;  New :RESTRICTION production, per task 22: 
;;  restrict p must no longer be a function but part of a construct, 
;;  i.e. it must be always followed by an expression, i.e. restrict p e
(define-sw-parser-rule :RESTRICTION ()
  (:anyof 
   (:tuple     "restrict" (1 :CLOSED-EXPRESSION)     (2 :CLOSED-EXPRESSION))
   (:tuple "(" "restrict" (1 :CLOSED-EXPRESSION) ")" (2 :CLOSED-EXPRESSION))
   )
  (make-application (make-restrictor 1 ':left-lcb ':right-lcb) (list 2) ':left-lcb ':right-lcb)
  :documentation "Restriction")

(define-sw-parser-rule :QUOTIENTER ()
  (:tuple "quotient" (1 :CLOSED-EXPRESSION))
  (make-quotienter 1  ':left-lcb ':right-lcb)
  :documentation "Quotient")

(define-sw-parser-rule :CHOOSER ()
  (:tuple "choose"   (1 :CLOSED-EXPRESSION))
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

(define-sw-parser-rule :MONAD-BINDING-EXPRESSION ()
  (:tuple "{" (1 :PATTERN) "<-" (2 :EXPRESSION) ";" (3 :MONAD-STMT-LIST) "}")
  (make-monad-binding-expression 1 2 3 ':left-lcb ':right-lcb)
  :documentation "Monadic binding")

(define-sw-parser-rule :MONAD-STMT-LIST ()
  (:anyof
   ((:tuple (1 :EXPRESSION))                                             1)
   ((:tuple (1 :EXPRESSION) ";" (2 :MONAD-STMT-LIST))                    (make-monad-term-expression    1 2   ':left-lcb ':right-lcb))
   ((:tuple (1 :PATTERN) "<-" (2 :EXPRESSION) ";" (3 :MONAD-STMT-LIST))  (make-monad-binding-expression 1 2 3 ':left-lcb ':right-lcb))
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
  (:tuple (1 :PATTERN) "->" (2 :EXPRESSION))
  (make-branch 1 2 ':left-lcb ':right-lcb))

(define-sw-parser-rule :NON-BRANCH-BRANCH () ; as above, but not ending with "| .. -> .."
  ;; i.e., a branch that doesn't end in a branch
  (:tuple (1 :PATTERN) "->" (2 :NON-BRANCH-EXPRESSION))
  (make-branch 1 2 ':left-lcb ':right-lcb))

;;; ========================================================================
;;;  PATTERN
;;;  http://www.specware.org/manual/html/matchesandpatterns.html
;;; ========================================================================

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
   :RELAX-PATTERN
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
  (:tuple (1 :PATTERN) ":" (2 :SORT))                            (make-annotated-pattern  1 2   ':left-lcb ':right-lcb) :documentation "Annotated Pattern")

(define-sw-parser-rule :ALIASED-PATTERN   ()
  (:tuple (1 :VARIABLE-PATTERN) "as" (2 :TIGHT-PATTERN))         (make-aliased-pattern    1 2   ':left-lcb ':right-lcb) :documentation "Aliased pattern")

(define-sw-parser-rule :CONS-PATTERN ()
  (:tuple (1 :CLOSED-PATTERN) "::" (2 :TIGHT-PATTERN))           (make-cons-pattern       1 2   ':left-lcb ':right-lcb) :documentation "CONS pattern")

(define-sw-parser-rule :EMBED-PATTERN ()
  (:tuple (1 :CONSTRUCTOR) (2 :CLOSED-PATTERN))                  (make-embed-pattern      1 2   ':left-lcb ':right-lcb) :documentation "Embed pattern")

(define-sw-parser-rule :QUOTIENT-PATTERN ()
  (:tuple "quotient" (1 :CLOSED-EXPRESSION) (2 :TIGHT-PATTERN))  (make-quotient-pattern   1 2   ':left-lcb ':right-lcb) :documentation "Quotient pattern")

(define-sw-parser-rule :RELAX-PATTERN ()
  (:tuple "relax"    (1 :CLOSED-EXPRESSION) (2 :TIGHT-PATTERN))  (make-relax-pattern      1 2   ':left-lcb ':right-lcb) :documentation "Relax pattern")

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
;; we might provide some sort of expressions or patterns
;; that match sets of identifiers.
;; (define-sw-parser-rule :SC-NAME-EXPR ()
;;   (:tuple "{" (1 (:optional :QUALIFIABLE-AMBIGUOUS-NAME-LIST)) "}")
;; (list . 1))

(define-sw-parser-rule :SC-DECL-REFS ()
  (:repeat* :SC-DECL-REF ","))

(define-sw-parser-rule :SC-DECL-REF ()
  (:anyof 
   ((:tuple :KW-TYPE        (1 :SC-SORT-REF))          (make-sc-sort-ref      1 ':left-lcb ':right-lcb))
   ((:tuple "op"            (1 :SC-OP-REF))            (make-sc-op-ref        1 ':left-lcb ':right-lcb))
   ((:tuple (1 :CLAIM-KIND) (2 :SC-CLAIM-REF))         (make-sc-claim-ref     1 2 ':left-lcb ':right-lcb))
   ;; Without an explicit "sort" or "op" keyword, if ref is annotated, its an op ref:
   ((:tuple                 (1 :SC-ANNOTATED-OP-REF))  (make-sc-op-ref        1 ':left-lcb ':right-lcb))
   ;; Otherwise, it's probably ambiguous (semantic routine will notice that "=" must be an op):
   ((:tuple                 (1 :SC-AMBIGUOUS-REF))     (make-sc-ambiguous-ref 1 ':left-lcb ':right-lcb))
   ))

;;; ------------------------------------------------------------------------
;;;  SORT REF
;;; ------------------------------------------------------------------------

(define-sw-parser-rule :SC-SORT-REF ()
  ;; When we know it must be a sort ref...
  ;; "[A.]X" "([A.]X)", but X cannot be "="
  (:anyof 
   ((:tuple     (1 :QUALIFIABLE-SORT-NAME)     )  1) ; "[A.]f"  
   ((:tuple "(" (1 :QUALIFIABLE-SORT-NAME) ")" )  1) ; "([A.]f)"
   ))

;;; ------------------------------------------------------------------------
;;;  OP REF
;;; ------------------------------------------------------------------------

(define-sw-parser-rule :SC-OP-REF ()
  ;; When we know it must be an op ref...
  ;; "[A,]f", "([A,]f)", "[A.]f : <sort>", "([A.]f : <sort>)"
  (:anyof 
   ((:tuple     (1 :SC-OP-REF-AUX)     )  1) ; "[A.]f"  
   ((:tuple "(" (1 :SC-OP-REF-AUX) ")" )  1) ; "([A.]f)"
   ))

(define-sw-parser-rule :SC-OP-REF-AUX ()
  ;; "[A,]f", "([A,]f)", "[A.]f : <sort>", "([A.]f : <sort>)"
  (:anyof 
   :SC-UNANNOTATED-OP-REF
   :SC-ANNOTATED-OP-REF))

(define-sw-parser-rule :SC-UNANNOTATED-OP-REF ()
  ;; When we know it must be an op ref...
  ;; "[A.]f"
  (1 :QUALIFIABLE-OP-NAME) 
  (make-unannotated-op-ref 1 ':left-lcb ':right-lcb))

(define-sw-parser-rule :SC-ANNOTATED-OP-REF ()
  ;; This can only be an op ref...
  ;; "[A.]f : <sort>"
  (:tuple (1 :QUALIFIABLE-OP-NAME) ":" (2 :SORT))
  (make-annotated-op-ref 1 2 ':left-lcb ':right-lcb))

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
  ;; When we're not sure if its a sort/op/axiom ref...
  ;; "X"  "A.X"  "(X)"  "(A.X)"
  ;; We assume that semantic routines will disambiguate as an OP-REF if X is "="
  (:anyof 
   ((:tuple     (1 :QUALIFIABLE-AMBIGUOUS-NAME)     )  1) ; "[A.]f"  
   ((:tuple "(" (1 :QUALIFIABLE-AMBIGUOUS-NAME) ")" )  1) ; "([A.]f)"
   ))

;;; ------------------------------------------------------------------------
;;;  QUALIFIABLE-AMBIGUOUS-NAME (might refer to sort/op/axiom)
;;; ------------------------------------------------------------------------

(define-sw-parser-rule :QUALIFIABLE-AMBIGUOUS-NAME ()
  ;; might be sort or op name, but will be of the form XXX or QQQ.XXX
  (:anyof :UNQUALIFIED-AMBIGUOUS-NAME :QUALIFIED-AMBIGUOUS-NAME))

(define-sw-parser-rule :UNQUALIFIED-AMBIGUOUS-NAME ()
  (:anyof
   ;; maybe :NAME should be :NON-KEYWORD-NAME
   ;; that would automatically rule out "=", "*", "/", "translate", etc.
   ((:tuple (1 :NAME)) (MetaSlang::mkUnQualifiedId 1))
   ((:tuple "_")       (MetaSlang::mkUnQualifiedId "_"))
   ))

(define-sw-parser-rule :QUALIFIED-AMBIGUOUS-NAME ()
  (:anyof
   ;; maybe :NAME should be :NON-KEYWORD-NAME
   ;; that would automatically rule out "=", "*", "/", "translate", etc.
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
   ((:tuple :KW-TYPE (1 :SC-SORT-REF)         :MAPS-TO (2 :SC-SORT-REF))          (make-sc-sort-rule      1 2 ':left-lcb ':right-lcb))
   ((:tuple "op"     (1 :SC-OP-REF)           :MAPS-TO (2 :SC-OP-REF))            (make-sc-op-rule        1 2 ':left-lcb ':right-lcb))
   ;; ?? axiom/thoerem/conjecture ??
   ;;
   ;; Without an explicit "sort" or "op" keyword, 
   ;;  if either side is annotated, this is an op rule:
   ((:tuple        (1 :SC-ANNOTATED-OP-REF) :MAPS-TO (2 :SC-OP-REF))            (make-sc-op-rule        1 2 ':left-lcb ':right-lcb))
   ((:tuple        (1 :SC-ANNOTATED-OP-REF) :MAPS-TO (2 :SC-ANNOTATED-OP-REF))  (make-sc-op-rule        1 2 ':left-lcb ':right-lcb))
   ((:tuple        (1 :SC-OP-REF)           :MAPS-TO (2 :SC-ANNOTATED-OP-REF))  (make-sc-op-rule        1 2 ':left-lcb ':right-lcb))
   ;; Otherwise, it's probably ambiguous (semantic routine will notice that "=" must be an op):
   ((:tuple        (1 :SC-AMBIGUOUS-REF)    :MAPS-TO (2 :SC-AMBIGUOUS-REF))     (make-sc-ambiguous-rule 1 2 ':left-lcb ':right-lcb))
   ))

(define-sw-parser-rule :MAPS-TO ()
  (:tuple "+->"))

;;; ========================================================================
;;;  SC-SPEC-MORPH
;;; ========================================================================

(define-sw-parser-rule :SC-SPEC-MORPH ()
  (:tuple "morphism" (1 :SC-TERM) "->" (2 :SC-TERM) "{" (3 :SC-SPEC-MORPH-RULES) "}")
  (make-sc-spec-morph 1 2 3 ':left-lcb ':right-lcb)
  )

;;  (:anyof
;;    ((:tuple (1 :SC-TERM) "to" (2 :SC-TERM) "{" (3 :SC-SPEC-MORPH-RULES) "}")
;;     (make-sc-spec-morph 1 2 3 ':left-lcb ':right-lcb)))

(define-sw-parser-rule :SC-SPEC-MORPH-RULES ()
  (:repeat* :SC-SPEC-MORPH-RULE ","))

(define-sw-parser-rule :SC-SPEC-MORPH-RULE ()
  ;; (:tuple (1 :QUALIFIABLE-OP-NAME) :MAPS-TO (2 :QUALIFIABLE-OP-NAME))
  ;; (make-sc-spec-morph-rule 1 2 ':left-lcb ':right-lcb))
  (:anyof 
   ((:tuple :KW-TYPE (1 :SC-SORT-REF)         :MAPS-TO (2 :SC-SORT-REF))          (make-sm-sort-rule      1 2 ':left-lcb ':right-lcb))
   ((:tuple "op"     (1 :SC-OP-REF)           :MAPS-TO (2 :SC-OP-REF))            (make-sm-op-rule        1 2 ':left-lcb ':right-lcb))
   ;; ?? axiom/thoerem/conjecture ??
   ;;
   ;; Without an explicit "sort" or "op" keyword, 
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
  (:tuple (1 :NAME) ":" (2 :NAME) "->" (3 :NAME) :MAPS-TO (4 :SC-TERM))
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
  (:tuple "prove" (1 :CLAIM-NAME) "in" (2 :SC-TERM) 
	  (:optional (:tuple "with"    (3 :PROVER-NAME)))
	  (:optional (:tuple "using"   (4 :PROVER-ASSERTIONS)))
	  (:optional (:tuple "options" (5 :PROVER-OPTIONS))))
  (make-sc-prover 1 2 3 4 5 ':left-lcb ':right-lcb))

(define-sw-parser-rule :PROVER-NAME ()
  (:anyof "Snark" "PVS"))

(define-sw-parser-rule :PROVER-ASSERTIONS ()
  (:anyof 
   "ALL"
   (:repeat+ :CLAIM-NAME ",")))

(define-sw-parser-rule :PROVER-OPTIONS ()
  (:anyof
   (:tuple (1 :STRING)) 
   (:tuple (1 :QUALIFIABLE-OP-NAME)))
  ;; returns (:|OptionString| <sexpressions>) or (:|Error| msg string) or (:|OptionName| op)
  (make-sc-prover-options 1))


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

