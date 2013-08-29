;;; -*- Mode: LISP;  Base: 10; Syntax: Common-Lisp -*-

(in-package :Parser4)

(defpackage :MetaSlang)
(defpackage :SpecCalc)
(defpackage :StandardSpec)
(defpackage :MS)
(defpackage :Position)

;;; ========================================================================

;; TODO:  can more of this be expressed directly in metaslang?
(defun Parser4::mkProverOptions (string)
  (let ((done? nil)
	(whitespaces '(#\space #\tab #\newline)))
    (let* ((trimmed-string (string-trim whitespaces string))
	   (index 0)
	   (result 
	    (catch 'problem
	      (prog1
		  (handler-bind ((error #'(lambda (signal) 
					    (throw 'problem (list signal index)))))
		    (let ((sexp nil)
			  (s-expressions ())
			  (n (length trimmed-string)))
		      (loop
                          (multiple-value-setq (sexp index)
                            ;; bug in Allegro?  
                            ;; Setting eof-error-p to nil won't suppress eof error 
                            ;; unless there is no text at all to parse.
                            ;; At any rate, other kinds of errors are also possible.
                            (let ((*package* (find-package 'snark)))
                              (read-from-string trimmed-string nil nil 
                                                :start               index 
                                                :preserve-whitespace t)))
                          (push sexp s-expressions)
			(when (>= index n)
			  (return (reverse s-expressions))))))
                ;; Prog1 returns the value of the first expression.
		;; So if there were no problems, done? will become true but
		;; result will be bound to the value returned from the loop.
		(setq done? t)))))
      (if done?
	  (cons :|OptionString| result)
          ;; cause parser error?
          (let ((signal (first result))
                (index  (second result)))
            (let ((error-msg 
                   (format nil "~A at position ~D" 
                           (if (eq (type-of signal) 'common-lisp::end-of-file)
                               "Premature EOF for expression starting"
                               signal)
                           index)))
              (cons :|Error| (cons error-msg string))))))))

;;; ========================================================================

(defun new-version? (n) 
  ;; temporary hack for transition to new code
  (let* ((sym (find-symbol "ABSTRACTTYPE-3" "STANDARDSPEC"))
         (result (and sym (fboundp sym))))
    ;; (format t (if result "~&=== PARSER SEES NEW VERSION AT ~D ===~%" "~&=== PARSER SEES OLD VERSION AT ~D ===~%") n)
    result))

;;; variables associated with new definition tables (circa May 8, 2002)
(defvar *current-module-name*   nil) ; used only in this file
(defvar *collected-symbols*     nil) ; used in this file and in meta-slang-parser-semantics-espec.lisp
(defvar *collected-definitions* nil) ; used in this file and in load.lisp

(defvar *show-results?* nil)

(defparameter *internal-parser-position* 
  (cons :|Internal| "built-in from parser"))

;;; ========================================================================
;;;  Misc utilities
;;; ========================================================================

(defun make-pos (x y) 
  ;; make-region defined in Library/Algorithms/Parsing/Chart/Handwritten/Lisp/parse-semantics.lisp 
  (make-region x y))

(defun freshMetaTypeVar (left right)
  (Utilities::freshMetaTyVar-2 "parser" (make-pos left right)))

;;; These are for instantiations of type variables. E.g. the type variable for the type of equality.
;;; They are treated specially by type inference. See
(defun freshPolyMetaTypeVar (left right)
  (Utilities::freshMetaTyVar-2 "parser-poly" (make-pos left right)))

(defun make-equality-fun (op l r)
  (let ((tyvar (freshPolyMetaTypeVar l r))
	(pos (make-pos l r)))
    (cons :|Fun|
	  (vector op 
		  ;; (TypeChecker::makeEqualityType-2 tyvar pos)
		  (temp-makeEqualityType-2 tyvar pos)
		  pos))))

(defun temp-makeEqualityType-2 (tyvar pos)
  (cons :|Arrow|
	(vector (cons :|Product| (cons (cons (cons "1" tyvar) (cons (cons "2" tyvar) nil))
				       *internal-parser-position*))
		(cons :|Boolean| nil)
		pos)))

(defun make-pragma (x l r)
  (let ((prefix  (first  x))
	(body    (second x))
	(postfix (third  x))
	(pos     (make-pos l r)))
    (SpecCalc::mkPragma-4 prefix body postfix pos)))
  

(defun make-sm-pragma (x l r)
  (let ((prefix  (first  x))
	(body    (second x))
	(postfix (third  x))
	(pos     (make-pos l r)))
    (cons (vector prefix body postfix) pos)))
  
(defun namedTypeVar (name)
  name)

;;; (defun mkQualifiedId (qualifier id) 
;;;   (MetaSlang::mkQualifiedId qualifier id))
;;;
;;; (defun mkUnQualifiedId (id) 
;;;   (MetaSlang::mkUnQualifiedId id))
;;; 
;;; (defun make-unqualified-type-name (id left right)
;;;   (declare (ignore left right))
;;;   (MetaSlang::mkUnQualifiedId id))
;;; 
;;; (defun make-qualified-type-name (qualifier id left right)
;;;   (declare (ignore left right))
;;;   (MetaSlang::mkQualifiedId-2 qualifier id))
;;; 
;;; (defun make-unqualified-op-name (id left right)
;;;   (declare (ignore left right))
;;;   (MetaSlang::mkUnQualifiedId id))
;;; 
;;; (defun make-qualified-op-name (qualifier id left right)
;;;   (declare (ignore left right))
;;;   (MetaSlang::mkQualifiedId-2 qualifier id))
;;; 
;;; (defun make-unqualified-claim-name (id left right)
;;;   (declare (ignore left right))
;;;   (MetaSlang::mkUnQualifiedId id))
;;; 
;;; (defun make-qualified-claim-name (qualifier id left right)
;;;   (declare (ignore left right))
;;;   (MetaSlang::mkQualifiedId-2 qualifier id))
;;; 
;;; (defun make-unqualified-ambiguous-name (id left right)
;;;   (declare (ignore left right))
;;;   (MetaSlang::mkUnQualifiedId id))
;;; 
;;; (defun make-qualified-ambiguous-name (qualifier id left right)
;;;   (declare (ignore left right))
;;;   (MetaSlang::mkQualifiedId-2 qualifier id))
;;; 
;;; ========================================================================
;;;  Primitives
;;; ========================================================================

;;; ========================================================================
;;;  TOPLEVEL
;;; ========================================================================

;; (defun make-sc-toplevel-term (sc-term l r)
;;  (SpecCalc::mkTerm-2 sc-term (make-pos l r)))

;; (defun make-sc-toplevel-decls (sc-decls l r)
;;  (SpecCalc::mkDecls-2 sc-decls (make-pos l r)))

(defun make-sc-decl (name sc-term l r)
  (declare (ignore l r))
  (cons name sc-term))

;;; ========================================================================
;;;  SC-TERM
;;; ========================================================================

(defun make-sc-print (term l r)
  (SpecCalc::mkPrint-2 term (make-pos l r)))

;;; ========================================================================
;;;  SC-UNIT-ID
;;; ========================================================================

(defun make-sc-absolute-unit-id (sc-unit-id-path optional-fragment-id l r)
  (let ((uid
	 (cons :|SpecPath_Relative|
	       (cons
		(cond ((eq optional-fragment-id :unspecified)
		       '(:|None|))
		      (t
		       (cons :|Some| optional-fragment-id)))
		sc-unit-id-path))))
    (SpecCalc::mkUnitId-2 uid (make-pos l r))))

(defun make-sc-relative-unit-id (sc-unit-id-path optional-fragment-id l r)
  (let ((uid 
	 (cons :|UnitId_Relative|
	       (cons
		(cond ((eq optional-fragment-id :unspecified)
		       '(:|None|))
		      (t
		       (cons :|Some| optional-fragment-id)))
		sc-unit-id-path))))
    (SpecCalc::mkUnitId-2 uid (make-pos l r))))

(defun make-fragment-id (char optional-number optional-symbol l r)
  (declare (ignore l r))
  (let ((fragment-id 
	 (format nil "~A~A~A"
		 (if (member char '(#\space #\tab))
		     "" 
		   (format nil "~C" char))
		 (if (eq optional-number :unspecified)
		     "" 
		   (format nil "~D" optional-number))
		 (if (equal optional-symbol :unspecified)
		     "" 
		   optional-symbol))))
    (cond ((digit-char-p char)
	   (warn "Fragment identifiers must be simple names, hence must not begin with digits: ~A" fragment-id))
	  ((equal fragment-id "")
	   (warn "Fragment identifier is missing.")))
    fragment-id))

;;;(defun make-sc-specpath-unit-id (sc-unit-id-path l r)
;;;  (cons (cons :|UnitId| (cons :|SpecPath| sc-unit-id-path))
;;;        (make-pos l r)))
;;;

;;; ========================================================================
;;;  SC-SPEC-DEFINITION
;;;  http://www.specware.org/manual/html/modules.html
;;;  TODO: In doc: Change references to modules
;;; ========================================================================

(defun make-internal-type (name)
  (cons :|Base| 
	(vector (MetaSlang::mkQualifiedId-2 name name)
		nil 
		*internal-parser-position*)))

(defparameter char-type   (make-internal-type "Char"    ))
(defparameter string-type (make-internal-type "String"  ))
(defparameter int-type    (make-internal-type "Integer" ))
(defparameter nat-type    (make-internal-type "Nat"     ))

(defparameter bool-type   (cons :|Boolean| nil)) ; special built-in type

(defparameter forall-op   (cons :|Forall| nil))
(defparameter exists-op   (cons :|Exists| nil))
(defparameter exists1-op  (cons :|Exists1| nil))

(defparameter unspecified-fixity '(:|Unspecified|))

(defun make-sc-spec (declaration-sequence l r)
  :comment "A specification"
  (SpecCalc::mkSpec-2 declaration-sequence (make-pos l r)))

(defun make-spec-definition (declaration-sequence l r) ; deprecate
  :comment "A specification"
  (SpecCalc::mkSpec-2 declaration-sequence (make-pos l r)))

;;; ========================================================================
;;;  DECLARATION
;;;  http://www.specware.org/manual/html/declarations.html
;;; ========================================================================

;;; ------------------------------------------------------------------------
;;;  IMPORT-DECLARATION
;;; ------------------------------------------------------------------------

(defun make-import-declaration (sc-terms l r)
  (cons (cons :|Import| sc-terms)
        (make-pos l r)))

;;; ------------------------------------------------------------------------
;;;  TYPE-DECLARATION
;;; ------------------------------------------------------------------------


;; To factor the parser further, perhaps we should think about removing
;; the reference to StandardSpec from the semantic rules.
(defun make-type-declaration (qualifiable-type-names optional-tvs l r)
  (let*  ((tvs     (if (eq :unspecified optional-tvs) nil optional-tvs))
	  ;;
	  (names   (remove-duplicates qualifiable-type-names :test 'equal :from-end t))
          ;; use of nat-type below is a hack -- conversion by abstractType will be ignored
          (tvs-and-types (StandardSpec::abstractType-3 #'namedTypeVar tvs nat-type))
	  ;; Since namedTypeVar is the identity function,
	  ;;  (car tvs-and-type) will just be a copy of typeVars1,
	  ;;  (cdr tvs-and-type) will be ignored. 
          (tvs     (car tvs-and-types))
	  (defs    '())
	  (pos     (make-pos l r)))
    (SpecCalc::mkTypeSpecElem-4 names tvs defs pos)
    ))

;;; ------------------------------------------------------------------------
;;;  TYPE-DEFINITION
;;; ------------------------------------------------------------------------

(defun make-type-definition (qualifiable-type-names optional-tvs type l r)
  (let* ((tvs      (if (eq :unspecified optional-tvs) nil optional-tvs))
	 (names    (remove-duplicates qualifiable-type-names :test 'equal :from-end t))
         (tvs-and-types
           (StandardSpec::abstractType-3 #'namedTypeVar tvs type))
	 ;; Since namedTypeVar is the identity function,
	 ;;  (car tvs-and-types) will just be a copy of typeVars1,
	 ;;  (cdr tvs-and-types) will be a copy of type with (Base qid) replaced by (TyVar id) where appropriate.
         (tvs      (car tvs-and-types))
         (defs     (list (cdr tvs-and-types)))
	 (pos      (make-pos l r))) 
    (SpecCalc::mkTypeSpecElem-4 names tvs defs pos)
    ))


;;; ------------------------------------------------------------------------
;;;  OP-DECLARATION
;;;  OP-DEFINITION
;;; ------------------------------------------------------------------------

(defun make-op-elem (qualifiable-op-names 
		     optional-fixity 
		     optional-pre-tvs 
		     optional-post-tvs 
		     optional-type 
		     optional-params 
		     optional-def
                     optional-refine
                     optional-transform-expr
		     l r)
  (let* ((names  (remove-duplicates qualifiable-op-names :test 'equal :from-end t))
	 (fixity (if (equal  optional-fixity :unspecified) 
		     unspecified-fixity
		     optional-fixity))
	 (pos    (make-pos l r))
	 (tvs    (cond ((equal optional-pre-tvs :unspecified) 
			(if (equal optional-post-tvs :unspecified)
			    '()
			  optional-post-tvs))
		       ((equal optional-post-tvs :unspecified)
			optional-pre-tvs)
		       (t
			(warn "For op ~A, illegal to provide both pre- and post- type-variable-binder.  Ignoring both binders."
			      (MetaSlang::printAliases names))
			())))
	 (typ    (if (equal  optional-type :unspecified) 
		     (freshMetaTypeVar l r)
		     (cdr 
                      (StandardSpec::abstractType-3 #'namedTypeVar tvs optional-type))
                     ))
	 ;; ---------------------------------------------------------------
	 (refine?            (not (eq optional-refine :unspecified)))
         (dfn                (if (and refine? (not (eq optional-transform-expr :unspecified)))
                                 (make-transform-term optional-transform-expr pos)
                               (if (equal optional-def :unspecified)
                                   (cons :|Any| pos)
                                   optional-def)))
	 (typed-term         (make-typed-term dfn typ l r))
	 (typed-term         (if (equal optional-params :unspecified)
				  typed-term 
				  (bind-op-parameters optional-params typed-term l r)))
	 (tvs-and-typed-term (StandardSpec::abstractTerm-3 #'namedTypeVar tvs typed-term))
	 ;; Since namedTypeVar is the identity function,
	 ;;  (car tvs-and-typed-term) will just be a copy of tvs
	 ;;  (cdr tvs-and-typed-term) will be a copy of typed-term,
	 ;;   with (Base qid) replaced by (TyVar id) where appropriate.
	 (typed-term         (cdr tvs-and-typed-term))
	 (defs               (list typed-term)))
    (SpecCalc::mkOpSpecElem-7 names fixity tvs typ defs refine? pos)))

(defun bind-op-parameters (params term l r)
  (if (null params)
      term
      (MS::mkLambda-2 
       (car params)
       (bind-op-parameters (cdr params) term l r))))

(defun make-restricted-formal-pattern (pat pred l r)
  (make-restricted-pattern pat pred l r)
;  (MS::mkTypedPat-2
;   pat 
;   (MS::mkSubtype-2 (freshMetaTypeVar l r)
;		    (MS::mkLambda-2 pat pred)))
  )

(defun make-fixity (associativity priority l r)
  (declare (ignore l r))
  (cons :|Infix| (cons (cons associativity nil) priority)))

#||
If we want the precedence to be optional:

(defun make-fixity (associativity optional-priority l r)
  (let ((priority (if (equal :unspecified optional-priority) 1 optional-priority)))
    (cons (cons associativity nil) priority)))
||#

;;; ------------------------------------------------------------------------
;;;  CLAIM-DEFINITION
;;; ------------------------------------------------------------------------


(defun make-claim-definition (claim-kind label claim l r)
  (let ((optional-type-quantification (car claim))
        (expression                   (cdr claim)))
    (let* ((typevars     (if (equal :unspecified optional-type-quantification) nil optional-type-quantification))
           (typeVarsTerm (StandardSpec::abstractTerm-3 #'namedTypeVar typevars expression))
           (typevars     (car typeVarsTerm))
           (term         (cdr typeVarsTerm)))
      ;; Since namedTypeVar is the identity function,
      ;;  (car typeVarsTerm) will just be a copy of the original typevars
      ;;  (cdr typeVarsTerm) will be a copy of expression with (Base qid) replaced by (TyVar id) where appropriate.
      ;; TODO: Move the responsibility for all this conversion into the linker.
      (cons (cons :|Claim| (vector (list claim-kind) label typevars term))
            (make-pos l r)))))

;;;  TODO: In doc and code: The syntax for naming axioms is pretty ugly
(defun make-claim-name (description-elements)
  (apply 'concatenate (cons 'string (intersperse-blanks description-elements))))

(defun intersperse-blanks (x)
  (labels ((aux (x)
             (if (null x)
                 x
               (cons " " (cons (car x) (aux (cdr x)))))))
    (if (null (cdr x))
        x
      (cons (car x) (aux (cdr x))))))

;;; ========================================================================
;;;   TYPE
;;;   http://www.specware.org/manual/html/types.html
;;; ========================================================================

;;; ------------------------------------------------------------------------
;;;   TYPE-SUM
;;; ------------------------------------------------------------------------

(defun make-type-sum (type-summands l r)
  (let ((alphabetical-type-summands (sort type-summands #'(lambda (x y) (string< (car x) (car y))))))
    (cons :|CoProduct|
          (cons alphabetical-type-summands
                (make-pos l r)))))

(defun make-type-summand (constructor optional-slack-type l r)
  (declare (ignore l r))
  (cons constructor
        (if (eq :unspecified optional-slack-type)
            '(:|None|)
            (cons :|Some| optional-slack-type))))

;;; ------------------------------------------------------------------------
;;;   TYPE-ARROW
;;; ------------------------------------------------------------------------

(defun make-type-arrow (arrow-source type l r)
  (cons :|Arrow|
        (vector arrow-source type
                (make-pos l r))))

;;; ------------------------------------------------------------------------
;;;   TYPE-PRODUCT
;;; ------------------------------------------------------------------------

(defun make-type-product (tight-types l r)
  (if (> (length tight-types) 1)
      (make-product tight-types l r)
    (car tight-types)))

(defun make-product (fields l r)
  (cons :|Product|
        (cons (MS::tagTuple fields)
              (make-pos l r))))

;;; ------------------------------------------------------------------------
;;;   TYPE-INSTANTIATION
;;; ------------------------------------------------------------------------

(defun make-type-instantiation (qualifiable-type-name actual-type-parameters l r)
  (cons :|Base|
        (vector qualifiable-type-name actual-type-parameters
                (make-pos l r))))

;;; ------------------------------------------------------------------------
;;;   TYPE-REF
;;; ------------------------------------------------------------------------

(defun make-type-ref (qualifiable-type-name l r)
  (if (or (equal qualifiable-type-name '(:|Qualified| "<unqualified>" . "Boolean"))
	  (equal qualifiable-type-name '(:|Qualified| "Boolean" . "Boolean")))      ; Deprecate "Boolean" as qualifier?
      (cons :|Boolean| (make-pos l r))
    (let ((type-args nil))
      (cons :|Base|
	    (vector qualifiable-type-name type-args
		    (make-pos l r))))))

;;; ------------------------------------------------------------------------
;;;   TYPE-RECORD
;;; ------------------------------------------------------------------------

(defun make-type-record (field-types l r)
  (let ((alphabetical-field-types (sort field-types #'(lambda (x y) (string< (car x) (car y))))))
    (cons :|Product|
          (cons alphabetical-field-types
                (make-pos l r)))))

(defun make-field-type (field-name type l r)
  (declare (ignore l r))
  (cons field-name type))

;;; ------------------------------------------------------------------------
;;;   TYPE-RESTRICTION
;;; ------------------------------------------------------------------------

(defun make-type-restriction (slack-type expression l r)
  (cons :|Subtype|
        (vector slack-type expression
                (make-pos l r))))

;;; ------------------------------------------------------------------------
;;;   TYPE-COMPREHENSION
;;; ------------------------------------------------------------------------

(defun make-type-comprehension (annotated-pattern expression l r)
  ;; (cons :|TypedPat|   (vector pattern type (make-pos l r))))
  ;; why did we build the structure above in the first place?
  (let* ((v (cdr annotated-pattern))
         (pattern (svref v 0))
         (type    (svref v 1)))
    (cons :|Subtype|
          (vector type
                  (make-lambda-form (list (make-branch pattern expression l r))
                                    l r)
                  (make-pos l r)))))

;;; ------------------------------------------------------------------------
;;;   TYPE-QUOTIENT
;;; ------------------------------------------------------------------------

(defun make-type-quotient (type tight-expression l r)
  (cons :|Quotient|
        (vector type tight-expression
                (make-pos l r))))

;;; ========================================================================
;;;   EXPRESSION
;;;   http://www.specware.org/manual/html/expressions.html
;;; ========================================================================

(defun make-bool-fun (op l r)
  (make-fun op MS::binaryBoolType l r))

;;; ------------------------------------------------------------------------
;;;   UNQUALIFIED-OP-REF
;;; ------------------------------------------------------------------------

(defun make-unqualified-op-ref (name l r)
  (cond ((or (equal name "~") (equal name "\\_not"))   
	 ;; "~" is treated specially:
	 ;; "~" refers to the built-in Not, but "foo.~" is just an ordinary operator...
	 (make-fun '(:|Not|) MS::unaryBoolType l r))
	((equal name "=")
	 ;; "=" is treated specially:
	 ;; "=" can refer to the built-in Equals, but can also be syntax for defs, etc.
	 (make-equality-fun '(:|Equals|) 
			    l r))
	(t
	 (make-fun (cons :|OneName| (cons name unspecified-fixity))
		   (freshMetaTypeVar l r)
		   l r))))

;;; ------------------------------------------------------------------------
;;;   TWO-NAME-EXPRESSION
;;; ------------------------------------------------------------------------

(defun make-two-name-expression (name-1 name-2 l r)
  (make-fun (cons :|TwoNames| (vector name-1 name-2 unspecified-fixity))
            (freshMetaTypeVar l r)
            l r))

;;; ------------------------------------------------------------------------
;;;   LAMBDA-FORM
;;; ------------------------------------------------------------------------

(defun make-lambda-form (match l r)
  ;; match is defined as a sequence of branches
  (cons :|Lambda|
        (cons match
              (make-pos l r))))

;;; ------------------------------------------------------------------------
;;;   SET-COMPREHENSION
;;; ------------------------------------------------------------------------

(defun make-set-comprehension (pat body l r)
  (make-application
   (make-unqualified-op-ref "collect" l r)
   (list (cons :|Lambda|
               (cons (list (make-branch pat body l r))
                     (make-pos l r))))
   l r))


;;; ------------------------------------------------------------------------
;;;   CASE-EXPRESSION
;;; ------------------------------------------------------------------------

(defun make-case-expression (expression match l r)
  ;; match is defined as a sequence of branches
  (make-application (make-lambda-form match l r) (list expression) l r))

;;; ------------------------------------------------------------------------
;;;   LET-EXPRESSION
;;; ------------------------------------------------------------------------

(defun make-let-binding-term (recless-let-binding expression l r)
  (cons :|Let|
        (vector (cons recless-let-binding nil) 
		expression
                (make-pos l r))))

(defun make-rec-let-binding-term (rec-let-binding-sequence expression l r)
  (cons :|LetRec|
        (vector rec-let-binding-sequence 
		expression
                (make-pos l r))))

(defun make-recless-let-binding (pattern expression l r)
  (declare (ignore l r))
  (cons pattern expression))

(defun make-rec-let-binding (name formal-parameter-sequence optional-type expression l r)
  (let* ((var  (cons name (freshMetaTypeVar l r)))
         (term (if (eq :unspecified optional-type)
                   expression
                 (make-typed-term expression optional-type l r)))
         (term (bindParams formal-parameter-sequence term l r)))
    (cons var term)))

(defun bindParams (params term l r)
  (if (null params)
      term
    (cons :|Lambda|
          (cons (list (vector (car params)
                              (MS::mkTrue-0)
                              (bindParams (cdr params) term l r)))
                (make-pos l r)))))

;;; ------------------------------------------------------------------------
;;;   IF-EXPRESSION
;;; ------------------------------------------------------------------------

(defun make-if-expression (term1 term2 term3 l r)
  (cons :|IfThenElse|
        (vector term1 term2 term3
                (make-pos l r))))

;;; ------------------------------------------------------------------------
;;;   THE (IOTA)
;;; ------------------------------------------------------------------------

(defun make-the (var expression l r)
  (cons :|The|
        (vector var expression
                (make-pos l r))))

;;; ------------------------------------------------------------------------
;;;   QUANTIFICATION
;;; ------------------------------------------------------------------------

(defun make-quantification (quantifier local-variable-list expression l r)
  (cons :|Bind|
        (vector quantifier local-variable-list expression
                (make-pos l r))))

(defun make-local-variable-list (annotated-variables l r)
  (declare (ignore l r))
  annotated-variables)

(defun make-annotated-variable (local-variable optional-type l r)
  (let ((type (if (eq optional-type :unspecified)
                  (freshMetaTypeVar l r)
                optional-type)))
    (cons local-variable type)))

;;; ------------------------------------------------------------------------
;;;   ANNOTATED-EXPRESSION
;;; ------------------------------------------------------------------------

(defun make-annotated-expression (tight-expression type l r)
  (make-typed-term tight-expression type l r))

(defun make-typed-term (tight-expression type l r)
  (cons :|TypedTerm|
        (vector tight-expression type
                (make-pos l r))))

(defun make-transform-term (transform-expression pos)
  (cons :|Transform|
        (cons transform-expression pos)))

;;; ------------------------------------------------------------------------
;;;   APPLICATION
;;; ------------------------------------------------------------------------

(defun make-application (closed-expression closed-expressions l r)
  (cons :|ApplyN|
	(cons (cons closed-expression closed-expressions)
	      (make-pos l r))))

;;; ------------------------------------------------------------------------
;;;   LITERAL
;;; ------------------------------------------------------------------------

(defun make-boolean-literal (boolean   l r) (make-fun (cons :|Bool|   boolean)    bool-type   l r))
(defun make-nat-literal     (number    l r) (make-fun (cons :|Nat|    number)     nat-type    l r))
(defun make-char-literal    (character l r) (make-fun (cons :|Char|   character)  char-type   l r))
(defun make-string-literal  (string    l r) (make-fun (cons :|String| string)     string-type l r))

;;; ------------------------------------------------------------------------
;;;   FIELD-SELECTION
;;; ------------------------------------------------------------------------

(defun make-field-selection (selector body l r)
  ;; what does this annotation buy?
  (make-annotated-expression (make-application selector (list body) l r) 
			     (freshMetaTypeVar l r) 
			     l r))

(defun make-nat-selector        (number     l r) (make-projector (format nil "~D" number) l r))
(defun make-field-name-selector (field-name l r) (make-projector field-name               l r))

;;; ------------------------------------------------------------------------
;;;  TUPLE-DISPLAY
;;; ------------------------------------------------------------------------

(defun make-tuple-display (optional-tuple-display-body l r)
  ;; :unspecified for 0, otherwise length of optional-tuple-display-body will be at least 2
  ;;  I.e., length of terms will be 0 or 2-or-more, but will never be 1.
  (let ((terms (if (equal optional-tuple-display-body :unspecified)
                   ()
                 optional-tuple-display-body)))
    (cons ':|Record|
          (cons (MS::tagTuple terms)
                (make-pos l r)))))

;;; ------------------------------------------------------------------------
;;;  RECORD-DISPLAY
;;; ------------------------------------------------------------------------

(defun make-record-display (field-fillers l r)
  (let ((alphabetical-field-fillers (sort field-fillers #'(lambda (x y) (string< (car x) (car y))))))
    (cons :|Record|
          (cons alphabetical-field-fillers
                (make-pos l r)))))

(defun make-field-filler (field-name expression l r)
  (declare (ignore l r))
  (cons field-name expression))

;;; ------------------------------------------------------------------------
;;;  SEQUENTIAL-EXPRESSION
;;; ------------------------------------------------------------------------

(defun make-sequential-expression (void-expressions expression l r)
  (let ((terms (append void-expressions (list expression))))
    (cons :|Seq|
          (cons terms
                (make-pos l r)))))

;;; ------------------------------------------------------------------------
;;;  LIST-DISPLAY
;;; ------------------------------------------------------------------------

(defun make-list-display (expressions l r)
  (StandardSpec::mkList-3 expressions
			  (make-pos l r)
			  (freshPolyMetaTypeVar l r)))

;;; ------------------------------------------------------------------------
;;;  STRUCTOR
;;; ------------------------------------------------------------------------

(defun make-projector      (field-selector l r) (make-fun (cons :|Project|   field-selector)         (freshMetaTypeVar l r) l r))
(defun make-quotienter     (type-qid       l r) (make-fun (cons :|PQuotient| type-qid)               (freshMetaTypeVar l r) l r))
(defun make-chooser        (type-qid       l r) (make-fun (cons :|PChoose|   type-qid)               (freshMetaTypeVar l r) l r))
(defun make-embedder       (constructor    l r) (make-fun (cons :|Embed|     (cons constructor nil)) (freshMetaTypeVar l r) l r))
(defun make-embedding-test (constructor    l r) (make-fun (cons :|Embedded|  constructor)            (freshMetaTypeVar l r) l r))

(defun make-fun (f s l r)
  (cons :|Fun|
        (vector f s
                (make-pos l r))))

(defun make-nonfix (x)
  (cond ((and (consp x) (eq (car x) :|Fun|) (simple-vector-p (cdr x)))
	 (let* ((v (cdr x))
		(f (svref v 0)))
	   (cond ((not (consp f))
		  x)
		 ((eq (car f) :|OneName|)
		  (let* ((new-f (cons :|OneName| 
				      (cons (cadr f)    ; id
					    '(:|Nonfix|))))
			 (new-v (vector new-f (svref v 1) (svref v 2))))
		    (cons :|Fun| new-v)))
		 ((eq (car f) :|TwoNames|)
		  (let* ((z (cdr f))
			 (new-f (cons :|TwoNames| 
				      (vector (svref z 0) ; id
					      (svref z 1) ; id
					      '(:|Nonfix|))))
			 (new-v (vector new-f (svref v 1) (svref v 2))))
		    (cons :|Fun| new-v)))
		 (t (let* ((pos0 (svref v 2))
			   (pos (cdr pos0))
			   (l (svref pos 1))
			   (r (svref pos 2)))
		      (cond ((member (car f) '(:|And| :|Or| :|Implies| :|Iff|))
                             (MS::mkBinaryFn-5 f MS::boolType MS::boolType MS::boolType pos0))
			    ((eq (car f) :|Not|)
			     (MS::mkUnaryBooleanFn-2 f pos0))
			    ((member (car f) '(:|Equals| :|NotEquals|))
			     (let ((a1 (freshMetaTypeVar l r)))
			       (MS::mkBinaryFn-5 f a1 a1 MS::boolType pos0)))
			    ((eq (car f) :|RecordMerge|)
			     (MS::mkBinaryFn-5 f 
                                               (freshMetaTypeVar l r) 
                                               (freshMetaTypeVar l r)
					       (freshMetaTypeVar l r) 
                                               pos0))
			    (t
			     x)))))))
	(t
	 x)))

;;; ------------------------------------------------------------------------
;;;   MONAD-EXPRESSION
;;; ------------------------------------------------------------------------

;; The syntax supports sequences of monadic compositions.

;; The following serves to translate a sequence of monadic statements into
;; a nested application term. Ideally the handling of the monads should not be
;; done here. It should be added to the abstract syntax and handled in
;; the elaboration phase. In that way we would get more meaningful error
;; messages.

;; The general form of a statement sequence is:
;;  {
;;    stmt ;
;;    ...
;;    stmt
;;  }

;; There can be two types of statements: a term and
;; a bind. A term is a MetaSlang term and a bind has the form "pat <- term".

;; The translation rules are largely the same as for Haskell. We assume
;; the two monadic sequencing operators "monadSeq" and "monadBind" are
;; defined.  These correspond to the Haskell infix operators ">>" and
;; ">>=" respectively.  Let t be a MetaSlang term, p be pattern and stmts
;; be a sequence of statements. The translation implements the following
;; equalities:

;;  {t} = t
;;  {t ; stmts} = t >> {stmts}
;;  {p <- t ; stmts} = t >>= (fn p -> {stmts})

;; Using the prefix functions instead these are:

;;  {t} = t
;;  {t ; stmts} = monadSeq (t, {stmts})
;;  {p <- t ; stmts} = monadBind (t, (fn p -> {stmts}))

;;;(defun make-monad-term-expression (expression monad-stmt-list l r)
;;;  (let* (;; (seqIdent    (make-one-name-reference "monadSeq" l r))
;;;         (seqIdent    (make-unqualified-op-ref "monadSeq" l r))
;;;         ;; (seqTerm     (make-long-ident-term seqIdent l r))
;;;         (tupleTerm   (make-tuple-display (list expression monad-stmt-list) l r))
;;;         (application (make-application seqIdent (list tupleTerm) l r)))
;;;    application))

(defun make-monad-term-expression (expression monad-stmt-list l r)
  (let* (;; (seqIdent    (make-one-name-reference "monadSeq" l r))
         (seqIdent    (make-unqualified-op-ref "monadBind" l r))
         ;; (seqTerm     (make-long-ident-term seqIdent l r))
         (branch      (make-branch (make-wildcard-pattern l r) monad-stmt-list l r))
         (fun         (make-lambda-form (list branch) l r))
         (tupleTerm   (make-tuple-display (list expression fun) l r))
         (application (make-application seqIdent (list tupleTerm) l r)))
    application))

(defun make-monad-binding-expression (pattern expression monad-stmt-list l r)
  (let* (;; (seqIdent    (make-one-name-reference "monadBind" l r))
         (seqIdent    (make-unqualified-op-ref "monadBind" l r))
         ;; (seqTerm     (make-long-ident-term seqIdent l r))
         (branch      (make-branch pattern monad-stmt-list l r))
         (fun         (make-lambda-form (list branch) l r))
         (tupleTerm   (make-tuple-display (list expression fun) l r))
         (application (make-application seqIdent (list tupleTerm) l r)))
    application))

;;; ========================================================================
;;;  MATCH
;;;  http://www.specware.org/manual/html/matchesandpatterns.html
;;; ========================================================================

;;; match is defined as a sequence of branches

(defun make-branch (pattern expression l r)
  (declare (ignore l r))
  (vector pattern (MS::mkTrue-0) expression))

;;; ========================================================================
;;;  PATTERN
;;;  http://www.specware.org/manual/html/matchesandpatterns.html
;;; ========================================================================

(defun make-annotated-pattern  (pattern type     l r)
  (when (eq (car pattern) ':|VarPat|)	; Optimize common case, and ensure that variable gets correct type
    (setf (cdadr pattern) type))
  (cons :|TypedPat| (vector pattern type (make-pos l r))))

(defun make-aliased-pattern    (pat1 pat2        l r) (cons :|AliasPat|      (vector pat1 pat2                                          (make-pos l r))))
(defun make-embed-pattern      (id pattern       l r) (cons :|EmbedPat|      (vector id (cons :|Some| pattern) (freshMetaTypeVar l r)   (make-pos l r))))
(defun make-quotient-pattern   (type-qid pattern l r) (cons :|QuotientPat|   (vector pattern type-qid                                   (make-pos l r))))
(defun make-restricted-pattern (pattern term     l r) (cons :|RestrictedPat| (vector pattern term                                       (make-pos l r))))
(defun make-variable-pattern   (id               l r) (cons :|VarPat|        (cons   (cons id (freshMetaTypeVar l r))                   (make-pos l r))))
(defun make-wildcard-pattern   (                 l r) (cons :|WildPat|       (cons   (freshMetaTypeVar l r)                             (make-pos l r))))
(defun make-boolean-pattern    (bool             l r) (cons :|BoolPat|       (cons   bool                                               (make-pos l r))))
(defun make-nat-pattern        (nat              l r) (cons :|NatPat|        (cons   nat                                                (make-pos l r))))
(defun make-char-pattern       (char             l r) (cons :|CharPat|       (cons   char                                               (make-pos l r))))
(defun make-string-pattern     (str              l r) (cons :|StringPat|     (cons   str                                                (make-pos l r))))

(defun make-cons-pattern       (pattern patterns l r) (StandardSpec::mkConsPattern-4 pattern patterns (make-pos l r) (freshPolyMetaTypeVar l r)))
(defun make-list-pattern       (patterns         l r) (StandardSpec::mkListPattern-3 patterns         (make-pos l r) (freshPolyMetaTypeVar l r)))

(defun make-tuple-pattern      (patterns         l r)
  (if (= (length patterns) 1)
      (car patterns)
    (cons :|RecordPat| (cons (MS::tagTuple patterns) (make-pos l r)))))

(defun make-record-pattern     (fields            l r)
  (let ((alphabetized-fields (sort fields #'(lambda (x y) (string< (car x) (car y))))))
    (cons :|RecordPat| (cons alphabetized-fields (make-pos l r)))))

(defun make-field-pattern      (field-name optional-pattern l r)
  (let ((pattern (if (equal optional-pattern :unspecified)
                     (make-variable-pattern field-name l r)
                   optional-pattern)))
    (cons field-name pattern)))

;;; ========================================================================
;;;  SC-LET
;;;  SC-WHERE
;;;  These refer to names for specs, etc.
;;;  E.g.  let SET = /a/b/c in spec import SET ... end-spec
;;; ========================================================================

(defun make-sc-let   (sc-decls sc-term l r)
  (SpecCalc::mkLet-3 sc-decls sc-term (make-pos l r)))

(defun make-sc-where (sc-decls sc-term l r)
  (SpecCalc::mkWhere-3 sc-decls sc-term (make-pos l r)))

;;; ========================================================================
;;;  SC-QUALIFY
;;; ========================================================================

(defun make-sc-qualify (qualifer sc-term l r)
  (SpecCalc::mkQualify-3 sc-term qualifer (make-pos l r)))

;;; ========================================================================
;;;  SC-HIDE
;;;  SC-EXPORT
;;; ========================================================================

(defun make-sc-hide (name-list sc-term l r)
  (SpecCalc::mkHide-3 name-list sc-term (make-pos l r)))

(defun make-sc-export (name-list sc-term l r)
  (SpecCalc::mkExport-3 name-list sc-term (make-pos l r)))

(defun make-sc-type-ref      (type-ref             l r)  
  (declare (ignore l r))
  (cons :|Type|      type-ref))

(defun make-sc-op-ref        (op-ref               l r)  
  (declare (ignore l r))
  (cons :|Op|        op-ref))

(defun make-sc-claim-ref     (claim-type claim-ref l r)  
  (declare (ignore l r))
  (cons claim-type   claim-ref))

(defun make-sc-ambiguous-ref (ambiguous-ref        l r)  
  (declare (ignore l r))
  (cons :|Ambiguous| ambiguous-ref))

(defun make-sc-unannotated-op-ref (op-ref      l r)
  (declare (ignore l r))
  (cons op-ref '(:|None|)))

(defun make-unannotated-op-ref (op-ref      l r) ; deprecate
  (declare (ignore l r))
  (cons op-ref '(:|None|)))

(defun make-sc-annotated-op-ref   (op-ref type l r)
  (declare (ignore l r))
  (cons op-ref (cons :|Some| type)))

(defun make-annotated-op-ref   (op-ref type l r) ; deprecate
  (declare (ignore l r))
  (cons op-ref (cons :|Some| type)))

;;; ========================================================================
;;;  SC-TRANSLATE
;;; ========================================================================

(defun make-sc-translate (sc-term sc-translate-expr l r)
  (SpecCalc::mkTranslate-3 sc-term sc-translate-expr (make-pos l r)))

(defun make-sc-translate-expr (rules l r)
  (cons rules
        (make-pos l r)))

;;; (defun make-sc-translate-rules (rules)
;;;   (if (equal rules :unspecified)
;;;      ()
;;;    rules))

;;; (defun make-sc-translate-rule (left-qualifiable-name right-qualifiable-name l r)
;;;   (cons (cons left-qualifiable-name right-qualifiable-name)
;;;        (make-pos l r)))

(defun make-sc-type-rule (left-type-ref right-type-ref l r)
  (cons (cons :|Type| (vector left-type-ref right-type-ref (list right-type-ref)))
        (make-pos l r)))

(defun make-sc-op-rule (left-op-ref right-op-ref l r)
  (cons (cons :|Op| (vector left-op-ref right-op-ref (list (car right-op-ref))))
        (make-pos l r)))

(defun make-sc-ambiguous-rule (left-ref right-ref l r)
  (cons (cons :|Ambiguous| (vector left-ref right-ref (list right-ref)))
        (make-pos l r)))

;;; ------------------------------------------------------------------------
;;;  QUALIFIABLE-NAME (might refer to type or op)
;;; ------------------------------------------------------------------------

;;; ========================================================================
;;;  SC-SPEC-MORPH
;;; ========================================================================

(defun make-sc-spec-morph (dom-sc-term cod-sc-term rules pragmas l r)
  ;; (let ((rules (if (eq rules :unspecified) nil rules))) ...)
  (let ((pragmas (if (eq pragmas :unspecified)
		     '()
		   pragmas)))
    (SpecCalc::mkSpecMorph-5 dom-sc-term cod-sc-term rules pragmas (make-pos l r))))

;;; (defun make-sc-spec-morph-rule (qualifiable-name-dom qualifiable-name-cod l r)
;;;  (vector qualifiable-name-dom qualifiable-name-cod (make-pos l r)))

(defun make-sm-type-rule (left-type-ref right-type-ref l r)
  (cons (cons :|Type|
              (cons left-type-ref right-type-ref))
		(make-pos l r)))

(defun make-sm-op-rule (left-op-ref right-op-ref l r)
  (cons (cons :|Op| (cons left-op-ref right-op-ref))
		(make-pos l r)))

(defun make-sm-ambiguous-rule (left-ref right-ref l r)
  (cons (cons :|Ambiguous| (cons left-ref right-ref))
		(make-pos l r)))

;;; ========================================================================
;;;  SC-SHAPE
;;; ========================================================================

;;; ========================================================================
;;;  SC-DIAG
;;; ========================================================================

(defun make-sc-diag (sc-diag-elems l r)
  :comment "A diagram"
  (SpecCalc::mkDiag-2 sc-diag-elems (make-pos l r)))

(defun make-sc-diag-node (node-name sc-term l r)
  (cons (cons :|Node| (cons node-name sc-term))
        (make-pos l r)))

(defun make-sc-diag-edge (edge-name dom-node-name cod-node-name sc-term l r)
  (cons (cons :|Edge| (vector edge-name dom-node-name cod-node-name sc-term))
        (make-pos l r)))

;;; ========================================================================
;;;  SC-COLIMIT
;;; ========================================================================

(defun make-sc-colimit (diag l r)
  (SpecCalc::mkColimit-2 diag (make-pos l r)))

;;; ========================================================================
;;;  SC-SUBSTITUTE
;;; ========================================================================

(defun make-sc-substitute (spec-term morph-term l r)
  (SpecCalc::mkSubst-3 spec-term morph-term (make-pos l r)))

;;; ========================================================================
;;;  SC-OP-REFINE
;;; ========================================================================

(defun make-sc-op-refine (spec-term elts l r)
  (SpecCalc::mkOpRefine-3 spec-term elts (make-pos l r)))

;;; ========================================================================
;;;  SC-OP-TRANSFORM
;;; ========================================================================
(defun make-sc-transform (spec-term transforms pragmas l r)
  (SpecCalc::mkTransform-4 spec-term transforms pragmas (make-pos l r)))

(defun make-transform-name (name l r)
  (SpecCalc::mkTransformName-2 name (make-pos l r)))

(defun make-transform-boolean (bool l r)
  (SpecCalc::mkTransformName-2 (if bool "true" "false") (make-pos l r)))

(defun make-transform-number (num l r)
  (SpecCalc::mkTransformNumber-2 num (make-pos l r)))

(defun make-transform-string (num l r)
  (SpecCalc::mkTransformString-2 num (make-pos l r)))

(defun make-transform-scterm (uid l r)
  (SpecCalc::mkTransformSCTerm-2 uid (make-pos l r)))

(defun make-transform-qual (q name l r)
  (SpecCalc::mkTransformQual-3 q name (make-pos l r)))

(defun make-transform-item (oper transform l r)
  (SpecCalc::mkTransformItem-3 oper transform (make-pos l r)))

(defun make-transform-slice (root_ops root_types cut_ops cut_types l r)
  (let* ((root_ops   (if (equal root_ops   :unspecified) '() root_ops))
         (root_types (if (equal root_types :unspecified) '() root_types))
         (cut_ops    (if (equal cut_ops    :unspecified) '() cut_ops))
         (cut_types  (if (equal cut_types  :unspecified) '() cut_types))
         (cut_op?   #'(lambda (opname)   (member opname   cut_ops   :test 'equal)))
         (cut_type? #'(lambda (typename) (member typename cut_types :test 'equal))))
    (SpecCalc::mkTransformSlice-5 root_ops root_types cut_op? cut_type? (make-pos l r))))

(defun make-transform-block (transforms l r)
  (SpecCalc::mkTransformBlock-2 transforms (make-pos l r)))

(defun make-transform-at (qids transform l r)
  (SpecCalc::mkTransformAt-3 qids transform (make-pos l r)))

(defun make-transform-repeat (transforms l r)
  (SpecCalc::mkTransformRepeat-2 transforms (make-pos l r)))

(defun make-transform-command (name args l r)
  (SpecCalc::mkTransformCommand-3 name args (make-pos l r)))

(defun make-transform-options (options l r)
  (SpecCalc::mkTransformOptions-2 options (make-pos l r)))

(defun make-transform-tuple (transforms l r)
  (SpecCalc::mkTransformTuple-2 transforms (make-pos l r)))

(defun make-transform-record (record-pairs l r)
  (SpecCalc::mkTransformRecord-2 record-pairs (make-pos l r)))

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

(defun make-sc-generate (target-language sc-term optFilNm l r)
  (let ((opt-filename
	 (if (equal optFilNm :unspecified)
	     '(:|None|)
	   (let ((fname (if (stringp optFilNm)
			    optFilNm
			  (string optFilNm))))
	     (cons :|Some| fname)))))
    (SpecCalc::mkGenerate-4 target-language 
			    sc-term
			    opt-filename
			    (make-pos l r))))


;; ========================================================================
;;;  SC-OBLIGATIONS
;;; ========================================================================

(defun make-sc-obligations (term l r)
  (SpecCalc::mkObligations-2 term (make-pos l r)))

;;; ========================================================================
;;;  SC-PROVE
;;; ========================================================================

(defun make-sc-prover (claim-name spec-term prover-name assertions options answerVar l r)
  ;; The various names here are case sensitive.  Is this desirable?
  (let ((prover-name (if (eq prover-name :unspecified) 
			 "Both" ; what does this mean?
		       (unless (member prover-name '("Snark" "PVS" "FourierM" "Checker")) 
			 (warn "Unrecognized prover: ~A, not Snark, PVS, FourierM, or Checker" prover-name)
			 prover-name)))
	(assertions  (if (eq assertions :unspecified)  '(:|All|)	   (cons :|Explicit| assertions))) 
	(options     (if (eq options    :unspecified)  '(:|OptionString|)  options))
	(baseOptions '(:|ProverBase|))
	(answerVar   (if (eq answerVar  :unspecified)  '(:|None|)          answerVar))
	(here        (make-pos l r)))
    ;; "WELLFORMED" or "Checker" => ProofCheck ..
    ;; otherwise                 => Prove      ...
    (cond ((equal claim-name  (MetaSlang::mkUnQualifiedId "WELLFORMED"))
	   (let ((claim '(:|WellFormed|)))	     (SpecCalc::mkProofCheck-7  claim      spec-term prover-name assertions options baseOptions           here)))
	  ((equal prover-name "Checker")  
	   (let ((claim (list :|Claim| claim-name))) (SpecCalc::mkProofCheck-7  claim      spec-term prover-name assertions options baseOptions           here)))
	  (t                                         (SpecCalc::mkProve-8       claim-name spec-term prover-name assertions options baseOptions answerVar here)))))

(defun make-sc-prover-options-from-string (s)
  (read_list_of_s_expressions_from_string s))

(defun make-sc-answerVar (annotated-variable)
  (cons :|Some| annotated-variable))

;; ========================================================================
;;;  SC-OBLIGATIONS
;;; ========================================================================

(defun make-sc-expand (term l r)
  (SpecCalc::mkExpand-2 term (make-pos l r)))

;;; ========================================================================
;;;  SC-REDUCE
;;; ========================================================================

(defun make-sc-reduce (ms-term sc-term l r)
  (SpecCalc::mkReduce-3 ms-term sc-term (make-pos l r)))

;;; ========================================================================
;;;  SC-EXTEND
;;; ========================================================================

(defun make-sc-extend (term l r)
  (SpecCalc::mkExtendMorph-2 term (make-pos l r)))

