;;; -*- Mode: LISP;  Base: 10; Syntax: Common-Lisp -*-

(in-package "PARSER4")

(defpackage "METASLANG")
(defpackage "SPECCALC")
(defpackage "STANDARDSPEC")
(defpackage "MS")
(defpackage "POSITION")

;;; variables associated with new definition tables (circa May 8, 2002)
(defvar *current-module-name*   nil) ; used only in this file
(defvar *collected-symbols*     nil) ; used in this file and in meta-slang-parser-semantics-espec.lisp
(defvar *collected-definitions* nil) ; used in this file and in load.lisp
(defvar *varcounter*            -1)  ; used only in this file (starts at -1 merely for backwards cosmetic compatibility)

(defvar *show-results?* nil)

;;; ========================================================================
;;;  Misc utilities
;;; ========================================================================

(defvar *make-pos-warnings-seen* 0)

(defun make-pos (left right) 
  (declare (special *parser-source*)) ; bound in parser-interface.lisp
  (when (consp left)
    (when (< (incf *make-pos-warnings-seen*) 10)
      (warn "In MAKE-POS: Bogus left position: ~S" left))
    (let* ((line   (car left))
	   (column (cdr left))
	   (byte   0))
      (setq left (vector line column byte))))
  (when (consp right)
    (when (< (incf *make-pos-warnings-seen*) 10)
      (warn "In MAKE-POS: Bogus right position: ~S" right))
    (let* ((line   (car right))
	   (column (cdr right))
	   (byte   0))
      (setq right (vector line column byte))))
  (case (first *parser-source*)
    (:file   (cons :|File|     (vector (second *parser-source*) left right)))
    (:string (cons :|String|   (vector (second *parser-source*) left right)))
    (t       (when (< (incf *make-pos-warnings-seen*) 10)
	       (warn "In MAKE-POS: What are we parsing? : ~S" *parser-source*))
	     (cons :|Internal| (second *parser-source*)))))

(defun freshMetaTypeVar (left right)
  (cons :|MetaTyVar|
        (cons (cons :|Ref| (vector (cons :|None| nil) "#intern" (incf *varcounter*)))
              (make-pos left right))))

(defun namedTypeVar (name)
  name
  ;;(cons :|TyVar| name)
  ;;(cons :|ref| (vector (cons :|None| nil) name (incf *varcounter*)))
  )

;;; (defun mkQualifiedId (qualifier id) 
;;;   (MetaSlang::mkQualifiedId qualifier id))
;;;
;;; (defun mkUnQualifiedId (id) 
;;;   (MetaSlang::mkUnQualifiedId id))
;;; 
;;; (defun make-unqualified-sort-name (id left right)
;;;   (declare (ignore left right))
;;;   (MetaSlang::mkUnQualifiedId id))
;;; 
;;; (defun make-qualified-sort-name (qualifier id left right)
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

(defun make-sc-toplevel-term (sc-term l r)
  (speccalc::mkTerm-2 sc-term (make-pos l r)))

(defun make-sc-toplevel-decls (sc-decls l r)
  (speccalc::mkDecls-2 sc-decls (make-pos l r)))

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

(defun make-sc-absolute-unit-id (sc-unit-id-path optional-hash-name l r)
  (let ((uid
	 (cons :|SpecPath_Relative|
	       (cons
		(if (eq :unspecified optional-hash-name)
		    (cons :|None| nil)
		  (cons :|Some| optional-hash-name))
		sc-unit-id-path))))
    (speccalc::mkUnitId-2 uid (make-pos l r))))

(defun make-sc-relative-unit-id (sc-unit-id-path optional-hash-name l r)
  (let ((uid 
	 (cons :|UnitId_Relative|
	       (cons
		(if (eq :unspecified optional-hash-name)
		    (cons :|None| nil)
		  (cons :|Some| optional-hash-name))
		sc-unit-id-path))))
    (speccalc::mkUnitId-2 uid (make-pos l r))))

;;;(defun make-sc-specpath-unit-id (sc-unit-id-path l r)
;;;  (cons (cons :|UnitId| (cons :|SpecPath| sc-unit-id-path))
;;;        (make-pos l r)))
;;;

;;; ========================================================================
;;;  SC-SPEC-DEFINITION
;;;  http://www.specware.org/manual/html/modules.html
;;;  TODO: In doc: Change references to modules
;;; ========================================================================

(defparameter internal-parser-position (cons :|Internal| "built-in from parser"))
(defun make-internal-sort (name)
  (cons :|Base| 
	(vector (MetaSlang::mkQualifiedId-2 name name)
		nil 
		internal-parser-position)))

(defparameter char-sort   (make-internal-sort "Char"    ))
(defparameter bool-sort   (make-internal-sort "Boolean" ))
(defparameter string-sort (make-internal-sort "String"  ))
(defparameter int-sort    (make-internal-sort "Integer" ))
(defparameter nat-sort    (make-internal-sort "Nat"     ))

(defparameter forall-op   (cons :|Forall| nil))
(defparameter exists-op   (cons :|Exists| nil))

(defparameter unspecified-fixity '(:|Unspecified|))

;; The counter here is for freshMetaTypeVar. Perhaps it should be moved
;; out of the parser. Needs thought.
(defun make-spec-definition (optional-qualifier declaration-sequence l r)
  :comment "A specification"
  (setq *varcounter* 0)
  (let* ((spec_def (speccalc::mkSpec-2 declaration-sequence (make-pos l r))))
    (if (eq :unspecified optional-qualifier)
        spec_def
      (make-sc-qualify optional-qualifier spec_def l r))))

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
;;;  SORT-DECLARATION
;;; ------------------------------------------------------------------------


;; To factor the parser further, perhaps we should think about removing
;; the reference to StandardSpec from the semantic rules.
(defun make-sort-declaration (qualifiable-sort-names formal-sort-parameters l r)
  (let*  ((typeVars1 (if (eq :unspecified formal-sort-parameters) nil formal-sort-parameters))
          (sort      nat-sort) ; hack -- conversion by abstractSort will be ignored
          (tyVarsSrt (StandardSpec::abstractSort-3 #'namedTypeVar typeVars1 sort))
          (typeVars2 (car tyVarsSrt)))
    ;; Since namedTypeVar is the identity function,
    ;;  (car tyVarsSrt) will just be a copy of typeVars1,
    ;;  (cdr tyVarsSrt) will be ignored.
    ;; TODO: skip the code above and use typeVars1 for typeVars2 below
    (cons (cons :|Sort| (cons (remove-duplicates qualifiable-sort-names :test 'equal :from-end t)
			      (cons typeVars2 ())))
          (make-pos l r))))

;;; ------------------------------------------------------------------------
;;;  SORT-DEFINITION
;;; ------------------------------------------------------------------------

(defun make-sort-definition (qualifiable-sort-names formal-sort-parameters sort l r)
  (let* ((typeVars1 (if (eq :unspecified formal-sort-parameters) nil formal-sort-parameters))
         (tyVarsSrt (StandardSpec::abstractSort-3 #'namedTypeVar typeVars1 sort))
         (typeVars2 (car tyVarsSrt))
         (sort2     (cdr tyVarsSrt)))
    ;; Since namedTypeVar is the identity function,
    ;;  (car tyVarsSrt) will just be a copy of typeVars1,
    ;;  (cdr tyVarsSrt) will be a copy of sort with (Base qid) replaced by (TyVar id) where appropriate.
    ;; TODO: Move the responsibility for this conversion into the linker.
    (cons (cons :|Sort| (cons (remove-duplicates qualifiable-sort-names :test 'equal :from-end t)
			      (cons typeVars2 (list (cons typeVars2 sort2)))))
          (make-pos l r))))

;;; ------------------------------------------------------------------------
;;;  OP-DECLARATION
;;; ------------------------------------------------------------------------

(defun make-op-declaration (qualifiable-op-names optional-fixity sort-scheme l r)
  (let ((fixity (if (equal :unspecified optional-fixity) 
		    unspecified-fixity
		  optional-fixity)))
    (cons (cons :|Op| (cons (remove-duplicates qualifiable-op-names :test 'equal :from-end t)
                            (vector fixity sort-scheme ())))
          (make-pos l r))))

(defun make-fixity (associativity priority l r)
  (declare (ignore l r))
  (cons :|Infix| (cons (cons associativity nil) priority)))

#||
If we want the precedence to be optional:

(defun make-fixity (associativity optional-priority l r)
  (let ((priority (if (equal :unspecified optional-priority) 1 optional-priority)))
    (cons (cons associativity nil) priority)))
||#

(defun make-sort-scheme (optional-sort-variable-binder sort l r)
  (declare (ignore l r))
  (let ((vars (if (equal :unspecified optional-sort-variable-binder)
                  ()
                optional-sort-variable-binder)))
    ;; Since namedTypeVar is the identity function,
    ;;  (car <result>) will just be a copy of vars
    ;;  (cdr <result>) will be a copy of sort with (Base qid) replaced by (TyVar id) where appropriate.
    ;; TODO: Move the responsibility for that conversion into the linker.
    (StandardSpec::abstractSort-3 #'namedTypeVar vars sort)))

;;; ------------------------------------------------------------------------
;;;  OP-DEFINITION
;;; ------------------------------------------------------------------------

(defun make-op-definition (tyVars qualifiable-op-names params optional-sort term l r)
  (let* ((tyVars     (if (equal :unspecified tyVars) () tyVars))
         (term       (if (equal :unspecified optional-sort) term (make-sorted-term term optional-sort l r)))
         (term       (bind-parameters params term l r))
         (tyVarsTerm (StandardSpec::abstractTerm-3 #'namedTypeVar tyVars term))
         (term       (cdr tyVarsTerm))
         (tyVars     (car tyVarsTerm))
         (srtScheme  (cons tyVars (freshMetaTypeVar l r))))
    ;; Since namedTypeVar is the identity function,
    ;;  (car tyVarsTerm) will just be a copy of tyVars
    ;;    so srtScheme will be tyVars * Mtv -- i.e. Mtv parameterized by tyVars
    ;;  (cdr tyVarsTerm) will be a copy of term with (Base qid) replaced by (TyVar id) where appropriate.
    ;; TODO: Move the responsibility for all this conversion into the linker.
    (cons (cons :|Op| (cons (remove-duplicates qualifiable-op-names :test 'equal :from-end t)
                            (vector unspecified-fixity srtScheme (list (cons tyVars term))))) 
	  (make-pos l r))))

(defun bind-parameters (params term l r)
  (if (null params)
      term
    (cons :|Lambda|
          (cons (list (vector (car params) (MS::mkTrue-0)
                              (bind-parameters (cdr params) term l r)))
                (make-pos l r)))))

;;; ------------------------------------------------------------------------
;;;  CLAIM-DEFINITION
;;; ------------------------------------------------------------------------


(defun make-claim-definition (claim-kind label claim l r)
  (let ((optional-sort-quantification (car claim))
        (expression                   (cdr claim)))
    (let* ((typevars     (if (equal :unspecified optional-sort-quantification) nil optional-sort-quantification))
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
;;;   SORT
;;;   http://www.specware.org/manual/html/sorts.html
;;; ========================================================================

;;; ------------------------------------------------------------------------
;;;   SORT-SUM
;;; ------------------------------------------------------------------------

(defun make-sort-sum (sort-summands l r)
  (let ((alphabetical-sort-summands (sort sort-summands #'(lambda (x y) (string< (car x) (car y))))))
    (cons :|CoProduct|
          (cons alphabetical-sort-summands
                (make-pos l r)))))

(defun make-sort-summand (constructor optional-slack-sort l r)
  (declare (ignore l r))
  (cons constructor
        (if (eq :unspecified optional-slack-sort)
            (cons :|None| nil)
            (cons :|Some| optional-slack-sort))))

;;; ------------------------------------------------------------------------
;;;   SORT-ARROW
;;; ------------------------------------------------------------------------

(defun make-sort-arrow (arrow-source sort l r)
  (cons :|Arrow|
        (vector arrow-source sort
                (make-pos l r))))

;;; ------------------------------------------------------------------------
;;;   SORT-PRODUCT
;;; ------------------------------------------------------------------------

(defun make-sort-product (tight-sorts l r)
  (if (> (length tight-sorts) 1)
      (make-product tight-sorts l r)
    (car tight-sorts)))

(defun make-product (fields l r)
  (cons :|Product|
        (cons (MS::tagTuple fields)
              (make-pos l r))))

;;; ------------------------------------------------------------------------
;;;   SORT-INSTANTIATION
;;; ------------------------------------------------------------------------

(defun make-sort-instantiation (qualifiable-sort-name actual-sort-parameters l r)
  (cons :|Base|
        (vector qualifiable-sort-name actual-sort-parameters
                (make-pos l r))))

;;; ------------------------------------------------------------------------
;;;   SORT-REF
;;; ------------------------------------------------------------------------

(defun make-sort-ref (qualifiable-sort-name l r)
  (let ((sort-args nil))
    (cons :|Base|
          (vector qualifiable-sort-name sort-args
                  (make-pos l r)))))

;;; ------------------------------------------------------------------------
;;;   SORT-RECORD
;;; ------------------------------------------------------------------------

(defun make-sort-record (field-sorts l r)
  (let ((alphabetical-field-sorts (sort field-sorts #'(lambda (x y) (string< (car x) (car y))))))
    (cons :|Product|
          (cons alphabetical-field-sorts
                (make-pos l r)))))

(defun make-field-sort (field-name sort l r)
  (declare (ignore l r))
  (cons field-name sort))

;;; ------------------------------------------------------------------------
;;;   SORT-RESTRICTION
;;; ------------------------------------------------------------------------

(defun make-sort-restriction (slack-sort expression l r)
  (cons :|Subsort|
        (vector slack-sort expression
                (make-pos l r))))

;;; ------------------------------------------------------------------------
;;;   SORT-COMPREHENSION
;;; ------------------------------------------------------------------------

(defun make-sort-comprehension (annotated-pattern expression l r)
  ;; (cons :|SortedPat|   (vector pattern sort (make-pos l r))))
  ;; why did we build the structure above in the first place?
  (let* ((v (cdr annotated-pattern))
         (pattern (svref v 0))
         (sort    (svref v 1)))
    (cons :|Subsort|
          (vector sort
                  (make-lambda-form (list (make-branch pattern expression l r))
                                    l r)
                  (make-pos l r)))))

;;; ------------------------------------------------------------------------
;;;   SORT-QUOTIENT
;;; ------------------------------------------------------------------------

(defun make-sort-quotient (sort tight-expression l r)
  (cons :|Quotient|
        (vector sort tight-expression
                (make-pos l r))))

;;; ========================================================================
;;;   EXPRESSION
;;;   http://www.specware.org/manual/html/expressions.html
;;; ========================================================================

;;; ------------------------------------------------------------------------
;;;   UNQUALIFIED-OP-REF
;;; ------------------------------------------------------------------------

(defun make-unqualified-op-ref (name l r)
  (make-fun (if (equal name "=")
                (cons :|Equals| nil)
              (cons :|OneName| (cons name unspecified-fixity)))
            (freshMetaTypeVar l r)
            l r))

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

(defun make-rec-let-binding (name formal-parameter-sequence optional-sort expression l r)
  (let* ((var  (cons name (freshMetaTypeVar l r)))
         (term (if (eq :unspecified optional-sort)
                   expression
                 (make-sorted-term expression optional-sort l r)))
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
;;;   QUANTIFICATION
;;; ------------------------------------------------------------------------

(defun make-quantification (quantifier local-variable-list expression l r)
  (cons :|Bind|
        (vector quantifier local-variable-list expression
                (make-pos l r))))

(defun make-local-variable-list (annotated-variables l r)
  (declare (ignore l r))
  annotated-variables)

(defun make-annotated-variable (local-variable optional-sort l r)
  (let ((sort (if (eq optional-sort :unspecified)
                  (freshMetaTypeVar l r)
                optional-sort)))
    (cons local-variable sort)))

;;; ------------------------------------------------------------------------
;;;   ANNOTATED-EXPRESSION
;;; ------------------------------------------------------------------------

(defun make-annotated-expression (tight-expression sort l r)
  (make-sorted-term tight-expression sort l r))

(defun make-sorted-term (tight-expression sort l r)
  (cons :|SortedTerm|
        (vector tight-expression sort
                (make-pos l r))))

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

(defun make-boolean-literal (boolean   l r) (make-fun (cons :|Bool|   boolean)    bool-sort   l r))
(defun make-nat-literal     (number    l r) (make-fun (cons :|Nat|    number)     nat-sort    l r))
(defun make-char-literal    (character l r) (make-fun (cons :|Char|   character)  char-sort   l r))
(defun make-string-literal  (string    l r) (make-fun (cons :|String| string)     string-sort l r))

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
			  (freshMetaTypeVar l r)))

;;; ------------------------------------------------------------------------
;;;  STRUCTOR
;;; ------------------------------------------------------------------------

(defun make-projector      (field-selector    l r) (make-fun (cons :|Project|   field-selector)         (freshMetaTypeVar l r) l r))
(defun make-relaxator      (closed-expression l r) (make-fun (cons :|PRelax|    closed-expression)      (freshMetaTypeVar l r) l r))
(defun make-restrictor     (closed-expression l r) (make-fun (cons :|PRestrict| closed-expression)      (freshMetaTypeVar l r) l r))
(defun make-quotienter     (closed-expression l r) (make-fun (cons :|PQuotient| closed-expression)      (freshMetaTypeVar l r) l r))
(defun make-chooser        (closed-expression l r) (make-fun (cons :|PChoose|   closed-expression)      (freshMetaTypeVar l r) l r))
(defun make-embedder       (constructor       l r) (make-fun (cons :|Embed|     (cons constructor nil)) (freshMetaTypeVar l r) l r))
(defun make-embedding-test (constructor       l r) (make-fun (cons :|Embedded|  constructor)            (freshMetaTypeVar l r) l r))

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
		 (t
		  x))))
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

(defun make-monad-term-expression (expression monad-stmt-list l r)
  (let* (;; (seqIdent    (make-one-name-reference "monadSeq" l r))
         (seqIdent    (make-unqualified-op-ref "monadSeq" l r))
         ;; (seqTerm     (make-long-ident-term seqIdent l r))
         (tupleTerm   (make-tuple-display (list expression monad-stmt-list) l r))
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

(defun make-annotated-pattern        (pattern sort     l r)
  (when (eq (car pattern) ':|VarPat|)	; Optimize common case, and ensure that variable gets correct type
    (setf (cdadr pattern) sort))
  (cons :|SortedPat| (vector pattern sort (make-pos l r))))
(defun make-aliased-pattern          (pat1 pat2        l r) (cons :|AliasPat|    (vector pat1 pat2                                          (make-pos l r))))
(defun make-embed-pattern            (id pattern       l r) (cons :|EmbedPat|    (vector id (cons :|Some| pattern) (freshMetaTypeVar l r)   (make-pos l r))))
(defun make-quotient-pattern         (term pattern     l r) (cons :|QuotientPat| (vector pattern term                                       (make-pos l r))))
(defun make-relax-pattern            (term pattern     l r) (cons :|RelaxPat|    (vector pattern term                                       (make-pos l r))))
(defun make-variable-pattern         (id               l r) (cons :|VarPat|      (cons   (cons id (freshMetaTypeVar l r))                   (make-pos l r))))
(defun make-wildcard-pattern         (                 l r) (cons :|WildPat|     (cons   (freshMetaTypeVar l r)                             (make-pos l r))))
(defun make-boolean-pattern          (bool             l r) (cons :|BoolPat|     (cons   bool                                               (make-pos l r))))
(defun make-nat-pattern              (nat              l r) (cons :|NatPat|      (cons   nat                                                (make-pos l r))))
(defun make-char-pattern             (char             l r) (cons :|CharPat|     (cons   char                                               (make-pos l r))))
(defun make-string-pattern           (str              l r) (cons :|StringPat|   (cons   str                                                (make-pos l r))))

(defun make-cons-pattern             (pattern patterns l r) (StandardSpec::mkConsPattern-4 pattern patterns (make-pos l r) (freshMetaTypeVar l r)))
(defun make-list-pattern             (patterns         l r) (StandardSpec::mkListPattern-3 patterns         (make-pos l r) (freshMetaTypeVar l r)))

(defun make-tuple-pattern            (patterns         l r)
  (if (= (length patterns) 1)
      (car patterns)
    (cons :|RecordPat| (cons (MS::tagTuple patterns) (make-pos l r)))))

(defun make-record-pattern          (fields            l r)
  (let ((alphabetized-fields (sort fields #'(lambda (x y) (string< (car x) (car y))))))
    (cons :|RecordPat| (cons alphabetized-fields (make-pos l r)))))

(defun make-field-pattern           (field-name optional-pattern l r)
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
  (speccalc::mkLet-3 sc-decls sc-term (make-pos l r)))

(defun make-sc-where (sc-decls sc-term l r)
  (speccalc::mkWhere-3 sc-decls sc-term (make-pos l r)))

;;; ========================================================================
;;;  SC-QUALIFY
;;; ========================================================================

(defun make-sc-qualify (qualifer sc-term l r)
  (speccalc::mkQualify-3 sc-term qualifer (make-pos l r)))

;;; ========================================================================
;;;  SC-HIDE
;;;  SC-EXPORT
;;; ========================================================================

(defun make-sc-hide (name-list sc-term l r)
  (speccalc::mkHide-3 name-list sc-term (make-pos l r)))

(defun make-sc-export (name-list sc-term l r)
  (speccalc::mkExport-3 name-list sc-term (make-pos l r)))

(defun make-sc-sort-ref      (sort-ref             l r)  
  (declare (ignore l r))
  (cons :|Sort|      sort-ref))

(defun make-sc-op-ref        (op-ref               l r)  
  (declare (ignore l r))
  (cons :|Op|        op-ref))

(defun make-sc-claim-ref     (claim-type claim-ref l r)  
  (declare (ignore l r))
  (cons claim-type   claim-ref))

(defun make-sc-ambiguous-ref (ambiguous-ref        l r)  
  (declare (ignore l r))
  (cons :|Ambiguous| ambiguous-ref))

(defun make-unannotated-op-ref (op-ref      l r)
  (declare (ignore l r))
  (cons op-ref '(:|None|)))

(defun make-annotated-op-ref   (op-ref sort l r)
  (declare (ignore l r))
  (cons op-ref (cons :|Some| sort)))

;;; ========================================================================
;;;  SC-TRANSLATE
;;; ========================================================================

(defun make-sc-translate (sc-term sc-translate-expr l r)
  (speccalc::mkTranslate-3 sc-term sc-translate-expr (make-pos l r)))

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

(defun make-sc-sort-rule (left-sort-ref right-sort-ref l r)
  (cons (cons :|Sort| (vector left-sort-ref right-sort-ref (list right-sort-ref)))
        (make-pos l r)))

(defun make-sc-op-rule (left-op-ref right-op-ref l r)
  (cons (cons :|Op| (vector left-op-ref right-op-ref (list (car right-op-ref))))
        (make-pos l r)))

(defun make-sc-ambiguous-rule (left-ref right-ref l r)
  (cons (cons :|Ambiguous| (vector left-ref right-ref (list right-ref)))
        (make-pos l r)))

;;; ------------------------------------------------------------------------
;;;  QUALIFIABLE-NAME (might refer to sort or op)
;;; ------------------------------------------------------------------------

;;; ========================================================================
;;;  SC-SPEC-MORPH
;;; ========================================================================

(defun make-sc-spec-morph (dom-sc-term cod-sc-term rules l r)
  ;; (let ((rules (if (eq rules :unspecified) nil rules))) ...)
  (speccalc::mkSpecMorph-4 dom-sc-term cod-sc-term rules (make-pos l r)))

;;; (defun make-sc-spec-morph-rule (qualifiable-name-dom qualifiable-name-cod l r)
;;;  (vector qualifiable-name-dom qualifiable-name-cod (make-pos l r)))

(defun make-sm-sort-rule (left-sort-ref right-sort-ref l r)
  (cons (cons :|Sort| (cons left-sort-ref right-sort-ref))
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
  (speccalc::mkDiag-2 sc-diag-elems (make-pos l r)))

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
  (speccalc::mkColimit-2 diag (make-pos l r)))

;;; ========================================================================
;;;  SC-SUBSTITUTE
;;; ========================================================================

(defun make-sc-substitute (spec-term morph-term l r)
  (speccalc::mkSubst-3 spec-term morph-term (make-pos l r)))

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
    (speccalc::mkGenerate-4 target-language 
			    sc-term
			    opt-filename
			    (make-pos l r))))


;; ========================================================================
;;;  SC-OBLIGATIONS
;;; ========================================================================

(defun make-sc-obligations (term l r)
  (speccalc::mkObligations-2 term (make-pos l r)))

;;; ========================================================================
;;;  SC-PROVE
;;; ========================================================================

(defun make-sc-prover (claim-name spec-term prover-name assertions options l r)
  (let ((prover-name (if (eq prover-name :unspecified) "Snark" prover-name))
	(assertions  (if (eq assertions  :unspecified) (cons :|All| nil) (cons :|Explicit| assertions)))
	(options     (if (eq options     :unspecified) (cons :|OptionString| nil) options)))
    (speccalc::mkProve-6 claim-name spec-term prover-name assertions options (make-pos l r))))

(defun make-sc-prover-options (name_or_string)
  (cond ((stringp name_or_string) 
	 (read_list_of_s_expressions_from_string name_or_string))
	(t (cons :|OptionName| name_or_string))))

;;; ========================================================================
;;;  SC-REDUCE
;;; ========================================================================

(defun make-sc-reduce (ms-term sc-term l r)
  (speccalc::mkReduce-3 ms-term sc-term (make-pos l r)))

;;; ========================================================================
;;;  SC-EXTEND
;;; ========================================================================

(defun make-sc-extend (term l r)
  (speccalc::mkExtendMorph-2 term (make-pos l r)))

