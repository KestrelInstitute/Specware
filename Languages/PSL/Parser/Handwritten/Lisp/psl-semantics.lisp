;;; ======================================================================
;;; The next portion of the file deals with terms in the procedural
;;; specification language (PSL).

(defun make-procspec (decls l r) 
  :comment "A specification" 
  (setq *varcounter* 0)
  (let ((decls (if (eq :unspecified decls) nil decls)))
    (cons (cons :|PSL| decls) (make-pos l r))))

(defun make-psl-var-decl (varName sortScheme l r)
  (cons
    (cons :|Var| (cons varName (vector nil sortScheme (cons :|None| nil))))
    (make-pos l r)))

(defun make-psl-proc-def (procName args returnSort commands l r)
  (let* ((args1 (if (eq :unspecified args) nil args))
         (commands1 (if (eq :unspecified commands) nil commands)))
        (cons (cons :|Proc|
                    (cons procName
                         (vector args1
                                    (make-psl-seq commands1 l r) returnSort))) 
              (make-pos l r))))

(defun make-psl-relation (term l r)
  (cons (cons :|Relation| term) (make-pos l r)))

(defun make-psl-seq (commands l r)
  (cons (cons :|Seq| commands) (make-pos l r)))

(defun make-psl-if (alternatives l r)
  (cons (cons :|If| alternatives) (make-pos l r)))

(defun make-psl-do (alternatives l r)
  (cons (cons :|Do| alternatives) (make-pos l r)))

(defun make-psl-case (term cases l r)
  (cons (cons :|Case| (cons term cases)) (make-pos l r)))

(defun make-psl-let (decls commands l r)
  (cons
    (cons :|Let| (cons decls (make-psl-seq commands l r))) 
    (make-pos l r)))

(defun make-psl-call (id params l r)
  (let ((params1 (if (eq :unspecified params) nil params)))
  (cons
    (cons :|Call| (cons id params1)) 
    (make-pos l r))))

(defun make-psl-assign-call (term id params l r)
  (let ((params1 (if (eq :unspecified params) nil params)))
  (cons
    (cons :|AssignCall| (vector term id params1)) 
    (make-pos l r))))

(defun make-psl-assign (left right l r)
  (cons (cons :|Assign| (cons left right)) (make-pos l r)))

(defun make-psl-exec (term l r)
  (cons (cons :|Exec| term) (make-pos l r)))

(defun make-psl-skip (l r)
  (cons (cons :|Skip| nil) (make-pos l r)))

(defun make-psl-return (term l r)
  (cons (cons :|Return| term) (make-pos l r)))

(defun make-psl-alternative (guard commands l r)
  (cons (cons guard (make-psl-seq commands l r)) (make-pos l r)))

;; Identical to the Specware make-op-definition .. only the constructor has changed from Op to Def
(defun make-psl-op-definition (tyVars qualifiable-op-names params optional-sort term l r)
  (let* ((params     (if (equal :unspecified params) nil params))
         (tyVars     (if (equal :unspecified tyVars) nil tyVars))
         (term       (if (equal :unspecified optional-sort) term (make-sorted-term term optional-sort l r)))
         (term       (bind-parameters params term l r))
         (tyVarsTerm (PosSpec::abstractTerm #'namedTypeVar tyVars term))
         (term       (cdr tyVarsTerm))
         (tyVars     (car tyVarsTerm))
         (srtScheme  (cons tyVars (freshMetaTypeVar l r))))
    ;; Since namedTypeVar is the identity function,
    ;;  (car tyVarsTerm) will just be a copy of tyVars
    ;;    so srtScheme will be tyVars * Mtv -- i.e. Mtv parameterized by tyVars
    ;;  (cdr tyVarsTerm) will be a copy of term with (PBase qid) replaced by (TyVar id) where appropriate.
    ;; TODO: Move the responsibility for all this conversion into the linker.
    (cons (cons :|Def| (cons (remove-duplicates qualifiable-op-names :test 'equal :from-end t)
                            (vector nil srtScheme (cons :|Some| term))))
      (make-pos l r))))

