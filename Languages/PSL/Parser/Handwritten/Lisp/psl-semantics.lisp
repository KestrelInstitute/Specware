;;; This file deals with terms in the procedural
;;; specification language (PSL).
(defpackage "OscarAbsSyn")
(in-package "PARSER4")

;; Identical to the Specware make-op-definition .. only the constructor has changed from Op to Def
(defun make-psl-op-definition (tyVars qualifiable-op-names params optional-sort term l r)
  (let* ((params     (if (equal :unspecified params) nil params))
         (tyVars     (if (equal :unspecified tyVars) nil tyVars))
         (term       (if (equal :unspecified optional-sort) term (make-sorted-term term optional-sort l r)))
         (term       (bind-parameters params term l r))
         (tyVarsTerm (StandardSpec::abstractTerm-3 #'namedTypeVar tyVars term))
         (term       (cdr tyVarsTerm))
         (tyVars     (car tyVarsTerm))
         (srtScheme  (cons tyVars (freshMetaTypeVar l r)))
         (qids       (remove-duplicates qualifiable-op-names :test 'equal :from-end t)))
    ;; Since namedTypeVar is the identity function,
    ;;  (car tyVarsTerm) will just be a copy of tyVars
    ;;    so srtScheme will be tyVars * Mtv -- i.e. Mtv parameterized by tyVars
    ;;  (cdr tyVarsTerm) will be a copy of term with (PBase qid) replaced by (TyVar id) where appropriate.
    ;; TODO: Move the responsibility for all this conversion into the linker.
    (OscarAbsSyn::mkDef-5 qids Option::None srtScheme (list (cons tyVars term)) (make-pos l r))))
