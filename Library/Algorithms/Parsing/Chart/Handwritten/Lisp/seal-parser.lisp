;;; -*- Mode: LISP; Package: Parser4; Base: 10; Syntax: Common-Lisp -*-

(in-package "PARSER4") 

(defun load-parser (file &key 
			 (name (intern (gensym "PARSER-") "KEYWORD"))
			 (case-sensitive? nil)
			 (rule-package    (find-package "KEYWORD"))
			 (symbol-package  common-lisp::*package*))
  (let ((new-parser (new-parser name 
				:case-sensitive? case-sensitive?
				:rule-package    rule-package
				:symbol-package  symbol-package)))
    (setq *current-parser* new-parser)
    (when (null (pathname-type file))
      (let ((fasl-file (make-pathname :type "fasl" :defaults file))
	    (lisp-file (make-pathname :type "lisp" :defaults file)))
	(when (<= (or (file-write-date fasl-file) 0)
		  (file-write-date lisp-file))
	  (compile-file lisp-file))))
    (load file)				; see parse-add-rules.lisp  
    (setf (parser-keywords-are-keywords-only? new-parser) t)
    (seal-parser new-parser)
    (when-debugging
     (comment "New parser is also in PARSER4::*CURRENT-PARSER*"))
    new-parser))

(defun seal-parser (parser)
    ;;

    (when-debugging
     (comment "============================================================================")
     (comment "Sealing parser")
     (comment "================================="))
    ;;
    
    (when-debugging
     (verify-all-parser-rule-references parser))

    (install-rules                  parser) ; sets parser-rules
    (bypass-id-rules                parser) 
    (install-reductions             parser) ; sets parser-ht-name-to-reductions
    (install-parents                parser) ; sets parser-rule-reductions
    (install-bvs                    parser) ; sets parser-bv-size 
					    ;   parser-scratch-bv, parser-zero-bv
					    ;   parser-rule-bvi
					    ;   parser-rule-item-possible-handles-bv
    ;;
    (install-default-semantic-alist parser) ; sets parser-default-semantic-alist
    (install-special-rules          parser) ; finds toplevel, symbol, number, string, etc.
    ;;
    (propagate-optionals            parser) ; items referencing optional rules become optional themselves
    (install-pprinters              parser) ; sets parser-ht-expr-to-pprint, 
                                            ;   parser-ht-type-to-pprint,
                                            ;   parser-ht-car-to-pprint
    ;;
    (when-debugging
     (comment "============================================================================"))
    )

;;; ====================

(defun install-rules (parser)
  (when-debugging
   (comment "=================================")
   (comment "Installing rules")
   (comment "- - - - - - - - - - - - - - - - -"))
  (maphash #'(lambda (ignore-name rule) 
	       (declare (ignore ignore-name))
	       ;; (when (parental-parser-rule? rule))
	       (push rule (parser-rules parser))
	       ;; parser-total-rule-count is used only for commentary
	       (incf (parser-total-rule-count parser)))
	   (parser-ht-name-to-rule parser)))

;;; ====================

(defun bypass-id-rules (parser)
  (when-debugging
   (comment "=================================")
   (comment "Bypassing id rules")
   (comment "- - - - - - - - - - - - - - - - -"))
  ;; efficiency hack to eliminate id reductions
  ;; (A) avoids those reductions
  ;; (B) makes desired-bv's smaller (hence more efficeient) since id rules become irrelevant
  (dolist (rule (parser-rules parser))
    (bypass-children-id-rules parser rule)))

(defun bypass-children-id-rules (parser rule)
  (debugging-comment "Replacing any id rules in ~20A ~S" 
		     (structure-type-of rule) 
		     (parser-rule-name rule))
  (do-parser-rule-items (item rule)
    (unless (null item)
      (bypass-any-id-rule-in-item parser item))))


(defun bypass-any-id-rule-in-item (parser item)
  (when-debugging
   (unless (parser-rule-item-p item)
     (break "Expected parser-rule-item: ~S" item)))
  (let* ((child-rule-name (parser-rule-item-rule item))
	 #+DEBUG-PARSER (original-name child-rule-name)
	 (child-rule (find-parser-rule parser child-rule-name)))
    (when (parser-id-rule-p child-rule)
      (loop while (parser-id-rule-p child-rule) do
	(setq child-rule-name (parser-id-rule-subrule child-rule))
	(setq child-rule (find-parser-rule parser child-rule-name)))
      (debugging-comment "    Replacing ~S by ~S" original-name child-rule-name)
      (setf (parser-rule-item-rule item) child-rule-name))))

;;; ====================

(defun install-reductions (parser)
  (when-debugging
   (comment "=================================")
   (comment "Installing reductions")
   (comment "- - - - - - - - - - - - - - - - -"))
  ;;
  (clrhash (parser-ht-name-to-reductions parser))
  ;;
  (dolist (rule (parser-rules parser))
    (note-reductions-to parser rule))
  ;;
  (bypass-reductions-to-superfluous-anyof-rules parser)
  )

(defun note-reductions-to (parser parent-rule)
  (ecase (structure-type-of parent-rule) ; faster than etypecase since we're doing exact matches
    (parser-anyof-rule 
     (do-parser-rule-items (item parent-rule nil i)
       (note-reduction-to parser parent-rule i item)))
    (parser-tuple-rule   
     (do-parser-rule-items (item parent-rule nil i)
       (note-reduction-to parser parent-rule i item)))
    (parser-pieces-rule
     (do-parser-rule-items (item parent-rule nil i)
       (note-reduction-to parser parent-rule i item)))
    (parser-repeat-rule
     (note-reduction-to parser parent-rule 0 (parser-repeat-rule-element   parent-rule))
     (unless (null (parser-repeat-rule-separator parent-rule))
       (note-reduction-to parser parent-rule 1 (parser-repeat-rule-separator parent-rule))))
    (parser-id-rule      nil)
    (parser-keyword-rule nil)
    (parser-atomic-rule  nil)
    ))

(defun note-reduction-to (parser parent-rule position item)
  (let ((child-name (parser-rule-item-rule item)))
    (when-debugging
     (unless (symbolp child-name) (break "Expected child to be a symbol: ~S" child-name)))
    (push (make-reduction :parent-rule parent-rule 
			  :child-index position)
	  (gethash child-name (parser-ht-name-to-reductions parser)))))

(defun bypass-reductions-to-superfluous-anyof-rules (parser)
  (let ((ht-name-to-reductions (parser-ht-name-to-reductions parser))
	(done? nil))
    (loop until done? do
      (let ((reductions-to-bypass nil))
	(maphash 
	 #'(lambda (child-name reductions)
	     (dolist (reduction reductions)
	       (when (superfluous-anyof-rule? (reduction-parent-rule reduction))
		 (push (cons child-name reduction) 
		       reductions-to-bypass))))
	 ht-name-to-reductions)
	(setq done? (null reductions-to-bypass))
	(dolist (bypass reductions-to-bypass)
	  (let* ((child-name (car bypass))
		 (reduction  (cdr bypass))
		 (parent-rule (reduction-parent-rule reduction))
		 (parent-name (parser-rule-name parent-rule))
		 (parent-reductions (gethash parent-name ht-name-to-reductions)))
	    (setf (gethash child-name ht-name-to-reductions)
	      (append (remove reduction (gethash child-name ht-name-to-reductions))
		      parent-reductions))))))
    ))

;;; ====================

(defun install-parents (parser)
  (when-debugging
   (comment "=================================")
   (comment "Installing rule parents")
   (comment "- - - - - - - - - - - - - - - - -"))
  ;;
  (maphash #'(lambda (child-name reductions)
	       (add-parser-rule-parents parser child-name reductions))
	   (parser-ht-name-to-reductions parser)))

(defun add-parser-rule-parents (parser child-name reductions)
  ;; child -> (... (parent . position) ...)
  (let* ((child-rule (find-parser-rule parser child-name))
	 (head-reductions
	  (remove-if-not #'(lambda (reduction)
			     (possible-start-of-reduction? child-rule reduction))
			 reductions)))
    (cond ((null head-reductions)
	   (debugging-comment "~50S no head reductions" child-name)
	   nil)
	  ((keyword-triggered-rule? parser child-name)
	   (debugging-comment "~50S -- Keyword triggered rule, head for reductions: ~:{~S.~D ~}" 
			      child-name
			      (mapcar #'(lambda (reduction)
					  (list (parser-rule-name (reduction-parent-rule reduction))
						(reduction-child-index reduction)))
				      head-reductions))
	   (dolist (reduction head-reductions)
	     (push reduction (parser-rule-reductions child-rule))))
	  ((null (rest head-reductions))
	   (let ((only-head-reduction (first head-reductions)))
	     (debugging-comment "~50S -- Head for just one reduction: ~S.~D)" 
				child-name 
				(parser-rule-name (reduction-parent-rule only-head-reduction))
				(reduction-child-index only-head-reduction))
	     (push only-head-reduction
		   (parser-rule-reductions child-rule))))
	  (t 
	   (debugging-comment "~50S -- Head for multiple reductions: ~:{~S.~D ~}" child-name
			      (mapcar #'(lambda (reduction)
					  (list (parser-rule-name (reduction-parent-rule reduction))
						(reduction-child-index reduction)))
				      head-reductions))
	   (dolist (reduction head-reductions)
	     (push reduction (parser-rule-reductions child-rule)))
	   ))))

(defun possible-start-of-reduction? (child-rule reduction)
  (let* ((parent-rule (reduction-parent-rule reduction))
	 (child-index (reduction-child-index reduction)))
    (and (or (eq child-index 0)
	     (parser-anyof-rule-p parent-rule)
	     (parser-pieces-rule-p parent-rule)
	     (and (parser-tuple-rule-p parent-rule)
		  (let ((items (parser-tuple-rule-items parent-rule)))
		    ;; following returns true iff all the items preceeding 
		    ;; child-index are optional, i.e. have a car of t
		    (dotimes (i child-index t)
		      (unless (parser-rule-item-optional? (svref items i))
			(return nil))))))
	 (let ((child-precedence (parser-rule-precedence child-rule)))
	   (or (null child-precedence)
	       (or (not (parser-tuple-rule-p parent-rule))
		   (let* ((parent-item (svref (parser-tuple-rule-items parent-rule) 
					      child-index))
			  (parent-precedence (parser-rule-item-precedence parent-item)))
		     (or (null parent-precedence)
			 (>= parent-precedence child-precedence)))))))))

(defun keyword-triggered-rule? (parser rule-name)
  (aux-keyword-triggered-rule? parser rule-name nil))

(defun aux-keyword-triggered-rule? (parser item-or-rule-name parent-rule-names)
  (let ((rule-name
	 (if (parser-rule-item-p item-or-rule-name)
	     (parser-rule-item-rule item-or-rule-name)
	   item-or-rule-name)))
    (if (member rule-name parent-rule-names)
	nil
      (let ((rule (find-parser-rule parser rule-name)))
	(cond ((parser-keyword-rule-p rule) 
	       t)
	      ((parser-id-rule-p rule)  
	       (aux-keyword-triggered-rule? parser
					    (parser-id-rule-subrule rule) 
					    (push rule-name parent-rule-names)))
	      ((parser-anyof-rule-p rule) 
	       (do-parser-rule-items (item rule t)
		 (unless (aux-keyword-triggered-rule? 
			  parser
			  item
			  (push rule-name parent-rule-names))
		   (return nil))))
	      ((parser-tuple-rule-p rule) 
	       (do-parser-rule-items (item rule t)
		 (cond ((not (aux-keyword-triggered-rule? 
			      parser
			      item
			      (push rule-name parent-rule-names)))
			(return nil))
		       ((not (parser-rule-item-optional? item))
			(return t)))))
	      ((parser-pieces-rule-p rule) 
	       (do-parser-rule-items (item rule t)
		 (unless (aux-keyword-triggered-rule? 
			  parser
			  item
			  (push rule-name parent-rule-names))
		   (return nil))))
	      (t
	       nil))))))

;;; ====================

(defun install-bvs (parser)
  (when-debugging
   (comment "=================================")
   (comment "Installing bit vectors")
   (comment "- - - - - - - - - - - - - - - - -"))
  (install-p2bvi-keys           parser) ; initializes parser-rule-p2bvi alist
  (install-p2bvi-values         parser) ; puts values into parser-rule-p2bvi alist
  (install-rule-bvis            parser)
  (install-bv-size              parser) ; sets parser-bv-size
  (install-aux-bvs              parser) ; sets parser-scratch-bv, parser-zero-bv
  (install-ht-rnp-to-handles-bv parser) ; sets parser-ht-rnp-to-handles-bv,
					; parser-rule-item-possible-handles-bv,
					; parser-rule-item-possible-children-bv
  )

;;; ====================

(defun install-p2bvi-keys (parser)
  (initialize-p2bvi-keys          parser)
  (compute-closure-for-p2bvi-keys parser)
  (finalize-p2bvi-keys            parser))

(defun initialize-p2bvi-keys (parser)
  (when-debugging 
   (comment "Initializing precedences"))
  (dolist (rule (parser-rules parser))
    (let ((rule-precedence (parser-rule-precedence rule)))
      ;; default is 0, so null means user explicitly said "no (i.e. any) precedence"
      (setf (parser-rule-p2bvi-map rule)	
	`((,rule-precedence))))))

(defun compute-closure-for-p2bvi-keys (parser)
  (when-debugging 
   (comment "Computing fixpoint for precedences"))
  (let (#+DEBUG-PARSER (n 0)
	(rules (parser-rules parser))
	(do-another-round? t))
    ;; find fixpoint...
    ;; When done, p2bvi-map has alist for possible precedences for each rule.
    ;; If there is no explicit precedence for an anyof rule, it gets all the precedences
    ;;  of it's child rules.
    (loop while do-another-round? do
	  (when-debugging (comment " Precedences Round ~D" (incf n)))
	  (setq do-another-round? nil)
	  (dolist (rule rules)
	    (when (case (structure-type-of rule) ; faster than etypecase since we are doing exact matches
		    (parser-anyof-rule (update-p2bvi-keys-for-anyof-rule parser rule))
		    (otherwise         nil))
	      (setq do-another-round? t))))))

(defun update-p2bvi-keys-for-anyof-rule (parser anyof-rule)
  (cond ((not (null (parser-rule-precedence anyof-rule)))
	 ;; use explicit precedence
	 nil)
	((null (parser-rule-semantics anyof-rule))
	 ;; if there is no precedence but also no semantics, this anyof rule is superfluous
	 ;; and will be bypassed..
	 nil)
	(t
	 ;; Since we have semantics, we need to build explicit nodes for this rule.
	 ;; But since we do not have an explicit precedence, we must effectively 
	 ;; create a version of this rule for each precedence from a child rule.
	 ;; That versioning information is kept in parser-rule-p2bvi-map,
	 ;; where each entry will get its own bit-veector-index..
	 (let* ((anyof-p2bvi-alist (parser-rule-p2bvi-map anyof-rule))
		(changed?          nil))
	   (do-parser-rule-items (item anyof-rule)
	     (let* ((child-rule-name        (parser-rule-item-rule   item))
		    (child-rule             (find-parser-rule parser child-rule-name))
		    (child-rule-p2bvi-alist (parser-rule-p2bvi-map   child-rule)))
	       (dolist (p2bvi-pair child-rule-p2bvi-alist)
		 (let ((child-rule-precedence (car p2bvi-pair)))
		   (unless (assoc child-rule-precedence anyof-p2bvi-alist)
		     (setq changed? t))
		   (push (cons child-rule-precedence nil) anyof-p2bvi-alist)))))
	   (when changed?
	     (setf (parser-rule-p2bvi-map anyof-rule) anyof-p2bvi-alist))
	   changed?))))

;;; ===

(defun finalize-p2bvi-keys (parser)
  ;; why bother sorting?? 
  (dolist (rule (parser-rules parser))
    (let* ((raw-p2bvi-alist (parser-rule-p2bvi-map rule))
	   (null-pair (assoc nil raw-p2bvi-alist))
	   (sorted-p2bvi-alist
	    (sort (remove null-pair raw-p2bvi-alist)
		  #'(lambda (x y) (< (car x) (car y))))))
      ;; (when (null sorted-p2bvi-alist) (setq sorted-p2bvi-alist (list (cons 0 nil))))
      (setf (parser-rule-p2bvi-map rule) 
	(if (null null-pair)
	    sorted-p2bvi-alist
	  (cons null-pair sorted-p2bvi-alist))))))

;;; ====================

(defun install-p2bvi-values (parser)
  (when-debugging 
   (comment "Installing maps for precedence to bv indices"))
  (let ((bv-index -1))
    (dolist (rule (parser-rules parser))
      (when ;(and (parental-parser-rule? rule)
	  (not (superfluous-anyof-rule? rule))
					;)
	(dolist (p2bvi-pair (parser-rule-p2bvi-map rule))
	  (setf (cdr p2bvi-pair) (incf bv-index)))))))

;;; ====================

(defun install-rule-bvis (parser)
  ;; why bother sorting?? 
  (dolist (rule (parser-rules parser))
    (let ((p2bvi-alist (parser-rule-p2bvi-map rule)))
      (when (null (rest p2bvi-alist))
	(setf (parser-rule-bvi rule) (cdr (first p2bvi-alist)))))))

;;; ====================

(defun install-bv-size (parser)
  (when-debugging 
   (comment "Computing bv size"))
  (dolist (rule (parser-rules parser))
    (when ;;(and (parental-parser-rule? rule)
	       (not (superfluous-anyof-rule? rule))
      ;;)
      (incf (parser-bv-size parser) 
	    (length (parser-rule-p2bvi-map rule)))))
  (when-debugging 
   (comment "  bv-size = ~D" (parser-bv-size parser))))

;;; ====================

(defun install-aux-bvs (parser)
  (when-debugging 
   (comment "Installing aux bv's"))
  (let ((bv-size (parser-bv-size parser)))
    (setf (parser-scratch-bv parser)
	  (make-array bv-size 
		      :element-type    'bit
		      :initial-element 0))
    (setf (parser-zero-bv parser)
	  (make-array bv-size 
		      :element-type    'bit
		      :initial-element 0))))


;;; ====================

(defun install-ht-rnp-to-handles-bv (parser) 
  ;; Create the mapping (rule . precedence) => bit-vector of handles
  (initialize-ht-rnp-to-handles-bv  parser)
  (compute-closures-for-handles-bvs parser)
  (install-rule-item-bvs            parser)
  (install-possible-children-bvs    parser)
  (install-composite-handles-bvs    parser)
  )

;;; ===

(defun initialize-ht-rnp-to-handles-bv (parser)
  (let ((ht-rnp-to-handles-bv (parser-ht-rnp-to-handles-bv parser))
	(bv-size              (parser-bv-size              parser)))
    (clrhash ht-rnp-to-handles-bv)
    (dolist (rule (parser-rules parser))
      (let ((rule-name (parser-rule-name rule)))
	(dolist (p2bvi-pair (parser-rule-p2bvi-map rule))
	  (let* ((precedence (car p2bvi-pair))
		 (bv-index   (cdr p2bvi-pair)) 
		 (rnp (cons rule-name precedence)) 
		 (handles-bv (make-array bv-size 
					 :element-type    'bit
					 :initial-element 0)))
	    (unless (null bv-index)
	      (setf (sbit handles-bv bv-index) 1))
	    (setf (gethash rnp ht-rnp-to-handles-bv) handles-bv)))))))
	      

;;; ===

(defun compute-closures-for-handles-bvs (parser)
  (when-debugging
   (comment "Computing fixpoint for desired bv's."))
  (let ((rules (parser-rules parser))
	#+DEBUG-PARSER (n 0)
	(do-another-round? t))
    ;;
    ;; add entry for (rn . nil)
    ;;
    (let ((ht-rnp-to-handles-bv (parser-ht-rnp-to-handles-bv parser))
	  (bv-size (parser-bv-size parser)))
      (dolist (rule rules)
	(let* ((rule-name (parser-rule-name rule))
	       (rn-nullp (cons rule-name nil)))
	  (when (null (gethash rn-nullp ht-rnp-to-handles-bv))
	    (let ((p2bvi-alist (parser-rule-p2bvi-map rule))
		  (null-p-handles-bv (make-array bv-size 
						 :element-type    'bit
						 :initial-element 0)))
	      (dolist (p2bvi p2bvi-alist)
		(let* ((precedence (car p2bvi))
		       (rnp-handles-bv (gethash (cons rule-name precedence)
						ht-rnp-to-handles-bv)))
		  (bit-ior null-p-handles-bv rnp-handles-bv null-p-handles-bv)))
	      (setf (gethash rn-nullp ht-rnp-to-handles-bv)
		null-p-handles-bv))))))
    ;;
    ;; Propagate until fixpoint
    ;;
    (loop while do-another-round? do
	  (when-debugging (comment "Round ~D" (incf n)))
	  (setq do-another-round? nil)
	  (dolist (rule rules)
	    (when (ecase (structure-type-of rule) ; faster than etypecase since we are doing exact matches
		    (parser-anyof-rule   (update-handles-bv-for-anyof-rule  parser rule))
		    (parser-pieces-rule  (update-handles-bv-for-pieces-rule parser rule))
		    (parser-tuple-rule   (update-handles-bv-for-tuple-rule  parser rule))
		    (parser-repeat-rule  (update-handles-bv-for-repeat-rule parser rule))
		    (parser-id-rule      nil)
		    (parser-keyword-rule nil)
		    (parser-atomic-rule  nil)
		    )
	      (setq do-another-round? t))))
    ))

(defun update-handles-bv-for-anyof-rule (parser rule)
  ;;
  ;; This code is tricky, and depends on the fact that an anyof rule may 
  ;; be used in three different ways, depending on exisitance of semantics
  ;; and/or explicit precedence.
  ;; 
  ;;  Case 1: precedence
  ;;  Case 2: no precedence, but semantics
  ;;  Case 3: no precedence, no semantics
  ;;
  ;;  In cases 1 and 2, we need to build a node for occurrences of this rule,
  ;; where in case 3, we can bypass this rule.
  ;;
  ;;  In cases 2, we don't have a fixed precedence, but must carry along
  ;;  the precedence we get from the child rule, which is a bit messy.
  ;;  The net result in that case is that we have several bit vector indices
  ;;  for the same rule, so it is really a concise implementation of a family
  ;;  of rules.
  ;;
  (let* ((ht-rnp-to-handles-bv (parser-ht-rnp-to-handles-bv parser))
	 ;; ht-rnp-to-handles-bv:  (rule . precedence) => handles-bv
	 (anyof-rule-name  (parser-rule-name       rule))
	 (anyof-precedence (parser-rule-precedence rule))
	 (primary-anyof-handles-bv 
	  (if (null anyof-precedence)
	      ;; no fixed precedence, so there is not just one handles-bv (see below)
	      nil
	    ;; fixed precedence, so there is just one handles-bv
	    (gethash (cons anyof-rule-name anyof-precedence) ht-rnp-to-handles-bv)))
	 ;;
	 (scratch-bv (parser-scratch-bv parser))
	 (changed?   nil))
    ;;
    (do-parser-rule-items (item rule)
      (let* ((item-precedence (parser-rule-item-precedence item))
	     (item-rule-name  (parser-rule-item-rule       item))
	     (child-rule      (find-parser-rule parser item-rule-name))
	     (child-p2bvi-alist (parser-rule-p2bvi-map child-rule))
	     (max-pair 
	      (let ((local-max-pair nil))
		(dolist (p2bvi-pair child-p2bvi-alist)
		  (let ((child-possible-precedence (car p2bvi-pair)))
		    (if (or (null item-precedence)
			    (< child-possible-precedence item-precedence))
			(setq local-max-pair p2bvi-pair)
		      (return nil))))
		local-max-pair))
	     (max-acceptable-child-precedence (car max-pair))
	     (item-rnp (cons item-rule-name max-acceptable-child-precedence))
	     (item-handles-bv (gethash item-rnp ht-rnp-to-handles-bv)))
	;;
	;;
	;; item-handles-bv will be nil for keywords, etc.
	;;
	(unless (null item-handles-bv)
	  (let ((anyof-handles-bv 
		 (or 
		  ;; if there is a fixed precedence for anyof rule, use
		  ;; that,
		  primary-anyof-handles-bv 
		  ;; else get bv for version of anyof rule with same precedence as child
		  (gethash (cons anyof-rule-name 
				 max-acceptable-child-precedence)
			   ht-rnp-to-handles-bv))))
	    ;; if rule is superfluous, the handles may be null
	    (unless (null anyof-handles-bv)
	      (bit-andc1 anyof-handles-bv item-handles-bv scratch-bv)
	      (bit-ior   anyof-handles-bv item-handles-bv anyof-handles-bv)
	      (unless (equal scratch-bv (parser-zero-bv parser))
		(setq changed? t)))))))
    changed?))

(defun update-handles-bv-for-pieces-rule (parser rule)
  (let* ((ht-rnp-to-handles-bv (parser-ht-rnp-to-handles-bv parser))
	 ;;
	 (pieces-rnp        (cons (parser-rule-name       rule) 
				  (parser-rule-precedence rule))) 
	 (pieces-handles-bv (gethash pieces-rnp ht-rnp-to-handles-bv))
	 ;;
	 (scratch-bv (parser-scratch-bv parser))
	 (changed?   nil))
    ;;
    (do-parser-rule-items (item rule)
      (let* ((item-rnp        (cons (parser-rule-item-rule       item)
				    (parser-rule-item-precedence item)))
	     (item-handles-bv (gethash item-rnp ht-rnp-to-handles-bv)))
	;;
	;;
	;; item-handles-bv will be nil for keywords, etc.
	;;
	(unless (null item-handles-bv)
	  (bit-andc1 pieces-handles-bv item-handles-bv scratch-bv)
	  (bit-ior   pieces-handles-bv item-handles-bv pieces-handles-bv)
	  (unless (equal scratch-bv (parser-zero-bv parser))
	    (setq changed? t)))))
    changed?))

(defun update-handles-bv-for-tuple-rule (parser rule)
  (let* ((ht-rnp-to-handles-bv  (parser-ht-rnp-to-handles-bv parser))
	 ;;
	 (tuple-rnp        (cons (parser-rule-name       rule) 
				 (parser-rule-precedence rule))) 
	 (tuple-handles-bv (gethash tuple-rnp ht-rnp-to-handles-bv))
	 ;; 
	 (scratch-bv  (parser-scratch-bv parser))
	 (changed?    nil))
    ;;
    (do-parser-rule-items (head-item rule)
      ;; repeat for each item that can start production     (dotimes (i (length items))
      (let* ((item-rule-name  (parser-rule-item-rule       head-item))
	     (item-precedence (parser-rule-item-precedence head-item))
	     (item-rnp (cons item-rule-name item-precedence))
	     (item-handles-bv (gethash item-rnp ht-rnp-to-handles-bv)))
	;;
	;; item-handles-bv will be nil for keywords, etc.
	;;
	(unless (null item-handles-bv)
	  (bit-andc1 tuple-handles-bv item-handles-bv scratch-bv)
	  (bit-ior   tuple-handles-bv item-handles-bv tuple-handles-bv)
	  (unless (equal scratch-bv (parser-zero-bv parser))
	    (setq changed? t)))
	(unless (parser-rule-item-optional? head-item)
	  (return nil))))
    changed?))

(defun update-handles-bv-for-repeat-rule (parser rule)
  (let* ((ht-rnp-to-handles-bv (parser-ht-rnp-to-handles-bv parser))
	 ;;
	 (repeat-rnp           (cons (parser-rule-name       rule) 
				     (parser-rule-precedence rule))) 
	 (repeat-handles-bv    (gethash repeat-rnp ht-rnp-to-handles-bv))
	 ;;
	 (element-item         (parser-repeat-rule-element  rule))
	 (element-rnp          (cons (parser-rule-item-rule       element-item)
				     (parser-rule-item-precedence element-item)))
	 (element-handles-bv   (gethash element-rnp ht-rnp-to-handles-bv))
	 ;;
	 (scratch-bv           (parser-scratch-bv parser))
	 (changed?             nil))
    ;;
    ;; element-handles-bv will be nil for :SYMBOL rule
    ;;
    (unless (null element-handles-bv)
      (bit-andc1 repeat-handles-bv element-handles-bv scratch-bv)
      (bit-ior   repeat-handles-bv element-handles-bv repeat-handles-bv)
      (unless (equal scratch-bv (parser-zero-bv parser))
	(setq changed? t)))
    changed?))

;;; ===

(defun install-rule-item-bvs (parser)
  (let ((ht-rnp-to-handles-bv (parser-ht-rnp-to-handles-bv parser))
	(bv-size              (parser-bv-size              parser)))
    ;;
    (dolist (rule (parser-rules parser))
      (do-parser-rule-items (item rule)
	(unless (null item)		; can happen for repeat rules
	  (let* ((item-precedence   (parser-rule-item-precedence item))
		 (item-rule-name    (parser-rule-item-rule       item))
		 (child-rule        (find-parser-rule parser item-rule-name))
		 (child-p2bvi-alist (parser-rule-p2bvi-map child-rule))
		 (children-bv       (make-array bv-size 
						:element-type    'bit
						:initial-element 0))
		 (handles-bv 
		  (let ((max-allowed-precedence-seen nil)) 
		    (dolist (p2bvi-pair child-p2bvi-alist)
		      (let ((child-possible-precedence (car p2bvi-pair))
			    (child-possible-bvi        (cdr p2bvi-pair)))
			(cond ((null child-possible-bvi)
			       nil)
			      ((or (null item-precedence)
				   (null child-possible-precedence)
				   (<= child-possible-precedence item-precedence))
			       (setf (sbit children-bv child-possible-bvi) 1)
			       (when (or (null max-allowed-precedence-seen)
					 (> child-possible-precedence 
					    max-allowed-precedence-seen))
				 (setq max-allowed-precedence-seen
				   child-possible-precedence))))))
		    (let* ((effective-item-precedence (if (null item-precedence) 
							  item-precedence
							max-allowed-precedence-seen))
			   (item-rnp (cons item-rule-name effective-item-precedence)))
		      (gethash item-rnp ht-rnp-to-handles-bv)))))
	    (setf (parser-rule-item-possible-children-bv item) children-bv)
	    (setf (parser-rule-item-possible-handles-bv  item) (bit-ior handles-bv children-bv))))))))


(defun install-possible-children-bvs (parser)
  ;; don't just look at parser-rule-reductions -- 
  ;;  those only include the reductions for which rule is a handle
  (maphash #'(lambda (rule-name reductions)
	       (let ((child-rule (find-parser-rule parser rule-name)))
		 (when (not (superfluous-anyof-rule? child-rule)) 
		   (let ((child-rule-bvi (parser-rule-bvi child-rule))
			 (child-rule-precedence (parser-rule-precedence child-rule)))
		     (dolist (reduction reductions)
		       (let* ((parent-rule (reduction-parent-rule reduction))
			      (child-index (reduction-child-index reduction))
			      (item (svref (parser-rule-items parent-rule) child-index))
			      (item-precedence (parser-rule-item-precedence item))
			      (children-bv (parser-rule-item-possible-children-bv item))
			      (handles-bv  (parser-rule-item-possible-handles-bv  item)))
			 (when (or (null item-precedence)
				   (null child-rule-precedence)
				   (<= child-rule-precedence item-precedence))
			   (setf (sbit children-bv child-rule-bvi) 1)
			   (setf (sbit handles-bv  child-rule-bvi) 1)
			   )))))))
	   (parser-ht-name-to-reductions parser)))

;;; ===

(defun install-composite-handles-bvs (parser)
  (let ((bv-size (parser-bv-size parser)))
    (dolist (rule (parser-rules parser))
      (case (structure-type-of rule) ; faster than etypecase since we are doing exact matches
	(parser-anyof-rule 
	 (let ((composite-handles-bv (make-array bv-size 
						 :element-type    'bit
						 :initial-element 0)))
	   (unless (null (parser-rule-bvi rule))
	     (setf (sbit composite-handles-bv (parser-rule-bvi rule)) 1))
	   (do-parser-rule-items (item rule)
	     (let* ((item-handles-bv (parser-rule-item-possible-handles-bv item)))
	       (unless (null item-handles-bv)
		 (bit-ior composite-handles-bv item-handles-bv composite-handles-bv))))
	   (setf (parser-anyof-rule-possible-handles-bv rule) composite-handles-bv)))
	(parser-pieces-rule
	 (let ((composite-handles-bv (make-array bv-size 
						 :element-type    'bit
						 :initial-element 0)))
	   (setf (sbit composite-handles-bv (parser-rule-bvi rule)) 1)
	   (do-parser-rule-items (item rule)
	     (let* ((item-handles-bv (parser-rule-item-possible-handles-bv item)))
	       (unless (null item-handles-bv)
		 (bit-ior composite-handles-bv item-handles-bv composite-handles-bv))))
	   (setf (parser-pieces-rule-possible-handles-bv rule) composite-handles-bv)))
	))))


;;; ====================

(defun install-default-semantic-alist (parser)
  (when-debugging
   (comment "=================================")
   (comment "Installing default semantic alist")
   (comment "- - - - - - - - - - - - - - - - -"))
  (let ((all-numbers '())
	(alist '()))
    (dolist (rule (parser-rules parser))
      (let* ((pattern (parser-rule-semantics rule))
	     (numbers (find-numbers-in pattern)))
	(dolist (number numbers)
	  (pushnew number all-numbers))))
    (dolist (number all-numbers)
      (push (cons number :unspecified) alist))
    (setf (parser-default-semantic-alist parser) 
	  alist)))

(defun find-numbers-in (pattern)
  (cond ((numberp pattern) (list pattern))
	((atom pattern) nil)
	(t
	 (nconc (find-numbers-in (car pattern))
		(find-numbers-in (cdr pattern))))))


;;; ====================

(defun install-special-rules (parser)
  (when-debugging
   (comment "=================================")
   (comment "Installing special rules")
   (comment "- - - - - - - - - - - - - - - - -"))
  (let ((symbol-rule    (maybe-find-parser-rule parser :SYMBOL))
	(string-rule    (maybe-find-parser-rule parser :STRING))
	(number-rule    (maybe-find-parser-rule parser :NUMBER))
	(character-rule (maybe-find-parser-rule parser :CHARACTER))
	(toplevel-rule  (maybe-find-parser-rule parser :TOPLEVEL)))
    (when (null symbol-rule)
      (warn "Cannot find rule named :SYMBOL"))
    (when (null string-rule)
      (warn "Cannot find rule named :STRING"))
    (when (null number-rule)
      (warn "Cannot find rule named :NUMBER"))
    (when (null character-rule)
      (warn "Cannot find rule named :CHARACTER"))
    (when (null toplevel-rule)
      (warn "Cannot find rule named :TOPLEVEL"))
    (setf (parser-symbol-rule    parser) symbol-rule)
    (setf (parser-string-rule    parser) string-rule)
    (setf (parser-number-rule    parser) number-rule)
    (setf (parser-character-rule parser) character-rule)
    (setf (parser-toplevel-rule  parser) toplevel-rule)
    ))

;;; ====================

(defun install-pprinters (parser)
  (when-debugging
   (comment "=================================")
   (comment "Installing pprinters")
   (comment "- - - - - - - - - - - - - - - - -"))
  (let ((ht-expr-to-parser-rules (parser-ht-expr-to-parser-rules parser))
	(ht-car-to-parser-rules  (parser-ht-car-to-parser-rules parser)))
    (dolist (rule (parser-rules parser))
      (install-pprinter-rule rule 
			     ht-expr-to-parser-rules
			     ht-car-to-parser-rules))))
      

(defun install-pprinter-rule (rule ht-expr-to-parser-rules ht-car-to-parser-rules)
  (let ((semantics (parser-rule-semantics rule)))
    (cond ((consp semantics)
	   (push rule (gethash (car semantics) ht-car-to-parser-rules)))
	  ((null semantics)
	   nil)
	  (t
	   (push rule (gethash semantics ht-expr-to-parser-rules))))))


;;; ============================================================================

    
(defun propagate-optionals (&optional (parser *current-parser*))
  (debugging-comment "========================================")
  (debugging-comment "First round: look for optional rules.")
  (loop 
    ;; iterate to fixpoint   
    (unless (propagate-optional-one-round parser)
      (return nil))
    (debugging-comment "========================================")
    (debugging-comment "New round: look for more optional rules."))
  (debugging-comment "========================================"))

(defun propagate-optional-one-round (parser)
  (let ((ht-name-to-rule (parser-ht-name-to-rule parser))
	(changed? nil)) 
    ;;
    ;; make rules optional if all their items are optional
    ;;
    (maphash #'(lambda (rule-name rule)
		 (declare (ignore rule-name))
		 (let* ((items (parser-rule-items rule))
			(n (length items))
			(all-optional? 
			 (and (> n 0)
			      (dotimes (i n t)
				(let ((item (svref items i)))
				  (unless (null item)
				    (when (not (parser-rule-item-optional? item))
				      (return nil))))))))
		   (when all-optional?
		     (unless (parser-rule-optional? rule)
		       (setq changed? t)
		       (setf (parser-rule-optional? rule) t)
		       (let ((semantic-pattern (parser-rule-semantics rule)))
			 (when (not (null semantic-pattern))
			   (let ((semantic-alist nil)
				 (items (parser-rule-items rule)))
			     (dotimes (i n)
			       (let ((item (svref items i)))
				 (unless (null item)
				   (let ((index (parser-rule-item-semantic-index item)))
				     (push (cons index (parser-rule-item-default-semantics item))
					   semantic-alist)))))
			     (setf (parser-rule-default-semantics rule)
			       (eval (sanitize-sexpression (sublis-result semantic-alist semantic-pattern)))))))
		       ;; (when (parser-repeat-rule-p rule) (setf (parser-rule-default-semantics rule) '()))
		       (debugging-comment "Rule ~S is now optional with semantics ~S." 
					  rule
					  (parser-rule-default-semantics rule))
		       ))))
	     ht-name-to-rule)
    ;;
    ;; make items optional if they invoke an optional rule 
    ;;
    (maphash #'(lambda (rule-name rule)
		 (declare (ignore rule-name))
		 (let* ((items (parser-rule-items rule))
			(n (length items)))
		   (dotimes (i n t)
		     (let ((item (svref items i)))
		       (unless (null item)
			 (let* ((item-rule-name (parser-rule-item-rule item))
				(item-rule (gethash item-rule-name ht-name-to-rule)))
			   (when (parser-rule-optional? item-rule)
			     (unless (parser-rule-item-optional? item)
			       (setq changed? t)
			       (setf (parser-rule-item-optional? item) t)
			       (setf (parser-rule-item-default-semantics item) (parser-rule-default-semantics item-rule))
			       (debugging-comment "In rule ~30S, item ~D (~S) is now optional with semantics ~S."
						  rule i item-rule-name
						  (parser-rule-item-default-semantics item))))))))))
	     ht-name-to-rule)
    ;; changed? will be NIL once we reach a fixpoint (probably about 2 rounds)
    changed?))

(defun sanitize-sexpression (s)
  (cond ((atom s) s)
	((and (eq (car s) 'list)
	      (atom (cdr s))
	      (not (null (cdr s))))
	 :ILLEGAL-SEXPRESSION)
	(t (mapcar #'sanitize-sexpression s))))
    

