;;; -*- Mode: LISP; Package: Parser; Base: 10; Syntax: Common-Lisp -*-

(in-package "PARSER4")

;; ======================================================================
(defmacro warn-pos (&rest args)
  `(warn-pos-fn session ,@args))

(defun warn-pos-fn (session &rest args)
  (emacs::goto-file-position (namestring (parse-session-file session))
			     (second args) (third args))
  (apply 'warn args))

(defun parser-attach-rules (session)
  ;;
  (when-debugging (delta-time))
  ;;
  (initialize-location-desired-bvs session)
  ;;
  ;;(add-toplevel-node session 0)
  ;;
  (let* ((locations  (parse-session-locations session))
	 (parser     (parse-session-parser    session))
	 ;;
	 (ht-string-to-keyword-rules  (parser-ht-string-to-keyword-rule   parser))
	 (generic-symbol-rule         (parser-symbol-rule                 parser))
	 (generic-string-rule         (parser-string-rule                 parser))
	 (generic-number-rule         (parser-number-rule                 parser))
	 (generic-character-rule      (parser-character-rule              parser))
	 (keywords-are-keywords-only? (parser-keywords-are-keywords-only? parser))
         #+DEBUG-PARSER
	 (number-of-tokens-to-process 0)
	 (preceding-location-had-no-pending-rules? nil))
    ;;
    (dotimes (i (length locations))
      ;;
      (when-debugging
       (when *verbose?*
	 (unless (> (decf number-of-tokens-to-process) 0)
	   (let ((str (read-line t nil))) ; t = stream, nil = eof-error-p 
	     (setq number-of-tokens-to-process (if (null str) 
						   1
						 (or (parse-integer str :junk-allowed t) 
						     1)))))
	 (terpri)
	 (format t "====================================================================================================")
	 (terpri)))
      ;;
      (let ((location (svref locations i)))
	;;
	'(let ((token
	       (dolist (forward-node (parser-location-post-nodes location))
		 (when (eq (parser-node-rule forward-node) +token-rule+)
		   (return (parser-node-semantics forward-node))))))
	  (format t "~&[~3D : ~30D~% ~S]~%"
		  i
		  token
		  (parser-location-partial-node-data location)))
	(cond ((or (eq i 0) (not (null (parser-location-partial-node-data location))))
	       (setq preceding-location-had-no-pending-rules? nil))
	      (preceding-location-had-no-pending-rules?
	       ;; Suppress complaint if immediately preceding location also had the same problem.
	       ;; This avoids showing millions (well, perhaps thousands) of annoying messages.
	       nil)
	      (t
	       (setf (parse-session-error-reported? session) t)
	       (if (null (parser-location-position location))
		   (warn "Syntax error at EOF")
		 (let* ((prior-location (svref locations (- i 1)))
			(prior-position (parser-location-position prior-location)))
		   (let* ((prior-byte-pos (first  prior-position))
			  (prior-line     (second prior-position))
			  (prior-column   (third  prior-position))
			  (prior-token-node 
			   (find-if #'(lambda (node) (parser-token-rule-p (parser-node-rule node)))
				    (parser-location-post-nodes prior-location))))
		     (cond ((null prior-token-node)
			    (warn-pos "At line ~3D:~2D  Peculiar syntax error (no tokens seen)."
				      prior-line prior-column prior-byte-pos))
			   ((eq (first (parser-node-semantics prior-token-node))
				:EXTENDED-COMMENT-ERROR)
			    (let ((comment-text 
				   ;; trim text of comment down to include at most 2 newlines
				   (do ((text (second (parser-node-semantics prior-token-node))
					      (subseq text 0 (1- (length text)))))
				       ((< (count-if #'(lambda (char) (eq char #\newline)) 
						     text) 
					   3)
					text))))
			      ;; trim text of comment down to include at most 20 characters
			      (when (> (length comment-text) 20)
				(setq comment-text (format nil "~A ..." (subseq comment-text 0 16))))
			      (warn-pos "At line ~3D:~2D  EOF while scanning for close of extended comment starting with \"~A\""
					prior-line prior-column ;; prior-byte-pos
					comment-text 
					)))
			   (t
			    (warn-pos "At line ~3D:~2D  Syntactic error with \"~A\""
				      prior-line prior-column ; prior-byte-pos
				      (second (parser-node-semantics prior-token-node))
				      ))))))
	       (setq preceding-location-had-no-pending-rules? t)
	       ))
	(when-debugging
	 (when *verbose?*
	   (report-pending-rules parser i location)))
	;;
	(dolist (forward-node (parser-location-post-nodes location))
	  (when (eq (parser-node-rule forward-node) +token-rule+)
	    (let* ((token (parser-node-semantics forward-node))
		   ;; (column (third (third token)))
		   )
	      ;;
	      ;; (when (and (zerop (mod i 1000)) (> i 0)) (comment "[~8D] At token ~6D ~4D ~4D ~4D ~S" (delta-time) i pos line column xxx ))
	      ;;
	      (when (null (parser-location-partial-node-data location))
		;; Maybe we finished one toplevel form and are about to parse another.
		;; But if there were errors, we're probably still inside a buggy form,
		;;  so don't try to parse toplevel forms until we get back to column 1.
		(let ((column (third (third token))))
		  (unless (and (parse-session-error-reported? session) (> column 1))
		    (add-toplevel-node session i))))
	      (let* ((tok2 (second token)) 
		     (specific-keyword-rule (if (stringp tok2)
						(gethash (second token) ht-string-to-keyword-rules)
					      nil)))
		(case (first token) 
		  ((:WORD-SYMBOL :NON-WORD-SYMBOL)             
		   (cond ((null specific-keyword-rule)
			  (add-partial-node session generic-symbol-rule   forward-node 0))
			 (keywords-are-keywords-only?
			  (add-partial-node session specific-keyword-rule forward-node 0))
			 (t
			  (add-partial-node session specific-keyword-rule forward-node 0)
			  (add-partial-node session generic-symbol-rule   forward-node 0))))
		  (:CHARACTER
		   ;; never add keyword rule
		   (add-partial-node session generic-character-rule forward-node 0))
		  (:STRING
		   ;; never add keyword rule
		   (add-partial-node session generic-string-rule forward-node 0))
		  (:NUMBER	
		   (cond ((null specific-keyword-rule)
			  (add-partial-node session generic-number-rule forward-node 0))
			 (keywords-are-keywords-only?
			  (add-partial-node session specific-keyword-rule forward-node 0))
			 (t
			  (add-partial-node session generic-number-rule   forward-node 0)
			  (add-partial-node session specific-keyword-rule forward-node 0))))
		  (:AD-HOC-KEYWORD-ONLY 
		   (if (null specific-keyword-rule)
		       (warn "Token claimed to be a keyword is not in the grammar: ~S" token)
		     (add-partial-node session specific-keyword-rule forward-node 0)))
		  (:AD-HOC-SYMBOL-ONLY 
		   ;; never add keyword rule
		   (unless (null specific-keyword-rule)
		     (warn "Token claimed to be only a symbol has appeared as a keyword in the grammar: ~S" 
			   token))
		   (add-partial-node session generic-symbol-rule   forward-node 0))
		  (:AD-HOC-NUMBER-ONLY  
		   ;; never add keyword rule
		   (unless (null specific-keyword-rule)
		     (warn "Token claimed to be only a number has appeared as a keyword in the grammar: ~S" 
			   token))
		   (add-partial-node session generic-number-rule forward-node 0))
		  (:AD-HOC-KEYWORD-AND-SYMBOL-ONLY
		   (if (null specific-keyword-rule)
		       (warn "Token claimed to be a keyword (and a symbol) is not in the grammar: ~S" token)
		     (add-partial-node session specific-keyword-rule forward-node 0))
		   (add-partial-node session generic-symbol-rule forward-node 0))
		  (:AD-HOC-KEYWORD-AND-NUMBER-ONLY
		   (if (null specific-keyword-rule)
		       (warn "Token claimed to be a keyword (and a number) is not in the grammar: ~S" 
			     token)
		     (add-partial-node session specific-keyword-rule forward-node 0))
		   (add-partial-node session generic-number-rule forward-node 0))
		  (:AD-HOC-SYMBOL-AND-NUMBER-ONLY
		   ;; never add keyword rule
		   (unless (null specific-keyword-rule)
		     (warn "Token claimed to be only a symbol or a number has appeared as a keyword in the grammar: ~S" 
			   token))
		   (add-partial-node session generic-symbol-rule forward-node 0)
		   (add-partial-node session generic-number-rule forward-node 0))
		  (:AD-HOC-KEYWORD-AND-SYMBOL-AND-NUMBER-ONLY
		   (if (null specific-keyword-rule)
		       (warn "Token claimed to be a keyword (and a symbol and a number) is not in the grammar: ~S" 
			     token)
		     (add-partial-node session specific-keyword-rule forward-node 0))
		   (add-partial-node session generic-symbol-rule forward-node 0)
		   (add-partial-node session generic-number-rule forward-node 0))
		  )))))))))

(defun initialize-location-desired-bvs (session)
  (let* ((locations (parse-session-locations session))
	 (parser    (parse-session-parser    session))
	 (bv-size   (parser-bv-size parser)))
    (dotimes (i (length locations))
      (setf (parser-location-desired-bv (svref locations i))
	    (make-array bv-size
			:element-type    'bit 
			:initial-element 0)))))

;; ======================================================================

(defun add-toplevel-node (session index)
  (let* ((locations     (parse-session-locations session))
	 (location      (svref locations index))
	 (parser        (parse-session-parser session))
	 (toplevel-rule (parser-toplevel-rule parser))
	 (new-toplevel-node
	  (create-parser-node  :rule      toplevel-rule
			       :pre-index index
			       :children  (make-array 1 :initial-element nil)))
	 (handles-bv (parser-anyof-rule-possible-handles-bv toplevel-rule)))
    (when-debugging
     (when *verbose?*
       (let ((position (parser-location-position location)))
	 (comment "Adding top-level node for index ~D at line ~D, column ~D, byte ~D"
		  index
		  (second position)
		  (third  position)
		  (first  position)))))
    (augment-location-partial-node-data location new-toplevel-node 0) 
    (augment-location-desired-bv        location handles-bv)
    (when-debugging
     (when *verbose?*
       (report-pending-rules parser index location)))
    ))

(defun report-pending-rules (parser index location)
  #-DEBUG-PARSER
  (declare (ignore parser index location))
  #+DEBUG-PARSER
  (progn
    (comment "Pending at ~4D: ~6D" index (length (parser-location-partial-node-data location)))
    (dolist (datum (parser-location-partial-node-data location))
      (let ((node  (car datum))
	    ;; iii refers to position of child node within parent node
	    (iii   (cdr datum)))
	(comment "Pending at location ~6D: ~6D ~20A ~D"
		 index
		 (parser-node-number node)
		 (parser-rule-name (parser-node-rule node))
		 iii)))
    (format t "======")
    (dolist (rule (rules-for-bv parser (parser-location-desired-bv location)))
      (comment "Desired rule: ~A" rule))
    (format t "======")))

;; ======================================================================

(defun add-partial-node (session parent-rule child-node child-index)
  (ecase (structure-type-of parent-rule) ; faster than etypecase since we are looking for exact type matches
    (parser-anyof-rule   (add-unit-reduction      session parent-rule child-node))
    ;;
    (parser-tuple-rule   (add-partial-tuple-node  session parent-rule child-node child-index))
    (parser-pieces-rule  (add-partial-pieces-node session parent-rule child-node))
    (parser-repeat-rule  (add-partial-repeat-node session parent-rule child-node))
    ;;
    (parser-keyword-rule (add-unit-reduction      session parent-rule child-node))
    (parser-atomic-rule  (add-unit-reduction      session parent-rule child-node))
    (parser-id-rule      (add-unit-reduction      session parent-rule child-node)) ; this case shouldn't happen
    ))

(defun add-unit-reduction (session rule child-node)
  ;; "bvi" stands for "bit-vector-index"
  (when (null rule) (break "Missing rule in unit-reduction"))
  (let* ((pre-index  (parser-node-pre-index  child-node))
	 (post-index-ptr (parser-node-post-index-ptr child-node))
	 (inherited-precedence 
	  (parser-rule-precedence (parser-node-rule child-node)))
	 (explicit-bvi (parser-rule-bvi rule))
	 (p2bvi-alist (parser-rule-p2bvi-map rule))
	 (implicit-bvi (cdr (assoc inherited-precedence p2bvi-alist)))
	 (new-node (create-parser-node :rule           rule
				       :bvi            (or explicit-bvi implicit-bvi)
				       :semantics      nil
				       :pre-index      pre-index
				       :post-index-ptr post-index-ptr
				       :parents        nil
				       :children       (vector child-node)
				       :precedence     inherited-precedence))
	 (locations (parse-session-locations session)))
    (push new-node (parser-node-parents child-node))
    (push new-node (parser-location-post-nodes (svref locations pre-index)))
    (when-debugging 
     (when *verbose?*
       (show-node new-node "Completed")))
    (parser-propagate-from-node session new-node)
    new-node))

(defun augment-location-partial-node-data (location parent-node child-index)
  ;; child-index refers to the position of the child rule within the parent rule
  (push (cons parent-node child-index)
	(parser-location-partial-node-data location)))

(defun augment-location-desired-bv (location additional-desired-bv)
  ;; (when-debugging
  ;;   (when *verbose?* 
  ;;      (comment "At loc ~6D, turn on bits ~S" (parser-location-index location) additional-desired-bv)
  ;;     ))
  (unless (null additional-desired-bv) 
    (bit-ior (parser-location-desired-bv location)
	     additional-desired-bv
	     (parser-location-desired-bv location))))

(defun add-partial-tuple-node (session rule child-node child-index)
  ;; child-index will normally be 0, but could be larger if we are skipping past leading optionals
  (unless (eq rule (parser-toplevel-rule (parse-session-parser session)))
    (let* ((child-pre-index  (parser-node-pre-index child-node))
	   (pattern (parser-rule-items rule))
	   (pattern-size (length pattern))
	   (next-child-index (1+ child-index))
	   (children (make-array pattern-size :initial-element nil)))
      (declare (simple-vector children))
      (let ((new-node
	     (create-parser-node  :rule       rule
				  :bvi        (parser-rule-bvi rule) 
				  :pre-index  child-pre-index
				  :children   children
				  )))
	(adopt-child new-node children child-index child-node)
	(let ((all-other-required-children-present?
	       (dotimes (i (length children) t)
		 (when (and 
			;; ignoring this child (which will be filled in),
			(not (equal i child-index))
			;; if no child  and not optional, return nil
			(null (svref children i))    
			(not (parser-rule-item-optional? (svref pattern i))))
		   (return nil))))
	      (this-is-not-last-child? 
	       (< next-child-index (length children)))
	      (locations (parse-session-locations session)))
	  (when-debugging
	   (when *verbose?*
	     (when (not all-other-required-children-present?)
	       (show-node new-node "Created  "))))
	  (when all-other-required-children-present?
	    (install-completed-node session new-node child-node))
	  (when this-is-not-last-child?
	    (let ((post-loc 
		   (svref locations (parser-node-post-index child-node))))
	      (let ((repeat? t))
		(loop while (and repeat? (< next-child-index pattern-size))
		    do
		      ;; This will normally get the bv for the SECOND item, since we normally
		      ;; have just matched on the first item and now looking for more items.
		      ;; But if the first item(s) is/are optional, and we got to this rule by matching
		      ;; on the second or a later item, then the bv might be for the third or later item.
		      ;; And if that item is optional, we may also get the bv for subsequent items.
		      ;; So we could get just the second, or second thru fourth, or just third, or
		      ;; third thru sixth, etc.  We could probably cache this for each way of getting
		      ;; here, but it's probably not worth the effort to avoid the occasional extra bit-ior
		      ;; when this item is optional.
		      (let* ((next-child-item (svref pattern next-child-index))
			     (optional?  (parser-rule-item-optional?            next-child-item))
			     (handles-bv (parser-rule-item-possible-handles-bv  next-child-item)))
			(augment-location-partial-node-data post-loc new-node next-child-index)
			(augment-location-desired-bv        post-loc handles-bv)
			(setq repeat? optional?)
			(incf next-child-index)
			)))
	      ))
	  new-node)))))


(defun add-partial-pieces-node (session rule child-node)
  (let* ((child-pre-index  (parser-node-pre-index  child-node))
	 (child-post-index (parser-node-post-index child-node))
	 (child-post-location  (svref (parse-session-locations session)
				      child-post-index))
	 (children (make-array (length (parser-rule-items rule)) :initial-element nil))
	 (new-node 
	  (create-parser-node  :rule      rule
			       :bvi       (parser-rule-bvi rule) 
			       :pre-index child-pre-index
			       :children  children
			       ))
	  ;; The desired-bv for a pieces rule is just the union of the desired-bvs for 
	  ;; each child, any of which can appear in any order, so the desired bv for
	  ;; the next child is always the same.
	 (handles-bv (parser-pieces-rule-possible-handles-bv rule)))
    (adopt-child new-node children 0 child-node)
    (augment-location-partial-node-data child-post-location new-node 1)
    (augment-location-desired-bv        child-post-location handles-bv)
    (install-completed-node session new-node child-node)
    new-node))


(defun add-partial-repeat-node (session rule child-node)
  (let* ((child-pre-index     (parser-node-pre-index  child-node))
	 (child-post-index    (parser-node-post-index child-node))
	 (child-post-location (svref (parse-session-locations session)
				     child-post-index))
	 (children  (make-array 6 :initial-element nil))
	 (new-node  (create-parser-node  :rule      rule
					 :bvi       (parser-rule-bvi rule) 
					 :pre-index child-pre-index
					 :children  children
					 ))
	 (desired-rule-item
	  (or (parser-repeat-rule-separator rule)
	      (parser-repeat-rule-element   rule)))
	 (handles-bv (parser-rule-item-possible-handles-bv desired-rule-item))
	 )
    (adopt-child new-node children 0 child-node)
    (augment-location-partial-node-data child-post-location new-node 1)
    (augment-location-desired-bv        child-post-location handles-bv)
    (install-completed-node session new-node child-node)
    new-node))
  
;; ======================================================================

(defun install-completed-node (session node last-child-node)
  (let* ((pre-index      (parser-node-pre-index      node))
	 (post-index-ptr (parser-node-post-index-ptr last-child-node))
	 (rule (parser-node-rule node))
	 (explicit-precedence (parser-rule-precedence rule)))
    (if (null explicit-precedence)
	(when (parser-anyof-rule-p rule)
	  (setf (parser-node-precedence node) 
	    (parser-node-precedence last-child-node)))
      (setf (parser-node-precedence node) explicit-precedence))
    (setf (parser-node-post-index-ptr node) post-index-ptr)
    (when-debugging
     (when *verbose?*
       (show-node node "Completed")))
    (push node (parser-location-post-nodes 
		(svref (parse-session-locations session) 
		       pre-index)))
    (parser-propagate-from-node session node)
    node))

(defun parser-propagate-from-node (session this-node)
  (unless (or (null (parser-node-pre-index  this-node))
	      (null (parser-node-post-index this-node)))
    (attach-reductions session this-node)
    (extend-partial-nodes-reaching-this-node session this-node))
  (when (eq (parser-node-rule this-node)
	    (parser-toplevel-rule (parse-session-parser session)))
    (add-toplevel-node session (parser-node-post-index this-node)))
  nil)

(defun attach-reductions (session this-node)
  (let* ((locations  (parse-session-locations session))
	 (pre-index  (parser-node-pre-index this-node))
	 (pre-loc    (svref locations pre-index))
	 (desired-bv (parser-location-desired-bv pre-loc))
	 (this-rule  (parser-node-rule this-node))
	 (reductions (parser-rule-reductions this-rule)))
    (dolist (reduction reductions)
      (let* ((parent-rule (reduction-parent-rule reduction))
	     (parent-bv-index 
	      (or (parser-rule-bvi parent-rule)
		  (cdr (assoc (parser-node-precedence this-node)
			      (parser-rule-p2bvi-map parent-rule))))))
	(if (eq (sbit desired-bv parent-bv-index) 1)
	    (let ((child-index (reduction-child-index reduction)))
	      (add-partial-node session parent-rule this-node child-index))
	  (debugging-comment "Reduction from ~D not plausible : ~S ~S (bit ~D) at ~D" 
			     (parser-node-number this-node)
			     (structure-type-of  parent-rule)
			     (parser-rule-name   parent-rule)
			     parent-bv-index
			     (reduction-child-index reduction)
			     ))))))

;; ======================================================================

(defun extend-partial-nodes-reaching-this-node (session this-node)
  (let* ((pre-index (parser-node-pre-index this-node))
	 (pre-loc   (svref (parse-session-locations session) pre-index))
	 (partial-node-data (parser-location-partial-node-data pre-loc)))
    (dolist (partial-node-datum partial-node-data)
      (let ((candidate-parent-node (car partial-node-datum))
	    (child-index           (cdr partial-node-datum)))
	(maybe-extend-partial-node session 
				   candidate-parent-node 
				   child-index 
				   this-node)))))

(defun maybe-extend-partial-node (session parent-node child-index this-node)
  (let ((parent-rule (parser-node-rule parent-node)))
    (ecase (structure-type-of parent-rule) ; faster than etypecase since we are doing exact matches
      (parser-tuple-rule 
       (maybe-extend-partial-tuple-node  session parent-node parent-rule child-index this-node))
      (parser-pieces-rule 
       (maybe-extend-partial-pieces-node session parent-node parent-rule child-index this-node))
      (parser-repeat-rule 
       (maybe-extend-partial-repeat-node session parent-node parent-rule child-index this-node))
      (parser-anyof-rule
       (when-debugging
	(unless (eq (parser-node-rule parent-node)
		    (parser-toplevel-rule (parse-session-parser session)))
	  (warn "Attempt to extend non-toplevel ANYOF node ~S at ~D using node ~S" 
		parent-node 
		child-index 
		(parser-node-number this-node)))))
      )))

(defun maybe-extend-partial-tuple-node (session node rule child-index candidate-child)
  (let* ((pattern       (parser-rule-items rule))
	 (pattern-size  (length pattern))
	 (desired-item  (svref pattern child-index)))
    (when (parser-rule-item-matches? desired-item candidate-child)
      (let ((children (parser-node-children node)))
	(declare (simple-vector children))
	(let* ((next-child-index (1+ child-index))
	       (all-other-required-children-present?
		(dotimes (i (length children) t)
		  (when (and 
			 ;; ignoring this child (which will be filled in),
			 (not (equal i child-index))  
			 ;; if no child  and not optional, return nil
			 (null (svref children i))    
			 (not (parser-rule-item-optional? (svref pattern i)))	
			 )
		    (return nil))))
	       (this-or-following-child-is-already-present?
		(do ((i child-index (1+ i)))
		    ((>= i (length children))
		     nil)
		  (unless (null (svref children i))
		    (return t))))
	       (this-is-not-last-child? (< next-child-index (length children)))
	       (this-child-is-optional? (parser-rule-item-optional? desired-item))
	       (locations (parse-session-locations session))
	       ;;(parser    (parse-session-parser    session))
	       (cannibalizing? nil))
	  ;; if this slot is already full, we may replicate the partial parent
	  (when (and (or this-or-following-child-is-already-present?
			 (and all-other-required-children-present? 
			      (or this-is-not-last-child?
				  this-child-is-optional?)))
		     (not
		       (setq cannibalizing?
			     (let ((desired-precedence (parser-rule-item-precedence desired-item)))
			       (and (not (null desired-precedence))
				    (let ((candidate-precedence (parser-node-precedence candidate-child)))
				      (and (not (null candidate-precedence))
					   (<= candidate-precedence desired-precedence))))))))
	    (setq node (replicate-parser-node node child-index))
	    (setq children (parser-node-children node)))
	  ;;
	  (adopt-child node children child-index candidate-child)
	  ;; number of children is fixed...
	  (when cannibalizing?
	    (debugging-comment "Cannibalized ~D.  Last node now ~D"
			       (parser-node-number node)
			       (parser-node-number candidate-child))
	    (revise-cannibalized-node node candidate-child))
	  ;; whether or not we're cannibalizing, see if we're done 
	  ;; (revision 7/31/03 for forges parsers)
	  (cond (all-other-required-children-present?
		 (install-completed-node session node candidate-child))
		(t
		 (when-debugging
		  (when *verbose?* 
		    (show-node node (format nil "Extended ~D" child-index))))))
	  (when this-is-not-last-child?
	    (let ((post-loc (svref locations (parser-node-post-index candidate-child)))
		  (repeat? t))
	      (loop while (and repeat? (< next-child-index pattern-size)) do
		(let* ((next-child-item (svref pattern next-child-index))
		       (optional?  (parser-rule-item-optional?           next-child-item))
		       (handles-bv (parser-rule-item-possible-handles-bv next-child-item)))
		  (augment-location-partial-node-data post-loc node next-child-index)
		  (augment-location-desired-bv        post-loc handles-bv)
		  (setq repeat? optional?)
		  (incf next-child-index)
		  ))))
	  )))))

(defun revise-cannibalized-node (node last-child)
  (when-debugging
   (when *verbose?*
     (show-node node "Revised  ")))
  (let ((post-index (parser-node-post-index last-child)))
    ;; put ptr cell from parent into child as well, then mutate to use data from child
    (setf (parser-node-post-index-ptr last-child) (parser-node-post-index-ptr node))
    (setf (parser-node-post-index last-child) post-index)))

(defun maybe-extend-partial-pieces-node (session node rule child-index candidate-child)
  (let ((alternatives (parser-rule-items rule))
	(locations    (parse-session-locations session)))
    (dotimes (i (length alternatives))
      (let ((desired-item (svref alternatives i)))
	(when (parser-rule-item-matches? desired-item candidate-child)
	  (let ((children (parser-node-children node)))
	    ;; if this slot is already full, replicate partial parent, otherwise just use it
	    (unless (null (svref children child-index))
	      (setq node (replicate-parser-node node child-index))
	      (setq children (parser-node-children node)))
	    ;;
	    (adopt-child node children child-index candidate-child)
	    (let ((post-loc (svref locations (parser-node-post-index candidate-child)))
		  (handles-bv (parser-pieces-rule-possible-handles-bv rule)))
	      (augment-location-partial-node-data post-loc node (1+ child-index))
	      ;; The desired-bv for a pieces rule is just the union of the desired-bvs for 
	      ;; each child, any of which can appear in any order, so the desired bv for
	      ;; the next child is always the same.
	      (augment-location-desired-bv post-loc handles-bv))
	    (install-completed-node session node candidate-child)))))))

(defun maybe-extend-partial-repeat-node (session node rule child-index candidate-child)
  (let* ((looking-for-element? (or (evenp child-index)
				   (null (parser-repeat-rule-separator rule)))) 
	 (desired-item         (if looking-for-element?
				   (parser-repeat-rule-element rule)
				 (parser-repeat-rule-separator rule))))
    (when (parser-rule-item-matches? desired-item candidate-child)
      (let* ((children (parser-node-children node))
	     (children-size (length children)))
	(declare (simple-vector children))
	;; if this slot is already full, replicate partial parent, otherwise just use it
	(when (or looking-for-element?
		  (and 
		   (< child-index children-size)
		   (not (null (svref children child-index)))))
	  (setq node (replicate-parser-node node child-index))
	  (setq children (parser-node-children node)))
	;; number of children is indefinite, so we may need to extend vector
	(when (>= child-index children-size)
	  (let ((new-children (make-array (* child-index 2) :initial-element nil)))
	    (dotimes (i children-size)
	      (setf (svref new-children i) (svref children i)))
      	    (setf (parser-node-children node) new-children)
	    (setf children new-children)))
	;;
	(adopt-child node children child-index candidate-child)
	(when looking-for-element?
	  (install-completed-node session node candidate-child))
	(let* ((post-loc (svref (parse-session-locations session)
				(parser-node-post-index candidate-child)))
	       (next-item
		;; next subrule is separator if this was element, and vice versa, 
		;; unless separator is null, in which case always use element
		(if (or (oddp child-index) (null (parser-repeat-rule-separator rule)))
		    (parser-repeat-rule-element rule)
		  (parser-repeat-rule-separator rule)))
	       (handles-bv (parser-rule-item-possible-handles-bv next-item)))
	  (augment-location-partial-node-data post-loc node (1+ child-index))
	  (augment-location-desired-bv        post-loc handles-bv)
	  )))))

(defun parser-rule-item-matches? (parent-item child-node)
  (and (let ((child-bvi (parser-node-bvi child-node)))
	 (and (if (null child-bvi)
		  (eq (parser-rule-item-rule parent-item) 
		      (parser-rule-name (parser-node-rule child-node)))
		(eq (sbit (parser-rule-item-possible-children-bv parent-item) child-bvi)
		    1))))
       (let ((max-precedence-allowed (parser-rule-item-precedence parent-item)))
	 (or (null max-precedence-allowed)
	     (let ((child-precedence (parser-node-precedence child-node)))
	       (or (null child-precedence)
		   (<= child-precedence max-precedence-allowed)))))))

;; ======================================================================

(defun replicate-parser-node (old-node child-index)
  (declare (fixnum child-index))
  (let ((new-node (copy-parser-node old-node)))
    ;;
    (when-debugging
     (setf (parser-node-number new-node) (incf *parser-node-number*)))
    ;;
    (let* ((old-children (parser-node-children old-node))
	   (new-children (make-array (length old-children) :initial-element nil)))
      (declare (simple-vector old-children) 
	       (simple-vector new-children))
      (dotimes (i child-index)
	(setf (svref new-children i) (svref old-children i)))
      (setf (parser-node-children new-node) new-children))
    ;;
    (when-debugging
     (when *verbose?* 
       (show-node new-node (format nil "~6D =>" (parser-node-number old-node))))
     (push new-node *all-nodes*))
    ;;
    new-node))
;; ======================================================================

(defun adopt-child (node children child-index child-node)
  (declare (simple-vector children) (fixnum child-index))
  (setf (svref children child-index) child-node)
  (push node (parser-node-parents child-node))
  (let ((n (length children)))
    (do ((i (1+ child-index) (1+ i)))
	((>= i n))
      (setf (svref children i) nil))))


