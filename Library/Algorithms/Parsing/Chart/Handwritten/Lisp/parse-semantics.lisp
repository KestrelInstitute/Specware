;;; -*- Mode: LISP; Package: Parser4; Base: 10; Syntax: Common-Lisp -*-

(in-package "PARSER4")

(defun parser-get-values (session &optional (min-size 1))
  (let* ((locations (parse-session-locations session))
	 (max-index        (length locations))
	 (index            0)
	 (prior-post-index 0)
	 ;; (new-reported-gap? nil)
	 ;; (reported-gap?     nil)
	 )
    (loop while (< -1 index max-index) do
	  (multiple-value-setq (index prior-post-index) ;  new-reported-gap?
	    (aux-parser-get-values session
				   (svref locations index) 
				   min-size
				   prior-post-index))
	  ;; (when new-reported-gap? (setq reported-gap? t))
	  )
    (unless (>= prior-post-index (1- max-index))
      ;; (when 
      (report-gap session prior-post-index max-index)
      ;; (setq reported-gap? t)
      )
    (setf (parse-session-results session)
	  (nreverse (parse-session-results session)))
    ;; (when reported-gap? (comment "============================================================================"))
    session))
      
(defun aux-parser-get-values (session loc min-size prior-post-index)
  (let ((pre-index      (parser-location-index loc))
	(max-index       -1)
	(max-nodes      nil)
	(toplevel-count   0)
	(toplevel-rule  (parser-toplevel-rule (parse-session-parser session)))
	(locations      (parse-session-locations session))
	;; (reported-gap?  nil)
	)
    (dolist (node (parser-location-post-nodes loc))
      (let ((post-index (parser-node-post-index node)))
	(cond ((> post-index max-index)
	       (setq max-nodes (list node))
	       (setq max-index post-index))
	      ((= post-index max-index)
	       (push node max-nodes)))))
    (when (>= max-index (+ pre-index min-size))
      ;;
      (unless (= prior-post-index pre-index) 
	;; (when 
	(report-gap session prior-post-index pre-index)
	;; (setq reported-gap? t)
	)
      (setq prior-post-index max-index)
      ;;
      (let ((alternative-results nil))
	(dolist (node max-nodes)
	  (when (eq (parser-node-rule node) toplevel-rule)
	    (incf toplevel-count)
	  (push (list (parser-location-position (svref locations pre-index))
		      (parser-location-position (svref locations max-index))
		      (eval-node session node))
		alternative-results)))
	(unless (null (cdr alternative-results))
	  (when (parse-session-report-ambiguities? session)
	    (report-ambiguity session pre-index max-index alternative-results)))
	(setf (parse-session-results session)
	  (append alternative-results (parse-session-results session)))))
    (values max-index prior-post-index))) ;  reported-gap?

(defun report-gap (session start end)
  (let ((locations (parse-session-locations session))
	(tokens nil))
    (do ((index start (1+ index)))
	((= index end))
      (let ((loc (svref locations index)))
	(dolist (node (parser-location-post-nodes loc))
	  (when (eq (parser-node-rule node) +token-rule+)
	    (push (parser-node-semantics node) tokens)))))
    (setq tokens (nreverse tokens))
    (push tokens (parse-session-gaps session))
    (when (or (parse-session-report-gaps? session)
	      (null (parse-session-error-reported? session)))
      ;; (comment "============================================================================")
      (let* ((first-pos (third (first tokens)))
	     (first-byte (first  first-pos))
	     (first-line (second first-pos))
	     (first-char (third  first-pos))
	     ;; (last-line 0)
	     )
	(warn-pos "Pending or unparsed text at line ~4D, column ~2D   (byte ~D)" first-line first-char first-byte)
	;; (let ((line-count 0))
	;;   (dolist (token tokens)
	;;     (let ((this-line (second (third token))))
	;;       (unless (eq this-line last-line)
	;; 	(unless (= last-line 0)
	;; 	  (incf line-count)
	;; 	  (unless (> line-count 1)
	;; 	    (terpri)))
	;; 	(setq last-line this-line)))
	;;     (unless (> line-count 1)
	;;       (format t (if (eq (first token) :STRING) "~S " "~A ") (second token))))
	;;   (when (> line-count 1)
	;;     (comment " ... ~D more lines ..." (1- line-count))))
	))
    t))
      

(defun report-ambiguity (session start end alternative-results)
  (push alternative-results (parse-session-ambiguities session))
  ;; (comment "============================================================================")
  (warn-pos "There are ~D results for the text from ~D to ~D"
	    (length alternative-results) start end)
  ;; (comment "============================================================================")
  )

(defun eval-node (session node)
  (if (null node)
      nil
    (let* ((rule           (parser-node-rule      node))
	   (node-semantics (parser-node-semantics node))
	   (rule-semantics (parser-rule-semantics rule))
	   (children       (parser-node-children  node)))
      (if (null rule-semantics)
	  (eval-children-nodes session rule children node-semantics)
	(let* ((locations     (parse-session-locations session))
	       (parser        (parse-session-parser    session))
	       (default-alist (parser-default-semantic-alist parser))
	       ;;
	       (first-plc (parser-location-position
			   (svref locations (parser-node-pre-index node))))
	       (first-byte-position  (first  first-plc))
	       (first-line           (second first-plc))
	       (first-column         (third  first-plc))
	       (first-lc             (cons first-line first-column))
	       (first-lcb            (vector first-line first-column first-byte-position))
	       ;;
	       (rightmost-token-node (rightmost-descendent session node))
	       (token                (parser-node-semantics rightmost-token-node))
	       (last-plc             (fourth token))
	       (last-byte-position   (first  last-plc))
	       (last-line            (second last-plc))
	       (last-column          (third  last-plc))
	       (last-lc              (cons last-line last-column))
	       (last-lcb             (vector last-line last-column last-byte-position))
	       (full-alist           (list* 
				       ;;
				       (cons :left-pos     first-byte-position)
				       (cons :left-line    first-line)
				       (cons :left-column  first-column)
				       (cons :left-lc      first-lc)
				       (cons :left-lcb     first-lcb)
				       ;;
				       (cons :right-pos    last-byte-position)
				       (cons :right-line   last-line)
				       (cons :right-column last-column)
				       (cons :right-lc     last-lc)
				       (cons :right-lcb    last-lcb)
				       (append 
					(children-alist session rule children) 
					default-alist)))
		 (result             (sublis-result full-alist rule-semantics)))
	  (when-debugging
	   (let ((reconstructed-alist (compute-pprint-alist rule-semantics result)))
	     (unless (sub-alist? reconstructed-alist full-alist)
	       (warn "Jim may care: Alists differ: ~S ~S ~S" reconstructed-alist full-alist result))))
	  result)))))

;;; ===== TEMP HERE ====

#+DEBUG-PARSER
(defvar *position-keys* 
  ;; should match keys mentioned above in eval-node
  '(:LEFT-POS  :LEFT-LINE  :LEFT-COLUMN  :LEFT-LC  :LEFT-LCB     
    :RIGHT-POS :RIGHT-LINE :RIGHT-COLUMN :RIGHT-LC :RIGHT-LCB))

#+DEBUG-PARSER
(defun compute-pprint-alist (pattern value)
  (catch 'mismatch
    (let ((alist nil))
      (labels ((collect (pattern value)
		 (cond ((fixnum? pattern)
			;;(comment "New pair: ~S ~S" pattern value)
			(push (cons pattern value) alist))
		       ((eql pattern value)
			;;(comment "Quiet match: ~S ~S" pattern value)
			nil)
		       ((atom pattern)
			(cond ((member pattern *position-keys*)
			       ;;(comment "New pair: ~S ~S" pattern value)
			       (push (cons pattern value) alist))
			      (t
			       ;;(comment "Throw out on pattern ~S" pattern)
			       (throw 'mismatch :no-match))))
		       ((atom value)
			;;(comment "Throw out on value ~S" value)
			(throw 'mismatch  :no-match))
		       (t
			;;(comment "Recur on ~S ~S" pattern value)
			(collect (car pattern) (car value))
			(collect (cdr pattern) (cdr value))))))
	(collect pattern value)
	alist))))

#+DEBUG-PARSER
(defun sub-alist? (x y)
  (dolist (pair x t)
    (unless (eq (cdr (assoc (car pair) y)) (cdr pair))
      (return nil))))

(defun rightmost-descendent (session node)
  (let* ((post-index (parser-node-post-index node))
	 (last-loc (svref (parse-session-locations session) (1- post-index))))
    (dolist (node (parser-location-post-nodes last-loc))
      (when (eq (parser-node-rule node) +token-rule+)
	(return node)))))

(defun eval-children-nodes (session rule children node-semantics)
  ;(declare (simple-vector children))
  ;(format t "eval-children-nodes: 1 ~A~%" children)
  (ecase (structure-type-of rule) ; faster than etypecase, since matches are exact here
    (parser-atomic-rule ;(format t "eval-children-nodes: 2~%")
     (eval-node session (svref children 0)))
    (parser-keyword-rule
     (parser-keyword-rule-keyword rule)
     )
    (parser-token-rule
     (let ((token-type  (first  node-semantics))
	   (token-value (second node-semantics)))
       (cond ((member token-type '(:WORD-SYMBOL 
				   :NON-WORD-SYMBOL 
				   :AD-HOC-SYMBOL-ONLY 
				   :AD-HOC-KEYWORD-AND-SYMBOL-ONLY 
				   :AD-HOC-SYMBOL-AND-NUMBER-ONLY
				   :AD-HOC-KEYWORD-AND-SYMBOL-AND-NUMBER-ONLY))
	      ;; Use explicit second value of nil to override second
	      ;; value returned by intern (e.g. :INTERNAL) See calls
	      ;; to eval-node that expect alist for second value.
	      (values (intern (if (parser-case-sensitive? (parse-session-parser session)) 
				  token-value
				(string-upcase token-value))
			      (parse-session-package session))
		      nil))
	     ((member token-type '(:NUMBER 
				   :STRING
				   :CHARACTER
				   :AD-HOC-NUMBER-ONLY 
				   :AD-HOC-KEYWORD-AND-NUMBER-ONLY)) 
	      token-value)
	     (t
	      `(,token-type ,token-value)))))
    (parser-anyof-rule
     (eval-anyof-children session rule children))
    (parser-id-rule
     (eval-node session (svref children 0)))
    (parser-repeat-rule
     ;; Use default value of nil for second value returned (for alist -- see calls to eval-node)
     (let ((has-sep? (not (null (parser-repeat-rule-separator rule))))
	   (c-values nil))
       (dotimes (i (length children))
	 (unless (and has-sep? (oddp i))
	   (let ((child (svref children i)))
	     (if (null child)
		 (return nil)
	       (push (eval-node session child) c-values)))))
       (reverse c-values)))
    (parser-pieces-rule
     (warn "Need semantics for rule ~S" (parser-rule-name rule))
     :JUNK)
    (parser-tuple-rule
     (values nil (tuple-children-alist session rule children)))
    ))

(defun children-alist (session rule children)
  (ecase (structure-type-of rule) ; faster than etypecase, since matches are exact here
    (parser-tuple-rule  (tuple-children-alist  session rule children))
    (parser-anyof-rule  (anyof-children-alist  session rule children))
    (parser-pieces-rule (pieces-children-alist session rule children))
    ))

(defun tuple-children-alist (session rule children)
  (declare (simple-vector children))
  (let* ((items (parser-tuple-rule-items rule))
	 (alist nil))
    (dotimes (i (length children))
      (let* ((child (svref children i))
	     (item  (svref items i))
	     (index (parser-rule-item-semantic-index item)))
	(if (null child)
	    (if (null index) 
		nil 
	      (push (cons index (parser-rule-item-default-semantics item)) ; was :unspecified 
		    alist))
	  (multiple-value-bind (child-value child-alist)
	      (eval-node session child)
	    (cond ((null index)
		   (unless (or (null child-value) (stringp child-value))
		     (break "Tuple child ~A returned value ~S (with alist ~S) where alist expected"
			   child
			   child-value
			   child-alist))
		   (setq alist (append child-alist alist)))
		  (t
		   (unless (null child-alist)
		     (warn "Tuple child ~A returned alist ~S (with value ~S) where value expected"
			   child
			   child-alist
			   child-value))
		   (push (cons index child-value) alist)))))))
    (reverse alist)))

(defun pieces-children-alist (session rule children)
  (declare (simple-vector children))
  (let ((alist nil))
    (dotimes (i (length children))
      (let ((child (svref children i)))
	(unless (null child)
	  (let* (;; (child-rule-name (parser-rule-name (parser-node-rule child)))
		 (items (parser-rule-items rule))
		 (item  (dotimes (i (length items))
			  (let ((item (svref items i)))
			    (when (parser-rule-item-matches? item child)
			      (return item)))))
		 (index (if (null item) nil (parser-rule-item-semantic-index item))))
	    (if (null child)
		(if (null index) 
		    nil 
		  (push (cons index (parser-rule-item-default-semantics item)) ; was :unspecified
			alist))
	      (multiple-value-bind (child-value child-alist)
		  (eval-node session child)
		(cond ((null index)
		       (unless (or (null child-value) (stringp child-value))
			 (warn "Pieces child ~A returned value ~S (with alist ~S) where alist expected"
			       child
			       child-value
			       child-alist))
		       (setq alist (append child-alist alist)))
		      (t
		       (unless (null child-alist)
			 (warn "Pieces child ~A returned alist ~S (with value ~S) where value expected"
			       child
			       child-alist
			       child-value))
		       (push (cons index child-value) alist)))))))))
    (reverse alist)))

(defun anyof-children-alist (session rule children)
  (let* ((child (svref children 0))
	 ;;(child-rule-name (parser-rule-name (parser-node-rule child)))
	 (index nil)
	 (items (parser-rule-items rule)))
    (dotimes (i (length items))
      (let ((item (svref items i)))
	(when (parser-rule-item-matches? item child)
	  (return (setq index (parser-rule-item-semantic-index item))))))
    (multiple-value-bind (child-value child-alist)
	(eval-node session child)
      (cond ((null index)
	     (unless (or (null child-value) (stringp child-value))
	       (warn "Anyof child ~A returned value ~S (with alist ~S) where alist expected"
		     child
		     child-value
		     child-alist))
	     child-alist)
	    (t
	     (unless (null child-alist)
	       (warn "Anyof child ~A returned alist ~S (with value ~S) where value expected"
		     child
		     child-alist
		     child-value))
	     (list (cons index child-value)))))))


(defun eval-anyof-children (session rule children)
  (let* ((child (svref children 0))
	 ;;(child-rule-name (parser-rule-name (parser-node-rule child)))
	 (index nil)
	 (items (parser-rule-items rule)))
    (dotimes (i (length items))
      (let ((item (svref items i)))
	(when (symbolp item) (break "item ~S" item))
	(when (parser-rule-item-matches? item child)
	  (return (setq index (parser-rule-item-semantic-index item))))))
    (if (null index)
	(eval-node session child)
      (multiple-value-bind (child-value child-alist)
	  (eval-node session child)
	(unless (null child-alist)
	  (warn "?? child ~A returned alist ~S (with value ~S) where value expected"
		child
		child-alist
		child-value))
	(values nil (list (cons index child-value)))))))

;; Ad hoc functions, due to parser features
(defun :NUMBER             (x) x)
(defun :AD-HOC-SYMBOL-ONLY (x) x)


