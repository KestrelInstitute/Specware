;;; -*- Mode: LISP; Package: Specware; Base: 10; Syntax: Common-Lisp -*-

(in-package "PARSER4")

(defun reset-parser-debug-vars ()
  (setq *parser-node-number* 0)
  (setq *all-nodes* nil)
  )

(defun find-node (n)
  (find-if #'(lambda (x) (= (parser-node-number x) n))
	   *all-nodes*))

(defun show-node (node &optional (msg ""))
  (unless (parse-session-p *current-parser-session*)
    (break "SHOW-NODE called with *CURRENT-PARSER-SESSION*  not a session")
    (return-from show-node nil))
  (let ((locations (parse-session-locations *current-parser-session*))
	(rule (parser-node-rule node)))
    (when (null locations)
      (break "No locations in *current-parser-session*")
      (return-from show-node nil))
    (cond ((parser-token-rule-p rule)
	   (let* ((semantics (parser-node-semantics node))
		  (token-type  (first semantics))
		  (token-value (second semantics))
		  (pre-index  (parser-node-pre-index node))
		  (post-index (parser-node-post-index node)))
	     (comment "~14A ~6D ~3D [~6D:~20S ~30A] from ~10A ~10S"
		      msg
		      (parser-node-number node)
		      (parser-node-bvi    node)
		      pre-index
		      (parser-location-position (svref locations pre-index))
		      (if (null post-index) 
			  ""
			(let ((post-loc (svref locations post-index)))
			  (if (null post-loc)
			      (format nil " ~6D:~20A " post-index "<not installed yet>")
			    (let ((post-position (parser-location-position post-loc)))
			      (format nil " ~6D:~20A " 
				      post-index
				      (if (null post-position) "   eof"
					(format nil "~S" post-position)))))))
		      token-type
		      token-value)))
	  (t
	   (let* ((pre-index  (parser-node-pre-index node))
		  (pre-position (parser-location-position (svref locations pre-index))) 
		  (post-index (parser-node-post-index node))
		  (last-child-post-index nil)
		  (children (parser-node-children node)))
	     (dotimes (i (length children))
	       (let ((child (svref children i)))
		 (unless (null child)
		   (let ((child-post-index (parser-node-post-index child)))
		     (unless (null child-post-index)
		       (setq last-child-post-index child-post-index))))))
	     (comment "~14A ~6D ~3D [~6D:~20S ~30A] using ~20A ~12A from ~A"
		      msg
		      (parser-node-number node)
		      (parser-node-bvi    node)
		      pre-index
		      pre-position
		      (cond ((not (null post-index))
			     (let ((post-loc (svref locations post-index)))
			       (if (null post-loc)
				   (format nil " ~6D:~20A " post-index "<not installed yet>")
				 (let ((post-position (parser-location-position post-loc)))
				   (format nil " ~6D:~20A " 
					   post-index
					   (if (null post-position) "   eof"
					     (format nil "~S" post-position)))))))

			    ((not (null last-child-post-index))
			     (let ((post-loc (svref locations last-child-post-index)))
			       (if (null post-loc)
				   (format nil " ~6D:~20A " post-index "<not installed yet>")
				 (let ((post-position (parser-location-position post-loc)))
				   (format nil "(~6D:~20A)" 
					   last-child-post-index
					   (if (null post-position) "   eof"
					     (format nil "~S" post-position)))))))
			    (t
			     ""))
		      (type-of rule)
		      (parser-rule-name rule)
		      (format-children node)))))))

(defun verify-children (children msg)
  (let ((prior-loc nil))
    (dotimes (i (length children))
      (let ((child (svref children i)))
	(cond ((null child)
	       (setq prior-loc nil))
	      ((null prior-loc)
	       (setq prior-loc (parser-node-post-index child)))
	      ((eq prior-loc (parser-node-pre-index child))
	       (setq prior-loc (parser-node-post-index child)))
	      (t
	       (break "~A bad seq of children at ~D" msg i)))))))

(defun verify-all-partial-node-data (session msg)
  (let ((locations (parse-session-locations session))) 
    (dotimes (i (length locations))
      (verify-partial-node-data session (svref locations i) msg))))

(defun verify-partial-node-data (session loc msg)
  (let ((this-index (parser-location-index loc))
	(partial-node-data (parser-location-partial-node-data loc))
	(toplevel-rule (parser-toplevel-rule (parse-session-parser session))))
    (dolist (partial-node-datum partial-node-data)
      (let ((parent-node (car partial-node-datum)))
	(unless (equal (parser-node-rule parent-node) toplevel-rule)
	  (let* ((child-index (cdr partial-node-datum))
		 (prior-index child-index)
		 (prior-child nil)
		 (children-of-parent (parser-node-children parent-node)))
	    (loop while (and (null prior-child) (>= (decf prior-index) 0)) do
	      (setq prior-child (svref children-of-parent prior-index)))
	    (unless (null prior-child)
	      (let ((prior-child-post-index (parser-node-post-index prior-child)))
		(unless (= prior-child-post-index this-index)
		  (comment "========================================")
		  (comment "Prior-child-post-index ~D   this-index ~D"
			   prior-child-post-index this-index)
		  (show-node parent-node "Parent")
		  (dotimes (i (length children-of-parent))
		    (let ((child (svref children-of-parent i)))
		      (unless (null child)
			(show-node child "child"))))
		  (warn "~A: Bad partial-node-data at location ~S : node ~S, index ~S" 
			msg
			this-index 
			(parser-node-number parent-node)
			child-index))))))))))

(defun rules-for-bv (parser bv)
  (let ((rules nil))
    (dolist (rule (parser-rules parser))
      ;; (when (parental-parser-rule? rule)
      (unless (null (parser-rule-bvi rule))
	(when (equal (sbit bv (parser-rule-bvi rule)) 1)
	  (push (parser-rule-name rule) rules))))
    rules))

(defvar *last-time* 0)

(defun delta-time ()
  (let ((now (lisp::get-internal-run-time)))
    (prog1
	(- now *last-time*)
      (setq *last-time* now))))

;;; --------------------------------------------------------------------------------

(defun verify-all-parser-rule-references (parser)
  (maphash #'(lambda (name rule) 
	       (aux-verify-all-parser-rule-references parser name rule))
	   (parser-ht-name-to-rule parser)))


(defun aux-verify-all-parser-rule-references (parser name rule)
  (etypecase rule ; use etypcase, not (ecase (type-of rule) ..) since parser-rule is generic...
    (parser-id-rule    
     (verify-parser-rule-reference parser
				   (parser-id-rule-subrule rule) 			  
				   name))
    (parser-anyof-rule   
     (let ((items (parser-rule-items rule)))
       (dotimes (i (length items))
	 (let ((item (svref items i)))
	   (verify-parser-rule-item-reference parser item name)))))
    (parser-tuple-rule
     (let ((items (parser-rule-items rule)))
       (dotimes (i (length items))
	 (let ((item (svref items i)))
	   (verify-parser-rule-item-reference parser item name)))))
    (parser-pieces-rule  
     (let ((items (parser-rule-items rule)))
       (dotimes (i (length items))
	 (let ((item (svref items i)))
	   (verify-parser-rule-item-reference parser item name)))))
    (parser-repeat-rule 
     (let ((items (parser-rule-items rule)))
       (dotimes (i (length items))
	 (let ((item (svref items i)))
	   (unless (null item)
	     (verify-parser-rule-item-reference parser item name))))))
    (parser-keyword-rule nil)
    (parser-rule         nil)))

(defun verify-parser-rule-item-reference (parser item parent-rule-name)
  (verify-parser-rule-reference parser 
				(parser-rule-item-rule item)
				parent-rule-name))

(defun verify-parser-rule-reference (parser child-rule-name parent-rule-name)
  (unless (maybe-find-parser-rule parser child-rule-name)
    (warn "In rule for ~S, cannot find rule named ~S" 
	  parent-rule-name child-rule-name)))

;;; ----------------------------------------

(defun show-partial-data (locations n)
  (dotimes (i (1+ n))
    (let ((loc (svref locations i)))
      (dolist (datum (parser-location-partial-node-data loc))
	(comment "Datum for ~D ~D ~D" 
		 i
		 (parser-node-number (car datum)) 
		 (cdr datum)))
      (comment "====="))))

(defun format-children (node)
  (let ((children (parser-node-children node)))
    (if (null children)
	""
      (let ((components nil))
	(dotimes (i (length children))
	  (push (let ((child (svref children i)))
		  (if (null child)
		      "."
		    (let ((node-number (parser-node-number child))
			  (rule-name (parser-rule-name (parser-node-rule child))))
		      (if (eq rule-name :TOKEN)
			  (let ((semantics (parser-node-semantics child)))
			    (list node-number rule-name (first semantics) (second semantics)))
			(list node-number rule-name)))))
		components))
	(let ((lisp::*print-circle* nil))
	  (format nil "~{~A~^ ~}"
		  (reverse components)))))))

(defun show-node-2 (locations node)
  (show-node node)
  (show-node-source-tokens locations node))

(defun show-node-source-tokens (locations node)
  (let ((tokens nil))
    (do ((index (parser-node-pre-index  node) (1+ index)))
	((>= index (parser-node-post-index node)))
      (let ((token-node 
	     (find-if #'(lambda (node) (parser-token-rule-p (parser-node-rule node)))
		      (parser-location-post-nodes (svref locations index)))))
	(push (second (parser-node-semantics token-node)) tokens)))
    (comment "~{~A~^ ~}" (reverse tokens))))
		   
(defun verify-reductions (parser)
  (maphash #'(lambda (name rule)
	       (comment "----")
	       (comment "~20A ~30A ~3D" (type-of rule) name (parser-rule-bvi rule))
	       (if (superfluous-anyof-rule? rule)
		   (comment "  superfluous")
		 (dolist (reduction (parser-rule-reductions rule))
		   (let* ((parent-rule (reduction-parent-rule reduction))
			  (match?
			   (ecase (type-of parent-rule)
			     (parser-anyof-rule  (verify-reduction-to-anyof-rule  rule reduction))
			     (parser-tuple-rule  (verify-reduction-to-tuple-rule  rule reduction))
			     (parser-pieces-rule (verify-reduction-to-pieces-rule rule reduction))
			     (parser-repeat-rule (verify-reduction-to-repeat-rule rule reduction)))))
		     (when (not match?)
		       (comment "~60T => ~20A ~30A ~D"
				(type-of          parent-rule)
				(parser-rule-name parent-rule)
				(reduction-child-index reduction)))))))
      	   (parser-ht-name-to-rule parser)))

(defun verify-reduction-to-anyof-rule (rule reduction)
  (let* ((parent-rule (reduction-parent-rule reduction))
	 (child-index (reduction-child-index reduction))
	 (item (svref (parser-rule-items parent-rule) child-index)))
    (verify-item-matches? item rule)))

(defun verify-reduction-to-repeat-rule (rule reduction)
  (let* ((parent-rule (reduction-parent-rule reduction))
	 (child-index (reduction-child-index reduction))
	 (item (svref (parser-rule-items parent-rule) child-index)))
    (verify-item-matches? item rule)))

#||
  (let* ((parent-rule (reduction-parent-rule reduction))
	 (child-index (reduction-child-index reduction))
	 (looking-for-element? (or (evenp child-index)
				   (null (parser-repeat-rule-separator parent-rule)))) 
	 (desired-item         (if looking-for-element?
				   (parser-repeat-rule-element parent-rule)
				 (parser-repeat-rule-separator parent-rule))))
    (verify-item-matches? desired-item rule)))
||#

(defun verify-reduction-to-tuple-rule (rule reduction)
  (let* ((parent-rule (reduction-parent-rule reduction))
	 (child-index (reduction-child-index reduction))
	 (item (svref (parser-rule-items parent-rule) child-index)))
    (verify-item-matches? item rule)))

(defun verify-reduction-to-pieces-rule (rule reduction)
  (let* ((parent-rule (reduction-parent-rule reduction))
	 (child-index (reduction-child-index reduction))
	 (item (svref (parser-rule-items parent-rule) child-index)))
    (verify-item-matches? item rule)))
#||
  (let* ((parent-rule (reduction-parent-rule reduction))
	 (items (parser-rule-items parent-rule)))
    (dotimes (i (length items) nil)
      (let ((item (svref items i)))
	(when (verify-item-matches? item rule)
	  (return t))))))
||#
(defun verify-item-matches? (item rule)
  (let ((name  (parser-rule-name rule))
	(bvi   (parser-rule-bvi  rule))
	;;
	(item-rule-name (parser-rule-item-rule                 item))
	(children-bv    (parser-rule-item-possible-children-bv item)))
    (if (null bvi)
	(eq item-rule-name name)
      (eq (sbit children-bv bvi) 1))))
