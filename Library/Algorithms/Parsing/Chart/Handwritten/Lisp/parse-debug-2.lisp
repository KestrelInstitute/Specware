;;; -*- Mode: LISP; Package: Specware; Base: 10; Syntax: Common-Lisp -*-

(in-package "PARSER4")

(defun show-reductions (parser)
  (let (#+allegro(excl::*print-nickname* t))
    (comment-blank-lines 3)
    (comment "============================================================")
    (comment "        AMBIGUOUS NON-KEYWORD ")
    (comment "============================================================")
    (dolist (rule (parser-rules parser))
      (unless (keyword-triggered-rule? parser (parser-rule-name rule))
	(let ((reductions (parser-rule-reductions rule)))
	  (when (not (null (rest reductions)))
	    (comment "~50S ==PPP==> ~S" 
		     (parser-rule-name rule) 
		     (parser-rule-name (reduction-parent-rule (pop reductions))))
	    (dolist (reduction reductions)
	      (comment "~50T ==PPP==> ~S" 
		       (parser-rule-name (reduction-parent-rule reduction))))))))

    (comment "============================================================")
    (comment "        Unique or keyword ")
    (comment "============================================================")
    (dolist (rule (parser-rules parser))
      (let ((reductions  (parser-rule-reductions rule)))
	(when (null reductions) 
	  (comment "~50S *" (parser-rule-name rule))) 
	(when (and (not (null reductions))
		   (or (keyword-triggered-rule? parser (parser-rule-name rule))
		       (null (rest reductions))))
	  (comment "~50S ==PPP==> ~S" 
		   (parser-rule-name rule) 
		   (parser-rule-name (reduction-parent-rule (pop reductions))))
	  (dolist (reduction reductions)
	    (comment "~50T ==PPP==> ~S" 
		     (parser-rule-name (reduction-parent-rule reduction)))))))

    (comment "==================================================")
    ))

(defun parser-show-all-max-nodes (&optional (session *current-parser-session*) (min-size 2))
  (declare (special *current-parser-session*))
  (let ((index           0)
	(last-post-index 0)
	(locations (parse-session-locations session)))
    (loop while (< -1 index (length locations)) do
      (multiple-value-setq (index last-post-index)
	(parser-show-max-nodes session
			       (svref locations index) 
			       min-size 
			       last-post-index)))))

(defun parser-show-max-nodes (session loc min-size last-post-index)
  (let ((locations (parse-session-locations session)) 
	(pre-index (parser-location-index loc))
	(max-index -1)
	(max-nodes nil)
	(toplevel-count 0))
    (dolist (node (parser-location-post-nodes loc))
      (let ((post-index (parser-node-post-index node)))
	(cond ((> post-index max-index)
	       (setq max-nodes (list node))
	       (setq max-index post-index))
	      ((= post-index max-index)
	       (push node max-nodes)))))
    (when (> max-index (+ pre-index min-size))
      ;;
      (unless (= last-post-index pre-index)
	(comment "============================================================================")
	(comment "---gap---"))
      (comment "============================================================================")
      (setq last-post-index max-index)
      ;;
      (dolist (node max-nodes)
	(when (eq (parser-rule-name (parser-node-rule node)) :TOPLEVEL)
	  (incf toplevel-count)
	  (push (list (parser-location-position (svref locations pre-index))
		      (parser-location-position (svref locations max-index))
		      (eval-node session node))
		(parse-session-results session))))
      (when (> toplevel-count 1)
	(comment "MULTIPLE PARSES: ~D" toplevel-count))
      ;;
      (let ((n 20))
	(dolist (node max-nodes)
	  (when (< (decf n) 0) 
	    (comment "... ~D more nodes ..." (- (length max-nodes) 20))
	    (return nil))
	  (show-node node)
	  (when (equal (parser-rule-name (parser-node-rule node)) :TOPLEVEL)
	    (terpri)))))
    (values max-index last-post-index)))

