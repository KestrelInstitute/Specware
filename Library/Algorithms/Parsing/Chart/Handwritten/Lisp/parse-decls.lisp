;;; -*- Mode: LISP; Package: Parser; Base: 10; Syntax: Common-Lisp -*-

(in-package "PARSER4")

;;; ========================================


(defpackage "PARSER4-RULES"  (:nicknames "PR4") (:use))

(defvar *verbose?* nil)

(defconstant +default-precedence+ nil)

;; auxiliary rutine for controlling whether to convert strings to upper case

;;; ========================================

(defstruct (parser (:print-function print-parser)) 
  name					; symbol
  (total-rule-count  0 :type fixnum)	; number of rules of all types
  (bv-size           0 :type fixnum)	; number of rules that can be parents of other
					; rules (i.e., non-keyword  and non-atomic)
					; Note:  a rule is counted multiple times if 
					; it is referenced with multiple precedences.
  toplevel-rule				; 
  symbol-rule				; rule for symbol    [provided by user's grammar]
  string-rule				; rule for string    [provided by user's grammar]
  number-rule				; rule for number    [provided by user's grammar]
  character-rule			; rule for character [provided by user's grammar]
  rules					; list of rules
  ;;
  ht-name-to-rule			; hash table:  name ->  rule
  ht-name-to-reductions			; hash table:  name ->  (... (rule . child-index) ...)
  ht-string-to-keyword-rule		; hash table:  string -> keyword-rule
  ht-name-to-precedences		; hash table:  rule-name ->  (... precedence ...)
  ht-rnp-to-bvi				; hash table:  (rule-name  . precedence) => bit vector index
  ht-rnp-to-handles-bv			; hash table:  (rule-name  . precedence) => bit-vector
  ;;
  scratch-bv				; simple bitvector of length number-of-rules
  zero-bv				; simple bitvector of length number-of-rules
  keywords-are-keywords-only?		; boolean
  default-semantic-alist		; alist of pairs: (<number> . :unspecified)
  case-sensitive?                       ; boolean
  ;;
  rule-package                          ;  package in which aux parser rules are interned
  symbol-package                        ;  package in which parser will create symbols in results
  ;;
  ht-expr-to-parser-rules               ; hash table:  expr -> pprinter routine for expr
  ht-type-to-parser-rules               ; hash table:  (type-of expr) -> pprinter routine for expr
  ht-car-to-parser-rules                ; hash table:  (car expr) -> pprinter routine for expr
  )

(defun print-parser (parser stream ignore-level)
  (declare (ignore ignore-level))
  (format stream "<Parser ~A with ~D rules, and keywords ~A>" 
	  (parser-name parser)
	  (parser-total-rule-count parser)
	  (if (parser-keywords-are-keywords-only? parser)
	      "are only keywords"
	    "may also be symbols or numbers")))
  
(defvar *current-parser* nil) ; used by define-sw-parser-rule 
#+DEBUG-PARSER (defvar *current-parser-session* nil) 

(defun new-parser (&optional (name (intern (gensym "PARSER-") "KEYWORD"))
			     &key 
			     (case-sensitive? nil)
			     (rule-package    (find-package "KEYWORD"))
			     (symbol-package  lisp::*package*))
  #+DEBUG-PARSER 
  (progn
    (terpri)
    (comment "Note:  These values are determined by keyword args in the call to new-parser:")
    (comment " ")
    (comment "  Parser will ~Abe case sensitive." (if case-sensitive? "" "not "))
    (comment "  Auxiliary parser rules will be interned in the ~A package." 
	     (package-name rule-package))
    (comment "  Symbols generated when parsing will be interned in the ~A package." 
	     (package-name symbol-package))
    (terpri))
  (let ((parser
	 (make-parser 
	  :name                      name
	  :ht-name-to-rule           (make-hash-table :size 2000)
	  :ht-name-to-reductions     (make-hash-table :size 2000)
	  :ht-string-to-keyword-rule
	  (make-hash-table :size 2000 
			   :test (if case-sensitive? 
				     #+allegro 'string= #-allegro 'equal 
				    'string-equal))
	  :ht-name-to-precedences    (make-hash-table :size 2000)
	  :ht-rnp-to-bvi             (make-hash-table :size 2000 :test 'equal)
	  :ht-rnp-to-handles-bv      (make-hash-table :size 2000 :test 'equal)
	  :case-sensitive?           case-sensitive?
	  ;;
	  :rule-package              rule-package 
	  :symbol-package            symbol-package 
	  ;;
	  :ht-expr-to-parser-rules   (make-hash-table :size 2000 :test 'eq)
	  :ht-type-to-parser-rules   (make-hash-table :size 2000 :test 'eq)
	  :ht-car-to-parser-rules    (make-hash-table :size 2000 :test 'eq)
	  )))
    (setq *current-parser* parser)
    parser))

;;; ========================================

(defstruct (parse-session (:print-function print-parser-session))
  file
  parser
  tokenizer
  locations
  comments
  results
  gaps
  ambiguities
  (report-gaps?        t)
  (report-ambiguities? t)
  package
  (error-reported?    nil) 
  )

(defun print-parser-session (session stream ignore-level)
  (declare (ignore ignore-level))
  (format stream "<Parse of ~A using ~A (~D token~:P) yielding ~D result~:P with ~D gap~:P and ~D ambiguit~:@P>"
	  (parse-session-file session)
	  (parser-name (parse-session-parser      session))
	  (length      (parse-session-locations   session))
	  (length      (parse-session-results     session))
	  (length      (parse-session-gaps        session))
	  (length      (parse-session-ambiguities session))
	  ))

(defun SUCCESSFUL-PARSE-SESSION? (session)
  (and (null (parse-session-gaps            session))
       (null (parse-session-ambiguities     session))
       (null (parse-session-error-reported? session))
       (not (null (parse-session-results    session)))))

;;; ========================================

(defstruct (parser-location (:print-function print-parser-location))
  index			; fixnum -- location in vector
  position		;  (byte-position line column)
  post-nodes		; seq of parser-node
  ;;  pre-nodes		; seq of parser-node  (never used)
  partial-node-data	; seq of (parser-node . <index into children vector>)
  desired-bv		; bitvector containing bits for rules targeted above
  pre-comments		; comment tokens between previous location and this one
  )

(defun print-parser-location (ploc stream ignore-level)
  (declare (ignore ignore-level))
  (let* ((plc (parser-location-position ploc))
	 (plc-str
	  (if (null plc)
	      "eof"
	    (let ((byte-pos (first plc))
		  (line     (second plc))
		  (column   (third plc)))
	      (format nil "~6D (~4D ~2D )" byte-pos line column)))))
    (format stream "<Parser location ~6D at ~A with ~4D productions, ~3D post-nodes>"
	    (parser-location-index ploc)
	    plc-str
	    (length (parser-location-post-nodes ploc))
	    (length (parser-location-partial-node-data ploc)))))


;;; ========================================

(defstruct (parser-rule (:print-function print-parser-rule))
  name             
  reductions    ; seq of reduction's [parent-rule, child-index, bv-index ?]
  ;; [parent-rule 0 ..] => whenever a node is created using this rule, 
  ;;                                    create a (possibly partial) new parent node using the parent rule
  ;;                                    such that this node will be the first child, i.e.
  ;;                                    such that the parent node starts at the same location as this node
  ;; [parent-rule 1..] => whenever a node is created using this rule, 
  ;;                                    create a partial parent node using the parent rule
  ;;                                    such that this node will be the second child, i.e.
  ;;                                    such that the parent node will start at some earlier location 
  (precedence +default-precedence+) ; fixed precedence 
  bvi            ; bit-vector index
  semantics      ; e.g., the actual string for a symbol
  p2bvi-map      ; alist:   precedence => bvi
  items          ; the sub-rules of this rule
  main-rule?     ; was this entered by the user as a top-level rule?
  documentation 
  )

(defmacro unspecified? (x)
  `(eq ,x :unspecified))

(defun print-parser-rule (prule stream level)
  (let ((semantics (parser-rule-semantics prule)))
    (format stream "<~A: ~A~A>" 
	    (type-of prule)
	    (parser-rule-name prule)
	    (cond ((null semantics) 
		   "")
		  ((and (numberp *print-level*)
			(numberp level)
			(> level *print-level*))
		   "#")
		  (t
		   (format nil " ~S" semantics))))))

(defstruct (parser-atomic-rule (:include parser-rule))
  )

(defstruct (parser-token-rule (:include parser-rule))
  )

(defstruct (parser-keyword-rule (:include parser-rule))
  keyword
  )

(defstruct (parser-id-rule (:include parser-rule))
  subrule
  )

(defstruct (parser-tuple-rule (:include parser-rule)))

(defstruct (parser-anyof-rule (:include parser-rule))
  possible-handles-bv)

(defstruct (parser-pieces-rule (:include parser-rule))
  possible-handles-bv)

(defstruct (parser-repeat-rule (:include parser-rule)))

(defmacro parser-repeat-rule-element (rule)
  `(svref (parser-rule-items ,rule) 0))

(defmacro parser-repeat-rule-separator (rule)
  `(svref (parser-rule-items ,rule) 1))

;;; (defmacro do-parser-rule-items ((item-var rule 
;;; 				 &optional (final-value nil) (index-var (gensym))) 
;;; 				&body body)
;;;   (let ((items-var (gensym "ITEMS")))
;;;     `(let ((,items-var (parser-rule-items ,rule)))
;;;        (dotimes (,index-var (length ,items-var) ,final-value)
;;; 	 (let ((,item-var (svref ,items-var ,index-var)))
;;; 	   ,@body)))))
  
(defmacro do-parser-rule-items ((item-var rule 
				 &optional (final-value nil) (index-var (gensym))) 
				&body body)
  (let ((rule-var  (gensym "RULE"))
	(items-var (gensym "ITEMS")))
    `(let* ((,rule-var ,rule)
	    (,items-var (parser-rule-items ,rule-var)))
       (dotimes (,index-var (length ,items-var) ,final-value)
	 (let ((,item-var (svref ,items-var ,index-var)))
	   (unless (and (null ,item-var)
			(parser-repeat-rule-p ,rule-var))
	     ,@body))))))
  
(defmacro superfluous-anyof-rule? (rule)
  (let ((rule-var (gensym)))
    `(let* ((,rule-var ,rule))
       ;; if both of these are nil, the rule will be bypassed...
       (let ((superfluous?
	      (and (eq (structure-type-of ,rule-var) 'parser-anyof-rule)
		   (null (parser-rule-precedence ,rule-var))
		   (null (parser-rule-semantics  ,rule-var))
		   (do-parser-rule-items (item ,rule-var t) 
 		     (when (not (null (parser-rule-item-semantic-index item)))
		       (return nil)))
		   )))
	 (when-debugging
	  (when *verbose?*
	    (when superfluous?
	      (format t "~&Superfluous ANYOF rule: ~S~%" ,rule-var))))
	 superfluous?))))
    
(defun find-parser-rule (parser name)
  (or (maybe-find-parser-rule parser name)
      (progn (break "Can't find rule ~S" name) nil)))

(defun maybe-find-parser-rule (parser name)
  (cond ((symbolp name)
	 (gethash name (parser-ht-name-to-rule parser)))
	((parser-rule-p name)
	 (warn "Trying to find rule, but already have it: ~S" name)
	 name)
	(t
	 (error "Trying to find rule using a name that is not a symbol: ~S" name))))

(defun install-parser-rule (parser new-rule)
  (let* ((name (parser-rule-name new-rule))
	 (old-rule (maybe-find-parser-rule parser name)))
    (cond ((null old-rule)
	   (setf (gethash name (parser-ht-name-to-rule parser)) new-rule))
	  ((eq new-rule old-rule)
	   nil)
	  (t
	   (warn "Redefining rule ~A from ~S to ~S" name old-rule new-rule)
	   (setf (gethash name (parser-ht-name-to-rule parser)) new-rule)))))

;;; ========================================

(defstruct parser-rule-item
  optional?      
  rule                 
  precedence
  ;; rule & precedence => possible-children-bv
  possible-children-bv ; allows quick match on multiple rules...
  ;; closure routine maps possible-children-bv => possible-handles-bv
  possible-handles-bv  ; was desired-bv
  semantic-index 
  )
  
;;; ========================================

(defstruct reduction
  parent-rule
  child-index)

;;; ========================================

(defstruct (parser-node (:print-function print-parser-node))
  rule             ; parser-rule
  precedence       ; nil or fixnum
  bvi              ; bit-vector index
  semantics  
  pre-index        ; index of parser-location 
  post-index-ptr   ; mutable cell containing index of parser-location 
  parents          ; seq of parser-node
  children         ; vector of parser-node
  number
  )

(defmacro parser-node-post-index (node)
  `(car (parser-node-post-index-ptr ,node)))

(defun print-parser-node (pnode stream ignore-level)
  (declare (ignore ignore-level))
  (format stream "<Parser Node ~6D at [~3D:~3D] with rule ~A>"
	  (parser-node-number     pnode)
	  (parser-node-pre-index  pnode)
	  (parser-node-post-index pnode)
	  (let ((rule (parser-node-rule pnode)))
	    (if (parser-rule-p rule)
		(parser-rule-name rule)
	      (format nil "[?? Rule: ~S ??]" rule)))))

#+DEBUG-PARSER (defvar *all-nodes* nil)
#+DEBUG-PARSER (defvar *parser-node-number* 0)

(defmacro create-parser-node (&body x)
  #-DEBUG-PARSER
  `(make-parser-node ,@x)
  #+DEBUG-PARSER
  `(let ((new-node (make-parser-node 
		    :NUMBER (incf *parser-node-number*) 
		    ,@x)))
     (when-debugging
      ;; show-node mightl not be very informative here
      (push new-node *all-nodes*))
     new-node)
  )

#+OPTIMIZE-PARSER
(defmacro structure-type-of (structure)
  `(caar (excl::structure-ref ,structure 0)))
#-OPTIMIZE-PARSER
(defmacro structure-type-of (structure)
  `(type-of ,structure))

#+OPTIMIZE-PARSER
(defmacro sv-length (sv)
  `(excl::sv_size ,sv))
#-OPTIMIZE-PARSER
(defmacro sv-length (sv)
  `(length ,sv))

;;; ========================================

#-OPTIMIZE-PARSER
(defmacro sublis-result (alist pattern)
  `(sublis ,alist ,pattern :test 'eq))
;; #+OPTIMIZE-PARSER
;; (defmacro sublis-result (alist pattern)
;;   (let ((a-var (gensym))
;; 	(p-var (gensym))
;; 	(result-var (gensym)))
;;     `(let ((,a-var ,alist)
;; 	   (,p-var ,pattern) 
;; 	   (,result-var nil)) 
;;        (cond ((atom ,p-var)
;; 	      (or (cdr (assoc ,p-var ,a-var :test 'eq)) ,p-var))
;; 	     (t
;; 	      (dolist (elt ,p-var)
;; 		(push (or (cdr (assoc elt ,a-var :test 'eq)) elt)
;; 		      ,result-var))
;; 	      (nreverse ,result-var))))))
#+OPTIMIZE-PARSER
(defmacro sublis-result (alist pattern)
  `(labels ((local-sublis (alist pattern)
	      (cond ((null pattern)
		     nil)
		    ((atom pattern)
		     (let ((pair (assoc pattern alist :test 'eq))) 
		       (if (null pair)
			   pattern
			 (cdr pair))))
		    (t
		     (cons (local-sublis alist (car pattern))
			   (local-sublis alist (cdr pattern)))))))
     (local-sublis ,alist ,pattern)))

;;; ===== performance hacks ===

(defvar *OLD-TIMING-DATA* nil)
(defvar *TIMING-DATA*     nil)
(defvar *LAST-REAL-TIME*  0)
(defvar *LAST-RUN-TIME*   0)

(defun reset-timing-data ()
  (push *timing-data* *old-timing-data*)
  (setq *timing-data* nil))

(defun incf-timing-data (key)
  (let* ((run-time (GET-INTERNAL-RUN-TIME))
	 (real-time (GET-INTERNAL-REAL-TIME))
	 (run-delta  (- run-time  *last-run-time*))
	 (real-delta (- real-time *last-real-time*))
	 (entry (assoc key *timing-data*)))
    (cond ((null entry)
	   (push (list key run-delta real-delta) *timing-data*))
	  (t
	   (incf (cadr entry) run-delta)
	   (incf (caddr entry) real-delta)))
    (setq *last-run-time*  (GET-INTERNAL-RUN-TIME))
    (setq *last-real-time* (GET-INTERNAL-REAL-TIME))))

