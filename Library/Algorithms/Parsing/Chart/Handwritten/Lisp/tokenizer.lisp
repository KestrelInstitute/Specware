;;; -*- Mode: LISP; Package: Parser; Base: 10; Syntax: Common-Lisp -*-

(in-package "PARSER4")

;;; ========================================================================

(defun ctp-arg-test (arg value example)
  (when (null value)
    (warn "CREATE-TOKENIZER-PARAMETERS missing keyword arg  ~S, e.g. ~A"
	  arg
	  example)))

(defun create-tokenizer-parameters (&key
				    ;;
				    name
				    ;;
				    size-of-character-set
				    ;;
				    word-symbol-start-chars
				    word-symbol-continue-chars
				    ;;
				    non-word-symbol-start-chars
				    non-word-symbol-continue-chars
				    ;;
				    number-start-chars
				    number-continue-chars
				    ;;
				    digits-may-start-symbols?
				    ;;
				    string-quote-char
				    string-escape-char
				    ;;
				    whitespace-chars 
				    ;;
				    separator-chars
				    ;;
				    comment-to-eol-chars
				    ;;
				    extended-comment-delimiters
				    ;;
				    ad-hoc-keywords
				    ad-hoc-symbols
				    ad-hoc-numbers
				    ;;
				    case-sensitive?
				    ;;
				    )
  (ctp-arg-test :word-symbol-start-chars         word-symbol-start-chars         "the alphabet")
  (ctp-arg-test :word-symbol-continue-chars      word-symbol-continue-chars      "the alphabet, digits, and underbar")

  (ctp-arg-test :non-word-symbol-start-chars     non-word-symbol-start-chars     "some chars like !@#$^&*~+-=|<>?/.")
  (ctp-arg-test :non-word-symbol-continue-chars  non-word-symbol-continue-chars  "some chars like !@#$^&*~+-=|<>?/.")

  (ctp-arg-test :number-start-chars              number-start-chars              "the digits, plus, minus, and maybe dot and/or slash")
  (ctp-arg-test :number-continue-chars           number-continue-chars           "the digits, and maybe dot and/or slash")

  (ctp-arg-test :comment-to-eol-chars            comment-to-eol-chars            "semi-colon (#\;) or percent (#\%) ")

  (let ((whitespace-table      (make-array size-of-character-set :initial-element 0))
	(word-symbol-table     (make-array size-of-character-set :initial-element 0))
	(non-word-symbol-table (make-array size-of-character-set :initial-element 0))
	(number-table          (make-array size-of-character-set :initial-element 0))
	(string-table          (make-array size-of-character-set :initial-element 0))
	(comment-table         (make-array size-of-character-set :initial-element 0))
	(ad-hoc-table          (make-array size-of-character-set :initial-element 0))
	(separator-tokens      (make-array size-of-character-set :initial-element 0))
	)
    ;; Note: in the following, we consistently assign the problematic codes first, so that legal codes can override them
    ;; in cases where a character has both an illegal and a legal code for some context.
    ;;
    ;;  whitespace-table is used when scanning whitespace...
    ;;
    ;; codes that are illegal after whitespace is started:
    (assign-tokenizer-codes whitespace-table word-symbol-continue-chars     +word-symbol-continue-code+)
    (assign-tokenizer-codes whitespace-table non-word-symbol-continue-chars +non-word-symbol-continue-code+)
    (assign-tokenizer-codes whitespace-table number-continue-chars          +number-continue-code+)
    ;; codes that are legal after whitespace is started:
    (assign-tokenizer-codes whitespace-table word-symbol-start-chars        +word-symbol-start-code+)
    (assign-tokenizer-codes whitespace-table non-word-symbol-start-chars    +non-word-symbol-start-code+)
    (assign-tokenizer-codes whitespace-table number-start-chars             +number-start-code+)
    (assign-tokenizer-code  whitespace-table string-quote-char              +string-quote-code+)
    (assign-tokenizer-codes whitespace-table comment-to-eol-chars           +comment-to-eol-code+)
    (assign-tokenizer-codes whitespace-table whitespace-chars               +whitespace-code+)
    (assign-tokenizer-codes whitespace-table separator-chars                +separator-code+)
    (assign-tokenizer-code  whitespace-table #\#                            +char-literal-start-code+)
    ;;
    ;;  word-symbol-table 
    ;;
    ;; codes that are illegal after a word symbol is started:
    (assign-tokenizer-codes word-symbol-table word-symbol-start-chars        +word-symbol-start-code+) 
    (assign-tokenizer-codes word-symbol-table number-continue-chars          +number-continue-code+)
    (assign-tokenizer-codes word-symbol-table non-word-symbol-continue-chars +non-word-symbol-continue-code+)
    ;; codes that are legal after a word symbol is started:
    (assign-tokenizer-codes word-symbol-table non-word-symbol-start-chars    +non-word-symbol-start-code+)
    (assign-tokenizer-codes word-symbol-table number-start-chars             +number-start-code+) ; probably overridden by +word-symbol-continue-code+
    (assign-tokenizer-code  word-symbol-table string-quote-char              +string-quote-code+)
    (assign-tokenizer-codes word-symbol-table comment-to-eol-chars           +comment-to-eol-code+)
    (assign-tokenizer-codes word-symbol-table whitespace-chars               +whitespace-code+)
    (assign-tokenizer-codes word-symbol-table word-symbol-continue-chars     +word-symbol-continue-code+)
    (assign-tokenizer-codes word-symbol-table separator-chars                +separator-code+)
    ;;
    ;;  non-word-symbol-table 
    ;;
    ;; codes that are illegal after a non-word symbol is started:
    (assign-tokenizer-codes non-word-symbol-table non-word-symbol-start-chars    +non-word-symbol-start-code+) 
    (assign-tokenizer-codes non-word-symbol-table number-continue-chars          +number-continue-code+)
    (assign-tokenizer-codes non-word-symbol-table word-symbol-continue-chars     +word-symbol-continue-code+)
    ;; codes that are legal after a non-word symbol is started:
    (assign-tokenizer-codes non-word-symbol-table word-symbol-start-chars        +word-symbol-start-code+)
    (assign-tokenizer-codes non-word-symbol-table number-start-chars             +number-start-code+) ; proably survive as final code 
    (assign-tokenizer-code  non-word-symbol-table string-quote-char              +string-quote-code+)
    (assign-tokenizer-codes non-word-symbol-table comment-to-eol-chars           +comment-to-eol-code+)
    (assign-tokenizer-codes non-word-symbol-table whitespace-chars               +whitespace-code+)
    (assign-tokenizer-codes non-word-symbol-table non-word-symbol-continue-chars +non-word-symbol-continue-code+)
    (assign-tokenizer-codes non-word-symbol-table separator-chars                +separator-code+)
    ;;
    ;;  number-table is used when scanning numbers...
    ;;
    ;; codes that are illegal after a number is started:
    (assign-tokenizer-codes number-table number-start-chars              +number-start-code+)
    (assign-tokenizer-codes number-table word-symbol-continue-chars      +word-symbol-continue-code+)
    (assign-tokenizer-codes number-table non-word-symbol-continue-chars  +non-word-symbol-continue-code+)
    ;; codes that are illegal after a number is started, but might become legal:
    (assign-tokenizer-codes number-table word-symbol-start-chars         +word-symbol-start-code+)
    (assign-tokenizer-codes number-table non-word-symbol-start-chars     +non-word-symbol-start-code+)
    ;; codes that are legal after a number is started:
    (assign-tokenizer-code  number-table string-quote-char               +string-quote-code+)
    (assign-tokenizer-codes number-table comment-to-eol-chars            +comment-to-eol-code+)
    (assign-tokenizer-codes number-table whitespace-chars                +whitespace-code+)
    (assign-tokenizer-codes number-table number-continue-chars           +number-continue-code+)
    (assign-tokenizer-codes number-table separator-chars                 +separator-code+)
    ;;
    ;;  string-table is used when scanning strings
    ;;
    (assign-tokenizer-code  string-table string-quote-char     +string-quote-code+)
    (assign-tokenizer-code  string-table string-escape-char    +string-escape-code+)
    ;;
    ;;
    (dolist (quad extended-comment-delimiters)
      (let* ((open-comment-string  (first  quad))
	     (close-comment-string (second quad))
	     (recursive?           (third  quad)) 
	     (eof-ok?              (if (null (cdddr quad)) nil (fourth quad))))
	(unless (and (stringp open-comment-string)
		     (> (length open-comment-string) 0)
		     (stringp close-comment-string)
		     (> (length close-comment-string) 0)
		     (member recursive? '(t nil))
		     (member eof-ok?    '(t nil)))
	  (break "Bad description of extended comment delimiters.  Want (open-str close-str recursive? eof-ok?) : ~S" 
		 quad))
	(setf (svref comment-table (char-code (schar open-comment-string 0)))
	  +maybe-open-comment-code+)))
    ;;
    (dolist (char separator-chars)
      (setf (svref separator-tokens (char-code char)) (string char)))
    (dolist (string ad-hoc-keywords)
      (setf (svref ad-hoc-table (char-code (schar string 0))) 
	+maybe-start-of-ad-hoc-token+))
    (dolist (string ad-hoc-symbols)
      (setf (svref ad-hoc-table (char-code (schar string 0))) 
	+maybe-start-of-ad-hoc-token+))
    (dolist (string ad-hoc-numbers)
      (setf (svref ad-hoc-table (char-code (schar string 0))) 
	+maybe-start-of-ad-hoc-token+))
    (let ((ht-ad-hoc-types (make-hash-table
			    :test (if case-sensitive?
				      #+allegro 'string= #-allegro 'equal
				    'string-equal))))
      (dolist (keyword-string ad-hoc-keywords)
	(setf (gethash keyword-string ht-ad-hoc-types) :AD-HOC-KEYWORD-ONLY))
      (dolist (symbol-string ad-hoc-symbols)
	(let ((old-value (gethash symbol-string ht-ad-hoc-types)))
	  (setf (gethash symbol-string ht-ad-hoc-types) 
	    (if (null old-value)
		:AD-HOC-SYMBOL-ONLY
                :AD-HOC-KEYWORD-AND-SYMBOL-ONLY))))
      (dolist (number-string ad-hoc-numbers)
	(let ((old-value (gethash number-string ht-ad-hoc-types)))
	  (setf (gethash number-string ht-ad-hoc-types) 
	    (ecase old-value
	      ((nil)               :AD-HOC-NUMBER-ONLY)
	      (:KEYWORD            :AD-HOC-KEYWORD-AND-NUMBER-ONLY)
	      (:SYMBOL             :AD-HOC-SYMBOL-AND-NUMBER-ONLY)
	      (:KEYWORD-AND-SYMBOL :AD-HOC-KEYWORD-AND-SYMBOL-AND-NUMBER-ONLY)))))

      ;;
      (when-debugging
       (when *verbose?* 
	 (let ((alist `((,+number-start-code+             . +number-start-code+)
			(,+number-continue-code+          . +number-continue-code+)
			(,+word-symbol-start-code+        . +word-symbol-start-code+)
			(,+word-symbol-continue-code+     . +word-symbol-continue-code+)
			(,+non-word-symbol-start-code+    . +non-word-symbol-start-code+)
			(,+non-word-symbol-continue-code+ . +non-word-symbol-continue-code+)
			(,+separator-code+                . +separator-code+)
			(,+string-quote-code+             . +string-quote-code+)
			(,+string-escape-code+            . +string-escape-code+)
			(,+comment-to-eol-code+           . +comment-to-eol-code+)
			(,+whitespace-code+               . +whitespace-code+)
			(,+char-literal-start-code+       . +char-literal-start-code+)
			(0                                . "...")
			)))
	   (comment "============================================================================")
	   (terpri)
	   (dotimes (i size-of-character-set)
	     (let ((n (svref whitespace-table i)))
	       (comment "At whitespace ~3D (~12S) => ~A" 
			i (code-char i)  (cdr (assoc n alist)))))
	   (terpri)
	   (dotimes (i size-of-character-set)
	     (let ((n (svref word-symbol-table i)))
	       (comment"At word symbol ~3D (~12S) => ~A" 
		       i (code-char i)  (cdr (assoc n alist)))))
	   (terpri)
	   (dotimes (i size-of-character-set)
	     (let ((n (svref non-word-symbol-table i)))
	       (comment"At non-word symbol ~3D (~12S) => ~A" 
		       i (code-char i)  (cdr (assoc n alist)))))
	   (terpri)
	   (dotimes (i size-of-character-set)
	     (let ((n (svref number-table i)))
	       (comment "At number ~3D (~12S) => ~A" 
			i (code-char i)  (cdr (assoc n alist)))))
	   (terpri)
	   (dotimes (i size-of-character-set)
	     (let ((n (svref string-table i)))
	       (comment "At string ~3D (~12S) => ~A" 
			i (code-char i)  (cdr (assoc n alist)))))
	   (terpri)
	   (dotimes (i size-of-character-set)
	     (if (= (svref comment-table i) +maybe-open-comment-code+)
		 (comment "The character ~D (~S) may start an extended comment"
			  i (code-char i))))
	   (terpri)
	   (dotimes (i (length ad-hoc-table))
	     (comment "Ad-hoc-table (~3D ~S) = ~S" i (code-char i) (svref ad-hoc-table i)))
	   (terpri)
	   (dolist (x ad-hoc-keywords) (comment "Ad-hoc-keyword : ~S" x))
	   (dolist (x ad-hoc-symbols)  (comment "Ad-hoc-symbol  : ~S" x))
	   (dolist (x ad-hoc-numbers)  (comment "Ad-hoc-number  : ~S" x))
	   (terpri)
	   (maphash #'(lambda (key value) (comment "ad-hoc-type for ~S = ~S" key value))
		    ht-ad-hoc-types)
	   (terpri)
	   (comment "============================================================================"))))

      (let ((ad-hoc-strings
	     ;; sort the strings in descending length so that "__" will be seen before "_", "??" before "?" etc.
	     (sort (append ad-hoc-keywords 
			   ad-hoc-symbols 
			   ad-hoc-numbers)
		   #'(lambda (x y) 
		       (> (length x) (length y))))))
	(make-tokenizer-parameters :name                      name
				   :whitespace-table          whitespace-table 
				   :word-symbol-table         word-symbol-table 
				   :non-word-symbol-table     non-word-symbol-table 
				   :number-table              number-table 
				   :string-table              string-table 
				   :digits-may-start-symbols? digits-may-start-symbols?
				   :comment-table             comment-table 
				   :separator-tokens          separator-tokens
				   :comment-delimiters        extended-comment-delimiters
				   :ad-hoc-types-ht           ht-ad-hoc-types
				   :ad-hoc-table              ad-hoc-table
				   :ad-hoc-strings            ad-hoc-strings
				   ))
      )))




(defun assign-tokenizer-codes (table chars code)
  (setq chars (coerce chars 'list))
  (dotimes  (i (length chars))
    (setf (svref table (char-code (nth i chars))) code)))

(defun assign-tokenizer-code (table char code)
  (unless (null char)
    (setf (svref table (char-code char)) code)))

;;; ========================================================================

(defun tokenize-file (session file tokenizer)
  (incf-timing-data  'start-tokenize-file)
  (let ((all-tokens 
	 ;; the tokenizer will call extract-tokens-from-file, using language-specific parameters
	 (funcall tokenizer file))
	(comment-tokens     '())
	(non-comment-tokens '())
	(comment-eof-error? nil))
    (incf-timing-data 'tokenize-file)
    (dolist (token all-tokens)
      (cond ((member (first token) '(:COMMENT-TO-EOL :EXTENDED-COMMENT))
	     (push token comment-tokens))
	    (t
	     (when (eq (first token) :EXTENDED-COMMENT-ERROR)
	       (setq comment-eof-error? t))
	     (push token non-comment-tokens))))
    (setq non-comment-tokens (nreverse non-comment-tokens)) 
    (setq comment-tokens     (nreverse comment-tokens)) 
    (incf-timing-data 'tokenize-file)
    (let ((result
	   (install-tokens session non-comment-tokens comment-tokens)))
      (incf-timing-data 'install-tokens)
      (values result (length all-tokens) comment-eof-error?))))

;;; ========================================================================

(defun extract-tokens-from-file (file tokenizer-parameters)
  (let ((whitespace-table          (tokenizer-parameters-whitespace-table          tokenizer-parameters))
	(word-symbol-table         (tokenizer-parameters-word-symbol-table         tokenizer-parameters))
	(non-word-symbol-table     (tokenizer-parameters-non-word-symbol-table     tokenizer-parameters))
	(number-table              (tokenizer-parameters-number-table              tokenizer-parameters))
	(string-table              (tokenizer-parameters-string-table              tokenizer-parameters))
	(comment-table             (tokenizer-parameters-comment-table             tokenizer-parameters))
	(separator-tokens          (tokenizer-parameters-separator-tokens          tokenizer-parameters))
	(comment-quads             (tokenizer-parameters-comment-delimiters        tokenizer-parameters))
	(digits-may-start-symbols? (tokenizer-parameters-digits-may-start-symbols? tokenizer-parameters))
	(ht-ad-hoc-types           (tokenizer-parameters-ad-hoc-types-ht           tokenizer-parameters))
	(ad-hoc-table              (tokenizer-parameters-ad-hoc-table              tokenizer-parameters))
	(ad-hoc-strings            (tokenizer-parameters-ad-hoc-strings            tokenizer-parameters)))
    (let ((tokens nil))
      (with-open-file (stream file) 
	(let ((ps-stream (make-pseudo-stream :unread-chars nil :stream stream))
	      ;; The upper-left corner of the file is considered 1:0:1 (line 1, column 0, byte 1)
	      ;; so the character one to the left of that is 1:-1:0 (line 1, column -1, byte 0).
	      ;; So we are at 1:-1 before we read the first character.
	      (pre-line 1) (pre-column -1) (pre-byte 0))
	  (loop do
	    (multiple-value-bind (type value 
				       first-byte first-line first-column
				       last-byte  last-line  last-column)
		(extract-token-from-pseudo-stream ps-stream 
						  pre-byte pre-line pre-column
						  whitespace-table 
						  word-symbol-table 
						  non-word-symbol-table 
						  number-table 
						  string-table 
						  digits-may-start-symbols?
						  comment-table
						  separator-tokens 
						  comment-quads
						  ad-hoc-table
						  ad-hoc-strings)
	      (cond ((eq type :EOF)
		     (return nil))
		    ((eq type :WORD-SYMBOL-TERMINATED-BY-HASH) ; new hack for # inside URI's...
		     (push (list (or (gethash value ht-ad-hoc-types)
				     :WORD-SYMBOL)
				 value 
				 (list first-byte first-line first-column) 
				 (list last-byte  last-line  last-column)) 
			   tokens)
		     (incf last-byte)
		     (incf last-column)
		     (push (list (or (gethash :NON-WORD-SYMBOL ht-ad-hoc-types)
				     :NON-WORD-SYMBOL)
				 "#"
				 (list last-byte  last-line  last-column)
				 (list last-byte  last-line  last-column))
			   tokens))
		    (t
		     (push (list (or (and (or (eq type :AD-HOC) 
					      (eq type :WORD-SYMBOL)
					      (eq type :NON-WORD-SYMBOL))
					  (gethash value ht-ad-hoc-types))
				     type)
				 value 
				 (list last-byte  last-line  last-column) 
				 (list last-byte  last-line  last-column)) 
			   tokens)))
	      (setq pre-byte   last-byte 
		    pre-line   last-line 
		    pre-column last-column)))))
      (nreverse tokens))))

;;; ========================================================================

(defun extract-token-from-pseudo-stream (ps-stream 
					 pre-byte pre-line pre-column
					 whitespace-table 
					 word-symbol-table
					 non-word-symbol-table
					 number-table
					 string-table
					 digits-may-start-symbols?
					 comment-table
					 separator-tokens 
					 extended-comment-quads
					 ad-hoc-table
					 ad-hoc-strings)
  (when digits-may-start-symbols?
    (error "The option digits-may-start-symbols? is currently diabled."))

  (let* ((current-byte   pre-byte)
	 (current-line   pre-line)
	 (current-column pre-column)
	 (first-byte     )
	 (first-line     )
	 (first-column   )
	 (last-byte      )
	 (last-line      )
	 (last-column    )
	 (char           )
	 (char-code      )
	 (token-chars    nil)
	 (this-ec-quad   nil)
	 (hex-char-1      )
	 (hex-char-code-1 )
	 (hex-char-2      )
	 (hex-char-code-2 ))

    (macrolet ((local-warn (prefix line column byte msg &rest args)
		 `(warn "At line ~3D:~2D  ~?" 
			;; ,prefix
			,line ,column	; ,byte
			,msg (list ,@args)))
	       (warn-here (msg &rest args)
		 `(local-warn "At" current-line current-column current-byte 
			      ,msg ,@args))
	       (local-read-char (char-var char-code-var eof-action newline-action open-extended-comment-action)
		 `(progn              
		    (setq ,char-var (ps-read-char ps-stream))
		    (incf current-byte)
		    (if (eq ,char-var +tokenizer-eof+) 
			,eof-action
		      (progn
			(setq ,char-code-var (char-code ,char-var))
			(cond ((eq ,char-var #\newline)
			       ;; we proceed to line+1 : -1, so that the next character read 
			       ;;  (which will be the leftmost on the line) will be at line+1 : 0
			       ;; current-byte was incremented above, so we don't need to touch that here
			       (incf current-line)
			       (setq current-column -1)
			       ,newline-action)
			      (t
			       (incf current-column)))
			,@(if (null open-extended-comment-action)
			      ()
			    `((when (and (eq (svref comment-table ,char-code-var) 
					     +maybe-open-comment-code+)
					 (not (null (setq this-ec-quad
						      (applicable-extended-comment-quad
						       ,char-var
						       ps-stream 
						       extended-comment-quads)))))
				,open-extended-comment-action)))))))
	       (local-unread-char (char-var)
		 `(progn
		    (ps-unread-char ,char-var ps-stream)
		    ;; ??  If we do this repeatedly, unreading newlines, can we end up at a column left of -1 ??
		    ;; If that happens, we could decrement the line, but then what should the column be??
		    (decf current-byte)
		    (decf current-column)
		    ))
	       (set-first-positions ()
		 ;; inclusive -- first character of token
		 `(setq first-byte   current-byte
			first-line   current-line
			first-column current-column))
	       (set-last-positions ()
		 ;; inclusive -- last character of token
		 `(setq last-byte   current-byte
			last-line   current-line
			last-column current-column))
	       (return-values-using-prior-last (type value)
		 `(return-from extract-token-from-pseudo-stream 
		    (values ,type ,value
			    first-byte first-line first-column
			    last-byte  last-line  last-column)))
	       (return-values (type value)
		 `(progn
                    (set-last-positions)
                    (return-values-using-prior-last ,type ,value)))
	       (termination-warning (char-var char-code-var kind-of-token misc-chars kind-of-char)
		 `(local-warn "After"
			      last-line last-column last-byte 
			      "Terminating ~A \"~A~A\" with ~S (hex code ~2,'0X)~A."
			      ,kind-of-token
			      ,misc-chars
			      (coerce (nreverse token-chars) 'string)
			      ,char-var ,char-code-var
			      ,kind-of-char))
	       (look-for-ad-hoc-tokens (char-var char-code-var)
		 `(unless (eq (svref ad-hoc-table ,char-code-var) 0)
		    (dolist (ad-hoc-string ad-hoc-strings)
		      (debugging-comment "Looking for ad-hoc-string ~S starting with ~S" ad-hoc-string ,char-var)
		      (when (eq (schar ad-hoc-string 0) ,char-var)
			(let ((found-ad-hoc-string? 
			       (dotimes (i (1- (length ad-hoc-string)) t)
				 (let ((local-char (ps-read-char ps-stream)))
				   (debugging-comment "Looking for ad-hoc-string ~S, now at ~S" ad-hoc-string local-char)
				   (when (eq ,char-var +tokenizer-eof+) 
				     (debugging-comment "Saw EOF")
				     (return nil)) ; from dotimes
				   ;; Note: ad-hoc tokens take
				   ;; precedence over open extended
				   ;; comments, so we won't look here
				   ;; to see if a comment is
				   ;; starting.
				   (let ((current-string-index (+ i 1)))
				     (cond ((eq local-char (schar ad-hoc-string current-string-index))
					    (debugging-comment "  extending match."))
					   (t
					    (debugging-comment "  match to ~S failed." ad-hoc-string)
					    ;; put back the char that doesn't match
					    (ps-unread-char local-char ps-stream)
					    ;; put back all but the first char
					    (dotimes (j i)
					      (ps-unread-char (schar ad-hoc-string (- current-string-index 1 j))
							      ps-stream))
					    (return nil))))))))
			  (when found-ad-hoc-string?
			    ;; If an as-hoc-token is found, make sure it is not the start of a longer token
			    (let ((following-char (ps-read-char ps-stream)))
                              (unless (eq following-char +tokenizer-eof+) 
				(let* ((following-char-code (char-code following-char))
				       (dispatch-code (svref word-symbol-table following-char-code)))
				  ;; in all cases (except eof, of course) , put back the following char 
				  (ps-unread-char following-char ps-stream)
				  ;; then see if ad-hoc string should go back...
				  (when (or (eq dispatch-code #.+word-symbol-start-code+)
					    (eq dispatch-code #.+word-symbol-continue-code+))
				    ;; put back all but the first char of the ad-hoc-string
				    (let ((n (1- (length ad-hoc-string))))
				      (dotimes (i n)
					(ps-unread-char (schar ad-hoc-string (- n i))
							ps-stream)))
				    (return nil)))))
			    (debugging-comment "Found match to ~S." ad-hoc-string)
			    ;; char-var was seen via local-read-char, so the current position is already 
			    ;; set  to point at it
			    (set-first-positions) 
			    (dotimes (i (1- (length ad-hoc-string)))
			      (let ((temp-char (schar ad-hoc-string (+ i 1))))
				(incf current-byte)
				(cond ((eq temp-char #\newline)
				       ;; we proceed to line+1 : -1, so that the next character read 
				       ;;  (which will be the leftmost on the line) will be at line+1 : 0
				       ;; current-byte was incremented above, so we don't need to touch that here
				       (incf current-line)
				       (setq current-column -1))
				      (t
				       (incf current-column)))))
			    (return-values :AD-HOC ad-hoc-string)))))))
	       )
      
      (tagbody
	(go start-scan-for-new-token) 
	;; 
	;; ======================================================================
	;;                 WHITESPACE 
	;; ======================================================================
	;; 

       unrecognized-char-while-scanning-whitespace
	(warn-here "Unrecognized ~6S (hex code ~2,'0X) while scanning whitespace -- treated as whitespace"
		   char char-code)
	;;
       start-scan-for-new-token
       continue-whitespace
	;; 
	(local-read-char char char-code
			 (return-values :EOF nil) 
			 () 
			 (go start-extended-comment))
	(look-for-ad-hoc-tokens char char-code)
	;; 
	(case (svref whitespace-table char-code)
	  ;; majority
	  (#.+whitespace-code+               (go continue-whitespace))
	  ;; normal termination
	  (#.+word-symbol-start-code+        (go start-word-symbol))
	  (#.+non-word-symbol-start-code+    (go start-non-word-symbol))
	  (#.+number-start-code+             (go start-number))
	  (#.+string-quote-code+             (go start-string))
	  (#.+separator-code+                (go start-separator))
	  (#.+comment-to-eol-code+           (go start-comment-to-eol))
          (#.+char-literal-start-code+       (go start-char-literal))
 	  ;; peculiar termination  
	  (#.+word-symbol-continue-code+     (go weird-middle-of-word-symbol-after-whitespace))
	  (#.+non-word-symbol-continue-code+ (go weird-middle-of-non-word-symbol-after-whitespace))
	  (#.+number-continue-code+          (go weird-middle-of-number-after-whitespace))
	  (otherwise                         (go unrecognized-char-while-scanning-whitespace)))
	;;   
	;; ========================================
	;; 
       weird-middle-of-word-symbol-after-whitespace
	;; 
	(set-first-positions)
	(warn-here "Ignoring illegal start for word symbol: ~S" char)
	(return-values :ERROR (format nil "~A" char)) 
	;;
	;; ========================================
	;; 
       weird-middle-of-non-word-symbol-after-whitespace
	;; 
	(set-first-positions)
	(warn-here "Ignoring illegal start for non-word symbol: ~S" char)
	(return-values :ERROR (format nil "~A" char))
	;;
	;; ========================================
	;; 
       weird-middle-of-number-after-whitespace
	;; 
	(set-first-positions)
	(warn-here "Ignoring illegal start for number: ~S" char)
	(return-values :ERROR (format nil "~A" char))
	;;
	;; ======================================================================
	;;                 COMMENT TO END OF LINE
	;; ======================================================================
	;; 
       start-comment-to-eol
	(set-first-positions)

       continue-comment-to-eol
	;;
	(push char token-chars)
	(local-read-char char char-code
			 (return-values :COMMENT-TO-EOL
					(coerce (nreverse token-chars) 'string))
			 (return-values :COMMENT-TO-EOL
					(coerce (nreverse token-chars) 'string))
			 ())
	(go continue-comment-to-eol)
	;;
	;; ======================================================================
	;;                 SEPARATOR
	;; ======================================================================
	;; 
       start-separator
	;;
	(set-first-positions)
	;; 
	(return-values :NON-WORD-SYMBOL (svref separator-tokens char-code))
	;;
	;; ======================================================================
	;;                 WORD-SYMBOL
	;; ======================================================================
	;; 
       start-word-symbol
	;;
	(set-first-positions)
	;;
       extend-word-symbol
	;; 
	(push char token-chars)
	(set-last-positions)
	(local-read-char char char-code
			 (go terminate-word-symbol-with-eof)
			 ()
			 (go terminate-word-symbol-with-extended-comment))
	;; 
	;; look for ad hoc symbols that happen to start with word symbol char

	;;
	(case (svref word-symbol-table char-code)
	  ;; majority
	  (#.+word-symbol-continue-code+     (go extend-word-symbol))
	  ;; normal termination
	  (#.+whitespace-code+               (go terminate-word-symbol-with-whitespace))
	  ;; less likely 
	  (#.+non-word-symbol-start-code+    (go terminate-word-symbol-with-start-non-word-symbol))
	  (#.+separator-code+                (go terminate-word-symbol-with-start-separator))
	  (#.+comment-to-eol-code+           (go terminate-word-symbol-with-start-comment-to-eol))
	  ;; unlikely 
	  (#.+word-symbol-start-code+        (go terminate-word-symbol-with-start-word-symbol))
	  (#.+number-start-code+             (go terminate-word-symbol-with-start-number))
	  (#.+string-quote-code+             (go terminate-word-symbol-with-start-string))
          (#.+char-literal-start-code+       (go terminate-word-symbol-with-start-char-literal))
	  ;; weird
	  (#.+non-word-symbol-continue-code+ (go terminate-word-symbol-with-continue-non-word-symbol))
	  (#.+number-continue-code+          (go terminate-word-symbol-with-continue-number)) 
	  (otherwise                         (go unrecognized-char-while-scanning-word-symbol)))

       unrecognized-char-while-scanning-word-symbol
	(when (eq char #\#) ; new hack for # inside URI's...
	  (return-values-using-prior-last :WORD-SYMBOL-TERMINATED-BY-HASH (coerce (nreverse token-chars) 'string)))
	(termination-warning char char-code "word symbol" "" ", which is unrecognized")
	(go terminate-word-symbol)
	;;
       terminate-word-symbol-with-continue-number ; weird
	(termination-warning char char-code "word symbol" "" ", which can continue but not start  a number")
	(return-values-using-prior-last :WORD-SYMBOL (coerce (nreverse token-chars) 'string))
	;;
       terminate-word-symbol-with-continue-non-word-symbol ; weird
	(termination-warning char char-code "word symbol" "" ", which can continue but not start a non-word symbol")
	(go terminate-word-symbol)
	;;
       terminate-word-symbol-with-start-word-symbol
	(termination-warning char char-code "word symbol" "" ", which can start a word symbol but not continue one")
	(go terminate-word-symbol)
	;;
       terminate-word-symbol-with-start-number
	;;(termination-warning char char-code "word symbol" "" "is a beginning of a number")
	(go terminate-word-symbol)
	;;
       terminate-word-symbol-with-start-non-word-symbol
       terminate-word-symbol-with-start-separator
       terminate-word-symbol-with-start-string
       terminate-word-symbol-with-start-char-literal
       terminate-word-symbol-with-start-comment-to-eol
       terminate-word-symbol-with-whitespace
       terminate-word-symbol-with-extended-comment
       terminate-word-symbol
	;;
	;; Last-byte, last-line, last-column all refer to the last character of the symbol we've been scanning.
	;; Char is the first character past that position.  
	;; We put char back into the stream, and tell our caller the last-xxx values.
	;; Those become the initial values in the next call here, and they are 
	;; incremented when the char we're pushing here is then popped.
	(local-unread-char char)
	;;
       terminate-word-symbol-with-eof
	;; 
	(return-values-using-prior-last :WORD-SYMBOL (coerce (nreverse token-chars) 'string))
	;;
	;; ======================================================================
	;; NON-WORD-SYMBOL
	;; ======================================================================
	;; 
       start-non-word-symbol
	;;
	(set-first-positions)
	;;
       extend-non-word-symbol
	;; 
	(push char token-chars)
	(set-last-positions)
	(local-read-char char char-code
			 (go terminate-non-word-symbol-with-eof)
			 ()
			 (go terminate-non-word-symbol-with-extended-comment))
	;; 
	(case (svref non-word-symbol-table char-code)
	  ;; majority
	  (#.+non-word-symbol-continue-code+ (go extend-non-word-symbol))
	  ;; non-word termination
	  (#.+whitespace-code+               (go terminate-non-word-symbol-with-whitespace))
	  ;; less likely 
	  (#.+word-symbol-start-code+        (go terminate-non-word-symbol-with-start-word-symbol))
	  (#.+separator-code+                (go terminate-non-word-symbol-with-start-separator))
	  (#.+comment-to-eol-code+           (go terminate-non-word-symbol-with-start-comment-to-eol))
	  ;; unlikely 
	  (#.+non-word-symbol-start-code+    (go terminate-non-word-symbol-with-start-non-word-symbol))
	  (#.+number-start-code+             (go terminate-non-word-symbol-with-start-number))
	  (#.+string-quote-code+             (go terminate-non-word-symbol-with-start-string))
          (#.+char-literal-start-code+       (go terminate-non-word-symbol-with-start-char-literal))
	  ;; weird
	  (#.+word-symbol-continue-code+     (go terminate-non-word-symbol-with-continue-word-symbol))
	  (#.+number-continue-code+          (go terminate-non-word-symbol-with-continue-number)) 
	  (otherwise                         (go unrecognized-char-while-scanning-non-word-symbol)))

       unrecognized-char-while-scanning-non-word-symbol
	(termination-warning char char-code "non-word symbol" "" ", which is unrecognized")
	(go terminate-non-word-symbol)
	;;
       terminate-non-word-symbol-with-continue-number ; weird
	(termination-warning char char-code "non-word symbol" "" ", which can continue but not start a number")
	(return-values-using-prior-last :NON-WORD-SYMBOL (coerce (nreverse token-chars) 'string))
	;;
       terminate-non-word-symbol-with-continue-word-symbol 
	;;   this may happen in patterns, e.g. (y::_), where :: means a cons pattern, and underbar is a special keyword to match anything
	;;   it also may happen with forms like ::?, where the question mark is dubious, hence:
	(unless (eq char #\_)
	  (termination-warning char char-code "non-word symbol" "" ", which can continue but not start a word symbol"))
	(go terminate-non-word-symbol)
	;;
       terminate-non-word-symbol-with-start-non-word-symbol
	(termination-warning char char-code "non-word symbol" "" ", which can start a non-word symbol but not continue one")
	(go terminate-non-word-symbol)
	;;
       terminate-non-word-symbol-with-start-number
	;;(termination-warning char char-code "non-word symbol" "" ", which is beginning of a number.")
	(go terminate-non-word-symbol)
	;;
       terminate-non-word-symbol-with-start-word-symbol
       terminate-non-word-symbol-with-start-separator
       terminate-non-word-symbol-with-start-string
       terminate-non-word-symbol-with-start-char-literal
       terminate-non-word-symbol-with-start-comment-to-eol
       terminate-non-word-symbol-with-whitespace
       terminate-non-word-symbol-with-extended-comment
       terminate-non-word-symbol
	;;
	;; Last-byte, last-line, last-column all refer to the last character of the symbol we've been scanning.
	;; Char is the first character past that position.  
	;; We put char back into the stream, and tell our caller the last-xxx values.
	;; Those become the initial values in the next call here, and they are 
	;; incremented when the char we're pushing here is then popped.
	(local-unread-char char)
	;;
       terminate-non-word-symbol-with-eof
	;; 
	(return-values-using-prior-last :NON-WORD-SYMBOL (coerce (nreverse token-chars) 'string))
	;;
	;; ======================================================================
	;;                 CHARACTER
	;; ======================================================================
	;; 
	;; Note: #\abcde => two tokens: (:CHARACTER #\a) (:SYMBOL "bcde")
	;;
       start-char-literal
	(set-first-positions)
	(set-last-positions)
	(local-read-char 
	 char char-code
       	 (termination-warning char char-code "partial character literal" "#" ", which is eof")
       	 (termination-warning char char-code "partial character literal" "#" "")
       	 (termination-warning char char-code "partial character literal" "#" ", which starts an extended comment")
	 )
	(set-last-positions)
	(cond ((eq char #\\)
	       (local-read-char 
		char char-code
		(termination-warning char char-code "partial non-word character literal" "#\\" ", which is eof")
		(termination-warning char char-code "partial non-word character literal" "#\\" "")
		(termination-warning char char-code "partial non-word character literal" "#\\" ", which starts an extended comment")
		)
	       (case char
		 (#\a (return-values :CHARACTER #\bel       ))
		 (#\b (return-values :CHARACTER #\backspace ))
		 (#\t (return-values :CHARACTER #\tab       ))
		 (#\n (return-values :CHARACTER #\newline   ))
		 (#\v (return-values :CHARACTER #\vt        ))
		 (#\f (return-values :CHARACTER #\page      ))
		 (#\r (return-values :CHARACTER #\return    ))
		 (#\s (return-values :CHARACTER #\space     ))
		 (#\\ (return-values :CHARACTER #\\         ))
		 (#\" (return-values :CHARACTER #\"         ))
		 (#\x (progn
			(set-last-positions)
			(local-read-char 
			 hex-char-1 hex-char-code-1
                	 (termination-warning hex-char-1 hex-char-code-1 "partial hex character literal" "#\\x" ", which is eof")
			 (termination-warning hex-char-1 hex-char-code-1 "partial hex character literal" "#\\x" "")
			 (termination-warning hex-char-1 hex-char-code-1 "partial hex character literal" "#\\x" ", which starts an extended comment")
			 )
			(set-last-positions)
			(local-read-char 
			 hex-char-2 hex-char-code-2
                	 (termination-warning hex-char-2 hex-char-code-2 "partial hex character literal" (format nil "#\\x~A" hex-char-1) ", which is eof")
			 (termination-warning hex-char-2 hex-char-code-2 "partial hex character literal" (format nil "#\\x~A" hex-char-1) "")
			 (termination-warning hex-char-2 hex-char-code-2 "partial hex character literal" (format nil "#\\x~A" hex-char-1) ", which starts an extended comment")
			 )
			(let ((high-nibble (convert-hex-char-to-number hex-char-1))
			      (low-nibble  (convert-hex-char-to-number hex-char-2)))
			  (when (or (null high-nibble) (null low-nibble))
			    (let ((token (format nil "#x\\~A~A" hex-char-1 hex-char-2)))
			      (warn-here "Unrecognized character literal, chars after \"#\\x\" are ~S ~S, with hex codes ~2,'0X ~2,'0X"
					 ;; token
					 hex-char-1
					 hex-char-2
					 hex-char-code-1
					 hex-char-code-2)
			      (return-values :ERROR token)))
			  (return-values :CHARACTER (code-char (+ (ash high-nibble 4) low-nibble))))))
		 (otherwise
		  (let ((token (format nil "#\\~A" char)))
		    (warn-here "Unrecognized character literal, char after \"#\\\" is ~S with hex code ~2,'0X" 
			       ;; token 
			       char
			       char-code)
		    (return-values :ERROR token)))))
	      (t
	       (return-values-using-prior-last :CHARACTER char)))

	;; ======================================================================
	;;                 NUMBER
	;; ======================================================================
	;; 
       start-number
	;;
	(set-first-positions)
	;;
       extend-number
	;; 
	(push char token-chars)
	(set-last-positions)
	(local-read-char char char-code
			 (go terminate-number-with-eof)
			 ()
			 (go terminate-number-with-extended-comment))
	;; 
	(case (svref number-table char-code)
	  ;; majority
	  (#.+number-continue-code+          (go extend-number))
	  ;; normal termination
	  (#.+whitespace-code+               (go terminate-number-with-whitespace))
	  ;; e.g.  123ABC 
	  (#.+word-symbol-start-code+        (go terminate-number-with-start-word-symbol))
	  (#.+word-symbol-continue-code+     (go terminate-number-with-continue-word-symbol))
	  ;; e.g.  123ABC 
	  (#.+non-word-symbol-start-code+    (go terminate-number-with-start-non-word-symbol))
	  (#.+non-word-symbol-continue-code+ (go terminate-number-with-continue-non-word-symbol))
	  ;; less likely
	  (#.+separator-code+                (go terminate-number-with-start-separator))
	  (#.+comment-to-eol-code+           (go terminate-number-with-start-comment-to-eol))
	  ;; unlikely
	  (#.+number-start-code+             (go terminate-number-with-start-number))
	  (#.+string-quote-code+             (go terminate-number-with-start-string))
          (#.+char-literal-start-code+       (go terminate-number-with-start-char-literal))
	  ;;
	  (otherwise                         (go unrecognized-char-while-scanning-number)))
	;;
       unrecognized-char-while-scanning-number
	(termination-warning char char-code "number" "" ", which is unrecognized")
	(go terminate-number)
	;;
       terminate-number-with-start-word-symbol
       (termination-warning char char-code "number" "" ", which starts a word symbol")
       (go terminate-number)
	;;
       terminate-number-with-continue-word-symbol 
       ;;(termination-warning char char-code "number" "" ", which continues but does not start a word symbol")
       (go terminate-number)
	;;
       terminate-number-with-continue-non-word-symbol 
       ;;(termination-warning char char-code "number" "" ", which continues but does not start a non-word symbol")
       (go terminate-number)
	;;
       terminate-number-with-start-number
	(termination-warning char char-code "number" "" ", which starts a new number")
	(go terminate-number)
 
       terminate-number-with-start-non-word-symbol ;; e.g. +, -, =, etc.
       terminate-number-with-start-separator
       terminate-number-with-start-string
       terminate-number-with-start-char-literal
       terminate-number-with-start-comment-to-eol
       terminate-number-with-whitespace
       terminate-number-with-extended-comment
	;;
	;; Last-byte, last-line, last-column all refer to the last character of the number we've been scanning.
	;; Char is the first character past that position.  
	;; We put char back into the stream, and tell our caller the last-xxx values.
	;; Those become the initial values in the next call here, and they are 
	;; incremented when the char we're pushing here is then popped.
	(local-unread-char char)
	;;
       terminate-number-with-eof

       terminate-number
	;; 
	(return-values-using-prior-last :NUMBER (parse-integer (coerce (nreverse token-chars) 'string)))
	;;
	;; ======================================================================
	;;                 STRING
	;; ======================================================================
	;; 
       escape-next-char-in-string
	;; 
	(local-read-char 
	 char char-code
	 (let ((token (format nil "~A\\" (coerce (nreverse token-chars) 'string))))
	   (warn-here "EOF immediately after escape character in string ~S" token)
	   (return-values :ERROR token))
	 ()
	 ())
        (case char
	  (#\a (push #\bel       token-chars)) 
	  (#\b (push #\backspace token-chars)) 
	  (#\t (push #\tab       token-chars)) 
	  (#\n (push #\newline   token-chars)) 
	  (#\v (push #\vt        token-chars)) 
	  (#\f (push #\page      token-chars)) 
	  (#\r (push #\return    token-chars)) 
	  (#\s (push #\space     token-chars)) 
	  (#\\ (push #\\         token-chars)) 
	  (#\" (push #\"         token-chars)) 
	  (#\x (progn
		 (set-last-positions)
		 (local-read-char 
		  hex-char-1 hex-char-code-1
		  (termination-warning hex-char-1 hex-char-code-1 "partial hex character lliteral" "#\\x" ", which is eof")
		  (termination-warning hex-char-1 hex-char-code-1 "partial hex character lliteral" "#\\x" "")
		  (termination-warning hex-char-1 hex-char-code-1 "partial hex character lliteral" "#\\x" ", which starts of an extended comment")
		  )
		 (set-last-positions)
		 (local-read-char 
		  hex-char-2 hex-char-code-2
		  (termination-warning hex-char-2 hex-char-code-2 "partial hex character lliteral" (format nil "#\\x~A" hex-char-1) ", which is eof")
		  (termination-warning hex-char-2 hex-char-code-2 "partial hex character lliteral" (format nil "#\\x~A" hex-char-1) "")
		  (termination-warning hex-char-2 hex-char-code-2 "partial hex character lliteral" (format nil "#\\x~A" hex-char-1) ", which starts an extended comment")
		  )
		 (let ((high-nibble (convert-hex-char-to-number hex-char-1))
		       (low-nibble  (convert-hex-char-to-number hex-char-2)))
		   (when (or (null high-nibble) (null low-nibble))
		     (let ((token (format nil "#\\x~A~A" hex-char-1 hex-char-2)))
		       (warn-here "Unrecognized character literal, chars after \"#\\x\" are ~S ~S, with hex codes ~2,'0X ~2,'0X"
				  ;; token
				  hex-char-1
				  hex-char-2
				  hex-char-code-1
				  hex-char-code-2)
		       (return-values :ERROR token)))
		   (push (code-char (+ (ash high-nibble 4) low-nibble)) token-chars))))
	  (otherwise
	   (let ((token (format nil "#\\~A" char)))
	     (warn-here "Unrecognized character literal, char after \"#\\\" is ~S, with hex code ~2,'0X" 
			;; token
			char
			char-code)
	     (return-values :ERROR token))))
	(go extend-string)
	;; 
       start-string
	;;
	(set-first-positions)
	;; 
       extend-string
	;; 
	(local-read-char
	 char char-code
	 (let ((token (coerce (nreverse token-chars) 'string)))
	   (warn-here "EOF inside string starting at line ~S, column ~S" first-line first-column)
	   (return-values :ERROR token))
	 ()
	 ())
	(case (svref string-table char-code)
	  (#.+string-quote-code+  (go close-string))
	  (#.+string-escape-code+ (go escape-next-char-in-string))
	  (otherwise              (push char token-chars) (go extend-string)))
	;;
       close-string
	;; 
	(return-values :STRING (coerce (nreverse token-chars) 'string))
	;; 
	;; ======================================================================
	;;                 EXTENDED COMMENT
	;; ======================================================================
	;;
       start-extended-comment
	;;
	(set-first-positions)
	;;
	(multiple-value-bind (error? comment-chars last-byte last-line last-column)
	    (skip-extended-comment char ps-stream this-ec-quad 
				   extended-comment-quads
				   comment-table
				   first-byte
				   first-line
				   first-column)
	  (return-values-using-prior-last (if error? :EXTENDED-COMMENT-ERROR :EXTENDED-COMMENT)
					  (coerce (nreverse comment-chars) 'string)))
	;;
	;; ========================================
	))))

(defun convert-hex-char-to-number (x)
  (case x
    (#\0        0)
    (#\1        1)
    (#\2        2)
    (#\3        3)
    (#\4        4)
    (#\5        5)
    (#\6        6)
    (#\7        7)
    (#\8        8)
    (#\9        9)
    ((#\a #\A) 10)
    ((#\b #\B) 11)
    ((#\c #\C) 12)
    ((#\d #\D) 13)
    ((#\e #\E) 14)
    ((#\f #\F) 15)
    (otherwise nil)))

(defun applicable-extended-comment-quad (first-char ps-stream extended-comment-quads)
  (dolist (quad extended-comment-quads)
    (when (pseudo-stream-has-prefix? first-char ps-stream (first quad))
      (return quad))))

(defun pseudo-stream-has-prefix? (first-char ps-stream open-comment-string)
  (and (eq (schar open-comment-string 0) first-char)
       (let* ((lookahead-chars nil)
	      (result
	       (dotimes (i (1- (length open-comment-string)) 
			  ;; if all chars match, the result is t
			  t)
		 (let ((char (ps-read-char ps-stream)))
		   (cond ((eq char +tokenizer-eof+)
			  ;; if eof intervenes, the result is nil
			  (return nil))
			 ((eq char (schar open-comment-string (1+ i)))
			  (push char lookahead-chars))
			 (t
			  ;; if some char is a mismatch, the result is nil
			  (ps-unread-char char ps-stream)
			  (return nil)))))))
	 ;; back out so stream is in original state
	 (dolist (char lookahead-chars)
	   (ps-unread-char char ps-stream))
	 result)))


(defstruct extended-comment-state
  error?
  all-quads
  comment-table
  byte
  line
  column
  chars)
  
(defvar *extended-comment-state* (make-extended-comment-state))

(defun skip-extended-comment (first-char ps-stream this-quad all-quads
					 comment-table
					 first-byte first-line first-column)
  (let ((ec-state *extended-comment-state*)) 
    (setf (extended-comment-state-error?        ec-state) nil)
    (setf (extended-comment-state-all-quads     ec-state) all-quads)
    (setf (extended-comment-state-comment-table ec-state) comment-table)
    (setf (extended-comment-state-byte          ec-state) first-byte)
    (setf (extended-comment-state-line          ec-state) first-line)
    (setf (extended-comment-state-column        ec-state) first-column)
    (setf (extended-comment-state-chars         ec-state) (list first-char))
    (aux-skip-extended-comment ps-stream this-quad ec-state)
    (values (extended-comment-state-error? ec-state) 
	    (extended-comment-state-chars  ec-state) 
	    (extended-comment-state-byte   ec-state)
	    (extended-comment-state-line   ec-state)
	    (extended-comment-state-column ec-state))))

(defun aux-skip-extended-comment (ps-stream this-quad ec-state)
  (let* ((open-comment  (first  this-quad))
	 (close-comment (second this-quad))
	 (recursive?    (third  this-quad))
	 (eof-ok?       (fourth this-quad))
	 (open-size  (1- (length open-comment)))
	 (close-size (1- (length close-comment)))
	 (close-char-0 (schar close-comment 0))
	 (comment-table (extended-comment-state-comment-table ec-state)))
    ;; skip past open-comment
    (dotimes (i open-size) 
      (push (ps-read-char ps-stream)
	    (extended-comment-state-chars ec-state)))
    (incf (extended-comment-state-byte   ec-state) open-size)
    (incf (extended-comment-state-column ec-state) open-size)
    ;; scan for close-comment or recursive open-comment
    (do ((char (ps-read-char ps-stream) (ps-read-char ps-stream)))
	((eq char +tokenizer-eof+)
	 (cond (eof-ok?
		nil)
	       (t
		(setf (extended-comment-state-error? ec-state) t)
		t)))
      (push char (extended-comment-state-chars ec-state))
      (incf (extended-comment-state-byte   ec-state))
      (cond ((eq char #\newline)
	     (incf (extended-comment-state-line   ec-state))
	     (setf (extended-comment-state-column ec-state) 1))
	    (t
	     (incf (extended-comment-state-column ec-state))))
      (cond ((and (eq char close-char-0)
		  (pseudo-stream-has-prefix? char ps-stream close-comment))
	     ;; skip past close-comment
	     (dotimes (i close-size) 
	       (push (ps-read-char ps-stream) 
		     (extended-comment-state-chars ec-state)))
	     (incf (extended-comment-state-byte   ec-state) close-size)
	     (incf (extended-comment-state-column ec-state) close-size)
	     (return-from aux-skip-extended-comment nil))
	    ((and recursive?
		  (eq (svref comment-table (char-code char)) 
		      +maybe-open-comment-code+))
	     (let ((new-quad (applicable-extended-comment-quad 
				char ps-stream 
				(extended-comment-state-all-quads ec-state))))
	       (when (not (null new-quad))
		 (aux-skip-extended-comment ps-stream new-quad ec-state))))))))

;;; ========================================================================

(defun install-tokens (session tokens comments)
  (when (null +token-rule+) (break "???"))
  (let ((locations (make-array (1+ (length tokens))))
	(pre-index 0)
	(pre-location (make-parser-location
		       :index      0
		       :post-nodes nil))
	(last-node nil))
    (setf (svref locations pre-index) pre-location)
    (setf (parse-session-locations session) locations)
    (setf (parse-session-comments  session) comments)
    (dolist (token tokens)
      (let* ((token-start-byte (first (third token)))
	     (pre-comments  '())
	     (post-index (1+ pre-index))
	     (node (create-parser-node :rule           +token-rule+
				       :semantics      token
				       :pre-index      pre-index
				       :post-index-ptr (list post-index)
				       :parents        nil
				       :children       nil
				       )))
	(setq last-node node)
	(push node (parser-location-post-nodes pre-location))
	(when-debugging (when *verbose?* (show-node node "Created  ")))
	(setf (parser-location-position pre-location) (third token))

	;; (third comment) is pre-position of comment: (byte line column)
	(loop while (and (not (null comments))
			 (< (first (third (first comments))) 
			    token-start-byte) )
	  do (push (pop comments) pre-comments))
	(setf (parser-location-pre-comments pre-location) pre-comments)
	(when-debugging 
	 (when *verbose?*
	   (unless (null pre-comments) 
	     (comment "Pre-Comemnts for ~6D: ~S" pre-index pre-comments))))
	(setq pre-index    post-index)
	(setq pre-location (make-parser-location
			    :index          post-index
			    :post-nodes     nil))
	(setf (svref locations pre-index) pre-location)))
    (debugging-comment "Pre-Comments for ~6D (eof): ~S" pre-index comments)
    (let ((eof-location pre-location))
      (setf (parser-location-pre-comments eof-location) comments)
      (let* ((last-token (if (null comments)
			     (parser-node-semantics last-node)
			   (first (last comments))))
	     (last-pos   (fourth last-token)))
	(debugging-comment "Last token: ~S" last-token)
	(setf (parser-location-position eof-location) last-pos)))
    locations))

