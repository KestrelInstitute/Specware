;;;; -*- mode: lisp -*-
;;;;
;;;; $Id$
;;;;
;;;; This is a Common Lisp implementation of a very basic XML parser.
;;;; The parser is non-validating and not at all complete (no CDATA).
;;;; The API into the parser is a pure functional parser hook model that comes from SSAX,
;;;; see also http://pobox.com/~oleg/ftp/Scheme/xml.html or http://ssax.sourceforge.net
;;;; Different DOM models are provided, an XSML, an LXML and a xml-element struct based one.
;;;;
;;;; Copyright (C) 2002, 2004 Sven Van Caekenberghe, Beta Nine BVBA.
;;;;
;;;; You are granted the rights to distribute and use this software
;;;; as governed by the terms of the Lisp Lesser General Public License
;;;; (http://opensource.franz.com/preamble.html), also known as the LLGPL.

(in-package :s-xml)

;;; error reporting

(define-condition xml-parser-error (error)
  ((message :initarg :message :reader xml-parser-error-message)
   (args :initarg :args :reader xml-parser-error-args)
   (stream :initarg :stream :reader xml-parser-error-stream :initform nil))
  (:report (lambda (condition stream)
	     (format stream
		     "XML parser ~?~@[ near stream position ~d~]."
		     (xml-parser-error-message condition)
		     (xml-parser-error-args condition)
		     (and (xml-parser-error-stream condition)
			  (file-position (xml-parser-error-stream condition))))))
  (:documentation "Thrown by the XML parser to indicate errorneous input"))

(setf (documentation 'xml-parser-error-message 'function)
      "Get the message from an XML parser error"
      (documentation 'xml-parser-error-args 'function)
      "Get the error arguments from an XML parser error"
      (documentation 'xml-parser-error-stream 'function)
      "Get the stream from an XML parser error")

(defun parser-error (message &optional args stream)
  (make-condition 'xml-parser-error
		  :message message
		  :args args
		  :stream stream))
   
;;; utilities

(defun whitespace-char-p (char)
  "Is char an XML whitespace character ?"
  (or (char= char #\space)
      (char= char #\tab)
      (char= char #\return)
      (char= char #\linefeed)))

(defun identifier-char-p (char)
  "Is char an XML identifier character ?"
  (or (and (char<= #\A char) (char<= char #\Z))
      (and (char<= #\a char) (char<= char #\z))
      (and (char<= #\0 char) (char<= char #\9))
      (char= char #\-)
      (char= char #\_)
      (char= char #\.)
      (char= char #\:)))

(defun skip-whitespace (stream)
  "Skip over XML whitespace in stream, return first non-whitespace
  character which was peeked but not read, return nil on eof"
  (loop
   (let ((char (peek-char nil stream nil nil)))
     (if (and char (whitespace-char-p char))
	 (read-char stream)
       (return char)))))

(defun make-extendable-string (&optional (size 10))
  "Make an extendable string which is a one-dimensional character
  array which is adjustable and has a fill pointer"
  (make-array size
	      :element-type 'character
	      :adjustable t
	      :fill-pointer 0))

(defun print-string-xml (string stream &key (start 0) end)
  "Write the characters of string to stream using basic XML conventions"
  (loop for offset upfrom start below (or end (length string))
        for char = (char string offset)
	do (case char
	     (#\& (write-string "&amp;" stream))
	     (#\< (write-string "&lt;" stream))
	     (#\> (write-string "&gt;" stream))
	     (#\" (write-string "&quot;" stream))
             ((#\newline #\return #\tab) (write-char char stream))
	     (t (if (and (<= 32 (char-code char))
			 (<= (char-code char) 126))
		    (write-char char stream)
		  (progn
		    (write-string "&#x" stream)
		    (write (char-code char) :stream stream :base 16)
		    (write-char #\; stream)))))))

(defun make-standard-entities ()
  "A hashtable mapping XML entity names to their replacement strings,
  filled with the standard set"
  (let ((entities (make-hash-table :test #'equal)))
    (setf (gethash "amp" entities) (string #\&)
	  (gethash "quot" entities) (string #\")
	  (gethash "apos" entities) (string #\')
	  (gethash "lt" entities) (string #\<)
	  (gethash "gt" entities) (string #\>)
	  (gethash "nbsp" entities) (string #\space))
    entities))

(defun resolve-entity (stream extendable-string entities &optional (entity (make-extendable-string)))
  "Read and resolve an XML entity from stream, positioned on the '&'
  entity marker, accepting &name; , &DEC; and &#HEX; formats,
  destructively modifying string, which is also returned,
  destructively modifying entity, incorrect entity formats result in
  errors"
  (loop
   (let ((char (read-char stream nil nil)))
     (cond ((null char) (error (parser-error "encountered eof before end of entity")))
	   ((char= #\; char) (return))
	   (t (vector-push-extend char entity)))))
  (if (char= (char entity 0) #\#)
      (let ((code (if (char= (char entity 1) #\x)
		      (parse-integer entity :start 2 :radix 16)
		    (parse-integer entity :start 1 :radix 10))))
	(if (null code) (error (parser-error "encountered incorrect entity &~s;" (list entity) stream)))
	(vector-push-extend (code-char code) extendable-string))
    (let ((value (gethash entity entities)))
      (if value
	  (dotimes (i (length value))
	    (vector-push-extend (char value i) extendable-string))
	(error (parser-error "encountered unknown entity &~s;" (list entity) stream)))))
  extendable-string)

;;; the parser state

(defclass xml-parser-state ()
  ((entities :documentation "A hashtable mapping XML entity names to their replacement stings"
	     :accessor get-entities
	     :initarg :entities
	     :initform (make-standard-entities))
   (seed :documentation "The user seed object"
	 :accessor get-seed
	 :initarg :seed
	 :initform nil)
   (buffer :documentation "The main reusable character buffer"
	   :accessor get-buffer
	   :initform (make-extendable-string))
   (mini-buffer :documentation "The secondary, smaller reusable character buffer"
		:accessor get-mini-buffer
		:initform (make-extendable-string))
   (new-element-hook :documentation "Called when new element starts"
		     ;; Handle the start of a new xml element with name and attributes,
		     ;; receiving seed from previous element (sibling or parent)
		     ;; return seed to be used for first child (content) 
                     ;; or directly to finish-element-hook
		     :accessor get-new-element-hook
		     :initarg :new-element-hook
		     :initform #'(lambda (name attributes seed)
				   (declare (ignore name attributes))
                                   seed))
   (finish-element-hook :documentation "Called when element ends"
			;; Handle the end of an xml element with name and attributes,
			;; receiving parent-seed, the seed passed to us when this element started,
                        ;; i.e. passed to our corresponding new-element-hook
			;; and receiving seed from last child (content) 
                        ;; or directly from new-element-hook
			;; return final seed for this element to next element (sibling or parent)
			:accessor get-finish-element-hook
			:initarg :finish-element-hook
			:initform #'(lambda (name attributes parent-seed seed)
				      (declare (ignore name attributes parent-seed))
                                      seed))
   (text-hook :documentation "Called when text is found"
	      ;; Handle text in string, found as contents,
	      ;; receiving seed from previous element (sibling or parent), 
              ;; return final seed for this element to next element (sibling or parent)
	      :accessor get-text-hook
	      :initarg :text-hook
	      :initform #'(lambda (string seed)
			    (declare (ignore string))
                            seed)))
  (:documentation "The XML parser state passed along all code making up the parser"))

(setf (documentation 'get-seed 'function)
      "Get the initial user seed of an XML parser state"
      (documentation 'get-entities 'function)
      "Get the entities hashtable of an XML parser state"
      (documentation 'get-new-element-hook 'function)
      "Get the new element hook of an XML parser state"
      (documentation 'get-finish-element-hook 'function)
      "Get the finish element hook of an XML parser state"
      (documentation 'get-text-hook 'function)
      "Get the text hook of an XML parser state")

#-allegro
(setf (documentation '(setf get-seed) 'function)
      "Set the initial user seed of an XML parser state"
      (documentation '(setf get-entities) 'function)
      "Set the entities hashtable of an XML parser state"
      (documentation '(setf get-new-element-hook) 'function)
      "Set the new element hook of an XML parser state"
      (documentation '(setf get-finish-element-hook) 'function)
      "Set the finish element hook of an XML parser state"
      (documentation '(setf get-text-hook) 'function)
      "Set the text hook of an XML parser state")

(defmethod get-mini-buffer :after ((state xml-parser-state))
  "Reset and return the reusable mini buffer"
  (with-slots (mini-buffer) state
    (setf (fill-pointer mini-buffer) 0)))

(defmethod get-buffer :after ((state xml-parser-state))
  "Reset and return the main reusable buffer"
  (with-slots (buffer) state
    (setf (fill-pointer buffer) 0)))
  
;;; parser support

(defun parse-whitespace (stream extendable-string)
  "Read and collect XML whitespace from stream in string which is
  destructively modified, return first non-whitespace character which
  was peeked but not read, return nil on eof"
  (loop
   (let ((char (peek-char nil stream nil nil)))
     (if (and char (whitespace-char-p char))
	 (vector-push-extend (read-char stream) extendable-string)
       (return char)))))

(defun parse-string (stream state &optional (string (make-extendable-string)))
  "Read and return an XML string from stream, delimited by either
  single or double quotes, the stream is expected to be on the opening
  delimiter, at the end the closing delimiter is also read, entities
  are resolved, eof before end of string is an error"
  (let ((delimiter (read-char stream nil nil))
	(char))
    (when (or (null delimiter) (not (or (char= delimiter #\') (char= delimiter #\"))))
      (error (parser-error "expected string delimiter" nil stream)))
    (loop
     (setf char (read-char stream nil nil))
     (cond ((null char) (error (parser-error "encountered eof before end of string")))
	   ((char= char delimiter) (return))
	   ((char= char #\&) (resolve-entity stream string (get-entities state) (get-mini-buffer state)))
	   (t (vector-push-extend char string))))
    string))

(defun parse-text (stream state extendable-string)
  "Read and collect XML text from stream in string which is
  destructively modified, the text ends with a '<', which is peeked and
  returned, entities are resolved, eof is considered an error"
  (let (char)
    (loop
     (setf char (peek-char nil stream nil nil))
     (when (null char) (error (parser-error "encountered unexpected eof in text")))
     (when (char= char #\<) (return))
     (read-char stream)
     (if (char= char #\&)
	 (resolve-entity stream extendable-string (get-entities state) (get-mini-buffer state))
       (vector-push-extend char extendable-string)))
    char))

(defun parse-identifier (stream &optional (identifier (make-extendable-string)))
  "Read and returns an XML identifier from stream, positioned at the
  start of the identifier, ending with the first non-identifier
  character, which is peeked, the identifier is written destructively
  into identifier which is also returned"
  (loop
   (let ((char (peek-char nil stream nil nil)))
     (cond ((and char (identifier-char-p char))
	    (read-char stream)
	    (vector-push-extend char identifier))
	   (t
	    (return identifier))))))
	 
(defun skip-comment (stream)
  "Skip an XML comment in stream, positioned after the opening '<!--',
  consumes the closing '-->' sequence, unexpected eof or a malformed
  closing sequence result in a error"
  (let ((dashes-to-read 2))
    (loop
     (if (zerop dashes-to-read) (return))
     (let ((char (read-char stream nil nil)))
       (if (null char)
	   (error (parser-error "encountered unexpected eof for comment")))
       (if (char= char #\-)
	   (decf dashes-to-read)
	 (setf dashes-to-read 2)))))
  (if (char/= (read-char stream nil nil) #\>)
      (error (parser-error "expected > ending comment" nil stream))))

(defun skip-special-tag (stream)
  "Skip an XML special tag (comments and processing instructions) in
  stream, positioned after the opening '<', unexpected eof is an error"
  ;; opening < has been read, consume ? or !
  (read-char stream)
  (let ((char (read-char stream nil nil)))
    ;; see if we are dealing with a comment
    (when (char= char #\-)
      (setf char (read-char stream nil nil))
      (when (char= char #\-)
	(skip-comment stream)
	(return-from skip-special-tag)))
    ;; loop over chars, dealing with strings (skipping their content)
    ;; and counting opening and closing < and > chars
    (let ((taglevel 1)
	  (string-delimiter))
      (loop
       (when (zerop taglevel) (return))
       (setf char (read-char stream nil nil))
       (when (null char)
	 (error (parser-error "encountered unexpected eof for special (! or ?) tag" nil stream)))
       (if string-delimiter
	   ;; inside a string we only look for a closing string delimiter
	   (when (char= char string-delimiter)
	     (setf string-delimiter nil))
	 ;; outside a string we count < and > and watch out for strings
	 (cond ((or (char= char #\') (char= char #\")) (setf string-delimiter char))
	       ((char= char #\<) (incf taglevel))
	       ((char= char #\>) (decf taglevel))))))))
	
;;; the XML parser proper

(defun parse-xml-element-attributes (stream state)
  "Parse XML element attributes from stream positioned after the tag
  identifier, returning the attributes as an assoc list, ending at
  either a '>' or a '/' which is peeked and also returned"
  (let (char attributes)
    (loop
     ;; skip whitespace separating items
     (setf char (skip-whitespace stream))
     ;; start tag attributes ends with > or />
     (when (and char (or (char= char #\>) (char= char #\/))) (return))
     ;; read the attribute key
     (let ((key (intern (parse-identifier stream (get-mini-buffer state)) :keyword)))
       ;; skip separating whitespace
       (setf char (skip-whitespace stream))
       ;; require = sign (and consume it if present)
       (if (and char (char= char #\=))
	   (read-char stream)
	 (error (parser-error "expected =" nil stream)))
       ;; skip separating whitespace
       (skip-whitespace stream)
       ;; read the attribute value as a string
       (push (cons key (copy-seq (parse-string stream state (get-buffer state))))
	     attributes)))
    ;; return attributes peek char ending loop
    (values attributes char)))

(defun parse-xml-element (stream state)
  "Parse and return an XML element from stream, positioned after the opening '<'"
  ;; opening < has been read
  (when (char= (peek-char nil stream nil nil) #\!)
    (skip-special-tag stream)
    (return-from parse-xml-element))
  (let (char buffer open-tag parent-seed has-children)
    (setf parent-seed (get-seed state))
    ;; read tag name (no whitespace between < and name ?)
    (setf open-tag (intern (parse-identifier stream (get-mini-buffer state)) :keyword))
    ;; tag has been read, read attributes if any
    (multiple-value-bind (attributes peeked-char)
	(parse-xml-element-attributes stream state)
      (setf (get-seed state) (funcall (get-new-element-hook state)
				      open-tag attributes (get-seed state)))
      (setf char peeked-char)
      (when (char= char #\/)
	;; handle solitary tag of the form <tag .. />
	(read-char stream)
	(setf char (read-char stream nil nil))
	(if (char= #\> char)
	    (progn
	      (setf (get-seed state) (funcall (get-finish-element-hook state)
					      open-tag attributes parent-seed (get-seed state)))
	      (return-from parse-xml-element))
	  (error (parser-error "expected >" nil stream))))
      ;; consume >
      (read-char stream)
      (loop
       (setf buffer (get-buffer state))
       ;; read whitespace into buffer
       (setf char (parse-whitespace stream buffer))
       ;; see what ended the whitespace scan
       (cond ((null char) (error (parser-error "encountered unexpected eof handling ~a" (list open-tag))))
	     ((char= char #\<)
	      ;; consume the <
	      (read-char stream)
	      (if (char= (peek-char nil stream nil nil) #\/)
		  (progn
		    ;; handle the matching closing tag </tag> and done
                    ;; if we read whitespace as this (leaf) element's contents, it is significant
                    (when (and (not has-children) (plusp (length buffer)))
                      (setf (get-seed state) (funcall (get-text-hook state)
                                                      (copy-seq buffer) (get-seed state))))
		    (read-char stream)
		    (let ((close-tag (intern (parse-identifier stream (get-mini-buffer state)) :keyword)))
		      (unless (eq open-tag close-tag)
			(error (parser-error "found <~a> not matched by </~a> but by <~a>"
					     (list open-tag open-tag close-tag) stream)))
		      (unless (char= (read-char stream nil nil) #\>)
			(error (parser-error "expected >" nil stream)))
		      (setf (get-seed state) (funcall (get-finish-element-hook state)
						      open-tag attributes parent-seed (get-seed state))))
		    (return))
		;; handle child tag and loop, no hooks to call here
                ;; whitespace between child elements is skipped
                (progn
                  (setf has-children t)
                  (parse-xml-element stream state))))
	     (t
	      ;; no child tag, concatenate text to whitespace in buffer
	      ;; handle text content and loop
	      (setf char (parse-text stream state buffer))
	      (setf (get-seed state) (funcall (get-text-hook state)
					      (copy-seq buffer) (get-seed state)))))))))

(defun start-parse-xml (stream &optional (state (make-instance 'xml-parser-state)))
  "Parse and return a toplevel XML element from stream, using parser state"
  (loop
   (let ((char (skip-whitespace stream)))
     (when (null char) (return-from start-parse-xml))
     ;; skip whitespace until start tag
     (unless (char= char #\<)
       (error (parser-error "expected <" nil stream)))
     (read-char stream)			; consume peeked char
     (setf char (peek-char nil stream nil nil))
     (if (or (char= char #\!) (char= char #\?))
	 ;; deal with special tags
	 (skip-special-tag stream)
       (progn
	 ;; read the main element
	 (parse-xml-element stream state)
	 (return-from start-parse-xml (get-seed state)))))))

;;; A simple example as well as a useful tool: parse, echo and pretty print XML

(defun indent (stream count)
  (loop :repeat (* count 2) :do (write-char #\space stream)))

(defclass echo-xml-seed ()
  ((stream :initarg :stream)
   (level :initarg :level :initform 0)))

#+NIL
(defmethod print-object ((seed echo-xml-seed) stream)
  (with-slots (stream level) seed
    (print-unreadable-object (seed stream :type t)
      (format stream "level=~d" level))))

(defun echo-xml-new-element-hook (name attributes seed)
  (with-slots (stream level) seed
    (indent stream level)
    (format stream "<~a" name)
    (dolist (attribute (reverse attributes)) 
      (format stream " ~a=\'" (car attribute))
      (print-string-xml (cdr attribute) stream)
      (write-char #\' stream))
    (format stream ">~%")
    (incf level)
    seed))

(defun echo-xml-finish-element-hook (name attributes parent-seed seed)
  (declare (ignore attributes parent-seed))
  (with-slots (stream level) seed 
    (decf level)
    (indent stream level)
    (format stream "</~a>~%" name)
    seed))

(defun echo-xml-text-hook (string seed)
  (with-slots (stream level) seed
    (indent stream level)
    (print-string-xml string stream)
    (terpri stream)
    seed))
  
(defun echo-xml (in out)
  "Parse a toplevel XML element from stream in, echoing and pretty printing the result to stream out"
  (start-parse-xml in
		   (make-instance 'xml-parser-state
				  :seed (make-instance 'echo-xml-seed :stream out)
				  :new-element-hook #'echo-xml-new-element-hook
				  :finish-element-hook #'echo-xml-finish-element-hook
				  :text-hook #'echo-xml-text-hook)))

;;;; eof
