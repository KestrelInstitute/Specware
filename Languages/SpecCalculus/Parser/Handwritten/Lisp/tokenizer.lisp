;;; -*- Mode: LISP; Package: Specware; Base: 10; Syntax: Common-Lisp -*-

(in-package "PARSER4")

(defparameter *specware4-tokenizer-parameters*
  (create-tokenizer-parameters 
   ;;
   :name                        'meta-slang
   ;;
   :size-of-character-set       128
   ;;
   :word-symbol-start-chars     "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz"
   :word-symbol-continue-chars  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz?0123456789'"
   ;;
   :non-word-symbol-start-chars    "!@$^&*~+-=|<>/:\\`?'"  ; note: we need to repeat \ here, since lisp removes one
   :non-word-symbol-continue-chars "!@$^&*~+-=|<>/:\\`?'"  ; note: we need to repeat \ here, since lisp removes one
   ;;
   :number-start-chars          "0123456789"
   :number-continue-chars       "0123456789"
   ;;
   :string-quote-char           #\"
   :string-escape-char          #\\
   ;;
   :whitespace-chars            '(#\space #\tab #\newline #\page #\return)
   ;;
   ;; I think these are called special characters in the user documentation
   :separator-chars             '(#\( #\) #\{ #\} #\[ #\]  ; brackets
				  #\. #\, #\;              ; dot, comma, semi
				  ;; #\'                   ; apostrophe
				  )

   ;; Fri Apr  9 01:46:42 PDT 2004
   ;; We are in the process of replacing "sort" with "type" as a keyword.
   ;; "type" is now a keyword synonym for "sort", but is also a symbol
   ;; Fri Apr 23 17:00:23 PDT 2004
   ;; "type" is now just a keyword synonym for "sort", and is no longer a symbol

   :ad-hoc-keywords             '("end-spec" ".." "reduce" "expand") ; "using" "options" ; "_" 
   :ad-hoc-symbols              '("reduce" "expand")                 ; "using" "options" ; "__" 
   :ad-hoc-numbers              '()
   ;;
   :comment-to-eol-chars        "%"
   ;;
   :extended-comment-delimiters '(("(*" "*)" t)  ; t means recursive
				  ("\\section{"    "\\begin{spec}" nil t) ; t means ok to terminate with eof
				  ("\\subsection{" "\\begin{spec}" nil t)
				  ("\\document{"  "\\begin{spec}" nil t)
				  ("\\end{spec}"   "\\begin{spec}" nil t)
				  )
   ;;
   :pragma-delimiters           '(("proof" "end-proof"))
   ;;
   :case-sensitive?             t
   ;;
   ;; Underbar #\_ is implicitly given its own code as a syllable separator
   ))


(defun extract-specware4-tokens-from-file (file)
  (extract-tokens-from-file file *specware4-tokenizer-parameters*))


