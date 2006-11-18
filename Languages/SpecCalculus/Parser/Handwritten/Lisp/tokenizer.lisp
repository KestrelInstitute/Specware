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
   :word-symbol-continue-chars  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789'?"
   ;;
   :non-word-symbol-start-chars    "`~!@$^&*-=+\\|:<>/'?"
   :non-word-symbol-continue-chars "`~!@$^&*-=+\\|:<>/'?"  ; note: we need to repeat \ here, since lisp removes one
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

   :ad-hoc-keywords             '(;; By default, these two strings would be multiple tokens,
				  ;; so we specially treat them as a single token:
				  "end-spec" ".." 

				  ;; These are here merely to maintain their status
				  ;; as keywords given their inclusion in :ad-hoc-symbols.

				  "reduce" "expand"  "hide" "export" "extendMorph" 
				  "colimit" "diagram" "with" "translate" "print" 
				  "is" "/" "*" "\\_times" 
				  "Snark" "answerVar" "Checker")

   :ad-hoc-symbols              '("reduce" "expand"  "hide" "export" "extendMorph" 
				  "colimit" "diagram" "with" "translate" "print" 
				  "is" "/" "*" "\\_times"
				  "Snark" "answerVar" "Checker")
   ;;
   :ad-hoc-numbers              '()
   ;;
   :comment-to-eol-chars        "%"
   ;;
   :extended-comment-delimiters '(("(*"            "*)"            t   nil) ; t means recursive
				  ("\\section{"    "\\begin{spec}" nil t)   ; t means ok to terminate with eof
				  ("\\subsection{" "\\begin{spec}" nil t)
				  ("\\document{"   "\\begin{spec}" nil t)
				  ("\\end{spec}"   "\\begin{spec}" nil t)
				  )
   ;;
   :pragma-delimiters           '(("proof" "end-proof" nil nil)) 
					; First nil:  Not recusive, to avoid problems when the word "proof" appears 
					;             inside an extended comment.
					; Second nil: Not ok to terminate with eof -- that's a hack for the latex stuff.
   ;;
   :case-sensitive?             t
   ;;
   ;; Underbar #\_ is implicitly given its own code as a syllable separator
   ))


(defun extract-specware4-tokens-from-file (file)
  (extract-tokens-from-file file *specware4-tokenizer-parameters*))
