(in-package :PARSER4)

(defparameter *specware4-tokenizer-parameters*
  (create-tokenizer-parameters 
   ;;
   :name                        'meta-slang
   ;;
   :size-of-character-set       128
   ;;
   :word-symbol-start-chars     "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz"
   :word-symbol-continue-chars  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz?_0123456789'"
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
   :ad-hoc-keywords             '("end-spec" "_" ".." "reduce") ; "using" "options" 
   :ad-hoc-symbols              '("__" "reduce")                ; "using" "options" 
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
   :case-sensitive?             t
   ;;
   ))


(defun extract-specware4-tokens-from-file (file)
  (extract-tokens-from-file file *specware4-tokenizer-parameters*))


