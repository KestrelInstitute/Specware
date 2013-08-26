;;; -*- Mode: LISP; Package: Specware; Base: 10; Syntax: Common-Lisp -*-

(in-package :Parser4)

(defparameter *sw-to-c-tokenizer-parameters*
  (create-tokenizer-parameters 
   ;;
   :name                        'sw-to-c
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
   :separator-chars             '(#\. #\/)

   :ad-hoc-keywords             '("-include" "-translate" "-native" "type" "field" "op") ; to avoid getting multiple tokens
   :ad-hoc-symbols              '("-include" "-translate" "-native" "type" "field" "op") ; to allow filename called type.c, etc.
   ;;
   :ad-hoc-numbers              '()
   ;;
   :comment-to-eol-chars        "%"
   ;;
   :extended-comment-delimiters '(("(*" "*)" t nil)) ; t means recursive
   ;;
   :pragma-delimiters           '(("-verbatim" "-end" nil nil))
   ;;
   :case-sensitive?             t
   ;;
   ;; Underbar #\_ is implicitly given its own code as a syllable separator
   ))

(defun extract-sw-to-c-tokens-from-file (file)
  (extract-tokens-from-file file *sw-to-c-tokenizer-parameters*))
