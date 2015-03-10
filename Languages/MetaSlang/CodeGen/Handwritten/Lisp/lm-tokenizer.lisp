;;; -*- Mode: LISP; Package: Specware; Base: 10; Syntax: Common-Lisp -*-

(in-package :Parser4)

(defparameter *lm-tokenizer-parameters*
  (create-tokenizer-parameters 
   ;;
   :name                        'language-morphism
   ;;
   :size-of-character-set       128
   ;;
   :word-symbol-start-chars     "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789~`!@#$%^&*_+-={}|\\:;'<>?/\""
   :word-symbol-continue-chars  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789~`!@#$%^&*_+-={}|\\:;'<>?/\""
   ;;

   :non-word-symbol-start-chars    ""
   :non-word-symbol-continue-chars ""
   ;;
   :number-start-chars          "0123456789"
   :number-continue-chars       "0123456789"
   ;;
   ;; :string-quote-char           #\"
   :string-escape-char          #\\
   ;;
   :whitespace-chars            '(#\space #\tab #\newline #\page #\return)
   ;;
   ;; I think these are called special characters in the user documentation
   :separator-chars             '(#\. #\, #\/ #\( #\) #\[ #\])

   :ad-hoc-keywords             '("-import" "-include" "-himport" "-hinclude" "-cimport" "-cinclude" 
                                  "-morphism" "-translate" "-native" "-generated")   ;; to avoid getting multiple tokens
   :ad-hoc-symbols              '("-import" "-include" "-himport" "-hinclude" "-cimport" "-cinclude" 
                                  "-morphism" "-translate" "-native" "-generated")
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

(defun extract-lm-tokens-from-file (file)
  (extract-tokens-from-file file *lm-tokenizer-parameters*))
