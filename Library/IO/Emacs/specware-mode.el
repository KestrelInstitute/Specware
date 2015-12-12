;; specware-mode.el. Major mode for editing Specware
;;; Adapted from sml-mode
;; Copyright (C) 1989, Lars Bo Nielsen; 1994, Matthew J. Morley

;; (autoload 'specware-mode "specware-mode" "Major mode for editing Specware specs." t)
;;
;; Files ending in ".sw" are considered by emacs hereafter to
;; be Specware source, so put their buffers into specware-mode automatically

;;; (setq auto-mode-alist
;;;       (cons '("\\.sw$" . specware-mode) auto-mode-alist))

;; Here's an example of setting things up in the sw:specware-mode-hook:

;; (setq sw:specware-mode-hook
;;       '(lambda() "Specware mode hacks"
;;          (setq sw:indent-level 2         ; conserve on horiz. space
;;                indent-tabs-mode nil)))    ; whatever

;; sw:specware-mode-hook is run whenever a new specware-mode buffer is created.
;; There is an specware-load-hook too, which is only run when this file is
;; loaded. One use for this hook is to select your preferred
;; highlighting scheme, like this:

;; Alternatively, you can (require 'sw-font) which uses the font-lock
;; package instead. 

;; Finally, there is also an inferior-specware-mode-hook -- see
;; sl-proc.el. For more information consult the mode's *info* tree.

;;; VERSION STRING

(defconst specware-mode-version-string
  "specware-mode, Version 4.2.15")

(provide 'specware-mode)

;;; VARIABLES CONTROLLING THE MODE
(defgroup specware nil
  "Specware mode control."
  :prefix "sw:"
  :group 'applications)

(defcustom sw:use-x-symbol nil
  "If non-nil use x-symbol package with Specware"
  :type 'boolean
  :group 'specware)

(defun sw-use-x-symbol? ()
  sw:use-x-symbol)

(defcustom sw:process-on-load nil
  "If non-nil process Specware file automatically when loaded"
  :type 'boolean
  :group 'specware)

(defcustom sw:use-hide-show t
  "If non-nil use the hide-show folding package with Specware"
  :type 'boolean
  :group 'specware)

(defcustom sw:indent-level 2
  "*Indentation of blocks in Specware."
  :type 'integer
  :group 'specware)

(defcustom sw:pipe-indent -2
  "*Extra (usually negative) indentation for lines beginning with |."
  :type 'integer
  :group 'specware)

;;; This doesn't really behave as stated
(defvar sw:case-indent t
  "*How to indent case-of expressions.
    If t:   case expr                     If nil:   case expr of
              of exp1 -> ...                            exp1 -> ...
               | exp2 -> ...                          | exp2 -> ...

The first seems to be the standard in SL/NJ, but the second
seems nicer...")

(defcustom sw:nested-if-indent t
  "*Determine how nested if-then-else will be formatted:
    If t: if exp1 then exp2               If nil:   if exp1 then exp2
          else if exp3 then exp4                    else if exp3 then exp4
          else if exp5 then exp6                         else if exp5 then exp6
               else exp7                                      else exp7"
  :type 'boolean
  :group 'specware)

(defvar sw:type-of-indent t
  "*How to indent `let' `struct' etc.
    If t:  fun foo bar = let              If nil:  fun foo bar = let
                             val p = 4                 val p = 4
                         in                        in
                             bar + p                   bar + p
                         end                       end

Will not have any effect if the starting keyword is first on the line.")

(defvar sw:electric-semi-mode nil
  "*If t, `\;' will self insert, reindent the line, and do a newline.
If nil, just insert a `\;'. (To insert while t, do: C-q \;).")

(defvar sw:paren-lookback 1000
  "*How far back (in chars) the indentation algorithm should look
for open parenthesis. High value means slow indentation algorithm. A
value of 1000 (being the equivalent of 20-30 lines) should suffice
most uses. (A value of nil, means do not look at all)")

(defcustom sw:specware-mode-hook nil
  "*This hook is run when specware-mode is loaded, or a new specware-mode buffer created.
This is a good place to put your preferred key bindings."
  :type 'hook
  :group 'specware)

(defcustom sw:specware-load-hook nil
  "*This hook is only run when specware-mode is loaded."
  :type 'hook
  :group 'specware)

;;; CODE FOR SPECWARE-MODE 

(defun sw:indent-level (&optional indent)
   "Allow the user to change the block indentation level. Numeric prefix 
accepted in lieu of prompting."
   (interactive "NIndentation level: ")
   (setq sw:indent-level indent))

(defun sw:pipe-indent (&optional indent)
  "Allow to change pipe indentation level (usually negative). Numeric prefix
accepted in lieu of prompting."
   (interactive "NPipe Indentation level: ")
   (setq sw:pipe-indent indent))

(defun sw:case-indent (&optional of)
  "Toggle sw:case-indent. Prefix means set it to nil."
  (interactive "P")
  (setq sw:case-indent (and (not of) (not sw:case-indent)))
  (if sw:case-indent (message "%s" "true") (message "%s" nil)))

(defun sw:nested-if-indent (&optional of)
  "Toggle sw:nested-if-indent. Prefix means set it to nil."
  (interactive "P")
  (setq sw:nested-if-indent (and (not of) (not sw:nested-if-indent)))
  (if sw:nested-if-indent (message "%s" "true") (message "%s" nil)))

(defun sw:type-of-indent (&optional of)
  "Toggle sw:type-of-indent. Prefix means set it to nil."
  (interactive "P")
  (setq sw:type-of-indent (and (not of) (not sw:type-of-indent)))
  (if sw:type-of-indent (message "%s" "true") (message "%s" nil)))

(defun sw:electric-semi-mode (&optional of)
  "Toggle sw:electric-semi-mode. Prefix means set it to nil."
  (interactive "P")
  (setq sw:electric-semi-mode (and (not of) (not sw:electric-semi-mode)))
  (message "%s" (concat "Electric semi mode is " 
                   (if sw:electric-semi-mode "on" "off"))))

;(defun insert-circle-s () (interactive) (insert "§"))
;(defun insert-open-quote () (interactive) (insert "«"))
;(defun insert-close-quote () (interactive) (insert "»"))
;(defun insert-degree () (interactive) (insert "°"))
;(defun insert-center-dot () (interactive) (insert "·"))
;(defun insert-mu () (interactive) (insert "µ"))
;(defun insert-times () (interactive) (insert "×"))
;(defun insert-beta () (interactive) (insert "ß"))
;(defun insert-negation () (interactive) (insert "¬"))
;(defun insert-emptyset () (interactive) (insert "Ø"))

(defvar x-symbol-mode)

(defun sw:x-symbol-toggle ()
  (customize-set-variable 'sw:use-x-symbol (not sw:use-x-symbol))
  (unless (eq sw:use-x-symbol x-symbol-mode)
    (funcall x-symbol-mode)))

(defvar hs-minor-mode nil) ;; declared in hideshow.el, which is dynamically loaded

(defun sw:hide-show-toggle ()
  (customize-set-variable 'sw:use-hide-show (not sw:use-hide-show))
  (unless (eq sw:use-hide-show hs-minor-mode)
    (hs-minor-mode)))

(defun sw:save-options ()
  (interactive)
  (customize-save-customized))

(require 'easymenu) 

(defconst specware-menu 
    '("Specware"
      ["Process Current File" sw:process-current-file t]
      ["Process Unit" sw:process-unit t]
      ["Generate Lisp" sw:generate-lisp t]
      ["Generate & Load Lisp" sw:generate-compile-and-load-lisp t]
      ["Generate Sliced Lisp" sw:generate-sliced-lisp t]
      ["Generate & Load Sliced Lisp" (sw:generate-sliced-lisp t) t]
      ["Generate Local Lisp"  sw:gcl-current-file t]
      ["Evaluate Region" sw:evaluate-region (mark t)]
      ["ctext Spec" sw:set-swe-spec t]
      ["cd to this directory" cd-current-directory t] 
      ["Generate Isabelle Obligation Theory" sw:convert-spec-to-isa-thy t]
      "-----"
      ["Find Definition" sw:meta-point t]
      ["Find Theorem" sw:find-theorems t]
      ["Find Importing Spec" sw:find-importing-specs t]
      ["Find Case dispatch on type" sw:find-case-dispatch-on-type t]
      ["Find Op references" sw:find-op-references t]
      ["Go to next match" sw:continue-specware-search *pending-specware-search-results*]
      ["Ignore current matches" sw:ignore-matches *pending-specware-search-results*]
      "-----"
      ["Switch to Specware Shell" sw:switch-to-lisp t]
      ["Comment Out Region" (comment-region (region-beginning) (region-end)) (mark t)]
      ["Uncomment Region"
       (comment-region (region-beginning) (region-end) '(4))
       (mark t)]
      ["Indent region" (sw:indent-region (region-beginning) (region-end)) (mark t)]
      ["Find Unbalanced Parenthesis" (sw:find-unbalanced-parenthesis) t]
      ["Insert addParameter Template" (sw:insert-addParameter-template) t]
      ["Run Specware" run-specware4 (not (inferior-lisp-running-p))]
      "-----"
      ("Options"
       ["X-Symbol" (sw:x-symbol-toggle)
	:style toggle
	:selected sw:use-x-symbol]
       ["Hide-Show" (sw:hide-show-toggle)
	:style toggle
	:selected sw:use-hide-show]
       ["Save Options" (sw:save-options)])
      ["About Specware" about-specware t])) 

(defconst specware-interaction-menu 
    '("Specware"
      ["Find Definition" sw:meta-point t]
      ["Find Theorem" sw:find-theorems t]
      ["Find Terms of Type" sw:find-terms-of-type t]
      ["Find Case dispatch on type" sw:find-case-dispatch-on-type t]
      ["Find Op reference" sw:find-op-references t]
      ["Go to next match" sw:continue-specware-search *pending-specware-search-results*]
      ["Ignore current matches" sw:ignore-matches *pending-specware-search-results*]
      "-----"
      ["Switch to Previous File" sw:switch-to-lisp t]
      ["Search for Previous Input" isearch-backward-regexp t]
      ["Run Specware" run-specware4 (not (inferior-lisp-running-p))]
      ["Exit Specware" sw:exit-lisp (inferior-lisp-running-p)]
      "-----"
      ("Options"
       ["X-Symbol" (sw:x-symbol-toggle)
	:style toggle
	:selected (and (boundp 'x-symbol-mode) x-symbol-mode)]
       ["Save Options" (sw:save-options)])
      ["About Specware" about-specware t]))

;;; BINDINGS: should be common to the source and process modes...

(defvar specware-mode-menu)

(defun install-sw-keybindings (map)
  ;; Text-formatting commands:
  (define-key map "\C-c\C-m" 'sw:insert-form)
  (define-key map "\M-|"     'sw:electric-pipe)
  (define-key map "\;"       'sw:electric-semi)
  (define-key map "\C-ci"    'sw:insert-in)
  (define-key map "\M-\t"    'sw:back-to-outer-indent)
  (define-key map "\C-j"     'newline-and-indent)
  ;(define-key map "\177"     'backward-delete-char-untabify)
  (define-key map [backspace] 'backward-delete-char-untabify)
  (define-key map "\C-\M-\q" 'sw:indent-sexp)
  (define-key map "\C-\M-\\" 'sw:indent-region)
  (define-key map "\t"       'sw:indent-line) ; ...except this one

  (define-key map "\M-."     'sw:meta-point)
  (define-key map "\M-,"     'sw:continue-specware-search)
  (define-key map "\C-cp"    'sw:process-current-file)
  (define-key map "\C-c\C-p" 'sw:process-unit)
  (define-key map "\C-c\g"   'sw:generate-lisp)
  (define-key map "\C-cl"    'sw:generate-compile-and-load-lisp)
  (define-key map "\C-c\C-l" 'sw:gcl-current-file)
  (define-key map "\C-c\C-e" 'sw:evaluate-region)
  (define-key map "\C-c\C-s" 'sw:set-swe-spec)
  (define-key map "\C-c\C-u" 'sw:cl-unit)
  (define-key map "\C-c\C-a"    'sw:apropos-symbol)
  (define-key map "\C-c!"    'cd-current-directory)
  (define-key map "\M-*"     'sw:switch-to-lisp)
  ;(define-key map "\C-?"     'backward-delete-char-untabify)
  (define-key map "\C-\M-a"  'sw:beginning-of-unit)
  (define-key map "\C-\M-e"  'sw:end-of-unit)
  (define-key map [(control super a)]  'sw:beginning-of-element)
  (define-key map [(control super e)]  'sw:end-of-element)
  (define-key map "\C-\M-n"  'sw:next-unit)
  (define-key map "\C-c%"    'extract-sexp)
  (define-key map "\C-c;"    'comment-region)

  (define-key map "\C-cfi"   'sw:find-importing-specs)
  (define-key map "\C-cfc"   'sw:find-case-dispatch-on-type)
  (define-key map "\C-cft"   'sw:find-terms-of-type)
  (define-key map "\C-cfr"   'sw:find-op-references)
  (define-key map "\C-cf\C-t" 'sw:find-theorems)
  (define-key map "\C-cf"  'sw:ignore-matches)

  (define-key map "\C-c\C-i" 'sw:convert-spec-to-isa-thy)
  (define-key map "\C-ch"    'sw:convert-spec-to-haskell)
  (define-key map "\C-cH"    'sw:convert-top-spec-to-haskell)

  (define-key map [(meta super down-mouse-1)] 'sw:show-containing-object)
					          ; Franz binding
;  (define-key map "\C-cs"    'insert-circle-s)    ; Process to debug
;  (define-key map "\C-c`"    'insert-open-quote)
;  (define-key map "\C-c'"    'insert-close-quote)
;  (define-key map "\C-cd"    'insert-degree)      ; Describe symbol
;  (define-key map "\C-cu"    'insert-mu)
;  (define-key map "\C-ct"    'insert-center-dot)  ; trace
;  (define-key map "\C-cx"    'insert-times)
;  (define-key map "\C-cb"    'insert-beta)
;  (define-key map "\C-cn"    'insert-negation)
;  (define-key map "\C-ce"    'insert-emptyset)

  (easy-menu-add specware-mode-menu map) 
  )

(defvar sw:no-doc
  "This function is part of sw:proc, and has not yet been loaded.
Full documentation will be available after autoloading the function."
  "Documentation for autoload functions.")

(defvar specware-mode-map nil "The mode map used in specware-mode.")
(cond ((not specware-mode-map)
       (setq specware-mode-map (make-sparse-keymap))
       (easy-menu-define specware-mode-menu
			 specware-mode-map
			 "Menu used in Specware mode."
			 specware-menu)
       (install-sw-keybindings specware-mode-map)))

;;;(and fi:lisp-listener-mode-map
;;;     (install-sl-keybindings fi:lisp-listener-mode-map))
;;;(and fi:inferior-common-lisp-mode-map
;;;     (install-sl-keybindings fi:inferior-common-lisp-mode-map))

(defun specware-mode-version ()
  "This file's version number (specware-mode)."
  (interactive)
  (message specware-mode-version-string))

(defvar specware-mode-syntax-table nil "The syntax table used in specware-mode.")
(if specware-mode-syntax-table
    ()
  (setq specware-mode-syntax-table (make-syntax-table))
  ;; Set everything to be "." (punctuation) except for [A-Za-z0-9],
  ;; which will default to "w" (word-constituent).
  (let ((i 0))
    (while (< i ?0)
      (modify-syntax-entry i "." specware-mode-syntax-table)
      (setq i (1+ i)))
    (setq i (1+ ?9))
    (while (< i ?A)
      (modify-syntax-entry i "." specware-mode-syntax-table)
      (setq i (1+ i)))
    (setq i (1+ ?Z))
    (while (< i ?a)
      (modify-syntax-entry i "." specware-mode-syntax-table)
      (setq i (1+ i)))
    (setq i (1+ ?z))
    (while (< i 128)
      (modify-syntax-entry i "." specware-mode-syntax-table)
      (setq i (1+ i))))

  ;; Now we change the characters that are meaningful to us.
  (modify-syntax-entry ?\(      "() 1"   specware-mode-syntax-table)
  (modify-syntax-entry ?\)      ")( 4"   specware-mode-syntax-table)
  (modify-syntax-entry ?\[      "(]"    specware-mode-syntax-table)
  (modify-syntax-entry ?\]      ")["    specware-mode-syntax-table)
  (modify-syntax-entry ?{       "(}"    specware-mode-syntax-table)
  (modify-syntax-entry ?}       "){"    specware-mode-syntax-table)
;;;  (modify-syntax-entry ?\*      ". 67"  specware-mode-syntax-table) ;; commented out by MB
  (modify-syntax-entry ?*      ". 23"  specware-mode-syntax-table) ;; added by MB
  
  (modify-syntax-entry ?\"      "\"    " specware-mode-syntax-table)
  (modify-syntax-entry ?\\      "\\   " specware-mode-syntax-table)
  (modify-syntax-entry ?\#      "/"     specware-mode-syntax-table)
  (modify-syntax-entry ?        " "     specware-mode-syntax-table)
  (modify-syntax-entry ?\t      " "     specware-mode-syntax-table)
  ;(modify-syntax-entry ?\%      "<   "  specware-mode-syntax-table) ;; commented out by MB
  (modify-syntax-entry ?\%      "< b"  specware-mode-syntax-table) ;; added by MB
  ;(modify-syntax-entry ?\n      ">   "  specware-mode-syntax-table)
  (modify-syntax-entry ?\n      "> b"  specware-mode-syntax-table) ;; added by MB
  (modify-syntax-entry ?\f      " "     specware-mode-syntax-table)
  (modify-syntax-entry ?\'      "w"     specware-mode-syntax-table)
  (modify-syntax-entry ?\_      "w"     specware-mode-syntax-table)
  (modify-syntax-entry ?\-      "w"     specware-mode-syntax-table)
  (modify-syntax-entry ?\?      "w"     specware-mode-syntax-table)
  (modify-syntax-entry ?\«      "."     specware-mode-syntax-table)
  (modify-syntax-entry ?\»      "."     specware-mode-syntax-table))


(require 'regexp-opt)

;;; Hide-show support
(defvar sw:definition-introducing-words
  (regexp-opt '("axiom"
		"conjecture"
		"def"
		"op"
		"theorem"
		"type"
                "refine"
                "proof"
                "#translate")))

(defvar sw:whitespace "\\(\n\\|\\s-\\)")

(defvar sw:basic-unit-intro-regexp "^\\(\\sw+\\)\\(\n\\|\\s-\\)* =\\(\n\\| \\)\\s-*")

(defvar sw:definition-intro-sexp
  (concat "\\<\\(" sw:definition-introducing-words "\\)"))

(defvar sw:definition-ending-sexp
  (concat "\\<\\(" sw:definition-introducing-words
	  "\\|end-?spec"
	  "\\)\\>"))

(defvar sw:def-ending-sexp		; Add "in" for def because of local definitions
  (concat "\\<\\(" sw:definition-introducing-words
	  "\\|\\<\\|in"
	  "\\|end-?spec"
	  "\\)\\>"))

;; (defvar hs-minor-mode-map)
(defvar hs-allow-nesting)
(defvar hs-marker-begin-regexp)
(defvar hs-marker-end-regexp)

(when sw:use-hide-show
  ;(setq hs-minor-mode-map nil)		; Force resetting in case of old version
  (require 'hideshow)
  (setq hs-allow-nesting t)
  (add-to-list 'hs-special-modes-alist
	       `(specware-mode ,(concat "\\(\\s(\\|\\<def\\>\\|"
					sw:definition-intro-sexp
					"\\|"
					sw:basic-unit-intro-regexp
					"\\|%{{{"
					"\\)")
                               "\\(\\<end-?spec\\|%}}}\\)"
			       nil
			       sw:forward-exp
			       nil      ;sw:adjust-begin
			       ))
  ;; (add-to-list 'hs-special-modes-alist
  ;;              `(specware-mode ,(concat "\\(\\s(\\|\\<proof\\>\\|^#translate\\>\\|"
  ;;       				sw:definition-intro-sexp
  ;;       				"\\|"
  ;;       				sw:basic-unit-intro-regexp
  ;;       				"\\|%{{{"
  ;;       				"\\)")
  ;;                              nil ;"\\(\\s)\\|\\<end-proof|\\<#end\\|\\<end-?spec\\|%}}}\\)"
  ;;       		       nil
  ;;       		       sw:forward-exp
  ;;       		       sw:adjust-begin
  ;;       		       ))
  )

(defun sw:forward-exp (n)
  (interactive "p")
  (if (looking-at "#translate\\>")
      (sw:re-search-forward "#end")
    (if (looking-at "\\s-*proof\\>")
      (sw:re-search-forward "\\<end-proof\\>")
      (if (looking-at sw:basic-unit-intro-regexp)
          (progn (forward-char 1)
                 (if (sw:re-search-forward sw:basic-unit-intro-regexp)
                     (progn (beginning-of-line))
                   (goto-char (point-max)))
                 (forward-comment -100)) ; Go backward until non-comment found
        (if (and (looking-at "\\<def\\>") (not (looking-back "\\<refine\\s-*")))
            (let ((beg-indentation (1+ (current-column))) ; 1+ just in case user indent by 1
                  (found-end nil))
              (while (not found-end)
                (end-of-line)
                (if (sw:re-search-forward sw:def-ending-sexp)
                    (progn (forward-sexp -1)
                           (if (<= (current-column) beg-indentation)
                               (setq found-end t)))
                  (if (sw:re-search-forward sw:basic-unit-intro-regexp)
                      (progn (beginning-of-line)
                             (setq found-end t))
                    (goto-char (point-max)))))
              (forward-comment -100))
          (if (looking-at sw:definition-intro-sexp) ; other than def
              (let ((beg-indentation (1+ (current-column))) ; 1+ just in case user indent by 1
                    (found-end nil))
                (while (not found-end)
                  (end-of-line)
                  (if (or (sw:re-search-forward sw:definition-ending-sexp)
                          (sw:re-search-forward sw:basic-unit-intro-regexp))
                      (progn (forward-sexp -1)
                             (if (and (<= (current-column) beg-indentation)
                                      (not (looking-back"\\<let\\s-*")))
                                 (setq found-end t)))
                    (goto-char (point-max))))
                (forward-comment -100))
            (if (looking-at hs-marker-begin-regexp)
                (sw:scan-matching-patterns "%{{{" "\\(%{{{\\|%}}}\\)")
              (if (looking-at "(\\*")
                  (sw:scan-matching-patterns "(\\*" "\\((\\*\\|\\*)\\)")
                (let ((parse-sexp-ignore-comments t))
                  (forward-sexp n))))))))))

(defun sw:scan-matching-patterns (beg beg-end)
  (let ((beg-marker (re-search-forward beg nil t)))
    (if (null beg-marker)
	(warn "No region marker")
      (sw:scan-to-end-matching-patterns beg beg-end))))

(defun sw:scan-to-end-matching-patterns (beg beg-end)
  (let ((next-marker (re-search-forward beg-end nil t)))
    (if (null next-marker)
	(warn "Unmatched marker")
      (progn (goto-char (match-beginning 0))
	     (if (looking-at beg)
		 (progn (sw:scan-matching-patterns beg beg-end)
			(sw:scan-to-end-matching-patterns beg beg-end))
	       (goto-char (match-end 0)))))))

(defun sw:adjust-begin (n)
  (point))

;;; hs-block-start-regexp hs-block-start-mdata-select hs-block-end-regexp
;;; hs-forward-sexp-func hs-adjust-block-beginning

(defun specware-mode ()
  "Major mode for editing Specware code.
Tab indents for Specware code.
Comments are delimited with (* ... *).
Blank lines and form-feeds separate paragraphs.
Delete converts tabs to spaces as it moves back.

For information on running an inferior Specware process, see the documentation
for inferior-specware-mode (set this up with \\[sl]).

Customization: Entry to this mode runs the hooks on sw:specware-mode-hook.

Variables controlling the indentation
=====================================

Seek help (\\[describe-variable]) on individual variables to get current settings.

sw:indent-level (default 2)
    The indentation of a block of code.

sw:pipe-indent (default -2)
    Extra indentation of a line starting with \"|\".

sw:case-indent (default nil)
    Determine the way to indent case-of expression.

sw:nested-if-indent (default nil)
    Determine how nested if-then-else expressions are formatted.

sw:type-of-indent (default t)
    How to indent let, etc.
    Will not have any effect if the starting keyword is first on the line.

sw:electric-semi-mode (default nil)
    If t, a `\;' will reindent line, and perform a newline.

sw:paren-lookback (default 1000)
    Determines how far back (in chars) the indentation algorithm should 
    look to match parenthesis. A value of nil, means do not look at all.

Mode map
========
\\{specware-mode-map}"

  (interactive)
  (kill-all-local-variables)
  (specware-mode-variables)
  (use-local-map specware-mode-map)
  (setq major-mode 'specware-mode)
  (setq mode-name "Specware")
  (easy-menu-add specware-mode-menu)
  (setq indent-tabs-mode nil)		; Don't use tabs when doing automatic indentation
  (if sw:use-x-symbol
      (funcall x-symbol-mode t))
  (run-mode-hooks 'sw:specware-mode-hook))           ; Run the hook

(when sw:use-hide-show
  (add-hook 'sw:specware-mode-hook
            (lambda ()
              (hs-minor-mode 1)
              (setq hs-marker-begin-regexp "\\s-*%{{{")
              (setq hs-marker-end-regexp "\\s-*%}}}"))))

;; This is to make up for the fact that the space is not part of the prompt
(defun sw:move-beginning-of-line (n)
  (interactive "P")
  (move-beginning-of-line n)
  (when (and (eq (char-after) ? )
             (eq (char-after (- (point) 1)) ?*))
    (forward-char 1)))

(defun sw:at-prompt ()
  (= (point)
     (with-current-buffer sw:common-lisp-buffer-name
       (sw:move-beginning-of-line nil)
       (point))))

(defun sw:process-current-file-and-return ()
  (when sw:process-on-load
    (let ((buf (current-buffer)))
        (unless (or (eq (point) (point-max))
                    (eq ?~ (elt buffer-file-name (- (length buffer-file-name) 1)))
                    (not (sw:at-prompt)))
          (let ((filename (sw::file-to-specware-unit-id buffer-file-name t)))
            (lisp-or-specware-command-quiet ":sw " "proc " filename)))
      ;(pop-to-buffer buf)
      )))

(add-hook 'sw:specware-mode-hook
          'sw:process-current-file-and-return)

(defvar specware-mode-abbrev-table nil "*Specware mode abbrev table (default nil)")

(defun specware-mode-variables ()
  (set-syntax-table specware-mode-syntax-table)
  (setq local-abbrev-table specware-mode-abbrev-table)
  ;; A paragraph is separated by blank lines or ^L only.
  (make-local-variable 'paragraph-start)
  (setq paragraph-start (concat "^[\t ]*$\\|" page-delimiter))
  (make-local-variable 'paragraph-separate)
  (setq paragraph-separate paragraph-start)
  (make-local-variable 'indent-line-function)
  (setq indent-line-function 'sw:indent-line)
  (make-local-variable 'comment-start)
  (setq comment-start "%")
  (make-local-variable 'block-comment-start)
  (setq block-comment-start "(*")
  (make-local-variable 'block-comment-end)
  (setq block-comment-end "*)")
  (make-local-variable 'comment-column)
  (setq comment-column 40)              
  (make-local-variable 'comment-start-skip)
  (setq comment-start-skip "\\((\\*\\|\`\end{spec}\\)+[ \t]?")
  (make-local-variable 'comment-indent-function)
  (setq comment-indent-function 'sw:comment-indent)
  (make-local-variable 'font-lock-fontify-region-function)
;;   (setq font-lock-fontify-region-function
;;         'specware-font-lock-fontify-region-function)
  (setq font-lock-defaults '(specware-font-lock-keywords))
  ;;
  ;; Adding these will fool the matching of parens. I really don't
  ;; know why. It would be nice to have comments treated as
  ;; white-space.
  ;; 
  ;;(make-local-variable 'parse-sexp-ignore-comments)
  (setq parse-sexp-ignore-comments t)
  )

(defun specware-font-lock-fontify-region-function (beg end &optional loudvar)
  ;(specware-font-lock-fontify-tex beg end)
  (font-lock-default-fontify-region beg end loudvar)
  (specware-font-lock-fontify-tex beg end)
)

(defun specware-font-lock-fontify-tex (beg end)
  (goto-char beg)
  (let ((start (if (search-forward "\\end{spec}" end t)
		   ;; In case region starts within a begin-end-spec block
		   (match-beginning 0)
		 beg)))
    (goto-char beg)
    (while (and (< (point) end)
		(search-forward "\\begin{spec}" end t))
      (when (> start (point))
	;; Only possible first time through loop
	(setq start beg))
      (font-lock-set-face start (point) font-lock-comment-face)
      (setq start (if (search-forward "\\end{spec}" end t)
		      (match-beginning 0)
		    (goto-char end))))
    (when (and (> start beg) (< start end))
      (font-lock-set-face start end font-lock-comment-face))))

(defvar lazy-shot-step-size)

(unless (and (boundp 'lazy-shot-step-size)
	     lazy-shot-step-size
	     (> lazy-shot-step-size 1024))
  (setq lazy-shot-step-size 4096))

;;; ??
(defconst sw:pipe-matchers-reg
  "\\bcase\\b\\|\\bfn\\b\\|\\bfun\\b\
\\|\\bdatatype\\b"
  "The keywords a `|' can follow.")

(defun sw:electric-pipe ()
  "Insert a \"|\". 
Depending on the context insert the name of function, a \"->\" etc."
  (interactive)
  (let ((case-fold-search nil)          ; Case sensitive
        ;(here (point))
        (match (save-excursion
                 (sw:find-matching-starter sw:pipe-matchers-reg)
                 (point)))
        (tmp "  -> ")
        (case-or-handle-exp t))
    (if (/= (line-beginning-position)
            (save-excursion (skip-chars-backward "\t ") (point)))
        (insert "\n"))
    (insert "|")
    (save-excursion
      (goto-char match)
      (cond
       ;; It was a function, insert the function name
       ((looking-at "fn\\b")
        (setq tmp (concat " " (buffer-substring-no-properties
                               (progn (forward-char 3)
                                      (skip-chars-forward "\t\n ") (point))
                               (progn (forward-word 1) (point))) " "))
        (setq case-or-handle-exp nil))
       ;; It was a datatype, insert nothing
       ((looking-at "type\\b")  ; ??
        (setq tmp " ") (setq case-or-handle-exp nil))
       ;; If it is an and, then we have to see what is was
       ((looking-at "and\\b")  ; ??
        (let (isfun)
          (save-excursion
            (condition-case ()
                (progn
                  (re-search-backward "type\\b\\|fn\\b")
                  (setq isfun (looking-at "fn\\b")))
              (error (setq isfun nil))))
          (if isfun
              (progn
                (setq tmp
                      (concat " " (buffer-substring-no-properties
                                   (progn (forward-char 3)
                                          (skip-chars-forward "\t\n ") (point))
                                   (progn (forward-word 1) (point))) " "))
                (setq case-or-handle-exp nil))
            (setq tmp " ") (setq case-or-handle-exp nil))))))
    (insert tmp)
    (sw:indent-line nil)
    (beginning-of-line)
    (skip-chars-forward "\t ")
    (forward-char (1+ (length tmp)))
    (if case-or-handle-exp
        (forward-char -4))))

(defun sw:electric-semi ()
  "Inserts a \;.
If variable sw:electric-semi-mode is t, indent the current line, insert 
a newline, and indent."
  (interactive)
  (insert "\;")
  (if sw:electric-semi-mode
      (reindent-then-newline-and-indent)))

(defun sw:insert-in ()
  "Inserts in on a new line and indents, then inserts another new line and indents"
  (interactive)
  (delete-horizontal-space t)
  (newline)
  (insert "in")
  (reindent-then-newline-and-indent))

;;; INDENTATION !!!

(defun sw:mark-function ()
  "Synonym for mark-paragraph -- sorry.
If anyone has a good algorithm for this..."
  (interactive)
  (mark-paragraph))

(defun sw:indent-sexp (n)
  (interactive "p")
  (sw:indent-region (save-excursion (forward-line 1) (point))
		    (save-excursion
                      (skip-chars-forward " \t")
                      (if (looking-at "\\s(")
                          (forward-sexp (or n 1))
                        (sw:end-of-element))
                      (point))))

(defun sw:indent-region (beg end)
  "Indent region of Specware code."
  (interactive "r")
  (message "Indenting region...")
  (let ((font-lock-mode nil))           ; Can't rely on font-lock for comment and string info
    (save-excursion
      (goto-char end) (setq end (point-marker)) ; necessary for < comparison to work properly when byte-compiled ?!
      (goto-char beg)
      (while (looking-at " *\n")
        (forward-line 1))
      (while (< (point) end)
        (sw:indent-line t)
        (when (looking-at "(\\*")
          (forward-comment 1))
        (beginning-of-line 2)
        (while (looking-at " *\n")
          (forward-line 1)))))
  (message "Indenting region... done"))

(defun sw:indent-line (&optional indent-comment-wrt-next-line)
  "Indent current line of Specware code."
  (interactive "p")
  (let* ((indent (sw:calculate-indentation))
         (indent (if (and (not (equal indent-comment-wrt-next-line 1))
                          (looking-at " *\\(%\\|(\\*\\)"))
                     (min indent (sw:indent-from-next-line))
                   indent)))
    (if (/= (current-indentation) indent)
        (save-excursion                 ;; Added 890601 (point now stays)
          (let ((beg (progn (beginning-of-line) (point))))
            (skip-chars-forward "\t ")
            (delete-region beg (point))
            (indent-to indent))))
    ;; If point is before indentation, move point to indentation
    (if (< (current-column) (current-indentation))
        (skip-chars-forward "\t "))))

(defun sw:back-to-outer-indent ()
  "Unindents to the next outer level of indentation."
  (interactive)
  (save-excursion
    (beginning-of-line)
    (skip-chars-forward "\t ")
    (let ((start-column (current-column))
          (indent (current-column)))
      (if (> start-column 0)
          (progn
            (save-excursion
              (while (>= indent start-column)
                (if (re-search-backward "^[^\n]" nil t)
                    (setq indent (current-indentation))
                  (setq indent 0))))
            (backward-delete-char-untabify (- start-column indent)))))))

(defconst sw:top-starters-reg  ; ??
  "\\b\\op\\b\\|\\bdef\\b\\|\\btype\\b\\|import\\b"
  "The starters of new top-level expressions.")

(defconst sw:indent-starters-reg  ; ??
  "let\\b\\|case\\b\\|fn\\b\
\\|else\\b\\|def\\b\\|if\\b\\|else if\\b\
\\|in\\b\\|infix\\b\\|infixr\\b\
\\|nonfix\\b\\|of\\b\\|open\\b\\|raise\\b\\|sig\\b\\|signature\\b\
\\|struct\\b\\|structure\\b\\|then\\b\
\\|specmap\\b\\|progmap\\b\\|while\\b\\|withtype\\b\
\\|\\(initial[ \\t]*\\|final[ \\t]*\\|\\b\\)\\(mode\\|stad\\)\\b\\|prog\\b\\|step\\b"
  "The indentation starters. The next line will be indented.")

(defconst sw:all-indent-starters-reg (concat sw:top-starters-reg "\\|" sw:indent-starters-reg))

(defconst sw:starters-indent-after
  "let\\b"
  "Indent after these.")

(defun sw:calculate-indentation ()
  (save-excursion
    (let ((case-fold-search nil))
      (beginning-of-line)
      (if (bobp)                        ; Beginning of buffer
          0                             ; Indentation = 0
        (skip-chars-forward "\t ")
        (cond
         ;; Indentation for comments alone on a line, matches the
         ;; proper indentation of the next line. Search only for the
         ;; next "*)", not for the matching.
         ((looking-at "(\\*")
          (if (not (search-forward "*)" nil t))
              (error "Comment not ended."))
          (end-of-line)
          (skip-chars-forward "\n\t ")
          ;; If we are at eob, just indent 0
          (if (eobp) 0 (sw:calculate-indentation)))
         ;; Continued string ? (Added 890113 lbn)
         ((looking-at "\\\\")
          (save-excursion
            (if (save-excursion (forward-line -1)
                                (beginning-of-line)
                                (looking-at "[\t ]*\\\\"))
                (progn (forward-line -1) (current-indentation))
            (if (re-search-backward "[^\\\\]\"" nil t)
                (1+ (current-indentation))
              0))))
         ;; Are we looking at a case expression ?
         ((looking-at "| ")
          (sw:back-exp-until "\\(of\\b\\||\\|case\\b\\|fn\\b\\|handle\\b\\|->\\|| \\|type\\b\\)")
          (cond ((looking-at "of\\b")
                 ;; "case of | ..."  treat like "of"
                 (sw:re-search-backward "\\bcase\\b")
                 (+ (current-column) sw:indent-level))
	    ;; Dont get fooled by fn _ -> in case statements (890726)
	    ;; Changed the regexp a bit, so fn has to be first on line,
	    ;; in order to let the loop continue (Used to be ".*\bfn....")
	    ;; (900430).
                ((looking-at "|")
                 (let (indent
                       (beg-of-line (line-beginning-position)))
                   (while (> (point) beg-of-line)
                     (setq indent (current-column))
                     (sw:back-exp-until "|"))
                   indent))
                ((looking-at "case") (+ (current-column) sw:indent-level))
                ((looking-at "fn") (1+ (current-indentation)))
                ((looking-at "type") (+ (current-column) sw:indent-level))
                ((looking-at "handle") (+ (current-indentation) 5))
                ((looking-at "->")
                 (sw:block-back)
                 (while (not (or (looking-at "of\\b\\|fn\\b") (looking-back "|\\s-*")) )
                   (sw:block-back))
                 (if (looking-at "of\\b\\|fn\\b")
                     (+ (current-column) 1)
                   (+ (current-indentation) (if (looking-at "of\\b") 1 0))))
                (t (+ (current-indentation) sw:pipe-indent))))
         ((looking-at "and\\b")
          (if (sw:find-matching-starter sw:top-starters-reg)
              (current-column)
            0))
         ((looking-at "in\\b")          ; Match the beginning let/local
          (sw:find-match-indent "in" "\\bin\\b" "\\blet\\b"))
	 ((looking-at "spec\\b")
          (backward-sexp)
          (if (looking-at "qualifying")
              (progn (backward-sexp)
                     (current-column))
            (current-indentation)))
	 ((looking-at "end-?spec\\b")
	  (sw:find-match-indent "end-spec" "\\bend-spec\\b" "\\bspec\\b"))
         ((and sw:nested-if-indent (looking-at "else[\t ]*if\\b"))
          (sw:re-search-backward "\\bif\\b\\|\\belse\\b")
          (current-indentation))
         ((looking-at "else\\b")        ; Match the if
          (sw:find-match-indent "else" "\\belse\\b" "\\bif\\b" t "\\belse if\\b"))
         ((looking-at "then\\b")        ; Match the if + extra indentation
          (+ (sw:find-match-indent "then" "\\bthen\\b" "\\bif\\b" t)
             sw:indent-level))
         ((and sw:case-indent (looking-at "of\\b"))
          (sw:re-search-backward "\\bcase\\b")
          (+ (current-column) 1))
         ((looking-at "\\s)")           ; Close paren
          (forward-char 1)
          (sw:backward-sexp)
          (current-column))
         ((looking-at sw:top-starters-reg)
          (let ((start (point)))
            (sw:backward-sexp)
            (if (and (looking-at sw:starters-indent-after)
                     (/= start (point)))
                (+ (if sw:type-of-indent
                       (current-column)
                     (if (progn (beginning-of-line)
                                (skip-chars-forward "\t ")
                                (looking-at "|"))
                         (- (current-indentation) sw:pipe-indent)
                       (current-indentation)))
                   sw:indent-level)
              (beginning-of-line)
              (skip-chars-forward "\t ")
              (if (and (looking-at sw:starters-indent-after)
                       (/= start (point)))
                  (+ (if sw:type-of-indent
                         (current-column)
                       (current-indentation))
                     sw:indent-level)
                (goto-char start)
                (if (sw:find-matching-starter sw:top-starters-reg)
                    (current-column)
                  0)))))
         (t
          (let* ((follows-comma (sw:previous-line-ends-in-comma))
                 (paren-indent (sw:get-paren-indent follows-comma))
                 (indent (sw:get-indent-from-previous-line
                          follows-comma
                          paren-indent)))
            (when (and (looking-at "|")
                       (not (looking-at "||")))
              (setq indent (if (sw:find-matching-starter
                                "\\bcase\\b\\|\\bfn\\b\\|\\band\\b\\|\\bhandle\\b\\|\\btype\\b")
                               (cond
                                 ((looking-at "case\\b") (- (current-column) sw:pipe-indent))
                                 ((looking-at "fn\\b") (1+ (current-column)))
                                 ((looking-at "type\\b") (1+ (1+ (current-column))))
                                 ((looking-at "and\\b") (1+ (1+ (current-column))))
                                 ((looking-at "handle\\b") (+ (current-column) 5)))
                             (+ indent sw:pipe-indent))))
            (if sw:paren-lookback       ; Look for open parenthesis ?
                (max indent paren-indent)
              indent))))))))

(defun looking-before (str)
  (and (> (point) (length str))
       (save-excursion
         (forward-char (- (length str)))
         (looking-at str))))

(defun sw:previous-line-ends-in-comma ()
  (save-excursion
    (sw:end-of-previous-line)
    (forward-comment -100)
    (while (re-search-backward comment-start (line-beginning-position) t)
      (skip-chars-backward "\t\n "))
    (if (looking-before " in") 'in
      (if (or (member (preceding-char) '(?, ?\;))
              (looking-before "||")
              (looking-before "&&"))
          'comma nil))))

(defun sw:end-of-previous-line ()
  (beginning-of-line)
  (skip-chars-backward "\t\n "))

(defun sw:indent-from-next-line ()
  (save-excursion
    (forward-sexp)
    (current-indentation)))

(defun sw:get-indent-from-previous-line (no-extra-indent-p paren-indent)
  (save-excursion
    (let ((case-fold-search nil)
          (expr-ended no-extra-indent-p)
          (origpoint (point)))
      (beginning-of-line)
      ;;(skip-chars-backward "\t\n; ") (when (looking-at ";") (sw:backward-sexp))
      (if (not (sw:backward-sexp))
          0                         ; Failed fall back on paren-indent
        (when (save-excursion
                (beginning-of-line)
                (forward-whitespace 1)
                (looking-at sw:top-starters-reg))
          (setq expr-ended t))
        (cond ((bobp) 0)
              ((looking-at "in\\b")   (sw:find-match-indent "in" "\\bin\\b" "\\blet\\b"))
              ((looking-at "then\\b") (+ (sw:find-match-indent "then" "\\bthen\\b" "\\bif\\b" t "\\belse if\\b") sw:indent-level))
              (t 
               ;; Go backward by grouped expressions until you are at the beginning of a line or after =
               (let ((backward-sexp-failed nil))
                 (while (not (or backward-sexp-failed
                                 (= (current-column) (current-indentation))
                                 (looking-at sw:indent-starters-reg)
                                 (and (not expr-ended)
                                      (looking-back "let .* = *\\|-> *"))))
                   (let ((ipos (point)))
                     (when (looking-at "->\\|else\\b\\|else\\b")
                       (setq expr-ended t))
                     (unless (sw:backward-sexp)
                       (setq backward-sexp-failed t)
                       (forward-char 1))
                     (when (and (not (sw:same-line-p ipos (point)))
                                (not (sw:same-line-p ipos (save-excursion (forward-sexp)
                                                                          (point)))))
                       (goto-char ipos)
                       (beginning-of-line)
                       (forward-whitespace 1)))))
               ;; (forward-whitespace 1)
               (let ((indent (current-column)))
                 ;; ?? (skip-chars-forward "\t (")
                 (cond
                  (no-extra-indent-p (min indent paren-indent))
                  ((looking-at "\\(in\\|then\\|else\\)\\b") (+ indent sw:indent-level))
                  ((looking-at "let +def\\b") (+ indent 4 sw:indent-level))
                  ((looking-at "let\\b") (+ indent 4))
                  ((looking-at "| _ -> *\n")
                   (- indent 2))
                  ;; Started fun...
                  ((or (looking-at sw:indent-starters-reg)
                       (looking-at "| "))
                   (+ indent sw:indent-level))
                  ((looking-at sw:top-starters-reg)
                   (if (save-excursion
                         (goto-char origpoint)
                         (or (looking-at sw:top-starters-reg)
                             (and (looking-at "%%\\|(\\*")
                                  (save-excursion
                                    (sw:end-of-previous-line)
                                    (skip-chars-backward "\t\n ")
                                    (not (looking-before "="))))))
                       indent (+ indent sw:indent-level)))
                  ;; else keep the same indentation or + sw:indent-level as previous line
                  (t  (if (or ; (= indent paren-indent)
                              (sw:prev-line-arg-p indent))
                          indent
                        (+ indent sw:indent-level)))))))))))

;;; True if the previous line is a curried arg
(defun sw:prev-line-arg-p (indent)
  (and (= (current-column) (current-indentation))
       (sw:backward-sexp)
       (not (bobp))
       (let ((prev-indent (current-indentation)))
         (beginning-of-line)
         (forward-char (if (or (= indent prev-indent)
                               (= indent (+ prev-indent 2)))
                           prev-indent
                         indent))
         (not (or (looking-at sw:all-indent-starters-reg)
                  (looking-at "| ")
                  (and (/= (current-column) (current-indentation))
                       (progn (backward-word 1)
                              (looking-at sw:all-indent-starters-reg))))))))

(defun sw:same-line-p (pos1 pos2)
  "Return t if buffer positions POS1 and POS2 are on the same line."
  (save-excursion (goto-char (min pos1 pos2))
                  (<= (max pos1 pos2) (line-end-position 1))))

(defun sw:get-paren-indent (;indent
                            after-comma)
  (save-excursion
    (let ((origpoint (point))
          (at-top-level nil)
          open-paren-point)
      (insert ")")
      (condition-case ()
          (backward-sexp 1)
        (error (setq at-top-level t)))
      (save-excursion (goto-char origpoint)
                      (delete-char 1))
      (setq open-paren-point (point))
      (if at-top-level 0
          ;; (if (or (looking-at sw:top-starters-reg)
          ;;         (looking-at "%\\|(\\*")
          ;;         (re-search-forward "\\bspec\\b" (save-excursion (end-of-line) (point)) t))
          ;;     0 sw:indent-level)
        (progn (forward-char 1)
               (unless (save-excursion (skip-chars-forward "\t ")
                                       (looking-at "\n"))
                 (skip-chars-forward "\t "))
               (if (save-excursion
                     (goto-char origpoint)
                     (looking-at "[\\|]\\|)\\|}\\|(\\*\\|%"))
                   (current-column)
                 (if (and after-comma
                          (save-excursion (skip-chars-forward "\t ")
                                          (or (looking-at "\n")
                                              (looking-at "(\\*")
                                              (looking-at comment-start))))
                     0
                   ;; (if (save-excursion (goto-char origpoint)
                   ;;                     (beginning-of-line 0)
                   ;;                     (< (point) open-paren-point))
                   ;;     (- indent 1)
                   ;;   indent)
                   (if (save-excursion
                         (and t         ;(looking-at sw:indent-starters-reg)
                              (not (looking-at "\n"))
                              (not (looking-at "let\\b\\|case\\b"))
                              (progn (goto-char origpoint)
                                     (not after-comma))
                              (sw:backward-sexp)))
                       (+ (current-column) sw:indent-level)
                     (current-column)))))))))

(defun sw:inside-comment-or-string-p ()
  (if (and (boundp 'font-lock-mode) font-lock-mode)
      (in-comment-or-string-p)
    (let ((start (point)))
      (if (or (save-excursion
                (beginning-of-line)
                (search-forward "%" start t))
              (save-excursion
                (condition-case ()
                    (progn
                      (search-backward "(*")
                      (search-forward "*)")
                      (forward-char -1)	; A "*)" is not inside the comment
                      (> (point) start))
                  (error nil)))
              (save-excursion
                (condition-case ()
                    (progn
                      (search-backward "\end{spec}")
                      (search-forward "\begin{spec}")
                      (forward-char -1)	; A "*)" is not inside the comment
                      (> (point) start))
                  (error nil))))
          t
        (let ((numb 0))
          (save-excursion
            (save-restriction
              (narrow-to-region (line-beginning-position) start)
              (condition-case ()
                  (while t
                    (search-forward "\"")
                    (unless (and (not (eq (current-column) 1))
                                 (save-excursion (forward-char -2)
                                                 (looking-at "\\\\")))
                      (setq numb (1+ numb))))
                (error (if (and (not (zerop numb))
                                (not (zerop (% numb 2))))
                           t nil))))))))))
 
(defun sw:block-back ()
  (let ((case-fold-search nil))
    (skip-chars-backward " \t")
    (if (equal (char-syntax (char-before)) ?.)
        (skip-syntax-backward ".")
      (sw:backward-sexp))
    (cond ((looking-at "else\\b")
           (while (not (looking-at "if\\b"))
             (sw:block-back))
           (sw:block-back))
          ((looking-at "in\\b")
           (while (not (looking-at "let\\b"))
             (sw:block-back))
           (sw:block-back))
      ;; Here we will need to skip backward past if-then-else
      ;; and case-of expression. Please - tell me how !!
      )))

(defun sw:back-exp-until (pat)
  (sw:block-back)
  (while (not (looking-at pat))
    (sw:block-back))
  (current-column))

(defvar save-point nil)

(defun sw:find-match-backward (unquoted-this this match &optional start)
  (save-excursion
    (let ((case-fold-search nil)
          (level 1)
          (pattern (concat this "\\|" match)))
      (if start (goto-char start))
      (while (not (zerop level))
        (if (sw:re-search-backward pattern)
            (unless (in-comment-or-string-p)
              (setq level (cond
                            ((looking-at this) (1+ level))
                            ((looking-at match) (1- level)))))
          ;; The right match couldn't be found
          (progn (setq save-point (point))
                 (error (concat "Unbalanced: " unquoted-this)))))
      (point))))

(defun sw:find-match-indent (unquoted-this this match &optional indented pre-match)
  (save-excursion
    (goto-char (sw:find-match-backward unquoted-this this match))
    (when (and pre-match
               (save-excursion (forward-word -1)
                               (looking-at pre-match)))
      (forward-word -1))
    (if (or indented
            (and sw:type-of-indent
                 (not (and (looking-at (concat match " *\n"))
                           (> (- (current-column) (current-indentation)) 2)))))
        (current-column)
      (if (progn
            (beginning-of-line)
            (skip-chars-forward "\t ")
            (looking-at "|"))
          (- (current-indentation) sw:pipe-indent)
        (current-indentation)))))

(defun sw:find-match-indent-for-stad (unquoted-this this match &optional indented)
  (save-excursion
    (goto-char (sw:find-match-backward unquoted-this this match))
    (current-indentation)))

(defun sw:find-matching-starter (regexp)
  (let ((case-fold-search nil)
        (start-let-point (sw:point-inside-let-etc))
        (start-up-list (sw:up-list))
        (found t))
    (if (sw:re-search-backward regexp)
        (progn
          (condition-case ()
              (while (or (sw:inside-comment-or-string-p)
                         (/= start-up-list (sw:up-list))
                         (/= start-let-point (sw:point-inside-let-etc)))
                (re-search-backward regexp))
            (error (setq found nil)))
          found)
      nil)))

(defun sw:point-inside-let-etc ()
  (let ((case-fold-search nil) (last nil) (loop t) (found t) (start (point)))
    (save-excursion
      (while loop
        (condition-case ()
            (progn
              (re-search-forward "\\bin\\b")
              (while (sw:inside-comment-or-string-p)
                (re-search-forward "\\bin\\b"))
              (forward-char -3)
              (setq last (sw:find-match-backward "in" "\\bin\\b" "\\blet\\b" last))
              (if (< last start)
                  (setq loop nil)
                (forward-char 3)))
          (error (progn (setq found nil) (setq loop nil)))))
      (if found
          last
        0))))

(defun sw:re-search-backward (regexpr)
  (let ((case-fold-search nil) (found t))
    (if (re-search-backward regexpr nil t)
        (progn
          (condition-case ()
              (while (sw:inside-comment-or-string-p)
                (re-search-backward regexpr))
            (error (setq found nil)))
          (when found
            (re-search-forward regexpr nil t)
            (re-search-backward regexpr nil t))
          found)
      nil)))

(defun sw:re-search-forward (regexpr)
  (let ((case-fold-search nil) (found t))
    (if (re-search-forward regexpr nil t)
        (progn
          (condition-case ()
              (while (sw:inside-comment-or-string-p)
                (re-search-forward regexpr))
            (error (setq found nil)))
          found)
      nil)))

(defun sw:up-list ()
  (save-excursion
    (condition-case ()
        (progn
          (up-list 1)
          (point))
      (error 0))))

(defun sw:backward-sexp ()
  (condition-case ()
      (progn
        (let ((start (point)))
          (backward-sexp 1)
          (while (and (/= start (point)) (looking-at "(\\*"))
            (setq start (point))
            (backward-sexp 1))
          t))
    (error (forward-char -1)
           nil)))

(defun sw:comment-indent ()
  (if (looking-at "^(\\*")              ; Existing comment at beginning
      0                                 ; of line stays there.
    (save-excursion
      (skip-chars-backward " \t")
      (max (1+ (current-column))        ; Else indent at comment column
           comment-column))))           ; except leave at least one space.

;;; INSERTING PROFORMAS (COMMON SW FORMS) 

(defconst sw:form-alist
  '(("let") ("datatype")
    ("case"))
  "The list of regions to auto-insert.")

(defun sw:insert-form ()
  "Interactive short-cut to insert a common Specware form."
  (interactive)
  (let ((newline nil)                   ; Did we insert a newline
        (name (completing-read "Form to insert: (default let) "
                               sw:form-alist nil t nil)))
    ;; default is "let"
    (if (string= name "") (setq name "let"))
    ;; Insert a newline if point is not at empty line
    (sw:indent-line nil)                   ; Indent the current line
    (if (save-excursion (beginning-of-line) (skip-chars-forward "\t ") (eolp))
        ()
      (setq newline t)
      (insert "\n"))
    (condition-case ()
        (cond
         ((string= name "let") (sw:let))
         ((string= name "case") (sw:case)))
      (quit (if newline 
                (progn
                  (delete-char -1)
                  (beep)))))))

(defun sw:let () 
  "Insert a `let in'."
  (sw:let-local "let"))

(defun sw:case ()
  "Insert a case, prompting for case-expresion."
  (let (indent (expr (read-string "Case expr: ")))
    (insert (concat "case " expr))
    (sw:indent-line nil)
    (setq indent (current-indentation))
    (end-of-line)
    (if sw:case-indent
        (progn
          (insert "\n")
          (indent-to (+ 2 indent))
          (insert "of "))
      (insert " of\n")
      (indent-to (+ indent sw:indent-level)))
    (save-excursion (insert " -> "))))


(defun sw:let-local (starter)
  (let (indent)
    (insert starter)
    (sw:indent-line nil)
    (setq indent (current-indentation))
    (end-of-line)
    (insert "\n") (indent-to (+ sw:indent-level indent))
    (insert "\n") (indent-to indent)
    (insert "in\n") (indent-to (+ sw:indent-level indent))
    (forward-line -1) (end-of-line)))

(defun sw:running-specware-shell-p ()
  (and (inferior-lisp-running-p)
       (or (eq lisp-emacs-interface-type 'slime)
	   (member (sw:eval-in-lisp "(SWShell::in-specware-shell?)") '(t T)))))

(defun lisp-or-specware-command (lisp-comm spec-comm &rest argstrs)
  (simulate-input-expression
   (apply 'concat
	  (if (sw:running-specware-shell-p)
	      spec-comm lisp-comm)
	   argstrs)))

(defun lisp-or-specware-command-quiet (lisp-comm spec-comm &rest argstrs)
  (simulate-input-expression-quiet
   (apply 'concat
	  (if (sw:running-specware-shell-p)
	      spec-comm lisp-comm)
	   argstrs)))

(defun sw:process-current-file ()
  (interactive)
  (save-buffer)
  (let ((filename (sw::file-to-specware-unit-id buffer-file-name t)))
    (lisp-or-specware-command ":sw " "proc " filename)))

(defun sw::file-to-specware-unit-id (filename relativise)
  (let ((len (length filename)))
    (when (equal ".sw" (substring filename (- len 3)))
      (setq filename (substring filename 0 (- len 3))))
    (setq filename (sw::normalize-filename filename))
    (when relativise
      (setq filename (name-relative-to-swpath filename)))
    (when (eq (elt filename 1) ?:)
      (setq filename (substring filename 2)))
    filename))

(unless (fboundp 'match-string-no-properties)
  (defun match-string-no-properties (num &optional string)
  "Return string of text matched by last search, without text properties.
NUM specifies which parenthesized expression in the last regexp.
 Value is nil if NUMth pair didn't match, or there were less than NUM pairs.
Zero means the entire text matched by the whole regexp or whole string.
STRING should be given if the last search was by `string-match' on STRING."
  (if (match-beginning num)
      (if string
	  (substring-no-properties string (match-beginning num)
				   (match-end num))
	(buffer-substring-no-properties (match-beginning num)
					(match-end num))))))

(defun sw:containing-specware-unit-id (relativise)
  (save-excursion
    (end-of-line)
    (let* ((file-uid (sw::file-to-specware-unit-id buffer-file-name relativise))
	   (match (sw:re-search-backward sw:basic-unit-intro-regexp)))
      (if match
	  (let ((match_str (match-string-no-properties 1)))
            (concat file-uid "#" (if (fboundp 'substring-no-properties)
                                     ;; Gnu Emacs stupidity
                                     (substring-no-properties match_str)
                                   match_str)))
	file-uid))))

(when (and (not (featurep 'xemacs)) (not (fboundp 'replace-in-string)))
  (defun replace-in-string (str regexp rep)
    (replace-regexp-in-string regexp rep str)))

(defun convert-pathname-to-cygwin (str)
  (let ((found-index (cl-position ?: str)))
    (if (null found-index)
        str
      (let* ((dev (cl-subseq str 0 found-index))
             (dir (cl-subseq str (1+ found-index)))
             (dir (replace-in-string dir "\\\\" "/"))) 
        (if (and (> (length dir) 8) (string= "/cygwin/" (cl-subseq dir 0 8)))
            (cl-subseq dir 7)
          (concatenate 'string "/cygdrive/" (downcase dev) dir))))))

(defun to-cygwin-name (pname)
  (if cygwin?
      (convert-pathname-to-cygwin pname)
      pname))

(defun convert-pathname-from-cygwin (dir-str)
  (if (and (> (length dir-str) 10) (string= "/cygdrive/" (substring dir-str 0 10)))
      (let* ((rem-dir (cl-subseq dir-str 10))
             (i (cl-position ?/ rem-dir)))
        (if (null i)
            rem-dir
            (concat (upcase (cl-subseq rem-dir 0 i)) ":/" (cl-subseq rem-dir (+ i 1)))))
      (if (and (> (length dir-str) 6) (string= "/home/" (cl-subseq dir-str 0 6)))
          (concat "C:/cygwin" dir-str)dir-str)))

(defun from-cygwin-name (pname)
  (if cygwin?
      (convert-pathname-from-cygwin pname)
      pname))

(defun sw::normalize-filename (filename)
  (setq filename (replace-in-string filename "\\\\" "/"))
  (setq filename (replace-in-string filename "Program Files" "Progra~1"))
  (setq filename (from-cygwin-name filename))
  (when (and (> (length filename) 2)
	     (equal (cl-position ?: filename) 1)
	     (not (equal (elt filename 0) (upcase (elt filename 0)))))
    (setq filename (concat (upcase (cl-subseq filename 0 1))
			   (cl-subseq filename 1))))
  filename)

(defun get-swpath ()
  (let ((rawpath (or (sw:eval-in-lisp "(cl-user::get-swpath)") ""))
	(delim (if (or (eq window-system 'mswindows) (eq window-system 'w32) cygwin?) ?\; ?:))
	(result ())
	(specware4 (sw:eval-in-lisp "(Specware::getenv \"SPECWARE4\")"))
	pos)
    (when (member rawpath '(nil NIL))		; SWPATH not set -- be agnostic about case
      (setq rawpath specware4)
      (when (member rawpath '(nil NIL))		; SPECWARE4 not set -- be agnostic about case
	(setq rawpath "")))
    (while (setq pos (cl-position delim rawpath))
      (push (substring rawpath 0 pos) result)
      (setq rawpath (substring rawpath (+ pos 1))))
    (push rawpath result)
    (unless (member specware4 result)
      (push specware4 result))
    (nreverse result)))

(defun split-filename-for-path (filename)
  ;; Splits absolute filename into head suitable for swpath entry and
  ;; tail suitable for a uid. Note that uids cannot contain ~ or spaces
  ;; Assumes sw::normalize-filename has been called
  (let (head pos) 
    (if (eq (elt filename 1) ?:)
	(progn (setq head (cl-subseq filename 0 3))
	       (setq filename (cl-subseq filename 3)))
      (progn (setq head (cl-subseq filename 0 1))
	     (setq filename (cl-subseq filename 1))))
    (while (and (cl-position-if-not 'unitIdChar filename)
		(setq pos (cl-position ?/ filename)))
      (setq head (concat head (cl-subseq filename 0 (1+ pos))))
      (setq filename (cl-subseq filename (1+ pos))))
    (cons head (concat "/" filename))))

(unless (fboundp 'char-to-int) (defalias 'char-to-int 'identity))

(defun unitIdChar (ch)
  (or (member ch '(?/ ?_ ?#))
      (let ((num (char-to-int ch)))
	(or (and (>= num (char-to-int ?0))
		 (<= num (char-to-int ?9)))
	    (and (>= num (char-to-int ?a))
		 (<= num (char-to-int ?z)))
	    (and (>= num (char-to-int ?A))
		 (<= num (char-to-int ?Z)))))))

(defun name-relative-to-swpath (filename)
  (save-excursion
    (let ((swpath (get-swpath)))
      (loop for dir in swpath
            do (let ((dir (sw::normalize-filename dir)))
                 (if (string-equal dir
                                   (substring filename 0 (min (length dir)
                                                              (length filename))))
                     (let ((rel-filename (substring filename (length dir))))
                       (unless (cl-position-if-not 'unitIdChar rel-filename)
                         (return (if (eq (elt rel-filename 0) ?/)
                                     rel-filename
                                   (concat "/" rel-filename)))))))
            finally (let ((oldpath (sw:eval-in-lisp "(cl-user::get-swpath)"))
                          (head-dir-uid (split-filename-for-path filename)))
                      (lisp-or-specware-command
                       ":swpath " "path "
                       (if (member oldpath '(nil NIL)) "" oldpath)
                       (if (or (eq window-system 'mswindows) (eq window-system 'w32) cygwin?) ";" ":")
                       (car head-dir-uid))
                      (sleep-for 0.1) ; Just to avoid confusing output
                      (return (cdr head-dir-uid)))))))

(defun sw:process-unit (unitid)
  (interactive (list (read-from-minibuffer "Process Unit: "
					   (sw:containing-specware-unit-id t))))
  (save-buffer)
  (lisp-or-specware-command ":sw " "proc " unitid))

(defun sw:generate-lisp (compile-and-load?)
  (interactive "P")
  (save-buffer)
  (let* ((buf-name buffer-file-name)
	 (filename (sw:containing-specware-unit-id t))
	 (dir default-directory))
    (lisp-or-specware-command ":swl " "gen-lisp " filename)
    (when compile-and-load?
      (sit-for 1 t)
      (lisp-or-specware-command ":cl " "cl " dir "lisp/"
				(substring buf-name (length dir) -3)
				".lisp"))))

(defun sw:generate-compile-and-load-lisp ()
  (interactive)
  (sw:generate-lisp t))

(defun sw:generate-sliced-lisp (compile-and-load?)
  (interactive "P")
  (save-buffer)
  (let* ((buf-name buffer-file-name)
	 (filename (sw:containing-specware-unit-id t))
	 (dir default-directory))
    (lisp-or-specware-command ":swl " "gen-lisp-top " filename)
    (when compile-and-load?
      (sit-for 1 t)
      (lisp-or-specware-command ":cl " "cl " dir "lisp/"
				(substring buf-name (length dir) -3)
				".lisp"))))

(defun sw:gcl-current-file ()
  (interactive)
  (save-buffer)
  (let ((filename (sw:containing-specware-unit-id t)))
    (lisp-or-specware-command ":swll " "lgen-lisp " filename)))

(defun sw:evaluate-region (beg end)
  (interactive "r")
  (let ((filename (sw::file-to-specware-unit-id buffer-file-name t))
	(text (buffer-substring-no-properties beg end)))
    (when (or (buffer-modified-p)
	      (let ((result 
		     (sw:eval-in-lisp "(Specware::unitIDCurrentInCache? %S)"
				      buffer-file-name)))
		(member result '(nil NIL))))
      (sw:gcl-current-file)
      (sleep-for 1))			; Give :swll a chance to finish
    (unless (string-equal filename
			  (sw:eval-in-lisp "cl-user::*current-swe-spec*"))
      (lisp-or-specware-command ":swe-spec " "ctext " filename)
      (sleep-for 0.1))
    (lisp-or-specware-command ":swe " "eval " text)))

(defun sw:set-swe-spec ()
  (interactive)
  (let ((filename (sw:containing-specware-unit-id t)))
    (lisp-or-specware-command ":swe-spec " "ctext " filename)))

(defun sw:cl-unit (unitid)
  (interactive (list (read-from-minibuffer "Compile and Load Unit: "
					   (sw:containing-specware-unit-id t))))
  (save-buffer)
  (let ((temp-file-name (concat (temp-directory) "-cl-current-file")))
    (if (member (sw:eval-in-lisp
		 "(Specware::evaluateLispCompileLocal_fromLisp-2 %S '(:|Some| . %S))"
		 unitid temp-file-name)
		'(t T))
	(sw:eval-in-lisp-no-value
	   "(let (*redefinition-warnings*)
              (Specware::compile-and-load-lisp-file %S))"
	   temp-file-name)
      (message "Specware Processing Failed!"))))

(defun sw:dired-process-current-file ()
  (interactive)
  (let ((filename (sw::file-to-specware-unit-id (dired-get-filename) t)))
    (lisp-or-specware-command ":sw " "proc " filename)))

(defun sw:apropos-symbol ()
  (interactive)
  (let ((sym (sw::get-symbol-at-point)))
    (simulate-input-expression (format "(apropos \"%s\")" (upcase sym)))))

(when (boundp 'dired-mode-map)
  (define-key dired-mode-map "\C-cp" 'sw:dired-process-current-file)
  (define-key dired-mode-map "\C-c!" 'cd-current-directory))

(defun cd-current-directory ()
  (interactive)
  (lisp-or-specware-command ":cd " "cd " default-directory))

(defun sw:beginning-of-unit ()
  (interactive "")
  (unless (sw:re-search-backward sw:basic-unit-intro-regexp)
    (goto-char (point-min))
    (sw:re-search-forward "^\\sw")      ; Find any non-comment word
    (beginning-of-line))
  (beginning-of-line))

(defun sw:end-of-unit ()
  (interactive "")
  (forward-char 1)
  (if (and (sw:re-search-forward "\\s-")
           (sw:re-search-forward sw:basic-unit-intro-regexp))
      (progn (sw:re-search-backward sw:basic-unit-intro-regexp)
             (beginning-of-line)
  (forward-char -1)
  (sw:re-search-backward "\\s-")	; Find any non-comment word
  (beginning-of-line)
  (forward-line 1))
    (goto-char (point-max))))

(defvar sw:element-intro-regexp "^\\s-*\\(op\\|def\\|refine\\|type\\|axiom\\|theorem\\|proof\\|#translate\\) ")

(defun sw:beginning-of-element ()
  (interactive "")
  (unless (sw:re-search-backward sw:element-intro-regexp)
    (goto-char (point-min))
    (sw:re-search-forward "^\\sw")      ; Find any non-comment word
    (beginning-of-line))
  (beginning-of-line))

(defun sw:end-of-element ()
  (interactive "")
  (forward-char 1)
  (if (and (sw:re-search-forward "\\s-")
           (sw:re-search-forward sw:element-intro-regexp))
      (progn (sw:re-search-backward sw:element-intro-regexp)
             (beginning-of-line)
  (forward-char -1)
  (sw:re-search-backward "\\S-")	; Find any non-comment whitespace elt
  (beginning-of-line)
  (forward-line 1))
    (goto-char (point-max))))


(defun sw:next-unit ()
  (interactive "")
  (forward-char 1)
  (unless (sw:re-search-forward sw:element-intro-regexp)
    (goto-char (point-max)))
  (beginning-of-line))

(defvar *pending-specware-search-results* nil)

;;; supersedes sw:continue-meta-point
(defun sw:continue-specware-search ()
  "Continue last Specware find command."
  (interactive)
  (if (null *pending-specware-search-results*)
      (error "No more results")
    (let ((next-results (pop *pending-specware-search-results*)))
      (if (eq (car next-results) 'meta-point)
	(goto-specware-meta-point-definition
	 (cadr next-results)
	 (cddr next-results))
      (goto-specware-search-result
	 (cadr next-results)
	 (cddr next-results))))))

(defun sw:ignore-matches (all)
  (interactive "P")
  (if all
      (setq *pending-specware-search-results* nil)
    (pop *pending-specware-search-results*))
  (report-next-match-task-status))

;;;; Meta-point facility (adapted from refine-meta-point fi:lisp-find-definition)
(defun sw:meta-point (name)
  (interactive (list (car (sw::get-default-symbol "Specware locate source" t t))))
  (let* ((pr (find-qualifier-info name))
	 (qualifier (car pr))
	 (sym (cadr pr)))
    (message "Requesting info from Lisp...")
    (let ((sym (if (and (> (length sym) 3) (equal (substring sym 0 2) "|!"))
		   (substring sym 2 -1)
		 sym)))
      (let ((results (sw:eval-in-lisp (make-search-form qualifier sym)))
            (current (cons "Op" (if buffer-file-name
                                    (sw:containing-specware-unit-id nil)
                                  ""))))
	(message nil)
	(setq results (if (member results '(nil NIL Error:))
                          (list current)
                        (if (member current results)
                            (cons current (remove current results))
                          results)))
        (goto-specware-meta-point-definition sym results)))))


(defvar *end-of-def-regexp* "\\(\\b\\|\\s-\\|\\s(\\)")

(defun goto-specware-meta-point-definition (sym results)
  (let* ((def-info (car results))
         (kind (car def-info))
	 (file (cdr def-info))
	 (sort? (member kind '("Type" "Sort")))
         (theorem? (equal kind "Prop"))
         (line-num (read kind)))
    (unless (null (cdr results))
      (push (cons 'meta-point (cons sym (cdr results)))
	    *pending-specware-search-results*))
    (if (equal file "")
        (message "Definition of %s not found!" sym)
      (unless (string-equal (substring file -3) ".sw")
        (setq file (concatenate 'string (strip-hash-suffix file) ".sw")))
      (push-mark (point))
      (let ((buf
             (or (get-file-buffer file)
                 (if (not (file-exists-p file)) ; Check if file exists.
                     (error "File %s does not exist" file)
                   (if (not (file-readable-p file)) ; Check if file readable.
                       (error "File %s is not readable" file)
                     ;; Can't fail now.
                     (find-file-noselect file))))))
        (if (member major-mode '(fi:inferior-common-lisp-mode
                                 fi:lisp-listener-mode
                                 ilisp-mode))
            (other-window 1))
        (switch-to-buffer buf))
      (goto-char (point-min))
      (if (numberp line-num)
          (progn (forward-line (1- line-num))
                 (end-of-line)
                 (sw:beginning-of-element))
        (let ((qsym (regexp-quote sym)))
          (or (if sort?
                  (or (re-search-forward (concat "\\b\\(type\\|sort\\)\\s-+" qsym "\\b") nil t)
                      ;; type fie.foo
                      (re-search-forward (concat "\\b\\(type\\|sort\\)\\s-+\\w+\\." qsym "\\b") nil t))
                (if theorem?
                    (or (re-search-forward (concat "\\b\\(axiom\\|theorem\\|conjecture\\)\\s-+" qsym "\\b") nil t)
                        (re-search-forward (concat "\\b\\(axiom\\|theorem\\|conjecture\\)\\s-+\\w+\\." qsym "\\b") nil t))
                  (if (null current-prefix-arg)
                      (or (re-search-forward (concat "\\bop\\s-+" qsym *end-of-def-regexp*) nil t)
                          (re-search-forward (concat "\\bop\\s-+\\[.+\\]\\s-+" qsym *end-of-def-regexp*) nil t)
                          (re-search-forward ; op fie.foo
                           (concat "\\bop\\s-+\\w+\\." qsym *end-of-def-regexp*) nil t)
                          (re-search-forward ; op [a] fie.foo
                           (concat "\\bop\\s-+\\[.+\\]\\s-+\\w+\\." qsym *end-of-def-regexp*) nil t)
                          (re-search-forward (concat "\\bdef\\s-+" qsym *end-of-def-regexp*) nil t)
                          (re-search-forward ; def fa(a) foo
                           (concat "\\bdef\\s-+fa\\s-*(.+)\\s-+" qsym *end-of-def-regexp*) nil t)
                          (re-search-forward ; def [a] foo
                           (concat "\\bdef\\s-+\\[.+\\]\\s-+" qsym *end-of-def-regexp*) nil t)
                          (re-search-forward ; def fie.foo
                           (concat "\\bdef\\s-\\w+\\." qsym *end-of-def-regexp*) nil t)
                          )
                    (or (re-search-forward (concat "\\bop\\s-+" qsym *end-of-def-regexp*) nil t)
                        (re-search-forward (concat "\\bop\\s-+\\[.+\\]\\s-+" qsym *end-of-def-regexp*) nil t)
                        (re-search-forward ; op fie.foo
                         (concat "\\bop\\s-+\\w+\\." qsym *end-of-def-regexp*) nil t)
                        (re-search-forward ; op [a] fie.foo
                         (concat "\\bop\\s-+\\[.+\\]\\s-+\\w+\\." qsym *end-of-def-regexp*) nil t)))))
              (error "Can't find definition of %s in %s" qsym file))))
      (beginning-of-line)
      (unless (and (pos-visible-in-window-p)
                   (save-excursion (sw:end-of-element)
                                   (pos-visible-in-window-p)))
        (recenter 4))
      (report-next-match-task-status))))

(defun report-next-match-task-status ()
  (if (null *pending-specware-search-results*)
      (message "No more matches")
    (let ((search-info (car *pending-specware-search-results*)))
      (message "%s more %s for %s"
	       (length (cddr search-info))
	       (if (eq (car search-info) 'meta-point)
		   "definitions" "matches")
	       (cadr search-info)))))

;; (defvar *specware-context-str* "cl-user::*specware-global-context*")
(defvar *specware-context-str* "(MonadicStateInternal::readGlobalVar \"GlobalContext\")")

(defun make-search-form (qualifier sym)
  (if (specware-file-name-p buffer-file-name)
      (format
       "(SpecCalc::findDefiningUID-3 '(:|Qualified| %S . %S) %S %s)"
       qualifier sym (sw:containing-specware-unit-id nil)
       *specware-context-str*)
    (format
     "(SpecCalc::searchForDefiningUID-2 '(:|Qualified| %S . %S) %s)"
     qualifier sym *specware-context-str*)))

(defun specware-file-name-p (str)
  (let ((len (length str)))
    (and (> len 3)
	 (string-equal (substring str (- len 3))
		       ".sw"))))

(defvar sw::UnQualified "<unqualified>")

(defun normalize-qualifier (qual)
  (if (equal qual "SW-USER") sw::UnQualified
    qual))

(defun find-qualifier-info (name)
  (let ((colon-pos (cl-position ?: name)))
      (if colon-pos			; has a package
	  (list sw::UnQualified
		;; Don't currently used qualifier as the case is wrong
		;;(normalize-qualifier (substring name 0 colon-pos))
		(substring name (if (and (< (+ colon-pos 1) (length name))
					 (eq ?: (elt name (+ colon-pos 1))))
				    (+ colon-pos 2)
				  (+ colon-pos 1))))
	(let ((dot-pos (cl-position ?. name)))
	  (if dot-pos			; has a package
	      (list (substring name 0 dot-pos)
		    (substring name (+ dot-pos 1)))
	    (list sw::UnQualified name))))))

(defun strip-hash-suffix (str)
  (let ((pos (cl-position ?# str)))
    (if pos (substring str 0 pos)
      str)))


(defun sw:find-theorems (name)
  (interactive (list (car (sw::get-default-symbol "Specware locate theorem" t t))))
  (let* ((pr (find-qualifier-info name))
	 (qualifier (car pr))
	 (sym (cadr pr)))
    (message "Requesting info from Lisp...")
    (let ((results (sw:eval-in-lisp (make-search-theorems-form qualifier sym)))
          (current (cons "Theorem" (if buffer-file-name
                                       (sw:containing-specware-unit-id nil)
                                     ""))))
      (message nil)
      (setq results (if (member results '(nil NIL Error:))
                        (list current)
                      (if (member current results)
                          (cons current (remove current results))
                        results)))
      (goto-specware-meta-point-definition sym results))))

(defun make-search-theorems-form (qualifier sym)
  (if (specware-file-name-p buffer-file-name)
      (format
       "(SpecCalc::findTheoremLocations-3 '(:|Qualified| %S . %S) %S %s)"
       qualifier sym (sw:containing-specware-unit-id nil)
       *specware-context-str*)
    (format
     "(SpecCalc::findTheoremLocationsInEnv-2 '(:|Qualified| %S . %S) %s)"
     qualifier sym *specware-context-str*)))

(defun find-containing-spec ()
  (save-excursion
     (if (or (and (search-backward-regexp "^spec\\s-" nil t)
		  (progn (forward-char 5) t))
	     (and (search-backward-regexp "\\s-spec\\s-" nil t)
		  (progn (forward-char 4) t))
	     (search-forward-regexp "^mmodule\\s-" nil t)
	     (search-forward-regexp "\\s-module\\s-" nil t)
	     (search-forward-regexp "^spec\\s-" nil t)
	     (search-forward-regexp "\\s-spec\\s-" nil t)
	     (search-forward-regexp "^espec\\s-" nil t)
	     (search-forward-regexp "\\s-espec\\s-" nil t)
	     )
	(progn (forward-sexp)
	       (let ((end-pos (point)))
		 (forward-sexp -1)
		 (buffer-substring-no-properties (point) end-pos)))
       "")))

(defun sw::get-default-symbol (prompt &optional up-p ignore-keywords)
  (let ((symbol-at-point (sw::get-symbol-at-point up-p)))
    (let ((read-symbol
	   (read-from-minibuffer
	    (concat prompt (if symbol-at-point
			       (concat " (" symbol-at-point ")")
			     "")
		    ": "))))
      (list (if (string= read-symbol "")
		symbol-at-point
	      read-symbol)))))

(defun sw::get-symbol-at-point (&optional up-p)
  (save-excursion
    (when (and (member (char-syntax (following-char)) '(?_ ?>))
	       (eq ?w (char-syntax (preceding-char))))
      (forward-char -1))
    (let ((symbol
	   (cond
	    ((looking-at "\\sw\\|\\s_\\|\\.")
	     (while (looking-at "\\sw\\|\\s_\\|\\.\\||")
	       (forward-char 1))
	     (while (eq (char-after (- (point) 2)) ?-)
	       (forward-char -2))
	     (buffer-substring-no-properties
	      (point)
	      (progn (forward-sexp -1)
		     (while (looking-at "\\s'")
		       (forward-char 1))
		     (while (member (preceding-char)
                                    (if (eq major-mode 'specware-mode)
                                        '(?.)
                                      '(?. ?:)))
		       (forward-sexp -1))
		     (point))))
	    (t
	     (condition-case ()
		 (if up-p
		     (let ((opoint (point)))
		       (cond ((= (following-char) ?\()
			      (forward-char 1))
			     ((= (preceding-char) ?\))
			      (forward-char -1)))
		       (up-list -1)
		       (forward-char 1)
		       (if (looking-at "def")
			   (goto-char opoint)
			 (if (looking-at "funcall\\|apply")
			     (progn
			       (forward-sexp 2)
			       (backward-sexp 1)
			       (if (looking-at "#'")
				   (forward-char 2)
				 (if (looking-at "(function")
				     (progn
				       (forward-char 1)
				       (forward-sexp 2)
				       (backward-sexp 1)))))))))
	       (while (looking-at "\\sw\\|\\s_\\|\\.")
		 (forward-char 1))
	       (if (re-search-backward "\\sw\\|\\s_\\|\\." nil t)
		   (progn (forward-char 1)
			  (buffer-substring-no-properties
			   (point)
			   (progn (forward-sexp -1)
				  (while (looking-at "\\s'")
				    (forward-char 1))
				  (point))))
		 nil)
	       (error nil))))))
      (when (member symbol '(":"))
	(setq symbol nil))
      (or symbol
	  (if (and up-p (null symbol))
	      (sw::get-symbol-at-point))))))

;;;; Commands for finding Specware expressions
(defun sw:find-terms-of-type (name)
  "Find case statements splitting on type name"
  (interactive (list (car (sw::get-default-symbol "Type name" t t))))
  (let* ((pr (find-qualifier-info name))
	 (qualifier (car pr))
	 (sym (cadr pr)))
    (message "Requesting info from Lisp...")
    (let ((sym (if (and (> (length sym) 3) (equal (substring sym 0 2) "|!"))
		   (substring sym 2 -1)
		 sym)))
      (let ((results (sw:eval-in-lisp (make-find-terms-of-type-form qualifier sym))))
	(message nil)
	(if (member results '(nil NIL Error:))
	    (error "Can't find any case tests on %s." name)
	  (goto-specware-search-result sym (sw:sort-search-results results)))))))

(defun sw:find-case-dispatch-on-type (name)
  "Find case statements splitting on type name"
  (interactive (list (car (sw::get-default-symbol "Type name" t t))))
  (let* ((pr (find-qualifier-info name))
	 (qualifier (car pr))
	 (sym (cadr pr)))
    (message "Requesting info from Lisp...")
    (let ((sym (if (and (> (length sym) 3) (equal (substring sym 0 2) "|!"))
		   (substring sym 2 -1)
		 sym)))
      (let ((results (sw:eval-in-lisp (make-find-case-search-form qualifier sym))))
	(message nil)
	(if (member results '(nil NIL Error:))
	    (error "Can't find any case tests on %s." name)
	  (goto-specware-search-result sym (sw:sort-search-results results)))))))

(defun sw:find-op-references (name)
  "Find references to op"
  (interactive (list (car (sw::get-default-symbol "Op name" t t))))
  (let* ((pr (find-qualifier-info name))
	 (qualifier (car pr))
	 (sym (cadr pr)))
    (message "Requesting info from Lisp...")
    (let ((sym (if (and (> (length sym) 3) (equal (substring sym 0 2) "|!"))
		   (substring sym 2 -1)
		 sym)))
      (let ((results (sw:eval-in-lisp (make-op-references-search-form qualifier sym))))
	(message nil)
	(if (member results '(nil NIL Error:))
	    (error "Can't find any references to %s." name)
	  (goto-specware-search-result sym (sw:sort-search-results results)))))))

(defun sw:sort-search-results (results)
  (sort results
	#'(lambda (x y)
	    (if (equal (car x) (car y))
		(if (equal (cadr x) (cadr y))
		    (< (cddr x)(cddr y))
		  (< (cadr x)(cadr y)))
	      (string< (car x) (car y))))))

(defun goto-specware-search-result (sym results)
  (let* ((def-info (car results))
	 (file (car def-info))
	 (line (cadr def-info))
	 (col (cddr def-info)))
    (unless (null (cdr results))
      (push (cons 'specware-search (cons sym (cdr results)))
	    *pending-specware-search-results*))
    (push-mark (point))
    (let ((buf
	   (or (get-file-buffer file)
	       (if (not (file-exists-p file)) ; Check if file exists.
		   (error "File %s does not exist" file)
		 (if (not (file-readable-p file)) ; Check if file readable.
		     (error "File %s is not readable" file)
		   ;; Can't fail now.
		   (find-file-noselect file))))))
      (if (member major-mode '(fi:inferior-common-lisp-mode
			       fi:lisp-listener-mode
			       ilisp-mode))
	  (other-window 1))
      (switch-to-buffer buf))
    (goto-char (point-min))
    (forward-line (1- line))
    (beginning-of-line)
    (forward-chars-counting-x-symbols col)
    (let ((saved_pt (point)))
      (sw:beginning-of-element)
      (recenter 0)
      (goto-char saved_pt))
    (report-next-match-task-status)))

(defvar *top-level-unit*
  (concat (getenv "SPECWARE4") "/Applications/Specware/Specware4"))

(defun make-find-terms-of-type-form (qualifier sym)
  (format "(EditFn::findExpressionsOfType-4 %S %S %S %s)"
	  qualifier sym
	  (if (specware-file-name-p buffer-file-name)
	      (sw:containing-specware-unit-id nil)
	    *top-level-unit*)
	  *specware-context-str*))

(defun make-find-case-search-form (qualifier sym)
  (format "(EditFn::findCaseDispatchesOnType-4 %S %S %S %s)"
	  qualifier sym
	  (if (specware-file-name-p buffer-file-name)
	      (sw:containing-specware-unit-id nil)
	    *top-level-unit*)
	  *specware-context-str*))

(defun make-op-references-search-form (qualifier sym)
  (format "(EditFn::findOpReferences-4 %S %S %S %s)"
	  qualifier sym
	  (if (specware-file-name-p buffer-file-name)
	      (sw:containing-specware-unit-id nil)
	    *top-level-unit*)
	  *specware-context-str*))


(defun sw:find-importing-specs ()
  (interactive)
  (let* ((spec-name (sw:containing-specware-unit-id nil))
	 (results (sw:eval-in-lisp (format "(EditFn::findImportingSpecs-2 %S %s)"
					  spec-name
					  *specware-context-str*))))
	(message nil)
	(if (member results '(nil NIL Error:))
	    (error "Can't find any imports of %s." spec-name)
	  (goto-specware-search-result spec-name (sw:sort-search-results results)))))

;;; Object tracking

(defface sw:current-object-face
  '((((class color) (min-colors 88) (background light))
     :background "LightBlue1")
    (((class color) (min-colors 88) (background dark))
     :background "Blue4")
    (((class color) (min-colors 16) (background light))
     :background "yellow")
    (((class color) (min-colors 16) (background dark))
     :background "paleblue")
    (((class color) (min-colors 8))
     :background "cyan" :foreground "black")
    (t :inverse-video t))
  "Face used highlighting current object in Specware buffers."
  :group 'specware)

(defconst sw:current-object-overlay
  (let ((ol (make-overlay (point-min) (point-min))))
    (delete-overlay ol)
    (overlay-put ol 'face 'sw:current-object-face)
    ol)
  "An overlay which records the current secondary selection.
It is deleted when there is no secondary selection.")

(defun sw:show-object-at (spec-name pos)
  (let ((result (sw:eval-in-lisp (format "(EditFn::findObjectAtPosition-2 %S %s)"
                                         spec-name pos))))
    (delete-overlay sw:current-object-overlay)
    (when (and (consp result)
               (eq (car result) ':|Some|))
      (move-overlay sw:current-object-overlay (cadr result) (1+ (cddr result))))))

(defun sw:show-containing-object (start-event)
  (interactive "e")
  (let* ((event-info (event-start start-event))
         (curr-pos (posn-point event-info))
         (window (posn-window event-info))
         (event-buffer (window-buffer window))
         (spec-name (with-current-buffer event-buffer
                      (goto-char curr-pos)
                      (sw:containing-specware-unit-id nil)))
         (done nil)
         event mouse)
    (with-selected-window window
      (sw:show-object-at spec-name curr-pos)
      (track-mouse
        (while (not done)
          (setq event (read-event))
          (setq mouse (mouse-position))
          (cond
           ((not (consp event))
            (delete-overlay sw:current-object-overlay)
            (setq done t))
           ((memq (car event) '(mouse-movement drag-mouse-3))
            (let* ((new_pos (posn-point (event-start event))))
              (unless (eq new_pos curr-pos)
                (setq curr-pos new_pos)
                (sw:show-object-at spec-name curr-pos))))
           (t (delete-overlay sw:current-object-overlay)
              (setq done t))))))))

;;;; Prompt regexp for specware shell
(defvar *lisp-prompt-regexp*)		; make buffer local?

(defun set-comint-prompt ()
  (unless (boundp '*lisp-prompt-regexp*)
    (setq *lisp-prompt-regexp* comint-prompt-regexp))
  (when (equal *lisp-prompt-regexp* comint-prompt-regexp)
      (setq comint-prompt-regexp (concat "\\(" comint-prompt-regexp "\\|^\\* \\)")))
  (setq bridge-prompt-regexp comint-prompt-regexp)
  ;; (when (boundp 'fi::prompt-pattern)
  ;;    (setq fi::prompt-pattern comint-prompt-regexp))
  )

(defvar sw:check-unbalanced-parentheses-when-saving t
  "Check whether parens are balanced before saving a specware file."
  ;:type 'boolean
  ;:group 'specware
  )

(defun sw:check-unbalanced-parentheses-when-saving ()
  (if (and sw:check-unbalanced-parentheses-when-saving
	   (memq major-mode '(fi:common-lisp-mode fi:emacs-lisp-mode
			      fi:franz-lisp-mode specware-mode ilisp-mode)))
      (if (eq 'warn sw:check-unbalanced-parentheses-when-saving)
	  (condition-case nil
	      (progn (sw:find-unbalanced-parenthesis) nil)
	    (error
	     (message "Warning: parens are not balanced in this buffer.")
	     (ding)
	     (sit-for 2)
	     ;; so the file is written:
	     nil))
	(condition-case nil
	    (progn (sw:find-unbalanced-parenthesis) nil)
	  (error
	   ;; save file if user types "yes":
	   (not (y-or-n-p "Parens are not balanced.  Save file anyway? ")))))))

(defvar *sw-after-prompt-forms* nil)

(defvar sw:addParameter-template
  "addParameter {function: ,
parameter_position: ,
return_position: ,
parameter_name: ,
parameter_type: ,
top_function: ,
initial_value: ,
qualifier: }")

(defun sw:insert-addParameter-template ()
  (interactive)
  (let ((start_pt (point)))
    (insert sw:addParameter-template)
    (goto-char start_pt)
    (forward-word)
    (sw:indent-sexp 1)
    (forward-word)
    (forward-char 2)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; For use by error reporting routines
;; (go-to-file-position "~/specware/2000/emacs/sw-utilities.el" 7 4)

(defun goto-file-position (file line col)
  (let ((full-file (expand-file-name file
				     (with-current-buffer sw:common-lisp-buffer-name
				       default-directory))))
    (unless (equal (buffer-file-name) full-file)
      (find-file-other-window-0 full-file))
    (goto-char (point-min))
    (forward-line (1- line))
    (when (> col 0)
      (forward-chars-counting-x-symbols col))))

;;; Command for showing error point in specware shell
(defun show-error-on-new-input (col skip_command?)
  (if (eq lisp-emacs-interface-type 'slime)
      (push `(show-error-on-new-input-real ,col ,skip_command?) *sw-after-prompt-forms*)
    (progn (sit-for 0.5 t)   ; Allow error message to be printed
	   (show-error-on-new-input-real col skip_command?)))
  nil)

(defun show-error-on-new-input-real (col skip_command?)
  (goto-char (point-max))
  (previous-input-line)
  (if (eq (current-column) 0)
      (delete-char -1))
  (if (eq lisp-emacs-interface-type 'slime)
      (goto-char slime-repl-input-start-mark)
    (comint-bol nil))
  (when skip_command? (forward-sexp 1))
  (when (looking-at "[\t \n\014]")                ; Skip to beginning of non-whitespace
    (re-search-forward "[^\t \n\014]")
    (forward-char -1))
  (forward-chars-counting-x-symbols (max 0 col))
  ())


(defun forward-chars-counting-x-symbols (i)
  (if (or (not sw:use-x-symbol) (not x-symbol-mode) (< i 1))
      (forward-char i)
    (while (> i 0) 
      (let ((x-symbol-char (cdr (x-symbol-charsym-after (point)))))
	(decf i (if (null x-symbol-char)
		    1
		  (length (x-symbol-expansion x-symbol-char))))
	(forward-char 1)))))

(defun x-symbol-expansion (x-symbol-char)
  (car (x-symbol-default-valid-charsym x-symbol-char)))

;;; About Specware command implementation
(defvar specware-logo
  (if (featurep 'xemacs)
      (make-glyph `[xpm :file ,(concat *specware*
				       "/Library/IO/Emacs/specware_logo.xpm")])
    `(image :type xpm :file ,(concat *specware*
				     "/Library/IO/Emacs/specware_logo.xpm"))))

(defun goto-specware-web-page (&rest ign)
  (browse-url "http://specware.org/"))

(defun goto-specware-release-notes (&rest ign)
  (browse-url
   (if (inferior-lisp-running-p)
       (format "http://specware.org/release-notes-%s-%s.html"
	       (sw:eval-in-lisp "cl-user::*Specware-Major-Version-String*")
	       (sw:eval-in-lisp "cl-user::*Specware-Patch-Level*"))
     "http://specware.org/news.html")))

(defface about-specware-link-face
  '((((class color) (background dark))
     (:foreground "blue" :underline t))
    ;; blue4 is hardly different from black on windows.
    (((class color) (background light) (type mswindows))
     (:foreground "blue3" :underline t))
    (((class color) (background light))
     (:foreground "blue4" :underline t))
    (((class grayscale) (background light))
     (:foreground "DimGray" :bold t :italic t :underline t))
    (((class grayscale) (background dark))
     (:foreground "LightGray" :bold t :italic t :underline t))
    (t (:underline t)))
  "Face used for links in the Specware About page."
  :group 'specware)

;; Derived from about.el functions
;; I don't use the about functions because they are different in different 
;; versions of xemacs
(defvar about-left-margin 3)
(defvar widget-button-face)

(defun about-specware-get-buffer (name)
  (cond ((get-buffer name)
	 (switch-to-buffer name)
         (goto-char (point-min))
         (forward-line 1)
	 name)
	(t
	 (switch-to-buffer name)
	 (buffer-disable-undo)
	 ;(set-specifier left-margin-width about-left-margin (current-buffer))
	 nil)))

(defun about-specware-center (str)
  (let ((n (- (length str) about-left-margin)))
    (make-string (if (natnump n) n 0) ?\ )))

(defun about-specware-finish-buffer ()
  (goto-char (point-max))
  (insert "\n\n\n")
  (insert-button "Bury"
                                        ;  'face 'Bold
                                        ;  'help-echo "mouse-1, see Specware Web Page"
                 'action (lambda (_button) (bury-buffer))
                 'follow-link t)
  (insert " this buffer and return to previous.\n")
  (center-line)
  (use-local-map (make-sparse-keymap))
  (local-set-key "q" 'bury-buffer)
  (local-set-key "l" 'bury-buffer)
  (local-set-key " " 'scroll-up)
  (local-set-key [backspace] 'scroll-down)
  (local-set-key "\177" 'scroll-down)
 ; (widget-setup)
  (goto-char (point-min))
  (read-only-mode)
  (set-buffer-modified-p nil))

(defun about-specware ()
  "Describe the Specware System"
  (interactive)
  (unless (about-specware-get-buffer "*About Specware*")
    (let* ((image-width (and specware-logo (car (image-size specware-logo))))
           (fill-column (window-width)))
      (when (> fill-column image-width)
	;; Center the image in the window.
	(insert (propertize " " 'display
			    `(space :align-to (+ center (-1.0 . ,specware-logo)))))

	;; Insert the image with a help-echo and a link.
	(make-button (prog1 (point) (insert-image specware-logo)) (point)
		     'face 'default
		     'help-echo "mouse-1, RET: Browse http://www.specware.org/"
		     'action (lambda (_button) (goto-specware-web-page))
		     'follow-link t)
	(insert "\n\n")))
    (when (inferior-lisp-running-p)
      (let* ((specware-major-version (sw:eval-in-lisp "cl-user::*Specware-Major-Version*"))
	     (specware-minor-version (sw:eval-in-lisp "cl-user::*Specware-Minor-Version*"))
	     (specware-patch-number (sw:eval-in-lisp
				     "cl-user::*Specware-Patch-Level*"))
	     (specware-version (format "Version %s.%s.%s"
				       specware-major-version
				       specware-minor-version
				       specware-patch-number)))
        (insert "\n\n")
        (insert (about-specware-center specware-version))
	(insert specware-version)
        (center-line)
        ;; (insert "\n\n")
        ;; (make-button (prog1 (point) (insert "Specware Release Notes ") (insert specware-version)) (point)
	;; 	     'face 'bold
	;; 	     'help-echo "mouse-2, see Specware Version Release Notes"
	;; 	     'action (lambda (_button) (goto-specware-release-notes))
	;; 	     'follow-link t)
        ;; (center-line)
        ))
    (insert "\n\n")
    (insert-button "Specware"
                   'face 'about-specware-link-face
                   'action 'goto-specware-web-page
                   'follow-link t)
    (insert " is a leading-edge automated software development system 
that allows users to precisely specify the desired functionality of 
their applications and to generate provably correct code based on 
these requirements. At the core of the design process in Specware 
lies stepwise refinement, in which users begin with a simple, abstract 
model of their problem and iteratively refine this model until it 
uniquely and concretely describes their application.")
    (center-line -7)
    (insert "\n")
    (about-specware-finish-buffer)
    (goto-char (point-min))
    (forward-line 1)))

;;; Run test harness
(defun sw:run-test-harness (non-rec)
  ;; Prefix arg means don't recur on sub-directories
  (interactive "P")
  (unless (inferior-lisp-running-p)
    (run-specware4)
    (sit-for 1 t))
  (simulate-input-expression
   (if non-rec
       (format "(Specware-Test::run-test-directories %S)"
	       default-directory)
     (format "(Specware-Test::run-test-directories-rec %S)"
	     default-directory))))

;;; For Gnu Emacs. This will be already defined in xemacs
(defvar display-warning-suppressed-classes ())

;;; Isabelle Interface
(defun sw:convert-spec-to-isa-thy (arg)
  "Converts Spec to Isabelle/HOL theory.
With an argument of 1 it doesn't convert imports.
With any other argument it simplifies terms."
  (interactive "P")
  (save-buffer)
  (let* ((filename (sw:containing-specware-unit-id t))
	 (thy-file (sw:eval-in-lisp
		    (format
		     "(let ((TypeObligations::generateTerminationConditions? nil)
                            (TypeObligations::generateExhaustivityConditions? t)
                            (Simplify::simplifyUsingSubtypes? t)
                            (Prover::treatNatSpecially? nil)
                            (Utilities::namedTypesRaised? t))
                        (IsaTermPrinter::printUIDtoThyFile-3 %S %s %s))"
		     filename
		     (if (eq arg 1) "nil" "t")
                     (if (and arg (not (eq arg 1))) "nil" "t"))))
	 (revert-without-query (cons ".*.thy" revert-without-query))
	 (display-warning-suppressed-classes (cons 'warning
						   display-warning-suppressed-classes)))
    (if (string-match "Error: Unknown UID" thy-file)
        (error "Error processing spec %s" filename)
      (let ((buf (find-file-noselect thy-file t)))
        (kill-buffer buf)		; Because of x-symbol problems if it already exists
        ;(sw:add-specware-to-isabelle-path)
        (find-file-other-window-0 (to-cygwin-name thy-file))
        (when (fboundp 'proof-unregister-buffer-file-name)
          (proof-unregister-buffer-file-name t))))))

(defun sw:regenerate-isa-theories-for-uid ()
  "Regenerate Isabelle/HOL theories for unit."
  (interactive)
  (save-buffer)
  (let* ((filename (sw:containing-specware-unit-id t))
	 (thy-file (sw:eval-in-lisp
		    (format
		     "(let ((TypeObligations::generateTerminationConditions? nil)
                            (TypeObligations::generateExhaustivityConditions? t)
                            (Simplify::simplifyUsingSubtypes? t)
                            (Prover::treatNatSpecially? nil)
                            (Utilities::namedTypesRaised? t))
                        (IsaTermPrinter::deleteThyFilesForUID %S)
                        (IsaTermPrinter::printUIDtoThyFile-3 %S t nil))"
		     filename filename)))
	 (revert-without-query (cons ".*.thy" revert-without-query))
	 (display-warning-suppressed-classes (cons 'warning
						   display-warning-suppressed-classes)))
    (if (string-match "Error: Unknown UID" thy-file)
        (error "Error processing spec %s" filename)
      (let ((buf (find-file-noselect thy-file t)))
        (kill-buffer buf)		; Because of x-symbol problems if it already exists
        ;(sw:add-specware-to-isabelle-path)
        (find-file-other-window-0 (to-cygwin-name thy-file))
        (when (fboundp 'proof-unregister-buffer-file-name)
          (proof-unregister-buffer-file-name t))))))

;; Version of find-file-other-window that doesn't create new windows willy-nilly on Gnu Emacs
(defun find-file-other-window-0 (filename)
  (let ((value (find-file-noselect filename)))
    (pop-to-buffer value t)))

(defun sw:add-specware-to-isabelle-path ()
  (when (fboundp 'proof-shell-invisible-command)
    (proof-shell-ready-prover)
    ;(proof-cd-sync)
    (proof-assistant-invisible-command-ifposs   ;proof-shell-invisible-command
     (format "ML_val  {* ThyLoad.add_path \"%s/Library/Isa/\" *}"
	     (getenv "SPECWARE4")))))

;(sw:add-specware-to-isabelle-path)

;;; Haskell generation
(defun sw:convert-top-spec-to-haskell (non-recursive?)
    "Generates Haskell code for spec assuming spec is top-level.
With an argument, it doesn't convert imports."
  (interactive "P")
  (sw:convert-spec-to-haskell non-recursive? t))

(defun sw:convert-spec-to-haskell (non-recursive? &optional slicing?)
  "Generates Haskell code for spec.
With an argument, it doesn't convert imports."
  (interactive "P")
  (save-buffer)
  (let* ((filename (sw:containing-specware-unit-id t))
	 (thy-file (sw:eval-in-lisp
		    (format
		     "(Haskell::printUIDtoHaskellFile-3 %S %s %s)"
		     filename
                     (if slicing? "t" "nil")
		     (if non-recursive? "nil" "t"))))
	 (revert-without-query (cons ".*.thy" revert-without-query))
	 (display-warning-suppressed-classes (cons 'warning
						   display-warning-suppressed-classes)))
    (if (string-match "Error: Unknown UID" thy-file)
        (error "Error processing spec %s" filename)
      (let ((buf (find-file-noselect thy-file t)))
        (kill-buffer buf)		; Because of x-symbol problems if it already exists
        (find-file-other-window-0 (to-cygwin-name thy-file))
        (when (fboundp 'proof-unregister-buffer-file-name)
          (proof-unregister-buffer-file-name t))))))

(defvar haskell-ghci-program-args)
(defvar haskell-program-name)

(let ((path (format (if (or (eq window-system 'mswindows) (eq window-system 'w32))
                        "\"-i.;%s/Library/Haskell\"" "-i.:%s/Library/Haskell")
                    (replace-in-string (getenv "SPECWARE4") "\\\\" "/"))))
  (unless (boundp 'haskell-ghci-program-args)
    (setq haskell-ghci-program-args nil))
  (unless (member path haskell-ghci-program-args)
    (push path haskell-ghci-program-args))
  ;; New interface
  (unless nil; (boundp 'haskell-program-name)
    (setq haskell-program-name (concat "ghci " path))))

(defun sw:specware-mode-folding ()
  (folding-add-to-marks-list 'specware-mode "%{{{" "%}}}" nil t))

(add-hook 'folding-load-hook 'sw:specware-mode-folding)

;(add-hook 'proof-activate-scripting-hook 'sw:add-specware-to-isabelle-path t)

;;; & do the user's customisation

(add-hook 'sw:specware-load-hook 'specware-mode-version t)

(run-hooks 'sw:specware-load-hook)

;;; specware-mode.el has just finished.

