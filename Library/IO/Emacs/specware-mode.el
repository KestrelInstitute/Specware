;;; specware-mode.el. Major mode for editing Specware
;;; Adapted from sml-mode
;; Copyright (C) 1989, Lars Bo Nielsen; 1994, Matthew J. Morley

;; (autoload 'specware-mode "specware-mode" "Major mode for editing Specware specs." t)
;;
;; Files ending in ".sw" are considered by emacs hereafter to
;; be Specware source, so put their buffers into specware-mode automatically

;;; (setq auto-mode-alist
;;;       (cons '("\\.sl$" . specware-mode) auto-mode-alist))

;; Here's an example of setting things up in the specware-mode-hook:

;; (setq specware-mode-hook
;;       '(lambda() "Specware mode hacks"
;;          (setq sl-indent-level 2         ; conserve on horiz. space
;;                indent-tabs-mode nil)))    ; whatever

;; specware-mode-hook is run whenever a new specware-mode buffer is created.
;; There is an specware-load-hook too, which is only run when this file is
;; loaded. One use for this hook is to select your preferred
;; highlighting scheme, like this:

;; Alternatively, you can (require 'sl-font) which uses the font-lock
;; package instead. 

;; Finally, there is also an inferior-specware-mode-hook -- see
;; sl-proc.el. For more information consult the mode's *info* tree.

;;; VERSION STRING

(defconst specware-mode-version-string
  "specware-mode, Version 0.2")

(provide 'specware-mode)

;;; VARIABLES CONTROLLING THE MODE

(defvar sl-indent-level 2
  "*Indentation of blocks in Specware.")

(defvar sl-pipe-indent -2
  "*Extra (usually negative) indentation for lines beginning with |.")

(defvar sl-case-indent t
  "*How to indent case-of expressions.
    If t:   case expr                     If nil:   case expr of
              of exp1 -> ...                            exp1 -> ...
               | exp2 -> ...                          | exp2 -> ...

The first seems to be the standard in SL/NJ, but the second
seems nicer...")

(defvar sl-nested-if-indent t
  "*Determine how nested if-then-else will be formatted:
    If t: if exp1 then exp2               If nil:   if exp1 then exp2
          else if exp3 then exp4                    else if exp3 then exp4
          else if exp5 then exp6                         else if exp5 then exp6
               else exp7                                      else exp7")

(defvar sl-type-of-indent t
  "*How to indent `let' `struct' etc.
    If t:  fun foo bar = let              If nil:  fun foo bar = let
                             val p = 4                 val p = 4
                         in                        in
                             bar + p                   bar + p
                         end                       end

Will not have any effect if the starting keyword is first on the line.")

(defvar sl-electric-semi-mode nil
  "*If t, `\;' will self insert, reindent the line, and do a newline.
If nil, just insert a `\;'. (To insert while t, do: C-q \;).")

(defvar sl-paren-lookback 1000
  "*How far back (in chars) the indentation algorithm should look
for open parenthesis. High value means slow indentation algorithm. A
value of 1000 (being the equivalent of 20-30 lines) should suffice
most uses. (A value of nil, means do not look at all)")

(defvar specware-mode-hook nil
  "*This hook is run when specware-mode is loaded, or a new specware-mode buffer created.
This is a good place to put your preferred key bindings.")

(defvar specware-load-hook nil
  "*This hook is only run when specware-mode is loaded.")

;;; CODE FOR SPECWARE-MODE 

(defun sl-indent-level (&optional indent)
   "Allow the user to change the block indentation level. Numeric prefix 
accepted in lieu of prompting."
   (interactive "NIndentation level: ")
   (setq sl-indent-level indent))

(defun sl-pipe-indent (&optional indent)
  "Allow to change pipe indentation level (usually negative). Numeric prefix
accepted in lieu of prompting."
   (interactive "NPipe Indentation level: ")
   (setq sl-pipe-indent indent))

(defun sl-case-indent (&optional of)
  "Toggle sl-case-indent. Prefix means set it to nil."
  (interactive "P")
  (setq sl-case-indent (and (not of) (not sl-case-indent)))
  (if sl-case-indent (message "%s" "true") (message "%s" nil)))

(defun sl-nested-if-indent (&optional of)
  "Toggle sl-nested-if-indent. Prefix means set it to nil."
  (interactive "P")
  (setq sl-nested-if-indent (and (not of) (not sl-nested-if-indent)))
  (if sl-nested-if-indent (message "%s" "true") (message "%s" nil)))

(defun sl-type-of-indent (&optional of)
  "Toggle sl-type-of-indent. Prefix means set it to nil."
  (interactive "P")
  (setq sl-type-of-indent (and (not of) (not sl-type-of-indent)))
  (if sl-type-of-indent (message "%s" "true") (message "%s" nil)))

(defun sl-electric-semi-mode (&optional of)
  "Toggle sl-electric-semi-mode. Prefix means set it to nil."
  (interactive "P")
  (setq sl-electric-semi-mode (and (not of) (not sl-electric-semi-mode)))
  (message "%s" (concat "Electric semi mode is " 
                   (if sl-electric-semi-mode "on" "off"))))

(defun insert-circle-s () (interactive) (insert "§"))
(defun insert-open-quote () (interactive) (insert "«"))
(defun insert-close-quote () (interactive) (insert "»"))
(defun insert-degree () (interactive) (insert "°"))
(defun insert-center-dot () (interactive) (insert "·"))
(defun insert-mu () (interactive) (insert "µ"))
(defun insert-times () (interactive) (insert "×"))
(defun insert-beta () (interactive) (insert "ß"))
(defun insert-negation () (interactive) (insert "¬"))
(defun insert-emptyset () (interactive) (insert "Ø"))



;;; BINDINGS: should be common to the source and process modes...

(defun install-sl-keybindings (map)
  ;; Text-formatting commands:
  (define-key map "\C-c\C-m" 'sl-insert-form)
  (define-key map "\M-|"     'sl-electric-pipe)
  (define-key map "\;"       'sl-electric-semi)
  (define-key map "\M-\t"    'sl-back-to-outer-indent)
  (define-key map "\C-j"     'newline-and-indent)
  (define-key map "\177"     'backward-delete-char-untabify)
  (define-key map [backspace] 'backward-delete-char-untabify)
  (define-key map "\C-\M-\q" 'sl-indent-sexp)
  (define-key map "\C-\M-\\" 'sl-indent-region)
  (define-key map "\t"       'sl-indent-line) ; ...except this one

  (define-key map "\M-."     'specware-meta-point)
  (define-key map "\M-,"     'continue-specware-meta-point)
  (define-key map "\C-cl"    'switch-to-lisp)
  (define-key map "\M-*"     'switch-to-lisp)
  (define-key map "\C-?"     'backward-delete-char-untabify)
  (define-key map "\C-c%"    'extract-sexp)
  (define-key map "\C-c;"    'comment-region)

					          ; Franz binding
  (define-key map "\C-cs"    'insert-circle-s)    ; Process to debug
  (define-key map "\C-c`"    'insert-open-quote)
  (define-key map "\C-c'"    'insert-close-quote)
  (define-key map "\C-cd"    'insert-degree)      ; Describe symbol
  (define-key map "\C-cu"    'insert-mu)
  (define-key map "\C-ct"    'insert-center-dot)  ; trace
  (define-key map "\C-cx"    'insert-times)
  (define-key map "\C-cb"    'insert-beta)
  (define-key map "\C-cn"    'insert-negation)
  (define-key map "\C-ce"    'insert-emptyset)



  ;; Process commands added to specware-mode-map -- these should autoload
;;;  (define-key map "\C-c\C-s" 'switch-to-sl)
;;;  (define-key map "\C-c\C-l" 'sl-load-file)
;;;  (define-key map "\C-c\C-r" 'sl-send-region)
;;;  (define-key map "\C-c\C-b" 'sl-send-buffer)
;;;  (define-key map "\C-c`"    'sl-next-error)
  )

(defvar sl-no-doc
  "This function is part of sl-proc, and has not yet been loaded.
Full documentation will be available after autoloading the function."
  "Documentation for autoload functions.")

;;;(autoload 'switch-to-sl   "sl-proc"   sl-no-doc t)
;;;(autoload 'sl             "sl-proc"   sl-no-doc t)
;;;(autoload 'sl-load-file   "sl-proc"   sl-no-doc t)
;;;(autoload 'sl-send-region "sl-proc"   sl-no-doc t)
;;;(autoload 'sl-send-buffer "sl-proc"   sl-no-doc t)
;;;(autoload 'sl-next-error  "sl-proc"   sl-no-doc t)

(defvar specware-mode-map nil "The mode map used in specware-mode.")
(cond ((not specware-mode-map)
       (setq specware-mode-map (make-sparse-keymap))
       (install-sl-keybindings specware-mode-map)))

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
  (modify-syntax-entry ?\(      "()5"   specware-mode-syntax-table)
  (modify-syntax-entry ?\)      ")(8"   specware-mode-syntax-table)
  (modify-syntax-entry ?\[      "(]"    specware-mode-syntax-table)
  (modify-syntax-entry ?\]      ")["    specware-mode-syntax-table)
  (modify-syntax-entry ?{       "(}"    specware-mode-syntax-table)
  (modify-syntax-entry ?}       "){"    specware-mode-syntax-table)
  (modify-syntax-entry ?\*      ". 67"  specware-mode-syntax-table)
  (modify-syntax-entry ?\"      "\""    specware-mode-syntax-table)
  (modify-syntax-entry ?        " "     specware-mode-syntax-table)
  (modify-syntax-entry ?\t      " "     specware-mode-syntax-table)
  (modify-syntax-entry ?\%      "<   "     specware-mode-syntax-table)
  (modify-syntax-entry ?\n      ">   "     specware-mode-syntax-table)
  (modify-syntax-entry ?\f      " "     specware-mode-syntax-table)
  (modify-syntax-entry ?\'      "w"     specware-mode-syntax-table)
  (modify-syntax-entry ?\_      "w"     specware-mode-syntax-table)
  (modify-syntax-entry ?\-      "w"     specware-mode-syntax-table)
  (modify-syntax-entry ?\?      "w"     specware-mode-syntax-table))

(defun specware-mode ()
  "Major mode for editing Specware code.
Tab indents for Specware code.
Comments are delimited with (* ... *).
Blank lines and form-feeds separate paragraphs.
Delete converts tabs to spaces as it moves back.

For information on running an inferior Specware process, see the documentation
for inferior-specware-mode (set this up with \\[sl]).

Customization: Entry to this mode runs the hooks on specware-mode-hook.

Variables controlling the indentation
=====================================

Seek help (\\[describe-variable]) on individual variables to get current settings.

sl-indent-level (default 4)
    The indentation of a block of code.

sl-pipe-indent (default -2)
    Extra indentation of a line starting with \"|\".

sl-case-indent (default nil)
    Determine the way to indent case-of expression.

sl-nested-if-indent (default nil)
    Determine how nested if-then-else expressions are formatted.

sl-type-of-indent (default t)
    How to indent let, etc.
    Will not have any effect if the starting keyword is first on the line.

sl-electric-semi-mode (default nil)
    If t, a `\;' will reindent line, and perform a newline.

sl-paren-lookback (default 1000)
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
  (run-hooks 'specware-mode-hook))           ; Run the hook

;; What is the deal? This is a symbol, but it's also defined as a var?

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
  (setq indent-line-function 'sl-indent-line)
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
  (setq comment-indent-function 'sl-comment-indent)
  (make-local-variable 'font-lock-fontify-region-function)
  (setq font-lock-fontify-region-function
        'specware-font-lock-fontify-region-function)
  ;;
  ;; Adding these will fool the matching of parens. I really don't
  ;; know why. It would be nice to have comments treated as
  ;; white-space.
  ;; 
  ;;(make-local-variable 'parse-sexp-ignore-comments)
  ;;(setq parse-sexp-ignore-comments t)
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

(unless (and (boundp 'lazy-shot-step-size)
	     lazy-shot-step-size
	     (> lazy-shot-step-size 1024))
  (setq lazy-shot-step-size 4096))

;;; ??
(defconst sl-pipe-matchers-reg
  "\\bcase\\b\\|\\bfn\\b\\|\\bfun\\b\
\\|\\bdatatype\\b"
  "The keywords a `|' can follow.")

(defun sl-electric-pipe ()
  "Insert a \"|\". 
Depending on the context insert the name of function, a \"->\" etc."
  (interactive)
  (let ((case-fold-search nil)          ; Case sensitive
        ;(here (point))
        (match (save-excursion
                 (sl-find-matching-starter sl-pipe-matchers-reg)
                 (point)))
        (tmp "  -> ")
        (case-or-handle-exp t))
    (if (/= (save-excursion (beginning-of-line) (point))
            (save-excursion (skip-chars-backward "\t ") (point)))
        (insert "\n"))
    (insert "|")
    (save-excursion
      (goto-char match)
      (cond
       ;; It was a function, insert the function name
       ((looking-at "fun\\b")
        (setq tmp (concat " " (buffer-substring
                               (progn (forward-char 3)
                                      (skip-chars-forward "\t\n ") (point))
                               (progn (forward-word 1) (point))) " "))
        (setq case-or-handle-exp nil))
       ;; It was a datatype, insert nothing
       ((looking-at "datatype\\b\\|abstype\\b")  ; ??
        (setq tmp " ") (setq case-or-handle-exp nil))
       ;; If it is an and, then we have to see what is was
       ((looking-at "and\\b")  ; ??
        (let (isfun)
          (save-excursion
            (condition-case ()
                (progn
                  (re-search-backward "datatype\\b\\|abstype\\b\\|fun\\b")
                  (setq isfun (looking-at "fun\\b")))
              (error (setq isfun nil))))
          (if isfun
              (progn
                (setq tmp
                      (concat " " (buffer-substring
                                   (progn (forward-char 3)
                                          (skip-chars-forward "\t\n ") (point))
                                   (progn (forward-word 1) (point))) " "))
                (setq case-or-handle-exp nil))
            (setq tmp " ") (setq case-or-handle-exp nil))))))
    (insert tmp)
    (sl-indent-line)
    (beginning-of-line)
    (skip-chars-forward "\t ")
    (forward-char (1+ (length tmp)))
    (if case-or-handle-exp
        (forward-char -4))))

(defun sl-electric-semi ()
  "Inserts a \;.
If variable sl-electric-semi-mode is t, indent the current line, insert 
a newline, and indent."
  (interactive)
  (insert "\;")
  (if sl-electric-semi-mode
      (reindent-then-newline-and-indent)))

;;; INDENTATION !!!

(defun sl-mark-function ()
  "Synonym for mark-paragraph -- sorry.
If anyone has a good algorithm for this..."
  (interactive)
  (mark-paragraph))

(defun sl-indent-sexp (n)
  (interactive "p")
  (sl-indent-region (save-excursion (forward-line 1) (point))
		    (save-excursion (forward-sexp (or n 1)) (point))))

(defun sl-indent-region (begin end)
  "Indent region of Specware code."
  (interactive "r")
  (message "Indenting region...")
  (save-excursion
    (goto-char end) (setq end (point-marker)) (goto-char begin)
    (while (< (point) end)
      (skip-chars-forward "\t\n ")
      (sl-indent-line)
      (end-of-line))
    (move-marker end nil))
  (message "Indenting region... done"))

(defun sl-indent-line ()
  "Indent current line of Specware code."
  (interactive)
  (let ((indent (sl-calculate-indentation)))
    (if (/= (current-indentation) indent)
        (save-excursion                 ;; Added 890601 (point now stays)
          (let ((beg (progn (beginning-of-line) (point))))
            (skip-chars-forward "\t ")
            (delete-region beg (point))
            (indent-to indent))))
    ;; If point is before indentation, move point to indentation
    (if (< (current-column) (current-indentation))
        (skip-chars-forward "\t "))))

(defun sl-back-to-outer-indent ()
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

(defconst sl-indent-starters-reg  ; ??
  "case\\b\\|datatype\\b\
\\|else\\b\\|fun\\b\\|def\\b\\|if\\b\
\\|in\\b\\|infix\\b\\|infixr\\b\
\\|nonfix\\b\\|of\\b\\|open\\b\\|raise\\b\\|sig\\b\\|signature\\b\
\\|struct\\b\\|structure\\b\\|then\\b\\|\\btype\\b\\|val\\b\
\\|specmap\\b\\|progmap\\b\\|while\\b\\|withtype\\b\
\\|spec\\b\\|espec\\b\\|espec-refinement\\b\\|module\\b\
\\|\\(initial[ \\t]*\\|final[ \\t]*\\|\\b\\)\\(mode\\|stad\\)\\b\\|prog\\b\\|step\\b"
  "The indentation starters. The next line will be indented.")

(defconst sl-starters-reg  ; ??
  "\\babstraction\\b\\|\\babstype\\b\\|\\bdatatype\\b\
\\|\\bdef\\b\\|\\bfun\\b\\|\\bfunctor\\b\\|\\blocal\\b\
\\|\\binfix\\b\\|\\binfixr\\b\\|\\bsharing\\b\
\\|\\bnonfix\\b\\|\\bopen\\b\\|\\bsignature\\b\\|\\bstructure\\b\
\\|\\btype\\b\\|\\bval\\b\\|\\bwithtype\\b"
  "The starters of new expressions.")

(defconst sl-end-starters-reg  ; ??
  "\\blet\\b\\|\\blocal\\b\\|\\bsig\\b\\|\\bstruct\\b\\|\\bwith\\b"
  "Matching reg-expression for the \"end\" keyword.")

(defconst sl-starters-indent-after
  "struct\\b"
  "Indent after these.")

(defun sl-calculate-indentation ()
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
          (if (eobp) 0 (sl-calculate-indentation)))
         ;; Continued string ? (Added 890113 lbn)
         ((looking-at "\\\\")
          (save-excursion
            (if (save-excursion (previous-line 1)
                                (beginning-of-line)
                                (looking-at "[\t ]*\\\\"))
                (progn (previous-line 1) (current-indentation))
            (if (re-search-backward "[^\\\\]\"" nil t)
                (1+ (current-indentation))
              0))))
         ;; Are we looking at a case expression ?
         ((looking-at "|.*->")
          (sl-skip-block)
          (if (looking-at "of\\b")
	      ;; "case of | ..."  treat like "of"
	      (progn (sl-re-search-backward "\\bcase\\b")
		     (+ (current-column) 2))
	    (sl-re-search-backward "->")
	    ;; Dont get fooled by fn _ -> in case statements (890726)
	    ;; Changed the regexp a bit, so fn has to be first on line,
	    ;; in order to let the loop continue (Used to be ".*\bfn....")
	    ;; (900430).
	    (let ((loop t))
	      (while (and loop (save-excursion
				 (beginning-of-line)
				 (looking-at "[^ \t]+\\bfn\\b.*->")))
		(setq loop (sl-re-search-backward "->"))))
	    (beginning-of-line)
	    (skip-chars-forward "\t ")
	    (cond
	     ((looking-at "|") (current-indentation))
	     ((and sl-case-indent (looking-at "of\\b"))
	      (1+ (current-indentation)))
	     ((looking-at "fn\\b") (1+ (current-indentation)))
	     ((looking-at "handle\\b") (+ (current-indentation) 5))
	     (t (+ (current-indentation) sl-pipe-indent)))))
         ((looking-at "and\\b")
          (if (sl-find-matching-starter sl-starters-reg)
              (current-column)
            0))
         ((looking-at "in\\b")          ; Match the beginning let/local
          (sl-find-match-indent "in" "\\bin\\b" "\\blocal\\b\\|\\blet\\b"))
	 ((looking-at "end-spec\\b")
	  (sl-find-match-indent "end-spec" "\\bend-spec\\b" "\\bspec\\b"))
	 ((looking-at "end-espec\\b")
	  (sl-find-match-indent "end-espec" "\\bend-espec\\b" "\\bespec\\b"))
	 ((looking-at "end-espec-refinement\\b")
	  (sl-find-match-indent "end-espec-refinement" "\\bend-espec-refinement\\b"
				"\\bespec-refinement\\b"))
	 ((looking-at "end-specmap\\b")
	  (sl-find-match-indent "end-specmap" "\\bend-specmap\\b" "\\bspecmap\\b"))
	 ((looking-at "end-with\\b")
	  (sl-find-match-indent "end-with" "\\bend-with\\b" "\\bwith\\b"))
	 ((looking-at "end-progmap\\b")
	  (sl-find-match-indent "end-progmap" "\\bend-progmap\\b" "\\bprogmap\\b"))
	 ((looking-at "end-module\\b")
	  (sl-find-match-indent "end-module" "\\bend-module\\b" "\\bmodule\\b"))
	 ((looking-at "end-while\\b")
	  (sl-find-match-indent "end-while" "\\bend-while\\b" "\\bwhile\\b"))
	 ((looking-at "end-mode\\b")
	  (sl-find-match-indent-for-stad "end-mode" "\\bend-mode\\b" "\\bmode\\b"))
	 ((looking-at "end-stad\\b")
	  (sl-find-match-indent-for-stad "end-stad" "\\bend-stad\\b" "\\bstad\\b"))
	 ((looking-at "end-step\\b")
	  (sl-find-match-indent "end-step" "\\bend-step\\b" "\\bstep\\b"))
	 ((looking-at "end-if\\b")
	  (sl-find-match-indent "end-if" "\\bend-if\\b" "\\bif\\b"))
	 ((looking-at "end-prog\\b")
	  (sl-find-match-indent "end-prog" "\\bend-prog\\b" "\\bprog\\b"))
         ((looking-at "end\\b")         ; Match the beginning
          (sl-find-match-indent "end" "\\bend\\b" sl-end-starters-reg))
         ((and sl-nested-if-indent (looking-at "else[\t ]*if\\b"))
          (sl-re-search-backward "\\bif\\b\\|\\belse\\b")
          (current-indentation))
         ((looking-at "else\\b")        ; Match the if
          (sl-find-match-indent "else" "\\belse\\b" "\\bif\\b" t))
         ((looking-at "then\\b")        ; Match the if + extra indentation
          (+ (sl-find-match-indent "then" "\\bthen\\b" "\\bif\\b" t)
             sl-indent-level))
         ((and sl-case-indent (looking-at "of\\b"))
          (sl-re-search-backward "\\bcase\\b")
          (+ (current-column) 2))
         ((looking-at sl-starters-reg)
          (let ((start (point)))
            (sl-backward-sexp)
            (if (and (looking-at sl-starters-indent-after)
                     (/= start (point)))
                (+ (if sl-type-of-indent
                       (current-column)
                     (if (progn (beginning-of-line)
                                (skip-chars-forward "\t ")
                                (looking-at "|"))
                         (- (current-indentation) sl-pipe-indent)
                       (current-indentation)))
                   sl-indent-level)
              (beginning-of-line)
              (skip-chars-forward "\t ")
              (if (and (looking-at sl-starters-indent-after)
                       (/= start (point)))
                  (+ (if sl-type-of-indent
                         (current-column)
                       (current-indentation))
                     sl-indent-level)
                (goto-char start)
                (if (sl-find-matching-starter sl-starters-reg)
                    (current-column)
                  0)))))
         (t
          (let ((indent (sl-get-indent)))
            (cond
             ((looking-at "|")
              ;; Lets see if it is the follower of a function definition
              (if (sl-find-matching-starter
                   "\\bfun\\b\\|\\bfn\\b\\|\\band\\b\\|\\bhandle\\b")
                  (cond
                   ((looking-at "fun\\b") (- (current-column) sl-pipe-indent))
                   ((looking-at "fn\\b") (1+ (current-column)))
                   ((looking-at "and\\b") (1+ (1+ (current-column))))
                   ((looking-at "handle\\b") (+ (current-column) 5)))
                (+ indent sl-pipe-indent)))
             (t
              (if sl-paren-lookback    ; Look for open parenthesis ?
                  (max 
		   (if (looking-at "[])}]") (1- indent) indent)
		   (sl-get-paren-indent))
                indent))))))))))

(defun sl-get-indent ()
  (save-excursion
    (let ((case-fold-search nil))
      (beginning-of-line)
      (skip-chars-backward "\t\n; ")
      (if (looking-at ";") (sl-backward-sexp))
      (cond
       ((save-excursion (sl-backward-sexp) (looking-at "end\\b"))
        (- (current-indentation) sl-indent-level))
       (t
        (while (/= (current-column) (current-indentation))
          (sl-backward-sexp))
        (skip-chars-forward "\t |")
        (let ((indent (current-column)))
          (skip-chars-forward "\t (")
          (cond
           ;; Started val/fun/structure...
           ((looking-at sl-indent-starters-reg)
            (+ (current-column) sl-indent-level))
           ;; Indent after "->" pattern, but only if its not an fn _ ->
           ;; (890726)
           ((looking-at ".*->")
            (if (looking-at ".*\\bfn\\b.*->")
                indent
              (+ indent sl-indent-level)))
           ;; else keep the same indentation as previous line
           (t indent))))))))

(defun sl-get-paren-indent ()
  (save-excursion
    (let ((levelpar 0)                  ; Level of "()"
          (levelcurl 0)                 ; Level of "{}"
          (levelsqr 0)			; Level of "[]"
	  (origpoint (save-excursion (point)))
          (backpoint (max (- (point) sl-paren-lookback) (point-min))))
      (catch 'loop
        (while (and (/= levelpar 1) (/= levelsqr 1) (/= levelcurl 1))
          (if (re-search-backward "[][{}()]" backpoint t)
              (if (not (sl-inside-comment-or-string-p))
                  (cond
                   ((looking-at "(") (setq levelpar (1+ levelpar)))
                   ((looking-at ")") (setq levelpar (1- levelpar)))
                   ((looking-at "\\[") (setq levelsqr (1+ levelsqr)))
                   ((looking-at "\\]") (setq levelsqr (1- levelsqr)))
                   ((looking-at "{") (setq levelcurl (1+ levelcurl)))
                   ((looking-at "}") (setq levelcurl (1- levelcurl)))))
            (throw 'loop 0)))		; Exit with value 0
	(if (save-excursion
	      (goto-char origpoint)
	      (looking-at "[])}]"))
	    (current-column)
	  (if (save-excursion
		(forward-char 1)
		(looking-at sl-indent-starters-reg))
	      (1+ (+ (current-column) sl-indent-level))
	    (1+ (current-column))))))))

(defun sl-inside-comment-or-string-p ()
  (let ((start (point)))
    (if (or (save-excursion
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
            (narrow-to-region (progn (beginning-of-line) (point)) start)
            (condition-case ()
                (while t
                  (search-forward "\"")
                  (setq numb (1+ numb)))
              (error (if (and (not (zerop numb))
                              (not (zerop (% numb 2))))
                         t nil)))))))))

(defun sl-skip-block ()
  (let ((case-fold-search nil))
    (sl-backward-sexp)
    (if (looking-at "end\\b")
        (progn
          (goto-char (sl-find-match-backward "end" "\\bend\\b"
                                              sl-end-starters-reg))
          (skip-chars-backward "\n\t "))
      ;; Here we will need to skip backward past if-then-else
      ;; and case-of expression. Please - tell me how !!
      )))

(defun sl-find-match-backward (unquoted-this this match &optional start)
  (save-excursion
    (let ((case-fold-search nil)
          (level 1)
          (pattern (concat this "\\|" match)))
      (if start (goto-char start))
      (while (not (zerop level))
        (if (sl-re-search-backward pattern)
            (setq level (cond
                         ((looking-at this) (1+ level))
                         ((looking-at match) (1- level))))
          ;; The right match couldn't be found
          (error (concat "Unbalanced: " unquoted-this))))
      (point))))

(defun sl-find-match-indent (unquoted-this this match &optional indented)
  (save-excursion
    (goto-char (sl-find-match-backward unquoted-this this match))
    (if (or sl-type-of-indent indented)
        (current-column)
      (if (progn
            (beginning-of-line)
            (skip-chars-forward "\t ")
            (looking-at "|"))
          (- (current-indentation) sl-pipe-indent)
        (current-indentation)))))

(defun sl-find-match-indent-for-stad (unquoted-this this match &optional indented)
  (save-excursion
    (goto-char (sl-find-match-backward unquoted-this this match))
    (current-indentation)))

(defun sl-find-matching-starter (regexp)
  (let ((case-fold-search nil)
        (start-let-point (sl-point-inside-let-etc))
        (start-up-list (sl-up-list))
        (found t))
    (if (sl-re-search-backward regexp)
        (progn
          (condition-case ()
              (while (or (/= start-up-list (sl-up-list))
                         (/= start-let-point (sl-point-inside-let-etc)))
                (re-search-backward regexp))
            (error (setq found nil)))
          found)
      nil)))

(defun sl-point-inside-let-etc ()
  (let ((case-fold-search nil) (last nil) (loop t) (found t) (start (point)))
    (save-excursion
      (while loop
        (condition-case ()
            (progn
              (re-search-forward "\\bend\\b")
              (while (sl-inside-comment-or-string-p)
                (re-search-forward "\\bend\\b"))
              (forward-char -3)
              (setq last (sl-find-match-backward "end" "\\bend\\b"
                                                  sl-end-starters-reg last))
              (if (< last start)
                  (setq loop nil)
                (forward-char 3)))
          (error (progn (setq found nil) (setq loop nil)))))
      (if found
          last
        0))))

(defun sl-re-search-backward (regexpr)
  (let ((case-fold-search nil) (found t))
    (if (re-search-backward regexpr nil t)
        (progn
          (condition-case ()
              (while (sl-inside-comment-or-string-p)
                (re-search-backward regexpr))
            (error (setq found nil)))
          found)
      nil)))

(defun sl-up-list ()
  (save-excursion
    (condition-case ()
        (progn
          (up-list 1)
          (point))
      (error 0))))

(defun sl-backward-sexp ()
  (condition-case ()
      (progn
        (let ((start (point)))
          (backward-sexp 1)
          (while (and (/= start (point)) (looking-at "(\\*"))
            (setq start (point))
            (backward-sexp 1))))
    (error (forward-char -1))))

(defun sl-comment-indent ()
  (if (looking-at "^(\\*")              ; Existing comment at beginning
      0                                 ; of line stays there.
    (save-excursion
      (skip-chars-backward " \t")
      (max (1+ (current-column))        ; Else indent at comment column
           comment-column))))           ; except leave at least one space.

;;; INSERTING PROFORMAS (COMMON SL-FORMS) 

(defconst sl-form-alist
  '(("let") ("datatype")
    ("case"))
  "The list of regions to auto-insert.")

(defun sl-insert-form ()
  "Interactive short-cut to insert a common Specware form."
  (interactive)
  (let ((newline nil)                   ; Did we insert a newline
        (name (completing-read "Form to insert: (default let) "
                               sl-form-alist nil t nil)))
    ;; default is "let"
    (if (string= name "") (setq name "let"))
    ;; Insert a newline if point is not at empty line
    (sl-indent-line)                   ; Indent the current line
    (if (save-excursion (beginning-of-line) (skip-chars-forward "\t ") (eolp))
        ()
      (setq newline t)
      (insert "\n"))
    (condition-case ()
        (cond
         ((string= name "let") (sl-let))
         ((string= name "functor") (sl-functor))
         ((string= name "case") (sl-case))
         ((string= name "datatype") (sl-datatype)))
      (quit (if newline 
                (progn
                  (delete-char -1)
                  (beep)))))))

(defun sl-let () 
  "Insert a `let in end'."
  (sl-let-local "let"))

(defun sl-case ()
  "Insert a case, prompting for case-expresion."
  (let (indent (expr (read-string "Case expr: ")))
    (insert (concat "case " expr))
    (sl-indent-line)
    (setq indent (current-indentation))
    (end-of-line)
    (if sl-case-indent
        (progn
          (insert "\n")
          (indent-to (+ 2 indent))
          (insert "of "))
      (insert " of\n")
      (indent-to (+ indent sl-indent-level)))
    (save-excursion (insert " -> "))))


(defun sl-let-local (starter)
  (let (indent)
    (insert starter)
    (sl-indent-line)
    (setq indent (current-indentation))
    (end-of-line)
    (insert "\n") (indent-to (+ sl-indent-level indent))
    (insert "\n") (indent-to indent)
    (insert "in\n") (indent-to (+ sl-indent-level indent)) (previous-line 1) (end-of-line)))

(defun sl-functor ()
  "Insert `functor ? () : ? = struct end', prompting for name/type."
  (let (indent
        (name (read-string "Name of functor: "))
        (signame (read-string "Signature type of functor: ")))
    (insert (concat "functor " name " () : " signame " ="))
    (sl-indent-line)
    (setq indent (current-indentation))
    (end-of-line)
    (insert "\n") (indent-to (+ sl-indent-level indent))
    (insert "struct\n")
    (indent-to (+ (* 2 sl-indent-level) indent))
    (insert "\n") (indent-to (+ sl-indent-level indent))
    (insert "end") (previous-line 1) (end-of-line)))

(defun sl-datatype ()
  "Insert a `datatype ??? =', prompting for name."
  (let (indent 
        (type (read-string (concat "Type of datatype (default none): ")))
        (name (read-string (concat "Name of datatype: "))))
    (insert (concat "datatype "
                    (if (string= type "") "" (concat type " "))
                    name " ="))
    (sl-indent-line)
    (setq indent (current-indentation))
    (end-of-line) (insert "\n") (indent-to (+ sl-indent-level indent))))

(defvar *pending-specware-meta-point-results* nil)

(defun continue-specware-meta-point ()
  "Continue last \"\\[specware-meta-point]\" command."
  (interactive)
  (if (null *pending-specware-meta-point-results*)
      (error "No more Definitions")
    (goto-specware-meta-point-definition (car *pending-specware-meta-point-results*)
					 (cdr *pending-specware-meta-point-results*))))

;;;; Meta-point facility (adapted from refine-meta-point fi:lisp-find-definition)
;;;; Uses Franz interface functions to communicate with Lisp
(defun specware-meta-point (name)
  (interactive (list (car (sw::get-default-symbol "Specware locate source" t t))))
  (let* ((pr (find-qualifier-info name))
	 (qualifier (car pr))
	 (sym (cadr pr)))
    (message "Requesting info from Lisp...")
    (let ((sym (if (equal (substring sym 0 2) "|!")
		   (substring sym 2 -1)
		 sym)))
      (let ((results (fi:eval-in-lisp (make-search-form qualifier sym))))
	(message nil)
	(if (null results)
	    (error "Can't find definition of %s." name)
	  (goto-specware-meta-point-definition sym results))))))

(defun goto-specware-meta-point-definition (sym results)
  (let* ((def-info (car results))
	 (file (cdr def-info))
	 (sort? (equal (car def-info) "Sort")))
    (setq *pending-specware-meta-point-results*
      (if (null (cdr results))
	  nil
	(cons sym (cdr results))))
    (setq file (concatenate 'string (strip-hash-suffix file) ".sw"))
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
			       fi:lisp-listener-mode))
	  (other-window 1))
      (switch-to-buffer buf))
    (goto-char 0)
    (let ((qsym (regexp-quote sym)))
      (or (if sort?
	      (re-search-forward (concat "\\bsort\\s-+" qsym "\\b") nil t)
	    (if (null current-prefix-arg)
		(or (re-search-forward (concat "\\bdef\\s-+" qsym "\\b") nil t)
		    (re-search-forward (concat "\\bop\\s-+" qsym "\\b") nil t))
	      (re-search-forward (concat "\\bop\\s-+" qsym "\\W") nil t)))
	  (error "Can't find definition of %s in %s" name file)))
    (beginning-of-line)
    (recenter 4)
    (when (not (null (cdr *pending-specware-meta-point-results*)))
      (message "%S more definitions."
	       (length (cdr *pending-specware-meta-point-results*))))))

(defun make-search-form (qualifier sym)
  (if (specware-file-name-p buffer-file-name)
      (format
       "(SpecCalc::findDefiningURI '(:|Qualified| %S . %S) %S %s)"
       qualifier sym (substring buffer-file-name 0 (- (length buffer-file-name) 3))
       *specware-context-str*)
    (format
     "(SpecCalc::searchForDefiningURI '(:|Qualified| %S . %S) %s)"
     qualifier sym *specware-context-str*)))

(defvar *specware-context-str* "user::*specware-global-context*")

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
  (let ((colon-pos (fi::lisp-find-char ?: name)))
      (if colon-pos			; has a package
	  (list (normalize-qualifier (substring name 0 colon-pos))
		(substring name (if (eq ?: (elt name (+ colon-pos 1)))
				    (+ colon-pos 2)
				  (+ colon-pos 1))))
	(let ((dot-pos (fi::lisp-find-char ?. name)))
	  (if dot-pos			; has a package
	      (list (substring name 0 dot-pos)
		    (substring name (+ dot-pos 1)))
	    (list sw::UnQualified name))))))

(defun strip-hash-suffix (str)
  (let ((pos (fi::lisp-find-char ?# str)))
    (if pos (substring str 0 pos)
      str)))

(defun spec-from-fi:package ()
  (if (null fi:package) ""
    (let ((colon-pos (fi::lisp-find-char ?: fi:package)))
      (upcase (if (null colon-pos) fi:package
		(substring fi:package (+ colon-pos 1)))))))

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
		 (buffer-string (point) end-pos)))
       "")))

(defun sw::get-default-symbol (prompt &optional up-p ignore-keywords)
  (let ((symbol-at-point (sw::get-symbol-at-point up-p)))
    (if fi::use-symbol-at-point
	(list symbol-at-point)
      (let ((read-symbol
	     (let ((fi::original-package fi:package))
	       (fi::ensure-minibuffer-visible)
	       (fi::completing-read
		(if symbol-at-point
		    (format "%s: (default %s) " prompt symbol-at-point)
		  (format "%s: " prompt))
		'fi::minibuffer-complete))))
	(list (if (string= read-symbol "")
		  symbol-at-point
		read-symbol))))))

(defun sw::get-symbol-at-point (&optional up-p)
  (let ((symbol
	 (cond
	  ((looking-at "\\sw\\|\\s_\\|\\.")
	   (save-excursion
	     (while (looking-at "\\sw\\|\\s_\\|\\.\\||")
	       (forward-char 1))
	     (while (eq (char-after (- (point) 2)) ?-)
			   (forward-char -2))
	     (fi::defontify-string
		 (buffer-substring
		  (point)
		  (progn (forward-sexp -1)
			 (while (looking-at "\\s'")
			   (forward-char 1))
			 (while (member (char-before) '(?. ?:))
			   (forward-sexp -1))
			 (point))))))
	  (t
	   (condition-case ()
	       (save-excursion
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
			    (fi::defontify-string
				(buffer-substring
				 (point)
				 (progn (forward-sexp -1)
					(while (looking-at "\\s'")
					  (forward-char 1))
					(point)))))
		   nil))
	     (error nil))))))
    (or symbol
	(if (and up-p (null symbol))
	    (sw::get-symbol-at-point)))))

(defun fi:check-unbalanced-parentheses-when-saving ()
  (if (and fi:check-unbalanced-parentheses-when-saving
	   (memq major-mode '(fi:common-lisp-mode fi:emacs-lisp-mode
			      fi:franz-lisp-mode specware-mode)))
      (if (eq 'warn fi:check-unbalanced-parentheses-when-saving)
	  (condition-case nil
	      (progn (fi:find-unbalanced-parenthesis) nil)
	    (error
	     (message "Warning: parens are not balanced in this buffer.")
	     (ding)
	     (sit-for 2)
	     ;; so the file is written:
	     nil))
	(condition-case nil
	    (progn (fi:find-unbalanced-parenthesis) nil)
	  (error
	   ;; save file if user types "yes":
	   (not (y-or-n-p "Parens are not balanced.  Save file anyway? ")))))))


;;; Load the menus, if they can be found on the load-path,

;;;(condition-case nil
;;;    (require 'sl-menus)
;;;  (error (message "Sorry, not able to load SL mode menus.")))

;;; & do the user's customisation

(add-hook 'specware-load-hook 'specware-mode-version t)

(run-hooks 'specware-load-hook)

;;; specware-mode.el has just finished.
