;; specware-mode.el. Major mode for editing Specware
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
;;          (setq sw:indent-level 2         ; conserve on horiz. space
;;                indent-tabs-mode nil)))    ; whatever

;; specware-mode-hook is run whenever a new specware-mode buffer is created.
;; There is an specware-load-hook too, which is only run when this file is
;; loaded. One use for this hook is to select your preferred
;; highlighting scheme, like this:

;; Alternatively, you can (require 'sw-font) which uses the font-lock
;; package instead. 

;; Finally, there is also an inferior-specware-mode-hook -- see
;; sl-proc.el. For more information consult the mode's *info* tree.

;;; VERSION STRING

(defconst specware-mode-version-string
  "specware-mode, Version 1.0")

(provide 'specware-mode)

;;; VARIABLES CONTROLLING THE MODE

(defvar sw:indent-level 2
  "*Indentation of blocks in Specware.")

(defvar sw:pipe-indent -2
  "*Extra (usually negative) indentation for lines beginning with |.")

(defvar sw:case-indent t
  "*How to indent case-of expressions.
    If t:   case expr                     If nil:   case expr of
              of exp1 -> ...                            exp1 -> ...
               | exp2 -> ...                          | exp2 -> ...

The first seems to be the standard in SL/NJ, but the second
seems nicer...")

(defvar sw:nested-if-indent t
  "*Determine how nested if-then-else will be formatted:
    If t: if exp1 then exp2               If nil:   if exp1 then exp2
          else if exp3 then exp4                    else if exp3 then exp4
          else if exp5 then exp6                         else if exp5 then exp6
               else exp7                                      else exp7")

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

(defvar specware-mode-hook nil
  "*This hook is run when specware-mode is loaded, or a new specware-mode buffer created.
This is a good place to put your preferred key bindings.")

(defvar specware-load-hook nil
  "*This hook is only run when specware-mode is loaded.")

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

(require 'easymenu) 

(defconst specware-menu 
    '("Specware"
      ["Process Current File" sw:process-current-file t]
      ["Process Unit" sw:process-unit t]
      ["Generate Lisp" sw:generate-lisp t]
      ["Generate & Load Lisp" (sw:generate-lisp t) t]
      ["Generate Local Lisp"  sw:gcl-current-file t]
      ["Evaluate Region" sw:evaluate-region (mark)]
      ["ctext Spec" sw:set-swe-spec t]
      ["cd to this directory" cd-current-directory t] 
      ["Find Definition" sw:meta-point t]
      ["Find Next Definition" sw:continue-meta-point
       *pending-specware-meta-point-results*]
      ["Switch to Specware Shell" sw:switch-to-lisp t]
      ["Comment Out Region" (comment-region (region-beginning) (region-end)) (mark)]
      ["Uncomment Region"
       (comment-region (region-beginning) (region-end) '(4))
       (mark)]
      ["Indent region" (sw:indent-region (region-beginning) (region-end)) (mark)]
      ["Run Specware" run-specware4 (not (inferior-lisp-running-p))]
      "-----"
      ["About Specware" about-specware t])) 


(defconst specware-interaction-menu 
    '("Specware"
      ["Find Definition" sw:meta-point t]
      ["Find Next Definition" sw:continue-meta-point
       *pending-specware-meta-point-results*]
      ["Switch to Previous File" sw:switch-to-lisp t]
      ["Search for Previous Input" fi:re-search-backward-input t]
      ["Run Specware" run-specware4 (not (inferior-lisp-running-p))]
      ["Exit Specware" sw:exit-lisp (inferior-lisp-running-p)]
      "-----"
      ["About Specware" about-specware t]))

;;; BINDINGS: should be common to the source and process modes...

(defun install-sw-keybindings (map)
  ;; Text-formatting commands:
  (define-key map "\C-c\C-m" 'sw:insert-form)
  (define-key map "\M-|"     'sw:electric-pipe)
  (define-key map "\;"       'sw:electric-semi)
  (define-key map "\M-\t"    'sw:back-to-outer-indent)
  (define-key map "\C-j"     'newline-and-indent)
  ;(define-key map "\177"     'backward-delete-char-untabify)
  (define-key map [backspace] 'backward-delete-char-untabify)
  (define-key map "\C-\M-\q" 'sw:indent-sexp)
  (define-key map "\C-\M-\\" 'sw:indent-region)
  (define-key map "\t"       'sw:indent-line) ; ...except this one

  (define-key map "\M-."     'sw:meta-point)
  (define-key map "\M-,"     'sw:continue-meta-point)
  (define-key map "\C-cp"    'sw:process-current-file)
  (define-key map "\C-c\C-p" 'sw:process-unit)
  (define-key map "\C-c\g"   'sw:generate-lisp)
  (define-key map "\C-c\C-l" ' sw:gcl-current-file)
  (define-key map "\C-c\C-e" 'sw:evaluate-region)
  (define-key map "\C-c\C-s" 'sw:set-swe-spec)
  (define-key map "\C-c\C-u" 'sw:cl-unit)
  (define-key map "\C-c!"    'cd-current-directory)
  (define-key map "\C-cl"    'sw:switch-to-lisp)
  (define-key map "\M-*"     'sw:switch-to-lisp)
  ;(define-key map "\C-?"     'backward-delete-char-untabify)
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

sw:indent-level (default 4)
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
  (run-hooks 'specware-mode-hook))           ; Run the hook

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
    (sw:indent-line)
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

;;; INDENTATION !!!

(defun sw:mark-function ()
  "Synonym for mark-paragraph -- sorry.
If anyone has a good algorithm for this..."
  (interactive)
  (mark-paragraph))

(defun sw:indent-sexp (n)
  (interactive "p")
  (sw:indent-region (save-excursion (forward-line 1) (point))
		    (save-excursion (forward-sexp (or n 1)) (point))))

(defun sw:indent-region (begin end)
  "Indent region of Specware code."
  (interactive "r")
  (message "Indenting region...")
  (save-excursion
    (goto-char end) (setq end (point-marker)) (goto-char begin)
    (while (< (point) end)
      (skip-chars-forward "\t\n ")
      (sw:indent-line)
      (end-of-line))
    (move-marker end nil))
  (message "Indenting region... done"))

(defun sw:indent-line ()
  "Indent current line of Specware code."
  (interactive)
  (let ((indent (sw:calculate-indentation)))
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

(defconst sw:indent-starters-reg  ; ??
  "case\\b\\|datatype\\b\
\\|else\\b\\|fun\\b\\|def\\b\\|if\\b\
\\|in\\b\\|infix\\b\\|infixr\\b\
\\|nonfix\\b\\|of\\b\\|open\\b\\|raise\\b\\|sig\\b\\|signature\\b\
\\|struct\\b\\|structure\\b\\|then\\b\\|\\btype\\b\\|val\\b\
\\|specmap\\b\\|progmap\\b\\|while\\b\\|withtype\\b\
\\|spec\\b\\|espec\\b\\|espec-refinement\\b\\|module\\b\
\\|\\(initial[ \\t]*\\|final[ \\t]*\\|\\b\\)\\(mode\\|stad\\)\\b\\|prog\\b\\|step\\b"
  "The indentation starters. The next line will be indented.")

(defconst sw:starters-reg  ; ??
  "\\babstraction\\b\\|\\babstype\\b\\|\\bdatatype\\b\
\\|\\bdef\\b\\|\\bfun\\b\\|\\bfunctor\\b\\|\\blocal\\b\
\\|\\binfix\\b\\|\\binfixr\\b\\|\\bsharing\\b\
\\|\\bnonfix\\b\\|\\bopen\\b\\|\\bsignature\\b\\|\\bstructure\\b\
\\|\\btype\\b\\|\\bval\\b\\|\\bwithtype\\b"
  "The starters of new expressions.")

(defconst sw:end-starters-reg  ; ??
  "\\blet\\b\\|\\blocal\\b\\|\\bsig\\b\\|\\bstruct\\b\\|\\bwith\\b"
  "Matching reg-expression for the \"end\" keyword.")

(defconst sw:starters-indent-after
  "struct\\b"
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
            (if (save-excursion (previous-line 1)
                                (beginning-of-line)
                                (looking-at "[\t ]*\\\\"))
                (progn (previous-line 1) (current-indentation))
            (if (re-search-backward "[^\\\\]\"" nil t)
                (1+ (current-indentation))
              0))))
         ;; Are we looking at a case expression ?
         ((looking-at "|.*->")
          (sw:skip-block)
          (if (looking-at "of\\b")
	      ;; "case of | ..."  treat like "of"
	      (progn (sw:re-search-backward "\\bcase\\b")
		     (+ (current-column) 2))
	    (sw:re-search-backward "->")
	    ;; Dont get fooled by fn _ -> in case statements (890726)
	    ;; Changed the regexp a bit, so fn has to be first on line,
	    ;; in order to let the loop continue (Used to be ".*\bfn....")
	    ;; (900430).
	    (let ((loop t))
	      (while (and loop (save-excursion
				 (beginning-of-line)
				 (looking-at "[^ \t]+\\bfn\\b.*->")))
		(setq loop (sw:re-search-backward "->"))))
	    (beginning-of-line)
	    (skip-chars-forward "\t ")
	    (cond
	     ((looking-at "|") (current-indentation))
	     ((and sw:case-indent (looking-at "of\\b"))
	      (1+ (current-indentation)))
	     ((looking-at "fn\\b") (1+ (current-indentation)))
	     ((looking-at "handle\\b") (+ (current-indentation) 5))
	     (t (+ (current-indentation) sw:pipe-indent)))))
         ((looking-at "and\\b")
          (if (sw:find-matching-starter sw:starters-reg)
              (current-column)
            0))
         ((looking-at "in\\b")          ; Match the beginning let/local
          (sw:find-match-indent "in" "\\bin\\b" "\\blocal\\b\\|\\blet\\b"))
	 ((looking-at "end-spec\\b")
	  (sw:find-match-indent "end-spec" "\\bend-spec\\b" "\\bspec\\b"))
	 ((looking-at "end-espec\\b")
	  (sw:find-match-indent "end-espec" "\\bend-espec\\b" "\\bespec\\b"))
	 ((looking-at "end-espec-refinement\\b")
	  (sw:find-match-indent "end-espec-refinement" "\\bend-espec-refinement\\b"
				"\\bespec-refinement\\b"))
	 ((looking-at "end-specmap\\b")
	  (sw:find-match-indent "end-specmap" "\\bend-specmap\\b" "\\bspecmap\\b"))
	 ((looking-at "end-with\\b")
	  (sw:find-match-indent "end-with" "\\bend-with\\b" "\\bwith\\b"))
	 ((looking-at "end-progmap\\b")
	  (sw:find-match-indent "end-progmap" "\\bend-progmap\\b" "\\bprogmap\\b"))
	 ((looking-at "end-module\\b")
	  (sw:find-match-indent "end-module" "\\bend-module\\b" "\\bmodule\\b"))
	 ((looking-at "end-while\\b")
	  (sw:find-match-indent "end-while" "\\bend-while\\b" "\\bwhile\\b"))
	 ((looking-at "end-mode\\b")
	  (sw:find-match-indent-for-stad "end-mode" "\\bend-mode\\b" "\\bmode\\b"))
	 ((looking-at "end-stad\\b")
	  (sw:find-match-indent-for-stad "end-stad" "\\bend-stad\\b" "\\bstad\\b"))
	 ((looking-at "end-step\\b")
	  (sw:find-match-indent "end-step" "\\bend-step\\b" "\\bstep\\b"))
	 ((looking-at "end-if\\b")
	  (sw:find-match-indent "end-if" "\\bend-if\\b" "\\bif\\b"))
	 ((looking-at "end-prog\\b")
	  (sw:find-match-indent "end-prog" "\\bend-prog\\b" "\\bprog\\b"))
         ((looking-at "end\\b")         ; Match the beginning
          (sw:find-match-indent "end" "\\bend\\b" sw:end-starters-reg))
         ((and sw:nested-if-indent (looking-at "else[\t ]*if\\b"))
          (sw:re-search-backward "\\bif\\b\\|\\belse\\b")
          (current-indentation))
         ((looking-at "else\\b")        ; Match the if
          (sw:find-match-indent "else" "\\belse\\b" "\\bif\\b" t))
         ((looking-at "then\\b")        ; Match the if + extra indentation
          (+ (sw:find-match-indent "then" "\\bthen\\b" "\\bif\\b" t)
             sw:indent-level))
         ((and sw:case-indent (looking-at "of\\b"))
          (sw:re-search-backward "\\bcase\\b")
          (+ (current-column) 2))
         ((looking-at sw:starters-reg)
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
                (if (sw:find-matching-starter sw:starters-reg)
                    (current-column)
                  0)))))
         (t
          (let ((indent (sw:get-indent)))
            (cond
             ((looking-at "|")
              ;; Lets see if it is the follower of a function definition
              (if (sw:find-matching-starter
                   "\\bfun\\b\\|\\bfn\\b\\|\\band\\b\\|\\bhandle\\b")
                  (cond
                   ((looking-at "fun\\b") (- (current-column) sw:pipe-indent))
                   ((looking-at "fn\\b") (1+ (current-column)))
                   ((looking-at "and\\b") (1+ (1+ (current-column))))
                   ((looking-at "handle\\b") (+ (current-column) 5)))
                (+ indent sw:pipe-indent)))
             (t
              (if sw:paren-lookback    ; Look for open parenthesis ?
                  (max 
		   (if (looking-at "[])}]") (1- indent) indent)
		   (sw:get-paren-indent))
                indent))))))))))

(defun sw:get-indent ()
  (save-excursion
    (let ((case-fold-search nil))
      (beginning-of-line)
      (skip-chars-backward "\t\n; ")
      (if (looking-at ";") (sw:backward-sexp))
      (cond
       ((save-excursion (sw:backward-sexp) (looking-at "end\\b"))
        (- (current-indentation) sw:indent-level))
       (t
        (while (/= (current-column) (current-indentation))
          (sw:backward-sexp))
        (skip-chars-forward "\t |")
        (let ((indent (current-column)))
          (skip-chars-forward "\t (")
          (cond
           ;; Started val/fun/structure...
           ((looking-at sw:indent-starters-reg)
            (+ (current-column) sw:indent-level))
           ;; Indent after "->" pattern, but only if its not an fn _ ->
           ;; (890726)
           ((looking-at ".*->")
            (if (looking-at ".*\\bfn\\b.*->")
                indent
              (+ indent sw:indent-level)))
           ;; else keep the same indentation as previous line
           (t indent))))))))

(defun sw:get-paren-indent ()
  (save-excursion
    (let ((levelpar 0)                  ; Level of "()"
          (levelcurl 0)                 ; Level of "{}"
          (levelsqr 0)			; Level of "[]"
	  (origpoint (save-excursion (point)))
          (backpoint (max (- (point) sw:paren-lookback) (point-min))))
      (catch 'loop
        (while (and (/= levelpar 1) (/= levelsqr 1) (/= levelcurl 1))
          (if (re-search-backward "[][{}()]" backpoint t)
              (if (not (sw:inside-comment-or-string-p))
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
		(looking-at sw:indent-starters-reg))
	      (1+ (+ (current-column) sw:indent-level))
	    (1+ (current-column))))))))

(defun sw:inside-comment-or-string-p ()
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

(defun sw:skip-block ()
  (let ((case-fold-search nil))
    (sw:backward-sexp)
    (if (looking-at "end\\b")
        (progn
          (goto-char (sw:find-match-backward "end" "\\bend\\b"
                                              sw:end-starters-reg))
          (skip-chars-backward "\n\t "))
      ;; Here we will need to skip backward past if-then-else
      ;; and case-of expression. Please - tell me how !!
      )))

(defun sw:find-match-backward (unquoted-this this match &optional start)
  (save-excursion
    (let ((case-fold-search nil)
          (level 1)
          (pattern (concat this "\\|" match)))
      (if start (goto-char start))
      (while (not (zerop level))
        (if (sw:re-search-backward pattern)
            (setq level (cond
                         ((looking-at this) (1+ level))
                         ((looking-at match) (1- level))))
          ;; The right match couldn't be found
          (error (concat "Unbalanced: " unquoted-this))))
      (point))))

(defun sw:find-match-indent (unquoted-this this match &optional indented)
  (save-excursion
    (goto-char (sw:find-match-backward unquoted-this this match))
    (if (or sw:type-of-indent indented)
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
              (while (or (/= start-up-list (sw:up-list))
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
              (re-search-forward "\\bend\\b")
              (while (sw:inside-comment-or-string-p)
                (re-search-forward "\\bend\\b"))
              (forward-char -3)
              (setq last (sw:find-match-backward "end" "\\bend\\b"
                                                  sw:end-starters-reg last))
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
            (backward-sexp 1))))
    (error (forward-char -1))))

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
    (sw:indent-line)                   ; Indent the current line
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
    (sw:indent-line)
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
    (sw:indent-line)
    (setq indent (current-indentation))
    (end-of-line)
    (insert "\n") (indent-to (+ sw:indent-level indent))
    (insert "\n") (indent-to indent)
    (insert "in\n") (indent-to (+ sw:indent-level indent))
    (previous-line 1) (end-of-line)))

(defun sw:running-specware-shell-p ()
  (and (inferior-lisp-running-p)
       (member (sw:eval-in-lisp "(SWShell::in-specware-shell?)") '(t T))))

(defun lisp-or-specware-command (lisp-comm spec-comm &rest argstrs)
  (simulate-input-expression
   (apply 'concat
	  (if (sw:running-specware-shell-p)
	      spec-comm lisp-comm)
	   argstrs)))

(defun ensure-list (fm-str)
  (if (equal (elt fm-str 0) (elt "(" 0))
      fm-str
    (format "(progn %s)" fm-str)))

(defun sw:process-current-file ()
  (interactive)
  (save-buffer)
  (let ((filename (sw::file-to-specware-unit-id buffer-file-name)))
    (lisp-or-specware-command ":sw " "proc " filename)))

(defun sw::file-to-specware-unit-id (filename)
  (let ((len (length filename)))
    (when (equal ".sw" (substring filename (- len 3)))
      (setq filename (substring filename 0 (- len 3))))
    (setq filename (sw::normalize-filename filename))
    (setq filename (name-relative-to-swpath filename))
    (when (eq (elt filename 1) ?:)
      (setq filename (substring filename 2)))
    filename))

(defun sw::normalize-filename (filename)
  (setq filename (replace-in-string filename "\\\\" "/"))
  (replace-in-string filename "Program Files" "Progra~1")
  (when (and (> (length filename) 2)
	     (equal (position ?: filename) 1)
	     (not (equal (elt filename 0) (upcase (elt filename 0)))))
    (setq filename (concat (upcase (subseq filename 0 1))
			   (subseq filename 1))))
  filename)

(defun get-swpath ()
  (let ((rawpath (sw:eval-in-lisp "(specware::getenv \"SWPATH\")"))
	(delim (if (eq window-system 'mswindows) ?\; ?:))
	(result ())
	(specware4 (sw:eval-in-lisp "(specware::getenv \"SPECWARE4\")"))
	pos)
    (when (eq rawpath 'nil)		; SWPATH not set
      (setq rawpath specware4)
      (when (eq rawpath 'nil)		; SPECWARE4 not set
	(setq rawpath "")))
    (while (setq pos (position delim rawpath))
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
	(progn (setq head (subseq filename 0 3))
	       (setq filename (subseq filename 3)))
      (progn (setq head (subseq filename 0 1))
	     (setq filename (subseq filename 1))))
    (while (and (position-if-not 'unitIdChar filename)
		(setq pos (position ?/ filename)))
      (setq head (concat head (subseq filename 0 (1+ pos))))
      (setq filename (subseq filename (1+ pos))))
    (cons head (concat "/" filename))))

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
  (let ((swpath (get-swpath)))
    (loop for dir in swpath
       do (let ((dir (sw::normalize-filename dir)))
	    (if (string-equal dir
			      (substring filename 0 (min (length dir)
							 (length filename))))
		(let ((rel-filename (substring filename (length dir))))
		  (unless (position-if-not 'unitIdChar rel-filename)
		    (return (if (eq (elt rel-filename 0) ?/)
				rel-filename
			      (concat "/" rel-filename)))))))
       finally (let ((oldpath (sw:eval-in-lisp "(specware::getenv \"SWPATH\")"))
		     (head-dir-uid (split-filename-for-path filename)))
		 (lisp-or-specware-command
		  ":swpath " "path "
		  oldpath
		  (if (eq window-system 'mswindows) ";" ":")
		  (car head-dir-uid))
		 (sleep-for 0.1)	; Just to avoid confusing output
		 (return (cdr head-dir-uid))))))

(defun sw:process-unit (unitid)
  (interactive (list (read-from-minibuffer "Process Unit: "
					   (sw::file-to-specware-unit-id
					    buffer-file-name))))
  (lisp-or-specware-command ":sw " "proc " unitid))

(defun sw:generate-lisp (compile-and-load?)
  (interactive "P")
  (save-buffer)
  (let* ((buf-name buffer-file-name)
	 (filename (sw::file-to-specware-unit-id buf-name))
	 (dir default-directory))
    (lisp-or-specware-command ":swl " "gen-lisp " filename)
    (when compile-and-load?
      (sit-for 1 t)
      (lisp-or-specware-command ":cl " "cl " dir "lisp/"
				(substring buf-name (length dir) -3)
				".lisp"))))

(defun sw:gcl-current-file ()
  (interactive)
  (save-buffer)
  (let ((filename (sw::file-to-specware-unit-id buffer-file-name)))
    (lisp-or-specware-command ":swll " "lgen-lisp " filename)))

(defun sw:evaluate-region (beg end)
  (interactive "r")
  (let ((filename (sw::file-to-specware-unit-id buffer-file-name))
	(text (buffer-substring beg end)))
    (when (or (buffer-modified-p)
	      (not (sw:eval-in-lisp "(Specware::unitIDCurrentInCache? %S)"
				    buffer-file-name)))
      (sw:gcl-current-file)
      (sleep-for 1))			; Give :swll a chance to finish
    (unless (string-equal filename
			  (sw:eval-in-lisp "cl-user::*current-swe-spec*"))
      (lisp-or-specware-command ":swe-spec " "ctext " filename)
      (sleep-for 0.1))
    (lisp-or-specware-command ":swe " "eval " text)))

(defun sw:set-swe-spec ()
  (interactive)
  (let ((filename (sw::file-to-specware-unit-id buffer-file-name)))
    (lisp-or-specware-command ":swe-spec " "ctext " filename)))

(defun sw:cl-unit (unitid)
  (interactive (list (read-from-minibuffer "Compile and Load Unit: "
					   (sw::file-to-specware-unit-id
					    buffer-file-name))))
  (save-buffer)
  (let ((temp-file-name (concat (temp-directory) "-cl-current-file")))
    (if (sw:eval-in-lisp
	   "(Specware::evaluateLispCompileLocal_fromLisp-2 %S '(:|Some| . %S))"
	   unitid temp-file-name)
	(sw:eval-in-lisp-no-value
	   "(let (*redefinition-warnings*)
              (specware::compile-and-load-lisp-file %S))"
	   temp-file-name)
      (message "Specware Processing Failed!"))))

(defun sw:dired-process-current-file ()
  (interactive)
  (let ((filename (sw::file-to-specware-unit-id (dired-get-filename))))
    (lisp-or-specware-command ":sw " "proc " filename)))

(when (boundp 'dired-mode-map)
  (define-key dired-mode-map "\C-cp" 'sw:dired-process-current-file)
  (define-key dired-mode-map "\C-c!" 'cd-current-directory))

(defun cd-current-directory ()
  (interactive)
  (lisp-or-specware-command ":cd " "cd " default-directory))

(defvar *pending-specware-meta-point-results* nil)

(defun sw:continue-meta-point ()
  "Continue last \"\\[sw:meta-point]\" command."
  (interactive)
  (if (null *pending-specware-meta-point-results*)
      (error "No more Definitions")
    (goto-specware-meta-point-definition
     (car *pending-specware-meta-point-results*)
     (cdr *pending-specware-meta-point-results*))))

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
      (let ((results (sw:eval-in-lisp (make-search-form qualifier sym))))
	(message nil)
	(if (or (null results) (eq results 'NIL))
	    (error "Can't find definition of %s." name)
	  (goto-specware-meta-point-definition sym results))))))

(defun goto-specware-meta-point-definition (sym results)
  (let* ((def-info (car results))
	 (file (cdr def-info))
	 (sort? (member (car def-info) '("Type" "Sort"))))
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
			       fi:lisp-listener-mode
			       ilisp-mode))
	  (other-window 1))
      (switch-to-buffer buf))
    (goto-char 0)
    (let ((qsym (regexp-quote sym)))
      (or (if sort?
	      (re-search-forward (concat "\\b\\(type\\|sort\\)\\s-+" qsym "\\b") nil t)
	    (if (null current-prefix-arg)
		(or (re-search-forward (concat "\\bdef\\s-+" qsym "\\b") nil t)
		    (re-search-forward	; def fa(a) foo
		     (concat "\\bdef\\s-+fa\\s-*(.+)\\s-+" qsym "\\b") nil t)
		    (re-search-forward	; def fa(a) foo
		     (concat "\\bdef\\s-+\\[.+\\]\\s-+" qsym "\\b") nil t)
		    (re-search-forward	; def fie.foo
		     (concat "\\bdef\\s-\\w+\\." qsym "\\b") nil t)
		    (re-search-forward (concat "\\bop\\s-+" qsym "\\b") nil t)
		    (re-search-forward	; op fie.foo
		     (concat "\\bop\\s-+\\w+\\." qsym "\\b") nil t))
	      (or (re-search-forward (concat "\\bop\\s-+" qsym "\\b") nil t)
		  (re-search-forward	; op fie.foo
		   (concat "\\bop\\s-+\\w+\\." qsym "\\b") nil t))))
	  (error "Can't find definition of %s in %s" qsym file)))
    (beginning-of-line)
    (recenter 4)
    (when (not (null (cdr *pending-specware-meta-point-results*)))
      (message "%S more definitions."
	       (length (cdr *pending-specware-meta-point-results*))))))

(defun make-search-form (qualifier sym)
  (if (specware-file-name-p buffer-file-name)
      (format
       "(SpecCalc::findDefiningUID-3 '(:|Qualified| %S . %S) %S %s)"
       qualifier sym (substring buffer-file-name 0 (- (length buffer-file-name) 3))
       *specware-context-str*)
    (format
     "(SpecCalc::searchForDefiningUID-2 '(:|Qualified| %S . %S) %s)"
     qualifier sym *specware-context-str*)))

;; (defvar *specware-context-str* "cl-user::*specware-global-context*")
(defvar *specware-context-str* "(MonadicStateInternal::readGlobalVar \"GlobalContext\")")

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
  (let ((colon-pos (position ?: name)))
      (if colon-pos			; has a package
	  (list sw::UnQualified
		;; Don't currently used qualifier as the case is wrong
		;;(normalize-qualifier (substring name 0 colon-pos))
		(substring name (if (and (< (+ colon-pos 1) (length name))
					 (eq ?: (elt name (+ colon-pos 1))))
				    (+ colon-pos 2)
				  (+ colon-pos 1))))
	(let ((dot-pos (position ?. name)))
	  (if dot-pos			; has a package
	      (list (substring name 0 dot-pos)
		    (substring name (+ dot-pos 1)))
	    (list sw::UnQualified name))))))

(defun strip-hash-suffix (str)
  (let ((pos (position ?# str)))
    (if pos (substring str 0 pos)
      str)))

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
  (let ((symbol
	 (cond
	  ((looking-at "\\sw\\|\\s_\\|\\.")
	   (save-excursion
	     (while (looking-at "\\sw\\|\\s_\\|\\.\\||")
	       (forward-char 1))
	     (while (eq (char-after (- (point) 2)) ?-)
			   (forward-char -2))
	     (buffer-substring
	      (point)
	      (progn (forward-sexp -1)
		     (while (looking-at "\\s'")
		       (forward-char 1))
		     (while (member (char-before) '(?. ?:))
		       (forward-sexp -1))
		     (point)))))
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
			    (buffer-substring
			     (point)
			     (progn (forward-sexp -1)
				    (while (looking-at "\\s'")
				      (forward-char 1))
				    (point))))
		   nil))
	     (error nil))))))
    (when (member symbol '(":"))
      (setq symbol nil))
    (or symbol
	(if (and up-p (null symbol))
	    (sw::get-symbol-at-point)))))

;;;; Prompt regexp for specware shell
(defvar *lisp-prompt-regexp*)		; make buffer local?

(defun set-comint-prompt ()
  (unless (boundp '*lisp-prompt-regexp*)
    (setq *lisp-prompt-regexp* comint-prompt-regexp))
  (when (equal *lisp-prompt-regexp* comint-prompt-regexp)
      (setq comint-prompt-regexp (concat "\\(" comint-prompt-regexp "\\|^\\* \\)")))
  (setq bridge-prompt-regexp comint-prompt-regexp)
  (when (boundp 'fi::prompt-pattern)
    (setq fi::prompt-pattern comint-prompt-regexp)))

(defvar sw:check-unbalanced-parentheses-when-saving t)
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

;;; Command for showing error point in specware shell
(defun show-error-on-new-input (col)
  (sit-for 0.1 t)                         ; Allow error message to be printed
  (goto-char (point-max))
  (previous-input-line)
  (if (eq (current-column) 0)
      (delete-backward-char 1))
  (comint-bol nil)
  (forward-sexp 1)
  (forward-char col)
  ())

;;; About Specware command implementation
(defvar specware-logo
  (make-glyph `[xpm :file ,(concat *specware*
				   "/Library/IO/Emacs/specware_logo.xpm")]))

(defun goto-specware-web-page (&rest ign)
  (browse-url "http://specware.org/"))

(defun goto-specware-release-notes (&rest ign)
  (browse-url
   (if (inferior-lisp-running-p)
       (format "http://specware.org/release-notes-%s-%s.html"
	       (sw:eval-in-lisp "specware::Major-Version-String")
	       (sw:eval-in-lisp "cl-user::Specware-patch-level"))
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
  "Face used for links in the Specware About page.")

;; Derived from about.el functions
;; I don't use the about functions because they are different in different 
;; versions of xemacs
(defun about-specware-get-buffer (name)
  (cond ((get-buffer name)
	 (switch-to-buffer name)
	 (goto-line 2)
	 name)
	(t
	 (switch-to-buffer name)
	 (buffer-disable-undo)
	 ;; #### This is a temporary fix until wid-edit gets fixed right.
	 ;; We don't do everything that widget-button-click does -- i.e.
	 ;; we don't change the link color on button down -- but that's
	 ;; not important.
	 (add-local-hook
	  'mouse-track-click-hook
	  #'(lambda (event count)
	      (cond
	       ((widget-event-point event)
		(let* ((pos (widget-event-point event))
		       (button (get-char-property pos 'button)))
		  (when button
		    (widget-apply-action button event)
		    t))))))
	 (set-specifier left-margin-width about-left-margin (current-buffer))
	 (set (make-local-variable 'widget-button-face) 'about-specware-link-face)
	 nil)))

(defvar about-left-margin 3)

(defun about-specware-center (string-or-glyph)
  (let ((n (- (startup-center-spaces string-or-glyph) about-left-margin)))
    (make-string (if (natnump n) n 0) ?\ )))

(defun about-specware-finish-buffer ()
  (widget-insert "\n")
  (widget-create 'link
		 :help-echo "Bury this buffer"
		 :action (lambda (widget event)
			   (if event
			       ;; For some reason,
			       ;; (bury-buffer (event-buffer event))
			       ;; doesn't work.
			       (with-selected-window (event-window event)
				 (bury-buffer))
			     (bury-buffer)))
		 :tag "Bury")
  (widget-insert " this buffer and return to previous.\n")
  (use-local-map (make-sparse-keymap))
  (set-keymap-parent (current-local-map) widget-keymap)
  (local-set-key "q" 'bury-buffer)
  (local-set-key "l" 'bury-buffer)
  (local-set-key " " 'scroll-up)
  (local-set-key [backspace] 'scroll-down)
  (local-set-key "\177" 'scroll-down)
  (widget-setup)
  (goto-char (point-min))
  (toggle-read-only 1)
  (set-buffer-modified-p nil))

(defun about-specware ()
  "Describe the Specware System"
  (interactive)
  (unless (about-specware-get-buffer "*About Specware*")
    (set-glyph-image specware-logo
		     "./specware_logo.xpm"
		     'global 'x)
    (widget-insert (about-specware-center specware-logo))
    (widget-create 'default
		   :format "%t"
		   :tag-glyph specware-logo)
    (widget-insert "\n\n")
    (when (inferior-lisp-running-p)
      (let* ((specware-version (sw:eval-in-lisp "cl-user::Specware-version"))
	     (specware-patch-number (sw:eval-in-lisp
				     "cl-user::Specware-patch-level"))
	     (specware-version (format "Version %s.%s"
				       specware-version
				       specware-patch-number)))
	(widget-insert (about-specware-center specware-version))
	(widget-create 'link :help-echo "Specware Version Release Notes"
		       :action 'goto-specware-release-notes
		       :button-prefix ""
		       :button-suffix ""
		       specware-version)))
    (widget-insert "\n\n")
    (widget-create 'link :help-echo "Specware Web Page"
		   :action 'goto-specware-web-page
		   :button-prefix ""
		   :button-suffix ""
		   "Specware")
    (widget-insert " is a leading-edge automated software development system 
that allows users to precisely specify the desired functionality of 
their applications and to generate provably correct code based on 
these requirements. At the core of the design process in Specware 
lies stepwise refinement, in which users begin with a simple, abstract 
model of their problem and iteratively refine this model until it 
uniquely and concretely describes their application.")
    (widget-insert "\n")
    (about-specware-finish-buffer)
    (goto-line 2)))

;;; Run test harness
(defun sw:run-test-harness (non-rec)
  ;; Prefix arg means don't recur on sub-directories
  (interactive "P")
  (unless (inferior-lisp-running-p)
    (run-specware4)
    (sit-for 1 t))
  (simulate-input-expression
   (if non-rec
       (format "(specware-test::run-test-directories %S)"
	       default-directory)
     (format "(specware-test::run-test-directories-rec %S)"
	     default-directory))))

;;; & do the user's customisation

(add-hook 'specware-load-hook 'specware-mode-version t)

(run-hooks 'specware-load-hook)

;;; specware-mode.el has just finished.
