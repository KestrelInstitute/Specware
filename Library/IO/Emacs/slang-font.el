;;; slang-font.el --- Highlighting for slang-mode using font-lock.

(require 'font-lock)

(when font-lock-use-colors
  (font-lock-use-default-colors))

;;;(make-face 'font-lock-fixed-width-comment-face)
;;;(or (face-differs-from-default-p 'font-lock-fixed-width-comment-face)
;;;    (copy-face 'bold 'font-lock-fixed-width-comment-face))

;;(set-face-underline-p 'font-lock-string-face nil)
(setq font-lock-face-list
  (cons 'font-lock-reserved-word-face
	font-lock-face-list))
(defface font-lock-reserved-word-face
  '((((class color) (background light))
     (:bold t
      :foreground "darkblue"))
    (t (:italic t)))
  "Font Lock mode face used to highlight reserved words."
  :group 'font-lock-faces)
;;;(defface font-lock-reserved-word-face
;;;  '((t (:italic t)))
;;;  "Font Lock mode face used to highlight reserved words."
;;;  :group 'font-lock-faces)

(add-hook 'slang-mode-hook 'turn-on-font-lock)

(defconst symbol-sep "[^-_?a-z0-9A-Z]")

(defconst slang-definition-introducing-words
  (regexp-opt '("spec" "module" "op" "sort" "espec" "espec-refinement" "stad" "mode"
		"morphism" "diagram" "ip-scheme-morphism"
		"ip-scheme" "conjecture" "axiom" "theorem"
		"interpretation" "def"
		)))

(defconst slang-definition-regexp
    (concat "\\(^\\|" symbol-sep "\\)\\("
	    slang-definition-introducing-words
	    "\\)"
	    "[^-_?a-z0-9A-Z,:\"}`\n]+") )

(defconst slang-keywords
    '("nodes" "arcs" "end-diagram"
      "import" "let" "spec" "U" "qualifying"
      "diagram" "from" "as" "compile"
      "case" "if" "else" "fn" "then" "in" "of"
      "fa" "or"
      "colimit" "of" "by" "translate"
      "import" "true" "false" "while" "end-while"
      "end-spec" "end-module" "is"
      "prog" "end-prog" "step" "end-step" "with" "end-with"
      "end-mode" "end-stad" "end-espec" "end-espec-refinement" "end-if"
      "initial" "final" "when" "cond" "guard" "do"
      "specmap" "end-specmap" "progmap" "end"
      ))

(defconst slang-keywords-regexp
  (regexp-opt slang-keywords))

(defconst slang-font-lock-keywords
  (list (list slang-definition-regexp
	      '(2 font-lock-reserved-word-face keep))
	(list (concat slang-definition-regexp
		      "\\(\\(\\w\\|\\s_\\|-\\|\\.\\)+\\)")
	      '(3 font-lock-function-name-face keep))
	(list (concat symbol-sep "let" symbol-sep
		      "+\\(def \\|\\(.*?\\)=\\)")
	      '(1 font-lock-function-name-face keep))
	;; next two cases are for above except for vars that don't start at beginning of line
	;;(list "[^?a-z0-9A-Z---]\\(var\\)\\s-" 1 'font-lock-reserved-word-face)
	;; symbol followed by a : is a defining occurrence
;;; Doesn't work and very inefficient
;;;	(list (concat symbol-sep
;;;		      "\\(\\(\\w\\|\\s_\\|-\\)+\\)\\( \\|\t\\|\n\\)*:\\s_")
;;;	  1 'font-lock-function-name-face)
	(list (concat symbol-sep "\\("
		      slang-keywords-regexp
		      "\\)" symbol-sep)`
	      1 'font-lock-reserved-word-face 'keep)
	; ... keyword is at the end of a line ...
	(list (concat symbol-sep "\\("
		      slang-keywords-regexp
		      "\\)$")
	      1 'font-lock-reserved-word-face 'keep)
	; ... keyword is at the beginning of a line ...
	(list (concat "^\\("
		      slang-keywords-regexp
		      "\\)$")
	      1 'font-lock-reserved-word-face 'keep)
	; ... keyword is the only thing on the line ...
	(list (concat "^\\("
		      slang-keywords-regexp
		      "\\)" symbol-sep)
	      1 'font-lock-reserved-word-face 'keep)
	"&" "=>" "=" "~" "<" ">" "->" "<-" ";" ":" "::" ":=" "|" "_"
	"\\." "!" "*"			; no? "}" "{" "]" "\\[" "(" ")"
;;;	; Fixed width if % followed by 2 spaces, %%%, tab, or space--- or nothing
;;;	'("\\(%+\\(  \\|%%%\\|\t\\| \t\\| ---\\|---\\|$\\).*$\\)"
;;;	  1 font-lock-fixed-width-comment-face t)
	))

(defconst specware-font-lock-keywords slang-font-lock-keywords)

(provide 'slang-font)
