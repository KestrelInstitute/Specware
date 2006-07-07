;;; sw-font.el --- Highlighting for specware-mode using font-lock.

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

(add-hook 'specware-mode-hook 'turn-on-font-lock)

(defconst symbol-sep "[^-_?a-z0-9A-Z]")

;; reserved symbols that introduce named entities:
(defconst specware-definition-introducing-words
    (regexp-opt '(
   ;; core specware:
      "axiom"
      "conjecture"
      "def"
      "op"
      "theorem"
      "type"
   ;; accord extension:
      "diagram"
      "espec"
      "espec-refinement"
      "interpretation"
      "ip-scheme"
      "ip-scheme-morphism"
      "mode"
      "module"
      "morphism"
      "spec"
      "stad"
      )))

(defconst specware-definition-regexp
    (concat "\\(^\\|" symbol-sep "\\)\\("
	    specware-definition-introducing-words
	    "\\)"
	    "[^-_?a-z0-9A-Z,:\"}`\n]+") )

;; reserved symbols:
(defconst specware-keywords
    '(
   ;; core specware:
      "as"
      "axiom"
      "by"
      "case"
      "choose"
      "colimit"
      "conjecture"
      "def"
      "diagram"
      "else"
      "embed"
      "embed?"
      "endspec"
      "ex"
      "ex1"
      "fa"
      "false"
      "fn"
      "from"
      "generate"
      "if"
      "import"
      "in"
      "infixl"
      "infixr"
      "is"
      "let"
      "morphism"
      "obligations"
      "of"
      "op"
      "options"
      "project"
      "prove"
      "qualifying"
      "quotient"
      "spec"
      "the"
      "then"
      "theorem"
      "translate"
      "true"
      "type"
      "using"
      "where"
      "with"
   ;; accord extension:
      "arcs"
      "compile"
      "cond"
      "diagram"
      "do"
      "proof"
      "end"
      "end-diagram"
      "end-espec"
      "end-espec-refinement"
      "end-if"
      "end-mode"
      "end-module"
      "end-prog"
      "end-spec"
      "end-specmap"
      "end-stad"
      "end-step"
      "end-while"
      "end-with"
      "end-proof"
      "espec"
      "espec-refinement"
      "final"
      "guard"
      "initial"
      "interpretation"
      "ip-scheme"
      "ip-scheme-morphism"
      "mode"
      "module"
      "morphism"
      "spec"
      "nodes"
      "prog"
      "progmap"
      "specmap"
      "stad"
      "step"
      "when"
      "while"
      ))

(defconst specware-keywords-regexp
  (regexp-opt specware-keywords))

(defconst specware-font-lock-keywords
  (list (list specware-definition-regexp
	      '(2 font-lock-reserved-word-face keep))
	(list (concat specware-definition-regexp
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
		      specware-keywords-regexp
		      "\\)" symbol-sep)`
	      1 'font-lock-reserved-word-face 'keep)
	; ... keyword is at the end of a line ...
	(list (concat symbol-sep "\\("
		      specware-keywords-regexp
		      "\\)$")
	      1 'font-lock-reserved-word-face 'keep)
	; ... keyword is at the beginning of a line ...
	(list (concat "^\\("
		      specware-keywords-regexp
		      "\\)$")
	      1 'font-lock-reserved-word-face 'keep)
	; ... keyword is the only thing on the line ...
	(list (concat "^\\("
		      specware-keywords-regexp
		      "\\)" symbol-sep)
	      1 'font-lock-reserved-word-face 'keep)
	"&&" "||" "=>" "=" "~=" "~" "<" ">" "->" "<-" ";" ":" "::" ":=" "|" "_"
	"+->" "\\." "!" "*" "<<"           ; no? "}" "{" "]" "\\[" "(" ")"
;;;	; Fixed width if % followed by 2 spaces, %%%, tab, or space--- or nothing
;;;	'("\\(%+\\(  \\|%%%\\|\t\\| \t\\| ---\\|---\\|$\\).*$\\)"
;;;	  1 font-lock-fixed-width-comment-face t)
	))

;(defconst specware-font-lock-keywords specware-font-lock-keywords)

(provide 'sw-font)
