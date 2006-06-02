;; x-symbol-specware.el   

;;	Token language "Specware Symbols" for package x-symbol
;;
;;  ID:         x-symbol-specware.el,v 1.0 2006/03/29
;;  Author:     Stephen Westfold
;;  Copyright   2006 Kestrel Institute
;;  License     GPL (GNU GENERAL PUBLIC LICENSE)
;;
;;
;; NB: Part of Specware distribution.
;;
;;  Based on x-symbol-isabelle.el by Technische Universitaet Muenchen

(pushnew (concat (getenv "SPECWARE4") "/Library/IO/Emacs/") data-directory-list)
(pushnew (concat (getenv "SPECWARE4") "/Library/IO/Emacs/x-symbol/") data-directory-list)
(require 'x-symbol)

(defvar x-symbol-specware-name "Specware Symbols")
(defvar x-symbol-specware-modes '(specware-mode specware-listener-mode))
(x-symbol-register-language 'specware 'x-symbol-specware x-symbol-specware-modes)

(defvar x-symbol-specware-required-fonts nil)

;;;===========================================================================
;;;  General language accesses, see `x-symbol-language-access-alist'
;;;===========================================================================

(defvar x-symbol-specware-name "Specware Symbol")
(defvar x-symbol-specware-modeline-name "sw")

(defcustom x-symbol-specware-header-groups-alist nil
   "*If non-nil, used in swsym specific grid/menu.
See `x-symbol-header-groups-alist'."
  :group 'x-symbol-specware
  :group 'x-symbol-input-init
  :type 'x-symbol-headers)

(defcustom x-symbol-specware-electric-ignore 
  "[:'][A-Za-z]\\|<=\\|\\[\\[\\|\\]\\]\\|~="
  "*Additional Specware version of `x-symbol-electric-ignore'."
  :group 'x-symbol-specware
  :group 'x-symbol-input-control
  :type 'x-symbol-function-or-regexp)


(defvar x-symbol-specware-required-fonts nil
  "List of features providing fonts for language `specware'.")

(defvar x-symbol-specware-extra-menu-items nil
  "Extra menu entries for language `specware'.")


(defvar x-symbol-specware-token-grammar
  '(x-symbol-make-grammar
    :encode-spec (((t . "\\\\")))
    :decode-regexp "\\\\+_[A-Za-z]+"
    :input-spec nil
    :token-list x-symbol-specware-token-list))

(defun x-symbol-specware-token-list (tokens)
  (mapcar (lambda (x) (cons x t)) tokens))

(defvar x-symbol-specware-user-table nil
  "User table defining Specware commands, used in `x-symbol-specware-table'.")

(defvar x-symbol-specware-generated-data nil
  "Internal.")

;;;===========================================================================
;;;  No image support
;;;===========================================================================

(defvar x-symbol-specware-master-directory  'ignore)
(defvar x-symbol-specware-image-searchpath '("./"))
(defvar x-symbol-specware-image-cached-dirs '("images/" "pictures/"))
(defvar x-symbol-specware-image-file-truename-alist nil)
(defvar x-symbol-specware-image-keywords nil)


;;;===========================================================================
;;  super- and subscripts
;;;===========================================================================

;; _\^_val _\__val where val is specware symbol sub-token or \_name

(defcustom x-symbol-specware-subscript-matcher 'x-symbol-specware-subscript-matcher
  "Function matching super-/subscripts for language `sw'.
See language access `x-symbol-LANG-subscript-matcher'."
  :group 'x-symbol-specware
  :type 'function)

(defcustom x-symbol-specware-font-lock-regexp "_\\\\[_^]_" ; "\\\\\\^_i?su[bp]"
  "Regexp matching the start tag of Specware super- and subscripts."
  :group 'x-symbol-specware
  :type 'regexp)

;(defcustom x-symbol-specware-font-lock-limit-regexp "\n\\|\\\\_\\^esu[bp]"
;  "Regexp matching the end of line and the end tag of Specware
;spanning super- and subscripts."
;  :group 'x-symbol-specware
;  :type 'regexp)

(defconst specware-alpha-num-char "[a-z0-9A-Z]")
(defconst specware-special-sym-char "[\/+-=^]")
(defconst specware-special-token "\\\\_[a-z0-9A-Z]+")

(defcustom x-symbol-specware-font-lock-contents-regexp
  (concat "\\(" specware-alpha-num-char "+\\|"
	  specware-special-sym-char "+\\|"
	  "." "\\)")
  "*Regexp matching the spanning super- and subscript contents.
This regexp should match the text to be sub- or super-scripted."
  :group 'x-symbol-specware  
  :type 'regexp)


(defun x-symbol-specware-subscript-matcher (limit)  
  (block nil
    (let (open-beg open-end close-end script-type)
      (while (re-search-forward x-symbol-specware-font-lock-regexp limit t)
        (setq open-beg (match-beginning 0)
              open-end (match-end 0)
              script-type (if (eq (char-after (- open-end 2)) ?_)
                              'x-symbol-sub-face
                           'x-symbol-sup-face))
        (when (save-excursion
		(goto-char open-end)
		(re-search-forward x-symbol-specware-font-lock-contents-regexp
				   limit t))
	  (setq close-end (match-end 0))
          (store-match-data (list open-beg close-end
				  open-beg open-end
				  open-end close-end))
          (return script-type))))))

(defvar x-symbol-specware-subscript-type)

(defun specware-match-subscript (limit)
  (setq x-symbol-specware-subscript-type
	(funcall x-symbol-specware-subscript-matcher limit)))

;; these are used for Specware output only. x-symbol does its own
;; setup of font-lock-keywords for the theory buffer
;; (x-symbol-specware-font-lock-keywords does not belong to language
;; access any more)
(defvar x-symbol-specware-font-lock-keywords
  '((specware-match-subscript
     (1 x-symbol-invisible-face t)
     (2 (progn x-symbol-specware-subscript-type) prepend)
     (3 x-symbol-invisible-face t t)))
  "Specware font-lock keywords for super- and subscripts.")

(defvar x-symbol-specware-font-lock-allowed-faces t)


;;;===========================================================================
;;;  Charsym Info
;;;===========================================================================

(defcustom x-symbol-specware-class-alist
  '((VALID "Specware Symbol" (x-symbol-info-face))
    (INVALID "no Specware Symbol" (red x-symbol-info-face)))
  "Alist for Specware's token classes displayed by info in echo area.
See `x-symbol-language-access-alist' for details."
  :group 'x-symbol-texi
  :group 'x-symbol-info-strings
;;  :set 'x-symbol-set-cache-variable   [causes compile error]
  :type 'x-symbol-class-info)


(defcustom x-symbol-specware-class-face-alist nil
  "Alist for Specware's color scheme in TeXinfo's grid and info.
See `x-symbol-language-access-alist' for details."
  :group 'x-symbol-specware
  :group 'x-symbol-input-init
  :group 'x-symbol-info-general
;;  :set 'x-symbol-set-cache-variable   [causes compile error]
  :type 'x-symbol-class-faces)



;;;===========================================================================
;;;  The tables
;;;===========================================================================

(defvar x-symbol-specware-case-insensitive nil)
(defvar x-symbol-specware-token-shape nil)
(defvar x-symbol-specware-input-token-ignore nil)
(defvar x-symbol-specware-token-list 'identity)

(defvar x-symbol-specware-symbol-table      ; symbols (specware font)
  '((visiblespace "\\_spacespace")
    (Gamma "\\_Gamma")
    (Delta "\\_Delta")
    (Theta "\\_Theta")
    (Lambda "\\_Lambda")
    (Pi "\\_Pi")
    (Sigma "\\_Sigma")
    (Phi "\\_Phi")
    (Psi "\\_Psi")
    (Omega "\\_Omega")
    (alpha "\\_alpha")
    (beta "\\_beta")
    (gamma "\\_gamma")
    (delta "\\_delta")
    (epsilon1 "\\_epsilon")
    (zeta "\\_zeta")
    (eta "\\_eta")
    (theta "\\_theta")
    (kappa1 "\\_kappa")
    (lambda "\\_lambda")
    (mu "\\_mu")
    (nu "\\_nu")
    (xi "\\_xi")
    (pi "\\_pi")
    (rho1 "\\_rho")
    (sigma "\\_sigma")
    (tau "\\_tau")
    (phi1 "\\_phi")
    (chi "\\_chi")
    (psi "\\_psi")
    (omega "\\_omega")
    (notsign "\\_not")
    (logicaland "\\_and")
    (logicalor "\\_or")
    (universal1 "\\_forall")
    (existential1 "\\_exists")
    (epsilon "\\_some")
    (biglogicaland "\\_And")
    (ceilingleft "\\_lceil")
    (ceilingright "\\_rceil")
    (floorleft "\\_lfloor")
    (floorright "\\_rfloor")
    (bardash "\\_turnstile")
    (bardashdbl "\\_Turnstile")
    (semanticsleft "\\_lbrakk")
    (semanticsright "\\_rbrakk")
    (periodcentered "\\_cdot")
    (element "\\_in")
    (reflexsubset "\\_subseteq")
    (intersection "\\_inter")
    (union "\\_union")
    (bigintersection "\\_Inter")
    (bigunion "\\_Union")
    (sqintersection "\\_sqinter")
    (squnion "\\_squnion")
    (bigsqintersection "\\_Sqinter")
    (bigsqunion "\\_Squnion")
    (perpendicular "\\_bottom")
    (dotequal "\\_doteq")
    (wrong "\\_wrong")
    (equivalence "\\_equiv")
    (notequal "\\_noteq")
    (propersqsubset "\\_sqsubset")
    (reflexsqsubset "\\_sqsubseteq")
    (properprec "\\_prec")
    (reflexprec "\\_preceq")
    (propersucc "\\_succ")
    (approxequal "\\_approx")
    (similar "\\_sim")
    (simequal "\\_simeq")
    (lessequal "\\_le")
    (coloncolon "\\_Colon")
    (arrowleft "\\_leftarrow")
    (endash "\\_midarrow")
    (arrowright "\\_rightarrow")
    (arrowdblleft "\\_Leftarrow")
;   (nil "\\_Midarrow")
    (arrowdblright "\\_Rightarrow")
    (frown "\\_frown")
    (mapsto "\\_mapsto")
    (leadsto "\\_leadsto")
    (arrowup "\\_up")
    (arrowdown "\\_down")
    (notelement "\\_notin")
    (multiply "\\_times")
    (circleplus "\\_oplus")
    (circleminus "\\_ominus")
    (circlemultiply "\\_otimes")
    (circleslash "\\_oslash")
    (propersubset "\\_subset")
    (infinity "\\_infinity")
    (box "\\_box")
    (lozenge1 "\\_diamond")
    (circ "\\_circ")
    (bullet "\\_bullet")
    (bardbl "\\_parallel")
    (radical "\\_surd")
    (copyright "\\_copyright")))

(defvar x-symbol-specware-xsymbol-table    ; xsymbols
  '((Xi "\\_Xi")
    (Upsilon1 "\\_Upsilon")
    (iota "\\_iota")
    (upsilon "\\_upsilon")
    (plusminus "\\_plusminus")
    (division "\\_div")
    (longarrowright "\\_longrightarrow")
    (longarrowleft "\\_longleftarrow")
    (longarrowboth "\\_longleftrightarrow")
    (longarrowdblright "\\_Longrightarrow")
    (longarrowdblleft "\\_Longleftarrow")
    (longarrowdblboth "\\_Longleftrightarrow")
    (brokenbar "\\_bar")
    (hyphen "\\_hyphen")
    (macron "\\_inverse")
    (exclamdown "\\_exclamdown")
    (questiondown "\\_questiondown")
    (guillemotleft "\\_guillemotleft")
    (guillemotright "\\_guillemotright")
    (degree "\\_degree")
    (onesuperior "\\_onesuperior")
    (onequarter "\\_onequarter")
    (twosuperior "\\_twosuperior")
    (onehalf "\\_onehalf")
    (threesuperior "\\_threesuperior")
    (threequarters "\\_threequarters")
    (paragraph "\\_paragraph")
    (registered "\\_registered")
    (ordfeminine "\\_ordfeminine")
    (masculine "\\_ordmasculine")
    (section "\\_section")
    (sterling "\\_pounds")
    (yen "\\_yen")
    (cent "\\_cent")
    (currency "\\_currency")
    (braceleft2 "\\_lbrace")
    (braceright2 "\\_rbrace")
    (top "\\_top")
    (congruent "\\_cong")
    (club "\\_clubsuit")
    (diamond "\\_diamondsuit")
    (heart "\\_heartsuit")
    (spade "\\_spadesuit")
    (arrowboth "\\_leftrightarrow")
    (greaterequal "\\_ge")
    (proportional "\\_propto")
    (partialdiff "\\_partial")
    (ellipsis "\\_dots")
    (aleph "\\_aleph")
    (Ifraktur "\\_Im")
    (Rfraktur "\\_Re")
    (weierstrass "\\_wp")
    (emptyset "\\_emptyset")
    (angle "\\_angle")
    (gradient "\\_nabla")
    (product "\\_Prod")
    (arrowdblboth "\\_Leftrightarrow")
    (arrowdblup "\\_Up")
    (arrowdbldown "\\_Down")
    (angleleft "\\_langle")
    (angleright "\\_rangle")
    (summation "\\_Sum")
    (integral "\\_integral")
    (circleintegral "\\_ointegral")
    (dagger "\\_dagger")
    (sharp "\\_sharp")
    (star "\\_star")
    (smltriangleright "\\_triangleright")
    (triangleleft "\\_lhd")
    (triangle "\\_triangle")
    (triangleright "\\_rhd")
    (trianglelefteq "\\_unlhd")
    (trianglerighteq "\\_unrhd")
    (smltriangleleft "\\_triangleleft")
    (natural "\\_natural")
    (flat "\\_flat")
    (amalg "\\_amalg")
    (Mho "\\_mho")
    (arrowupdown "\\_updown")
    (longmapsto "\\_longmapsto")
    (arrowdblupdown "\\_Updown")
    (hookleftarrow "\\_hookleftarrow")
    (hookrightarrow "\\_hookrightarrow")
    (rightleftharpoons "\\_rightleftharpoons")
    (leftharpoondown "\\_leftharpoondown")
    (rightharpoondown "\\_rightharpoondown")
    (leftharpoonup "\\_leftharpoonup")
    (rightharpoonup "\\_rightharpoonup")
    (asym "\\_asymp")
    (minusplus "\\_minusplus")
    (bowtie "\\_bowtie")
    (centraldots "\\_cdots")
    (circledot "\\_odot")
    (propersuperset "\\_supset")
    (reflexsuperset "\\_supseteq")
    (propersqsuperset "\\_sqsupset")
    (reflexsqsuperset "\\_sqsupseteq")
    (lessless "\\_lless")
    (greatergreater "\\_ggreater")
    (unionplus "\\_uplus")
    (smile "\\_smile")
    (reflexsucc "\\_succeq")
    (dashbar "\\_stileturn")
    (biglogicalor "\\_Or")
    (bigunionplus "\\_Uplus")
    (daggerdbl "\\_ddagger")
    (bigbowtie "\\_Join")
    (booleans "\\_bool")
    (complexnums "\\_complex")
    (natnums "\\_nat")
    (rationalnums "\\_rat")
    (realnums "\\_real")
    (integers "\\_int")
    (lesssim "\\_lesssim")
    (greatersim "\\_greatersim")
    (lessapprox "\\_lessapprox")
    (greaterapprox "\\_greaterapprox")
    (definedas "\\_triangleq")
    (cataleft "\\_lparr")
    (cataright "\\_rparr")
    (bigcircledot "\\_Odot")
    (bigcirclemultiply "\\_Otimes")
    (bigcircleplus "\\_Oplus")
    (coproduct "\\_Coprod")
    (cedilla "\\_cedilla")
    (diaeresis "\\_dieresis")
    (acute "\\_acute")
    (hungarumlaut "\\_hungarumlaut")
    (lozenge "\\_lozenge")
    (smllozenge "\\_struct")
    (dotlessi "\\_index")
    (euro "\\_euro")
    (zero1 "\\_zero")
    (one1 "\\_one")
    (two1 "\\_two")
    (three1 "\\_three")
    (four1 "\\_four")
    (five1 "\\_five")
    (six1 "\\_six")
    (seven1 "\\_seven")
    (eight1 "\\_eight")
    (nine1 "\\_nine")
    ))

(defun x-symbol-specware-prepare-table (table)
  (mapcar (lambda (entry)
	    (list (car entry) nil
		  (cadr entry) ))
	  table))

(defvar x-symbol-specware-table
  (x-symbol-specware-prepare-table
   (append
    x-symbol-specware-user-table
    x-symbol-specware-symbol-table
    x-symbol-specware-xsymbol-table)))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; User-level settings for X-Symbol 
;;
;; this is MODE-ON CODING 8BITS UNIQUE SUBSCRIPTS IMAGE
(defcustom x-symbol-specware-auto-style
  '(t  	  ; MODE-ON: whether to turn on interactively
    nil   ;; x-symbol-coding
    'null ;; x-symbol-8bits	   [NEVER want it; null disables search]
    nil   ;; x-symbol-unique
    t     ;; x-symbol-subscripts
    nil)  ;; x-symbol-image
  "Variable used to document a language access.
See documentation of `x-symbol-auto-style'."
  :group 'x-symbol-specware
  :group 'x-symbol-mode
  :type 'x-symbol-auto-style)

;; FIXME da: is this needed?
(defcustom x-symbol-specware-auto-coding-alist nil
  "*Alist used to determine the file coding of SPECWARE buffers.
Used in the default value of `x-symbol-auto-mode-alist'.  See
variable `x-symbol-auto-coding-alist' for details."
  :group 'x-symbol-specware
  :group 'x-symbol-mode
  :type 'x-symbol-auto-coding)


     

(provide 'x-symbol-specware)
