
(in-package "SNARK")


;; This adds a SNARK setting to the Settings menu.
;; It handles the cases where the SNARK setting can take on
;; Two values t or nil.


;;; --------------------------------------

(defvar *Menu-commands* nil)

(defun add-menu-command (command)
  (setq *Menu-commands* (cons command *Menu-commands*)))

(defun clear-menu-command ()
  (setq *Menu-commands* ()))

(defun eval-menu-commands ()
  (re::emacs-eval (format nil "(progn ~A ~A ~A)"
			  "(select-frame *current-specware-ui-foci-frame*) "
			  "(switch-to-buffer *mspe-buffer*) "
			  (apply #'concatenate (cons 'string (reverse *Menu-commands*))))))

;;; --------------------------------------

(defun add-menu-button (button)
  (add-menu-command (format nil "(add-menu-button ~A)" button)))


;  (let
;  ((line1 "(select-frame *current-specware-ui-foci-frame*) ")
;   (line2 "(switch-to-buffer *mspe-buffer*) ")
;   (line3 (format nil "(add-menu-button ~A)" button)))
;  (re::emacs-eval (format nil "(progn ~A ~A ~A)" line1 line2 line3)))
;  )

(defun add-snark-binary-menu-option (name default &optional submenu)
  (let*
      ((line1 "") ; (select-frame *current-specware-ui-foci-frame*) ")
       (line2 "") ; (switch-to-buffer *mspe-buffer*) ")
       (defVariable (format nil "(defvar ~A nil)" name))
       (toggleMe (format nil "(progn (setq ~A (not ~A)) (send-message-to-lisp (if ~A \"(snark::default-~A t)\" \"(snark::default-~A nil)\")))" name name name name name))
       (submenu (if submenu (format nil "~S" submenu) ""))
       (line3 (format nil "(add-menu-button '(\"Settings\" \"SNARK\" ~A) [ ~S ~A :style toggle :selected ~A])" submenu name toggleMe name))
       (menu-option (format nil "(progn ~A ~A ~A )" line1 line2 line3)))
    (add-menu-command defVariable)
    (if default 
	(progn 
	  (add-menu-command (format nil "(setq ~A t)" name))
	  (eval (read-from-string (format nil "(snark::default-~A t)" name)))
	  )
      (progn
	(eval (read-from-string (format nil "(snark::default-~A nil)" name))))
      )
    (add-menu-command menu-option)
    ))



(defun add-snark-multiple-options-menu-option (name options &optional submenu)
  (let*
      ((defVariable (format nil "(defvar ~A '~A)" name (car options)))
       (toggleMe #'(lambda (x) (format nil "(progn (setq ~A '~A) (message \"~A\") (send-message-to-lisp \"(snark::default-~A '~S)\"))" name x x name x)))
       (submenu (if submenu (format nil "~S" submenu) ""))
       (menu-option #'(lambda(x) 
			 (format 
			  nil 
			  "(add-menu-button '(\"Settings\" \"SNARK\" ~A) [ \"~A-~A\" ~A :style radio :selected (eq ~A '~A)])" 
			  submenu name x (funcall toggleMe x) name x))))
    (add-menu-command defVariable)
    (eval (read-from-string (format nil "(snark::default-~A '~S)" name (car options))))
    (mapcar #'(lambda(x) (add-menu-command (funcall menu-option x))) options)
    ()
    ))


;; Test case:
;; (add-snark-multiple-options-menu-option "Use-Literal-Ordering-With-Hyperresolution" '(nil neg pos) "G")

;(defun snark::default-print-rows-when-derived (value)
;  (setq SNARK::PRINT-ROWS-WHEN-DERIVED value))

(defun add-snark-menu-options ()
  (let*
      ((rp "(progn (setq recursive-path-flag t   none-of-above nil knuth-bendix-flag nil) (send-message-to-lisp \"(snark::use-term-ordering :recursive-path)\"))")
       (kb "(progn (setq recursive-path-flag nil none-of-above nil knuth-bendix-flag t) (send-message-to-lisp \"(snark::use-term-ordering :knuth-bendix)\"))")
       (na "(progn (setq recursive-path-flag nil none-of-above t knuth-bendix-flag nil) (send-message-to-lisp \"(snark::use-term-ordering nil)\"))")
       )

    (clear-menu-command)
    ;; sjw: 4/16/01 Richard Waldinger thinks resolution is better default than hyperresolution for real problems
    (add-snark-binary-menu-option "Use-Resolution" t)
    (add-snark-binary-menu-option "Use-Hyperresolution" Nil)
    (add-snark-binary-menu-option "Use-Paramodulation" t)
  
    (add-snark-binary-menu-option "Use-Negative-Hyperresolution" Nil "Strategy")
    (Add-Snark-Binary-Menu-Option "Use-Ur-Resolution" Nil "Strategy")
    (Add-Snark-Binary-Menu-Option "Use-Ur-Pttp" Nil "Strategy")
    (Add-Snark-Binary-Menu-Option "Use-Factoring" Nil "Strategy")
    (Add-Snark-Binary-Menu-Option "Use-Unit-Restriction" Nil "Strategy")
    (Add-Snark-Binary-Menu-Option "Use-Input-Restriction" Nil "Strategy")
    (Add-Snark-Binary-Menu-Option "Use-Code-For-Equality" T "Theories")
    (add-menu-command "(defvar recursive-path-flag nil)")
    (add-menu-command "(defvar knuth-bendix-flag nil)")
    (add-menu-command "(defvar none-of-above nil)")
    (add-menu-command "(setq recursive-path-flag t)")

    (add-menu-button "'(\"Settings\" \"SNARK\"  \"Ordering\") \"Select term comparison\"")
    (add-menu-button (format nil "'(\"Settings\" \"SNARK\" \"Ordering\") [\"Recursive Path\" ~A :style radio :selected recursive-path-flag]" rp))
    (add-menu-button (format nil "'(\"Settings\" \"SNARK\" \"Ordering\") [\"Knuth Bendix\" ~A :style radio :selected knuth-bendix-flag]" kb))
    (add-menu-button (format nil "'(\"Settings\" \"SNARK\" \"Ordering\") [\"None of the above\" ~A :style radio :selected none-of-above]" na))
    (add-menu-button "'(\"Settings\" \"SNARK\" \"Ordering\") \"------------\"")
  

    (Add-Snark-multiple-options-Menu-Option "Use-Literal-Ordering-With-Resolution" '(nil literal-ordering-a literal-ordering-n literal-ordering-p) "Ordering")
    (add-menu-button "'(\"Settings\" \"SNARK\" \"Ordering\") \"------------\"")

    (Add-Snark-multiple-options-Menu-Option "Use-Literal-Ordering-With-Hyperresolution" '(nil literal-ordering-a literal-ordering-n literal-ordering-p) "Ordering")
    (add-menu-button "'(\"Settings\" \"SNARK\" \"Ordering\") \"------------\"")

    (Add-Snark-multiple-options-Menu-Option "Use-Literal-Ordering-With-Negative-Hyperresolution" '(nil literal-ordering-a literal-ordering-n literal-ordering-p) "Ordering")
    (add-menu-button "'(\"Settings\" \"SNARK\" \"Ordering\") \"------------\"")

    (Add-Snark-multiple-options-Menu-Option "Use-Literal-Ordering-With-Ur-Resolution" '(nil literal-ordering-a literal-ordering-n literal-ordering-p) "Ordering")
    (add-menu-button "'(\"Settings\" \"SNARK\" \"Ordering\") \"------------\"")

    (Add-Snark-multiple-options-Menu-Option "Use-Literal-Ordering-With-Paramodulation" '(nil literal-ordering-a literal-ordering-n literal-ordering-p) "Ordering")
    (add-menu-button "'(\"Settings\" \"SNARK\" \"Ordering\") \"------------\"")

    (Add-Snark-Binary-Menu-Option "Use-Indefinite-Answers" Nil "Answer Creation")
    (Add-Snark-Binary-Menu-Option "Use-Conditional-Answer-Creation" T "Answer Creation")
    (Add-Snark-Binary-Menu-Option "Use-Constructive-Answer-Restriction" T "Answer Creation")
    (Add-Snark-Binary-Menu-Option "Use-Answers-During-Subsumption" T "Answer Creation")
    (Add-Snark-Binary-Menu-Option "Use-Constraint-Solver-In-Subsumption" Nil "Theories")
    (Add-Snark-Binary-Menu-Option "Rewrite-Terms-In-Answer" T "Answer Creation")
    (Add-Snark-Binary-Menu-Option "Rewrite-Terms-In-Constraint" Nil "Theories")
    (Add-Snark-Binary-Menu-Option "Use-Embedded-Rewrites" T "Strategy")
    (Add-Snark-Binary-Menu-Option "Use-Replacement-Resolution-With-X=X" T "Strategy")
    (Add-Snark-Binary-Menu-Option "Use-Paramodulation-Only-Into-Units" Nil "Strategy")
    (Add-Snark-Binary-Menu-Option "Use-Paramodulation-Only-From-Units" Nil "Strategy")
    (Add-Snark-Binary-Menu-Option "Use-Single-Replacement-Paramodulation" Nil "Strategy")
    (Add-Snark-Binary-Menu-Option "Assert-Supported" Nil "Strategy")
    (Add-Snark-Binary-Menu-Option "Assume-Supported" T "Strategy")
    (Add-Snark-Binary-Menu-Option "Prove-Supported" T "Strategy")
    (Add-Snark-Binary-Menu-Option "Assert-Sequential" Nil "Strategy")
    (Add-Snark-Binary-Menu-Option "Assume-Sequential" Nil "Strategy")
    (Add-Snark-Binary-Menu-Option "Prove-Sequential" Nil "Strategy")
					;  (Add-Snark-Binary-Menu-Option "Number-Of-Given-Rows-Limit" Nil "Resources")
;  (Add-Snark-Binary-Menu-Option "Number-Of-Rows-Limit" Nil "Resources")
					;       (Add-Snark-Binary-Menu-Option "Agenda-Length-Before-Simplification-Limit" 10000)
					;       (Add-Snark-Binary-Menu-Option "Agenda-Length-Limit" 3000);
					;  (Add-Snark-Binary-Menu-Option "Run-Time-Limit" Nil "Resources")
;  (Add-Snark-Binary-Menu-Option "Row-Weight-Limit" Nil "Resources")
					;  (Add-Snark-Binary-Menu-Option "Row-Weight-Before-Simplification-Limit" Nil "Resources")
;  (Add-Snark-Binary-Menu-Option "Level-Pref-For-Giving" Nil "Resources")
					;       (Add-Snark-Binary-Menu-Option "Variable-Weight" 1)
					;       (Add-Snark-Binary-Menu-Option "Agenda-Ordering-Function" Row-Weight+Depth)
					;       (Add-Snark-Binary-Menu-Option "Pruning-Tests" (Add-Snark-Binary-Menu-Option "Row-Weight-Limit-Exceeded))
					;       (Add-Snark-Binary-Menu-Option "Pruning-Tests-Before-Simplification" (Add-Snark-Binary-Menu-Option "Row-Weight-Before-Simplification-Limit-Exceeded))
    (Add-Snark-Binary-Menu-Option "Use-Clausification" T "Strategy")
    (Add-Snark-Binary-Menu-Option "Use-Clausification-Rewrites" Nil "Strategy")
    (Add-Snark-Binary-Menu-Option "Use-Magic-Transformation" Nil "Strategy")
    (Add-Snark-Binary-Menu-Option "Use-And-Splitting" Nil "Strategy")

    ;; Not implemented in new version:
    ;; (Add-Snark-Binary-Menu-Option "Use-Case-Splitting" Nil "Strategy")

    (Add-Snark-Binary-Menu-Option "Use-Ac-Connectives" T "Theories")
    (Add-Snark-Binary-Menu-Option "Use-Kif-Rewrites" T "Theories")
    (Add-Snark-Binary-Menu-Option "Use-Many-To-One-Subsumption" Nil "Strategy")
    (Add-Snark-Binary-Menu-Option "Use-Associative-Unification" Nil "Theories")
    (Add-Snark-Binary-Menu-Option "Use-Dp-Subsumption" Nil "Strategy")
					;       (Add-Snark-Binary-Menu-Option "Unify-Bag-Basis-Size-Limit" 1000)
					;       (Add-Snark-Binary-Menu-Option "Ao-Args-To-Bdd-Strategy" :Smallest-First)
    (Add-Snark-Binary-Menu-Option "Use-Term-Memory-Deletion" T "Resources")
    ;; (Add-Snark-Binary-Menu-Option "Use-Sort-Implementation" :Dp)

    ;; Name changed in new version:
    ;; (Add-Snark-Binary-Menu-Option "Use-Number-Sorts" T "Theories")
    (Add-Snark-Binary-Menu-Option "Use-Lisp-Types-As-Sorts" T "Theories")

    (Add-Snark-Binary-Menu-Option "Use-Numbers-As-Constructors" T "Theories")
    (Add-Snark-Binary-Menu-Option "Use-Code-For-Characters" T "Theories")
    (Add-Snark-Binary-Menu-Option "Use-Code-For-Numbers" T "Theories")
    (Add-Snark-Binary-Menu-Option "Use-Code-For-Lists" T "Theories")
    (Add-Snark-Binary-Menu-Option "Use-Unify-Bag-Constant-Abstraction" Nil)
    (Add-Snark-Binary-Menu-Option "Use-Function-Creation" Nil)
    (Add-Snark-Binary-Menu-Option "Use-Subsumption" T)
    (Add-Snark-Binary-Menu-Option "Use-Subsumption-By-False" T)
    (Add-Snark-Binary-Menu-Option "Use-Simplification-By-Units" T)
    (Add-Snark-Binary-Menu-Option "Use-Simplification-By-Equalities" T)
					;       (Add-Snark-Binary-Menu-Option "Use-Term-Ordering" :Recursive-Path)
    (Add-Snark-Binary-Menu-Option "Use-Default-Ordering" Nil "Ordering")
					;       (Add-Snark-Binary-Menu-Option "Recursive-Path-Ordering-Status" :Multiset)
					;       (Add-Snark-Binary-Menu-Option "Knuth-Bendix-Ordering-Status" :Left-To-Right)

    (Add-Snark-Binary-Menu-Option "Print-Rows-When-Derived" t )
    (eval-menu-commands)
    ))

;; 
;;(Setq SNARK::PRINT-ROWS-WHEN-GIVEN" NIL) 
;;(SETQ SNARK::PRINT-ROWS-WHEN-DERIVED" NIL)
;;(SNARK::USE-TERM-ORDERING :RECURSIVE-PATH) 
;;
