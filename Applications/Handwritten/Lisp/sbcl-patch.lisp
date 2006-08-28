(in-package "SB-IMPL")

;(sb-ext:unlock-package "SB-IMPL")
;(sb-ext:unlock-package "SB-INT")
;(sb-ext:unlock-package "SB-EXT")
;(sb-ext:unlock-package "SB-C")


(eval-when (:compile-toplevel :load-toplevel :execute)
  (sb-ext:unlock-package "CL")
  (defparameter *default-package-use-list* '("CL")))

(sb-ext:without-package-locks
(defun %defpackage (name nicknames size shadows shadowing-imports
                    use imports interns exports implement lock doc-string
                    source-location)
  (declare (type simple-string name)
           (type list nicknames shadows shadowing-imports
                 imports interns exports)
           (type (or list (member :default)) use)
           (type (or simple-string null) doc-string)
          ; #!-sb-package-locks
          ; (ignore implement lock)
)
  (let ((package (or (find-package name)
                     (progn
                       (when (eq use :default)
                         (setf use '#.*default-package-use-list*))
                       (make-package name
                                     :use nil
                                     :internal-symbols (or size 10)
                                     :external-symbols (length exports))))))
    (sb-c:with-source-location (source-location)
      (setf (package-source-location package) source-location))
    (unless (string= (the string (package-name package)) name)
      (error 'simple-package-error
             :package name
             :format-control "~A is a nickname for the package ~A"
             :format-arguments (list name (package-name name))))
    (enter-new-nicknames package nicknames)
    ;; Handle shadows and shadowing-imports.
    (let ((old-shadows (package-%shadowing-symbols package)))
      (shadow shadows package)
      (dolist (sym-name shadows)
        (setf old-shadows (remove (find-symbol sym-name package) old-shadows)))
      (dolist (simports-from shadowing-imports)
        (let ((other-package (find-undeleted-package-or-lose
                              (car simports-from))))
          (dolist (sym-name (cdr simports-from))
            (let ((sym (find-or-make-symbol sym-name other-package)))
              (shadowing-import sym package)
              (setf old-shadows (remove sym old-shadows))))))
      (when old-shadows
        (warn 'package-at-variance
              :format-control "~A also shadows the following symbols:~%  ~S"
              :format-arguments (list name old-shadows))))
    ;; Handle USE.
    (unless (eq use :default)
      (let ((old-use-list (package-use-list package))
            (new-use-list (mapcar #'find-undeleted-package-or-lose use)))
        (use-package (set-difference new-use-list old-use-list) package)
        (let ((laterize (set-difference old-use-list new-use-list)))
          (when laterize
            (unuse-package laterize package)
            (warn 'package-at-variance
                  :format-control "~A used to use the following packages:~%  ~S"
                  :format-arguments (list name laterize))))))
    ;; Handle IMPORT and INTERN.
    (dolist (sym-name interns)
      (intern sym-name package))
    (dolist (imports-from imports)
      (let ((other-package (find-undeleted-package-or-lose (car
                                                            imports-from))))
        (dolist (sym-name (cdr imports-from))
          (import (list (find-or-make-symbol sym-name other-package))
                  package))))
    ;; Handle exports.
    (let ((old-exports nil)
          (exports (mapcar (lambda (sym-name) (intern sym-name package))
                           exports)))
      (do-external-symbols (sym package)
        (push sym old-exports))
      (export exports package)
      (let ((diff (set-difference old-exports exports)))
        (when diff
          (warn 'package-at-variance
                :format-control "~A also exports the following symbols:~%  ~S"
                :format-arguments (list name diff)))))
    ;#!+sb-package-locks
    (progn
      ;; Handle packages this is an implementation package of
      (dolist (p implement)
        (add-implementation-package package p))
      ;; Handle lock
      (setf (package-lock package) lock))
    ;; Handle documentation.
    (setf (package-doc-string package) doc-string)
    package))

(defun eval-in-lexenv (original-exp lexenv)
  (declare (optimize (safety 1)))
  ;; (aver (lexenv-simple-p lexenv))
  (handler-bind
      ((sb-c:compiler-error
        (lambda (c)
          (if (boundp 'sb-c::*compiler-error-bailout*)
              ;; if we're in the compiler, delegate either to a higher
              ;; authority or, if that's us, back down to the
              ;; outermost compiler handler...
              (progn
                (signal c)
                nil)
              ;; ... if we're not in the compiler, better signal the
              ;; error straight away.
              (invoke-restart 'sb-c::signal-error)))))
    (let ((exp (macroexpand original-exp lexenv)))
      (typecase exp
        (symbol
         (ecase (info :variable :kind exp)
           (:constant
            (values (info :variable :constant-value exp)))
           ((:special :global)
            (symbol-value exp))
           ;; FIXME: This special case here is a symptom of non-ANSI
           ;; weirdness in SBCL's ALIEN implementation, which could
           ;; cause problems for e.g. code walkers. It'd probably be
           ;; good to ANSIfy it by making alien variable accessors
           ;; into ordinary forms, e.g. (SB-UNIX:ENV) and (SETF
           ;; SB-UNIX:ENV), instead of magical symbols, e.g. plain
           ;; SB-UNIX:ENV. Then if the old magical-symbol syntax is to
           ;; be retained for compatibility, it can be implemented
           ;; with DEFINE-SYMBOL-MACRO, keeping the code walkers
           ;; happy.
           (:alien
            (%eval original-exp lexenv))))
        (list
         (let ((name (first exp))
               (n-args (1- (length exp))))
           (case name
             ((function)
              (unless (= n-args 1)
                (error "wrong number of args to FUNCTION:~% ~S" exp))
              (let ((name (second exp)))
                (if (and (legal-fun-name-p name)
                         (not (consp (let ((sb-c:*lexenv* lexenv))
                                       (sb-c:lexenv-find name funs)))))
                    (%coerce-name-to-fun name)
                    (%eval original-exp lexenv))))
             ((quote)
              (unless (= n-args 1)
                (error "wrong number of args to QUOTE:~% ~S" exp))
              (second exp))
             (if (unless (or (= n-args 2) (= n-args 3))
                   (error "Wrong number of args to IF:~% ~S." exp))
               (if (eval-in-lexenv (second  exp) lexenv)
                   (eval-in-lexenv (third exp) lexenv)
                 (eval-in-lexenv (fourth exp) lexenv)))
             (setq
              (unless (evenp n-args)
                (error "odd number of args to SETQ:~% ~S" exp))
              (unless (zerop n-args)
                (do ((name (cdr exp) (cddr name)))
                    ((null name)
                     (do ((args (cdr exp) (cddr args)))
                         ((null (cddr args))
                          ;; We duplicate the call to SET so that the
                          ;; correct value gets returned.
                          (set (first args) (eval-in-lexenv (second args) lexenv)))
                       (set (first args) (eval-in-lexenv (second args) lexenv))))
                  (let ((symbol (first name)))
                    (case (info :variable :kind symbol)
                      (:special)
                      (t (return (%eval original-exp lexenv))))
                    (unless (type= (info :variable :type symbol)
                                   *universal-type*)
                      ;; let the compiler deal with type checking
                      (return (%eval original-exp lexenv)))))))
             ((progn)
              (eval-progn-body (rest exp) lexenv))
             ((eval-when)
              ;; FIXME: DESTRUCTURING-BIND returns ARG-COUNT-ERROR
              ;; instead of PROGRAM-ERROR when there's something wrong
              ;; with the syntax here (e.g. missing SITUATIONS). This
              ;; could be fixed by hand-crafting clauses to catch and
              ;; report each possibility, but it would probably be
              ;; cleaner to write a new macro
              ;; DESTRUCTURING-BIND-PROGRAM-SYNTAX which does
              ;; DESTRUCTURING-BIND and promotes any mismatch to
              ;; PROGRAM-ERROR, then to use it here and in (probably
              ;; dozens of) other places where the same problem
              ;; arises.
              (destructuring-bind (eval-when situations &rest body) exp
                (declare (ignore eval-when))
                (multiple-value-bind (ct lt e)
                    (sb-c:parse-eval-when-situations situations)
                  ;; CLHS 3.8 - Special Operator EVAL-WHEN: The use of
                  ;; the situation :EXECUTE (or EVAL) controls whether
                  ;; evaluation occurs for other EVAL-WHEN forms; that
                  ;; is, those that are not top level forms, or those
                  ;; in code processed by EVAL or COMPILE. If the
                  ;; :EXECUTE situation is specified in such a form,
                  ;; then the body forms are processed as an implicit
                  ;; PROGN; otherwise, the EVAL-WHEN form returns NIL.
                  (declare (ignore ct lt))
                  (when e
                    (eval-progn-body body lexenv)))))
             ((locally)
              (eval-locally exp lexenv))
             ((macrolet)
              (destructuring-bind (definitions &rest body)
                  (rest exp)
                (let ((lexenv
                       (let ((sb-c:*lexenv* lexenv))
                         (sb-c::funcall-in-macrolet-lexenv
                          definitions
                          (lambda (&key funs)
                            (declare (ignore funs))
                            sb-c:*lexenv*)
                          :eval))))
                  (eval-locally `(locally ,@body) lexenv))))
             ((symbol-macrolet)
              (destructuring-bind (definitions &rest body) (rest exp)
                (multiple-value-bind (lexenv vars)
                    (let ((sb-c:*lexenv* lexenv))
                      (sb-c::funcall-in-symbol-macrolet-lexenv
                       definitions
                       (lambda (&key vars)
                         (values sb-c:*lexenv* vars))
                       :eval))
                  (eval-locally `(locally ,@body) lexenv :vars vars))))
             (t
              (if (and (symbolp name)
                       (eq (info :function :kind name) :function))
                  (collect ((args))
                    (dolist (arg (rest exp))
                      (args (eval-in-lexenv arg lexenv)))
                    (apply (symbol-function name) (args)))
                  (%eval exp lexenv))))))
        (t
         exp)))))

(defun interactive-eval (form)
  "Evaluate FORM, returning whatever it returns and adjusting ***, **, *,
   +++, ++, +, ///, //, /, and -."
  (setf - form)
  (unwind-protect
      (let ((results
	     (multiple-value-list
	      (if (and (fboundp 'cl::commandp) (funcall 'cl::commandp form))
		  (funcall 'cl::invoke-command-interactive form)
		(eval form)))))
	(setf /// //
	      // /
	      / results
	      *** **
	      ** *
	      * (car results)))
    (setf +++ ++
        ++ +
        + -))
  (unless (boundp '*)
    ;; The bogon returned an unbound marker.
    ;; FIXME: It would be safer to check every one of the values in RESULTS,
    ;; instead of just the first one.
    (setf * nil)
    (cerror "Go on with * set to NIL."
            "EVAL returned an unbound marker."))
  (values-list /))
)