(in-package :sb-impl)

;(sb-ext:unlock-package "SB-IMPL")
;(sb-ext:unlock-package "SB-INT")
;(sb-ext:unlock-package "SB-EXT")
;(sb-ext:unlock-package "SB-C")


(eval-when (:compile-toplevel :load-toplevel :execute)
  (sb-ext:unlock-package "CL")
  (defparameter *default-package-use-list* '("CL")))

(sb-ext:without-package-locks

(if (find-symbol "USE-LIST-PACKAGES" "SB-IMPL")
(defun use-list-packages (package package-designators)
  (cond ((listp package-designators)
         (mapcar #'find-undeleted-package-or-lose package-designators))
        (package
         ;; :default for an existing package means preserve the
         ;; existing use list
         (package-use-list package))
        (t
         ;; :default for a new package is the *default-package-use-list*
         '#.*default-package-use-list*)))

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
)

#-sb-xc-host
(defun %defun (name def doc inline-lambda source-location)
  (declare (ignore source-location))
  (declare (type function def))
  (declare (type (or null simple-string) doc))
  (aver (legal-fun-name-p name)) ; should've been checked by DEFMACRO DEFUN
  (sb-c:%compiler-defun name inline-lambda nil)
;;; Heavy-handed way to get rid of spurious warnings
;  (when (fboundp name)
;    (/show0 "redefining NAME in %DEFUN")
;    (style-warn "redefining ~S in DEFUN" name))
  (setf (fdefinition name) def)

  ;; FIXME: I want to do this here (and fix bug 137), but until the
  ;; breathtaking CMU CL function name architecture is converted into
  ;; something sane, (1) doing so doesn't really fix the bug, and
  ;; (2) doing probably isn't even really safe.
  #+nil (setf (%fun-name def) name)

  (when doc
    (setf (fdocumentation name 'function) doc))
  name)

#|
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
|#

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


;;; Rename on windows doesn't allow overwrite of file
#+win32
(defun sb-unix:unix-rename (name1 name2)
  (declare (type sb-unix:unix-pathname name1 name2))
  (when (sb-unix:unix-stat name2)
    (sb-unix:unix-unlink name2))
  (sb-win32::void-syscall* (("MoveFile" 8 t) sb-win32::system-string sb-win32::system-string)
                           name1 name2))

)

;; #+win32
;; (let ((proto-db '(("ip" . 0) ("icmp" . 1) ("tcp" . 6) ("udp" . 17))))
;;   (defun sb-bsd-sockets:get-protocol-by-name (proto)
;;     (declare (string proto))
;;     (cdr (assoc (string-downcase proto) proto-db :test #'equal))))

;; read-line in windows includes \Return (^M) at end
(defun ansi-stream-read-line-from-frc-buffer (stream eof-error-p eof-value)
  (prepare-for-fast-read-char stream
    (declare (ignore %frc-method%))
    (let ((chunks-total-length 0)
          (chunks nil))
      (declare (type index chunks-total-length)
               (list chunks))
      (labels ((refill-buffer ()
                 (prog1
                     (fast-read-char-refill stream nil nil)
                   (setf %frc-index% (ansi-stream-in-index %frc-stream%))))
               (newline-position ()
                 (position #\Newline (the (simple-array character (*))
                                       %frc-buffer%)
                           :test #'char=
                           :start %frc-index%))
               (make-and-return-result-string (pos)
                 (let* ((crlf-p (and pos
                                     (not (eq pos 0))
                                     (eq (elt (the (simple-array character (*))
                                                %frc-buffer%)
                                              (- pos 1))
                                         #\Return)))
                        (pos (if (and crlf-p pos) (- pos 1) pos))
                        (len (+ (- (or pos %frc-index%)
                                   %frc-index%)
                                chunks-total-length))
                        (res (make-string len))
                        (start 0))
                   (declare (type index start))
                   (when chunks
                     (dolist (chunk (nreverse chunks))
                       (declare (type (simple-array character) chunk))
                       (replace res chunk :start1 start)
                       (incf start (length chunk))))
                   (unless (null pos)
                     (replace res %frc-buffer%
                              :start1 start
                              :start2 %frc-index% :end2 pos)
                     (setf %frc-index% (1+ pos))
                     (when crlf-p (incf %frc-index%)))
                   (done-with-fast-read-char)
                   (return-from ansi-stream-read-line-from-frc-buffer (values res (null pos)))))
               (add-chunk ()
                 (let* ((end (length %frc-buffer%))
                        (len (- end %frc-index%))
                        (chunk (make-string len)))
                   (replace chunk %frc-buffer% :start2 %frc-index% :end2 end)
                   (push chunk chunks)
                   (incf chunks-total-length len)
                   (when (refill-buffer)
                     (make-and-return-result-string nil)))))
        (declare (inline make-and-return-result-string
                         refill-buffer))
        (when (and (= %frc-index% +ansi-stream-in-buffer-length+)
                   (refill-buffer))
          ;; EOF had been reached before we read anything
          ;; at all. Return the EOF value or signal the error.
          (done-with-fast-read-char)
          (return-from ansi-stream-read-line-from-frc-buffer
            (values (eof-or-lose stream eof-error-p eof-value) t)))
        (loop
           (let ((pos (newline-position)))
             (if pos
                 (make-and-return-result-string pos)
                 (add-chunk))))))))


(in-package :cl-user)

(define-alien-variable ("dynamic_space_size" dynamic-space-size-bytes)
    unsigned-long)
(defun heap-n-bytes ()
  (+ dynamic-space-size-bytes
     (- sb-vm::read-only-space-end sb-vm::read-only-space-start)
     (- sb-vm::static-space-end sb-vm::static-space-start)))

