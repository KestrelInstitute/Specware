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
           ;; #!-sb-package-locks
           ;; (ignore implement lock)
           )
  (with-package-graph ()
    (let* ((existing-package (find-package name))
           (use (use-list-packages existing-package use))
           (shadowing-imports (import-list-symbols shadowing-imports))
           (imports (import-list-symbols imports)))
      (if existing-package
          (update-package-with-variance existing-package name
                                        nicknames source-location
                                        shadows shadowing-imports
                                        use imports interns exports
                                        implement lock doc-string)
          (let ((package (make-package name
                                       :use nil
                                       :internal-symbols (or size 10)
                                       :external-symbols (length exports))))
            (update-package package
                            nicknames source-location
                            shadows shadowing-imports
                            use imports interns exports
                            implement lock doc-string))))))
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

   ;; %COMPILER-DEFUN doesn't do this except at compile-time, when it
  ;; also checks package locks. By doing this here we let (SETF
  ;; FDEFINITION) do the load-time package lock checking before
  ;; we frob any existing inline expansions.
  (sb-c::%set-inline-expansion name nil inline-lambda)

  (sb-c::note-name-defined name :function)

  (when doc
    (setf (fdocumentation name 'function) doc))
  name)

(defun interactive-eval (form &key (eval #'eval))
  "Evaluate FORM, returning whatever it returns and adjusting ***, **, *,
   +++, ++, +, ///, //, /, and -."
  (setf - form)
  (unwind-protect
       (let ((results (multiple-value-list (funcall eval form))))
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

(defvar *fasl-type* sb-fasl:*fasl-file-type*)

(provide "SBCL_PATCH")
