;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: snark -*-
;;; File: utilities.lisp
;;; The contents of this file are subject to the Mozilla Public License
;;; Version 1.1 (the "License"); you may not use this file except in
;;; compliance with the License. You may obtain a copy of the License at
;;; http://www.mozilla.org/MPL/
;;;
;;; Software distributed under the License is distributed on an "AS IS"
;;; basis, WITHOUT WARRANTY OF ANY KIND, either express or implied. See the
;;; License for the specific language governing rights and limitations
;;; under the License.
;;;
;;; The Original Code is SNARK.
;;; The Initial Developer of the Original Code is SRI International.
;;; Portions created by the Initial Developer are Copyright (C) 1981-2003.
;;; All Rights Reserved.
;;;
;;; Contributor(s): Mark E. Stickel <stickel@ai.sri.com>.

(in-package :snark)

(defmacro in-language (language)
  (cl:assert (member language '(:hpkb-with-kif-3.0 :hpkb-with-ansi-kif)))
  `(use-kif-version ',language))

(defmacro in-kb (kb)
  ;; use suspend/resume for this?  okbc calls?
  (declare (ignore kb))
  `(warn "Ignoring IN-KB form."))

(defmacro has-author (author)
  `(setf *form-author* ',author))

(defmacro has-documentation (documentation)
  `(setf *form-documentation* ',documentation))

(defmacro has-name (name)
  `(setf *form-name* ',name))

(defmacro has-source (source)
  `(setf *form-source* ',source))

(defvar *read-assertion-file-commands* '(assertion
                                         has-author	;has-xxx specifies xxx for later assertions
                                         has-documentation
                                         has-name
                                         has-source
                                         in-package
                                         in-language
                                         in-kb
                                         ))		;every other form is an assertion

(defvar *read-assertion-file-keywords* '((:author *form-author*)
                                         (:documentation *form-documentation*)
                                         (:name *form-name*)
                                         (:source *form-source*)))

(defvar *read-assertion-file-format* nil)
(defvar *read-assertion-file-if-does-not-exist* :error)
(defvar *read-assertion-file-verbose* nil)
(defvar *read-assertion-file-package* :snark-user)

(defun read-assertion-file (filespec
                            &key
                            (format *read-assertion-file-format*)
                            (if-does-not-exist *read-assertion-file-if-does-not-exist*)
                            (verbose *read-assertion-file-verbose*)
                            (package *read-assertion-file-package*)
                            (readtable *readtable*)
                            hash-dollar)
  ;; read-asssertion-file executes commands and return a list of calls on 'assertion'
  ;; every form that is not a command (commands are named in *read-assertion-file-commands*)
  ;; is treated as a formula to be asserted
  (cond
   ((eq :cycl format)
    (return-from read-assertion-file
      (read-cycl-assertion-file
       filespec
       :if-does-not-exist if-does-not-exist
       :verbose verbose
       :hash-dollar hash-dollar)))
   ((eq :km format)
    (return-from read-assertion-file
      (read-km-assertion-file
       filespec
       :if-does-not-exist if-does-not-exist
       :verbose verbose
       :hash-dollar hash-dollar))))
  (prog->
    (identity readtable -> *readtable*)
    (identity *read-assertion-file-commands* -> commands)
    (identity *read-assertion-file-keywords* -> keywords)
    (progv (mapcar #'second keywords)
           (consn nil nil (length keywords))
      (funcall (cond
                ((eq :tptp format)
                 'mapnconc-tptp-file-forms)
                (t
                 'mapnconc-file-forms))
               filespec
               :if-does-not-exist if-does-not-exist
               :package package
               ->* form)
      (and (consp form)
           (symbolp (first form))
           (first (member (first form) commands
                          :test #'string-equal		;command matching ignores package and case
                          :key #'symbol-name))
           -> command)
      (case command
        ((nil)
         (setf form (list 'assertion form)))
        (assertion
         (setf form (cons command (append (rest form) nil)))
         (setf command nil))
        (otherwise
         (eval (cons command (rest form)))))
      (unless command
        (case (and (consp form) (first form))
          (assertion
           (cond
            ((getf (cddr form) :ignore)
             nil)
            (t
             (dolist (x keywords)
               (let ((v (symbol-value (second x))))
                 (when (and v (eq none (getf (cddr form) (first x) none)))
                   (nconc form (list (first x) v)))))
             (list form))))
          (otherwise
           (list form)))))))

(defun read-cycl-assertion-file (filespec
                                 &key
                                 (if-does-not-exist *read-assertion-file-if-does-not-exist*)
                                 (verbose *read-assertion-file-verbose*)
                                 hash-dollar)
  ;; do read-assertion-file using case-sensitive reader
  ;; #$expressions will be read into CYCL package
  ;; other expressions will also be read into CYCL package, unless in-package is used in the file
  (let ((*hash-dollar-package* (cycl-package)))
    (read-assertion-file
     filespec
     :if-does-not-exist if-does-not-exist
     :verbose verbose
     :package *hash-dollar-package*
     :readtable (if hash-dollar *hash-dollar-readtable* *readtable*))))

(defun read-km-assertion-file (filespec &key
                                        (if-does-not-exist *read-assertion-file-if-does-not-exist*)
                                        (verbose *read-assertion-file-verbose*)
                                        hash-dollar)
  ;; do read-assertion-file using case-sensitive reader
  ;; #$expressions will be read into KM package
  ;; other expressions will also be read into KM package, unless in-package is used in the file
  (let ((*hash-dollar-package* (km-package)))
    (read-assertion-file
     filespec
     :if-does-not-exist if-does-not-exist
     :verbose verbose
     :package *hash-dollar-package*
     :readtable (if hash-dollar *hash-dollar-readtable* *readtable*))))

(defun translate-assertion-file-to-tptp-format (inputfilespec &optional outputfilespec
                                                              &rest read-assertion-file-options)
  (let ((snark-state (suspend-snark)))
    (unwind-protect
      (progn
        (initialize)
        (use-subsumption nil)
        (use-simplification-by-units nil)
        (use-simplification-by-equalities nil)
        (print-options-when-starting nil)
        (print-summary-when-finished nil)
        (print-rows-when-derived nil)
        (mapc #'eval (apply #'read-assertion-file inputfilespec read-assertion-file-options))
        (closure)
        (cond
         (outputfilespec
          (with-open-file (*standard-output* outputfilespec :direction :output)
            (print-rows :format :tptp)))
         (t
          (print-rows :format :tptp))))
      (resume-snark snark-state))
    nil))

(defun assertion-wff (x)
  (cond
   ((and (consp x)
         (eq 'assertion (car x))
         (consp (cdr x)))
    (second x))
   #+ignore
   ((and (consp x)
         (eq 'assert (car x))
         (consp (cdr x))
         (let ((x (second x)))
           (and (consp x)
                (eq 'quote (car x))
                (consp (cdr x))
                (null (cddr x)))))
    (warn "value ~S is not of the expected form (ASSERTION expr ...)." x)
    (second (second x)))
   (t
    (error "value ~S is not of the expected form (ASSERTION expr ...)." x))))

(defun km-package ()
  cl-user::*km-package*)

(defvar *refute-file-options* nil)
(defvar *refute-file-ignore-errors* nil)
(defvar *refute-file-verbose* t)
(defvar *refute-file-output-file* nil)
(defvar *refute-file-if-exists* nil)

(defun refute-file (filespec
                    &key
                    (format *read-assertion-file-format*)
		    (options *refute-file-options*)
                    (ignore-errors *refute-file-ignore-errors*)
		    (verbose *refute-file-verbose*)
                    (output-file *refute-file-output-file*)
                    (if-exists *refute-file-if-exists*)
                    (package *read-assertion-file-package*)
                    (readtable *readtable*))
  (labels
    ((refute-file0 ()
       (initialize)
       (mapc #'eval options)
       (mapc #'eval (funcall 'read-assertion-file filespec
                             :format format
                             :package package
                             :readtable readtable))
       (or (closure) :done))
     (refute-file1 ()
       (prog2
        (when verbose
          (format t "~&; Begin refute-file ~A " filespec) (print-current-time) (terpri))
        (if ignore-errors
            (mvlet (((:values value condition) (ignore-errors (refute-file0))))
              (or value (princ condition)))
            (refute-file0))
        (when verbose
          (format t "~&; End refute-file ~A "   filespec) (print-current-time) (terpri)))))
    (if output-file
        (with-open-file (stream output-file :direction :output :if-exists if-exists)
          (when stream
            (let ((*standard-output* stream) (*error-output* stream))
              (refute-file1))))
        (refute-file1))))

(defvar *tptp-input-directory*
  #+cmu '(:absolute "home" "stickel" "TPTP" "in")
  #+allegro '(:absolute "home" "pacific1" "stickel" "TPTP" "in"))

(defvar *tptp-output-directory*
  #+cmu '(:absolute "home" "stickel" "TPTP" "snark" "out")
  #+allegro '(:absolute "home" "pacific1" "stickel" "TPTP" "snark" "out"))

(defvar *tptp-problem-name-suffix* "+short+rm_eq_rstfp")

(defun do-tptp-problem (problem &key (format *read-assertion-file-format*) options)
  (let* ((name (string problem)))
    (refute-file (make-pathname
                  :directory *tptp-input-directory*
                  :name (concatenate 'string name *tptp-problem-name-suffix*)
                  :type (if format (string-downcase (symbol-name format)) "kif"))
                 :format format
                 :options options
                 :ignore-errors t
                 :verbose t
                 :output-file (make-pathname
                               :directory *tptp-output-directory*
                               :name name
                               :type "out")
                 :if-exists nil)))

(defun do-tptp-problem1 (problem &key (format *read-assertion-file-format*) options)
  (let* ((name (string problem)))
    (refute-file (concatenate 'string
                              #+cmu "/home/stickel/snark/examples/"
                              #+mcl "Nori:Research:SNARK:examples:"
                              name
                              *tptp-problem-name-suffix*
                              "."
                              (if format (string-downcase (symbol-name format)) "kif"))
                 :format format
                 :options (append '((use-hyperresolution t)
                                    (use-paramodulation t)
                                    (use-factoring :pos)
                                    (use-literal-ordering-with-hyperresolution 'literal-ordering-p)
                                    (use-literal-ordering-with-paramodulation  'literal-ordering-p)
                                    (print-rows-when-given t)
                                    (print-rows-when-derived t))
                                  options))))

(defstruct snark-result
  problem-name
  outcome
  proof-time
  generated-count
  retained-count
  given-count
  proof-length)

(defun print-snark-result (v)
  (cond
   ((eq v :header)
    (format t "~%; Problem            ")
    (format t "    Result")
    (format t "      Time")
    (format t "      Wffs")
    (format t "      Kept")
    (format t "     Given")
    (format t "     Proof"))
   (t
    (let (outcome1 outcome2)
      (ecase (snark-result-outcome v)
        (refutation    (setf outcome1 'p outcome2 1))
        (satisfiable   (setf outcome1 'm outcome2 1))
        (agenda-empty  (setf outcome1 '- outcome2 'noinfer))
        (no-file       (setf outcome1 '- outcome2 'notdone))
        (timeout       (setf outcome1 '- outcome2 'timeout))
        (?             (setf outcome1 '- outcome2 '?)))
      (print-snark-result1
       (snark-result-problem-name v)
       outcome1
       outcome2
       (snark-result-proof-time v)
       (snark-result-generated-count v)
       (snark-result-retained-count v)
       (snark-result-given-count v)
       (snark-result-proof-length v)))))
  v)

(defun print-snark-result1 (problem-name outcome1 outcome2 &optional proof-time
                                         generated-count retained-count given-count
                                         proof-length)
  (format t "~%(~20S" problem-name)
  (format t "~1A" outcome1)
  (format t "~(~9@A~)" outcome2)
  (cond
   ((null proof-time)
    (format t "          "))
   ((> 9.95 proof-time)
    (format t "~10,1F" proof-time))
   (t
    (format t "~10D" (round proof-time))))
  (format t "~:[          ~;~:*~10D~]" generated-count)
  (format t "~:[          ~;~:*~10D~]" retained-count)
  (format t "~:[          ~;~:*~10D~]" given-count)
  (format t "~:[          ~;~:*~10D~]" proof-length)
  (format t ")")
  nil)

(defun summarize-output (&optional (dir *tptp-output-directory*))
  (let ((*print-pretty* nil) (*print-radix* nil) (*print-base* 10.)
        (result nil) result-last)
    (print-snark-result :header)
    (dolist (filename (directory (make-pathname :directory dir :name :wild :type "out")))
      (collect (print-snark-result (summarize-output-file filename)) result))
    (terpri)
    result))

(defun problem-name-from-file-name (filename)
  (let ((s (string (if (pathnamep filename) (pathname-name filename) filename))))
    (intern (subseq s 0 (or (search ".out" s) (length s))))))

(defun summarize-output-file (filename)
  (with-open-file (stream filename :direction :input :if-does-not-exist nil)
    (let ((refutation-p nil)
	  (agenda-empty-p nil)
	  (satisfiable-p nil)
	  (proof-time nil)
	  (generated-count nil)
	  (retained-count nil)
	  (given-count nil)
	  (proof-length nil)
          (time-limit nil)
	  line n1)
      (loop
	(setq line (if stream (read-line stream nil :eof) :eof))
	(when (eq :eof line)
	  (return (make-snark-result
                   :problem-name (problem-name-from-file-name filename)
                   :outcome (cond
                             ((null stream)
                              'no-file)
                             (refutation-p
                              'refutation)
                             (satisfiable-p
                              'satisfiable)
                             (agenda-empty-p
                              'agenda-empty)
                             ((and proof-time time-limit (>= proof-time time-limit))
                              'timeout)
                             (t
                              '?))
                   :proof-time proof-time
                   :generated-count generated-count
                   :retained-count retained-count
                   :given-count given-count
                   :proof-length proof-length)))
	(when (eql 0 (search "(Refutation" line))
          (cond
           (refutation-p
            (warn "File ~A contains more than one refutation." filename))
           (t
            (setq refutation-p t)
            (setq proof-length 0)
            (loop
              (let ((row (read stream)))
                (incf proof-length)
                (when (eq 'false (third row))
                  (return)))))))
        (when (search ";       (RUN-TIME-LIMIT " line)
          (setf time-limit (read-from-string (subseq line 24))))
	(when (search "Propositional abstraction of input is satisfiable." line)
          (setq satisfiable-p t))
        (when (eql 0 (search "; All agendas are empty." line))
          (setq agenda-empty-p t))
	(when (setq n1 (search " Total" line))
          (assert (null proof-time))
          (setq proof-time (read-from-string (subseq line 1)))
          (assert (numberp proof-time)))
	(when (setq n1 (search " formulas have been input or derived (from " line))
          (assert (null generated-count))
          (setq generated-count (read-from-string (remove #\, (subseq line 1))))
          (assert (integerp generated-count))
          (setq given-count (read-from-string (remove #\, (subseq line (+ n1 43)))))
          (assert (integerp given-count)))
        (when (setq n1 (search ") were retained." line))
          (assert (null retained-count))
          (setq retained-count (read-from-string (remove #\, (subseq line 1))))
          (assert (integerp retained-count)))))))

(defun extract-results (problems &optional (filename "nori:research:snark:private:tptp-results.lisp"))
  (prog->
    (mapnconc-file-forms filename ->* form)
    (when (member (first form) problems)
      (list form))))

(defun score-tptp-results (&optional
                           (results-file "nori:research:snark:private:tptp-results.lisp")
                           (problems-file "nori:research:snark:private:tptp-problems.lisp"))
  (score-tptp-results* (read-file results-file) (read-file problems-file)))

(defun score-tptp-results* (results problems)
  (stable-sort (mapcan (lambda (problem)
                         (let ((result (assoc (first problem) results)))
                           (if result
                               (list (score-tptp-result result problem))
                               (list (score-tptp-result (cons (first problem) '(- notdone)) problem)))))
                       problems)
               #'<
               :key #'seventh))

(defun score-tptp-result (result problem)
  (let ((name (first problem)))
    (cl:assert (<= 4 (length problem)))
    (cl:assert (eq name (first result)))
    (let ((status (third problem))
          (rating (fourth problem))
          (fof (find #\+ (symbol-name name))))
      (list (first problem)
            (second problem)
            (third problem)
            (fourth problem)
            (second result)
            (third result)
            (if fof
                (ecase status
                  ((t)
                   (ecase (second result)
                     (- (- (* 9.0 rating) 10.0))
                     (p (+ (* 9.0 rating) 1.0))
                     (m -1000.0)))
                  (s
                   (ecase (second result)
                     (- 0.0)
                     (p -1000.0)
                     (m (+ (* 9.0 rating) 1.0))))
                  ((? o)
                   (ecase (second result)
                     (- 0.0)
                     (p 100.0)
                     (m 100.0))))
                (ecase status
                  (u
                   (ecase (second result)
                     (- (- (* 9.0 rating) 10.0))
                     (p (+ (* 9.0 rating) 1.0))
                     (m -1000.0)))
                  (s
                   (ecase (second result)
                     (- 0.0)
                     (p -1000.0)
                     (m (+ (* 9.0 rating) 1.0))))
                  ((? o)
                   (ecase (second result)
                     (- 0.0)
                     (p 100.0)
                     (m 100.0)))))))))

(defun diff-tptp-results (file1 file2)
  (let ((l1 (read-file file1))
        (l2 (read-file file2)))
    (dolist (x1 l1)
      (let ((x2 (assoc (first x1) l2)))
        (when x2
          (unless (or (and (eq (third x1) (third x2))
                           (member (third x1) '(timeout depth prstack trstack)))
                      (equal (list* (second x1) (third x1) (cddddr x1))
                             (list* (second x2) (third x2) (cddddr x2))))
            (print x1)
            (print x2)
            (terpri)))))))

(defun tptp-fof-problem-name-p (x)
  (ecase (char (symbol-name x) 6)
    (#\+
     t)
    (#\-
     nil)))

(defun summarize-tptp-results (result-file)
  (let ((cnf-proofs 0) (fof-proofs 0)
        (cnf-models 0) (fof-models 0)
        (cnf-noinfer 0) (fof-noinfer 0)
        (cnf-timeout 0) (fof-timeout 0)
        (cnf-aborted 0) (fof-aborted 0)
        (cnf-error 0) (fof-error 0))
    (dolist (x (read-file result-file))
      (cond
       ((eq 'p (second x))
        (if (tptp-fof-problem-name-p (first x)) (incf fof-proofs) (incf cnf-proofs)))
       ((eq 'm (second x))
        (if (tptp-fof-problem-name-p (first x)) (incf fof-models) (incf cnf-models)))
       ((eq 'noinfer (third x))
        (if (tptp-fof-problem-name-p (first x)) (incf fof-noinfer) (incf cnf-noinfer)))
       ((eq 'timeout (third x))
        (if (tptp-fof-problem-name-p (first x)) (incf fof-timeout) (incf cnf-timeout)))
       ((eq 'aborted (third x))
        (if (tptp-fof-problem-name-p (first x)) (incf fof-aborted) (incf cnf-aborted)))
       ((eq 'notdone (third x))
        )
       (t
        (if (tptp-fof-problem-name-p (first x)) (incf fof-error) (incf cnf-error)))))
    (list (list 'proofs (+ cnf-proofs fof-proofs) cnf-proofs fof-proofs)
          (list 'models (+ cnf-models fof-models) cnf-models fof-models)
          (list 'noinfer (+ cnf-noinfer fof-noinfer) cnf-noinfer fof-noinfer)
          (list 'timeout (+ cnf-timeout fof-timeout) cnf-timeout fof-timeout)
          (list 'aborted (+ cnf-aborted fof-aborted) cnf-aborted fof-aborted)
          (list 'error (+ cnf-error fof-error) cnf-error fof-error))))

(defun compare-snark-systems (snark-directory-string1 &optional (snark-directory-string2 "~/snark/"))
  (let ((defs1 (snark-system-defs snark-directory-string1))
	(defs2 (snark-system-defs snark-directory-string2))
	(diff12 nil) diff12-last
	(diff21 nil) diff21-last
	(diff12a nil) diff12a-last
	(diff21a nil) diff21a-last
	(deletions nil) deletions-last
	(changes nil) changes-last
	(additions nil) additions-last)
    (dolist (def defs1)
      (unless (or (member def defs2 :test #'equal)
		  (and (eq 'defvar (first def))
		       (eq 'mes::*%assoc-cache-special-item%* (second def))))
	(collect def diff12)
	(collect (list (first def) (definiendum def)) diff12a)))
    (dolist (def defs2)
      (unless (or (member def defs1 :test #'equal)
		  (and (eq 'defvar (first def))
		       (eq 'mes::*%assoc-cache-special-item%* (second def))))
	(collect def diff21)
	(collect (list (first def) (definiendum def)) diff21a)))
    (dolist (def diff12a)
      (if (member def diff21a :test #'equal)
	  nil
	  (collect def deletions)))
    (dolist (def diff21a)
      (if (member def diff12a :test #'equal)
	  (collect def changes)
	  (collect def additions)))
    (when deletions
      (format t "~%~A deletes definitions in ~A:~{~%  ~A~}~%"
	      snark-directory-string2 snark-directory-string1 deletions))
    (when changes
      (format t "~%~A changes definitions in ~A:~{~%  ~A~}~%"
	      snark-directory-string2 snark-directory-string1 changes))
    (when additions
      (format t "~%~A adds definitions not in ~A:~{~%  ~A~}~%"
	      snark-directory-string2 snark-directory-string1 additions))
    (when diff12
      (format t "~%Definitions in ~A but not ~A:~%"
	      snark-directory-string1 snark-directory-string2)
      (dolist (def diff12)
	(let ((*print-pretty* t))
	  (print def))
	(terpri)))
    (when diff21
      (format t "~%Definitions in ~A but not ~A:~%"
	      snark-directory-string2 snark-directory-string1)
      (dolist (def diff21)
	(let ((*print-pretty* t))
	  (print def))
	(terpri))
      nil)))

(defun snark-system-defs (&optional (snark-directory-string "~/snark/"))
  (let ((filenames nil) (defs nil) defs-last)
    (mapnconc-file-forms
     (lambda (form)
       (cond
        ((and (consp form)
              (eq 'defparameter (first form))
              (eq 'cl-user::*snark-files* (second form)))
         (setq filenames (second (third form)))))
       nil)
     (concatenate 'string snark-directory-string "snark-system.lisp"))
    (dolist (filename filenames)
      (mapnconc-file-forms
       (lambda (form)
         (cond
          ((definitionp form)
           (collect form defs)))
         nil)
       (concatenate 'string snark-directory-string filename ".lisp")
       :if-does-not-exist nil))
    defs))

(defun definitionp (form)
  (and (consp form)
       (symbolp (first form))
       (or (string= "DEF" (subseq (symbol-name (first form)) 0 3))
           (eq 'declare-snark-option (first form))
           (eq 'declare-snark-option2 (first form))
           (eq 'new-option-name (first form))
           (eq 'new-function-name (first form)))))

(defun definiendum (definition)
  (cond
    ((member (first definition) '(defstruct defstructset))
     (if (atom (second definition))
	 (second definition)
	 (first (second definition))))
    (t
     (second definition))))

(defun internal-symbols (package)
  (setq package (find-package package))
  (let ((symbols nil) symbols-last)
    (do-symbols (symbol package)
      (when (and (eq package (symbol-package symbol))
                 (eq :internal (nth-value 1 (intern (symbol-name symbol) package))))
        (collect symbol symbols)))
    symbols))

(defun snark-functions ()
  (let ((package (find-package :snark))
        (option-functions
         (nconc (mapcar (lambda (opt)
                          (intern (concatenate 'string (symbol-name :default-) (symbol-name opt) "?")
                                  :snark))
                        *snark-options*)
                (mapcar (lambda (opt)
                          (intern (concatenate 'string (symbol-name :default-) (symbol-name opt))
                                  :snark))
                        *snark-options*)
                (mapcar (lambda (opt)
                          (intern (concatenate 'string (symbol-name opt) "?") :snark))
                        *snark-options*)
                *snark-options*))
        (functions nil) functions-last)
    (do-symbols (symbol package)
      (when (and (eq package (symbol-package symbol))
                 (fboundp symbol)
                 (or (eq 'assert symbol)
                     (eq :external (nth-value 1 (intern (symbol-name symbol) package))))
                 (not (member symbol option-functions)))
        (collect
          #-mcl symbol
          #+mcl (cons symbol (ccl:arglist symbol t))
          functions)))
    functions))

(defun make-snark-system (&optional compile)
  (cl-user::make-snark-system compile))

;;; utilities.lisp EOF
