;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: snark-user -*-
;;; File: coder.lisp
;;; Copyright (c) 2003 Mark E. Stickel
;;;
;;; Permission is hereby granted, free of charge, to any person obtaining a
;;; copy of this software and associated documentation files (the "Software"),
;;; to deal in the Software without restriction, including without limitation
;;; the rights to use, copy, modify, merge, publish, distribute, sublicense,
;;; and/or sell copies of the Software, and to permit persons to whom the
;;; Software is furnished to do so, subject to the following conditions:
;;;
;;; The above copyright notice and this permission notice shall be included
;;; in all copies or substantial portions of the Software.
;;;
;;; THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
;;; EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
;;; MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
;;; IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
;;; CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
;;; TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
;;; SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

(in-package :snark-user)

;;; coder finds shortest condensed-detachment proofs

(defstruct (proof-line
            (:constructor make-proof-line (just
                                           wff
                                           &optional
                                           (wff-size (snark::size wff))
                                           (wff-vars (snark::variables wff))))
            (:copier nil))
  (just nil :read-only t)
  (wff nil :read-only t)
  (wff-size 0 :read-only t)
  (wff-vars nil :read-only t)
  (target nil)
  (cut nil))

(defvar *coder-start-time*)
(defvar *coder-step-count*)
(defvar *coder-derivation-count*)
(defvar *coder-print-state-interval* 1000000)
(defvar *coder-maximum-term-size-found*)
(defvar *coder-maximum-target-size*)
(defvar *coder-term-size-limit*)
(defvar *coder-term-vars-limit*)
(defvar *coder-ordering* :rpo)

(defvar *test1* nil)
(defvar *test2* nil)
(defvar *test3* t)				;make this the default 2003-08-14

(defun coder (axioms target &rest options
              &key (max 100) (min 1) (max-syms nil) (max-vars nil) (op nil)
              kill all-proofs must-use resume
              (*test1* *test1*) (*test2* *test2*) (*test3* *test3*))
  (declare (ignore kill all-proofs must-use resume))
  (print (cons 'coder
               (mapcar (lambda (x) (if (constantp x) x (list 'quote x)))
                       (list* axioms target options))))
  (initialize)
  (use-term-ordering *coder-ordering*)
  (use-default-ordering 'coder-default-symbol-ordering)
  (test-option19 t)
  (unless op
    (dolist (x axioms)
      (when (and (consp x) (= 3 (length x)))
        (cond
         ((null op)
          (setf op (first x)))
         ((not (eq op (first x)))
          (warn "There is more than one binary relation; using condensed detachment for ~A." op)
          (return))))))
  (prog->
    (identity 0 -> naxioms)
    (reverse (mapcar
              (lambda (x)
                (make-proof-line (incf naxioms) (snark::renumber-new (snark::input-term x))))
              axioms)
             -> axioms)
    (declare-function 'cd 2 :ordering-status :left-to-right -> cd)
    (input-target target -> target target-alist)
    (and (not (contains-test-target? target))
         (reduce #'max target-alist :key (lambda (x) (snark::size (cdr x))))
         -> *coder-maximum-target-size*)
    (identity max-syms -> *coder-term-size-limit*)
    (identity max-vars -> *coder-term-vars-limit*)
    (identity nil -> all-targets-found)
    (setf *coder-step-count* 0)
    (setf *coder-derivation-count* 0)
    (setf *coder-maximum-term-size-found* 0)
    (get-internal-run-time -> *coder-start-time*)
    (loop for nsteps from min to max
          do (let (targets-found)
               (format t "~2%Search for ~D-step proof... " nsteps)
               (force-output)
               (setf targets-found (apply 'coder1 axioms target nsteps cd op options))
               (format t "~%~D steps in ~D seconds"
                       *coder-step-count*
                       (round (- (get-internal-run-time) *coder-start-time*)
                              internal-time-units-per-second))
               (when targets-found
                 (setf target (remove-target target targets-found))
                 (setf all-targets-found (nconc targets-found all-targets-found))
                 (when (null target)
                   (return)))))
    (mapcar (lambda (x) (or (car (rassoc x target-alist)) x)) all-targets-found)))

(defun coder1 (axioms target nsteps cd op
               &key (kill nil) (all-proofs nil) (must-use nil) (resume nil)
               &allow-other-keys)
  (let ((together-target? (together-target? target))
        (targets-found nil))
    (labels
      ((coder2 (lines nsteps unused target* ntargets)
         ;; target* is used to record remaining targets only if target is a together-target
         (cond
          ((eql 0 nsteps)
           (incf *coder-derivation-count*)
           (cond
            (together-target?
             (cl:assert (null target*))		;all targets should have been matched
             (print-proof lines)
             (print-proof-for-otter-verification lines op)
             (force-output)
             (setf targets-found (rest target))
             (unless all-proofs
               (return-from coder1 targets-found)))
            (t
             (let ((found (target? target (proof-line-wff (first lines)))))	;is final wff a target?
               (when found
                 (setf (proof-line-target (first lines)) found)
                 (print-proof lines)
                 (print-proof-for-otter-verification lines op)
                 (force-output)
                 (dolist (v found)
                   (pushnew v targets-found))
                 (unless all-proofs
                   (when (null (setf target (remove-target target found)))
                     (return-from coder1 targets-found))))))))
          (t
           (flet
             ((coder3 (x y xunused? yunused? new-line)
                (let ((found (and together-target? (target? target* (proof-line-wff new-line)))))
                  (cond
                   (found
                    ;;(mes:princf *coder-step-count*)
                    (cl:assert (null (rest found)) ()
                               "More than one together-target simultaneously satisfied.")
                    (when (eql 0 (rem (incf *coder-step-count*) *coder-print-state-interval*))
                      (print-coder-state (cons new-line lines)))
                    (setf (proof-line-target new-line) found)
                    (coder2
                     (cons new-line lines)
                     (1- nsteps)
                     (let ((unused (if xunused? (remove x unused) unused)))
                       (if yunused? (remove y unused) unused))
                     (remove-target target* found)
                     (1- ntargets)))
                   ((not (and together-target? (eql ntargets nsteps)))
                    ;;(mes:princf *coder-step-count*)
                    (when (eql 0 (rem (incf *coder-step-count*) *coder-print-state-interval*))
                      (print-coder-state (cons new-line lines)))
                    (coder2
                     (cons new-line lines)
                     (1- nsteps)
                     (let ((unused (if xunused? (remove x unused) unused)))
                       (cons new-line (if yunused? (remove y unused) unused)))
                     target*
                     ntargets))))))
             (declare (dynamic-extent #'coder3))
             (let ((new-lines nil))
               (let ((nunused (length unused)))
                 (dolist (x (reverse lines))	;use reverse to reorder search 2003-04-17
                   (let ((xunused? (member x unused)))
                     (dolist (y lines)
                       (let ((yunused? (and (not (eq x y)) (member y unused))))
                         (unless (> (if xunused?
                                        (if yunused? (1- nunused) nunused)
                                        (if yunused? nunused (1+ nunused)))
                                    (if (eql 1 ntargets) nsteps (+ nsteps ntargets -1)))
                           (let ((just (make-compound cd (proof-line-just x) (proof-line-just y))))
                             (unless (eq '> (snark::simplification-ordering-compare-terms0
                                             just (proof-line-just (first lines)) nil '>))
                               ;; lines are ordered by >rpo, so if (cd x y) is not >rpo (first lines),
                               ;; then (cd x y') for later y' in lines will not be either, so exit loop
                               (return))
                             (prog->
                               (do-cd (proof-line-wff x) (proof-line-wff y) op (eql ntargets nsteps)
                                      ->* new-wff new-wff-size cut)
                               (if new-wff-size
                                   (make-proof-line just new-wff new-wff-size)
                                   (make-proof-line just new-wff)
                                   -> new-line)
                               (when cut
                                 (setf (proof-line-cut new-line) t))
                               (cond
                                ((and resume
                                      (let ((l1 resume) (l2 (coder-state (cons new-line lines))))
                                        (loop
                                          (cond
                                           ((null l1)
                                            (setf resume nil)
                                            (setf *coder-step-count* -1)
                                            (return nil))
                                           ((null l2)
                                            (return nil))
                                           ((not (equal (pop l1) (pop l2)))
                                            (return t))))))
                                 )
                                ((or *test1* *test2*)
                                 (cond
                                  ((and kill (funcall kill new-line))
                                   )
                                  ((and *test2* (backward-subsumes? new-line lines))
                                   ;; reject all derivations beginning with lines
                                   ;; when new-line is equal to an earlier line
                                   ;; as well as when it strictly subsumes it
                                   ;; as in the case below
                                   (return-from coder2))
                                  ((forward-subsumed? new-line lines)
                                   )
                                  ((and (not *test2*) (backward-subsumes? new-line lines))
                                   ;; don't just block adding new-line to lines but
                                   ;; reject all derivations beginning with lines
                                   (return-from coder2))
                                  (t
                                   (push (list x y xunused? yunused? new-line) new-lines))))
                                (t
                                 (unless (or (and kill (funcall kill new-line))
                                             (forward-subsumed? new-line lines)
                                             (backward-subsumes? new-line lines))
                                   (coder3 x y xunused? yunused? new-line))))
                               (when cut
                                 (return))))))))))
               (when new-lines
                 (dolist (new-line (nreverse new-lines))
                   (apply #'coder3 new-line)))))))))
      (let ((ntargets (if together-target? (length (rest target)) 1)))
        (unless (> ntargets nsteps)
          (coder2 axioms nsteps (selected-lines axioms must-use) target ntargets)))
      targets-found)))

(defun selected-lines (lines nums)
  (cond
   ((null nums)
    nil)
   ((eq t nums)
    (reverse lines))
   (t
    (let ((result nil) (i (length lines)))
        (dolist (line lines result)
          (when (or (eq t nums) (member i nums))
            (push line result))
          (decf i))))))

(defun coder-default-symbol-ordering (x y)
  (if (numberp x)
      (if (and (numberp y) (> x y)) '> '<)
      '>))

(defun forward-subsumed? (new-line lines)
  ;; return true iff new-line is subsumed by an earlier line
  (let ((new-wff (proof-line-wff new-line))
        (new-wff-size (proof-line-wff-size new-line))
        (new-wff-vars (proof-line-wff-vars new-line)))
    (dolist (l lines nil)
      (when (and (>= new-wff-size (proof-line-wff-size l))
                 (snark::subsumed-p1 new-wff (proof-line-wff l) new-wff-vars))
        (return t)))))

(defun backward-subsumes? (new-line lines)
  ;; return true iff new-line subsumes an earlier line that is not used to derive new-line
  (let ((new-wff (proof-line-wff new-line))
        (new-wff-size (proof-line-wff-size new-line)))
    (dolist (l lines nil)
      (let ((j (proof-line-just l)))
        ;; don't backward subsume axioms or ancestors
        (cond
         ((not (compound-p j))	;l and rest of lines are all axioms
          (return nil))
         ((and (<= new-wff-size (proof-line-wff-size l))
               (snark::subsumes-p1 new-wff (proof-line-wff l) (proof-line-wff-vars l))
               (not (snark::occurs-p j (proof-line-just new-line) nil)))
          (return t)))))))

(defun do-cd (function x y op &optional last-line)
  ;; perform condensed detachment operation
  ;; with x as major premise and y as minor premise
  ;; assume x and y are variable disjoint unless (eq x y)
  ;; return result with new variables
  (prog->
    (when (and (compound-p x) (eq op (function-name (head x))))
      (arg1 x -> x1)
      (arg2 x -> x2)
      ;; (cd (i x t) s) always yields t for any s if x does not occur in t
      ;; producing alternative derivations which differ only in which minor premise is used
      (and *test3* (snark::variable-p x1) (not (snark::occurs-p x1 x2)) -> cut)
      (unify x1 (if (eq x y) (snark::renumber-new y) y) ->* subst)
      (snark::size x2 subst -> n)
      ;; don't create big terms that cannot subsume a target for the last line of proof
      (unless (or (and last-line *coder-maximum-target-size* (< *coder-maximum-target-size* n))
                  (and *coder-term-size-limit* (< *coder-term-size-limit* n))
                  (and *coder-term-vars-limit* (< *coder-term-vars-limit* (length (snark::variables
                                                                                   x2 subst)))))
        (when (and (not *coder-term-size-limit*) (< *coder-maximum-term-size-found* n))
          (format t " ~D syms " n)
          (force-output)
          (setf *coder-maximum-term-size-found* n))
        (funcall function (snark::renumber-new x2 subst) n cut)))))

(defun just-list (j lines)
  (if (compound-p j)
      (list (function-name (head j))
            (proof-line-number (arg1 j) lines)
            (proof-line-number (arg2 j) lines))
      j))

(defun print-just (line lines &optional (j (proof-line-just line)))
  (format t "~2D ~A"
          (proof-line-number line lines)
          (if (compound-p j) (just-list j lines) 'ax))
  (when (proof-line-cut line)
    (format t "!")))

(defun proof-line-number (j lines)
  (1+ (position (if (proof-line-p j) (proof-line-just j) j) lines
                :key #'proof-line-just :test 'equal-p)))

(defun print-proof-line (line lines)
  (let ((j (proof-line-just line)))
    (format t "~%") (print-just line lines j) (format t "~13T")
    (print-term (snark::renumber (proof-line-wff line)))
    (cond
     ((compound-p j)
      (format t "~84T;~2D sym~:P, ~D var~:P"
              (snark::size (proof-line-wff line))
              (length (snark::variables (proof-line-wff line)))))
     ((not (member j lines
                   :key #'proof-line-just
                   :test (lambda (x y) (and (not (snark::equal-p x y)) (snark::occurs-p x y nil)))))
      (format t "~84T;unused")))))

(defun print-proof-lines (lines)
  (mapc (lambda (line) (print-proof-line line lines)) lines))

(defun print-proof (lines)
  (format t "~2%Proof:")
  (print-proof-lines (reverse lines))
  (terpri))

(defun coder-state (lines)
  (let ((lines (reverse lines)))
    (mapcan (lambda (line)
              (let ((j (proof-line-just line)))
                (if (compound-p j)
                    (list (list (function-name (head j))
                                (proof-line-number (arg1 j) lines)
                                (proof-line-number (arg2 j) lines)))
                    nil)))
            lines)))

(defun print-coder-state (lines)
  (format t "~%  ~A ~5Dm "
          (subseq (mes:print-current-time nil t) 4 13)
          (round (- (get-internal-run-time) *coder-start-time*)
                 (* 60 internal-time-units-per-second)))
  (mapc (lambda (x) (princ x) (princ " ")) (coder-state lines))
  (force-output))

;;; coder's target argument is either a normal-target or a together-target
;;;
;;; a single-target is one of
;;;   a term - find generalization (or variant) of this term
;;;   (TEST predicate)
;;;
;;; a normal-target is one of
;;;   a single-target
;;;   (OR normal-target1 ... normal-targetn)  - search until one target is found
;;;   (AND normal-target1 ... normal-targetn) - search until all targets are found
;;;
;;; a together-target is
;;;   (TOGETHER single-target1 ... single-targetn) - search until all targets are found in a single derivation
;;;   it is assumed that no single formula will satisfy more than one of these targets

(defvar *input-target-alist*)

(defun input-target (target)
  (let ((*input-target-alist* nil))
    (values (cond
             ((together-target? target)
              (input-together-target target))
             (t
              (input-normal-target target)))
            *input-target-alist*)))

(defun together-target? (target)
  (and (consp target) (eq 'together (first target))))

(defun contains-test-target? (target)
  (case (and (consp target) (first target))
    (test
     t)
    ((and or together)
     (some #'contains-test-target? (rest target)))))

(defun wrap2 (f l)
  (cl:assert (consp l))
  (if (null (rest l)) (first l) (cons f l)))

(defun input-together-target (target)
  (wrap2 (first target) (mapcar #'input-single-target (rest target))))

(defun input-normal-target (target)
  (cond
   ((and (consp target) (member (first target) '(or and)))
    (wrap2 (first target) (mapcar #'input-normal-target (rest target))))
   (t
    (input-single-target target))))

(defun input-single-target (target)
  (cl:assert (not (and (consp target) (member (first target) '(or and together)))))
  (cond
   ((and (consp target) (eq 'test (first target)))
    target)
   (t
    (let ((target* (snark::renumber-new (snark::input-term target))))
      (push (cons target target*) *input-target-alist*)
      target*))))

(defun target? (target x &optional l)
  ;; does x generalize a term in target?
  (cond
   ((and (consp target) (member (first target) '(or and together)))
    (dolist (y (rest target) l)
      (setf l (target? y x l))))
   ((and (consp target) (eq 'test (first target)))
    (if (funcall (second target) x) (adjoin target l) l))
   (t
    (if (snark::subsumes-p x target) (adjoin target l) l))))

(defun remove-target (target l)
  (cond
   ((and (consp target) (eq 'or (first target)))
    (let ((v (mapcar (lambda (y)
                        (let ((y* (remove-target y l)))
                          (or y* (return-from remove-target nil))))
                      (rest target))))
      (wrap2 'or v)))
   ((and (consp target) (member (first target) '(and together)))
    (let ((v (mapcan (lambda (y)
                       (let ((y* (remove-target y l)))
                         (and y* (list y*))))
                     (rest target))))
      (and v (wrap2 (first target) v))))
   (t
    (if (member target l) nil target))))

(defun print-proof-for-otter-verification (lines op)
  ;; Bob Veroff provided the template for this script
  (let ((lines (reverse lines)))
    (format t "~%% OTTER SCRIPT TO TRY TO FIND SAME PROOF")
    (format t "~%  set(hyper_res). clear(print_kept). clear(print_back_sub). assign(stats_level,0).")
    (format t "~%  assign(bsub_hint_add_wt,-1000000). set(keep_hint_subsumers). assign(max_weight,1).")
    (format t "~%  list(sos).                    % AXIOMS:")
    (dolist (l lines)
      (unless (compound-p (proof-line-just l))
        (format t "~%    ") (print-term-for-otter2 (proof-line-wff l)) (format t ".")))
    (format t " end_of_list.")
    (format t "~%  list(usable).                 % CONDENSED DETACHMENT RULE:")
    (format t "~%    -P(~A(x,y)) | -P(x) | P(y)." (string-downcase (string op)))
    (format t " end_of_list.")
    (let ((first t))
      (dolist (l lines)
        (when (proof-line-target l)
          (cond
           (first
            (setf first nil)
            (format t "~%  list(usable).                 % TARGET:"))
           (t
            (format t " |")))
          (format t "~%    -") (print-term-for-otter2 (proof-line-wff l) t)))
      (unless first
        (format t ". end_of_list.")))
    (format t "~%  list(hints).                  % PROOF LINES:")
    (dolist (l lines)
      (format t "~%    ") (print-term-for-otter2 (proof-line-wff l)) (format t ".")
      (format t "~72T%") (print-just l lines))
    (format t "~%    end_of_list.")
    (format t "~%% OTTER SCRIPT END~%")
    ))

(defun print-term-for-otter2 (term &optional ground)
  (princ "P(")
  (print-term-for-otter (snark::renumber term) ground)
  (princ ")")
  term)

(defun print-term-for-otter (term &optional ground)
  (dereference
   term nil
   :if-variable (cond
                 (ground
                  (princ #\c)
                  (princ (snark::variable-number term)))
                 (t
                  (prog->
                    (floor (snark::variable-number term) 6 -> i j)
                    (princ (case j (0 #\x) (1 #\y) (2 #\z) (3 #\u) (4 #\v) (5 #\w)))
                    (unless (eql 0 i)
                      (princ i)))))
   :if-constant (cond
                 ((numberp term)
                  (princ term))
                 (t
                  (princ #\c)
                  (princ (string-downcase (string term)))))
   :if-compound (progn 
                  (princ (string-downcase (string (function-name (head term)))))
                  (princ "(")
                  (let ((first t))
                    (dolist (arg (args term))
                      (if first (setf first nil) (princ ","))
                      (print-term-for-otter arg ground)))
                  (princ ")")))
  term)

;;; coder.lisp EOF
