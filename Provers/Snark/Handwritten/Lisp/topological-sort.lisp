;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: mes -*-
;;; File: topological-sort.lisp
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
;;; Portions created by the Initial Developer are Copyright (C) 1981-2002.
;;; All Rights Reserved.
;;;
;;; Contributor(s): Mark E. Stickel <stickel@ai.sri.com>.

(in-package :mes)

(defun topological-sort* (items adj)
  ;; see Cormen, Leiserson, Rivest text
  ;; (funcall adj cc u items) iterates over v in items
  ;; that must occur after u and executes (funcall cc v)
  ;; note: also eliminates EQL duplicates
  (let ((color (make-hash-table))
	(result nil))
    (labels
      ((dfs-visit (u)
         (when (eq :white (gethash u color :white))
           (setf (gethash u color) :gray)
           (funcall adj #'dfs-visit u items)
           (push u result))))
      (mapc #'dfs-visit items)
      result)))

(defun topological-sort (items must-precede-predicate)
  (topological-sort*
   items
   (lambda (cc u items)
     (mapc (lambda (v)
             (when (and (neql u v) (funcall must-precede-predicate u v))
               (funcall cc v)))
           items))))

#+ignore
(defun test-topological-sort* ()
  (topological-sort*
   '(undershorts pants belt shirt tie jacket socks shoes watch)
   (lambda (cc u items)
     (declare (ignore items))
     (dolist (x '((undershorts . pants)
                  (undershorts . shoes)
                  (pants . belt)
                  (pants . shoes)
                  (belt . jacket)
                  (shirt . belt)
                  (shirt . tie)
                  (tie . jacket)
                  (socks . shoes)))
       (when (eql u (car x))
         (funcall cc (cdr x)))))))

#+ignore
(defun test-topological-sort ()
  (topological-sort
   '(undershorts pants belt shirt tie jacket socks shoes watch)
   (lambda (u v)
     (member v
             (cdr (assoc u
                         '((undershorts pants shoes)
                           (pants belt shoes)
                           (belt jacket)
                           (shirt belt tie)
                           (tie jacket)
                           (socks shoes))))))))

;;; topological-sort.lisp EOF
