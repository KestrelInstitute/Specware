;;; -*- Mode: LISP; Syntax: Common-Lisp; Package: mes -*-
;;; File: map-file.lisp
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

(defun mapnconc-file-forms (function filespec &key (if-does-not-exist :error) (package *package*))
  ;; apply function to each form in file specified by filespec
  ;; and return the result of nconc'ing the values
  (mapnconc-file0
   (lambda (form)
     (cond
      ((and (consp form) (eq 'in-package (first form)))
       (eval form)
       nil)
      (t
       (funcall function form))))
   filespec
   if-does-not-exist
   package
   #'read))

(defun mapnconc-file-lines (function filespec &key (if-does-not-exist :error) (package *package*))
  ;; apply function to each line in file specified by filespec
  ;; and return the result of nconc'ing the values
  (mapnconc-file0
   function
   filespec
   if-does-not-exist
   package
   #'read-line))

(defun mapnconc-file0 (function filespec if-does-not-exist package read-function)
  (with-open-file (stream filespec
			  :direction :input
			  :if-does-not-exist if-does-not-exist)
    (when stream
      (let ((eof (cons nil nil))
            (result nil) result-last
            (*package* (if (packagep package) package (find-package package))))
        (loop
	  (let ((x (funcall read-function stream nil eof)))
            (if (eq eof x)
                (return result)
                (ncollect (funcall function x) result))))))))

(defun read-file (filespec &rest mapnconc-file-forms-options)
  (declare (dynamic-extent mapnconc-file-forms-options))
  (apply #'mapnconc-file-forms #'list filespec mapnconc-file-forms-options))

;;; map-file.lisp EOF
