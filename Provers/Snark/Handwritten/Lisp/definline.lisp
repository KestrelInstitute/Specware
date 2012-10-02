;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: mes-definline -*-
;;; File: definline.lisp
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

(in-package :mes-definline)

(defmacro definline (name lambda-list &body body)
  #-clisp
  `(progn 
     (defun ,name ,lambda-list ,@body)
     (define-compiler-macro ,name (&rest arg-list)
       (cons '(lambda ,lambda-list ,@body) arg-list)))
  #+clisp
  `(defun ,name ,lambda-list ,@body))

;;; definline.lisp EOF
