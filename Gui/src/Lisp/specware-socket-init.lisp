;;;-*- Mode: fi:common-lisp ; Package: USER ; Base: 10; Syntax: common-lisp  -*-
;;;-------------------------------------------------------------------------
;;;               Copyright (C) 2002 by Kestrel Technology
;;;                          All Rights Reserved
;;;-------------------------------------------------------------------------
;;;
;;;
;;;  $Id$
;;;
;;;
;;;
;;;
;;; $Log$
;;; Revision 1.1  2003/06/17 22:27:18  westfold
;;; New socket interface to java
;;;
;;; Revision 1.2  2003/03/04 07:08:56  westfold
;;; Changes for openmcl compatibility
;;;
;;; Revision 1.1  2003/02/14 21:28:40  weilyn
;;; Initial version
;;;
;;; Revision 1.2  2003/02/06 18:04:48  becker
;;; Added actions to start lisp process explicitly from the user interface.
;;; Modified code generation and schedule execution actions.
;;;
;;; Revision 1.1  2003/02/05 05:32:18  becker
;;; Fixed the code generation and code execution
;;;
;;; Revision 1.2  2003/01/25 00:21:48  becker
;;; Small changes
;;;
;;; Revision 1.1  2002/10/04 00:41:33  becker
;;; Added code for initializing lisp process from JAVA.
;;;
;;;
;;;
;;;
;;;
;;;

(in-package :cl-user)

(setq *specware-home* (or (specware::getenv "SPECWARE4") "~/Specware4"))
(specware::setenv "SWPATH" (format nil "~A/" (specware::getenv "SPECWARE4")))

(defun concat-specware (path)
  (concatenate 'string  *specware-home* path))


(setf (logical-pathname-translations "specware")
  `(("interface;**;*.*"  ,(concat-specware "/Gui/**/*.*"))
    ("lisp-ui;*.*"  ,(concat-specware "/Gui/src/Lisp/*.*"))
    ("java-ui;*.*"  ,(concat-specware "/Gui/src/*.*"))
    ))


(load (compile-file "specware:lisp-ui;init-java-socket-connection"))
;?(specware::change-directory "specware:java-ui;")
(cl-user::init-java-listener)
