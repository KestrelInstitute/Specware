(defpackage "SPECWARE")
(in-package "SPECWARE")

;;; This file is loaded before Specware4.lisp when generating
;;; a Specware distribution

;; Used in printing out the license
(defvar user::Specware-version "4.0")
(defvar user::Specware-version-name "Specware-4-0")

;;; Normally autoloaded, but we want to preload them for a stand-alone world
(require "eli")
(require "sock")

;; Override normal definition because of an apparent Allegro bug in
;; generate-application where excl::compile-file-if-needed compiles
;; even if not needed
(defun compile-file-if-needed (file) file)