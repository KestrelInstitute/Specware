;;; -*- Mode: LISP; Package: Specware; Base: 10; Syntax: Common-Lisp -*-

(in-package "PARSER4")

(load "../../../../SpecCalculus/Parser/Handwritten/Lisp/parser-interface")

(defun parsePSLFile   (file) (parseSpecwareFile   file))
(defun parsePSLString (s)    (parseSpecwareString s))
