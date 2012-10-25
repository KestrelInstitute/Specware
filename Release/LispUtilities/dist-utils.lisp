(in-package :common-lisp-user)

;; for simplicity, use the same package that GatherComponents.lisp uses
(defpackage :Distribution)

(defvar Distribution::*verbose* t)

#+Allegro (provide "dist-utils")

