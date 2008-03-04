(in-package :cl-user)

(specware::make-system ".")

(defun foo () (parser4::parseSpecwareFile "Test.spec"))
