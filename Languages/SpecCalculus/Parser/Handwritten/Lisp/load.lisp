(in-package :cl-user)

(Specware::make-system ".")

(defun foo () (parser4::parseSpecwareFile "Test.spec"))
