(in-package "USER")

(specware::make-system ".")

(defun foo () (parser4::parseFile "Test.spec"))
