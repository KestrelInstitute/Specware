(in-package "CL-USER")

(specware::make-system ".")

(defun foo () (parser4::parseFile "Test.spec"))
