(in-package "CL-USER")

(specware::make-system ".")

(defun foo () (parser4::parseSpecwareFile "Test.spec"))
