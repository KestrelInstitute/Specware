(in-package "USER")

(defun cur-directory ()
  (excl::current-directory))

(defun change-directory (directory)
  ;; (lisp::format t "Changing to: ~A~%" directory)
  (excl::chdir directory)
  (setq lisp::*default-pathname-defaults* (excl::current-directory)))

(defun make-system (new-directory)
  (let ((old-directory (cur-directory)))
    (change-directory new-directory)
    (unwind-protect (load "system.lisp")
      (change-directory old-directory))))

(make-system ".")

(defun foo () (parser4::parseFile "Test.spec"))
