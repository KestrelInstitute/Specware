(in-package :user)

(terpri) ; purely cosmetic

;;; ---------------

(defun cur-directory ()
  (excl::current-directory))

(defun change-directory (directory)
  ;; (lisp::format t "Changing to: ~A~%" directory)
  (excl::chdir directory)
  (setq lisp::*default-pathname-defaults* (excl::current-directory)))

(defun make-sw4 (new-directory)
  (let ((old-directory (cur-directory)))
    (change-directory new-directory)
    (unwind-protect (load "load.lisp")
    (change-directory old-directory))))

(make-sw4 "../SW4")

(format t "~2%To test, run (test)~2%")

(defun test ()
  (sw "/Library/Structures/Data/Categories/Sketches/Monomorphic")
)
