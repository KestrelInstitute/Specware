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

(defun make-system (new-directory)
  (let ((old-directory (cur-directory)))
    (change-directory new-directory)
    (unwind-protect (load "system.lisp")
    (change-directory old-directory))))

(make-sw4 "../SW4")

;; Turns off global gc until idle for 10 seconds or 10 x normal amount tenured
(setq *global-gc-behavior* '(10 10.0))

(format t "~2%No don't do that.~2%")
(format t "~2%To test, run (test)~%")
(format t "~%That will run (sw \"/Applications/Specware/Specware4\")~2%")

(defun test ()
  (make-system "Library/Algorithms/Parsing/Chart/Handwritten/Lisp/")
  (make-system "Languages/SpecCalculus/Parser/Handwritten/Lisp/")
  (sw "/Applications/Specware/Specware4")
  )
