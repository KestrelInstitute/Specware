(in-package :cl-user)

(terpri) ; purely cosmetic

;;; ---------------

(defun current-directory ()
  #+allegro(excl::current-directory)
  #+Lispworks(hcl:get-working-directory)  ;(current-pathname)
  )

(defun change-directory (directory)
  ;; (lisp::format t "Changing to: ~A~%" directory)
  #+allegro(excl::chdir directory)
  #+Lispworks (hcl:change-directory directory)
  (setq lisp::*default-pathname-defaults* (current-directory)))

(defun make-sw4 (new-directory)
  (let ((old-directory (current-directory)))
    (change-directory new-directory)
    (unwind-protect (load "load.lisp")
    (change-directory old-directory))))

(defun make-system (new-directory)
  (let ((old-directory (current-directory)))
    (change-directory new-directory)
    (unwind-protect (load "system.lisp")
    (change-directory old-directory))))

(make-sw4 "../SW4")

;; Turns off global gc until idle for 10 seconds or 10 x normal amount tenured
(setq *global-gc-behavior* '(10 10.0))

(format t "~2%No don't do that.~2%")
(format t "~2%To test, run (test)~%")
(format t "~%That will run (sw \"/Applications/Specware/Specware4\")~2%")

;; Want the new parser to be available whether or not we do a bootstrap.
(make-system "Library/Algorithms/Parsing/Chart/Handwritten/Lisp/")
(make-system "Languages/SpecCalculus/Parser/Handwritten/Lisp/")

(defun test ()
  (sw "/Applications/Specware/Specware4")
  )
