(defpackage "SYSTEM-SPEC")
(in-package "SYSTEM-SPEC")

(defun toString (s) (let ((*print-pretty* nil)) (format nil "~S" s)))
(defun |!print| (x) (print x))
(defun fail (s) (error "~a" s))
(defun |!warn| (s) (warn "~a" s))
(defmacro |!time| (x) (time x))
#-Lispworks
(defun getenv (x) (re::getenv x))
(defparameter temporaryDirectory (namestring #+allegro(SYSTEM:temporary-directory)
                                             #+Lispworks SYSTEM::*TEMP-DIRECTORY*))


(defun withRestartHandler (restart-msg restart-action body-action)
  (loop
    (let ((results (multiple-value-list 
		    (with-simple-restart (abort restart-msg) 
		      (funcall body-action (vector))))))
      (if (equal results '(nil t))
	  (funcall restart-action (vector))
	(return (values-list results))))))
