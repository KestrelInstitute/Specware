(defpackage "SYSTEM-SPEC")
(in-package "SYSTEM-SPEC")

(defun toString (s) (let ((*print-pretty* nil)) (format nil "~S" s)))
(defun |!print| (x) (print x))
(defun fail (s) (error "~a" s))
(defun |!warn| (s) (warn "~a" s))
(defmacro |!time| (x) (time x))

;;; #-Lispworks
;;; (defun getenv (x) (specware::getenv x))

;; The Lisp getenv returns nil if the name is not in the environment. 
;; Otherwise it returns a string. We want to be able to distinguish
;; the outcomes in MetaSlang
(defun getEnv (name)
  (let ((val (system:getenv name)))
    (if (or (eq val nil) (equal val ""))    ; I think it returns "" if not set
	(cons :|None| nil)
      (cons :|Some| val))))

(defparameter temporaryDirectory (namestring #+allegro   (SYSTEM:temporary-directory)
                                             #+Lispworks SYSTEM::*TEMP-DIRECTORY*))


(defun withRestartHandler (restart-msg restart-action body-action)
  (loop
    (let ((results (multiple-value-list 
		    (with-simple-restart (abort restart-msg) 
		      (funcall body-action (vector))))))
      (if (equal results '(nil t))
	  (funcall restart-action (vector))
	(return (values-list results))))))

(defun garbageCollect (full?)
  (sys::gc full?))

;; hackMemory essentially calls (room nil) in an attempt to appease 
;; Allegro CL into not causing mysterious storage conditions during 
;; the bootstrap. (sigh)  
;; Calling (gc nil) and (gc t) both failed to have the desired effect.
(defun hackMemory ()
  ;; (sys::room nil)
  )
