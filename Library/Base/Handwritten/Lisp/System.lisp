(defpackage "SYSTEM-SPEC")
(in-package "SYSTEM-SPEC")

;;; op fail     : fa(a) String -> a
(defun fail (s) (error "~a" s))

;;; op toString : fa(a) a -> String
(defun toString (s) (let ((*print-pretty* nil)) (format nil "~S" s)))

;;; op print    : fa(a) a -> a
(defun |!print| (x) (print x))

;;; op warn     : fa(a) String -> a
(defun |!warn| (s) (warn "~a" s))

;;; op time     : fa(a) a -> a
(defmacro |!time| (x) (time x))

;;; #-Lispworks
;;; (defun getenv (x) (specware::getenv x))

;; The Lisp getenv returns nil if the name is not in the environment. 
;; Otherwise it returns a string. We want to be able to distinguish
;; the outcomes in MetaSlang

;;; op getEnv : String -> Option String
(defun getEnv (name)
  (let ((val (system:getenv name)))
    (if (or (eq val nil) (equal val ""))    ; I think it returns "" if not set
	(cons :|None| nil)
      (cons :|Some| val))))

;;;  op temporaryDirectory : String
(defparameter temporaryDirectory (namestring #+allegro   (SYSTEM:temporary-directory)
                                             #+Lispworks SYSTEM::*TEMP-DIRECTORY*))


;;; op withRestartHandler : fa (a) String * (() -> ()) * (() -> a) -> a
(defun withRestartHandler (restart-msg restart-action body-action)
  (loop
    (let ((results (multiple-value-list 
		    (with-simple-restart (abort restart-msg) 
		      (funcall body-action (vector))))))
      (if (equal results '(nil t))
	  (funcall restart-action (vector))
	(return (values-list results))))))

;;; op garbageCollect : Boolean -> ()
(defun garbageCollect (full?)
  (sys::gc full?))

;; hackMemory essentially calls (room nil) in an attempt to appease 
;; Allegro CL into not causing mysterious storage conditions during 
;; the bootstrap. (sigh)  
;; Calling (gc nil) and (gc t) both failed to have the desired effect.

;;; op hackMemory     : ()      -> ()
(defun hackMemory ()
  ;; (sys::room nil)
  )

;;; op trueFilename : (List String * String * String) -> (List String * String * String)
(defun trueFilename (directory name type)
  (let* ((given-pathname (make-pathname :directory (cons :absolute directory)
					:name      name
					:type      type))
	 (resolved-pathname
	  #+Allegro
	  (excl::pathname-resolve-symbolic-links given-pathname)
	  #-Allegro
	  (truename given-pathname)
	  )
	 (resolved-directory
	  (rest				; trim off leading :ABSOLUTE
	   (pathname-directory resolved-pathname))))
    (list
     resolved-directory
     (pathname-name resolved-pathname)
     (pathname-type resolved-pathname))))
     