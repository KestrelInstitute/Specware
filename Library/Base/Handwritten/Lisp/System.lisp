(defpackage "SYSTEM-SPEC")
(in-package "SYSTEM-SPEC")

(defvar System-spec::specwareDebug? nil)

 ;;; op fail     : fa(a) String -> a
(defun fail (s) (error "~a" s))

;;; op debug     : fa(a) String -> a
(defun |!debug| (s) (when specwareDebug? (break "~a" s)))

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
  (let ((val (specware::getenv name)))
    (if (or (eq val nil) (equal val ""))    ; I think it returns "" if not set
	(cons :|None| nil)
      (cons :|Some| val))))

(defvar msWindowsSystem? #+mswindows t #-mswindows nil)

;;;  op temporaryDirectory : String
(defparameter temporaryDirectory (namestring #+allegro   (SYSTEM:temporary-directory)
                                             #+Lispworks SYSTEM::*TEMP-DIRECTORY*
					     #+(or mcl cmu) "/tmp/"
					     ))


;;; op withRestartHandler : fa (a) String * (() -> ()) * (() -> a) -> a
(defun withRestartHandler-3 (restart-msg restart-action body-action)
  (loop
    (let ((results (multiple-value-list 
		    (with-simple-restart (abort restart-msg) 
		      (funcall body-action (vector))))))
      (if (equal results '(nil t))
	  (funcall restart-action (vector))
	(return (values-list results))))))

;;; op garbageCollect : Boolean -> ()
(defun garbageCollect (full?)
  #+allegro (sys::gc full?)
  #+cmu (ext:gc :full full?))

;; hackMemory essentially calls (room nil) in an attempt to appease 
;; Allegro CL into not causing mysterious storage conditions during 
;; the bootstrap. (sigh)  
;; Calling (gc nil) and (gc t) both failed to have the desired effect.

;;; op hackMemory     : ()      -> ()
(defun hackMemory-0 ()
  ;; (sys::room nil)
  )

;;; op trueFilename : String -> String 
(defun trueFilename (filename)
  (let* ((given-pathname (pathname filename))
	 (resolved-pathname
	  #+Allegro
	  (excl::pathname-resolve-symbolic-links given-pathname)
	  #-Allegro
	  (truename given-pathname)
	  ))
    (namestring resolved-pathname)))

;;; op trueFilePath : List String * Boolean -> List String
(defun trueFilePath-2 (path relative?)
  (let* ((rpath (reverse path))
	 (name (first rpath))
	 (dir  (cons (if relative? :relative :absolute)
		     (reverse (rest rpath))))
	 (given-pathname (make-pathname :directory dir :name name))
	 (resolved-pathname
	  #+Allegro
	  (excl::pathname-resolve-symbolic-links given-pathname)
	  #-Allegro
	  (truename given-pathname)
	  ))
    (append (rest (pathname-directory resolved-pathname))
	    (list (pathname-name resolved-pathname)))))
