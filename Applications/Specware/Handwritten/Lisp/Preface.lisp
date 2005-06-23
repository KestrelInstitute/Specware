(in-package :cl-user)

;; The following is in ./Languages/SpecCalculus/Semantics/Evaluate/Make.sw:
;;
;;  op Specware.run_cmd : String * List String -> () % defined in toplevel.lisp file for each application [perhaps just Prism]
;;
;; Make.sw is only used by Prism for now, so this is pre-emptive, in case Specware itself begins to use it:

;; To avoid compiler warnings about run_cmd being undefined, Specware::run_cmd is 
;; defined here in Preface.lisp, which is loaded before Specware4.lisp is compiled and loaded, 

(defun Specware::run_cmd (fn)
  (run-cmd fn ()))

(defun Specware::run_cmd-2 (fn args)
  (run-cmd fn args))

#-(or allegro cmu mcl sbcl gcl) 
(defun run-cmd (cmd &rest args)
  (warn "ignoring non-[ALLEGRO/CMU/MCL/SBCL] RUN-CMD : ~A~{ ~A~}" cmd args))


#+(or cmu mcl sbcl gcl) 
(defun run-cmd (cmd args)
  (let ((process
	 ;; cmu defaults for keywords args to run-program:
	 ;;   (env *environment-list*)
	 ;;   (wait t) 
	 ;;   pty 
	 ;;   input            if-input-does-not-exist 
	 ;;   output           (if-output-exists :error) 
	 ;;   (error :output)  (if-error-exists :error) 
	 ;;   status-hook
	 #+cmu  (ext:run-program    cmd args :output *standard-output* :error :output :wait t)
	 #+mcl  (ccl:run-program    cmd args :output *standard-output* :error :output :wait t)
	 #+sbcl (sb-ext:run-program cmd args :output *standard-output* :error :output :wait t)
	 #+gcl  (lisp:system (format nil "~a ~a" cmd args))))
    (let ((rc (process-exit-code process)))
      (unless (equal rc 0)
	(warn "Return code from run-shell-command was non-zero: ~S" rc))))
  (values))

(defparameter *known-programs* '())

#+allegro
(defun run-cmd (fn args)
  ;; first try to verify that fn actually exists
  ;; There is no simple way to get "which" to avoid printing to the terminal,
  ;; so cache the result to avoid needless verbiage.
  (let ((pair (or (assoc fn *known-programs* :test 'equalp)
		  (let ((cmd (format nil "which ~A" fn)))
		    (format t "~&;;; Looking for ")
		    (let ((rc
			   #+UNIX      (run-shell-command cmd 
							  :output       *standard-output* 
							  :error-output :output 
							  :wait t) 
			   #+MSWINDOWS (run-shell-command cmd 
							  ;; :output       *standard-output* ; mysterious problems under windows
							  ;; :error-output :output           ; mysterious problems under windows
							  :wait t)
			   #-(OR UNIX MSWINDOWS) (progn (warn "ignoring non-[UNIX/MSWINDOWS] ALLEGRO RUN-CMD : ~A" cmd) 1)))
		      (let ((pair (cons fn (equal rc 0))))
			(push pair *known-programs*)
			pair))))))
    (if (null (cdr pair))
	(warn "Function given to run-cmd could not be found: ~A ~{~A ~}" fn args)
      (let ((cmd (format nil "~A~{ ~A~}" fn args)))
	(let ((rc
	       #+UNIX      (run-shell-command cmd 
					      :output       *standard-output* 
					      :error-output :output 
					      :wait t) 
	       #+MSWINDOWS (run-shell-command cmd 
					      ;; :output       *standard-output* ; mysterious problems under windows
					      ;; :error-output :output           ; mysterious problems under windows
					      :wait t)
	       #-(OR UNIX MSWINDOWS) (progn (warn "ignoring non-[UNIX/MSWINDOWS] ALLEGRO RUN-CMD : ~A" cmd) 1)))
	  (unless (equal rc 0)
	    (warn "Return code from ~S was non-zero: ~S" cmd rc)))))
    (values)))
  
;; Specware::initializeInterpreterBaseAux is funcalled from 
;; Specware::initializeInterpreterBase-0 in Preface.lisp, which in turn is called from
;; intializeSpecware in Specware.sw
;; This indirection avoids compiler warnings about Specware::initializeInterpreterBase-0
;; being undefined when Specware4.lisp is compiled.
(defun Specware::initializeInterpreterBase-0 () 
  (funcall 'Specware::initializeInterpreterBaseAux))