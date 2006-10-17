(in-package :cl-user)
(defpackage :Specware)
(defpackage :Emacs)

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


#+mcl
(defun process-exit-code (process)
  (ccl::external-process-%exit-code process))

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
	 #+cmu  (ext:run-program    cmd args :input t :output *standard-output* :error :output :wait t )
	 #+mcl  (ccl:run-program    cmd args :output *standard-output* :error :output :wait t) ; TODO: add :input t ??
	 #+sbcl (sb-ext:run-program cmd args :output *standard-output* :error :output :wait t
				    :search t) ; TODO: add :input t ??
	 #+gcl  (lisp:system (format nil "~a ~a" cmd args))              
	 ))
    (let ((rc (process-exit-code process)))
      (unless (equal rc 0)
	;; (warn "Return code from run-shell-command was non-zero: ~S" rc)
	nil)))
  (values))

(defparameter *known-programs* '())

#+allegro
(defun run-cmd (fn args)
  (aux-run-cmd (format nil "~A~{ ~A~}" fn args))
  (finish-output *standard-output*)
  (values))
  
#+allegro
(defun aux-run-cmd (cmd)
  ;; :input and :output args to run-shell-command must refer to file streams, 
  ;; not *terminal-io*, string strings, etc.
  ;; There doesn't seem to be a concept of :error-output on windows
  (let ((rc 
	 (cond ((eq (type-of *standard-output*) 'excl::FILE-SIMPLE-STREAM)
		#+UNIX      (run-shell-command cmd :wait t :output *standard-output* :error-output :output) 
		#+MSWINDOWS (run-shell-command cmd :wait t :output *standard-output*) 
		#-(OR UNIX MSWINDOWS) (progn (warn "ignoring non-[UNIX/MSWINDOWS] ALLEGRO RUN-CMD : ~A" cmd) 1))
	       (t
		#+UNIX      (run-shell-command cmd :wait t :error-output :output) 
		#+MSWINDOWS (run-shell-command cmd :wait t)
		#-(OR UNIX MSWINDOWS) (progn (warn "ignoring non-[UNIX/MSWINDOWS] ALLEGRO RUN-CMD : ~A" cmd) 1)))))
    (cond ((equal rc 0)
	   t)
	  ;; #+MSWINDOWS (equal rc 2) ;; unclear if this can happen under "ok" conditions
	  (t
	   ;; (warn "Return code from ~S was non-zero: ~S" cmd rc)
	   nil))))

;;; --------
;; The following is in ./Languages/SpecCalculus/Semantics/Evaluate/Make.sw:
;;;
;;;  op Specware.cd                    : String -> () % defined in Preface.lisp -- side effect: prints arg to screen

(defun specware::cd (&optional (dir ""))
  (if (equal dir "")
      (setq dir (home-dir))
    (setq dir (subst-home dir)))
  (let ((new-dir (specware::current-directory))
	(error? nil))
    (loop while (and (not error?) (> (length dir) 1) (equal (subseq dir 0 2) ".."))
      do (setq dir (subseq dir (if (and (> (length dir) 2) (eq (elt dir 2) #\/))
				   3 2)))
         (let* ((olddirpath (pathname-directory new-dir))
		(pathlen (length olddirpath)))
	   (if (< pathlen 2)
	       (progn (warn "At top of directory tree")
		      (setq error? t))
	       (setq new-dir (make-pathname :directory (subseq olddirpath 0 (- pathlen 1))
					    :defaults new-dir)))))
    (unless error?
      (setq new-dir (specware::dir-to-path dir new-dir))
      (when (specware::change-directory new-dir)
	(let* ((dirpath new-dir)
	       (newdir (namestring dirpath)))
	  (emacs::eval-in-emacs (format nil "(set-default-directory ~s)"
					(specware::ensure-final-slash newdir)))
	  (when (under-ilisp?)
	    (emacs::eval-in-emacs (format nil "(setq lisp-prev-l/c-dir/file
                                               (cons default-directory nil))"
					  (specware::ensure-final-slash newdir)))))))
    (princ (namestring (specware::current-directory)))
    (values)))

(defun under-ilisp? ()
  (and (find-package "ILISP")
       (find-symbol "ILISP-COMPILE" "ILISP")))

(defun home-dir ()
  (specware::getenv #+mswindows "HOMEPATH" #-mswindows "HOME"))
    
;;; Normalization utilities

(defun subst-home (path)
  (when (stringp path)
    (setq path (substitute #\/ #\\ path))
    (when (and (>= (length path) 2) (equal (subseq path 0 2) "~/"))
      (setq path (concatenate 'string (home-dir) (subseq path 1))))
    (setq path (string-subst path " ~/" (concatenate 'string " " (home-dir) "/")))
    (when #+mswindows t #-mswindows nil
	  (setq path (string-subst path "/Program Files/" "/Progra~1/"))))
  path)

(defun string-subst (str source target)
  (let (pos)
    (loop while (setq pos (search source str :test #+mswindows #'string-equal
				                   #-mswindows #'string=))
	  do (setq str (concatenate 'string
			 (subseq str 0 pos)
			 target
			 (subseq str (+ pos (length source))))))
    str))


(unless (fboundp 'cd)
  (defun cd (&optional (dir "")) (specware::cd dir)))

;;; --------------------------------------------------------------------------------
;;  The following is in ./Languages/SpecCalculus/Semantics/Evaluate/Make.sw:
;;;   op Specware.pwdAsString           : () -> String % defined in Preface.lisp

(defun specware::pwdAsString-0 () ; used by make
  (namestring (specware::current-directory)))

(defun specware::currentDeviceAsString-0 () ; used by make and CPrint
  (let ((x (pathname-device (specware::current-directory))))
    (if (stringp x) (concatenate 'string x ":") ""))) 

;;; --------------------------------------------------------------------------------

;; Specware::initializeInterpreterBaseAux is funcalled from 
;;  Specware::initializeInterpreterBase-0 in Preface.lisp, which in turn is called from
;;  intializeSpecware in Specware.sw
;;  This indirection avoids compiler warnings about Specware::initializeInterpreterBase-0
;;  being undefined when Specware4.lisp is compiled.

(defun Specware::initializeInterpreterBase-0 () 
  (funcall 'Specware::initializeInterpreterBaseAux))