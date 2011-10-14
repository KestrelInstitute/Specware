(defpackage :System-Spec (:use :cl))
(in-package :System-Spec)

(defvar specwareDebug? nil)

(defvar proverUseBase? t)

(defvar caseSensitiveSubstrate?
  #+case-sensitive t
  #-case-sensitive nil)

(defun |!error| (s)
  (format t "Error: ~a~%" s)
  (error s))

 ;;; op fail     : fa(a) String -> a
(defun fail (s) (break "~a" s))

;;; op debug     : fa(a) String -> a
(defun |!debug| (s) (when specwareDebug? (break "~a" s)))

(defvar *spec-print-mode*  :terse)
;;; NIL      -- handle as any other data
;;; :TERSE   -- search for specs and print them like this:  #<spec with I elements, J types, K ops, qualified as "foo">
;;; :LIMITED -- look for specs and print them using special *print-level* and *print-length*, defaulting to 4 and 40

(defvar *spec-print-level*  4)
(defvar *spec-print-length* 40)

(defun printSpecSpecial? (x)
  (and (not (null *spec-print-mode*))
       (typep  x '(simple-vector 4))
       ;; elements: SpecElements 
       (typep (svref x 0) 'cons)
       ;; ops: OpMap
       (typep (svref x 1) '(SIMPLE-VECTOR 3))
       (typep (svref (svref x 1) 0) 'HASH-TABLE)
       (typep (svref (svref x 1) 1) 'BOOLEAN)
       (typep (svref (svref x 1) 2) 'LIST)
       ;; qualifier: Option Qualifier
       (typep (svref x 2) 'cons)
       ;; types: TypeMap
       (typep (svref x 1) '(SIMPLE-VECTOR 3))
       (typep (svref (svref x 3) 0) 'HASH-TABLE)
       (typep (svref (svref x 3) 1) 'BOOLEAN)
       (typep (svref (svref x 3) 2) 'LIST)))

(defun specialSpecToString (s) 
  (case *spec-print-mode*
    (:terse
     (format nil "<Spec with ~3D elements, ~3D types, ~3D ops, ~A>"
             (length (svref s 0))
             (hash-table-count (svref (svref s 3) 0))
             (hash-table-count (svref (svref s 1) 0))
             (if (eq (car (svref s 2)) :|Some|)
                 (format nil "qualified by ~S" (cdr (svref s 2)))
                 "unqualified")))
    (t
     ;; :limited
     (let* ((*print-level*  (min *print-level*  *spec-print-level*))   
            (*print-length* (min *print-length* *spec-print-length*)))
       (format nil "~S" s)))))

;;; op anyToString : fa(a) a -> String
(defun anyToString (x) 
  (let ((common-lisp::*print-pretty* nil)) 
    (if (null *spec-print-mode*)
        (format nil "~S" x)
        (flet ((aux (x)
                 (typecase x 
                   (cons 
                    (let ((strs '("(")))
                      (do ((x x (cdr x)))
                          ((atom x)
                           (pop strs)
                           (unless (null x)
                             (push " . " strs)
                             (push (anyToString x) strs))
                           (push ")" strs))
                        (push (anyToString (car x)) strs)
                        (push " " strs))
                      (pop strs)
                      (push ")" strs)
                      (apply 'concatenate 'string (reverse strs))))
                   (simple-vector 
                    (if (printSpecSpecial? x)
                        (specialSpecToString x)
                        (let ((strs '("#(")))
                          (when (> (length x) 0)
                            (dotimes (i (length x))
                              (push (anyToString (svref x i)) strs)
                              (push " " strs))
                            (pop strs))
                          (push ")" strs)
                          (apply 'concatenate 'string (reverse strs)))))
                   (t
                    (format nil "~S" x)))))
          (aux x)))))

;;; op print    : fa(a) a -> a
(defun |!print| (x) (print x) (force-output) x)

(defun toScreen (x)
 ;; Note: (format t ...) goes to *standard-output*
 ;;    but (princ ... t) goes to *terminal-io*
 ;; Confusing, but that's the standard...
 ;; We want *standard-output* so it can be redirected (e.g., by the test suite)
 (declare (type cl:simple-string x))
 (princ x *standard-output*)
 (force-output *standard-output*))

(defun writeLine (x)
 ;; Note: (format t ...) goes to *standard-output*
 ;;    but (princ ... t) goes to *terminal-io*
 ;; Confusing, but that's the standard...
 ;; We want *standard-output* so it can be redirected (e.g., by the test suite)
 (declare (type cl:simple-string x))
 (princ x *standard-output*)
 (terpri *standard-output*)
 (force-output *standard-output*))

;;; op warn     : fa(a) String -> a
(defun |!warn| (s) (warn "~a" s))

;;; op time     : fa(a) a -> a
(defmacro |!time| (x) (time x))

;;; op internalRunTime () : Nat
(defun internalRunTime-0 () (GET-INTERNAL-RUN-TIME))

(defun |!random| (n) (random n))

;;; #-Lispworks
;;; (defun getenv (x) (Specware::getenv x))

;; The Lisp getenv returns nil if the name is not in the environment. 
;; Otherwise it returns a string. We want to be able to distinguish
;; the outcomes in MetaSlang

;;; op getEnv : String -> Option String
(defun getEnv (name)
  (let ((val (Specware::getenv name)))
    (if (or (eq val nil) (equal val ""))    ; I think it returns "" if not set
	(cons :|None| nil)
      (cons :|Some| val))))

(defvar msWindowsSystem? #+(or mswindows win32) t #-(or mswindows win32) nil)

;; The same function with the same name, but in a different package is
;; defined in Specware4/Applications/Handwritten/Lisp/load-utilities.lisp
(defun temporaryDirectory-0 ()
  (ensure-final-slash
   (cl:substitute #\/ #\\
		  #+(or win32 winnt mswindows)
		  (or (Specware::getenv "TEMP") (Specware::getenv "TMP")
		      #+allegro
		      (namestring (SYSTEM:temporary-directory)))
		  #+(and (not unix) Lispworks) (namestring SYSTEM::*TEMP-DIRECTORY*)
		  #+(and (not win32) unix) "/tmp/"
		  )))

;; The same function with the same name, but in a different package is
;; defined in Specware4/Applications/Handwritten/Lisp/load-utilities.lisp
(defun ensure-final-slash (dirname)
  (if (member (elt dirname (- (length dirname) 1))
	      '(#\/ #\\))
      dirname
    (concatenate 'string dirname "/")))

;;;  op temporaryDirectory : String
(defparameter temporaryDirectory
    (substitute #\/ #\\ (temporaryDirectory-0)))

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
  #+(and cmu (not darwin)) (ext:gc :full full?)
  #+(and cmu darwin) (when full? (ext:gc)))

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
