(in-package "CL-USER")

(defmacro exiting-on-errors (&body body)
  `(handler-bind ((storage-condition                    (function bail-out))
		  (error                                (function bail-out))
		  #+Allegro
		  (synchronous-operating-system-signal  (function bail-out))
		  #+Allegro
		  (interrupt-signal                     (function bail-out))
		  )
     ,@body))

(defun return-code-for-exception (exception)
  ;; Unix return codes are encoded in a byte (i.e. mod 256),
  ;; so for clarity avoid values outside [0 .. 255]
  #+Allegro
  (typecase exception
    (INTERRUPT-SIGNAL                    
     (let ((signal-number (excl::operating-system-signal-number exception))
	   (signal-name   (excl::operating-system-signal-name   exception)))
       (when (stringp signal-number) (rotatef signal-name signal-number)) ; workaround for Allegro bug 
       signal-number))

    (STORAGE-CONDITION                   
     101)

    (SYNCHRONOUS-OPERATING-SYSTEM-SIGNAL 
     102)

    (t
     103))
  #-Allegro
  (declare (ignore exception))
  #-Allegro
  1)

;; Note: shell scripts may use this directly to terminate sessions:
(defun exit-from-lisp (return-code)
  (format t "~%Lisp session exiting with code ~D~%" return-code)
  #+Allegro                       (excl::exit        return-code)
  #+CMU                           (unix::unix-exit   return-code)
  #+SBCL                          (sb-unix:unix-exit return-code)
  #+OpenMCL                       (quit              return-code)
  #-(or Allegro CMU SBCL OpenMCL) (quit              return-code)
  )

(defun bail-out (exception)
  (format t "~2%Exception : ~A~%" exception)
  (let ((return-code (return-code-for-exception exception)))
    (exit-from-lisp return-code)))

