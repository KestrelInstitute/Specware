(in-package "CL-USER")

#+Allegro
(defun bail-out (exception)
  (let ((return-code
	 ;; Unix return codes are encoded in a byte (i.e. mod 256),
	 ;; so for clarity avoid values outside [0 .. 255]
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
	    103))))

    (format t "~%Lisp session exiting with code ~D after : ~A~%" return-code exception)
    (exit return-code)))

(defmacro exiting-on-errors (&body body)
  #+Allegro
  `(handler-bind ((storage-condition                    (function bail-out))
		  (error                                (function bail-out))
		  (synchronous-operating-system-signal  (function bail-out))
		  (interrupt-signal                     (function bail-out))
		  )
     ,@body)
  #-Allegro
  (progn
    (format t "exiting-on-errors currently just expands to PROGN for non-Allegro lisp")
    `(progn ,@body)))
  

