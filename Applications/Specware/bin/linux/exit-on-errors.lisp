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
  

(defun enlarge-stack (&optional (proposed 10000000))
  #+Allegro
  (let* ((old (sys::stack-cushion)))
    (sys::set-stack-cushion proposed)
    (let ((new (sys::stack-cushion)))
      (format t "~%Stack cushion was ~10D [#x~8X],~%" old old)
      (format t "~&       was set to ~10D [#x~8X],~%" proposed proposed)
      (format t "~&       and now is ~10D [#x~8X].~%" new new)
      new))
  #-Allegro
  (format t "enlarge-stack is currently a no-op for non-Allegro lisp")
  )

(defun set-gc-parameters (&optional verbose?)
  (setf (sys::gsgc-parameter :free-percent-new)            5) ; default is 25
  (setf (sys::gsgc-parameter :expansion-free-percent-new) 10) ; default is 35
  (setf (sys::gsgc-parameter :expansion-free-percent-old) 90) ; default is 35
  (setf (sys::gsgc-parameter :expansion-free-percent-old) 90) ; default is 35
  (setf (sys::gsgc-parameter :generation-spread)           2) ; default is  4, range is 0-26 
  (when verbose?
    (sys::gsgc-parameters)
    (room t)))

(defun compact-memory (&optional verbose?)
  (gc)
  (sys::resize-areas :verbose        verbose?
		     :global-gc      t          ; first, trigger global gc to compact oldspace
		     :tenure         t          ; second, move data from newspace into oldspace
		     :sift-old-areas t          ; third, combine adjacent oldspaces
		     :pack-heap      nil        ; do not make topmost oldspace as small as possible
		     :expand         t          ; expand oldspace if necessary, as follows:
		     :old            #x2000000  ; last, make oldspace at least this large 
		     )
  (when verbose?
    (sys::gsgc-parameters)
    (room t)))
