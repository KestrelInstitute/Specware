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

(defun set-gc-parameters-for-build (&optional verbose?)
  (format t "~3%;;; Set GC parameters to good values for building specware (e.g. loading fasl files).~2%")
  ;;
  ;; make newspace grow slowly (maybe not the best strategy?)
  ;;
  (setf (sys::gsgc-parameter :free-percent-new)            5) ; default is 25
  (setf (sys::gsgc-parameter :expansion-free-percent-new) 10) ; default is 35
  ;;
  ;; make oldspaces grow quickly, to minimize the number of them
  ;;
  (setf (sys::gsgc-parameter :expansion-free-percent-old) 90) ; default is 35
  ;;
  ;; reduce the number of generations data must live before being tenured,
  ;; since most data created during the build phase is destined for 
  ;; permanent residence in oldspace anyway
  ;;
  (setf (sys::gsgc-parameter :generation-spread)           2) ; default is  4, range is 0-26 
  ;;
  (when verbose?
    (sys::gsgc-parameters)
    (room t)))

(defun set-gc-parameters-for-use (&optional verbose?)
  (format t "~3%;;; Set GC parameters to good values for normal use (e.g. processing specs).~2%")
  ;;
  ;; Restore parameters to default values.  (Still might want to fine tune these more.)
  ;;
  (setf (sys::gsgc-parameter :free-percent-new)           25) ; default is 25
  (setf (sys::gsgc-parameter :expansion-free-percent-new) 35) ; default is 35
  (setf (sys::gsgc-parameter :expansion-free-percent-old) 35) ; default is 35
  (setf (sys::gsgc-parameter :expansion-free-percent-old) 35) ; default is 35
  ;;
  ;; Make this at least about 6, to avoid tenuring interim data created by type checker, etc.
  ;;
  (setf (sys::gsgc-parameter :generation-spread)          12) ; default is  4, range is 0-26 
  (when verbose?
    (sys::gsgc-parameters)
    (room t)))

(defun compact-memory (&optional verbose?)
  (format t "~3%;;; Restructure memory to compact old spaces, etc.~2%")
  (gc)
  (gc t)
  (sys::resize-areas :verbose        verbose?
		     :global-gc      t          ; first, trigger global gc to compact oldspace
		     :tenure         t          ; second, move data from newspace into oldspace
		     :sift-old-areas t          ; third, combine adjacent oldspaces
		     :pack-heap      nil        ; do not make topmost oldspace as small as possible
		     :expand         t          ; expand oldspace if necessary, as follows:
		     :old            #x2000000  ; last, make oldspace at least this large (~ 20 MByte)
		     )
  ;; close all but the latest oldspace areas, so their contents
  ;; won't be gc'd again and again...
  (setf (sys::gsgc-parameter :open-old-area-fence)        -1)
  (gc t)
  (when verbose?
    (sys::gsgc-parameters)
    (room t)))
