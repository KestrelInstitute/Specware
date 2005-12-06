(in-package "CL-USER")

(defun enlarge-stack (&optional (proposed 10000000))
  #+Allegro (let* ((old (sys::stack-cushion)))
	      (sys::set-stack-cushion proposed)
	      (let ((new (sys::stack-cushion)))
		(format t "~%Stack cushion was ~10D [#x~8X],~%" old old)
		(format t "~&       was set to ~10D [#x~8X],~%" proposed proposed)
		(format t "~&       and now is ~10D [#x~8X].~%" new new)
		new))
  #-Allegro (declare (ignore proposed))
  #-Allegro (format t "~&enlarge-stack is currently a no-op for non-Allegro lisp~%")
  )

(defun set-gc-parameters-for-build (&optional verbose?)
  (format t "~3%;;; Set GC parameters to good values for building specware (e.g. loading fasl files).~2%")
  (when verbose?
    (format t "~&;;; (room) before setting parameters for build phase:~%")
    (room))
  #+Allegro (progn
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
	      )
  #-Allegro (format t "~&set-gc-parameters-for-build is currently a no-op for non-Allegro lisp~%")
  ;;
  (when verbose?
    #+Allegro (sys::gsgc-parameters)
    (format t "~&;;; (room) after setting parameters for build phase:~%")
    (room)))

(defun set-gc-parameters-for-use (&optional verbose?)
  (format t "~3%;;; Set GC parameters to good values for normal use (e.g. processing specs).~2%")
  (when verbose?
    (format t "~&;;; (room) before setting parameters for normal use:~%")
    (room))
  #+Allegro (progn
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
	      )
  ;;; Set gc parameters at startup
  #+mcl
  (push  #'(lambda ()
	     (ccl:set-lisp-heap-gc-threshold (* 16777216 8))
	     (ccl:egc nil))
	 ccl:*lisp-startup-functions*)

  #-(or Allegro mcl) (format t "~&set-gc-parameters-for-use is currently a no-op for non-Allegro lisp~%")
  ;;
  (when verbose?
    #+Allegro (sys::gsgc-parameters)
    (format t "~&;;; (room) after setting parameters for normal use:~%")
    (room)))

(defun compact-memory (&optional verbose? (fence -1) (old 0))
  (format t "~3%;;; Restructure memory to compact old spaces, etc.~2%")
  (when verbose?
    (format t "~&;;; (room) before compacting.~%")
    (room))
  #+Allegro (progn
	      (dotimes (i 4)
		(dotimes (j 30) (gc :tenure))
		(dotimes (j  4) (gc t))
		(sys::resize-areas :verbose        verbose?
				   :global-gc      t ; first, trigger global gc to compact oldspace
				   :tenure         t ; second, move data from newspace into oldspace
				   :sift-old-areas t ; third, combine adjacent oldspaces
				   :pack-heap      nil ; make topmost oldspace as small as possible
				   :expand         t ; expand oldspace if necessary, as follows:
				   :old            old ; last, make oldspace at least this large
				   ))
	      (when verbose?
		(format t "~&;;; (room) after resize-areas:~%")
		(room))
	      ;; close all but the latest oldspace areas, so their contents
	      ;; won't be gc'd again and again...
	      #+ALLEGRO-V6.2 
	      (setf (sys::gsgc-parameter :open-old-area-fence) fence)
	      (gc t)
	      (when verbose?
		(sys::gsgc-parameters)
		(format t "~&;;; (room) after setting fence to -1:~%")
		(room)))
  #-Allegro  (format t "~&compact-memory is currently a no-op for non-Allegro lisp~%")
  (when verbose?
    (format t "~&;;; (room) after compacting:~%")
    (room)))


