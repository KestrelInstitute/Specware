;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: mes -*-
;;; File: profiling.lisp
;;; The contents of this file are subject to the Mozilla Public License
;;; Version 1.1 (the "License"); you may not use this file except in
;;; compliance with the License. You may obtain a copy of the License at
;;; http://www.mozilla.org/MPL/
;;;
;;; Software distributed under the License is distributed on an "AS IS"
;;; basis, WITHOUT WARRANTY OF ANY KIND, either express or implied. See the
;;; License for the specific language governing rights and limitations
;;; under the License.
;;;
;;; The Original Code is SNARK.
;;; The Initial Developer of the Original Code is SRI International.
;;; Portions created by the Initial Developer are Copyright (C) 1981-2003.
;;; All Rights Reserved.
;;;
;;; Contributor(s): Mark E. Stickel <stickel@ai.sri.com>.

(in-package :mes)

#+(or MCL CMU)
(defmacro monitor-form (form 
                        &optional (nested :exclusive) (threshold mon:*default-threshold*)
                        (key :percent-time))
  `(unwind-protect
     (progn
       (mapc 'mon:monitor-all
             (adjoin *package* (mapcar 'find-package '(:mes :mes-sparse-array :snark))))
       (mon:reset-all-monitoring)
       (prog1
         (time ,form)
         (let ((*package* (find-package :snark)))
           (mon:report-monitoring :all ,nested ,threshold ,key :ignore-no-calls))))
     (mon:unmonitor)))

#+(or MCL CMU)
(defmacro profile (form)
  `(monitor-form ,form))

#+Allegro
(defun profile-form (form)
  (let ((prof::*maxsamples* 100000000))
    (unwind-protect
	(progn
	  (prof::start-profiler
	    :type :time
;;	    #+ALLEGRO-V4.3 :COUNT #+ALLEGRO-V4.3 10000
	    )
	  (eval form))
      (prof::stop-profiler)
;;      (prof::show-call-counts :count 100)
      (let ((prof::*significance-threshold* 0.002))
	(prof::show-flat-profile))
      (prof::show-call-graph))))

#+Allegro
(defmacro profile (form)
  `(profile-form ',form))

#+Lucid
(defvar monitor-fns nil)

#+Lucid
(defun profile-functions-in-current-package ()
  (setq monitor-fns nil)
  (do-symbols (x *package*)
    (when (and (eq (symbol-package x) *package*) (fboundp x))
      (push x monitor-fns)))
  nil)

#+Lucid
(defmacro profile (form)
  `(multiple-value-prog1
     (progn
       (unless monitor-fns
	 (profile-functions-in-current-package))
       (monitor::monitor-functions monitor-fns)
       (monitor::start-monitoring)
       ,form)
     (monitor::stop-monitoring)
;;   (monitor::print-monitors)
;;   (monitor::summarize-monitors :exclusive-time t :inclusive-time t :exclusive-consing t :inclusive-consing t :number-of-calls t)
     (show-monitors)
     (monitor::unmonitor-functions monitor-fns)))

#+Lucid
(defun extract-monitor-data (obj)
  (let ((s (with-output-to-string (s) (monitor::print-monitor obj s) s)))
    (list obj
	  (let ((n (search "Number of calls           :" s))) (or (and n (read-from-string (subseq s (+ 27 n)))) 0))
	  (let ((n (search "Inclusive Time (secs)     :" s))) (or (and n (read-from-string (subseq s (+ 27 n)))) 0.0))
	  (let ((n (search "Exclusive Time (secs)     :" s))) (or (and n (read-from-string (subseq s (+ 27 n)))) 0.0))
	  (let ((n (search "Inclusive Consing (words) :" s))) (or (and n (read-from-string (subseq s (+ 27 n)))) 0))
	  (let ((n (search "Exclusive Consing (words) :" s))) (or (and n (read-from-string (subseq s (+ 27 n)))) 0)))))

#+Lucid
(defun show-monitor-data (x)
  (unless (= (second x) 0)
    (format t "~%~8,2F~10,2F~11D~10D~9D  ~S"
	    (third x)
	    (fourth x)
	    (* (fifth x) 4)
	    (* (sixth x) 4)
	    (second x)
	    (first x)))
  x)

#+Lucid
(defun show-monitors ()
  (format t "~%   Incl.     Excl.      Incl.     Excl.")
  (format t "~%Run Time  Run Time    Consing   Consing    Calls  Function")
  (format t "~%   (sec)     (sec)    (bytes)   (bytes)")
  (mapc #'show-monitor-data (sort (mapcar #'extract-monitor-data monitor-fns) #'> :key #'third))
  (format t "~%")
  nil)

;;; profiling.lisp EOF
