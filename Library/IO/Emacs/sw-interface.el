;;;; Emacs side of Emacs-Lisp communication protocol.

;;; Cloned from refine-comm.el, changing "refine" => "lisp"
;;; Then modified for our purposes.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;; User defined signal 1.
(defvar *lisp-message-interrupt-signal-number*
  (cond ((eq system-type 'berkeley-unix) 30)
	((eq system-type 'hpux)          16)
	((eq system-type 'aix-v3)        30)
	((eq system-type 'usg-unix-v)    30)
	((eq system-type 'windows-nt)    30)
	((eq system-type 'linux)         30)
	((eq system-type 'darwin)        30)
	(t (error "unknown operating system type")))
  "Signal number to tell lisp that a message is comming.")

;;; User defined signal 2.
(defvar *lisp-preemptive-message-interrupt-signal-number*
  (cond ((eq system-type 'berkeley-unix) 31)
	((eq system-type 'hpux)          17)
	((eq system-type 'aix-v3)        31)
	((eq system-type 'usg-unix-v)    31)
	((eq system-type 'windows-nt)    31)
	((eq system-type 'linux)         31)
	((eq system-type 'darwin)        31)
	(t (error "unknown operating system type")))
  "Signal number to tell lisp that a preemptive message is comming.")

(defun adjust-lisp-signals (sig1 sig2)
  (setq *lisp-message-interrupt-signal-number*            sig1)
  (setq *lisp-preemptive-message-interrupt-signal-number* sig2))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defvar sw:*current-specware-process* nil)

;;;(defun sw:eval-in-lisp (string)
;;;  (fi:eval-in-lisp (format "(emacs::make-process '%s)" string)))


(defun send-message-to-lisp (string)
  "Send a message to the lisp process.  First sends signal
 *lisp-message-interrupt-signal-number* to the lisp process, whose
 handler should make sure Lisp is ready to deal with an incoming message."
;  (send-signal-to-lisp *lisp-message-interrupt-signal-number*)
  (sw:eval-in-lisp (format "(io-spec::makeProcess '%s)" string)))

(defun sw:eval-interruptable-in-lisp (string)
  (setq sw:*current-specware-process* 
	(sw:eval-in-lisp (format "(IO-spec::makeProcess '%s)" string))))


(defun send-preemptive-message-to-lisp (string)
  "Send a message to the Lisp process.  First sends signal
 *lisp-preemptive-message-interrupt-signal-number* to the Lisp process, whose
 handler should make sure Lisp is ready to deal with an incoming message."
;  (send-signal-to-lisp *lisp-preemptive-message-interrupt-signal-number*)
  (sw:eval-in-lisp string))


(custom-set-variables
  ; Make it slightly wider
  '(dialog-frame-plist (quote (width 90 height 20))))

;;;-----------------------------------------------------------------------

(defvar startup-startup-hook nil)

(run-hooks 'specware-startup-hook)


;;;-----------------------------------------------------------------------


(provide 'sw-interface)
