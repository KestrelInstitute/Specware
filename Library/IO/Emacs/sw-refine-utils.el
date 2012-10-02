
;; From /specware/emacs/reshape-frame.el :

(defun select-frame-if-active (frame)
  (if (frame-live-p frame)
      (select-frame frame)))

;; From /specware/emacs/rea-x-mouse.el :

(defmacro eval-in-window (window &rest forms)
  "Switch to WINDOW, evaluate FORMS, return to original window."
  (` (let ((OriginallySelectedWindow (selected-window)))
       (unwind-protect
	   (progn
	     (select-window (, window))
	     (,@ forms))
	 (select-window OriginallySelectedWindow)))))
(put 'eval-in-window 'lisp-indent-hook 1)

;; From /specware/emacs/rea-x-mouse.el :

(defun window-under-xy (event)
;;;: cem: 8/17/90 13:03  Fix bug left over from 2/19/90 that was caused by the
 ;; save-excursion and save-window-excursion being in the wrong order.
;;;: cem: 2/19/90 16:32  Added save-excursion wrapper.  Fixes a bug where
 ;; if you had two windows viewing the same buffer and you called this function
 ;; on a point over one of them, it would change the part of the buffer viewed
 ;; to be the same as the part of the buffer viewed in the other window.
  (save-excursion
    (save-window-excursion
      (mouse-set-point event)
      (selected-window))))

;; From /specware/emacs/refine-comm.el :

(defun query-about-saving-file (file)
  "If there is a modified buffer visiting FILE, save it if user gives ok."
  (let ((buffer (get-file-buffer file)))
    (if buffer
	(save-excursion
	  (set-buffer buffer)
	  (and
	   (buffer-modified-p buffer)
	   (y-or-n-p (format "Save file %s ? " buffer-file-name))
	   (save-buffer))))))

