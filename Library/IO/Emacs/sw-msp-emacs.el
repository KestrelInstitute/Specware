
;;(verify-emacs-version)

(defvar *mspe-number-to-array* (make-vector 10000 nil))

(defun initialize-mspe-extents ()
  (fillarray *mspe-number-to-array* nil))

(add-hook 'specware-startup-hook 'initialize-mspe-extents)

(defun mspe-adjust-vector (vec sz)
  (let ((new-vec (make-vector sz nil)))
    (dotimes (i (length vec))
      (aset new-vec i (aref vec i)))
    new-vec))

(defun mspe-store-object-extent (n ext)
  (unless (< n (length *mspe-number-to-array*))
    (setq *mspe-number-to-array*
	  (mspe-adjust-vector *mspe-number-to-array*
			      (+ 10000 (length *mspe-number-to-array*)))))
  (aset *mspe-number-to-array* n (cons ext (aref *mspe-number-to-array* n))))

(defvar mspe-keymap nil)

(defun mspe-start-object-extent (n)
  (let ((ext (make-extent (point) (point))))
    (mspe-store-object-extent n ext)))

(defun mspe-extents-for-object (n)
  (let ((exts (aref *mspe-number-to-array* n)))
    (when (null exts)
      (error "Object %d has no extents" n))
    exts))

(defvar mspe-extents-duplicablep nil
  "Controls whether killed regions get copies of mspe-extents")

(defun mspe-finish-object-extent (n)
  (let ((ext (car (aref *mspe-number-to-array* n))))
    (set-extent-endpoints ext (extent-start-position ext) (point))
    (set-extent-property ext 'object-number n)
    (set-extent-property ext 'highlight t)
    (set-extent-property ext 'duplicable mspe-extents-duplicablep)
    (set-extent-property ext 'keymap mspe-keymap)
    (set-extent-property ext 'priority 0)))

(defun mspe-highlight-object-n (n)
  (let ((ext (car (aref *mspe-number-to-array* n))))
    (highlight-extent ext t)))

(defvar *mspe-buffer* nil)
(defvar *mspe-marker* nil)
(defvar *mspe-save-char-position* 0)

(defun string-to-mspe-buffer (s)
  (save-excursion
    (when *mspe-buffer* (set-buffer *mspe-buffer*))
    (when *mspe-marker* (goto-char *mspe-marker*))
    (insert-before-markers s)))

(defun mspe-insert (pp-fil ms-file)
  (save-excursion
    (when *mspe-buffer* (set-buffer *mspe-buffer*))
    (when *mspe-marker* (goto-char *mspe-marker*))
    (let ((font-lock-on font-lock-mode)
	  (buffer-read-only nil))
      (if font-lock-on (font-lock-mode -1))
      (insert-file-contents pp-fil)
      (load-file ms-file)
      (if font-lock-on (font-lock-mode 1)))
    (when *mspe-marker* (set-marker *mspe-marker* (point)))))

(defun mspe-add-extents (ext-lst)
   (while (consp ext-lst)
     (cond ((consp (car ext-lst))
	    (mspe-add-extents (car ext-lst))
	    (setq ext-lst (cdr ext-lst)))
	   (t (forward-char (cadr ext-lst))
	      (if (null (cddr ext-lst))
		  (mspe-finish-object-extent (car ext-lst))
		(mspe-start-object-extent (car ext-lst)))
	      (setq ext-lst (cddr ext-lst))))))

(defvar *beginning-of-mspe-output*)

(defun mspe-note-point ()
  (setq *beginning-of-mspe-output* (point)))
   
(defun mspe-insert-at-last (fil)
  (save-excursion
    (goto-char *beginning-of-mspe-output*)
    (load-file fil)))

(unless mspe-keymap
  (setq mspe-keymap (make-keymap))
  ;; unnecessary (set-keymap-parent map (current-global-map))
  (set-keymap-name mspe-keymap 'mspe-keymap)
  (define-key mspe-keymap '(button3) 'extent-copy-as-kill)
  (define-key mspe-keymap '(control button1) 'extent-insert-lisp-ref))

(defun extent-insert-lisp-ref (e)
  (interactive "e")
  (let ((ext (extent-of-event e)))
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;;;    (make-refine-window-visible t nil)
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    (insert (format "(mspe-n-o %d)" (extent-property ext 'object-number)))))

;; Not needed, since this function is defined in sw-refine-utils.el.

; (if (and (fboundp 'x:window-under-xy)
;          (not (fboundp 'window-under-xy)))
;     (defun window-under-xy (event)
;       (x:window-under-xy event)))

;;; Original version with macro call.

(defun extent-of-event (event)
  (eval-in-window (window-under-xy event)
    (let ((pt (event-point event)))
      (and pt (extent-at pt  nil 'object-number)))))

;; Expanded version.
;; Not needed, since the macro is defined in sw-refine-utils.el.

; (defun extent-of-event (event)
;   (let ((OriginallySelectedWindow (selected-window)))
;     (unwind-protect
; 	(progn
; 	  (select-window (window-under-xy event))
; 	  (let ((pt (event-point event)))
; 	    (and pt
; 		 (progn (setq *mspe-save-char-position* pt) t)
; 		 (extent-at pt  nil 'object-number))))
; 	 (select-window OriginallySelectedWindow))))

(defun extent-copy-as-kill (e)
  (interactive "e")
  (insert (extent-copy/delete e nil nil)))

(defun extent-copy/delete (event &optional delete copy-as-kill set-point)
  "Return the string that is designated by EXTENT. 
Arguments are:
           EXTENT
&optional DELETE - delete the motion active text region
    COPY-AS-KILL - copy the string to the kill ring
       SET-POINT - set point to the start of the motion active region."
  (eval-in-window (window-under-xy event)
    (let ((extent (extent-at (event-point event) nil 'object-number)))
      (if extent
	  (let* ((start (extent-start-position extent))
		 (end (extent-end-position extent))
		 (text 
		  (buffer-substring
		   (extent-start-position extent)
		   (extent-end-position extent))))
	    (if copy-as-kill (copy-region-as-kill start end))
	    (cond 
	     (delete (delete-region start end)
		     ;; (select-window window)
		     (if set-point 
			 (goto-char start))))
	    text)
	(error "No extent.")))))

(defvar *selecting-mspe-object?* nil)

(defun looking-for-mspe-object (prompt)
  (message prompt)
  (setq *selecting-mspe-object?* t))

;;;: jlm: 4/2/96 11:36    This is meaningful only as of version 19.13
;;;                                     In 19.11 it is effectively a no-op
;;;                                     See  /kids/dev4/editor/mspe-kids.el for ad hoc call in 19.11
;;;                                      to select-mspe-object via mspe-keymap 
(add-hook 'mouse-track-click-hook 'select-mspe-object)

(defun select-mspe-object (e ign)
  (if *selecting-mspe-object?*
      (let ((ext (extent-of-event e)))
	(if (extentp ext)
	    (let ((obj-num (extent-property ext 'object-number)))
	      (if obj-num
		  (progn
		    (setq *selecting-mspe-object?* nil)
		    (send-preemptive-message-to-lisp
		     (format "(emacs::mspe-object-selected %d)" obj-num)))))))))


(defun sw-erase-buffer (buf)
  (save-excursion
    (set-buffer buf)
    (let ((buffer-read-only nil))
      (erase-buffer))))

(provide 'sw-msp-emacs)
