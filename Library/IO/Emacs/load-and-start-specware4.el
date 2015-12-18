;;; Load this file into Emacs to start up Specware 4.
;;; The only requirements are that Specware4 be properly installed
;;; and the environment variable SPECWARE4 be set.

;;; If the current emacs already has a specware shell in it,
;;; loading this file just selects it.

;;; If you already set the environment variable SPECWARE4 somewhere
;;; before starting Emacs, you can put the following defun in your ~/.emacs file
;;; to define the "M-x run-specware" command so that it loads this file.
;;; (Take out the initial semicolons.)
;
;(defun run-specware () (interactive) 
;  (load (concat (getenv "SPECWARE4") "/Library/IO/Emacs/load-and-start-specware4")))

;;; If you don't want to bother with setting environment variables
;;; you can put this longer form in your ~/.emacs file
;;; to define the "m-x run-specware" command so that it loads this file.
;;; (Take out the initial semicolons.)
;
;(defun run-specware ()
;  (interactive)
;  ;; The convention in the various scripts is that either SPECWARE4 is defined
;  ;; or it is set to "$HOME/Specware".
;  (let ((specware4dir (getenv "SPECWARE4")))
;    (when (null specware4dir)
;      (let ((default-specware4-dir (concat (getenv "HOME") "/Specware")))
;        (when (file-accessible-directory-p default-specware4-dir)
;          (setq specware4dir (setenv "SPECWARE4" default-specware4-dir)))))
;    (if (null specware4dir)
;        (error "SPECWARE4 is not defined and there is no Specware directory under your HOME directory")
;      (load (concat specware4dir "/Library/IO/Emacs/load-and-start-specware4")))))



;;; Concept of this file
;;;
;;; The idea is that this should do the same thing in terms of setting environment variables
;;; as the scripts such as SpecwareMac and Specware-gnu
;;; so that you can easily start Specware in a vanilla Emacs using "M-x run-specware".
;;;
;;; If you load this file in an emacs that already has a specware shell buffer,
;;; it just selects it.


;;; Although we could look at the directory containing this source file,
;;; that seems like a bad idea because it could become detached.
;;; Better to make sure the environment variable is set.
(when (or (null (getenv "SPECWARE4"))
          (equal (getenv "SPECWARE4") ""))
  (error "SPECWARE4 must be defined prior to loading load-and-start-specware4.el"))



(defun set-specware-env ()

  ;;; act='launch Specware'
  ;;; Not bothering with this, since it is not exported (from SpecwareMac).

  ;;; PATH=/bin:/usr/bin:/etc:/sbin:/usr/sbin:${PATH}
  ;;; Not sure that this was really needed; but just in case, let's add them if they are not already there.
  (let ((path-dirs (split-string (getenv "PATH") path-separator)))
    ;; I don't use parse-colon-path instead of split-string because it appends slashes
    (dolist (s (reverse '("/bin"
                          "/usr/bin"
                          "/etc"
                          "/sbin"
                          "/usr/sbin")))
      (when (not (member s path-dirs))
        (push s path-dirs)))
    (setenv "PATH" (mapconcat 'identity path-dirs path-separator)))

  ;;; $defaultemacsapp, $EmacsApp
  ;;; Not bothering with these, since they are not exported (from SpecwareMac).

  ;;; $SPECWARE4
  ;;; Not bothering with most of these forms, you can't get here unless
  ;;; SPECWARE4 is defined, and hopefully this file is being loaded relative to $SPECWARE4.
  ;;; However, we can set it to a full pathname.
  (unless (equal (substring (getenv "SPECWARE4") 0 1) "/")
    (setenv "SPECWARE4" (concat (getenv "PWD") "/" (getenv "SPECWARE4"))))

  ;;; SPECWARE_BIN="$SPECWARE4"/Applications/Specware/bin/unix
  (setenv "SPECWARE_BIN" (concat (getenv "SPECWARE4") "/Applications/Specware/bin/unix"))

  ;;; # Ensure SWPATH is set
  ;;; Emacs setenv does not require a separate export command.
  (when (null (getenv "SWPATH"))
    (setenv "SWPATH" (concat (getenv "SPECWARE4") ":/")))

  ;;; # Try to find lisp executable:
  (when (null (getenv "LISP"))
    (let ((lisps '("/Applications/sbcl/bin/sbcl"
                   "/usr/local/bin/sbcl"
                   (concat (getenv "HOME") "/bin/sbcl")
                   "/bin/lisp")))
      (let ((lisp-ex (pop lisps)))
        (while lisp-ex
          (if (file-executable-p lisp-ex)
              (progn (setenv "LISP" lisp-ex)
                     (setq lisp-ex nil))
            (setq lisp-ex (pop lisps)))))))

  ;;; -z "$LISP" and -x "$LISP"
  (unless (and (getenv "LISP") (file-executable-p (getenv "LISP")))
    (error "Failed to start Specware because no executable lisp could be found"))

  ;;; -z "$SPECWARE_INIT_FORM"
  (when (null (getenv "SPECWARE_INIT_FORM"))
    (setenv "SPECWARE_INIT_FORM" "NIL"))

  ;;; LISP_DIR=`dirname "$LISP"`
  ;;; This seems not to be used.

  ;;; LISP_EXECUTABLE="$SPECWARE_BIN"/Specware4.sbclexe
  (setenv "LISP_EXECUTABLE" (concat (getenv "SPECWARE_BIN") "/Specware4.sbclexe"))

  ;;; LISP_HEAP_IMAGE=NONE
  (setenv "LISP_HEAP_IMAGE" "NONE")

  ;;; LISP_DIRECTORY="$SPECWARE4"/
  (setenv "LISP_DIRECTORY" (concat (getenv "SPECWARE4") "/"))

) ; end of defun set-specware-env


(defun load-slime-and-run ()

  ;;; -l "$SPECWARE4"/Library/IO/Emacs/load-slime \
  (load (concat (getenv "SPECWARE4") "/Library/IO/Emacs/load-slime"))

  ;;; -f run-specware4
  (run-specware4)
)


;;; If specware is already in this emacs, just switch to it.
(if (and (boundp '*specware-buffer-name*)
         (get-buffer *specware-buffer-name*))
    (progn (switch-to-buffer *specware-buffer-name*)
	   (if (not (inferior-lisp-running-p))
	       (run-specware4)
	       ;; TODO: Fix the following bug:
	       ;; When you are in a *Specware Shell* buffer that does not have
	       ;; its inferior lisp running (i.e., you had done a "quit" earlier)
	       ;; and then you load this file (e.g., by doing "m-x run-specware")
	       ;; it does not put you at the end of the buffer at the Specware
	       ;; prompt, it leaves you one line up.
	       ;; I tried to fix this by putting (goto-char (point-max))
	       ;; after the (run-specware4), but that doesn't work,
	       ;; so there must be something else going on.
	       ;; Note that this doesn't happen if you are in a different
	       ;; buffer when you load this file.
	     ))
  (set-specware-env)
  (load-slime-and-run))
