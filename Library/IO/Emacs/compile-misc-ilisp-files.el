;; Hack by Jim McDonald, Fri Apr 18, 2003

;; This file compiles some cmucl/xemacs ilisp interface files.
;; See $SPECWARE4/Applications/Specware/bin/linux/Init-ilisp-for-xemacs

;; There might be a simpler way to do this, but my attempts to
;; simply compile the given files led to peculiar problems,
;; so I finally just wrote this magic incantation and now hope
;; it keeps working...

(setq lisp-emacs-interface-type 'ilisp) 

(run-plain-lisp)      ; start cmucl
(ilisp-compile-inits) ; tell it to compile the appropriate files

(defun wait-for-file-to-compile (file)
  (let ((file (concat *specware* "/Library/IO/Emacs/ilisp/" file ".x86f")))
    (while (not (file-exists-p file))
      (message "waiting for cmucl to compile %s" file)
      (sleep-for .5))))

(wait-for-file-to-compile "ilisp-pkg")
(wait-for-file-to-compile "cmulisp")
(wait-for-file-to-compile "cl-ilisp")

(kill-emacs t)
