;; Hack by Jim McDonald, Fri Apr 18, 2003

;; This file compiles some cmucl/xemacs ilisp interface files.
;; See $SPECWARE4/Applications/Specware/bin/linux/Init-ilisp-for-xemacs

;; There might be a simpler way to do this, but my attempts to
;; simply compile the given files led to peculiar problems,
;; so I finally just wrote this magic incantation and now hope
;; it keeps working...

;; Revised Fri Mar  5 17:05:35 PST 2004
;; It stopped working (apparently due to changes to run-plain-lisp), 
;; but using (cmulisp) seems to fix this (modulo pre-setting some vars)

(setq lisp-emacs-interface-type 'ilisp) 

(when (eq *specware-lisp* cmulisp)
  (unless (and (file-executable-p cmulisp-program)
	       (not (file-directory-p cmulisp-program)))
    (setq cmulisp-program "/usr/share/cmulisp/bin/lisp"))

  (unless (and (file-executable-p cmulisp-program)
	       (not (file-directory-p cmulisp-program)))
    (error "Ooops -- no cmulisp at %s" cmulisp-program)))

;; avoid trying to recompile on write-protected /usr/share/ directory

(setq ilisp-*directory* (concat *specware* "/Library/IO/Emacs/ilisp/"))
(cmulisp)
(ilisp-compile-inits) ; tell it to compile the appropriate files

(defun wait-for-file-to-compile (file)
  (let ((file (concat ilisp-*directory* file "." *fasl-extension*)))
    (while (not (file-exists-p file))
      (message "waiting for lisp to compile %s" file)
      (sleep-for 1))))

(wait-for-file-to-compile "ilisp-pkg")
(when (eq *specware-lisp* cmulisp)
  (wait-for-file-to-compile "cmulisp"))
(wait-for-file-to-compile "cl-ilisp")

;; cmulisp.x86f often seems truncated -- give it time to complete
(sleep-for 4) 

(kill-emacs t)
