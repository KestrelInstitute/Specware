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

(unless (and (file-executable-p allegro-program)
	     (not (file-directory-p allegro-program)))
  (cond ((file-executable-p "/usr/local/acl/acl62/alisp")
	 (setq allegro-program "/usr/local/acl/acl62/alisp"))
	((file-executable-p "/usr/local/acl/acl70/alisp")
	 (setq allegro-program "/usr/local/acl/acl70/alisp"))))

(unless (and (file-executable-p allegro-program)
	     (not (file-directory-p allegro-program)))
  (error "Ooops -- no alisp at %s" allegro-program))

;; avoid trying to recompile on write-protected /usr/share/ directory

(setq ilisp-*directory* (concat *specware* "/Library/IO/Emacs/ilisp/"))
(allegro)
(ilisp-compile-inits) ; tell it to compile the appropriate files

(defun wait-for-file-to-compile (file)
  (let ((file (concat ilisp-*directory* file ".x86f")))
    (while (not (file-exists-p file))
      (message "waiting for cmucl to compile %s" file)
      (sleep-for 1))))

(wait-for-file-to-compile "ilisp-pkg")
(wait-for-file-to-compile "cmulisp")
(wait-for-file-to-compile "cl-ilisp")

;; When using cmulisp, cmulisp.x86f often seems truncated,
;; so for paranoia's sake, give it time to complete here
;; under allegro  as well
(sleep-for 4) 

(kill-emacs t)
