;;; -*- Mode: Emacs-Lisp -*-

;;; ilisp-openmcl

;;; This file is part of ILISP.
;;; Please refer to the file COPYING for copyrights and licensing
;;; information.
;;; Please refer to the file ACKNOWLEGDEMENTS for an (incomplete) list
;;; of present and past contributors.

;;;
;;; ILISP OpenMCL Common Lisp dialect definition
;;;
;;;


;;;%%%OpenMCL
(defvar ilisp-openmcl-init-file "openmcl.lisp")

(defun openmcl-check-prompt (old new)
  "Compare the break level printed at the beginning of the prompt."
  (let* ((old-level (if (and old (eq 1 (string-match "[0-9]+" old)))
 			(string-to-int (substring old 1))
 			0))
 	 (new-level (if (eq 1 (string-match "[0-9]+" new))
 			(string-to-int (substring new 1))
 			0)))
    (<= new-level old-level)))

;;;
(defdialect openmcl "OpenMCL"
  common-lisp
  (ilisp-load-init 'openmcl ilisp-openmcl-init-file)

  (setq comint-prompt-regexp "^\\([0-9]+ >\\|\\?\\|Step>\\|Inspect.*>\\) "
	ilisp-trace-command "(ilisp::openmcl-trace \"%s\" \"%s\" \"%s\")"
	comint-prompt-status 
	(function (lambda (old line)
	  (comint-prompt-status old line 'openmcl-check-prompt)))

	ilisp-error-regexp "ILISP:[^\"]*\\|Error [^\n]*\n\n"


	ilisp-arglist-command "(ilisp::arglist \"%s\" \"%s\")"

	ilisp-find-source-command "(ilisp::source-file \"%s\" \"%s\" \"%s\")"

	comint-fix-error ":pop"

	comint-continue ":go"

	ilisp-reset ":q"

	comint-interrupt-regexp "Break .*:"


	ilisp-directory-command  "(ccl::current-directory-name)"
	ilisp-set-directory-command "(ccl:cwd \"%s\")"

	)
  (setq ild-abort-string ":pop"
	ild-continue-string ":go"
	ild-next-string ":dn"		;needs work
	ild-next-string-arg ":dn %s"		;needs work
	ild-previous-string ":up"		;needs work
	ild-previous-string-arg ":up %s"		;needs work
	ild-top-string ":to"		;needs work
	ild-bottom-string ":bo"		;needs work
	ild-backtrace-string ":b"
	ild-locals-string "(:b t)"		;needs work
	ild-local-string-arg "(:f 0)"		;needs work
	ild-return-string "(:v 0 0)"		;needs work
	ild-retry-string ":rest"		;needs work
	ild-trap-on-exit-string ":boe")		;needs work
  )


(if (not openmcl-program) (setq openmcl-program "openmcl"))
