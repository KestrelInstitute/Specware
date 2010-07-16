;; haskell-hugs.el --- simplistic interaction mode with a
;; Hugs interpreter for Haskell developped by 
;;    The University of Nottingham and Yale University, 1994-1997.
;;    Web: http://www.haskell.org/hugs.
;; In standard Emacs terminology, this would be called
;;    inferior-hugs-mode
;;    
;; Copyright 1999 Guy Lapalme

;; Author:1998, 1999 Guy Lapalme <lapalme@iro.umontreal.ca>

;; Keywords: Hugs inferior mode, Hugs interaction mode
;; Version: 1.1
;; URL: http://www.iro.umontreal.ca/~lapalme/Hugs-interaction.html

;;; This file is not part of GNU Emacs.

;; This file is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.

;; This file is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 59 Temple Place - Suite 330,
;; Boston, MA 02111-1307, USA.


;;; Commentary:

;; Purpose:
;;
;; To send a Haskell buffer to another buffer running a Hugs interpreter
;; The functions are adapted from  the Hugs Mode developed by
;;         Chris Van Humbeeck <chris.vanhumbeeck@cs.kuleuven.ac.be>
;; which can be obtained at:
;; http://www-i2.informatik.rwth-aachen.de/Forschung/FP/Haskell/hugs-mode.el
;;
;; Installation:
;; 
;; To use with the Haskell mode of 
;;        Moss&Thorn <http://www.haskell.org/haskell-mode>
;; add this to .emacs:
;;
;;    (add-hook haskell-mode-hook 'turn-on-haskell-hugs)
;;
;; Customisation:
;;       The name of the hugs interpreter is in variable
;;          haskell-hugs-program-name
;;       Arguments can be sent to the Hugs interpreter when it is called
;;       by setting the value of the variable
;;          haskell-hugs-program-args
;;       which by default contains '("+.") so that the progress of the
;;       interpreter is visible without any "^H" in the *hugs* Emacs buffer.
;;
;;       This value can be interactively by calling C-cC-s with an
;;       argument. 
;;
;;       If the command does not seem to respond, see the
;;          content of the `comint-prompt-regexp' variable
;;          to check that it waits for the appropriate Hugs prompt
;;          the current value is appropriate for Hugs 1.3 and 1.4
;;
;;
;;    `haskell-hugs-hook' is invoked in the *hugs* once it is started.
;;    
;;; All functions/variables start with
;;; `(turn-(on/off)-)haskell-hugs' or `haskell-hugs-'.

(defgroup haskell-hugs nil
  "Major mode for interacting with an inferior Hugs session."
  :group 'haskell
  :prefix "haskell-hugs-")

(defun turn-on-haskell-hugs ()
  "Turn on Haskell interaction mode with a Hugs interpreter running in an
another Emacs buffer named *hugs*.
Maps the followind commands in the haskell keymap.
     \\[haskell-hugs-load-file]
       to save the current buffer and load it by sending the :load command
       to Hugs.
     \\[haskell-hugs-reload-file]
       to send the :reload command to Hugs without saving the buffer.
     \\[haskell-hugs-show-hugs-buffer]
       to show the Hugs buffer and go to it."
  (interactive)
  (local-set-key "\C-c\C-s" 'haskell-hugs-start-process)
  (local-set-key "\C-c\C-l" 'haskell-hugs-load-file)
  (local-set-key "\C-c\C-r" 'haskell-hugs-reload-file)
  (local-set-key "\C-c\C-b" 'haskell-hugs-show-hugs-buffer)
  )

(defun turn-off-haskell-hugs ()
  "Turn off Haskell interaction mode with a Hugs interpreter within a buffer."
  (interactive)
  (local-unset-key  "\C-c\C-s")
  (local-unset-key  "\C-c\C-l")
  (local-unset-key  "\C-c\C-r")
  (local-unset-key  "\C-c\C-b")
  )

(defvar haskell-hugs-mode-map nil)

(defun haskell-hugs-mode ()
;; called by haskell-hugs-start-process,
;; itself called by haskell-hugs-load-file
;; only when the file is loaded the first time
  "Major mode for interacting with an inferior Hugs session.

The commands available from within a Haskell script are:
     \\<haskell-mode-map>\\[haskell-hugs-load-file]
       to save the current buffer and load it by sending the :load command
       to Hugs.
     \\[haskell-hugs-reload-file]
       to send the :reload command to Hugs without saving the buffer.
     \\[haskell-hugs-show-hugs-buffer]
       to show the Hugs buffer and go to it.

\\<haskell-hugs-mode-map>
Commands:
Return at end of buffer sends line as input.
Return not at end copies rest of line to end and sends it.
\\[comint-kill-input] and \\[backward-kill-word] are kill commands,
imitating normal Unix input editing.
\\[comint-interrupt-subjob] interrupts the comint or its current
subjob if any.
\\[comint-stop-subjob] stops, likewise.
 \\[comint-quit-subjob] sends quit signal."
  (interactive)
  (comint-mode)
  (setq major-mode 'haskell-hugs-mode)
  (setq mode-name "Haskell Hugs")
  (if haskell-hugs-mode-map
      nil
    (setq haskell-hugs-mode-map (copy-keymap comint-mode-map))
    )
  (use-local-map haskell-hugs-mode-map)
  )

;; Hugs-interface

(require 'comint)
(require 'shell)

(defvar haskell-hugs-process nil
  "The active Hugs subprocess corresponding to current buffer.")

(defvar haskell-hugs-process-buffer nil
  "*Buffer used for communication with Hugs subprocess for current buffer.")

(defvar haskell-hugs-last-loaded-file nil
  "The last file loaded into the Hugs process.")

(defcustom haskell-hugs-program-name "hugs"
  "*The name of the command to start the Hugs interpreter."
  :type 'string
  :group 'haskell-hugs)

(defcustom haskell-hugs-program-args '("+.")
  "*A list of string args to send to the hugs process."
  :type '(repeat string)
  :group 'haskell-hugs)

(defvar haskell-hugs-load-end nil
  "Position of the end of the last load command.")

(defvar haskell-hugs-send-end nil
  "Position of the end of the last send command.")

(defun haskell-hugs-start-process (arg)
  "Start a Hugs process and invokes `haskell-hugs-hook' if not nil.
Prompts for a list of args if called with an argument."
  (interactive "P")
  (message "Starting `hugs-process' %s" haskell-hugs-program-name)
  (if arg
      (setq haskell-hugs-program-args
            (read-minibuffer "List of args for Hugs:"
                             (prin1-to-string haskell-hugs-program-args))))
  (setq haskell-hugs-process-buffer
        (apply 'make-comint
               "hugs" haskell-hugs-program-name nil
               haskell-hugs-program-args))
  (setq haskell-hugs-process
        (get-buffer-process haskell-hugs-process-buffer))
  ;; Select Hugs buffer temporarily
  (set-buffer haskell-hugs-process-buffer)
  (haskell-hugs-mode)
  (make-variable-buffer-local 'shell-cd-regexp)
  (make-local-variable 'shell-dirtrackp)
  (setq shell-cd-regexp         ":cd")
  (setq shell-dirtrackp         t)
  (setq comint-input-sentinel   'shell-directory-tracker)
                                ; ? or  module name in Hugs 1.4
  (setq comint-prompt-regexp  "^\? \\|^[A-Z][_a-zA-Z0-9\.]*> ")
    ;; comint's history syntax conflicts with Hugs syntax, eg. !!
  (setq comint-input-autoexpand nil)
  (run-hooks 'haskell-hugs-hook)
  (message "")
  )

(defun haskell-hugs-wait-for-output ()
  "Wait until output arrives and go to the last input."
  (while (progn			
	   (goto-char comint-last-input-end)
	   (not (re-search-forward comint-prompt-regexp nil t)))
    (accept-process-output haskell-hugs-process)))

(defun haskell-hugs-send (&rest string)
  "Send `haskell-hugs-process' the arguments (one or more strings).
A newline is sent after the strings and they are inserted into the
current buffer after the last output."
  ;; Wait until output arrives and go to the last input.
  (haskell-hugs-wait-for-output)
  ;; Position for this input.
  (goto-char (point-max))		
  (apply 'insert string)
  (comint-send-input)
  (setq haskell-hugs-send-end (marker-position comint-last-input-end)))

(defun haskell-hugs-go (load-command cd)
  "Save the current buffer and load its file into the Hugs process.
The first argument LOAD-COMMAND specifies how the file should be
loaded: as a new file (\":load \") or as a reload (\":reload \").

If the second argument CD is non-nil, change the Haskell-Hugs process to the
current buffer's directory before loading the file.

If the variable \"haskell-hugs-command\" is set then its value will be sent to
the Hugs process after the load command.  This can be used for a
top-level expression to evaluate."
  (let (file)
    (hack-local-variables);; In case they've changed
    (save-buffer)
    (if (string-equal load-command ":load ")
        (progn
          (setq file (buffer-file-name))
          (setq haskell-hugs-last-loaded-file file))
      (setq file ""))
    (let ((dir (expand-file-name default-directory))
          (cmd (and (boundp 'haskell-hugs-command)
                    haskell-hugs-command
                    (if (stringp haskell-hugs-command)
                        haskell-hugs-command
                      (symbol-name haskell-hugs-command)))))
      (if (and haskell-hugs-process-buffer
               (eq (process-status haskell-hugs-process) 'run))
	  ;; Ensure the Hugs buffer is selected.
	  (set-buffer haskell-hugs-process-buffer)
        ;; Start Haskell-Hugs process.
        (haskell-hugs-start-process nil))
 
      (if cd (haskell-hugs-send (concat ":cd " dir)))
      ;; Wait until output arrives and go to the last input.
      (haskell-hugs-wait-for-output)
      (haskell-hugs-send load-command file)
      ;; Error message search starts from last load command.
      (setq haskell-hugs-load-end (marker-position comint-last-input-end))
      (if cmd (haskell-hugs-send cmd))
      ;; Wait until output arrives and go to the last input.
      (haskell-hugs-wait-for-output)))
  )

(defun haskell-hugs-load-file (cd)
  "Save a hugs buffer file and load its file.
If CD (prefix argument if interactive) is non-nil, change the Hugs
process to the current buffer's directory before loading the file.
If there is an error, set the cursor at the error line otherwise show
the Hugs buffer."
  (interactive "P")
  (haskell-hugs-gen-load-file ":load " cd)
  )
 
(defun haskell-hugs-reload-file (cd)
  "Save a hugs buffer file and load its file.
If CD (prefix argument if interactive) is non-nil, change the Hugs
process to the current buffer's directory before loading the file.
If there is an error, set the cursor at the error line otherwise show
the Hugs buffer."
  (interactive "P")
  (haskell-hugs-gen-load-file ":reload " cd)
  )

(defun haskell-hugs-gen-load-file (cmd cd)
  "Save a hugs buffer file and load its file or reload depending on CMD.
If CD is non-nil, change the process to the current buffer's directory 
before loading the file. If there is an error, set the cursor at the 
error line otherwise show the Hugs buffer."
  (save-excursion (haskell-hugs-go cmd cd))
  ;; Ensure the Hugs buffer is selected.
  (set-buffer haskell-hugs-process-buffer)
  ;; Error message search starts from last load command.
  (goto-char haskell-hugs-load-end)
  (if (re-search-forward
       "^ERROR \"\\([^ ]*\\)\"\\( (line \\([0-9]*\\))\\|\\)" nil t)
      (let ((efile (buffer-substring (match-beginning 1)
				     (match-end 1)))
	    (eline (if (match-beginning 3)
                       (string-to-int (buffer-substring (match-beginning 3)
                                                        (match-end 3)))))
	    (emesg (buffer-substring (1+ (point))
				     (save-excursion (end-of-line) (point)))))
        (pop-to-buffer  haskell-hugs-process-buffer) ; show *hugs* buffer
        (goto-char (point-max))
        (recenter)
	(message "Hugs error %s %s"
                 (file-name-nondirectory efile) emesg)
        (if (file-exists-p efile)
            (progn (find-file-other-window efile)
                   (if eline (goto-line eline))
                   (recenter)))
        )
    (pop-to-buffer  haskell-hugs-process-buffer) ; show *hugs* buffer
    (goto-char (point-max))
    (message "There were no errors.")
    (recenter 2)                        ; show only the end...
    )
  )

(defun haskell-hugs-show-hugs-buffer ()
  "Goes to the Hugs buffer."
  (interactive)
  (if (or (not haskell-hugs-process-buffer)
          (not (buffer-live-p haskell-hugs-process-buffer)))
      (haskell-hugs-start-process nil))
  (pop-to-buffer  haskell-hugs-process-buffer)
  )
