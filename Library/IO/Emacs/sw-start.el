(defvar sw:buffer-name "*specware*"
  "*Default buffer name used by specware.  This variable is set by
start-specware when a new buffer name is used.")

(defvar sw:directory nil
  "*Default directory in which the process started by start-specware uses.")

(defvar sw:image-name "lisp"
  "*Default Common Lisp executable image used by start-specware.  The value
is a string that names the executable image start-specware invokes.")

(defvar sw:image-arguments nil
  "*Default Common Lisp image arguments when invoked from `start-specware',
which must be a list of strings.  Each element of the list is one command
line argument.")

(defvar sw:host nil
  "*The host on which start-specware starts the Common Lisp
subprocess.  The default is the host on which emacs is running.")

(defvar sw:image-file nil
  "*Default Common Lisp heap image used by start-specware.  If this
variable is nil, and the corresponding argument to start-specware is not
given, then a default heap image is loaded.")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun sw:start-specware (&optional buffer-name directory executable-image-name
				 image-args host image-file)
  (interactive)
  (sw:common-lisp buffer-name directory executable-image-name image-args
		  host image-file))
