;; for simplicity, use the same package that GatherComponents.lisp uses
(defpackage :Distribution (:use :common-lisp))
(in-package :Distribution)

;;(eval-when (compile eval load)
;;  #+Allegro (require "dist-utils")
;;  #-Allegro (load    "dist-utils")
;;  )

;;; Utilities for manipulating files and directories

;;; ================================================================================

(defun generic-directory (dir)
  (directory #-(or mcl sbcl) dir
	     #+(or mcl sbcl)
	       (if (null (pathname-name dir))
		   (merge-pathnames (make-pathname :name :wild :type :wild) dir)
		 dir)
	     :allow-other-keys      t	         ; permits implementation-specific keys to be ignored by other implementations (sbcl gives a style warning, sigh...)
	     ; :all                 recursive?   ; specific to mcl, but for uniformity, ignore
	     :directories           t	         ; specific to mcl     -- what does this mean?  TODO
	     :directories-are-files nil          ; specific to allegro -- we never want this option, but it defaults to T (!)
	     ))

(defun generic-directory? (pathname)
  #+Allegro (excl::file-directory-p pathname)
  #-Allegro (and (null (pathname-name pathname))
		 (null (pathname-type pathname))
		 (not (null (generic-directory pathname)))))

(defun generic-make-directory (dir)
  (let ((dir (if (pathnamep dir)
		 (namestring dir)
	       dir)))
    #+allegro (sys::make-directory dir)
    #+cmu     (unix:unix-mkdir dir #o755)
    #+mcl     (ccl:run-program "mkdir" (list dir))
    #+sbcl    (sb-ext:run-program "/bin/mkdir" (list dir))
    #+gcl     (lisp:system (format nil "mkdir ~a" dir))
    #-(or allegro cmu mcl sbcl gcl) (error "generic-make-directory: not Allegro, cmu, mcl, sbcl, or gcl")
    ))

(defun generic-delete-directory (dir &optional (contents? t))
  #+allegro
  (if contents?
      (excl:delete-directory-and-files dir)
    (excl:delete-directory dir))
  #-allegro
  (let* ((dirpath (if (stringp dir) (parse-namestring dir) dir))
	 (dirstr  (if (stringp dir) dir    (namestring dirpath))))
    #+mcl
    (if contents?
	(ccl:run-program "rm" (list "-R" dirstr))
      (ccl:run-program "rmdir" (list dirstr)))
    #+sbcl
    (if contents?
	(sb-ext::run-program "/bin/rm" (list "-R" dirstr))
      (sb-ext::run-program "/bin/rmdir" (list dirstr)))
    #-(or mcl sbcl)
    (progn
      (when contents?
	(loop for dir-item in (generic-directory dirpath) do
	  (when (generic-directory? dir-item)
	    (generic-delete-directory dir-item contents?))))
      #+cmu (unix:unix-rmdir dirstr)
      #+gcl (lisp:system (format nil "rmdir ~a" dirstr))
      #-(or cmu gcl mcl) (error "dir_utils::delete-directory doesn't know how to delete directories using ~A, which is not Allegro, MCL, CMU, or GCL"
				(lisp-implementation-type)))))

;;; --------------------------------------------------------------------------------

(defun generic-copy-file (source target)
  ;; This just copies the file verbatim, as you'd expect...
  ;; similar to concatenate-files below, but with special cases
  #+allegro (sys:copy-file source target :preserve-time t)
  #+mcl     (ccl:copy-file source target :if-exists :supersede)
  #+cmu     (ext:run-program    "cp"      (list (namestring source) (namestring target)))
  #+(and sbcl (not win32)) (sb-ext:run-program "/bin/cp"
                                ;#+win32 "c:\\WINDOWS\\system32\\xcopy.exe"
                                (list (namestring source) (namestring target)))
  #-(or allegro cmu mcl (and sbcl (not win32)))
  ;; use unsigned-byte to avoid problems reading x-symbol chars
  ;; For example, read-char might complain for chars with codes above #xC0
  (with-open-file (istream source 
			   :direction    :input 
			   :element-type 'unsigned-byte)
    (with-open-file (ostream target 
			     :direction         :output 
			     :element-type      'unsigned-byte 
			     :if-does-not-exist :create)
      (loop
	(let ((byte (read-byte istream nil :eof)))
	  (cond ((eq :eof byte) 
		 (return))
		(t 
		 (write-byte byte ostream))))))))

(defun concatenate-files (sources target)
  ;; similar to generic-copy-file above -- rarely used
  (ensure-directories-exist target)
  (with-open-file (ostream target 
			   :direction         :output 
			   :element-type      'unsigned-byte
			   :if-does-not-exist :create
			   :if-exists         :supersede)
    (loop for source in sources do
      (with-open-file (istream source 
			       :direction    :input 
			       :element-type 'unsigned-byte)
	(loop
	  (let ((byte (read-byte istream nil :eof)))
	    (cond
	     ((eq :eof byte)
	      (return))
	     (t
	      (write-byte byte ostream)))))))))

;;; ================================================================================

(defun namestring-lessp (x y)
  (string-lessp (namestring x) (namestring y)))

(defun name-lessp (x y)
  (string-lessp (pathname-name x) (pathname-name y)))

(defun equivalent-files? (source target)
  (and (probe-file source) 
       (probe-file target)
       (let ((return-code      (char-code #\Return))
	     (newline-code     (char-code #\Newline))
	     (whitespace-codes (list (char-code #\Space)
				     (char-code #\Tab)
				     (char-code #\Return)))
	     (outer-reversed-s-bytes nil))
	 (with-open-file   (ss source :element-type 'unsigned-byte)
	   (with-open-file (tt target :element-type 'unsigned-byte)
	     (do ((s-byte (read-byte ss nil nil)  (read-byte ss nil nil))
		  (t-byte (read-byte tt nil nil)  (read-byte tt nil nil)))
		 ((or (null s-byte) (null t-byte))
		  (and (null s-byte) (null t-byte)))
	       (push s-byte outer-reversed-s-bytes)
	       (unless 
		   (or (equal s-byte t-byte)
		       (and (= s-byte return-code)  (= t-byte newline-code) (equal (read-byte ss nil nil) t-byte))
		       (and (= s-byte newline-code) (= t-byte return-code)  (equal (read-byte tt nil nil) s-byte))
		       (let ((reversed-s-bytes (list s-byte))
			     (reversed-t-bytes (list t-byte)))
			 (do ((s-byte (read-byte ss nil nil)  (read-byte ss nil nil)))
			     ((or (null s-byte) (= s-byte newline-code)))
			   (push s-byte reversed-s-bytes))
			 (do ((t-byte (read-byte tt nil nil)  (read-byte tt nil nil)))
			     ((or (null t-byte) (= t-byte newline-code)))
			   (push t-byte reversed-t-bytes))
			 (cond ((and (equal (first reversed-s-bytes) return-code)
				     (equal (rest  reversed-s-bytes) reversed-t-bytes))
				(when *verbose*
				  (format t "~&;;; Ignoring CRLF/LF diff for ~A~%" source))
				t)
			       ((and (equal (first reversed-t-bytes) return-code)
				     (equal (rest  reversed-t-bytes) reversed-s-bytes))
				(when *verbose*
				  (format t "~&;;; Ignoring LF/CRLF diff for ~A~%" source))
				t)
			       ((and (equal (pathname-type source) "fasl")
				     (equal (pathname-type target) "fasl"))
				;; be smarter later, but for now quietly assume base libraries don't change
				(when (member (pathname-name source) '("Char" "Integer" "Nat" "String" "System"
								       "meta-slang-runtime" "ProvideSpecwareRuntime"
								       "IO" "State" "Lisp" "SpecwareRuntime")
					      :test 'equal)
				  (when *verbose*
				    (format t "~&;;; Assuming ~A is unchanged~%" (file-namestring source)))
				  t))
			       (t
				(let ((trimmed-reversed-s-bytes (do ((x reversed-s-bytes (cdr x)))
								    ((not (member (car x) whitespace-codes))
								     x)))
				      (trimmed-reversed-t-bytes (do ((x reversed-t-bytes (cdr x)))
								    ((not (member (car x) whitespace-codes))
								     x))))
				  (cond ((and (>= (length trimmed-reversed-s-bytes) 6)
					      (>= (length trimmed-reversed-t-bytes) 6)
					      (equal (subseq trimmed-reversed-s-bytes 0 (min (length trimmed-reversed-s-bytes) 6)) '(36 32 112 120 69 32)) ; "$ pxE "
					      (equal (subseq trimmed-reversed-t-bytes 0 (min (length trimmed-reversed-t-bytes) 6)) '(36 32 112 120 69 32))) ; "$ pxE "
					 (when *verbose*
					   (format t "~&;;; Ignoring minor cvs-related diff for ~A~%" source))
					 t)
					((and (equal (reverse trimmed-reversed-s-bytes) 
						     ;; "cc $(ABI_FLAG)"     
						     '(   99 99 32 36           40 65 66 73 95 70 76 65 71 41))   
					      (equal (reverse trimmed-reversed-t-bytes) 
						     ;; "gcc -w $(ABI_FLAG)" 
						     '(103 99 99 32 45 119 32 36 40 65 66 73 95 70 76 65 71 41)))  
					 (when *verbose*
					   (format t "~&;;; Ignoring minor makefile    diff for ~A~%" source))
					 t)
					((< (or (search 
						 '(32 58 101 116 97 68 36 123 101 100 111 99 64 32 68 69 84 65 68 80 85 32 116 101 115 64) ; reverse of "@set UPDATED @code{$Date: "
						 outer-reversed-s-bytes)
						999)
					    ;; A full line could look like this: "@set UPDATED @code{$Date: 2010/01/26 22:33:38 $}"
					    ;; so the match above might be preceeded by the reverse of some segment such as "2006/09/25" or "2006/".
					    ;; To count, the match must be within those few characters.
					    12)
					 (when *verbose*
					   (format t "~&;;; Ignoring minor texi date   diff for ~A~%" source))
					 t)
					(t 
					 (let ((s-bytes (reverse reversed-s-bytes))
					       (t-bytes (reverse reversed-t-bytes)))
					   (when *verbose*
					     (cond ((equalp (pathname-type source) "pdf")
						    (format t "~&;;; PDF files differ: ~A~%" source))
						   (t
						    (format t "~&;;; Diff from : ~A~%" source)
						    (format t "~&;;;        to : ~A~%" target)
						    (format t "~&Source: ~A~%" (coerce (mapcar #'code-char s-bytes) 'string))
						    (format t "~&Target: ~A~%" (coerce (mapcar #'code-char t-bytes) 'string))
						    (format t "~&Prior:  ~A~%" (subseq outer-reversed-s-bytes 0 (min (length outer-reversed-s-bytes) 26)))
						    )))
					   nil))))))))
		 (return nil))))))))

(defun coerce-to-directory (filename)
  (let* ((pn   (pathname filename))
	 (name (pathname-name      pn))
	 (path (pathname-directory pn))
	 (new-path (if (null name)
		       path
		     (append path (list name)))))
    (unless (member (first new-path) '(:absolute :relative))
      (setq new-path (cons :relative new-path)))
    (make-pathname :directory new-path :name nil :defaults pn)))

(defun ensure-subdirs-exist (dir &rest subdirs)
  (unless (probe-file dir)
    (ensure-directories-exist dir))
  (dolist (subdir subdirs)
    (setq dir (ensure-subdir-exists dir subdir)))
  dir)

(defun ensure-subdir-exists (dir subdir)
  (let ((pn (extend-directory dir subdir)))
    (unless (probe-file pn)
      (ensure-directories-exist pn))
    pn))

(defun extend-directory (dir &rest subdirs)
  (let* ((pn   (coerce-to-directory dir))
	 (path (append (pathname-directory pn) subdirs)))
    (make-pathname :directory path :name nil :defaults pn)))

;;; ================================================================================

(defparameter *ignored-directories* 
  '("CVS" "lisp" "Snark" ".svn"))

(defparameter *ignored-files*
  '(".cvsignore"))

(defparameter *ignored-types*
  ;; Don't copy vendor-specific files unless using that vendor
  ;; We assume we are using the same lisp for preparing the 
  ;; distribution as will be used to run the distributed images.
  '(#-Allegro "fasl" 
    #-CMU     "x86f"
    ))

(defun ignored-file? (file)
  (let* ((pn   (pathname file))
	 (dir  (first (last (pathname-directory pn))))
	 (name (pathname-name      pn))
	 (type (pathname-type      pn)))
    (or (member dir    *ignored-directories* :test 'equal)
	(member name   *ignored-directories* :test 'equal)
	(member name   *ignored-files*       :test 'equal)
	(member type   *ignored-types*       :test 'equal)
	(find #\~  name)
        (find #\~  type)
        (and (>= (length name) 2)
             (string-equal ".#" name :end2 2)) ; CVS diff files
	)))
      
;;; ================================================================================

(defun sorted-directory (pathname &key recursive? (sort-fn 'name-lessp))
  (unless (ignored-file? pathname)
    (let ((all-files '()))
      (labels ((add-file (file)
			 (let ((sub-files (generic-directory file)))
			   (dolist (pn sub-files)
			     (unless (or (ignored-file? pn)
					 (member pn all-files :test 'equalp))
			       (push pn all-files)
			       (when recursive?
				 (add-file pn)))))))
	(cond ((probe-file pathname)
	       (add-file (truename pathname))
	       (sort all-files sort-fn))
	      (t
	       '()))))))

;;; ================================================================================

(defun copy-dist-directory (source target &optional (recursive? t) (exclude? #'(lambda (x) (declare (ignore x)) nil)))
  (unless (ignored-file? source)
    (let* ((source-dirpath (coerce-to-directory source))
	   (target-dirpath (coerce-to-directory target)))
      ;; (ensure-directories-exist target-dirpath)
      (loop for dir-item in (generic-directory source-dirpath) do
	(if (and recursive? (generic-directory? dir-item))
	    (unless (equalp dir-item source)
	      (copy-dist-directory dir-item 
				   (extend-directory target-dirpath 
						     (or (pathname-name dir-item)
							 (car (last (pathname-directory dir-item)))))
				   t))
	  (unless (funcall exclude? dir-item) 
	    (copy-dist-file dir-item (merge-pathnames target-dirpath dir-item))))))))

(defun copy-dist-file (source target &optional (force? t))
  (unless (ignored-file? source)
    (cond ((probe-file source)
	   (let ((suppress?
		  (and (probe-file target)
		       (cond ((equivalent-files? source target)
			      t)
			     (force? 
			      (warn "Replacing old ~A with ~A" source target)
			      (delete-file target)
			      nil)
			     (t
			      (warn "Not replacing old ~A with ~A" source target)
			      t)))))
	     (unless suppress?
	       (ensure-directories-exist target)
	       (generic-copy-file source target))))
	  (t
	   (error "Cannot copy non-existing ~A to ~A" source target)))))

;;; ================================================================================

#+Allegro (provide "dir-utils")
