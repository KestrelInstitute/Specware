#+Lispworks
(setq *default-package-use-list* '("CL"))
#+mcl
(setq ccl:*make-package-use-defaults* '("CL"))

(defpackage :Specware (:use :cl))
(defpackage :System-Spec)

(in-package :Specware)

(terpri) ; purely cosmetic

(defvar cygwin? nil)
(defvar System-Spec::msWindowsSystem? #+(or win32 mswindows) t
                                      #-(or win32 mswindows) nil)

(defun fixCase (str)
  #+case-sensitive str
  #-case-sensitive (string-upcase str))

#+allegro(setq excl:*global-gc-behavior* '(10 2.0))

;; The following flag disables the collection of xref information when a lisp
;; file is compiled and loaded. When true, it collects such information,
;; but it seems that for monadic code (with lots of closures), compiling
;; such information is very slow (ie. minutes). Other than changing the
;; load time, there is no change to the behaviour of a program.
#+allegro(setq xref::*record-xref-info* nil)

#+sbcl (eval-when (:compile-toplevel :load-toplevel :execute)
         (let ((sb-fasl:*fasl-file-type* "fasl"))
           (require :sb-posix)))

(defun sw-parse-namestring (str)
  #-sbcl (parse-namestring str)
  #+sbcl (sb-ext:parse-native-namestring str))

;;; ---------------
;; The following collection have been adapted from the 2000 load.lisp
;; file. Perhaps they should be factored into a separate file as they
;; are likely to be used for many of the generated lisp applications?

(defun pathname-directory-string (p)
  (let* ((dirnames (pathname-directory p))
         (main-dir-str (apply #'concatenate 'string
                              (loop for d in (cdr dirnames)
                                nconcing (list "/" d)))))
    (if (eq (car dirnames) :absolute)
        main-dir-str
      (format nil ".~a" main-dir-str))))

(defun parse-device-directory (str)
  (let ((found-index (position #\: str)))
    (if found-index
        (values (subseq str 0 found-index)
                (subseq str (1+ found-index)))
      (values nil str))))

(defun convert-pathname-to-cygwin (dir-str)
  (multiple-value-bind (dev dir)
      (parse-device-directory dir-str)
    (let ((dir (substitute #\/ #\\ dir)))
      (if (and (> (length dir) 8) (string= dir "/cygwin/" :end1 8))
          (subseq dir 7)
          (concatenate 'string "/cygdrive/" (string-downcase dev) dir)))))

(defun to-cygwin-name (pname)
  (if cygwin?
      (convert-pathname-to-cygwin pname)
      pname))

(defun convert-pathname-from-cygwin (dir-str)
  (if (and (> (length dir-str) 10) (string= dir-str "/cygdrive/" :end1 10))
      (let* ((rem-dir (subseq dir-str 10))
             (i (position #\/ rem-dir)))
        (if i
            (concatenate 'string (string-upcase (subseq rem-dir 0 i)) ":/" (subseq rem-dir (+ i 1)))
            rem-dir))
      (if (and cygwin? (> (length dir-str) 6) (string= dir-str "/home/" :end1 6))
          (concatenate 'string "C:/cygwin" dir-str)
          dir-str)))

(defun from-cygwin-name (pname)
  (if cygwin?
      (convert-pathname-from-cygwin pname)
      pname))

;; The same function with the same name, but in a different package is
;; defined in Specware4/Library/Legacy/Utilities/Handwritten/Lisp/System.lisp
(defun ensure-final-slash (dirname)
  (if (member (elt dirname (- (length dirname) 1))
              '(#\/ #\\))
      dirname
    (concatenate 'string dirname "/")))

(defun current-directory ()
  ;; we need consistency: all pathnames, or all strings, or all lists
  ;; of strings, ...
  (let* ((dir
         #+allegro   (substitute #\/ #\\ (namestring (excl::current-directory)))
         #+Lispworks (hcl:get-working-directory)   ; ??       (current-pathname)
         #+mcl       (ccl::current-directory-name) ; ??
         #+cmu       (extensions:default-directory) ; pathname
         #+sbcl      (sb-unix:posix-getcwd)
         #+gcl       (system-short-str #+unix "pwd" #-unix "cd")
         #+clisp     (ext:default-directory)
         )
         (str-dir (if (pathnamep dir)
                      (pathname-directory-string dir)
                      dir)))
    (ensure-final-slash str-dir)))

#+gcl
(defun system-str (cmd &optional args)
  (let ((tmp-file (format nil "~a/system_output" (temporaryDirectory-0)))
        (result ""))
    (lisp:system (format nil "~a ~a > ~a" cmd (or args "") tmp-file))
    (file-to-string tmp-file)))

#+gcl
(defun system-short-str (cmd &optional args)
  (let ((tmp-file (format nil "~a/system_output" (temporaryDirectory-0)))
        (result ""))
    (lisp:system (format nil "~a ~a > ~a" cmd (or args "") tmp-file))
    (first-line-of-file tmp-file)))

(defun split-components (str delimiters)
  (let* ((chars (coerce str 'list))
         (components nil)
         (this-component-chars nil))
    (dolist (char chars)
      (if (member char delimiters)
          (unless (null this-component-chars)
            (push (coerce (reverse this-component-chars) 'string)
                  components)
            (setq this-component-chars nil))
        (push char this-component-chars)))
    (unless (null this-component-chars)
      (push (coerce (reverse this-component-chars) 'string)
            components))
    (reverse components)))

(defun split-dir-components (str)
  (split-components str '(#\/ #\\)))

(defun dir-to-path (directory &optional default-dir)
  (if (pathnamep directory) directory
    (let ((directory (from-cygwin-name directory)))
      (multiple-value-bind (dev dir)
        (parse-device-directory directory)
      (if (and (> (length dir) 0) (member (elt dir 0) '(#\/ #\\)))
          (setq dir (cons #+gcl :root #-gcl :absolute (split-dir-components dir)))
        (setq dir (concatenate 'list
                               (pathname-directory (or default-dir (current-directory)))
                               (split-dir-components directory))))
      (make-pathname :directory dir
                     :device (or dev (and default-dir (pathname-device default-dir))))))))

(defvar *tdir*)
(defvar *tdirp*)

(defun remove-final-slash (dirname)
  (let ((last-index (- (length dirname) 1)))
    (if (member (elt dirname last-index) '(#\/ #\\))
        (subseq dirname 0 last-index)
      dirname)))

(defun change-directory (directory)
  ;; (format t "Changing to: ~A~%" directory)
  (let ((dirpath (dir-to-path directory)))
    (setq directory (namestring dirpath))
    (if #-clisp (probe-file (remove-final-slash directory)) ; remove necessary in some cl's
        #+clisp (ext:probe-directory directory)
        (progn
          #+allegro   (excl::chdir          directory)
          #+Lispworks (hcl:change-directory directory)
          #+mcl       (ccl::%chdir          directory)
          #+gcl       (si:chdir         directory)
          #+cmu       (setf (extensions:default-directory) directory)
          #+cmu       (unix:unix-chdir directory)
          #+sbcl      (sb-posix:chdir directory)
          ;            (sb-unix::int-syscall ("chdir" sb-alien:c-string) directory)
          #+clisp     (setf (ext:default-directory) directory)
                                        ;#+gcl
          ;; in Allegro CL, at least,
          ;; if (current-directory) is already a pathname, then
          ;; (make-pathname (current-directory)) will fail
          (setq cl:*default-pathname-defaults* dirpath))
      (warn "Directory ~a does not exist" directory))))

(defun full-file-name (file-or-dir)
  (namestring (make-pathname :name file-or-dir :defaults cl:*default-pathname-defaults*)))

(defun program-and-user-command-line-arguments ()
  ;; The invoked program name followed by a list of user command line arguments (skipping runtime/toplevel/etc. options).
  #+allegro   (system::command-line-arguments)  ;; alisp -W -- x y z   =>   ("/usr/home/kestrel/xxx/alisp" "x" "y" "z")
  #+sbcl      sb-ext:*posix-argv*               ;; sbcl --noinform --end-runtime-options  --no-userinit --end-toplevel-options x y z   =>   ("sbcl" "x" "y" "z")
                                                ;; sbcl x y z      =>   ("sbcl" "x" "y" "z")
                                                ;; sbcl -- x y z   =>   ("sbcl" "--" "x" "y" "z")
  #-(or allegro sbcl) '()
  )

(defun user-command-line-arguments ()
  ;; A list of user command line arguments
  (cdr (program-and-user-command-line-arguments)))

#+(or mcl sbcl)                                 ; doesn't have setenv built=in
(defvar *environment-shadow* nil)

(defun getenv (varname)
  #+allegro   (si::getenv varname)
  #+mcl       (or (cdr (assoc (intern varname "KEYWORD") *environment-shadow*))
                  (ccl::getenv varname))
  #+lispworks (hcl::getenv varname)     ;?
  #+cmu       (cdr (assoc (intern varname "KEYWORD") ext:*environment-list*))
  #+sbcl      (or (cdr (assoc (intern varname "KEYWORD") *environment-shadow*))
                  (sb-ext:posix-getenv  varname))
  #+gcl       (si:getenv varname)
  #+clisp     (ext:getenv varname)
  )

(defun setenv (varname newvalue)
  #+allegro   (setf (si::getenv varname) newvalue)
  #+(or mcl sbcl) (let ((pr (assoc (intern varname "KEYWORD") *environment-shadow*)))
                    (if pr (setf (cdr pr) newvalue)
                        (push (cons (intern varname "KEYWORD") newvalue)
                              *environment-shadow*)))
  #+lispworks (setf (hcl::getenv varname) newvalue)
  #+cmu       (let ((pr (assoc (intern varname "KEYWORD") ext:*environment-list*)))
                (if pr (setf (cdr pr) newvalue)
                  (push (cons (intern varname "KEYWORD") newvalue)
                        ext:*environment-list*)))
  #+gcl       (si:setenv varname newvalue)
  #+clisp     (setf (ext:getenv varname) newvalue)
  )

#+(or mcl Lispworks)
(defun make-system (new-directory)
  (let ((*default-pathname-defaults*
         (make-pathname :name (concatenate 'string new-directory "/")
                        :defaults
                        #+Lispworks system::*current-working-pathname*
                        #-Lispworks *default-pathname-defaults*))
        (old-directory (current-directory)))
    (change-directory new-directory)
    (unwind-protect (load "system.lisp")
      (change-directory old-directory))))

#-(or mcl Lispworks)
(defun make-system (new-directory)
  (let ((old-directory (current-directory))
        (*default-pathname-defaults* *default-pathname-defaults*))
    (change-directory new-directory)
    (unwind-protect (load "system.lisp")
      (change-directory old-directory))))

#+sbcl
(setq sb-fasl:*fasl-file-type* "sfsl")  ; Default is "fasl" which conflicts with allegro

(defvar *fasl-type*
  #+allegro "fasl"
  #+mcl     "dfsl"
  #+(and cmu (not ppc)) "x86f"
  #+(and cmu ppc)       "ppcf"
  #+sbcl    sb-fasl:*fasl-file-type*
  #+gcl     "o"
  #+clisp   "fas")

#+cmu
(setq lisp::*load-lp-object-types* (remove "FASL" lisp::*load-lp-object-types* :test 'string=)
      lisp::*load-object-types* (remove "fasl" lisp::*load-object-types* :test 'string=))

;; (unless (fboundp 'compile-file-if-needed)
  ;; Conditional because of an apparent Allegro bug in generate-application
  ;; where excl::compile-file-if-needed compiles even if not needed
  (defun compile-file-if-needed (file)
    (when (null (pathname-type file))
      (setq file (make-pathname :defaults file :type "lisp")))
    #+allegro (excl::compile-file-if-needed file)
    #+Lispworks (hcl:compile-file-if-needed file)
    #+(or cmu mcl sbcl gcl clisp)
    (unless (>
             ;; Make sure the fasl file is strictly newer to avoid the following
             ;; race condition that can occur in automated scripts, etc.
             ;;
             ;;  old  X.lisp   [write time = N]
             ;;  old  X.fasl   [write time = N+1]
             ;;  new  X.lisp   [write time = N+1]
             ;;
             ;; If we were to use >= as the test here, we would decide the
             ;; old X.fasl was current for thw new X.lisp
             ;;
             (let ((fasl-file (probe-file (make-pathname :defaults file
                                                         :type *fasl-type*))))
               (if fasl-file
                   (or (file-write-date fasl-file) 0)
                 0))
             (or (file-write-date file) 0))
      (compile-file file)))
;; )

(defun compile-and-load-lisp-file (file)
  (let ((filep (make-pathname :defaults (from-cygwin-name file) :type "lisp")))
    ;;(format t "C: ~a~%" filep)
    ;;(compile-file filep)
    ;;(format t "L: ~a~%" (make-pathname :defaults filep :type nil))
    (if (probe-file filep)
        (progn (compile-file-if-needed filep)
               ;; scripts depend upon the following returning true iff successful
               (load (make-pathname :defaults filep :type *fasl-type*)))
      (warn "File ~a does not exist" file))))

(defun load-lisp-file (file &rest ignore)
  (declare (ignore ignore))
  (load (make-pathname :defaults file :type "lisp")))

#+mcl                                   ; Patch openmcl bug
(defmacro cl-user::without-package-locks (&rest body)
  `(let ((ccl::*warn-if-redefine-kernel* nil))
    ,@body))

#+mcl                                   ; Patch openmcl bug
(cl-user::without-package-locks
(defun ccl::overwrite-dialog (filename prompt)
  (if ccl::*overwrite-dialog-hook*
    (funcall ccl::*overwrite-dialog-hook* filename prompt)
    filename))
)

(defparameter temporaryDirectory
  (ensure-final-slash
   (substitute #\/ #\\
               #+(or win32 winnt mswindows)
               (if cygwin? "/tmp/"
                   (or (getenv "TEMP") (getenv "TMP")
                       #+allegro
                       (namestring (SYSTEM:temporary-directory))))
               #+(and (not unix) Lispworks) (namestring System::*temp-directory*)
               #+(and (not win32) unix) "/tmp/"
               )))

;; The same function with the same name, but in a different package is
;; defined in Specware4/Library/Legacy/Utilities/Handwritten/Lisp/System.lisp
(defun temporaryDirectory-0 ()
  (ensure-final-slash
   (substitute #\/ #\\
               (if (and System-Spec::msWindowsSystem? (not cygwin?))
                   (or (getenv "TEMP") (getenv "TMP")
                       #+allegro
                       (namestring (SYSTEM:temporary-directory)))
                   "/tmp/"))))

(defun setTemporaryDirectory ()
  (setq temporaryDirectory (temporaryDirectory-0)))

(defun run-program (command-str)
  #+(and allegro unix)
  (excl:run-shell-command command-str)
  #+(and allegro mswindows)
  (let ((str (excl:run-shell-command (format nil "c:\\cygwin\\bin\\bash.exe -c ~S"
                                             (format nil "command -p ~A" command-str))
                                     :wait nil :output :stream
                                     :show-window :hide)))
    (do ((ch (read-char str nil nil) (read-char str nil nil)))
        ((null ch) (close str) (sys:os-wait)) (write-char ch)))
  #+cmu  (ext:run-program command-str nil :output t)
  #+mcl  (ccl:run-program command-str nil :output t)
  #+sbcl (sb-ext:run-program command-str (list "-p" command-str) :output t :search t)
  #+gcl  (lisp:system command-str)
  #+clisp (ext:run-program command-str )
  #-(or cmu mcl sbcl allegro gcl) (format nil "Not yet implemented"))

(defun copy-file (source target)
  ;; This just copies the file verbatim, as you'd expect...
  ;; similar to concatenate-files below, but with special cases
  #+allegro (sys:copy-file source target :preserve-time t)
  #+mcl     (ccl:copy-file source target :if-exists :supersede)
  #+cmu     (ext:run-program    "cp"      (list (namestring source) (namestring target)))
  #+sbcl    (sb-ext:run-program (if System-Spec::msWindowsSystem?
                                    "c:\\cygwin\\bin\\cp.exe"  "/bin/cp")
                                (list (namestring source) (namestring target)))
  #-(or allegro cmu sbcl mcl)
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

(defun file-to-string (file)
  ;; Note: ead-char might complain for chars with codes above #xC0
  ;; So use unsigned-byte to avoid problems reading x-symbol chars.
  ;; Alternatively, add error handler for smooth continuation.
  (with-open-file (istream file
                           :direction    :input
                           :element-type 'unsigned-byte)
    (with-output-to-string (ostream)
      (loop
        (let ((byte (read-byte istream nil :eof)))
          ;; read as a byte and do sanity check before trying to put it into a stream
          ;; some lisps will get upset at non-ascii characters...
          (cond
           ((eq byte :eof)  (return))
           ((> byte #x8F)   ) ; ignore non-ascii (chars above 127)
           ((= byte 12)     ) ; ignore #\Page    TODO: why this particular control char??
           (t
            (write-char (code-char byte) ostream))))))))

(defun first-line-of-file (file)
  (with-open-file (istream file :direction :input)
    (read-line istream)))

(defun sw-directory (pathname &optional #+mcl recursive?)
  (directory #-(or mcl sbcl) pathname
             #+(or mcl sbcl)
             (merge-pathnames (make-pathname :name :wild :type :wild) pathname)
             #-sbcl :allow-other-keys         #-sbcl    t  ; permits implementation-specific keys to be ignored by other implementations
             #+mcl  :directories              #+mcl     t  ; specific to mcl
             #+mcl  :all                      #+mcl     recursive?    ; specific to mcl
             #+allegro :directories-are-files #+allegro nil  ; specific to allegro -- we never want this option, but it defaults to T (!)
             ))

(defun directory? (pathname)
  #+Allegro (excl::file-directory-p pathname)
  #-Allegro (and (null (pathname-name pathname))
                 (null (pathname-type pathname))
                 (not (null (sw-directory pathname)))))

(defun extend-directory (dir ext-dir)
  (make-pathname :directory
                 (concatenate 'list
                              (pathname-directory dir)
                              (last (pathname-directory ext-dir)))))

(defun make-directory (dir)
  (let ((dir (if (pathnamep dir)
                 (namestring dir)
               dir)))
    #+allegro (sys::make-directory dir)
    #+cmu     (unix:unix-mkdir dir #o755)
    #+mcl     (ccl:run-program "mkdir" (list dir))
    #+sbcl    (sb-unix:unix-mkdir dir #o755)
    #+gcl     (lisp:system (format nil "mkdir ~a" dir))))

(defun copy-directory (source target &optional (recursive? t))
  ;; #+allegro (sys::copy-directory source target) ;  buggy when recursive? is nil
  ;; #-allegro
  ;; this is the desired behavior
  (let* ((source-dirpath (if (stringp source)
                             (sw-parse-namestring (ensure-final-slash source))
                           source))
         ;(source-dirpath (merge-pathnames (make-pathname :name :wild) source-dirpath))
         (target-dirpath (if (stringp target)
                             (sw-parse-namestring (ensure-final-slash target))
                           target)))
    #+mcl
    (when recursive?
      (return
        (ccl:run-program "cp"(list "-R"
                                   (namestring source-dirpath)
                                   (namestring target-dirpath)))))
    ;; For mcl, only if not recursive.  For all others, always.
    (unless (probe-file target-dirpath)
      (make-directory target-dirpath))
    (loop for dir-item in (sw-directory source-dirpath)
          do (if (and recursive? (directory? dir-item))
                 (copy-directory dir-item (extend-directory target-dirpath dir-item) t)
                 (copy-file dir-item (merge-pathnames target-dirpath dir-item))))))

(defun Specware::delete-directory (dir &optional (contents? t))
  #+allegro
  (if contents?
      (excl:delete-directory-and-files dir)
    (excl:delete-directory dir))
  #-allegro
  (let* ((dirpath (if (stringp dir) (sw-parse-namestring dir) dir))
         (dirstr (if (stringp dir) dir (namestring dirpath))))
    (if contents?
        (progn
          #+mcl  (ccl:run-program    "rm"      (list "-R" dirstr))
          #+sbcl (sb-ext:run-program (if System-Spec::msWindowsSystem?
                                         "c:/cygwin/bin/rm.exe" "/bin/rm")
                                     (list "-R" dirstr))
          #-(or mcl sbcl)
          (loop for dir-item in (sw-directory dirpath)
            do (if (directory? dir-item)
                   (Specware::delete-directory dir-item contents?)
                 (delete-file dir-item))))
      (progn
        #+mcl  (ccl:run-program    "rmdir"      (list dirstr))
        #+sbcl (sb-ext:run-program (if System-Spec::msWindowsSystem?
                                       "c:/cygwin/bin/rmdir.exe" "/bin/rmdir")
                                   (list dirstr))
        #+cmu  (unix:unix-rmdir dirstr)
        #+gcl  (lisp:system (format nil "rmdir ~a" dirstr))
        #-(or cmu gcl mcl sbcl) nil     ; No general way
        ))))

(defun parent-directory (pathname)
  (let ((dir (pathname-directory pathname)))
    (if (< (length dir) 2)
        pathname
      (make-pathname :directory (butlast dir)))))


(unless (fboundp 'cl-user::without-redefinition-warnings)
  (defmacro cl-user::without-redefinition-warnings (&body body)
    `(let (#+Allegro (cl-user::*redefinition-warnings* nil))
       #+Allegro (declare (special cl-user::*redefinition-warnings*))
       ,@body)))

(unless (fboundp 'Specware::define-compiler-macro)
  #+gcl
  (defmacro Specware::define-compiler-macro (name vl &rest body)
    `(si::define-compiler-macro ,name ,vl,@ body)))

(unless (fboundp 'Specware::without-package-locks)
  (defmacro Specware::without-package-locks (&rest args)
    #+cmu19 `(ext:without-package-locks ,@args)
    #+sbcl `(sb-ext:without-package-locks ,@args)
    #+allegro `(excl:without-package-locks ,@args)
    #-(or cmu19 sbcl allegro) `(progn ,@args)))


(defun wait (msg pred &optional (sleep-time 1))

  #+(or allegro cmu) (declare (ignore sleep-time))
  #+(or allegro cmu) (mp:process-wait msg pred)

  #-(or allegro cmu) (declare (ignore msg))
  #-(or allegro cmu) (loop until (funcall pred)
                       do (sleep sleep-time))

  )

;; (defpackage :swank)

(defun exit-when-done ()
  ;; use find-symbol hack to avoid sbcl complaints about eval-in-emacs
  ;; not being defined at compile-time
  ;; (also avoids need to have swank package available yet)
  (let ((e-in-e (find-symbol (fixCase "eval-in-emacs")
                             :swank)))
    (wait "Commands in progress"
          #'(lambda () (<= (funcall e-in-e
                                    '(length (slime-rex-continuations)))
                           1)))
    (format t "Exiting ~a~%" (funcall e-in-e '(length (slime-rex-continuations))))
    (funcall e-in-e '(slime-quit-specware))))

(defmacro with-unique-names ((&rest bindings) &body body)
  "Evaluate BODY with BINDINGS bound to fresh unique symbols.

Syntax: WITH-UNIQUE-NAMES ( [ var | (var x) ]* ) declaration* form*

Executes a series of forms with each VAR bound to a fresh,
uninterned symbol. The uninterned symbol is as if returned by a call
to GENSYM with the string denoted by X - or, if X is not supplied, the
string denoted by VAR - as argument.

The variable bindings created are lexical unless special declarations
are specified. The scopes of the name bindings and declarations do not
include the Xs.

The forms are evaluated in order, and the values of all but the last
are discarded \(that is, the body is an implicit PROGN)."
  ;; reference implementation posted to comp.lang.lisp as
  ;; <cy3bshuf30f.fsf@ljosa.com> by Vebjorn Ljosa - see also
  ;; <http://www.cliki.net/Common%20Lisp%20Utilities>
  `(let ,(mapcar (lambda (binding)
                   (check-type binding (or cons symbol))
                   (destructuring-bind (var &optional (prefix (symbol-name var)))
                       (if (consp binding) binding (list binding))
                     (check-type var symbol)
                     `(,var (gensym ,(concatenate 'string prefix "-")))))
                 bindings)
     ,@body))