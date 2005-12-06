(defpackage "INTEGER-SPEC")
(defpackage :Integer_)
(IN-PACKAGE "INTEGER-SPEC")


;;; For each binary op in the spec Integer without a def, there are two Lisp
;;; functions. One takes two arguments, the other takes one argument that is a
;;; pair. In MetaSlang, there is no such distinction: all ops are really
;;; unary, from a domain sort D to a codomain sort C, where D can be a
;;; product, e.g. A * B, in which case the op can be "viewed" as being
;;; binary. These double variants match Specware's Lisp code generator, which
;;; generates two variants for ops whose domain is a product: one that takes
;;; one argument for each factor, and the other that takes just one argument
;;; that is a tuple. The naming convention is that the variant that takes just
;;; one argument has the name directly derived from the op name from which it
;;; is generated, while the variant that takes n arguments (n > 1) has that
;;; name with a "-n" suffix.

;;; The define-compiler-macro definitions are necessary to get efficient
;;; arithmetic.


;;; mechanism for allowing the user to declare global restrictions on integers:
(eval-when (compile load)
  (defvar specware::*integer-impl* 'integer))

(defmacro the-int (x)
  `(the ,specware::*integer-impl* ,x))

(defun -- (x) ; TODO: deprecate 
  (declare (integer x))
  (the-int (- 0 x)))

(defun Integer_::|!-| (x)
  (declare (integer x))
  (the-int (- 0 x)))

(defun ~ (x) ; TODO: deprecate
  (declare (integer x))
  (the-int (- 0 x)))

(defun +-2 (x y)
  (declare (integer x y))
  (the-int (+ x y)))

(define-compiler-macro +-2 (x y)
  `(the-int (+ (the-int ,x) (the-int ,y))))

(defun |!+| (xy)
  (declare (cons xy))
  (the-int (+ (the-int (car xy)) (the-int (cdr xy)))))

(defun --2 (x y)
  (declare (integer x y))
  (the-int (- x y)))

(define-compiler-macro --2 (x y)
  `(the-int (- (the-int ,x) (the-int ,y))))

(defun |!-| (xy)
  (declare (cons xy))
  (the-int (- (the-int (car xy)) (the-int (cdr xy)))))

(defun *-2 (x y)
  (declare (integer x y))
  (the-int (* x y)))

(define-compiler-macro *-2 (x y)
  `(the-int (* (the-int ,x) (the-int ,y))))

(defun |!*| (xy)
  (declare (cons xy))
  (the-int (* (the-int (car xy)) (the-int (cdr xy)))))

(defun div-2 (x y)
  (declare (integer x y))
  (the-int (cl::truncate x y)))

(define-compiler-macro div-2 (x y)
  `(the-int (cl:truncate (the-int ,x) (the-int ,y))))

(defun div (xy)
  (declare (cons xy))
  (the-int (cl:truncate (the-int (car xy)) (the-int (cdr xy)))))

(defun rem-2 (x y)
  (declare (integer x y))
  (the-int (cl:rem x y)))

(define-compiler-macro rem-2 (x y)
  `(the-int (cl:rem (the-int ,x) (the-int ,y))))

(defun |!rem| (xy)
  (declare (cons xy))
  (the-int (cl::rem (the-int (car xy)) (the-int (cdr xy)))))

(defun <-2 (x y)
  (declare (integer x y))
  (the boolean (< x y)))

(define-compiler-macro <-2 (x y)
  `(< (the-int ,x) (the-int ,y)))

(defun |!<| (xy)
  (declare (cons xy))
  (< (the-int (car xy)) (the-int (cdr xy))))

(defun <=-2 (x y)
  (declare (integer x y))
  (the boolean (<= x y)))

(define-compiler-macro <=-2 (x y)
  `(<= (the-int ,x) (the-int ,y)))

(defun |!<=| (xy)
  (declare (cons xy))
  (<= (the-int (car xy)) (the-int (cdr xy))))

(define-compiler-macro >-2 (x y)
  `(> (the-int ,x) (the-int ,y)))

(define-compiler-macro >=-2 (x y)
  `(>= (the-int ,x) (the-int ,y)))

(define-compiler-macro max-2 (x y)
  `(max (the-int ,x) (the-int ,y)))

(define-compiler-macro min-2 (x y)
  `(min (the-int ,x) (the-int ,y)))

(define-compiler-macro |!abs| (x)
  `(abs (the-int ,x)))

(defun gcd-2 (x y)
  (declare (integer x y))
  (the-int (cl:gcd x y)))

(define-compiler-macro gcd-2 (x y)
  `(cl:gcd (the-int ,x) (the-int ,y)))

(defun |!gcd| (xy)
  (declare (cons xy))
  (cl:gcd (the-int (car xy)) (the-int (cdr xy))))

(defun lcm-2 (x y)
  (declare (integer x y))
  (the-int (cl:lcm x y)))

(define-compiler-macro lcm-2 (x y)
  `(cl:lcm (the-int ,x) (the-int ,y)))

(defun |!lcm| (xy)
  (declare (cons xy))
  (cl:lcm (the-int (car xy)) (the-int (cdr xy))))
(defpackage "NAT-SPEC")
(IN-PACKAGE "NAT-SPEC")


;;; For each binary op in the spec Nat without a def, there are two Lisp
;;; functions. One takes two arguments, the other takes one argument that is a
;;; pair. In MetaSlang, there is no such distinction: all ops are really
;;; unary, from a domain sort D to a codomain sort C, where D can be a
;;; product, e.g. A * B, in which case the op can be "viewed" as being
;;; binary. These double variants match Specware's Lisp code generator, which
;;; generates two variants for ops whose domain is a product: one that takes
;;; one argument for each factor, and the other that takes just one argument
;;; that is a tuple. The naming convention is that the variant that takes just
;;; one argument has the name directly derived from the op name from which it
;;; is generated, while the variant that takes n arguments (n > 1) has that
;;; name with a "-n" suffix.

;;; The define-compiler-macro definitions are necessary to get efficient
;;; arithmetic.


(defconstant zero 0)

(defun succ (x) (+ 1 x))

(defun plus (xy) (+ (car xy) (cdr xy)))

(defun minus (xy) (- (car xy) (cdr xy)))

(defun lteq (xy) (<= (car xy) (cdr xy)))

(defun plus-2 (x y) (+ x y))

(defun minus-2 (x y) (- x y))

(defun lteq-2 (x y) (<= x y))
(DEFPACKAGE "CHAR-SPEC")
(IN-PACKAGE "CHAR-SPEC")


;;; While in Metaslang characters are exactly those occupying decimal
;;; positions 0 to 255 in the ISO-8859-1 code table, the Common Lisp
;;; standard does not commit to that. So, Specware-generated code and the
;;; hand-written code in this file may not work as expected in Common Lisp
;;; implementation whose characters do not coincide with, or at least
;;; include, the Metaslang characters.


(defun ord (ch)
  (char-code ch))

(defun chr (n)
  (code-char n))

;;; lower-case-p, upper-case-p etc. only guaranteed for Standard ASCII (First 96 characters)
(defun isUpperCase (char)
  (declare (character char))
  (let ((ch-num (char-code char)))
    (or (< 64 ch-num 91)		; A-Z
	(< 191 ch-num 215)		; À-Ö
	(< 215 ch-num 224)		; Ø-ß
	)))

(defun isLowerCase (char)
  (declare (character char))
  (let ((ch-num (char-code char)))
    (or (< 96 ch-num 123)		; a-z
	(< 223 ch-num 247)		; à-à
	(< 247 ch-num 256)		; ø-ÿ
	)))

(defun isAlpha (ch)
  (or (isUpperCase ch)
      (isLowerCase ch)))

(defun isNum (ch)
  (and (<= 48 (char-code ch)) (<= (char-code ch) 57)))

(defun isAlphaNum (ch)
  (or (isAlpha ch)
      (isNum ch)))

(defun isAscii (char)
  (declare (character char))
  (< -1
     (char-code char)
     256))

;;; Relationship between ÿ and ß is anomalous
(defun toUpperCase (char)
  (declare (character char))
  (if (isLowerCase char)
      (code-char (- (char-code char) 32))
    char))

(defun toLowerCase (char)
  (declare (character char))
  (if (isUpperCase char)
      (code-char (+ (char-code char) 32))
    char))
(defpackage "SYSTEM-SPEC")
(defpackage "STRING-SPEC")
(IN-PACKAGE "STRING-SPEC")


;;; For each curried binary op in the spec String whose Lisp code is
;;; hand-written, there are two Lisp functions. One takes the first argument
;;; and returns a closure that takes the second argument, the other takes the
;;; two arguments in non-curried form. These double variants match Specware's
;;; Lisp code generator, which generates various variants for curried ops:
;;; each variant takes some of the curried arguments and returns a closure
;;; that takes the remaining arguments. For a curried binary op, the naming
;;; convention is that the variant that takes the first argument and return a
;;; closure has the name directly derived from the op, while the variant that
;;; takes the two arguments has that name with a "-1-1" suffix.

;;; For each (non-curried) binary op in the spec String whose Lisp code is
;;; hand-written, there are also two Lisp functions. See the comments in
;;; Integer.lisp for an explanation.


(defun explode (s) 
  ;; (reduce #'cons s :from-end t :initial-value nil)) ; ugh... uses generic sequence functions to treat string as list, then rebuilds list
  (coerce s 'list) ; let lisp do something smart
  )

(defun implode (s) 
  ;; (apply #'concatenate (cons 'string (mapcar #'string s))) ; brain damage -- hugely inefficient
  (coerce s 'string) ; let lisp do something smart
  )

(defun |!length| (x)
  (declare (type cl:simple-base-string x))
  (the cl:fixnum 
    (array-dimension x 0)))

(defun concat-2 (x y)
  (declare (type cl:simple-base-string x y))
  (the cl:simple-base-string 
    (concatenate 'string x y)))

;;; Putting (the cl:simple-base-string ,y) gives mcl exponential compiler behavior
(define-compiler-macro concat-2 (x y)
  `(concatenate 'string ,(if (stringp x) x `(the cl:simple-base-string ,x)) ,y))

(defun concat (xy)
  (declare (cons xy))
  (the cl:simple-base-string 
    (concatenate 'string 
                 (the cl:simple-base-string (car xy)) 
                 (the cl:simple-base-string (cdr xy)))))

(defun ++-2 (x y)
  (declare (type cl:simple-base-string x y))
  (the cl:simple-base-string 
    (concatenate 'string x y)))

;;; Putting (the cl:simple-base-string ,y) gives mcl exponential compiler behavior
(define-compiler-macro ++-2 (x y)
  `(concatenate 'string ,(if (stringp x) x `(the cl:simple-base-string ,x))
		,y))

(defun |!++| (xy)
  (declare (cons xy))
  (the cl:simple-base-string 
    (concatenate 'string 
                 (the cl:simple-base-string (car xy)) 
                 (the cl:simple-base-string (cdr xy)))))

(defun ^-2 (x y)
  (declare (type cl:simple-base-string x y))
  (the cl:simple-base-string 
    (concatenate 'string x y)))

;;; Putting (the cl:simple-base-string ,y) gives mcl exponential compiler behavior
(define-compiler-macro ^-2 (x y)
  `(concatenate 'string ,x ,(if (stringp y) y `(the cl:simple-base-string ,y))))

(defun ^ (xy)
  (declare (cons xy))
  (the cl:simple-base-string 
    (concatenate 'string 
                 (the cl:simple-base-string (car xy)) 
                 (the cl:simple-base-string (cdr xy)))))

(defun |!map| (f)
  (lambda (s)
    (map 'string f (the cl:simple-base-string s))))

(defun map-1-1 (f s)
  (map 'string f (the cl:simple-base-string s)))

(defun |!exists| (p)
  (lambda (s)
    (some p s)))

(defun exists-1-1 (p s)
  (some p s))

(defun all (p)
  (lambda (s)
    (every p s)))

(defun all-1-1 (p s)
  (every p s))

(defun sub-2 (s n)
  (declare (type cl:simple-base-string s) (type cl:fixnum n))
  (elt s n))

(defun sub (sn)
  (declare (cons sn))
  (elt (the cl:simple-base-string (car sn)) (the cl:fixnum (cdr sn))))

(defun substring-3 (s start end)
  (declare (type cl:simple-base-string s) (type cl:fixnum start end))
  (the cl:simple-base-string (subseq s start end)))

(define-compiler-macro substring-3 (s start end)
  `(subseq
     (the cl:simple-base-string ,s) (the cl:fixnum ,start) (the cl:fixnum ,end)))

(defun substring (sse)
  (the cl:simple-base-string (subseq (the cl:simple-base-string (svref sse 0))
                                     (the cl:fixnum (svref sse 1))
                                     (the cl:fixnum (svref sse 2)))))

(defun concatList (x)
  (the cl:simple-base-string 
    (apply #'concatenate 'string x)))

(defun translate (f)
  (lambda (str)
    (let* ((chars (explode str))
           (translated-char-strings 
            (mapcar #'(lambda (ch) 
                        (string (funcall f ch)))
                    chars)))
      (declare (type list translated-char-strings))
      (the cl:simple-base-string 
        (apply #'concatenate 'string translated-char-strings)))))

(defun translate-1-1 (f str)
  (let* ((chars (explode str))
         (translated-char-strings 
          (mapcar #'(lambda (ch) 
                      (string (funcall f ch)))
                  chars)))
    (declare (type list translated-char-strings))
    (the cl:simple-base-string 
      (apply #'concatenate 'string translated-char-strings))))

(defun lt-2 (s1 s2)
  (declare (type cl:simple-base-string s1 s2))
  (if (string< s1 s2) t nil))

(defun lt (s1s2)
  (if (string< (the cl:simple-base-string (car s1s2))
               (the cl:simple-base-string (cdr s1s2)))
   t nil))

(defun leq-2 (s1 s2)
  (declare (type cl:simple-base-string s1 s2))
  (if (string<= s1 s2) t nil))

(defun leq (s1s2)
  (if (string<= (the cl:simple-base-string (car s1s2))
                (the cl:simple-base-string (cdr s1s2)))
   t nil))

(defun <-2 (s1 s2)
  (declare (type cl:simple-base-string s1 s2))
  (if (string< s1 s2) t nil))

(define-compiler-macro <-2 (x y)
  `(string< (the cl:simple-base-string ,x) (the cl:simple-base-string ,y)))

(defun |!<| (s1s2)
  (if (string< (the cl:simple-base-string (car s1s2))
               (the cl:simple-base-string (cdr s1s2)))
   t nil))

(defun <=-2 (s1 s2)
  (declare (type cl:simple-base-string s1 s2))
  (if (string<= s1 s2) t nil))

(define-compiler-macro <=-2 (x y)
  `(string<= (the cl:simple-base-string ,x) (the cl:simple-base-string ,y)))

(defun |!<=| (s1s2)
  (if (string<= (the cl:simple-base-string (car s1s2))
                (the cl:simple-base-string (cdr s1s2)))
   t nil))

(define-compiler-macro >-2 (x y)
  `(let ((x ,x) (y ,y))
     (string< (the cl:simple-base-string y) (the cl:simple-base-string x))))

(define-compiler-macro >=-2 (x y)
  `(let ((x ,x) (y ,y))
     (string<= (the cl:simple-base-string y) (the cl:simple-base-string x))))

(defparameter newline
  (format nil "~c" #\newline))

(defun toScreen (x)
  (declare (type cl:simple-base-string x))
  (common-lisp::format t "~A" x))

(defun writeLine (x)
  (declare (type cl:simple-base-string x))
  (common-lisp::format t "~A" x)
  (common-lisp::format t "~%"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defpackage :BOOLEAN-SPEC)
(IN-PACKAGE :BOOLEAN-SPEC)


(defun toString (x)
  (if x "true" "false"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defpackage :INTEGER-SPEC)
(IN-PACKAGE :INTEGER-SPEC)


(defun toString (x)
  (declare (type integer x))
  (the string (princ-to-string x)))

(defun intToString (x)
  (declare (type integer x))
  (the string (princ-to-string x)))

(defun stringToInt (s)
  (declare (type string s))
  (multiple-value-bind (n new-index)
      (parse-integer s :junk-allowed t)
    (cond ((null n)
	   (System-Spec::fail 
	    (format nil "stringToInt could not parse ~S" 
		    s)))
	  ((< new-index (length s))
	   (System-Spec::fail
	    (format nil "stringToInt found ~D, but also extra junk in ~S" 
		    n s)))
	  ((let ((c0 (char s 0))) 
	     (or (digit-char-p c0) 
		 (eq c0 #\-)))
	   (the integer n))
	  (t
	   (System-Spec::fail
	    (format nil "stringToInt: leading ~:C in ~S is not allowed"
		    (char s 0) s))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defpackage :NAT-SPEC)
(IN-PACKAGE :NAT-SPEC)


(defun toString (x)
  (declare (type integer x))
  (the string (princ-to-string x)))

(defun natToString (x)
  (declare (type integer x))
  (the string (princ-to-string x)))

(defun stringToNat (s)
  (declare (type string s))
  ;; lisp automatically returns the first value as a normal value
  (multiple-value-bind (n new-index)
      (parse-integer s :junk-allowed t)
    (cond ((null n)
	   (System-Spec::fail
	    (format nil "stringToNat could not parse ~S" 
		    s)))
	  ((< new-index (length s))
	   (System-Spec::fail
	    (format nil "stringToNat found ~D, but also extra junk in ~S" 
		    n s)))
	  ((digit-char-p (char s 0))
	   (the integer n))
	  (t
	   (System-Spec::fail
	    (format nil "stringToNat: leading ~:C in ~S is not allowed"
		    (char s 0) s))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(DEFPACKAGE :CHAR-SPEC)
(IN-PACKAGE :CHAR-SPEC)


(defun toString (x)
  (string x))
(defpackage "SYSTEM-SPEC")
(in-package "SYSTEM-SPEC")

(defvar System-spec::specwareDebug? nil)

(defvar System-spec::proverUseBase? t)

 ;;; op fail     : fa(a) String -> a
(defun fail (s) (break "~a" s))

;;; op debug     : fa(a) String -> a
(defun |!debug| (s) (when specwareDebug? (break "~a" s)))

;;; op anyToString : fa(a) a -> String
(defun anyToString (s) (let ((*print-pretty* nil)) (format nil "~S" s)))

;;; op print    : fa(a) a -> a
(defun |!print| (x) (print x) (force-output))

;;; op warn     : fa(a) String -> a
(defun |!warn| (s) (warn "~a" s))

;;; op time     : fa(a) a -> a
(defmacro |!time| (x) (time x))

;;; #-Lispworks
;;; (defun getenv (x) (specware::getenv x))

;; The Lisp getenv returns nil if the name is not in the environment. 
;; Otherwise it returns a string. We want to be able to distinguish
;; the outcomes in MetaSlang

;;; op getEnv : String -> Option String
(defun getEnv (name)
  (let ((val (specware::getenv name)))
    (if (or (eq val nil) (equal val ""))    ; I think it returns "" if not set
	(cons :|None| nil)
      (cons :|Some| val))))

(defvar msWindowsSystem? #+mswindows t #-mswindows nil)

;; The same function with the same name, but in a different package is
;; defined in Specware4/Applications/Handwritten/Lisp/load-utilities.lisp
(defun temporaryDirectory-0 ()
  (ensure-final-slash
   (namestring #+(or win32 winnt mswindows)
	       (or (cdr (getenv "TEMP")) (cdr (getenv "TMP"))
		   #+allegro
		   (SYSTEM:temporary-directory))
	       #+(and (not unix) Lispworks) SYSTEM::*TEMP-DIRECTORY*
	       #+unix "/tmp/"
	       )))

;; The same function with the same name, but in a different package is
;; defined in Specware4/Applications/Handwritten/Lisp/load-utilities.lisp
(defun ensure-final-slash (dirname)
  (if (member (elt dirname (- (length dirname) 1))
	      '(#\/ #\\))
      dirname
    (concatenate 'string dirname "/")))

;;;  op temporaryDirectory : String
(defparameter temporaryDirectory
    (substitute #\/ #\\ (temporaryDirectory-0)))

;;; op withRestartHandler : fa (a) String * (() -> ()) * (() -> a) -> a
(defun withRestartHandler-3 (restart-msg restart-action body-action)
  (loop
    (let ((results (multiple-value-list 
		    (with-simple-restart (abort restart-msg) 
		      (funcall body-action (vector))))))
      (if (equal results '(nil t))
	  (funcall restart-action (vector))
	(return (values-list results))))))

;;; op garbageCollect : Boolean -> ()
(defun garbageCollect (full?)
  #+allegro (sys::gc full?)
  #+cmu (ext:gc :full full?))

;; hackMemory essentially calls (room nil) in an attempt to appease 
;; Allegro CL into not causing mysterious storage conditions during 
;; the bootstrap. (sigh)  
;; Calling (gc nil) and (gc t) both failed to have the desired effect.

;;; op hackMemory     : ()      -> ()
(defun hackMemory-0 ()
  ;; (sys::room nil)
  )

;;; op trueFilename : String -> String 
(defun trueFilename (filename)
  (let* ((given-pathname (pathname filename))
	 (resolved-pathname
	  #+Allegro
	  (excl::pathname-resolve-symbolic-links given-pathname)
	  #-Allegro
	  (truename given-pathname)
	  ))
    (namestring resolved-pathname)))

;;; op trueFilePath : List String * Boolean -> List String
(defun trueFilePath-2 (path relative?)
  (let* ((rpath (reverse path))
	 (name (first rpath))
	 (dir  (cons (if relative? :relative :absolute)
		     (reverse (rest rpath))))
	 (given-pathname (make-pathname :directory dir :name name))
	 (resolved-pathname
	  #+Allegro
	  (excl::pathname-resolve-symbolic-links given-pathname)
	  #-Allegro
	  (truename given-pathname)
	  ))
    (append (rest (pathname-directory resolved-pathname))
	    (list (pathname-name resolved-pathname)))))
(defpackage "PARSER4")
(defpackage "UNICODE")
(defpackage "IO-SPEC")
(in-package "IO-SPEC")

;;;  sort Filename = String
;;;  sort Time     = Nat          % Not a fixnum
;;;  sort Byte     = {x : Nat | 0 <= x &  x < 256} 
;;;
;;;  op getCurrentDirectory   : () -> Filename
;;;  op fileExistsAndReadable : Filename -> Boolean
;;;  op fileWriteTime         : Filename -> Time
;;;
;;;  op fileWritable          : Filename -> Boolean
;;;  op readBytesFromFile     : Filename -> List Byte
;;;  op writeBytesToFile      : List Byte * Filename -> ()
;;;


;;; This returns true if, as the name suggests, the given file
;;; exists and is readable. Otherwise, it returns false.
(defun fileExistsAndReadable (x)
  (handler-case
      (progn (close (open x :direction :input)) t)
    (file-error (condition) 
      (declare (ignore condition))
      nil)
    #+gcl
    (error (condition) 
      (declare (ignore condition))
      nil)))

(defvar nullFileWriteTime 9999999999999)   ; eons from now: "Thu May 21 10:46:39 PST 318787"

(defun fileWriteTime (file)
  ;; bignum (i.e., not a lisp fixnum, not a C int)
  ;; Bigger than 536870911 = 2^29 - 1 = most-positive-fixnum
  ;; Bigger than 2147483648 = 2^31 = biggest 32-bit int 
  (or #+allegro(excl::filesys-write-date file)    ; faster?
      ;;
      ;; The allegro hack above returns nil for names such as "~/foo.sw"
      ;; The following should succeed where the above hack returns nil, 
      ;; but maybe this is all that the standard file-write-date does:
      ;;  (excl::filesys-write-date (namestring (truename  file))) 
      ;;
      ;; Call this when hack fails (or we're not running Allego CL) ...
      (file-write-date file)
      ;; If file doesn't exist then return a future time! 
      ;; 3288592472 = "Thu Mar 18 01:54:32 PST 2004"
      nullFileWriteTime))

(defun currentTime-0 ()
  ;; bignum (i.e., not a lisp fixnum, not a C int)
  ;; Bigger than 536870911 = 2^29 - 1 = most-positive-fixnum
  ;; Bigger than 2147483648 = 2^31 = biggest 32-bit int 
  (get-universal-time))

(defun getCurrentDirectory-0 ()
  (convert-windows-filename (namestring (specware::current-directory))))

(defun convert-windows-filename (filestr)
  (declare (simple-string filestr))
  (let ((strip-c-colon-nm
	 (if (string-equal "c:" (subseq filestr 0 2))  ; Ignore case of c in =
	     (subseq filestr 2 (length filestr))
	   filestr)))
    (substitute #\/ #\\ strip-c-colon-nm)))

;;;  (defun fileExists (x)
;;;    (probe-file x))
;;;  
;;;  (defun openFile (name mode)
;;;    (handler-case
;;;      (cons :|Ok| (open name))
;;;  ;;    (ecase mode
;;;  ;;      (:|Read| )
;;;  ;;      (:|Write| )
;;;  ;;      (:|Append| )
;;;  ;;      (:|ReadWrite| )
;;;  ;;    ) 
;;;    (file-error (condition)
;;;      (let* ((errno
;;;               (if (null (excl::file-error-errno condition))
;;;                  (list :|None|)
;;;                  (cons :|Some| (excl::file-error-errno condition)))))
;;;      (cons :|FileError|
;;;         (vector errno
;;;         (format nil "~A" (file-error-pathname condition))
;;;         (format nil "~A" condition)))))))

(defun readStringFromFile (filename)
  #+allegro(excl::file-contents filename)
  #-allegro
  (let ((eof (cons nil nil)))
    (if (probe-file filename)
	(with-open-file (s filename)
	  (with-output-to-string (str)
	    (do ((char (read-char s nil eof) 
		       (read-char s nil eof)))
		((eq char eof) str)
	      (write-char char str))))
      (error "Can't find file ~a" filename))))

(defun readBytesFromFile (filename)
  (let ((eof (cons nil nil))
	(chars nil))
    (if (probe-file filename)
	(with-open-file (s filename :element-type 'unsigned-byte)
	  (do ((char (read-byte s nil eof) 
		     (read-byte s nil eof)))
	      ((eq char eof)
	       (cons :|Some| (reverse chars)))
	    (push char chars)))
      '(:|None|))))

(defun writeBytesToFile-2 (bytes filename)
  (ensure-directories-exist filename)
  (with-open-file (s filename :element-type 'unsigned-byte
		   :direction :output
		   :if-exists :supersede)
    (dolist (byte bytes)
      (write-byte byte s))))

;;; From UnicodeSig.sw :
;;;
;;;  sort Encoding = UChars -> Bytes   % UTF-8, UTF-16, JIS, etc.
;;;  sort Decoding = Bytes  -> UChars  % UTF-8, UTF-16, JIS, etc.
;;;
;;;  op read_unicode_chars_from_file : Filename * Encoding -> Option UChars
;;;  op write_unicode_chars_to_file  : UChars * Filename * Encoding -> ()

(defun unicode::read_unicode_chars_from_file-2 (filename decoding)
  (let ((bytes (readBytesFromFile filename)))
    (case (car bytes)
      (:|None| '(:|None|))
      (:|Some| (cons :|Some|
		     (let ((uchars (funcall decoding (cdr bytes))))
		       uchars))))))

(defun unicode::write_unicode_chars_to_file-3 (uchars filename encoding)
  (let ((bytes (funcall encoding uchars)))
    (writeBytesToFile-2 bytes filename)))

;; Used by prover interface:
;; Hopefully not Allegro specific.
(defun parser4::read_list_of_s_expressions_from_string (string)
  (let ((done? nil)
	(whitespaces '(#\space #\tab #\newline)))
    (let* ((trimmed-string (string-trim whitespaces string))
	   (index 0)
	   (result 
	    (catch 'problem
	      (prog1
		  (handler-bind ((error #'(lambda (signal) 
					    (throw 'problem (list signal index)))))
		    (let ((sexp nil)
			  (s-expressions ())
			  (n (length trimmed-string)))
		      (loop
			(multiple-value-setq (sexp index)
			  ;; bug in Allegro?  
			  ;; Setting eof-error-p to nil won't
			  ;; suppress eof error unless there is no 
			  ;; text at all to parse.
			  ;; At any rate, other kinds of errors are
			  ;; also possible.
			  (let ((*package* (find-package 'snark)))
			    (read-from-string trimmed-string nil nil 
					      :start               index 
					      :preserve-whitespace t)))
			(push sexp s-expressions)
			(when (>= index n)
			  (return (reverse s-expressions))))))
		;; if there were no problems, done? will become true,
		;; but we will return the value from the handler-bind 
		;; above from the prog1
		(setq done? t)))))
      (if done?
	  (cons :|OptionString| result)
	;; cause parser error?
	(let ((signal (first result))
	      (index  (second result)))
	  (let ((error-msg 
		 (format nil "~A at position ~D" 
			 (if (eq (type-of signal) 'common-lisp::end-of-file)
			     "Premature EOF for expression starting"
			   signal)
			 index)))
	    (cons :|Error| (cons error-msg string))))))))

;; translate invalid file name characters to valid ones
(defun convertToFileName(str)
  (let* ((chars (STRING-SPEC::explode str))
	 (translated-char-strings 
	  (mapcar #'(lambda (ch) 
		      (case ch
			(#\? "_p")
			((#\\ #\/ #\: #\* #\" #\< #\> #\|)
			 (format nil "_x~a" (char-code ch)))
			(t (string ch))))
		  chars)))
    (declare (type list translated-char-strings))
    (the cl:simple-base-string 
      (apply #'concatenate 'string translated-char-strings))))

(defpackage :STATE)
(IN-PACKAGE :STATE)

(defun ref (x) 
  (cons :|ref| x))

(defun |:=-2| (x y)
  (rplacd x y))

(defun |!!| (x) (cdr x))
(defpackage :IO-SPEC) 
(in-package :IO-SPEC)

(defun withOpenFileForRead-2 (name p)
  (with-open-file (s name :direction :input :if-does-not-exist :error)
    (funcall p s)))

(defun withOpenFileForWrite-2 (name p)
  (with-open-file (s name :direction :output :if-exists :new-version)
    (funcall p s)))

(defun withOpenFileForAppend-2 (name p)
  (with-open-file (s name :direction :output :if-exists :append)
    (funcall p s)))

(defun withOutputToString (p)
  (with-output-to-string (s)
    (funcall p s)))

(defun deleteFile (name)
  (delete-file name))

(defun fileExists? (name)
  (not (null (probe-file name))))

;; op readLines : [A] String * (String * A -> A) * A -> A

;; Works like foldL, not foldR.  That is, first we fold in lines from
;; the beginning of the file, not the end.

(defun readLines-3 (name fn val)
    (withOpenFileForRead-2 name
      #'(lambda (s)
          (loop
	    (let ((line (read-line s nil nil)))
	      (if (null line) (return val)
		(setq val (funcall fn (cons line val)))))))))

(defun writeLines-2 (name fn) 
  (withOpenFileForWrite-2 
   name
   #'(lambda (s) 
       (loop
	(let ((line? (funcall fn ())))
	  (if (eq (car line?) :|None|)
	      (return ())
	    (let ((line (cdr line?)))
	      (write-line line s))))))))


;; op readLines : [A] String * (String * A -> A) * A -> A

;; Works like foldL, not foldR.  That is, first we fold in lines from
;; the beginning of the file, not the end.

(defparameter terminal  t)
(defparameter |!string| nil)

(defun format1-3 (s control data1)
  (if (equal control "~A")
      (princ data1 s)
    (format s control data1)))

(defun format2-4 (s control data1 data2)
  (declare (ignore data2))
  (format s control data1))

(defun format3-5 (s control data1 data2 data3)
  (format s control data1 data2 data3))

(defun formatTerminal1-2 (control data1) 
  (format terminal control data1))

(defun formatTerminal2-3 (control data1 data2) 
  (format terminal control data1 data2))

(defun formatTerminal3-4 (control data1 data2 data3) 
  (format terminal control data1 data2 data3))

(defun formatString1-2 (control data1) 
  (format |!string| control data1))

(defun formatString2-3 (control data1 data2) 
  (format |!string| control data1 data2))

(defun formatString3-4 (control data1 data2 data3) 
  (format |!string| control data1 data2 data3))

(defun |!read| (s)
  (let ((eof-value 'eof))
    (let ((a (read s nil eof-value)))
      (if (eq a eof-value)
	  (cons :|None| nil)
	(cons :|Some| a)))))

(defun write-2 (s a)
  (prin1 a s))

(defun fileOlder?-2 (f1 f2)
  ;#+allegro(excl::file-older-p f1 f2)
  (let ((d1 (or (file-write-date f1) 0))
	(d2 (or (file-write-date f2) 0)))
    (< d1 d2)))

(defun ensureDirectoriesExist (s)
  (ensure-directories-exist s :verbose t))

(defun writeNat (n)
  (format t "~A" n))

(defun writeChar (c)
  (format t "~A" c))

(defun writeString (s)
  (format t "~A" s))

(defun writeLineNat (n)
  (format t "~A~%" n))

(defun writeLineChar (c)
  (format t "~A~%" c))

(defun writeLineString (s)
  (format t "~A~%" s))

;; (defun FileNameInSpecwareHome (s)
  ;; (declare (special re::*specware-home-directory*))
  ;; (concatenate 'string re::*specware-home-directory* "/" s))

;;; Lisp functions to avoid creating grarbage for indentation strings when prettyprinting
(defpackage "PRETTYPRINT")

(defun make-blanks-array (n)
  (let ((a (make-array n)))
    (loop for i from 1 to n do (setf (svref a (- i 1))
				     (format nil "~v@t" i)))
    a))

(defvar *blanks-array-size* 60)

(defvar *blanks-array* (make-blanks-array *blanks-array-size*))

;; op defined in /Library/PrettyPrinter/BjornerEspinosa
(defun prettyprint::blanks (n)
  (if (= n 0) ""
    (if (<= n *blanks-array-size*) (svref *blanks-array* (- n 1))
      (format nil "~vT" n))))

(defpackage "EMACS")
(defun gotoFilePosition-3 (file line col)
  (emacs::goto-file-position file line col))

(defun emacsEval (str)
  (emacs::eval-in-emacs str))

(defun chooseMenu (strs)
  (emacs::open-multiple-choice-window strs))

;;; The following used by send-message-to-lisp
(defvar emacs::*procs* 0)

#-mcl
(defun makeProcess (sym)
  (let* 
      ((procNum emacs::*procs*)
       (procName (format nil "Specware process : ~S" procNum)) 
       (proc #+allegro
	     (mp:process-run-function procName 
				      #'tpl:start-interactive-top-level
				      excl::*initial-terminal-io*
				      #'my-eval
				      (list sym))
	     #+Lispworks
	     (mp:process-run-function procName nil
				      #'my-eval
				      (list sym)))
       )
    (declare (ignore proc))
    (setq emacs::*procs* (1+ procNum))
    procName))

(defun my-eval (x)
  (let ((*standard-input* *terminal-io*)
	(*standard-output* *terminal-io*))
    (eval x)))

#+(or allegro Lispworks)
(defun emacs::kill-process (procName)
  (mp::process-kill (mp::process-name-to-process procName)))(defpackage :LISP-SPEC)
(in-package :LISP-SPEC) 

(defun nil-0  () nil)
(defun |!nil|  (x) (declare (ignore x)) nil)
(defun cons-2 (x y) (cons x y))
(defun |!cons| (x) x)
(defun |!car|  (x) (car x))
(defun |!cdr|  (x) (cdr x))
(defun symbol-2  (pkg name) (intern name (find-package pkg)))
(defun |!symbol|  (x) (intern (car x) (find-package (cdr x))))
(defun |!string|   (s) s)
(defun lispstring (s) (string s))
;(defun toString (s) (format nil "~A" s))
(defun |!nat|   (n) n)
(defun |!char|  (c) c)
(defun bool    (b) b)
(defun |!list|  (l) l)
(defun |!null|  (l) (null l))
(defun ++-2 (l1 l2)
  (append l1 l2))
(defun |!++|    (x)
  (append (car x) (cdr x)))
(defun apply-2  (f x) (apply f x))
(defun |!apply|  (pr) (apply (car pr) (cdr pr)))
(defun |!eval|  (x) (eval x))
(defun |!quote| (l) (list 'quote l))
(defun |!print| (x) (print x))
(defun cell (l) l)
(defun uncell (l) l)
(defun fail (s) (error s))

;;(defun |!PPRINT| (term) (write-to-string term :pretty t))
(defun |!PPRINT| (term) (pprint term))

;;; This should be in a separate I/O spec.

;;; With Open File

(defun with-open-file-for-read-2 (name p)
  (with-open-file (s name :direction :input :if-does-not-exist :error)
    (funcall p s)))
(defun with-open-file-for-read (x) (with-open-file-for-read-2 (car x) (cdr x)))

(defun with-open-file-for-write-2 (name p)
  (with-open-file (s name :direction :output :if-exists :new-version)
    (funcall p s)))
(defun with-open-file-for-write (x) (with-open-file-for-write-2 (car x) (cdr x)))
(defpackage "MONADICSTATEINTERNAL")
(in-package "MONADICSTATEINTERNAL")

(defpackage "Specware-Global-Variables")

;; (defun findSymbol (name)
;;    (multiple-value-bind (symb ok) (find-symbol name "Specware-Global-Variables")
;;      (if ok
;;         (cons :|Some| symb)
;;         (cons :|None| nil)))
;; )

(defun newGlobalVar-2 (name value)
   (multiple-value-bind (symb found) (intern name "Specware-Global-Variables")
     (if (not found)
       (progn (setf (symbol-value symb) value) t)
       nil))
)
    
(defun readGlobalVar (name)
   (multiple-value-bind (symb ok) (find-symbol name "Specware-Global-Variables")
     (if ok
       (cons :|Some| (symbol-value symb))
       (cons :|None| nil)))
)

(defun writeGlobalVar-2 (name value)
   (multiple-value-bind (symb ok) (find-symbol name "Specware-Global-Variables")
     (if ok
       (progn (setf (symbol-value symb) value) t)
       nil))
)

(defun newVar (value) ; why does metaslang codegen think it should mangle this name?
   (cons :|VarRef| value)
)

; readVar written in MetaSlang.

; The test below should not be necessary because of MetaSlang typechecking.
(defun writeVar-2 (variable value)
   (if (eq (car variable) :|VarRef|)
     (progn (rplacd variable value) t)
     (error "writeVar: argument not a variable"))
)
;; This file defines general utilities that are necessary to 
;; connect EXTENDED-SLANG specs with lisp code.
;; The functions here are referenced in code produced by 
;;  Specware4/Languages/MetaSlang/CodeGen/Lisp/SpecToLisp.sw

(defpackage "SPECCALC")
(defpackage :SLANG-BUILT-IN)
(IN-PACKAGE :SLANG-BUILT-IN)

;; defvar specwareWizard? here (as opposed to def in Monad.sw) 
;; to avoid having CMUCL treat it as a constant, in which case
;; code under the false branch would be optimized away!
(defvar SPECCALC::specwareWizard? nil) ; see Specware4/Languages/SpecCalculus/Semantics/Monad.sw

(defparameter quotient-tag
  (list :|Quotient|))

(defun quotient (r)
  #'(lambda(x)  (vector quotient-tag r x)))

(defun quotient-1-1 (r x)
  (vector quotient-tag r x))

(defun quotient? (x)
  (and (vectorp x)
       (eq (svref x 0) quotient-tag)))

(defun quotient-relation (x)
  (svref x 1))

(defun quotient-element (x)
  (if (quotient? x)
      (svref x 2)
    (error "Expected an equivalence class, but got (presumably) a representative: ~S" x)))

(define-compiler-macro quotient-element (x)
  `(svref ,x 2))

(defun choose ()
  #'(lambda (f) #'(lambda(x) (funcall f (quotient-element x)))))

(defun choose-1 (f)
  #'(lambda(x) (funcall f (quotient-element x))))

(defun choose-1-1 (f x) 
  (funcall f (quotient-element x)))

#|
  
  slang-term-equals
  -----------------
     This function determines equality for lisp expressions that
     are generated from EXT-SLANG terms admitting equality.


     A translated ext-slang term admitting equality can be in one of the
     following forms:

  (vector t1 t2 ... tn)   - a product
  (cons t1 t2)            - a two tuple
  (cons t1 t2) , nil      - an element of a list sort
  (list 'Quotient 'fn t)  - an element of a quotient sort
  (cons 'Name t)          - an embedding
  atom                    - a string, char, or nat constant.

|#

;;;  (defun slang-term-equals (t1 t2)
;;;     (or 
;;;      (eq t1 t2)
;;;      (cond
;;;        ((null t1) (null t2))
;;;        ((stringp t1) (string= t1 t2))
;;;        ((symbolp t1) (eql t1 t2))
;;;        ((numberp t1) (eq t1 t2))
;;;        ((characterp t1) (eql t1 t2))
;;;  #| 
;;;     Determine equality by calling the quotient 
;;;     operator in the second position 
;;;     |#
;;;        ((and (quotient? t1)
;;;  	    (quotient? t2))
;;;         (funcall 
;;;  	(quotient-relation t1)
;;;  	(quotient-element t1) 
;;;  	(quotient-element t2)))
;;;       
;;;  #|
;;;     Cons cells are equal if their elements are equal too.
;;;  |#
;;;        ((consp t1) 	 
;;;             (and 
;;;  	    (consp t2) 
;;;  	    (slang-term-equals (car t1) (car t2))
;;;  	    (slang-term-equals (cdr t1) (cdr t2))))
;;;  #|
;;;     Two vectors (corresponding to tuple types)
;;;     are equal if all their elements are equal.
;;;  |#
;;;        ((vectorp t1)
;;;             (and 
;;;  	    (vectorp t2)
;;;  	    (let ((dim (array-dimension t1 0)))
;;;  	      (do ((i 0 (+ i 1))
;;;  		   (v-equal t (slang-term-equals (svref t1 i)  (svref t2 i))))
;;;  		  ((or (= i dim) (not v-equal)) v-equal)))))
;;;        (t (progn (format t "Ill formed terms~%") nil))
;;;        )
;;;      )
;;;     )

;;; This is twice as fast as the version above...
(defun slang-term-equals-2 (t1 t2)
  (or (eq t1 t2)
      (typecase t1
	(null      (null    t2))
	(string    (string= t1 t2))
	(symbol    (eq      t1 t2))
	(number    (eq      t1 t2)) ; catches complex numbers, etc.
	(character (eq      t1 t2))
	(cons      (and (consp t2) 
			;;   Cons cells are equal if their elements are equal too.
			(slang-term-equals-2 (car t1) (car t2))
			(slang-term-equals-2 (cdr t1) (cdr t2))))
        (vector    (cond ((and   
			   ;; (quotient? t1) 
			   ;; (quotient? t2)
			   (eq (svref t1 0) quotient-tag)
			   (vectorp t2)
			   (eq (svref t2 0) quotient-tag)
			   )
			  ;; Determine equality by calling the quotient 
			  ;; operator in the second position 
			  (funcall (svref t1 1) ; (quotient-relation t1)
				   (cons (svref t1 2) ; (quotient-element t1) 
				         (svref t2 2) ; (quotient-element t2)
				   )))
			 (t
			  (and
			   ;; Two vectors (corresponding to tuple types)
			   ;; are equal if all their elements are equal.
			   (vectorp t2)
			   (let ((dim (array-dimension t1 0)))
			     (do ((i 0 (+ i 1))
				  (v-equal t (slang-term-equals-2 (svref t1 i)  (svref t2 i))))
				 ((or (= i dim) (not v-equal)) v-equal)))))))
	(hash-table
	 ;; This can happen, for example, when comparing specs, which use maps from
	 ;; /Library/Structures/Data/Maps/SimpleAsSTHarray.sw that are implemented
	 ;; with hash tables in the associated Handwritten/Lisp/MapAsSTHarray.lisp
	 ;; Expensive pair of sub-map tests, but should be used rarely:
	 (catch 'fail
	   ;; fail if t1 disagrees with t2 for something in the domain of t1
	   (maphash #'(lambda (k v) 
			(unless (slang-term-equals-2 v (gethash k t2))
			  (throw 'fail nil)))
		    t1)
	   ;; fail if t2 disagrees with t1 for something in the domain of t2
	   (maphash #'(lambda (k v) 
			(unless (slang-term-equals-2 v (gethash k t1))
			  (throw 'fail nil)))
		    t2)
	   ;; the maps are functionally equivalent
	   t))
	(pathname
	 ;; As long as we might have hash-tables, maybe pathnames?
	 (equal t1 t2))
	(t 
	 ;; structures, etc. will end up here
	 ;; print semi-informative error message, but avoid printing
	 ;; what could be enormous structures...
	 (progn 
	   (warn "In slang-term-equals, ill formed terms of types ~S and ~S are ~A~%" 
		 (type-of t1)
		 (type-of t2)
		 (if (equal t1 t2) "LISP:EQUAL" "not LISP:EQUAL"))
	   ;; would it be better to just fail?
	   (equal t1 t2))))))

(defun slang-term-equals (x) (slang-term-equals-2 (car x) (cdr x)))

(defun slang-term-not-equals-2 (x y) 
  (not (slang-term-equals-2 x y)))

;;; optimizations of not-equals for Booleans and Strings:

;; The boolean version of slang-term-equals-2 is just cl:eq, 
;; and we wouldn't need boolean-not-equals-2 if neq was also defined in ANSI Common Lisp.
;; We avoid calling this neq, to mimimize confusion in implementations that define neq.
(defun boolean-not-equals-2 (x y) 
  (not (eq x y)))

(defun string-not-equals-2 (x y)
  ;; Note: this     returns NIL or T  
  ;;       string/= returns NIL or integer, which could confuse subsequent boolean 
  ;;       comparisons implemented with cl::eq.
  (not (string= x y)))

;; CL 'and' and 'or' correspond to (non-strict) "&&" and "||"

;; Nothing in CL corresponds to boolean 'implies':
;; TODO: This probably isn't (or shouldn't be) possible, 
;;       since syntax ("&&", "||", "=>", etc.) can't (shouldn't) be passed as an arg
(defun implies-2 (x y) 
  (or (not x) y))

#|

 Tests:

 (slang-term-equals (cons (vector 1 2 3) (vector 1 2 3)))

 (slang-term-equals (cons (vector 1 2 "3") (vector 1 2 "3")))
 (slang-term-equals (cons (vector 1 2 "3") (vector 1 2 "4")))

 (slang-term-equals (cons 
            (list 'Quotient 
                  (lambda (x) (eq (< 10 (car x)) (< 10 (cdr x))))
                  3)
            (list 'Quotient 
                  (lambda (x) (eq (< 10 (car x)) (< 10 (cdr x))))
                  11)))

|#



(provide "SpecwareRuntime")