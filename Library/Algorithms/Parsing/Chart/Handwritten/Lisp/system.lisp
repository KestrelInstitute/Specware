;;; -*- Mode: LISP; Package: User; Base: 10; Syntax: Common-Lisp -*-

(in-package "CL-USER")

(defun local-file (filename) 
  (make-pathname :name filename :defaults *LOAD-PATHNAME*))

(defun load-local-file (filename) 
  (specware::load-lisp-file (local-file filename) :compiled? nil))

(defun compile-and-load-local-file (filename) 
  (specware::compile-and-load-lisp-file (local-file filename)))

(load-local-file "parser-package") 

;; Setting the count to 1 means you can push :DEBUG-PARSER twice onto
;;  *features* prior to loading this file and one occurrence will survive.
(setq *features* (remove :DEBUG-PARSER    *features* :count 1))
(setq *features* (remove :OPTIMIZE-PARSER *features* :count 1))

;; Choose either or neither (both is ok, but would be peculiar)
;(pushnew :DEBUG-PARSER *features*)
;(pushnew :OPTIMIZE-PARSER *features*)

#+DEBUG-PARSER    (format t "~%DEBUG-PARSER    feature is on.~2%")
#+OPTIMIZE-PARSER (format t "~%OPTIMIZE-PARSER feature is on.~2%")

#+DEBUG-PARSER 
(proclaim '(optimize (speed 0) (safety 3) (compilation-speed 0) (space 0) (debug 3)))

#-DEBUG-PARSER 
(progn
  #+OPTIMIZE-PARSER
  (proclaim '(optimize (speed 3) (safety 0) (compilation-speed 0) (space 0) (debug 0)))
  #-OPTIMIZE-PARSER
  (proclaim '(optimize (speed 3) (safety 1) (compilation-speed 0) (space 0) (debug 2)))
  )

(defmacro parser4::when-debugging (&body body)  
  #-DEBUG-PARSER ()
  #+DEBUG-PARSER `(progn ,@body)
  )

(defmacro parser4::debugging-comment (&body body) 
  `(parser4::when-debugging 
    (when parser4::*verbose?*
      (parser4::comment ,@body))))

#+allegro 
;;; The strategy below is perhaps misguided.
;;; Keeping the old space large and new space small might be the best strategy, e.g.
;;;  (setf (sys::gsgc-parameter :expansion-free-percent-new)  5) ; default is 35
;;;  (setf (sys::gsgc-parameter :expansion-free-percent-old) 80) ; default is 35
;;; At any rate, do this in the main build file, not down here.
'(progn
  ; (proclaim '(:explain :types :calls :boxing :variables))
  (proclaim '(:explain :notypes :nocalls :noboxing :novariables))

  ;; Increase initial freespace by factor of 16, to reduce frequency of GC's 
  ;;  (setting it too large, e.g. another facto of 16,  tends to cause many page faults during gc's)
  (setf (sys::gsgc-parameter :free-bytes-new-other) #x200000) ; default is #x20000

  ;; The next three settings cause new/old space to grow more aggressively than
  ;;  the defaults settings.
  ;; This setting will tend to make free space grow more aggressively, since each scavange 
  ;; must this percentage free to avoid expansion...
  (setf (sys::gsgc-parameter :free-percent-new) 30) ; default is 25
  ;;  These two indicate the per cent of new/old space that must be free 
  ;; after gc to avoid expanding new/old space.
  (setf (sys::gsgc-parameter :expansion-free-percent-new) 50) ; default is 35
  (setf (sys::gsgc-parameter :expansion-free-percent-old) 50) ; default is 35
)

;;; Remove quote to enable gc messages...
#+allegro
'(progn
  (setf (sys::gsgc-parameter :print)   t) ; default is nil
  (setf (sys::gsgc-parameter :stats)   t) ; default is nil
  (setf (sys::gsgc-parameter :verbose) nil) ; default is nil
  )

;(sys::resize-areas :new #x6000000) ; big! (hmm... too big...)

(compile-and-load-local-file "comment-hack")
(compile-and-load-local-file "parse-decls")

#+DEBUG-PARSER (compile-and-load-local-file "parse-debug-1")

(compile-and-load-local-file "parse-add-rules")
(compile-and-load-local-file "seal-parser")

(compile-and-load-local-file "parse-node-utilities")

(compile-and-load-local-file "tokenizer-decls")
(compile-and-load-local-file "tokenizer")

(compile-and-load-local-file "parse-semantics")
;;   (compile-and-load-local-file  "pprint") ; will be here soon 

(compile-and-load-local-file "parse-top")

#+DEBUG-PARSER (compile-and-load-local-file "parse-debug-2")

(compile-and-load-local-file "describe-grammar")

;(parser4::load-slang-parser "/usr/local/specware/parser/sw-ops") ; object, arrow, span, pullback, etc.

;(gc)
;(setf (sys::gsgc-parameter :generation-spread) 0) ; default is 4 -- this triggers immediate tenuring
;(gc)
;(gc)
;(gc)
;(gc)


;; Making generation-spread larger avoids having temp structures being 
;;  promoted into old space.  With this setting they need to survive 
;; 20 gc's for that to happen.  (Legal range is 4-26)  Downside: they get
;; copied back and forth more.
#+allegro
(setf (sys::gsgc-parameter :generation-spread) 12) ; default is 4
