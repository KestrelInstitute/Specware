(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

SpecwareShell qualifying spec

import /Library/Legacy/Utilities/System  % writeLine
import CommandParser

op showCurrentDirectory (ctxt : CommandContext) 
 : Result CommandContext =
 let _ = writeLine (ctxt.current_dir) in
 Good ctxt

op connectToDirectory (dir  : DirectoryName, 
                       ctxt : CommandContext)  
 : Result CommandContext =
 let ctxt = ctxt << {current_dir = dir} in
 showCurrentDirectory ctxt

op list_sw_files (dir : DirectoryName) : () 

op listFilesInDirectory (dir        : DirectoryName, 
                         recursive? : Bool, 
                         ctxt       : CommandContext) 
 : Result CommandContext =
 let dir = if dir = "" then 
             ctxt.current_dir 
           else 
             dir 
 in
 let _ = list_sw_files dir in
 Good ctxt

#translate lisp
-verbatim

(defpackage :SWShell)
(in-package :SWShell)

(defun SpecwareShell::list_sw_files (dir)
   (ls dir))

(defun ls (&optional (str ""))
  (let* ((dirpath  (Specware::dir-to-path str))
	 (contents (Specware::sw-directory dirpath))
	 (sw-files (loop for p in contents
		     when (or (string= (pathname-type p) "sw")
			      (Specware::directory? p))
		     collect p)))
    (list-files sw-files)
    (values)))

(defun Specware::dir (&optional (str ""))
  (ls str))

(unless (fboundp 'dir)
  (defun dir (&optional (str ""))
    (ls str)))

(defun dirr (&optional (str ""))
  (list-directory-rec (Specware::dir-to-path str))
  (values))

(defun list-directory-rec (dir)
  (let* ((contents (Specware::sw-directory dir))
	 (sw-files (loop for p in contents
		     when (string= (pathname-type p) "sw")
		     collect p)))
    (when (not (null sw-files))
      (format t "~a:~%" (namestring dir))
      (list-files sw-files))
    (loop for p in contents
      unless (equal (pathname-name p) "CVS")
      do (when (Specware::directory? p)
	   (list-directory-rec p))))
  )

(defparameter *dir-width* 80)

(defun list-files (files)
  (when files
    (let* ((names (loop for fil in files
		        for nm = (pathname-name fil)
			for ty = (pathname-type fil)
			collect (if (and (null nm) (null ty))
				    (last (pathname-directory fil))
				  (cons nm ty))))
	   (num-files (length names))
	   (max-width (1+ (loop for name in names maximize (+ (length (car name)) (length (cdr name))))))
	   (across (floor *dir-width* max-width))
	   (rows (ceiling num-files across))
	   (grouped-names (loop for i from 0 to (- rows 1)
			    collect
			    (loop for j from i to (min (- num-files 1) ( * across rows)) by rows
			          collect (elt names j)))))
      (loop for row in grouped-names
	do (loop for fil in row
	     do (format t " ~va" max-width (if (null (cdr fil))
					       (concatenate 'string (car fil) "/")
					     (concatenate 'string (car fil) "." (cdr fil)))))
	   (format t "~%")))))
-end
#end

end-spec
