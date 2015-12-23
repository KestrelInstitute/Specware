(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

Directory qualifying spec

import Pathname

%% specware::directory? and specware::sw-directory are defined in <sw>/Applications/Handwritten/Lisp/load-utilities.lisp
%% They handle non-standard features in various implementations of Common Lisp.

op directory? : Pathname -> Bool

op directory (pathname : Pathname) : Option (List Pathname) =
 if directory? pathname then
   Some (list_directory pathname)
 else
   None


op list_directory            : Pathname -> List Pathname  % when looking for <dir>/*.*
op list_restricted_directory : Pathname -> List Pathname  % when looking for <dir>/x.* or <dir>/*.y

op list_files_with_type (dir : String, file_type : String) : List Pathname =
 let p1 = parse_namestring dir in
 let p2 = case p1.file_name  of
            | None -> p1 << {file_name = Wild}
            | _ -> p1
 in
 let p3 = null_pathname << {file_type = Some file_type} in
 let p4 = merge_pathnames (p3, p2)                      in
 list_restricted_directory p4

%% If pathname refers to a directory, list_directory will return Some list of files 
%% Otherwise it will return None.

#translate lisp
-verbatim

;; general pattern is to convert args, process, convert result back

(defun Directory-Spec::directory? (sw_pathname)
  (let ((lisp_pathname (pathname-spec::sw_to_lisp sw_pathname)))
   (specware::directory? lisp_pathname)))

(defun Directory-Spec::list_directory (sw_pathname)
  ;; sw-directory replaces any provided :name and/or :type with :wild,
  ;;  collecting files that match <dir>/*.*
  ;; At least for sbcl, the match for this pattern will include files that lack a dot.
  (let* ((lisp_pathname  (pathname-spec::sw_to_lisp sw_pathname))
         (lisp_pathnames (specware::sw-directory    lisp_pathname))
         (sw_pathnames   (mapcar #'pathname-spec::lisp_to_sw 
                                 lisp_pathnames)))
     sw_pathnames))

(defun Directory-Spec::restricted_directory (lisp_pathname)
  (directory lisp_pathname                                         ; differs from sw-directory here, does not merge in :wild fields
             #-sbcl :allow-other-keys         #-sbcl    t          ; permits implementation-specific keys to be ignored by other implementations
             #+mcl  :directories              #+mcl     t          ; specific to mcl
          ;; #+mcl  :all                      #+mcl     recursive? ; specific to mcl
             #+allegro :directories-are-files #+allegro nil        ; specific to allegro -- we never want this option, but it defaults to T (!)
             ))

(defun Directory-Spec::list_restricted_directory (sw_pathname)
  ;; Use this function to get finer control over the :name and :type fields
  (let* ((lisp_pathname  (pathname-spec::sw_to_lisp            sw_pathname))
         (lisp_pathnames (directory-spec::restricted_directory lisp_pathname))
         (sw_pathnames   (mapcar #'pathname-spec::lisp_to_sw 
                                 lisp_pathnames)))
    sw_pathnames))

-end
#end

end-spec
