(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

Pathname qualifying spec

import IO
import /Library/Legacy/Utilities/System

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Common Lisp Pathnames
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% We follow the structure, but not the exact naming, used by Common Lisp.
%%
%% Note: In Common Lisp, nil (i.e. None) and Unspecific are processed the same,
%%       except that nil is replaced when merging, while Unspecific is not.
%%
%% Note: Pathname.FileName is the name of a pathname component
%%       IO.Filename       is a string holding the entire name of a file

type Namestring = Filename

type RawHost    % some internal lisp structure

type Host       = | Some RawHost
                  | None
                  | Unspecific
                  | Wild

type Device     = | Some String 
                  | None
                  | Unspecific
                  | Wild

type Directory  = | Some (List String)
                  | None
                  | Unspecific
                  | Wild

type FileName   = | Some String
                  | None
                  | Unspecific
                  | Wild

type FileType   = | Some String
                  | None
                  | Unspecific
                  | Wild

type Version    = | Some Int
                  | None          
                  | Unspecific    
                  | Newest
                  | Wild

type Pathname   = {host      : Host,
                   device    : Device,
                   directory : Directory,
                   file_name : FileName,                 % name in Common Lisp
                   file_type : FileType,                 % type in Common Lisp
                   version   : Version}

op make_Pathname (host      : Host,
                  device    : Device,
                  directory : Directory,
                  file_name : FileName,   
                  file_type : FileType,   
                  version   : Version)
 : Pathname =
 {host      = host,
  device    = device,
  directory = directory,
  file_name = file_name,
  file_type = file_type,
  version   = version}
 
op pathname_host      (pathname : Pathname) : Host       = pathname.host
op pathname_device    (pathname : Pathname) : Device     = pathname.device
op pathname_directory (pathname : Pathname) : Directory  = pathname.directory
op pathname_name      (pathname : Pathname) : FileName   = pathname.file_name
op pathname_type      (pathname : Pathname) : FileType   = pathname.file_type
op pathname_version   (pathname : Pathname) : Version    = pathname.version

op null_pathname : Pathname = 
 make_Pathname (None, None, None, None, None, None)

op parse_namestring : Namestring          -> Pathname    % parse-namestring in Common Lisp
op print_pathname   : Pathname            -> Namestring  % namestring       in Common Lisp
op merge_pathnames  : Pathname * Pathname -> Pathname    % merge-pathnames  in Common Lisp

#translate lisp
-verbatim

;; sw_to_lisp and lisp_to_sw convert between sw and lisp formats for pathname structures

(defun Pathname-Spec::sw_to_lisp (sw_pathname)
   (let ((sw_host      (pathname-spec::pathname_host      sw_pathname))
         (sw_device    (pathname-spec::pathname_device    sw_pathname))
         (sw_directory (pathname-spec::pathname_directory sw_pathname))
         (sw_name      (pathname-spec::pathname_name      sw_pathname))
         (sw_type      (pathname-spec::pathname_type      sw_pathname))
         (sw_version   (pathname-spec::pathname_version   sw_pathname)))
    (let ((lisp_host      (case (car sw_host)   
                             (:|Some|       (cdr sw_host))
                             (:|Wild|       :Wild)
                             (:|Unspecific| :Unspecific)
                             (:|None|       nil)
                             (t             nil)))

          (lisp_device    (case (car sw_device) 
                             (:|Some|       (cdr sw_device)) 
                             (:|Wild|       :Wild)
                             (:|Unspecific| :Unspecific)
                             (:|None|       nil)
                             (t             nil)))

          (lisp_directory (case (car sw_directory)
                             (:|Some|       (cdr sw_directory))
                             (:|Wild|       :Wild)
                             (:|Unspecific| :Unspecific)
                             (:|None|       nil)
                             (t             nil)))

          (lisp_name      (case (car sw_name)
                             (:|Some|       (cdr sw_name))
                             (:|Wild|       :Wild)
                             (:|Unspecific| :Unspecific)
                             (:|None|       nil)
                             (t             nil)))

          (lisp_type      (case (car sw_type)
                             (:|Some|       (cdr sw_type))
                             (:|Wild|       :Wild)
                             (:|Unspecific| :Unspecific)
                             (:|None|       nil)
                             (t             nil)))

          (lisp_version   (case (car sw_version)
                             (:|Some|       (cdr sw_version))
                             (:|Wild|       :Wild)
                             (:|Unspecific| :Unspecific)
                             (:|Newest|     :Newest)
                             (:|None|       nil)
                             (t             nil))))

    (make-pathname :host      lisp_host
                   :device    lisp_device
                   :directory lisp_directory
                   :name      lisp_name
                   :type      lisp_type
                   :version   lisp_version))))
     
(defun Pathname-Spec::lisp_to_sw (lisp_pathname)
   (let ((lisp_host      (pathname-host      lisp_pathname))
         (lisp_device    (pathname-device    lisp_pathname))
         (lisp_directory (pathname-directory lisp_pathname))
         (lisp_name      (pathname-name      lisp_pathname))
         (lisp_type      (pathname-type      lisp_pathname))
         (lisp_version   (pathname-version   lisp_pathname)))
    (let ((sw_host       (case lisp_host
                            (:Unspecific `(:|Unspecific|))
                            (:Wild       `(:|Wild|))
                            ((nil)       `(:|None|))
                            (t           `(:|Some| . ,lisp_host))))
          (sw_device     (case lisp_device
                            (:Unspecific `(:|Unspecific|))
                            (:Wild       `(:|Wild|))
                            ((nil)       `(:|None|))
                            (t           `(:|Some| . ,lisp_device))))
          (sw_directory  (case lisp_directory
                            (:Unspecific `(:|Unspecific|))
                            (:Wild       `(:|Wild|))
                            ((nil)       `(:|None|))
                            (t           `(:|Some| . ,lisp_directory))))
          (sw_name       (case lisp_name
                            (:Unspecific `(:|Unspecific|))
                            (:Wild       `(:|Wild|))
                            ((nil)       `(:|None|))
                            (t           `(:|Some| . ,lisp_name))))
          (sw_type      (case lisp_type
                            (:Unspecific `(:|Unspecific|))
                            (:Wild       `(:|Wild|))
                            ((nil)       `(:|None|))
                            (t           `(:|Some| . ,lisp_type))))
          (sw_version   (case lisp_version
                            (:Unspecific `(:|Unspecific|))
                            (:Wild       `(:|Wild|))
                            ((nil)       `(:|None|))
                            (:Newest     `(:|Newest|))
                            (t           `(:|Some| . ,lisp_version)))))

     (pathname-spec::make_pathname-6 sw_host 
                                     sw_device 
                                     sw_directory 
                                     sw_name 
                                     sw_type 
                                     sw_version))))

;; general pattern is to convert args, process, convert result back

(defun Pathname-Spec::parse_namestring (namestring) 
  (let ((lisp_pathname (common-lisp::parse-namestring namestring)))
   (pathname-spec::lisp_to_sw lisp_pathname)))

(defun Pathname-Spec::print_pathname (sw_pathname) 
  (let ((lisp_pathname (pathname-spec::sw_to_lisp sw_pathname)))
   (common-lisp::namestring lisp_pathname)))

(defun Pathname-Spec::merge_pathnames-2 (sw_p1 sw_p2)
  (let* ((lisp_p1 (pathname-spec::sw_to_lisp sw_p1))
         (lisp_p2 (pathname-spec::sw_to_lisp sw_p2))
         (merged  (common-lisp::merge-pathnames lisp_p1 lisp_p2)))
    (pathname-spec::lisp_to_sw merged)))

-end
#end

end-spec
