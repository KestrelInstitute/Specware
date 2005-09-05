(format t "loading xml-rpc...~%")

(defpackage :s-xml)
(defpackage :s-xml-rpc)

(defvar Specware4 (specware::getenv "SPECWARE4"))

(defvar *xml-rpc-dir* (concatenate 'string Specware4 "/Library/IO/XmlRpc"))

(compile-and-load-lisp-file (concatenate 'string *xml-rpc-dir* "/s-xml/package"))
(compile-and-load-lisp-file (concatenate 'string *xml-rpc-dir* "/s-xml/xml"))
(compile-and-load-lisp-file (concatenate 'string *xml-rpc-dir* "/s-xml-rpc/base64"))
(compile-and-load-lisp-file (concatenate 'string *xml-rpc-dir* "/s-xml-rpc/package"))
(compile-and-load-lisp-file (concatenate 'string *xml-rpc-dir* "/s-xml-rpc/sysdeps"))
(compile-and-load-lisp-file (concatenate 'string *xml-rpc-dir* "/s-xml-rpc/xml-rpc"))
(compile-and-load-lisp-file (concatenate 'string *xml-rpc-dir* "/s-xml-rpc/extensions"))


(in-package :common-lisp-user)

(defun start-xml-rpc-server (port) 
  (s-xml-rpc:start-xml-rpc-server :port port)
  (format t ";;; XML-RPC server listening at port ~A~%" port)
)

