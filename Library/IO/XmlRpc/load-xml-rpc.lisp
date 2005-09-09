(format t "loading xml-rpc...~%")

#+allegro
(progn
  (in-package :common-lisp-user)

  (defvar *xml-rpc-server-id*)
  (require :xml-rpc)
  (defun start-xml-rpc-server (port)
    (let ((start-args (list :port port)))
      (progn
	(setq *xml-rpc-server-id*
	      (net.xml-rpc:make-xml-rpc-server
	       :start start-args :enable t :introspect t))
	(net.xml-rpc:export-standard-xml-rpc-methods *xml-rpc-server-id*))))
)

#+openmcl
(progn
  (defpackage :s-xml)
  (defpackage :s-xml-rpc)

  (in-package :common-lisp-user)

  (defun start-xml-rpc-server (port) 
    (s-xml-rpc:start-xml-rpc-server :port port)
    (format t ";;; XML-RPC server listening at port ~A~%" port)
    )
)

