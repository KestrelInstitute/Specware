(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

SpecwareShell qualifying spec

%%% This facilitates interoperability between specware functions
%%% and lower-level implementation (e.g. Lisp) functions.

type Symbol = String

type TypedValues = List TypedValue
type TypedValue  = | String  String
                   | Symbol  Symbol        % note: unit ids are symbols
                   | Bool    Bool
                   | Int     Int
                   | List    TypedValues
                   | Char    Char          % unlikely to be used
                   | Unknown String        


#translate lisp
-verbatim

(defpackage :SpecwareShell)
(in-package :SpecwareShell)

(defun type_values (lisp_values)
  (mapcar #'type_value lisp_values))

(defun type_value (lisp_value)
  (typecase lisp_value
    (string    (cons :|String|  lisp_value))
    (integer   (cons :|Int|     lisp_value))
    (character (cons :|Char|    lisp_value))
    (boolean   (cons :|Bool|    lisp_value))
    (symbol    (cons :|Symbol|  (symbol-name lisp_value)))
    (list      (cons :|List|    (mapcar #'type_value lisp_value)))
    (t         (cons :|Uknown|  (format nil "~S" lisp_value)))))

(defun untype_values (sw_values)
  (mapcar #'untype_value sw_values))

(defun untype_value (sw_value)
  (case (car sw_value)
     (:|List|   (untype_values (cdr sw_value)))
     (:|Symbol| (intern (cdr sw_value)))
     (t         (cdr sw_value))))

-end
#end

end-spec
