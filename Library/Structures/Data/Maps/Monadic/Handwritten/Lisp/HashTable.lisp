(defpackage "MonadicMapsInternal")
(in-package "MonadicMapsInternal")

(defun makeHashtableEqualDefaults ()
  (make-hash-table :test 'equal)
)

(defun makeHashtableEqDefaults ()
  (make-hash-table :test 'eq)
)

(defun makeHashtableEqual (params)
  (makeHashtableEqual-2 (car params) (cdr params))
)

(defun makeHashtableEqual-2 (tableSize rehashSize)
  (make-hash-table :test 'equal :size tableSize :rehash-size rehashSize)
)

(defun makeHashtableEq (params)
  (makeHashtableEq-2 (car params) (cdr rehashSize))
)

(defun makeHashtableEq-2 (tableSize rehashSize)
  (make-hash-table :test 'eq :size tableSize :rehash-size rehashSize)
)

(defun getHashtable (params)
  (getHashtable-3 (svref params 0) (svref params 1) (svref params 2))
)

(defun getHashtable-3 (table key defaultValue)
  (gethash key table defaultValue)
)

(defun setHashtable-3 (table key value)
  (setf (gethash key table) value)
)

(defun remHashtable-2 (table key)
  (remhash table key)
)

(defun mapHashtable-2 (table fcn)
  (maphash #'(lambda (key val) (funcall fcn (cons key val))) table)
)
