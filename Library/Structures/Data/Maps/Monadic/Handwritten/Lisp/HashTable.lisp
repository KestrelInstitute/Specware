(defpackage "MonadicMapsInternal")
(in-package "MonadicMapsInternal")

(defun makeHashtableEqualDefaults ()
  (make-hash-table :test 'equal)
)

(defun makeHashtableEqDefaults ()
  (make-hash-table :test 'eq)
)

(defun makeHashtableEqual-1 (params)
  (makeHashtableEqual (car params) (cdr params))
)

(defun makeHashtableEqual (tableSize rehashSize)
  (make-hash-table :test 'equal :size tableSize :rehash-size rehashSize)
)

(defun makeHashtableEq-1 (params)
  (makeHashtableEq (car params) (cdr rehashSize))
)

(defun makeHashtableEq (tableSize rehashSize)
  (make-hash-table :test 'eq :size tableSize :rehash-size rehashSize)
)

(defun getHashtable-1 (params)
  (getHashtable (svref params 0) (svref params 1) (svref params 2))
)

(defun getHashtable (table key defaultValue)
  (gethash key table defaultValue)
)

(defun setHashtable (table key value)
  (setf (gethash key table) value)
)

(defun remHashtable (table key)
  (remhash table key)
)

(defun mapHashtable (table fcn)
  (maphash #'(lambda (key val) (funcall fcn (cons key val))) table)
)
