(defpackage :Thread)
(in-package :Thread)

(defun makeThread (f)
  #+sb-thread (sb-thread:make-thread f)
  #-sb-thread (funcall f))

(defun joinThread (t1)
  #+sb-thread (sb-thread:join-thread t1)
  #-sb-thread t1)


(defun makeMutex (nm)
  #+sb-thread (sb-thread:make-mutex :name nm)
  #-sb-thread nm)

(defun getMutex (mx)
  #+sb-thread (sb-thread:get-mutex mx)
  #-sb-thread mx)
(defun releaseMutex (mx)
  #+sb-thread (sb-thread:release-mutex mx)
  #-sb-thread mx)

(defun haveMutex? (mx)
  #+sb-thread (eq (sb-thread:mutex-value mx) sb-thread:*current-thread*)
  #-sb-thread t)

(defmacro withMutex-1-1 (mx body)
  #+sb-thread `(sb-thread:with-mutex (,mx) ,body)
  #-sb-thread `,body)

(defun Thread::mapT-1-1 (f l) 
  (let ((threads 
         (List-Spec::map-1-1 
          #'(lambda (x) 
             (Thread::makeThread 
              #'(lambda () (funcall f x)))) 
          l))) 
    (List-Spec::map-1-1 #'Thread::joinThread threads)))

(defun Thread::mapT (x1) #'(lambda (x2) (Thread::mapT-1-1 x1 x2)))

