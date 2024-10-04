(in-package "JVM")
(include-book "../M6-DJVM-shared/jvm-state")
(include-book "../M6-DJVM-shared/jvm-thread")
(include-book "../M6-DJVM-shared/jvm-frame-manipulation-primitives")

;----------------------------------------------------------------------

(defun wff-method-ptr-regular (method-ptr)
  (and (wff-method-ptr method-ptr)
       (equal (make-method-ptr (method-ptr-classname method-ptr)
                               (method-ptr-methodname method-ptr) 
                               (method-ptr-args-type  method-ptr)
                               (method-ptr-returntype method-ptr))
              method-ptr)))

(defun wff-call-frame-regular (frame)
  (and (wff-call-frame frame)
       (equal (make-frame (return-pc frame)
                          (operand-stack frame)
                          (locals frame)
                          (method-ptr frame)
                          (sync-obj-ref frame)
                          (resume-pc frame)
                          (frame-aux frame))
              frame)))

(defun wff-call-stack-regular (cs)
  (wff-call-stack cs))

(defun wff-thread-regular (thread)
  (and (wff-thread thread)
       (equal (make-thread (thread-id thread)
                           (thread-saved-pc thread)
                           (thread-call-stack thread)
                           (thread-state thread)
                           (thread-mref thread)
                           (thread-mdepth thread)
                           (thread-ref thread))
              thread)))

(defun wff-thread-table-regular (thread-table)
  (if (not (consp thread-table)) t
    (and (wff-thread-regular (car thread-table))
         (wff-thread-table-regular (cdr thread-table)))))

(defun wff-state-regular (s)
  (and (wff-state s)
       (equal (make-state (pc s)
                          (current-thread s)
                          (heap s)
                          (thread-table s)
                          (class-table s)
                          (env s)
                          (error-flag s)
                          (aux s))
              s)))

;----------------------------------------------------------------------
