(in-package "DJVM")
(include-book "../M6-DJVM-shared/jvm-state")
(include-book "../M6-DJVM-shared/jvm-thread") ;; for wff-thread
(include-book "../M6-DJVM-shared/jvm-frame-manipulation-primitives") ;; for wff-call-stack
(include-book "../M6-DJVM-shared/jvm-linker") ;; deref-mehtod
(include-book "../DJVM/djvm-thread") ;; 

;; basically copied from consistent-state.lisp
;; ??

(acl2::set-verify-guards-eagerness 2)

(defun max-stack-guard (s)
  (mylet* ((th (thread-by-id (current-thread s)
                             (thread-table s)))
           (frame (top (thread-call-stack th)))
           (method-ptr (method-ptr frame))
           (method     (deref-method method-ptr (instance-class-table s))))
  (and (wff-state s)
       (wff-thread-table (thread-table s))
       (wff-thread th)
       (wff-call-stack (thread-call-stack th))
       (wff-call-frame (top (thread-call-stack th)))
       (wff-class-table (class-table s))
       (wff-instance-class-table (instance-class-table s))
       (wff-method-ptr method-ptr)
       (wff-method-decl method)
       (wff-code (method-code method)))))

(defun max-stack (s)
  (declare (xargs :guard (max-stack-guard s)))
  (mylet* ((th (thread-by-id (current-thread s)
                             (thread-table s)))
           (frame (top (thread-call-stack th)))
           (method-ptr (method-ptr frame))
           (method     (deref-method method-ptr (instance-class-table s))))
       (method-maxstack method)))

;; (in-theory (enable wff-call-stack))

(defun max-local (s)
  (declare (xargs :guard (max-stack-guard s)))
  (mylet* ((th (thread-by-id (current-thread s)
                             (thread-table s)))
           (frame (top (thread-call-stack th)))
           (method-ptr (method-ptr frame))
           (method     (deref-method method-ptr (instance-class-table s))))
       (method-maxlocals method)))

