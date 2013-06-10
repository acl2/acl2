#|
(include-book "m5")
(certify-book "apprentice-state" 1)
JSM
|#

(in-package "M5")

; The material below is the output of jvm2acl2 on Apprentice.java.

(defconst *Apprentice-class-table*
 (make-class-def
  (list
    (make-class-decl "Apprentice"
                     '("java.lang.Object")
                     '()
                     '()
                     '()
                     (list
                        '("<init>" () nil
                           (aload_0)
                           (invokespecial "java.lang.Object" "<init>" 0)
                           (return))
                        '("main" (java.lang.String[]) nil
                           (new "Container")
                           (dup)
                           (invokespecial "Container" "<init>" 0)
                           (astore_1)
                           (goto LABEL::TAG_0)
                           (LABEL::TAG_0 new "Job")
                           (dup)
                           (invokespecial "Job" "<init>" 0)
                           (astore_2)
                           (aload_2)
                           (aload_1)
                           (invokevirtual "Job" "setref" 1)
                           (aload_2)
                           (invokevirtual "java.lang.Thread" "start" 0)
                           (goto LABEL::TAG_0)))
                     '(REF -1))
    (make-class-decl "Container"
                     '("java.lang.Object")
                     '("counter")
                     '()
                     '()
                     (list
                        '("<init>" () nil
                           (aload_0)
                           (invokespecial "java.lang.Object" "<init>" 0)
                           (return)))
                     '(REF -1))
    (make-class-decl "Job"
                     '("java.lang.Thread" "java.lang.Object")
                     '("objref")
                     '()
                     '()
                     (list
                        '("<init>" () nil
                           (aload_0)
                           (invokespecial "java.lang.Thread" "<init>" 0)
                           (return))
                        '("incr" () nil
                           (aload_0)
                           (getfield "Job" "objref")
                           (astore_1)
                           (aload_1)
                           (monitorenter)
                           (LABEL::TAG_1 aload_0)
                           (getfield "Job" "objref")
                           (aload_0)
                           (getfield "Job" "objref")
                           (getfield "Container" "counter")
                           (iconst_1)
                           (iadd)
                           (putfield "Container" "counter")
                           (aload_1)
                           (monitorexit)
                           (goto LABEL::TAG_0)
                           (LABEL::TAG_2 astore_2)
                           (aload_1)
                           (monitorexit)
                           (aload_2)
                           (athrow)
                           (LABEL::TAG_0 aload_0)
                           (areturn))
                        '("setref" (Container) nil
                           (aload_0)
                           (aload_1)
                           (putfield "Job" "objref")
                           (return))
                        '("run" () nil
                           (goto LABEL::TAG_0)
                           (LABEL::TAG_0 aload_0)
                           (invokevirtual "Job" "incr" 0)
                           (pop)
                           (goto LABEL::TAG_0)))
                     '(REF -1)))))

(defconst *Apprentice-main*
   '((new "Container")
     (dup)
     (invokespecial "Container" "<init>" 0)
     (astore_1)
     (goto LABEL::TAG_0)
     (LABEL::TAG_0 new "Job")
     (dup)
     (invokespecial "Job" "<init>" 0)
     (astore_2)
     (aload_2)
     (aload_1)
     (invokevirtual "Job" "setref" 1)
     (aload_2)
     (invokevirtual "java.lang.Thread" "start" 0)
     (goto LABEL::TAG_0)))

(defun Apprentice-ms ()
  (make-state
   (make-tt (push (make-frame 0
                              nil
                              nil
                              *Apprentice-main*
                              'UNLOCKED
                              nil)
                  nil))
   nil
   *Apprentice-class-table*))

(defun Apprentice ()
  (m5_load (Apprentice-ms)))
