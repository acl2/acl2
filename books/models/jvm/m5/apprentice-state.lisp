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
                        '("<init>:()V" () nil
                           (aload_0)
                           (invokespecial "java.lang.Object" "<init>:()V" 0)
                           (return))
                        '("main:([Ljava/lang/String;)V" (java.lang.String[]) nil
                           (new "Container")
                           (dup)
                           (invokespecial "Container" "<init>:()V" 0)
                           (astore_1)
                           (goto LABEL::TAG_0)
                           (LABEL::TAG_0 new "Job")
                           (dup)
                           (invokespecial "Job" "<init>:()V" 0)
                           (astore_2)
                           (aload_2)
                           (aload_1)
                           (invokevirtual "Job" "setref:(LContainer;)V" 1)
                           (aload_2)
                           (invokevirtual "java.lang.Thread" "start:()V" 0)
                           (goto LABEL::TAG_0)))
                     '(REF -1))
    (make-class-decl "Container"
                     '("java.lang.Object")
                     '("counter:I")
                     '()
                     '()
                     (list
                        '("<init>:()V" () nil
                           (aload_0)
                           (invokespecial "java.lang.Object" "<init>:()V" 0)
                           (return)))
                     '(REF -1))
    (make-class-decl "Job"
                     '("java.lang.Thread" "java.lang.Object")
                     '("objref:LContainter;")
                     '()
                     '()
                     (list
                        '("<init>:()V" () nil
                           (aload_0)
                           (invokespecial "java.lang.Thread" "<init>:()V" 0)
                           (return))
                        '("incr:()LJob;" () nil
                           (aload_0)
                           (getfield "Job" "objref:LContainter;")
                           (astore_1)
                           (aload_1)
                           (monitorenter)
                           (LABEL::TAG_1 aload_0)
                           (getfield "Job" "objref:LContainter;")
                           (aload_0)
                           (getfield "Job" "objref:LContainter;")
                           (getfield "Container" "counter:I")
                           (iconst_1)
                           (iadd)
                           (putfield "Container" "counter:I")
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
                        '("setref:(LContainer;)V" (Container) nil
                           (aload_0)
                           (aload_1)
                           (putfield "Job" "objref:LContainter;")
                           (return))
                        '("run:()V" () nil
                           (goto LABEL::TAG_0)
                           (LABEL::TAG_0 aload_0)
                           (invokevirtual "Job" "incr:()LJob;" 0)
                           (pop)
                           (goto LABEL::TAG_0)))
                     '(REF -1)))))

(defconst *Apprentice-main*
   '((new "Container")
     (dup)
     (invokespecial "Container" "<init>:()V" 0)
     (astore_1)
     (goto LABEL::TAG_0)
     (LABEL::TAG_0 new "Job")
     (dup)
     (invokespecial "Job" "<init>:()V" 0)
     (astore_2)
     (aload_2)
     (aload_1)
     (invokevirtual "Job" "setref:(LContainer;)V" 1)
     (aload_2)
     (invokevirtual "java.lang.Thread" "start:()V" 0)
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
