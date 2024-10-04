(in-package "BCV")
(include-book "../DJVM/consistent-state-strong")
(include-book "../DJVM/consistent-state-to-sig-state")
(include-book "../BCV/typechecker")
(include-book "../BCV/typechecker-ext")
(include-book "../BCV/typechecker-simple")
(include-book "../BCV/bcv-functions")

(encapsulate
  (((good-scl-strong *) => *)
   ((good-static-frame * *) => *)
   ((icl-witness-x *) => *))
 
   (local 
    (defun good-scl-strong (scl)
      (declare (ignore scl))
      nil))

   (local 
    (defun icl-witness-x (scl)
      (declare (ignore scl))
      nil))


   (local 
    (defun good-static-frame (frame scl)
      (declare (ignore frame scl))
      nil))


   (defthm good-scl-strong-icl-witness-x
     (implies (good-scl-strong scl)
              (good-icl (icl-witness-x scl))))
              

   (defthm if-scl-icl-scl-compatible
     (implies (good-scl-strong scl)
              (icl-scl-compatible (icl-witness-x scl)
                                  (scl-jvm2bcv scl))))
   

   (defthm consistent-sig-stack-if-good-static-frame
     (implies (and (good-scl-strong scl)
                   (good-static-frame frame scl))
              (consistent-sig-stack
               (frameStack frame)
               (icl-witness-x scl))))


   (defthm consistent-state-strong-implies-good-static-frame
     (implies (and (djvm::consistent-state-strong s)
                   (good-scl-strong (djvm::env-class-table (djvm::env s))))
              (good-static-frame 
               (djvm::frame-sig (djvm::current-frame s)
                          (djvm::instance-class-table s)
                          (djvm::heap s)
                          (djvm::heap-init-map (djvm::aux s)))
               (djvm::env-class-table (djvm::env s)))))


   (defthm consistent-state-strong-implies-good-static-frame-2
     (implies (and (djvm::consistent-state-strong s)
                   (good-scl-strong (djvm::env-class-table (djvm::env s)))
                   (car (jvm::class-by-name-s classname 
                                               (SCL-JVM2BCV
                                                (djvm::env-class-table (djvm::env s)))))
                   
                   (car (jvm::method-by-name-s 
                         method-name 
                         args 
                         returntype (jvm::methods-s (mv-nth 1 (jvm::class-by-name-s
                                                               classname 
                                                               (scl-jvm2bcv (djvm::env-class-table 
                                                                             (djvm::env s))))))))
                   
                   (bcv-simple-method 
                    (mv-nth 1 
                            (jvm::class-by-name-s 
                             classname
                             (scl-jvm2bcv (djvm::env-class-table (djvm::env
                                                                  s)))))
                    (mv-nth 1 (jvm::method-by-name-s 
                               method-name 
                               args 
                               returntype (methods-s (mv-nth 1 (jvm::class-by-name-s
                                                                classname 
                                                                (scl-jvm2bcv (djvm::env-class-table 
                                                                              (djvm::env s))))))))
                    stack-maps
                    (scl-jvm2bcv (djvm::env-class-table (djvm::env s))))
                   (searchStackFrame pc (stack-map-wrap stack-maps)))
              (good-static-frame 
                   (searchStackFrame pc (stack-map-wrap stack-maps))
                   (scl-jvm2bcv (djvm::env-class-table (djvm::env s)))))))




                   
                   
              
                   
              


