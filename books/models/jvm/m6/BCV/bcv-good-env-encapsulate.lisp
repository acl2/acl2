(in-package "BCV")
(include-book "typechecker")
(include-book "typechecker-ext")
(include-book "typechecker-simple")
(include-book "../M6-DJVM-shared/jvm-bytecode")
(include-book "bcv-functions")


;----------------------------------------------------------------------



(encapsulate
  (((good-env *) => *)
   ((icl-witness *) => *))
 
   (local 
    (defun good-env (env)
      (declare (ignore env))
      nil))

   (local 
    (defun icl-witness (env)
      (declare (ignore env))
      nil))

;;;  We can provide real definitions for 
;;;  good-frame and good-typelist 
;;;
;;;  So one only need to convince ourselves the existance of good-env and
;;;  icl-witness!! 


   (defun good-typelist (l env)
     (let ((icl (icl-witness env)))
       (if (endp l) t
         (and (good-bcv-type (car l) icl)
              (good-typelist (cdr l) env)))))
   
   (defun good-frame (frame env)
     (and (good-typelist (framelocals frame) env)
          (good-typelist (framestack frame) env)))
   

   (defthm good-env-ipmlies-good-scl
     (implies (good-env env)
              (good-scl (classtableEnvironment env))))


   (defthm good-env-implies-good-icl-icl-witness
     (implies (good-env env)
              (good-icl (icl-witness env))))


   (defthm good-env-implies-icl-scl-compatible
     (implies (good-env env)
              (icl-scl-compatible (icl-witness env)
                                  (classtableEnvironment env))))

   (defthm good-frame-sig-do-inst-1
     (implies (and (good-env env)
                   (good-frame frame env))
              (good-frame (car (sig-do-inst any env frame))
                          env)))

   
   (defthm good-frame-sig-do-inst-2
     (implies (and (good-env env)
                   (good-frame frame env))
              (good-frame (mv-nth 1 (sig-do-inst any env frame))
                          env))))

;
;
;----------------------------------------------------------------------

