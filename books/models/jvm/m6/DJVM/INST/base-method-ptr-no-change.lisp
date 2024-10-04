(in-package "DJVM")
(include-book "base")
(include-book "base-locals")

(encapsulate () 
  (local (include-book "base-consistent-state-more"))
  (defthm method-ptr-no-change-pushStack 
    (equal (method-ptr (current-frame (pushStack v s)))
           (method-ptr (current-frame s))))

  (defthm method-ptr-no-change-popStack
    (equal (method-ptr (current-frame (popStack s)))
           (method-ptr (current-frame s)))))


(encapsulate () 
   (local (include-book "base-state-set-local-at"))
   (DEFTHM
     STATE-SET-LOCAL-AT-METHOD-PTR-EFFECT
     (EQUAL
      (METHOD-PTR (CURRENT-FRAME (STATE-SET-LOCAL-AT I ANY S)))
      (METHOD-PTR (CURRENT-FRAME S))))

   (defthm  METHOD-PTR-INVALIDATE-CATEGORY2-VALUE
     (EQUAL
      (METHOD-PTR
       (CURRENT-FRAME (INVALIDATE-CATEGORY2-VALUE ANY S)))
      (METHOD-PTR (CURRENT-FRAME S)))))


(encapsulate () 
   (local (include-book "base-skip-proofs"))
   (defthm method-ptr-no-change-after-raise-exception
     (equal (METHOD-PTR
             (CURRENT-FRAME (RAISE-EXCEPTION any S)))
            (METHOD-PTR (CURRENT-FRAME S)))))



