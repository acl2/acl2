(in-package "HANOI")

(acl2::set-verify-guards-eagerness 2)

(include-book "basic")

(defun mem (e x)
  (if (consp x)
      (if (equal e (car x))
          x
        (mem e (cdr x)))
    nil))


(defun del (e x)
  (if (consp x)
      (if (equal e (car x))
          (cdr x)
        (cons (car x) (del e (cdr x))))
    nil))

(defun perm (x y)
  (if (consp x)
      (and (mem (car x) y)
           (perm (cdr x)
                 (del (car x) y)))
    (not (consp y))))



(encapsulate ()
   (local (encapsulate ()
            (defthm mem-del
              (implies (not (mem v1 x))
                       (not (mem v1 (del v2 x)))))

            (defthm mem-perm
              (IMPLIES (AND (perm x y)
                            (mem v x))
                       (mem v y))
              :hints (("Goal" :do-not '(generalize))))

            (defthm mem-del2
              (implies (and (mem v1 x)
                            (not (equal v2 v1)))
                       (mem v1 (del v2 x))))

            (defthm del-del-norm
              (equal (DEL Y (DEL X Z))
                     (del x (del y z))))
 

            (defthm perm-del
              (implies (perm x y)
                       (perm (del v x)
                             (del v y)))
              :hints (("Goal" :do-not '(generalize))))

            (defthm perm-transitive
              (implies (and (perm x y)
                            (perm y z))
                       (perm x z)))

            (defthm perm-reflexive
              (perm x x))

            (defthm perm-cons
              (IMPLIES (mem v x)
                       (equal (PERM X (CONS v y))
                              (perm (del v x) y)))
              :hints (("Goal" :induct (perm x y))))

            (defthm perm-commutitive
              (implies (perm y x)
                       (perm x y))
              :hints (("Goal" :do-not '(generalize))))))
   
   (defequiv perm))

;----------------------------------------------------------------------

(encapsulate () 
  (local (encapsulate ()
     (defthmd mem-app-cons
       (mem v (app l1 (cons v l2))))

     (defthmd perm-app-del
       (perm (del v (app l1 (cons v l2)))
             (app l1 l2))
       :hints (("Goal" :do-not '(generalize)
                :in-theory (enable mem-app-cons))))

     (defthmd perm-app-comm
       (perm (app l2 l1)
             (app l1 l2))
       :hints (("Goal" :do-not '(generalize)
                :in-theory (enable mem-app-cons
                                   perm-app-del))))

     (defthmd perm-app-assoc
       (perm (app (app l1 l2) l3)
             (app l1 (app l2 l3)))
       :hints (("Goal" :do-not '(generalize))))


     (defthmd perm-app-reduce-1
       (equal (perm (app l1 l3)
                    (app l1 l2))
              (perm l3 l2)))


     (defthmd app-app-swap-lema
       (PERM (APP L (APP L1 L2))
             (APP L1 (APP L L2)))
       :hints (("Goal" 
                :in-theory (e/d (perm-app-assoc
                                 perm-app-comm
                                 perm-app-reduce-1)
                                (perm app))
                :use ((:instance perm-app-comm
                                 (l2 l1)
                                 (l1 (app l l2)))))))


     (defthmd perm-app-reduce-2
       (equal (perm (app l1 (app l l2))
                    (app s1 (app l s2)))
              (perm (app l1 l2)
                    (app s1 s2)))
       :hints (("Goal" 
                :do-not '(generalize)
                :do-not-induct t
                :in-theory (e/d (perm-app-comm
                                 perm-app-assoc
                                 app-app-swap-lema
                                 perm-app-reduce-1)
                                (perm))
                :cases ((not (and  (perm (app l (app l1 l2))
                                         (app l1 (app l l2)))
                                   (perm (app l (app s1 s2))
                                         (app s1 (app l s2)))))))))
                        

     (defthmd perm-app-cons-norm-lemma
        (equal (perm (cons v l2)
                     (cons v l1))
               (perm l2 l1)))

     (defthmd perm-app-cons-norm-0
       (perm (cons v (app l1 l2))
             (app l1 (cons v l2))))

     (defthmd perm-app-cons-norm-1
        (equal (perm (app l1 (cons v l2))
                     (cons v l))
               (perm (app l1 l2)
                     l))
        :hints (("Goal" 
                 :do-not '(generalize)
                 :do-not-induct t
                 :in-theory (e/d (perm-app-cons-norm-lemma) 
                                 (perm))
                 :use ((:instance perm-app-comm
                                  (l2 l1)
                                  (l1 (cons v l2)))
                       (:instance perm-app-comm
                                  (l2 l1)
                                  (l1 l2))))))))


  (defthmd perm-app-reduce-1
    (equal (perm (app l1 l3)
                 (app l1 l2))
           (perm l3 l2)))

  (defthmd perm-app-reduce-2
    (equal (perm (app l1 (app l l2))
                 (app s1 (app l s2)))
           (perm (app l1 l2)
                 (app s1 s2))))
  
  (defthmd perm-app-comm
       (perm (app l2 l1)
             (app l1 l2))
       :hints (("Goal" :do-not '(generalize)
                :in-theory (enable mem-app-cons
                                   perm-app-del))))

   (defthmd perm-app-assoc
       (perm (app (app l1 l2) l3)
             (app l1 (app l2 l3)))
       :hints (("Goal" :do-not '(generalize))))


   (defthmd perm-app-cons-norm-0
       (perm (cons v (app l1 l2))
             (app l1 (cons v l2))))

   (defthmd perm-app-cons-norm-1
     (equal (perm (app l1 (cons v l2))
                  (cons v l))
            (perm (app l1 l2)
                  l))))
                             
