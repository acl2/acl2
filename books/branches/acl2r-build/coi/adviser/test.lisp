#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
;; test.lisp
;; Jared Davis 

(in-package "ADVISER")
(include-book "adviser")

;; Some primitive tests.  First we set up a predicate to check that all
;; elements of a list are not integerp's.  We then create a membership based
;; strategy to show this.

(defun all-not-integerp (x)
  (if (consp x)
      (if (integerp (car x))
          nil
        (all-not-integerp (cdr x)))
    t))

(defthm integerp-when-member-of-all-not-integerp
  (implies (and (all-not-integerp x)
                (member a x))
           (not (integerp a))))


(encapsulate
 ()
 (encapsulate
  (((all-not-integerp-hyps) => *)
   ((all-not-integerp-term) => *))
  (local (defun all-not-integerp-hyps () nil))
  (local (defun all-not-integerp-term () nil))
  (defthmd all-not-integerp-constraint
    (implies (and (all-not-integerp-hyps)
                  (member all-not-integerp-member (all-not-integerp-term)))
             (not (integerp all-not-integerp-member)))))

 (local (defun which-one? (x)
          (if (consp x)
              (if (integerp (car x))
                  (car x)
                (which-one? (cdr x)))
            nil)))

 (local (defthm lemma
          (equal (not (all-not-integerp x))
                 (and (member (which-one? x) x)
                      (integerp (which-one? x))))))
    
 (defthm all-not-integerp-by-membership-driver
   (implies (all-not-integerp-hyps)
            (all-not-integerp (all-not-integerp-term)))
   :hints(("Goal" 
           :in-theory (disable lemma)
           :use ((:instance all-not-integerp-constraint 
                            (all-not-integerp-member 
                             (which-one? (all-not-integerp-term))))
                 (:instance lemma
                            (x (all-not-integerp-term)))))))
 
 (defadvice not-all-not-integerp-by-membership
   (implies (all-not-integerp-hyps)
            (all-not-integerp (all-not-integerp-term)))
   :rule-classes (:pick-a-point :driver
                                all-not-integerp-by-membership-driver))
)



;; We also introduce a predicate that test whether or not a list contains some
;; member which is an integer, and a membership based strategy for proving that
;; some list satisfies some-integerp.

(defun some-integerp (x)
  (if (consp x)
      (if (integerp (car x))
          t
        (some-integerp (cdr x)))
    nil))

(defthm integerp-when-member-of-not-some-integerp
  (implies (and (not (some-integerp x))
                (member a x))
           (not (integerp a))))

(encapsulate
 ()
 (encapsulate
  (((some-integerp-hyps) => *)
   ((some-integerp-term) => *))
  (local (defun some-integerp-hyps () nil))
  (local (defun some-integerp-term () nil))
  (defthmd not-some-integerp-constraint
    (implies (and (some-integerp-hyps)
                  (member some-integerp-member (some-integerp-term)))
             (not (integerp some-integerp-member)))))

 (local (defun which-one? (x)
          (if (consp x)
              (if (integerp (car x))
                  (car x)
                (which-one? (cdr x)))
            nil)))

 (local (defthm lemma
          (equal (some-integerp x)
                 (and (member (which-one? x) x)
                      (integerp (which-one? x))))))
    
 (defthm not-some-integerp-by-membership-driver
   (implies (some-integerp-hyps)
            (not (some-integerp (some-integerp-term))))
   :hints(("Goal" 
           :use (:instance not-some-integerp-constraint 
                           (some-integerp-member 
                            (which-one? (some-integerp-term)))))))
 
 (defadvice not-some-integerp-by-membership
   (implies (some-integerp-hyps)
            (not (some-integerp (some-integerp-term))))
   :rule-classes (:pick-a-point :driver
                                not-some-integerp-by-membership-driver))
)


;; We can now conclude, without inducting over the definitions of
;; all-not-integerp and some-integerp, that these ideas are actually opposites
;; of one another.

(in-theory (disable all-not-integerp some-integerp))

(defthm lemma1
  (implies (all-not-integerp x)
           (not (some-integerp x))))

(defthm lemma2
  (implies (not (some-integerp x))
           (all-not-integerp x)))

(defthm conclusion
  (equal (some-integerp x)
         (not (all-not-integerp x))))

  
  
