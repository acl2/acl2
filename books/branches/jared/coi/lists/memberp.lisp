#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
;; memberp.lisp
;; The memberp function and theorems about it

(in-package "LIST")
(include-book "basic")



;; We'll use MEMBERP instead of MEMBER in our reasoning from now on.  (Since
;; MEMBER doesn't always return a boolean, many of its rules must be IFF
;; rules. Since MEMBERP always returns a boolean, the analogous rules for it
;; can be EQUAL rules.)

(defund memberp (a x)
  (declare (type t a x))
  (if (consp x)
      (if (equal a (car x)) 
          t
        (memberp a (cdr x)))
    nil))



;; Make sure memberp's :type-prescription rule is as strong as we think.  Don't
;; remove this just because its has no effect on the world.

(local 
 (encapsulate
  ()
  (local (defthm memberp-type-prescription-test
           (or (equal (memberp a x) t)
               (equal (memberp a x) nil))
           :rule-classes nil
           :hints (("Goal" 
                    :in-theory (union-theories '((:type-prescription memberp))
                                               (theory 'minimal-theory))))))))



;; There are several functions similar to our memberp.  We rewrite all of the
;; others to ours (when they're used in a propositional context).
;;
;; Note: There was once some question as to whether or not having these rules
;; is a good idea.  But, I think we can make a strong case for preferring this
;; approach.  In particular, without these rules, we have many different
;; versions of the same function.  And, as a result, we would have to prove the
;; same theorems over and over in different equivalence contexts for each of
;; the different names.  It's quite likely that we would eventually forget one
;; and so forth.  By preferring memberp everywhere, we only need to write our
;; theorems about one function symbol.

(defthm member-is-memberp-propositionally
  (iff (member a x)
       (memberp a x))
  :hints(("Goal" :in-theory (enable memberp))))

(defthm member-equal-is-memberp-propositionally
  (iff (member-equal a x)
       (memberp a x))
  :hints(("Goal" :in-theory (enable memberp))))

(defthm member-eq-is-memberp-propositionally
  (iff (member-eq a x)
       (memberp a x))
  :hints(("Goal" :in-theory (enable memberp))))

(defthm member-implies-memberp
  (implies
   (member a x)
   (memberp a x))
  :rule-classes (:forward-chaining))

(defthm member-equal-implies-memberp
  (implies
   (member-equal a x)
   (memberp a x))
  :rule-classes (:forward-chaining))

(defthm member-eq-implies-memberp
  (implies
   (member-eq a x)
   (memberp a x))
  :rule-classes (:forward-chaining))

(in-theory (disable member member-equal member-eq))

;; jcd - i think this should be enabled
(defthmd memberp-of-non-consp
  (implies (not (consp x))
           (equal (memberp a x)
                  nil))
  :hints (("Goal" :in-theory (enable memberp))))

;; jcd - i think memberp-of-non-consp should be enabled instead
(defthm memberp-of-non-consp-cheap
  (implies (not (consp x))
           (equal (memberp a x)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable memberp))))

;; jcd - i think memberp-of-non-consp should be enabled instead
(defthm memberp-of-nil
  (equal (memberp a nil) 
         nil)
  :hints (("goal" :in-theory (enable memberp))))

;; jcd - I don't see where it is disabled
;later disabled, since it introduces an IF
(defthm memberp-of-cons
  (equal (memberp a (cons b x))
         (if (equal a b)
             t
           (memberp a x)))
  :hints (("Goal" :in-theory (enable memberp))))

;; jcd - i think this is redundant
;non -cheap version?
(defthm memberp-of-cons-irrel
  (implies (not (equal a b))
           (equal (memberp a (cons b x))
                  (memberp a x)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable memberp))))

;; jcd - i think this is redundant
;non -cheap version?
(defthm memberp-of-cons-reduce-cheap
  (implies (not (memberp a x))
           (equal (memberp a (cons b x))
                  (equal b a)))
  :rule-classes ((:rewrite :backchain-limit-lst 0))
  :hints (("Goal" :in-theory (enable memberp))))

;When a and b are constants, the if test should always get resolved.
;So we probably always want this rule enabled. -ews
(defthm memberp-of-cons-cheap
  (implies (syntaxp (and (quotep a)
                         (quotep b)))
           (equal (list::memberp a (cons b x))
                  (if (equal a b)
                      t
                    (list::memberp a x)))))



;; jcd - I think a congruence rule is much better here, so I am eliminating
;; this in favor of a defcong.
;;
;; (defthm memberp-of-fix
;;   (equal (memberp a (fix x))
;;          (memberp a x))
;;   :hints (("Goal" :in-theory (enable memberp fix))))

(defcong equiv equal (memberp a x) 2
  :hints(("Goal" :in-theory (enable memberp)
          :induct (len-len-induction x x-equiv))))



(defthm memberp-car
  (equal (memberp (car x) x)
         (consp x)))



;; jcd - should we try this fc rule instead?
;;
;; (defthm memberp-of-cdr-forward-to-memberp
;;   (implies (memberp a (cdr x))
;;            (memberp a x))
;;   :rule-classes :forward-chaining)

;bzo expensive
;but maybe enable in the naive theory?
(defthmd memberp-of-cdr
  (implies (memberp a (cdr x))
           (memberp a x)))

(defthm memberp-of-cdr-cheap
  (implies (memberp a (cdr x))
           (memberp a x))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))








;; jcd - i don't like these rules and i'm removing them.

(defthmd memberp-when-not-memberp-of-cdr
  (implies (not (memberp a (cdr x)))
           (equal (memberp a x)
                  (if (consp x)
                      (equal a (car x))
                    nil)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :induct t
           :in-theory (enable memberp))))

;could try 0 for the backchain-limit
(defthmd memberp-when-not-memberp-of-cdr-cheap
  (implies (not (memberp a (cdr x)))
           (equal (memberp a x)
                  (if (consp x)
                      (equal a (car x))
                    nil)))
  :rule-classes ((:rewrite :backchain-limit-lst (1))))



;; jcd - try this theorem instead?
;;
;; (defthm member-of-cdr-when-not-car
;;   (implies (and (memberp a x)
;;                 (not (equal (car x) a)))
;;            (memberp a (cdr x))))

;hung on car... hang on (equal (car x) a)??
(defthmd memberp-and-not-cdr-implies-equality
  (implies (and (memberp a x)
                (not (memberp a (cdr x))))
           (equal (car x) a)))




(defthm memberp-of-append
  (equal (memberp a (append x y))
         (or (memberp a x) (memberp a y)))
  :hints (("Goal" :in-theory (enable append))))

;; jcd - this seems redundant
;make -alt version?
(defthmd memberp-of-append-irrel
  (implies (not (memberp a x))
           (equal (memberp a (append x y))
                  (memberp a y))))

;; jcd - this seems redundant
;make -alt version?
(defthm memberp-of-append-irrel-cheap
  (implies (not (memberp a x))
           (equal (memberp a (append x y))
                  (memberp a y)))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))



;; Jared's Additions

(defthm memberp-type-1
  (implies (not (consp x))
           (equal (memberp a x) nil))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable memberp))))

(defthm memberp-of-nthcdr-forward-to-memberp
  (implies (memberp a (nthcdr n x))
           (memberp a x))
  :rule-classes :forward-chaining
  :hints(("Goal" :in-theory (enable nthcdr))))

(defthm member-of-firstn-forward-to-memberp
  (implies (memberp a (firstn n x))
           (memberp a x))
  :rule-classes :forward-chaining
  :hints(("Goal" :in-theory (enable firstn))))

(defthm memberp-from-memberp-of-cdr-cheap
  (implies (list::memberp a (cdr x))
           (list::memberp a x))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

;; Some non-membership stuff (previously in disjoint .. why?)

(encapsulate
 (
  ((non-member *) => *)
  )
 
 (local
  (defun max-member (list)
    (if (consp list)
	(let ((max (max-member (cdr list))))
	  (if (< max (nfix (car list)))
	      (nfix (car list))
	    max))
      0)))

 (local
  (defthm natp-max-member
    (natp (max-member list))))

 (local
  (defthm max-member-bound
    (implies
     (memberp a list)
     (<= (nfix a) (max-member list)))
    :rule-classes (:linear)))

 (local
  (defthm max-member-bound-implication
    (implies
     (< (max-member list) (nfix n))
     (not (memberp n list)))
    :hints (("Goal" :in-theory (disable nfix)))))

 (local
  (defun non-member (list)
    (1+ (max-member list))))
 
 (defthm not-memberp-non-member
   (not (memberp (non-member list) list)))

 )
