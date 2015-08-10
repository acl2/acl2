(in-package "BAG")

;;This book deals with two-level bags (bags which contain bags).

(include-book "bind-free-rules")



(defund any-subbagp (term list)
  (declare (type t term list))
  (if (consp list)
      (or (subbagp term (car list))
	  (any-subbagp term (cdr list)))
    nil))

(defund flat (zlist)
  (if (consp zlist)
      (append (car zlist)
	      (flat (cdr zlist)))
    nil))

(defthm true-listp-flat
  (true-listp (flat list))
  :hints (("Goal" :in-theory (enable flat))))

(defthm flat-append
  (equal (flat (append x y))
	 (append (flat x) (flat y)))
  :hints (("goal" :in-theory (enable binary-append flat))))

(defthm flat-of-non-consp-cheap
  (implies (not (consp x))
           (equal (flat x)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable flat))))

(defthm flat-of-singleton
  (equal (flat (cons x nil))
         (list-fix x))
  :hints (("Goal" :in-theory (enable flat list-fix))))

(defthmd flat-of-cons
  (equal (flat (cons a x))
         (append a (flat x)))
  :hints (("Goal" :in-theory (enable flat))))

;could we just say that TERM is disjoint from (flat LIST) ?
(defund disjoint-list (term list)
  (declare (type t term list))
  (if (consp list)
      (and (disjoint term (car list))
	   (disjoint-list term (cdr list)))
    t))

;disable?
;rename?
(defthm not-consp-disjoint-list
  (implies (not (consp list))
	   (disjoint-list x list))
  :hints (("goal" :in-theory (enable disjoint-list flat))))

(defthm open-disjoint-list
  (and
   (equal (disjoint-list term (cons entry rest))
	  (and (disjoint term entry)
	       (disjoint-list term rest)))
   (equal (disjoint-list term nil) t))
  :hints (("Goal" :in-theory (enable disjoint-list))))

(defthm any-subbagp-implies-subbagp-flat
  (implies (any-subbagp term list)
           (subbagp term (flat list)))
  :rule-classes (:rewrite :forward-chaining)
  :hints (("Goal" :in-theory (enable flat any-subbagp))))

(defthm disjoint-list-implies-disjoint-flat
  (implies (disjoint-list term list)
	   (disjoint term (flat list)))
  :rule-classes (:rewrite :forward-chaining)
  :hints (("Goal" :in-theory (enable flat))))

;BOZO
(defthm memberp-implies-subbagp-flat
  (implies (memberp x xx)
           (subbagp x (flat xx)))
  :hints (("goal" :in-theory (enable memberp flat))))

;eric's version:
;rename
(defthm subbagp-append-reduction
  (implies (memberp sblk list)
           (equal (subbagp sblk (append x (flat list)))
                  t))
  :hints (("goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (memberp) (CONS-CAR-ONTO-REMOVE-1-OF-CDR ;why?
                                             )))))

#|
(thm
 (implies (memberp x1 y)
          (perm (append x1 (flat (remove-1 x1 y)))
                (flat y)))
 :hints (("Goal" :do-not '(generalize eliminate-destructors)
          :in-theory (e/d (memberp remove-1 perm) (append))))
 )
|#



;bozo
(defthm flat-perm
  (implies (perm x y)
           (equal (perm (flat x) (flat y))
                  t))
  :hints (("goal" :in-theory (enable perm memberp remove-1 flat))))

(defcong perm perm (flat x) 1)

(defthm disjoint-list-reduction
  (equal (disjoint-list x list)
         (disjoint x (flat list)))
  :hints (("goal" :in-theory (enable disjoint-list flat))))


;bozo
(defthm flat-remove-1
  (implies (memberp x y)
           (perm (flat (remove-1 x y))
                 (remove-bag x (flat y))))
  :hints (("goal" :in-theory (enable memberp-of-cons remove-bag remove-1 flat)
           :induct (remove-1 x y))))

(defthm subbagp-flat-backchain
  (implies (subbagp f1 f2)
           (subbagp (flat f1) (flat f2)))
  :otf-flg t
  :hints (("goal" :do-not '(generalize eliminate-destructors)
;           :do-not-induct t
;           :induct (REMOVE-BAG F2 F1)
           :in-theory (e/d (subbagp
                            remove-bag flat)
                           (;SUBBAGP-OF-REMOVE-1-BOTH
                            SUBBAGP-CDR-REMOVE-1-REWRITE
                            ;SUBBAGP-APPEND-2
                            )))))

(defthm flat-remove-bag
  (implies (subbagp x y)
           (perm (flat (remove-bag x y))
                 (remove-bag (flat x) (flat y))))
  :hints (("Goal" :in-theory (enable flat remove-bag
                                     ))))

(defthmd disjoint-of-flat-helper
  (implies (memberp lst lst-of-lsts)
           (equal (disjoint (flat lst-of-lsts) lst)
                  (not (consp lst))
                  ))
  :hints (("Goal"
           :do-not '(generalize eliminate-destructors))))

(defthmd disjoint-of-flat-helper-2
  (implies (memberp lst lst-of-lsts)
           (equal (disjoint lst (flat lst-of-lsts))
                  (not (consp lst))
                  ))
  :hints (("Goal" :in-theory (disable disjoint-of-flat-helper)
           :use  disjoint-of-flat-helper
           :do-not '(generalize eliminate-destructors))))

;yuck?
;bozo name should mention flat
(defthmd subbagp-membership-fwd ;trying disabled..
  (implies (memberp x list1)
           (subbagp x (flat list1)))
  :rule-classes (:forward-chaining))



#|

(DEFTHM APPEND-of-flat-and-flat
  (EQUAL (APPEND (FLAT X) (FLAT Y))
         (FLAT (APPEND X Y)))
  :HINTS
  (("goal" :IN-THEORY (ENABLE BINARY-APPEND))))

(in-theory (disable flat-append))

(theory-invariant (incompatible (:rewrite flat-append)
                                (:rewrite APPEND-of-flat-and-flat)))

(encapsulate
 ()

(local
  (encapsulate
   ()

   (defthmd unique-subbagps-not-subbagps
     (implies (and (unique list)
                   (unique-subbagps x y list))
              (equal (subbagp x y)
                   (not (consp x))))
     :rule-classes (:rewrite :forward-chaining)
     :hints (("goal" :in-theory (enable disjoint-subbagp-rewrite)
              :use (:instance *trigger*-unique-subbagps-implies-disjointness
                              (x x)
                              (y y)
                              (list list)))))

   (defthmd subbagp-membership-free
     (implies (and (memberp x list1)
                   (equal list2 (flat list1)))
              (subbagp x list2)))

   (defthm memberp-unique-subbagps
     (implies (and (memberp x y)
                   (consp x)
                   (unique-subbagps x (flat y) list))
              (not (unique list)))
     :hints (("goal" :use (:instance unique-subbagps-not-subbagps
				     (y (flat y))))))

   ))

|#

(defthm any-subbagp-subbagp
  (implies (and (any-subbagp pair list)
                (subbagp x pair))
           (any-subbagp x list))
  :hints (("goal" :in-theory (enable any-subbagp SUBBAGP-CHAINING))))

(defthm disjoint-list-append-reduction
  (equal (disjoint-list (append x y) list)
         (and (disjoint-list x list)
              (disjoint-list y list)))
  :hints (("goal" :in-theory (enable ;disjoint-of-append
;disjoint-list-reduction
                              ))))

;yuck?
;add flat to name
(defthmd memberp-not-disjoint-free
  (implies (and (memberp x list1)
                (consp x)
                (subbagp (flat list1) list2))
           (equal (disjoint x list2)
                  nil))
  :hints (("Goal" :use (:instance DISJOINT-OF-FLAT-HELPER-2 (lst x) (lst-of-lsts list1)))))


(defthm disjoint-from-disjoint-of-flat-one
  (implies (and (disjoint x (flat a))
                (memberp y a))
           (equal (disjoint x y)
                  t)))

(defthm disjoint-from-disjoint-of-flat-two
  (implies (and (disjoint y (flat a))
                (memberp x a))
           (equal (disjoint x y)
                  t)))

(defthm disjoint-from-disjoint-of-flat-three
  (implies (and (disjoint (flat a) x)
                (memberp y a))
           (equal (disjoint x y)
                  t)))

(defthm disjoint-from-disjoint-of-flat-four
  (implies (and (disjoint (flat a) y)
                (memberp x a))
           (equal (disjoint x y)
                  t)))

