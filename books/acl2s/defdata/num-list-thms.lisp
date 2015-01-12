#|$ACL2s-Preamble$;
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "../portcullis")
(acl2::begin-book);$ACL2s-Preamble$|#

(in-package "DEFDATA")

(include-book "num-list-fns")

(defthm pos-list--first
  (implies (and (pos-listp l)
                (consp l))
           (< 0 (car l)))
  :rule-classes (:linear :rewrite))

(defthm sum-list-poses-type
  (implies (and (pos-listp l)
                (consp l))
           (< 0 (sum-list l)))
  :rule-classes (:linear :rewrite))

(defthm sum-list-nats-type
  (implies (nat-listp l)
           (<= 0 (sum-list l)))
  :rule-classes (:linear :rewrite))

(defthm sum-list-integers-type
  (implies (integer-listp l)
           (integerp (sum-list l)))
  :rule-classes (:rewrite :type-prescription))

(defthm sum-list-rationals-type
  (implies (rational-listp l)
           (rationalp (sum-list l)))
  :rule-classes (:rewrite :type-prescription))

(defthm sum-list>=element
  (implies (and (nat-listp l)
                (consp l))
           (>= (sum-list l) (car l)))
  :rule-classes (:rewrite :linear))

(defthm sum-list--append
  (equal (sum-list (append x y))
         (+ (sum-list x) (sum-list y))))


(encapsulate nil
  (local (include-book "arithmetic-5/top" :dir :system))

  (local (SET-DEFAULT-HINTS '((acl2::NONLINEARP-DEFAULT-HINT
                               acl2::STABLE-UNDER-SIMPLIFICATIONP
                               acl2::HIST 
                               acl2::PSPV))))
  
  (defthm product-list-poses-type
    (implies (pos-listp l)
             (< 0 (product-list l)))
    :rule-classes (:linear :rewrite))
  
  (defthm product-list-nats-type
    (implies (nat-listp l)
             (<= 0 (product-list l)))
    :rule-classes (:linear :rewrite))
  
  (defthm product-list-integers-type
    (implies (integer-listp l)
             (integerp (product-list l)))
    :rule-classes (:rewrite :type-prescription))
  
  (defthm product-list-rationals-type
    (implies (rational-listp l)
             (rationalp (product-list l)))
    :rule-classes (:rewrite :type-prescription))
  
  (defthm product-list>=element
    (implies (and (pos-listp l)
                  (consp l))
             (>= (product-list l) (car l)))
    :rule-classes (:rewrite :linear))

  (defthm product-list--append
    (equal (product-list (append x y))
           (* (product-list x) (product-list y)))))


(defthm max-nat-list<=sum-list
  (implies (nat-listp l)
           (<= (max-nat-list l) (sum-list l)))
  :rule-classes (:linear :rewrite))

(defthm max-nat-list>=element
  (implies (and (nat-listp l)
                (consp l))
           (>= (max-nat-list l) (car l)))
  :rule-classes (:linear :rewrite))

(defthm max-nat-list--nat-listp
  (implies (nat-listp l)
           (integerp (max-nat-list l)))
  :rule-classes (:type-prescription :rewrite))

(defthm max-nat-list--nat-listp2
  (implies (nat-listp l)
           (<= 0 (max-nat-list l)))
  :rule-classes (:linear :rewrite))



(defthm len=0--not-consp
  (implies (equal (len x) 0)
           (not (consp x))))


(defthm scale--pos-list
  (implies (and (pos-listp l)
                (integerp x)
                (< 0 x))
           (pos-listp (scale l x)))
  :rule-classes (:type-prescription :rewrite))

(defthm scale--nat-list
  (implies (and (nat-listp l)
                (integerp x)
                (<= 0 x))
           (nat-listp (scale l x)))
  :rule-classes (:type-prescription :rewrite))

(defthm scale--integer-list
  (implies (and (integer-listp l)
                (integerp x))
           (integer-listp (scale l x)))
  :rule-classes (:type-prescription :rewrite))

(defthm scale--rational-list
  (implies (and (rational-listp l)
                (rationalp x))
           (rational-listp (scale l x)))
  :rule-classes (:type-prescription :rewrite))

(defthm scale--number-list
  (implies (and (acl2-number-listp l)
                (acl2-numberp x))
           (acl2-number-listp (scale l x)))
  :rule-classes (:type-prescription :rewrite))

(defthm scale--consp
  (implies (consp l)
           (consp (scale l x)))
  :rule-classes (:type-prescription :rewrite))

(defthm scale--len
  (equal (len (scale l x))
         (len l)))


(defthm shift--pos-list
  (implies (and (pos-listp l)
                (integerp x)
                (< 0 x))
           (pos-listp (shift l x)))
  :rule-classes (:type-prescription :rewrite))

(defthm shift--nat-list
  (implies (and (nat-listp l)
                (integerp x)
                (<= 0 x))
           (nat-listp (shift l x)))
  :rule-classes (:type-prescription :rewrite))

(defthm shift--integer-list
  (implies (and (integer-listp l)
                (integerp x))
           (integer-listp (shift l x)))
  :rule-classes (:type-prescription :rewrite))

(defthm shift--rational-list
  (implies (and (rational-listp l)
                (rationalp x))
           (rational-listp (shift l x)))
  :rule-classes (:type-prescription :rewrite))

(defthm shift--number-list
  (implies (and (acl2-number-listp l)
                (acl2-numberp x))
           (acl2-number-listp (shift l x)))
  :rule-classes (:type-prescription :rewrite))

(defthm shift--consp
  (implies (consp l)
           (consp (shift l x)))
  :rule-classes (:type-prescription :rewrite))

(defthm shift--len
  (equal (len (shift l x))
         (len l)))

#|
(defthm pow--pos-list
  (implies (and (pos-listp l)
                (integerp x)
                (<= 0 x))
           (pos-listp (pow l x)))
  :rule-classes (:type-prescription :rewrite))

(defthm pow--nat-list
  (implies (and (nat-listp l)
                (integerp x)
                (<= 0 x))
           (nat-listp (pow l x)))
  :rule-classes (:type-prescription :rewrite))

(defthm pow--integer-list
  (implies (and (integer-listp l)
                (integerp x)
                (<= 0 x))
           (integer-listp (pow l x)))
  :rule-classes (:type-prescription :rewrite))

(defthm pow--rational-list
  (implies (and (rational-listp l)
                (integerp x)
                (<= 0 x))
           (rational-listp (pow l x)))
  :rule-classes (:type-prescription :rewrite))

(defthm pow--number-list
  (implies (and (acl2-number-listp l)
                (integerp x)
                (<= 0 x))
           (acl2-number-listp (pow l x)))
  :rule-classes (:type-prescription :rewrite))

(defthm pow--consp
  (implies (consp l)
           (consp (pow l x)))
  :rule-classes (:type-prescription :rewrite))

(defthm pow--len
  (equal (len (pow l x))
         (len l)))
|#

(defthm list-expt--number-list
  (implies (and (acl2-number-listp l)
                (integerp x)
                (<= 0 x))
           (acl2-number-listp (list-expt x l)))
  :rule-classes (:type-prescription :rewrite))

(defthm list-expt--consp
  (implies (consp l)
           (consp (list-expt x l)))
  :rule-classes (:type-prescription :rewrite))

(defthm list-expt--len
  (equal (len (list-expt x l))
         (len l)))


(defthm expt--integer
  (implies (and (integerp x)
                (integerp y)
                (<= 0 y))
           (integerp (expt x y))))

(defthm expt-->=0
  (implies (and (integerp x)
                (< 0 x)
                (integerp y)
                (<= 0 y))
           (< 0 (expt x y)))
  :rule-classes (:rewrite :linear))

(defthm expt--2
  (implies (and (integerp x)
                (<= 0 x)
                (integerp y)
                (< 0 y))
           (<= 2 (expt 2 y))))

(defthm <=-lists--transitive
  (implies (and (<=-lists a b)
                (<=-lists b c))
           (<=-lists a c))
  :rule-classes ((:rewrite :match-free :all)))

(defthm <=-lists--reflexive
  (<=-lists x x))

(defthm all-<=--<=
  (implies (and (all-<= l a)
                (<= a b))
           (all-<= l b)))

(defthm all-<=--nth-<=
  (implies (and (all-<= l v)
                (integerp i)
                (<= 0 i)
                (< i (len l)))
           (<= (nth i l) v)))

(defthm all-<=--car-<=
  (implies (and (all-<= l v)
                (consp l))
           (<= (car l) v)))

(defthm <=-lists--all-<=
  (implies (and (all-<= b x)
                (<=-lists a b))
           (all-<= a x))
  :rule-classes (:rewrite :forward-chaining))

(defthm *-lists-poses-type
  (implies (and (pos-listp l1)
                (pos-listp l2))
           (pos-listp (*-lists l1 l2)))
  :rule-classes (:type-prescription :rewrite))

(defthm *-lists-nats-type
  (implies (and (nat-listp l1)
                (nat-listp l2))
           (nat-listp (*-lists l1 l2)))
  :rule-classes (:type-prescription :rewrite))

(defthm *-lists-integers-type
  (implies (and (integer-listp l1)
                (integer-listp l2))
           (integer-listp (*-lists l1 l2)))
  :rule-classes (:type-prescription :rewrite))

(defthm *-lists-rationals-type
  (implies (and (rational-listp l1)
                (rational-listp l2))
           (rational-listp (*-lists l1 l2)))
  :rule-classes (:type-prescription :rewrite))

(defthm *-lists--len
  (equal (len (*-lists l1 l2))
         (min (len l1) (len l2))))

(defthm +-lists-poses-type
  (implies (and (pos-listp l1)
                (pos-listp l2))
           (pos-listp (+-lists l1 l2)))
  :rule-classes (:type-prescription :rewrite))

(defthm +-lists-nats-type
  (implies (and (nat-listp l1)
                (nat-listp l2))
           (nat-listp (+-lists l1 l2)))
  :rule-classes (:type-prescription :rewrite))

(defthm +-lists-integers-type
  (implies (and (integer-listp l1)
                (integer-listp l2))
           (integer-listp (+-lists l1 l2)))
  :rule-classes (:type-prescription :rewrite))

(defthm +-lists-rationals-type
  (implies (and (rational-listp l1)
                (rational-listp l2))
           (rational-listp (+-lists l1 l2)))
  :rule-classes (:type-prescription :rewrite))

(defthm +-lists--len
  (equal (len (+-lists l1 l2))
         (min (len l1) (len l2))))

(defthm make-list-ac=make-list-logic--lemma
  (equal (append (make-list-logic e n)
                 (cons e l))
         (cons e
               (append (make-list-logic e n)
                       l))))

(defthm make-list-ac=make-list-logic-append
  (equal (make-list-ac n e l)
         (append (make-list-logic e n) l)))

(defthm make-list-ac--to--make-list-logic
  (equal (make-list-ac n e nil)
         (make-list-logic e n)))

(defthm make-list--len
  (implies (and (integerp n)
                (<= 0 n))
           (equal (len (make-list-logic v n))
                  n)))

(defthm make-list--consp
  (implies (and (integerp n)
                (< 0 n))
            (consp (make-list-logic v n)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Subgoal *1/3'" :expand ((make-list-logic v 1)))))

(defthm make-list--nats
  (implies (and (integerp v)
                (<= 0 v))
           (nat-listp (make-list-logic v n)))
  :rule-classes (:rewrite :type-prescription))

(defthm make-list--pos
  (implies (and (integerp v)
                (< 0 v))
           (pos-listp (make-list-logic v n)))
  :rule-classes (:rewrite :type-prescription))

(defthm car--make-list
  (implies (and (integerp n)
                (< 0 n))
           (equal (car (make-list-logic v n))
                  v))
  :hints (("Subgoal *1/3'" :expand ((make-list-logic v 1)))))

(defthm cdr--make-list
  (implies (and (integerp n)
                (< 0 n))
           (equal (cdr (make-list-logic v n))
                  (make-list-logic v (- n 1)))))

(defthm all-<=--make-list
  (equal (all-<= (make-list-logic x n)
                 y)
         (or (zp n)
             (<= x y))))


(defthm pfix--integerp
  (integerp (pfix x))
  :rule-classes (:rewrite :type-prescription))

(defthm pfix>=1
  (<= 1 (pfix x))
  :rule-classes (:rewrite :linear))

(defthm pfix=
  (implies (and (integerp x)
                (< 0 x))
           (equal (pfix x)
                  x)))

(in-theory (disable pfix))

(defthm pos-list-fix--pos-listp
  (pos-listp (pos-list-fix x)))

;unfortunate
(defthm pos-list-fix--nat-listp
  (nat-listp (pos-list-fix x)))

;unfortunate
(defthm pos-list-fix--integer-listp
  (integer-listp (pos-list-fix x)))

;unfortunate
(defthm pos-list-fix--rational-listp
  (rational-listp (pos-list-fix x)))


(defthm pos-list-fix--pos-list
  (implies (pos-listp x)
           (equal (pos-list-fix x)
                  x)))

(defthm pos-list-fix--len
  (equal (len (pos-list-fix x))
         (len x)))

(defthm pos-list-fix--cons
  (implies (consp x)
           (equal (car (pos-list-fix x))
                  (pfix (car x)))))

(defthm pos-list-fix--cdr
  (equal (cdr (pos-list-fix x))
         (pos-list-fix (cdr x))))

(defthm pos-list-fix--consp
  (equal (consp (pos-list-fix x))
         (consp x)))

(in-theory (disable pos-list-fix))#|ACL2s-ToDo-Line|#
