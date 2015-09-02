(in-package "LIST")

;hmmmm should which package should these be in?  do we need them
(defmacro cdddddr (x)
  `(cdr (cddddr ,x)))

(defmacro cddddddr (x)
  `(cddr (cddddr ,x)))

(defmacro caddddddr (x)
  `(car (cddddddr ,x)))

(defmacro cadddddr (x)
  `(car (cdddddr ,x)))

(defmacro caddddr (x)
  `(car (cddddr ,x)))

(in-theory (disable append))


(in-theory (disable len))

(defthm len-linear
  (<= 0 (len list))
  :rule-classes (:rewrite :linear))

(defthm len-when-consp-linear
  (implies (consp x)
           (< 0 (len x)))
 :rule-classes :linear
 :hints (("Goal" :in-theory (enable len))))

(defthm len-of-non-consp
  (implies (not (consp x))
           (equal (len x)
                  0))
  :hints (("Goal" :in-theory (enable len))))

(defthm len-equal-0-rewrite
  (equal (equal (len x) 0)
         (not (consp x)))
  :hints (("Goal" :in-theory (enable len))))

(defthm len-pos-rewrite
  (equal (< 0 (len x))
         (consp x))
  :hints (("Goal" :in-theory (enable len))))

(defthm nfix-len
  (equal (nfix (len x))
	 (len x)))

(defun len-len-induction (x y)
  (if (and (consp x)
	   (consp y))
      (len-len-induction (cdr x) (cdr y))
    nil))

;; (defun two-list-induct (l1 l2)
;;   (if (or (endp l1)
;;           (endp l2))
;;       (cons l1 l2)
;;     (two-list-induct (cdr l1) (cdr l2))))

(defthm len-append
  (equal (len (append x y))
	 (+ (len x)
	    (len y)))
  :hints (("goal" :in-theory (enable binary-append len))))

(defthm len-cons
  (equal (len (cons a x))
         (+ 1 (len x)))
  :hints (("Goal" :in-theory (enable len))))

(defthm len-cdr-less-than-len
  (equal (< (len (cdr l)) (len l))
         (consp l)))

(defthm len-not-less-than-len-cdr
  (equal (< (len l) (len (cdr l)))
         nil))



;yuck?
(defthm equal-len-append
  (implies (and (true-listp x)
                (true-listp y)
                (equal (len x)
                       (len y)))
           (equal (equal (append x p)
                         (append y q))
                  (and (equal x y)
                       (equal p q))))
  :hints (("goal" :in-theory (enable binary-append ;yuck?
                                     len ;yuck
                                     )
	   :induct (len-len-induction x y))))

(defthm cdr-does-nothing-rewrite
  (equal (equal x (cdr x))
         (equal x nil))
  :hints (("Goal" :in-theory (disable CAR-CDR-ELIM
                                      acl2::cons-car-cdr ; added for v2-9-3 by Matt K.
;                                      acl2::cons-equal-rewrite
                                      ;EQUAL-CONS-CASES-2
                                      ;EQUAL-TRUE-LIST-CASES
                                      )
           :use (:instance car-cdr-elim (acl2::x x)))))


(defthm equal-car-differential
  (implies (and (not (equal a b))
                (equal (cdr a) (cdr b))
                (consp a)
                (consp b)
                )
           (equal (equal (car a) (car b))
                  nil)))


(defthm true-listp-of-non-consp-cheap
  (implies (not (consp x))
           (equal (true-listp x)
                  (equal nil x)))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

(defthm true-listp-of-cons
  (equal (true-listp (cons a y))
         (true-listp y)))


;;
;;
;; list-fix
;;
;;

;LIST-FIX changes the final cdr of X to be nil.  Many functions which operate on lists (like the bags functions?) don't access
;those final cdrs and so are unaffected if we call list-fix on their arguments.

(defund list-fix (x)
  (declare (type t x))
  (if (consp x)
      (cons (car x) (list-fix (cdr x)))
    nil))

(defthm list-fix-iff
  (iff (list-fix x)
       (consp x))
  :hints (("Goal" :in-theory (enable list-fix))))

(defthm list-fix-of-non-consp
  (implies (not (consp x))
           (equal (list-fix x)
                  nil)))

(defthm list-fix-of-cons
  (equal (list-fix (cons a y))
         (cons a (list-fix y)))
  :hints (("Goal" :in-theory (enable list-fix ))))

(defthm list-fix-of-list-fix
  (equal (list-fix (list-fix x))
         (list-fix x))
  :hints (("Goal" :in-theory (enable list-fix))))

(defthm true-listp-list-fix
  (implies (true-listp x)
           (equal (list-fix x)
                  x))
  :hints (("Goal" :in-theory (enable list-fix))))

(defthm len-of-list-fix
  (equal (len (list-fix x))
	 (len x))
  :hints (("Goal" :in-theory (enable list-fix))))

(defthm consp-of-list-fix
  (equal (consp (list-fix x))
         (consp x))
  :hints (("Goal" :in-theory (enable list-fix))))

(defthm list-fix-does-nothing-rewrite
  (equal (equal x (list-fix x))
         (true-listp x)))

(defthm len-equal-1-rewrite
  (equal (equal (len y) 1)
         (equal (list-fix y) (list (car y))))
  :hints (("Goal" :in-theory (enable len))))

;;
;;
;; append
;;
;;

;append is built in to ACL2.

(defthm car-append
  (equal (car (append x y))
	 (if (consp x)
             (car x)
           (car y)))
  :hints (("goal" :in-theory (enable binary-append))))

(defthm cdr-append
  (equal (cdr (append x y))
	 (if (consp x)
             (append (cdr x) y)
           (cdr y)))
  :hints (("goal" :in-theory (enable binary-append))))

(defthm consp-append
  (equal (consp (append x y))
         (or (consp x) (consp y)))
  :hints (("goal" :in-theory (enable binary-append))))

(defthm append-consp-type-one
  (implies (consp x)
           (consp (append x y)))
    :rule-classes ((:type-prescription)))

(defthm append-consp-type-two
  (implies (consp y)
           (consp (append x y)))
    :rule-classes ((:type-prescription)))


;the -two version of this rule isn't easy to state (if we append x onto a non-consp y, we change the final cdr of x to be y)...
;bozo make it anyway
(defthm append-of-non-consp-one
  (implies (not (consp x))
           (equal (append x y)
                  y))
  :hints (("Goal" :in-theory (enable append))))

(defthm append-of-nil-one
  (equal (append nil x)
         x)
  :hints (("Goal" :in-theory (enable append))))

(defthm append-iff
  (iff (append x y)
       (or (consp x) y))
  :hints (("Goal" :in-theory (enable append))))

(defthm append-of-cons
  (equal (append (cons a x) y)
	 (cons a (append x y))))

(defthm equal-append-x-append-x
  (equal (equal (append x y) (append x z))
         (equal y z))
  :hints (("Goal" :in-theory (enable append))))

;I added the "-better" to the name, because arithmetic/top-with-meta already has a rule called
;append-true-listp-type-prescription.  This rule is better.
(defthm append-true-listp-type-prescription-better
  (implies (true-listp y)
           (true-listp (append x y)))
  :rule-classes (:type-prescription)
  :hints (("Goal" :in-theory (enable append))))

(defthm true-listp-of-append
  (equal (true-listp (append x y))
         (true-listp y))
  :hints (("Goal" :in-theory (enable append))))

;was called append-append-reduction
(defthm append-associative
  (equal (append (append x y) z)
	 (append x (append y z)))
  :hints (("Goal" :in-theory (enable append))))

#|
old:

(defthm append-nil
  (and (implies (true-listp x)
                (equal (append x nil)
                       x))
       (equal (append nil x)
              x))
  :hints (("Goal" :in-theory (enable append))))

;note the fw-chaining??
(defthm true-listp-append-implication
  (implies (true-listp (append x y))
           (true-listp y))
  :hints (("Goal" :in-theory (enable append)))
  :rule-classes (:forward-chaining))

|#


(defthm list-fix-of-append
  (equal (list-fix (append x y))
         (append x (list-fix y)))
  :hints (("Goal" :in-theory (enable list-fix append))))

(defthm append-of-nil-two
  (equal (append x nil)
         (list-fix x))
  :hints (("Goal" :in-theory (enable list-fix))))

;keep talking cdrs of X until we hit an atom.  Return that atom.
;For a true-listp, that atom will be nil.
(defund final-cdr (x)
  (declare (type t x))
  (if (consp x)
      (final-cdr (cdr x))
    x))

;Make sure final-cdr's :type-prescription rule is as strong as we think.
;Don't remove this just because its has no effect on the world.
(encapsulate
 ()
 (local (defthm final-cdr-type-prescription-test
          (not (consp (final-cdr x)))
          :hints (("Goal"   :in-theory (union-theories '(booleanp
                                                       (:type-prescription final-cdr))
                                                     (theory 'minimal-theory)))))))

(defthm final-cdr-when-true-listp
  (implies (true-listp x)
           (equal (final-cdr x)
                  nil))
  :hints (("Goal" :in-theory (enable final-cdr))))

(defthm final-cdr-when-non-consp
  (implies (not (consp x))
           (equal (final-cdr x)
                  x))
  :hints (("Goal" :in-theory (enable final-cdr))))

;a special case of final-cdr-when-true-listp
(defthm final-cdr-of-list-fix
  (equal (final-cdr (list-fix x))
         nil))

;bozo prove more rules about final-cdr?


;yuck?
(defthm final-cdr-when-cdr-not-consp
  (implies (and (consp x) (not (consp (cdr x))))
           (equal (final-cdr x)
                  (cdr x)))
 :hints (("Goal" :in-theory (enable final-cdr))))


(defthm len-fw-to-consp
  (implies (and (equal (len x) a) ;a is a free variable
                (<= 1 a))
           (consp x)))

(defthm final-cdr-of-cdr-when-consp
  (implies (consp y)
           (equal (final-cdr (cdr y))
                  (final-cdr y)))
  :hints (("Goal" :in-theory (enable final-cdr))))

(local (include-book "arithmetic/top-with-meta" :dir :system))

(encapsulate
 ()


 (local (defthm acl2-count-of-append-when-consp
          (implies (consp y)
                   (equal (acl2-count (append y x))
                          (+(- (acl2-count (final-cdr y)))
                            (acl2-count x)
                            (acl2-count y))))
          :hints (("Goal" :do-not '(generalize eliminate-destructors)
                   :in-theory (enable append)))))

 (local (defthm acl2-count-of-append-when-not-consp
          (implies (not (consp y))
                   (equal (acl2-count (append y x))
                          (acl2-count x)))
          :hints (("Goal" :do-not '(generalize eliminate-destructors)
                   :in-theory (enable)))))

 (defthm acl2-count-of-append
   (equal (acl2-count (append y x))
          (if (consp y)
              (+ (- (acl2-count (final-cdr y))) ;or we could replace the first 2 summands with acl2-count of (list-fix y); BOZO lemma about that?
                 (acl2-count y)
                 (acl2-count x)
                 )
            (acl2-count x)))
   :hints (("Goal" :do-not '(generalize eliminate-destructors)
            :in-theory (enable)))))

(defthm acl2-count-of-final-cdr-linear
  (implies (consp y)
           (< (acl2-count (final-cdr y)) (acl2-count y)))
  :rule-classes :linear)

(defthm acl2-count-final-cdr-less-than-acl2-count
  (equal (< (acl2-count (final-cdr y)) (acl2-count y))
         (consp y))
  :hints (("Goal" :in-theory (disable INTEGER-ABS LENGTH))))


;do we need this?
;make a linear rule?
;more like this?
(defthm acl2-count-of-append-increases
  (implies (consp y)
           (< (acl2-count x) (acl2-count (append y x))))
  :hints (("Goal" :in-theory (disable acl2-count))))


;yuck? hung on equal.
(defthmd acl2-count-diff-means-not-equal
  (implies (< (acl2-count x) (acl2-count y))
           (not (equal x y))))

(defthm append-equal-self-one
  (equal (equal x (append x y))
         (equal y (final-cdr x)))
  :hints (("Goal" :in-theory (enable append acl2-count-diff-means-not-equal))))

(defthm append-equal-self-two
  (equal (equal x (append y x))
         (not (consp y)))
  :hints (("Goal" :in-theory (enable acl2-count-diff-means-not-equal))))



;bozo improve eric's stanford libraries with this
(defthm appends-equal
  (equal (equal (append x1 y) (append x2 y))
         (equal (list-fix x1) (list-fix x2)))
  :hints (("Goal" :induct (len-len-induction x1 x2)
           :do-not '(generalize eliminate-destructors)
           :in-theory (enable append list-fix))))




;yuck?
;We don't need this rule if associativity of append is turned on!
(defthm append-equality-cancel
  (equal (equal (append x y)
                (append (append x z) w))
         (equal y (append z w))))



(defthm acl2-count-of-list-fix
  (equal (acl2-count (list-fix x))
         (- (acl2-count x) (acl2-count (final-cdr x))))
  :hints (("Goal" :in-theory (enable list-fix))))


;;merge in the stuff below this better?

(defthm final-cdr-of-cons
  (equal (final-cdr (cons a x))
         (final-cdr x))
  :hints (("Goal" :in-theory (enable final-cdr))))

(defthm final-cdr-does-nothing-rewrite
  (equal (equal (final-cdr x) x)
         (not (consp x))))

(defthm append-equal-list-fix-rewrite
  (equal (equal (append x y) (list-fix x))
         (equal nil y))
  :hints (("Goal" :in-theory (enable append))))


;Two lists are congruent iff they differ only in their final cdrs.
(defund list-cong (x y)
  (declare (type t x y))
  (equal (list-fix x)
         (list-fix y)))

(defequiv list-cong :hints (("Goal" :in-theory (enable list-cong))))

(defthm list-fix-list-cong
  (list-cong (list-fix l)
             l)
  :hints (("Goal" :in-theory (enable list-cong))))

(defthm list-cong-of-non-consp-two
  (implies (not (consp y))
           (equal (list-cong x y)
                  (not (consp x))))
  :hints (("Goal" :in-theory (enable list-cong))))

(defthm list-cong-of-non-consp-one
  (implies (not (consp x))
           (equal (list-cong x y)
                  (not (consp y))))
  :hints (("Goal" :in-theory (enable list-cong))))

(defthm list-cong-of-cdr-and-cdr
  (implies (list-cong x y)
           (equal (list-cong (cdr x) (cdr y))
                  t))
  :hints (("Goal" :in-theory (enable list-cong))))

;could be made more general?
(defthm list-cong-of-append-onto-final-cdr
  (list-cong (append x (final-cdr y))
             x)
  :hints (("Goal" :in-theory (enable list-cong))))

(defthm list-cong-of-append-self-one
 (equal (list-cong (append x y) x)
        (list-cong nil y))
 :hints (("Goal" :in-theory (enable list-cong))))

(defthm list-cong-of-append-self-two
  (equal (list-cong x (append x y))
         (list-cong nil y))
  :hints (("Goal" :in-theory (enable list-cong))))

(defthm list-cong-of-append-self-three
  (equal (list-cong (append y x) x)
         (list-cong nil y))
  :hints (("Goal" :in-theory (enable list-cong))))

(defthm list-cong-of-append-self-four
  (equal (list-cong x (append y x))
         (list-cong nil y))
  :hints (("Goal" :in-theory (enable list-cong))))

(defcong list-cong equal (len x) 1 :hints (("Goal" :in-theory (e/d (list-cong) (list::len-of-list-fix))
                                            :use ((:instance list::len-of-list-fix (list::x x))
                                                  (:instance list::len-of-list-fix (list::x x-equiv))))))

(defcong list-cong equal (append x y) 1 :hints (("Goal" :in-theory (enable list-cong append))))

(defcong list-cong list-cong (append x y) 2 :hints (("Goal" :in-theory (enable list-cong append))))


(defthm list-cong-with-list-fix-two
  (equal (list-cong x (list-fix y))
         (list-cong x y))
  :hints (("Goal" :in-theory (enable list-cong list-fix))))

(defthm list-cong-with-list-fix-one
  (equal (list-cong (list-fix x) y)
         (list-cong x y))
  :hints (("Goal" :in-theory (enable list-cong list-fix))))

;might be expensive?
(defthm list-cong-not-when-lens-differ-one
  (implies (< (len x) (len y))
           (not (list-cong x y))))

;might be expensive?
(defthm list-cong-not-when-lens-differ-two
  (implies (< (len y) (len x))
           (not (list-cong x y))))

;note the list-cong
(defthm append-of-non-consp-2
  (implies (not (consp y))
           (list-cong (append x y)
                      x)))


;;
;; stuff about nthcdr (which is built into ACL2)
;;


(defthm nthcdr-of-0
  (equal (nthcdr 0 x)
         x)
  :hints (("Goal" :in-theory (enable nthcdr))))

(defthm true-listp-of-nthcdr
  (implies (true-listp l)
           (true-listp (nthcdr n l)))
  :hints (("Goal" :in-theory (enable nthcdr))))

;may be too strong?
(defthmd nthcdr-of-cons
  (equal (nthcdr n (cons a x))
         (if (and (integerp n)
                  (< 0 n))
             (nthcdr (+ -1 n) x)
           (cons a x))))

(defthmd nthcdr-of-cons-special-one
  (implies (syntaxp (quotep n))
           (equal (nthcdr n (cons a x))
                  (if (and (integerp n)
                           (< 0 n))
                      (nthcdr (+ -1 n) x)
                    (cons a x)))))

(defthmd nthcdr-of-cons-special-two
  (implies (syntaxp (quotep m))
           (equal (nthcdr (+ m n) (cons a x))
                  (if (and (integerp (+ m n))
                           (< 0 (+ m n)))
                      (nthcdr (+ (+ -1 m) n) x)
                    (cons a x)))))


;(local (include-book "arithmetic/top-with-meta" :dir :system))

(defthm nthcdr-of-len
  (equal (nthcdr (len x) x)
         (final-cdr x))
  :hints (("Goal" :in-theory (enable nthcdr len))))

;yuck?
(defthm nthcdr-of-non-consp
  (implies (not (consp x))
           (equal (nthcdr n x)
                  (if (zp n)
                      x
                    nil)))
  :hints (("Goal" :in-theory (enable nthcdr))))

;more general? nthcdr of append?
(defthm nthcdr-of-len-and-append
  (equal (nthcdr (len p) (append p list))
         list)
  :hints (("Goal" :in-theory (enable nthcdr append))))

(defthm len-of-nthcdr
  (equal (len (nthcdr n l))
         (if (natp n) ;change to use nfxi around n?
             (max 0 (- (len l) n))
           (len l)))
  :otf-flg t
  :hints (("Goal" :in-theory (enable len nthcdr))))

 ;BOZO okay?
(defthm equal-of-booleans-rewrite
  (implies (and (booleanp x)
                (booleanp y))
           (equal (equal x y)
                  (iff x y)))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm consp-of-nthcdr
  (equal (consp (nthcdr n l))
         (< (nfix n) (len l)))
  :hints (("Goal" :in-theory (enable nthcdr))))

(defcong list-cong list-cong (nthcdr n l) 2 :hints (("Goal" :in-theory (enable nthcdr))))

; Do we want to push the list-fix in or pull it out?
(defthm list-fix-of-nthcdr
  (equal (list-fix (nthcdr n l))
         (nthcdr n (list-fix l)))
  :hints (("Goal" :in-theory (enable nthcdr list-fix))))

(defthmd nthcdr-of-list-fix
  (equal (nthcdr n (list-fix p))
         (list-fix (nthcdr n p))))

(defthm nthcdr-of-nthcdr
  (equal (nthcdr n1 (nthcdr n2 l))
         (nthcdr (+ (nfix n1) (nfix n2)) l))
  :hints (("Goal" :in-theory (enable nthcdr))))

(defthm equal-of-list-fixes
  (equal (equal (list::list-fix p) (list::list-fix p2))
         (list::list-cong p p2))
  :hints (("Goal" :in-theory (enable list::list-cong))))

(theory-invariant (incompatible (:rewrite equal-of-list-fixes) (:definition list-cong )))

(defthm list-cong-of-constant
  (implies (and (syntaxp (quotep k))
                (consp k))
           (equal (list::list-cong k x)
                  (and (consp x)
                       (equal (car x) (car k))
                       (list::list-cong (cdr x) (cdr k)))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors preprocess)
           :in-theory (e/d (list::list-cong list::list-fix) (EQUAL-OF-LIST-FIXES)))))

(in-theory (disable nthcdr))

(defthm len-of-cdr-linear
  (implies (consp x)
           (equal (LEN (CDR x)) (+ -1 (len x))))
  :rule-classes :linear)

(defthm list-cong-commutative
  (equal (list::list-cong x y)
         (list::list-cong y x)))

;same as in books/ordinals/ordinal-definitions.lisp and elsewhere in books/?
(DEFUN FIRSTN (N L)
  "The sublist of L consisting of its first N elements."
  (DECLARE (XARGS :GUARD
                  (AND (TRUE-LISTP L)
                       (INTEGERP N)
                       (<= 0 N))))
  (COND ((ENDP L) NIL)
        ((ZP N) NIL)
        (T (CONS (CAR L)
                 (FIRSTN (1- N) (CDR L))))))


(defthm firstn-of-len-and-append-same
  (equal (firstn (len x) (append x y))
         (list::list-fix x))
  :hints (("Goal" :in-theory (enable firstn append))))


(defthmd not-equal-from-len-not-equal
  (implies (not (equal (len x) (len y)))
           (not (equal x y))))



(in-theory (disable firstn))

(defthm len-of-firstn
  (equal (len (firstn n x))
         (min (nfix n) (len x)))
  :hints (("Goal" :in-theory (enable firstn))))

;do we really need this?
(defthm equal-of-if-hack
  (implies (and (not (equal x y))
                (not (equal x z)))
           (equal (equal x (if test y z))
                  nil)))

(defthm equal-of-firstn-and-firstn-same-two-helper
  (implies (and (not (equal n1 n2))
                (integerp n1)
                (integerp n2)
                (<= 0 n1)
                (<= 0 n2))
           (equal (equal (firstn n1 x)
                         (firstn n2 x))
                  (and (equal (firstn (min n1 n2) x)
                              (firstn (min n1 n2) x))
                       (<= (len x) (min n1 n2)))))
  :rule-classes nil
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable firstn))))

(defthm firstn-of-zp
  (implies (zp n)
           (equal  (FIRSTN n X)
                   nil))
  :hints (("Goal" :in-theory (enable firstn))))

(defthm firstn-iff
  (iff (FIRSTN N X)
       (and (not (zp n))
            (consp x)))
  :hints (("Goal" :in-theory (enable firstn))))

(defthm equal-of-firstn-and-firstn-same-two
  (implies (not (equal n1 n2))
           (equal (equal (firstn n1 x)
                         (firstn n2 x))
                  (if (zp n1)
                      (or (zp n2) (not (consp x)))
                    (if (zp n2)
                        (or (zp n1) (not (consp x)))
                      (and (equal (firstn (min n1 n2) x)
                                  (firstn (min n1 n2) x))
                           (<= (len x) (min n1 n2)))))))
  :hints (("Goal" :use (:instance equal-of-firstn-and-firstn-same-two-helper))))

(defthm len-of-cdr
  (implies (consp x)
           (equal (LEN (CDR X))
                  (+ -1 (len x))))
  :hints (("Goal" :in-theory (enable len))))

(theory-invariant (incompatible (:rewrite len-of-cdr) (:definition len)))

(defthm firstn-of-append
  (equal (firstn n (append x y))
         (append (firstn n x) (firstn (+ n (- (len x))) y)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable firstn append))))

(defthm firstn-of-len-same
  (equal (firstn (len x) x)
         (list::list-fix x))
  :hints (("Goal" :in-theory (e/d (firstn len) (len-of-cdr)))))



;may be expensive?
(defthm list-cong-when-len-<
  (implies (< (len x) (len y))
           (equal (list::list-cong x y)
                  nil)))

(defthm list-cong-when-len-<-alt
  (implies (< (len y) (len x))
           (equal (list::list-cong x y)
                  nil)))

(defthm list-cong-of-cons-of-car-same
  (equal (LIST::LIST-CONG X (CONS (CAR X) y))
         (and (consp x)
              (LIST::LIST-CONG (cdr X) y)))
  :hints (("Goal" :in-theory (e/d (LIST::LIST-CONG) (EQUAL-OF-LIST-FIXES)))))

(defthm car-of-firstn
  (equal (car (firstn n y))
         (if (zp n)
             nil
           (car y)))
  :hints (("Goal" :in-theory (enable firstn))))

;make more like this?
(defthm list-cong-of-two-append-same
  (equal (LIST::LIST-CONG (APPEND x y) (APPEND x z))
         (LIST::LIST-CONG y z))
  :hints (("Goal" :in-theory (e/d (LIST::LIST-CONG) (EQUAL-OF-LIST-FIXES)))))


(defthm list-cong-of-two-true-listps
  (implies (and (true-listp x)
                (true-listp y))
           (equal (LIST::LIST-CONG x y)
                  (equal x y)))
  :hints (("Goal" :in-theory (e/d (LIST::LIST-CONG) (EQUAL-OF-LIST-FIXES)))))


(defthm nthcdr-when-<=
  (implies (and (<= (len l) (nfix n))
                (true-listp l) ;yuck?
                )
           (equal (nthcdr n l)
                  nil))
  :hints (("Goal" :in-theory (e/d (nthcdr len) (len-of-cdr)))))


(defthm open-list-cong
  (implies
   (and
    (consp x)
    (consp y))
   (equal (list-cong x y)
	  (and (equal (car x) (car y))
	       (list-cong (cdr x) (cdr y)))))
  :hints (("goal" :in-theory (e/d (list-cong list-fix)
				  (equal-of-list-fixes)))))

(in-theory
 (e/d
  (len nthcdr firstn)
  (len-of-cdr)
  ))

(defthmd equal-append-reduction!
  (equal (equal (append x y) z)
	 (and
	  (list-cong x (firstn (len x) z))
	  (equal y (nthcdr (len x) z))))
  :hints (("goal" :induct (len-len-induction x z)
	   :in-theory (enable firstn nthcdr len binary-append))))

(defthm equal-cons-cases
  (implies
   (consp c)
   (equal (equal (cons a b) c)
	  (and (equal a (car c))
	       (equal b (cdr c))))))

(defthmd equal-consp-cases
  (implies
   (consp x)
   (equal (equal x y)
	  (and (consp y)
	       (equal (car x) (car y))
	       (equal (cdr x) (cdr y))))))

;;
;; acl2-count lemmas
;;

(defthm acl2-count-of-cdr-bound-weak
  (<= (acl2-count (cdr x)) (acl2-count x))
  :rule-classes (:rewrite :linear))

(defthm acl2-count-of-car-bound-weak
  (<= (acl2-count (car x)) (acl2-count x))
  :rule-classes (:rewrite :linear))

(defthm acl2-count-of-car-bound-tight
  (implies (consp x)
           (< (acl2-count (car x)) (acl2-count x)))
  :rule-classes (:rewrite :linear))

(defthm acl2-count-of-cdr-bound-tight
  (implies (consp x)
           (< (acl2-count (cdr x)) (acl2-count x)))
  :rule-classes (:rewrite :linear))

