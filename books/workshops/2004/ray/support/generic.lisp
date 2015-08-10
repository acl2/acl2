(in-package "ACL2")

#|

  generic.lisp
  ~~~~~~~~~~~~

In this book, we achieve the following. Assume that we have a function
copy with the property that (copy x) has the same number of elements
as x, and nth i of x is the same as nth i of (copy x). Then I want to
guarantee that (copy x) is the identity function. This

|#

; The following was removed with the addition of natp-compound-recognizer to
; ACL2 2.9.2.
;(local
; (defthm natp-compound-recognizer
;   (iff (natp n)
;        (and (integerp n)
;             (<= 0 n)))
;   :rule-classes :compound-recognizer))

(local
 (in-theory (disable natp)))

(local
 (in-theory (enable nth update-nth mv-nth)))

(local
 (defthm nth-update-nth-diff
   (implies (not (equal (nfix n) (nfix m)))
            (equal (nth n (update-nth m v l)) (nth n l)))))

(local
 (defthm nth-update-nth-same
   (implies (equal (nfix n) (nfix m))
            (equal (nth n (update-nth m v l)) v))))

(local
 (defthm update-nth-update-nth-same
   (equal (update-nth n v (update-nth n x l))
          (update-nth n v l))))

(local
 (defthm update-nth-update-nth-diff
   (implies (not (equal (nfix n) (nfix m)))
            (equal (update-nth n v (update-nth m x l))
                   (update-nth m x (update-nth n v l))))
   :rule-classes ((:rewrite :loop-stopper ((n m))))))

(local
 (in-theory (disable nth update-nth)))

;; Here we build up the theory for proving that copying is identity.

(local
 ;; [Jared] changed this to use arithmetic-3 instead of 2
 (include-book "arithmetic-3/bind-free/top" :dir :system))

(local
  (defun falsifier-index (a b i)
    (if (endp a) i
      (if (equal (car a) (car b))
          (falsifier-index (rest a) (rest b) (1+ i))
        i))))

(local
  (defthm consp-to-nth
    (implies (and (consp l)
                  (natp i)
                  (< 0 i))
           (equal (nth (+ -1 i) (cdr l))
                  (nth i l)))
    :hints (("Goal"
             :in-theory (enable nth)))))

(local
 (defthm falsifier-natp
   (implies (natp i)
            (natp (falsifier-index a b i)))
   :rule-classes :type-prescription))


(local
 (defthm falsifier->=i
   (implies  (natp i)
             (<= i (falsifier-index a b i)))
   :rule-classes :linear))

(local
 (defthm falsifier-<=-len
   (implies (natp i)
            (<= (falsifier-index a b i)
                (+ i (len a))))
   :rule-classes :linear))

(local
 (defthm <=-implies-natp
   (implies (and (<= i f)
                 (natp i)
                 (natp f))
            (natp (+ (- i) f)))
   :hints (("Goal"
            :in-theory (enable natp)))))

(local
 (defthm falsifier-index-falsifies
   (implies (and (not (equal a b))
                 (true-listp a)
                 (true-listp b)
                 (natp i)
                 (equal (len a) (len b)))
            (equal (equal (nth (- (falsifier-index a b i) i) a)
                          (nth (- (falsifier-index a b i) i) b))
                   nil))
   :rule-classes nil))

(local
 (defthm falsifier-falsifies
   (implies (and (not (equal a b))
                 (true-listp a)
                 (true-listp b)
                 (equal (len a) (len b)))
            (equal (equal (nth (falsifier-index a b 0) a)
                          (nth (falsifier-index a b 0) b))
                   nil))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance falsifier-index-falsifies
                             (i 0)))))))


(local
 (defthm falsifier-!=i-for-consp
   (implies (and (consp a)
                 (equal (len a) (len b))
                 (true-listp a)
                 (true-listp b)
                 (not (equal a b)))
            (not (equal (falsifier-index a b i)
                        (+ i (len a)))))
   :rule-classes nil))

(local
 (defthm falsifier-<-i
   (implies (and (case-split (consp a))
                 (force (equal (len a) (len b)))
                 (not (equal a b))
                 (force (true-listp a))
                 (force (true-listp b)))
            (< (falsifier-index a b 0)
               (len a)))
   :rule-classes :linear
   :hints (("Goal"
            :do-not '(eliminate-destructors generalize fertilize)
            :do-not-induct t
            :use ((:instance falsifier-<=-len
                             (i 0))
                  (:instance falsifier-!=i-for-consp
                             (i 0)))))))

(local
 (defthm len=0-implies-not-consp
   (implies (equal 0 (len x))
            (not (consp x)))
   :rule-classes :forward-chaining))


;; We now specify several encapsulated functions. Each would be proved to be
;; the identity easily, and with some clever trick I could have made only one
;; encapsulation. But I plan to use them with functional instantiation and I am
;; just doing it this way so that functional instantiation is easy to apply.

(encapsulate
 (((copy-from *) => *)
  ((hypos *) => *))

 (local (defun copy-from (x) x))
 (local (defun hypos (x) (declare (ignore x)) t))

 (defthm copy-from-has-same-nth
   (implies (and (natp i)
                 (hypos x)
                 (< i (len x)))
            (equal (nth i (copy-from x))
                   (nth i x))))

 (defthm copy-from-has-same-len
   (implies (hypos x)
            (equal (len (copy-from x)) (len x))))

 (defthm copy-from-is-true-list
   (implies (and (true-listp x)
                 (hypos x))
            (true-listp (copy-from x)))
   :rule-classes :type-prescription)
)




(defthm |copy from is identity|
  (implies (and (true-listp x)
                (hypos x))
           (equal (copy-from x) x))
  :hints (("Goal"
           :do-not '(eliminate-destructors generalize fertilize)
           :do-not-induct t
           :use ((:instance falsifier-falsifies
                            (a (copy-from x))
                            (b x))
                 (:instance copy-from-has-same-nth
                            (i (falsifier-index (copy-from x) x 0)))))))

(encapsulate
 (((copy-from-fld *) => *)
  ((fldf) => *))

 (local (defun copy-from-fld (x) (nth 0 x)))
 (local (defun fldf () 0))

 (defthm copy-from-fld-has-same-nth
   (implies (and (natp i)
                 (< i (len (nth (fldf) x))))
            (equal (nth i (copy-from-fld x))
                   (nth i (nth (fldf) x)))))

 (defthm copy-from-fld-has-same-len
   (implies (true-listp (nth (fldf) x))
            (equal (len (copy-from-fld x)) (len (nth (fldf) x)))))

 (defthm copy-from-fld-is-true-list
   (implies (true-listp (nth (fldf) x))
            (true-listp (copy-from-fld x)))
   :rule-classes :type-prescription)
)




(defthm |copy from field is identity|
  (implies (true-listp (nth (fldf) x))
           (equal (copy-from-fld x) (nth (fldf) x)))
  :hints (("Goal"
           :in-theory (disable copy-from-fld-has-same-len)
           :use ((:instance falsifier-falsifies
                            (a (copy-from-fld x))
                            (b (nth (fldf) x)))
                 (:instance copy-from-fld-has-same-nth
                            (i (falsifier-index (copy-from-fld x)
                                                (nth (fldf) x)
                                                0)))
                 (:instance copy-from-fld-has-same-len)))))


;; I define copy-to in two flavors. One simply copies over the entire data in l
;; to x, the other copies the data in l to a component of x. In each case I
;; prove that the corresponding target (entire or component) is an identity. I
;; do it this way rather than with one encapsulate so that it facilitates
;; functional instantiation.

(encapsulate

 (((copy-to * *) => *)
  ((hypotheses * *) => *))

 (local (defun copy-to (l x) (declare (ignore x)) l))
 (local (defun hypotheses (l x) (declare (ignore l x)) t))

 (defthm copy-to-has-same-nth
   (implies (and (natp i)
                 (hypotheses l x)
                 (< i (len l)))
            (equal (nth i (copy-to l x))
                   (nth i l))))

 (defthm copy-to-has-same-len
   (implies (and (true-listp l)
                 (true-listp x)
                 (hypotheses l x)
                 (equal (len l) (len x)))
            (equal (len (copy-to l x)) (len x))))

 (defthm copy-to-is-true-list
   (implies (and (true-listp x)
                 (true-listp l)
                 (hypotheses l x))
            (true-listp (copy-to l x)))
   :rule-classes :type-prescription)
)

(defthm |copy to whole is identity|
  (implies (and (true-listp l)
                (true-listp x)
                (hypotheses l x)
                (equal (len l) (len x)))
           (equal (copy-to l x) l))
  :hints (("Goal"
           :use ((:instance falsifier-falsifies
                            (a (copy-to l x))
                            (b l))
                 (:instance copy-to-has-same-nth
                            (i (falsifier-index (copy-to l x) l 0)))))))

;; OK finally a version of copy-to that copies l to a component (fld) of x.

(encapsulate

 (((copy-to-fld * *) => *)
  ((fld) => *))

 (local (defun copy-to-fld (l x) (update-nth 0 l x)))
 (local (defun fld () 0))

 (defthm copy-to-fld-has-same-nth
   (implies (and (natp i)
                 (< i (len l)))
            (equal (nth i (nth (fld) (copy-to-fld l x)))
                   (nth i l))))

 (defthm copy-to-fld-has-same-len
   (implies (and (true-listp l)
                 (true-listp (nth (fld) x))
                 (equal (len l) (len (nth (fld) x))))
            (equal (len (nth (fld) (copy-to-fld l x))) (len (nth (fld) x)))))

 (defthm copy-to-fld-is-true-list
   (implies (and (true-listp (nth (fld) x))
                 (true-listp l))
            (true-listp (nth (fld) (copy-to-fld l x))))
   :rule-classes :type-prescription)
)

(defthm |copy to field is identity|
  (implies (and (true-listp l)
                (true-listp (nth (fld) x))
                (equal (len l) (len (nth (fld) x))))
           (equal (nth (fld) (copy-to-fld l x)) l))
  :otf-flg t
  :hints (("Goal"
           :in-theory (disable copy-to-fld-has-same-len)
           :do-not-induct t
           :do-not '(eliminate-destructors generalize fertilize)
           :use ((:instance falsifier-falsifies
                            (a (nth (fld) (copy-to-fld l x)))
                            (b l))
                 (:instance copy-to-fld-has-same-nth
                            (i (falsifier-index (nth (fld) (copy-to-fld l x)) l
                                                0)))
                 (:instance copy-to-fld-has-same-len)))))




