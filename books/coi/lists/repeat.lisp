#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
;; repeat.lisp
;; Theorems about repeat.

(in-package "LIST")
(include-book "basic")

;; bzo (jcd) - consider disabling repeat

(defund repeat (n x)
  ;; [Jared]: Modified by adding MBE and changing variable name from V to X,
  ;; for compatibility with std/lists/repeat.lisp
  (declare (xargs :guard (natp n)
                  :verify-guards nil))
  (mbe :logic (if (zp n)
                  nil
                (cons x (repeat (- n 1) x)))
       :exec (make-list n :initial-element x)))

(local (encapsulate
        ()
        (local
         (defthm test-for-type-prescription-of-repeat
           (true-listp (repeat n l))
           :rule-classes nil
           :hints(("Goal" 
                   :in-theory (union-theories '(booleanp
                                                (:type-prescription repeat))
                                              (theory 'minimal-theory))))))))

(defthm repeat-zp
  (implies (zp n)
           (equal (repeat n v)
                  nil))
  :hints(("Goal" :in-theory (enable repeat))))

;; TEMP (jcd) - the following are two new rules inspired by list-defthms.lisp.

(defthm consp-repeat
  (equal (consp (repeat n v))
         (not (zp n)))
  :hints(("Goal" :in-theory (enable repeat))))

(defthm consp-repeat-type-prescription
  (implies (and (integerp n)
                (< 0 n))
           (consp (repeat n v)))
  :rule-classes :type-prescription)

(defthm repeat-iff
  (iff (repeat n v)
       (not (zp n))))

(defthm car-repeat
  (equal (car (repeat n v))
         (if (zp n)
             nil
           v))
  :hints(("Goal" :in-theory (enable repeat))))

(defthm cdr-repeat
  (equal (cdr (repeat n v))
         (if (zp n)
             nil
           (repeat (1- n) v)))
  :hints(("Goal" :in-theory (enable repeat))))

(defthm len-repeat
  (equal (len (repeat n v))
         (nfix n))
  :hints(("Goal" :in-theory (enable repeat))))

(local (defun double-sub1-induct (n1 n2)
         (if (not (zp n1))
             (double-sub1-induct (1- n1) (1- n2))
           n2)))

(defthm equal-repeat-simple
  (equal (equal (repeat n v) nil)
         (zp n)))

(defthm equal-repeat-cons
  (equal (equal (repeat n v) (cons v2 x))
         (and (equal v v2)
              (< 0 (nfix n))
              (equal (repeat (1- n) v) x)))
  :hints(("Goal" :in-theory (enable repeat))))

(defthm equal-repeat-repeat
  (equal (equal (repeat n v) (repeat n2 v2))
         (and (equal (nfix n) (nfix n2))
              (or (zp n) (equal v v2))))
  :hints (("Goal" :in-theory (enable repeat)
           :induct (double-sub1-induct n n2))))

(defthm firstn-repeat
  (equal (firstn n (repeat n2 v))
         (repeat (min (nfix n) (nfix n2)) v))
  :hints (("Goal" :in-theory (enable repeat)
           :induct (double-sub1-induct n n2))))

;; Here's a rule inspired by the list-defthms book, which shows what 
;; happens when nthcdr is applied to repeat.

(defthm nthcdr-repeat
  (equal (nthcdr i (repeat j v))
         (if (<= (nfix j) (nfix i))
             nil
           (repeat (- (nfix j) (nfix i)) v)))
  :hints(("Goal" :in-theory (enable repeat)
          :induct (double-sub1-induct i j))))

(defthm append-of-repeat-and-repeat-same-val
  (implies (and (force (natp n))
                (force (natp m)))
           (equal (append (repeat n val) (repeat m val))
                  (repeat (+ m n) val)))
  :hints (("Goal" :in-theory (enable append repeat))))

;bzo gen the (list k) to (cons k rest) ?
(defthm append-repeat-singleton-same
  (equal (append (repeat n k) (list k))
         (repeat (+ 1 (nfix n)) k))
  :hints (("Goal" :in-theory (e/d (LIST::EQUAL-APPEND-REDUCTION!) 
                                  ()))))
        

(encapsulate
  ()
  ;; [Jared] MBE equivalence proof adapted from std/lists/repeat.lisp

  (local (defthm commutativity-2-of-+
           (equal (+ x (+ y z))
                  (+ y (+ x z)))))

  (local (defthm fold-consts-in-+
           (implies (and (syntaxp (quotep x))
                         (syntaxp (quotep y)))
                    (equal (+ x (+ y z)) (+ (+ x y) z)))))

  (local (defthm distributivity-of-minus-over-+
           (equal (- (+ x y)) (+ (- x) (- y)))))

  (local (defthm l0
           (equal (append (repeat n x) (cons x acc))
                  (append (repeat (+ 1 (nfix n)) x) acc))
           :hints(("Goal" :in-theory (enable repeat)))))

  (local (defthm make-list-ac-removal
           (equal (make-list-ac n x acc)
                  (append (repeat n x)
                          acc))))

  (verify-guards repeat))
