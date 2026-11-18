(in-package "ACL2")

(include-book "kestrel/bv/bitxor" :dir :system)
(include-book "kestrel/bv/bitand" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "std/lists/repeat" :dir :system)
(include-book "std/basic/inductions" :dir :system)

(local (include-book "std/lists/append" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bit-list-p (x)
  :enabled t
  :returns (yes/no booleanp)
  (if (atom x)
      (null x)
    (and (bitp (car x))
         (bit-list-p (cdr x))))
  ///

  (defrule true-listp-when-bit-list-p
    (implies (bit-list-p x)
             (true-listp x))
    :rule-classes (:rewrite :forward-chaining))

  ;; Structural support for the :returns proofs below; the exported append
  ;; theorem is the dimensioned bit-listnp-of-append.
  (local
   (defrule bit-list-p-of-append
     (implies (bit-list-p x)
              (equal (bit-list-p (append x y))
                     (bit-list-p y))))))

(define bit-listnp (x (n natp))
  :returns (yes/no booleanp)
  (if (zp n)
      (null x)
    (and (consp x)
         (bitp (car x))
         (bit-listnp (cdr x) (1- n))))
  ///

  (defrule bit-list-p-when-bit-listnp
    (implies (bit-listnp x n)
             (bit-list-p x))
    :enable bit-list-p
    :rule-classes (:rewrite :forward-chaining))

  (defruled len-of-bit-listnp
    (implies (and (bit-listnp x n)
                  (natp n))
             (equal (len x) n)))

  (defruled bit-listnp-alt-def
    (implies (natp n)
             (iff (bit-listnp x n)
                  (and (bit-list-p x)
                       (equal (len x) n)))))

  ;; Every bit list is a bit list of its own length.  This is the bridge that
  ;; lets the dimensioned identities fire on lengths computed by the prover.
  (defrule bit-listnp-of-own-len
    (implies (bit-list-p x)
             (bit-listnp x (len x)))
    :induct (bit-list-p x)
    :enable bit-list-p)

  (local
   (defrule bit-listnp-of-append-core
     (implies (and (bit-listnp x m)
                   (bit-listnp y n)
                   (natp m)
                   (natp n))
              (bit-listnp (append x y) (+ m n)))
     :induct (bit-listnp x m)))

  ;; The exported form binds the dimension through an equation so the rule
  ;; fires on any syntactic presentation of the sum.
  (defrule bit-listnp-of-append
    (implies (and (bit-listnp x m)
                  (bit-listnp y n)
                  (natp m)
                  (natp n)
                  (equal l (+ m n)))
             (bit-listnp (append x y) l))
    :use (bit-listnp-of-append-core)))

(define bit-listn0 ((n natp))
  :returns (r bit-list-p
              :hints (("Goal" :in-theory (enable repeat))))
  (repeat n 0)
  ///

  (defrule len-of-bit-listn0
    (equal (len (bit-listn0 k))
           (nfix k)))

  (defrule bit-listnp-of-bit-listn0
    (bit-listnp (bit-listn0 n) n)
    :enable (repeat bit-listnp))

  (defrule append-of-bit-listn0
    (equal (append (bit-listn0 m) (bit-listn0 n))
           (bit-listn0 (+ (nfix m) (nfix n))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; bitxor and bitand read their arguments through bvchop, which ifixes; so
;;; wrapping an argument in ifix changes nothing.  This is what lets a
;;; function whose index bound is not expressible in its own guard -- see
;;; scheme-sum-entry in entry.lisp, which has no dimension formal -- fix the
;;; out-of-range nth without changing the function's value anywhere.

(defrule bitxor-of-ifix-arg1
  (equal (bitxor (ifix x) y)
         (bitxor x y))
  :hints (("Goal" :in-theory (e/d (bitxor) (bvxor-1-becomes-bitxor)))))

(defrule bitand-of-ifix-arg1
  (equal (bitand (ifix x) y)
         (bitand x y))
  :hints (("Goal" :in-theory (e/d (bitand) (bvand-1-becomes-bitand)))))

;; ifix must stay closed for the two rules above to fire: if it opens to
;; (if (integerp x) x 0) first, their left-hand sides never match.  Nothing
;; in this development reasons about ifix itself.
(in-theory (disable ifix))

(define bit-list-add ((x bit-list-p) (y bit-list-p))
  :returns (z bit-list-p)
  (if (and (consp x) (consp y))
      (cons (bitxor (car x) (car y))
            (bit-list-add (cdr x) (cdr y)))
    nil)
  ///

  (defrule len-of-bit-list-add
    (equal (len (bit-list-add x y))
           (min (len x) (len y))))

  (defrule bit-listnp-of-bit-list-add
    (implies (and (bit-listnp x n)
                  (bit-listnp y n))
             (bit-listnp (bit-list-add x y) n))
    :enable bit-listnp)

  (defruled bit-list-add-commutative
    (equal (bit-list-add x y)
           (bit-list-add y x)))

  (defruled bit-list-add-associative
    (equal (bit-list-add (bit-list-add x y) z)
           (bit-list-add x (bit-list-add y z))))

  (defruled bit-list-add-commutative-2
    (equal (bit-list-add x (bit-list-add y z))
           (bit-list-add y (bit-list-add x z)))
    :use (bit-list-add-associative
          (:instance bit-list-add-associative (x y) (y x))
          (:instance bit-list-add-commutative)))

  (defruled bit-list-add-self
    (equal (bit-list-add x x)
           (bit-listn0 (len x)))
    :enable (bit-listn0 repeat))

  (defrule bit-list-add-same
    (implies (bit-listnp x n)
             (equal (bit-list-add x x)
                    (bit-listn0 n)))
    :enable (repeat bit-listn0 bit-listnp))

  (defrule bit-list-add-cancel-1
    (implies (and (bit-listnp x n)
                  (bit-listnp y n))
             (equal (bit-list-add y (bit-list-add y x))
                    x))
    :enable bit-listnp)

  (defrule bit-list-add-cancel-2
    (implies (and (bit-listnp x n)
                  (bit-listnp y n))
             (equal (bit-list-add y (bit-list-add x y))
                    x))
    :enable bit-listnp)

  (defruled bit-list-add-of-append
    (implies (equal (len x1) (len y1))
             (equal (bit-list-add (append x1 x2) (append y1 y2))
                    (append (bit-list-add x1 y1) (bit-list-add x2 y2))))
    :induct (bit-list-add x1 y1))

  (defrule bit-list-add-of-bit-listn0-1
    (implies (bit-listnp x n)
             (equal (bit-list-add (bit-listn0 n) x)
                    x))
    :enable (repeat bit-listn0 bit-listnp))

  (defrule bit-list-add-of-bit-listn0-2
    (implies (bit-listnp x n)
             (equal (bit-list-add x (bit-listn0 n))
                    x))
    :enable (repeat bit-listn0 bit-listnp))

  (defrule bit-list-add-of-bit-listn0-both
    (equal (bit-list-add (bit-listn0 j) (bit-listn0 k))
           (bit-listn0 (min (nfix j) (nfix k))))
    :induct (dec-dec-induct j k)
    :enable (repeat bit-listn0))

  (defrule bit-list-add-zero-iff-equal
    (implies (and (bit-listnp x n)
                  (bit-listnp y n))
             (iff (equal (bit-list-add x y) (bit-listn0 n))
                  (equal x y)))
    :enable (repeat bit-listn0 bit-listnp))

  (defruled bit-list-add-equal-arg2
    (implies (and (bit-listnp x n)
                  (bit-listnp y n))
             (iff (equal (bit-list-add x y) y)
                  (equal x (bit-listn0 n))))
    :enable (repeat bit-listn0 bit-listnp))

  (defruled bit-list-add-equal-arg1
    (implies (and (bit-listnp x n)
                  (bit-listnp y n))
             (iff (equal (bit-list-add x y) x)
                  (equal y (bit-listn0 n))))
    :enable (repeat bit-listn0 bit-listnp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bit-list-scale ((b bitp) (x bit-list-p))
  :returns (z bit-list-p)
  (if (atom x)
      nil
    (cons (bitand b (car x))
          (bit-list-scale b (cdr x))))
  ///

  (defrule len-of-bit-list-scale
    (equal (len (bit-list-scale b x))
           (len x)))

  (defrule bit-listnp-of-bit-list-scale
    (implies (bit-listnp x n)
             (bit-listnp (bit-list-scale b x) n))
    :induct (bit-listnp x n)
    :enable bit-listnp)

  (defrule bit-list-scale-of-0
    (equal (bit-list-scale 0 x)
           (bit-listn0 (len x)))
    :enable (bit-listn0 repeat))

  (local
   (defrule bit-list-scale-of-1-general
     (implies (bit-list-p x)
              (equal (bit-list-scale 1 x)
                     x))))

  (defrule bit-list-scale-of-1
    (implies (bit-listnp x n)
             (equal (bit-list-scale 1 x)
                    x)))

  (defrule bit-list-scale-of-bit-listn0
    (equal (bit-list-scale b (bit-listn0 k))
           (bit-listn0 k))
    :enable (bit-listn0 repeat)))

(define bit-list-outer ((u bit-list-p) (v bit-list-p))
  :returns (z bit-list-p)
  (if (atom u)
      nil
    (append (bit-list-scale (car u) v)
            (bit-list-outer (cdr u) v)))
  ///

  (defrule len-of-bit-list-outer
    (equal (len (bit-list-outer u v))
           (* (len u) (len v))))

  (defrule bit-listnp-of-bit-list-outer
    (implies (and (bit-listnp u j)
                  (bit-listnp v k)
                  (natp j)
                  (natp k))
             (bit-listnp (bit-list-outer u v) (* j k)))
    :enable (bit-listnp-alt-def
             len-of-bit-listnp))

  (defruled bit-list-outer-of-bit-listn0-arg1
    (implies (natp k)
             (equal (bit-list-outer (bit-listn0 k) v)
                    (bit-listn0 (* k (len v)))))
    :induct (bit-list-outer (repeat k 0) v)
    :enable (bit-listn0 repeat bit-list-scale-of-0))

  (defruled bit-list-outer-of-bit-listn0-arg2
    (implies (natp k)
             (equal (bit-list-outer u (bit-listn0 k))
                    (bit-listn0 (* (len u) k))))
    :enable (bit-list-scale-of-bit-listn0)))

;;; Bilinearity of scale and outer over bit-list-add.  The general version,
;;; with structural hypotheses, is a local proof vehicle; the exported
;;; statements are dimensioned, with the length-agreement hypothesis of
;;; outer-of-add-arg2 dissolved into a shared dimension.

(local
 (defruled bit-list-scale-of-add-general
   (implies (and (bitp b) (bit-list-p x) (bit-list-p y))
            (equal (bit-list-scale b (bit-list-add x y))
                   (bit-list-add (bit-list-scale b x)
                                 (bit-list-scale b y))))
   :induct (bit-list-add x y)
   :enable (bit-list-scale bit-list-add)))

(local
 (defruled bit-list-scale-of-bitxor-general
   (implies (and (bitp b1) (bitp b2) (bit-list-p x))
            (equal (bit-list-scale (bitxor b1 b2) x)
                   (bit-list-add (bit-list-scale b1 x)
                                 (bit-list-scale b2 x))))
   :enable (bit-list-scale bit-list-add)))

(local
 (defruled bit-list-outer-of-add-arg1-general
   (implies (and (bit-list-p u1) (bit-list-p u2) (bit-list-p v))
            (equal (bit-list-outer (bit-list-add u1 u2) v)
                   (bit-list-add (bit-list-outer u1 v)
                                 (bit-list-outer u2 v))))
   :induct (bit-list-add u1 u2)
   :enable (bit-list-outer bit-list-add bit-list-scale-of-bitxor-general
            bit-list-add-of-append bit-list-add-self)))

(defruled bit-list-outer-of-add-arg1
  (implies (and (bit-listnp u1 j) (bit-listnp u2 j) (bit-listnp v k)
                (natp j) (natp k))
           (equal (bit-list-outer (bit-list-add u1 u2) v)
                  (bit-list-add (bit-list-outer u1 v)
                                (bit-list-outer u2 v))))
  :enable (bit-list-outer-of-add-arg1-general len-of-bit-listnp))

(local
 (defruled bit-list-outer-of-add-arg2-general
   (implies (and (bit-list-p u) (bit-list-p v) (bit-list-p w)
                 (equal (len v) (len w)))
            (equal (bit-list-outer u (bit-list-add v w))
                   (bit-list-add (bit-list-outer u v)
                                 (bit-list-outer u w))))
   :induct (len u)
   :enable (bit-list-outer bit-list-scale-of-add-general
            bit-list-add-of-append bit-list-add-self)))

(defruled bit-list-outer-of-add-arg2
  (implies (and (bit-listnp u j) (bit-listnp v k) (bit-listnp w k)
                (natp j) (natp k))
           (equal (bit-list-outer u (bit-list-add v w))
                  (bit-list-add (bit-list-outer u v)
                                (bit-list-outer u w))))
  :use (bit-list-outer-of-add-arg2-general)
  :enable (len-of-bit-listnp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bit-list-listp (a)
  :enabled t
  :returns (yes/no booleanp)
  (if (atom a)
      (null a)
    (and (bit-list-p (car a))
         (bit-list-listp (cdr a)))))

(define bit-matp (a (m natp) (n natp))
  :returns (yes/no booleanp)
  :measure (nfix m)
  (if (zp m)
      (null a)
    (and (consp a)
         (bit-listnp (car a) n)
         (bit-matp (cdr a) (1- m) n)))
  ///

  (defrule bit-list-listp-when-bit-matp
    (implies (bit-matp a m n)
             (bit-list-listp a))
    :rule-classes (:rewrite :forward-chaining))

  (defruled len-of-bit-matp
    (implies (and (bit-matp a m n)
                  (natp m))
             (equal (len a) m))))

(define bit-mat0 ((m natp) (n natp))
  :returns (a bit-list-listp
              :hints (("Goal" :in-theory (enable repeat))))
  (repeat m (bit-listn0 n))
  ///

  (defrule bit-matp-of-bit-mat0
    (bit-matp (bit-mat0 m n) m n)
    :enable (repeat bit-matp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bit-mat-add ((a bit-list-listp) (b bit-list-listp))
  :returns (c bit-list-listp)
  (if (and (consp a) (consp b))
      (cons (bit-list-add (car a) (car b))
            (bit-mat-add (cdr a) (cdr b)))
    nil)
  ///

  (defrule bit-matp-of-bit-mat-add
    (implies (and (bit-matp a m n)
                  (bit-matp b m n))
             (bit-matp (bit-mat-add a b) m n))
    :enable bit-matp)

  (defrule bit-mat-add-of-bit-mat0
    (implies (bit-matp a m n)
             (equal (bit-mat-add (bit-mat0 m n) a)
                    a))
    :enable (repeat bit-mat0 bit-matp))

  (defruled bit-mat-add-same
    (implies (bit-matp a m n)
             (equal (bit-mat-add a a)
                    (bit-mat0 m n)))
    :enable (repeat bit-mat0 bit-matp))

  (defrule bit-mat-add-cancel-1
    (implies (and (bit-matp a m n)
                  (bit-matp b m n))
             (equal (bit-mat-add b (bit-mat-add b a))
                    a))
    :enable bit-matp)

  (defrule bit-mat-add-cancel-2
    (implies (and (bit-matp a m n)
                  (bit-matp b m n))
             (equal (bit-mat-add b (bit-mat-add a b))
                    a))
    :enable bit-matp)

  (defrule bit-mat-add-zero-iff-equal
    (implies (and (bit-matp a m n)
                  (bit-matp b m n))
             (iff (equal (bit-mat-add a b) (bit-mat0 m n))
                  (equal a b)))
    :enable (repeat bit-mat-add-same bit-matp bit-mat0))

  (defruled bit-mat-add-equal-arg2
    (implies (and (bit-matp a m n)
                  (bit-matp b m n))
             (iff (equal (bit-mat-add a b) b)
                  (equal a (bit-mat0 m n))))
    :enable (repeat bit-list-add-equal-arg2 bit-matp bit-mat0))

  (defruled bit-mat-add-equal-arg1
    (implies (and (bit-matp a m n)
                  (bit-matp b m n))
             (iff (equal (bit-mat-add a b) a)
                  (equal b (bit-mat0 m n))))
    :enable (repeat bit-list-add-equal-arg1 bit-matp bit-mat0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define mat-flat ((a bit-list-listp))
  :returns (l bit-list-p :hyp (bit-list-listp a))
  (if (atom a)
      nil
    (append (car a) (mat-flat (cdr a))))
  ///

  (defrule len-of-mat-flat
    (implies (and (bit-matp a m n)
                  (natp m)
                  (natp n))
             (equal (len (mat-flat a))
                    (* m n)))
    :induct (bit-matp a m n)
    :enable (bit-matp len-of-bit-listnp))

  (defrule bit-listnp-of-mat-flat
    (implies (and (bit-matp a m n)
                  (natp m)
                  (natp n))
             (bit-listnp (mat-flat a) (* m n)))
    :enable bit-listnp-alt-def)

  (defruled mat-flat-of-bit-mat0
    (implies (and (natp m) (natp n))
             (equal (mat-flat (bit-mat0 m n))
                    (bit-listn0 (* m n))))
    :induct (dec-induct m)
    :enable (bit-mat0 bit-listn0 repeat))

  ;; The core is stated with (len a) as the row count so that its hypotheses
  ;; are stable under plain cdr-cdr induction; no bespoke induction scheme
  ;; cdring two lists while decrementing a counter is needed.
  (local
   (defruled mat-flat-of-bit-mat-add-core
     (implies (and (bit-matp a (len a) n)
                   (bit-matp b (len b) n)
                   (equal (len a) (len b))
                   (natp n))
              (equal (mat-flat (bit-mat-add a b))
                     (bit-list-add (mat-flat a) (mat-flat b))))
     :induct (cdr-cdr-induct a b)
     :enable (bit-mat-add mat-flat bit-matp len-of-bit-listnp
              bit-list-add-of-append)))

  (defruled mat-flat-of-bit-mat-add
    (implies (and (bit-matp a m n)
                  (bit-matp b m n)
                  (natp m)
                  (natp n))
             (equal (mat-flat (bit-mat-add a b))
                    (bit-list-add (mat-flat a) (mat-flat b))))
    :use (mat-flat-of-bit-mat-add-core)
    :enable (len-of-bit-matp)))
