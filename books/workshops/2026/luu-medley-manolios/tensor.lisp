(in-package "ACL2")

(include-book "scheme")
(local (include-book "std/lists/append" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tensor ((a bit-list-listp) (b bit-list-listp) (c bit-list-listp))
  :returns (tt bit-list-p :hyp :guard)
  (bit-list-outer (mat-flat a)
                  (bit-list-outer (mat-flat b) (mat-flat c)))
  ///

  ;; Unconditional and free-variable-free.
  (defrule len-of-tensor
    (equal (len (tensor a b c))
           (* (len (mat-flat a))
              (len (mat-flat b))
              (len (mat-flat c)))))

  ;; The size-constrained return theorem: three n x n factors denote a tensor
  ;; of exactly n^6 bits.
  (defrule bit-listnp-of-tensor
    (implies (and (bit-matp a n n)
                  (bit-matp b n n)
                  (bit-matp c n n)
                  (natp n))
             (bit-listnp (tensor a b c) (* n n n n n n)))
    :enable (bit-listnp-alt-def)
    :disable tensor)

  (defruled tensor-when-zero-a
    (implies (and (equal a (bit-mat0 n n))
                  (bit-matp b n n)
                  (bit-matp c n n)
                  (natp n))
             (equal (tensor a b c)
                    (bit-listn0 (* n n n n n n))))
    :enable (mat-flat-of-bit-mat0
             bit-list-outer-of-bit-listn0-arg1
             bit-list-outer-of-bit-listn0-arg2))

  (defruled tensor-when-zero-b
    (implies (and (equal b (bit-mat0 n n))
                  (bit-matp a n n)
                  (bit-matp c n n)
                  (natp n))
             (equal (tensor a b c)
                    (bit-listn0 (* n n n n n n))))
    :enable (mat-flat-of-bit-mat0
             bit-list-outer-of-bit-listn0-arg1
             bit-list-outer-of-bit-listn0-arg2))

  (defruled tensor-when-zero-c
    (implies (and (equal c (bit-mat0 n n))
                  (bit-matp a n n)
                  (bit-matp b n n)
                  (natp n))
             (equal (tensor a b c)
                    (bit-listn0 (* n n n n n n))))
    :enable (mat-flat-of-bit-mat0
             bit-list-outer-of-bit-listn0-arg1
             bit-list-outer-of-bit-listn0-arg2)))

;;; A pure abbreviation: kept enabled so that every summand denotation
;;; normalizes to tensor of the summand components, which compute through
;;; any cons structure the simplifier leaves behind.
(define summand-tensor ((s mat-triplep))
  :enabled t
  (tensor (car s) (cadr s) (caddr s))
  ///
  (defrule bit-listnp-of-summand-tensor
    (implies (and (summand-dimp s n)
                  (natp n))
             (bit-listnp (summand-tensor s) (* n n n n n n)))))

;;; Bilinearity of the denotation in each factor.  The dimensioned outer/scale
;;; lemmas of bits.lisp are brought in by explicit instantiation, with the
;;; dimensions spelled out.

(defruled tensor-of-add-a
  (implies (and (bit-matp a1 n n) (bit-matp a2 n n)
                (bit-matp b n n) (bit-matp c n n)
                (natp n))
           (equal (tensor (bit-mat-add a1 a2) b c)
                  (bit-list-add (tensor a1 b c)
                                (tensor a2 b c))))
  :use ((:instance bit-list-outer-of-add-arg1
                   (u1 (mat-flat a1)) (u2 (mat-flat a2))
                   (v (bit-list-outer (mat-flat b) (mat-flat c)))
                   (j (* n n)) (k (* n n n n))))
  :enable (tensor mat-flat-of-bit-mat-add
           bit-listnp-alt-def len-of-bit-listnp))

(defruled tensor-of-add-b
  (implies (and (bit-matp a n n) (bit-matp b1 n n)
                (bit-matp b2 n n) (bit-matp c n n)
                (natp n))
           (equal (tensor a (bit-mat-add b1 b2) c)
                  (bit-list-add (tensor a b1 c)
                                (tensor a b2 c))))
  :use ((:instance bit-list-outer-of-add-arg1
                   (u1 (mat-flat b1)) (u2 (mat-flat b2))
                   (v (mat-flat c))
                   (j (* n n)) (k (* n n)))
        (:instance bit-list-outer-of-add-arg2
                   (u (mat-flat a))
                   (v (bit-list-outer (mat-flat b1) (mat-flat c)))
                   (w (bit-list-outer (mat-flat b2) (mat-flat c)))
                   (j (* n n)) (k (* n n n n))))
  :enable (tensor mat-flat-of-bit-mat-add
           bit-listnp-alt-def len-of-bit-listnp))

(defruled tensor-of-add-c
  (implies (and (bit-matp a n n) (bit-matp b n n)
                (bit-matp c1 n n) (bit-matp c2 n n)
                (natp n))
           (equal (tensor a b (bit-mat-add c1 c2))
                  (bit-list-add (tensor a b c1)
                                (tensor a b c2))))
  :use ((:instance bit-list-outer-of-add-arg2
                   (u (mat-flat b))
                   (v (mat-flat c1)) (w (mat-flat c2))
                   (j (* n n)) (k (* n n)))
        (:instance bit-list-outer-of-add-arg2
                   (u (mat-flat a))
                   (v (bit-list-outer (mat-flat b) (mat-flat c1)))
                   (w (bit-list-outer (mat-flat b) (mat-flat c2)))
                   (j (* n n)) (k (* n n n n))))
  :enable (tensor mat-flat-of-bit-mat-add
           bit-listnp-alt-def len-of-bit-listnp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define scheme-sum ((l mat-triple-listp) (n natp))
  :returns (tt bit-list-p)
  (if (atom l)
      (bit-listn0 (* n n n n n n))
    (bit-list-add (summand-tensor (car l))
                  (scheme-sum (cdr l) n)))
  ///

  (defrule len-of-scheme-sum
    (implies (and (summand-dim-listp l n)
                  (natp n))
             (equal (len (scheme-sum l n))
                    (* n n n n n n)))
    :enable bit-listn0)

  ;; The size-constrained return theorem: an n-scheme denotes an n^6-bit
  ;; tensor.
  (defrule bit-listnp-of-scheme-sum
    (implies (and (summand-dim-listp l n)
                  (natp n))
             (bit-listnp (scheme-sum l n) (* n n n n n n)))
    :enable (bit-listnp-alt-def)
    :disable scheme-sum))

;;; scheme-sum against the obag operations: inserting a summand adds its
;;; tensor, and -- characteristic 2 -- so does deleting one.

(defruled scheme-sum-of-insert
  (implies (and (obag::bagp sch)
                (summand-listp sch n)
                (summandp x n)
                (natp n))
           (equal (scheme-sum (obag::insert x sch) n)
                  (bit-list-add (summand-tensor x)
                                (scheme-sum sch n))))
  :induct (obag::insert x sch)
  :enable (obag::insert obag::bagp obag::head obag::tail
           obag::emptyp obag::bfix scheme-sum
           bit-list-add-commutative bit-list-add-commutative-2
           bit-list-add-associative)
  :disable (summandp tensor))

(defruled scheme-sum-of-delete
  (implies (and (obag::bagp sch)
                (summand-listp sch n)
                (obag::in x sch)
                (natp n))
           (equal (scheme-sum (obag::delete x sch) n)
                  (bit-list-add (summand-tensor x)
                                (scheme-sum sch n))))
  :do-not-induct t
  :use ((:instance scheme-sum-of-insert (sch (obag::delete x sch)))
        (:instance summandp-when-in-summand-listp (s x))
        (:instance bit-list-add-cancel-1
                   (x (scheme-sum (obag::delete x sch) n))
                   (y (summand-tensor x))
                   (n (* n n n n n n))))
  :disable (tensor))
