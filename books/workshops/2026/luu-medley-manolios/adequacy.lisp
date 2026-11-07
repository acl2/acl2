; Adequacy of correct schemes: every correct scheme computes the matrix
; product over F2.
;
; A scheme sch with summands (A^r, B^r, C^r) denotes the algorithm that, on
; input matrices D and F, forms the products m_r = (A^r . D)(B^r . F) of the
; two inner products and returns the sum over r of m_r C^r; this is
; eval-scheme below.  The theorem eval-scheme-computes-product says that when
; sch is correct (correct-schemep, mm-tensor.lisp) this algorithm returns
; the ordinary product D F (bit-mat-mul below) for every D and F.
;
; The proof contracts the flat tensor representation with D and F.  A flat
; tensor of n^6 bits is a list of n^2 blocks of n^4 bits, and a block of n^4
; bits is a list of n^2 blocks of n^2 bits.  block-contract sums the blocks
; of a list with the coefficients of a bit list; tensor-contract applies it
; twice, with the flat D and then the flat F.  Because tensor is built from
; bit-list-outer, block-contract of an outer product is the outer's second
; factor scaled by an inner product (block-contract-of-bit-list-outer), so
; tensor-contract of (tensor A B C) is the flat of C scaled by
; (A . D)(B . F), and by additivity tensor-contract of a scheme-sum is the
; flat of eval-scheme.  On the other side, mm-tensor is a sum of unit
; tensors level by level (mm-tensor-3/2/1), and tensor-contract turns it
; into the matching sum of scaled unit matrices (product-3/2/1), whose
; entries collapse to the entries of bit-mat-mul by the delta form of
; bit-mat-unit.  mat-flat is injective on n x n matrices, which turns the
; flat identity into the matrix one.
;
; Validated by execution at n = 2 on all 256 pairs of 2 x 2 matrices with
; the standard scheme, and at n = 3 on spot checks, before proving; the
; checks are the local assert-event forms at the end.

(in-package "ACL2")

(include-book "span")

(local (include-book "std/lists/append" :dir :system))
(local (include-book "std/lists/take" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))
(local (include-book "std/lists/nth" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))

;; bitxor-of-0-arg1 rewrites (bitxor 0 x) to (getbit 0 x); this puts it back
;; when x is known to be a bit (the kestrel rule getbit-of-0-when-bitp lives
;; in a book that bitxor includes only locally).
(local
 (defrule getbit-0-of-bit
   (implies (bitp x)
            (equal (getbit 0 x) x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Part 1: the algorithm a scheme denotes
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; The inner product over F2 of two bit lists, and of two matrices through
;;; their flattenings: (mat-dot a d) is the sum over g, h of a[g,h] d[g,h].

(define bit-list-dot ((x bit-list-p) (y bit-list-p))
  :returns (b bitp)
  (if (and (consp x) (consp y))
      (bitxor (bitand (car x) (car y))
              (bit-list-dot (cdr x) (cdr y)))
    0))

(define mat-dot ((a bit-list-listp) (d bit-list-listp))
  :returns (b bitp)
  (bit-list-dot (mat-flat a) (mat-flat d)))

;;; Scaling a matrix by a bit, row by row.

(define bit-mat-scale ((b bitp) (a bit-list-listp))
  :returns (c bit-list-listp)
  (if (atom a)
      nil
    (cons (bit-list-scale b (car a))
          (bit-mat-scale b (cdr a))))
  ///
  (defrule bit-matp-of-bit-mat-scale
    (implies (bit-matp a m n)
             (bit-matp (bit-mat-scale b a) m n))
    :induct (bit-matp a m n)
    :enable bit-matp))

;;; The algorithm: the r-th multiplication is (A^r . D)(B^r . F), and its
;;; result is scaled onto C^r.

(define eval-scheme ((sch mat-triple-listp) (d bit-list-listp)
                     (f bit-list-listp) (n natp))
  :returns (c bit-list-listp)
  :verify-guards :after-returns
  (if (atom sch)
      (bit-mat0 n n)
    (bit-mat-add (bit-mat-scale (bitand (mat-dot (car (car sch)) d)
                                        (mat-dot (cadr (car sch)) f))
                                (caddr (car sch)))
                 (eval-scheme (cdr sch) d f n)))
  ///
  (defrule bit-matp-of-eval-scheme
    (implies (summand-dim-listp sch n)
             (bit-matp (eval-scheme sch d f n) n n))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Part 2: the ordinary matrix product
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Entry (k, l) of the product is the sum over h < n of d[k,h] f[h,l];
;;; mat-mul-entry with bound h is the partial sum over h' < h.  The guard is
;;; the dimensioned one, as for a-witness-sum in span.lisp: the mat-entry
;;; calls must be in range for bitand's guard.

(define mat-mul-entry ((d bit-list-listp) (f bit-list-listp)
                       (k natp) (l natp) (h natp) (n natp))
  :guard (and (bit-matp d n n) (bit-matp f n n) (< k n) (< l n) (<= h n))
  :guard-hints (("Goal" :in-theory (e/d (integerp-of-mat-entry) (mat-entry))
                        :do-not-induct t))
  :returns (b bitp)
  :verify-guards :after-returns
  (if (zp h)
      0
    (bitxor (bitand (mat-entry k (1- h) d) (mat-entry (1- h) l f))
            (mat-mul-entry d f k l (1- h) n))))

;;; Row k of the product, columns n-c .. n-1; then rows n-c .. n-1; then the
;;; product itself.  Built by downward recursions like bit-mat-unit.

(define bit-mat-mul-row ((d bit-list-listp) (f bit-list-listp)
                         (k natp) (c natp) (n natp))
  :guard (and (bit-matp d n n) (bit-matp f n n) (< k n) (<= c n))
  :returns (r bit-list-p)
  :verify-guards :after-returns
  (if (zp c)
      nil
    (cons (mat-mul-entry d f k (- n c) n n)
          (bit-mat-mul-row d f k (1- c) n)))
  ///
  (defrule bit-listnp-of-bit-mat-mul-row
    (bit-listnp (bit-mat-mul-row d f k c n) c)
    :enable bit-listnp))

(define bit-mat-mul-rows ((d bit-list-listp) (f bit-list-listp)
                          (c natp) (n natp))
  :guard (and (bit-matp d n n) (bit-matp f n n) (<= c n))
  :returns (a bit-list-listp)
  :verify-guards :after-returns
  (if (zp c)
      nil
    (cons (bit-mat-mul-row d f (- n c) n n)
          (bit-mat-mul-rows d f (1- c) n)))
  ///
  (defrule bit-matp-of-bit-mat-mul-rows
    (bit-matp (bit-mat-mul-rows d f c n) c n)
    :enable bit-matp))

(define bit-mat-mul ((d bit-list-listp) (f bit-list-listp) (n natp))
  :guard (and (bit-matp d n n) (bit-matp f n n))
  :returns (a bit-list-listp)
  (bit-mat-mul-rows d f n n)
  ///
  (defrule bit-matp-of-bit-mat-mul
    (bit-matp (bit-mat-mul d f n) n n)))

;;; The entry characterization of the product.  Position j of the row for
;;; columns n-c .. n-1 is column n-c+j; likewise for rows.

(defruled nth-of-bit-mat-mul-row
  (implies (and (natp j) (natp c) (< j c))
           (equal (nth j (bit-mat-mul-row d f k c n))
                  (mat-mul-entry d f k (+ j (- n c)) n n)))
  :induct (dec-dec-induct j c)
  :enable bit-mat-mul-row
  :expand ((bit-mat-mul-row d f k c n)))

(defruled nth-of-bit-mat-mul-rows
  (implies (and (natp i) (natp c) (< i c))
           (equal (nth i (bit-mat-mul-rows d f c n))
                  (bit-mat-mul-row d f (+ i (- n c)) n n)))
  :induct (dec-dec-induct i c)
  :enable bit-mat-mul-rows
  :expand ((bit-mat-mul-rows d f c n)))

(defruled mat-entry-of-bit-mat-mul
  (implies (and (natp k) (natp l) (natp n)
                (< k n) (< l n))
           (equal (mat-entry k l (bit-mat-mul d f n))
                  (mat-mul-entry d f k l n n)))
  :enable (bit-mat-mul nth-of-bit-mat-mul-rows nth-of-bit-mat-mul-row))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Part 3: block contraction
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; tt is a list of (len y) blocks of m bits; block-contract sums the blocks
;;; with the coefficients of y.  The guard says tt has enough bits; without
;;; it take would pad with nil and bit-list-scale's guard would fail.

(defrule bit-list-p-of-nthcdr
  (implies (bit-list-p x)
           (bit-list-p (nthcdr m x))))

(defrule bit-list-p-of-take
  (implies (and (bit-list-p x)
                (<= (nfix m) (len x)))
           (bit-list-p (take m x))))

(define block-contract ((tt bit-list-p) (y bit-list-p) (m natp))
  :guard (<= (* (len y) m) (len tt))
  :returns (r bit-list-p)
  :verify-guards :after-returns
  (if (atom y)
      (bit-listn0 m)
    (bit-list-add (bit-list-scale (car y) (take m tt))
                  (block-contract (nthcdr m tt) (cdr y) m)))
  ///
  (defrule len-of-block-contract
    (equal (len (block-contract tt y m))
           (nfix m)))
  (defrule bit-listnp-of-block-contract
    (implies (natp m)
             (bit-listnp (block-contract tt y m) m))
    :enable bit-listnp-alt-def
    :disable block-contract))

;;; Peeling one block off the front.

(defruled nthcdr-len-of-append
  (equal (nthcdr (len x) (append x y))
         y))

(defruled take-len-of-append
  (implies (true-listp x)
           (equal (take (len x) (append x y))
                  x)))

(defruled block-contract-of-append-block
  (implies (and (true-listp blk)
                (equal (len blk) m)
                (consp y))
           (equal (block-contract (append blk rest) y m)
                  (bit-list-add (bit-list-scale (car y) blk)
                                (block-contract rest (cdr y) m))))
  :enable (block-contract nthcdr-len-of-append take-len-of-append))

;;; Scale algebra.  The two general bilinearity facts are local proof
;;; vehicles, as in bits.lisp, whose exported forms carry dimensions that
;;; would be free variables here.

(defruled bit-list-scale-of-bit-list-scale
  (equal (bit-list-scale b (bit-list-scale c x))
         (bit-list-scale (bitand b c) x))
  :enable (bit-list-scale bitand-commutative-2))

(local
 (defruled bit-list-scale-of-bitxor-general
   (implies (and (bitp b1) (bitp b2) (bit-list-p x))
            (equal (bit-list-scale (bitxor b1 b2) x)
                   (bit-list-add (bit-list-scale b1 x)
                                 (bit-list-scale b2 x))))
   :enable (bit-list-scale bit-list-add)))

(local
 (defruled bit-list-scale-of-add-general
   (implies (and (bitp b) (bit-list-p x) (bit-list-p y))
            (equal (bit-list-scale b (bit-list-add x y))
                   (bit-list-add (bit-list-scale b x)
                                 (bit-list-scale b y))))
   :induct (bit-list-add x y)
   :enable (bit-list-scale bit-list-add)))

;;; The block lemma: contracting an outer product u (x) v with y scales v by
;;; the inner product of u and y.

(defruled block-contract-of-bit-list-outer
  (implies (and (bit-list-p u) (bit-list-p y) (bit-list-p v)
                (equal (len u) (len y))
                (equal m (len v)))
           (equal (block-contract (bit-list-outer u v) y m)
                  (bit-list-scale (bit-list-dot u y) v)))
  :induct (cdr-cdr-induct u y)
  :enable (bit-list-outer bit-list-dot block-contract
           block-contract-of-append-block
           bit-list-scale-of-bit-list-scale
           bit-list-scale-of-bitxor-general))

;;; Linearity of block-contract in the tensor argument: take and nthcdr pass
;;; through bit-list-add and bit-list-scale.

(defruled take-of-bit-list-add
  (implies (and (<= (nfix m) (len x))
                (<= (nfix m) (len y)))
           (equal (take m (bit-list-add x y))
                  (bit-list-add (take m x) (take m y))))
  :induct (list (cdr-dec-induct x m) (cdr-dec-induct y m))
  :enable bit-list-add)

(defruled nthcdr-of-bit-list-add
  (equal (nthcdr m (bit-list-add x y))
         (bit-list-add (nthcdr m x) (nthcdr m y)))
  :induct (list (cdr-dec-induct x m) (cdr-dec-induct y m))
  :enable bit-list-add)

(defruled take-of-bit-list-scale
  (implies (<= (nfix m) (len x))
           (equal (take m (bit-list-scale b x))
                  (bit-list-scale b (take m x))))
  :induct (cdr-dec-induct x m)
  :enable bit-list-scale)

(defruled nthcdr-of-bit-list-scale
  (equal (nthcdr m (bit-list-scale b x))
         (bit-list-scale b (nthcdr m x)))
  :induct (cdr-dec-induct x m)
  :enable bit-list-scale)

(defruled block-contract-of-bit-list-add
  (implies (and (bit-list-p t1) (bit-list-p t2) (bit-list-p y) (natp m)
                (<= (* (len y) m) (len t1))
                (<= (* (len y) m) (len t2)))
           (equal (block-contract (bit-list-add t1 t2) y m)
                  (bit-list-add (block-contract t1 y m)
                                (block-contract t2 y m))))
  :induct (list (block-contract t1 y m) (block-contract t2 y m))
  :enable (block-contract take-of-bit-list-add nthcdr-of-bit-list-add
           bit-list-scale-of-add-general
           bit-list-add-commutative bit-list-add-commutative-2
           bit-list-add-associative))

;; bit-list-scale-of-0 is disabled so that the b = 0 case is not rewritten
;; away from the shape the induction hypothesis has.
(defruled block-contract-of-bit-list-scale
  (implies (and (bitp b) (bit-list-p tt) (bit-list-p y) (natp m)
                (<= (* (len y) m) (len tt)))
           (equal (block-contract (bit-list-scale b tt) y m)
                  (bit-list-scale b (block-contract tt y m))))
  :induct (block-contract tt y m)
  :enable (block-contract take-of-bit-list-scale nthcdr-of-bit-list-scale
           bit-list-scale-of-bit-list-scale bit-list-scale-of-add-general)
  :disable (bit-list-scale-of-0))

;; The zero tensor is 0 scaled onto itself, so this is a case of linearity.
(defruled block-contract-of-bit-listn0
  (implies (and (natp m) (natp k) (bit-list-p y)
                (<= (* (len y) m) k))
           (equal (block-contract (bit-listn0 k) y m)
                  (bit-listn0 m)))
  :use ((:instance block-contract-of-bit-list-scale
                   (b 0) (tt (bit-listn0 k)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Part 4: contracting a tensor with D and F
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tensor-contract ((tt bit-list-p) (d bit-list-listp)
                         (f bit-list-listp) (n natp))
  :guard (and (bit-listnp tt (* n n n n n n))
              (bit-matp d n n)
              (bit-matp f n n))
  :guard-hints (("Goal" :in-theory (enable len-of-bit-listnp)))
  :returns (r bit-list-p)
  (block-contract (block-contract tt (mat-flat d) (* n n n n))
                  (mat-flat f)
                  (* n n))
  ///
  (defrule bit-listnp-of-tensor-contract
    (implies (natp n)
             (bit-listnp (tensor-contract tt d f n) (* n n)))))

(defruled bit-list-scale-of-append
  (equal (bit-list-scale b (append x y))
         (append (bit-list-scale b x) (bit-list-scale b y)))
  :enable bit-list-scale)

(defruled mat-flat-of-bit-mat-scale
  (equal (mat-flat (bit-mat-scale b a))
         (bit-list-scale b (mat-flat a)))
  :enable (mat-flat bit-mat-scale bit-list-scale bit-list-scale-of-append))

;;; The contraction of one summand's tensor: the block lemma twice.

(defruled tensor-contract-of-tensor
  (implies (and (bit-matp a n n) (bit-matp b n n) (bit-matp c n n)
                (bit-matp d n n) (bit-matp f n n)
                (natp n))
           (equal (tensor-contract (tensor a b c) d f n)
                  (mat-flat (bit-mat-scale (bitand (mat-dot a d) (mat-dot b f))
                                           c))))
  :enable (tensor-contract tensor mat-dot mat-flat-of-bit-mat-scale
           bit-list-scale-of-bit-list-scale)
  :use ((:instance block-contract-of-bit-list-outer
                   (u (mat-flat a))
                   (v (bit-list-outer (mat-flat b) (mat-flat c)))
                   (y (mat-flat d))
                   (m (* n n n n)))
        (:instance block-contract-of-bit-list-scale
                   (b (bit-list-dot (mat-flat a) (mat-flat d)))
                   (tt (bit-list-outer (mat-flat b) (mat-flat c)))
                   (y (mat-flat f))
                   (m (* n n)))
        (:instance block-contract-of-bit-list-outer
                   (u (mat-flat b))
                   (v (mat-flat c))
                   (y (mat-flat f))
                   (m (* n n)))))

(defruled tensor-contract-of-bit-list-add
  (implies (and (bit-listnp t1 (* n n n n n n))
                (bit-listnp t2 (* n n n n n n))
                (bit-matp d n n) (bit-matp f n n)
                (natp n))
           (equal (tensor-contract (bit-list-add t1 t2) d f n)
                  (bit-list-add (tensor-contract t1 d f n)
                                (tensor-contract t2 d f n))))
  :enable (tensor-contract len-of-bit-listnp)
  :use ((:instance block-contract-of-bit-list-add
                   (y (mat-flat d)) (m (* n n n n)))
        (:instance block-contract-of-bit-list-add
                   (t1 (block-contract t1 (mat-flat d) (* n n n n)))
                   (t2 (block-contract t2 (mat-flat d) (* n n n n)))
                   (y (mat-flat f)) (m (* n n)))))

(defruled tensor-contract-of-bit-listn0
  (implies (and (bit-matp d n n) (bit-matp f n n)
                (natp n))
           (equal (tensor-contract (bit-listn0 (* n n n n n n)) d f n)
                  (bit-listn0 (* n n))))
  :enable (tensor-contract)
  :use ((:instance block-contract-of-bit-listn0
                   (k (* n n n n n n)) (y (mat-flat d)) (m (* n n n n)))
        (:instance block-contract-of-bit-listn0
                   (k (* n n n n)) (y (mat-flat f)) (m (* n n)))))

;;; mat-flat-of-bit-mat-add carries its dimensions as free variables; this
;;; form binds n through the eval-scheme term so it can fire inside the
;;; induction below.

(defruled mat-flat-of-bit-mat-add-eval-scheme
  (implies (and (bit-matp x n n)
                (summand-dim-listp sch n)
                (natp n))
           (equal (mat-flat (bit-mat-add x (eval-scheme sch d f n)))
                  (bit-list-add (mat-flat x)
                                (mat-flat (eval-scheme sch d f n)))))
  :use ((:instance mat-flat-of-bit-mat-add
                   (a x) (b (eval-scheme sch d f n)) (m n))))

;;; The contraction of a scheme's denotation is the flat of the algorithm's
;;; output.

(defruled tensor-contract-of-scheme-sum
  (implies (and (summand-dim-listp sch n)
                (bit-matp d n n) (bit-matp f n n)
                (natp n))
           (equal (tensor-contract (scheme-sum sch n) d f n)
                  (mat-flat (eval-scheme sch d f n))))
  :induct (scheme-sum sch n)
  :enable (scheme-sum eval-scheme tensor-contract-of-bit-list-add
           tensor-contract-of-tensor tensor-contract-of-bit-listn0
           mat-flat-of-bit-mat-add-eval-scheme mat-flat-of-bit-mat0)
  :disable (tensor tensor-contract))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Part 5: contracting the matrix multiplication tensor
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; The inner product with a unit matrix picks out an entry.  The flat of
;;; e_ij is i*n zeros, the unit list at j, and zeros to the end.

(defruled bit-list-dot-of-append-arg1
  (equal (bit-list-dot (append x1 x2) y)
         (bitxor (bit-list-dot x1 y)
                 (bit-list-dot x2 (nthcdr (len x1) y))))
  :induct (bit-list-dot x1 y)
  :enable bit-list-dot)

(defruled bit-list-dot-of-bit-listn0
  (equal (bit-list-dot (bit-listn0 k) y)
         0)
  :induct (cdr-dec-induct y k)
  :enable (bit-listn0 repeat bit-list-dot))

(defruled bit-list-dot-of-bit-unit-list
  (implies (and (natp j) (natp n) (< j n)
                (bit-list-p y) (< j (len y)))
           (equal (bit-list-dot (bit-unit-list j n) y)
                  (nth j y)))
  :induct (list (bit-unit-list j n) (cdr-dec-induct y j))
  :enable (bit-unit-list bit-list-dot bit-list-dot-of-bit-listn0
           bitp-of-nth-when-bit-list-p))

(defruled append-of-bit-listn0-assoc
  (equal (append (bit-listn0 m) (append (bit-listn0 n) rest))
         (append (bit-listn0 (+ (nfix m) (nfix n))) rest))
  :use ((:instance associativity-of-append
                   (a (bit-listn0 m)) (b (bit-listn0 n)) (c rest)))
  :disable (associativity-of-append))

(defruled mat-flat-of-bit-mat-unit
  (implies (and (natp i) (natp m) (natp n) (< i m))
           (equal (mat-flat (bit-mat-unit i j m n))
                  (append (bit-listn0 (* i n))
                          (append (bit-unit-list j n)
                                  (bit-listn0 (* (- m (+ i 1)) n))))))
  :induct (bit-mat-unit i j m n)
  :enable (bit-mat-unit mat-flat mat-flat-of-bit-mat0
           append-of-bit-listn0-assoc))

(local
 (defruled pair-index-upper-bound
   (implies (and (natp i) (natp j) (natp n)
                 (< i n) (< j n))
            (< (+ j (* i n)) (* n n)))
   :rule-classes :linear
   :hints (("Goal" :nonlinearp t))))

(defruled mat-dot-of-bit-mat-unit
  (implies (and (bit-matp d n n)
                (natp n) (natp i) (natp j)
                (< i n) (< j n))
           (equal (mat-dot (bit-mat-unit i j n n) d)
                  (mat-entry i j d)))
  :enable (mat-dot mat-flat-of-bit-mat-unit bit-list-dot-of-append-arg1
           bit-list-dot-of-bit-listn0 bit-list-dot-of-bit-unit-list
           pair-index-upper-bound)
  :disable (mat-entry))

;;; The product as a sum of scaled unit matrices, in the three nested levels
;;; of mm-tensor: product-3 sums d[i,j] f[j,k'] e_ik' over k' < k, product-2
;;; sums product-3 over j' < j, product-1 sums product-2 over i' < i.

(define product-3 ((d bit-list-listp) (f bit-list-listp)
                   (i natp) (j natp) (k natp) (n natp))
  :guard (and (bit-matp d n n) (bit-matp f n n) (< i n) (< j n) (<= k n))
  :guard-hints (("Goal" :in-theory (e/d (integerp-of-mat-entry) (mat-entry))
                        :do-not-induct t))
  :returns (a bit-list-listp)
  :verify-guards :after-returns
  (if (zp k)
      (bit-mat0 n n)
    (bit-mat-add (bit-mat-scale (bitand (mat-entry i j d)
                                        (mat-entry j (1- k) f))
                                (bit-mat-unit i (1- k) n n))
                 (product-3 d f i j (1- k) n)))
  ///
  (defrule bit-matp-of-product-3
    (bit-matp (product-3 d f i j k n) n n)))

(define product-2 ((d bit-list-listp) (f bit-list-listp)
                   (i natp) (j natp) (n natp))
  :guard (and (bit-matp d n n) (bit-matp f n n) (< i n) (<= j n))
  :returns (a bit-list-listp)
  :verify-guards :after-returns
  (if (zp j)
      (bit-mat0 n n)
    (bit-mat-add (product-3 d f i (1- j) n n)
                 (product-2 d f i (1- j) n)))
  ///
  (defrule bit-matp-of-product-2
    (bit-matp (product-2 d f i j n) n n)))

(define product-1 ((d bit-list-listp) (f bit-list-listp) (i natp) (n natp))
  :guard (and (bit-matp d n n) (bit-matp f n n) (<= i n))
  :returns (a bit-list-listp)
  :verify-guards :after-returns
  (if (zp i)
      (bit-mat0 n n)
    (bit-mat-add (product-2 d f (1- i) n n)
                 (product-1 d f (1- i) n)))
  ///
  (defrule bit-matp-of-product-1
    (bit-matp (product-1 d f i n) n n)))

;;; mat-flat-of-bit-mat-add in the shapes the level inductions produce (the
;;; second summand binds n).

(defruled mat-flat-of-bit-mat-add-product-3
  (implies (and (bit-matp x n n) (natp n))
           (equal (mat-flat (bit-mat-add x (product-3 d f i j k n)))
                  (bit-list-add (mat-flat x)
                                (mat-flat (product-3 d f i j k n)))))
  :use ((:instance mat-flat-of-bit-mat-add
                   (a x) (b (product-3 d f i j k n)) (m n))))

(defruled mat-flat-of-bit-mat-add-product-2
  (implies (and (bit-matp x n n) (natp n))
           (equal (mat-flat (bit-mat-add x (product-2 d f i j n)))
                  (bit-list-add (mat-flat x)
                                (mat-flat (product-2 d f i j n)))))
  :use ((:instance mat-flat-of-bit-mat-add
                   (a x) (b (product-2 d f i j n)) (m n))))

(defruled mat-flat-of-bit-mat-add-product-1
  (implies (and (bit-matp x n n) (natp n))
           (equal (mat-flat (bit-mat-add x (product-1 d f i n)))
                  (bit-list-add (mat-flat x)
                                (mat-flat (product-1 d f i n)))))
  :use ((:instance mat-flat-of-bit-mat-add
                   (a x) (b (product-1 d f i n)) (m n))))

;;; Level by level: the contraction of mm-tensor-3/2/1 is the flat of
;;; product-3/2/1, by additivity and the per-summand contraction, with the
;;; unit inner products read as entries.

(defruled tensor-contract-of-mm-tensor-3
  (implies (and (bit-matp d n n) (bit-matp f n n)
                (natp n) (natp i) (natp j) (natp k)
                (< i n) (< j n) (<= k n))
           (equal (tensor-contract (mm-tensor-3 i j k n) d f n)
                  (mat-flat (product-3 d f i j k n))))
  :induct (mm-tensor-3 i j k n)
  :enable (mm-tensor-3 product-3 tensor-contract-of-bit-list-add
           tensor-contract-of-tensor tensor-contract-of-bit-listn0
           mat-flat-of-bit-mat-add-product-3
           mat-flat-of-bit-mat0 mat-dot-of-bit-mat-unit)
  :disable (tensor tensor-contract mat-entry))

(defruled tensor-contract-of-mm-tensor-2
  (implies (and (bit-matp d n n) (bit-matp f n n)
                (natp n) (natp i) (natp j)
                (< i n) (<= j n))
           (equal (tensor-contract (mm-tensor-2 i j n) d f n)
                  (mat-flat (product-2 d f i j n))))
  :induct (mm-tensor-2 i j n)
  :enable (mm-tensor-2 product-2 tensor-contract-of-bit-list-add
           tensor-contract-of-mm-tensor-3 tensor-contract-of-bit-listn0
           mat-flat-of-bit-mat-add-product-2 mat-flat-of-bit-mat0)
  :disable (tensor tensor-contract mat-entry))

(defruled tensor-contract-of-mm-tensor-1
  (implies (and (bit-matp d n n) (bit-matp f n n)
                (natp n) (natp i)
                (<= i n))
           (equal (tensor-contract (mm-tensor-1 i n) d f n)
                  (mat-flat (product-1 d f i n))))
  :induct (mm-tensor-1 i n)
  :enable (mm-tensor-1 product-1 tensor-contract-of-bit-list-add
           tensor-contract-of-mm-tensor-2 tensor-contract-of-bit-listn0
           mat-flat-of-bit-mat-add-product-1 mat-flat-of-bit-mat0)
  :disable (tensor tensor-contract mat-entry))

(defruled tensor-contract-of-mm-tensor
  (implies (and (bit-matp d n n) (bit-matp f n n)
                (natp n))
           (equal (tensor-contract (mm-tensor n) d f n)
                  (mat-flat (product-1 d f n n))))
  :enable (mm-tensor tensor-contract-of-mm-tensor-1))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Part 6: the unit-matrix sum is the product
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Entries through bit-mat-scale.

(defruled nth-row-of-bit-mat-scale
  (implies (< (nfix i) (len a))
           (equal (nth i (bit-mat-scale b a))
                  (bit-list-scale b (nth i a))))
  :induct (cdr-dec-induct a i)
  :enable bit-mat-scale)

(defruled mat-entry-of-bit-mat-scale
  (implies (and (bit-matp a m n)
                (natp m) (natp n) (natp i) (natp j)
                (< i m) (< j n))
           (equal (mat-entry i j (bit-mat-scale b a))
                  (bitand b (mat-entry i j a))))
  :do-not-induct t
  :use ((:instance nth-row-of-bit-mat-scale)
        (:instance len-of-bit-matp)
        (:instance bit-listnp-of-nth-when-bit-matp (x a))
        (:instance len-of-bit-listnp (x (nth i a)))))

;;; mat-entry-of-bit-mat-add in the three shapes the level inductions
;;; produce; each binds n through the summand that carries it.

(defruled mat-entry-of-bit-mat-add-unit-scale
  (implies (and (bit-matp rest n n)
                (natp n) (natp a) (natp b) (natp i) (natp k)
                (< a n) (< b n) (< i n) (< k n))
           (equal (mat-entry a b (bit-mat-add (bit-mat-scale s (bit-mat-unit i k n n))
                                              rest))
                  (bitxor (if (and (equal a i) (equal b k)) (bitand s 1) 0)
                          (mat-entry a b rest))))
  :do-not-induct t
  :disable (mat-entry)
  :use ((:instance mat-entry-of-bit-mat-add
                   (x (bit-mat-scale s (bit-mat-unit i k n n))) (y rest)
                   (m n) (i a) (j b))
        (:instance mat-entry-of-bit-mat-scale
                   (b s) (a (bit-mat-unit i k n n)) (m n) (i a) (j b))))

(defruled mat-entry-of-bit-mat-add-product-3
  (implies (and (bit-matp rest n n)
                (natp n) (natp a) (natp b)
                (< a n) (< b n))
           (equal (mat-entry a b (bit-mat-add (product-3 d f i j k n) rest))
                  (bitxor (mat-entry a b (product-3 d f i j k n))
                          (mat-entry a b rest))))
  :do-not-induct t
  :disable (mat-entry)
  :use ((:instance mat-entry-of-bit-mat-add
                   (x (product-3 d f i j k n)) (y rest) (m n) (i a) (j b))))

(defruled mat-entry-of-bit-mat-add-product-2
  (implies (and (bit-matp rest n n)
                (natp n) (natp a) (natp b)
                (< a n) (< b n))
           (equal (mat-entry a b (bit-mat-add (product-2 d f i j n) rest))
                  (bitxor (mat-entry a b (product-2 d f i j n))
                          (mat-entry a b rest))))
  :do-not-induct t
  :disable (mat-entry)
  :use ((:instance mat-entry-of-bit-mat-add
                   (x (product-2 d f i j n)) (y rest) (m n) (i a) (j b))))

;;; The entries of the three levels: a delta in the row for product-3, the
;;; partial sum mat-mul-entry for product-2, and the full sum below row i
;;; for product-1.

(defruled mat-entry-of-product-3
  (implies (and (bit-matp d n n) (bit-matp f n n)
                (natp n) (natp i) (natp j) (natp k) (natp a) (natp b)
                (< i n) (< j n) (<= k n) (< a n) (< b n))
           (equal (mat-entry a b (product-3 d f i j k n))
                  (if (and (equal a i) (< b k))
                      (bitand (mat-entry i j d) (mat-entry j b f))
                    0)))
  :induct (product-3 d f i j k n)
  :enable (product-3 mat-entry-of-bit-mat-add-unit-scale)
  :disable (mat-entry))

(defruled mat-entry-of-product-2
  (implies (and (bit-matp d n n) (bit-matp f n n)
                (natp n) (natp i) (natp j) (natp a) (natp b)
                (< i n) (<= j n) (< a n) (< b n))
           (equal (mat-entry a b (product-2 d f i j n))
                  (if (equal a i)
                      (mat-mul-entry d f a b j n)
                    0)))
  :induct (product-2 d f i j n)
  :enable (product-2 mat-mul-entry mat-entry-of-bit-mat-add-product-3
           mat-entry-of-product-3)
  :disable (mat-entry))

(defruled mat-entry-of-product-1
  (implies (and (bit-matp d n n) (bit-matp f n n)
                (natp n) (natp i) (natp a) (natp b)
                (<= i n) (< a n) (< b n))
           (equal (mat-entry a b (product-1 d f i n))
                  (if (< a i)
                      (mat-mul-entry d f a b n n)
                    0)))
  :induct (product-1 d f i n)
  :enable (product-1 mat-entry-of-bit-mat-add-product-2
           mat-entry-of-product-2)
  :disable (mat-entry))

;;; Both are n x n with the same entries, so they are equal (mat-diff-pos).

(defruled product-1-is-bit-mat-mul
  (implies (and (bit-matp d n n) (bit-matp f n n)
                (natp n))
           (equal (product-1 d f n n)
                  (bit-mat-mul d f n)))
  :do-not-induct t
  :disable (mat-entry product-1 bit-mat-mul)
  :use ((:instance mat-diff-pos-correct
                   (x (product-1 d f n n)) (y (bit-mat-mul d f n)) (m n))
        (:instance mat-entry-of-product-1
                   (i n)
                   (a (car (mat-diff-pos (product-1 d f n n) (bit-mat-mul d f n))))
                   (b (cdr (mat-diff-pos (product-1 d f n n) (bit-mat-mul d f n)))))
        (:instance mat-entry-of-bit-mat-mul
                   (k (car (mat-diff-pos (product-1 d f n n) (bit-mat-mul d f n))))
                   (l (cdr (mat-diff-pos (product-1 d f n n) (bit-mat-mul d f n)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Part 7: adequacy
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Flattening is injective on m x n matrices: unequal matrices differ at a
;;; valid position, and nth-of-mat-flat reads that position off the flats.

(defrule mat-flat-injective
  (implies (and (bit-matp a m n)
                (bit-matp b m n)
                (natp m) (natp n)
                (equal (mat-flat a) (mat-flat b)))
           (equal a b))
  :rule-classes nil
  :do-not-induct t
  :disable (mat-entry nth-of-mat-flat)
  :use ((:instance mat-diff-pos-correct (x a) (y b))
        (:instance nth-of-mat-flat
                   (a a)
                   (i (car (mat-diff-pos a b)))
                   (j (cdr (mat-diff-pos a b))))
        (:instance nth-of-mat-flat
                   (a b)
                   (i (car (mat-diff-pos a b)))
                   (j (cdr (mat-diff-pos a b))))))

;;; The chain: flat(eval-scheme) = contraction of scheme-sum = contraction
;;; of mm-tensor [correctness] = flat(product-1) = flat(bit-mat-mul).

(defrule eval-scheme-computes-product
  (implies (and (correct-schemep sch n)
                (natp n)
                (bit-matp d n n)
                (bit-matp f n n))
           (equal (eval-scheme sch d f n)
                  (bit-mat-mul d f n)))
  :do-not-induct t
  :enable (correct-schemep)
  :disable (eval-scheme bit-mat-mul mm-tensor tensor-contract product-1)
  :use ((:instance mat-flat-injective
                   (a (eval-scheme sch d f n)) (b (bit-mat-mul d f n)) (m n))
        (:instance tensor-contract-of-scheme-sum)
        (:instance tensor-contract-of-mm-tensor)
        (:instance product-1-is-bit-mat-mul)))
