
;; Make more defabbrevs!!!

;; A Bit vector library supporting all the primitives
;; needed for the bit vector benchmarks.

;; You can tell which functions are the top-level functions, which need rewrite
;; rules, because they are defined with defund (defun and disable).  These
;; functions are my implementation of the bit-vector functions in the
;; SMT library, described at:
;; http://combination.cs.uiowa.edu/smtlib

;; Argument name conventions:
;; * "n" or "n<arg-name>" (e.g. "nx") is used to denote natural numbers
;;   representing the size of the bit vectors input to the function.  These
;;   arguments are not part of the original SMT-lib functions, but come
;;   from the move from a typed to an untyped language.  These arguments
;;   will be constant for any given SMT expression.
;; * "j" or "k": arguments that take on natural numbers present in the
;;   original SMT-lib function.  These numbers will be constant for any
;;   given SMT expression.
;; * "x" or "y": arguments that take on Bit vectors values.

;; One issue I've had to grapple with is whether use a strict bit vector
;; representation, where all bit vectors that are equal are really equal
;; (i.e. there is only one legal representation for each bit vector),
;; or whether to use a "loose" representation
;; (e.g. '(t t), '(t t nil nil), and '(t t nil nil t) all can be used to
;; represent the four bit, bit vector "12").  For now, I'm using the loose
;; representation.  However, every function has all the inputs needed so
;; that I can switch if needed.
;;
;; I expect that the "loose" representation can achieve superior performance
;; if we assume all formulas are well-typed.  The downside is that we
;; need this "well-typed" assumption, so none of the rewrite rules we
;; want are actually valid theorems.  My strategy for now is going to be
;; to solve the SMT benchmarks as effeciently as possible, even if that
;; means using invalid rewrite rules (but with the hidden knowledge that
;; all formulas are well-typed).
;;
;; For the purpose of these rewrite rules, it is best to assume that
;; each top-level function "(f n x)" returning an "(f-output-size n)"
;; bit, bit vector is redefined to be "(f-safe n x)" where "(f-safe n x)" is:
;;
;; (defun f-safe (n x)
;;   (map-to-bv (f-output-size n) (f n x)))
;;
;; See the definition of map-to-bv below.  This ensures that every function
;; returns a bit vector in the "strict" representation so that (bv-eq n x y)
;; implies (equal x y).  Note that mapping inputs into the strict
;; representation shouldn't be necessary because the functions are designed
;; to operate correctly given the "loose" representation.

;; Furthermore, note that when designing these functions it's important to
;; keep duplication to a minimum, especially during recursive calls,
;; since my SAT algorithm does not remove redundance.  For example,
;; (if x (bv-not 4 y) (bv-not 4 y)) will lead to two seperate
;; unrollings of bv-not!  Of course, I have plans to fix this...

(in-package "ACL2")
(set-irrelevant-formals-ok t)

(include-book "../clause-processors/sym-str")

(defun bvp (x)
  (declare (xargs :guard t))
  (and (consp x) (natp (car x)) (true-listp (cdr x))))

(defun bv-size (x)
  (declare (xargs :guard (bvp x)))
  (mbe :exec (car x)
       :logic (nfix (car x))))

(defun bv-raw-bv (x)
  (declare (xargs :guard (bvp x)))
  (cdr x))

(defun make-bv (sz x)
  (declare (xargs :guard t))
  (cons sz x))

(defund bv-eq-raw (n x y)
  (declare (xargs :guard (and (natp n)
                              (true-listp x)
                              (true-listp y))))
  (cond
   ((zp n)
    t)
   ((iff (car x) (car y))
    (bv-eq-raw (1- n) (cdr x) (cdr y)))
   (t
    nil)))

(defund bv-eq (x y)
  (declare (xargs :guard (and (bvp x) (bvp y))))
  (let ((sx (bv-size x))
        (sy (bv-size y)))
    (cond
     ((= sx sy)
      (bv-eq-raw sx (bv-raw-bv x) (bv-raw-bv y)))
     (t
      nil))))

(table bv-defeval-sigs 'bv-eq '(x y) :put)

(skip-proofs (defequiv bv-eq))

;; Generally speaking, we don't worry about the fact that
;; a bit vector may have some trailing irrelevant bits
;; on it (e.g. a four bit, bit vector representing
;; 1011 may be '(t nil t t t nil t)).  Sometimes, however,
;; we need to know that these trailing bits are gone and
;; thus we use the following function.
(defund rem-extra-bits-raw (n x)
  (declare (xargs :guard (and (natp n) (true-listp x))))
  (cond
   ((zp n)
    nil)
   (t
    (cons (car x) (rem-extra-bits-raw (1- n) (cdr x))))))

;; If we're expecting an actual bit vector that is larger than
;; the real bit vector, we really do NEED to get rid of those
;; bits.
(defun bv-truncated-raw-bv (n x)
  (declare (xargs :guard (and (natp n) (bvp x))))
  (cond
   ((< (bv-size x) n)
    (rem-extra-bits-raw (bv-size x) (bv-raw-bv x)))
   (t
    (bv-raw-bv x))))

#|
;; Currently figuring out why this works and the other doesn't
;; .... Is this bv-eq-bv-concat's faulst???
(defun bv-truncated-raw-bv (n x)
  (declare (xargs :guard (and (natp n) (bvp x))))
  (cond
   ((< (bv-size x) n)
    (rem-extra-bits-raw n (bv-raw-bv x)))
   (t
    (bv-raw-bv x))))
|# ;|

;; ------------------------------------------------------------

(defun bv-nat-typep (x)
  (declare (xargs :guard t))
  (equal x 'nat))

(defun bv-bool-typep (x)
  (declare (xargs :guard t))
  (equal x 'bool))

(defun bv-bitvec-typep (x)
  (declare (xargs :guard t))
  (and (consp x)
       (consp (cdr x))
       (equal (cddr x) nil)
       (equal (car x) 'bitvec)))

(defun bv-bitvec-size (x)
  (declare (xargs :guard (bv-bitvec-typep x)))
  (cadr x))

(defun bv-typep (x)
  (declare (xargs :guard t))
  (or (bv-nat-typep x)
      (bv-bool-typep x)
      (bv-bitvec-typep x)))

(defun bv-type-listp (x)
  (declare (xargs :guard t))
  (cond
   ((atom x)
    (equal x nil))
   ((bv-typep (car x))
    (bv-type-listp (cdr x)))
   (t
    nil)))

(defun create-defbv-guards (rev-input-list rev-input-type-list acc)
  (declare (xargs :guard (and (bv-type-listp rev-input-type-list)
                              (true-listp rev-input-list))))
  (cond
   ((endp rev-input-list)
    acc)

   ((bv-bool-typep (car rev-input-type-list))
    (create-defbv-guards (cdr rev-input-list)
                         (cdr rev-input-type-list)
                         (cons `(Booleanp ,(car rev-input-list)) acc)))

   ((bv-nat-typep (car rev-input-type-list))
    (create-defbv-guards (cdr rev-input-list)
                         (cdr rev-input-type-list)
                         (cons `(natp ,(car rev-input-list)) acc)))

   (t ;;(eq (caar rev-input-type-list) 'bitvec)
    (create-defbv-guards (cdr rev-input-list)
                         (cdr rev-input-type-list)
                         (cons `(bvp ,(car rev-input-list)) acc)))))

(defun create-defbv-raw-args (rev-input-list rev-input-type-list acc)
  (declare (xargs :guard (and (bv-type-listp rev-input-type-list)
                              (true-listp rev-input-list))))
  (cond
   ((or (endp rev-input-list) (endp rev-input-type-list))
    acc)

   ((bv-bool-typep (car rev-input-type-list))
    (create-defbv-raw-args (cdr rev-input-list)
                           (cdr rev-input-type-list)
                           (cons (car rev-input-list) acc)))

   ((bv-nat-typep (car rev-input-type-list))
    (create-defbv-raw-args (cdr rev-input-list)
                           (cdr rev-input-type-list)
                           (cons (car rev-input-list) acc)))

   (t ;;(eq (caar rev-input-type-list) 'bitvec)
    (create-defbv-raw-args
     (cdr rev-input-list)
     (cdr rev-input-type-list)
     (cons `(bv-truncated-raw-bv ,(bv-bitvec-size (car rev-input-type-list))
                                 ,(car rev-input-list))
           acc)))))

(defun create-defbv-equiv (type)
  (declare (xargs :guard (bv-typep type)))
  (cond
   ((bv-bool-typep type)
    'iff)
   ((bv-nat-typep type)
    'equal)
   (t
    'bv-eq)))

(defun create-defbv-defcongs1 (n rev-input-type-list call out-equiv acc)
  (declare (xargs :guard (and (integerp n) (bv-type-listp rev-input-type-list))))
  (cond
   ((endp rev-input-type-list)
    acc)

   ((bv-bool-typep (car rev-input-type-list))
    (create-defbv-defcongs1
     (1- n)
     (cdr rev-input-type-list)
     call
     out-equiv
     (cons `(skip-proofs (defcong iff ,out-equiv ,call ,n)) acc)))

   ((bv-nat-typep (car rev-input-type-list))
    (create-defbv-defcongs1 (1- n) (cdr rev-input-type-list) call out-equiv acc))

   (t ;;(eq (caar rev-input-type-list) 'bitvec)
    (create-defbv-defcongs1
     (1- n)
     (cdr rev-input-type-list)
     call
     out-equiv
     (cons `(skip-proofs (defcong bv-eq ,out-equiv ,call ,n)) acc)))))

(defun create-defbv-defcongs (rev-input-type-list name args out-type)
  (declare (xargs :guard (and (bv-type-listp rev-input-type-list)
                              (bv-typep out-type))))
  (create-defbv-defcongs1 (len rev-input-type-list)
                          rev-input-type-list
                          `(,name . ,args)
                          (create-defbv-equiv out-type)
                          nil))

(defmacro defbv (name args sig raw-name)
  (declare (xargs :guard (and (bv-type-listp (cdr sig))
                              (true-listp args))))
  (let* ((size-thm-name (symbol-from-sym-str
                         name
                         "-BV-SIZE-SIMPLIFICATION"))
         (rev-sig (revappend (cdr sig) nil))
         (rev-input-list (revappend args nil))
         (out-type (car rev-sig))
         (rev-input-type-list (cdr rev-sig)))
    `(encapsulate
      nil

      (defun ,name ,args
        (declare (xargs :guard (and .
                                    ,(create-defbv-guards rev-input-list rev-input-type-list
                                                          nil))))
        ,(if (bv-bitvec-typep out-type)
             `(make-bv ,(bv-bitvec-size out-type)
                       (,raw-name . ,(create-defbv-raw-args rev-input-list rev-input-type-list nil)))
           `(,raw-name . ,(create-defbv-raw-args rev-input-list rev-input-type-list nil))))

      ,(if (bv-bitvec-typep out-type)
           `(defthm ,size-thm-name
              (equal (bv-size (,name . ,args))
                     (nfix ,(bv-bitvec-size out-type))))
         `(value-triple nil) ;; This value-triple is just a NO-op
         )

      (in-theory (disable ,name))

      (table bv-defeval-sigs (quote ,name) (quote ,args) :put)

      .

      ,(create-defbv-defcongs rev-input-type-list name args out-type))))

;; ------------------------------------------------------------

;; Return the unsigned integer corresponding to the
;; n bit, bit vector x.
(defun bv-to-num-raw1 (n x)
  (declare (xargs :guard (and (natp n)
                              (true-listp x))
                  :verify-guards nil))
  (cond
   ((zp n)
    (cons 0 1))
   (t
    (let* ((ans (bv-to-num-raw1 (1- n) (cdr x)))
           (q (car ans))
           (expt2 (cdr ans)))
      (cond
       ((car x)
        (cons (+ expt2 q) (* 2 expt2)))
       (t
        (cons q (* 2 expt2))))))))

(defthm bv-to-num-raw1-int
  (and (acl2-numberp (car (bv-to-num-raw1 n x)))
       (acl2-numberp (cdr (bv-to-num-raw1 n x)))))

(verify-guards bv-to-num-raw1)

(defun bv-to-num-raw (n x)
  (declare (xargs :guard (and (natp n)
                              (true-listp x))))
  (car (bv-to-num-raw1 n x)))

(defbv bv-to-num (n x)
  (sig nat (bitvec n) nat)
  bv-to-num-raw)

(defun fill0-raw (j)
   (declare (xargs :guard t)
            (ignore j))
   nil)

(defbv fill0 (j)
  (sig nat (bitvec j))
  fill0-raw)

(defun fill1-raw (j)
  (declare (xargs :guard (natp j)))
  (cond
   ((zp j)
    nil)
   (t
    (cons t (fill1-raw (1- j))))))

(defbv fill1 (j)
  (sig nat (bitvec j))
  fill1-raw)

(defun bv-const1 (n j acc)
  (declare (xargs :guard (and (natp n)
                              (natp j))))
  (cond
   ((zp n)
    acc)
   (t
    (bv-const1 (1- n)
               (floor j 2)
               (cons (equal (mod j 2) 1) acc)))))

;; Convert a positive integer j into an n-bit
;; constant.
(defun bv-const-raw (n j)
  (declare (xargs :guard (and (natp n)
                              (natp j))))
  (bv-const1 n j nil))

(defbv bv-const (n j)
  (sig nat nat (bitvec n))
  bv-const-raw)

;; Returns whether the signed bit vector x is negative.
(defund bv-s-negp-raw (n x)
  (declare (xargs :guard (and (true-listp x)))
           (ignore n))
  (car x))

(defbv bv-s-negp (n x)
  (sig nat (bitvec n) bool)
  bv-s-negp-raw)

(defund bv-ex-raw (n hbit lbit x)
  (declare (xargs :measure (nfix (- n hbit))
                  :guard (and (natp n)
                              (natp hbit)
                              (natp lbit)
                              (true-listp x))))
  (cond
   ((or (not (natp n))
        (not (natp hbit))
        (not (natp lbit))
        (<= n hbit))
    nil)
   ((= (1- n) hbit)
    x)
   (t
    (bv-ex-raw (1- n) hbit lbit (cdr x)))))

(defbv bv-ex (n hbit lbit x)
  (sig nat nat nat (bitvec n) (bitvec (1+ (- hbit lbit))))
  bv-ex-raw)

(defund append-n (n x y)
  (declare (xargs :guard (and (natp n)
                              (true-listp x))))
  (cond
   ((zp n)
    y)
   (t
    (cons (car x) (append-n (1- n) (cdr x) y)))))

#|
(defun bv-concat-raw (nx ny x y)
  (declare (ignore ny)
           (xargs :guard (and (natp nx)
                              (true-listp x))))
  (append-n nx x y))
|# ;|

(defabbrev bv-concat-raw (nx ny x y)
  (declare (ignore ny))
  (append-n nx x y))

(defbv bv-concat (nx ny x y)
  (sig nat nat (bitvec nx) (bitvec ny) (bitvec (+ nx ny)))
  bv-concat-raw)

(defun revappend-n (n x acc)
  (declare (xargs :guard (and (natp n)
                              (true-listp x))))
  (cond
   ((zp n)
    acc)
   (t
    (revappend-n (1- n)
                 (cdr x)
                 (cons (car x) acc)))))

(defund bv-not-raw (n x)
  (declare (xargs :guard (and (natp n)
                              (true-listp x))))
  (if (zp n)
      nil
    (cons (not (car x))
          (bv-not-raw (1- n) (cdr x)))))

(defbv bv-not (n x)
  (sig nat (bitvec n) (bitvec n))
  bv-not-raw)

(defund bv-and-raw (n x y)
  (declare (xargs :guard (and (natp n)
                              (true-listp x)
                              (true-listp y))))
  (if (zp n)
      nil
    (cons (and (car x) (car y))
          (bv-and-raw (1- n) (cdr x) (cdr y)))))

(defbv bv-and (n x y)
  (sig nat (bitvec n) (bitvec n) (bitvec n))
  bv-and-raw)

(defund bv-or-raw (n x y)
  (declare (xargs :guard (and (natp n)
                              (true-listp x)
                              (true-listp y))))
  (if (zp n)
      nil
    (cons (or (car x) (car y))
          (bv-or-raw (1- n) (cdr x) (cdr y)))))

(defbv bv-or (n x y)
  (sig nat (bitvec n) (bitvec n) (bitvec n))
  bv-or-raw)

;; (defund bv-xor (n x y)
;;   (if (zp n)
;;       nil
;;     (cons (xor (car x) (car y))
;;           (bv-xor (1- n) (cdr x) (cdr y)))))

(defabbrev bv-xor (n x y)
  (bv-or n
         (bv-and n x y)
         (bv-and n (bv-not n x) (bv-not n y))))

(defun xor3 (a b c)
  (declare (xargs :guard t))
  (xor a (xor b c)))

(defun maj3 (a b c)
  (declare (xargs :guard t))
  (if a (or b c) (and b c)))

(defun bv-add1 (n x y)
  (declare (xargs :guard (and (natp n)
                              (true-listp x)
                              (true-listp y))))
  (cond
   ((zp n)
    (cons nil nil))
   (t
    (let* ((ans (bv-add1 (1- n) (cdr x) (cdr y)))
           (sum (car ans))
           (carry (cdr ans)))
      (cons (cons (xor3 carry (car x) (car y))
                  sum)
            (maj3 carry (car x) (car y)))))))

(defund bv-add-raw (n x y)
  (declare (xargs :guard (and (natp n)
                              (true-listp x)
                              (true-listp y))))
  (let* ((ans (bv-add1 n x y))
         (sum (car ans)))
   sum))

(defbv bv-add (n x y)
  (sig nat (bitvec n) (bitvec n) (bitvec n))
  bv-add-raw)

(defun bv-neg1 (n x)
  (declare (xargs :guard (and (natp n)
                              (true-listp x))))
  (cond
   ((zp n)
    (cons nil t))
   (t
    (let* ((ans (bv-neg1 (1- n) (cdr x)))
           (neg (car ans))
           (carry (cdr ans)))
      (cons (cons (iff carry (car x))
                  neg)
            (if carry (not (car x)) nil))))))

;; Negate a two's complement number
(defund bv-neg-raw (n x)
  (declare (xargs :guard (and (natp n)
                              (true-listp x))))
  (let* ((ans (bv-neg1 n x))
         (neg (car ans)))
   neg))

(defbv bv-neg (n x)
  (sig nat (bitvec n) (bitvec n))
  bv-neg-raw)

(defabbrev bv-sub (n x y)
  (bv-add n x (bv-neg n y)))

(defun bv-mul1 (nx ny x y)
  (declare (xargs :guard (and (natp nx)
                              (natp ny)
                              (true-listp x)
                              (true-listp y))
                  :verify-guards nil))
  (cond
   ((zp nx)
    (cons nil (rem-extra-bits-raw ny y)))
   (t
    (let* ((ans (bv-mul1 (1- nx) ny (cdr x) y))
           (product (car ans))
           (shifted-y (cdr ans)))
     (cond
      ((car x)
       (cons (bv-add-raw ny product shifted-y)
             (cdr shifted-y)))
      (t
       (cons product (cdr shifted-y))))))))

(defthm rem-extra-bits-true-listp
  (implies (true-listp x)
           (true-listp (rem-extra-bits-raw n x)))
  :hints (("Goal" :in-theory (enable rem-extra-bits-raw)))
  :rule-classes :type-prescription)

(defthm true-listp-bv-add-raw
  (true-listp (bv-add-raw n x y))
  :hints (("Goal" :in-theory (enable bv-add-raw)))
  :rule-classes :type-prescription)

(defthm bv-mul1-true-listp-car
  (true-listp (car (bv-mul1 nx ny x y))))

(defthm bv-mul1-true-listp-cdr
  (implies (true-listp y)
           (true-listp (cdr (bv-mul1 nx ny x y)))))

(verify-guards bv-mul1)

;; If I was going to prove more rules about bv-mul1 I would make
;; a pair-true-listp predicate and make the above rules into
;; type prescription rules.  But seeing as all I wanted was the
;; guard proof...
(in-theory (disable bv-mul1-true-listp-car bv-mul1-true-listp-cdr))

(defund bv-mul-raw (n x y)
  (declare (xargs :guard (and (natp n)
                              (true-listp x)
                              (true-listp y))))
  (let* ((ans (bv-mul1 n n x y))
         (product (car ans)))
   product))

(defbv bv-mul (n x y)
  (sig nat (bitvec n) (bitvec n) (bitvec n))
  bv-mul-raw)

;; BV Predicates
(defund bv-lt-raw (n x y)
  (declare (xargs :guard (and (natp n)
                              (true-listp x)
                              (true-listp y))))
  (cond
   ((zp n)
    nil)
   ((iff (car x) (car y))
    (bv-lt-raw (1- n) (cdr x) (cdr y)))
   ((car x)
    nil)
   (t
    t)))

(defbv bv-lt (n x y)
  (sig nat (bitvec n) (bitvec n) bool)
  bv-lt-raw)

(defabbrev bv-leq (n x y)
  (b-not (bv-lt n y x)))

(defabbrev bv-gt (n x y)
  (bv-lt n y x))

(defabbrev bv-geq (n x y)
  (b-not (bv-lt n x y)))

;; The "abbreviations"
(defabbrev bv-nand (n x y)
  (bv-not n (bv-and n x y)))

(defabbrev bv-nor (n x y)
  (bv-not n (bv-or n x y)))

;; Signed less than
;; Haven't decided yet whether this should be
;; unrolled by ACL2!!!
(defund bv-s-lt-raw (n x y)
  (declare (xargs :guard (and (natp n)
                              (true-listp x)
                              (true-listp y))))
  (cond
   ((zp n)
    nil)
   (t
    (let ((lx-lt-ly (bv-lt-raw (1- n) (cdr x) (cdr y))))
      (cond
       ((car x)
        (cond
         ((car y)
          lx-lt-ly)
         (t
          t)))
       ((car y)
        nil)
       (t
        lx-lt-ly))))))

(defbv bv-s-lt (n x y)
  (sig nat (bitvec n) (bitvec n) bool)
  bv-s-lt-raw)

#|
(defabbrev bv-s-lt (n x y)
  (let ((lx-lt-ly (bv-lt (1- n)
                         (bv-ex n (- n 2) 0 x)
                         (bv-ex n (- n 2) 0 y))))
    (cond
     ((bv-s-negp n x)
      (cond
       ((bv-s-negp n y)
        lx-lt-ly)
       (t
        t)))
     ((bv-s-negp n y)
      nil)
     (t
      lx-lt-ly))))
|# ;|

(defabbrev bv-s-leq (n x y)
  (b-not (bv-s-lt n y x)))

(defabbrev bv-s-gt (n x y)
  (bv-s-lt n y x))

(defabbrev bv-s-geq (n x y)
  (b-not (bv-s-lt n x y)))

(defund bv-repeat-raw (n x j)
  (declare (xargs :guard (and (natp n)
                              (true-listp x)
                              (natp j))))
  (cond
   ((zp j)
    nil)
   (t
    (append-n n x (bv-repeat-raw n x (1- j))))))

(defbv bv-repeat (n x j)
  (sig nat (bitvec n) nat (bitvec (* n j)))
  bv-repeat-raw)

(defabbrev shift-left0 (n x j)
  (bv-concat (- n j) j
             (bv-ex n (+ n (- j) -1) 0 x)
             (fill0 j)))

(defabbrev shift-left1 (n x j)
  (bv-concat (- n j) j
             (bv-ex n (+ n (- j) -1) 0 x)
             (fill1 j)))

(defabbrev shift-right0 (n x j)
  (bv-concat j n (fill0 j) x))

(defabbrev shift-right1 (n x j)
  (bv-concat j n (fill1 j) x))

(defabbrev sign-extend (n x j)
  (bv-concat j n (bv-repeat 1 x j) x))

(defabbrev bv-rotate-left (n x j)
  (bv-concat (- n j) j (bv-ex n (+ n (- j) (- 1)) 0 x) x))

(defabbrev bv-rotate-right (n x j)
  (bv-concat j (- n j) (bv-ex n (1- j) 0 x) x))

;;(mv-let (erp val state) (table embedded-bv-fns nil nil :alist) (mv erp (strip-cars val) state))

;; --------------------------------------------------------------------------------
;; Bv-resize, created during rewriting to map a bit vector
;; to a smaller bit vector.

(defabbrev bv-resize-raw (n x)
  (declare (ignore n))
  x)

(defbv bv-resize (n x)
  (sig nat (bitvec n) (bitvec n))
  bv-resize-raw)

;; --------------------------------------------------------------------------------
;; Additional logical primitives.

(defabbrev id-raw (x)
  x)

(defund b-if-raw (a b c)
  (declare (xargs :guard t))
  (if a b c))

(defbv b-if (a b c)
  (sig bool bool bool bool)
  b-if-raw)

(defund bv-if-raw (n a x y)
  (declare (xargs :guard t)
           (ignore n))
  (if a x y))

(skip-proofs
(defbv bv-if (n a x y)
  (sig nat bool (bitvec n) (bitvec n) (bitvec n))
  bv-if-raw)
)

(defabbrev b-implies (a b)
  (b-if a b 't))

(defun b-and-& (arg-list)
  (cond
   ((endp arg-list)
    t)
   ((endp (cdr arg-list))
    (car arg-list))
   (t
    `(b-if ,(car arg-list)
           ,(b-and-& (cdr arg-list))
           nil))))

(defmacro b-and (&rest x)
  (b-and-& x))

(defun b-or-& (arg-list)
  (cond
   ((endp arg-list)
    nil)
   ((endp (cdr arg-list))
    (car arg-list))
   (t
    `(b-if ,(car arg-list)
           t
           ,(b-or-& (cdr arg-list))))))

(defmacro b-or (&rest x)
  (b-or-& x))

(defabbrev b-xor2 (a b)
  (b-if a (b-not b) b))

(defun b-xor-& (arg-list)
  (cond
   ((endp arg-list)
    nil)
   ((endp (cdr arg-list))
    (car arg-list))
   (t
    `(b-xor2 ,(car arg-list)
             ,(b-xor-& (cdr arg-list))))))

(defmacro b-xor (&rest x)
  (b-xor-& x))

(defund b-iff-raw (x y)
  (declare (xargs :guard t))
  (iff x y))

(defbv b-iff (a b)
  (sig bool bool bool)
  b-iff-raw)

(defund b-not-raw (x)
  (declare (xargs :guard t))
  (not x))

(defbv b-not (a)
  (sig bool bool)
  b-not-raw)

;; I could use b-iff rather than iff as my base
;; equivalence relation for Booleans, but as they
;; are equal, I don't see any reason to do so.
;; However, I don't want case splits, so I use b-iff
;; when an if-and-only-if occurs in the SMT problem.
(skip-proofs (defequiv b-iff))





