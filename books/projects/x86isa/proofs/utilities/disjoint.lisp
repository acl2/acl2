;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")
(include-book "std/util/define" :dir :system)

;; ===================================================================

;; Member-p:

(define member-p
  (e
   (x (true-listp x)))

  :parents (proof-utilities)
  :enabled t

  (if (endp x)
      nil
    (if (equal e (car x))
        t
      (member-p e (cdr x))))

  ///

  (defthm member-p-of-not-a-consp
    (implies (not (consp x))
             (equal (member-p e x) nil)))

  (defthm member-p-of-nil
    (equal (member-p e nil) nil))

  (defthm member-p-cons
    (equal (member-p e1 (cons e2 x))
           (if (equal e1 e2)
               t
             (member-p e1 x))))

  (defthm member-p-append
    (equal (member-p e (append x y))
           (or (member-p e x)
               (member-p e y))))

  (defthm member-p-cdr
    (implies (member-p e (cdr x))
             (member-p e x))
    ;; From the ACL2-DOC:
    ;; The relieving of hypotheses may be limited to the use of
    ;; contextual information (without backchaining, i.e., without
    ;; recursively rewriting hypotheses) by executing
    ;; :set-backchain-limit 0.
    :rule-classes ((:rewrite :backchain-limit-lst (0)))))

;; ======================================================================

;; Disjoint-p:

(define disjoint-p
  ((x (true-listp x))
   (y (true-listp y)))

  :parents (proof-utilities)
  :short "@('disjoint-p') recognizes whether @('x') and @('y') are
  disjoint lists."
  :enabled t

  (if (endp x)
      t
    (if (member-p (car x) y)
        nil
      (disjoint-p (cdr x) y)))

  ///

  (defthm disjoint-p-nil-1
    (equal (disjoint-p nil y) t)
    :hints (("Goal" :in-theory (e/d (disjoint-p) ()))))

  (defthm disjoint-p-nil-2
    (equal (disjoint-p x nil) t)
    :hints (("Goal" :in-theory (e/d (disjoint-p) ()))))

  (defthmd disjoint-p-cdr-1
    (implies (disjoint-p x y)
             (disjoint-p (cdr x) y))
    :hints (("Goal" :in-theory (e/d (disjoint-p member-p) ())))
    :rule-classes ((:rewrite :backchain-limit-lst (0))))

  (defthmd disjoint-p-cdr-2
    (implies (disjoint-p x y)
             (disjoint-p x (cdr y)))
    :hints (("Goal" :in-theory (e/d (disjoint-p member-p) ())))
    :rule-classes ((:rewrite :backchain-limit-lst (0))))

  (defthm disjoint-p-cons
    (equal (disjoint-p a (cons e x))
           (and (disjoint-p a x)
                (equal (member-p e a) nil)))
    :rule-classes
    ((:rewrite)
     ;; (:forward-chaining
     ;;  :corollary
     ;;  (implies (disjoint-p a (cons e x))
     ;;           (and (disjoint-p a x)
     ;;                (equal (member-p e a) nil))))
     ))

  (defthmd disjoint-p-commutative
    (equal (disjoint-p a b)
           (disjoint-p b a))
    :rule-classes ((:rewrite :loop-stopper ((a b)))))

  (defthm member-p-when-not-disjoint-p
    ;; Note: e is free.
    (implies (and (member-p e x)
                  (member-p e y))
             (equal (disjoint-p x y) nil))
    :rule-classes :forward-chaining)

  (defthm not-member-p-when-disjoint-p
    ;; Note: x is free.
    (implies (and (disjoint-p x y)
                  (member-p e x))
             (equal (member-p e y) nil))
    :rule-classes :forward-chaining)

  (defthm disjoint-p-append
    (implies (true-listp b)
             (equal (disjoint-p a (append b c))
                    (and (disjoint-p a b)
                         (disjoint-p a c))))))

(define pairwise-disjoint-p-aux
  ((x true-listp)
   (l true-list-listp))
  :parents (proof-utilities)
  :short "@('pairwise-disjoint-p-aux') recognizes whether a true-list
  @('x') is disjoint from every sub-list in a true-list-list @('l')."
  :guard t
  :enabled t

  (if (endp l)
      t
    (if (disjoint-p x (car l))
        (pairwise-disjoint-p-aux x (cdr l))
      nil)))

(define pairwise-disjoint-p
  ((l true-list-listp))
  :parents (proof-utilities)
  :short "@('pairwise-disjoint-p') recognizes whether all the
  sub-lists in the true-list-list @('l') are pairwise disjoint."
  :guard t
  :enabled t

  (if (endp l)
      t
    (if (pairwise-disjoint-p-aux (car l) (cdr l))
        (pairwise-disjoint-p (cdr l))
      nil)))

(define true-list-list-disjoint-p
  ((xs true-list-listp)
   (ys true-list-listp))
  :parents (proof-utilities)
  :short "@('true-list-list-disjoint-p') recognizes whether a
  true-list-list @('xs') is disjoint from another true-list-list
  @('ys')."
  :guard t
  :enabled t

  (if (endp xs)
      t
    (if (pairwise-disjoint-p-aux (car xs) ys)
        (true-list-list-disjoint-p (cdr xs) ys)
      nil)))


(defthm disjoint-p-members-of-pairwise-disjoint-p-aux
  (implies (and (pairwise-disjoint-p-aux xs l)
                (member-p ys l))
           (disjoint-p xs ys)))

(defthm disjoint-p-members-of-pairwise-disjoint-p
  (implies (and (pairwise-disjoint-p l)
                (member-p xs l)
                (member-p ys l)
                (not (equal xs ys)))
           (disjoint-p xs ys)))

(defthm disjoint-p-members-of-true-list-list-disjoint-p
  (implies (and (true-list-list-disjoint-p xs ys)
                (member-p x xs)
                (member-p y ys))
           (disjoint-p x y)))

;; ======================================================================

;; Position:

(defun pos-1 (e x n)
  (declare (xargs :guard (and (true-listp x)
                              (natp n))))
  (if (endp x)
      nil
    (if (equal e (car x))
        n
      (pos-1 e (cdr x) (1+ n)))))

(defthm member-p-pos-1-non-nil
  (implies (and (member-p e x)
                (natp n))
           (natp (pos-1 e x n)))
  :rule-classes :type-prescription)

(defthm member-p-pos-1-value
  (implies (and (member-p e x)
                (natp n))
           (< (- (pos-1 e x n) n) (len x)))
  :rule-classes :linear)

(defthm not-member-p-pos-1-nil
  (implies (equal (member-p e x) nil)
           (equal (pos-1 e x n) nil)))

(defthm pos-1-accumulator-thm
  (implies (member-p e x)
           (equal (pos-1 e x (+ n1 n2))
                  (+ n1 (pos-1 e x n2)))))

(define pos
  (e
   (x (true-listp x)))

  :parents (proof-utilities)
  :short "Position of element @('e') in a list @('x')"

  :long "<p>We use this function to get the byte located at a memory
  address; thus, in our use case, @('e') is the address, @('x') is the
  region of memory represented as a true-list, and the return value is
  the byte at address @('e') \(if @('e') is a valid address in
  @('x')\).  We use this function exclusively on the output obtained
  from functions like @(see rb) and @(see program-at).</p>"

  :enabled t

  (pos-1 e x 0)

  ///

  (defthm member-p-pos-non-nil
    (implies (member-p e x)
             (and (integerp (pos e x))
                  (<= 0 (pos e x))))
    :rule-classes :type-prescription)

  (defthm member-p-pos-value
    (implies (member-p e x)
             (< (pos e x) (len x)))
    :rule-classes :linear)

  (defthm not-member-p-pos-nil
    (implies (equal (member-p e x) nil)
             (equal (pos e x) nil))))

;; ======================================================================

;; Subset-p:

(define subset-p
  ((x (true-listp x))
   (y (true-listp y)))

  :parents (proof-utilities)
  :enabled t

  (if (consp x)
      (if (member-p (car x) y)
          (subset-p (cdr x) y)
        nil)
    (if (equal x nil)
        t
      nil))

  ///

  (defthm subset-p-cdr-x
    (implies (subset-p x y)
             (subset-p (cdr x) y))
    :rule-classes ((:rewrite :backchain-limit-lst (0))))

  (defthm subset-p-cdr-y
    (implies (subset-p x (cdr y))
             (subset-p x y))
    :rule-classes ((:rewrite :backchain-limit-lst (0))))

  (defthm subset-p-cons
    (implies (subset-p x y)
             (subset-p (cons e x) (cons e y)))
    :rule-classes ((:rewrite :backchain-limit-lst (0))))

  (defthm subset-p-reflexive
    (implies (true-listp x)
             (equal (subset-p x x) t))))

;; ======================================================================

;; no-duplicates-p

(define no-duplicates-p
  ((l (true-listp l)))

  :parents (proof-utilities)
  :enabled t

  (cond ((endp l) t)
        ((member-p (car l) (cdr l)) nil)
        (t (no-duplicates-p (cdr l)))))

;; ======================================================================

;; Misc. theorems:

(defthm cdr-strip-cars-is-strip-cars-cdr
  (equal (cdr (strip-cars x))
         (strip-cars (cdr x))))

(defthm strip-cars-append
  (equal (strip-cars (append x y))
         (append (strip-cars x)
                 (strip-cars y))))

(defthm disjoint-p-subset-p
  ;; This is a bad rule.  For the :rewrite rule, x and y are free.
  ;; For the :forward-chaining rule, a and b are free. Ugh.
  (implies (and (disjoint-p x y)
                (subset-p a x)
                (subset-p b y))
           (disjoint-p a b))
  :rule-classes (:rewrite :forward-chaining))

;; ======================================================================

(in-theory (e/d () (member-p disjoint-p pos subset-p)))

;; ======================================================================
