; X86ISA Library

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2015, Regents of the University of Texas
; All rights reserved.

; Redistribution and use in source and binary forms, with or without
; modification, are permitted provided that the following conditions are
; met:

; o Redistributions of source code must retain the above copyright
;   notice, this list of conditions and the following disclaimer.

; o Redistributions in binary form must reproduce the above copyright
;   notice, this list of conditions and the following disclaimer in the
;   documentation and/or other materials provided with the distribution.

; o Neither the name of the copyright holders nor the names of its
;   contributors may be used to endorse or promote products derived
;   from this software without specific prior written permission.

; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
; "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
; LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
; A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
; HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
; SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
; LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
; DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
; THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
; (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
; OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

; Original Author(s):
; Shilpi Goel         <shigoel@cs.utexas.edu>

(in-package "X86ISA")
(include-book "std/util/define" :dir :system)
(include-book "std/lists/rev" :dir :system)
(include-book "std/lists/flatten" :dir :system)
(include-book "clause-processors/find-matching" :dir :system)

(local (xdoc::set-default-parents general-memory-utils))

;; ===================================================================

(define separate ((r-w-x-1 :type (member :r :w :x))
                  (n-1     posp)
                  (addr-1  integerp)
                  (r-w-x-2 :type (member :r :w :x))
                  (n-2     posp)
                  (addr-2  integerp))
  ;; r-w-x-1 and r-w-x-2 are just for finding appropriate bindings for
  ;; the free variables of rules where separateness of small regions
  ;; is to be deduced from that of bigger ones.
  :irrelevant-formals-ok t
  :non-executable t

  (or (<= (+ n-2 addr-2) addr-1)
      (<= (+ n-1 addr-1) addr-2))

  ///

  (defthmd separate-is-commutative
    (implies (separate r-w-x-1 n-1 a-1 r-w-x-2 n-2 a-2)
             (separate r-w-x-2 n-2 a-2 r-w-x-1 n-1 a-1))
    :hints (("Goal" :in-theory (e/d* (separate) ()))))

  (defun separate-free-var-candidates (calls)
    (if (endp calls)
        nil
      (cons (list ;; (cons 'r-w-x-1 (nth 1 (car calls)))
             (cons 'n-1     (nth 2 (car calls)))
             (cons 'a-1     (nth 3 (car calls)))
             ;; (cons 'r-w-x-2 (nth 4 (car calls)))
             (cons 'n-2     (nth 5 (car calls)))
             (cons 'a-2     (nth 6 (car calls))))
            (separate-free-var-candidates (cdr calls)))))

  (defun separate-bindings (name r-w-x-1 r-w-x-2 mfc state)
    (declare (xargs :stobjs (state) :mode :program)
             (ignorable name state))
    ;; (acl2::find-matches-list
    ;;  '(separate ':r a b ':w c d)
    ;;  '((separate ':r n1 a1 ':w n2 a2)
    ;;    (a b c)
    ;;    (separate ':r a b x c d))
    ;;  nil)
    (b* ((calls (acl2::find-matches-list
                 `(separate ,r-w-x-1 a b ,r-w-x-2 c d)
                 (acl2::mfc-clause mfc)
                 nil))
         ((when (not calls)) nil))
      (separate-free-var-candidates calls)))

  (defthm separate-smaller-regions
    (implies (and
              (bind-free
               (separate-bindings
                'separate-smaller-regions r-w-x-1 r-w-x-2 mfc state)
               (n-1 a-1 n-2 a-2))
              (<= a-2 a-2-bigger)
              (<= (+ n-2-smaller a-2-bigger) (+ n-2 a-2))
              (<= a-1 a-1-bigger)
              (<= (+ n-1-smaller a-1-bigger) (+ n-1 a-1))
              (separate r-w-x-1 n-1 a-1 r-w-x-2 n-2 a-2))
             (separate r-w-x-1 n-1-smaller a-1-bigger r-w-x-2 n-2-smaller a-2-bigger))
    :hints (("Goal" :in-theory (e/d* (separate) ())))
    ;; I don't want too much effort to be expended on rewriting a
    ;; separate term --- such terms should be more-or-less directly
    ;; inferrable from other separate terms already present in the
    ;; goal.  Also, the reason why the backchain limit below is 1 and
    ;; not 0 is because I do need _some_ rewriting --- for instance,
    ;; to prove away hypotheses like (<= a-2 a-2-bigger).
    :rule-classes ((:rewrite :backchain-limit-lst 1)))

  (defthm separate-contiguous-regions
    (and (separate r-w-x-1 i (+ (- i) x) r-w-x-2 j x)
         (implies (<= j i)
                  (separate r-w-x-1 i x r-w-x-2 j (+ (- i) x)))
         (separate r-w-x-1 i x r-w-x-2 j (+ i x))
         (implies (or (<= (+ j k2) k1) (<= (+ i k1) k2))
                  (separate r-w-x-1 i (+ k1 x) r-w-x-2 j (+ k2 x))))
    :hints (("Goal" :in-theory (e/d* (separate) ()))))

  (in-theory (e/d () ((separate)))))

;; (acl2::why separate-smaller-regions)
;; (acl2::trace$ separate-bindings)

(local
 (defthm separate-smaller-regions-test-1
   (implies (and (separate :x 500 6000 :w 10 10000)
                 (separate :w 10     0 :w 20 500)
                 (separate :r 20     0 :w 50 100))
            (separate :r 10 0 :w 20 120))
   :hints (("Goal" :in-theory (e/d* () (separate (separate)))))))

(local
 (defthm separate-smaller-regions-test-2
   (implies (separate :x (+ 1 i)       prog-addr :w n addr)
            (separate :x i       (+ 1 prog-addr) :w n addr))
   :rule-classes nil))

;; ======================================================================

;; Member-p:

(define member-p
  (e
   (x (true-listp x)))

  :parents (proof-utilities)
  :enabled t

  (if (atom x)
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
    :rule-classes ((:rewrite :backchain-limit-lst (0))))

  (defthmd member-p-iff-member-equal
    (iff (member-p e x)
         (member-equal e x))))

;; ======================================================================

;; Disjoint-p:

(define disjoint-p
  ((x (true-listp x))
   (y (true-listp y)))

  :parents (proof-utilities)
  :long "<p>@('disjoint-p') returns @('t') if @(see true-listp)-satisfying
  inputs @('x') and @('y') have no element in common. Otherwise, @('nil') is
  returned.</p>"
  :enabled t

  (if (atom x)
      t
    (if (member-p (car x) y)
        nil
      (disjoint-p (cdr x) y)))

  ///

  (defthm disjoint-p-x-x
    (implies (consp x)
             (equal (disjoint-p x x) nil)))

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

  (defthmd disjoint-p-cons-1
    (equal (disjoint-p (cons e x) a)
           (and (disjoint-p x a)
                (equal (member-p e a) nil)))
    :hints (("Goal" :in-theory (e/d* (disjoint-p) ()))))

  (defthm disjoint-p-cons-2
    (equal (disjoint-p a (cons e x))
           (and (disjoint-p a x)
                (equal (member-p e a) nil))))

  (defthmd disjoint-p-commutative
    (equal (disjoint-p a b)
           (disjoint-p b a))
    :rule-classes ((:rewrite :loop-stopper ((a b)))))

  (defthmd member-p-when-not-disjoint-p
    (implies (and (member-p e x)
                  (member-p e y))
             (equal (disjoint-p x y) nil)))

  (defthm not-member-p-when-disjoint-p
    (implies (and (disjoint-p x y)
                  (member-p e x))
             (equal (member-p e y) nil)))

  (defthm disjoint-p-append-1
    (implies (true-listp a)
             (equal (disjoint-p (append a b) c)
                    (and (disjoint-p a c)
                         (disjoint-p b c)))))

  (defthm disjoint-p-append-2
    (implies (true-listp b)
             (equal (disjoint-p a (append b c))
                    (and (disjoint-p a b)
                         (disjoint-p a c))))))

(define disjoint-p$ ((x (true-listp x))
                     (y (true-listp y)))
  (disjoint-p x y)
  ///
  (defthmd rewrite-disjoint-p$-to-disjoint-p
    (equal (disjoint-p$ x y) (disjoint-p x y))))

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
             (equal (pos e x) nil)))

  (defthm nth-pos-of-list-first
    ;; See nth-pos-of-addr-range-first.
    (implies (and (syntaxp (not (and (consp xs)
                                     (eq (car xs) 'addr-range))))
                  (equal index (car xs))
                  (consp xs))
             (equal (pos index xs) 0))
    :hints (("Goal" :in-theory (e/d* (pos) ())))))

;; ======================================================================

;; Subset-p:

(define subset-p
  ((x (true-listp x))
   (y (true-listp y)))

  :parents (proof-utilities)
  :enabled t

  (cond ((atom x) t)
        ((member-p (car x) y) (subset-p (cdr x) y))
        (t nil))

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
    (equal (subset-p x x) t))

  (defthmd subset-p-transitive
    (implies (and (subset-p x y)
                  (subset-p y z))
             (subset-p x z)))

  ;; (defthm append-subset-p-1
  ;;   (implies (and (subset-p a x)
  ;;                 (subset-p b x))
  ;;            (subset-p (append a b) x)))

  (defthm subset-p-of-append-1
    (equal (subset-p (append a b) x)
           (and (subset-p a x)
                (subset-p b x))))

  (defthm subset-p-of-append-2
    (implies (or (subset-p a x)
                 (subset-p a y))
             (subset-p a (append x y))))

  (defthm subset-p-and-append-both
    (implies (subset-p a b)
             (subset-p (append e a) (append e b))))

  (defthm subset-p-of-nil
    (equal (subset-p x nil)
           (atom x)))

  (defthm subset-p-cons-2
    (implies (subset-p x y)
             (subset-p x (cons e y))))

  (defthm member-p-of-subset-is-member-p-of-superset
    (implies (and (subset-p x y)
                  (member-p e x))
             (member-p e y)))

  (defthmd not-member-p-of-superset-is-not-member-p-of-subset
    (implies (and (equal (member-p e y) nil)
                  (subset-p x y))
             (equal (member-p e x) nil))
    :hints (("Goal" :in-theory (e/d* (member-p) ()))))

  (defthmd subset-p-and-remove-duplicates-equal-1
    (implies (subset-p x y)
             (subset-p (remove-duplicates-equal x) y))
    :hints (("Goal" :in-theory (e/d* (subset-p) ()))))

  (defthmd subset-p-and-remove-duplicates-equal-2
    (implies (subset-p x y)
             (subset-p x (remove-duplicates-equal y)))
    :hints (("Goal" :in-theory (e/d* (subset-p) ()))))

  (defthmd subset-p-and-remove-duplicates-equal-both
    (implies (subset-p x y)
             (subset-p (remove-duplicates-equal x) (remove-duplicates-equal y)))
    :hints (("Goal" :in-theory (e/d* (subset-p-and-remove-duplicates-equal-1
                                      subset-p-and-remove-duplicates-equal-2)
                                     ())))))

;; ======================================================================

;; no-duplicates-p:

(define no-duplicates-p
  ((l (true-listp l)))

  :parents (proof-utilities)
  :enabled t

  (cond ((endp l) t)
        ((member-p (car l) (cdr l)) nil)
        (t (no-duplicates-p (cdr l))))

  ///

  (defthm no-duplicates-p-and-append
    (implies (no-duplicates-p (append a b))
             (and (no-duplicates-p a)
                  (no-duplicates-p b)))
    :rule-classes (:forward-chaining :rewrite)))

(defthmd no-duplicatesp-equal-to-no-duplicates-p
  (equal (no-duplicatesp-equal xs)
         (no-duplicates-p xs)))

(defthmd no-duplicates-p-to-no-duplicatesp-equal
  (equal (no-duplicates-p xs)
         (no-duplicatesp-equal xs)))

;; ======================================================================

;; Misc. theorems:

(defthm disjoint-p-forward-chain-to-member-p
  (implies (disjoint-p (list i) x)
           (not (member-p i x)))
  :rule-classes :forward-chaining)

(defthm cdr-strip-cars-is-strip-cars-cdr
  (equal (cdr (strip-cars x))
         (strip-cars (cdr x))))

(defthm strip-cars-append
  (equal (strip-cars (append x y))
         (append (strip-cars x)
                 (strip-cars y))))

(defthm disjoint-p-subset-p
  ;; Ugh, free vars.
  (implies (and (disjoint-p x y)
                (subset-p a x)
                (subset-p b y))
           (disjoint-p a b)))

(defthm subset-p-cons-member-p-lemma
  ;; Ugh, free vars.
  (implies (and (subset-p x (cons e y))
                (not (subset-p x y)))
           (not (member-p e y))))

(local (include-book "std/lists/reverse" :dir :system))

(defthm assoc-of-append-when-member-p-1
  (implies (member-p a (strip-cars xs))
           (equal (assoc-equal a (append xs ys))
                  (assoc-equal a xs))))

(defthm assoc-of-append-when-member-p-2
  (implies (not (member-p a (strip-cars xs)))
           (equal (assoc-equal a (append xs ys))
                  (assoc-equal a ys))))

(defthm strip-cars-of-rev-is-rev-of-strip-cars
  (equal (strip-cars (acl2::rev x))
         (acl2::rev (strip-cars x))))

;; (defthm member-p-of-rev
;;   (equal (member-p x (acl2::rev y))
;;          (member-p x y))
;;   :hints (("Goal" :in-theory (e/d (member-p) ()))))

(defthm member-p-of-rev
  (iff (member-p e (acl2::rev x))
       (member-p e x)))

(defthm subset-p-of-rev
  (equal (subset-p x (acl2::rev y))
         (subset-p x y))
  :hints (("Goal" :in-theory (e/d (subset-p) ()))))

(defthm member-of-rev
  (implies (member-p a xs)
           (member-p a (acl2::rev xs)))
  :hints (("Goal" :in-theory (e/d (member-p) ()))))

 (defthm member-strip-cars-assoc-and-rev
   (implies (member-p a (strip-cars xs))
            (member-p a (acl2::rev (strip-cars xs)))))

(defthm assoc-of-append-when-member-p-with-rev
  (implies (member-p a (strip-cars xs))
           (equal (assoc-equal a (append (acl2::rev xs) ys))
                  (assoc-equal a (acl2::rev xs)))))

(defthm not-member-assoc-equal-with-rev-and-strip-cars
  (implies (not (member-p a (strip-cars xs)))
           (equal (cdr (assoc a (acl2::rev (acons a b xs))))
                  b))
  :hints (("Goal" :in-theory (e/d (member-p) ()))))

(defthm assoc-equal-append-list-cons-and-not-member-p
  (implies (and (not (member-p e (strip-cars x)))
                (alistp x))
           (equal (assoc-equal e (append x (list (cons e y))))
                  (cons e y)))
  :hints (("Goal" :in-theory (e/d* (member-p) ()))))

;; ======================================================================

(in-theory (e/d () (member-p disjoint-p pos subset-p)))

;; ======================================================================
