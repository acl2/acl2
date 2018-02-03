; AIGNET - And-Inverter Graph Networks
; Copyright (C) 2013 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Sol Swords <sswords@centtech.com>

(in-package "AIGNET")

;; This book just shows how to derive the set of 2-level reductions used in
;; construction.lisp.

;; This replicates the reductions derived in:
;; Brummayer, Robert, and Armin Biere. "Local two-level and-inverter graph
;; minimization without blowup." Proc. MEMICS 6 (2006): 32-38.

;; It also derives additional ones that contain XOR gates and groups them
;; according to the levels defined in that paper, where:
;; Level 1: one-level reductions.
;; Level 2: two-level reductions that create no new gates.
;; Level 3: two-level reductions that create at most one new gate and are uniquely applicable.
;; Level 4: two-level reductions that create at most one new gate and are not uniquely applicable.

(include-book "centaur/truth/sizes" :dir :system)
(include-book "centaur/fty/deftypes" :dir :system)
(include-book "std/util/defenum" :dir :system)
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))

(std::defenum axi-op-p (and xor))


(defsection axi-lit$
  (define axi-lit-construct$ (negp abs)
    :inline t
    (if negp (list 'not abs) abs))
  (local (in-theory (enable axi-lit-construct$)))

  (define axi-lit->negp$ (x)
    :returns (res booleanp :rule-classes :type-prescription)
    (and (consp x) (eq (car x) 'not)))
  (local (in-theory (enable axi-lit->negp$)))

  ;; true of axi-lits
  (define axi-lit-shape$ (x)
    (if (consp x)
        (and (consp (cdr x))
             (if (eq (car x) 'not) (not (cddr x)) t))
      t))
  (local (in-theory (enable axi-lit-shape$)))

  ;; true of axi-terms
  (define axi-lit-guard$ (x)
    (if (consp x) (and (not (eq (car x) 'not)) (consp (cdr x))) t))

  (local (in-theory (enable axi-lit-guard$)))

  (define axi-lit->abs$ (x)
    :guard (axi-lit-shape$ x)
    (if (and (consp x) (eq (car x) 'not))
        (cadr x)
      x))
  (local (in-theory (enable axi-lit->abs$)))

  (defthm acl2-count-of-axi-lit->abs$
    (<= (acl2-count (axi-lit->abs$ x)) (acl2-count x))
    :rule-classes :linear)

  (defthm axi-lit-shape$-of-axi-lit-construct$
    (implies (axi-lit-guard$ abs)
             (axi-lit-shape$ (axi-lit-construct$ neg abs))))

  (defthm axi-lit->abs$-of-axi-lit-construct$
    (implies (axi-lit-guard$ abs)
             (equal (axi-lit->abs$ (axi-lit-construct$ neg abs)) abs)))

  (defthm axi-lit->negp$-of-axi-lit-construct$
    (implies (axi-lit-guard$ abs)
             (iff (axi-lit->negp$ (axi-lit-construct$ neg abs)) neg)))

  (defthm axi-lit-construct$-identity
    (implies (axi-lit-shape$ x)
             (equal (axi-lit-construct$ (axi-lit->negp$ x)
                                        (axi-lit->abs$ x))
                    x)))

  (defthm acl2-count-of-axi-lit-construct$
    (<= (acl2-count abs) (acl2-count (axi-lit-construct$ negp abs)))
    :rule-classes :linear))

(define axi-varname-p (x)
  (or (integerp x)
      (and x (symbolp x)))
  ///
  (defthm axi-varname-p-compound-recognizer
    (equal (axi-varname-p x)
           (or (integerp x)
               (and x (symbolp x))))
    :rule-classes :compound-recognizer)

  (define axi-varname-fix ((x axi-varname-p))
    :returns (new-x axi-varname-p :rule-classes :type-prescription)
    (mbe :logic (if (axi-varname-p x) x 0)
         :exec x)
    ///
    (defret axi-variame-fix-when-axi-varname-p
      (implies (axi-varname-p x)
               (equal new-x x)))

    (fty::deffixtype axi-varname :pred axi-varname-p :fix axi-varname-fix
      :equiv axi-varname-equiv :define t)))
    
    
(fty::deftypes axi
  :enable-rules (axi-lit-shape$-of-axi-lit-construct$
                 axi-lit->abs$-of-axi-lit-construct$
                 axi-lit->negp$-of-axi-lit-construct$)
  (fty::defflexsum axi-term
    (:const :cond (eq x nil)
     :type-name axi-const
     :fields nil
     :ctor-body nil)
    (:var :cond (atom x)
     :type-name axi-var
     :fields ((name :acc-body x :type axi-varname :rule-classes :type-prescription))
     :ctor-body name)
    (:gate
     :type-name axi-gate
     :shape (and (consp (cdr x))
                 (consp (cddr x))
                 (not (cdddr x)))
     :fields ((op :acc-body (car x) :type axi-op-p)
              (left :acc-body (cadr x) :type axi-lit)
              (right :acc-body (caddr x) :type axi-lit))
     :ctor-body (list op left right))
    :measure (* 2 (acl2-count x)))
  (fty::defflexsum axi-lit
    :kind nil
    (:lit :type-name axi-lit
     :shape (axi-lit-shape$ x)
              
     :fields ((negp :acc-body (axi-lit->negp$ x) :type booleanp)
              (abs :acc-body (axi-lit->abs$ x) :type axi-term))
     :ctor-body (axi-lit-construct$ negp abs))
     :measure (+ 1 (* 2 (acl2-count x))))
  :post-pred-events ((local (defthm axi-lit-guard$-when-axi-term-p
                              (implies (axi-term-p x)
                                       (axi-lit-guard$ x))
                              :hints(("Goal" :in-theory (enable axi-lit-guard$)
                                      :expand ((axi-term-p x))))))))

(define axi-xor ((left axi-lit-p) (right axi-lit-p))
  :enabled t
  (axi-gate 'xor left right))

(define axi-and ((left axi-lit-p) (right axi-lit-p))
  :enabled t
  (axi-gate 'and left right))

(define axi-not ((x axi-lit-p))
  :enabled t
  (axi-lit (not (axi-lit->negp x)) (axi-lit->abs x)))


(fty::deflist axi-litlist :elt-type axi-lit)

(fty::deflist axi-termlist :elt-type axi-term)

(define axi-not-list ((x axi-litlist-p))
  :returns (negs axi-litlist-p)
  (if (atom x)
      nil
    (cons (axi-not (car x))
          (axi-not-list (cdr x)))))

;; We want to find all reductions of (op lit1 lit2) where lit1's term is a gate whose inputs are 0, 1.
;; Symmetries we'll exploit:

;; - If lit2 is a variable, then if it is 0 or 1 we'll pick 0 wlog.  Otherwise,
;;   there are no reductions so we skip this.

;; - If lit1 and lit2's terms are gates of differing types, then we'll say wlog that lit1's term is the xor.

;; - If lit1 and lit2's terms are of the same type and only one of them is negated, we'll say it's lit1.

;; - If lit2's term is a gate and exactly one of its inputs is 0 or 1 or a
;; negation, we'll say it's the left input and it is 0 or (not 0).
(defconst *axi-reduce-first-operands*
  '((and 0 1)
    (xor 0 1)))

(defconst *axi-reduce-second-operands*
  '(0   
    (xor 0 1)
    (xor 0 2)
    (and 0 1)
    (and (not 0) 1)
    (and (not 0) (not 1))
    (and 0 2)
    (and (not 0) 2)))

(define candidate-term-ok ((x axi-term-p))
  (axi-term-case x
    :const nil
    :var nil
    :gate (b* (((axi-lit x.left))
               ((axi-lit x.right))
               ((when (equal x.left.abs x.right.abs)) nil)
               ((when (and (eq x.op 'xor)
                           (or x.left.negp x.right.negp)))
                ;; negations bubble to top of xors
                nil)
               ((unless (axi-term-case x.left.abs :gate)) nil)
               ((axi-gate x.left.abs)))
            (axi-term-case x.right.abs
              :const nil
              :var t
              :gate (b* (((when (and (eq x.left.abs.op 'and)
                                     (eq x.right.abs.op 'xor)))
                          ;; left one has to be the xor if different
                          nil)
                         ((when (and (eq x.left.abs.op x.right.abs.op)
                                     x.right.negp (not x.left.negp)))
                          ;; left one has to be the negation if both same gates with different negations
                          nil))
                      t)))))


(define axi-reduce-candidate-terms-and-op2s ((op1 axi-lit-p)
                                        (op2s axi-litlist-p))
  :returns (terms axi-termlist-p)
  (if (atom op2s)
      nil
    (b* ((cand (axi-and op1 (car op2s))))
      (if (candidate-term-ok cand)
          (cons cand (axi-reduce-candidate-terms-and-op2s op1 (cdr op2s)))
        (axi-reduce-candidate-terms-and-op2s op1 (cdr op2s))))))

(define axi-reduce-candidate-terms-and ((op1s axi-litlist-p)
                                        (op2s axi-litlist-p))
  :returns (terms axi-termlist-p)
  (if (atom op1s)
      nil
    (append (axi-reduce-candidate-terms-and-op2s (car op1s) op2s)
            (axi-reduce-candidate-terms-and (cdr op1s) op2s))))

(define axi-reduce-candidate-terms-xor-op2s ((op1 axi-lit-p)
                                        (op2s axi-litlist-p))
  :returns (terms axi-termlist-p)
  (if (atom op2s)
      nil
    (b* ((cand (axi-xor op1 (car op2s))))
      (if (candidate-term-ok cand)
          (cons cand (axi-reduce-candidate-terms-xor-op2s op1 (cdr op2s)))
        (axi-reduce-candidate-terms-xor-op2s op1 (cdr op2s))))))

(define axi-reduce-candidate-terms-xor ((op1s axi-litlist-p)
                                        (op2s axi-litlist-p))
  :returns (terms axi-termlist-p)
  (if (atom op1s)
      nil
    (append (axi-reduce-candidate-terms-xor-op2s (car op1s) op2s)
            (axi-reduce-candidate-terms-xor (cdr op1s) op2s))))

(defconst *axi-reduce-candidates*
  (b* ((op1s (append *axi-reduce-first-operands*
                     (axi-not-list *axi-reduce-first-operands*)))
       (op2s (append *axi-reduce-second-operands*
                     (axi-not-list *axi-reduce-second-operands*))))
    (append (axi-reduce-candidate-terms-and op1s op2s)
            (axi-reduce-candidate-terms-xor op1s op2s))))


(defines axi-truth3
  (define axi-term-truth3 ((x axi-term-p))
    :returns (truth truth::truth3-p)
    :measure (axi-term-count x)
    (axi-term-case x
      :const 0
      :var (if (and (natp x.name)
                    (< x.name 3))
               (truth::var3 x.name)
             0)
      :gate (b* ((left (axi-lit-truth3 x.left))
                 (right (axi-lit-truth3 x.right)))
              (if (eq x.op 'and)
                  (logand left right)
                (logxor left right)))))
  (define axi-lit-truth3 ((x axi-lit-p))
    :returns (truth truth::truth3-p)
    :measure (axi-lit-count x)
    (b* (((axi-lit x))
         (abs (axi-term-truth3 x.abs)))
      (if x.negp
          (truth::truth-norm3 (lognot abs))
        abs)))
  ///
  (fty::deffixequiv-mutual axi-truth3))

(define axi-truth-compare ((x-truth truth::truth3-p)
                           (y axi-term-p))
  :returns (mv ok
               (subst (implies ok (axi-lit-p subst))))
  (b* ((x-truth (truth::truth3-fix x-truth))
       (y-truth (axi-term-truth3 y))
       ((when (eql y-truth x-truth))
        (mv t (axi-lit nil y)))
       ((when (eql (truth::truth-norm3 (lognot y-truth)) x-truth))
        (mv t (axi-lit t y))))
    (mv nil nil)))

(define axi-try-truths ((x-truth truth::truth3-p)
                        (cands axi-termlist-p))
  :returns (mv ok
               (subst (implies ok (axi-lit-p subst))))
  (b* (((when (atom cands)) (mv nil nil))
       ((mv ok subst) (axi-truth-compare x-truth (car cands)))
       ((when ok) (mv ok subst)))
    (axi-try-truths x-truth (cdr cands))))
    
(define axi-target-extensions ((x axi-lit-p))
  :returns (targets axi-termlist-p)
  (b* (((axi-lit x)))
    (list x.abs
          (axi-and 0 x)
          (axi-and (axi-not 0) x)
          (axi-and 1 x)
          (axi-and (axi-not 1) x)
          (axi-and 0 (axi-not x))
          (axi-and (axi-not 0) (axi-not x))
          (axi-and 1 (axi-not x))
          (axi-and (axi-not 1) (axi-not x))
          (axi-xor 0 x)
          (axi-xor 1 x)
          (axi-xor 2 x))))
          


(define axi-find-reduction ((x axi-term-p))
  :returns (mv ok
               (subst (implies ok (axi-lit-p subst))))
  (b* ((truth (axi-term-truth3 x))
       (cands
        ;; List of terms to compare to.
        (append '(nil 0 1 2
                      (and 0 1)
                      (and (not 0) 1)
                      (and 0 (not 1))
                      (and (not 0) (not 1))
                      (and 0 2)
                      (and (not 0) 2)
                      (and 0 (not 2))
                      (and (not 0) (not 2))
                      (and 1 2)
                      (and (not 1) 2)
                      (and 1 (not 2))
                      (and (not 1) (not 2))
                      (xor 0 1)
                      (xor 0 2)
                      (xor 1 2))
               (axi-term-case x
                 :const nil
                 :var nil
                 :gate (append
                        (axi-target-extensions x.left)
                        (axi-target-extensions x.right)
                        (b* (((axi-lit x.right)))
                        (axi-term-case x.right.abs
                          :const nil
                          :var nil
                          :gate (append (axi-target-extensions x.right.abs.left)
                                        (axi-target-extensions x.right.abs.right)))))))))
    (axi-try-truths truth cands)))

(define axi-subterm-p ((sub axi-term-p) (x axi-term-p))
  :measure (axi-term-count x)
  (or (axi-term-equiv sub x)
      (axi-term-case x
        :const nil
        :var nil
        :gate (or (axi-subterm-p sub (axi-lit->abs x.left))
                  (axi-subterm-p sub (axi-lit->abs x.right))))))

(fty::defalist axi-map :key-type axi-term :val-type axi-lit)

(define axi-find-reductions ((cands axi-termlist-p))
  :returns (map axi-map-p)
  (b* (((when (atom cands)) nil)
       (cand (car cands))
       ((mv ok subst) (axi-find-reduction cand))
       ((when ok)
        (cons (cons (axi-term-fix cand) subst)
              (axi-find-reductions (cdr cands)))))
    (axi-find-reductions (cdr cands))))

(defconst *axi-reductions*
  (axi-find-reductions *axi-reduce-candidates*))

(define print-axi-map ((x axi-map-p))
  :verify-guards nil
  (if (atom x)
      nil
    (if (mbt (consp (car x)))
        (prog2$ (cw "~x0~t1~x2~%" (axi-term-fix (caar x)) 55
                    (axi-lit-fix (cdar x)))
                (print-axi-map (cdr x)))
      (print-axi-map (cdr x)))))


(defconst *axi-reduction-list*
  '(
    ;; Most of the entries from the following table can be obtained by:
    ;; (print-axi-map *axi-reductions*)

    ;; The one-level reductions are entered by hand, as are the level numbers.

    ;; LHS                                                 RHS                            Level
    ;; --------------------------------------------------------------------------------------------

    ;; Optimization level 1: one operation (note: hand coded)
    (AND 0 NIL)                                            NIL                             1
    (AND 0 (NOT NIL))                                      0                               1
    (AND 0 0)                                              0                               1
    (AND 0 (NOT 0))                                        NIL                             1

    (XOR 0 NIL)                                            0                               1
    (XOR 0 0)                                              NIL                             1


    ;; Levels 2 through 4.

    ;; (and (and 0 1) var)
    (AND (AND 0 1) 0)                                      (AND 0 1)                       2
    (AND (AND 0 1) (NOT 0))                                NIL                             2

    ;; (and (not (and 0 1)) var)
    (AND (NOT (AND 0 1)) (NOT 0))                          (NOT 0)                         2
    (AND (NOT (AND 0 1)) 0)                                (AND 0 (NOT 1))                 3

    ;; (and (xor 0 1) var)
    (AND (XOR 0 1) 0)                                      (AND 0 (NOT 1))                 3
    (AND (XOR 0 1) (NOT 0))                                (AND (NOT 0) 1)                 3
    (AND (NOT (XOR 0 1)) 0)                                (AND 0 1)                       3
    (AND (NOT (XOR 0 1)) (NOT 0))                          (AND (NOT 0) (NOT 1))           3

    ;; (and (and 0 1) (and ...))
    (AND (AND 0 1) (AND (NOT 0) 2))                        NIL                             2
    ;; (AND (AND 0 1) (AND (NOT 0) 1))                        NIL ;; subsumed by above
    ;; (AND (AND 0 1) (AND (NOT 0) (NOT 1)))                  NIL
    (AND (AND 0 1) (AND 0 2))                              (AND 1 (AND 0 2))               4

    ;; (and (not (and 0 1)) (and ...))
    (AND (NOT (AND 0 1)) (AND (NOT 0) 2))                  (AND (NOT 0) 2)                 2
    ;; (AND (NOT (AND 0 1)) (AND (NOT 0) 1))                  (AND (NOT 0) 1) subsumed by above
    ;; (AND (NOT (AND 0 1)) (AND (NOT 0) (NOT 1)))            (AND (NOT 0) (NOT 1))      
    (AND (NOT (AND 0 1)) (AND 0 2))                        (AND (NOT 1) (AND 0 2))         3

    ;; (and (not (and 0 1)) (not (and ...)))
    (AND (NOT (AND 0 1)) (NOT (AND (NOT 0) 1)))            (NOT 1)                         2
    (AND (NOT (AND 0 1)) (NOT (AND (NOT 0) (NOT 1))))      (XOR 0 1)                       3


    ;; (and (xor 0 1) (and ...))
    (AND (XOR 0 1) (AND 0 1))                              NIL                             2
    (AND (XOR 0 1) (AND (NOT 0) (NOT 1)))                  NIL                             2
    ;; (AND (NOT (XOR 0 1)) (AND (NOT 0) 1))                  NIL                             2
    ;; (AND (NOT (XOR 0 1)) (AND 0 1))                        (AND 0 1)                       2
    (AND (XOR 0 1) (AND (NOT 0) 1))                        (AND (NOT 0) 1)                 2
    ;; (AND (NOT (XOR 0 1)) (AND (NOT 0) (NOT 1)))            (AND (NOT 0) (NOT 1))           2
    (AND (XOR 0 1) (AND 0 2))                              (AND (NOT 1) (AND 0 2))         3
    (AND (XOR 0 1) (AND (NOT 0) 2))                        (AND 1 (AND (NOT 0) 2))         3
    ;; (AND (NOT (XOR 0 1)) (AND 0 2))                        (AND 1 (AND 0 2))               3
    ;; (AND (NOT (XOR 0 1)) (AND (NOT 0) 2))                  (AND (NOT 1) (AND (NOT 0) 2))   3

    ;; (and (xor 0 1) (not (and ...)))
    (AND (XOR 0 1) (NOT (AND 0 1)))                        (XOR 0 1)                       2
    (AND (XOR 0 1) (NOT (AND (NOT 0) (NOT 1))))            (XOR 0 1)                       2
    ;; (AND (NOT (XOR 0 1)) (NOT (AND (NOT 0) 1)))            (NOT (XOR 0 1))                 2
    (AND (XOR 0 1) (NOT (AND (NOT 0) 1)))                  (AND 0 (NOT 1))                 3
    ;; (AND (NOT (XOR 0 1)) (NOT (AND 0 1)))                  (AND (NOT 0) (NOT 1))           3
    ;; (AND (NOT (XOR 0 1)) (NOT (AND (NOT 0) (NOT 1))))      (AND 0 1)                       3

    ;; (xor (and 0 1) var)
    (XOR (AND 0 1) 0)                                      (AND 0 (NOT 1))                 3

    ;; (xor (xor 0 1) var)
    (XOR (XOR 0 1) 0)                                      1                               2

    ;; (xor (and 0 1) (and ...))
    (XOR (AND 0 1) (AND (NOT 0) 1))                        1                               2
    (XOR (AND 0 1) (AND (NOT 0) (NOT 1)))                  (NOT (XOR 0 1))                 3

    ;; (xor (xor 0 1) (and ...))
    (XOR (XOR 0 1) (AND 0 1))                              (NOT (AND (NOT 0) (NOT 1)))     3
    (XOR (XOR 0 1) (AND (NOT 0) 1))                        (AND 0 (NOT 1))                 3
    (XOR (XOR 0 1) (AND (NOT 0) (NOT 1)))                  (NOT (AND 0 1))                 3

    ;; (xor (xor 0 1) (xor ...))
    (XOR (XOR 0 1) (XOR 0 2))                              (XOR 1 2)                       3
    ))
