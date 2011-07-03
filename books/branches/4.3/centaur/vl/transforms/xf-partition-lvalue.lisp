; VL Verilog Toolkit
; Copyright (C) 2008-2011 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "VL")
(include-book "../mlib/expr-tools")
(include-book "../mlib/range-tools")
(local (include-book "../util/arithmetic"))


(defthm acl2-count-of-list-fix-weak
  (<= (acl2-count (list-fix x))
      (acl2-count x))
  :rule-classes ((:rewrite) (:linear))
  :hints(("Goal" :in-theory (enable acl2-count))))



(defsection vl-exprlist-totalwidth

  (defthm natp-of-vl-expr->finalwidth-when-vl-expr-widthsfixed-p
    (implies (vl-expr-widthsfixed-p x)
             (natp (vl-expr->finalwidth x)))
    :hints(("Goal" :in-theory (enable vl-expr-widthsfixed-p))))

  (defund vl-exprlist-totalwidth (x)
    (declare (xargs :guard (and (vl-exprlist-p x)
                                (vl-exprlist-widthsfixed-p x))))
    (if (consp x)
        (+ (mbe :logic (nfix (vl-expr->finalwidth (car x)))
                :exec (vl-expr->finalwidth (car x)))
           (vl-exprlist-totalwidth (cdr x)))
      0))

  (local (in-theory (enable vl-exprlist-totalwidth)))

  (defthm vl-exprlist-totalwidth-when-not-consp
    (implies (not (consp x))
             (equal (vl-exprlist-totalwidth x)
                    0)))

  (defthm vl-exprlist-totalwidth-of-cons
    (equal (vl-exprlist-totalwidth (cons a x))
           (+ (nfix (vl-expr->finalwidth a))
              (vl-exprlist-totalwidth x)))
    :hints(("Goal" :in-theory (disable (force))))))



; Part 1.  We just bust the expressions up into bit lists.

(defsection vl-msb-bitexprs-for-id-aux
  :parents (vl-partition-lvalue)
  :short "@(call vl-msb-bitexprs-for-id-aux) returns the list of bit-select
expressions <tt>(idexpr[high] idexpr[high-1] ... idexpr[low])</tt>."

  (defund vl-msb-bitexprs-for-id-aux (idexpr low high)
    (declare (xargs :guard (and (vl-expr-p idexpr)
                                (vl-idexpr-p idexpr)
                                (natp high)
                                (natp low)
                                (<= low high))
                    :measure (nfix (- (nfix high) (nfix low)))))
    (b* ((high    (mbe :logic (nfix high) :exec high))
         (low     (mbe :logic (nfix low) :exec low))
         (hindex  (vl-make-index high))
         (hselect (make-vl-nonatom :op :vl-bitselect
                                   :args (list idexpr hindex)
                                   :finalwidth 1
                                   :finaltype :vl-unsigned
                                   :atts nil))
         ((when (mbe :logic (zp (- high low))
                     :exec (= high low)))
          (list hselect))
         (rest (vl-msb-bitexprs-for-id-aux idexpr low (- high 1))))
        (cons hselect rest)))

  (local (in-theory (enable vl-msb-bitexprs-for-id-aux)))

  (defthm vl-exprlist-p-of-vl-msb-bitexprs-for-id-aux
    (implies (and (force (vl-expr-p idexpr))
                  (force (vl-idexpr-p idexpr))
                  (force (natp high))
                  (force (natp low))
                  (force (<= low high)))
             (vl-exprlist-p (vl-msb-bitexprs-for-id-aux idexpr low high))))

  (defthm len-of-vl-msb-bitexprs-for-id-aux
    (equal (len (vl-msb-bitexprs-for-id-aux idexpr low high))
           (+ 1 (nfix (- (nfix high) (nfix low)))))))



(defsection vl-msb-bitexprs-for-id
  :parents (vl-partition-lvalue)
  :short "@(call vl-msb-bitexprs-for-id) returns <tt>(mv successp exprs)</tt>,
where <tt>exprs</tt> is basically <tt>(idexpr[high] idexpr[high-1]
... idexpr[low])</tt>."

  :long "<p>When <tt>idexpr</tt> is a multi-bit wire, we actually just return
the singleton list <tt>(idexpr)</tt>.</p>"

;; BOZO this is wrong.
  (defund vl-msb-bitexprs-for-id (idexpr mod)
    "Returns (MV SUCCESSP EXPRS)"
    (declare (xargs :guard (and (vl-expr-p idexpr)
                                (vl-idexpr-p idexpr)
                                (vl-module-p mod))))
    (b* ((name (vl-idexpr->name idexpr))
         ((mv successp range)
          (vl-slow-find-net/reg-range name mod))
         ((unless (and successp
                       (vl-maybe-range-resolved-p range)))
          (mv nil nil))
         ((unless range)
          ;; A one-bit wire, no need to add indexes
          (mv t (list idexpr)))
         (high (vl-resolved->val (vl-range->left range)))
         (low  (vl-resolved->val (vl-range->right range)))
         (bits (vl-msb-bitexprs-for-id-aux idexpr low high)))
        (mv t bits)))

  (defmvtypes vl-msb-bitexprs-for-id (booleanp true-listp))

  (local (in-theory (enable vl-msb-bitexprs-for-id)))

  (defthm vl-exprlist-p-of-vl-msb-bitexprs-for-id
    (implies (and (force (vl-expr-p idexpr))
                  (force (vl-idexpr-p idexpr))
                  (force (vl-module-p mod)))
             (vl-exprlist-p
              (mv-nth 1 (vl-msb-bitexprs-for-id idexpr mod))))))



(defsection vl-msb-bitexprs-for-partselect
  :parents (vl-partition-lvalue)
  :short "@(call vl-msb-bitexprs-for-partselect) returns <tt>(mv successp
exprs)</tt>, where <tt>selexpr</tt> is basically <tt>foo[high:low]</tt> and
<tt>exprs</tt> is <tt>(foo[high] foo[high-1] ... foo[low])</tt>."

  (defund vl-msb-bitexprs-for-partselect (selexpr)
    "Returns (MV SUCCESSP EXPRS)"
    (declare (xargs :guard (and (vl-expr-p selexpr)
                                (vl-nonatom-p selexpr)
                                (equal (vl-nonatom->op selexpr) :vl-partselect-colon))))
    (b* ((args (vl-nonatom->args selexpr))
         (from (first args))
         (high (second args))
         (low  (third args))
         ((unless (and (vl-idexpr-p from)
                       (vl-expr-resolved-p high)
                       (vl-expr-resolved-p low)))
          (mv nil nil))
         (high-index (vl-resolved->val high))
         (low-index  (vl-resolved->val low))
         ((unless (and (natp high-index)
                       (natp low-index)
                       (<= low-index high-index)))
          (mv nil nil))
         (bits (vl-msb-bitexprs-for-id-aux from low-index high-index)))
        (mv t bits)))

  (defmvtypes vl-msb-bitexprs-for-partselect (booleanp true-listp))

  (local (in-theory (enable vl-msb-bitexprs-for-partselect)))

  (defthm vl-exprlist-p-of-vl-msb-bitexprs-for-partselect
    (implies (and (force (vl-expr-p selexpr))
                  (force (vl-nonatom-p selexpr))
                  (force (equal (vl-nonatom->op selexpr) :vl-partselect-colon)))
             (vl-exprlist-p
              (mv-nth 1 (vl-msb-bitexprs-for-partselect selexpr))))))



(defsection vl-lvalue-msb-bitexprs
  :parents (vl-partition-lvalue)
  :short "@(call vl-lvalue-msb-bitexprs) returns <tt>(mv successp exprs)</tt>,
where <tt>exprs</tt> is a list of one-bit expressions whose concatenation is
semantically equivalent to <tt>x</tt>."

  (mutual-recursion

   (defund vl-lvalue-msb-bitexprs (x mod)
     "Returns (MV SUCCESSP EXPRS)"
     (declare (xargs :guard (and (vl-expr-p x)
                                 (vl-module-p mod))
                     :verify-guards nil
                     :measure (two-nats-measure (acl2-count x) 1)))
     (if (vl-fast-atom-p x)
         (cond ((vl-idexpr-p x)
                (vl-msb-bitexprs-for-id x mod))
               (t
                ;; Not supported as lvalue
                (mv nil nil)))
       (case (vl-nonatom->op x)
         (:vl-concat
          (vl-lvaluelist-msb-bitexprs (vl-nonatom->args x) mod))
         (:vl-bitselect
          (mv t (list x)))
         (:vl-partselect-colon
          (vl-msb-bitexprs-for-partselect x))
         (otherwise
          ;; Not supported as lvalue
          (mv nil nil)))))

   (defund vl-lvaluelist-msb-bitexprs (x mod)
     (declare (xargs :guard (and (vl-exprlist-p x)
                                 (vl-module-p mod))
                     :measure (two-nats-measure (acl2-count x) 0)))
     (if (atom x)
         (mv nil nil)
       (b* (((mv car-successp car-bits)
             (vl-lvalue-msb-bitexprs (car x) mod))
            ((mv cdr-successp cdr-bits)
             (vl-lvaluelist-msb-bitexprs (cdr x) mod)))
           (mv (and car-successp cdr-successp)
               (append car-bits cdr-bits))))))

  (FLAG::make-flag flag-vl-lvalue-msb-bitexprs
                   vl-lvalue-msb-bitexprs
                   :flag-mapping ((vl-lvalue-msb-bitexprs . expr)
                                  (vl-lvaluelist-msb-bitexprs . list)))

  (defthm-flag-vl-lvalue-msb-bitexprs lemma
    (expr (implies (and (force (vl-expr-p x))
                        (force (vl-module-p mod)))
                   (vl-exprlist-p
                    (mv-nth 1 (vl-lvalue-msb-bitexprs x mod))))
          :name vl-expr-list-p-of-vl-lvalue-msb-bitexprs)
    (list (implies (and (force (vl-exprlist-p x))
                        (force (vl-module-p mod)))
                   (vl-exprlist-p
                    (mv-nth 1 (vl-lvaluelist-msb-bitexprs x mod))))
          :name vl-expr-list-p-of-vl-lvaluelist-msb-bitexprs)
    :hints(("Goal"
            :induct (flag-vl-lvalue-msb-bitexprs flag x mod)
            :in-theory (enable vl-lvalue-msb-bitexprs
                               vl-lvaluelist-msb-bitexprs))))

  (defthm-flag-vl-lvalue-msb-bitexprs lemma
    (expr (true-listp (mv-nth 1 (vl-lvalue-msb-bitexprs x mod)))
          :rule-classes :type-prescription
          :name true-listp-of-vl-lvalue-msb-bitexprs)
    (list (true-listp (mv-nth 1 (vl-lvaluelist-msb-bitexprs x mod)))
          :rule-classes :type-prescription
          :name true-listp-of-vl-lvaluelist-msb-bitexprs)
    :hints(("Goal"
            :induct (flag-vl-lvalue-msb-bitexprs flag x mod)
            :in-theory (enable vl-lvalue-msb-bitexprs
                               vl-lvaluelist-msb-bitexprs))))

  (verify-guards vl-lvalue-msb-bitexprs))




(defsection vl-safe-lvalue-msb-bitexprs
  :parents (vl-partition-lvalue)
  :short "Same as @(see vl-lvalue-msb-bitexprs), but with some extra sanity
checking."
  :long "@(def vl-safe-lvalue-msb-bitexprs)"

  (defund vl-safe-lvalue-msb-bitexprs (x mod)
    "Returns (MV SUCCESSP EXPRS)"
    (declare (xargs :guard (and (vl-expr-p x)
                                (vl-module-p mod))))
    (b* (((mv successp bits)
          (vl-lvalue-msb-bitexprs x mod))
         ((unless successp)
          ;; some problem with the lvalue itself
          (mv nil nil))

         ;; Extra sanity checks, consider trying to prove these away
         (blen (len bits))
         ((unless (all-equalp 1 (vl-exprlist->finalwidths bits)))
          (mv (cw "vl-partition-lvalue: expected msb-bitexprs to each be one bit wide.")
              nil))
         ((unless (equal blen (vl-expr->finalwidth x)))
          (mv (cw "vl-partition-lvalue: expected msb-bitexprs to have lvalue's width.")
              nil)))
        (mv t bits)))

  (defmvtypes vl-safe-lvalue-msb-bitexprs (booleanp true-listp))

  (local (in-theory (enable vl-safe-lvalue-msb-bitexprs)))

  (defthm vl-exprlist-p-of-vl-safe-lvalue-msb-bitexprs
    (implies (and (force (vl-expr-p x))
                  (force (vl-module-p mod)))
             (vl-exprlist-p
              (mv-nth 1 (vl-safe-lvalue-msb-bitexprs x mod)))))

  (local (defthm crock
           (implies (and (equal (vl-exprlist->finalwidths x) (repeat n (len x)))
                         (natp n))
                    (equal (vl-exprlist-totalwidth x)
                           (* n (len x))))
           :hints(("Goal" :in-theory (enable repeat)))))

  (defthm vl-exprlist-totalwidth-of-vl-safe-lvalue-msb-bitexprs
    (implies (and (mv-nth 0 (vl-safe-lvalue-msb-bitexprs x mod))
                  (force (vl-expr-p x))
                  (force (vl-module-p mod)))
             (equal (vl-exprlist-totalwidth (mv-nth 1 (vl-safe-lvalue-msb-bitexprs x mod)))
                    (vl-expr->finalwidth x))))

  (defthm len-of-vl-safe-lvalue-msb-bitexprs
    (implies (and (mv-nth 0 (vl-safe-lvalue-msb-bitexprs x mod))
                  (force (vl-expr-p x))
                  (force (vl-module-p mod)))
             (equal (len (mv-nth 1 (vl-safe-lvalue-msb-bitexprs x mod)))
                    (vl-expr->finalwidth x))))

  (defthm vl-exprlist->finalwidths-of-vl-safe-lvalue-msb-bitexprs
    (implies (and (mv-nth 0 (vl-safe-lvalue-msb-bitexprs x mod))
                  (force (vl-expr-p x))
                  (force (vl-module-p mod)))
             (equal (vl-exprlist->finalwidths (mv-nth 1 (vl-safe-lvalue-msb-bitexprs x mod)))
                    (repeat 1 (vl-expr->finalwidth x))))))



; Part 2.  We now partition those bits into groups of size N.

(defsection vl-partition-bitexprs

  (local (defthm lemma
           (implies (and (equal (vl-exprlist->finalwidths x) (repeat 1 (len x)))
                         (natp n)
                         (<= n (len x)))
                    (equal (vl-exprlist->finalwidths (nthcdr n x))
                           (repeat 1 (- (len x) n))))
           :hints(("Goal" :in-theory (enable repeat nthcdr)))))

  (defund vl-partition-bitexprs (n x)
    (declare (xargs :guard (and (posp n)
                                (vl-exprlist-p x)
                                (true-listp x)
                                (all-equalp 1 (vl-exprlist->finalwidths x)))
                    :measure (len x)))
    (cond ((mbe :logic (zp n) :exec nil)
           nil)
          ((< (len x) (nfix n))
           nil)
          (t
           (cons (make-vl-nonatom :op :vl-concat
                                  :args (take n x)
                                  :finalwidth n
                                  :finaltype :vl-unsigned
                                  :atts nil)
                 (vl-partition-bitexprs n (nthcdr n x))))))

  (local (in-theory (enable vl-partition-bitexprs)))

  (defthm vl-exprlist-p-of-vl-partition-bitexprs
    (implies (force (vl-exprlist-p x))
             (vl-exprlist-p (vl-partition-bitexprs n x))))

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthm len-of-vl-partition-bitexprs
    (implies (force (posp n))
             (equal (len (vl-partition-bitexprs n x))
                    (floor (len x) n))))

  (defthm vl-exprlist-totalwidth-of-vl-partition-bitexprs
    (implies (and (force (equal (rem (len x) n) 0))
                  (force (vl-exprlist-p x))
                  (force (posp n)))
             (equal (vl-exprlist-totalwidth (vl-partition-bitexprs n x))
                    (len x)))))


; Unfortunately the concatenations that result from vl-partition-bitexprs are
; ugly and in a bad normal form for later transforms.  So, we want to go ahead
; and clean them up by merging adjacent bits and getting rid of unnecessary
; concatenations.


(defsection vl-maybe-merge-selects

  (defund vl-maybe-merge-selects-aux (x from n)
    "Returns (MIN REST)"

; We look for a sequence of decreasing bit- and part- selects that count
; downward from from[n], and return the index of the final bit select that
; matches this criteria as MIN, and the remainder of X as REST.

; Here are some examples.
; Suppose FROM is the idexpr "foo", and N is 6.
;
; Then, given a sequence x = (foo[5] foo[4] foo[3] bar baz), we return
;   MIN = 3
;   REST = (bar baz)
;
; But if x = (bar baz), we just immediately return
;   MIN = 6
;   REST = (bar baz).
;
; We also handle part selects, e.g., if X is (foo[5:3], foo[2], bar, baz),
; we return
;   MIN = 2
;   REST = (bar baz).

    (declare (xargs :guard (and (vl-exprlist-p x)
                                (vl-expr-p from)
                                (natp n))))
    (b* (((when (atom x))
          (mv n x))
         (expr1 (car x))
         ((unless (and (not (vl-fast-atom-p expr1))
                       (or (eq (vl-nonatom->op expr1) :vl-bitselect)
                           (eq (vl-nonatom->op expr1) :vl-partselect-colon))))
          (mv n x))

         ;; We'll treat everything like a part select.
         (expr1-args (vl-nonatom->args expr1))
         (expr1-from (first expr1-args))
         (expr1-high (second expr1-args))
         (expr1-low  (if (eq (vl-nonatom->op expr1) :vl-bitselect)
                         expr1-high
                       (third expr1-args)))
         ((unless (and (equal expr1-from from)
                       (vl-expr-resolved-p expr1-high)
                       (vl-expr-resolved-p expr1-low)))
          (mv n x))

         (high-val (vl-resolved->val expr1-high))
         (low-val  (vl-resolved->val expr1-low))
         ((unless (and (natp high-val)
                       (natp low-val)
                       (= high-val (- n 1))
                       (<= low-val high-val)))
          (mv n x)))

      ;; If we get this far, expr1 is from[n-1] or from[n-1:low].  Let's
      ;; keep looking for more to merge after low-val.
      (vl-maybe-merge-selects-aux (cdr x) from low-val)))

  (local (in-theory (enable vl-maybe-merge-selects-aux)))

  (defthm natp-of-vl-maybe-merge-selects-aux
    (implies (force (natp n))
             (natp (mv-nth 0 (vl-maybe-merge-selects-aux x from n))))
    :rule-classes :type-prescription)

  (defthm vl-exprlist-p-of-vl-maybe-merge-selects-aux
    (implies (force (vl-exprlist-p x))
             (vl-exprlist-p (mv-nth 1 (vl-maybe-merge-selects-aux x from n)))))

  (defthm acl2-count-of-vl-maybe-merge-selects-aux-weak
    (<= (acl2-count (mv-nth 1 (vl-maybe-merge-selects-aux x from n)))
        (acl2-count x))
    :rule-classes ((:rewrite) (:linear)))

  (defthm acl2-count-of-vl-maybe-merge-selects-aux-strong
    (implies (not (equal n (mv-nth 0 (vl-maybe-merge-selects-aux x from n))))
             (< (acl2-count (mv-nth 1 (vl-maybe-merge-selects-aux x from n)))
                (acl2-count x)))
    :rule-classes ((:rewrite) (:linear)))

  (defthm upper-bound-of-vl-maybe-merge-selects-aux
    (implies (force (natp n))
             (<= (mv-nth 0 (vl-maybe-merge-selects-aux x from n))
                 n))
    :rule-classes :linear)

  (local (in-theory (disable vl-maybe-merge-selects-aux)))

  (local (in-theory (enable vl-maybe-natp)))

  (defund vl-maybe-merge-selects (x)
    (declare (xargs :guard (vl-exprlist-p x)))
    (b* (((when (atom x))
          nil)

         (expr1 (car x))
         ((when (vl-fast-atom-p expr1))
          (cons expr1 (vl-maybe-merge-selects (cdr x))))

         (expr1-op (vl-nonatom->op expr1))
         ((unless (or (eq expr1-op :vl-bitselect)
                      (eq expr1-op :vl-partselect-colon)))
          (cons expr1 (vl-maybe-merge-selects (cdr x))))

         (expr1-args (vl-nonatom->args expr1))
         (expr1-from (first expr1-args))
         (expr1-high (second expr1-args))
         (expr1-low  (if (eq (vl-nonatom->op expr1) :vl-bitselect)
                         expr1-high
                       (third expr1-args)))

         ((unless (and (vl-expr-resolved-p expr1-high)
                       (vl-expr-resolved-p expr1-low)))
          (cons expr1 (vl-maybe-merge-selects (cdr x))))

         (high-val (vl-resolved->val expr1-high))
         (low-val  (vl-resolved->val expr1-low))
         ((unless (and (natp high-val)
                       (natp low-val)
                       (<= low-val high-val)))
          (cons expr1 (vl-maybe-merge-selects (cdr x))))

         ;; Looking good: we have a bit or part select with good indicies.  Lets
         ;; see if there's anything to merge it with.
         ((mv min rest)
          (vl-maybe-merge-selects-aux (cdr x) expr1-from low-val))

         ((when (= min low-val))
          ;; There wasn't anything to merge with.
          (cons expr1 (vl-maybe-merge-selects (cdr x))))

         ;; Found something to merge with.
         (min-expr  (vl-make-index min))
         (new-expr1 (make-vl-nonatom :op :vl-partselect-colon
                                     :args (list expr1-from expr1-high min-expr)
                                     :finalwidth (+ 1 (- high-val low-val))
                                     :finaltype :vl-unsigned
                                     :atts nil)))
      (cons new-expr1 (vl-maybe-merge-selects rest))))

  (local (in-theory (enable vl-maybe-merge-selects)))

  (defthm vl-exprlist-p-of-vl-maybe-merge-selects
    (implies (force (vl-exprlist-p x))
             (vl-exprlist-p (vl-maybe-merge-selects x)))))



(defsection vl-clean-concats

  (defund vl-elim-nested-concats-pass (x)
    "Returns (MV PROGRESSP X-PRIME)"
    (declare (xargs :guard (vl-exprlist-p x)))
    (b* (((when (atom x))
          (mv nil nil))
         ((mv cdr-progressp cdr-prime) (vl-elim-nested-concats-pass (cdr x)))
         (expr1 (car x))
         ((unless (and (not (vl-fast-atom-p expr1))
                       (eq (vl-nonatom->op expr1) :vl-concat)))
          (mv cdr-progressp (cons expr1 cdr-prime)))

         ;; Else, we found a concat.  Eliminate it.
         (args (vl-nonatom->args expr1)))
        (mv t (append-without-guard args cdr-prime))))

  (defmvtypes vl-elim-nested-concats-pass (booleanp true-listp))

  (local (in-theory (enable vl-elim-nested-concats-pass)))

  (defthm vl-exprlist-p-of-vl-elim-nested-concats-pass
    (implies (vl-exprlist-p x)
             (vl-exprlist-p (mv-nth 1 (vl-elim-nested-concats-pass x)))))

  (defthm acl2-count-of-vl-elim-nested-concats-pass-weak
    (<= (acl2-count (mv-nth 1 (vl-elim-nested-concats-pass x)))
        (acl2-count x))
    :rule-classes ((:rewrite) (:linear))
    :hints(("Goal"
            :do-not '(generalize fertilize)
            :in-theory (enable acl2-count))))

  (defthm acl2-count-of-vl-elim-nested-concats-pass-strong
    (implies (mv-nth 0 (vl-elim-nested-concats-pass x))
             (< (acl2-count (mv-nth 1 (vl-elim-nested-concats-pass x)))
                (acl2-count x)))
    :rule-classes ((:rewrite) (:linear))
    :hints(("Goal"
            :do-not '(generalize fertilize)
            :in-theory (enable acl2-count))))

  (local (in-theory (disable vl-elim-nested-concats-pass)))


  (defund vl-elim-nested-concats (x)
    (declare (xargs :guard (vl-exprlist-p x)))

    ;; We assume that X are the arguments to a concatenation.  We eliminate any
    ;; nested concatenations at the top-level of X.

    (b* (((mv progressp x-prime)
          (vl-elim-nested-concats-pass x)))
        (if progressp
            (vl-elim-nested-concats x-prime)
          x-prime)))

  (local (in-theory (enable vl-elim-nested-concats)))

  (defthm true-listp-of-vl-elim-nested-concats
    (true-listp (vl-elim-nested-concats x))
    :rule-classes :type-prescription)

  (defthm vl-exprlist-p-of-vl-elim-nested-concats
    (implies (force (vl-exprlist-p x))
             (vl-exprlist-p (vl-elim-nested-concats x))))

  (local (in-theory (disable vl-elim-nested-concats)))


  (mutual-recursion

   (defund vl-expr-clean-concats (x)
     (declare (xargs :guard (vl-expr-p x)
                     :measure (two-nats-measure (acl2-count x) 1)
                     :verify-guards nil))
     (b* (((when (vl-fast-atom-p x))
           x)
          (op         (vl-nonatom->op x))
          (args       (vl-nonatom->args x))

          ((unless (eq op :vl-concat))
           ;; Not a concat, just recursively clean its args.
           (change-vl-nonatom x :args (vl-exprlist-clean-concats args)))

          (args (vl-exprlist-clean-concats args))
          (args (vl-elim-nested-concats args))
          (args (vl-maybe-merge-selects args))

          ((when (and (= (length args) 1)
                      (eq (vl-expr->finaltype (car args)) :vl-unsigned)))
           ;; Eliminate concatenation of singleton, but be careful -- if
           ;; the argument is signed, we don't want to do this because the
           ;; concatenation changes it to unsigned.
           (car args)))
         (change-vl-nonatom x :args args)))

   (defund vl-exprlist-clean-concats (x)
     (declare (xargs :guard (vl-exprlist-p x)
                     :measure (two-nats-measure (acl2-count x) 0)))
     (if (atom x)
         nil
       (cons (vl-expr-clean-concats (car x))
             (vl-exprlist-clean-concats (cdr x))))))

  (defthm vl-exprlist-clean-concats-when-not-consp
    (implies (not (consp x))
             (equal (vl-exprlist-clean-concats x)
                    nil))
    :hints(("Goal" :in-theory (enable vl-exprlist-clean-concats))))

  (defthm vl-exprlist-clean-concats-of-cons
    (equal (vl-exprlist-clean-concats (cons a x))
           (cons (vl-expr-clean-concats a)
                 (vl-exprlist-clean-concats x)))
    :hints(("Goal" :in-theory (enable vl-exprlist-clean-concats))))

  (defprojection vl-exprlist-clean-concats (x)
    (vl-expr-clean-concats x)
    :already-definedp t)

  (flag::make-flag vl-flag-expr-clean-concats
                   vl-expr-clean-concats
                   :flag-mapping ((vl-expr-clean-concats . expr)
                                  (vl-exprlist-clean-concats . list)))

  (defthm-vl-flag-expr-clean-concats lemma
    (expr (implies (force (vl-expr-p x))
                   (vl-expr-p (vl-expr-clean-concats x)))
          :name vl-expr-p-of-vl-expr-clean-concats)
    (list (implies (force (vl-exprlist-p x))
                   (vl-exprlist-p (vl-exprlist-clean-concats x)))
          :name vl-exprlist-p-of-vl-exprlist-clean-concats)
    :hints(("Goal"
            :induct (vl-flag-expr-clean-concats flag x)
            :in-theory (enable vl-expr-clean-concats))))

  (verify-guards vl-expr-clean-concats))




(defsection vl-partition-lvalue
  :parents (replicate)
  :short "Split an lvalue into <tt>n</tt>-bit segments."

  :long "<p><b>Signature:</b> @(call vl-partition-lvalue) returns <tt>(mv
successp detail exprs)</tt>.</p>

<p>Recall the notion of lvalues from @(see vl-expr-lvaluep).  In lvalue
partitioning, we take a more restrictive view of lvalues, and in particular we
don't support hierarchical identifiers or indexed part selects like <tt>[i +:
3]</tt>.  (This is only done for pragmatic reasons and we might eventually
remove this restriction if we run into a case where we need to support these
other cases.)</p>

<p>The goal of <tt>vl-partition-lvalue</tt> is to partition the lvalue
<tt>x</tt> into a list of <tt>n</tt>-bit chunks.  We are also given
<tt>mod</tt>, the module wherein <tt>x</tt> occurs, which may be needed to look
up wire ranges.</p>

<p>It is not always possible to partition <tt>x</tt>.  For instance, <tt>n</tt>
might not evenly divide the width of <tt>x</tt>.  In such cases, we set the
<tt>successp</tt> flag to <tt>nil</tt> and <tt>detail</tt> is a string that
describes the problem.</p>

<p>On success, <tt>exprs</tt> is a list of expressions, <tt>e1</tt>,
<tt>e2</tt>, <tt>...</tt>, which are each <tt>n</tt> bits wide, and the
concatenation of <tt>{e1, e2, ...}</tt> is equal to <tt>x</tt>.</p>

<p>This function originally did not take <tt>mod</tt> because it assumed that
ranges had been shifted to end with <tt>0</tt>, and this caused a bug after we
removed the range-shifting transformation.  Now we take care to look up the
ranges of the wires we are splitting.</p>"

  (defund vl-partition-lvalue (x n mod)
    "Returns (MV SUCCESSP EXPRS)"
    (declare (xargs :guard (and (vl-expr-p x)
                                (posp n)
                                (vl-module-p mod))))
    (b* ((width (vl-expr->finalwidth x))
         ((unless (and (posp width)
                       (= (rem width n) 0)))
          ;; not an even division
          (mv nil nil))

         ((mv successp bits) (vl-safe-lvalue-msb-bitexprs x mod))
         ((unless successp)  (mv nil nil))

         (ugly-bit-partitions (vl-partition-bitexprs n bits))
         (cleaned-partitions  (vl-exprlist-clean-concats ugly-bit-partitions))
         )
      (mv t cleaned-partitions)))

  (local (in-theory (enable vl-partition-lvalue)))

  (defthm vl-exprlist-p-of-vl-partition-lvalue
    (implies (and (vl-expr-p x)
                  (posp n)
                  (vl-module-p mod))
             (vl-exprlist-p (mv-nth 1 (vl-partition-lvalue x n mod)))))

  (defthm len-of-vl-partition-lvalue
    (implies (and (mv-nth 0 (vl-partition-lvalue x n mod))
                  (vl-expr-p x)
                  (posp n)
                  (vl-module-p mod))
             (equal (len (mv-nth 1 (vl-partition-lvalue x n mod)))
                    (floor (vl-expr->finalwidth x) n)))))

