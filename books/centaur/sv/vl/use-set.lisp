; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2014-2015 Centaur Technology
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

(in-package "SV")

;; (include-book "elaborate")
(include-book "../mods/compile")
(include-book "../mods/path-string")
(include-book "centaur/vl/mlib/scopestack" :dir :system)
(include-book "centaur/vl/mlib/reportcard" :dir :system)
(include-book "centaur/vl/util/summarize-parts" :dir :system)

(local (include-book "std/basic/arith-equivs" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "std/lists/sets" :dir :system))
(local (include-book "std/util/termhints" :dir :system))

(local (std::add-default-post-define-hook :fix))
(local (in-theory (disable (tau-system))))

(defprod range
  ((lsb natp :rule-classes :type-prescription)
   (width maybe-posp :rule-classes :type-prescription))
  :layout :tree)

(define in-range ((x natp) (range range-p))
  (b* (((range range)))
    (and (<= range.lsb (lnfix x))
         (or (not range.width)
             (< (- (lnfix x) range.lsb) range.width)))))

(deflist rangelist :elt-type range :true-listp t)

(define in-rangelist ((x natp) (ranges rangelist-p))
  (if (atom ranges)
      nil
    (or (in-range x (car ranges))
        (in-rangelist x (cdr ranges)))))



(defsection in-rangelist-set-equiv-congruence
  (local (defthm in-rangelist-when-member
           (implies (and (in-range n x)
                         (member x y))
                    (in-rangelist n y))
           :hints(("Goal" :in-theory (enable in-rangelist rangelist-fix)))))

  (define in-rangelist-witness ((n natp) (x rangelist-p))
    :hooks nil
    (if (atom x)
        nil
      (if (in-range n (car x)) (car x) (in-rangelist-witness n (cdr x))))
    ///
    (defthm in-rangelist-implies-witness
      (implies (in-rangelist n x)
               (b* ((elt (in-rangelist-witness n x)))
                 (and (in-range n elt)
                      (member elt x))))
      :hints(("Goal" :in-theory (enable in-rangelist)))))

  (local (defthm in-rangelist-by-subset
           (implies (and (subsetp x y)
                         (in-rangelist n x))
                    (in-rangelist n y))
           :hints (("goal" :use ((:instance in-rangelist-implies-witness))
                    :in-theory (disable in-rangelist-implies-witness
                                        subsetp-equal)))))

  (defcong set-equiv equal (in-rangelist n x) 2
    :hints(("Goal" :in-theory (enable set-equiv)
            :cases ((in-rangelist n x))))))

(define proper-range-pair-p ((x range-p) (y range-p))
  (b* (((range x))
       ((range y)))
    (and x.width
         (< (+ x.lsb x.width) y.lsb)))
  ///
  (defthm proper-range-pair-p-transitive
    (implies (and (proper-range-pair-p x y)
                  (proper-range-pair-p y z))
             (proper-range-pair-p x z))))


(define proper-rangelist-p ((x rangelist-p))
  (if (or (atom x) (atom (cdr x)))
      t
    (and (proper-range-pair-p (car x) (cadr x))
         (proper-rangelist-p (cdr x)))))




(define rangesort-compare< ((x range-p) (y range-p))
  :returns (lessp booleanp :rule-classes :type-prescription)
  ;; Sort by increasing LSB, then by decreasing width.
  (b* (((range x))
       ((range y)))
    (or (< x.lsb y.lsb)
        (and (eql x.lsb y.lsb)
             (and y.width
                  (or (not x.width)
                      (< y.width x.width))))))
  ///
  (defthm rangesort-compare-transitive
    (implies (and (rangesort-compare< x y)
                  (rangesort-compare< y z))
             (rangesort-compare< x z)))

  (defthm rangesort-compare-transitive-inv
    (implies (and (not (rangesort-compare< x y))
                  (not (rangesort-compare< y z)))
             (not (rangesort-compare< x z))))

  (defthm rangesort-irrefl
    (not (rangesort-compare< x x)))

  (defthm rangesort-compare-asymm
    (implies (rangesort-compare< x y)
             (not (rangesort-compare< y x)))))

(acl2::defsort rangelist-sort (x)
  :comparablep range-p
  :comparable-listp rangelist-p
  :true-listp t
  :compare< rangesort-compare<)

(defsection rangelist-sort-set-equiv
  (local (defthmd duplicity-is-member
           (iff (equal 0 (duplicity x y))
                (not (member x y)))
           :hints(("Goal" :in-theory (enable duplicity member)))))

  (defthm rangelist-sort-preserves-member
    (iff (member k (rangelist-sort-insertsort x))
         (member k x))
    :hints (("goal" :use ((:instance duplicity-is-member
                           (x k) (y (rangelist-sort-insertsort x)))
                          (:instance duplicity-is-member
                           (x k) (y x))))))

  (defthm rangelist-sort-set-equiv
    (set-equiv (rangelist-sort-insertsort x) x)
    :hints(("Goal" :in-theory (enable acl2::set-unequal-witness-rw)))))

(define ranges-combinable ((x range-p) (y range-p))
  :guard (not (rangesort-compare< y x))
  ;; Combines x and y into a single range if possible, else returns them in sorted order.
  (b* (((range x))
       ((range y))
       ((when (not x.width)) t)
       (x-msb+1 (+ x.lsb x.width)))
    (<= y.lsb x-msb+1))
  ///
  (defthm proper-range-pair-p-by-not-combinable-and-ordered
    (implies (and (not (rangesort-compare< y x))
                  (not (ranges-combinable x y)))
             (proper-range-pair-p x y))
    :hints(("Goal" :in-theory (enable rangesort-compare< proper-range-pair-p)))))

(define range-union ((x range-p) (y range-p))
  :guard (and (not (rangesort-compare< y x))
              (ranges-combinable x y))
  :returns (union range-p)
  (b* (((range x))
       ((range y))
       ((when (or (not x.width) (not y.width)))
        (change-range x :width nil))
       (msb+1 (max (+ x.lsb x.width)
                   (+ y.lsb y.width)))
       (width (- msb+1 x.lsb)))
    (change-range x :width width))
  ///
  (defthm range-union-correct
    (implies (and (not (rangesort-compare< y x))
                  (ranges-combinable x y))
             (iff (in-range n (range-union x y))
                  (or (in-range n x)
                      (in-range n y))))
    :hints(("Goal" :in-theory (enable rangesort-compare<
                                      ranges-combinable
                                      in-range))))

  (defthm rangesort-compare<-of-range-union
    (implies (and (not (rangesort-compare< y x))
                  (not (rangesort-compare< z y)))
             (not (rangesort-compare< z (range-union x y))))
    :hints(("Goal" :in-theory (enable rangesort-compare<))))

  (defthm range-union-not-combinable
    (implies (and (not (rangesort-compare< y x))
                  (not (rangesort-compare< z y))
                  (not (ranges-combinable x y))
                  (ranges-combinable y z))
             (not (ranges-combinable x (range-union y z))))
    :hints(("Goal" :in-theory (enable ranges-combinable
                                      rangesort-compare<))))

  (defthm range-union-not-combinable-preserves-order
    (implies (and (not (rangesort-compare< y x))
                  (not (rangesort-compare< z y))
                  (not (ranges-combinable x y))
                  (ranges-combinable y z))
             (not (rangesort-compare< (range-union y z) x)))
    :hints(("Goal" :in-theory (enable ranges-combinable
                                      rangesort-compare<))))

  ;; (defthm rangesort-compare<-of-range-union2
  ;;   (implies (and (not (rangesort-compare< y x))
  ;;                 (not (rangesort-compare< y z)))
  ;;            (not (rangesort-compare< (range-union x y) z)))
  ;;   :hints(("Goal" :in-theory (enable rangesort-compare<))))
  )

(define rangelist-simplify-aux ((first range-p) (x rangelist-p))
  :guard (rangelist-sort-ordered-p (cons first x))
  :returns (new-x rangelist-p)
  :guard-hints (("Goal" :in-theory (enable rangelist-sort-ordered-p)))
  (if (atom x)
      (list (range-fix first))
    (if (ranges-combinable first (car x))
        (rangelist-simplify-aux (range-union first (car x)) (cdr x))
      (cons (range-fix first) (rangelist-simplify-aux (car x) (cdr x)))))
  ///
  (defthm rangelist-simplify-aux-correct
    (implies (rangelist-sort-ordered-p (cons first x))
             (iff (in-rangelist n (rangelist-simplify-aux first x))
                  (in-rangelist n (cons first x))))
    :hints(("Goal" :in-theory (enable rangelist-sort-ordered-p in-rangelist))))

  (defret rangelist-simplify-aux-preserves-first-order
    (implies (and (not (rangesort-compare< first k))
                  (not (ranges-combinable k first))
                  (rangelist-sort-ordered-p (cons first x)))
             (not (rangesort-compare< (car new-x) k)))
    :hints(("Goal" :in-theory (enable rangelist-sort-ordered-p))))

  (defret rangelist-simplify-aux-preserves-not-combinable
    (implies (and (not (rangesort-compare< first k))
                  (not (ranges-combinable k first))
                  (rangelist-sort-ordered-p (cons first x)))
             (not (ranges-combinable k (car new-x))))
    :hints(("Goal" :in-theory (enable rangelist-sort-ordered-p))))

  (defthm proper-rangelist-p-of-rangelist-simplify-aux
    (implies (rangelist-sort-ordered-p (cons first x))
             (proper-rangelist-p (rangelist-simplify-aux first x)))
    :hints(("Goal" :in-theory (enable rangelist-sort-ordered-p
                                      proper-rangelist-p)))))


(define rangelist-simplify ((x rangelist-p))
  :returns (new-x rangelist-p)
  (b* (((when (atom x)) nil)
       (sort (rangelist-sort (rangelist-fix x))))
    (rangelist-simplify-aux (car sort) (cdr sort)))
  ///
  (defret rangelist-simplify-correct
    (equal (in-rangelist n new-x)
           (in-rangelist n x))
    :hints((and stable-under-simplificationp
                '(:in-theory (enable in-rangelist)))))

  (defret proper-rangelist-p-of-rangelist-simplify
    (proper-rangelist-p (rangelist-simplify x))))


(defthm proper-range-pair-p-implies-compare
  (implies (proper-range-pair-p x y)
           (not (rangesort-compare< y x)))
  :hints(("Goal" :in-theory (enable proper-range-pair-p rangesort-compare<))))

(defthm proper-range-pair-p-implies-not-combinable
  (implies (proper-range-pair-p x y)
           (not (ranges-combinable x y)))
  :hints(("Goal" :in-theory (enable proper-range-pair-p ranges-combinable))))

(defthm rangelist-sort-ordered-p-when-proper-rangelist-p
  (implies (proper-rangelist-p x)
           (rangelist-sort-ordered-p x))
  :hints(("Goal" :in-theory (enable proper-rangelist-p
                                    rangelist-sort-ordered-p))))

(define rangelist-absorb ((x range-p)
                          (y rangelist-p))
  :guard (and (proper-rangelist-p y)
              (consp y)
              (not (rangesort-compare< (car y) x))
              (ranges-combinable x (car y)))
  :returns (mv (new-x range-p)
               (new-y rangelist-p))
  :measure (len y)
  :guard-hints (("goal" :in-theory (enable rangelist-sort-ordered-p proper-rangelist-p)))
  (b* ((next-x (range-union x (car y)))
       ((when (or (atom (cdr y))
                  (not (ranges-combinable next-x (cadr y)))))
        (mv next-x (rangelist-fix (cdr y)))))
    (rangelist-absorb next-x (cdr y)))
  ///
  (defret proper-rangelist-p-of-rangelist-absorb
    (implies (and (proper-rangelist-p y)
                  (consp y)
                  (not (rangesort-compare< (car y) x))
                  (ranges-combinable x (car y)))
             (proper-rangelist-p (cons new-x new-y)))
    :hints (("goal" :in-theory (enable rangelist-sort-ordered-p proper-rangelist-p))))

  (defret proper-rangelist-p-of-rangelist-absorb-rest
    (implies (and (proper-rangelist-p y)
                  (consp y)
                  (not (rangesort-compare< (car y) x))
                  (ranges-combinable x (car y)))
             (proper-rangelist-p new-y))
    :hints (("Goal" :use proper-rangelist-p-of-rangelist-absorb
             :in-theory (e/d (proper-rangelist-p)
                             (proper-rangelist-p-of-rangelist-absorb
                              rangelist-absorb)))))

  (defret len-of-rangelist-absorb
    (implies (consp y)
             (< (len new-y) (len y)))
    :rule-classes :linear)

  (defret len-of-rangelist-absorb-by-consp-result
    (implies (consp new-y)
             (< (len new-y) (len y)))
    :rule-classes :linear)

  (defret compare/combine-of-rangelist-absorb
    (implies (and (proper-rangelist-p y)
                  (consp y)
                  (not (rangesort-compare< (car y) x))
                  (ranges-combinable x (car y))
                  (consp new-y))
             (and (not (ranges-combinable new-x (car new-y)))
                  (not (rangesort-compare< (car new-y) new-x))))
    :hints (("goal" :use proper-rangelist-p-of-rangelist-absorb
             :in-theory (enable proper-rangelist-p))))

  (local (defthm compare-of-union-when-not-combinable
           (implies (and (not (rangesort-compare< z x)))
                         ;; (not (ranges-combinable x z)))
                    (not (rangesort-compare< z (range-union x y))))
           :hints(("Goal" :in-theory (enable range-union rangesort-compare< ranges-combinable)))))

  (defret compare-with-first-of-rangelist-absorb
    (implies (and (not (rangesort-compare< z x))
                  (proper-rangelist-p y)
                  (consp y)
                  (not (rangesort-compare< (car y) x))
                  (ranges-combinable x (car y)))
             (not (rangesort-compare< z new-x)))
    :hints(("Goal" :in-theory (enable proper-rangelist-p))))

  (defret compare-with-first-of-rangelist-absorb2
    (implies (and (proper-rangelist-p y)
                  (consp y)
                  (not (rangesort-compare< (car y) x))
                  (ranges-combinable x (car y))
                  (not (rangesort-compare< x z))
                  (not (ranges-combinable z x)))
             (and (not (rangesort-compare< new-x z))
                  (not (ranges-combinable z new-x))))
    :hints(("Goal" :in-theory (enable proper-rangelist-p))))



  (defretd in-rangelist-of-rangelist-absorb
    (implies (and (proper-rangelist-p y)
                  (consp y)
                  (not (rangesort-compare< (car y) x))
                  (ranges-combinable x (car y)))
             (iff (in-rangelist n (cons new-x new-y))
                  (in-rangelist n (cons x y))))
    :hints(("Goal" :in-theory (enable in-rangelist proper-rangelist-p))))
  ;; (defret compare-with-rest-of-rangelist-absorb
  ;;   (implies (and (not (rangesort-compare< z x))
  ;;                 (proper-rangelist-p y)
  ;;                 (consp y)
  ;;                 (not (rangesort-compare< (car y) x))
  ;;                 (ranges-combinable x (car y))
  ;;                 (consp new-y))
  ;;            (not (rangesort-compare< z (car new-y))))
  ;;   :hints(("Goal" :use (compare-with-first-of-rangelist-absorb
  ;;                        compare/combine-of-rangelist-absorb)
  ;;           :in-theory (disable rangelist-absorb
  ;;                               compare-with-first-of-rangelist-absorb
  ;;                               compare/combine-of-rangelist-absorb))))
  )

;; BOZO package
(defmacro hq (&rest args) (cons 'acl2::hq args))

(define rangelist-union-aux ((first range-p)
                              (x rangelist-p)
                              (y rangelist-p))
  :guard (and (proper-rangelist-p y)
              (consp y)
              (proper-rangelist-p (cons first x))
              (not (rangesort-compare< (car y) first)))
  :measure (+ (len x) (len y))
  :returns (mv (new-first range-p)
               (new-x rangelist-p)
               (new-y rangelist-p))
  :guard-hints (("goal" :in-theory (enable proper-rangelist-p)))
  (b* (((unless (ranges-combinable first (car y)))
        (mv (range-fix first)
            (rangelist-fix x)
            (rangelist-fix y)))
       ((mv next-first next-y) (rangelist-absorb first y))
       ((unless (and (consp x) (ranges-combinable next-first (car x))))
        (mv next-first (rangelist-fix x) next-y))
       ((when (atom next-y))
        (b* (((mv last-first last-x) (rangelist-absorb next-first x)))
          (mv last-first last-x next-y))))
    (rangelist-union-aux next-first next-y x))
  ///
  (defret len-of-rangelist-union-aux
    (implies (and (consp y))
             (<= (+ (len new-x) (len new-y))
                 (+ (len x) (len y))))
    :rule-classes :linear)

  (defret proper-rangelist-p-of-rangelist-union-aux
    (implies (and (proper-rangelist-p y)
                  (consp y)
                  (not (rangesort-compare< (car y) first))
                  (proper-rangelist-p (cons first x)))
             (and (proper-rangelist-p new-x)
                  (proper-rangelist-p new-y)
                  (implies (consp new-x)
                           (and (not (ranges-combinable new-first (car new-x)))
                                (not (rangesort-compare< (car new-x) new-first))))
                  (implies (consp new-y)
                           (and (not (ranges-combinable new-first (car new-y)))
                                (not (rangesort-compare< (car new-y) new-first))))))
    :hints(("Goal" :in-theory (enable proper-rangelist-p))))

  (defret rangelist-union-aux-proper-range-pair-first
    (implies (and (proper-rangelist-p y)
                  (consp y)
                  (not (rangesort-compare< (car y) first))
                  (proper-rangelist-p (cons first x))
                  (not (rangesort-compare< first z))
                  (not (ranges-combinable z first)))
             (and (not (rangesort-compare< new-first z))
                  (not (ranges-combinable z new-first))))
    :hints(("Goal" :in-theory (enable proper-rangelist-p))))

  (defretd in-rangelist-of-rangelist-union-aux
    (implies (and (proper-rangelist-p y)
                  (consp y)
                  (proper-rangelist-p (cons first x))
                  (not (rangesort-compare< (car y) first)))
             (iff (or (in-rangelist n y)
                      (in-rangelist n (cons first x)))
                  (or (in-range n new-first)
                      (in-rangelist n new-x)
                      (in-rangelist n new-y))))
    :hints(("Goal" :in-theory (enable in-rangelist proper-rangelist-p)
            :induct t)
           (acl2::use-termhint
            (b* (((unless (ranges-combinable first (car y)))
                  nil)
                 ((acl2::termhint-seq
                   ''(:use ((:instance in-rangelist-of-rangelist-absorb
                             (x first) (y y))))))
                 ((mv next-first next-y) (rangelist-absorb first y))
                 ((unless (and (consp x) (ranges-combinable next-first (car x))))
                  nil)
                 ((when (atom next-y))
                  `'(:use ((:instance in-rangelist-of-rangelist-absorb
                            (x ,(hq next-first)) (y ,(hq x)))))))
              nil)))))
        
  


(define rangelist-union ((x rangelist-p)
                             (y rangelist-p))
  :returns (union rangelist-p)
  :guard (and (proper-rangelist-p x)
              (proper-rangelist-p y))
  :measure (+ (len x) (len y))
  :guard-hints (("goal" :expand ((proper-rangelist-p x)
                                 (proper-rangelist-p y))
                 :in-theory (enable proper-rangelist-p)))
  (b* (((when (atom x)) (rangelist-fix y))
       ((when (atom y)) (rangelist-fix x))
       (x1 (car x))
       (y1 (car y))
       ((when (rangesort-compare< x1 y1))
        (b* (((mv first rest-x rest-y)
              (rangelist-union-aux x1 (cdr x) y)))
          (cons first (rangelist-union rest-x rest-y))))
       ((mv first rest-x rest-y)
        (rangelist-union-aux y1 (cdr y) x)))
    (cons first (rangelist-union rest-x rest-y)))
  ///
  (defretd rangelist-union-proper-range-pair-first
    (implies (and (proper-rangelist-p x)
                  (proper-rangelist-p y)
                  (case-split
                    (implies (consp x)
                             (proper-range-pair-p z (car x))))
                  (case-split
                    (implies (consp y)
                             (proper-range-pair-p z (car y))))
                  (consp union))
             (proper-range-pair-p z (car union))))

  (local (in-theory (enable rangelist-union-proper-range-pair-first)))

  (defret proper-rangelist-p-of-rangelist-union
    (implies (and (proper-rangelist-p x)
                  (proper-rangelist-p y))
             (proper-rangelist-p union))
    :hints(("Goal" :in-theory (enable proper-rangelist-p))))

  (defret in-rangelist-of-rangelist-union
    (implies (and (proper-rangelist-p x)
                  (proper-rangelist-p y))
             (iff (in-rangelist n union)
                  (or (in-rangelist n x)
                      (in-rangelist n y))))
    :hints (("goal" :induct t :in-theory (enable in-rangelist))
            (acl2::use-termhint
             (b* (((when (atom x)) nil)
                  ((when (atom y)) nil)
                  (x1 (car x))
                  (y1 (car y))
                  ((when (rangesort-compare< x1 y1))
                   `'(:use ((:instance in-rangelist-of-rangelist-union-aux
                             (first ,(hq x1)) (x ,(hq (cdr x))) (y ,(hq y)))))))
               `'(:use ((:instance in-rangelist-of-rangelist-union-aux
                         (first ,(hq y1)) (x ,(hq (cdr y))) (y ,(hq x))))))))))











(fty::defmap rangemap :key-type address :val-type rangelist :true-listp t)

(define translate-address-to-outer-scope ((scope name-p)
                                          (x address-p))
  :returns (new-x address-p)
  (b* (((address x) (address-fix x))
       ((when (eq x.scope :root)) x)
       ((when (< 0 x.scope)) (change-address x :scope (1- x.scope))))
    (change-address x :path (make-path-scope :namespace scope :subpath x.path))))

(local (defthmd rangemap-fix-when-first-bad
         (implies (not (and (consp (car x))
                            (address-p (caar x))))
                  (equal (rangemap-fix x)
                         (rangemap-fix (cdr x))))
         :hints(("Goal" :in-theory (enable rangemap-fix)))))



(define translate-rangemap-to-outer-scope ((scope name-p)
                                           (x rangemap-p))
  :returns (new-x rangemap-p)
  :prepwork ((local (in-theory (enable rangemap-fix-when-first-bad))))
  (b* (((when (atom x)) nil)
       ((unless (mbt (and (consp (car x))
                          (address-p (caar x)))))
        (translate-rangemap-to-outer-scope scope (cdr x))))
    (cons (cons (translate-address-to-outer-scope scope (caar x))
                (rangelist-fix (cdar x)))
          (translate-rangemap-to-outer-scope scope (cdr x)))))


(defprod use-set
  ((uses rangemap-p)
   (sets rangemap-p))
  :layout :tree)

(fty::defmap use-set-summaries :key-type modname :val-type use-set :true-listp t)


(define lhs-to-rangemap ((x lhs-p)
                         (rangemap rangemap-p))
  :guard (svarlist-addr-p (lhs-vars x))
  :guard-hints (("goal" :in-theory (enable lhs-vars lhatom-vars)))
  :prepwork ((local (in-theory (disable rangemap-fix-when-first-bad
                                        hons-assoc-equal-of-rangemap-fix))))
  :returns (new-rangemap rangemap-p)
  (b* (((when (atom x)) (rangemap-fix rangemap))
       ((lhrange x1) (car x))
       ((when (lhatom-case x1.atom :z))
        (lhs-to-rangemap (cdr x) rangemap))
       ((lhatom-var x1) x1.atom)
       (addr (svar->address x1.name))
       (rangemap (rangemap-fix rangemap))
       (prev (cdr (hons-get addr rangemap)))
       (range (make-range :lsb x1.rsh :width x1.w)))
    (lhs-to-rangemap (cdr x)
                     (hons-acons addr (cons range prev) rangemap))))


(define assigns-to-sets ((x assigns-p) (rangemap rangemap-p))
  :guard (svarlist-addr-p (assigns-vars x))
  :guard-hints (("goal" :in-theory (enable assigns-vars)))
  :returns (new-rangemap rangemap-p)
  :prepwork ((local (defthm assigns-fix-when-not-consp-car
                      (implies (and (consp x) (not (consp (car x))))
                               (equal (assigns-fix x)
                                      (assigns-fix (cdr x))))
                      :hints(("Goal" :in-theory (enable assigns-fix))))))
  (b* (((when (atom x)) (rangemap-fix rangemap))
       ((unless (mbt (consp (car x))))
        (assigns-to-sets (cdr x) rangemap)))
    (assigns-to-sets (cdr x) (lhs-to-rangemap (caar x) rangemap))))


(local (defthm trailing-0-count-of-lognot-when-logbitp
         (implies (and (< (nfix idx) (integer-length x))
                       ;; (natp x)
                       (logbitp idx x))
                  (< 0 (bitops::trailing-0-count (lognot (logtail idx x)))))
         :hints (("goal" :in-theory (enable* ihsext-inductions
                                             ihsext-recursive-redefs
                                             bitops::trailing-0-count)))
         :rule-classes :linear))

(local (defthm logbitp-of-trailing-0-count
         (implies (not (zip x))
                  (logbitp (bitops::trailing-0-count x) x))
         :hints (("goal" :in-theory (enable* ihsext-inductions
                                             ihsext-recursive-redefs
                                             bitops::trailing-0-count)))))
       
(local (defthmd logbitp-of-trailing-0-count-logtail
         (implies (< (nfix idx) (integer-length x))
                  (logbitp (+ (nfix idx) (bitops::trailing-0-count (logtail idx x))) x))
         :hints (("goal" :in-theory (enable* ihsext-inductions
                                             ihsext-recursive-redefs
                                             bitops::trailing-0-count)))))

(local (defthm trailing-0-count-lte-integer-length
         (<= (bitops::trailing-0-count x) (integer-length x))
         :hints (("goal" :in-theory (enable* ihsext-inductions
                                             ihsext-recursive-redefs
                                             bitops::trailing-0-count)))
         :rule-classes :linear))

(local (defthmd lte-integer-length-of-trailing-0-count-logtail
         (implies (< (nfix idx) (integer-length x))
                  (<= (+ (nfix idx) (bitops::trailing-0-count (logtail idx x)))
                      (integer-length x)))
         :hints (("goal" :in-theory (enable* ihsext-inductions
                                             ihsext-recursive-redefs
                                             bitops::trailing-0-count)))))

;; (local (defthm less-than-integer-length-when-logbitp
;;          (implies (and (natp x)
;;                        (logbitp n x))
;;                   (< (nfix n) (integer-length x)))
;;          :hints(("Goal" :in-theory (enable* ihsext-inductions
;;                                             ihsext-recursive-redefs)))))

;; (local (defthm less-than-integer-length-when-logbitp-nat
;;          (implies (and (natp x) (natp n)
;;                        (logbitp n x))
;;                   (< n (integer-length x)))
;;          :hints(("Goal" :in-theory (enable* ihsext-inductions
;;                                             ihsext-recursive-redefs)))))
        
(define mask-to-ranges-aux ((x sparseint-p)
                            (len (eql len (sparseint-length x)))
                            (idx natp))
  :measure (nfix (- (integer-length (sparseint-val x)) (nfix idx)))
  :guard (eql 1 (sparseint-bit idx x))
  :guard-hints (("goal" :use ((:instance logbitp-of-trailing-0-count-logtail
                               (idx (+ idx (bitops::trailing-0-count (lognot (logtail idx (sparseint-val x))))))
                               (x (sparseint-val x))))))
  :returns (ranges rangelist-p)


  :prepwork ((local (in-theory (disable acl2::unsigned-byte-p-plus
                                        unsigned-byte-p
                                        acl2::logtail-identity
                                        bitopS::trailing-0-count-bound
                                        bitops::logbitp-when-bitmaskp
                                        bitops::logcdr-natp))))
  (b* ((idx (lnfix idx))
       ((unless (mbt (eql 1 (sparseint-bit idx x)))) nil)
       (len (mbe :logic (sparseint-length x) :exec len))
       ((when (<= len idx))
        (list (make-range :lsb idx :width nil)))
       (count (sparseint-trailing-1-count-from x idx))
       (range (make-range :lsb idx :width count))
       (next-idx (+ idx count))
       ((when (>= next-idx len))
        (list range))
       (next-idx (+ next-idx (sparseint-trailing-0-count-from x next-idx))))
    (cons range (mask-to-ranges-aux x len next-idx)))
  ///
  (defret consp-of-mask-to-ranges-aux
    (implies (logbitp idx (sparseint-val x))
             (consp ranges)))

  (defret lsb-of-mask-to-ranges-aux
    (implies (consp ranges)
             (equal (range->lsb (car ranges)) (nfix idx))))

  ;; (local (defthm lognot-of-logtail
  ;;          (equal (lognot (logtail n x))
  ;;                 (logtail n (lognot x)))))
  ;; (local (in-theory (disable bitops::logtail-of-lognot)))
  ;; (local (defthm mask-to-ranges-aux-of-integer-length
  ;;          (equal (mask-to-ranges-aux x ~x 

  (local (defthm trailing-0-count-when-not-logbitp
           (implies (not (logbitp idx x))
                    (iff (equal (bitops::trailing-0-count (logtail idx x)) 0)
                         (equal 0 (logtail idx x))))
           :hints(("Goal" :in-theory (enable* ihsext-inductions
                                              ihsext-recursive-redefs
                                              bitops::trailing-0-count)))))

  (local (defthm logtail-equal-0-limits-integer-length
           (implies (equal 0 (logtail idx x))
                    (<= (integer-length x) (nfix idx)))
           :hints(("Goal" :in-theory (enable* ihsext-inductions
                                              ihsext-recursive-redefs)))
           :rule-classes :linear))

  (defret proper-rangelist-p-of-mask-to-ranges-aux
    (proper-rangelist-p ranges)
    :hints(("Goal" :in-theory (enable proper-rangelist-p proper-range-pair-p)
            :induct t)
           (and stable-under-simplificationp
                '(:use ((:instance logbitp-of-trailing-0-count-logtail
                               (idx idx) (x (lognot (sparseint-val x)))))
                  :in-theory (disable logbitp-of-trailing-0-count-logtail)))))

  (local (defthm greater-than-trailing-0-count-when-not-logbitp
           (implies (not (logbitp n x))
                    (<= (bitops::trailing-0-count (lognot x))
                        (nfix n)))
           :hints(("Goal" :in-theory (enable* ihsext-inductions
                                              ihsext-recursive-redefs
                                              bitops::trailing-0-count)))
           :rule-classes :linear))

  (local (defthm greater-than-trailing-0-count-when-not-logbitp-logtail
           (implies (and (not (logbitp n x))
                         (<= (nfix idx) (nfix n)))
                    (<= (bitops::trailing-0-count (lognot (logtail idx x)))
                        (+ (- (nfix idx)) (nfix n))))
           :hints(("Goal" :in-theory (enable* ihsext-inductions
                                              ihsext-recursive-redefs
                                              bitops::trailing-0-count)))))

  (local (defthm greater-than-trailing-0-count-when-not-logbitp-logtail-linear
           (implies (and (bind-free '((n . n)) (n))
                         (not (logbitp n x))
                         (<= (nfix idx) (nfix n)))
                    (<= (bitops::trailing-0-count (lognot (logtail idx x)))
                        (+ (- (nfix idx)) (nfix n))))
           :hints(("Goal" :in-theory (enable* ihsext-inductions
                                              ihsext-recursive-redefs
                                              bitops::trailing-0-count)))
           :rule-classes ((:linear :trigger-terms ((bitops::trailing-0-count (lognot (logtail idx x))))))))

  (local (defthm greater-than-trailing-0-count-when-logbitp
           (implies (logbitp n x)
                    (<= (bitops::trailing-0-count x)
                        (nfix n)))
           :hints(("Goal" :in-theory (enable* ihsext-inductions
                                              ihsext-recursive-redefs
                                              bitops::trailing-0-count)))
           :rule-classes :linear))

  (local (defthm greater-than-trailing-0-count-when-logbitp-logtail
           (implies (and (logbitp n x)
                         (<= (nfix idx) (nfix n)))
                    (<= (bitops::trailing-0-count (logtail idx x))
                        (+ (- (nfix idx)) (nfix n))))
           :hints(("Goal" :in-theory (enable* ihsext-inductions
                                              ihsext-recursive-redefs
                                              bitops::trailing-0-count)))))

  (local (defthm greater-than-trailing-0-count-when-logbitp-logtail-linear
           (implies (and (bind-free '((n . n)) (n))
                         (logbitp n x)
                         (<= (nfix idx) (nfix n)))
                    (<= (bitops::trailing-0-count (logtail idx x))
                        (+ (- (nfix idx)) (nfix n))))
           :hints(("Goal" :in-theory (enable* ihsext-inductions
                                              ihsext-recursive-redefs
                                              bitops::trailing-0-count)))
           :rule-classes ((:linear :trigger-terms ((bitops::trailing-0-count (logtail idx x)))))))

  (local (defthm in-rangelist-nil
           (not (in-rangelist n nil))
           :hints(("Goal" :in-theory (enable in-rangelist)))))

  (local (defthm logbitp-greater-than-integer-length
           (implies (<= (integer-length x) (nfix n))
                    (iff (logbitp n x)
                         (< (ifix x) 0)))
           :hints(("Goal" :in-theory (enable* ihsext-inductions
                                              ihsext-recursive-redefs)))))

  (defret in-rangelist-of-mask-to-ranges-aux
    (implies (logbitp idx (sparseint-val x))
             (iff (in-rangelist n ranges)
                  (and (<= (nfix idx) (nfix n))
                       (logbitp n (sparseint-val x)))))
    :hints(("Goal" :in-theory (e/d (in-range)
                                   ((:d mask-to-ranges-aux)))
            :induct <call>
            :expand (<call>
                     (:free (a b) (in-rangelist n (cons a b)))))
           (and stable-under-simplificationp
                '(:use ((:instance logbitp-of-trailing-0-count-logtail
                               (idx idx) (x (lognot (sparseint-val x))))
                        (:instance logbitp-of-trailing-0-count-logtail
                         (idx (+ (nfix idx) (bitops::trailing-0-count (lognot (logtail idx (sparseint-val x))))))
                         (x (sparseint-val x))))
                  :in-theory (disable logbitp-of-trailing-0-count-logtail))))))

(define mask-to-ranges ((x sparseint-p))
  :returns (ranges rangelist-p)
  (if (sparseint-equal x 0)
      nil
    (mask-to-ranges-aux x (sparseint-length x)
                        (sparseint-trailing-0-count x)))
  ///
  (defret proper-rangelist-p-of-mask-to-ranges
    (proper-rangelist-p ranges))

  (local (defthm in-rangelist-nil
           (not (in-rangelist n nil))
           :hints(("Goal" :in-theory (enable in-rangelist)))))

  
  (local (defthm greater-than-trailing-0-count-when-logbitp
           (implies (logbitp n x)
                    (<= (bitops::trailing-0-count x)
                        (nfix n)))
           :hints(("Goal" :in-theory (enable* ihsext-inductions
                                              ihsext-recursive-redefs
                                              bitops::trailing-0-count)))
           :rule-classes :linear))

  (defret in-rangelist-of-mask-to-ranges
    (iff (in-rangelist n ranges)
         (logbitp n (sparseint-val x)))))
       


(define svex-mask-alist-to-rangemap ((x svex-mask-alist-p)
                                     (uses rangemap-p)
                                     (warnings vl::vl-warninglist-p))
  :guard (svarlist-addr-p (svexlist-vars (svex-mask-alist-keys x)))
  :guard-hints (("goal" :in-theory (enable svex-mask-alist-keys)))
  :returns (mv (new-uses rangemap-p)
               (new-warnings vl::vl-warninglist-p))
  :prepwork ((local (defthm svex-mask-alist-fix-when-first-bad
                      (implies (and (consp x)
                                    (not (and (consp (car x))
                                              (svex-p (caar x)))))
                               (equal (svex-mask-alist-fix x)
                                      (svex-mask-alist-fix (cdr x))))
                    :hints(("Goal" :in-theory (enable svex-mask-alist-fix)))))
             (local (defthm svex-mask-alist-fix-when-first-good
                      (implies (and (consp x)
                                    (consp (car x))
                                    (svex-p (caar x)))
                               (equal (svex-mask-alist-fix x)
                                      (cons (cons (caar x) (4vmask-fix (cdar x)))
                                            (svex-mask-alist-fix (cdr x)))))
                    :hints(("Goal" :in-theory (enable svex-mask-alist-fix)))))
             (local (defthm svex-mask-alist-fix-when-atom
                      (implies (not (consp x))
                               (equal (svex-mask-alist-fix x) nil))
                      :hints(("Goal" :in-theory (enable svex-mask-alist-fix))))))
  (b* (((when (atom x))
        (mv (rangemap-fix uses)
            (vl::vl-warninglist-fix warnings)))
       ((unless (mbt (and (consp (car x)) (svex-p (caar x)))))
        (svex-mask-alist-to-rangemap (cdr x) uses warnings))
       (var (caar x))
       ((unless (svex-case var :var))
        (svex-mask-alist-to-rangemap (cdr x) uses warnings))
       (svar (svex-var->name var))
       (addr (svar->address svar))
       (mask (4vmask-fix (cdar x)))
       (ranges (mask-to-ranges mask))
       ;; note: we can have multiple entries for different delays of the same
       ;; address; we count them all as uses of the variable.
       (prev-ranges (cdr (hons-get addr (rangemap-fix uses))))
       (uses (hons-acons addr (append-tr ranges prev-ranges)
                         (rangemap-fix uses)))
       (warnings (if (sparseint-< mask 0)
                     (cons (vl::make-vl-warning
                            :type :sv-use-set-unresolved-range
                            :msg "Couldn't resolve the range of possible uses for ~w0 (negative caremask)."
                            :args (list (path->string-top (address->path addr))))
                           (vl::vl-warninglist-fix warnings))
                   (vl::vl-warninglist-fix warnings))))
    (svex-mask-alist-to-rangemap (cdr x) uses warnings)))





(define range-apply-atom-alias ((x range-p)
                                (width posp)
                                (lsb1 natp)
                                (lsb2 natp))
  ;; Suppose a segment of width W of signals A and B are aliased -- A[lsb1+:w]
  ;; <-> B[lsb2+:w].  If we know some range lsbR+:wR of A is used(set), find
  ;; the corresponding range of B that is used(set), if any.
  :returns (new-x (iff (range-p new-x) new-x))
  (b* (((range x))
       ;; Find overlap of x with the (lsb1, width) range.
       (overlap-lsb (max x.lsb (lnfix lsb1)))
       (overlap-msb (if x.width
                        (min (+ x.lsb x.width -1) (+ (lnfix lsb1) (lposfix width) -1))
                      (+ (lnfix lsb1) (lposfix width) -1)))
       ((when (< overlap-msb overlap-lsb))
        nil)
       (overlap-width (+ 1 (- overlap-msb overlap-lsb))))
    (make-range :width overlap-width
                :lsb (+ (lnfix lsb2) (- overlap-lsb (lnfix lsb1))))))

(define rangelist-apply-atom-alias ((x rangelist-p)
                                    (width posp)
                                    (lsb1 natp)
                                    (lsb2 natp))
  :returns (new-x rangelist-p)
  (if (atom x)
      nil
    (b* ((new-range (range-apply-atom-alias (car x) width lsb1 lsb2)))
      (if new-range
          (cons new-range
                (rangelist-apply-atom-alias (cdr x) width lsb1 lsb2))
        (rangelist-apply-atom-alias (cdr x) width lsb1 lsb2)))))

(define address-norm ((x address-p)
                      (modidx natp)
                      (moddb moddb-ok)
                      (aliases))
  :returns (mv errmsg (lhs lhs-p))
  :guard (and (< modidx (moddb->nmods moddb))
              (<= (moddb-mod-totalwires modidx moddb) (aliass-length aliases)))
  (b* (((address x))
       ((unless (eql 0 x.scope))
        ;; reference to a higher-level module. skip?
        (cw "Skipping address referencing higher-level scope: ~x0~%" (address-fix x))
        (mv nil nil))
       (idx (moddb-path->wireidx x.path modidx moddb))
       ((unless idx)
        (mv (msg "Couldn't find index for path ~s0~%" (path->string-top x.path)) nil)))
    (mv nil (get-alias idx aliases)))
  ///
  (defret svarlist-addr-p-of-addr-norm
    (implies (svarlist-addr-p (aliases-vars aliases))
             (svarlist-addr-p (lhs-vars lhs )))))

(define rangelist-apply-alias ((addr address-p)
                               (width posp)
                               (offset natp)
                               (rsh natp)
                               (ranges rangelist-p)
                               (acc rangemap-p))
  :returns (mv (new-acc rangemap-p)
               (new-ranges rangelist-p))
  :guard (proper-rangelist-p ranges)
  :prepwork ((local (in-theory (enable proper-rangelist-p))))
  (b* ((addr (address-fix addr))
       (acc (rangemap-fix acc))
       ((when (atom ranges)) (mv acc nil))
       ((range r1) (car ranges))
       (next-seg-lsb (+ (lnfix offset) (lposfix width)))
       ((when (<= next-seg-lsb
                  r1.lsb))
        ;; if the lsb is past the "from" segment we're done
        (mv acc (rangelist-fix ranges)))
       (new-range (range-apply-atom-alias r1 width offset rsh))
       (acc (if new-range
                (hons-acons addr (cons new-range (cdr (hons-get addr acc))) acc)
              acc))
       ;; if the msb of the range is not past the "from" segment then we don't
       ;; need to consider this range next time
       ((when (and r1.width (< (+ r1.lsb r1.width) next-seg-lsb)))
        (rangelist-apply-alias addr width offset rsh (cdr ranges) acc))
       ((mv acc &)
        (rangelist-apply-alias addr width offset rsh (cdr ranges) acc)))
    (mv acc (rangelist-fix ranges)))
  ///
  (defret proper-rangelist-p-of-rangelist-apply-alias
    (implies (proper-rangelist-p ranges)
             (proper-rangelist-p new-ranges)))

  ;; for fix hook
  (local (in-theory (disable (:d rangelist-apply-alias)))))
       
       

;; Ranges are uses/sets of a variable whose tail at offset is aliased to the
;; given lhs.  This function finds the ranges that overlap each segment of the
;; LHS and maps them into the segment address's entry in the new rangemap.
(define rangelist-map-lhs ((lhs lhs-p)
                           (offset natp)
                           (ranges rangelist-p)
                           (acc rangemap-p))
  :returns (new-acc rangemap-p)
  :guard (and (svarlist-addr-p (lhs-vars lhs))
              (proper-rangelist-p ranges))
  :guard-hints (("goal" :in-theory (enable lhs-vars lhatom-vars)))
  (b* (((when (atom lhs)) (rangemap-fix acc))
       ((lhrange l1) (car lhs))
       ((when (lhatom-case l1.atom :z))
        (rangelist-map-lhs (cdr lhs) (+ (lnfix offset) l1.w) ranges acc))
       ((lhatom-var l1) l1.atom)
       (addr (svar->address l1.name))
       ((mv acc ranges)
        ;; removes the prefix containing only ranges that don't extend past width
        (rangelist-apply-alias addr l1.w offset l1.rsh ranges acc)))
    (rangelist-map-lhs (cdr lhs) (+ (lnfix offset) l1.w) ranges acc)))

(define rangemap-norm-mapping ((addr address-p)
                               (ranges rangelist-p)
                               (modidx natp)
                               (moddb moddb-ok)
                               (aliases)
                               (acc rangemap-p))
  :guard (and (< modidx (moddb->nmods moddb))
              (<= (moddb-mod-totalwires modidx moddb) (aliass-length aliases))
              (svarlist-addr-p (aliases-vars aliases)))
  :returns (new-acc rangemap-p)
  (b* (((mv err lhs) (address-norm addr modidx moddb aliases))
       ((when err)
        (cw "error normalizing address ~x0: ~@1~%" addr err)
        (rangemap-fix acc))
       (sorted-ranges (rangelist-simplify ranges)))
    (rangelist-map-lhs lhs 0 sorted-ranges acc)))
       

(define rangemap-norm ((x rangemap-p)
                       (modidx natp)
                       (moddb moddb-ok)
                       (aliases)
                       (acc rangemap-p))
  :guard (and (< modidx (moddb->nmods moddb))
              (<= (moddb-mod-totalwires modidx moddb) (aliass-length aliases))
              (svarlist-addr-p (aliases-vars aliases)))
  :prepwork ((local (in-theory (enable rangemap-fix-when-first-bad))))
  :returns (new-acc rangemap-p)
  (b* (((when (atom x)) (rangemap-fix acc))
       ((unless (mbt (and (consp (car x))
                          (address-p (caar x)))))
        (rangemap-norm (cdr x) modidx moddb aliases acc))
       (acc (rangemap-norm-mapping (caar x) (cdar x) modidx moddb aliases acc)))
    (rangemap-norm (cdr x) modidx moddb aliases acc)))

(define proper-rangemap-p ((x rangemap-p))
  :prepwork ((local (in-theory (enable rangemap-fix-when-first-bad))))
  (b* (((when (atom x)) t)
       ((unless (mbt (and (consp (car x))
                          (address-p (caar x)))))
        (proper-rangemap-p (cdr x))))
    (and (proper-rangelist-p (cdar x))
         (proper-rangemap-p (cdr x))))
  ///
  
  (defthm proper-rangelist-p-of-lookup-in-proper-rangemap
    (implies (and (proper-rangemap-p x)
                  (rangemap-p x))
             (proper-rangelist-p (cdr (hons-assoc-equal k x))))
    :hints(("Goal" :in-theory (enable hons-assoc-equal))))

  (defthm proper-rangemap-p-when-atom
    (implies (atom x)
             (proper-rangemap-p x))
    :rule-classes ((:rewrite :backchain-limit-lst 0)))

  (local (in-theory (disable (:d proper-rangemap-p)))))

(define rangemap-simplify ((x rangemap-p) (acc rangemap-p))
  :returns (new-acc rangemap-p)
  :prepwork ((local (in-theory (enable rangemap-fix-when-first-bad))))
  (b* (((when (atom x)) (rangemap-fix acc))
       ((unless (mbt (and (consp (car x))
                          (address-p (caar x)))))
        (rangemap-simplify (cdr x) acc))
       (addr (caar x))
       ((when (hons-get addr acc))
        (rangemap-simplify (cdr x) acc))
       (acc (hons-acons addr (rangelist-simplify (cdar x)) acc)))
    (rangemap-simplify (cdr x) acc))
  ///
  (defret proper-rangemap-p-of-rangemap-simplify
    (implies (proper-rangemap-p acc)
             (proper-rangemap-p new-acc))
    :hints(("Goal" :in-theory (enable proper-rangemap-p))))

  (local (in-theory (disable (:d rangemap-simplify)))))


(include-book "centaur/vl/mlib/hid-tools" :dir :system)

(define path-find-vl-item/ss ((path path-p)
                           (ss vl::vl-scopestack-p))
  :returns (mv (item (iff (vl::vl-scopeitem-p item) item))
               (item-ss vl::vl-scopestack-p))
  :measure (path-count path)
  (path-case path
    :wire (b* (((unless (stringp path.name))
                (cw "in path-find-vl-item, expected a string but found ~x0" path)
                (mv nil nil))
               ((mv item item-ss) (vl::vl-scopestack-find-item/ss path.name ss)))
            (and (not item) (cw "in path-find-vl-item, didn't find a scope item for ~x0~%" path.name))
            (mv item item-ss))
    :scope (b* (((unless (stringp path.namespace))
                 (cw "in path-find-vl-item, found namespace ~x0 where we were expecting a string: ~x1~%"
                     path.namespace path)
                 (mv nil nil))
                ((mv item item-ss) (vl::vl-scopestack-find-item/ss path.namespace ss))
                ((unless item)
                 (cw "in path-find-vl-item, didn't find a scope item for namespace ~x0"
                     path.namespace path)
                 (mv nil nil))
                ((when (eq (tag item) :vl-genbegin))
                 (b* ((genblob (vl::vl-sort-genelements (vl::vl-genblock->elems (vl::vl-genbegin->block item))
                                                        :scopetype :vl-genblock
                                                        :id path.namespace))
                      (next-ss (vl::vl-scopestack-push genblob item-ss)))
                   (path-find-vl-item/ss path.subpath next-ss)))
                ((when (eq (tag item) :vl-genarray))
                 (path-case path.subpath
                   :wire (progn$ (cw "in path-find-vl-item, found terminal ~
                                      ~x0 where we were expecting a generate ~
                                      loop index: ~x1~%"
                                     path.subpath.name path)
                                 (mv nil nil))
                   :scope (b* (((unless (integerp path.subpath.namespace))
                                (cw "in path-find-vl-item, found namespace ~
                                     ~x0 where we were expecting an index: ~
                                     ~x1~%"
                                    path.subpath.namespace path)
                                (mv nil nil))
                               (block (vl::vl-genblocklist-find-block path.subpath.namespace
                                                                      (vl::vl-genarray->blocks item)))
                               ((unless block)
                                (cw "in path-find-vl-item, expected to find a generate
                                     block named ~x0 in generate array ~x1, but
                                     no dice: ~x2~%"
                                    path.subpath.namespace path.namespace path)
                                (mv nil nil))
                               (array-scope (vl::vl-sort-genelements nil :scopetype :vl-genarray
                                                                 :id path.namespace))
                               (block-scope (vl::vl-sort-genelements
                                             (vl::vl-genblock->elems block)
                                             :scopetype :vl-genarrayblock
                                             :id path.subpath.namespace))
                               (next-ss (vl::vl-scopestack-push block-scope
                                                                (vl::vl-scopestack-push array-scope item-ss))))
                            (path-find-vl-item/ss path.subpath.subpath next-ss)))))
             (cw "in path-find-vl-item, expected ~x0 to be a resolved ~
                  generate block or loop name, but none was found: ~x1~%"
                 path.namespace path)
             (mv nil nil))))

(local (defthmd not-in-rangelist-when-less
         (implies (and (proper-rangelist-p x)
                       (consp x)
                       (< (nfix n) (range->lsb (car x))))
                  (not (in-rangelist n x)))
         :hints(("Goal" :in-theory (enable proper-rangelist-p proper-range-pair-p
                                           in-rangelist in-range)))))

(define rangelist-inverse-aux ((x rangelist-p))
  :guard (and (proper-rangelist-p x)
              (consp x))
  :returns (inverse rangelist-p)
  :measure (len x)
  :guard-hints (("goal" :in-theory (enable proper-rangelist-p proper-range-pair-p)))
  ;; Returns the ranges missing between x1.lsb and w.
  (b* (((range x1) (car x))
       ((unless x1.width) nil)
       (after-msb (+ x1.lsb x1.width))
       (rest (cdr x))
       ((when (atom rest))
        (list (make-range :lsb after-msb :width nil)))
       ((range x2) (car rest)))
    (cons (make-range :lsb after-msb :width (- x2.lsb after-msb))
          (rangelist-inverse-aux rest)))
  ///
  (defret in-rangelist-of-rangelist-inverse-aux
    (implies (and (proper-rangelist-p x) (consp x))
             (iff (in-rangelist k inverse)
                  (and (<= (range->lsb (car x)) (nfix k))
                       (not (in-rangelist k x)))))
    :hints(("Goal" :in-theory (enable proper-rangelist-p proper-range-pair-p in-range in-rangelist
                                      not-in-rangelist-when-less)
            :expand ((in-rangelist k x))
            :induct t)))

  (defret proper-rangelist-p-of-rangelist-inverse-aux
    (implies (proper-rangelist-p x)
             (proper-rangelist-p inverse))
    :hints(("Goal" :in-theory (enable proper-rangelist-p proper-range-pair-p))))

  (defret rangelist-inverse-aux-lsb
    (implies (consp inverse)
             (< (range->lsb (car x))
                (range->lsb (car inverse))))
    :rule-classes :linear))


(define rangelist-inverse ((x rangelist-p))
  :guard (proper-rangelist-p x)
  :returns (inverse rangelist-p)
  (b* (((when (atom x))
        (list (make-range :lsb 0 :width nil)))
       ((range x1) (car x))
       ((when (eql 0 x1.lsb))
        (rangelist-inverse-aux x)))
    (cons (make-range :lsb 0 :width x1.lsb)
          (rangelist-inverse-aux x)))
  ///
  (defret in-rangelist-of-rangelist-inverse
    (implies (proper-rangelist-p x)
             (iff (in-rangelist k inverse)
                  (not (in-rangelist k x))))
    :hints(("Goal" :in-theory (enable proper-rangelist-p proper-range-pair-p in-range in-rangelist
                                      not-in-rangelist-when-less))))

  (defret proper-rangelist-p-of-rangelist-inverse
    (implies (proper-rangelist-p x)
             (proper-rangelist-p inverse))
    :hints(("Goal" :in-theory (enable proper-rangelist-p proper-range-pair-p)))))

(define rangelist-truncate ((x rangelist-p)
                            (w natp))
  :returns (new-x rangelist-p)
  (b* (((when (atom x)) nil)
       ((range x1) (car x))
       (w (lnfix w))
       ((when (<= w x1.lsb)) (rangelist-truncate (cdr x) w))
       (new-x1 (change-range x1 :width (if x1.width
                                           (min x1.width (- w x1.lsb))
                                         (- w x1.lsb)))))
    (cons new-x1 (rangelist-truncate (cdr x) w)))
  ///
  (local (defret lsb-of-rangelist-truncate
           (implies (and (proper-rangelist-p x)
                         (consp new-x))
                    (<= (range->lsb (car x)) (range->lsb (car new-x))))
           :hints(("Goal" :in-theory (enable proper-rangelist-p proper-range-pair-p)))
           :rule-classes :linear))

  (defret proper-rangelist-p-of-rangelist-truncate
    (implies (proper-rangelist-p x)
             (proper-rangelist-p new-x))
    :hints(("Goal" :in-theory (enable proper-rangelist-p proper-range-pair-p))))

  (defret in-range-of-rangelist-truncate
    (iff (in-rangelist n new-x)
         (and (< (nfix n) (lnfix w))
              (in-rangelist n x)))
    :hints(("Goal" :in-theory (enable in-rangelist in-range)))))

(define rangelist-chop ((lsb natp)
                        (x rangelist-p))
  :guard (proper-rangelist-p x)
  :guard-hints (("goal" :in-theory (enable proper-rangelist-p)))
  :returns (chop rangelist-p)
  :measure (len x)
  (b* (((when (atom x)) nil)
       ((range x1) (car x))
       (lsb (lnfix lsb))
       ((when (<= lsb x1.lsb)) (rangelist-fix x))
       ((unless x1.width)
        (list (make-range :lsb lsb :width nil)))
       (x-msb+1 (+ x1.lsb x1.width))
       ((when (<= x-msb+1 lsb))
        (rangelist-chop lsb (cdr x))))
    (cons (make-range :lsb lsb :width (- x-msb+1 lsb)) (rangelist-fix (cdr x))))
  ///
  (defret proper-rangelist-p-of-rangelist-chop
    (implies (proper-rangelist-p x)
             (proper-rangelist-p chop))
    :hints(("Goal" :in-theory (enable proper-rangelist-p proper-range-pair-p))))

  (defret in-range-of-rangelist-chop
    (implies (proper-rangelist-p x)
             (iff (in-rangelist n chop)
                  (and (<= (nfix lsb) (nfix n))
                       (in-rangelist n x))))
    :hints(("Goal" :in-theory (enable in-rangelist
                                      proper-rangelist-p
                                      in-range
                                      not-in-rangelist-when-less
                                      proper-range-pair-p)))))

(define rangelist-difference ((x rangelist-p)
                              (y rangelist-p))
  :guard (and (proper-rangelist-p x)
              (proper-rangelist-p y))
  :guard-hints (("goal" :in-theory (enable proper-rangelist-p
                                           proper-range-pair-p)))
  :measure (+ (len x) (len y))
  :returns (diff rangelist-p)
  (b* (((when (atom x)) nil)
       ((when (atom y)) (rangelist-fix x))
       ((range x1) (range-fix (car x)))
       ((range y1) (car y))
       ((unless x1.width) (rangelist-chop x1.lsb (rangelist-inverse (rangelist-chop x1.lsb y))))
       (x1-past-msb (+ x1.width x1.lsb))
       ((when (<= x1-past-msb y1.lsb))
        (cons x1 (rangelist-difference (cdr x) y)))
       ((unless y1.width)
        (and (< x1.lsb y1.lsb)
             (list (make-range :lsb x1.lsb :width (- y1.lsb x1.lsb)))))
       (y1-past-msb (+ y1.width y1.lsb))
       ((when (<= y1-past-msb x1.lsb))
        (rangelist-difference x (cdr y)))
       (rest (b* (((when (<= x1-past-msb y1-past-msb))
                   (rangelist-difference (cdr x) y))
                  (rest-x1 (make-range :lsb y1-past-msb :width (- x1-past-msb y1-past-msb))))
               (rangelist-difference (cons rest-x1 (cdr x)) (cdr y))))
       ((when (< x1.lsb y1.lsb))
        (b* ((range1 (make-range :lsb x1.lsb :width (- y1.lsb x1.lsb))))
          (cons range1 rest))))
    rest)
  /// 
  (local (defret lsb-of-rangelist-chop
           (implies (and (consp chop)
                         (proper-rangelist-p x))
                    (<= (nfix lsb) (range->lsb (car chop))))
           :hints(("Goal" :in-theory (enable proper-rangelist-p
                                             rangelist-chop)))
           :rule-classes :linear
           :fn rangelist-chop))

  (local (defret lsb-of-rangelist-difference
           (implies (and (proper-rangelist-p x)
                         (proper-rangelist-p y)
                         (consp diff))
                    (<= (range->lsb (car x)) (range->lsb (car diff))))
           :hints(("Goal" :in-theory (enable proper-rangelist-p proper-range-pair-p
                                             not-in-rangelist-when-less)))
           :rule-classes :linear))

  (defret proper-rangelist-p-of-rangelist-difference
    (implies (and (proper-rangelist-p x)
                  (proper-rangelist-p y))
             (proper-rangelist-p diff))
    :hints(("Goal" :in-theory (enable proper-rangelist-p proper-range-pair-p
                                      not-in-rangelist-when-less))))
  (local (defthm in-rangelist-when-atom
           (implies (atom x)
                    (not (in-rangelist n x)))
           :hints(("Goal" :in-theory (enable in-rangelist)))
           :rule-classes ((:rewrite :backchain-limit-lst 0))))

  (local (defthm proper-rangelist-p-when-atom
           (implies (atom x)
                    (proper-rangelist-p x))
           :hints(("Goal" :in-theory (enable proper-rangelist-p)))
           :rule-classes ((:rewrite :backchain-limit-lst 0))))

  ;; (local (defthm proper-range-pair-p-implies-linear
  ;;          (implies (proper-range-pair-p x y)
  ;;                   (b* (((range x)) ((range y)))
  ;;                     (< (+ x.lsb x.width) y.lsb)))
  ;;          :hints(("Goal" :in-theory (enable proper-range-pair-p)))
  ;;          :rule-classes :linear))

  ;; (local (defthm proper-range-pair-p-implies-x-width
  ;;          (implies (proper-range-pair-p x y)
  ;;                   (range->width x))
  ;;          :hints(("Goal" :in-theory (enable proper-range-pair-p)))))

  ;; (local (defthm prove-proper-range-pair-p
  ;;          (implies (b* (((range x)) ((range y)))
  ;;                     (and x.width
  ;;                          (< (+ x.lsb x.width) y.lsb)))
  ;;                   (proper-range-pair-p x y))
  ;;          :hints(("Goal" :in-theory (enable proper-range-pair-p)))))

  (defret in-range-of-rangelist-difference
    (implies (and (proper-rangelist-p x)
                  (proper-rangelist-p y))
             (iff (in-rangelist n diff)
                  (and (in-rangelist n x)
                       (not (in-rangelist n y)))))
    :hints(("Goal" :in-theory (e/d (;; in-rangelist
                                    ;; proper-rangelist-p
                                    in-range
                                    not-in-rangelist-when-less
                                    proper-range-pair-p)
                                   ((:d rangelist-difference)))
            :induct <call>
            :expand (<call>
                     (:free (a b) (proper-rangelist-p (cons a b)))
                     (proper-rangelist-p x)
                     (proper-rangelist-p y)
                     (in-rangelist n x)
                     (in-rangelist n y)
                     (in-rangelist n nil)
                     (:free (a b) (in-rangelist n (cons a b))))))))

(define rangelist-inverse-limited-aux ((w natp)
                               (x rangelist-p))
  :guard (and (proper-rangelist-p x)
              (consp x))
  :returns (inverse rangelist-p)
  :measure (len x)
  :guard-hints (("goal" :in-theory (enable proper-rangelist-p proper-range-pair-p)))
  ;; Returns the ranges missing between x1.lsb and w.
  (b* (((range x1) (car x))
       (w (lnfix w))
       ((unless x1.width) nil)
       (after-msb (+ x1.lsb x1.width))
       ((unless (< after-msb w)) nil)
       (rest (cdr x))
       ((when (atom rest))
        (list (make-range :lsb after-msb :width (- w after-msb))))
       ((range x2) (car rest))
       ((when (<= w x2.lsb))
        (list (make-range :lsb after-msb :width (- w after-msb)))))
    (cons (make-range :lsb after-msb :width (- x2.lsb after-msb))
          (rangelist-inverse-limited-aux w rest)))
  ///

  (defret in-rangelist-of-rangelist-inverse-limited-aux
    (implies (and (proper-rangelist-p x) (consp x))
             (iff (in-rangelist k inverse)
                  (and (< (nfix k) (nfix w))
                       (<= (range->lsb (car x)) (nfix k))
                       (not (in-rangelist k x)))))
    :hints(("Goal" :in-theory (enable proper-rangelist-p proper-range-pair-p in-range in-rangelist
                                      not-in-rangelist-when-less)
            :expand ((in-rangelist k x))
            :induct t)))

  (defret proper-rangelist-p-of-rangelist-inverse-limited-aux
    (implies (proper-rangelist-p x)
             (proper-rangelist-p inverse))
    :hints(("Goal" :in-theory (enable proper-rangelist-p proper-range-pair-p))))

  (defret rangelist-inverse-limited-aux-lsb
    (implies (consp inverse)
             (< (range->lsb (car x))
                (range->lsb (car inverse))))
    :rule-classes :linear))

(define rangelist-inverse-limited ((w natp)
                           (x rangelist-p))
  :guard (proper-rangelist-p x)
  :returns (inverse rangelist-p)
  (b* (((when (zp w)) nil)
       ((when (atom x))
        (list (make-range :lsb 0 :width w)))
       ((range x1) (car x))
       ((when (<= w x1.lsb))
        (list (make-range :lsb 0 :width w)))
       ((when (eql 0 x1.lsb))
        (rangelist-inverse-limited-aux w x)))
    (cons (make-range :lsb 0 :width x1.lsb)
          (rangelist-inverse-limited-aux w x)))
  ///
  (defret in-rangelist-of-rangelist-inverse-limited
    (implies (proper-rangelist-p x)
             (iff (in-rangelist k inverse)
                  (and (< (nfix k) (nfix w))
                       (not (in-rangelist k x)))))
    :hints(("Goal" :in-theory (enable proper-rangelist-p proper-range-pair-p in-range in-rangelist
                                      not-in-rangelist-when-less))))

  (defret proper-rangelist-p-of-rangelist-inverse-limited
    (implies (proper-rangelist-p x)
             (proper-rangelist-p inverse))
    :hints(("Goal" :in-theory (enable proper-rangelist-p proper-range-pair-p)))))


(include-book "centaur/vl/mlib/datatype-tools" :dir :system)

#!vl
(defthm vl-datatype-count-of-delete-dims
  (<= (vl-datatype-count (vl-datatype-update-dims nil nil x)) (vl-datatype-count x))
  :hints(("Goal" :in-theory (enable vl-datatype-count vl-datatype-update-dims)
          :expand ((vl-datatype-count x))))
  :rule-classes :linear)

;; #!vl
;; (defthm vl-datatype-size-no-err-of-delete-dims
;;   (implies (not (mv-nth 0 (vl-datatype-size x)))
;;            (not (mv-nth 0 (vl-datatype-size (vl-datatype-update-dims nil nil x)))))
;;   :hints(("Goal" :in-theory (enable vl-datatype-update-dims vl-datatype-size)
;;           :expand ((vl-datatype-size x)))))

;; #!vl
;; (defthm vl-datatype-size-exists-of-delete-dims
;;   (implies (mv-nth 1 (vl-datatype-size x))
;;            (mv-nth 1 (vl-datatype-size (vl-datatype-update-dims nil nil x))))
;;   :hints(("Goal" :in-theory (enable vl-datatype-update-dims vl-datatype-size)
;;           :expand ((vl-datatype-size x)))))

#!vl
(define entry-number-in-range ((n natp)
                               (range vl-range-p))
  :guard (vl-range-resolved-p range)
  :returns (entry integerp :rule-classes :type-prescription)
  (b* (((vl-range range))
       (msb (vl-resolved->val range.msb))
       (lsb (vl-resolved->val range.lsb))
       ((when (<= lsb msb))
        (+ lsb (lnfix n))))
    (- lsb (lnfix n))))

#!vl
(define vl-datatype-size-noerr ((x vl-datatype-p))
  :guard (vl-datatype-resolved-p x)
  :returns (size maybe-natp :rule-classes :type-prescription)
  :prepwork ((local (in-theory (disable member acl2::member-when-atom sum-nats-when-all-equalp-1 append))))
  (b* (((mv err size) (vl-datatype-size x)))
    (and (not err) size))
  ///
  (defret vl-datatype-size-exists-of-delete-dims
    (implies (vl-datatype-size-noerr x)
             (equal (vl-datatype-size-noerr (vl-datatype-update-dims nil nil x))
                    (/ (vl-datatype-size-noerr x)
                       (* (vl-dimensionlist-total-size (vl-datatype->udims x))
                          (vl-dimensionlist-total-size (vl-datatype->pdims x))))))
    :hints(("Goal" :in-theory (e/d (vl-datatype-size
                                      vl-datatype-update-dims)
                                   (ACL2::EQUAL-*-/-1))
            :expand ((vl-datatype-size x)))))
  (defret vl-datatype-size-noerr-implies-packeddims
    (implies (vl-datatype-size-noerr x)
             (and (vl-dimensionlist-resolved-p (vl-datatype->udims x))
                  (vl-dimensionlist-resolved-p (vl-datatype->pdims x))
                  (vl-dimensionlist-total-size (vl-datatype->udims x))
                  (vl-dimensionlist-total-size (vl-datatype->pdims x))))
    :hints(("Goal" :expand ((vl-datatype-size x)))))

  (defret vl-datatype-size-noerr-implies-enum-basetype
    (implies (and (vl-datatype-size-noerr x)
                  (vl-datatype-case x :vl-enum))
             (vl-datatype-size-noerr (vl-enum->basetype x)))
    :hints (("goal" :expand ((vl-datatype-size x)))))

  (defret vl-datatype-size-noerr-implies-usertype-res
    (implies (and (vl-datatype-size-noerr x)
                  (vl-datatype-case x :vl-usertype))
             (vl-datatype-size-noerr (vl-usertype->res x)))
    :hints (("goal" :expand ((vl-datatype-size x))))))



#!vl
(local
 (defsection vl-structmemberlist-sizes
   

  (local (in-theory (disable member acl2::subsetp-member
                             acl2::member-when-atom
                             sum-nats-when-all-equalp-1
                             acl2::consp-of-append
                             acl2::car-of-append
                             acl2::append-when-not-consp
                             acl2::rev-when-not-consp
                             (:d len))))

   (defthm vl-structmemberlist-sizes-of-append
     (b* (((mv err sizes) (vl-structmemberlist-sizes (append a b)))
          ((mv erra sizesa) (vl-structmemberlist-sizes a))
          ((mv errb sizesb) (vl-structmemberlist-sizes b)))
       (and (equal sizes (append sizesa sizesb))
            (iff err (or erra errb))))
     :hints(("Goal" :in-theory (enable vl-structmemberlist-sizes))))

   (defthm vl-structmemberlist-sizes-of-rev
     (b* (((mv err sizes) (vl-structmemberlist-sizes (rev x)))
          ((mv errx sizesx) (vl-structmemberlist-sizes x)))
       (and (equal sizes (rev sizesx))
            (iff err errx)))
     :hints(("Goal" :in-theory (e/d (rev) (append))
             :induct (rev x))
            (and stable-under-simplificationp
                 '(:expand ((vl-structmemberlist-sizes x)
                            (:free (a b) (vl-structmemberlist-sizes (cons a b))))))))))

#!vl
(define vl-structmemberlist-size-sum ((x vl-structmemberlist-p))
  :guard (vl-structmemberlist-resolved-p x)
  :returns (size maybe-natp :rule-classes :type-prescription)
  (b* (((mv err sizes) (vl-structmemberlist-sizes x)))
    (and (not err)
         (not (member nil sizes))
         (sum-nats sizes)))
  ///
  (defret vl-structmemberlist-size-sum-of-cons
    (equal (vl-structmemberlist-size-sum (cons a b))
           (b* ((first (vl-datatype-size-noerr (vl-structmember->type a)))
                (rest (vl-structmemberlist-size-sum b)))
             (and first rest (+ first rest))))
    :hints(("Goal" :in-theory (enable vl-datatype-size-noerr)
            :expand ((vl-structmemberlist-sizes (cons a b))))))

  (defret vl-structmemberlist-size-sum-of-vl-structmembers
    (implies (and (vl-datatype-size-noerr x)
                  (vl-datatype-case x :vl-struct)
                  (not (vl-datatype->pdims x))
                  (not (vl-datatype->udims x)))
             (equal (vl-structmemberlist-size-sum (vl-struct->members x))
                    (vl-datatype-size-noerr x)))
    :hints (("goal" :in-theory (enable vl-datatype-size-noerr)
             :expand ((vl-datatype-size x)))))
  
  (local (defthm sum-nats-of-rev
           (Equal (sum-nats (rev x))
                  (sum-nats x))))

  ;; (defthm vl-structmemberlist-size-sum-of-append
  ;;   (equal (vl-structmemberlist-size-sum (append a b))
  ;;          (and (vl-structmemberlist-size-sum a)
  ;;               (vl-structmemberlist-size-sum b)
  ;;               (+ (vl-structmemberlist-size-sum a)
  ;;                  (vl-structmemberlist-size-sum b))))
  ;;   :hints(("Goal" :in-theory (enable vl-structmemberlist-sizes)
  ;;           :induct (len a))))

  (defthm vl-structmemberlist-size-sum-of-rev
    (equal (vl-structmemberlist-size-sum (rev x))
           (vl-structmemberlist-size-sum x))
    :hints(("Goal" :in-theory (enable rev vl-structmemberlist-sizes)))))

#!vl
(define vl-structmemberlist-size-max ((x vl-structmemberlist-p))
  :guard (vl-structmemberlist-resolved-p x)
  :returns (size maybe-natp :rule-classes :type-prescription)
  (b* (((mv err sizes) (vl-structmemberlist-sizes x)))
    (and (not err)
         (not (member nil sizes))
         (max-nats sizes)))
  ///
  
  (defret vl-structmemberlist-size-max-of-cons
    (equal (vl-structmemberlist-size-max (cons a b))
           (b* ((first (vl-datatype-size-noerr (vl-structmember->type a)))
                (rest (vl-structmemberlist-size-max b)))
             (and first rest (max first rest))))
    :hints(("Goal" :in-theory (enable vl-datatype-size-noerr)
            :expand ((vl-structmemberlist-sizes (cons a b))))))

  (defret vl-structmemberlist-size-max-of-vl-unionmembers
    (implies (and (vl-datatype-size-noerr x)
                  (vl-datatype-case x :vl-union)
                  (not (vl-datatype->pdims x))
                  (not (vl-datatype->udims x)))
             (equal (vl-structmemberlist-size-max (vl-union->members x))
                    (vl-datatype-size-noerr x)))
    :hints (("goal" :in-theory (enable vl-datatype-size-noerr)
             :expand ((vl-datatype-size x))))))


;; (define first-range-overlapping ((size natp)
;;                                  (ranges rangelist-p)
;;                                  (offset natp))
;;   (b* (((unless (consp ranges)) nil)
;;        (size (lnfix size))
;;        (offset (lnfix offset))
;;        ((range r1) (car ranges))
;;        ((when (<= (+ size offset) r1.lsb))
;;         ;; msb of datatype is below lsb of ranges
;;         nil)
;;        ((when (<= (+ r1.lsb r1.width) offset))
;;         ;; lsb of datatype is above msb of first range
;;         nil))
;;     t))
       
         ;; ((when (atom ranges)) nil)
         ;; ((sv::range r1) (car ranges))
         ;; ((when (and r1.width (<= (+ r1.lsb r1.width) offset)))
         ;;  (sv-range-to-vl-chunks-datatype x size name (cdr ranges) offset))
         ;; ((when (and (<= r1.lsb offset)
         ;;             (or (not width)
         ;;                 (<= (+ size offset) (+ r1.lsb r1.width)))))
         ;;  ;; fully contained in first range
         ;;  (list (vl-printedlist->string name)))
         ;; ((when (or (<= size offset)
         ;;            (<= size r1.lsb)))
         ;;  nil))
       
#!vl
(defthm vl-structmemberlist-count-of-append
  (equal (vl-structmemberlist-count (append x y))
         (+ -1
            (vl-structmemberlist-count x)
            (vl-structmemberlist-count y)))
  :hints(("Goal" :in-theory (enable vl-structmemberlist-count))))
#!vl
(defthm vl-structmemberlist-count-of-rev
  (equal (vl-structmemberlist-count (rev x))
         (vl-structmemberlist-count x))
  :hints(("Goal" :in-theory (enable rev vl-structmemberlist-count))))

#!vl
(defthm vl-structmemberlist-resolved-p-of-append
  (implies (and (vl-structmemberlist-resolved-p x)
                (vl-structmemberlist-resolved-p y))
           (vl-structmemberlist-resolved-p (append x y)))
  :hints(("Goal" :in-theory (enable vl-structmemberlist-resolved-p append))))

#!vl
(defthm vl-structmemberlist-resolved-p-of-rev
  (implies (vl-structmemberlist-resolved-p x)
           (vl-structmemberlist-resolved-p (rev x)))
  :hints(("Goal" :in-theory (enable vl-structmemberlist-resolved-p rev))))


(local (include-book "clause-processors/just-expand" :dir :system))

(local (defthm string-listp-append
         (implies (and (string-listp x)
                       (string-listp y))
                  (string-listp (append x y)))))

(local
 (encapsulate nil
   (local (include-book "ihs/quotient-remainder-lemmas" :dir :system))
   (local (in-theory (disable (force))))
   (defthm natp-mod
     (implies (and (natp x) (natp y))
              (natp (mod x y)))
     :hints(("Goal" :in-theory (enable mod)))
     :rule-classes (:rewrite :type-prescription))

   (defthm natp-floor
     (implies (and (natp x) (natp y))
              (natp (floor x y)))
     :rule-classes (:rewrite :type-prescription))

   ;; (local (defthm floor-non-rational
   ;;          (implies (and (not (rationalp x))
   ;;                        (posp y))
   ;;                   (equal (floor x y) 0))
   ;;          :hints(("Goal" :in-theory (enable floor)))))


   (defthm mod-less
     (implies (and (posp y) (natp x))
              (< (mod x y) y))
     :hints(("Goal" :in-theory (enable mod)))
     :rule-classes :linear)))


#!vl
(defines sv-range-to-vl-chunks-datatype

  ;; modeled after vl-datatype-constraint in sv/vl/moddb.lisp
  (define sv-range-to-vl-chunks-datatype ((x vl-datatype-p)
                                          (name vl-printedtree-p)
                                          (lsb natp)
                                          (width posp))
    :returns (res string-listp)

    :well-founded-relation acl2::nat-list-<
    :measure (list (vl-datatype-count x) 10 0 0)
    :guard (and (vl-datatype-resolved-p x)
                (vl-datatype-size-noerr x))
    :verify-guards nil
    (b* ((dims (append-without-guard
                (vl-datatype->udims x)
                (vl-datatype->pdims x))))
         
      ;; (mbe :logic (b* (((mv res &)
      ;;                   (sv-range-to-vl-chunks-dims dims x name lsb width))
      ;;                  ((mv & size) (vl-datatype-size x)))
      ;;               (mv res size))
      ;;      :exec
      (sv-range-to-vl-chunks-dims dims (vl-datatype-update-dims nil nil x) name lsb width)))
  
  (define sv-range-to-vl-chunks-dims ((dims vl-dimensionlist-p)
                                      (x vl-datatype-p)
                                      (name vl-printedtree-p)
                                      (lsb natp)
                                      (width posp))
    
    :guard (and (vl-datatype-resolved-p x)
                (vl-dimensionlist-resolved-p dims)
                (vl-datatype-size-noerr x)
                (vl-dimensionlist-total-size dims)
                (not (vl-datatype->pdims x))
                (not (vl-datatype->udims x)))
    :returns (res string-listp)
    :measure (list (vl-datatype-count x) 9 (len dims) 0)
    (b* (((when (atom dims))
          (sv-range-to-vl-chunks-nodims x name lsb width))
         (name (vl-printedtree-fix name))
         (base-size (vl-datatype-size-noerr x))
         (rest-dims-size (vl-dimensionlist-total-size (cdr dims)))
         (entry-size (* base-size rest-dims-size))
         (lsb (lnfix lsb))
         (width (lposfix width))
         (dim1 (car dims))
         (range (vl-dimension->range dim1))
         (n-entries (vl-range-size range))
         (full-size (* n-entries entry-size))
         ((when (eql entry-size 0)) nil)
         ((when (and (eql lsb 0) (<= full-size width)))
          (list (vl-printedlist->string (list name))))

         ;; running example: suppose entry size is 3 and range is 5:2, so n-entries is 4.
         ;; how many entries in this array come before lsb?
         (entry-containing-lsb (floor lsb entry-size))
         ((when (<= n-entries entry-containing-lsb))
          ;; if lsb is 12, our range doesn't overlap the array at all.
          nil)
         ;; how much of the lowest entry is skipped.  If lsb is 5, then
         ;; entries-before-lsb is 1 and partial-low-entry-lsb is 2.
         (lsb-of-first-entry (mod lsb entry-size))
         ;; suppose lsb is 4. -- If width is 2, the bits we want to capture are
         ;; 5:4, which are in just one entry.  OTOH if width is 3, then it's
         ;; 6:4, which overlaps the next entry as well.
         (entry-containing-msb (floor (+ -1 lsb width) entry-size))
         ((when (eql entry-containing-msb entry-containing-lsb))
          ;; we just have (part of) one entry. Recur down.
          (sv-range-to-vl-chunks-dims (cdr dims) x
                                      (rlist name "["
                                             (str::intstr
                                              (entry-number-in-range entry-containing-lsb range))
                                             "]")
                                      lsb-of-first-entry width))
         ;; Otherwise, we have up to 3 pieces: the entry containing the lsb, if
         ;; it is not part of the middle part; the middle part between the
         ;; entries containing the lsb and the msb, and the entry containing
         ;; the msb.  We want to join the end parts with the middle part if they are complete.
         (lsb-end-complete (eql 0 lsb-of-first-entry))
         (msb-end-width (mod (+ lsb width) entry-size))
         (msb-end-complete (eql 0 msb-end-width))
         (lsb-chunk (and (not lsb-end-complete)
                         (sv-range-to-vl-chunks-dims (cdr dims) x
                                                     (rlist name "["
                                                            (str::intstr
                                                             (entry-number-in-range entry-containing-lsb range))
                                                            "]")
                                                     lsb-of-first-entry (- entry-size lsb-of-first-entry))))
         (msb-chunk (and (not msb-end-complete)
                         (sv-range-to-vl-chunks-dims (cdr dims) x
                                                     (rlist name "["
                                                            (str::intstr
                                                             (entry-number-in-range entry-containing-msb range))
                                                            "]")
                                                     0 msb-end-width)))
         (middle-range-start (if lsb-end-complete entry-containing-lsb (+ 1 entry-containing-lsb)))
         (middle-range-end (if msb-end-complete entry-containing-msb (+ -1 entry-containing-msb)))
         (middle-entry-ans (if (eql middle-range-start
                                    middle-range-end)
                               (vl-printedlist->string
                                (rlist name "[" (str::intstr (entry-number-in-range middle-range-start range)) "]"))
                             (vl-printedlist->string
                              (rlist name "["
                                    (str::intstr (entry-number-in-range middle-range-end range))
                                    ":"
                                    (str::intstr (entry-number-in-range middle-range-start range))
                                    "]")))))
      (append msb-chunk (cons middle-entry-ans lsb-chunk))))

  
  (define sv-range-to-vl-chunks-nodims ((x vl-datatype-p)
                                        (name vl-printedtree-p)
                                        (lsb natp)
                                        (width posp))
    :guard (and (vl-datatype-resolved-p x)
                (vl-datatype-size-noerr x)
                (not (vl-datatype->pdims x))
                (not (vl-datatype->udims x)))
    :returns (res string-listp)
    :measure (list (vl-datatype-count x) 8 0 0)
    (b* ((size (vl-datatype-size-noerr x))
         (lsb (lnfix lsb))
         ((when (<= size lsb))
          ;; not overlapping
          nil)
         ((when (and (eql lsb 0) (<= size (lposfix width))))
          ;; whole element
          (list (vl-printedlist->string (rlist name)))))
      (vl-datatype-case x
        :vl-coretype (b* ((msb (+ -1 (min (+ (lposfix width)  lsb) size))))
                       (list (vl-printedlist->string
                              (rlist name "[" (str::natstr msb) ":" (str::natstr lsb) "]"))))
        :vl-struct (sv-range-to-vl-chunks-structmembers (rev x.members) name lsb width)
        :vl-union (sv-range-to-vl-chunks-unionmembers x.members name size lsb width)
        :vl-enum (sv-range-to-vl-chunks-datatype x.basetype name lsb width)

        :vl-usertype (and (mbt (and x.res t))
                          (sv-range-to-vl-chunks-datatype x.res name lsb width)))))

  (define sv-range-to-vl-chunks-structmembers ((x vl-structmemberlist-p)
                                               (name vl-printedtree-p)
                                               (lsb natp)
                                               (width posp))
    :guard (and (vl-structmemberlist-resolved-p x)
                (vl-structmemberlist-size-sum x))
    :returns (res string-listp)
    :measure (list (vl-structmemberlist-count x) 11 0 0)
    (b* (((when (atom x)) nil)
         ((vl-structmember x1) (car x))
         (lsb (lnfix lsb))
         (width (lposfix width))
         (size1 (vl-datatype-size-noerr x1.type))
         ((when (<= size1 lsb))
          (sv-range-to-vl-chunks-structmembers (cdr x) name (- lsb size1) width))
         (first (sv-range-to-vl-chunks-datatype
                 x1.type
                 (rlist (vl-printedtree-fix name) "." x1.name)
                 lsb width))
         ((when (<= (+ lsb width) size1))
          first))
      (append first
              (sv-range-to-vl-chunks-structmembers (cdr x) name 0 (+ width lsb (- size1))))))

  (define sv-range-to-vl-chunks-unionmembers ((x vl-structmemberlist-p)
                                              (name vl-printedtree-p)
                                              (size)
                                              (lsb natp)
                                              (width posp))
    :guard (and (vl-structmemberlist-resolved-p x)
                (b* ((xsize (vl-structmemberlist-size-max x)))
                  (and xsize (eql size xsize))))
    :returns (res string-listp)
    :measure (list (vl-structmemberlist-count x) 11 0 0)
    (b* (((when (atom x)) nil)
         ((vl-structmember x1) (car x))
         (size (mbe :logic (vl-structmemberlist-size-max x)
                    :exec size))
         (size1 (vl-datatype-size-noerr x1.type))
         ((when (eql size1 size))
          (sv-range-to-vl-chunks-datatype
           x1.type
           (rlist (vl-printedtree-fix name) "." x1.name)
           lsb width)))
      (sv-range-to-vl-chunks-unionmembers (cdr x) name size lsb width)))
  ///
  (local (include-book "centaur/bitops/floor" :dir :system))
   
  (local (defthm floor-monotonic-inst
           (implies (and (posp width) (posp y) (natp lsb))
                    (<= (floor lsb y) (floor (+ -1 lsb width) y)))
           :hints (("goal" :use ((:instance bitops::floor-monotonic-arg1
                                  (a1 lsb) (a2 (+ -1 lsb width)) (b y)))))
           :rule-classes :linear))

  (local (defthm greater-than-nat-implies-nonnil
           (implies (and (< x y)
                         (natp x))
                    y)
           :rule-classes :forward-chaining))

  (local (defthm vl-printedtree-fix-of-cons
           (equal (vl-printedtree-fix (cons a b))
                  (cons (vl-printedtree-fix a)
                        (vl-printedtree-fix b)))
           :hints(("Goal" :in-theory (enable vl-printedtree-fix)))))

  (local (defthm vl-printedtree-p-of-cons
           (implies (and (vl-printedtree-p x)
                         (vl-printedtree-p y))
                    (vl-printedtree-p (cons x y)))
           :hints(("Goal" :in-theory (enable vl-printedtree-p)))))

  ;; (local (fty::deffixcong vl-printedtree-equiv vl-printedlist-equiv (cons a b) a
  ;;          :hints(("Goal" :expand ((vl-printedlist-fix a))))))

  (local (defthm vl-printedtree-p-when-stringp
           (implies (stringp x)
                    (vl-printedtree-p x))
           :hints(("Goal" :in-theory (enable vl-printedtree-p)))))
  
  (local (defthm x0
           (implies (mv-nth 1 (vl-dimension-size x))
                    (and (equal (vl-dimension-kind x) :range)
                         (vl-range-resolved-p (vl-dimension->range x))))
           :hints(("Goal" :in-theory (enable vl-dimension-size)))))

  (verify-guards sv-range-to-vl-chunks-datatype
    :hints (("goal" :do-not-induct t)
            (and stable-under-simplificationp
                 '(:expand ((vl-dimensionlist-total-size dims)
                            (vl-dimensionlist-resolved-p dims))))))

  (fty::deffixcong str::printtree-equiv equal (vl-printedlist->chars x acc) x
    :hints(("Goal" :in-theory (e/d (vl-printedlist->chars)
                                   (vl-printedlist-p-when-string-listp
                                    vl-printedlist-p-when-character-listp))
            :induct t
            :expand ((vl-printedlist-fix x)))))

  (fty::deffixcong str::printtree-equiv equal (vl-printedlist->string x) x
    :hints(("Goal" :in-theory (enable vl-printedlist->string))))

  (deffixequiv-mutual sv-range-to-vl-chunks-datatype))
    
                       
#!vl
(define sv-rangelist-to-vl-chunks ((x sv::rangelist-p)
                                   (type vl-datatype-p)
                                   (size)
                                   (name vl-printedtree-p))
  :guard (and (vl-datatype-resolved-p type)
              (equal size (vl-datatype-size-noerr type))
              (posp size))
  :returns (res string-listp)
  (b* (((when (atom x)) nil)
       ((sv::range x1) (car x))
       (size (mbe :logic (vl-datatype-size-noerr type) :exec size))
       (first (sv-range-to-vl-chunks-datatype type name x1.lsb
                                              (or x1.width size))))
    (append first
            (sv-rangelist-to-vl-chunks (cdr x) type size name))))



;; (define sv-range-to-vl-range ((svwire wire-p)
;;                               (x range-p))
;;   :returns (range vl::vl-maybe-range-p)
;;   (b* (((wire svwire))
;;        ((range x))
;;        ((unless (< x.lsb svwire.width))
;;         ;; totally out of bounds
;;         (cw "In ~x0, out of bounds range for wire ~x1: range ~x2, declared width ~x3 low-idx ~x4~%"
;;             __function__ svwire.name x svwire.width svwire.low-idx))
;;        ((when svwire.revp)
;;         (b* ((wire-lsb (+ -1 svwire.width svwire.low-idx))
;;              (wire-msb svwire.low-idx)
;;              (range-lsb (- wire-lsb x.lsb))
;;              (range-msb (if x.width
;;                             (max wire-msb (- range-lsb (+ -1 x.width)))
;;                           wire-msb)))
;;           (vl::make-vl-range :msb (vl::vl-make-index range-msb)
;;                              :lsb (vl::vl-make-index range-lsb))))
;;        (wire-lsb svwire.low-idx)
;;        (wire-msb (+ -1 svwire.width wire-lsb))
;;        (range-lsb (+ wire-lsb x.lsb))
;;        (range-msb (if x.width
;;                       (min wire-msb (+ range-lsb (+ -1 x.width)))
;;                     wire-msb)))
;;     (vl::make-vl-range :msb (vl::vl-make-index range-msb)
;;                              :lsb (vl::vl-make-index range-lsb)))
;;   ///
;;   (defret resolvedp-of-sv-range-to-vl-range
;;     (vl::vl-maybe-range-resolved-p range)
;;     :hints(("Goal" :in-theory (enable vl::vl-maybe-range-resolved-p
;;                                       vl::vl-range-resolved-p)))))

;; (define sv-rangelist-to-vl-msg-aux ((svwire wire-p)
;;                                     (x rangelist-p)
;;                                     (prevp))
;;   :returns (mv (msg (iff (vl::vl-msg-p msg) msg))
;;                (entries natp :rule-classes :type-prescription))
;;   :verify-guards nil
;;   (b* (((when (atom x)) (mv nil 0))
;;        (range1 (sv-range-to-vl-range svwire (car x)))
;;        ((mv rest rest-entries) (sv-rangelist-to-vl-msg-aux svwire (cdr x) (or prevp range1)))
;;        ((when (and range1 rest))
;;         (b* ((str (if (eql rest-entries 1)
;;                       (if prevp
;;                           "~a0, and ~@1" ;; Oxford comma
;;                         "~a0 and ~@1")
;;                     "~a0, ~@1"))
;;              (entries (+ 1 rest-entries)))
;;           (mv (vl::vl-msg str (list range1 rest))
;;               entries)))
;;        ((when range1)
;;         (mv (vl::vl-msg "~a0" (list range1)) 1))
;;        ((when rest) (mv rest rest-entries)))
;;     (mv nil 0))
;;   ///
;;   (defret sv-rangelist-to-vl-msg-aux-entries-posp
;;     (iff msg (posp entries)))

;;   (verify-guards sv-rangelist-to-vl-msg-aux)

;;   (local (in-theory (disable (:d sv-rangelist-to-vl-msg-aux)))))

#!vl
(define stringlist-to-vl-msg-more-than-2 ((x string-listp))
  :guard (consp x)
  :returns (msg vl-msg-p)
  (if (atom (cdr x))
      (vl-msg "and ~s0" (list (string-fix (car x))))
    (vl-msg "~s0, ~@1" (list (string-fix (car x))
                             (stringlist-to-vl-msg-more-than-2 (cdr x))))))

#!vl
(define sv-rangelist-to-vl-msg ((x sv::rangelist-p)
                                (type vl-datatype-p)
                                (size)
                                (name vl-printedtree-p))
  :returns (msg (iff (vl-msg-p msg) msg))
  :guard (and (vl-datatype-resolved-p type)
              (equal size (vl-datatype-size-noerr type))
              (posp size))
  :prepwork ((local (defthm vl-msg-p-car-of-string-list
                      (implies (and (string-listp x)
                                    (consp x))
                               (and (car x)
                                    (vl-msg-p (car x))))
                      :hints(("Goal" :in-theory (enable vl-msg-p)))))
             (local (defthm string-listp-of-rev
                      (implies (string-listp x)
                               (string-listp (rev x))))))
  (b* ((pieces (rev (sv-rangelist-to-vl-chunks x type size name)))
       (summary (summarize-parts pieces))
       ((when (atom summary)) nil)
       ((when (atom (cdr summary))) (car summary))
       ((when (atom (cddr summary)))
        (vl-msg "~s0 and ~s1" (list (car summary) (cadr summary)))))
    (stringlist-to-vl-msg-more-than-2 summary)))






(defmacro vl::warn-if (cond &rest args)
  `(if ,cond
       (vl::warn . ,args)
     vl::warnings))

#!vl
(define vl-scopestack-path-msg ((ss vl-scopestack-p))
  :measure (vl-scopestack-count ss)
  :returns (msg vl-msg-p)
  (vl-scopestack-case ss
    :null ":null"
    :global "$root"
    :local (b* ((id (vl-scope->id ss.top)))
             (if id
                 (vl-msg "~@0.~s1"
                         (list (vl-scopestack-path-msg ss.super)
                               (if (stringp id) id (str::intstr id))))
               (vl-msg "~@0.<unnamed-~x1>"
                       (list (vl-scopestack-path-msg ss.super)
                             (tag ss.top)))))))
                             



(local (defthm <<-negation-transitive
         (implies (and (not (<< x y))
                       (not (<< y z)))
                  (not (<< x z)))
         :hints ('(:cases ((equal x y)))
                 '(:cases ((equal y z))))))
(local (defthm <<-negation-transitive2
         (implies (and (not (<< y z))
                       (not (<< x y)))
                  (not (<< x z)))
         :hints ('(:cases ((equal x y)))
                 '(:cases ((equal y z))))))

(define path< ((x path-p) (y path-p))
  :measure (path-count x)
  (path-case x
    :wire (path-case y
            :wire (<< x.name y.name)
            :scope t)
    :scope (path-case y
             :wire nil
             :scope (or (<< x.namespace y.namespace)
                        (and (equal x.namespace y.namespace)
                             (path< x.subpath y.subpath)))))
  ///
  (defthm path<-irrefl
    (not (path< x x)))
  (defthm path<-anticommutative
    (implies (path< x y)
             (not (path< y x))))
  (defthm path<-transitive
    (implies (and (path< x y)
                  (path< y z))
             (path< x z)))
  
  (defthm path<=-transitive
    (implies (and (not (path< x y))
                  (not (path< y z)))
             (not (path< x z))))

  (defthm path<-trichotomy
    (implies (and (not (path< x y)) (not (equal (path-fix x) (path-fix  y))))
             (path< y x))
    :hints (("goal" :induct t)
            (and stable-under-simplificationp
                 '(:in-theory (e/d (path-fix-when-wire
                                    path-fix-when-scope)
                                   (path-scope-of-fields
                                    path-wire-of-fields)))))))
(fty::deflist addresslist :elt-type address :true-listp t)
(local (fty::deflist pathlist :elt-type path :true-listp t))

(acl2::defsort pathlist-sort (x)
  :comparablep path-p
  :comparable-listp pathlist-p
  :true-listp t
  :compare< path<)


(local (in-theory (disable len acl2-count)))

(fty::defmap name-alist :key-type name :true-listp t)

(deftypes scopetree
  (defprod scopetree
    ((leaves name-alist)
     (subscopes scopetree-alist))
    :measure (acl2::two-nats-measure (acl2-count x) 1)
    :layout :tree)
  (fty::defmap scopetree-alist :key-type name :val-type scopetree :true-listp t
    :measure (acl2::two-nats-measure (acl2-count x) 0)))


(fty::defalist path-alist :key-type path)
(fty::defalist address-alist :key-type address)




;; (local (defthm acl2-count-of-append
;;          (<= (acl2-count (append x y)) (+ (acl2-count x) (acl2-count y)))
;;          :hints(("Goal" :in-theory (enable append acl2-count)))
;;          :rule-classes :linear))

;; (local (defthm acl2-count-of-rev
;;          (<= (acl2-count (rev x)) (acl2-count x))
;;          :hints(("Goal" :in-theory (enable rev acl2-count)))
;;          :rule-classes :linear))

(define path-alist-count ((x path-alist-p))
  :returns (count natp :rule-classes :type-prescription)
  :measure (len x)
  :hints(("Goal" :in-theory (enable len)))
  (if (atom x)
      0
    (if (mbt (consp (car x)))
        (+ (path-count (caar x))
           (path-alist-count (cdr x)))
      (path-alist-count (cdr x))))
  ///
  (defthm path-alist-count-of-append
    (equal (path-alist-count (append x y))
           (+ (path-alist-count x) (path-alist-count y)))
    :hints(("Goal" :in-theory (enable append path-alist-fix) :induct (path-alist-fix x)
            :expand ((:free (a b) (path-alist-count (cons a b)))))))

  (defthm path-alist-count-of-rev
    (equal (path-alist-count (rev x))
           (path-alist-count x)))

  (fty::deffixequiv path-alist-count :hints(("Goal" :in-theory (enable path-alist-fix
                                                                       path-alist-count)))))
  

(define path-alist-split-wires ((x path-alist-p) (acc name-alist-p))
  :measure (len x)
  :hints(("Goal" :in-theory (enable len)))
  :returns (mv (wires name-alist-p) (rest path-alist-p))
  (b* (((when (atom x)) (mv (rev (name-alist-fix acc)) nil))
       ((unless (mbt (consp (car x))))
        (path-alist-split-wires (cdr x) acc))
       (x1 (path-fix (caar x))))
    (path-case x1
      :wire (path-alist-split-wires (cdr x) (cons (cons x1.name (cdar x)) acc))
      :scope (mv (rev (name-alist-fix acc)) (path-alist-fix x))))
  ///
  (defret path-alist-count-of-path-alist-split-wires
    (<= (path-alist-count rest) (path-alist-count x))
    :hints (("goal" :induct <call>
             :expand (<call>
                      (path-alist-count x)
                      (:free (a b) (path-alist-count (cons a b))))))
    :rule-classes :linear)

  (local (in-theory (enable path-alist-fix))))

(define path-alist-split-namespace-aux ((namespace name-p)
                                       (x path-alist-p)
                                       (acc path-alist-p))
  :returns (mv (namespace-paths path-alist-p)
               (rest path-alist-p))
  :hints(("Goal" :in-theory (enable len)))
  :measure (len x)
  (b* (((when (atom x))
        (mv (rev (path-alist-fix acc)) nil))
       ((unless (mbt (consp (car x))))
        (path-alist-split-namespace-aux namespace (cdr x) acc))
       (x1 (path-fix (caar x))))
    (path-case x1
      :wire (mv (rev (path-alist-fix acc)) (path-alist-fix x))
      :scope (if (equal x1.namespace (name-fix namespace))
                 (path-alist-split-namespace-aux namespace (cdr x) (cons (cons x1.subpath (cdar x)) acc))
               (mv (rev (path-alist-fix acc)) (path-alist-fix x)))))
  ///
  (defret path-alist-count-of-path-alist-split-namespace-aux-first
    (<= (path-alist-count namespace-paths) (+ (path-alist-count x) (path-alist-count acc)))
    :hints (("goal" :induct <call>
             :expand (<call>
                      (:free (a b) (path-alist-count (cons a b))))))
    :rule-classes :linear)

  (defret path-alist-count-of-path-alist-split-namespace-aux-first-strong
    (implies (< (len (path-alist-fix acc)) (len namespace-paths))
             (< (path-alist-count namespace-paths) (+ (path-alist-count x) (path-alist-count acc))))
    :hints (("goal" :induct <call>
             :expand (<call>
                      (:free (a b) (path-alist-count (cons a b))))))
    :rule-classes :linear)

  (defret path-alist-count-of-path-alist-split-namespace-aux-rest
    (<= (path-alist-count rest) (path-alist-count x))
    :hints (("goal" :induct <call>
             :expand (<call>
                      (path-alist-count x))))
    :rule-classes :linear)

  (defret path-alist-count-of-path-alist-split-namespace-aux-rest-strong
    (implies (< (len (path-alist-fix acc)) (len namespace-paths))
             (< (path-alist-count rest) (path-alist-count x)))
    :hints (("goal" :induct <call>
             :expand (<call>
                      (path-alist-count x))))
    :rule-classes :linear)

  (defret path-alist-split-namespace-aux-acc-len-nondecr
    (<= (len (path-alist-fix acc)) (len namespace-paths))
    :rule-classes :linear)

  (defret path-alist-split-namespace-aux-acc-len-incr
    (implies (b* ((x (path-alist-fix x))
                  (x1 (caar x)))
               (path-case x1
                 :wire nil
                 :scope (equal namespace x1.namespace)))
             (< (len (path-alist-fix acc)) (len namespace-paths)))
    :hints(("Goal" :in-theory (enable path-alist-fix)))
    :rule-classes :linear)

  (local (in-theory (enable path-alist-fix)))
  )

(define path-alist-split-namespace ((x path-alist-p))
  :returns (mv (namespace (implies namespace (name-p namespace)))
               (namespace-paths path-alist-p)
               (rest path-alist-p))
  (b* ((x (path-alist-fix x))
       ((when (atom x)) (mv nil nil nil))
       (x1 (caar x)))
    (path-case x1
      :wire (mv nil nil x)
      :scope (b* (((mv namespace-paths rest) (path-alist-split-namespace-aux x1.namespace x nil)))
               (mv x1.namespace namespace-paths rest))))
  ///
  (defret path-alist-count-of-path-alist-split-namespace-first
    (<= (path-alist-count namespace-paths) (path-alist-count x))
    :rule-classes :linear)

  (defret path-alist-count-of-path-alist-split-namespace-first-strong
    (implies namespace
             (< (path-alist-count namespace-paths) (path-alist-count x)))
    :rule-classes :linear)

  (defret path-alist-count-of-path-alist-split-namespace-rest
    (<= (path-alist-count rest) (path-alist-count x))
    :rule-classes :linear)

  (defret path-alist-count-of-path-alist-split-namespace-rest-strong
    (implies namespace
             (< (path-alist-count rest) (path-alist-count x)))
    :rule-classes :linear))
 


(defines path-alist-to-scopetree
  (define path-alist-to-scopetree ((x path-alist-p))
    :measure (acl2::two-nats-measure (path-alist-count x) 1)
    :returns (scopetree scopetree-p)
    :verify-guards nil
    (b* (((mv leaves rest) (path-alist-split-wires x nil))
         (subscopes (path-alist-to-scopetree-namespaces rest)))
      (make-scopetree :leaves leaves :subscopes subscopes)))
  (define path-alist-to-scopetree-namespaces ((x path-alist-p))
    :measure (acl2::two-nats-measure (path-alist-count x) 0)
    :returns (alist scopetree-alist-p)
    (b* (((mv namespace first rest) (path-alist-split-namespace x))
         ((unless namespace) nil))
      (cons (cons namespace (path-alist-to-scopetree first))
            (path-alist-to-scopetree-namespaces rest))))
  ///
  (verify-guards path-alist-to-scopetree)
  (fty::deffixequiv-mutual path-alist-to-scopetree))

(define path-alist-to-scopetree-top ((x path-alist-p))
  :enabled t
  (path-alist-to-scopetree x))



(defprojection addresslist->paths ((x addresslist-p))
  :returns (paths pathlist-p)
  (address->path x))    
  

#!vl
(define nest-hier-prefix ((prev-prefix stringp)
                          (new sv::name-p))
  :returns (new-prefix maybe-stringp)
  (b* ((new (sv::name-fix new))
       (new-string (cond ((stringp new) new)
                         ((integerp new) (cat "[" (str::intstr new) "]"))
                         (t nil)))
       ((unless new-string)
        (cw "In ~x0: new level of hierarchy didn't have a good name: ~x1 (prev: ~s2)"
            __function__ new (string-fix prev-prefix)))
       ((when (equal (string-fix prev-prefix) "")) new-string)
       ((when (integerp new)) (cat prev-prefix new-string)))
    (cat prev-prefix "." new-string))
  ///
  (defret nest-hier-prefix-when-stringp
    (implies (stringp (sv::name-fix new)) (stringp new-prefix))
    :rule-classes (:rewrite (:type-prescription :typed-term new-prefix))))


(define item-use/set-warnings ((item vl::vl-scopeitem-p)
                               (ss vl::vl-scopestack-p)
                               (hier-prefix stringp)
                               (base-name stringp)
                               (uses rangelist-p)
                               (sets rangelist-p)
                               (port-dir vl::vl-maybe-direction-p)
                               (instance-scope-p))
  :guard (and (proper-rangelist-p uses)
              (proper-rangelist-p sets))
  :returns (warnings vl::vl-warninglist-p)
  :prepwork ((local (defthm vl-printedtree-p-when-stringp
                      (implies (stringp x)
                               (vl::vl-printedtree-p x))
                      :hints(("Goal" :in-theory (enable vl::vl-printedtree-p vl::vl-printed-p))))))
  (b* ((port-dir (vl::vl-maybe-direction-fix port-dir))
       (hier-prefix (vl::string-fix hier-prefix))
       (base-name (vl::string-fix base-name))
       (var-desc (if port-dir
                     (b* ((port-desc (vl::vmsg "~s0 port ~w1"
                                               (case port-dir
                                                 (:vl-inout "Inout")
                                                 (:vl-input "Input")
                                                 (t "Output"))
                                               base-name)))
                       (if instance-scope-p
                           (vl::vmsg "~@0 of instance ~s1" port-desc hier-prefix)
                         port-desc))
                   (if (equal hier-prefix "")
                       (vl::vmsg "Variable ~w0" base-name)
                     (vl::vmsg "Variable ~s0.~w1" hier-prefix base-name))))
       (item (vl::vl-scopeitem-fix item))
       ((unless (eq (tag item) :vl-vardecl))
        (cw "In ~x0, item passed in as ~s1 was not a variable declaration; tag: ~x2~%"
            __function__ base-name (tag item))
        nil)
       ((vl::vl-vardecl item))
       (vl::warnings nil)
       (ss-path (vl::vl-scopestack-path-msg ss))
       ((when (and (atom uses)
                   (atom sets)
                   (not port-dir)))
        (vl::warn :type :sv-use-set-spurious
                  :msg "~@0 is never used or set anywhere. (~@1)"
                  :args (list var-desc ss-path item)))
       ((when (eq port-dir :vl-inout))
        ;; Should we even worry about inout ports?
        (vl::warn-if (and (atom uses)
                          (atom sets))
                     :type :sv-use-set-spurious-inout
                     :msg "~@0 is never used or set anywhere. (~@1)"
                     :args (list var-desc ss-path item)))
       ((when (eq port-dir :vl-input))
        ;; Only warn if it's never used.
        (vl::warn-if (atom uses)
                     :type :sv-use-set-unused-input
                     :msg "~@0 is never used. (~@1)"
                     :args (list var-desc ss-path item)))

       ((when (and (eq port-dir :vl-output)
                   (atom sets)))
        (vl::warn :type :sv-use-set-unset-output
                         :msg "~@0 is never set. (~@1)"
                         :args (list var-desc ss-path item)))
       ;; From here down we need the datatype to be OK in order to produce
       ;; reasonable warnings.
       (size (and (vl::vl-datatype-resolved-p item.type)
                  (vl::vl-datatype-size-noerr item.type)))
       ((unless (posp size)) vl::warnings)

       (unsets (rangelist-inverse-limited size sets))
       ((when (eq port-dir :vl-output))
        (vl::warn-if (consp unsets)
                     :type :sv-use-set-partly-unset-output
                     :msg "~@0 has parts that are never set: ~@1. (~@2)"
                     :args (list var-desc
                                 (vl::sv-rangelist-to-vl-msg unsets item.type size base-name)
                                 ss-path item)))

       ;; Now we've taken care of all ports.  Tackle totally unused and totally unsets wires now.
       ((when (atom uses))
        (vl::warn-if
         ;; note: it's normal in certain contexts to have supply wires sitting around that are not used.
         (not (or (eq item.nettype :vl-supply0)
                  (eq item.nettype :vl-supply1)))
         :type :sv-use-set-unused
         ;; BOZO Do we need to display what parts are set?
         :msg "~@0 is never used but ~s1. (~@2)"
         :args (list var-desc
                     (if (consp unsets)
                         "has parts that are set"
                       "is set")
                     ss-path
                     item)))

       (unuseds (rangelist-inverse-limited size uses))
       ((when (atom sets))
        (vl::warn :type :sv-use-set-unset
                  ;; BOZO Do we need to display what parts are used?
                  :msg "~@0 is never set but ~s1. (~@2)"
                  :args (list var-desc
                              (if (consp unuseds)
                                  "has parts that are used"
                                "is used")
                              ss-path
                              item)))

       ;; Now we've taken care of all port types and all completely unused or unset wires.
       (used-but-unsets (rangelist-truncate (rangelist-difference uses sets) size))
       (set-but-unuseds (rangelist-truncate (rangelist-difference sets uses) size))
       (unused-and-unsets (rangelist-truncate (rangelist-difference unuseds sets) size))

       (vl::warnings (vl::warn-if (consp used-but-unsets)
                                  :type :sv-use-set-partly-unset
                                  :msg "~@0 has parts that are used but not set: ~@1. (~@2)"
                                  :args (list var-desc
                                              (vl::sv-rangelist-to-vl-msg used-but-unsets item.type size base-name)
                                              ss-path item)))
       (vl::warnings (vl::warn-if (consp set-but-unuseds)
                                  :type :sv-use-set-partly-unused
                                  :msg "~@0 has parts that are set but never used: ~@1. (~@2)"
                                  :args (list var-desc
                                              (vl::sv-rangelist-to-vl-msg set-but-unuseds item.type size base-name)
                                              ss-path item)))

       ;; should we even bother with this one?
       (vl::warnings (vl::warn-if (consp unused-and-unsets)
                                 :type :sv-use-set-partly-spurious
                                 :msg "~@0 has parts that are never set or used: ~@1. (~@2)"
                                 :args (list var-desc
                                             (vl::sv-rangelist-to-vl-msg unused-and-unsets item.type size base-name)
                                             ss-path item))))
    vl::warnings))


#!vl
(define scope-item-use/set-warnings ((name sv::name-p)
                                     (key "an address, but we don't care")
                                     (ss vl-scopestack-p)
                                     (hier-prefix stringp)
                                     (uses sv::rangemap-p)
                                     (sets sv::rangemap-p)
                                     (ports vl-portdecl-alist-p)
                                     (instance-scope-p)
                                     (warnings vl-warninglist-p))
  :guard (and (sv::proper-rangemap-p uses)
              (sv::proper-rangemap-p sets))
  :returns (new-warnings vl-warninglist-p)
  (b* ((warnings (vl-warninglist-fix warnings))
       (name (sv::name-fix name))
       ((unless (stringp name))
        (cw "In ~x0, unexpected non-string name: ~x1~%" __function__ name)
        warnings)
       (item (vl-scopestack-find-item name ss))
       ((unless item)
        (cw "In ~x0, didn't find item in scope: ~x1~%" __function__ name)
        warnings)
       (useds-pair (hons-get key (sv::rangemap-fix uses)))
       (sets-pair (hons-get key (sv::rangemap-fix sets)))
       ;; ((unless (and useds-pair sets-pair))
       ;;  (cw "In ~x0, didn't find used/set info for ~x1 (address: ~x2)~%" __function__ name key)
       ;;  ;; (break$)
       ;;  warnings)
       (port (cdr (hons-get name (vl-portdecl-alist-fix ports))))
       (dir (and port (vl-portdecl->dir port))))
    (append-without-guard
     (sv::item-use/set-warnings item ss
                                hier-prefix name (cdr useds-pair) (cdr sets-pair) dir instance-scope-p)
     warnings)))
       

#!vl
(define scope-leaves-use/set-warnings ((x sv::name-alist-p)
                                      (ss vl-scopestack-p)
                                      (hier-prefix stringp)
                                      (uses sv::rangemap-p)
                                      (sets sv::rangemap-p)
                                      (ports vl-portdecl-alist-p)
                                      (instance-scope-p)
                                      (warnings vl-warninglist-p))
  :guard (and (sv::proper-rangemap-p uses)
              (sv::proper-rangemap-p sets))
  :returns (new-warnings vl-warninglist-p)
  :measure (len x)
  (b* (((When (atom x))
        (vl-warninglist-fix warnings))
       ((unless (mbt (And (consp (car x)) (sv::name-p (caar x)))))
        (scope-leaves-use/set-warnings (cdr x) ss hier-prefix uses sets ports instance-scope-p warnings))
       (warnings (scope-item-use/set-warnings
                  (caar x) (cdar x)
                   ss hier-prefix uses sets ports instance-scope-p warnings)))
    (scope-leaves-use/set-warnings (cdr x) ss hier-prefix uses sets ports instance-scope-p warnings))
  ///
  (local (in-theory (enable sv::name-alist-fix))))
                                              

;; (local (defthm scopetree-alist-count-of-cdr-strong
;;          (implies (consp x)
;;                   (< (scopetree-alist-count (cdr x))
;;                      (scopetree-alist-count x)))
;;          :hints(("Goal" :in-theory (enable scopetree-alist-count)))
;;          :rule-classes :linear))

#!vl
(define vl-scopedef-portdecls ((x vl-scopedef-p))
  :returns (portdecls vl-portdecllist-p)
  (b* ((x (vl-scopedef-fix x)))
    (case (tag x)
      (:vl-module (vl-module->portdecls x))
      (:vl-interface (vl-interface->portdecls x))
      (t nil))))
  
#!vl
(defines scopetree-collect-use/set-warnings
  :prepwork ((local (defthm vl-scope-p-when-vl-module-p-strong
                      (implies (or (vl-module-p x)
                                   (vl-interface-p x))
                               (vl-scope-p x)))))
  (define scopetree-collect-use/set-warnings ((x sv::scopetree-p)
                                              (ss vl-scopestack-p)
                                              (hier-prefix stringp)
                                              (uses sv::rangemap-p)
                                              (sets sv::rangemap-p)
                                              (ports vl-portdecl-alist-p)
                                              (instance-scope-p)
                                              (warnings vl-warninglist-p))
    :measure (list (sv::scopetree-count x) 0)
    :well-founded-relation acl2::nat-list-<
    :guard (and (sv::proper-rangemap-p uses)
                (sv::proper-rangemap-p sets))
    :returns (warnings vl-warninglist-p)
    :verify-guards nil
    :measure-debug t
    (b* (((sv::scopetree x))
         (warnings (scope-leaves-use/set-warnings x.leaves ss hier-prefix uses sets ports instance-scope-p warnings)))
      (scopetree-collect-use/set-warnings-scopes
       x.subscopes ss hier-prefix uses sets warnings)))

  (define scopetree-collect-use/set-warnings-scopes ((x sv::scopetree-alist-p)
                                                     (ss vl-scopestack-p)
                                                     (hier-prefix stringp)
                                                     (uses sv::rangemap-p)
                                                     (sets sv::rangemap-p)
                                                     (warnings vl-warninglist-p))
    :measure (list (sv::scopetree-alist-count x) 0)
    :guard (and (sv::proper-rangemap-p uses)
                (sv::proper-rangemap-p sets))
    :returns (warnings vl-warninglist-p)
    (b* ((x (sv::scopetree-alist-fix x))
         ((when (atom x)) (vl-warninglist-fix warnings))
         (name (caar x))
         ((unless (stringp name))
          (cw "Expected only strings for hierarchy names here: ~s0, ~x1~%" hier-prefix name)
          (scopetree-collect-use/set-warnings-scopes
           (cdr x) ss hier-prefix uses sets warnings))
         (new-prefix (nest-hier-prefix hier-prefix name))
         ((unless new-prefix)
          (scopetree-collect-use/set-warnings-scopes
           (cdr x) ss hier-prefix uses sets warnings))

         ((mv item item-ss) (vl-scopestack-find-item/ss name ss))
         ((unless item)
          (cw "in ~x0, didn't find a scope item for ~x1 (under scope ~@2)~%"
              __function__ name (vl-scopestack-path-msg ss)))
         ((when (eq (tag item) :vl-genbegin))
          (b* ((genblob (vl::vl-sort-genelements (vl::vl-genblock->elems (vl::vl-genbegin->block item))
                                                        :scopetype :vl-genblock
                                                        :id name))
               (next-ss (vl::vl-scopestack-push genblob item-ss))
               (warnings (scopetree-collect-use/set-warnings
                          (cdar x) next-ss new-prefix uses sets nil nil warnings)))
            (scopetree-collect-use/set-warnings-scopes (cdr x) ss hier-prefix uses sets warnings)))

         ((when (eq (tag item) :vl-genarray))
          (b* ((warnings (scopetree-collect-use/set-warnings-genarray
                          (cdar x)
                          (vl::vl-genarray->blocks item)
                          (vl::vl-scopestack-push
                           (vl::vl-sort-genelements nil :scopetype :vl-genarray
                                                    :id name)
                           item-ss)
                          new-prefix uses sets warnings)))
            (scopetree-collect-use/set-warnings-scopes (cdr x) ss hier-prefix uses sets warnings)))
         ((when (eq (tag item) :vl-modinst))
          (b* (((vl-modinst item))
               (dims    (and item.range (list (vl-range->dimension item.range))))
               ((mv mod mod-ss) (vl-scopestack-find-definition/ss item.modname item-ss))
               ((unless (and mod
                             (or (eq (tag mod) :vl-module)
                                 (eq (tag mod) :vl-interface))))
                (cw "in ~x0, instance ~s1, expected mod name ~s2 to point to a module or interface~%"
                    __function__ name item.modname)
                (scopetree-collect-use/set-warnings-scopes (cdr x) ss hier-prefix uses sets warnings))
               (next-ss (vl-scopestack-push mod mod-ss))
               (portalist (vl-portdecllist-alist (vl-scopedef-portdecls mod) nil))
               (warnings (with-fast-alist portalist
                           (if dims
                               (scopetree-collect-use/set-warnings-instarray-dims
                                (cdar x) 1 next-ss new-prefix uses sets portalist warnings)
                             (scopetree-collect-use/set-warnings
                              (cdar x) next-ss new-prefix uses sets portalist t warnings)))))
            (scopetree-collect-use/set-warnings-scopes (cdr x) ss hier-prefix uses sets warnings)))
         ((when (eq (tag item) :vl-interfaceport))
          (b* (((vl-interfaceport item))
               ((mv iface iface-ss) (vl-scopestack-find-definition/ss item.ifname item-ss))
               ((unless (and iface
                             (eq (tag iface) :vl-interface)))
                (cw "in ~x0, instance ~s1, expected interface name ~s2 to point to an interface~%"
                    __function__ name item.ifname)
                (scopetree-collect-use/set-warnings-scopes (cdr x) ss hier-prefix uses sets warnings))
               (next-ss (vl-scopestack-push iface iface-ss))
               (portalist (vl-portdecllist-alist (vl-interface->portdecls iface) nil))
               (warnings (with-fast-alist portalist
                           (if item.udims
                               (scopetree-collect-use/set-warnings-instarray-dims
                                (cdar x) (len item.udims) next-ss new-prefix uses sets portalist warnings)
                             (scopetree-collect-use/set-warnings
                              (cdar x) next-ss new-prefix uses sets portalist t warnings)))))
            (scopetree-collect-use/set-warnings-scopes (cdr x) ss hier-prefix uses sets warnings))))

      (cw "In ~x0, unexpected kind of scope found for ~x1: ~x2. Contents: ~x3~%"
          __function__ name (tag item) (cdar x))
      ;; (break$)
      (scopetree-collect-use/set-warnings-scopes (cdr x) ss hier-prefix uses sets warnings)))

  (define scopetree-collect-use/set-warnings-genarray ((x sv::scopetree-p)
                                                       (blocks vl-genblocklist-p)
                                                       (ss vl-scopestack-p)
                                                       (hier-prefix stringp)
                                                       (uses sv::rangemap-p)
                                                       (sets sv::rangemap-p)
                                                       (warnings vl-warninglist-p))
    :measure (list (sv::scopetree-count x) 0)
    :guard (and (sv::proper-rangemap-p uses)
                (sv::proper-rangemap-p sets))
    :returns (warnings vl-warninglist-p)
    (b* (((sv::scopetree x))
         (- (and (consp x.leaves)
                 (cw "In ~x0: Didn't expect any leaf variables directly in a genarray -- ~x1~%"
                     __function__ x.leaves))))
      (scopetree-collect-use/set-warnings-genarray-scopes
       x.subscopes blocks ss hier-prefix uses sets warnings)))

  (define scopetree-collect-use/set-warnings-genarray-scopes ((x sv::scopetree-alist-p)
                                                              (blocks vl-genblocklist-p)
                                                              (ss vl-scopestack-p)
                                                              (hier-prefix stringp)
                                                              (uses sv::rangemap-p)
                                                              (sets sv::rangemap-p)
                                                              (warnings vl-warninglist-p))
    :measure (list (sv::scopetree-alist-count x) 0)
    :guard (and (sv::proper-rangemap-p uses)
                (sv::proper-rangemap-p sets))
    :returns (warnings vl-warninglist-p)

    (b* ((x (sv::scopetree-alist-fix x))
         ((when (atom x)) (vl-warninglist-fix warnings))
         (name (caar x))
         ((unless (integerp name))
          (cw "Expected only integers for hierarchy names here: ~s0, ~x1~%" hier-prefix name)
          (scopetree-collect-use/set-warnings-genarray-scopes
           (cdr x) blocks ss hier-prefix uses sets warnings))
         (new-prefix (nest-hier-prefix hier-prefix name))
         ((unless new-prefix)
          (scopetree-collect-use/set-warnings-genarray-scopes
           (cdr x) blocks ss hier-prefix uses sets warnings))
         
         (block (vl::vl-genblocklist-find-block name blocks))
         ((unless block)
          (cw "in ~x0, expected to find a genarray block for index ~x1, but didn't, under ~s2~%"
              __function__ name hier-prefix)
          (scopetree-collect-use/set-warnings-genarray-scopes
           (cdr x) blocks ss hier-prefix uses sets warnings))

         (block-scope (vl::vl-sort-genelements
                       (vl::vl-genblock->elems block)
                       :scopetype :vl-genarrayblock
                       :id name))
         (next-ss (vl-scopestack-push block-scope ss))
         (warnings (scopetree-collect-use/set-warnings
                    (cdar x) next-ss new-prefix uses sets nil nil warnings)))
      (scopetree-collect-use/set-warnings-genarray-scopes
       (cdr x) blocks ss hier-prefix uses sets warnings)))

  (define scopetree-collect-use/set-warnings-instarray-dims ((x sv::scopetree-p)
                                                             (ndims natp)
                                                             (ss vl-scopestack-p)
                                                             (hier-prefix stringp)
                                                             (uses sv::rangemap-p)
                                                             (sets sv::rangemap-p)
                                                             (ports vl-portdecl-alist-p)
                                                             (warnings vl-warninglist-p))
    :measure (list (sv::scopetree-count x) 1)
    :guard (and (sv::proper-rangemap-p uses)
                (sv::proper-rangemap-p sets))
    :returns (warnings vl-warninglist-p)
    (b* (((sv::scopetree x))
         ((when (zp ndims))
          (scopetree-collect-use/set-warnings x ss hier-prefix uses sets ports t warnings))
         (- (and (consp x.leaves)
                 (cw "In ~x0: Didn't expect any leaf variables directly in a instarray -- ~x1~%"
                     __function__ x.leaves))))
      (scopetree-collect-use/set-warnings-instarray-scopes
       x.subscopes (1- ndims) ss hier-prefix uses sets ports warnings)))

  (define scopetree-collect-use/set-warnings-instarray-scopes ((x sv::scopetree-alist-p)
                                                               (ndims natp)
                                                               (ss vl-scopestack-p)
                                                               (hier-prefix stringp)
                                                               (uses sv::rangemap-p)
                                                               (sets sv::rangemap-p)
                                                               (ports vl-portdecl-alist-p)
                                                               (warnings vl-warninglist-p))
    :measure (list (sv::scopetree-alist-count x) 0)
    :guard (and (sv::proper-rangemap-p uses)
                (sv::proper-rangemap-p sets))
    :returns (warnings vl-warninglist-p)

    (b* ((x (sv::scopetree-alist-fix x))
         ((when (atom x)) (vl-warninglist-fix warnings))
         (name (caar x))
         ((unless (integerp name))
          (cw "Expected only integers for hierarchy names here: ~s0, ~x1~%" hier-prefix name)
          (scopetree-collect-use/set-warnings-instarray-scopes
           (cdr x) ndims ss hier-prefix uses sets ports warnings))
         (new-prefix (nest-hier-prefix hier-prefix name))
         ((unless new-prefix)
          (scopetree-collect-use/set-warnings-instarray-scopes
           (cdr x) ndims ss hier-prefix uses sets ports warnings))
         (warnings (scopetree-collect-use/set-warnings-instarray-dims
                    (cdar x) ndims ss new-prefix uses sets ports warnings)))
      (scopetree-collect-use/set-warnings-instarray-scopes
       (cdr x) ndims ss hier-prefix uses sets ports warnings)))

  ///
  (verify-guards scopetree-collect-use/set-warnings)

  (local (in-theory (disable sv::scopetree-alist-p-when-not-consp
                             sv::rangemap-fix-when-rangemap-p
                             sv::rangemap-p-when-not-consp
                             default-car default-cdr
                             vl::nest-hier-prefix-when-stringp
                             vl::vl-warninglist-p-when-not-consp)))

  (local (make-event
          `(in-theory (disable . ,(getpropc 'scopetree-collect-use/set-warnings 'acl2::recursivep)))))
  (with-output :off (prove)
    (progn
      (fty::deffixequiv-mutual scopetree-collect-use/set-warnings :args (uses))
      (fty::deffixequiv-mutual scopetree-collect-use/set-warnings :args (sets))
      (fty::deffixequiv-mutual scopetree-collect-use/set-warnings :args (warnings))
      (fty::deffixequiv-mutual scopetree-collect-use/set-warnings :omit (uses sets warnings)))))
         
                                                       
         



(define address< ((x address-p)
                  (y address-p))
  (b* (((address x))
       ((address y))
       ((when (<< x.scope y.scope)) t)
       ((unless (equal x.scope y.scope)) nil)
       ((when (path< x.path y.path)) t)
       ((unless (equal x.path y.path)) nil))
    (<< x.index y.index))
  ///
  (defthm address<-irrefl
    (not (address< x x)))
  (defthm address<-anticommutative
    (implies (address< x y)
             (not (address< y x))))
  (defthm address<-transitive
    (implies (and (address< x y)
                  (address< y z))
             (address< x z)))

  (defthm address<=-transitive
    (implies (and (not (address< x y))
                  (not (address< y z)))
             (not (address< x z)))))



(acl2::defsort addresslist-sort (x)
  :comparablep address-p
  :comparable-listp addresslist-p
  :true-listp t
  :compare< address<)



(define addresslist-remove-uprefs ((x addresslist-p) (acc addresslist-p))
  :returns (new-x addresslist-p)
  (if (atom x)
      (rev (addresslist-fix acc))
    (addresslist-remove-uprefs
     (cdr x)
     (if (eql (address->scope (car x)) 0)
         (cons (address-fix (car x)) acc)
       acc))))
              
             
  
  
#!vl
(define vl-scopedef-is-scope ((x vl-scopedef-p))
  (case (tag (vl-scopedef-fix x))
    ((:vl-module :vl-interface) t)
    (otherwise nil))
  ///
  (defthmd vl-scopedef-is-scope-implies
    (implies (and (vl-scopedef-is-scope x)
                  (vl-scopedef-p x))
             (vl-scope-p x))
    :hints (("goal" 
             :in-theory (e/d (vl-scope-p vl-scopedef-fix))))))



(define filter-portdecl-rangemap ((x rangemap-p)
                                  (alist)
                                  (acc rangemap-p))
  :returns (new-x rangemap-p)
  :measure (len (rangemap-fix x))
  :hints(("Goal" :in-theory (enable len)))
  (b* ((x (rangemap-fix x))
       ((when (atom x)) (rev (rangemap-fix acc)))
       ((address x1) (caar x))
       ((when (or (not (eql 0 x1.scope)) ;; Leave in upward reference vars
                  (path-case x1.path
                    :wire (and (stringp x1.path.name)
                               (hons-get x1.path.name alist))
                    :scope nil)))
        (filter-portdecl-rangemap (cdr x) alist
                                  (cons (cons (address-fix x1)
                                              (rangelist-fix (cdar x)))
                                        (rangemap-fix acc)))))
    (filter-portdecl-rangemap (cdr x) alist acc)))


(define filter-portdecl-wires ((x wirelist-p)
                               (alist)
                               (acc wirelist-p))
  :returns (new-x wirelist-p)
  (b* (((when (atom x)) (rev (wirelist-fix acc)))
       ((wire x1) (car x))
       ((when (eq x1.name :self))
        ;; hack for interfaces -- we have aliases to the :self wire when the interface is instantiated.
        (filter-portdecl-wires
         (cdr x) alist (cons (wire-fix x1) (wirelist-fix acc))))
       ((when (and (stringp x1.name)
                   (hons-get x1.name alist)))
        (filter-portdecl-wires (cdr x) alist (cons (wire-fix x1) (wirelist-fix acc)))))
    (filter-portdecl-wires (cdr x) alist acc)))
                

(local (defthm addresslist-p-of-remove-adjacent-duplicates
         (implies (addresslist-p x)
                  (addresslist-p (acl2::remove-adjacent-duplicates x)))
         :hints(("Goal" :in-theory (enable acl2::remove-adjacent-duplicates)))))


(local (include-book "tools/trivial-ancestors-check" :dir :system))
(local (acl2::use-trivial-ancestors-check))


(local
 (defthm svarlist-addr-p-of-lhsarr-to-svexarr
   (implies (and (svarlist-addr-p (aliases-vars aliases))
                 (equal (len init) (len aliases)))
            (svarlist-addr-p (svexarr-vars (lhsarr-to-svexarr 0 aliases init))))
   :hints (("goal" :do-not-induct t
            :in-theory (disable vars-of-get-svex
                                ACL2::NATP-WHEN-GTE-0)))))

(defthm addresslist-p-alist-keys-of-rangemap
  (implies (rangemap-p x)
           (addresslist-p (alist-keys x)))
  :hints(("Goal" :in-theory (enable alist-keys))))



(local
 (defsection member-vars-of-svexlist-mask-alist
   (defthm member-vars-of-svex-args-apply-masks
     (implies (and (not (member v (svexlist-vars args)))
                   (not (member v (svexlist-vars (svex-mask-alist-keys mask-al)))))
              (not (member v (svexlist-vars (svex-mask-alist-keys
                                             (svex-args-apply-masks args masks mask-al))))))
     :hints(("Goal" :in-theory (enable svex-args-apply-masks))))

   (defthm member-vars-of-svexlist-compute-masks
     (implies (and (not (member v (svexlist-vars x)))
                   (not (member v (svexlist-vars (svex-mask-alist-keys mask-al)))))
              (not (member v (svexlist-vars (svex-mask-alist-keys
                                             (svexlist-compute-masks x mask-al))))))
     :hints(("Goal" :in-theory (enable svexlist-compute-masks))))

   (defthm member-vars-of-svexlist-mask-alist/toposort
     (implies (not (member v (svexlist-vars x)))
              (not (member v (svexlist-vars (svex-mask-alist-keys
                                             (mv-nth 0 (svexlist-mask-alist/toposort x)))))))
     :hints(("Goal" :in-theory (enable svexlist-mask-alist/toposort))))

   (defthm member-vars-of-svexlist-mask-alist
     (implies (not (member v (svexlist-vars x)))
              (not (member v (svexlist-vars (svex-mask-alist-keys
                                             (svexlist-mask-alist x))))))
     :hints(("Goal" :in-theory (e/d (svexlist-mask-alist)
                                    (svexlist-mask-alist/toposort-to-mask-alist)))))
     
     

     ))



(defthm path-alist-p-of-pairlis$
  (implies (pathlist-p paths)
           (path-alist-p (pairlis$ paths values)))
  :hints(("Goal" :in-theory (enable pairlis$))))


                
(define lhs-collect-addresses ((x lhs-p)
                           (addresses-acc address-alist-p))
  :guard (svarlist-addr-p (lhs-vars x))
  :guard-hints (("goal" :in-theory (enable lhs-vars lhatom-vars)))
  :returns (new-addresses address-alist-p)
  (b* ((addresses-acc (address-alist-fix addresses-acc))
       ((when (atom x))
        addresses-acc)
       ((lhrange x1) (car x))
       ((unless (lhatom-case x1.atom :var))
        (lhs-collect-addresses (cdr x) addresses-acc))
       ((lhatom-var x1) x1.atom)
       ((address addr) (svar->address x1.name))
       ((unless (and (eql addr.scope 0)
                     (not (hons-get addr addresses-acc))))
        (lhs-collect-addresses (cdr x) addresses-acc)))
    (lhs-collect-addresses
     (cdr x)
     (hons-acons addr t addresses-acc))))

(define aliases-collect-normed-addresses ((n natp)
                                          (aliases)
                                          (addresses-acc address-alist-p))
  :guard (and (<= n (aliass-length aliases))
              (svarlist-addr-p (aliases-vars aliases)))
  :measure (nfix (- (aliass-length aliases) (nfix n)))
  :returns (new-addresses address-alist-p)
  (b* (((when (mbe :logic (zp (- (aliass-length aliases) (nfix n)))
                   :exec (eql n (aliass-length aliases))))
        (address-alist-fix addresses-acc))
       (addresses-acc (lhs-collect-addresses (get-alias n aliases) addresses-acc)))
    (aliases-collect-normed-addresses (1+ (lnfix n)) aliases addresses-acc)))

(define sv-module-analyze-use-set ((name modname-p)
                                   (mod module-p)
                                   (vlmod vl::vl-scopedef-p)
                                   (modalist modalist-p)
                                   (submod-use rangemap-p)
                                   (submod-set rangemap-p)
                                   (ss vl::vl-scopestack-p))
  :guard (svarlist-addr-p (modalist-vars modalist))
  ;;:guard-debug t
  :guard-hints (("goal" :in-theory (enable vl::vl-scopedef-is-scope-implies
                                           modscope-okp
                                           modscope-local-bound
                                           modscope->modidx)))
  :prepwork ((local (include-book "std/lists/resize-list" :dir :system))
             (local (defret assigns-boundedp-of-svex-design-flatten-special
                      (b* ((bound (moddb-mod-totalwires
                                   (moddb-modname-get-index name new-moddb)
                                   new-moddb)))
                        (implies (equal name  (design->top x))
                                 (and (svarlist-boundedp (assigns-vars flat-assigns) bound)
                                      (svarlist-boundedp (constraintlist-vars flat-constraints) bound)
                                      (svarlist-boundedp (assigns-vars flat-fixups) bound)
                                      ;; (svarlist-boundedp (svar-map-vars res-delays) (len aliases))
                                      )))
                      :fn svex-design-flatten))
             (local (defthm addresslist-p-alist-keys-of-address-alist
                      (implies (address-alist-p x)
                               (addresslist-p (alist-keys x)))
                      :hints(("Goal" :in-theory (enable alist-keys))))))
  :returns (mv (use-set use-set-p)
               (warnings vl::vl-warninglist-p)
               (stub-mod module-p))
  (b* (((acl2::local-stobjs moddb aliases svexarr)
        (mv moddb aliases svexarr use-set warnings stub-mod))
       ((module mod) (module-fix mod))
       (name (modname-fix name))
       ((unless (stringp name))
        (mv moddb aliases svexarr (make-use-set) nil mod))
       (- (cw "SV-Use-Set: Checking ~s0...~%" name))
       ((mv err assigns & & moddb aliases)
        (svex-design-flatten (make-design :modalist modalist :top name)))
       ((when err)
        (cw "In ~x0, module ~x1, error in svex-design-flatten: ~@2~%"
            __function__ name err)
        (mv moddb aliases svexarr (make-use-set) nil mod))
       (vlmod (vl::vl-scopedef-fix vlmod))
       ((unless (vl::vl-scopedef-is-scope vlmod))
        (cw "In ~x0, ~x1 was not a module/interface but an ~x2~%"
            __function__ name (tag vlmod))
        (mv moddb aliases svexarr (make-use-set) nil mod))
       (ss (vl::vl-scopestack-push vlmod ss))
       
       (modidx (moddb-modname-get-index name moddb))
       ((unless modidx)
        (cw "In ~x0, ~x1 was not found in the moddb~%"
            __function__ name)
        (mv moddb aliases svexarr (make-use-set) nil mod))
       ((mv aliases &) (aliases-indexed->named aliases (make-modscope-top :modidx modidx) moddb))

       ;; recreating a chunk of svex-normalize-assigns because we want the
       ;; substituted assigns, which it doesn't return
       (svexarr (resize-svexs (aliass-length aliases) svexarr))
       (svexarr (cwtime (lhsarr-to-svexarr 0 aliases svexarr) :mintime 1))
       (norm-assigns (assigns-subst assigns aliases svexarr))
       (assigns-alist (netassigns->resolves (assigns->netassigns norm-assigns)))
       (assign-rhses (svex-alist-vals assigns-alist))
       ;; (delays (delay-svarlist->delays (svarlist-collect-delays (svexlist-collect-vars assign-rhses))))

       (assigns-sets (assigns-to-sets norm-assigns nil))

       ((mv assigns-uses warnings) (svex-mask-alist-to-rangemap 
                                    (svexlist-mask-alist assign-rhses)
                                    nil nil))
       ;; (- (cw "assigns-uses: ~x0~%" (rangemap-simplify assigns-uses nil))
       ;;    (cw "assigns-sets: ~x0~%" (rangemap-simplify assigns-sets nil)))

       (uses (rangemap-simplify (rangemap-norm submod-use modidx moddb aliases assigns-uses) nil))
       (sets (rangemap-simplify (rangemap-norm submod-set modidx moddb aliases assigns-sets) nil))

       (all-addresses (addresslist-sort (alist-keys
                                         (fast-alist-free
                                          (aliases-collect-normed-addresses 0 aliases nil)))))

       (path-alist (pairlis$ (addresslist->paths all-addresses) all-addresses))

       ;; BOZO. This scopetree won't include any spurious wires, because it is
       ;; defined by scanning the items that have scope info.
       (scopetree (path-alist-to-scopetree-top path-alist))
       (portdecl-alist (vl::vl-portdecllist-alist (vl::vl-scopedef-portdecls vlmod) nil))
       ((acl2::with-fast portdecl-alist))
       (warnings (vl::scopetree-collect-use/set-warnings
                  scopetree ss "" uses sets
                  portdecl-alist nil warnings))

       (use-sets (make-use-set
                  :uses (filter-portdecl-rangemap uses portdecl-alist nil)
                  :sets (filter-portdecl-rangemap sets portdecl-alist nil)))
       (stub-mod (make-module :wires (filter-portdecl-wires mod.wires portdecl-alist nil))))
    (clear-memoize-table 'svex->absindexed)
    (clear-memoize-table 'svex-named->indexed)
    (clear-memoize-table 'svex-subst-from-svexarr)
    (clear-memoize-table 'vl-scope->scopeinfo-aux)
    (fast-alist-free path-alist)
    (mv moddb aliases svexarr use-sets warnings stub-mod))
  ///
  (defret module-vars-of-sv-module-analyze-use-set
    (implies (and (svarlist-addr-p (modalist-vars modalist))
                  (svarlist-addr-p (module-vars mod)))
             (svarlist-addr-p (module-vars stub-mod)))))

       

       



       
       
         
  

;; Process SV modules depth-first/post-order according to the instantiation
;; hierarchy.  For each proper module (corresponding to a VL module/interface,
;; rather than a subscope), flatten its subscopes and analyze the module as a
;; whole, then stub it out (leaving just the variables of its ports) once
;; finished.
(defines sv-use-set-analyze-rec
  (define sv-use-set-analyze-rec ((name modname-p)
                                  (modalist modalist-p)
                                  (stubbed-modalist modalist-p)
                                  (use-set-acc use-set-summaries-p)
                                  (reportcard vl::vl-reportcard-p)
                                  (ss vl::vl-scopestack-p))
    :guard (and (modhier-loopfree-p name modalist)
                (svarlist-addr-p (modalist-vars modalist))
                (svarlist-addr-p (modalist-vars stubbed-modalist))
                (equal (alist-keys stubbed-modalist)
                       (alist-keys use-set-acc)))
    :measure (mod-meas (modname-fix name) modalist)
    :returns (mv (new-modalist-local modalist-p)
                 (new-modalist-all modalist-p)
                 (new-use-set-acc use-set-summaries-p)
                 (new-reportcard vl::vl-reportcard-p)
                 (submod-use rangemap-p)
                 (submod-set rangemap-p))
    :verify-guards nil
    (b* ((name (modname-fix name))
         (mod (modalist-lookup name modalist))
         ((unless (and mod
                       (mbt (modhier-loopfree-p name (modalist-fix modalist)))))
          (mv nil
              (modalist-fix stubbed-modalist)
              (use-set-summaries-fix use-set-acc)
              (vl::vl-reportcard-fix reportcard)
              nil nil))
         ((module mod))
         (vlmod (and (stringp name)
                     (vl::vl-scopestack-find-definition name ss)))
         (use-set-pair (and vlmod (hons-get name (use-set-summaries-fix use-set-acc))))
         ((when use-set-pair)
          (mv (modalist-fix (list (cons name (modalist-lookup name stubbed-modalist))))
              (modalist-fix stubbed-modalist)
              (use-set-summaries-fix use-set-acc)
              (vl::vl-reportcard-fix reportcard)
              (use-set->uses (cdr use-set-pair)) (use-set->sets (cdr use-set-pair))))
         ((mv stubbed-modalist-local stubbed-modalist use-set-acc reportcard submod-use submod-set)
          (sv-use-set-analyze-instances mod.insts modalist stubbed-modalist use-set-acc reportcard ss))
         (stubbed-modalist-local (cons (cons name mod) stubbed-modalist-local))
         ((unless vlmod)
          (mv stubbed-modalist-local stubbed-modalist use-set-acc reportcard submod-use submod-set))
         ((acl2::with-fast stubbed-modalist-local))
         ((mv use-set warnings stub-mod)
          (time$ (sv-module-analyze-use-set name mod vlmod stubbed-modalist-local submod-use submod-set ss)
                  :mintime 1
                  :msg "; SV-USE-SET Checking ~x0: ~st sec, ~sa bytes~%"
                  :args (list name)))
         (use-set-acc (hons-acons name use-set use-set-acc))
         (reportcard (hons-acons name warnings reportcard))
         (stubbed-modalist (hons-acons name stub-mod stubbed-modalist)))
      (mv (list (cons name stub-mod))
          stubbed-modalist
          use-set-acc reportcard (use-set->uses use-set) (use-set->sets use-set))))

  (define sv-use-set-analyze-instances ((insts modinstlist-p)
                                        (modalist modalist-p)
                                        (stubbed-modalist modalist-p)
                                        (use-set-acc use-set-summaries-p)
                                        (reportcard vl::vl-reportcard-p)
                                        (ss vl::vl-scopestack-p))
    :guard (and (modhier-loopfreelist-p (modinstlist->modnames insts) modalist)
                (svarlist-addr-p (modalist-vars modalist))
                (svarlist-addr-p (modalist-vars stubbed-modalist))
                (equal (alist-keys stubbed-modalist)
                       (alist-keys use-set-acc)))
    :measure (modinstlist-meas insts modalist)
    :returns (mv (new-modalist-local modalist-p)
                 (new-modalist-all modalist-p)
                 (new-use-set-acc use-set-summaries-p)
                 (new-reportcard vl::vl-reportcard-p)
                 (submod-use rangemap-p)
                 (submod-set rangemap-p))
    (b* (((when (atom insts))
          (mv nil
              (modalist-fix stubbed-modalist)
              (use-set-summaries-fix use-set-acc)
              (vl::vl-reportcard-fix reportcard)
              nil nil))
         ((modinst inst1) (car insts))
         ((mv stubbed-modalist-local1 stubbed-modalist use-set-acc reportcard uses1 sets1)
          (sv-use-set-analyze-rec inst1.modname
                                  modalist stubbed-modalist use-set-acc reportcard ss))
         ((mv stubbed-modalist-local2 stubbed-modalist use-set-acc reportcard uses2 sets2)
          (sv-use-set-analyze-instances (cdr insts) modalist stubbed-modalist use-set-acc reportcard ss)))
      (mv (append-tr stubbed-modalist-local1 stubbed-modalist-local2)
          stubbed-modalist
          use-set-acc reportcard
          (append-tr (translate-rangemap-to-outer-scope inst1.instname uses1) uses2)
          (append-tr (translate-rangemap-to-outer-scope inst1.instname sets1) sets2))))
  ///

  (local (in-theory (disable (:d sv-use-set-analyze-rec)
                             (:d sv-use-set-analyze-instances)
                             member
                             svarlist-addr-p-when-subsetp-equal
                             append)))

  (local (defthm vars-of-modalist-lookup
           (implies (not (member v (modalist-vars modalist)))
                    (not (member v (module-vars (modalist-lookup name modalist)))))
           :hints(("Goal" :in-theory (e/d (modalist-lookup modalist-fix modalist-vars)
                                          (hons-assoc-equal-of-modalist-fix))
                   :induct (modalist-fix modalist)
                   :expand ((modalist-fix modalist)
                            (:free (a b) (modalist-vars (cons a b))))))))

  (std::defret-mutual sv-use-set-analyze-rec
    (defret vars-addr-p-of-sv-use-set-analyze-rec
      (implies (and (svarlist-addr-p (modalist-vars modalist))
                    (svarlist-addr-p (modalist-vars stubbed-modalist)))
               (and (svarlist-addr-p (modalist-vars new-modalist-local))
                    (svarlist-addr-p (modalist-vars new-modalist-all))))
      :hints ('(:expand (<call>
                         (:free (a b) (modalist-vars (cons a b))))))
      :fn sv-use-set-analyze-rec)
    (defret vars-addr-p-of-sv-use-set-analyze-instances
      (implies (and (svarlist-addr-p (modalist-vars modalist))
                    (svarlist-addr-p (modalist-vars stubbed-modalist)))
               (and (svarlist-addr-p (modalist-vars new-modalist-local))
                    (svarlist-addr-p (modalist-vars new-modalist-all))))
      :hints ('(:expand (<call>)))
      :fn sv-use-set-analyze-instances))

  (std::defret-mutual sv-use-set-analyze-rec
    (defret keys-equal-of-sv-use-set-analyze-rec
      (implies (and (equal (alist-keys use-set-acc) (alist-keys stubbed-modalist))
                    (use-set-summaries-p use-set-acc)
                    (modalist-p stubbed-modalist))
               (equal (alist-keys new-use-set-acc) (alist-keys new-modalist-all)))
      :hints ('(:expand (<call>)))
      :fn sv-use-set-analyze-rec)
    (defret keys-equal-of-sv-use-set-analyze-instances
      (implies (and (equal (alist-keys use-set-acc) (alist-keys stubbed-modalist))
                    (use-set-summaries-p use-set-acc)
                    (modalist-p stubbed-modalist))
               (equal (alist-keys new-use-set-acc) (alist-keys new-modalist-all)))
      :hints ('(:expand (<call>)))
      :fn sv-use-set-analyze-instances))

  (local (defthm cdr-hons-equal-iff-hons-equal
           (implies (modalist-p x)
                    (iff (cdr (hons-assoc-equal k x))
                         (hons-assoc-equal k x)))
           :hints(("Goal" :in-theory (enable hons-assoc-equal)))))

  (local (include-book "std/alists/alist-keys" :dir :system))

  (local (defthm modalist-lookup-when-use-set-acc-lookup
           (implies (and (hons-assoc-equal x use-set-acc)
                         (modalist-p modalist)
                         (equal (alist-keys modalist)
                                (alist-keys use-set-acc)))
                    (modalist-lookup x modalist))
           :hints(("Goal" :in-theory (e/d (modalist-lookup
                                           acl2::hons-assoc-equal-iff-member-alist-keys)
                                          (acl2::alist-keys-member-hons-assoc-equal))))))

  (verify-guards sv-use-set-analyze-rec
    :hints (("goal" :expand ((:free (a b) (modalist-vars (cons a b)))))))

  (fty::deffixequiv-mutual sv-use-set-analyze-rec))
                     


(define sv-use-set-analyze-all ((tail modalist-p)
                                (modalist modalist-p)
                                (stubbed-modalist modalist-p)
                                (use-set-acc use-set-summaries-p)
                                (reportcard vl::vl-reportcard-p)
                                (ss vl::vl-scopestack-p))
    :guard (and (modhier-loopfreelist-p (alist-keys (modalist-fix tail)) modalist)
                (svarlist-addr-p (modalist-vars modalist))
                (svarlist-addr-p (modalist-vars stubbed-modalist))
                (equal (alist-keys stubbed-modalist) (alist-keys use-set-acc)))
    :returns (mv (new-modalist modalist-p)
                 (new-use-set-acc use-set-summaries-p)
                 (new-reportcard vl::vl-reportcard-p))
    :measure (len (modalist-fix tail))
    :hints(("Goal" :in-theory (enable len)))
    (b* ((tail (modalist-fix tail))
         ((unless (consp tail))
          (mv (modalist-fix stubbed-modalist)
              (use-set-summaries-fix use-set-acc)
              (vl::vl-reportcard-fix reportcard)))
         (name (caar tail))
         ((mv & stubbed-modalist use-set-acc reportcard & &)
          (sv-use-set-analyze-rec name modalist stubbed-modalist use-set-acc reportcard ss)))
      (sv-use-set-analyze-all (cdr tail) modalist stubbed-modalist use-set-acc reportcard ss)))

#!vl
(define vl-design-sv-use-set ((x vl-design-p)
                              (modalist sv::modalist-p))
  :returns (new-x vl-design-p)
  :guard (sv::svarlist-addr-p (sv::modalist-vars modalist))
  :parents (vl-lint)
  :short "Analyze used/set variables using SV's semantics."
  :long "<p>This check issues warnings about variables that are unused, unset,
or spurious (neither used nor set).  It has some overlap with @(see vl::Lucid), but
each check does some things that the other doesn't:</p>

<ul>

<li>Lucid checks whether parameters, functions, types, etc. are used,
whereas sv-use-set only deals with variables (a category which includes wires
and regs, etc).</li>

<li>Lucid checks variables that are local to procedural code, which sv-use-set
currently does not.</li>

<li>Sv-use-set understands complex datatypes and is exact in its analysis of
which array/struct/etc. fields are used/set, which lucid does not.</li>

<li>Sv-use-set understands procedural constructs such as bounded loops and in
many cases can statically determine which indices of an array are accessed even
when the index is a local procedural variable.</li>

</ul>"

  (b* ((modalist (sv::modalist-fix modalist))
       ((unless (sv::modhier-loopfreelist-p (alist-keys modalist) modalist))
        (cw "Error: loop in instantiation hierarchy??~%")
        (vl-design-fix x))
       ((mv stubbed-modalist use-set-acc reportcard)
        (sv::sv-use-set-analyze-all modalist modalist nil nil nil (vl-scopestack-init x))))
    (fast-alist-free stubbed-modalist)
    (fast-alist-free use-set-acc)
    (vl-apply-reportcard x reportcard)))
