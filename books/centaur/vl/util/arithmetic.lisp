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

; BOZO Lib.  This book should only be locally included, and because of that you
; should never define a function here.  Instead, widely useful functions should
; generally be defined in defs.lisp.  Eventually, these lemmas should be moved
; into more other libraries.

(deflabel pre-arithmetic)

(include-book "arithmetic/top-with-meta" :dir :system)
(include-book "centaur/bitops/integer-length" :dir :system)

(defthm rationalp-when-integerp
  (implies (integerp x)
           (rationalp x)))

(defthm integerp-when-natp
  (implies (natp x)
           (integerp x)))

(defthm natp-when-posp
  (implies (posp x)
           (natp x)))

(defthm negative-when-natp
  (implies (natp x)
           (equal (< x 0)
                  nil)))

(defthm natp-of-one-plus
  (implies (natp x)
           (natp (+ 1 x))))

(defthm integerp-of-plus
  (implies (and (integerp a)
                (integerp b))
           (integerp (+ a b))))

(def-ruleset basic-arithmetic-rules
  (set-difference-equal (current-theory :here)
                        (current-theory 'pre-arithmetic)))

(add-to-ruleset basic-arithmetic-rules
                '(acl2::rationalp-implies-acl2-numberp
                  default-+-1
                  default-+-2
                  default-<-1
                  default-<-2
                  default-unary-minus
                  default-*-1
                  default-*-2))

(include-book "subsetp-equal")

(include-book "data-structures/list-defthms" :dir :system)

(include-book "misc/hons-help" :dir :system)

(include-book "unicode/list-defuns" :dir :system)
(include-book "unicode/nthcdr" :dir :system)
(include-book "unicode/take" :dir :system)
(include-book "unicode/coerce" :dir :system)
(include-book "unicode/list-fix" :dir :system)
(include-book "unicode/explode-atom" :dir :system)
(include-book "unicode/repeat" :dir :system)
(include-book "unicode/rev" :dir :system)

(include-book "defsort/duplicity" :dir :system)
(include-book "tools/mv-nth" :dir :system)
(include-book "tools/bstar" :dir :system)


(defun dec-dec-induct (k n)
  (if (zp k)
      nil
    (if (zp n)
        nil
      (dec-dec-induct (- k 1) (- n 1)))))


(in-theory (disable
            ;; I've had performance problems with these:
            (:type-prescription acl2::consp-append . 1)
            (:type-prescription acl2::consp-append . 2)
            ;; This seems like a lousy rule and causes performance problems:
            acl2::remove-equal-non-member-equal
            ;; My nomination for worst rule in the history of ACL2.  Causes
            ;; terrible goal blowup whenever state is involved in proofs that
            ;; have forcing round and just generally is a terrible idea.
            state-p1-forward
            ;; These just ought to be disabled
            o<
            o-p
            acl2-count
            explode-atom
            string-append
            string-append-lst
            append
            subseq
            subseq-list
            intersectp-equal
            intersection-equal
            no-duplicatesp-equal
            set-difference-equal
            pairlis$
            make-character-list

            simpler-take
            nthcdr

            true-listp
            string-listp
            symbol-listp
            character-listp

            assoc-equal
            alistp
            strip-cars
            strip-cdrs

            hons-shrink-alist
            make-fal

            ;; I often use len as a way to induct, so I only disable its
            ;; definition.  It would probably be better to use cdr-induction
            ;; instead, but oh well.
            (:definition len)))



(encapsulate ()

  (local (in-theory (enable true-listp)))

  (defthm true-listp-when-not-consp
    (implies (not (consp x))
             (equal (true-listp x)
                    (not x))))

  (defthm true-listp-of-cons
    (equal (true-listp (cons a x))
           (true-listp x)))

  (defthm consp-under-iff-when-true-listp
    (implies (true-listp x)
             (iff (consp x)
                  x))
    :rule-classes ((:rewrite :backchain-limit-lst 0))))



(encapsulate ()

  (local (in-theory (enable len)))

  (defthm len-when-not-consp
    (implies (not (consp x))
             (equal (len x)
                    0)))

  (defthm len-of-cons
    (equal (len (cons a x))
           (+ 1 (len x))))

  (defthm |(equal 0 (len x))|
    (equal (equal 0 (len x))
           (atom x)))

  (defthm |(< 0 (len x))|
    (equal (< 0 (len x))
           (consp x)))

  (defthm consp-by-len
    (implies (and (equal (len x) n)
                  (syntaxp (quotep n)))
             (equal (consp x)
                    (< 0 n))))

  (defthm consp-of-cdr-by-len
    (implies (and (equal (len x) n)
                  (syntaxp (quotep n)))
             (equal (consp (cdr x))
                    (< 1 n)))
    :hints(("Goal" :in-theory (enable len))))

  (defthm consp-of-cddr-by-len
    (implies (and (equal (len x) n)
                  (syntaxp (quotep n)))
             (equal (consp (cddr x))
                    (< 2 n)))
    :hints(("Goal" :in-theory (enable len))))

  (defthm consp-of-cdddr-by-len
    (implies (and (equal (len x) n)
                  (syntaxp (quotep n)))
             (equal (consp (cdddr x))
                    (< 3 n)))
    :hints(("Goal" :in-theory (enable len)))))




(defthm coerce-list-under-iff
  (implies (stringp string)
           (iff (coerce string 'list)
                (not (equal "" string))))
  :hints(("Goal"
          :in-theory (disable acl2::equal-of-coerce-lists)
          :use ((:instance acl2::equal-of-coerce-lists
                           (acl2::x string)
                           (acl2::y ""))))))


(encapsulate ()

  (local (in-theory (enable acl2-count o< o-p)))

  (defthm acl2-count-positive-when-consp
    (implies (consp x)
             (< 0 (acl2-count x)))
    :rule-classes ((:type-prescription) (:linear)))

  (defthm acl2-count-of-cons
    (equal (acl2-count (cons a x))
           (+ 1 (acl2-count a) (acl2-count x))))

  (defthm acl2-count-of-cdr
    (and (implies (consp x)
                  (< (acl2-count (cdr x))
                     (acl2-count x)))
         (<= (acl2-count (cdr x))
             (acl2-count x)))
    :rule-classes ((:rewrite) (:linear)))

  (defthm acl2-count-of-car
    (and (implies (consp x)
                  (< (acl2-count (car x))
                     (acl2-count x)))
         (<= (acl2-count (car x))
             (acl2-count x)))
    :rule-classes ((:rewrite) (:linear)))

  (defthm acl2-count-of-cdr-same-fc
    (implies (equal (acl2-count (cdr x))
                    (acl2-count x))
             (not (consp x)))
    :rule-classes :forward-chaining)

  (defthm acl2-count-zero-when-true-listp
    (implies (true-listp x)
             (equal (equal 0 (acl2-count x))
                    (not x))))

  (defthm acl2-count-zero-when-stringp
    (implies (stringp x)
             (equal (equal 0 (acl2-count x))
                    (equal x ""))))

  (defthm o<-when-natps
    (implies (and (natp x)
                  (natp y))
             (equal (o< x y)
                    (< x y))))

  (defthm o-p-when-natp
    (implies (natp x)
             (o-p x))))



(defthm duplicity-of-list-fix
  (equal (acl2::duplicity a (list-fix x))
         (acl2::duplicity a x))
  :hints(("Goal" :induct (len x))))

(defthm acl2-count-of-list-fix-weak
  (<= (acl2-count (list-fix x))
      (acl2-count x))
  :rule-classes ((:rewrite) (:linear))
  :hints(("Goal" :in-theory (enable acl2-count))))


(encapsulate ()

  (local (in-theory (enable append)))

  (defthm append-when-not-consp
    (implies (not (consp x))
             (equal (append x y)
                    y)))

  (defthm append-of-cons
    (equal (append (cons a x) y)
           (cons a (append x y))))

  (defthm append-of-nil
    (equal (append x nil)
           (list-fix x)))

  (defthm consp-of-append
    (equal (consp (append x y))
           (or (consp x)
               (consp y))))

  (defthm append-under-iff
    (iff (append x y)
         (or (consp x)
             y)))

  (defthm acl2-count-of-append
    (equal (acl2-count (append x y))
           (+ (acl2-count (list-fix x))
              (acl2-count y)))
    :hints(("Goal" :in-theory (enable acl2-count))))

  (defthm subsetp-equal-of-append
    (equal (subsetp-equal (append x y) z)
           (and (subsetp-equal x z)
                (subsetp-equal y z))))

  (defthm app-removal
    (equal (acl2::app x y)
           (append x (list-fix y)))
    :hints(("Goal" ::in-theory (enable acl2::binary-app)))))



(encapsulate ()

  (local (in-theory (enable rev)))

  (defthm rev-under-iff
    ;; BOZO move me to unicode/rev
    (iff (rev x) (consp x)))

  (defthm member-equal-of-rev
    (iff (member-equal a (rev x))
         (member-equal a x)))

  (defthm rev-under-subsetp-equiv
    (subsetp-equiv (rev x) (double-rewrite x))
    :hints(("Goal" :in-theory (enable subsetp-equiv))))

  (defthm duplicity-of-rev
    (equal (acl2::duplicity a (rev x))
           (acl2::duplicity a x))))



(encapsulate ()

  (local (in-theory (enable no-duplicatesp-equal)))

  (defthm no-duplicatesp-equal-when-not-consp
    (implies (not (consp x))
             (equal (no-duplicatesp-equal x)
                    t)))

  (defthm no-duplicatesp-equal-of-cons
    (equal (no-duplicatesp-equal (cons a x))
           (and (not (member-equal a (double-rewrite x)))
                (no-duplicatesp-equal x))))

  (defthm no-duplicatesp-equal-of-list-fix
    (equal (no-duplicatesp-equal (list-fix x))
           (no-duplicatesp-equal x)))

  (defthm no-duplicatesp-equal-of-rev
    (equal (no-duplicatesp-equal (rev x))
           (no-duplicatesp-equal x))
    :hints(("Goal"
            :use ((:functional-instance
                   acl2::no-duplicatesp-equal-same-by-duplicity
                   (acl2::duplicity-hyp (lambda () t))
                   (acl2::duplicity-lhs (lambda () (rev x)))
                   (acl2::duplicity-rhs (lambda () x)))))))

  (defthm no-duplicatesp-equal-of-append-of-rev-1
    (equal (no-duplicatesp-equal (append (rev x) y))
           (no-duplicatesp-equal (append x y)))
    :hints(("Goal"
            :use ((:functional-instance
                   acl2::no-duplicatesp-equal-same-by-duplicity
                   (acl2::duplicity-hyp (lambda () t))
                   (acl2::duplicity-lhs (lambda () (append (rev x) y)))
                   (acl2::duplicity-rhs (lambda () (append x y))))))))

  (defthm no-duplicatesp-equal-of-append-of-rev-2
    (equal (no-duplicatesp-equal (append x (rev y)))
           (no-duplicatesp-equal (append x y)))
    :hints(("Goal"
            :use ((:functional-instance
                   acl2::no-duplicatesp-equal-same-by-duplicity
                   (acl2::duplicity-hyp (lambda () t))
                   (acl2::duplicity-lhs (lambda () (append x (rev y))))
                   (acl2::duplicity-rhs (lambda () (append x y))))))))

  (defthm no-duplicatesp-equal-of-append-of-append
    (equal (no-duplicatesp-equal (append x y))
           (no-duplicatesp-equal (append y x)))
    :rule-classes ((:rewrite :loop-stopper ((x y))))
    :hints (("Goal" :use ((:functional-instance
                           acl2::no-duplicatesp-equal-same-by-duplicity
                           (acl2::duplicity-hyp (lambda () t))
                           (acl2::duplicity-lhs (lambda () (append x y)))
                           (acl2::duplicity-rhs (lambda () (append y x)))))))))



(encapsulate ()

  (local (in-theory (enable flatten)))

  (defthm true-listp-of-flatten
    (true-listp (flatten x))
    :rule-classes :type-prescription)

  (defthm flatten-when-not-consp
    (implies (not (consp x))
             (equal (flatten x)
                    nil)))

  (defthm flatten-of-cons
    (equal (flatten (cons a x))
           (append a (flatten x))))

  (defthm flatten-of-list-fix
    (equal (flatten (list-fix x))
           (flatten x)))

  (defthm flatten-of-append
    (equal (flatten (append x y))
           (append (flatten x) (flatten y))))

  (local (defthm l1
           (implies (and (subsetp-equal x y)
                         (member-equal a (flatten x)))
                    (member-equal a (flatten y)))))

  (local (defthm l2
           (implies (subsetp-equal x y)
                    (subsetp-equal (flatten x) (flatten y)))))

  (defcong subsetp-equiv subsetp-equiv (flatten x) 1
    :hints(("Goal" :in-theory (enable subsetp-equiv))))

  (defthm duplicity-of-flatten-of-rev
    (equal (acl2::duplicity a (flatten (rev x)))
           (acl2::duplicity a (flatten x)))
    :hints(("Goal" :induct (len x))))

  (defthm no-duplicatesp-equal-of-flatten-of-rev
    (equal (no-duplicatesp-equal (flatten (rev x)))
           (no-duplicatesp-equal (flatten x)))
    :hints(("Goal"
            :use ((:functional-instance
                   acl2::no-duplicatesp-equal-same-by-duplicity
                   (acl2::duplicity-hyp (lambda () t))
                   (acl2::duplicity-lhs (lambda () (flatten (rev x))))
                   (acl2::duplicity-rhs (lambda () (flatten x)))))))))



(encapsulate ()

  (local (in-theory (enable repeat)))

  (defthm repeat-when-zp
    (implies (zp n)
             (equal (repeat a n)
                    nil)))

  (defthm consp-of-repeat
    (equal (consp (repeat a n))
           (posp n)))

  (defthm repeat-1
    (equal (repeat a 1)
           (list a)))

  (defthm car-of-repeat-increment
    ;; Goofy rule that helps when recurring when repeat is involved.
    (implies (natp n)
             (equal (car (repeat x (+ 1 n)))
                    x)))

  (defthm cdr-of-repeat-increment
    ;; Goofy rule that helps when recurring when repeat is involved.
    (implies (natp n)
             (equal (cdr (repeat x (+ 1 n)))
                    (repeat x n))))

  (defthm member-equal-of-repeat
    (iff (member-equal a (repeat b n))
         (and (equal a b)
              (posp n)))))




(encapsulate ()

  (local (in-theory (enable simpler-take)))

  (defthm simpler-take-under-iff
    (iff (simpler-take n x)
         (posp n)))

  (defthm simpler-take-of-len-free
    (implies (equal len (len x))
             (equal (simpler-take len x)
                    (list-fix x))))

  (defthm simpler-take-of-repeat
    (equal (simpler-take n (repeat a k))
           (if (<= (nfix n) (nfix k))
               (repeat a n)
             (append (repeat a k)
                     (repeat nil (- (nfix n) (nfix k))))))
    :hints(("Goal"
            :induct (dec-dec-induct k n)
            :in-theory (enable repeat))))

  (defthm subsetp-equal-of-simpler-take
    (implies (<= (nfix n) (len x))
             (subsetp-equal (simpler-take n x) x))))



(encapsulate ()

  (local (in-theory (enable nthcdr)))

  (defthm nthcdr-when-atom
    (implies (atom x)
             (equal (nthcdr n x)
                    (if (posp n)
                        nil
                      x))))

  (defthm nthcdr-of-cons
    (equal (nthcdr n (cons a x))
           (if (zp n)
               (cons a x)
             (nthcdr (- n 1) x))))

  (defthm car-of-nthcdr
    (equal (car (nthcdr i x))
           (nth i x)))

  (defthm nthcdr-of-cdr
    (equal (nthcdr i (cdr x))
           (cdr (nthcdr i x))))

  (defthm append-of-simpler-take-and-nthcdr
    (implies (force (<= n (len x)))
             (equal (append (simpler-take n x)
                            (nthcdr n x))
                    x)))

  (defthm true-listp-of-nthcdr
    (equal (true-listp (nthcdr n x))
           (or (< (len x) (nfix n))
               (true-listp x))))

  (defthm nthcdr-when-less-than-len-under-iff
    (implies (< (nfix n) (len x))
             (iff (nthcdr n x)
                  t)))

  (defthm nthcdr-of-increment
    ;; Goofy rule which may be useful when nthcdr is used in recursive
    ;; definitions.
    (implies (natp n)
             (equal (nthcdr (+ 1 n) x)
                    (cdr (nthcdr n x)))))

  (defthm acl2-count-of-nthcdr
    (equal (acl2-count (nthcdr n x))
           (if (<= (nfix n) (len x))
               (- (acl2-count x)
                  (acl2-count (simpler-take n x)))
             0)))

  (defthm nthcdr-of-repeat
    (equal (nthcdr n (repeat a k))
           (if (<= (nfix n) (nfix k))
               (repeat a (- (nfix k) (nfix n)))
             nil))
    :hints(("Goal"
            :induct (dec-dec-induct k n)
            :in-theory (enable repeat)))))



(encapsulate ()

  (local (defthm l0
           (implies (equal (append (repeat a n) x) y)
                    (and (equal (repeat a n) (take n y))
                         (equal (nthcdr n y) x)))
           :hints(("Goal" :in-theory (enable repeat)))))

  (local (defthm l1
           (implies (not (<= (nfix n) (len y)))
                    (not (equal (append (repeat a n) x) y)))
           :hints(("Goal" :in-theory (enable repeat)))))

  (local (defthm l2
           (implies (and (<= n (len y))
                         (equal (repeat a n) (take n y))
                         (equal x (nthcdr n y)))
                    (equal (append (repeat a n) x) y))
           :hints(("Goal"
                   :in-theory (disable append-of-simpler-take-and-nthcdr)
                   :use ((:instance append-of-simpler-take-and-nthcdr
                                    (n n)
                                    (x y)))))))

  (defthm equal-of-append-repeat
    (implies (case-split (<= n (len y)))
             (equal (equal (append (repeat a n) x) y)
                    (and (equal (repeat a n) (take n y))
                         (equal x (nthcdr n y)))))
    :hints(("Goal"
            :use ((:instance l0)
                  (:instance l2))))))

(defthm rev-of-repeat
  (equal (rev (repeat a n))
         (repeat a n))
  :hints(("Goal" :in-theory (enable repeat))))




(encapsulate ()

  (local (in-theory (enable nth)))

  (defthm nth-of-atom
    (implies (not (consp x))
             (equal (nth n x)
                    nil)))

  (defthm nth-of-cons
    (equal (nth n (cons a x))
           (if (zp n)
               a
             (nth (- n 1) x))))

  (defthm nth-when-zp
    (implies (zp n)
             (equal (nth n x)
                    (car x))))

  (defthm nth-when-too-big
    (implies (<= (len x) (nfix n))
             (equal (nth n x)
                    nil))))


(encapsulate ()

  (local (in-theory (enable last)))

  (defthm last-when-atom
    (implies (atom x)
             (equal (last x)
                    x)))

  (defthm last-of-cons
    (equal (last (cons a x))
           (if (atom x)
               (cons a x)
             (last x))))

  (defthm last-under-iff
    (iff (last x)
         x))

  (defthm consp-of-last
    (equal (consp (last x))
           (consp x)))

  (defthm acl2-count-of-last-weak
    (<= (acl2-count (last x))
        (acl2-count x))
    :rule-classes ((:rewrite) (:linear)))

  (defthm acl2-count-of-last-strong
    (implies (consp (cdr x))
             (< (acl2-count (last x))
                (acl2-count x)))
    :rule-classes ((:rewrite) (:linear)))

  (defthm acl2-count-of-last-same
    (equal (equal (acl2-count x) (acl2-count (last x)))
           (atom (cdr x)))))



(defthm butlast-under-iff
  ;; Bleh, definition doesn't nfix n so we have to have the hyp...
  (implies (force (integerp n))
           (iff (butlast x n)
                (< n (len x))))
  :hints(("Goal" :in-theory (enable butlast))))



(encapsulate ()

  (local (in-theory (enable prefixp)))

  (defthm prefixp-when-atom
    (implies (atom x)
             (prefixp x y)))

  (defthm prefixp-of-cons
    (equal (prefixp (cons a x) y)
           (and (consp y)
                (equal a (car y))
                (prefixp x (cdr y)))))

  (defthm prefixp-when-atom-right
    (implies (atom y)
             (equal (prefixp x y)
                    (atom x))))

  (defthm prefixp-of-simpler-take
    (equal (prefixp (simpler-take n x) x)
           (<= (nfix n) (len x)))
    :hints(("Goal" :in-theory (enable simpler-take))))

  (defthm prefixp-impossible-by-len
    (implies (< (len x) (len p))
             (equal (prefixp p x)
                    nil)))

  (defthm prefixp-of-append
    (prefixp x (append x y)))

  (defthm prefixp-when-equal-lengths
    (implies (equal (len x) (len y))
             (equal (prefixp x y)
                    (equal (list-fix x) (list-fix y)))))

  (defthm prefixp-of-append-when-same-length
    (implies (equal (len x) (len y))
             (equal (prefixp x (append y z))
                    (prefixp x y)))))



(encapsulate ()

  (local (in-theory (enable alistp)))

  (defthm alistp-when-not-consp
    (implies (not (consp x))
             (equal (alistp x)
                    (not x))))

  (defthm alistp-of-cons
    (equal (alistp (cons a x))
           (and (consp a)
                (alistp x))))

  (defthm alistp-of-append
    (implies (and (force (alistp x))
                  (force (alistp y)))
             (alistp (append x y))))

  (defthm alistp-of-cdr
    (implies (alistp alist)
             (alistp (cdr alist))))

  (defthm alistp-of-insert
    (implies (and (alistp x)
                  (consp a))
             (alistp (sets::insert a x)))
    :hints(("Goal" :in-theory (enable (:ruleset sets::primitive-rules)))))

  (defthm alistp-of-mergesort
    (implies (alistp x)
             (alistp (sets::mergesort x)))))



(encapsulate ()

  (local (in-theory (enable strip-cars)))

  (defthm strip-cars-when-not-consp
    (implies (not (consp x))
             (equal (strip-cars x)
                    nil)))

  (defthm strip-cars-of-cons
    (equal (strip-cars (cons a x))
           (cons (car a)
                 (strip-cars x))))

  (defthm strip-cars-of-list-fix
    (equal (strip-cars (list-fix x))
           (strip-cars x)))

  (defthm strip-cars-of-append
    (equal (strip-cars (append x y))
           (append (strip-cars x)
                   (strip-cars y))))

  (defthm len-of-strip-cars
    (equal (len (strip-cars x))
           (len x))))



(encapsulate ()

  (local (in-theory (enable strip-cdrs)))

  (defthm strip-cdrs-when-not-consp
    (implies (not (consp x))
             (equal (strip-cdrs x)
                    nil)))

  (defthm strip-cdrs-of-cons
    (equal (strip-cdrs (cons a x))
           (cons (cdr a)
                 (strip-cdrs x))))

  (defthm len-of-strip-cdrs
    (equal (len (strip-cdrs x))
           (len x)))

  (defthm strip-cdrs-of-append
    (equal (strip-cdrs (append x y))
           (append (strip-cdrs x)
                   (strip-cdrs y))))

  (defthm strip-cdrs-of-rev
    (equal (strip-cdrs (rev x))
           (rev (strip-cdrs x)))))




(encapsulate ()

  (local (in-theory (enable pairlis$)))

  (defthm pairlis$-when-not-consp
    (implies (not (consp x))
             (equal (pairlis$ x y)
                    nil)))

  (defthm pairlis$-of-cons
    (equal (pairlis$ (cons a x) y)
           (cons (cons a (car y))
                 (pairlis$ x (cdr y)))))

  (defthm alistp-of-pairlis$
    (alistp (pairlis$ x y)))

  (defthm len-of-pairlis$
    (equal (len (pairlis$ x y))
           (len x)))

  (defthm strip-cars-of-pairlis$
    (equal (strip-cars (pairlis$ x y))
           (list-fix x)))

  (defthm strip-cdrs-of-pairlis$
    (equal (strip-cdrs (pairlis$ x y))
           (if (<= (len x) (len y))
               (simpler-take (len x) y)
             (append y (repeat nil (- (len x) (len y))))))
    :hints(("Goal"
            :induct (pairlis$ x y)
            :in-theory (enable repeat)))))



(encapsulate ()

  (local (in-theory (enable hons-assoc-equal)))

  (defthm hons-assoc-equal-when-atom
    (implies (atom alist)
             (equal (hons-assoc-equal a alist)
                    nil)))

  (defthm hons-assoc-equal-of-cons
    (equal (hons-assoc-equal key (cons entry map))
           (if (and (consp entry)
                    (equal key (car entry)))
               entry
             (hons-assoc-equal key map))))

  (defthm hons-assoc-equal-of-hons-acons
    (equal (hons-assoc-equal key (hons-acons key2 val map))
           (if (equal key key2)
               (cons key val)
             (hons-assoc-equal key map))))

  (defthm consp-of-hons-assoc-equal
    (equal (consp (hons-assoc-equal x alist))
           (if (hons-assoc-equal x alist)
               t
             nil)))

  (defthm car-of-hons-assoc-equal
    (equal (car (hons-assoc-equal key alist))
           (if (hons-assoc-equal key alist)
               key
             nil)))

  (defthm assoc-equal-elim
    (implies (force (alistp alist))
             (equal (assoc-equal key alist)
                    (hons-assoc-equal key alist)))
    :hints(("Goal" :in-theory (enable assoc-equal)))))



(defthm hons-assoc-equal-of-make-fal
  (equal (hons-assoc-equal a (make-fal x y))
         (or (hons-assoc-equal a x)
             (hons-assoc-equal a y)))
  :hints(("Goal" :in-theory (enable make-fal))))



(encapsulate ()

  (local (in-theory (enable hons-shrink-alist)))

  (defthm hons-shrink-alist-when-not-consp
    (implies (atom x)
             (equal (hons-shrink-alist x y)
                    y)))

  (defthm hons-shrink-alist-of-cons
    (equal (hons-shrink-alist (cons a x) y)
           (cond ((atom a)
                  (hons-shrink-alist x y))
                 ((hons-assoc-equal (car a) y)
                  (hons-shrink-alist x y))
                 (t
                  (hons-shrink-alist x (cons a y))))))

  (defthm alistp-of-hons-shrink-alist
    (implies (alistp ans)
             (alistp (hons-shrink-alist x ans))))

  (defthm assoc-equal-of-hons-shrink-alist
    (equal (hons-assoc-equal a (hons-shrink-alist x ans))
           (or (hons-assoc-equal a ans)
               (hons-assoc-equal a x))))

  (local (defthm l0
          (implies (alistp x)
                   (iff (hons-assoc-equal a x)
                        (member-equal a (strip-cars x))))))

  (local (defthm l1
           (implies (and (alistp x)
                         (alistp y))
                    (iff (member-equal a (strip-cars (hons-shrink-alist x y)))
                         (or (member-equal a (strip-cars x))
                             (member-equal a (strip-cars y)))))))

  (defthm strip-cars-of-hons-shrink-alist-under-subsetp-equiv
    (implies (and (alistp x)
                  (alistp y))
             (subsetp-equiv (strip-cars (hons-shrink-alist x y))
                            (strip-cars (append x y))))
    :hints(("Goal" :in-theory (enable subsetp-equiv))))

  (local (defthm l2
           (implies (and (not (member-equal a (strip-cars x)))
                         (not (member-equal a (strip-cars y))))
                    (not (member-equal a (strip-cars (hons-shrink-alist x y)))))))

  (defthm subsetp-equal-of-strip-cars-of-hons-shrink-alist
    (subsetp-equal (strip-cars (hons-shrink-alist x nil))
                   (strip-cars x))))



(encapsulate ()

  (local (in-theory (enable intersectp-equal)))

  (defthm intersectp-equal-when-atom-left
    (implies (atom x)
             (equal (intersectp-equal x y)
                    nil)))

  (defthm intersectp-equal-when-atom-right
    (implies (atom y)
             (equal (intersectp-equal x y)
                    nil)))

  (defthm intersect-equal-of-cons-left
    (equal (intersectp-equal (cons a x) y)
           (if (member-equal a y)
               t
             (intersectp-equal x y))))

  (defthm intersectp-equal-of-cons-right
    (equal (intersectp-equal x (cons a y))
           (if (member-equal a x)
               t
             (intersectp-equal x y))))

  (defthm intersectp-equal-of-append-left
    (equal (intersectp-equal (append x y) z)
           (or (intersectp-equal x z)
               (intersectp-equal y z))))

  (defthm intersectp-equal-of-append-right
    (equal (intersectp-equal x (append y z))
           (or (intersectp-equal x y)
               (intersectp-equal x z))))

  (defthm intersectp-equal-commutative
    (equal (intersectp-equal x y)
           (intersectp-equal y x)))

  (local (defun badguy (x y)
           (cond ((atom x)
                  nil)
                 ((member-equal (car x) y)
                  (list (car x)))
                 (t
                  (badguy (cdr x) y)))))

  (local (defthm l0
           (equal (intersectp-equal x y)
                  (if (badguy x y)
                      t
                    nil))))

  (local (defthm l1
           (implies (and (member-equal a x)
                         (member-equal a y))
                    (badguy x y))))

  (local (defthm l2
           (implies (and (subsetp-equal x x2)
                         (badguy x y))
                    (badguy x2 y))))

  (local (defthm l3
           (implies (and (subsetp-equal x x2)
                         (not (badguy x2 y)))
                    (not (badguy x y)))))

  (local (defthm l4
           (implies (and (subsetp-equal y y2)
                         (badguy x y))
                    (badguy x y2))))

  (local (defthm l5
           (implies (and (subsetp-equal y y2)
                         (not (badguy x y2)))
                    (not (badguy x y)))))

  (local (defcong subsetp-equiv iff (badguy x y) 1
           :hints(("Goal" :in-theory (enable subsetp-equiv)))))

  (local (defcong subsetp-equiv iff (badguy x y) 2
           :hints(("Goal" :in-theory (enable subsetp-equiv)))))

  (defcong subsetp-equiv equal (intersectp-equal x y) 1
    :hints(("Goal" :in-theory (enable subsetp-equiv))))

  (defcong subsetp-equiv equal (intersectp-equal x y) 2
    :hints(("Goal" :in-theory (enable subsetp-equiv)))))



(encapsulate ()

  (defthm no-duplicatesp-equal-of-append
    (equal (no-duplicatesp-equal (append x y))
           (and (no-duplicatesp-equal x)
                (no-duplicatesp-equal y)
                (not (intersectp-equal x y))))
    :hints(("Goal" :induct (len x))))

  (defthm subsetp-equal-of-append-when-empty-intersect-left
    (implies (not (intersectp-equal a b))
             (equal (subsetp-equal a (append b c))
                    (subsetp-equal a c)))
    :hints(("Goal" :in-theory (enable subsetp-equal))))

  (defthm subsetp-equal-of-append-when-empty-intersect-right
    (implies (not (intersectp-equal a c))
             (equal (subsetp-equal a (append b c))
                    (subsetp-equal a b)))
    :hints(("Goal" :in-theory (enable subsetp-equal)))))



(encapsulate ()

  (local (in-theory (enable intersection-equal)))

  (defthm intersection-equal-when-atom
    (implies (atom x)
             (equal (intersection-equal x y)
                    nil)))

  (defthm intersection-equal-of-cons
    (equal (intersection-equal (cons a x) y)
           (if (member-equal a y)
               (cons a (intersection-equal x y))
             (intersection-equal x y))))

  (defthm member-equal-of-intersection-equal
    (iff (member-equal a (intersection-equal x y))
         (and (member-equal a x)
              (member-equal a y))))

  (defthm subsetp-equal-of-intersection-equal-1
    (subsetp-equal (intersection-equal x y) x))

  (defthm subsetp-equal-of-intersection-equal-2
    (subsetp-equal (intersection-equal x y) y)))



(encapsulate ()

  (local (in-theory (enable set-difference-equal)))

  (defthm set-difference-equal-when-atom
    (implies (atom x)
             (equal (set-difference-equal x y)
                    nil)))

  (defthm set-difference-equal-of-cons
    (equal (set-difference-equal (cons a x) y)
           (if (member-equal a y)
               (set-difference-equal x y)
             (cons a (set-difference-equal x y)))))

  (defthm member-equal-of-set-difference-equal
    (iff (member-equal a (set-difference-equal x y))
         (and (member-equal a (double-rewrite x))
              (not (member-equal a (double-rewrite y))))))

  (defthm set-difference-equal-when-subsetp-equal
    (implies (subsetp-equal x y)
             (equal (set-difference-equal x y)
                    nil)))

  (defthm set-difference-equal-of-self
    (equal (set-difference-equal x x)
           nil))

  (defthm empty-intersect-with-difference-of-self
    (not (intersectp-equal a (set-difference-equal b a))))

  (defcong subsetp-equiv equal (set-difference-equal x y) 2)

  (defcong subsetp-equiv subsetp-equiv (set-difference-equal x y) 1
    :hints(("Goal" :in-theory (enable subsetp-equiv)))))



(encapsulate ()

  (local (in-theory (enable character-listp)))

  (defthm character-listp-when-not-consp
    (implies (not (consp x))
             (equal (character-listp x)
                    (not x))))

  (defthm character-listp-of-cons
    (equal (character-listp (cons a x))
           (and (characterp a)
                (character-listp x))))

  (defthm true-listp-when-character-listp
    (implies (character-listp x)
             (true-listp x)))

  (defthm characterp-of-car-when-character-listp
    (implies (character-listp x)
             (equal (characterp (car x))
                    (consp x))))

  (defthm character-listp-of-cdr-when-character-listp
    (implies (character-listp x)
             (character-listp (cdr x))))

  (defthm character-listp-of-make-list-ac
    (implies (and (force (character-listp ac))
                  (force (characterp x)))
             (character-listp (make-list-ac n x ac))))

  (defthm character-listp-of-repeat
    (equal (character-listp (repeat a n))
           (or (zp n)
               (characterp a)))
    :hints(("Goal" :in-theory (enable repeat))))

  (defthm character-listp-of-simpler-take
    (implies (and (character-listp x)
                  (force (<= (nfix n) (len x))))
             (character-listp (simpler-take n x)))
    :hints(("Goal" :in-theory (enable simpler-take))))

  (defthm character-listp-of-butlast
    (implies (and (character-listp x)
                  (force (natp n))
                  (force (<= n (len x))))
             (character-listp (butlast x n)))
    :hints(("Goal" :in-theory (enable butlast))))

  (defthm character-listp-of-last
    (implies (character-listp x)
             (character-listp (last x))))

  (defthm character-listp-of-nthcdr
    (implies (character-listp x)
             (character-listp (nthcdr n x)))))


(encapsulate ()

  (local (in-theory (enable string-listp)))

  (defthm string-listp-when-not-consp
    (implies (not (consp x))
             (equal (string-listp x)
                    (not x))))

  (defthm string-listp-of-cons
    (equal (string-listp (cons a x))
           (and (stringp a)
                (string-listp x))))

  (defthm true-listp-when-string-listp
    (implies (string-listp x)
             (true-listp x))
    :rule-classes ((:compound-recognizer)
                   (:rewrite :backchain-limit-lst 1)))

  (defthm string-listp-of-append
    (implies (and (force (string-listp x))
                  (force (string-listp y)))
             (string-listp (append x y))))

  (defthm string-listp-of-rev
    (implies (force (string-listp x))
             (string-listp (rev x))))

  (defthm string-listp-of-intersection-equal
    (implies (and (force (string-listp x))
                  (force (string-listp y)))
             (string-listp (intersection-equal x y)))
    :hints(("Goal" :induct (len x))))

  (defthm string-listp-of-set-difference-equal
    (implies (string-listp x)
             (string-listp (set-difference-equal x y))))

  (defthm string-listp-of-remove-equal
    (implies (string-listp x)
             (string-listp (remove-equal a x))))

  (defthm stringp-when-member-equal-in-string-listp
    (implies (and (member-equal name x)
                  (string-listp x))
             (stringp name))
    :rule-classes ((:rewrite)
                   (:rewrite :corollary (implies (and (string-listp x)
                                                      (member-equal name x))
                                                 (stringp name)))))

  (defthm string-listp-of-strip-cdrs-of-pairlis$
    ;; BOZO what nonsense is this?
    (implies (and (string-listp cdrs)
                  (force (equal (len cars) (len cdrs))))
             (string-listp (strip-cdrs (pairlis$ cars cdrs))))))



(encapsulate ()

  (local (in-theory (enable symbol-listp)))

  (defthm symbol-listp-when-not-consp
    (implies (not (consp x))
             (equal (symbol-listp x)
                    (not x))))

  (defthm symbol-listp-of-cons
    (equal (symbol-listp (cons a x))
           (and (symbolp a)
                (symbol-listp x))))

  (defthm symbol-listp-of-append
    (equal (symbol-listp (append x y))
           (and (symbol-listp (list-fix x))
                (symbol-listp y)))
    :hints(("Goal" :induct (len x))))

  (defthm symbol-listp-of-rev
    (implies (symbol-listp x)
             (symbol-listp (rev x))))

  (defthm true-listp-when-symbol-listp
    (implies (symbol-listp x)
             (true-listp x))
    :rule-classes ((:compound-recognizer)
                   (:rewrite :backchain-limit-lst 1)))

  (defthm symbolp-of-car-when-symbol-listp
    (implies (symbol-listp x)
             (symbolp (car x))))

  (defthm symbol-listp-of-cdr-when-symbol-listp
    (implies (symbol-listp x)
             (symbol-listp (cdr x))))

  (defthm symbol-listp-of-repeat
    (equal (symbol-listp (repeat a n))
           (or (symbolp a)
               (zp n)))
    :hints(("Goal" :in-theory (enable repeat))))

  (defthm symbol-listp-of-simpler-take
    (implies (force (symbol-listp x))
             (symbol-listp (simpler-take n x)))
    :hints(("Goal" :in-theory (enable simpler-take))))

  (defthm eqlable-listp-when-symbol-listp
    (implies (symbol-listp x)
             (eqlable-listp x)))

  (defthm symbolp-of-cdr-hons-assoc-equal-when-symbol-listp-of-strip-cdrs
    (implies (symbol-listp (strip-cdrs alist))
             (symbolp (cdr (hons-assoc-equal a alist))))))




;; BOZO uncategorized rules

(defthm characterp-of-char
  (implies (and (force (< (nfix n) (length x)))
                (force (stringp x)))
           (characterp (char x n)))
  :hints(("Goal" :in-theory (enable char))))

(defthm stringp-when-true-listp
  (implies (true-listp x)
           (equal (stringp x)
                  nil)))

(defthm eqlablep-when-characterp
  ; BOZO why do we need this rule when there is eqlablep-recog?
  (implies (characterp x)
           (eqlablep x)))

(defthm string-append-lst-when-not-consp
  (implies (not (consp x))
           (equal (string-append-lst x)
                  ""))
  :hints(("Goal" :in-theory (enable string-append-lst))))

(defthm string-append-lst-of-cons
  (equal (string-append-lst (cons a x))
         (string-append a
                        (string-append-lst x)))
  :hints(("Goal" :in-theory (enable string-append-lst))))


(defthm true-listp-of-explode-nonnegative-integer
  (implies (true-listp acc)
           (true-listp (explode-nonnegative-integer x n acc)))
  :rule-classes :type-prescription)

(defthm true-listp-of-explode-atom
  (true-listp (explode-atom x n))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (e/d (explode-atom)))))


(defthm plist-worldp-of-w
  (implies (state-p1 state)
           (plist-worldp (w state)))
  :hints(("Goal" :in-theory (enable state-p1 w))))


(defthm alistp-of-make-fal
  (equal (alistp (make-fal x y))
         (alistp y))
  :hints(("Goal" :in-theory (enable make-fal))))


(encapsulate
  ()
  (local (defthm l0
           (implies (and (< (nfix n) (len x))
                         (character-listp x))
                    (characterp (nth n x)))
           :hints(("Goal" :in-theory (enable nth)))))

  (defthm characterp-of-nth
    (implies (character-listp x)
             (equal (characterp (nth n x))
                    (< (nfix n) (len x))))
    :hints(("Goal" :use ((:instance l0))))))




(encapsulate
  ()
  (local (in-theory (enable make-character-list)))

  (defthm make-character-list-when-character-listp
    (implies (character-listp x)
             (equal (make-character-list x)
                    x)))

  (defthm character-listp-of-make-character-list
    (character-listp (make-character-list x)))

  (defthm len-of-make-character-list
    (equal (len (make-character-list x))
           (len x))))



(encapsulate
  ()
  (defthm length-of-coerce
    ;; Wow, coerce is sort of awful in that (coerce "foo" 'string) returns ""
    ;; and (coerce '(1 2 3) 'list) returns nil.  This leads to a weird length
    ;; theorem.  We normally just leave length enabled, so this rule won't
    ;; have many uses.
    (equal (length (coerce x y))
           (cond ((equal y 'list)
                  (if (stringp x)
                      (length x)
                    0))
                 (t
                  (if (stringp x)
                      0
                    (len x)))))
    :hints(("Goal"
            :use ((:instance acl2::completion-of-coerce
                             (acl2::x x)
                             (acl2::y y))))))

  (defthm len-of-coerce-to-string
    (equal (len (coerce x 'string))
           0))

  (defthm coerce-inverse-1-better
    (equal (coerce (coerce x 'string) 'list)
           (if (stringp x)
               nil
             (make-character-list x)))
    :hints(("Goal"
            :use ((:instance acl2::completion-of-coerce
                             (acl2::x x)
                             (acl2::y 'string))))))

  (defthm coerce-inverse-2-better
    (equal (coerce (coerce x 'list) 'string)
           (if (stringp x)
               x
             "")))

  (in-theory (disable coerce-inverse-1 coerce-inverse-2)))



(encapsulate
  ()
  (local (in-theory (enable subseq-list)))

  (defthm len-of-subseq-list
    (equal (len (subseq-list x start end))
           (nfix (- end start))))

  (defthm true-listp-subseq-list
    (true-listp (subseq-list x start end))
    :rule-classes :type-prescription))


(encapsulate
  ()
  (local (in-theory (enable subseq)))

  (defthm stringp-of-subseq
    (equal (stringp (subseq x start end))
           (stringp x)))

  (defthm length-of-subseq
    (equal (length (subseq x start end))
           (nfix (- (or end (length x)) start))))

  (defthm len-of-subseq
    (equal (len (subseq x start end))
           (if (stringp x)
               0
             (nfix (- (or end (len x)) start))))))
