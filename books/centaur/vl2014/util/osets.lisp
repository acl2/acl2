; VL 2014 -- VL Verilog Toolkit, 2014 Edition
; Copyright (C) 2008-2015 Centaur Technology
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
; Original author: Jared Davis <jared@centtech.com>

(in-package "VL2014")

; BOZO LIB.  This file should only be locally included.  Eventually move
; all of this stuff into libraries.

(include-book "subsetp-equal")
(include-book "arithmetic")


(defthm setp-of-cdr
  (implies (setp x)
           (setp (cdr x)))
  :hints(("Goal" :in-theory (enable (:ruleset set::primitive-rules)))))


;; We sometimes want to use set-theory routines just for their efficiency,
;; while treating the resulting output sets as if they were just regular lists.
;; Here, we introduce a few theorems for accomodating this.

(defthm string-listp-of-insert
  (implies (and (stringp a)
                (string-listp x))
           (string-listp (insert a x)))
  :hints(("Goal" :in-theory (enable (:ruleset set::primitive-rules)
                                    insert))))

(defthm string-listp-of-intersect-1
  (implies (string-listp x)
           (string-listp (intersect x y)))
  :hints(("Goal" :in-theory (enable (:ruleset set::primitive-rules)
                                    intersect))))

(defthm string-listp-of-intersect-2
  (implies (string-listp y)
           (string-listp (intersect x y)))
  :hints(("Goal"
          :in-theory (disable set::intersect-symmetric
                              string-listp-of-intersect-1)
          :use ((:instance string-listp-of-intersect-1
                           (x y)
                           (y x))
                (:instance set::intersect-symmetric
                           (set::x x)
                           (set::y y))))))

(defthm string-listp-of-difference
  (implies (string-listp x)
           (string-listp (difference x y)))
  :hints(("Goal" :in-theory (enable (:ruleset set::primitive-rules)
                                    difference))))

(defthm string-listp-of-union
  (implies (and (string-listp x)
                (string-listp y))
           (string-listp (union x y)))
  :hints(("Goal" :in-theory (enable (:ruleset set::primitive-rules)
                                    union))))

(defthm string-listp-of-mergesort
  (implies (string-listp x)
           (string-listp (mergesort x))))




(defthm symbol-listp-of-insert
  (implies (and (symbolp a)
                (symbol-listp x))
           (symbol-listp (insert a x)))
  :hints(("Goal" :in-theory (enable (:ruleset set::primitive-rules)
                                    insert))))

(defthm symbol-listp-of-intersect-1
  (implies (symbol-listp x)
           (symbol-listp (intersect x y)))
  :hints(("Goal" :in-theory (enable (:ruleset set::primitive-rules)
                                    intersect))))

(defthm symbol-listp-of-intersect-2
  (implies (symbol-listp y)
           (symbol-listp (intersect x y)))
  :hints(("Goal"
          :in-theory (disable set::intersect-symmetric
                              symbol-listp-of-intersect-1)
          :use ((:instance symbol-listp-of-intersect-1
                           (x y)
                           (y x))
                (:instance set::intersect-symmetric
                           (set::x x)
                           (set::y y))))))

(defthm symbol-listp-of-difference
  (implies (symbol-listp x)
           (symbol-listp (difference x y)))
  :hints(("Goal" :in-theory (enable (:ruleset set::primitive-rules)
                                    difference))))

(defthm symbol-listp-of-union
  (implies (and (symbol-listp x)
                (symbol-listp y))
           (symbol-listp (union x y)))
  :hints(("Goal" :in-theory (enable (:ruleset set::primitive-rules)
                                    union))))

(defthm symbol-listp-of-mergesort
  (implies (symbol-listp x)
           (symbol-listp (mergesort x))))



(defthm promote-member-equal-to-membership
  (implies (and (setp x)
                (syntaxp (not (quotep x))))
           (iff (member-equal a x)
                (in a x)))
  :hints(("Goal" :in-theory (enable set::in-to-member))))

(defthm member-equal-of-intersect
  (iff (member-equal a (intersect x y))
       (and (in a x)
            (in a y))))

(defthm subsetp-equal-of-intersect-1
  (implies (setp x)
           (subsetp-equal (intersect x y) x))
  :hints((set-reasoning)))

(defthm subsetp-equal-of-intersect-2
  (implies (setp y)
           (subsetp-equal (intersect x y) y)))

(defthm member-equal-of-difference
  (iff (member-equal a (difference x y))
       (and (in a x)
            (not (in a y)))))

(defthm member-equal-of-union
  (iff (member-equal a (union x y))
       (or (in a x)
           (in a y))))

(defthm subsetp-equal-of-difference-1
  (implies (setp x)
           (subsetp-equal (difference x y) x))
  :hints((set-reasoning)))

(defthm member-equal-of-mergesort
   (iff (member-equal a (mergesort x))
        (member-equal a (double-rewrite x))))

;; moved to osets
;; (defcong set-equiv equal (mergesort x) 1)

;; moved to osets
;; (defthm mergesort-under-set-equiv
;;   (set-equiv (mergesort x) x))

;; (defthm subsetp-equal-of-mergesort-left
;;   ;; BOZO seems redundant with mergesort-under-set-equiv
;;   (equal (subsetp-equal (mergesort x) y)
;;          (subsetp-equal x y)))

;; (defthm subsetp-equal-of-mergesort-right
;;   ;; BOZO seems redundant with mergesort-under-set-equiv
;;   (equal (subsetp-equal x (mergesort y))
;;          (subsetp-equal x y)))



(defthm subsetp-equal-when-cdr-atom
  (implies (atom (cdr x))
           (equal (subsetp-equal x y)
                  (if (consp x)
                      (if (member-equal (first x) y)
                          t
                        nil)
                    t)))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable subsetp-equal member-equal))))

(defthm subsetp-equal-of-insert
  (equal (subsetp-equal (insert a x) y)
         (and (member-equal a y)
              (subsetp-equal (sfix x) y)))
  :hints(("Goal"
          :induct (insert a x)
          :in-theory (enable insert (:ruleset set::primitive-rules)))))

(defthm subsetp-equal-when-first-two-same-yada-yada
  (implies (and (equal (second x) (first x))
                (subsetp-equal (cdr x) z)
                (consp (cdr x)))
         (subsetp-equal x z)))

(defthm subsetp-equal-of-union
  (equal (subsetp-equal (union x y) z)
         (and (subsetp-equal (sfix x) z)
              (subsetp-equal (sfix y) z)))
  :hints(("Goal"
          :induct (union x y)
          :in-theory (enable union (:ruleset set::primitive-rules)))))



(local (defun set-len (x)
         (if (consp x)
             (if (member-equal (car x) (cdr x))
                 (set-len (cdr x))
               (+ 1 (set-len (cdr x))))
           0)))

(local (defthm set-len-less
         (<= (set-len x)
             (len x))
         :rule-classes ((:rewrite) (:linear))))

(local (defthm set-len-same
         (equal (equal (set-len x) (len x))
                (no-duplicatesp-equal x))))

(local (defthm cardinality-of-mergesort
         (equal (cardinality (mergesort x))
                (set-len x))))

(local (defthm cardinality-is-len
         (implies (setp x)
                  (equal (len x)
                         (cardinality x)))
         :hints(("Goal"
                 :in-theory (enable (:ruleset set::primitive-rules)
                                    cardinality)))))

(defthm no-duplicatesp-equal-by-mergesort
  (equal (equal (len x) (len (mergesort x)))
         (no-duplicatesp-equal x)))

(defthm no-duplicatesp-equal-when-same-length-mergesort
  (implies (equal (len x) (len (mergesort x)))
           (no-duplicatesp-equal x)))

(defthm len-of-mergesort-when-no-duplicatesp-equal
  (implies (no-duplicatesp-equal x)
           (equal (len (mergesort x))
                  (len x))))

(defthm no-duplicatesp-equal-of-append-by-mergesort
  (equal (equal (+ (len x) (len y))
                (len (mergesort (append x y))))
         (no-duplicatesp-equal (append x y)))
  :hints(("Goal"
          :use ((:instance no-duplicatesp-equal-by-mergesort
                           (x (append x y)))))))


(defthm mergesort-of-rev
  (equal (mergesort (rev x))
         (mergesort (double-rewrite x))))

(defthm subset-of-mergesort-when-subsetp-equal
  (implies (setp b)
           (equal (subset (mergesort a) b)
                  (subsetp-equal a (double-rewrite b)))))

(defthm subset-of-union
  (equal (subset (union x y) z)
         (and (subset x z)
              (subset y z))))

(defthm string-listp-of-strip-cdrs-of-insert
  (implies (and (string-listp (strip-cdrs x))
                (stringp (cdr a)))
           (string-listp (strip-cdrs (insert a x))))
  :hints(("Goal" :in-theory (enable (:ruleset set::primitive-rules)))))

(defthm string-listp-of-strip-cdrs-of-mergesort
  (implies (string-listp (strip-cdrs x))
           (string-listp (strip-cdrs (mergesort x))))
  :hints(("Goal" :induct (len x))))

(defthm string-listp-when-subset
  (implies (and (subset x y)
                (string-listp y)
                (setp x))
           (string-listp x))
  :hints(("Goal"
          :induct (len x)
          :in-theory (enable (:ruleset set::primitive-rules)))))

(defthm subset-of-intersect-one
  (implies (or (subset a x)
               (subset b x))
           (subset (intersect a b) x)))

(defthm subset-of-difference-one
  (implies (subset a x)
           (subset (difference a b) x)))


(defthm difference-under-iff
  (iff (difference x y)
       (not (subset x y)))
  :hints(("Goal"
          :use ((:instance set::subset-difference
                           (set::x x)
                           (set::y y)))
          :do-not-induct t
          :in-theory (e/d (empty)
                          (set::subset-difference
                           set::pick-a-point-subset-strategy))
          )))

