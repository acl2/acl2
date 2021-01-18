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


(in-package "VL")

(include-book "centaur/fty/deftypes" :dir :system)
(include-book "../util/defs")
(include-book "../util/printedlist")

(fty::defflexsum partsum-comp
  (:str
   :cond (stringp x)
   :fields ((val :acc-body x :type stringp))
   :ctor-body val)
  (:idx
   :cond (atom x)
   :fields ((val :acc-body x :type integerp))
   :ctor-body val)
  (:range
   :fields ((msb :acc-body (car x) :type integerp)
            (lsb :acc-body (cdr x) :type integerp))
   :ctor-body (cons msb lsb)))

(fty::deflist partsum-elt :elt-type partsum-comp :true-listp t)

(fty::deflist partsumlist :elt-type partsum-elt :true-listp t)

(local (defthm len-of-nthcdr
         (implies (<= (nfix n) (len x))
                  (equal (len (nthcdr n x))
                         (- (len x) (nfix n))))
         :hints(("Goal" :in-theory (enable nthcdr)))))

(define parse-int-from-string ((x stringp)
                               (idx natp "offset")
                               (xlen (equal xlen (length x))))
  :guard (<= idx xlen)
  :returns (mv (val integerp :rule-classes :type-prescription)
               (len natp :rule-classes :type-prescription))
  (b* ((x (string-fix x))
       (xlen (mbe :logic (length x) :exec xlen))
       (idx (lnfix idx))
       ((unless (and (< idx xlen) (eql (char x idx) #\-)))
        (str::parse-nat-from-string x 0 0 idx xlen))
       ((mv val len) (str::parse-nat-from-string x 0 0 (+ 1 idx) xlen)))
    (mv (- val) (+ 1 len)))
  ///
  (local (defthm len-of-take-leading-dec-digit-chars
           (<= (len (str::take-leading-dec-digit-chars x)) (len x))
           :hints(("Goal" :in-theory (enable str::take-leading-dec-digit-chars)))
           :rule-classes :linear))

  (defret parse-int-from-string-len-upper-bound
    (implies (<= (nfix idx) (length (str-fix x)))
             (<= (+ len (nfix idx)) (length (str-fix x))))
    :rule-classes ((:linear :trigger-terms (len)))))


;; (local (defthm listpos-upper-bound
;;          (implies (acl2::sublistp x y)
;;                   (< (acl2::listpos x y) (len y)))
;;          :hints(("Goal" :in-theory (enable acl2::sublistp acl2::listpos)))
;;          :rule-classes :linear))

(local (in-theory (disable (force))))
(local (include-book "arithmetic/top-with-meta" :dir :system))

(local (defthm atom-nthcdr-of-len
         (not (consp (nthcdr (len x) x)))
         :hints(("Goal" :in-theory (enable nthcdr)))))

(local (defthm strpos-fast-upper-bound
         (implies (and (str::strpos-fast x y n xl yl)
                       (<= (nfix n) (nfix yl))
                       (equal yl (length (str-fix y)))
                       (equal xl (length (str-fix x)))
                       (not (equal 0 xl)))
                  (< (str::strpos-fast x y n xl yl) (nfix yl)))
         :hints(("Goal" :in-theory (enable str::strpos-fast)))
         :rule-classes :linear))

(local (defthm strpos-fast-lower-bound
         (implies (str::strpos-fast x y n xl yl)
                  (<= (nfix n) (str::strpos-fast x y n xl yl)))
         :hints(("Goal" :in-theory (enable str::strpos-fast)))
         :rule-classes :linear))


(local (defthmd sublistp-implies-consp
         (implies (acl2::sublistp (cons x y) z)
                  (consp z))
         :rule-classes :forward-chaining))


(define parse-partsum-elt ((idx natp)
                           (x stringp)
                           (xlen (equal xlen (length x))))
  :guard (<= idx xlen)
  :measure (nfix (- (length (str-fix x)) (nfix idx)))
  :returns (elt partsum-elt-p
                :hints(("Goal" :in-theory (disable (:d parse-partsum-elt))
                        :induct <call> :expand (<call>))))
  :guard-hints (("goal" :do-not-induct t
                 :in-theory (e/d (sublistp-implies-consp))))
  :prepwork ((local (in-theory (disable str::strpos-fast-removal
                                        len nth default-+-2 default-cdr))))
  (b* ((x (string-fix x))
       (xlen (mbe :logic (length x) :exec xlen))
       (idx (lnfix idx))
       ((when (mbe :logic (zp (- xlen (nfix idx)))
                   :exec (eql idx xlen)))
        nil)
       ;; Find the first [
       (lbrack-pos (str::strpos-fast "[" x idx 1 xlen))
       ((unless lbrack-pos)
        ;; No left bracket -- the rest of the string is one token
        (list (partsum-comp-str (subseq x idx nil))))
       ((mv int1 int1-len) (parse-int-from-string x (+ 1 lbrack-pos) xlen))
       ((when (eql 0 int1-len))
        (cons (partsum-comp-str (subseq x idx (+ 1 lbrack-pos)))
              (parse-partsum-elt (+ 1 lbrack-pos) x xlen)))
       (next-idx (+ 1 lbrack-pos int1-len))
       ((when (>= next-idx xlen))
        (list (partsum-comp-str (subseq x idx nil))))
       ((when (eql (char x next-idx) #\]))
        (list* (partsum-comp-str (subseq x idx lbrack-pos))
               (partsum-comp-idx int1)
               (parse-partsum-elt (+ 1 next-idx) x xlen)))
       ((unless (eql (char x next-idx) #\:))
        (cons (partsum-comp-str (subseq x idx next-idx))
              (parse-partsum-elt next-idx x xlen)))
       ((mv int2 int2-len) (parse-int-from-string x (+ 1 next-idx) xlen))
       ((when (eql 0 int2-len))
        (cons (partsum-comp-str (subseq x idx (+ 1 next-idx)))
              (parse-partsum-elt (+ 1 next-idx) x xlen)))
       (next-idx (+ 1 next-idx int2-len))
       ((when (>= next-idx xlen))
        (list (partsum-comp-str (subseq x idx nil))))
       ((unless (eql (char x next-idx) #\]))
        (cons (partsum-comp-str (subseq x idx next-idx))
              (parse-partsum-elt next-idx x xlen))))
    (list* (partsum-comp-str (subseq x idx lbrack-pos))
           (partsum-comp-range int1 int2)
           (parse-partsum-elt (+ 1 next-idx) x xlen))))

(define parse-partsumlist ((x string-listp))
  :returns (partsums partsumlist-p)
  (if (atom x)
      nil
    (cons (parse-partsum-elt 0 (car x) (length (string-fix (car x))))
          (parse-partsumlist (cdr x)))))


(define join-partsum-ranges ((left-msb integerp)
                             (left-lsb integerp)
                             (right-msb integerp)
                             (right-lsb integerp))
  :returns (mv ok
               (msb integerp :rule-classes :type-prescription)
               (lsb integerp :rule-classes :type-prescription))
  ;; Yucky cases
  (b* ((left-msb (lifix left-msb))
       (left-lsb (lifix left-lsb))
       (right-msb (lifix right-msb))
       (right-lsb (lifix right-lsb))
       (decreasingp (or (> left-msb left-lsb)
                        (and (eql left-msb left-lsb)
                             (or (> right-msb right-lsb)
                                 (and (eql right-msb right-lsb)
                                      (> left-msb right-msb))))))
       ((unless (if decreasingp
                    (and (>= left-msb left-lsb)
                         (>= right-msb right-lsb))
                  (and (<= left-msb left-lsb)
                       (<= right-msb right-lsb))))
        ;; inconsistent range directions
        (mv nil 0 0))
       ((when (if decreasingp
                  (or (> left-lsb (+ 1 right-msb))
                      (> right-lsb (+ 1 left-msb)))
                (or (< (+ 1 left-lsb) right-msb)
                    (< (+ 1 right-lsb) left-msb))))
        ;; nonempty gap between the ranges
        (mv nil 0 0)))
    (if decreasingp
        (mv t (max left-msb right-msb) (min left-lsb right-lsb))
      (mv t (min left-msb right-msb) (max left-lsb right-lsb))))
  ///
  (defret join-partsum-ranges-correct
    (implies (and ok
                  (integerp idx)
                  (or (and (<= (ifix left-msb) idx)
                           (<= idx (ifix left-lsb)))
                      (and (<= idx (ifix left-msb))
                           (<= (ifix left-lsb) idx))
                      (and (<= (ifix right-msb) idx)
                           (<= idx (ifix right-lsb)))
                      (and (<= idx (ifix right-msb))
                           (<= (ifix right-lsb) idx))))
             (or (and (<= msb idx) (<= idx lsb))
                 (and (<= idx msb) (<= lsb idx))))
    :hints(("Goal" :in-theory (disable ifix)))
    :rule-classes nil))

(define join-partsum-elts ((x partsum-elt-p)
                           (y partsum-elt-p))
  :measure (len x)
  :returns (mv ok (new-elt partsum-elt-p))
  (b* (((when (atom x))
        ;; ok if both empty
        (mv (atom y) nil))
       ((when (atom y)) (mv nil nil))
       (x1 (partsum-comp-fix (car x)))
       (y1 (partsum-comp-fix (car y)))
       ((when (equal x1 y1))
        (b* (((mv ok rest) (join-partsum-elts (cdr x) (cdr y))))
          (if ok
              (mv ok (cons x1 rest))
            (mv nil nil))))
       ((when (or (partsum-comp-case x1 :str)
                  (partsum-comp-case y1 :str)))
        ;; unequal string components
        (mv nil nil))
       ((unless (equal (partsum-elt-fix (cdr x))
                       (partsum-elt-fix (cdr y))))
        ;; more than one different element
        (mv nil nil))
       ((mv xmsb xlsb)
        (partsum-comp-case x1
          :idx (mv x1.val x1.val)
          :range (mv x1.msb x1.lsb)
          :otherwise (mv nil nil)))
       ((mv ymsb ylsb)
        (partsum-comp-case y1
          :idx (mv y1.val y1.val)
          :range (mv y1.msb y1.lsb)
          :otherwise (mv nil nil)))
       ((mv ok new-msb new-lsb)
        (join-partsum-ranges xmsb xlsb ymsb ylsb))
       ((unless ok)
        ;; different non-joinable selects
        (mv nil nil)))
    (mv t (cons (if (eql new-msb new-lsb)
                    (partsum-comp-idx new-msb)
                  (partsum-comp-range new-msb new-lsb))
                (partsum-elt-fix (cdr x))))))

(define summarize-partsumlist1 ((first partsum-elt-p)
                                (x partsumlist-p))
  :returns (new-x partsumlist-p)
  (b* (((when (atom x))
        (list (partsum-elt-fix first)))
       ((mv ok new-elt) (join-partsum-elts first (car x)))
       ((when ok)
        (summarize-partsumlist1 new-elt (cdr x))))
    (cons (partsum-elt-fix first)
          (summarize-partsumlist1 (car x) (cdr x))))
  ///
  (defret len-of-summarize-partsumlist1
    (<= (len new-x) (+ 1 (len x)))
    :rule-classes :linear))

(define summarize-partsumlist ((x partsumlist-p))
  :returns (summary partsumlist-p)
  :measure (len x)
  (b* (((when (atom x)) nil)
       (new-x (summarize-partsumlist1 (car x) (cdr x)))
       ((when (eql (len x) (len new-x)))
        new-x))
    (summarize-partsumlist new-x)))



(define partsum-elt< ((x partsum-elt-p)
                      (y partsum-elt-p))
  ;; Sorts by the strings inside x and y, then the index/range elements.
  (b* (((when (atom x))
        (not (atom y)))
       ((when (atom y)) nil)
       (x1 (car x))
       (y1 (car y))
       ((when (partsum-comp-equiv x1 y1))
        (partsum-elt< (cdr x) (cdr y))))
       ;; ranking: string < idx/range
       ;; but idx, range subrankings are lower priority than string compares.
    (partsum-comp-case x1
      :str (partsum-comp-case y1
             :str (<< x1.val y1.val)
             :otherwise t)
      :idx (partsum-comp-case y1
             :str nil
             :idx (or (partsum-elt< (cdr x) (cdr y))
                      (and (partsum-elt-equiv (cdr x) (cdr y))
                           (< x1.val y1.val)))
             :range (or (partsum-elt< (cdr x) (cdr y))
                        (and (partsum-elt-equiv (cdr x) (cdr y))
                             (< x1.val y1.msb))))
      :range (partsum-comp-case y1
               :str nil
               :idx (or (partsum-elt< (cdr x) (cdr y))
                        (and (partsum-elt-equiv (cdr x) (cdr y))
                             (<= x1.msb y1.val)))
               :range (or (partsum-elt< (cdr x) (cdr y))
                          (and (partsum-elt-equiv (cdr x) (cdr y))
                               (or (< x1.msb y1.msb)
                                   (and (eql x1.msb y1.msb)
                                        (< x1.lsb y1.lsb))))))))
  ///

  (local (in-theory (disable (:d partsum-elt<))))

  (fty::deffixequiv partsum-elt<)

  (defthm partsum-elt<-irrefl
    (not (partsum-elt< x x))
    :hints (("goal" :induct (partsum-elt< x x)
             :expand ((partsum-elt< x x)))))

  (defthm partsum-elt<-asymm
    (implies (partsum-elt< x y)
             (not (partsum-elt< y x)))
    :hints (("goal" :induct (partsum-elt< x y)
             :expand ((partsum-elt< x y)
                      (partsum-elt< y x)))))

  (defthm partsum-elt-trichotomy
    (implies (and (not (equal (partsum-elt-fix x)
                              (partsum-elt-fix y)))
                  (not (partsum-elt< x y)))
             (partsum-elt< y x))
    :hints (("goal" :induct (partsum-elt< x y)
             :expand ((partsum-elt< x y)
                      (partsum-elt< y x)
                      (partsum-elt-fix x)
                      (partsum-elt-fix y))
             :in-theory (disable (:d partsum-elt<)))
            (and stable-under-simplificationp
                 '(:in-theory (e/d (partsum-comp-fix-when-idx
                                    partsum-comp-fix-when-range
                                    partsum-comp-fix-when-str)
                                   (partsum-comp-range-of-fields
                                    partsum-comp-str-of-fields
                                    partsum-comp-idx-of-fields))))))

  (defthm partsum-elt<-transitive
    (implies (and (partsum-elt< x y)
                  (partsum-elt< y z))
             (partsum-elt< x z))
    :hints (("goal" :induct t
             :expand ((partsum-elt< x y)
                      (partsum-elt< y z)
                      (partsum-elt< x z)))))

  (defthm partsum-elt<-transitive-inv
    (implies (and (not (partsum-elt< x y))
                  (not (partsum-elt< y z)))
             (not (partsum-elt< x z)))
    :hints (("goal" :use ((:instance partsum-elt-trichotomy
                           (y x) (x y))
                          (:instance partsum-elt-trichotomy
                           (y y) (x z))
                          (:instance partsum-elt-trichotomy
                           (y z) (x x)))
             :in-theory (disable partsum-elt-trichotomy)
             :do-not-induct t))))


(acl2::defsort partsumlist-sort (x)
  :comparablep partsum-elt-p
  :comparable-listp partsumlist-p
  :true-listp t
  :compare< partsum-elt<)

(defmacro rlist (&rest args)
  (list-macro (reverse args)))

(define partsum-elt-to-printedlist ((x partsum-elt-p))
  :returns (print vl-printedlist-p)
  (if (atom x)
      nil
    (rlist (b* ((x1 (car x)))
             (partsum-comp-case x1
               :str x1.val
               :idx (rlist "[" (str::intstr x1.val) "]")
               :range (rlist "[" (str::intstr x1.msb) ":" (str::intstr x1.lsb) "]")))
           (partsum-elt-to-printedlist (cdr x)))))

(define partsum-elt-to-string ((x partsum-elt-p))
  :returns (print stringp :rule-classes :type-prescription)
  (vl-printedlist->string (partsum-elt-to-printedlist x)))

(define partsumlist-to-strings ((x partsumlist-p))
  :returns (strings string-listp)
  (if (atom x)
      nil
    (cons (partsum-elt-to-string (car x))
          (partsumlist-to-strings (cdr x)))))


(define summarize-parts ((x string-listp))
  :returns (new-x string-listp)
  (b* ((parts (partsumlist-sort (parse-partsumlist x)))
       (new-parts (summarize-partsumlist parts)))
    (partsumlist-to-strings new-parts)))
