; Defsort - Defines a stable sort when given a comparison function
; Copyright (C) 2008 Centaur Technology
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

(in-package "ACL2")
(include-book "std/lists/list-defuns" :dir :system)
(include-book "std/lists/abstract" :dir :system)
(include-book "tools/save-obligs" :dir :system)
(include-book "misc/without-waterfall-parallelism" :dir :system)
(local (include-book "std/lists/take" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))
(local (include-book "std/lists/list-fix" :dir :system))
(local (include-book "std/lists/revappend" :dir :system))
(local (include-book "std/lists/equiv" :dir :system))
(local (include-book "std/lists/no-duplicatesp" :dir :system))
(local (include-book "ihs/ihs-lemmas" :dir :system))
(local (in-theory (disable floor mod take nthcdr)))

(defthmd comparable-mergesort-admission-nthcdr
  (implies (consp (cdr x))
           (< (len (nthcdr (floor (len x) 2) x))
              (len x)))
  :rule-classes :linear)

(defthmd comparable-mergesort-admission-take
  (implies (consp (cdr x))
           (< (len (take (floor (len x) 2) x))
              (len x)))
  :rule-classes :linear)

(defthmd fast-mergesort-admission-1
  (implies (and (not (zp len))
                (not (equal len 1)))
           (< (nfix (+ len (- (ash len -1))))
              (nfix len)))
  :rule-classes :linear)

(defthmd fast-mergesort-admission-2
  (implies (and (not (zp len))
                (not (equal len 1)))
           (< (nfix (ash len -1))
              (nfix len)))
  :rule-classes :linear)

(local (in-theory (disable ash)))

(local (defthm ash-neg-1
         (implies (natp x)
                  (equal (ash x -1)
                         (floor x 2)))
         :hints(("Goal" :in-theory (enable ash*)))))

(encapsulate
 (((comparablep *) => *)
  ((compare< * *) => *))

 (local (defun comparablep (x)
          (declare (xargs :guard t))
          (natp x)))

 (local (defun compare< (x y)
          (declare (xargs :guard (and (comparablep x)
                                      (comparablep y))))
          (< x y)))

 (defthm type-of-comparablep
   (or (equal (comparablep x) t)
       (equal (comparablep x) nil))
   :rule-classes :type-prescription)

 (defthm type-of-compare<
   (or (equal (compare< x y) t)
       (equal (compare< x y) nil))
   :rule-classes :type-prescription)

 (defthm compare<-transitive
   (implies (and (compare< x y)
                 (compare< y z))
            (compare< x z))))




(defund comparable-listp (x)
  (declare (xargs :guard t))
  (if (consp x)
      (and (comparablep (car x))
           (comparable-listp (cdr x)))
    (element-list-final-cdr-p x)))

(local
 (progn
   (defthm comparable-listp-when-not-consp
     (implies (not (consp x))
              (equal (comparable-listp x)
                     (element-list-final-cdr-p x)))
     :hints(("Goal" :in-theory (enable comparable-listp))))

   (defthm comparable-listp-of-cons
     (equal (comparable-listp (cons a x))
            (and (comparablep a)
                 (comparable-listp x)))
     :hints(("Goal" :in-theory (enable comparable-listp))))

   (defthm comparable-listp-of-take
     (implies (and (force (comparable-listp x))
                   (force (<= (nfix n) (len x))))
              (comparable-listp (take n x)))
     :hints(("Goal"
             :in-theory (enable take)
             :induct (take n x))))

   (defthm comparable-listp-of-nthcdr
     (implies (force (comparable-listp x))
              (comparable-listp (nthcdr n x)))
     :hints(("Goal"
             :in-theory (enable (:induction nthcdr))
             :induct (nthcdr n x)
             :expand ((nthcdr n x)))))

   (defthm comparable-listp-of-cdr
     (implies (comparable-listp x)
              (comparable-listp (cdr x)))
     :hints(("Goal" :in-theory (disable (comparable-listp)))))

   (defthm comparablep-of-car
     (implies (comparable-listp x)
              (equal (comparablep (car x))
                     (or (consp x)
                         (comparablep nil)))))))




(defund comparable-merge (x y)
  (declare (xargs :measure (+ (len x)
                              (len y))
                  :guard (and (comparable-listp x)
                              (comparable-listp y))
                  :verify-guards nil))
  (cond ((atom x)
         y)
        ((atom y)
         x)
        ((compare< (car y) (car x))
         (cons (car y) (comparable-merge x (cdr y))))
        (t
         ;; Either (car x) < (car y) or they are equivalent.  In either case,
         ;; for stability, take (car x) first.
         (cons (car x) (comparable-merge (cdr x) y)))))

(verify-guards comparable-merge)

(defthm len-of-comparable-merge
  (equal (len (comparable-merge x y))
         (+ (len x) (len y)))
  :hints(("Goal" :in-theory (enable comparable-merge))))


(defthm comparable-listp-of-comparable-merge
  (implies (and (force (comparable-listp x))
                (force (comparable-listp y)))
           (equal (comparable-listp (comparable-merge x y))
                  t))
  :hints(("Goal" :in-theory (enable comparable-merge))))

(local
 (progn
   (defthm comparable-merge-when-not-consp-left
     (implies (not (consp x))
              (equal (comparable-merge x y)
                     y))
     :hints(("Goal" :in-theory (enable comparable-merge))))

   (defthm comparable-merge-when-not-consp-right
     (implies (not (consp y))
              (equal (comparable-merge x y)
                     (if (consp x)
                         x
                       y)))
     :hints(("Goal" :in-theory (enable comparable-merge))))

   (in-theory (disable floor-bounded-by-/
                       take-of-len-free
                       true-listp-when-element-list-p-rewrite))))







(defund comparable-merge-tr (x y acc)
  (declare (xargs :measure (+ (len x)
                              (len y))
                  :guard (and (comparable-listp x)
                              (comparable-listp y))
                  :verify-guards nil))
  (cond ((atom x)
         (revappend-without-guard acc y))
        ((atom y)
         (revappend-without-guard acc x))
        ((compare< (car y) (car x))
         (comparable-merge-tr x (cdr y) (cons (car y) acc)))
        (t
         ;; Either (car x) < (car y) or they are equivalent.  In either case,
         ;; for stability, take (car x) first.
         (comparable-merge-tr (cdr x) y (cons (car x) acc)))))

(verify-guards comparable-merge-tr)

(local
 (encapsulate
   ()
   (local (defthm comparable-merge-tr-removal-lemma
            (equal (comparable-merge-tr x y acc)
                   (revappend acc (comparable-merge x y)))
            :hints(("Goal"
                    :induct (comparable-merge-tr x y acc)
                    :in-theory (enable comparable-merge-tr
                                       comparable-merge
                                       revappend)))))

   (defthm comparable-merge-tr-removal
     (equal (comparable-merge-tr x y nil)
            (comparable-merge x y)))))





;; (encapsulate
;;  ()
;;  (defund first-half-len (len)
;;    (declare (xargs :guard (natp len)))
;;    (floor (nfix len) 2))

;;  (defthm natp-of-first-half-len
;;    (natp (first-half-len len))
;;    :rule-classes :type-prescription)

;;  (defthm first-half-len-less
;;    (implies (< 0 len)
;;             (< (first-half-len len) len))
;;    :rule-classes (:rewrite :linear)
;;    :hints(("Goal" :in-theory (enable first-half-len))))

;;  (defthm first-half-len-zero
;;    (equal (equal (first-half-len len) 0)
;;           (or (zp len)
;;               (= len 1)))
;;    :hints(("Goal" :in-theory (enable first-half-len))))

;;  (defund second-half-len (len)
;;    (declare (xargs :guard (natp len)))
;;    (- (nfix len) (floor (nfix len) 2)))

;;  (defthm natp-of-second-half-len
;;    (natp (second-half-len len))
;;    :hints(("Goal" :in-theory (enable second-half-len)))
;;    :rule-classes :type-prescription)

;;  (defthm second-half-len-less
;;    (implies (and (natp len)
;;                  (not (= 0 len))
;;                  (not (= 1 len)))
;;             (< (second-half-len len) len))
;;    :rule-classes (:rewrite :linear)
;;    :hints(("Goal" :in-theory (enable second-half-len))))

;;  (defthm second-half-len-zero
;;    (equal (equal (second-half-len len) 0)
;;           (zp len))
;;    :hints(("Goal" :in-theory (enable second-half-len zp))))

;;  (defthm first-plus-second-half
;;    (implies (natp len)
;;             (equal (+ (first-half-len len)
;;                       (second-half-len len))
;;                    len))
;;    :hints(("Goal" :in-theory (enable first-half-len second-half-len)))))


;; (defund comparable-mergesort-spec2 (x)
;;   (declare (xargs :measure (len x)
;;                   :hints(("Goal"
;;                           :use ((:instance comparable-mergesort-spec-admission))
;;                           :in-theory (enable first-half-len)))))
;;   (cond ((atom x)
;;          nil)
;;         ((atom (cdr x))
;;          (list (car x)))
;;         (t
;;          (let ((half (first-half-len (len x))))
;;            (comparable-merge
;;             (comparable-mergesort-spec2 (take half x))
;;             (comparable-mergesort-spec2 (nthcdr half x)))))))

;; (defthm true-listp-of-comparable-merge
;;   (implies (and (true-listp y)
;;                 (true-listp x))
;;            (true-listp (comparable-merge x y)))
;;   :rule-classes :type-prescription
;;   :hints(("Goal" :in-theory (enable comparable-merge))))

;; (defthm true-listp-of-comparable-mergesort-spec2
;;   (true-listp (comparable-mergesort-spec2 x))
;;   :rule-classes :type-prescription
;;   :hints(("Goal" :in-theory (enable comparable-mergesort-spec2))))

;; (defthm len-of-comparable-mergesort-spec2
;;   (equal (len (comparable-mergesort-spec2 x))
;;          (len x))
;;   :hints(("Goal" :in-theory (enable comparable-mergesort-spec2))))

;; (defthm consp-of-comparable-mergesort-spec2
;;   (equal (consp (comparable-mergesort-spec2 x))
;;          (consp x))
;;   :hints(("Goal" :in-theory (enable comparable-mergesort-spec2))))



;; (defthm comparable-mergesort-spec-redefinition
;;   (equal (comparable-mergesort-spec x)
;;          (comparable-mergesort-spec2 x))
;;   :hints(("Goal" :in-theory (enable comparable-mergesort-spec
;;                                     comparable-mergesort-spec2
;;                                     first-half-len))))

;; (defthm comparable-listp-of-comparable-mergesort-spec2
;;   (implies (force (comparable-listp x))
;;            (comparable-listp (comparable-mergesort-spec2 x)))
;;   :hints(("Goal" :in-theory (e/d (comparable-mergesort-spec2)
;;                                  ((comparable-listp))))))

;; (defthm comparable-listp-of-comparable-mergesort-spec
;;   (implies (force (comparable-listp x))
;;            (comparable-listp (comparable-mergesort-spec x))))




; Refinement 2.  Our efficient sorting routine only tries to sort the first n
; elements of the list.  This allows us to implicitly partition the list
; without having to do any consing.


;; (defun comparable-mergesort-spec3 (x len)
;;   (declare (xargs :guard (and (comparable-listp x)
;;                               (<= len (len x)))
;;                   :measure (nfix len)
;;                   :verify-guards nil)
;;            (type integer len))

;; ; This computes (comparable-mergesort-spec (take len x)).

;;   (cond ((zp len)
;;          nil)
;;         ((eql len 1)
;;          (list (car x)))
;;         (t
;;          (let* ((len1  (ash len -1))
;;                 (len2  (- len len1))
;;                 (part1 (comparable-mergesort-spec3 x len1))
;;                 (part2 (comparable-mergesort-spec3 (nthcdr len1 x) len2)))
;;            (comparable-merge part1 part2)))))

;; (encapsulate
;;  ()
;;  ;; (local (defthm +-collect-consts
;;  ;;          (implies (syntaxp (and (quotep a) (quotep b)))
;;  ;;                   (equal (+ a b c)
;;  ;;                          (+ (+ a b) c)))))

;;  ;; (local (defthm +-collect-consts
;;  ;;          (implies (syntaxp (and (quotep a) (quotep b)))
;;  ;;                   (equal (+ a b c)
;;  ;;                          (+ (+ a b) c)))))

;;  (local (defthm take-of-cdr
;;           (equal (take n (cdr x))
;;                  (cdr (take (+ 1 n) x)))
;;           :hints(("Goal" :expand ((take (+ 1 n) x))))))

;;  (local (defthm crock
;;           (implies (and (natp len1)
;;                         (natp len2))
;;                    (equal (NTHCDR len1 (TAKE (+ len1 len2) X))
;;                           (TAKE len2 (NTHCDR len1 X))))
;;           :hints(("Goal" :in-theory (e/d (take nthcdr)
;;                                          (open-small-nthcdr
;;                                           nthcdr-of-cdr))
;;                   :induct (nthcdr len1 x)))
;;           :rule-classes nil))

;;  (local (defthm nthcdr-of-take
;;           (implies (and (natp len1)
;;                         (natp len2)
;;                         (<= len1 len2))
;;                    (equal (nthcdr len1 (take len2 x))
;;                           (take (- len2 len1) (nthcdr len1 x))))
;;           :hints (("goal" :use ((:instance crock
;;                                  (len2 (- len2 len1))))))))

;;  ;; (local (defthm crock2
;;  ;;          (implies (and (natp len)
;;  ;;                        (<= len (len x)))
;;  ;;                   (equal (NTHCDR (FIRST-HALF-LEN LEN) (TAKE LEN X))
;;  ;;                          (TAKE (SECOND-HALF-LEN LEN)
;;  ;;                                (NTHCDR (FIRST-HALF-LEN LEN) X))))
;;  ;;          :hints(("Goal"
;;  ;;                  :in-theory (disable crock)
;;  ;;                  :use ((:instance crock
;;  ;;                                   (len1 (first-half-len len))
;;  ;;                                   (len2 (second-half-len len))))))))

;;  (local (defthm crock3
;;           (implies (< 1 (len x))
;;                    (consp (cdr x)))))

;;  (local (in-theory (disable nthcdr-of-nthcdr)))
;;  (local (in-theory (enable floor-bounds)))

;;  (defthm comparable-mergesort-spec3-redefinition
;;    (implies (and (<= len (len x))
;;                  (natp len))
;;             (equal (comparable-mergesort-spec3 x len)
;;                    (comparable-mergesort-spec (take len x))))
;;    :hints(("Goal"
;;            :do-not '(generalize eliminate-destructors)
;;            :induct (comparable-mergesort-spec3 x len)
;;            :in-theory (disable (:d comparable-mergesort-spec3))
;;            :expand ((comparable-mergesort-spec (take len x))
;;                     (:free (a b) (comparable-mergesort-spec (cons a b)))
;;                     (comparable-mergesort-spec3 x len)
;;                     (comparable-mergesort-spec3 x 1)
;;                     (comparable-mergesort-spec3 x 0))))))


; Refinement 3.  We now add fixnum and integer declarations, in order to make
; the arithmetic faster.

(defund fast-comparable-mergesort-fixnums (x len)
  (declare (xargs :guard (and (comparable-listp x)
                              (natp len)
                              (<= len (len x)))
                  :measure (nfix len)
                  :verify-guards nil)
           (type (signed-byte 30) len))
  (cond ((mbe :logic (zp len)
              :exec (eql (the (signed-byte 30) len) 0))
         nil)

        ((eql (the (signed-byte 30) len) 1)
         (list (car x)))

        (t
         (let* ((len1  (the (signed-byte 30)
                         (ash (the (signed-byte 30) len) -1)))
                (len2  (the (signed-byte 30)
                         (- (the (signed-byte 30) len)
                            (the (signed-byte 30) len1))))
                (part1 (fast-comparable-mergesort-fixnums x len1))
                (part2 (fast-comparable-mergesort-fixnums (rest-n len1 x) len2)))
           (comparable-merge-tr part1 part2 nil)))))


(local
 (defthm comparable-listp-of-fast-comparable-mergesort-fixnums
   (implies (and (<= len (len x))
                 (force (comparable-listp x)))
            (comparable-listp (fast-comparable-mergesort-fixnums x len)))
   :hints(("Goal" :in-theory (enable fast-comparable-mergesort-fixnums)))))


(without-waterfall-parallelism
(def-saved-obligs fast-comparable-mergesort-fixnums-guards
  :proofs ((fast-comparable-mergesort-fixnums-guards))
  (verify-guards fast-comparable-mergesort-fixnums))
)


(defmacro mergesort-fixnum-threshold () 536870912)


(defund fast-comparable-mergesort-integers (x len)
  (declare (xargs :guard (and (comparable-listp x)
                              (natp len)
                              (<= len (len x)))
                  :measure (nfix len)
                  :verify-guards nil)
           (type integer len))
  (cond ((mbe :logic (zp len)
              :exec (eql (the integer len) 0))
         nil)

        ((eql (the integer len) 1)
         (list (car x)))

        (t
         (let* ((len1  (the integer (ash (the integer len) -1)))
                (len2  (the integer
                         (- (the integer len) (the integer len1))))
                (part1 (if (< (the integer len1) (mergesort-fixnum-threshold))
                           (fast-comparable-mergesort-fixnums x len1)
                         (fast-comparable-mergesort-integers x len1)))
                (part2 (if (< (the integer len2) (mergesort-fixnum-threshold))
                           (fast-comparable-mergesort-fixnums (rest-n len1 x) len2)
                         (fast-comparable-mergesort-integers (rest-n len1 x) len2))))
           (comparable-merge-tr part1 part2 nil)))))

(local
 (defthm comparable-listp-of-fast-comparable-mergesort-integers
   (implies (and (<= len (len x))
                 (force (comparable-listp x)))
            (comparable-listp (fast-comparable-mergesort-integers x len)))
   :hints(("Goal" :in-theory (e/d ((:i fast-comparable-mergesort-integers))
                                  ((force)))
           :induct (fast-comparable-mergesort-integers x len)
           :expand ((fast-comparable-mergesort-integers x len)
                    (fast-comparable-mergesort-integers x 1))))))


(without-waterfall-parallelism
(encapsulate
  ()
  (local (defthm crock
           (equal (fast-comparable-mergesort-fixnums x len)
                  (fast-comparable-mergesort-integers x len))
           :hints(("Goal" :in-theory (e/d (fast-comparable-mergesort-integers
                                           fast-comparable-mergesort-fixnums))))))

  (def-saved-obligs fast-comparable-mergesort-integers-guards
    :proofs ((fast-comparable-mergesort-integers-guards))
    (verify-guards fast-comparable-mergesort-integers)))
)


(defund comparable-mergesort (x)
  (declare (xargs :measure (len x)
                  :guard (comparable-listp x)
                  :verify-guards nil))
  (mbe :logic (cond ((atom x)
                     nil)
                    ((atom (cdr x))
                     (list (car x)))
                    (t
                     (let ((half (floor (len x) 2)))
                       (comparable-merge
                        (comparable-mergesort (take half x))
                        (comparable-mergesort (nthcdr half x))))))
       :exec (let ((len (len x)))
               (if (< len (mergesort-fixnum-threshold))
                   (fast-comparable-mergesort-fixnums x len)
                 (fast-comparable-mergesort-integers x len)))))


;; We now establish that sorting preserves the duplicities of elements.  In
;; other words, the output is a permutation of its input.
(local
 (defthm duplicity-of-pieces
   (implies (<= (nfix n) (len x))
            (equal (+ (duplicity a (nthcdr n x))
                      (duplicity a (take n x)))
                   (duplicity a x)))
   :hints(("Goal" :in-theory (enable take nthcdr)))))

(defthm duplicity-of-comparable-merge
  (equal (duplicity a (comparable-merge x y))
         (+ (duplicity a x)
            (duplicity a y)))
  :hints(("Goal" :in-theory (enable comparable-merge))))

(defthm duplicity-of-comparable-mergesort
  (equal (duplicity a (comparable-mergesort x))
         (duplicity a x))
  :hints(("Goal" :in-theory (e/d (comparable-mergesort
                                  floor-bounded-by-/)
                                 (len)))))


(defthm true-listp-of-comparable-merge
  (implies (and (true-listp y)
                (true-listp x))
           (true-listp (comparable-merge x y)))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable comparable-merge))))

(defthm true-listp-of-comparable-mergesort
  (true-listp (comparable-mergesort x))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable comparable-mergesort))))

(defthm len-of-comparable-mergesort
  (equal (len (comparable-mergesort x))
         (len x))
  :hints(("Goal" :in-theory (e/d ((:i comparable-mergesort)
                                  floor-bounded-by-/)
                                 (take nthcdr))
          :induct (comparable-mergesort x)
          :expand ((comparable-mergesort x)))))

(defthm consp-of-comparable-mergesort
  (equal (consp (comparable-mergesort x))
         (consp x))
  :hints(("Goal" :in-theory (e/d ((:i comparable-mergesort))
                                 (take nthcdr))
          :induct (comparable-mergesort x)
          :expand ((comparable-mergesort x)))))

(defthm comparable-listp-of-comparable-mergesort
  (implies (force (comparable-listp x))
           (comparable-listp (comparable-mergesort x)))
  :hints(("Goal" :in-theory (e/d ((:i comparable-mergesort)
                                  floor-bounded-by-/)
                                 ((comparable-listp)))
          :induct (comparable-mergesort x)
          :expand ((comparable-mergesort x)))))

(defthm comparable-mergesort-of-list-fix
  (equal (comparable-mergesort (list-fix x))
         (comparable-mergesort x))
  :hints(("Goal"
          :in-theory (e/d (comparable-mergesort))
          :induct (comparable-mergesort x)
          :expand ((comparable-mergesort (list-fix x))))))


(local
 (encapsulate
   ()
   ;; (local (defthm +-collect-consts
   ;;          (implies (syntaxp (and (quotep a) (quotep b)))
   ;;                   (equal (+ a b c)
   ;;                          (+ (+ a b) c)))))

   ;; (local (defthm +-collect-consts
   ;;          (implies (syntaxp (and (quotep a) (quotep b)))
   ;;                   (equal (+ a b c)
   ;;                          (+ (+ a b) c)))))

   (local (defthm take-of-cdr
            (equal (take n (cdr x))
                   (cdr (take (+ 1 n) x)))
            :hints(("Goal" :expand ((take (+ 1 n) x))))))

   (local (defthm crock
            (implies (and (natp len1)
                          (natp len2))
                     (equal (NTHCDR len1 (TAKE (+ len1 len2) X))
                            (TAKE len2 (NTHCDR len1 X))))
            :hints(("Goal" :in-theory (e/d (take nthcdr)
                                           (open-small-nthcdr
                                            nthcdr-of-cdr))
                    :induct (nthcdr len1 x)))
            :rule-classes nil))

   (local (defthm nthcdr-of-take
            (implies (and (natp len1)
                          (natp len2)
                          (<= len1 len2))
                     (equal (nthcdr len1 (take len2 x))
                            (take (- len2 len1) (nthcdr len1 x))))
            :hints (("goal" :use ((:instance crock
                                   (len2 (- len2 len1))))))))

   (local (in-theory (disable take-of-cdr)))

   (local (defthm crock3
            (implies (< 1 (len x))
                     (consp (cdr x)))))

   (local (in-theory (disable nthcdr-of-nthcdr)))
   (local (in-theory (enable floor-bounded-by-/)))

   (defthm fast-comparable-mergesort-fixnums-redefinition
     (equal (fast-comparable-mergesort-fixnums x len)
            (comparable-mergesort (take len x)))
     :hints(("Goal"
             :in-theory (e/d ((:i fast-comparable-mergesort-fixnums)
                              comparable-mergesort))
             :induct (fast-comparable-mergesort-fixnums x len)
             :expand ((fast-comparable-mergesort-fixnums x len)
                      (fast-comparable-mergesort-fixnums x 1)
                      (fast-comparable-mergesort-fixnums x 0)
                      (comparable-mergesort (take len x))))))

   (defthm fast-comparable-mergesort-integers-redefinition
     (equal (fast-comparable-mergesort-integers x len)
            (comparable-mergesort (take len x)))
     :hints(("Goal"
             :in-theory (e/d ((:i fast-comparable-mergesort-integers)
                              comparable-mergesort))
             :induct (fast-comparable-mergesort-integers x len)
             :expand ((fast-comparable-mergesort-integers x len)
                      (fast-comparable-mergesort-integers x 1)
                      (fast-comparable-mergesort-integers x 0)
                      (comparable-mergesort (take len x))))))))

(defthm fast-comparable-mergesort-fixnums-of-len-is-spec
  (equal (fast-comparable-mergesort-fixnums x (len x))
         (comparable-mergesort x)))

(defthm fast-comparable-mergesort-integers-of-len-is-spec
  (equal (fast-comparable-mergesort-integers x (len x))
         (comparable-mergesort x)))

(without-waterfall-parallelism
(def-saved-obligs comparable-mergesort-guard
  :proofs ((comparable-mergesort-guard
            :hints ((and stable-under-simplificationp
                         '(:expand ((comparable-mergesort x)))))))
  (verify-guards comparable-mergesort))
)




; We now establish that the sort returns produces an ordered list.  There may
; be "equivalent" elements in the list, where we simultaneously have:
;
;    (compare< a b) = nil
;    (compare< b a) = nil
;
; For instance, when sorting integers with <, if there are any duplicates in
; the input list then we will have this situation.  So we only want to ensure
; that, for every A which preceeds B in the list, either A < B, or A === B in
; the above sense.

(defund comparable-orderedp (x)
  (declare (xargs :guard (comparable-listp x)))
  (cond ((atom x)
         t)
        ((atom (cdr x))
         t)
        ((compare< (first x) (second x))
         (comparable-orderedp (cdr x)))
        (t
         (and (not (compare< (second x) (first x)))
              (comparable-orderedp (cdr x))))))


(local
 (progn
   (defthm comparable-orderedp-when-not-consp
     (implies (not (consp x))
              (comparable-orderedp x))
     :hints(("Goal" :in-theory (enable comparable-orderedp))))

   (defthm comparable-orderedp-when-not-consp-of-cdr
     (implies (not (consp (cdr x)))
              (comparable-orderedp x))
     :hints(("Goal" :in-theory (enable comparable-orderedp))))))

(defthm comparable-orderedp-of-comparable-merge
  (implies (and (comparable-orderedp x)
                (comparable-orderedp y))
           (comparable-orderedp (comparable-merge x y)))
  :hints(("Goal" :in-theory (enable comparable-merge comparable-orderedp))))

(defthm comparable-orderedp-of-comparable-mergesort
  (comparable-orderedp (comparable-mergesort x))
  :hints(("Goal" :in-theory (enable comparable-mergesort))))


(defthm no-duplicatesp-equal-of-comparable-mergesort
  (equal (no-duplicatesp-equal (comparable-mergesort x))
         (no-duplicatesp-equal x))
  :hints(("Goal"
          :use ((:functional-instance
                 no-duplicatesp-equal-same-by-duplicity
                 (duplicity-hyp (lambda () t))
                 (duplicity-lhs (lambda () (comparable-mergesort x)))
                 (duplicity-rhs (lambda () x)))))))




;; To prove that the sort is stable (and therefore equivalent to a simpler
;; one), we need additional properties of the comparison function.

(defun-sk compare<-negation-transitive ()
  ;; This says that the negation of the comparison relation is also transitive.
  ;; One big effect of it is that incomparable elements -- where (not (compare<
  ;; x y)) and (not (compare< y x)) -- are all in an equivalence class under
  ;; the comparison function.  (Transitivity of compare< shows that elements
  ;; with (compare< x y) and (compare< y x) are in an equivalence class as
  ;; well.)
  (forall (x y z)
          (implies (and (not (compare< x y))
                        (not (compare< y z)))
                   (not (compare< x z))))
  :rewrite :direct)

(defun-sk compare<-strict ()
  ;; We need this property of the comparison to make our merge functions
  ;; stable; if we don't know that either compare< or its negation is strict,
  ;; then it doesn't suffice to do only one comparison per element merged.
  (forall (x) (not (compare< x x)))
  :rewrite :direct)




(local
 (progn
   (in-theory (disable compare<-negation-transitive compare<-strict))

   (defthm compare<-reverse-when-strict
     (implies (and (compare<-strict)
                   (compare< x y))
              (not (compare< y x)))
     :hints (("goal" :use ((:instance compare<-transitive
                            (x x) (z x) (y y)))
              :in-theory (disable compare<-transitive))))


   (defund compare-equiv-elts (elt x)
     ;; Extract elements of x that are compare<-equivalent to elt, in order.
     (if (atom x)
         nil
       (if (iff (compare< elt (car x))
                (compare< (car x) elt))
           (cons (car x) (compare-equiv-elts elt (cdr x)))
         (compare-equiv-elts elt (cdr x)))))

   (defthm compare-equiv-elts-empty-case
     (implies (and (comparable-orderedp x)
                   ;; (comparable-listp x)
                   (compare<-negation-transitive)
                   ;; (comparablep elt)
                   (compare< elt (car x))
                   (not (compare< (car x) elt)))
              (equal (compare-equiv-elts elt x) nil))
     :hints(("Goal" :in-theory (enable compare-equiv-elts comparable-orderedp
                                       comparable-listp))))

   ;; (defthm compare<-by-equiv
   ;;   (implies (and (compare<-negation-transitive)
   ;;                 (not (compare< x y))
   ;;                 (not (compare< y x))
   ;;                 ;; (comparablep x)
   ;;                 ;; (comparablep y)
   ;;                 ;; (comparablep z)
   ;;                 )
   ;;            (and (implies (compare< y z)
   ;;                          (compare< x z))
   ;;                 (implies (not (compare< y z))
   ;;                          (not (compare< x z)))
   ;;                 (implies (compare< z y)
   ;;                          (compare< z x))
   ;;                 (implies (not (compare< z y))
   ;;                          (not (compare< z x))))))

   ;; (defthm not-compare<-by-strict
   ;;   (implies (and (compare<-strict)
   ;;                 ;; (comparablep x)
   ;;                 ;; (comparablep y)
   ;;                 (compare< y x))
   ;;            (not (compare< x y))))

   ;; (defthm compare<-by-negated-trans
   ;;   (implies (and (compare<-negation-transitive)
   ;;                 (compare< x y)
   ;;                 (not (compare< z y))
   ;;                 (comparablep x)
   ;;                 (comparablep y)
   ;;                 (comparablep z))
   ;;            (compare< x z)))


   (defthm compare-negation-transitive-implies
     (implies (compare<-negation-transitive)
              (implies (and (not (compare< b c))
                            (compare< a c))
                       (compare< a b))))

   (defthm compare-transitive-implies
     (implies (and (not (compare< a c))
                   (compare< a b))
              (not (compare< b c))))

   (defthm compare-equiv-elts-of-comparable-merge
     (implies (and (compare<-negation-transitive)
                   (compare<-strict)
                   (comparable-orderedp x)
                   (comparable-orderedp y)
                   ;; (comparable-listp x)
                   ;; (comparable-listp y)
                   ;; (comparablep elt)
                   )
              (equal (compare-equiv-elts elt (comparable-merge x y))
                     (append (compare-equiv-elts elt x)
                             (compare-equiv-elts elt y))))
     :hints(("Goal" :in-theory (enable (:i comparable-merge)
                                       compare-equiv-elts
                                       comparable-orderedp
                                       comparable-listp)
             :induct (comparable-merge x y)
             :expand ((comparable-merge x y)
                      ;; (:free (a b) (compare-equiv-elts elt (cons a b)))
                      ;; (compare-equiv-elts elt nil)
                      ))
            (and stable-under-simplificationp
                 (cond ((member-equal '(compare< (car y) (car x)) clause)
                        '(:cases ((consp (cdr x)))
                          ;; :expand ((compare-equiv-elts elt x)
                          ;;          (compare-equiv-elts elt nil))
                          ))
                       (t ;; (member-equal '(not (compare< (car y) (car x))) clause)
                        '(:cases ((consp (cdr y)))
                          ;; :expand ((compare-equiv-elts elt y)
                          ;;          (compare-equiv-elts elt nil))
                          ))
                       ;; (t '(:expand ((compare-equiv-elts elt x)
                       ;;               (compare-equiv-elts elt y)
                       ;;               (compare-equiv-elts elt nil))))
                       ))))

   (defthm compare-equiv-elts-of-append
     (equal (compare-equiv-elts elt (append x y))
            (append (compare-equiv-elts elt x)
                    (compare-equiv-elts elt y)))
     :hints(("Goal" :in-theory (enable compare-equiv-elts))))

   (defthm append-compare-extracts-of-take/nthcdr
     (implies (< (nfix n) (len x))
              (equal (append (compare-equiv-elts elt (take n x))
                             (compare-equiv-elts elt (nthcdr n x)))
                     (compare-equiv-elts elt x)))
     :hints (("goal" :use ((:instance compare-equiv-elts-of-append
                            (x (take n x)) (y (nthcdr n x))))
              :in-theory (disable compare-equiv-elts-of-append
                                  (force)))))

   (defthm compare-equiv-elts-of-comparable-mergesort
     (implies (and (compare<-negation-transitive)
                   (compare<-strict)
                   ;; (comparable-listp x)
                   ;; (comparablep elt)
                   )
              (equal (compare-equiv-elts elt (comparable-mergesort x))
                     (compare-equiv-elts elt x)))
     :hints(("Goal" :in-theory (e/d ((:i comparable-mergesort)
                                     floor-bounded-by-/)
                                    ((force) (comparable-mergesort)
                                     compare-equiv-elts-empty-case))
             :expand ((comparable-mergesort x))
             :induct (comparable-mergesort x))
            (and stable-under-simplificationp
                 '(:in-theory (e/d (compare-equiv-elts)
                                   ((force) (comparable-mergesort)
                                    compare-equiv-elts-empty-case))))))

   ;; Canoncity: Two truelists are equal if they are both ordered and the
   ;; extract-equivalents of any element from the two lists are equal (as long as
   ;; the comparison function is good.)

   (defun-sk compare-elts-equiv (x y)
     (forall elt
             (equal (compare-equiv-elts elt x)
                    (compare-equiv-elts elt y)))
     :rewrite :direct)

   (defun unequal-lists-badguy (x y)
     (if (atom x)
         (car y)
       (if (atom y)
           (car x)
         (if (equal (car x) (car y))
             (unequal-lists-badguy (cdr x) (cdr y))
           (if (compare< (car x) (car y))
               (car x)
             (car y))))))

   ;; (defthm comparablep-of-unequal-lists-badguy
   ;;   (implies (not (equal (list-fix x) (list-fix y)))
   ;;            (comparablep (unequal-lists-badguy x y)))
   ;;   :hints(("Goal" :in-theory (enable list-fix))))

   (defthm compare-equiv-elts-when-not-consp
     (implies (not (consp x))
              (equal (compare-equiv-elts elt x) nil))
     :hints(("Goal" :in-theory (enable compare-equiv-elts))))

   (defthm compare-equiv-elts-when-past
     (implies (and (comparable-orderedp x)
                   (compare< elt (car x))
                   (not (compare< (car x) elt))
                   (compare<-negation-transitive))
              (equal (compare-equiv-elts elt x) nil))
     :hints(("Goal" :in-theory (enable comparable-orderedp
                                       compare-equiv-elts))))


   (defthm compare-equiv-elts-of-unequal-lists
     (implies (and (compare<-negation-transitive)
                   ;; (comparable-listp x)
                   ;; (comparable-listp y)
                   ;; (true-listp x)
                   ;; (true-listp y)
                   (comparable-orderedp x)
                   (comparable-orderedp y)
                   (not (equal (list-fix x) (list-fix y))))
              (not (equal (compare-equiv-elts (unequal-lists-badguy x y) x)
                          (compare-equiv-elts (unequal-lists-badguy x y) y))))
     :hints (("goal" :induct (unequal-lists-badguy x y)
              :expand ((:free (elt) (compare-equiv-elts elt x))
                       (:free (elt) (compare-equiv-elts elt y)))
              :in-theory (e/d (comparable-orderedp)))))))


(defund comparable-insert (elt x)
  (declare (xargs :guard (and (comparablep elt)
                              (comparable-listp x))))
  (if (atom x)
      (list elt)
    (if (compare< (car x) elt)
        (cons (car x) (comparable-insert elt (cdr x)))
      (cons elt x))))

(local
 (progn
   (defthm compare-equiv-elts-of-comparable-insert
     (implies (and (compare<-negation-transitive)
                   (compare<-strict))
              (equal (compare-equiv-elts a (comparable-insert b x))
                     (if (iff (compare< a b)
                              (compare< b a))
                         (cons b (compare-equiv-elts a x))
                       (compare-equiv-elts a x))))
     :hints(("Goal" :in-theory (enable compare-equiv-elts comparable-insert))))

   (defthm comparable-orderedp-of-comparable-insert
     (implies (and (comparable-orderedp x))
              (comparable-orderedp (comparable-insert elt x)))
     :hints(("Goal" :in-theory (enable comparable-orderedp comparable-insert))))

   (defthm comparable-listp-of-comparable-insert
     (implies (and (comparable-listp x)
                   (comparablep elt))
              (comparable-listp (comparable-insert elt x)))
     :hints(("Goal" :in-theory (enable comparable-insert))))

   (defthm true-listp-of-comparable-insert
     (implies (true-listp x)
              (true-listp (comparable-insert elt x)))
     :hints(("Goal" :in-theory (enable comparable-insert))))))


(defund comparable-insertsort (x)
  (declare (xargs :guard (comparable-listp x)
                  :verify-guards nil))
  (if (atom x)
      nil
    (comparable-insert (car x)
                       (comparable-insertsort (cdr x)))))

(defthm comparable-listp-of-comparable-insertsort
  (implies (comparable-listp x)
           (comparable-listp (comparable-insertsort x)))
  :hints(("Goal" :in-theory (e/d (comparable-insertsort)
                                 ((comparable-listp))))))

(without-waterfall-parallelism
(def-saved-obligs comparable-insertsort-guard
  :proofs ((comparable-insertsort-guard))
  (verify-guards comparable-insertsort))
)

(local
 (progn
   (defthm compare-equiv-elts-of-comparable-insertsort
     (implies (and (compare<-negation-transitive)
                   (compare<-strict))
              (equal (compare-equiv-elts a (comparable-insertsort x))
                     (compare-equiv-elts a x)))
     :hints(("Goal" :in-theory (e/d (comparable-insertsort)
                                    ((comparable-insertsort)))
             :induct (comparable-insertsort x)
             :expand ((compare-equiv-elts a x)
                      (compare-equiv-elts a nil)
                      (comparable-listp x)))))

   (defthm comparable-orderedp-of-comparable-insertsort
     (comparable-orderedp (comparable-insertsort x))
     :hints(("Goal" :in-theory (e/d (comparable-insertsort)
                                    ((comparable-orderedp)
                                     (comparable-insertsort))))))


   (defthm true-listp-of-comparable-insertsort
     (true-listp (comparable-insertsort x))
     :hints(("Goal" :in-theory (enable comparable-insertsort))))))


(defthm comparable-mergesort-equals-comparable-insertsort
  (implies (and (compare<-negation-transitive)
                (compare<-strict))
           (equal (comparable-mergesort x)
                  (comparable-insertsort x)))
  :hints (("goal" :use ((:instance compare-equiv-elts-of-unequal-lists
                         (x (comparable-mergesort x))
                         (y (comparable-insertsort x))))
           :in-theory (disable compare-equiv-elts-of-unequal-lists))))

(defthm subsetp-of-comparable-merge-1
  (implies (and (subsetp-equal x z)
                (subsetp-equal y z))
           (subsetp-equal (comparable-merge x y)
                          z))
  :hints (("goal" :in-theory (enable comparable-merge))))

(defun-sk compare<-total ()
  (forall (x y)
          (implies (and (not (compare< x y))
                        (not (equal x y)))
                   (compare< y x)))
  :rewrite :direct)

;; Mihir M. mod: comparable-mergesort-is-identity-under-set-equiv is a generic
;; lemma with a self-explanatory name instantiated in defsort for all sorts,
;; and common-sort-for-perms is a generic lemma stating all permutations of a
;; duplicate-free list sort under a total order to the same list which is not
;; yet instatiated in defsort.
(encapsulate
  ()

  (local (include-book "std/lists/sets" :dir :system))

  (defthm no-duplicatesp-equal-of-remove-duplicates-equal
    (no-duplicatesp-equal (remove-duplicates-equal x)))

  (local (in-theory (enable nth)))

  (local
   (defthm member-equal-nth
     (implies (< (nfix n) (len l))
              (member-equal (nth n l) l))))

  (local
   (defthm subsetp-of-comparable-mergesort
     (subsetp-equal (comparable-mergesort x) x)
     :hints(("Goal" :in-theory (e/d (comparable-mergesort
                                     floor-bounded-by-/)
                                    (len))))))

  (local
   (defthmd comparable-mergesort-is-identity-under-set-equiv-lemma-3
     (iff (member-equal x lst)
          (not (zp (duplicity x lst))))))

  (local (include-book "std/basic/inductions" :dir :system))

  (local
   (defthmd
     comparable-mergesort-is-identity-under-set-equiv-lemma-1
     (implies (<= (nfix n) (len x))
              (subsetp-equal (take n x)
                             (comparable-mergesort x)))
     :hints (("goal" :induct (dec-induct n)
              :in-theory (e/d
                          (take-as-append-and-nth)
                          (take))
              :expand ((:with comparable-mergesort-is-identity-under-set-equiv-lemma-3
                              (member-equal (nth (+ -1 n) x)
                                            (comparable-mergesort x))))))))

  (defthm
    comparable-mergesort-is-identity-under-set-equiv
    (set-equiv (comparable-mergesort x) x)
    :hints (("goal" :in-theory (enable set-equiv)
             :use (:instance comparable-mergesort-is-identity-under-set-equiv-lemma-1
                             (n (len x))))))
  (local
   (defthm
     common-sort-for-perms-lemma-1
     (implies (and (comparable-orderedp l)
                   (compare< x (car l))
                   (compare<-negation-transitive)
                   (compare<-strict))
              (not
               (member-equal x l)))
     :hints (("goal" :in-theory (enable comparable-orderedp member-equal)))))

  (local
   (defthmd
     common-sort-for-perms-lemma-2
     (implies (and (comparable-orderedp l)
                   (member-equal x l)
                   (compare< x (nth n l))
                   (compare<-negation-transitive)
                   (compare<-strict))
              (member-equal x (take n l)))
     :hints (("goal" :in-theory (enable comparable-orderedp member-equal)))))

  (local
   (defthm common-sort-for-perms-lemma-3
     (implies (and (no-duplicatesp-equal l)
                   (< (nfix n) (len l)))
              (not (member-equal (nth n l) (take n l))))
     :hints (("goal" :in-theory (e/d (member-equal) (member-equal-nth))
              :induct (nth n l))
             ("subgoal *1/3" :use (:instance (:rewrite member-equal-nth)
                                             (l (cdr l))
                                             (n (+ -1 n)))))))

  (local
   (defthm
     common-sort-for-perms-lemma-5
     (implies
      (and
       (equal (take (+ -1 n)
                    (comparable-insertsort (remove-duplicates-equal x)))
              (take (+ -1 n)
                    (comparable-insertsort (remove-duplicates-equal y))))
       (compare< (mv-nth 1
                         (compare<-negation-transitive-witness))
                 (mv-nth 2
                         (compare<-negation-transitive-witness)))
       (not (compare< (compare<-strict-witness)
                      (compare<-strict-witness)))
       (set-equiv x y)
       (<= n (len (remove-duplicates-equal x))))
      (not
       (member-equal (nth (+ -1 n)
                          (comparable-insertsort (remove-duplicates-equal y)))
                     (take (+ -1 n)
                           (comparable-insertsort (remove-duplicates-equal x))))))
     :hints
     (("goal"
       :do-not-induct t
       :in-theory (e/d
                   ((:definition compare<-negation-transitive)
                    (:definition compare<-strict))
                   ((:rewrite common-sort-for-perms-lemma-3)))
       :use (:instance (:rewrite common-sort-for-perms-lemma-3)
                       (l (comparable-mergesort (remove-duplicates-equal y)))
                       (n (+ -1 n)))))))

  (local
   (defthm
     common-sort-for-perms-lemma-6
     (implies
      (and
       (not (zp n))
       (compare< (mv-nth 1
                         (compare<-negation-transitive-witness))
                 (mv-nth 2
                         (compare<-negation-transitive-witness)))
       (not (compare< (compare<-strict-witness)
                      (compare<-strict-witness)))
       (set-equiv x y)
       (<= n (len (remove-duplicates-equal x))))
      (member-equal (nth (+ -1 n)
                         (comparable-insertsort (remove-duplicates-equal y)))
                    x))
     :hints
     (("goal"
       :do-not-induct t
       :in-theory (e/d
                   ((:definition compare<-negation-transitive)
                    (:definition compare<-strict))
                   ((:rewrite member-equal-nth)))
       :use (:instance (:rewrite member-equal-nth)
                       (l (comparable-mergesort (remove-duplicates-equal y)))
                       (n (+ -1 n)))))))

  (local
   (defthm
     common-sort-for-perms-lemma-4
     (implies
      (and
       (not (compare< (compare<-strict-witness)
                      (compare<-strict-witness)))
       (not (zp n))
       (equal (take (+ -1 n)
                    (comparable-mergesort (remove-duplicates-equal x)))
              (take (+ -1 n)
                    (comparable-mergesort (remove-duplicates-equal y))))
       (compare< (mv-nth 1
                         (compare<-negation-transitive-witness))
                 (mv-nth 2
                         (compare<-negation-transitive-witness)))
       (set-equiv x y)
       (<= n (len (remove-duplicates-equal x))))
      (not (compare< (nth (+ -1 n)
                          (comparable-mergesort (remove-duplicates-equal y)))
                     (nth (+ -1 n)
                          (comparable-mergesort (remove-duplicates-equal x))))))
     :hints
     (("goal"
       :do-not-induct t
       :in-theory (e/d
                   ((:definition compare<-negation-transitive)
                    (:definition compare<-strict)))
       :use (:instance
             (:rewrite common-sort-for-perms-lemma-2)
             (l (comparable-mergesort (remove-duplicates-equal x)))
             (n (+ -1 n))
             (x (nth (+ -1 n)
                     (comparable-mergesort (remove-duplicates-equal y)))))))))

  (local
   (defthm
     common-sort-for-perms-lemma-8
     (implies
      (and
       (compare< (mv-nth 0
                         (compare<-negation-transitive-witness))
                 (mv-nth 1
                         (compare<-negation-transitive-witness)))
       (not (compare< (compare<-strict-witness)
                      (compare<-strict-witness)))
       (<= n (len (remove-duplicates-equal x))))
      (not
       (member-equal (nth (+ -1 n)
                          (comparable-insertsort (remove-duplicates-equal x)))
                     (take (+ -1 n)
                           (comparable-insertsort (remove-duplicates-equal x))))))
     :hints
     (("goal"
       :in-theory (e/d
                   ((:definition compare<-negation-transitive)
                    (:definition compare<-strict))
                   ((:rewrite common-sort-for-perms-lemma-3)))
       :use (:instance
             (:rewrite common-sort-for-perms-lemma-3)
             (l (comparable-mergesort (remove-duplicates-equal x)))
             (n (+ -1 n)))))))

  (local
   (defthm
     common-sort-for-perms-lemma-9
     (implies
      (and
       (not (zp n))
       (compare< (mv-nth 0
                         (compare<-negation-transitive-witness))
                 (mv-nth 1
                         (compare<-negation-transitive-witness)))
       (not (compare< (compare<-strict-witness)
                      (compare<-strict-witness)))
       (<= n (len (remove-duplicates-equal x))))
      (member-equal (nth (+ -1 n)
                         (comparable-insertsort (remove-duplicates-equal x)))
                    x))
     :hints
     (("goal"
       :do-not-induct t
       :in-theory (e/d
                   ((:definition compare<-negation-transitive)
                    (:definition compare<-strict))
                   ((:rewrite member-equal-nth)))
       :use (:instance (:rewrite member-equal-nth)
                       (l (comparable-mergesort (remove-duplicates-equal x)))
                       (n (+ -1 n)))))))

  (local
   (defthm
     common-sort-for-perms-lemma-10
     (implies
      (and
       (not (zp n))
       (compare< (mv-nth 0
                         (compare<-negation-transitive-witness))
                 (mv-nth 1
                         (compare<-negation-transitive-witness)))
       (not (compare< (compare<-strict-witness)
                      (compare<-strict-witness)))
       (<= n (len (remove-duplicates-equal x))))
      (member-equal (nth (+ -1 n)
                         (comparable-mergesort (remove-duplicates-equal x)))
                    x))
     :hints
     (("goal"
       :in-theory (e/d
                   ((:definition compare<-negation-transitive)
                    (:definition compare<-strict)))
       :use
       (:instance
        (:rewrite comparable-mergesort-is-identity-under-set-equiv-lemma-3)
        (lst (remove-duplicates-equal x))
        (x (nth (+ -1 n)
                (comparable-mergesort (remove-duplicates-equal x)))))))))

  (local
   (defthm
     common-sort-for-perms-lemma-7
     (implies
      (and (not (< (len (remove-duplicates-equal x)) n))
           (not (zp n))
           (equal (take (+ -1 n)
                        (comparable-mergesort (remove-duplicates-equal x)))
                  (take (+ -1 n)
                        (comparable-mergesort (remove-duplicates-equal y))))
           (compare< (mv-nth 0
                             (compare<-negation-transitive-witness))
                     (mv-nth 1
                             (compare<-negation-transitive-witness)))
           (not (compare< (compare<-strict-witness)
                          (compare<-strict-witness)))
           (set-equiv x y))
      (not
       (compare< (nth (+ -1 n)
                      (comparable-mergesort (remove-duplicates-equal x)))
                 (nth (+ -1 n)
                      (comparable-mergesort (remove-duplicates-equal y))))))
     :hints
     (("goal"
       :do-not-induct t
       :in-theory (e/d
                   ((:definition compare<-negation-transitive)
                    (:definition compare<-strict)))
       :use (:instance
             (:rewrite common-sort-for-perms-lemma-2)
             (l (comparable-mergesort (remove-duplicates-equal y)))
             (n (+ -1 n))
             (x (nth (+ -1 n)
                     (comparable-mergesort (remove-duplicates-equal x)))))))))

  (local
   (defthm
     common-sort-for-perms-lemma-12
     (implies
      (and
       (not (compare< (mv-nth 0
                              (compare<-negation-transitive-witness))
                      (mv-nth 2
                              (compare<-negation-transitive-witness))))
       (not (compare< (compare<-strict-witness)
                      (compare<-strict-witness)))
       (<= n (len (remove-duplicates-equal x))))
      (not
       (member-equal (nth (+ -1 n)
                          (comparable-insertsort (remove-duplicates-equal x)))
                     (take (+ -1 n)
                           (comparable-insertsort (remove-duplicates-equal x))))))
     :hints
     (("goal"
       :do-not-induct t
       :in-theory (e/d
                   ((:definition compare<-negation-transitive)
                    (:definition compare<-strict))
                   ((:rewrite common-sort-for-perms-lemma-3)))
       :use (:instance
             (:rewrite common-sort-for-perms-lemma-3)
             (l (comparable-mergesort (remove-duplicates-equal x)))
             (n (+ -1 n)))))))

  (local
   (defthm
     common-sort-for-perms-lemma-13
     (implies
      (and
       (not (zp n))
       (not (compare< (mv-nth 0
                              (compare<-negation-transitive-witness))
                      (mv-nth 2
                              (compare<-negation-transitive-witness))))
       (not (compare< (compare<-strict-witness)
                      (compare<-strict-witness)))
       (<= n (len (remove-duplicates-equal x))))
      (member-equal (nth (+ -1 n)
                         (comparable-insertsort (remove-duplicates-equal x)))
                    x))
     :hints
     (("goal"
       :in-theory (e/d
                   ((:definition compare<-negation-transitive)
                    (:definition compare<-strict))
                   ((:rewrite member-equal-nth)))
       :use (:instance (:rewrite member-equal-nth)
                       (l (comparable-mergesort (remove-duplicates-equal x)))
                       (n (+ -1 n)))))))

  (local
   (defthm
     common-sort-for-perms-lemma-11
     (implies
      (and
       (not (zp n))
       (equal (take (+ -1 n)
                    (comparable-mergesort (remove-duplicates-equal x)))
              (take (+ -1 n)
                    (comparable-mergesort (remove-duplicates-equal y))))
       (not (compare< (mv-nth 0
                              (compare<-negation-transitive-witness))
                      (mv-nth 2
                              (compare<-negation-transitive-witness))))
       (not (compare< (compare<-strict-witness)
                      (compare<-strict-witness)))
       (set-equiv x y)
       (<= n (len (remove-duplicates-equal x))))
      (not (compare< (nth (+ -1 n)
                          (comparable-mergesort (remove-duplicates-equal x)))
                     (nth (+ -1 n)
                          (comparable-mergesort (remove-duplicates-equal y))))))
     :hints
     (("goal"
       :in-theory (e/d
                   ((:definition compare<-negation-transitive)
                    (:definition compare<-strict)))
       :use (:instance
             (:rewrite common-sort-for-perms-lemma-2)
             (l (comparable-mergesort (remove-duplicates-equal y)))
             (n (+ -1 n))
             (x (nth (+ -1 n)
                     (comparable-mergesort (remove-duplicates-equal x)))))))))

  (local
   (defthmd
     common-sort-for-perms-lemma-14
     (implies (and (compare<-total)
                   (compare<-negation-transitive)
                   (compare<-strict)
                   (set-equiv x y)
                   (<= (nfix n)
                       (len (remove-duplicates-equal x))))
              (equal (take n
                           (comparable-mergesort (remove-duplicates-equal x)))
                     (take n
                           (comparable-mergesort (remove-duplicates-equal y)))))
     :hints
     (("goal"
       :induct (dec-induct n)
       :in-theory (e/d
                   (take-as-append-and-nth
                    (:definition compare<-negation-transitive)
                    (:definition compare<-strict))
                   (compare<-total-necc
                    comparable-mergesort-equals-comparable-insertsort
                    take)))
      ("subgoal *1/2"
       :use (:instance
             compare<-total-necc
             (x (nth (+ -1 n)
                     (comparable-mergesort (remove-duplicates-equal y))))
             (y (nth (+ -1 n)
                     (comparable-mergesort (remove-duplicates-equal x)))))))))

  (defthm
    common-sort-for-perms
    (implies (and (compare<-negation-transitive)
                  (compare<-strict)
                  (compare<-total)
                  (set-equiv x y))
             (equal (comparable-mergesort (remove-duplicates-equal x))
                    (comparable-mergesort (remove-duplicates-equal y))))
    :hints
    (("goal"
      :do-not-induct t
      :in-theory (e/d (take-of-len-free)
                      (comparable-mergesort-equals-comparable-insertsort
                       set-equiv-implies-equal-len-remove-duplicates-equal))
      :use ((:instance common-sort-for-perms-lemma-14
                       (n (len (remove-duplicates-equal x))))
            set-equiv-implies-equal-len-remove-duplicates-equal)))))
