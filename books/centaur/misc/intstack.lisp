; Copyright (C) 2018 Centaur Technology
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

(in-package "ACL2")

(include-book "std/stobjs/updater-independence" :dir :system)
(include-book "std/stobjs/absstobjs" :dir :system)
(include-book "centaur/misc/u32-listp" :dir :system)
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "std/lists/nth" :dir :system))
(local (include-book "std/lists/take" :dir :system))
(local (include-book "std/lists/resize-list" :dir :system))
(local (include-book "std/lists/repeat" :dir :system))
;; (local (include-book "std/lists/index-of" :dir :system))

(local (in-theory (disable nth update-nth
                           acl2::nth-when-zp
                           nth-0-cons
                           nth-add1
                           acl2::zp-open
                           acl2::resize-list-when-atom
                           resize-list
                           unsigned-byte-p)))

;; This data structure implements a stack of unique unsigned integers that
;; supports constant-time membership checks, constant-time pushes,
;; constant-time pops, and linear-time rewinds.  It is implemented with a
;; simple vector-based stack of members as well as a bit array where the bit
;; corresponding to each member's value is set.  Membership checks are lookups
;; in the bit array, and pushes/pops just update the stack as well as the bit
;; array.


(defstobj intstack$c
  (intstack$c-bits :type (array bit (0)) :initially 0 :resizable t)
  (intstack$c-stack :type (array (unsigned-byte 32) (0)) :initially 0 :resizable t)
  (intstack$c-count :type (integer 0 *) :initially 0))

(local
 (defthm intstack$c-stackp-is-u32-listp
   (equal (intstack$c-stackp x) (u32-listp x))))

(defun-sk intstack$c-stack-elems-in-bounds (intstack$c)
  (forall n
          (implies (< (nfix n) (nfix (intstack$c-count intstack$c)))
                   (and (< (nth n (nth *intstack$c-stacki* intstack$c))
                           (len (nth *intstack$c-bitsi* intstack$c)))
                        (< (nfix (nth n (nth *intstack$c-stacki* intstack$c)))
                           (len (nth *intstack$c-bitsi* intstack$c))))))
  :rewrite :direct)

(in-theory (disable intstack$c-stack-elems-in-bounds
                    intstack$c-stack-elems-in-bounds-necc))

(local
 (defsection list-lemmas
   (defthmd take-of-update-nth-lemma
     (equal (take (+ 1 (nfix n)) (update-nth n x y))
            (append (take n y) (list x)))
     :hints(("Goal" :in-theory (enable update-nth))))

   (defthm take-of-update-nth
     (implies (equal nn (nfix n))
              (equal (take (+ 1 nn) (update-nth n x y))
                     (append (take n y) (list x))))
     :hints(("Goal" :in-theory (enable take-of-update-nth-lemma))))

   (defthm member-append
     (iff (member x (append y z))
          (or (member x y) (member x z))))

   (defthm member-of-cons
     (iff (member x (cons a b))
          (or (equal x a)
              (member x b))))

   (defthm member-of-nil
     (not (member x nil)))

   (defthmd take-prev-len-of-resize-list-lemma
     (implies (and (<= (len x) (nfix m)))
              (equal (take (len x) (resize-list x m val))
                     (list-fix x)))
     :hints(("Goal" :in-theory (e/d (resize-list repeat len))
             :induct (resize-list x m val)
             :expand ((repeat (len x) nil)))))

   (defthm take-prev-len-of-resize-list
     (implies (and (<= (len x) (nfix m))
                   (equal n (len x)))
              (equal (take n (resize-list x m val))
                     (list-fix x)))
     :hints(("Goal" :in-theory (enable take-prev-len-of-resize-list-lemma))))
   

   (defthmd nth-is-member
     (implies (< (nfix n) (len x))
              (member (nth n x) x))
     :hints(("Goal" :in-theory (enable nth))))
   
   (in-theory (disable member take))

   
   (defthm member-of-rev
     (iff (member k (rev x)) (member k x))
     :hints(("Goal" :in-theory (enable rev member))))

   (defthm consp-member-under-iff
     (iff (consp (member k x)) (member k x)))

   (defthm no-duplicatesp-of-append
     (iff (no-duplicatesp (append a b))
          (and (not (intersectp a b))
               (no-duplicatesp a)
               (no-duplicatesp b))))

   (defthm intersectp-of-append
     (iff (intersectp (append x y) z)
          (or (intersectp x z)
              (intersectp y z)))
     :hints(("Goal" :in-theory (enable rev))))

   (defthm intersectp-of-rev
     (iff (intersectp (Rev x) y)
          (intersectp x y))
     :hints(("Goal" :in-theory (enable rev))))

   (defthm intersectp-of-cons-second
     (iff (intersectp x (cons a y))
          (or (member a x)
              (intersectp x y)))
     :hints(("Goal" :in-theory (enable intersectp member))))

   (defthm intersectp-nil
     (not (intersectp x nil)))

   (defthm no-duplicatesp-of-rev
     (iff (no-duplicatesp (rev x))
          (no-duplicatesp x))
     :hints(("Goal" :in-theory (enable rev))))

   (defthm len-equal-0
     (equal (equal (len x) 0)
            (not (consp x))))

   (defthm cdr-of-rev
     (equal (cdr (rev x))
            (rev (take (+ -1 (len x)) x)))
     :hints(("Goal" :in-theory (enable rev))))

   (defun nthcdr-rev-ind (n x)
     (if (zp n)
         x
       (nthcdr-rev-ind (1- n) (take (+ -1 (len x)) x))))

   (defthm nthcdr-of-rev
     (equal (nthcdr n (rev x))
            (rev (take (+ (- (nfix n)) (len x)) x)))
     :hints(("Goal" :induct (nthcdr-rev-ind n x)
             :expand ((len x)))))

   (defthm no-duplicatesp-of-nthcdr
     (implies (no-duplicatesp x)
              (no-duplicatesp (nthcdr n x)))
     :hints(("Goal" :in-theory (enable nthcdr))))

   (defthm u32-listp-of-update-nth
     (implies (and (u32-listp x)
                   (unsigned-byte-p 32 k)
                   (< (nfix n) (len x)))
              (u32-listp (update-nth n k x)))
     :hints(("Goal" :in-theory (enable update-nth))))

   (defthm u32-listp-of-resize-list
     (implies (u32-listp x)
              (u32-listp (resize-list x n 0)))
     :hints(("Goal" :in-theory (enable resize-list))))))


(defsection intstack$c-bits-consistent
  (defun-sk intstack$c-bits-consistent (intstack$c)
    (forall x
            (iff (equal (nth x (nth *intstack$c-bitsi* intstack$c)) 1)
                 (member (nfix x) (take (nth *intstack$c-count* intstack$c)
                                        (nth *intstack$c-stacki* intstack$c)))))
    :rewrite :direct)

  (in-theory (disable intstack$c-bits-consistent
                      intstack$c-bits-consistent-necc))

  (defthmd intstack$c-bits-consistent-implies-member
    (implies (and (intstack$c-bits-consistent intstack$c)
                  (equal (nth x (nth *intstack$c-bitsi* intstack$c)) 1)
                  (natp x))
             (member x (take (nth *intstack$c-count* intstack$c)
                             (nth *intstack$c-stacki* intstack$c))))
    :hints (("goal" :use intstack$c-bits-consistent-necc)))

  (defthmd intstack$c-bits-consistent-implies-not-member
    (implies (and (intstack$c-bits-consistent intstack$c)
                  (not (equal (nth x (nth *intstack$c-bitsi* intstack$c)) 1))
                  (natp x))
             (not (member x (take (nth *intstack$c-count* intstack$c)
                                  (nth *intstack$c-stacki* intstack$c)))))
    :hints (("goal" :use intstack$c-bits-consistent-necc)))

  (defthmd intstack$c-bits-consistent-implies-nth-bit
    (implies (and (intstack$c-bits-consistent intstack$c)
                  (u32-listp (nth *intstack$c-stacki* intstack$c))
                  (<= (nfix (nth *intstack$c-count* intstack$c)) (len (nth *intstack$c-stacki* intstack$c)))
                  (< (nfix n) (nfix (nth *intstack$c-count* intstack$c))))
             (equal (nth (nth n (nth *intstack$c-stacki* intstack$c))
                         (nth *intstack$c-bitsi* intstack$c))
                    1))
    :hints (("goal" :use ((:instance intstack$c-bits-consistent-necc
                           (x (nth n (nth *intstack$c-stacki* intstack$c))))
                          (:instance nth-is-member
                           (x (take (nth *intstack$c-count* intstack$c)
                                    (nth *intstack$c-stacki* intstack$c)))))
             :in-theory (enable nth-in-u32-listp-natp)))))

(define intstack$c-push ((x :type (unsigned-byte 32))
                         (intstack$c))
  :guard-debug t
  :returns (new-intstack$c)
  (b* ((in-bounds (< (lnfix x) (intstack$c-bits-length intstack$c)))
       ((when (and in-bounds
                   (eql (intstack$c-bitsi x intstack$c) 1)))
        ;; already exists
        intstack$c)
       (count (lnfix (intstack$c-count intstack$c)))
       (intstack$c (if (< count (intstack$c-stack-length intstack$c))
                       intstack$c
                     (resize-intstack$c-stack (max 16 (* 2 count)) intstack$c)))
       (intstack$c (if in-bounds
                       intstack$c
                     (resize-intstack$c-bits (max 16 (* 2 (lnfix x))) intstack$c)))
       (intstack$c (update-intstack$c-stacki count (lnfix x) intstack$c))
       (intstack$c (update-intstack$c-count (+ 1 count) intstack$c)))
    (update-intstack$c-bitsi x 1 intstack$c))
  ///
  (defret intstack$c-push-preserves-stack-elems-in-bounds
    (implies (intstack$c-stack-elems-in-bounds intstack$c)
             (intstack$c-stack-elems-in-bounds new-intstack$c))
    :hints ((and stable-under-simplificationp
                 (b* ((lit (assoc 'intstack$c-stack-elems-in-bounds clause)))
                   (and lit
                        `(:computed-hint-replacement
                          ((and stable-under-simplificationp
                                '(:use ((:instance intstack$c-stack-elems-in-bounds-necc
                                         (n (intstack$c-stack-elems-in-bounds-witness . ,(cdr lit)))))
                                  :in-theory (disable intstack$c-stack-elems-in-bounds-necc))))
                          :expand (,lit)))))))
  

  (defret intstack$c-push-preserves-intstack$c-bits-consistent
    (implies (and (intstack$c-bits-consistent intstack$c)
                  (<= (nfix (nth *intstack$c-count* intstack$c))
                      (len (nth *intstack$c-stacki* intstack$c))))
             (intstack$c-bits-consistent new-intstack$c))
    :hints ((and stable-under-simplificationp
                 (b* ((lit (assoc 'intstack$c-bits-consistent clause)))
                   (and lit
                        `(:computed-hint-replacement
                          ((and stable-under-simplificationp
                                '(:use ((:instance intstack$c-bits-consistent-necc
                                         (x (intstack$c-bits-consistent-witness . ,(cdr lit)))))
                                  :in-theory (disable intstack$c-bits-consistent-necc))))
                          :expand (,lit)))))))

  (defret intstack$c-push-preserves-no-duplicatesp
    (implies (and (intstack$c-bits-consistent intstack$c)
                  (no-duplicatesp (take (nth *intstack$c-count* intstack$c)
                                        (nth *intstack$c-stacki* intstack$c)))
                  (<= (nfix (nth *intstack$c-count* intstack$c))
                      (len (nth *intstack$c-stacki* intstack$c))))
             (no-duplicatesp (take (nth *intstack$c-count* new-intstack$c)
                                   (nth *intstack$c-stacki* new-intstack$c))))
    :hints(("Goal" :use ((:instance intstack$c-bits-consistent-necc)))))
  
  (defret intstack$c-push-preserves-stack-length-ok
    (implies (<= (nfix (nth *intstack$c-count* intstack$c))
                 (len (nth *intstack$c-stacki* intstack$c)))
             (<= (nfix (nth *intstack$c-count* new-intstack$c))
                 (len (nth *intstack$c-stacki* new-intstack$c)))))

  (defret natp-count-of-intstack$c-push
    (implies (natp (nth *intstack$c-count* intstack$c))
             (natp (nth *intstack$c-count* new-intstack$c))))

  (defret intstack$c-push-preserves-stack-length-ok-natp
    (implies (and (natp (nth *intstack$c-count* intstack$c))
                  (<= (nth *intstack$c-count* intstack$c)
                      (len (nth *intstack$c-stacki* intstack$c))))
             (<= (nth *intstack$c-count* new-intstack$c)
                 (len (nth *intstack$c-stacki* new-intstack$c)))))

  (defret take-of-intstack$c-push
    (implies (<= (nfix (nth *intstack$c-count* intstack$c))
                 (len (nth *intstack$c-stacki* intstack$c)))
             (equal (take (nth *intstack$c-count* new-intstack$c)
                          (nth *intstack$c-stacki* new-intstack$c))
                    (if (equal (nth (nfix x) (nth *intstack$c-bitsi* intstack$c)) 1)
                        (take (nth *intstack$c-count* intstack$c)
                              (nth *intstack$c-stacki* intstack$c))
                      (append (take (nth *intstack$c-count* intstack$c)
                                    (nth *intstack$c-stacki* intstack$c))
                              (list (nfix x)))))))


  (defret u32-listp-of-intstack$c-push-stack
    (implies (and (u32-listp (nth *intstack$c-stacki* intstack$c))
                  (unsigned-byte-p 32 x))
             (u32-listp (nth *intstack$c-stacki* new-intstack$c)))))
  


(local
 (defsection no-duplicatesp-of-take-less

   (local (defthm member-of-take-more
            (implies (and (member k (take n x))
                          (natp m) (natp n))
                     (member k (take (+ m n) x)))
            :hints (("goal" :induct (take n x)
                     :in-theory (enable (:i take))))))

   (local (defthm no-duplicatesp-of-take-more
            (implies (and (not (no-duplicatesp (take n x)))
                          (natp m) (natp n))
                     (not (no-duplicatesp (take (+ m n) x))))
            :hints (("goal" :induct (take n x)
                     :in-theory (enable (:i take))
                     :expand ((take n x)
                              (take (+ m n) x)))
                    (and stable-under-simplificationp
                         '(:use ((:instance member-of-take-more
                                  (n (+ -1 n)) (k (car x)) (x (cdr x)))))))))

   (defthm no-duplicatesp-of-take-less
     (implies (and (no-duplicatesp (take n x))
                   (<= (nfix m) (nfix n)))
              (no-duplicatesp (take m x)))
     :hints (("goal" :use ((:instance no-duplicatesp-of-take-more
                            (n (nfix m))
                            (m (- (nfix n) (nfix m)))))
              :in-theory (disable no-duplicatesp-of-take-more))))))


(define intstack$c-pop (intstack$c)
  :guard (and (< 0 (intstack$c-count intstack$c))
              (<= (intstack$c-count intstack$c) (intstack$c-stack-length intstack$c))
              (ec-call (intstack$c-stack-elems-in-bounds intstack$c)))
  :returns (new-intstack$c)
  :guard-hints (("goal" :in-theory (enable nth-in-u32-listp-natp
                                           nth-in-u32-listp-integerp
                                           nth-in-u32-listp-gte-0
                                           intstack$c-stack-elems-in-bounds-necc)))
  (b* ((count (lnfix (intstack$c-count intstack$c)))
       (elem (lnfix (intstack$c-stacki (1- count) intstack$c)))
       (intstack$c (update-intstack$c-bitsi elem 0 intstack$c)))
    (update-intstack$c-count (1- count) intstack$c))
  ///
  (defret intstack$c-pop-preserves-stack-elems-in-bounds
    (implies (intstack$c-stack-elems-in-bounds intstack$c)
             (intstack$c-stack-elems-in-bounds new-intstack$c))
    :hints ((and stable-under-simplificationp
                 (b* ((lit (assoc 'intstack$c-stack-elems-in-bounds clause)))
                   (and lit
                        `(:computed-hint-replacement
                          ((and stable-under-simplificationp
                                '(:use ((:instance intstack$c-stack-elems-in-bounds-necc
                                         (n (intstack$c-stack-elems-in-bounds-witness . ,(cdr lit)))))
                                  :in-theory (disable intstack$c-stack-elems-in-bounds-necc))))
                          :expand (,lit)))))))


  (local (defthm member-of-take-plus-1
           (implies (not (equal (nth n x) k))
                    (iff (member k (take (+ 1 (nfix n)) x))
                         (member k (take n x))))
           :hints (("goal" :induct (take n x)
                    :in-theory (enable (:i take))
                    :expand ((nth n x)
                             (nth 0 x)
                             (take n x)
                             (take (+ 1 (nfix n)) x)
                             (member-equal k x))))))

  (local (defthm member-of-take-minus-1
           (implies (and (case-split (not (equal (nth (+ -1 n) x) k)))
                         (posp n))
                    (iff (member k (take (+ -1 n) x))
                         (member k (take n x))))
           :hints (("goal" :use ((:instance member-of-take-plus-1
                                  (n (+ -1 n))))))))

  (local (defthm member-nth-of-take-when-no-duplicates
           (implies (and (no-duplicatesp x)
                         (< (nfix n) (len x)))
                    (not (member (nth n x) (take n x))))
           :hints (("goal" :induct (take n x)
                    :in-theory (enable (:i take))
                    :expand ((nth n x)
                             (no-duplicatesp x))))))

  (local (defthm member-nth-of-take-when-no-duplicates-inst
           (implies (and (no-duplicatesp (take n x))
                         (posp n))
                    (not (member (nth (+ -1 n) x) (take (+ -1 n) x))))
           :hints (("goal" :use ((:instance member-nth-of-take-when-no-duplicates
                                  (x (take n x))
                                  (n (+ -1 n))))))))

  (local (in-theory (enable nth-in-u32-listp-natp)))

  (defret intstack$c-pop-preserves-intstack$c-bits-consistent
    (implies (and (intstack$c-bits-consistent intstack$c)
                  (u32-listp (nth *intstack$c-stacki* intstack$c))
                  (no-duplicatesp (take (nth *intstack$c-count* intstack$c)
                                        (nth *intstack$c-stacki* intstack$c)))
                  (<= (nfix (nth *intstack$c-count* intstack$c))
                      (len (nth *intstack$c-stacki* intstack$c)))
                  (< 0 (nfix (nth *intstack$c-count* intstack$c)) ))
             (intstack$c-bits-consistent new-intstack$c))
    :hints ((and stable-under-simplificationp
                 (b* ((lit (assoc 'intstack$c-bits-consistent clause)))
                   (and lit
                        `(:computed-hint-replacement
                          ((and stable-under-simplificationp
                                '(:use ((:instance intstack$c-bits-consistent-necc
                                         (x (intstack$c-bits-consistent-witness . ,(cdr lit)))))
                                  :in-theory (disable intstack$c-bits-consistent-necc))))
                          :expand (,lit)))))))

  (defret intstack$c-count-of-intstack$c-pop
    (equal (nth *intstack$c-count* new-intstack$c)
           (+ -1 (nfix (nth *intstack$c-count* intstack$c)))))

  (defret stack-of-intstack$c-pop
    (equal (nth *intstack$c-stacki* new-intstack$c)
           (nth *intstack$c-stacki* intstack$c))))
  

(define intstack$c-rewind ((n :type (unsigned-byte 32))
                           (intstack$c))
  :guard (and (<= n (intstack$c-count intstack$c))
              (<= (intstack$c-count intstack$c) (intstack$c-stack-length intstack$c))
              (ec-call (intstack$c-stack-elems-in-bounds intstack$c)))
  :measure (nfix (intstack$c-count intstack$c))
  :returns (new-intstack$c)
  (b* (((when (<= (lnfix (intstack$c-count intstack$c)) (lnfix n)))
        intstack$c)
       (intstack$c (intstack$c-pop intstack$c)))
    (intstack$c-rewind n intstack$c))
  ///
  (defret intstack$c-rewind-preserves-stack-elems-in-bounds
    (implies (intstack$c-stack-elems-in-bounds intstack$c)
             (intstack$c-stack-elems-in-bounds new-intstack$c)))

  (defret intstack$c-count-of-intstack$c-rewind
    (implies (and (<= (nfix n) (nth *intstack$c-count* intstack$c))
                  (natp (nth *intstack$c-count* intstack$c)))
             (equal (nth *intstack$c-count* new-intstack$c)
                    (nfix n))))

  (defret intstack$c-stack-of-intstack$c-rewind
    (equal (nth *intstack$c-stacki* new-intstack$c)
           (nth *intstack$c-stacki* intstack$c)))

  (defret intstack$c-rewind-preserves-intstack$c-bits-consistent
    (implies (and (intstack$c-bits-consistent intstack$c)
                  (u32-listp (nth *intstack$c-stacki* intstack$c))
                  (no-duplicatesp (take (nth *intstack$c-count* intstack$c)
                                        (nth *intstack$c-stacki* intstack$c)))
                  (<= (nfix (nth *intstack$c-count* intstack$c))
                      (len (nth *intstack$c-stacki* intstack$c)))
                  (<= (nfix n) (nfix (nth *intstack$c-count* intstack$c))))
             (intstack$c-bits-consistent new-intstack$c))
    :hints(("Goal" :in-theory (enable* arith-equiv-forwarding)))))


(define intstack$c-member ((x :type (unsigned-byte 32))
                           (intstack$c))
  (and (< x (intstack$c-bits-length intstack$c))
       (eql (intstack$c-bitsi x intstack$c) 1)))

(define intstack$c-nth ((n natp :type (integer 0 *))
                        (intstack$c))
  :guard (and (< n (intstack$c-count intstack$c))
              (<= (intstack$c-count intstack$c) (intstack$c-stack-length intstack$c)))
  :split-types t
  (intstack$c-stacki (- (1- (intstack$c-count intstack$c)) n) intstack$c))



(define create-intstack$a () nil)

(define intstack$ap (intstack$a)
  :enabled t
  (and (u32-listp intstack$a)
       (no-duplicatesp intstack$a)))

(define intstack$a-member ((x :type (unsigned-byte 32)) intstack$a)
  :enabled t
  (consp (ec-call (member-equal (nfix x) intstack$a))))

(define intstack$a-push ((x :type (unsigned-byte 32)) intstack$a)
  :enabled t
  (ec-call (add-to-set-equal (nfix x) intstack$a)))

(define intstack$a-count (intstack$a)
  :enabled t
  (len intstack$a))

(define intstack$a-pop (intstack$a)
  :guard (< 0 (intstack$a-count intstack$a))
  :enabled t
  (cdr intstack$a))

(define intstack$a-rewind ((n :type (unsigned-byte 32))
                           intstack$a)
  :guard (<= n (intstack$a-count intstack$a))
  :enabled t
  (ec-call (nthcdr (- (len intstack$a) (nfix n)) intstack$a)))

(local (defthm true-listp-when-u32-listp
         (implies (u32-listp x)
                  (true-listp x))))

(define intstack$a-nth ((n natp :type (integer 0 *))
                        (intstack$a intstack$ap))
  :guard (< n (intstack$a-count intstack$a))
  :prepwork ((local (in-theory (enable nth-in-u32-listp-natp))))
  :enabled t
  (lnfix (nth n intstack$a)))


(define intstack-corr (intstack$c intstack$a)
  :non-executable t
  :enabled t
  :verify-guards nil
  (and (intstack$c-bits-consistent intstack$c)
       (intstack$c-stack-elems-in-bounds intstack$c)
       (equal intstack$a (rev (take (nth *intstack$c-count* intstack$c)
                                    (nth *intstack$c-stacki* intstack$c))))
       (no-duplicatesp intstack$a)
       (natp (nth *intstack$c-count* intstack$c))
       (<= (nth *intstack$c-count* intstack$c)
           (len (nth *intstack$c-stacki* intstack$c)))
       (u32-listp (nth *intstack$c-stacki* intstack$c))))


(local (defthm intstack$c-bits-consistent-of-empty
         (intstack$c-bits-consistent '(nil nil 0))
         :hints(("Goal" :in-theory (enable intstack$c-bits-consistent)))))

(local (defthm intstack$c-stack-elems-in-bounds-of-empty
         (intstack$c-stack-elems-in-bounds '(nil nil 0))
         :hints(("Goal" :in-theory (enable intstack$c-stack-elems-in-bounds)))))


(local (in-theory (enable intstack$c-bits-consistent-necc
                          intstack$c-bits-consistent-implies-not-member
                          intstack$c-member
                          nth-in-u32-listp-natp
                          intstack$c-nth)))

;; (local (defthm nth-of-rev
;;          (equal (nth n (rev x))
;;                 (and (< (nfix n) (len x))
;;                      (nth (- (1- (len x)) (nfix n)) x)))
;;          :hints(("Goal" :in-theory (enable rev nth)))))
                  

(defabsstobj-events intstack
  :foundation intstack$c
  :corr-fn intstack-corr
  :recognizer (intstackp :logic intstack$ap :exec intstack$cp)
  :creator (create-intstack :logic create-intstack$a
                            :exec create-intstack$c)
  :exports ((intstack-count :logic intstack$a-count
                            :exec intstack$c-count)
            (intstack-push^ :logic intstack$a-push
                            :exec intstack$c-push
                            :protect t)
            (intstack-pop :logic intstack$a-pop
                          :exec intstack$c-pop
                          :protect t)
            (intstack-rewind^ :logic intstack$a-rewind
                              :exec intstack$c-rewind
                              :protect t)
            (intstack-member^ :logic intstack$a-member
                              :exec intstack$c-member)
            (intstack-nth :logic intstack$a-nth
                          :exec intstack$c-nth)))

(define intstack-push ((x natp) intstack)
  :enabled t
  (mbe :logic (non-exec (add-to-set-equal (nfix x) intstack))
       :exec (if (<= (the (integer 0 *) x) #xffffffff)
                 (intstack-push^ x intstack)
               (ec-call (intstack-push^ x intstack)))))

(define intstack-rewind ((n natp) intstack)
  :enabled t
  :guard (< n (intstack-count intstack))
  (mbe :logic (non-exec (nthcdr (- (len intstack) (nfix n)) intstack))
       :exec (if (<= (the (integer 0 *) n) #xffffffff)
                 (intstack-rewind^ n intstack)
               (ec-call (intstack-rewind^ n intstack)))))

(define intstack-member ((x natp) intstack)
  :enabled t
  (mbe :logic (non-exec (consp (member (nfix x) intstack)))
       :exec (if (<= (the (integer 0 *) x) #xffffffff)
                 (intstack-member^ x intstack)
               (ec-call (intstack-member^ x intstack)))))

