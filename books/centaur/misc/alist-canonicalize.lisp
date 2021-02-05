; Copyright (C) 2021 Centaur Technology
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

(include-book "duplicates")
(include-book "std/osets/top" :dir :system)
(include-book "std/alists/alist-equiv" :dir :system)
(include-book "std/alists/abstract" :dir :system)
(local (include-book "std/util/termhints" :dir :system))
(local (include-book "std/osets/under-set-equiv" :dir :system))
(local (include-book "std/alists/fast-alist-clean" :dir :System))
(local (include-book "std/osets/element-list" :dir :System))
(local (in-theory (disable set::mergesort)))


(local (defthm not-member-when-setp
         (implies (and (<< k (car x))
                       (set::setp x))
                  (not (member k x)))
         :hints(("Goal" :in-theory (enable set::setp
                                           <<-irreflexive
                                           <<-transitive)))))


(local
 (defthm no-duplicatesp-when-setp
   (implies (set::setp x)
            (no-duplicatesp x))
   :hints(("Goal" :in-theory (enable set::setp)))))





(local
 (defthm member-pair-implies-member-alist-keys
   (implies (and (member pair x)
                 (consp pair))
            (member (car pair) (alist-keys x)))
   :hints(("Goal" :in-theory (enable alist-keys)))))

;; If we have no duplicate alist keys, then there are not two pairs that both have the same car.
(local
 (defthmd no-duplicate-alist-keys-implies-pairs-unique
   (implies (and (no-duplicatesp (alist-keys x))
                 (member pair1 x)
                 (member pair2 x)
                 (consp pair1)
                 (consp pair2))
            (iff (equal (car pair1) (car pair2))
                 (equal pair1 pair2)))
   :hints(("Goal" :in-theory (enable alist-keys)))))

(local (include-book "std/alists/hons-assoc-equal" :dir :system))

(local (defthm hons-assoc-equal-when-member-alist-keys
         (implies (member k (alist-keys x))
                  (hons-assoc-equal k x))
         :hints(("Goal" :in-theory (enable alist-keys)))))

(local (defthm member-of-dup-witness
         (implies (not (no-duplicatesp x))
                  (member-equal (dup-witness x) x))
         :hints(("Goal" :in-theory (enable dup-witness no-duplicatesp)))))

(local (defthm alist-keys-of-member-of-hons-assoc-equal
         (implies (hons-assoc-equal k x)
                  (equal (alist-keys (member-equal (hons-assoc-equal k x) x))
                         (member-equal k (alist-keys x))))
         :hints(("Goal" :in-theory (enable alist-keys)))))

(local (defthm alist-keys-of-cdr-member-of-hons-assoc-equal
         (implies (hons-assoc-equal k x)
                  (equal (alist-keys (cdr (member-equal (hons-assoc-equal k x) x)))
                         (cdr (member-equal k (alist-keys x)))))
         :hints(("Goal" :in-theory (enable alist-keys)))))

(local (defthm member-of-hons-assoc-equal
         (implies (hons-assoc-equal k x)
                  (member (hons-assoc-equal k x) x))))

(local (defthm member-of-hons-assoc-equal-member
         (implies (hons-assoc-equal k (cdr (member k2 x)))
                  (member (hons-assoc-equal k x) x))))

(local (defthm not-member-of-cdr-member-equal
         (implies (not (member k x))
                  (not (member k (cdr (member k1 x)))))))


(local (defthm duplicates-p-by-member
         (implies (and (member k x)
                       (member k (cdr (member k x))))
                  (not (no-duplicatesp x)))))


(encapsulate nil
  (local (in-theory (disable member-equal hons-assoc-equal no-duplicatesp)))

  (defthm duplicate-alist-keys-of-mergesort
    (implies (no-duplicatesp (alist-keys x))
             (no-duplicatesp (alist-keys (set::mergesort x))))
    :hints (("goal" :do-not-induct t)
            (use-termhint
             (b* ((dup-key (dup-witness (alist-keys (set::mergesort x))))
                  ((unless (member dup-key (cdr (member dup-key (alist-keys (set::mergesort x))))))
                   '(:use ((:instance no-duplicatesp-by-dup-witness
                            (x (alist-keys (set::mergesort x))))
                           (:instance mark-clause-is-true (x 'dup-key-not-member)))
                     :in-theory (disable no-duplicatesp-by-dup-witness)))
                  (pair1 (hons-assoc-equal dup-key (set::mergesort x)))
                  (tail  (cdr (member-equal pair1 (set::mergesort x))))
                  (pair2 (hons-assoc-equal dup-key tail))
                  ((unless (consp pair1))
                   '(:use ((:instance mark-clause-is-true (x 'pair1-not-consp)))))
                  ((unless (consp pair2))
                   '(:use ((:instance mark-clause-is-true (x 'pair2-not-consp)))))
                  ((unless (member pair1 x))
                   `(:use ((:instance mark-clause-is-true (x 'pair1-not-member))
                           (:instance member-of-hons-assoc-equal
                            (k ,(hq dup-key)) (x (set::mergesort x))))
                     :in-theory (disable member-of-hons-assoc-equal)))
                  ((unless (member pair2 x))
                   `(:use ((:instance mark-clause-is-true (x 'pair2-not-member))
                           ;; (:instance member-of-hons-assoc-equal-member
                           ;;  (k ,(hq dup-key)) (k2 ,(hq pair1)) (x (set::mergesort x)))
                           (:instance not-member-of-cdr-member-equal
                            (k ,(hq pair2)) (k1 ,(hq pair1)) (x (set::mergesort x)))
                           )
                     :in-theory (disable ;; member-of-hons-assoc-equal-member
                                 not-member-of-cdr-member-equal)))
                  ((unless (equal pair1 pair2))
                   `(:use ((:instance no-duplicate-alist-keys-implies-pairs-unique
                            (pair1 ,(acl2::hq pair1))
                            (pair2 ,(acl2::hq pair2)))
                           (:instance mark-clause-is-true (x 'pairs-not-equal)))))
                  ((unless (member pair1 tail))
                   `(:use ((:instance member-of-hons-assoc-equal
                            (k ,(hq dup-key)) (x ,(hq tail)))
                           (:instance mark-clause-is-true (x 'pair1-not-in-tail)))
                     :in-theory (disable member-of-hons-assoc-equal))))
               `(:use ((:instance duplicates-p-by-member
                        (k ,(hq pair1))
                        (x (set::mergesort x)))                     
                       (:instance mark-clause-is-true (x 'pairs-equal)))))))
    :otf-flg t))


(defthm hons-assoc-equal-when-member
    (implies (and (member pair x)
                  (consp pair)
                  (equal k (car pair))
                  (no-duplicatesp-equal (acl2::alist-keys x)))
             (equal (hons-assoc-equal k x) pair))
    :hints(("Goal" :in-theory (enable hons-assoc-equal acl2::alist-keys member)))
    :rule-classes nil)

(defthm hons-assoc-equal-of-mergesort
    (implies (no-duplicatesp-equal (acl2::alist-keys x))
             (equal (hons-assoc-equal k (set::mergesort x))
                    (hons-assoc-equal k x)))
    :hints (("goal" :use ((:instance hons-assoc-equal-when-member
                           (pair (hons-assoc-equal k (set::mergesort x))))
                          (:instance hons-assoc-equal-when-member
                           (pair (hons-assoc-equal k x))
                           (x (set::mergesort x)))
                          (:instance member-of-hons-assoc-equal
                           (x (set::mergesort x)))
                          (:instance member-of-hons-assoc-equal))
             :in-theory (disable ;; hons-assoc-equal-when-member
                                 member-of-hons-assoc-equal))))

(defthm no-duplicate-keys-of-fast-alist-fork
  (implies (no-duplicatesp-equal (alist-keys y))
           (no-duplicatesp-equal (alist-keys (fast-alist-fork x y)))))

(defthm no-duplicate-keys-of-fast-alist-clean
  (no-duplicatesp-equal (alist-keys (fast-alist-clean x))))


(defsection alistp-of-mergesort
  (define atom-witness (x)
    (if (atom x)
        nil
      (if (consp (car x))
          (atom-witness (cdr x))
        (car x)))
    ///
    (defthmd atom-witness-member-when-not-alistp
      (implies (and (true-listp x)
                    (not (alistp x)))
               (member-equal (atom-witness x) x))))

  (defun maybe-improper-alistp (x)
    (if (atom x)
        t
      (and (consp (car x))
           (maybe-improper-alistp (cdr x)))))

  (local (defthm member-atom-when-maybe-improper-alistp
           (implies (and (maybe-improper-alistp x) (atom k))
                    (not (member k x)))))
                    



  (defthm alistp-of-mergesort
    (implies (maybe-improper-alistp x)
             (alistp (set::mergesort x)))
    :hints (("goal" :use ((:instance atom-witness-member-when-not-alistp
                           (x (set::mergesort x)))))))


  (defthm maybe-improper-alistp-of-fast-alist-fork
    (implies (maybe-improper-alistp y)
             (maybe-improper-alistp (fast-alist-fork x y))))

  (defthm maybe-improper-alistp-of-fast-alist-clean
    (maybe-improper-alistp (fast-alist-clean x))))

(local (in-theory (disable fast-alist-clean)))



(defsection member-of-fast-alist-clean
  (local (in-theory (enable fast-alist-clean)))

  (defthm member-of-fast-alist-fork
    (iff (member-equal k (fast-alist-fork x y))
         (or (member-equal k y)
             (and (consp k)
                  (equal (hons-assoc-equal (car k) x) k)
                  (not (hons-assoc-equal (car k) y))))))

  (defthm member-of-fast-alist-clean
    (iff (member-equal k (fast-alist-clean x))
         (and (consp k)
              (equal k (hons-assoc-equal (car k) x))))))


(defsection element-list-p-of-fast-alist-clean

  (local (defthm cdr-last-when-element-list-p
           (implies (and (element-list-p x)
                         (not (element-list-final-cdr-p t)))
                    (equal (cdr (last x)) nil))))

  (defthm element-list-p-of-fast-alist-fork
    (implies (and (element-list-p x)
                  (element-list-p y))
             (element-list-p (fast-alist-fork x y))))

  (defthm element-list-p-of-fast-alist-clean
    (implies (element-list-p x)
             (element-list-p (fast-alist-clean x)))
    :hints(("Goal" :in-theory (enable fast-alist-clean)
            :cases ((element-list-final-cdr-p t))))))


(define alist-canonicalize (x)
  :returns (new-x alistp)
  (set::mergesort (fast-alist-free (fast-alist-clean x)))
  ///
  (defret hons-assoc-equal-of-<fn>
    (equal (hons-assoc-equal k new-x)
           (hons-assoc-equal k x)))

  (defret <fn>-under-alist-equiv
    (alist-equiv new-x x)
    :hints(("Goal" :in-theory (enable alist-equiv-when-agree-on-bad-guy))))

  (defret setp-of-<fn>
    (set::setp new-x))

  (defret no-duplicate-keys-of-<fn>
    (no-duplicatesp-equal (alist-keys new-x)))

  (defret <fn>-idempotent
    (equal (alist-canonicalize new-x) new-x)
    :hints(("Goal" :in-theory (enable set::double-containment
                                      set::pick-a-point-subset-strategy))))

  (defret element-list-p-of-<fn>
    (implies (element-list-p x)
             (element-list-p new-x)))

  (defret keyval-alist-p-of-<fn>
    (implies (keyval-alist-p x)
             (keyval-alist-p new-x))
    :hints (("goal" :use ((:functional-instance element-list-p-of-<fn>
                           (element-p (lambda (x) (and (consp x)
                                                       (keytype-p (car x))
                                                       (valtype-p (cdr x)))))
                           (element-example (lambda () (cons (keytype-example)
                                                             (valtype-example))))
                           (element-list-final-cdr-p keyval-alist-final-cdr-p)
                           (element-list-p keyval-alist-p)))))))

(define canonical-alist-p (x)
  (equal x (alist-canonicalize x))
  ///
  (defthm setp-when-canonical-alist-p
    (implies (canonical-alist-p x)
             (set::setp x))
    :rule-classes :forward-chaining)

  (defthm no-duplicate-keys-when-canonical-alist-p
    (implies (canonical-alist-p x)
             (no-duplicatesp-equal (alist-keys x)))
    :rule-classes :forward-chaining)

  (defthm alistp-when-canonical-alist-p
    (implies (canonical-alist-p x)
             (alistp x))
    :rule-classes :forward-chaining)

  (defthmd setp-when-canonical-alist-p-rw
    (implies (canonical-alist-p x)
             (set::setp x)))

  (defthmd no-duplicate-keys-when-canonical-alist-p-rw
    (implies (canonical-alist-p x)
             (no-duplicatesp-equal (alist-keys x))))

  (defthmd alistp-when-canonical-alist-p-rw
    (implies (canonical-alist-p x)
             (alistp x)))

  (defthm canonical-alist-p-of-alist-canonicalize
    (canonical-alist-p (alist-canonicalize x)))

  (defthm alist-canonicalize-when-canonical-alist-p
    (implies (canonical-alist-p x)
             (equal (alist-canonicalize x) x))))

(define set-diff-witness ((x set::setp) (y set::setp))
  :guard (not (equal x y))
  :returns (memb)
  
  :prepwork ((local (in-theory (enable set::double-containment)))
             (local (defthm member-equal-when-setp
                      (implies (set::setp x)
                               (iff (member-equal k x)
                                    (set::in k x)))
                      :hints(("Goal" :in-theory (enable set::in set::tail Set::head set::setp set::empty)))))
             (local (defthm head-of-difference-in-y
                      (implies (not (set::empty (set::difference x y)))
                               (not (set::in (set::head (set::difference x y)) y)))
                      :hints(("Goal" :use ((:instance set::difference-in
                                            (a (set::head (set::difference x y)))
                                            (x x) (y y)))
                              :in-theory (disable set::difference-in)))))
             (local (defthm head-of-difference-in-x
                      (implies (not (set::empty (set::difference x y)))
                               (set::in (set::head (set::difference x y)) x))
                      :hints(("Goal" :use ((:instance set::difference-in
                                            (a (set::head (set::difference x y)))
                                            (x x) (y y)))
                              :in-theory (disable set::difference-in)))))
             ;; (local (defthm in-nil-when-alistp
             ;;          (implies (alistp y)
             ;;                   (not (set::in nil y)))
             ;;          :hints(("Goal" :use ((:instance member-atom-when-alistp
             ;;                                (k nil) (x y)))))))
             )
  (if (set::subset x y)
      (let ((diff (set::difference y x)))
        (set::head diff))
    (let ((diff (set::difference x y)))
       (set::head diff)))
  ///
  (std::defretd <fn>-correct
    (implies (and (set::setp x)
                  (set::setp y)
                  (not (equal x y)))
             (iff (member-equal memb x)
                  (not (member-equal memb y))))))

(local (defthmd member-atom-when-alistp
         (implies (and (alistp x) (atom k))
                  (not (member k x)))))


(define canonical-alist-key-diff ((x canonical-alist-p)
                                  (y canonical-alist-p))
  :guard (not (equal x y))
  :returns (key)
             ;; (enable set::pick-a-point-subset-strategy))))))
  :guard-hints (("goal" :use ((:instance member-atom-when-alistp
                               (k (set-diff-witness x y))
                               (x x))
                              (:instance member-atom-when-alistp
                               (k (set-diff-witness x y))
                               (x y)))
                 :in-theory (enable set-diff-witness-correct)))
  ;; By set::double-containment, if alist-canonicalizes differ then one is not a subset of the other
  (car (set-diff-witness x y))
  ///
  (std::defretd lookup-of-canonical-alist-key-diff
    (implies (and (canonical-alist-p x)
                  (canonical-alist-p y)
                  (not (equal x y)))
             (not (equal (hons-assoc-equal key x) (hons-assoc-equal key y))))
    :hints (("goal" :use ((:instance hons-assoc-equal-when-member
                           (pair (set-diff-witness x y))
                           (k (car (set-diff-witness x y)))
                           (x x))
                          (:instance hons-assoc-equal-when-member
                           (pair (set-diff-witness x y))
                           (k (car (set-diff-witness x y)))
                           (x y))
                          (:instance set-diff-witness-correct)
                          (:instance member-of-hons-assoc-equal
                           (k (car (set-diff-witness x y)))
                           (x x))
                          (:instance member-of-hons-assoc-equal
                           (k (car (set-diff-witness x y)))
                           (x y)))
             :do-not-induct t
             :in-theory (e/d (member-atom-when-alistp)
                             (set-diff-witness-correct
                              member-of-hons-assoc-equal))))))



(local
 (defthm canonical-alistp-when-setp-and-no-duplicate-keys
   (implies (and (alistp x)
                 (set::setp x)
                 (no-duplicatesp-equal (alist-keys x)))
            (canonical-alist-p x))
   :hints(("goal" :in-theory (enable canonical-alist-p)
           :use ((:instance set-diff-witness-correct
                  (y (alist-canonicalize x))))
           :do-not-induct t)
          (use-termhint
           (b* ((xcanon (alist-canonicalize x))
                (diff-witness (set-diff-witness x xcanon))
                (key (car diff-witness))
                ((when (member-equal diff-witness xcanon))
                 `(:use ((:instance hons-assoc-equal-when-member
                          (pair ,(hq diff-witness)) (x ,(hq xcanon)) (k ,(hq key)))
                         (:instance member-of-hons-assoc-equal
                          (k ,(hq key)) (x ,(hq x))))
                   :in-theory (e/d (member-atom-when-alistp)
                                   (member-of-hons-assoc-equal)))))
             `(:use ((:instance hons-assoc-equal-when-member
                      (pair ,(hq diff-witness)) (x ,(hq x)) (k ,(hq key)))
                     (:instance member-of-hons-assoc-equal
                      (k ,(hq key)) (x ,(hq xcanon))))
               :in-theory (e/d (member-atom-when-alistp)
                               (member-of-hons-assoc-equal))))))
   :otf-flg t))


(defthmd canonical-alist-p-redef
  (equal (canonical-alist-p x)
         (and (alistp x)
              (set::setp x)
              (no-duplicatesp-equal (alist-keys x))))
  :hints(("Goal" :cases ((canonical-alist-p x)))))


