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
(include-book "defs")
(local (include-book "arithmetic"))


(defsection nat-listp-by-membership

  (encapsulate
   (((nlp-hyp) => *)
    ((nlp-lst) => *))
   (local (defun nlp-hyp () nil))
   (local (defun nlp-lst () nil))
   (defthmd nat-listp-by-membership-constraint
     (implies (and (nlp-hyp)
                   (member-equal a (nlp-lst)))
              (natp a))))

  (local (defun nlp-badguy (x)
           (if (atom x)
               nil
             (if (natp (car x))
                 (nlp-badguy (cdr x))
               (list (car x))))))

  (local (defthm nlp-badguy-under-iff
           (iff (nlp-badguy x)
                (not (nat-listp x)))))

  (local (defthm nlp-badguy-member
           (implies (nlp-badguy x)
                    (member-equal (car (nlp-badguy x)) x))))

  (local (defthm nlp-badguy-bad
           (implies (nlp-badguy x)
                    (not (natp (car (nlp-badguy x)))))))

  (defthm nat-listp-by-membership
    (implies (nlp-hyp)
             (equal (nat-listp (nlp-lst))
                    t))
    :hints(("Goal"
            :use ((:instance nat-listp-by-membership-constraint
                             (a (car (nlp-badguy (nlp-lst))))))))))




(defsection sum-nats
  :parents (utilities)
  :short "Sum a list of natural numbers."

  (defund tr-sum-nats (x acc)
    (declare (xargs :guard (and (nat-listp x)
                                (natp acc)))
             (type integer acc))
    (if (consp x)
        (tr-sum-nats (cdr x) (the integer (+ (car x) acc)))
      acc))

  (defund sum-nats (x)
    (declare (xargs :guard (nat-listp x)
                    :verify-guards nil))
    (mbe :logic (if (consp x)
                    (+ (nfix (car x))
                       (sum-nats (cdr x)))
                  0)
         :exec (tr-sum-nats x 0)))

  (local (in-theory (enable tr-sum-nats sum-nats)))

  (local (defthm lemma
           (implies (and (nat-listp x)
                         (natp acc))
                    (equal (tr-sum-nats x acc)
                           (+ (sum-nats x) acc)))))

  (verify-guards sum-nats)

  (defthm sum-nats-when-atom
    (implies (atom x)
             (equal (sum-nats x)
                    0)))

  (defthm sum-nats-of-cons
    (equal (sum-nats (cons a x))
           (+ (nfix a)
              (sum-nats x))))

  (defthm sum-nats-of-list-fix
    (equal (sum-nats (list-fix x))
           (sum-nats x)))

  (defthm sum-nats-of-append
    (equal (sum-nats (append x y))
           (+ (sum-nats x)
              (sum-nats y))))

  (defthm sum-nats-of-rev
    (equal (sum-nats (rev x))
           (sum-nats x)))

  (defthm sum-nats-of-revappend
    (equal (sum-nats (revappend x y))
           (+ (sum-nats x)
              (sum-nats y))))

  (defthm sum-nats-of-reverse
    (implies (true-listp x)
             (equal (sum-nats (reverse x))
                    (sum-nats x))))

  (defthm sum-nats-when-all-equalp
    (implies (all-equalp n x)
             (equal (sum-nats x)
                    (* (nfix n) (len x))))
    :hints(("Goal" :in-theory (disable all-equalp))))

  (defthm sum-nats-when-all-equalp-1
    ;; Special corollary to avoid free-variable in the commonly useful N=1 case.
    (implies (all-equalp 1 x)
             (equal (sum-nats x)
                    (len x)))
    :hints(("Goal" :in-theory (disable all-equalp)))))



(defsection max-nats
  :parents (utilities)
  :short "Maximum member in a list of naturals."

  :long "<p>Typically you would only use this on non-empty lists, but as a
reasonable default we say the maximum member of the empty list is
<tt>0</tt>.</p>"

  (defund max-nats (x)
    (declare (xargs :guard (nat-listp x)))
    (if (atom x)
        0
      (max (lnfix (car x))
           (max-nats (cdr x)))))

  (local (in-theory (enable max-nats)))

  (defthm max-nats-when-atom
    (implies (atom x)
             (equal (max-nats x) 0)))

  (defthm max-nats-of-cons
    (equal (max-nats (cons a x))
           (max (nfix a) (max-nats x))))

  (defthm natp-of-max-nats
    (natp (max-nats x))
    :rule-classes :type-prescription)

  (defthm max-nats-of-append
    (equal (max-nats (append x y))
           (max (max-nats x)
                (max-nats y))))

  (defthm max-nats-of-rev
    (equal (max-nats (rev x))
           (max-nats x)))

  (defthm max-nats-of-revappend
    (equal (max-nats (revappend x y))
           (max (max-nats x)
                (max-nats y)))))



(defsection min-nats
  :parents (utilities)
  :short "Minimum member in a list of naturals."

  :long "<p>Typically you would only use this on non-empty lists, but as a
reasonable default we say the minimum of the empty list is <tt>0</tt>.</p>"

  (defund min-nats (x)
    (declare (xargs :guard (nat-listp x)))
    (cond ((atom x)
           0)
          ((atom (cdr x))
           (lnfix (car x)))
          (t
           (min (lnfix (car x))
                (min-nats (cdr x))))))

  (local (in-theory (enable min-nats)))

  (defthm natp-of-min-nats
    (natp (min-nats x))
    :rule-classes :type-prescription)

  (defthm min-nats-bound
    (implies (consp x)
             (<= (min-nats x) (max-nats x)))
    :rule-classes ((:rewrite) (:linear))
    :hints(("Goal" :in-theory (enable min-nats max-nats)))))



(defsection nats-from
  :parents (utilities)
  :short "@(call nats-from) enumerates the naturals from <tt>[a, b)</tt>."

;; copied from aigpu, minus a couple of theorems.

  (defund nats-from (a b)
    ;; [a, a+1, ..., b)
    (declare (xargs :guard (and (natp a)
                                (natp b)
                                (<= a b))
                    :measure (nfix (- (nfix b) (nfix a)))))
    (let ((a (lnfix a))
          (b (lnfix b)))
      (if (mbe :logic (zp (- b a))
               :exec (= a b))
          nil
        (cons a (nats-from (+ 1 a) b)))))

  (local (in-theory (enable nats-from)))

  (defthm true-listp-of-nats-from
    (true-listp (nats-from a b))
    :rule-classes :type-prescription)

  (defthm nat-listp-of-nats-from
    (nat-listp (nats-from a b)))

  (defthm consp-of-nats-from
    (equal (consp (nats-from a b))
           (< (nfix a) (nfix b))))

  (defthm nats-from-self
    (equal (nats-from a a)
           nil))

  (defthm member-equal-nats-from
    (iff (member-equal x (nats-from a b))
         (and (natp x)
              (<= (nfix a) x)
              (< x (nfix b)))))

  ;; (defthm all-at-least-of-nats-from
  ;;     (all-at-least (nats-from a b) a)
  ;;     :hints(("Goal"
  ;;             :use ((:functional-instance all-by-membership
  ;;                                         (all-hyp  (lambda ()  t))
  ;;                                         (all-list (lambda ()  (nats-from a b)))
  ;;                                         (all      (lambda (x) (all-at-least x a)))
  ;;                                         (pred     (lambda (x) (<= a x))))))))

  (defthm no-duplicatesp-equal-of-nats-from
    (no-duplicatesp-equal (nats-from a b)))


  ;; (defthm empty-intersection-with-nats-from-when-too-small
  ;;     (implies (and (all-less-than x max)
  ;;                   (<= max a))
  ;;              (not (intersectp-equal x (nats-from a b))))
  ;;     :hints(("Goal"
  ;;             :in-theory (disable empty-intersection-by-bounds)
  ;;             :use ((:instance empty-intersection-by-bounds
  ;;                              (x x)
  ;;                              (x-max max)
  ;;                              (y (nats-from a b))
  ;;                              (y-min a))))))

  ;; (defthm all-less-than-of-nats-from
  ;;   (all-less-than (nats-from a b) b))



  (encapsulate
   ()
   (local (defun ind (k a b)
            (declare (xargs :measure (nfix (- (nfix b) (nfix a)))))
            (if (zp (- (nfix b) (nfix a)))
                (list k a b)
              (ind (+ -1 k) (+ 1 (nfix a)) b))))

   (defthm simpler-take-of-nats-from
     (equal (simpler-take k (nats-from a b))
            (if (< (nfix k) (nfix (- (nfix b) (nfix a))))
                (nats-from a (+ (nfix a) (nfix k)))
              (append (nats-from a b)
                      (repeat nil (- (nfix k) (nfix (- (nfix b) (nfix a))))))))
     :hints(("Goal"
             :induct (ind k a b)
             :in-theory (enable simpler-take nats-from)))))


  (encapsulate
   ()
   (local (defun ind (k a b)
            (declare (xargs :measure (nfix (- (nfix b) (nfix a)))))
            (if (zp (- (nfix b) (nfix a)))
                (list k a b)
              (ind (+ -1 k) (+ 1 (nfix a)) b))))

   (defthm nthcdr-of-nats-from
     (equal (nthcdr k (nats-from a b))
            (if (< (nfix k) (nfix (- (nfix b) (nfix a))))
                (nats-from (+ (nfix a) (nfix k)) b)
              nil))
     :hints(("Goal"
             :induct (ind k a b)
             :in-theory (enable nats-from)))))

  (defthm len-of-nats-from
    (equal (len (nats-from a b))
           (nfix (- (nfix b) (nfix a))))
    :hints(("Goal" :in-theory (enable nats-from))))

  (defthm car-of-nats-from
    (equal (car (nats-from a b))
           (if (< (nfix a) (nfix b))
               (nfix a)
             nil))
    :hints(("Goal" :in-theory (enable nats-from))))

  (encapsulate
   ()
   (local (defun ind (n a b)
            (declare (xargs :measure (nfix (- (nfix b) (nfix a)))))
            (if (zp (- (nfix b) (nfix a)))
                (list n a b)
              (ind (+ -1 n) (+ 1 (nfix a)) b))))

   (defthm nth-of-nats-from
     (equal (nth n (nats-from a b))
            (if (< (nfix n) (nfix (- (nfix b) (nfix a))))
                (+ (nfix a) (nfix n))
              nil))
     :hints(("Goal"
             :induct (ind n a b)
             :do-not '(generalize fertilize)
             :in-theory (enable nth nats-from))))))
