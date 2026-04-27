; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "DATA")

(include-book "std/util/defrule" :dir :system)

(include-book "centaur/bitops/ihsext-basics" :dir :system)

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/utilities/ordinals" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-theory (disable acl2::nfix-equal-to-zero))

(def-ruleset bitops-expensive-rules nil)
(def-ruleset bitops-cheap-rules nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; logcar

(defrule logcar-when-int-equiv-congruence
  (implies (acl2::int-equiv i0 i1)
           (equal (acl2::logcar i0)
                  (acl2::logcar i1)))
  :enable acl2::logcar)

(defrule bitp-of-logcar
  (bitp (acl2::logcar i)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; logcdr

(defrule logcdr-when-int-equiv-congruence
  (implies (acl2::int-equiv i0 i1)
           (equal (acl2::logcdr i0)
                  (acl2::logcdr i1)))
  :rule-classes :congruence
  :enable acl2::logcdr)

;; Probably unneeded due to type prescription rule bitops::logcdr-natp
;; (defrule natp-of-logcdr-when-natp
;;   (implies (natp i)
;;            (natp (acl2::logcdr i))))

(defrule unsigned-byte-p-of-logcdr
  (implies (and (unsigned-byte-p (+ 1 size) n)
                (natp size))
           (unsigned-byte-p size (acl2::logcdr n)))
  :enable (acl2::unsigned-byte-p**
           acl2::fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; logcons

(defrule logcons-when-bit-equiv-congruence
  (implies (acl2::bit-equiv b0 b1)
           (equal (acl2::logcons b0 i)
                  (acl2::logcons b1 i)))
  :rule-classes :congruence
  :enable acl2::logcons)

(defrule logcons-when-int-equiv-congruence
  (implies (acl2::int-equiv i0 i1)
           (equal (acl2::logcons b i0)
                  (acl2::logcons b i1)))
  :rule-classes :congruence
  :enable acl2::logcons)

(defrule unsigned-byte-p-of-logcons-when-posp
  (implies (and (posp size))
           (equal (unsigned-byte-p size (acl2::logcons b i))
                  (unsigned-byte-p (- size 1) (ifix i))))
  :enable (unsigned-byte-p
           integer-range-p
           acl2::logcons)
  ;; TODO: It would be nice to avoid mixing and matching libraries, but neither
  ;; seemed to be able to get this on its own.
  :prep-books ((include-book "arithmetic-5/top" :dir :system)
               (include-book "kestrel/arithmetic-light/expt" :dir :system)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; loghead

(defrule loghead-when-nat-equiv-of-arg1-congruence
  (implies (acl2::nat-equiv size0 size1)
           (equal (acl2::loghead size0 i)
                  (acl2::loghead size1 i)))
  :rule-classes :congruence
  :enable acl2::loghead)

(defrule loghead-when-int-equiv-of-arg2-congruence
  (implies (acl2::int-equiv i0 i1)
           (equal (acl2::loghead size i0)
                  (acl2::loghead size i1)))
  :rule-classes :congruence
  :enable acl2::loghead)

(defrule loghead-of-arg1-and-logcons
  (equal (acl2::loghead size (acl2::logcons b i))
         (if (equal (nfix size) 0)
             0
           (acl2::logcons b (acl2::loghead (- size 1) i))))
  :enable acl2::loghead**)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; logapp

(defruled logcar-of-logapp-when-equal-0
  (implies (equal (nfix size) 0)
           (equal (acl2::logcar (acl2::logapp size i j))
                  (acl2::logcar j)))
  :enable bitops::logcar-of-logapp-split)

(add-to-ruleset bitops-expensive-rules
  '(logcar-of-logapp-when-equal-0))

(defrule logcar-of-logapp-when-equal-0-cheap
  (implies (equal (nfix size) 0)
           (equal (acl2::logcar (acl2::logapp size i j))
                  (acl2::logcar j)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by logcar-of-logapp-when-equal-0)

(add-to-ruleset bitops-cheap-rules
  '(logcar-of-logapp-when-equal-0-cheap))

;; Unlike bitops, not using zp as a normal form
;; TODO: make cheap?
(defrule logcar-of-logapp-when-not-equal-0
  (implies (not (equal (nfix size) 0))
           (equal (acl2::logcar (acl2::logapp size i j))
                  (acl2::logcar i)))
  :enable nfix)

(defruled logcdr-of-logapp-when-equal-0
  (implies (equal (nfix size) 0)
           (equal (acl2::logcdr (acl2::logapp size i j))
                  (acl2::logcdr j)))
  :enable bitops::logcdr-of-logapp-split)

(add-to-ruleset bitops-expensive-rules
  '(logcdr-of-logapp-when-equal-0))

(defrule logcdr-of-logapp-when-equal-0-cheap
  (implies (equal (nfix size) 0)
           (equal (acl2::logcdr (acl2::logapp size i j))
                  (acl2::logcdr j)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by logcdr-of-logapp-when-equal-0)

(add-to-ruleset bitops-cheap-rules
  '(logcdr-of-logapp-when-equal-0-cheap))

(defrule logcdr-of-logapp-when-not-equal-0
  (implies (not (equal (nfix size) 0))
           (equal (acl2::logcdr (acl2::logapp size i j))
                  (acl2::logapp (- size 1) (acl2::logcdr i) j)))
  :enable nfix)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Induction schemes

(defund nat-nat-logcdr-induct (n m l)
  (declare (xargs :measure (nfix n)
                  :hints (("Goal" :in-theory (enable nfix)))))
  (if (or (equal (nfix n) 0)
          (equal (nfix m) 0)
          (equal (nfix l) 0))
      nil
    (nat-nat-logcdr-induct (- n 1) (- m 1) (acl2::logcdr l))))

(in-theory (enable (:i nat-nat-logcdr-induct)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund nat-cdr-induct (n list)
  (declare (xargs :measure (nfix n)
                  :hints (("Goal" :in-theory (enable nfix)))))
  (if (or (equal (nfix n) 0)
          (not (consp list)))
      nil
    (nat-cdr-induct (- n 1) (cdr list))))

(in-theory (enable (:i nat-cdr-induct)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Unused
;; (defund nat-nat-cdr-induct (n m list)
;;   (declare (xargs :measure (nfix n)
;;                   :hints (("Goal" :in-theory (enable nfix)))))
;;   (if (or (equal (nfix n) 0)
;;           (equal (nfix m) 0)
;;           (not (consp list)))
;;       nil
;;     (nat-nat-cdr-induct (- n 1) (- m 1) (cdr list))))
;;
;; (in-theory (enable (:i nat-nat-cdr-induct)))
