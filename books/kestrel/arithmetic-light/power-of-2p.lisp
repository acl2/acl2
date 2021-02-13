; A recognizer for a power of 2
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;dup
;define in terms of lg?
(defund power-of-2p (x)
  (declare (xargs :guard t))
  (and (natp x) ;otherwise, this would count 1/2 but not 1/4
       (= x (expt 2 (+ -1 (integer-length x))))))

;; (defthm integerp-when-power-of-2p
;;   (implies (power-of-2p x)
;;            (integerp x))
;;   :rule-classes ((:rewrite :backchain-limit-lst (0)))
;;   :hints (("Goal" :in-theory (enable power-of-2p))))

(defthm power-of-2p-forward-to-natp
  (implies (power-of-2p x)
           (natp x))
  :rule-classes ((:forward-chaining))
  :hints (("Goal" :in-theory (enable power-of-2p))))

;; (defthm natp-when-power-of-2p
;;   (implies (power-of-2p x)
;;            (natp x))
;;   :rule-classes ((:rewrite :backchain-limit-lst (0)))
;;   :hints (("Goal" :in-theory (enable power-of-2p))))

(defthm expt-2-of-+-of--1-and-integer-length-when-power-of-2p-cheap
  (implies (acl2::power-of-2p x)
           (equal (expt 2 (+ -1 (integer-length x)))
                  x))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable acl2::power-of-2p))))
