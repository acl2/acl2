; A lightweight book about the built-in function first-n-ac.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "append"))
(local (include-book "revappend"))

(in-theory (disable first-n-ac))

(defthm consp-of-first-n-ac
  (equal (consp (first-n-ac i l ac))
         (or (posp i)
             (consp ac)))
  :hints (("Goal" :induct (first-n-ac i l ac)
           :in-theory (enable first-n-ac))))

(defthm first-n-ac-of-cons
  (equal (first-n-ac n (cons a x) ac)
         (if (posp n)
             (first-n-ac (+ -1 n) x (cons a ac))
           (revappend ac nil)))
  :hints (("Goal" :in-theory (enable first-n-ac))))

(defthm first-n-ac-of-append-arg3
  (equal (first-n-ac n x (append ac1 ac2))
         (append (revappend ac2 nil)
                 (first-n-ac n x ac1)))
  :hints (("Goal" :in-theory (enable revappend append first-n-ac))))

(defthm first-n-ac-of-cons-arg3
  (implies (syntaxp (not (equal ac *nil*))) ;prevent loops
           (equal (first-n-ac n x (cons val ac))
                  (append (revappend ac nil)
                          (first-n-ac n x (list val)))))
  :hints (("Goal" :use (:instance first-n-ac-of-append-arg3
                                  (ac1 (list val))
                                  (ac2 ac))
           :in-theory (e/d (append)
                           (first-n-ac-of-append-arg3)))))

(defthm first-n-ac-normalize-ac
  (implies (syntaxp (not (equal ac *nil*))) ;prevent loops
           (equal (first-n-ac i l ac)
                  (append (revappend ac nil)
                          (first-n-ac i l nil))))
  :hints (("Goal" :in-theory (enable revappend-normalize-acc first-n-ac))))

(defthm len-of-first-n-ac
  (equal (len (first-n-ac i l ac))
         (+ (len ac)
            (nfix i)))
  :hints (("Goal" :in-theory (enable first-n-ac))))

(defthm true-list-fix-of-first-n-ac
  (equal (true-list-fix (first-n-ac i l ac))
         (first-n-ac i l (true-list-fix ac)))
  :hints (("Goal" :induct (first-n-ac i l ac)
           :in-theory (enable first-n-ac true-list-fix))))

(defthm first-n-ac-of-0
  (equal (first-n-ac 0 i ac)
         (revappend ac nil))
  :hints (("Goal" :in-theory (enable first-n-ac))))

(defthm first-n-ac-iff
  (iff (first-n-ac n i ac)
       (or (posp n)
           (consp ac)))
  :hints (("Goal" :in-theory (enable first-n-ac))))

(defthm car-of-first-n-ac
  (equal (car (first-n-ac n i ac))
         (if (consp ac)
             (car (last ac))
           (if (zp n)
               nil
             (car i))))
  :hints (("Goal" :in-theory (enable first-n-ac))))

;; (defthm cdr-of-first-n-ac
;;   (equal (cdr (first-n-ac n i ac))
;;          (if (consp ac)
;;              (first-n-ac n i (butlast ac 1))
;;            (if (zp n)
;;                nil
;;              (first-n-ac (+ -1 n) (cdr i) ac))))
;;   :hints (("Goal" :in-theory (enable first-n-ac))))

(defthm first-n-ac-when-not-integerp-cheap
  (implies (not (integerp i))
           (equal (first-n-ac i l ac)
                  (revappend ac nil)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable first-n-ac))))
