; Copyright (C) 2025-2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "std/util/define" :dir :system)
(include-book "std/util/define-sk" :dir :system)
(include-book "std/util/defrule" :dir :system)

(include-book "internal/min-max-defs")
(include-book "set-defs")
(include-book "to-oset-defs")
(include-book "in-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))

(local (include-book "internal/tree"))
(local (include-book "internal/min-max"))
(local (include-book "internal/in-order"))
(local (include-book "set"))
(local (include-book "to-oset"))
(local (include-book "in"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (disable acl2::equal-of-booleans-cheap)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define min ((set setp))
  :parents (treeset)
  :short "The minimum element of a @(see treeset) (with respect to
          @(tsee <<))."
  :long
  (xdoc::topstring
   (xdoc::p
     "Time complexity: @($O(\\log(n))$).")
   (xdoc::p
     "If the set is empty (contrary to the guard), the logical result is
      @('nil')."))
  :guard (not (emptyp set))
  (mbe :logic (tree-min (fix set))
       :exec (tree-leftmost set))
  :inline t
  :guard-hints (("Goal" :in-theory (enable setp))))

;;;;;;;;;;;;;;;;;;;;

(defrule min-when-equiv-congruence
  (implies (equiv set0 set1)
           (equal (min set0)
                  (min set1)))
  :rule-classes :congruence
  :enable min)

(defruled min-when-emptyp
  (implies (emptyp set)
           (equal (min set)
                  nil))
  :enable (min
           emptyp))

(defrule min-when-emptyp-cheap
  (implies (emptyp set)
           (equal (min set)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by min-when-emptyp)

(defrule min-of-empty
  (equal (min (empty))
         nil)
  :enable min-when-emptyp)

(defrule in-of-min
  (equal (in (min set) set)
         (not (emptyp set)))
  :enable (min
           in
           emptyp))

(defrule <<-of-arg1-and-min-when-in
  (implies (in x set)
           (not (<< x (min set))))
  :enable (min
           in))

(defrule <<-of-min-when-in
  (implies (in x set)
           (equal (<< (min set) x)
                  (not (equal (min set) x))))
  :enable (min
           in))

;;;;;;;;;;;;;;;;;;;;

(defrule car-of-to-oset
  (equal (car (to-oset set))
         (min set))
  :enable (to-oset
           min
           break-abstraction))

(add-to-ruleset from-oset-theory '(car-of-to-oset))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk not-<<-all-l-sk (set x)
  :parents (min)
  :returns (yes/no booleanp)
  (forall (elem)
    (non-exec
      (implies (in elem set)
               (not (<< elem x))))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t not-<<-all-l-sk)))

(defrule not-<<-all-l-sk-type-prescription
  (booleanp (not-<<-all-l-sk set x))
  :rule-classes :type-prescription)

(defrule not-<<-all-l-sk-when-equiv-congruence
  (implies (equiv set0 set1)
           (equal (not-<<-all-l-sk set0 x)
                  (not-<<-all-l-sk set1 x)))
  :rule-classes :congruence
  :enable acl2::equal-of-booleans-cheap
  :prep-lemmas
  ((defrule not-<<-all-l-sk-when-not-<<-all-l-sk-of-equiv
     (implies (and (equiv set0 set1)
                   (not-<<-all-l-sk set1 x))
              (not-<<-all-l-sk set0 x))
     :expand ((not-<<-all-l-sk set0 x))
     :enable not-<<-all-l-sk-necc)))

(defrule not-<<-all-l-sk-of-arg1-and-min
  (not-<<-all-l-sk set (min set))
  :enable not-<<-all-l-sk)

(defruled equal-of-min-becomes-sk
  (equal (equal (min set) x)
         (if (emptyp set)
             (equal x nil)
           (and (in x set)
                (not-<<-all-l-sk set x))))
  :use (:instance not-<<-all-l-sk-necc
                  (elem (min set))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define max ((set setp))
  :parents (treeset)
  :short "The maximum element of a @(see treeset) (with respect to
          @(tsee <<))."
  :long
  (xdoc::topstring
    (xdoc::p
      "Time complexity: @($O(\\log(n))$)."))
  :guard (not (emptyp set))
  (mbe :logic (tree-max (fix set))
       :exec (tree-rightmost set))
  :inline t
  :guard-hints (("Goal" :in-theory (enable setp))))

;;;;;;;;;;;;;;;;;;;;

(defrule max-when-equiv-congruence
  (implies (equiv set0 set1)
           (equal (max set0)
                  (max set1)))
  :rule-classes :congruence
  :enable max)

(defruled max-when-emptyp
  (implies (emptyp set)
           (equal (max set)
                  nil))
  :enable (max
           emptyp))

(defrule max-when-emptyp-cheap
  (implies (emptyp set)
           (equal (max set)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by max-when-emptyp)

(defrule max-of-empty
  (equal (max (empty))
         nil)
  :enable max-when-emptyp)

(defrule in-of-max
  (equal (in (max set) set)
         (not (emptyp set)))
  :enable (max
           in
           emptyp))

(defrule <<-of-max-when-in
  (implies (in x set)
           (not (<< (max set) x)))
  :enable (max
           in))

(defrule <<-of-arg1-and-max-when-in
  (implies (in x set)
           (equal (<< x (max set))
                  (not (equal (max set) x))))
  :enable (max
           in))

;;;;;;;;;;;;;;;;;;;;

(defrule car-of-last-of-to-oset
  (equal (car (last (to-oset set)))
         (max set))
  :enable (to-oset
           max
           break-abstraction))

(add-to-ruleset from-oset-theory '(car-of-last-of-to-oset))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk not-<<-all-r-sk (x set)
  :parents (max)
  :returns (yes/no booleanp)
  (forall (elem)
    (non-exec
      (implies (in elem set)
               (not (<< x elem))))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t not-<<-all-r-sk)))

(defrule not-<<-all-r-sk-type-prescription
  (booleanp (not-<<-all-r-sk set x))
  :rule-classes :type-prescription)

(defrule not-<<-all-r-sk-when-equiv-congruence
  (implies (equiv set0 set1)
           (equal (not-<<-all-r-sk x set0)
                  (not-<<-all-r-sk x set1)))
  :rule-classes :congruence
  :enable acl2::equal-of-booleans-cheap
  :prep-lemmas
  ((defrule not-<<-all-r-sk-when-not-<<-all-r-sk-of-equiv
     (implies (and (equiv set0 set1)
                   (not-<<-all-r-sk x set1))
              (not-<<-all-r-sk x set0))
     :expand ((not-<<-all-r-sk x set0))
     :enable not-<<-all-r-sk-necc)))

(defrule not-<<-all-r-sk-of-arg1-and-max
  (not-<<-all-r-sk (max set) set)
  :enable not-<<-all-r-sk)

(defruled equal-of-max-becomes-sk
  (equal (equal (max set) x)
         (if (emptyp set)
             (equal x nil)
           (and (in x set)
                (not-<<-all-r-sk x set))))
  :use (:instance not-<<-all-r-sk-necc
                  (elem (max set))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: min = max implies empty or card 1
