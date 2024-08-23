; FTY Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/fty/defset" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defset pos-set
  :parents (fty::fty-extensions fty::specific-types)
  :short "Fixtype of finite sets of positive integers."
  :elt-type pos
  :elementp-of-nil nil
  :pred pos-setp
  :fix pos-sfix
  :equiv pos-sequiv
  ///

  (defrule posp-of-head-when-pos-setp-type-prescription
    (implies (and (pos-setp x)
                  (not (set::emptyp x)))
             (posp (set::head x)))
    :rule-classes :type-prescription))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pos-set->=-pos ((set pos-setp) (x posp))
  :returns (yes/no booleanp)
  :parents (pos-set)
  :short "Check if all the positive integers in a given set
          are greater than or equal to a given positive integer."
  (or (set::emptyp set)
      (and (>= (set::head set) x)
           (pos-set->=-pos (set::tail set) x)))
  :prepwork
  ((defrulel verify-guards-lemma
     (implies (posp x)
              (rationalp x))))
  ///

  (defruled pos-set->=-pos-element
    (implies (and (pos-set->=-pos set x)
                  (set::in elem set))
             (>= elem x))
    :induct t)

  (defruled pos-set->=-pos-subset
    (implies (and (pos-set->=-pos set x)
                  (set::subset set1 set))
             (pos-set->=-pos set1 x))
    :induct t
    :enable (set::subset
             pos-set->=-pos-element))

  (defrule pos-set->=-pos-when-emptyp
    (implies (set::emptyp set)
             (pos-set->=-pos set x)))

  (defrule pos-set->=-pos-of-singleton
    (equal (pos-set->=-pos (set::insert elem nil) x)
           (>= elem x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pos-set-max ((set pos-setp))
  :returns (max posp)
  :parents (pos-set)
  :short "Maximum of a set of positive integers."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the set is empty, we return 1,
     which is the smallest positive integer."))
  (cond ((set::emptyp set) 1)
        (t (max (pos-fix (set::head set))
                (pos-set-max (set::tail set)))))
  :prepwork
  ((defrulel verify-guards-lemma
     (implies (posp x)
              (rationalp x))))
  ///

  (defruled pos-set-max->=-element
    (implies (and (pos-setp set)
                  (set::in elem set))
             (<= elem (pos-set-max set)))
    :rule-classes ((:linear :trigger-terms ((pos-set-max set))))
    :induct t
    :enable max)

  (defruled pos-set-max->=-subset
    (implies (and (pos-setp set2)
                  (set::subset set1 set2))
             (<= (pos-set-max set1)
                 (pos-set-max set2)))
    :rule-classes ((:linear :trigger-terms ((pos-set-max set1)
                                            (pos-set-max set2))))
    :induct t
    :enable (max set::subset)
    :hints ('(:use (:instance pos-set-max->=-element
                              (elem (set::head set1))
                              (set set2)))))

  (defrule pos-set-max-when-emptyp
    (implies (set::emptyp set)
             (equal (pos-set-max set)
                    1)))

  (defrule pos-set-max-of-singleton
    (equal (pos-set-max (set::insert elem nil))
           (pos-fix elem))
    :enable (pos-fix max)))
