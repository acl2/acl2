; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TSET")

(include-book "std/util/defrule" :dir :system)

(include-book "../../internal/tree-defs")
(include-book "../../internal/bst-defs")
(include-book "zipper-defs")
(include-book "zip-side-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/utilities/arith-fix-and-equiv" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "kestrel/data/utilities/oset" :dir :system))

(local (include-book "kestrel/lists-light/len" :dir :system))

(local (include-book "zipper"))
(local (include-book "zip-step"))
(local (include-book "zip-side"))
(local (include-book "zip-order"))
(local (include-book "zip-step-side"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A zipper is determined by its tree, whether it is at a hole, and what
;; follows it. The tree need not be a search tree.

(local
  (define zip-position-induction ((zip1 zipp)
                                  (zip2 zipp))
    :type-prescription :none
    :verify-guards nil
    :enabled t
    (if (zip-at-end-p zip1)
        (list zip1 zip2)
      (zip-position-induction (zip-step-forward zip1)
                              (zip-step-forward zip2)))
    :measure (+ (* 2 (len (zip-after zip1)))
                (if (tree-empty-p (zip->focus zip1)) 0 1))
    :hints (("Goal" :in-theory
                    (enable zip-at-end-p-becomes-not-consp-of-zip-after)))))

(defrule zip-uniqueness
  (implies (and (equal (zip-plug zip1) (zip-plug zip2))
                (equal (tree-empty-p (zip->focus zip1))
                       (tree-empty-p (zip->focus zip2)))
                (equal (zip-after zip1) (zip-after zip2)))
           (equal (zip-fix zip1) (zip-fix zip2)))
  :rule-classes nil
  :hints (("Goal"
           :induct (zip-position-induction zip1 zip2)
           :in-theory (enable zip-at-end-p-becomes-not-consp-of-zip-after))
          (and stable-under-simplificationp
               '(:use ((:instance zip-step-backward-of-zip-step-forward
                                  (zip zip1))
                       (:instance zip-step-backward-of-zip-step-forward
                                  (zip zip2))
                       (:instance zip-end-of-zip-plug-when-zip-at-end-p
                                  (zip zip1))
                       (:instance zip-end-of-zip-plug-when-zip-at-end-p
                                  (zip zip2)))
                 :cases ((tree-empty-p (zip->focus zip1)))
                 :in-theory (e/d (zip-at-end-p-becomes-not-consp-of-zip-after)
                                 (zip-step-backward-of-zip-step-forward
                                  zip-end-of-zip-plug-when-zip-at-end-p))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Over a search tree, two zippers at elements with the same value are equal.

(defruledl zip-oset-after-when-same-value
  (implies (and (bstp (zip-plug zip1))
                (equal (zip-plug zip1) (zip-plug zip2))
                (not (tree-empty-p (zip->focus zip1)))
                (not (tree-empty-p (zip->focus zip2)))
                (equal (zip-value zip1) (zip-value zip2)))
           (equal (zip-oset-after zip1) (zip-oset-after zip2)))
  :enable (set::double-containment
           set::pick-a-point-subset-strategy)
  :disable in-of-zip-oset-after)

(defruledl zip-after-when-same-value
  (implies (and (bstp (zip-plug zip1))
                (equal (zip-plug zip1) (zip-plug zip2))
                (not (tree-empty-p (zip->focus zip1)))
                (not (tree-empty-p (zip->focus zip2)))
                (equal (zip-value zip1) (zip-value zip2)))
           (equal (zip-after zip1) (zip-after zip2)))
  :use ((:instance zip-oset-after-becomes-zip-after (zip zip1))
        (:instance zip-oset-after-becomes-zip-after (zip zip2))
        zip-oset-after-when-same-value))

(defrule zip-uniqueness-when-same-value
  (implies (and (zipp zip1)
                (zipp zip2)
                (bstp (zip-plug zip1))
                (equal (zip-plug zip1) (zip-plug zip2))
                (not (tree-empty-p (zip->focus zip1)))
                (not (tree-empty-p (zip->focus zip2)))
                (equal (zip-value zip1) (zip-value zip2)))
           (equal zip1 zip2))
  :rule-classes nil
  :use (zip-uniqueness
        zip-after-when-same-value))
