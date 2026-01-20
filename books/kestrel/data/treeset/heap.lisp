; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(include-book "binary-tree-defs")
(include-book "heap-order-defs")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

(include-book "binary-tree")
(include-book "heap-order")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::make-define-config
  :no-function t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define heap<-all-l
  ((tree binary-tree-p)
   x)
  (declare (xargs :type-prescription (booleanp (heap<-all-l tree x))))
  :parents (binary-tree)
  :short "Check that all members of a tree are @(tsee heap<) some value."
  (or (tree-emptyp tree)
      (and (heap< (tree-head tree) x)
           (heap<-all-l (tree-left tree) x)
           (heap<-all-l (tree-right tree) x)))
  :hints (("Goal" :in-theory (enable o< o-finp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule heap<-all-l-when-tree-equiv-congruence
  (implies (tree-equiv x y)
           (equal (heap<-all-l x a)
                  (heap<-all-l y a)))
  :rule-classes :congruence
  :enable tree-equiv
  :expand ((heap<-all-l x a)
           (heap<-all-l y a)))

(defrule heap<-all-l-of-nil
  (heap<-all-l nil tree)
  :enable heap<-all-l)

(defruled heap<-all-l-when-tree-emptyp
  (implies (tree-emptyp tree)
           (heap<-all-l tree x))
  :enable heap<-all-l)

(defrule heap<-all-l-when-tree-emptyp-cheap
  (implies (tree-emptyp tree)
           (heap<-all-l tree x))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable heap<-all-l-when-tree-emptyp)

(defrule tree-emptyp-when-not-heap<-all-l-forward-chaining
  (implies (not (heap<-all-l tree x))
           (not (tree-emptyp tree)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable heap<-all-l)

(defrule heap<-all-l-of-arg1-and-tree-head
  (equal (heap<-all-l tree (tree-head tree))
         (tree-emptyp tree))
  :enable (heap<-all-l
           heap<-rules))

(defruled heap<-all-l-of-tree-left-when-heap<-all-l
  (implies (heap<-all-l tree x)
           (heap<-all-l (tree-left tree) x))
  :enable heap<-all-l)

(defrule heap<-all-l-of-tree-left-when-heap<-all-l-cheap
  (implies (heap<-all-l tree x)
           (heap<-all-l (tree-left tree) x))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable heap<-all-l-of-tree-left-when-heap<-all-l)

(defruled heap<-all-l-of-tree-right-when-heap<-all-l
  (implies (heap<-all-l tree x)
           (heap<-all-l (tree-right tree) x))
  :enable heap<-all-l)

(defrule heap<-all-l-of-tree-right-when-heap<-all-l-cheap
  (implies (heap<-all-l tree x)
           (heap<-all-l (tree-right tree) x))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable heap<-all-l-of-tree-right-when-heap<-all-l)

(defrule heap<-all-l-of-tree-node
  (equal (heap<-all-l (tree-node head left right) x)
         (and (heap< head x)
              (heap<-all-l left x)
              (heap<-all-l right x)))
  :enable heap<-all-l)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled heap<-all-l-weaken
  (implies (and (heap< y x)
                (heap<-all-l tree y))
           (heap<-all-l tree x))
  :induct t
  :enable (heap<-all-l
           heap<-rules))

(defruled heap<-all-l-weaken2
  (implies (and (not (heap< x y))
                (heap<-all-l tree y))
           (heap<-all-l tree x))
  :enable heap<-all-l-weaken
  :use ((:instance heap<-trichotomy)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled heap<-of-tree-head-when-heap<-all-l
  (implies (and (heap<-all-l tree x)
                (not (tree-emptyp tree)))
           (heap< (tree-head tree) x))
  :enable heap<-all-l)

(defrule heap<-of-tree-head-when-heap<-all-l-cheap
  (implies (and (heap<-all-l tree x)
                (not (tree-emptyp tree)))
           (heap< (tree-head tree) x))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil)))
  :enable heap<-of-tree-head-when-heap<-all-l)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fast-nonempty-heapp ((tree binary-tree-p))
  :guard (not (tree-emptyp tree))
  :returns (mv (heapp booleanp :rule-classes :type-prescription)
               (hash-max (unsigned-byte-p 32 hash-max)))
  (let ((hash-head (hash (tree-head tree))))
    (declare (type (unsigned-byte 32) hash-head))
    (if (tree-emptyp (tree-left tree))
        (if (tree-emptyp (tree-right tree))
            (mv t hash-head)
          (mv-let (heapp hash-right)
                  (fast-nonempty-heapp (tree-right tree))
            (declare (type (unsigned-byte 32) hash-right))
            (mv (and heapp
                     (heap<-with-hashes (tree-head (tree-right tree))
                                        (tree-head tree)
                                        hash-right
                                        hash-head))
                hash-head)))
      (if (tree-emptyp (tree-right tree))
          (mv-let (heapp hash-left)
                  (fast-nonempty-heapp (tree-left tree))
            (declare (type (unsigned-byte 32) hash-left))
            (mv (and heapp
                     (heap<-with-hashes (tree-head (tree-left tree))
                                        (tree-head tree)
                                        hash-left
                                        hash-head))
                hash-head))
        (mv-let (heapp hash-left)
                (fast-nonempty-heapp (tree-left tree))
          (declare (type (unsigned-byte 32) hash-left))
          (if heapp
              (mv-let (heapp hash-right)
                      (fast-nonempty-heapp (tree-right tree))
                (declare (type (unsigned-byte 32) hash-right))
                (mv (and heapp
                         (heap<-with-hashes (tree-head (tree-left tree))
                                            (tree-head tree)
                                            hash-left
                                            hash-head)
                         (heap<-with-hashes (tree-head (tree-right tree))
                                            (tree-head tree)
                                            hash-right
                                            hash-head))
                    hash-head))
            (mv nil hash-head))))))
  :hints (("Goal" :in-theory (enable o< o-finp)))

  ;; Verified below
  :verify-guards nil)

(defrulel fast-nonempty-heapp.hash-max
  (equal (mv-nth 1 (fast-nonempty-heapp tree))
         (hash (tree-head tree)))
  :expand (fast-nonempty-heapp tree))

(verify-guards fast-nonempty-heapp)

(defrulel fast-nonempty-heapp.heapp-when-tree-emptyp-cheap
  (implies (tree-emptyp tree)
           (equal (mv-nth 0 (fast-nonempty-heapp tree))
                  t))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable fast-nonempty-heapp)

(defruledl fast-nonempty-heapp.heapp
  (equal (mv-nth 0 (fast-nonempty-heapp tree))
         (and (mv-nth 0 (fast-nonempty-heapp (tree-left tree)))
              (mv-nth 0 (fast-nonempty-heapp (tree-right tree)))
              (heap<-all-l (tree-left tree)
                           (tree-head tree))
              (heap<-all-l (tree-right tree)
                           (tree-head tree))))
  :induct t
  :enable (fast-nonempty-heapp
           heap<-all-l-weaken))

(defrulel fast-nonempty-heapp.heapp-when-not-tree-emptyp-cheap
  (implies (not (tree-emptyp tree))
           (equal (mv-nth 0 (fast-nonempty-heapp tree))
                  (and (mv-nth 0 (fast-nonempty-heapp (tree-left tree)))
                       (mv-nth 0 (fast-nonempty-heapp (tree-right tree)))
                       (heap<-all-l (tree-left tree)
                                 (tree-head tree))
                       (heap<-all-l (tree-right tree)
                                 (tree-head tree)))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :disable fast-nonempty-heapp.heapp
  :use fast-nonempty-heapp.heapp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define heapp ((tree binary-tree-p))
  (declare (xargs :type-prescription (booleanp (heapp tree))))
  :parents (binary-tree)
  :short "Check the max heap property."
  (or (tree-emptyp tree)
      (mbe :logic (and (heapp (tree-left tree))
                       (heapp (tree-right tree))
                       (heap<-all-l (tree-left tree)
                                 (tree-head tree))
                       (heap<-all-l (tree-right tree)
                                 (tree-head tree)))
           :exec (b* (((mv heapp -)
                       (fast-nonempty-heapp tree)))
                   heapp)))
  :hints (("Goal" :in-theory (enable o< o-finp)))

  ;; Verified below
  :verify-guards nil)

(defruledl heapp-becomes-fast-nonempty-heapp
  (equal (heapp tree)
         (mv-nth 0 (fast-nonempty-heapp tree)))
  :induct t
  :enable heapp)

(verify-guards heapp
  :hints (("Goal" :in-theory (enable heapp-becomes-fast-nonempty-heapp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule heapp-when-tree-equiv-congruence
  (implies (tree-equiv x y)
           (equal (heapp x)
                  (heapp y)))
  :rule-classes :congruence
  :enable tree-equiv
  :expand ((heapp x)
           (heapp y)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled heapp-of-tree-left-when-tree-orderdp
  (implies (heapp tree)
           (heapp (tree-left tree)))
  :enable heapp)

(defrule heapp-of-tree-left-when-tree-orderdp-cheap
  (implies (heapp tree)
           (heapp (tree-left tree)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable heapp-of-tree-left-when-tree-orderdp)

(defruled heapp-of-tree-right-when-heapp
  (implies (heapp tree)
           (heapp (tree-right tree)))
  :enable heapp)

(defrule heapp-of-tree-right-when-heapp-cheap
  (implies (heapp tree)
           (heapp (tree-right tree)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable heapp-of-tree-right-when-heapp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled heapp-when-tree-emptyp
  (implies (tree-emptyp tree)
           (heapp tree))
  :enable heapp)

(defrule heapp-when-tree-emptyp-cheap
  (implies (tree-emptyp tree)
           (heapp tree))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable heapp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled heapp-when-not-tree-emptyp
  (implies (not (tree-emptyp tree))
           (equal (heapp tree)
                  (and (heapp (tree-left tree))
                       (heapp (tree-right tree))
                       (heap<-all-l (tree-left tree) (tree-head tree))
                       (heap<-all-l (tree-right tree) (tree-head tree)))))
  :enable heapp)

(defrule heapp-when-not-tree-emptyp-cheap
  (implies (not (tree-emptyp tree))
           (equal (heapp tree)
                  (and (heapp (tree-left tree))
                       (heapp (tree-right tree))
                       (heap<-all-l (tree-left tree) (tree-head tree))
                       (heap<-all-l (tree-right tree) (tree-head tree)))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable heapp-when-not-tree-emptyp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule heapp-of-tree-node
  (equal (heapp (tree-node head left right))
         (and (heapp left)
              (heapp right)
              (heap<-all-l left head)
              (heap<-all-l right head)))
  :enable heapp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled heap<-of-tree-head-and-tree-head-of-tree-left
  (implies (and (heapp tree)
                (not (tree-emptyp (tree-left tree))))
           (heap< (tree-head (tree-left tree))
                  (tree-head tree))))

(defruled heap<-of-tree-head-and-tree-head-of-tree-right
  (implies (and (heapp tree)
                (not (tree-emptyp (tree-right tree))))
           (heap< (tree-head (tree-right tree))
                  (tree-head tree))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthy heap<-all-l-extra-rules
  '(heap<-all-l-when-tree-emptyp
    heap<-all-l-of-tree-left-when-heap<-all-l
    heap<-all-l-of-tree-right-when-heap<-all-l
    heap<-all-l-weaken
    heap<-all-l-weaken2
    heap<-of-tree-head-when-heap<-all-l))

(defthy heapp-extra-rules
  '(heapp-of-tree-left-when-tree-orderdp
    heapp-of-tree-right-when-heapp
    heapp-when-tree-emptyp
    heapp-when-not-tree-emptyp
    heap<-of-tree-head-and-tree-head-of-tree-left
    heap<-of-tree-head-and-tree-head-of-tree-right))
