; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "set-defs")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

(local (include-book "binary-tree"))
(local (include-book "bst-order"))
(local (include-book "bst"))
(local (include-book "heap-order"))
(local (include-book "heap"))
(local (include-book "set"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-in
  (x
   (tree binary-tree-p))
  (declare (xargs :type-prescription (booleanp (tree-in x tree))))
  :parents (implementation)
  :short "Determine if a value appears in the tree."
  :long
  (xdoc::topstring
   (xdoc::p
     "No assumptions are made about the structure of the tree, so this search
      takes linear time. In practice, this function is only used as part of the
      logical definition of @(tsee in) (which is provided a more efficient
      implementation with @(tsee mbe))."))
  (and (not (tree-emptyp tree))
       (or (equal x (tree-head tree))
           (tree-in x (tree-left tree))
           (tree-in x (tree-right tree))))
  :hints (("Goal" :in-theory (enable o< o-finp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule tree-in-when-tree-equiv-congruence
  (implies (tree-equiv x y)
           (equal (tree-in a x)
                  (tree-in a y)))
  :rule-classes :congruence
  :enable tree-equiv
  :expand ((tree-in a x)
           (tree-in a y)))

(defrule tree-in-of-tree-node
  (equal (tree-in x (tree-node head left right))
         (or (equal x head)
             (tree-in x left)
             (tree-in x right)))
  :enable tree-in)

(defruled tree-in-when-tree-emptyp
  (implies (tree-emptyp tree)
           (not (tree-in x tree)))
  :enable tree-in)

(defrule tree-in-when-tree-emptyp-cheap
  (implies (tree-emptyp tree)
           (not (tree-in x tree)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable tree-in-when-tree-emptyp)

(defrule tree-in-of-arg1-and-nil
  (not (tree-in x nil))
  :enable tree-in-when-tree-emptyp)

(defrule tree-in-of-tree-head
  (equal (tree-in (tree-head tree) tree)
         (not (tree-emptyp tree))))

(defruled tree-in-when-tree-in-of-tree-left
  (implies (tree-in x (tree-left tree))
           (tree-in x tree))
  :enable tree-in)

(defrule tree-in-when-tree-in-of-tree-left-forward-chaining
  (implies (tree-in x (tree-left tree))
           (tree-in x tree))
  :rule-classes :forward-chaining
  :enable tree-in-when-tree-in-of-tree-left)

(defrule tree-in-of-tree-left-when-not-tree-in-cheap
  (implies (not (tree-in x tree))
           (not (tree-in x (tree-left tree))))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

(defruled tree-in-when-tree-in-of-tree-right
  (implies (tree-in x (tree-right tree))
           (tree-in x tree))
  :enable tree-in)

(defrule tree-in-when-tree-in-of-tree-right-forward-chaining
  (implies (tree-in x (tree-right tree))
           (tree-in x tree))
  :rule-classes :forward-chaining
  :enable tree-in-when-tree-in-of-tree-right)

(defrule tree-in-of-tree-right-when-not-tree-in-cheap
  (implies (not (tree-in x tree))
           (not (tree-in x (tree-right tree))))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled tree-in-when-bst<-all-r
  (implies (bst<-all-r x tree)
           (not (tree-in x tree)))
  :induct t
  :enable (tree-in
           bst<-all-r))

(defrule tree-in-when-bst<-all-r-forward-chaining
  (implies (bst<-all-r x tree)
           (not (tree-in x tree)))
  :rule-classes :forward-chaining
  :enable tree-in-when-bst<-all-r)

(defruled tree-in-when-bst<-all-l
  (implies (bst<-all-l tree x)
           (not (tree-in x tree)))
  :induct t
  :enable (tree-in
           bst<-all-l))

(defrule tree-in-when-bst<-all-l-forward-chaining
  (implies (bst<-all-l tree x)
           (not (tree-in x tree)))
  :rule-classes :forward-chaining
  :enable tree-in-when-bst<-all-l)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled bst<-when-bst<-all-r-and-tree-in
  (implies (and (bst<-all-r x tree)
                (tree-in y tree))
           (bst< x y))
  :induct t
  :enable tree-in)

(defrule bst<-when-bst<-all-r-and-tree-in-forward-chaining
  (implies (and (bst<-all-r x tree)
                (tree-in y tree))
           (bst< x y))
  :rule-classes :forward-chaining
  :enable bst<-when-bst<-all-r-and-tree-in)

(defruled bst<-when-bst<-all-l-and-tree-in
  (implies (and (bst<-all-l tree y)
                (tree-in x tree))
           (bst< x y))
  :induct t
  :enable tree-in)

(defrule bst<-when-bst<-all-l-and-tree-in-forward-chaining
  (implies (and (bst<-all-l tree y)
                (tree-in x tree))
           (bst< x y))
  :rule-classes :forward-chaining
  :enable bst<-when-bst<-all-l-and-tree-in)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrulel tree-in-tree-right-when-not-bst<-of-tree-head
  (implies (and (bst-p tree)
                (not (tree-emptyp tree))
                (not (bst< (tree-head tree) x)))
           (not (tree-in x (tree-right tree))))
  :enable tree-in-when-bst<-all-r)

(defrulel tree-in-tree-right-when-not-bst<-of-tree-head-weak
  (implies (and (bst-p tree)
                (not (tree-emptyp tree))
                (bst< x (tree-head tree)))
           (not (tree-in x (tree-right tree))))
  :enable bst<-rules)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrulel tree-in-tree-left-when-not->>-of-tree-head
  (implies (and (bst-p tree)
                (not (tree-emptyp tree))
                (not (bst< x (tree-head tree))))
           (not (tree-in x (tree-left tree))))
  :enable tree-in-when-bst<-all-l)

(defrulel tree-in-tree-left-when-not->>-of-tree-head-weak
  (implies (and (bst-p tree)
                (not (tree-emptyp tree))
                (bst< (tree-head tree) x))
           (not (tree-in x (tree-left tree))))
  :enable bst<-rules)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule heap<-of-tree-head-and-arg2-when-tree-in-of-arg2
  (implies (and (heapp tree)
                (tree-in x tree))
           (not (heap< (tree-head tree) x)))
  :induct (tree-in x tree)
  :enable (tree-in
           heapp
           heap<-rules))

(defrule heap<-of-arg1-and-tree-head-when-tree-in-of-arg1
  (implies (and (heapp tree)
                (tree-in x tree))
           (equal (heap< x (tree-head tree))
                  (not (equal x (tree-head tree)))))
  :induct (tree-in x tree)
  :enable (tree-in
           heapp
           heap<-rules))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule tree-in-of-tree-head-and-tree-left
  (implies (bst-p tree)
           (not (tree-in (tree-head tree)
                         (tree-left tree)))))

(defrule tree-in-of-tree-head-and-tree-right
  (implies (bst-p tree)
           (not (tree-in (tree-head tree)
                         (tree-right tree)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled tree-head-when-heapp-and-tree-in-tree-head
  (implies (and (heapp x)
                (heapp y)
                (tree-in (tree-head x) y)
                (tree-in (tree-head y) x))
           (equal (tree-head x)
                  (tree-head y)))
  :enable heap<-rules
  :disable heap<-of-arg1-and-tree-head-when-tree-in-of-arg1
  :use ((:instance heap<-of-arg1-and-tree-head-when-tree-in-of-arg1
                   (x (tree-head x))
                   (tree y))
        (:instance heap<-of-arg1-and-tree-head-when-tree-in-of-arg1
                   (x (tree-head y))
                   (tree x))))

(defruled tree-head-when-heapp-and-tree-in-tree-head-syntaxp
  (implies (and (tree-in (tree-head x) y)
                ;; TODO: use loop-stoppers instead of syntaxp
                (syntaxp (<< y x))
                (heapp x)
                (heapp y)
                (tree-in (tree-head y) x))
           (equal (tree-head x)
                  (tree-head y)))
  :use tree-head-when-heapp-and-tree-in-tree-head)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define in
  (x
   (set setp))
  (declare (xargs :type-prescription (booleanp (in x set))))
  :parents (set)
  :short "Determine if a value is a member of the @(see set)."
  :long
  (xdoc::topstring
   (xdoc::p
     "Time complexity: @($O(log(n))$)."))
  (mbe :logic (tree-in x (sfix set))
       :exec (and (not (emptyp set))
                  (or (equal x (head set))
                      (if (bst< x (head set))
                          (in x (left set))
                        (in x (right set))))))
  :no-function t
  :inline t

  ;; Verified below
  :verify-guards nil
  ///

  (defruled tree-in-of-sfix-becomes-in-exec
    (equal (tree-in x (sfix set))
           (and (not (emptyp set))
                (or (equal x (head set))
                    (if (bst< x (head set))
                        (in x (left set))
                      (in x (right set))))))
    :enable (tree-in
             sfix
             emptyp
             head
             in
             left
             right))

  (verify-guards in$inline
    :hints (("Goal" :in-theory (enable emptyp)
                    :use tree-in-of-sfix-becomes-in-exec))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule in-when-set-equiv-congruence
  (implies (set-equiv x y)
           (equal (in a x)
                  (in a y)))
  :rule-classes :congruence
  :enable (set-equiv
           in))

;; TODO: disable by default? The RHS is quite large
(defrule in-of-tree-node
  (equal (in x (tree-node head left right))
         (and (setp (tree-fix left))
              (setp (tree-fix right))
              (bst<-all-l left head)
              (bst<-all-r head right)
              (heap<-all-l left head)
              (heap<-all-l right head)
              (or (equal x head)
                  (in x left)
                  (in x right))))
  :enable (in
           sfix
           setp))

(defruled in-when-emptyp
  (implies (emptyp set)
           (not (in x set)))
  :enable in)

(defrule in-when-emptyp-cheap
  (implies (emptyp set)
           (not (in x set)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable in-when-emptyp)

(defrule in-of-arg1-and-nil
  (not (in x nil))
  :enable in-when-emptyp)

(defrule in-of-head
  (equal (in (head set) set)
         (not (emptyp set)))
  :enable (in
           head
           emptyp))

(defruled in-when-in-of-left
  (implies (in x (left set))
           (in x set))
  :enable (in
           left))

(defrule in-when-in-of-left-forward-chaining
  (implies (in x (left set))
           (in x set))
  :rule-classes :forward-chaining
  :enable in-when-in-of-left)

(defrule in-of-left-when-not-in-cheap
  (implies (not (in x set))
           (not (in x (left set))))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

(defruled in-when-in-of-right
  (implies (in x (right set))
           (in x set))
  :enable (in
           right))

(defrule in-when-in-of-right-forward-chaining
  (implies (in x (right set))
           (in x set))
  :rule-classes :forward-chaining
  :enable in-when-in-of-right)

(defrule in-of-right-when-not-in-cheap
  (implies (not (in x set))
           (not (in x (right set))))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled in-when-bst<-all-r
  (implies (bst<-all-r x set)
           (not (in x set)))
  :enable (in
           sfix))

(defrule in-when-bst<-all-r-forward-chaining
  (implies (bst<-all-r x set)
           (not (in x set)))
  :rule-classes :forward-chaining
  :enable in-when-bst<-all-r)

(defruled in-when-bst<-all-l
  (implies (bst<-all-l set x)
           (not (in x set)))
  :enable (in
           sfix))

(defrule in-when-bst<-all-l-forward-chaining
  (implies (bst<-all-l set x)
           (not (in x set)))
  :rule-classes :forward-chaining
  :enable in-when-bst<-all-l)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled bst<-when-bst<-all-r-and-in
  (implies (and (bst<-all-r x tree)
                (in y tree))
           (bst< x y))
  :enable (in
           sfix))

(defrule bst<-when-bst<-all-r-and-in-forward-chaining
  (implies (and (bst<-all-r x tree)
                (in y tree))
           (bst< x y))
  :rule-classes :forward-chaining
  :enable bst<-when-bst<-all-r-and-in)

(defruled bst<-when-bst<-all-l-and-in
  (implies (and (bst<-all-l tree y)
                (in x tree))
           (bst< x y))
  :enable (in
           sfix))

(defrule bst<-when-bst<-all-l-and-in-forward-chaining
  (implies (and (bst<-all-l tree y)
                (in x tree))
           (bst< x y))
  :rule-classes :forward-chaining
  :enable bst<-when-bst<-all-l-and-in)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: keep rule non-local + enabled?
(defrule in-right-when-not-bst<-of-head
  (implies (and (not (emptyp set))
                (not (bst< (head set) x)))
           (not (in x (right set))))
  :enable (in
           emptyp
           head
           right
           sfix))

(defrulel in-right-when-not-bst<-of-head-weak
  (implies (and (not (emptyp set))
                (bst< x (head set)))
           (not (in x (right set))))
  :enable bst<-rules)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrulel in-left-when-not->>-of-head
  (implies (and (not (emptyp set))
                (not (bst< x (head set))))
           (not (in x (left set))))
  :enable (in
            emptyp
            head
            left
            sfix))

(defrulel in-left-when-not->>-of-head-weak
  (implies (and (not (emptyp set))
                (bst< (head set) x))
           (not (in x (left set))))
  :enable bst<-rules)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule heap<-of-head-and-arg2-when-in-of-arg2
  (implies (and (not (emptyp set))
                (in x set))
           (not (heap< (head set) x)))
  :enable (emptyp
           in
           head
           sfix))

(defrule heap<-of-arg1-and-head-when-in-of-arg1
  (implies (and (not (emptyp set))
                (in x set))
           (equal (heap< x (head set))
                  (not (equal x (head set)))))
  :enable (emptyp
           in
           head
           sfix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule in-of-head-and-left
  (not (in (head set) (left set)))
  :enable (in
           head
           left
           sfix))

(defrule in-of-head-and-right
  (not (in (head set) (right set)))
  :enable (in
           head
           right
           sfix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthy tree-in-extra-rules
  '(tree-in-when-tree-emptyp
    tree-in-when-tree-in-of-tree-left
    tree-in-when-tree-in-of-tree-right
    tree-in-when-bst<-all-r
    tree-in-when-bst<-all-l

    ;; TODO: should these also be in bst<-all rules? (would require defruleset)
    bst<-when-bst<-all-r-and-tree-in
    bst<-when-bst<-all-l-and-tree-in

    tree-head-when-heapp-and-tree-in-tree-head-syntaxp))

(defthy in-extra-rules
  '(in-when-emptyp
    in-when-in-of-left
    in-when-in-of-right
    in-when-bst<-all-r
    in-when-bst<-all-l

    ;; TODO: same as above
    bst<-when-bst<-all-r-and-in
    bst<-when-bst<-all-l-and-in))
