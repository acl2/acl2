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

(include-book "binary-tree-defs")
(include-book "cardinality-defs")
(include-book "in-defs")
(include-book "set-defs")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

(local (include-book "binary-tree"))
(local (include-book "bst"))
(local (include-book "bst-order"))
(local (include-book "cardinality"))
(local (include-book "heap"))
(local (include-book "heap-order"))
(local (include-book "in"))
(local (include-book "set"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (disable bst<-rules)))

(std::make-define-config
  :no-function t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-join
  ((left binary-tree-p)
   (right binary-tree-p))
  :returns (tree binary-tree-p)
  :parents (implementation)
  :short "Join two trees which have previously been @(see tree-split)."
  :long
  (xdoc::topstring
   (xdoc::p
     "Technically it is not required that the two trees are a result of a
      previous split call. It is only expected that, given a join @('(tree-join
      left right)'), there exists some @('x') such that @('(bst<-all-l left x)')
      and @('(bst<-all-r x right)'), as is produced by @('split')."))
  (cond ((tree-emptyp left)
         (tree-fix right))
        ((tree-emptyp right)
         (tree-fix left))
        ((heap< (tree-head left)
                (tree-head right))
         (tree-node (tree-head right)
                    (tree-join left (tree-left right))
                    (tree-right right)))
        (t (tree-node (tree-head left)
                      (tree-left left)
                      (tree-join (tree-right left) right))))
  :measure (+ (acl2-count left)
              (acl2-count right))
  :hints (("Goal" :in-theory (enable o-p o< o-finp)))
  :verify-guards :after-returns)

(define tree-join-at
  (split
   (left binary-tree-p)
   (right binary-tree-p))
  (declare (ignore split))
  :returns (tree binary-tree-p)
  :parents (implementation)
  :short "Wrapper around @(tsee tree-join) annotated with a split point."
  :long
  (xdoc::topstring
   (xdoc::p
     "This @('split') argument is the value such that:")
   (xdoc::codeblock
     "(and (bst<-all-l left split)"
     "     (bst<-all-r split right))")
   (xdoc::p
     "While the @('split') argument is not used by the function, it is
      convenient to have so various rewriting rules can bind the variable
      appropriately without requiring @(':use') hints."))
  (tree-join left right)
  :inline t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: prefer tree-join-at?

(defrule tree-join-type-prescription
  (or (consp (tree-join left right))
      (equal (tree-join left right) nil))
  :rule-classes :type-prescription
  :induct t
  :enable (tree-join
           tree-fix))

(defrule tree-join-at-type-prescription
  (or (consp (tree-join-at split left right))
      (equal (tree-join-at split left right) nil))
  :rule-classes :type-prescription
  :enable tree-join-at)

(defrule tree-join-when-tree-equiv-congruence
  (implies (tree-equiv left1 left2)
           (equal (tree-join left1 right)
                  (tree-join left2 right)))
  :rule-classes :congruence
  :enable tree-equiv
  :expand ((tree-join left1 right)
           (tree-join left2 right)))

(defrule tree-join-at-when-tree-equiv-congruence
  (implies (tree-equiv left1 left2)
           (equal (tree-join-at split left1 right)
                  (tree-join-at split left2 right)))
  :rule-classes :congruence
  :enable tree-join-at)

(defrule tree-emptyp-of-tree-join
  (equal (tree-emptyp (tree-join left right))
         (and (tree-emptyp left)
              (tree-emptyp right)))
  :induct t
  :enable tree-join)

(defrule tree-emptyp-of-tree-join-at
  (equal (tree-emptyp (tree-join-at split left right))
         (and (tree-emptyp left)
              (tree-emptyp right)))
  :enable tree-join-at)

(defrule tree-join-when-nil-type-prescription
  (implies (and (equal left nil)
                (equal right nil))
      (equal (tree-join left right) nil))
  :rule-classes :type-prescription)

(defrule tree-join-split-when-nil-type-prescription
  (implies (and (equal left nil)
                (equal right nil))
      (equal (tree-join-at split left right) nil))
  :rule-classes :type-prescription
  :enable tree-join-at)

(defrule tree-in-of-tree-join
  (equal (tree-in x (tree-join left right))
         (or (tree-in x left)
             (tree-in x right)))
  :induct t
  :enable tree-join)

(defrule tree-in-of-tree-join-at
  (equal (tree-in x (tree-join-at split left right))
         (or (tree-in x left)
             (tree-in x right)))
  :enable tree-join-at)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule tree-nodes-count-of-tree-join
  (equal (tree-nodes-count (tree-join left right))
         (+ (tree-nodes-count left)
            (tree-nodes-count right)))
  :induct t
  :enable (tree-join
           tree-nodes-count
           fix))

(defrule tree-nodes-count-of-tree-join-at
  (equal (tree-nodes-count (tree-join-at split left right))
         (+ (tree-nodes-count left)
            (tree-nodes-count right)))
  :enable tree-join-at)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule bst<-all-l-of-tree-join
  (equal (bst<-all-l (tree-join left right) x)
         (and (bst<-all-l left x)
              (bst<-all-l right x)))
  :induct t
  :enable tree-join)

(defrule bst<-all-l-of-tree-join-at
  (equal (bst<-all-l (tree-join-at split left right) x)
         (and (bst<-all-l left x)
              (bst<-all-l right x)))
  :enable tree-join-at)

(defrule bst<-all-r-of-arg1-and-tree-join
  (equal (bst<-all-r x (tree-join left right))
         (and (bst<-all-r x left)
              (bst<-all-r x right)))
  :induct t
  :enable tree-join)

(defrule bst<-all-r-of-arg1-and-tree-join-at
  (equal (bst<-all-r x (tree-join-at split left right))
         (and (bst<-all-r x left)
              (bst<-all-r x right)))
  :enable tree-join-at)

;;;;;;;;;;;;;;;;;;;;

(defrule bst-p-of-tree-join-when-bst-p-and-split
  (implies (and (bst<-all-l left x)
                (bst<-all-r x right))
           (equal (bst-p (tree-join left right))
                  (and (bst-p left)
                       (bst-p right))))
  :induct t
  :enable (tree-join
           bst<-all-extra-rules))

(defrule bst-p-of-tree-join-at-when-bst-p-and-split
  (implies (and (bst<-all-l left split)
                (bst<-all-r split right))
           ;; This demonstrates the utility of tree-join-at. The variable split
           ;; does not appear free in the hyps.
           (equal (bst-p (tree-join-at split left right))
                  (and (bst-p left)
                       (bst-p right))))
  :enable tree-join-at)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule heap<-all-l-of-tree-join
  (implies (and (heap<-all-l left x)
                (heap<-all-l right x))
           (heap<-all-l (tree-join left right) x))
  :induct t
  :enable tree-join)

(defrule heap<-all-l-of-tree-join-at
  (implies (and (heap<-all-l left x)
                (heap<-all-l right x))
           (heap<-all-l (tree-join-at split left right) x))
  :enable tree-join-at)

(defrulel heapp-of-tree-join-when-tree-emptyp-of-left
  (implies (tree-emptyp left)
           (equal (heapp (tree-join left right))
                  (heapp right)))
  :enable tree-join)

(defrulel heapp-of-tree-join-at-when-tree-emptyp-of-left
  (implies (tree-emptyp left)
           (equal (heapp (tree-join-at split left right))
                  (heapp right)))
  :enable tree-join-at)

(defrulel heapp-of-tree-join-when-tree-emptyp-of-right
  (implies (tree-emptyp right)
           (equal (heapp (tree-join left right))
                  (heapp left)))
  :enable tree-join)

(defrulel heapp-of-tree-join-at-when-tree-emptyp-of-right
  (implies (tree-emptyp right)
           (equal (heapp (tree-join-at split left right))
                  (heapp left)))
  :enable tree-join-at)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Need to know trees are disjoint so that
;;   (not (heap< (tree-head left)
;;               (tree-head right)))
;; implies
;;   (heap< (tree-head right)
;;          (tree-head left))

(defruled tree-in-right-when-disjoint-and-tree-in-left
  (implies (and (bst<-all-l left x)
                (bst<-all-r x right)
                (tree-in y left))
           (not (tree-in y right)))
  :induct t
  :enable (tree-in
           bst<-rules))

(defrule tree-in-right-when-disjoint-and-tree-in-left-forward-chaining
  (implies (and (bst<-all-l left x)
                (bst<-all-r x right)
                (tree-in y left))
           (not (tree-in y right)))
  :rule-classes :forward-chaining
  :enable tree-in-right-when-disjoint-and-tree-in-left)

(defruled tree-in-left-when-disjoint-and-tree-in-right
  (implies (and (bst<-all-l left x)
                (bst<-all-r x right)
                (tree-in y right))
           (not (tree-in y left)))
  :induct t
  :enable (tree-in
           bst<-rules))

(defrule tree-in-left-when-disjoint-and-tree-in-right-forward-chaining
  (implies (and (bst<-all-l left x)
                (bst<-all-r x right)
                (tree-in y right))
           (not (tree-in y left)))
  :rule-classes :forward-chaining
  :enable tree-in-left-when-disjoint-and-tree-in-right)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled equal-of-tree-heads-when-bst<-all-l-and-bst<-all-r
  (implies (and (bst<-all-l left x)
                (bst<-all-r x right))
           (or (tree-emptyp left)
               (tree-emptyp right)
               (not (equal (tree-head left)
                           (tree-head right)))))
  :use ((:instance tree-in-right-when-disjoint-and-tree-in-left
                   (y (tree-head left)))))

(defrule equal-of-tree-heads-when-bst<-all-l-and-bst<-all-r-forward-chaining
  (implies (and (bst<-all-l left x)
                (bst<-all-r x right))
           (or (tree-emptyp left)
               (tree-emptyp right)
               (not (equal (tree-head left)
                           (tree-head right)))))
  :rule-classes :forward-chaining
  :use equal-of-tree-heads-when-bst<-all-l-and-bst<-all-r)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: can this proof be simplified using tree-join-at?
;; - (Might need to provide fake definitions of tree-join-at that look like
;;   tree-join but include the split value (which will always be the same).)
(encapsulate ()
  (defrulel lemma0
    (implies (and (not (tree-emptyp left))
                  (not (heap< (tree-head left) (tree-head right)))
                  (heap<-all-l (tree-left right)
                            (tree-head right))
                  (bst<-all-l left x)
                  (bst<-all-r x right)
                  (heap<-all-l (tree-right right)
                               (tree-head right))
                  (heap<-all-l (tree-right left)
                               (tree-head left)))
             (heap<-all-l (tree-join (tree-right left) right)
                          (tree-head left)))
    :enable (heap<-all-l-extra-rules
             heap<-rules)
    :disable equal-of-tree-heads-when-bst<-all-l-and-bst<-all-r-forward-chaining
    :use equal-of-tree-heads-when-bst<-all-l-and-bst<-all-r)

  (defrulel lemma1
    (implies (and (not (heap< (tree-head left) (tree-head right)))
                  (heapp (tree-right left))
                  (heap<-all-l (tree-left right)
                               (tree-head right))
                  (bst<-all-l left x)
                  (bst<-all-r x right)
                  (not (heap<-all-l (tree-right left)
                                    (tree-head left))))
             (not (heap<-all-l (tree-join (tree-right left) right)
                               (tree-head left))))
    :enable (tree-join
             heapp-extra-rules
             heap<-all-l-extra-rules)
    :disable equal-of-tree-heads-when-bst<-all-l-and-bst<-all-r-forward-chaining
    :use equal-of-tree-heads-when-bst<-all-l-and-bst<-all-r)

  (defrulel lemma2
    (implies (and (heapp (tree-left right))
                  (heap<-all-l (tree-join left (tree-left right))
                               (tree-head right))
                  (not (heap<-all-l (tree-left right)
                                    (tree-head right))))
             (not (heap<-all-l (tree-right right)
                               (tree-head right))))
    :enable (tree-join
             heapp-extra-rules
             heap<-all-l-extra-rules
             heap<-rules)
    :disable heap<-trichotomy
    :use ((:instance heap<-trichotomy
                     (x (tree-head (tree-left right)))
                     (y (tree-head left)))))

  (defrulel lemma3
    (implies (and (heap< (tree-head left) (tree-head right))
                  (heap<-all-l (tree-left left)
                               (tree-head left))
                  (heap<-all-l (tree-right left)
                               (tree-head left))
                  (not (heap<-all-l (tree-join left (tree-left right))
                                    (tree-head right)))
                  (heap<-all-l (tree-left right)
                               (tree-head right)))
             (not (heap<-all-l (tree-right right)
                               (tree-head right))))
    :enable heap<-all-l-extra-rules)

  ;; rename "when disjoint"
  (defrule heapp-of-tree-join
    (implies (and (bst<-all-l left x)
                  (bst<-all-r x right))
             (equal (heapp (tree-join left right))
                    (and (heapp left)
                         (heapp right))))
    :induct t
    :enable tree-join))

(defrule heapp-of-tree-join-at
  (implies (and (bst<-all-l left split)
                (bst<-all-r split right))
           (equal (heapp (tree-join-at split left right))
                  (and (heapp left)
                       (heapp right))))
  :enable tree-join-at)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule bst-p-of-tree-join-of-tree-left-and-tree-right-when-bst-p
  (implies (and (not (tree-emptyp tree))
                (bst-p tree))
           (equal (bst-p (tree-join (tree-left tree) (tree-right tree)))
                  (and (bst-p (tree-left tree))
                       (bst-p (tree-right tree))))))

(defrule bst-p-of-tree-join-at-of-tree-left-and-tree-right-when-bst-p
  (implies (and (not (tree-emptyp tree))
                (bst-p tree))
           (equal (bst-p (tree-join-at split (tree-left tree) (tree-right tree)))
                  (and (bst-p (tree-left tree))
                       (bst-p (tree-right tree)))))
  :enable tree-join-at)

(defrule bst-p-of-tree-join-of-tree-left-and-tree-right-when-setp
  (implies (and (not (tree-emptyp tree))
                (setp tree))
           (bst-p (tree-join (tree-left tree) (tree-right tree))))
  :enable setp)

(defrule bst-p-of-tree-join-at-of-tree-left-and-tree-right-when-setp
  (implies (and (not (tree-emptyp tree))
                (setp tree))
           (bst-p (tree-join-at split (tree-left tree) (tree-right tree))))
  :enable tree-join-at)

(defrule bst-p-of-tree-join-of-left-and-right-when-setp
  (implies (and (not (emptyp tree))
                (setp tree))
           (bst-p (tree-join (left tree) (right tree))))
  :enable (left
           right
           emptyp))

(defrule bst-p-of-tree-join-at-of-left-and-right-when-setp
  (implies (and (not (emptyp tree))
                (setp tree))
           (bst-p (tree-join-at split (left tree) (right tree))))
  :enable tree-join-at)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule heapp-of-tree-join-of-tree-left-and-tree-right-when-bst-p
  (implies (and (not (tree-emptyp tree))
                (bst-p tree))
           (equal (heapp (tree-join (tree-left tree) (tree-right tree)))
                  (and (heapp (tree-left tree))
                       (heapp (tree-right tree)))))
  :enable bst-p)

(defrule heapp-of-tree-join-at-of-tree-left-and-tree-right-when-bst-p
  (implies (and (not (tree-emptyp tree))
                (bst-p tree))
           (equal (heapp (tree-join-at split (tree-left tree) (tree-right tree)))
                  (and (heapp (tree-left tree))
                       (heapp (tree-right tree)))))
  :enable tree-join-at)

(defrule heapp-of-tree-join-of-tree-left-and-tree-right-when-setp
  (implies (and (not (tree-emptyp tree))
                (setp tree))
           (heapp (tree-join (tree-left tree) (tree-right tree))))
  :enable setp)

(defrule heapp-of-tree-join-at-of-tree-left-and-tree-right-when-setp
  (implies (and (not (tree-emptyp tree))
                (setp tree))
           (heapp (tree-join-at split (tree-left tree) (tree-right tree))))
  :enable tree-join-at)

(defrule heapp-of-tree-join-of-left-and-right-when-setp
  (implies (and (not (emptyp tree))
                (setp tree))
           (heapp (tree-join (left tree) (right tree))))
  :enable (left
           right
           emptyp))

(defrule heapp-of-tree-join-at-of-left-and-right-when-setp
  (implies (and (not (emptyp tree))
                (setp tree))
           (heapp (tree-join-at split (left tree) (right tree))))
  :enable tree-join-at)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule setp-of-tree-join-when-disjoint
  (implies (and (bst<-all-l left x)
                (bst<-all-r x right))
           (equal (setp (tree-join left right))
                  (and (setp (tree-fix left))
                       (setp (tree-fix right)))))
  :enable setp)

(defrule setp-of-tree-join-at-when-disjoint
  (implies (and (bst<-all-l left split)
                (bst<-all-r split right))
           (equal (setp (tree-join-at split left right))
                  (and (setp (tree-fix left))
                       (setp (tree-fix right)))))
  :enable tree-join-at)

;; Note: overshadowed by setp-of-tree-join-when-disjoint
(defruled setp-of-tree-join-of-left-and-right-when-setp
  (implies (and (not (emptyp tree))
                (setp tree))
           (setp (tree-join (left tree) (right tree))))
  :enable setp)

(defruled setp-of-tree-join-split-of-left-and-right-when-setp
  (implies (and (not (emptyp tree))
                (setp tree))
           (setp (tree-join-at split (left tree) (right tree))))
  :enable (tree-join-at
           setp-of-tree-join-of-left-and-right-when-setp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO
;; (subset left (tree-join left right))

;; TODO
;; (subset right (tree-join left right))
