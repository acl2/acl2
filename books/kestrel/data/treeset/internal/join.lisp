; Copyright (C) 2025-2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "tree-defs")
(include-book "bst-defs")
(include-book "heap-defs")
(include-book "count-defs")
(include-book "in-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/data/utilities/total-order/total-order" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "tree"))
(local (include-book "bst"))
(local (include-book "heap-order"))
(local (include-book "heap"))
(local (include-book "count"))
(local (include-book "in"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Rules about disjointness

(defruled equal-of-tree->heads-when-<<-all-l-and-<<-all-r
  (implies (and (<<-all-l left x)
                (<<-all-r x right))
           (or (tree-empty-p left)
               (tree-empty-p right)
               (not (equal (tagged-element->elem (tree->head left))
                           (tagged-element->elem (tree->head right))))))
  :use ((:instance tree-in-right-when-disjoint-and-tree-in-left
                   (y (tagged-element->elem (tree->head left))))))

(defrule equal-of-tree->heads-when-<<-all-l-and-<<-all-r-forward-chaining
  (implies (and (<<-all-l left x)
                (<<-all-r x right))
           (or (tree-empty-p left)
               (tree-empty-p right)
               (not (equal (tagged-element->elem (tree->head left))
                           (tagged-element->elem (tree->head right))))))
  :rule-classes :forward-chaining
  :use equal-of-tree->heads-when-<<-all-l-and-<<-all-r)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-join
  ((left treep)
   (right treep))
  :returns (tree treep)
  :parents (implementation)
  :short "Join two trees which have previously been @(see tree-split)."
  :long
  (xdoc::topstring
   (xdoc::p
     "Technically it is not required that the two trees are a result of a
      previous split call. It is only expected that, given a join
      @('(tree-join left right)'), there exists some @('x') such that
      @('(<<-all-l left x)') and @('(<<-all-r x right)'), as is produced by
      @('split')."))
  (cond ((tree-empty-p left)
         (tree-fix right))
        ((tree-empty-p right)
         (tree-fix left))
        ((heap<-with-tagged-element (tree->head left) (tree->head right))
         (tree-node (tree->head right)
                    (tree-join left (tree->left right))
                    (tree->right right)))
        (t (tree-node (tree->head left)
                      (tree->left left)
                      (tree-join (tree->right left) right))))
  :measure (+ (acl2-count left)
              (acl2-count right))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-join)))

(defrule tree-join-type-prescription
  (or (consp (tree-join left right))
      (equal (tree-join left right) nil))
  :rule-classes :type-prescription
  :use treep-of-tree-join
  :disable treep-of-tree-join)

(defrule tree-join-when-tree-equiv-of-arg1-congruence
  (implies (tree-equiv left0 left1)
           (equal (tree-join left0 right)
                  (tree-join left1 right)))
  :rule-classes :congruence
  :expand ((tree-join left0 right)
           (tree-join left1 right))
  :enable tree-equiv)

(defrule tree-join-when-tree-equiv-of-arg2-congruence
  (implies (tree-equiv right0 right1)
           (equal (tree-join left right0)
                  (tree-join left right1)))
  :rule-classes :congruence
  :expand ((tree-join left right0)
           (tree-join left right1))
  :enable tree-equiv)

(defrule tree-empty-p-of-tree-join
  (equal (tree-empty-p (tree-join left right))
         (and (tree-empty-p left)
              (tree-empty-p right)))
  :induct t
  :enable tree-join)

(defrule tree-join-when-nil-type-prescription
  (implies (and (equal left nil)
                (equal right nil))
      (equal (tree-join left right) nil))
  :rule-classes :type-prescription)

(defrule tree-in-of-tree-join
  (equal (tree-in x (tree-join left right))
         (or (tree-in x left)
             (tree-in x right)))
  :induct t
  :enable tree-join)

(defrule tree-nodes-count-of-tree-join
  (equal (tree-nodes-count (tree-join left right))
         (+ (tree-nodes-count left)
            (tree-nodes-count right)))
  :induct t
  :enable (tree-join
           tree-nodes-count
           acl2::fix))

(defrule <<-all-l-of-tree-join
  (equal (<<-all-l (tree-join left right) x)
         (and (<<-all-l left x)
              (<<-all-l right x)))
  :induct t
  :enable tree-join)

(defrule <<-all-r-of-arg1-and-tree-join
  (equal (<<-all-r x (tree-join left right))
         (and (<<-all-r x left)
              (<<-all-r x right)))
  :induct t
  :enable tree-join)

(defrule bst-p-of-tree-join-when-bst-p-and-split
  (implies (and (<<-all-l left x)
                (<<-all-r x right))
           (equal (bstp (tree-join left right))
                  (and (bstp left)
                       (bstp right))))
  :induct t
  :enable (tree-join
           data::<<-rules
           <<-all-extra-rules))

(defrule heap<-all-l-of-tree-join
  (implies (and (heap<-all-l left x)
                (heap<-all-l right x))
           (heap<-all-l (tree-join left right) x))
  :induct t
  :enable tree-join)

(defrulel heapp-of-tree-join-when-tree-empty-p-of-left
  (implies (tree-empty-p left)
           (equal (heapp (tree-join left right))
                  (heapp right)))
  :enable tree-join)

(defrulel heapp-of-tree-join-when-tree-empty-p-of-right
  (implies (tree-empty-p right)
           (equal (heapp (tree-join left right))
                  (heapp left)))
  :enable tree-join)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-join-at
  (split
   (left treep)
   (right treep))
  (declare (ignore split))
  :returns (tree treep)
  :parents (implementation)
  :short "Wrapper around @(tsee tree-join) annotated with a split point."
  :long
  (xdoc::topstring
   (xdoc::p
     "This @('split') argument is the value such that:")
   (xdoc::codeblock
     "(and (<<-all-l left split)"
     "     (<<-all-r split right))")
   (xdoc::p
     "While the @('split') argument is not used by the function, it is
      convenient to have so various rewriting rules can bind the variable
      appropriately without requiring @(':use') hints."))
  (tree-join left right)
  :inline t)

;;;;;;;;;;;;;;;;;;;;

;; TODO: prefer tree-join-at?

(in-theory (disable (:t tree-join-at)))

(defrule tree-join-at-type-prescription
  (or (consp (tree-join-at split left right))
      (equal (tree-join-at split left right) nil))
  :rule-classes :type-prescription
  :enable tree-join-at)

(defrule tree-join-at-when-tree-equiv-congruence
  (implies (tree-equiv left0 left1)
           (equal (tree-join-at split left0 right)
                  (tree-join-at split left1 right)))
  :rule-classes :congruence
  :enable tree-join-at)

(defrule tree-join-at-when-tree-equiv-of-arg2-congruence
  (implies (tree-equiv right0 right1)
           (equal (tree-join-at split left right0)
                  (tree-join-at split left right1)))
  :rule-classes :congruence
  :enable tree-join-at)

(defrule tree-empty-p-of-tree-join-at
  (equal (tree-empty-p (tree-join-at split left right))
         (and (tree-empty-p left)
              (tree-empty-p right)))
  :enable tree-join-at)

(defrule tree-join-split-when-nil-type-prescription
  (implies (and (equal left nil)
                (equal right nil))
      (equal (tree-join-at split left right) nil))
  :rule-classes :type-prescription
  :enable tree-join-at)

(defrule tree-in-of-tree-join-at
  (equal (tree-in x (tree-join-at split left right))
         (or (tree-in x left)
             (tree-in x right)))
  :enable tree-join-at)

(defrule tree-nodes-count-of-tree-join-at
  (equal (tree-nodes-count (tree-join-at split left right))
         (+ (tree-nodes-count left)
            (tree-nodes-count right)))
  :enable tree-join-at)

(defrule <<-all-l-of-tree-join-at
  (equal (<<-all-l (tree-join-at split left right) x)
         (and (<<-all-l left x)
              (<<-all-l right x)))
  :enable tree-join-at)

(defrule <<-all-r-of-arg1-and-tree-join-at
  (equal (<<-all-r x (tree-join-at split left right))
         (and (<<-all-r x left)
              (<<-all-r x right)))
  :enable tree-join-at)

(defrule bst-p-of-tree-join-at-when-bst-p-and-split
  (implies (and (<<-all-l left split)
                (<<-all-r split right))
           ;; This demonstrates the utility of tree-join-at. The variable split
           ;; does not appear free in the hyps.
           (equal (bstp (tree-join-at split left right))
                  (and (bstp left)
                       (bstp right))))
  :enable tree-join-at)

(defrule heap<-all-l-of-tree-join-at
  (implies (and (heap<-all-l left x)
                (heap<-all-l right x))
           (heap<-all-l (tree-join-at split left right) x))
  :enable tree-join-at)

(defrulel heapp-of-tree-join-at-when-tree-empty-p-of-left
  (implies (tree-empty-p left)
           (equal (heapp (tree-join-at split left right))
                  (heapp right)))
  :enable tree-join-at)

(defrulel heapp-of-tree-join-at-when-tree-empty-p-of-right
  (implies (tree-empty-p right)
           (equal (heapp (tree-join-at split left right))
                  (heapp left)))
  :enable tree-join-at)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: can this proof be simplified using tree-join-at?
;; - (Might need to provide fake definitions of tree-join-at that look like
;;   tree-join but include the split value (which will always be the same).)
(encapsulate ()
  (defrulel lemma0
    (implies (and (not (tree-empty-p left))
                  (not (heap< (tagged-element->elem (tree->head left))
                              (tagged-element->elem (tree->head right))))
                  (heap<-all-l (tree->left right)
                               (tagged-element->elem (tree->head right)))
                  (<<-all-l left x)
                  (<<-all-r x right)
                  (heap<-all-l (tree->right right)
                               (tagged-element->elem (tree->head right)))
                  (heap<-all-l (tree->right left)
                               (tagged-element->elem (tree->head left))))
             (heap<-all-l (tree-join (tree->right left) right)
                          (tagged-element->elem (tree->head left))))
    :enable (heap<-all-l-extra-rules
             heap<-rules)
    :disable equal-of-tree->heads-when-<<-all-l-and-<<-all-r-forward-chaining
    :use equal-of-tree->heads-when-<<-all-l-and-<<-all-r)

  (defrulel lemma1
    (implies (and (heapp (tree->left right))
                  (heap<-all-l (tree-join left (tree->left right))
                               (tagged-element->elem (tree->head right)))
                  (not (heap<-all-l (tree->left right)
                                    (tagged-element->elem (tree->head right)))))
             (not (heap<-all-l (tree->right right)
                               (tagged-element->elem (tree->head right)))))
    :enable (tree-join
             heapp-extra-rules
             heap<-all-l-extra-rules
             heap<-rules)
    :disable heap<-trichotomy
    :use ((:instance heap<-trichotomy
                     (x (tagged-element->elem (tree->head (tree->left right))))
                     (y (tagged-element->elem (tree->head left))))))

  (defrulel lemma2
    (implies (and (heap< (tagged-element->elem (tree->head left))
                         (tagged-element->elem (tree->head right)))
                  (heap<-all-l (tree->left left)
                               (tagged-element->elem (tree->head left)))
                  (heap<-all-l (tree->right left)
                               (tagged-element->elem (tree->head left)))
                  (not (heap<-all-l (tree-join left (tree->left right))
                                    (tagged-element->elem (tree->head right))))
                  (heap<-all-l (tree->left right)
                               (tagged-element->elem (tree->head right))))
             (not (heap<-all-l (tree->right right)
                               (tagged-element->elem (tree->head right)))))
    :enable heap<-all-l-weaken)

  (defrule heapp-of-tree-join
    (implies (and (<<-all-l left x)
                  (<<-all-r x right))
             (equal (heapp (tree-join left right))
                    (and (heapp left)
                         (heapp right))))
    :induct t
    :enable (tree-join
             heap<-all-l-weaken)))

(defrule heapp-of-tree-join-at
  (implies (and (<<-all-l left split)
                (<<-all-r split right))
           (equal (heapp (tree-join-at split left right))
                  (and (heapp left)
                       (heapp right))))
  :enable tree-join-at)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule bstp-of-tree-join-of-tree->left-and-tree->right-when-bstp
  (implies (and (not (tree-empty-p tree))
                (bstp tree))
           (equal (bstp (tree-join (tree->left tree) (tree->right tree)))
                  (and (bstp (tree->left tree))
                       (bstp (tree->right tree))))))

(defrule bstp-of-tree-join-at-of-tree->left-and-tree->right-when-bstp
  (implies (and (not (tree-empty-p tree))
                (bstp tree))
           (equal (bstp (tree-join-at split (tree->left tree) (tree->right tree)))
                  (and (bstp (tree->left tree))
                       (bstp (tree->right tree)))))
  :enable tree-join-at)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule heapp-of-tree-join-of-tree->left-and-tree->right-when-bstp
  (implies (and (not (tree-empty-p tree))
                (bstp tree))
           (equal (heapp (tree-join (tree->left tree) (tree->right tree)))
                  (and (heapp (tree->left tree))
                       (heapp (tree->right tree)))))
  :enable bstp)

(defrule heapp-of-tree-join-at-of-tree->left-and-tree->right-when-bstp
  (implies (and (not (tree-empty-p tree))
                (bstp tree))
           (equal (heapp (tree-join-at split (tree->left tree) (tree->right tree)))
                  (and (heapp (tree->left tree))
                       (heapp (tree->right tree)))))
  :enable tree-join-at)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule tree-all-acl2-numberp-of-tree-join
  (implies (and (tree-all-acl2-numberp left)
                (tree-all-acl2-numberp right))
           (tree-all-acl2-numberp (tree-join left right)))
  :induct (tree-join left right)
  :enable (tree-join
           tree-all-acl2-numberp))

(defrule tree-all-symbolp-of-tree-join
  (implies (and (tree-all-symbolp left)
                (tree-all-symbolp right))
           (tree-all-symbolp (tree-join left right)))
  :induct (tree-join left right)
  :enable (tree-join
           tree-all-symbolp))

(defrule tree-all-eqlablep-of-tree-join
  (implies (and (tree-all-eqlablep left)
                (tree-all-eqlablep right))
           (tree-all-eqlablep (tree-join left right)))
  :induct (tree-join left right)
  :enable (tree-join
           tree-all-eqlablep))
