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

(include-book "hash")
(include-book "total-order")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (disable <<-rules)))

(std::make-define-config
  :no-function t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bst< (x y)
  (declare (xargs :type-prescription (booleanp (bst< x y))))
  :parents (binary-tree)
  :short "The total order used by @(tsee bst-p)."
  :long
  (xdoc::topstring
   (xdoc::p
     "This is just a wrapper around @(tsee <<). It is provided so that we may
      easily switch the total order to experiment with performance."))
  (<< x y)
  :inline t)

(defruled bst<-irreflexive
  (not (bst< x x))
  :enable (bst<
           <<-rules))

(defruled bst<-asymmetric
  (implies (bst< y x)
           (not (bst< x y)))
  :enable (bst<
           <<-rules))

(defruled bst<-transitive
  (implies (and (bst< x y)
                (bst< y z))
           (bst< x z))
  :enable (bst<
           <<-rules))

(defruled bst<-trichotomy
  (implies (and (not (bst< y x))
                (not (equal x y)))
           (bst< x y))
  :enable (bst<
           <<-rules))

;;;;;;;;;;;;;;;;;;;;

(defthy bst<-rules
  '(bst<-irreflexive
    bst<-asymmetric
    bst<-transitive
    bst<-trichotomy))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bst<-with-hashes (x y hash-x hash-y)
  (declare (xargs :type-prescription
                  (booleanp (bst<-with-hashes x y hash-x hash-y)))
           (ignore hash-x hash-y))
  :parents (bst<)
  :short "Variant of @(tsee bst<) which may use pre-computed hashes."
  :long
  (xdoc::topstring
   (xdoc::p
     "This is currently a dummy function warpping @(tsee bst<). It is provided
      in case we wish to change the order to make use of hash values, as @(tsee
      heap<) currently does."))
  (bst< x y)
  :enabled t
  :inline t)
