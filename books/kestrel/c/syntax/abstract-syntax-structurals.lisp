; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "abstract-syntax-trees")

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ abstract-syntax-structurals
  :parents (abstract-syntax)
  :short "Structural operations on ASTs."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are operations that depend only on the structure of the ASTs,
     and could be even automatically generated
     from the fixtype definitions themselves,
     in the future."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stringlit-list->prefix?-list ((strlits stringlit-listp))
  :returns (prefixes eprefix-option-listp)
  :short "Lift @(tsee stringlit->prefix?) to lists."
  (cond ((endp strlits) nil)
        (t (cons (stringlit->prefix? (car strlits))
                 (stringlit-list->prefix?-list (cdr strlits))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection trans-item-declon-list ((x ext-declon-listp))
  :returns (items trans-item-listp)
  :short "Lift @(tsee trans-item-declon) to lists."
  (trans-item-declon x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection trans-item-include-list ((x header-name-listp))
  :returns (item trans-item-listp)
  :short "Lift @(tsee trans-item-include) to lists."
  (trans-item-include x))
