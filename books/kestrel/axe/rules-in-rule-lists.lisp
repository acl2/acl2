; Rules mentioned in rule-lists.lisp
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book is intended to bring in all the rules that are in rule-lists.lisp.
;; See also rules-in-rule-lists-jvm.lisp.

(include-book "kestrel/arithmetic-light/mod2" :dir :system)
(include-book "basic-rules")
(include-book "boolean-rules-axe")
(include-book "bv-rules")
(include-book "bv-rules-axe") ;bring in theorems like LEFTROTATE32-OF-BVCHOP-5
(include-book "bv-list-rules-axe")
(include-book "kestrel/bv-lists/bv-arrays" :dir :system)
(include-book "kestrel/arithmetic-light/less-than" :dir :system) ;for not-<-same
(include-book "kestrel/arithmetic-light/minus" :dir :system)
(include-book "kestrel/arithmetic-light/plus" :dir :system)
(include-book "kestrel/arithmetic-light/ceiling" :dir :system)
(include-book "kestrel/bv/arith" :dir :system) ;for <-of-sums-cancel (todo: reduce)
(include-book "kestrel/bv/adder" :dir :system) ;for BVPLUS-BECOMES-RIPPLE-CARRY-ADDER, used in bit blasting in the phased rules
(include-book "bv-array-rules-axe")
;(include-book "rules1" :dir :system) ;included by bv-array-rules-axe
(include-book "axe-rules-mixed") ;reduce? since some rules in this file are now in the basic jvm rule set? for NOT-EQUAL-MAX-INT-WHEN-<=, etc.
(include-book "kestrel/bv/sbvdivdown-rules" :dir :system)
(include-book "kestrel/bv/sbvdiv-rules" :dir :system)
(include-book "kestrel/bv/bvif2" :dir :system)
(include-book "kestrel/lists-light/update-nth" :dir :system)
(include-book "kestrel/lists-light/nth" :dir :system)
(include-book "kestrel/lists-light/true-list-fix" :dir :system)
(include-book "kestrel/lists-light/firstn" :dir :system)
(include-book "kestrel/lists-light/cdr" :dir :system) ;for cdr-iff?
(include-book "kestrel/lists-light/nthcdr" :dir :system)
(include-book "kestrel/lists-light/len" :dir :system)
(include-book "kestrel/lists-light/take" :dir :system)
(include-book "kestrel/lists-light/firstn" :dir :system)
(include-book "kestrel/lists-light/append" :dir :system)
(include-book "kestrel/lists-light/cons" :dir :system)
(include-book "kestrel/lists-light/rules" :dir :system) ; for CONS-EQUAL-REWRITE-CONSTANT-VERSION
(include-book "kestrel/arithmetic-light/less-than" :dir :system)
(include-book "kestrel/lists-light/union-equal" :dir :system)  ;for UNION-EQUAL-OF-NIL-ARG1
;(include-book "kestrel/alists-light/assoc-equal" :dir :system) ;only needed by axe prover?
(include-book "kestrel/alists-light/strip-cdrs" :dir :system)
(include-book "kestrel/bv-lists/bv-array-conversions" :dir :system)  ;drop?  ;for LIST-TO-BV-ARRAY
(include-book "kestrel/bv/rightrotate32" :dir :system)
(include-book "list-rules-axe")
(include-book "packbv-axe")
(include-book "kestrel/lists-light/finalcdr" :dir :system)
(include-book "rule-lists")
(include-book "kestrel/utilities/mv-nth" :dir :system)
(include-book "kestrel/utilities/ensure-rules-known" :dir :system)

;;todo: add more like this:
(ensure-rules-known (lookup-rules))
(ensure-rules-known (booleanp-bv-rules))
(ensure-rules-known (booleanp-rules))
(ensure-rules-known (boolean-rules))
(ensure-rules-known (mv-nth-rules))
(ensure-rules-known (base-rules))
(ensure-rules-known (type-rules))
(ensure-rules-known (safe-trim-rules))
(ensure-rules-known (core-rules-bv))
(ensure-rules-known (update-nth2-rules))
(ensure-rules-known (list-rules))
(ensure-rules-known (list-rules-etc))
(ensure-rules-known (jvm-rules-list))
;(ensure-rules-known (jvm-rules-alist)) ; todo?
(ensure-rules-known (core-rules-non-bv))
(ensure-rules-known (bvif-rules))
(ensure-rules-known (unsigned-byte-p-rules))
(ensure-rules-known (unsigned-byte-p-forced-rules))
(ensure-rules-known (bvchop-list-rules))
(ensure-rules-known (logext-rules))
(ensure-rules-known (bv-array-rules))
;(ensure-rules-known (miter-rules)) ;todo:  equal-of-nil-and-group
