; Lists of known-boolean-returning functions
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

;; See known-booleans.lisp for a more flexible mechanism.

;todo: reduce deps
(include-book "known-booleans")
(include-book "kestrel/utilities/quote" :dir :system)

 ;since the functions are mentioned below (todo: make sure all functions mentioned below are included):
(include-book "kestrel/bv/bvlt" :dir :system)
(include-book "kestrel/bv/sbvlt" :dir :system)
(include-book "kestrel/typed-lists-light/items-have-len" :dir :system)
(include-book "kestrel/bv-lists/all-all-unsigned-byte-p" :dir :system)
(include-book "kestrel/bv-lists/all-unsigned-byte-p" :dir :system)
(include-book "kestrel/typed-lists-light/all-true-listp" :dir :system)
(include-book "kestrel/bv/unsigned-byte-p-forced" :dir :system)
(include-book "kestrel/booleans/booland" :dir :system)
(include-book "kestrel/booleans/boolor" :dir :system)
(include-book "kestrel/booleans/boolxor" :dir :system)
(include-book "kestrel/booleans/boolif" :dir :system)
(include-book "kestrel/booleans/bool-fix" :dir :system)
(include-book "kestrel/lists-light/memberp-def" :dir :system)
(include-book "std/lists/list-defuns" :dir :system) ;for prefixp
(include-book "std/osets/top" :dir :system) ;for set::in

;fixme add more
;fixme add theorems to justify these?
;I believe soundness depends on all of these actually being predicates (but maybe transition to using the known-booleans machinery for anything that depends on soundness):
;fixme keep in sync with booleanp-runes?
;when we use this, we could check for the booleanp-of-XXX theorem being present.  or check the type rule for XXX?
(defconst *known-predicates-except-not-basic*
  '(memberp
    unsigned-byte-p natp integerp rationalp acl2-numberp consp booleanp
    true-listp ;new
    iff        ;newer
    equal
    <
    bvlt sbvlt bvle sbvle
    unsigned-byte-p-forced
    booland boolor boolxor
    all-unsigned-byte-p items-have-len all-true-listp all-all-unsigned-byte-p
    prefixp         ;new
    bool-fix$inline ;new
    boolif          ;new
    set::in ; maybe drop?
    ))

(defconst *known-predicates-basic* (cons 'not *known-predicates-except-not-basic*))
