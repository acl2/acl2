; Copyright (C) 2025, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(include-book "projects/set-theory/portcullis" :dir :system)

(in-package "ZF")

(defconst *hol-symbols*
  '(include-book
    open-theory close-theory
    defhol hpp hap* type-match hol-typep typ hol-type-lookup hp-type hp-value
; From *hol-arities* in terms.lisp:
    equal hp-comma hp-none hp-some hp-nil
    hp-cons hp+ hp* hp-implies hp-and hp-or
    hp= hp< hp-not hp-forall hp-exists hp-true hp-false
; From hol-termp-rec:
    hp-num hp-bool
; Constants in terms:
    *hp-0* *hp-1*
; From ../utilities/alist-subsetp.lisp:
    alist-subsetp
; Other basic ACL2 symbols etc.:
    defthm defthmd defconst defgoal set-enforce-redundancy
    implies not and or
    force type in-theory enable disable e/d
    let let* mv-let
; Others from hol.lisp:
    hp-cons hp-list-p hp-nil-p hp-cons-p hp-list-car hp-list-cdr
    hp-comma hp-comma-p hp-hash-car hp-hash-cdr
; But we deliberately avoid importing t and nil, so that they can be used as
; variable names.
    ))

(defpkg "HOL"
  *hol-symbols*)
