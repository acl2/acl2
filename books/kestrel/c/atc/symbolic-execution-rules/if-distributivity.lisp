; C Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2022 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "../../language/computation-states")
(include-book "../integers")

(local (xdoc::set-default-parents atc-symbolic-execution-rules))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-distributivity-over-if-rewrite-rules
  :short "Rewrite rules about certain functions distributing over @(tsee if)."
  :long
  (xdoc::topstring
   (xdoc::p
    "We found it necessary to include rules
     to distribute certain functions over @(tsee if)s.
     It seems that, in the course of these symbolic execution proofs,
     we will always want to distribute functions over @(tsee if)s.
     This distribution happens at the goal level,
     but not in the rewriter by default."))

  (defruled car-of-if
    (equal (car (if a b c))
           (if a (car b) (car c))))

  (defruled mv-nth-of-if
    (equal (mv-nth n (if a b c))
           (if a (mv-nth n b) (mv-nth n c))))

  (defruled len-of-if
    (equal (len (if a b c))
           (if a (len b) (len c))))

  (defruled errorp-of-if
    (equal (errorp (if a b c))
           (if a (errorp b) (errorp c))))

  (defruled valuep-of-if
    (equal (valuep (if a b c))
           (if a (valuep b) (valuep c))))

  (defruled scharp-of-if
    (equal (scharp (if a b c))
           (if a (scharp b) (scharp c))))

  (defruled ucharp-of-if
    (equal (ucharp (if a b c))
           (if a (ucharp b) (ucharp c))))

  (defruled sshortp-of-if
    (equal (sshortp (if a b c))
           (if a (sshortp b) (sshortp c))))

  (defruled ushortp-of-if
    (equal (ushortp (if a b c))
           (if a (ushortp b) (ushortp c))))

  (defruled sintp-of-if
    (equal (sintp (if a b c))
           (if a (sintp b) (sintp c))))

  (defruled uintp-of-if
    (equal (uintp (if a b c))
           (if a (uintp b) (uintp c))))

  (defruled slongp-of-if
    (equal (slongp (if a b c))
           (if a (slongp b) (slongp c))))

  (defruled ulongp-of-if
    (equal (ulongp (if a b c))
           (if a (ulongp b) (ulongp c))))

  (defruled sllongp-of-if
    (equal (sllongp (if a b c))
           (if a (sllongp b) (sllongp c))))

  (defruled ullongp-of-if
    (equal (ullongp (if a b c))
           (if a (ullongp b) (ullongp c))))

  (defruled booleanp-of-if
    (equal (booleanp (if a b c))
           (if a (booleanp b) (booleanp c))))

  (defruled compustate->frames-of-if
    (equal (compustate->frames (if a b c))
           (if a (compustate->frames b) (compustate->frames c))))

  (defruled scope-fix-of-if
    (equal (scope-fix (if a b c))
           (if a (scope-fix b) (scope-fix c))))

  (defruled value-result-fix-of-if
    (equal (value-result-fix (if a b c))
           (if a (value-result-fix b) (value-result-fix c)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atc-distributivity-over-if-rewrite-rules*
  :short "List of rewrite rules about
          certain functions distributing over @(tsee if)."
  '(car-of-if
    mv-nth-of-if
    len-of-if
    errorp-of-if
    valuep-of-if
    scharp-of-if
    ucharp-of-if
    sshortp-of-if
    ushortp-of-if
    sintp-of-if
    uintp-of-if
    slongp-of-if
    ulongp-of-if
    sllongp-of-if
    ullongp-of-if
    booleanp-of-if
    compustate->frames-of-if
    scope-fix-of-if
    value-result-fix-of-if))
