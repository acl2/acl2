; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "bidi-display")
(include-book "bidi-rule")

(local (include-book "std/lists/top" :dir :system)) ; for more DEFLIST theorems

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection bidi-combining-mark-class
  :parents (bidi-rule-display)
  :short "A code point whose class is not @('L') (@('Left_To_Right'))
          is a combining mark exactly when its class is @('NSM')
          (@('Nonspacing_Mark'))."
  :long
  (xdoc::topstring
   (xdoc::p
    "Rule L3 of the Unicode Bidirectional Algorithm
     goes by the general category of a character
     (see @(tsee bidi-combining-mark-p)),
     and rule W1 by its bidirectional class
     (see @(tsee bidi-mark-code-point-p)).
     Some combining marks have the class @('L');
     apart from those, the two predicates agree.
     We prove it by checking it on every code point, for each version;
     so adding a version checks it for that version."))

  (local
   (define mark-class-ok ((cp code-point-p) (ver versionp))
     :returns (yes/no booleanp)
     (or (equal (bidi-class-kind (code-point-bidi-class cp ver))
                :left-to-right)
         (equal (bidi-combining-mark-p cp ver)
                (bidi-mark-code-point-p cp ver)))
     :hooks nil))

  (local
   (std::deflist mark-class-ok-listp (x ver)
     :guard (and (code-point-listp x)
                 (versionp ver))
     (mark-class-ok x ver)))

  (defrulel mark-class-ok-listp-of-all-code-points
    (mark-class-ok-listp (all-code-points) (version-fix ver))
    :enable (version-fix-in-terms-of-version-case
             (:e all-code-points))
    :disable mark-class-ok-listp-of-cons)

  (defrulel mark-class-ok-holds
    (mark-class-ok cp ver)
    :rule-classes nil
    :use (:instance
          mark-class-ok-when-member-equal-of-mark-class-ok-listp
          (acl2::a (code-point-fix cp))
          (x (all-code-points))
          (ver (version-fix ver)))
    :enable mark-class-ok)

  (defruled bidi-combining-mark-p-when-not-left-to-right
    (implies (not (equal (bidi-class-kind (code-point-bidi-class cp ver))
                         :left-to-right))
             (equal (bidi-combining-mark-p cp ver)
                    (bidi-mark-code-point-p cp ver)))
    :enable mark-class-ok
    :use mark-class-ok-holds))
