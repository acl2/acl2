; List Utilities -- Theorems about Lengths Equal/Above Constants
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "xdoc/constructors" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "arithmetic-3/top" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection list-len-const-theorems
  :parents (list-utilities)
  :short "Some theorems about lists whose lengths are
          equal, below, or above constant values."
  :long
  (xdoc::topstring
   (xdoc::p
    "These theorems are disabled by default.
     They can be enabled to turn
     assertions about lengths and constants
     into assertions about @(tsee consp) and @(tsee cdr):
     the expansion terminates because of the @(tsee syntaxp) restriction.")
   (xdoc::p
    "The @('lt') and @('gt') rules are formulated
     on @(tsee <) (with arguments in the appropriate order),
     but they apply to assertions with @(tsee <=) and @(tsee >=)
     according to the definitions of these macros."))

  (defruled equal-len-const
    (implies (syntaxp (quotep c))
             (equal (equal (len x) c)
                    (if (natp c)
                        (if (equal c 0)
                            (not (consp x))
                          (and (consp x)
                               (equal (len (cdr x))
                                      (1- c))))
                      nil))))

  (defruled lt-len-const
    (implies (syntaxp (quotep c))
             (equal (< (len x) c)
                    (and (> (fix c) 0)
                         (or (not (consp x))
                             (< (len (cdr x))
                                (1- c)))))))

  (defruled gt-len-const
    (implies (syntaxp (quotep c))
             (equal (> (len x) c)
                    (or (< (fix c) 0)
                        (and (consp x)
                             (> (len (cdr x))
                                (1- c))))))))
