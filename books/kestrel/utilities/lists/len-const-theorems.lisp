; List Utilities -- Theorems about Lengths Equal/Above Constants
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "xdoc/constructors" :dir :system)
(include-book "std/util/defrule" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection list-len-const-theorems
  :parents (list-utilities)
  :short "Some theorems about lists whose lengths are
          (i) equal, (ii) equal or above, or (iii) above constant values."
  :long
  (xdoc::topstring-p
   "These theorems are disabled by default.
    They can be enabled to turn
    assertions about lengths and constants
    into assertions about @(tsee consp) and @(tsee cdr):
    the expansion terminates because of the @(tsee syntaxp) restriction.")

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

  (defruled gteq-len-const
    (implies (syntaxp (quotep c))
             (equal (>= (len x) c)
                    (or (<= (fix c) 0)
                        (and (consp x)
                             (>= (len (cdr x))
                                 (1- c)))))))

  (defruled gt-len-const
    (implies (syntaxp (quotep c))
             (equal (> (len x) c)
                    (or (< (fix c) 0)
                        (and (consp x)
                             (> (len (cdr x))
                                (1- c))))))
    :use lemma
    :prep-lemmas
    ((defruled lemma
       (implies (and (consp x)
                     (or (< (fix c) 0)
                         (> (len (cdr x))
                            (1- c))))
                (> (len x) c))))))
