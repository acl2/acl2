; Fixing Function for Unsigned Bytes
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "centaur/fty/top" :dir :system)
(include-book "xdoc/constructors" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "arithmetic/top" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define unsigned-byte-fix ((bits natp) (x (unsigned-byte-p bits x)))
  :returns (fixed-x (unsigned-byte-p bits fixed-x)
                    :hyp (natp bits))
  :parents (kestrel-utilities unsigned-byte-p)
  :short "Fixing function for @(tsee unsigned-byte-p)."
  :long
  (xdoc::topstring
   (xdoc::p
    "Since the set denoted by @(tsee unsigned-byte-p)
     is empty for some values of @('bits')
     (namely, when @('bits') is not a natural number),
     this fixing function cannot always return a value satisfying the predicate.
     Even though @(tsee unsigned-byte-p)
     does not fix its @('bits') to @(tsee natp),
     this fixing function does,
     i.e. it treats @('bits') as a natural number.
     Thus, the set denoted by @(tsee unsigned-byte-p) is never empty.
     If @('x') is not in the range of @(tsee unsigned-byte-p),
     we return 0;
     another option is to return @(tsee loghead)
     (or its equivalent with built-in functions,
     to avoid a dependency on the IHS library).")
   (xdoc::p
    "Since @(tsee unsigned-byte-p) is enabled by default,
     this fixing function is also enabled by default.
     When these functions are enabled, they are meant as abbreviations,
     and theorems triggered by them may not fire during proofs."))
  (mbe :logic (b* ((bits (nfix bits)))
                (if (unsigned-byte-p bits x)
                    x
                  0))
       :exec x)
  :enabled t
  :hooks (:fix)
  ///

  (defrule unsigned-byte-fix-when-unsigned-byte-p
    (implies (unsigned-byte-p (nfix bits) x)
             (equal (unsigned-byte-fix bits x)
                    x))))
