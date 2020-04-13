; Fixing Function for Signed Bytes
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/basic/pos-fix" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(local (include-book "arithmetic/top" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define signed-byte-fix ((bits posp) (x (signed-byte-p bits x)))
  :returns (fixed-x (signed-byte-p bits fixed-x)
                    :hyp (posp bits))
  :parents (kestrel-utilities signed-byte-p)
  :short "Fixing function for @(tsee signed-byte-p)."
  :long
  (xdoc::topstring
   (xdoc::p
    "Since the set denoted by @(tsee signed-byte-p)
     is empty for some values of @('bits')
     (namely, when @('bits') is not a positive integer),
     this fixing function cannot always return a value satisfying the predicate.
     Even though @(tsee signed-byte-p)
     does not fix its @('bits') to @(tsee posp),
     this fixing function does,
     i.e. it treats @('bits') as a positive integer.
     Thus, the set denoted by @(tsee signed-byte-p) is never empty.
     If @('x') is not in the range of @(tsee signed-byte-p),
     we return 0;
     another option is to return @(tsee loghead)
     (or its equivalent with built-in functions,
     to avoid a dependency on the IHS library).")
   (xdoc::p
    "Since @(tsee signed-byte-p) is enabled by default,
     this fixing function is also enabled by default.
     When these functions are enabled, they are meant as abbreviations,
     and theorems triggered by them may not fire during proofs."))
  (mbe :logic (b* ((bits (pos-fix bits)))
                (if (signed-byte-p bits x)
                    x
                  0))
       :exec x)
  :enabled t
  ///

  (defthm signed-byte-fix-when-signed-byte-p
    (implies (signed-byte-p (pos-fix bits) x)
             (equal (signed-byte-fix bits x)
                    x)))

  (defthm signed-byte-fix-of-pos-fix-bits
    (equal (signed-byte-fix (pos-fix bits) x)
           (signed-byte-fix bits x)))

  (defthm signed-byte-fix-of-pos-fix-bits-normalize-const
    (implies (syntaxp (and (quotep bits)
                           (not (natp (cadr bits)))))
             (equal (signed-byte-fix bits x)
                    (signed-byte-fix (pos-fix bits) x)))))
