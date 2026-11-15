; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "../code-points")

(local (include-book "std/lists/top" :dir :system)) ; for more DEFLIST theorems

(acl2::controlled-configuration)

(local (in-theory (enable nfix natp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This book defines the fixtypes of the contents of the normalization
; conformance test of the Unicode Character Database, NormalizationTest.txt.
; The test data, in the books ../data/v<version>/normalization-test, are
; values of these types.  The book normalization-test in this directory
; defines how the test is run.
;
; The file consists of parts, numbered from 0.  Each part consists of lines.
; Each line has five columns, each of which is a sequence of code points:
; a source sequence, and its NFC, NFD, NFKC and NFKD forms.
; The conformance statement in the file calls them c1, c2, c3, c4 and c5.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod normalization-test-line
  :short "Fixtype of the lines of the normalization conformance test."
  ((source code-point-list)
   (nfc code-point-list)
   (nfd code-point-list)
   (nfkc code-point-list)
   (nfkd code-point-list))
  :pred normalization-test-line-p)

;;;;;;;;;;;;;;;;;;;;

(fty::deflist normalization-test-line-list
  :short "Fixtype of lists of lines of the normalization conformance test."
  :elt-type normalization-test-line
  :true-listp t
  :elementp-of-nil nil
  :pred normalization-test-line-listp)

;;;;;;;;;;;;;;;;;;;;

(fty::defprod normalization-test-part
  :short "Fixtype of the parts of the normalization conformance test."
  ((number nat)
   (lines normalization-test-line-list))
  :pred normalization-test-part-p)

;;;;;;;;;;;;;;;;;;;;

(fty::deflist normalization-test-part-list
  :short "Fixtype of lists of parts of the normalization conformance test."
  :elt-type normalization-test-part
  :true-listp t
  :elementp-of-nil nil
  :pred normalization-test-part-listp)
