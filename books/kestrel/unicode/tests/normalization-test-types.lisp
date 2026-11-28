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

(local (in-theory (enable nfix natp min)))

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
;
; The file of one version of Unicode differs little from the file of the
; version before it.  The data book of the earliest version has all the
; lines.  The data book of a later version writes each part as a list of
; edits, which this book also defines, applied to the lines of the same
; part of the version before it.

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum normalization-test-edit
  :short "Fixtype of the edits of a list of lines of the normalization
          conformance test."
  :long
  (xdoc::topstring
   (xdoc::p
    "A list of edits says how to make one list of lines from another;
     see @(tsee normalization-test-apply-edits).
     An edit of the kind @(':keep') keeps the next @('count') lines,
     one of the kind @(':drop') leaves the next @('count') lines out,
     and one of the kind @(':add') puts in the lines that it has."))
  (:keep ((count nat)))
  (:drop ((count nat)))
  (:add ((lines normalization-test-line-list)))
  :pred normalization-test-edit-p)

;;;;;;;;;;;;;;;;;;;;

(fty::deflist normalization-test-edit-list
  :short "Fixtype of lists of edits of a list of lines of the normalization
          conformance test."
  :elt-type normalization-test-edit
  :true-listp t
  :elementp-of-nil nil
  :pred normalization-test-edit-listp)

;;;;;;;;;;;;;;;;;;;;

(define normalization-test-apply-edits
  ((edits normalization-test-edit-listp)
   (lines normalization-test-line-listp))
  :returns (new-lines normalization-test-line-listp)
  :short "Apply a list of edits to a list of lines of the normalization
          conformance test."
  :long
  (xdoc::topstring
   (xdoc::p
    "The edits are applied in order, from the start of the list of lines.
     An edit that keeps or drops @('count') lines keeps or drops as many
     lines as are left, if fewer than @('count') are left.
     The lines that are left after the last edit are kept.")
   (xdoc::p
    "The data book of the normalization conformance test of a version of
     Unicode that is not the earliest one applies this function to the
     lines of each part of the version before it."))
  (b* ((lines (normalization-test-line-list-fix lines))
       ((when (endp edits)) lines)
       (edit (car edits)))
    (normalization-test-edit-case
     edit
     :keep (b* ((count (min edit.count (len lines))))
             (append (take count lines)
                     (normalization-test-apply-edits (cdr edits)
                                                     (nthcdr count lines))))
     :drop (normalization-test-apply-edits (cdr edits)
                                           (nthcdr edit.count lines))
     :add (append edit.lines
                  (normalization-test-apply-edits (cdr edits) lines)))))

;;;;;;;;;;;;;;;;;;;;

; Examples of the three kinds of edits,
; on lines whose five columns are the same code point.

(local
 (defconst *example-lines*
   (list (normalization-test-line '(1) '(1) '(1) '(1) '(1))
         (normalization-test-line '(2) '(2) '(2) '(2) '(2))
         (normalization-test-line '(3) '(3) '(3) '(3) '(3))
         (normalization-test-line '(4) '(4) '(4) '(4) '(4))
         (normalization-test-line '(5) '(5) '(5) '(5) '(5)))))

(local
 (defconst *example-line*
   (normalization-test-line '(9) '(9) '(9) '(9) '(9))))

; One line is kept, two are dropped, one is added;
; the two lines after the last edit are kept.

(local
 (assert-event
  (equal (normalization-test-apply-edits
          (list (normalization-test-edit-keep 1)
                (normalization-test-edit-drop 2)
                (normalization-test-edit-add (list *example-line*)))
          *example-lines*)
         (list (nth 0 *example-lines*)
               *example-line*
               (nth 3 *example-lines*)
               (nth 4 *example-lines*)))))

; Without edits, all the lines are kept.

(local
 (assert-event
  (equal (normalization-test-apply-edits nil *example-lines*)
         *example-lines*)))

; An edit that keeps or drops more lines than are left
; keeps or drops the lines that are left.

(local
 (assert-event
  (equal (normalization-test-apply-edits
          (list (normalization-test-edit-keep 7)
                (normalization-test-edit-add (list *example-line*)))
          *example-lines*)
         (append *example-lines* (list *example-line*)))))

(local
 (assert-event
  (equal (normalization-test-apply-edits
          (list (normalization-test-edit-keep 4)
                (normalization-test-edit-drop 7))
          *example-lines*)
         (take 4 *example-lines*))))
