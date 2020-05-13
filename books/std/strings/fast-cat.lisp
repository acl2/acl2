; ACL2 String Library
; Copyright (C) 2009-2013 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "STR")
(include-book "printtree")
(include-book "tools/include-raw" :dir :system)
; (depends-on "fast-cat-raw.lsp")

; NOTE: This book used to include several heavyweight books, including
; std/string/defs (which depends on std/strings/top).  This was because we
; needed to ensure that every book containing a definition of any of the
; functions redefined here is included before this book, due to the
; restrictions on redundancy of functions with raw Lisp code.

; Usually, this only means that the book introducing the raw Lisp definition
; should include the book introducing the logic definition.  However, because
; of the particular structure of the std/strings library, these functions had
; several definitions in different books.  For example, definitions of
; fast-string-append occurred in cat-base.lisp, defs-program.lisp, and
; defs.lisp.  Even though these were all generated from the same definition
; (from cat-base.lisp), they were technically independent events which needed
; to be redundant in order to include more than one of those books
; simultaneously.  They would be redundant, except that this book introduced a
; raw Lisp definition of fast-string-append.  So if we didn't include defs and
; defs-program in this book, then including this book followed by defs or
; defs-program would fail with a bad redundancy check.

; To avoid this, we ensure that the functions whose raw Lisp definitions are
; given in this book are only defined in one place apiece.
; For FAST-STRING-APPEND,
;     FAST-STRING-APPEND-LST,
; and RCHARS-TO-STRING,
;     the definition is in cat-base.lisp,
; for PRINTTREE->STR1,
;     the definition is in printtree.lisp.

; Since the program, logic, and guard verified definitinos are all in one
; place, this means that defs-program must actually include their logic
; definitions via these books.  We think this is harmless since the
; dependencies of both books together cost about 4 seconds to certify.  If it
; were necessary, however, we could separate the program mode definition,
; verify-termination, and verify-guards events.

; In CCL, the performance of str::cat is boosted by a factor of 6.6-9.5x by
; including this file, according to the stupid benchmarks at the end of this
; file.
;
; Perhaps Gary will write a compiler-macro to speed up concatenate in CCL, at
; which point this file will no longer be needed.
;
; I haven't tested performance in other Lisps.  If misc/fast-coerce is any
; indication, it may be that some other Lisps will also benefit.

(defttag fast-cat)
(acl2::include-raw "fast-cat-raw.lsp")


#|

(include-book
 "fast-cat" :ttags :all)

:q

(ccl::egc nil)

; STR::CAT is about 9.5x faster for this test:

(progn
  (ccl::gc)
  ;; 1.413 seconds, 1.12 GB allocated
  (time (loop for i fixnum from 1 to 10000000
              do
              (str::cat "sillyNameOneMightSee" "[33]"))))

(progn
  (ccl::gc)
  ;; 13.375 seconds, 1.12 GB allocated
  (time (loop for i fixnum from 1 to 10000000
              do
              (concatenate 'string "sillyNameOneMightSee" "[33]"))))


; STR::CAT is about 6.6x faster in this loop.

; BOZO weird -- why does CCL's concatenate function take so much less memory
; than ours?

(progn
  (ccl::gc)
  ;; 2.112 seconds, 1.760 gb
  (time (loop for i fixnum from 1 to 10000000
              do
              (str::cat "sillyNameOneMightSee" "[33]" "more"))))

(progn
  (ccl::gc)
  ;; 14.101 seconds, 1.28 gb
  (time (loop for i fixnum from 1 to 10000000
              do
              (concatenate 'string "sillyNameOneMightSee" "[33]" "more"))))


; Hrmn, this takes 480 MB:

(defun f (x) (list x x x))

(time
 (loop for i fixnum from 1 to 10000000
       do
       (f i)))

; And indeed (- 1760 1280) is 480.  So it looks like CCL's concatenate is
; somehow able to avoid consing its arguments into a list like our
; fast-concatenate macro is doing.

; Well, go figure.  I'm not sure how to avoid this.


(defparameter *test* (coerce "blah blah blah this is some text" 'list))

(progn
  (ccl::gc)
  ;; 6.782 seconds, 1.6 GB allocated
  (let ((test *test*))
    (time (loop for i fixnum from 1 to 10000000
                collect
                (str::rchars-to-string test))))
  nil)

(progn
  (ccl::gc)
  ;; 11.629 seconds, 3.04 GB allocated
  (let ((test *test*))
    (time (loop for i fixnum from 1 to 10000000
                collect
                (reverse (coerce test 'string)))))
  nil)

(progn
  (ccl::gc)
  ;; 10.314 seconds, 6.72 GB allocated
  (let ((test *test*))
    (time (loop for i fixnum from 1 to 10000000
                collect
                (coerce (reverse test) 'string))))
  nil)


|#
