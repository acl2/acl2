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
(include-book "cat")
(include-book "tools/include-raw" :dir :system)
; (depends-on "fast-cat-raw.lsp")

; Matt K. mod: Include the following three books, which define
; STR::FAST-STRING-APPEND, STR::FAST-STRING-APPEND-LST, and
; STR::RCHARS-TO-STRING, before we smash their definitions.  Otherwise, we can
; get an error when including fast-cat first and then including any of these
; books (e.g., when including centaur/gl/bfr-satlink, which includes all three
; of these books).  That's because the three function symbols above all belong
; to the list (@ logic-fns-with-raw-code).  See :DOC redundant-events,
; specifically, the paragraph starting with: "Redundancy is restricted for
; built-in macros and functions that have special raw Lisp code.".  I measured
; the time using LispWorks for including the original and modified versions of
; this book, and the increase -- from 0.8 to 1.0 seconds -- seems tolerable.
(include-book "xdoc/str" :dir :system)
(include-book "std/strings/defs" :dir :system)
(include-book "std/strings/defs-program" :dir :system)

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
