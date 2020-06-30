; Lispfloat - Interface to the Common Lisp Floating Point Operations
; Copyright (C) 2016 Centaur Technology
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

(in-package "LISPFLOAT")
(include-book "ops-logic")
(include-book "tools/include-raw" :dir :system)
(local (include-book "std/testing/assert-bang" :dir :system))
; (depends-on "ops-exec-raw.lsp")


; [Jared] marking this book as non-GCL because, at least on my copy of
; GCL 2.6.12 ANSI, I find that:
;
;    (type-of 1.0f+0) == LONG-FLOAT
;
; instead of a SHORT-FLOAT, which causes assertion failures, and I just don't
; want to spend the time to think about whether this is OK or not.
;
; cert_param: (non-gcl)

(define real-er-float+ ((a rationalp) (b rationalp))
  :mode :program
  (mv (raise "Under the hood definition not installed?" a b) 0))

(define real-er-float- ((a rationalp) (b rationalp))
  :mode :program
  (mv (raise "Under the hood definition not installed?" a b) 0))

(define real-er-float* ((a rationalp) (b rationalp))
  :mode :program
  (mv (raise "Under the hood definition not installed?" a b) 0))

(define real-er-float/ ((a rationalp) (b rationalp))
  :mode :program
  (mv (raise "Under the hood definition not installed?" a b) 0))

(define real-er-float-expt ((a rationalp) (b rationalp))
  :mode :program
  (mv (raise "Under the hood definition not installed?" a b) 0))



(define real-er-float-sqrt ((a rationalp))
  :mode :program
  (mv (raise "Under the hood definition not installed?" a) 0))

(define real-er-float-e^x ((a rationalp))
  :mode :program
  (mv (raise "Under the hood definition not installed?" a) 0))



(define real-er-float-sin ((a rationalp))
  :mode :program
  (mv (raise "Under the hood definition not installed?" a) 0))

(define real-er-float-cos ((a rationalp))
  :mode :program
  (mv (raise "Under the hood definition not installed?" a) 0))

(define real-er-float-tan ((a rationalp))
  :mode :program
  (mv (raise "Under the hood definition not installed?" a) 0))



(define real-er-double+ ((a rationalp) (b rationalp))
  :mode :program
  (mv (raise "Under the hood definition not installed?" a b) 0))

(define real-er-double- ((a rationalp) (b rationalp))
  :mode :program
  (mv (raise "Under the hood definition not installed?" a b) 0))

(define real-er-double* ((a rationalp) (b rationalp))
  :mode :program
  (mv (raise "Under the hood definition not installed?" a b) 0))

(define real-er-double/ ((a rationalp) (b rationalp))
  :mode :program
  (mv (raise "Under the hood definition not installed?" a b) 0))

(define real-er-double-expt ((a rationalp) (b rationalp))
  :mode :program
  (mv (raise "Under the hood definition not installed?" a b) 0))



(define real-er-double-sqrt ((a rationalp))
  :mode :program
  (mv (raise "Under the hood definition not installed?" a) 0))

(define real-er-double-e^x ((a rationalp))
  :mode :program
  (mv (raise "Under the hood definition not installed?" a) 0))



(define real-er-double-sin ((a rationalp))
  :mode :program
  (mv (raise "Under the hood definition not installed?" a) 0))

(define real-er-double-cos ((a rationalp))
  :mode :program
  (mv (raise "Under the hood definition not installed?" a) 0))

(define real-er-double-tan ((a rationalp))
  :mode :program
  (mv (raise "Under the hood definition not installed?" a) 0))




(defttag :lispfloat)
(include-raw "ops-exec-raw.lsp" :host-readtable t)


(defattach
  (er-float+ real-er-float+)
  (er-float- real-er-float-)
  (er-float* real-er-float*)
  (er-float/ real-er-float/)
  (er-float-expt real-er-float-expt)

  (er-float-sqrt real-er-float-sqrt)
  (er-float-e^x real-er-float-e^x)

  (er-float-sin real-er-float-sin)
  (er-float-cos real-er-float-cos)
  (er-float-tan real-er-float-tan)

  :skip-checks t)

(defattach
  (er-double+ real-er-double+)
  (er-double- real-er-double-)
  (er-double* real-er-double*)
  (er-double/ real-er-double/)
  (er-double-expt real-er-double-expt)

  (er-double-sqrt real-er-double-sqrt)
  (er-double-e^x real-er-double-e^x)

  (er-double-sin real-er-double-sin)
  (er-double-cos real-er-double-cos)
  (er-double-tan real-er-double-tan)

  :skip-checks t)


(defttag nil)

(push-untouchable real-er-float+ t)
(push-untouchable real-er-float- t)
(push-untouchable real-er-float* t)
(push-untouchable real-er-float/ t)
(push-untouchable real-er-float-expt t)

(push-untouchable real-er-float-sqrt t)
(push-untouchable real-er-float-e^x t)

(push-untouchable real-er-float-sin t)
(push-untouchable real-er-float-cos t)
(push-untouchable real-er-float-tan t)

(push-untouchable real-er-double+ t)
(push-untouchable real-er-double- t)
(push-untouchable real-er-double* t)
(push-untouchable real-er-double/ t)
(push-untouchable real-er-double-expt t)

(push-untouchable real-er-double-sqrt t)
(push-untouchable real-er-double-e^x t)

(push-untouchable real-er-double-sin t)
(push-untouchable real-er-double-cos t)
(push-untouchable real-er-double-tan t)


;; Rudimentary tests to see if it's working at all.

(local (progn

(defconst *pi* 13176795/4194304)
(defconst *pi/2* (/ *pi* 2))
(defconst *pi/4* (/ *pi* 4))

(defun close-to (x y)

; Originally this definition used 1/10000000 (i.e., 1.0E-7) rather
; than 2/10000000 as the tolerance.  However, for ACL2 built on 32-bit
; CCL, the test (test-close (er-float-tan *pi/4*) 1) has failed,
; because the value of (er-float-tan *pi/4*) was computed as
; 8388609/8388608, which differs from 1 by a bit more than 1.0E-7,
; namely, by 1.1920929E-7.  This might or might not be a 32-bit CCL
; bug, but other Lisps may someday similarly balk at the stricter
; bound, so we increase it here.

  (and (< (- y 2/10000000) x)
       (< x (+ y 2/10000000))))

(defmacro test-exact (body expect)
  `(assert! (b* (((mv err ans) ,body))
              (and (not err)
                   (equal ans ,expect)))))

(defmacro test-close (body expect)
  `(assert! (b* (((mv err ans) ,body))
              (and (not err)
                   (close-to ans ,expect)))))

(test-exact (er-float+ 1/2 1/2) 1)
(test-exact (er-float- 1 1/2) 1/2)
(test-exact (er-float* 3 1/2) 3/2)
(test-exact (er-float/ 5 2) 5/2)
(test-exact (er-float-expt 3 3) 27)

(test-exact (er-float-sqrt 4) 2)

(test-exact (er-float-e^x 0) 1)
(test-close (er-float-e^x 1) 271828182/100000000)

(test-exact (er-float-sin 0) 0)
(test-close (er-float-sin *pi*) 0)

(test-exact (er-float-cos 0) 1)
(test-close (er-float-cos *pi*) -1)

(test-exact (er-float-tan 0) 0)
(test-close (er-float-tan *pi/4*) 1)


(test-exact (er-double+ 1/2 1/2) 1)
(test-exact (er-double- 1 1/2) 1/2)
(test-exact (er-double* 3 1/2) 3/2)
(test-exact (er-double/ 5 2) 5/2)
(test-exact (er-double-expt 3 3) 27)

(test-exact (er-double-sqrt 4) 2)

(test-exact (er-double-e^x 0) 1)
(test-close (er-double-e^x 1) 271828182/100000000)

(test-exact (er-double-sin 0) 0)
(test-close (er-double-sin *pi*) 0)

(test-exact (er-double-cos 0) 1)
(test-close (er-double-cos *pi*) -1)

(test-exact (er-double-tan 0) 0)
(test-close (er-double-tan *pi/4*) 1)

))
