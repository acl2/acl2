; Standard Utilities Library
; Copyright (C) 2008-2014 Centaur Technology
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

(in-package "STD")
(include-book "../defmapappend")
(include-book "../deflist")
(include-book "../defprojection")
(include-book "std/testing/assert" :dir :system)

(deflist my-nat-listp (x)
  (natp x)
  :elementp-of-nil nil)

(defund nats (n)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      nil
    (cons n (nats (- n 1)))))

(defthm my-nat-listp-of-nats
  (my-nat-listp (nats n))
  :hints(("Goal" :in-theory (enable nats))))

(defprojection map-nats (x)
  (nats x)
  :guard (my-nat-listp x)
  :optimize nil)

(defmapappend append-nats (x)
  (nats x)
  :guard (my-nat-listp x))

(value-triple (map-nats (nats 5)))
(value-triple (append-nats (nats 5)))



(defmapappend m0 (x)
  (nats x)
  :guard (my-nat-listp x))

(assert! (let ((topic (xdoc::find-topic 'm0 (xdoc::get-xdoc-table (w state)))))
           (not topic)))

(xdoc::set-default-parents foo bar)

(defmapappend m1 (x)
  (nats x)
  :guard (my-nat-listp x))

(assert! (let ((topic (xdoc::find-topic 'm1 (xdoc::get-xdoc-table (w state)))))
           (and topic
                (equal (cdr (assoc :parents topic))
                       '(foo bar)))))

(defmapappend m2 (x)
  (nats x)
  :guard (my-nat-listp x)
  :parents (bar))

(assert! (let ((topic (xdoc::find-topic 'm2 (xdoc::get-xdoc-table (w state)))))
           (and topic
                (equal (cdr (assoc :parents topic))
                       '(bar)))))


(defmapappend m3 (x)
  (nats x)
  :guard (my-nat-listp x)
  :parents nil)

(assert! (let ((topic (xdoc::find-topic 'm3 (xdoc::get-xdoc-table (w state)))))
           (not topic)))
