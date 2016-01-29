; Centaur Miscellaneous Books
; Copyright (C) 2008-2011 Centaur Technology
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
; Original authors: Sol Swords <sswords@centtech.com>
;                   Jared Davis <jared@centtech.com>

(in-package "ACL2")

(include-book "std/util/bstar" :dir :system)


(defun accumulate-to-each (keys val al)
  (declare (xargs :guard t))
  (if (atom keys)
      al
    (b* ((rest (cdr (hons-get (car keys) al))))
      (accumulate-to-each (cdr keys) val
                          (hons-acons (car keys)
                                      (cons val rest)
                                      al)))))

(defun graph-transpose (edges acc)
  ;; This inverts an alist of keys to lists of values, e.g.,
  ;;    key1 -> (val1 val2)
  ;;    key2 -> (val1 val3)
  ;; And inverts it to produce an alist binding each value to all of the keys
  ;; that include it, e.g.,
  ;;    val1 -> (key1 key2)
  ;;    val2 -> (key1)
  ;;    val3 -> (key2)
  (declare (xargs :guard t))
  (cond ((atom edges)
         (b* ((ret (hons-shrink-alist acc nil)))
           (fast-alist-free acc)
           (fast-alist-free ret)
           ret))
        ((atom (car edges))
         ;; Bad alist convention
         (graph-transpose (cdr edges) acc))
        (t
         (graph-transpose (cdr edges)
                          (accumulate-to-each
                           (cdar edges) (caar edges)
                           acc)))))
