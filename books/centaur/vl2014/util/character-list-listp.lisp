; VL 2014 -- VL Verilog Toolkit, 2014 Edition
; Copyright (C) 2008-2015 Centaur Technology
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

(in-package "VL2014")
(include-book "defs")
(local (include-book "arithmetic"))

(deflist character-list-listp (x)
  (character-listp x)
  :elementp-of-nil t
  :parents (utilities))

(defthm character-listp-of-flatten
  (implies (character-list-listp x)
           (character-listp (flatten x)))
  :hints(("Goal" :in-theory (enable flatten))))


(defsection vl-character-list-list-values-p
  :parents (utilities)
  :short "Recognizer for alists whose values are strings."

;; BOZO switch to defalist

  (defund vl-character-list-list-values-p (x)
    (declare (xargs :guard t))
    (if (consp x)
        (and (consp (car x))
             (character-list-listp (cdar x))
             (vl-character-list-list-values-p (cdr x)))
      (not x)))

  (local (in-theory (enable vl-character-list-list-values-p)))

  (defthm vl-character-list-list-values-p-when-not-consp
    (implies (not (consp x))
             (equal (vl-character-list-list-values-p x)
                    (not x))))

  (defthm vl-character-list-list-values-p-of-cons
    (equal (vl-character-list-list-values-p (cons a x))
           (and (consp a)
                (character-list-listp (cdr a))
                (vl-character-list-list-values-p x))))

  (defthm vl-character-list-list-values-p-of-hons-shrink-alist
    (implies (and (vl-character-list-list-values-p x)
                  (vl-character-list-list-values-p ans))
             (vl-character-list-list-values-p (hons-shrink-alist x ans)))
    :hints(("Goal" :in-theory (e/d (hons-shrink-alist)
                                   ((force))))))

  (defthm character-list-listp-of-cdr-of-hons-assoc-equal-when-vl-character-list-list-values-p
    (implies (vl-character-list-list-values-p x)
             (character-list-listp (cdr (hons-assoc-equal a x))))))



(define explode-list ((x string-listp))
  :parents (utilities)
  :short "Coerce a list of strings into a @(see character-list-listp)."

  (if (atom x)
      nil
    (cons (explode (car x))
          (explode-list (cdr x))))

  :returns (ans character-list-listp)

  ///

  (defthm explode-list-when-atom
    (implies (atom x)
             (equal (explode-list x)
                    nil)))

  (defthm explode-list-of-cons
    (equal (explode-list (cons a x))
           (cons (explode a)
                 (explode-list x)))))


