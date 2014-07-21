
; no-duplicates.lisp: Reasoning about no-duplicatesp-equal and
; intersectp-equal.  Name-compatible with list-theory.lisp and set-theory.lisp.

; Copyright (C) 2010 Centaur Technology
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
; Original author: Sol Swords <sswords@centtech.com>


(in-package "ACL2")

(defthm associativity-of-append
  ;; Renamed by Jared for compatibility with data-structures/list-defthms
  (equal (append (append a b) c)
         (append a (append b c))))

(defthm member-equal-append
  (iff (member-equal x (append a b))
       (or (member-equal x a)
           (member-equal x b))))

;; Note: inesrting double-rewrites here because A and B are now in a
;; set-equivalence context within intersectp-equal, whereas they weren't
;; within no-duplicatesp-equal.
(defthm no-duplicatesp-equal-append-iff
  (iff (no-duplicatesp-equal (append a b))
       (and (no-duplicatesp-equal a)
            (no-duplicatesp-equal b)
            (not (intersectp-equal (double-rewrite a)
                                   (double-rewrite b))))))

(defthm intersectp-equal-append1
  (equal (intersectp-equal (append a b) c)
         (or (intersectp-equal a c)
             (intersectp-equal b c))))


(defthm intersectp-equal-cons-second
  (iff (intersectp-equal a (cons c b))
       (or (member-equal c a)
           (intersectp-equal a b))))

(defthm intersectp-equal-non-cons-1
  (implies (not (consp a))
           (not (intersectp-equal a b))))

(defthm intersectp-equal-non-cons
  (implies (not (consp b))
           (not (intersectp-equal a b))))

(defthm intersectp-equal-append2
  (equal (intersectp-equal c (append a b))
         (or (intersectp-equal c a)
             (intersectp-equal c b))))


(defthm intersectp-equal-commute
  (iff (intersectp-equal a b)
       (intersectp-equal b a)))




; [Removed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2.]
; (defthm member-is-member-equal
;   (equal (member x y) (member-equal x y)))

; [Removed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2.]
; (defthm no-duplicatesp-is-no-duplicatesp-equal
;   (equal (no-duplicatesp x)
;          (no-duplicatesp-equal x)))

(defthm no-duplicatesp-equal-non-cons
  (implies (not (consp x))
           (no-duplicatesp-equal x)))


