; Centaur Lexer Library
; Copyright (C) 2013 Centaur Technology
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

(in-package "ACL2")
(include-book "std/util/defrule" :dir :system)
(include-book "std/lists/top" :dir :system)
(include-book "std/strings/arithmetic" :dir :system)
(include-book "std/basic/arith-equivs" :dir :system)
(local (include-book "arithmetic/top-with-meta" :dir :system))

(in-theory (disable nth
                    update-nth
                    ;; These can interfere with stobj stuff
                    nth-0-cons
                    nth-when-zp
                    nth-add1))

(local (in-theory (enable nthcdr len nth)))

(defrule nthcdr-of-len
  (implies (true-listp x)
           (equal (nthcdr (len x) x)
                  nil)))

(defrule nthcdr-of-len-free
  (implies (and (equal n (len x))
                (true-listp x))
           (equal (nthcdr n x)
                  nil)))

(defrule cdr-of-nthcdr
  (equal (cdr (nthcdr n x))
         (nthcdr (+ 1 (nfix n)) x)))

(defrule nth-when-index-too-big
  (implies (<= (len x) (nfix n))
           (equal (nth n x)
                  nil)))

;; now part of std/lists
;; (defrule nth-of-nthcdr
;;   (equal (nth a (nthcdr b x))
;;          (nth (+ (nfix a) (nfix b)) x))
;;   :disable (acl2::nthcdr-of-cdr))

(defrule nthcdr-under-iff-when-true-listp
  (implies (true-listp x)
           (iff (nthcdr n x)
                (< (nfix n) (len x)))))

(defthm true-listp-when-character-listp
  (implies (character-listp x)
           (true-listp x)))

(defthm character-listp-of-nthcdr
  (implies (character-listp x)
           (character-listp (nthcdr n x)))
  :hints(("Goal" :in-theory (disable acl2::cdr-of-nthcdr))))

(defthm character-listp-of-take
  (implies (character-listp x)
           (equal (character-listp (take n x))
                  (<= (nfix n) (len x)))))
