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

(local (include-book "arithmetic/top-with-meta" :dir :system))

;; This function crops up all over the place.

(defun numlist-aux (last by n acc)
  (declare (xargs :guard (and (acl2-numberp last)
                              (acl2-numberp by)
                              (natp n))))
  (if (zp n)
      acc
    (numlist-aux (- last by) by (1- n) (cons last acc))))

(defun numlist (start by n)
  (declare (xargs :guard (and (acl2-numberp start)
                              (acl2-numberp by)
                              (natp n))
                  :verify-guards nil))
  (mbe :logic (if (mbe :logic (zp n) :exec (= n 0))
                  nil
                (cons start (numlist (+ start by) by (1- n))))
       :exec (numlist-aux (+ start (* (1- n) by)) by n nil)))

(local (defthm fix-when-number
         (implies (acl2-numberp n)
                  (equal (fix n) n))))

(local (defthm +-of-fix-1
         (equal (+ (fix y) x)
                (+ y x))))

(local
 (defthm numlist-absorb-append-lemma
   (implies (and (acl2-numberp start)
                 (equal start2 (+ start (* by (nfix n)))))
            (equal (append (numlist start by n)
                           (numlist start2 by m)
                           rest)
                   (append (numlist start by (+ (nfix n) (nfix m))) rest)))
   :hints (("goal" :induct (numlist start by n)
            :in-theory (disable (force) fix)))))

(local
 (defthm numlist-absorb-last
   (implies (and (acl2-numberp start)
                 (equal last (+ start (* by (+ -1 n))))
                 (posp n))
            (equal (append (numlist start by (+ -1 n))
                           (cons last rest))
                   (append (numlist start by n) rest)))
   :hints (("goal" :use ((:instance numlist-absorb-append-lemma
                          (start2 last)
                          (n (+ -1 n))
                          (m 1)))
            :expand ((:free (start by) (numlist start by 1)))
            :do-not-induct t
            :in-theory (disable numlist-absorb-append-lemma)))))

(local (defthm minus-plus-const-times-x-rest
         (implies (syntaxp (quotep n))
                  (equal (+ (- x) (* n x) rest)
                         (+ (* (1- n) x) rest)))))

(defthm numlist-aux-is-numlist
  (implies (acl2-numberp last)
           (equal (numlist-aux last by n acc)
                  (append (numlist (- last (* (1- (nfix n)) by)) by n) acc)))
  :hints (("goal" :induct (numlist-aux last by n acc)
           :in-theory (disable fix))))

(verify-guards numlist)



(defthm len-numlist
  (equal (len (numlist start by n))
         (nfix n)))

