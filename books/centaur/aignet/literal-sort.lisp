; Copyright (C) 2020 Centaur Technology
; AIGNET - And-Inverter Graph Networks
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


(in-package "AIGNET")

(include-book "centaur/satlink/litp" :dir :system)
(include-book "defsort/defsort" :dir :system)
(local (include-book "std/lists/sets" :dir :system))

(define lit< ((x litp) (y litp))
  :inline t
  (< (lit-fix x) (lit-fix y))
  ///
  (defthm lit<-transitive
    (implies (and (lit< x y)
                  (lit< y z))
             (lit< x z)))

  (defthm lit<-negation-transitive
    (implies (and (not (lit< x y))
                  (not (lit< y z)))
             (not (lit< x z))))


  (defthm lit<-irreflexive
    (not (lit< x x))))

(defsection literal-sort
  (acl2::defsort literal-sort (x)
    :compare< lit<
    :comparablep litp
    :comparable-listp lit-listp
    :true-listp t)


  (defthm set-equiv-of-literal-sort-insert
    (acl2::set-equiv (literal-sort-insert x y)
                     (cons x y))
    :hints(("Goal" :in-theory (enable literal-sort-insert)
            :induct t)
           (and stable-under-simplificationp
                '(:in-theory (enable acl2::set-unequal-witness-rw)))))

  (defthm set-equiv-of-literal-sort
    (acl2::set-equiv (literal-sort-insertsort x) x)
    :hints(("Goal" :in-theory (enable literal-sort-insertsort))))




  (defthm lit-listp-of-literal-sort-insert
    (implies (and (litp x) (lit-listp y))
             (lit-listp (literal-sort-insert x y)))
    :hints(("Goal" :in-theory (enable literal-sort-insert))))

  (defthm lit-listp-of-literal-sort-insertsort
    (implies (lit-listp x)
             (lit-listp (literal-sort-insertsort x)))
    :hints(("Goal" :in-theory (enable literal-sort-insertsort))))

  ;; (defthm aignet-lit-listp-of-literal-sort-insert
  ;;   (implies (and (aignet-litp x aignet) (aignet-lit-listp y aignet))
  ;;            (aignet-lit-listp (literal-sort-insert x y) aignet))
  ;;   :hints(("Goal" :in-theory (enable literal-sort-insert))))

  ;; (defthm aignet-lit-listp-of-literal-sort-insertsort
  ;;   (implies (aignet-lit-listp x aignet)
  ;;            (aignet-lit-listp (literal-sort-insertsort x) aignet))
  ;;   :hints(("Goal" :in-theory (enable literal-sort-insertsort))))

  (defthm len-of-literal-sort-insert
    (equal (len (literal-sort-insert x y))
           (+ 1 (len y)))
    :hints(("Goal" :in-theory (enable literal-sort-insert)))))




