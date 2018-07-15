; Centaur AIG Library
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "ACL2")
(include-book "aig-base")

;; BOZO should these be local?
(include-book "centaur/misc/equal-sets" :dir :system)
(include-book "centaur/misc/alist-equiv" :dir :system)

(local (in-theory (disable set::double-containment)))

(define aiglist-vars (x)
  (if (atom x)
      nil
    (set::union (aig-vars (car x))
                (aiglist-vars (cdr x)))))

(defsection aig-vars-thms
  :parents (aig-vars)
  :short "Theorems about @(see aig-vars) from @('centaur/aig/aig-vars')."

  (defthm aig-vars-cons
    (implies (or x (not y))
             (equal (aig-vars (cons x y))
                    (set::union (aig-vars x)
                                (aig-vars y)))))

  (defthm member-aig-vars-alist-vals
    (implies (not (set::in v (aiglist-vars (alist-vals al))))
             (not (set::in v (aig-vars (cdr (hons-assoc-equal x al))))))
    :hints(("Goal" :in-theory (enable hons-assoc-equal aiglist-vars))))


  (defthm aig-vars-aig-not
    (equal (aig-vars (aig-not x))
           (aig-vars x))
    :hints(("Goal" :in-theory (enable aig-not))))


  (local (defthm l1
           (b* (((mv ?hit ans) (aig-and-pass1 x y)))
             (implies (and (not (set::in v (aig-vars x)))
                           (not (set::in v (aig-vars y))))
                      (and (not (set::in v (aig-vars ans))))))
           :hints(("Goal" :in-theory (enable aig-and-pass1)))))

  (local (defthm l2a
           (b* (((mv ?status arg1 arg2) (aig-and-pass2a x y)))
             (implies (and (not (set::in v (aig-vars x)))
                           (not (set::in v (aig-vars y))))
                      (and (not (set::in v (aig-vars arg1)))
                           (not (set::in v (aig-vars arg2))))))
           :hints(("Goal" :in-theory (enable aig-and-pass2a)))))

  (local (defthm l2
           (b* (((mv ?status arg1 arg2) (aig-and-pass2 x y)))
             (implies (and (not (set::in v (aig-vars x)))
                           (not (set::in v (aig-vars y))))
                      (and (not (set::in v (aig-vars arg1)))
                           (not (set::in v (aig-vars arg2))))))
           :hints(("Goal" :in-theory (enable aig-and-pass2)))))

  (local (defthm l3
           (b* (((mv ?status arg1 arg2) (aig-and-pass3 x y)))
             (implies (and (not (set::in v (aig-vars x)))
                           (not (set::in v (aig-vars y))))
                      (and (not (set::in v (aig-vars arg1)))
                           (not (set::in v (aig-vars arg2))))))
           :hints(("Goal" :in-theory (enable aig-and-pass3)))))

  (local (defthm l4a
           (b* (((mv ?status arg1 arg2) (aig-and-pass4a x y)))
             (implies (and (not (set::in v (aig-vars x)))
                           (not (set::in v (aig-vars y))))
                      (and (not (set::in v (aig-vars arg1)))
                           (not (set::in v (aig-vars arg2))))))
           :hints(("Goal" :in-theory (enable aig-and-pass4a)))))

  (local (defthm l4
           (b* (((mv ?status arg1 arg2) (aig-and-pass4 x y)))
             (implies (and (not (set::in v (aig-vars x)))
                           (not (set::in v (aig-vars y))))
                      (and (not (set::in v (aig-vars arg1)))
                           (not (set::in v (aig-vars arg2))))))
           :hints(("Goal" :in-theory (enable aig-and-pass4)))))

  (local (defthm l5
           (b* (((mv ?status arg1 arg2) (aig-and-pass5 x y)))
             (implies (and (not (set::in v (aig-vars x)))
                           (not (set::in v (aig-vars y))))
                      (and (not (set::in v (aig-vars arg1)))
                           (not (set::in v (aig-vars arg2))))))
           :hints(("Goal" :in-theory (enable aig-and-pass5)))))

  (local (defthm l6a
           (b* (((mv ?status arg1 arg2) (aig-and-pass6a x y)))
             (implies (and (not (set::in v (aig-vars x)))
                           (not (set::in v (aig-vars y))))
                      (and (not (set::in v (aig-vars arg1)))
                           (not (set::in v (aig-vars arg2))))))
           :hints(("Goal" :in-theory (enable aig-and-pass6a)))))

  (local (defthm l6
           (b* (((mv ?status arg1 arg2) (aig-and-pass6 x y)))
             (implies (and (not (set::in v (aig-vars x)))
                           (not (set::in v (aig-vars y))))
                      (and (not (set::in v (aig-vars arg1)))
                           (not (set::in v (aig-vars arg2))))))
           :hints(("Goal" :in-theory (enable aig-and-pass6)))))

  (local (defthm member-aig-vars-aig-and-main
           (b* (((mv ?status arg1 arg2) (aig-and-main x y)))
             (implies (and (not (set::in v (aig-vars x)))
                           (not (set::in v (aig-vars y))))
                      (and (not (set::in v (aig-vars arg1)))
                           (not (set::in v (aig-vars arg2))))))
           :hints(("Goal" :in-theory (enable aig-and-main)))))

  (local (in-theory (enable aig-atom-p-of-cons-strong)))

  (defthm member-aig-vars-aig-and
    (implies (and (not (set::in v (aig-vars x)))
                  (not (set::in v (aig-vars y))))
             (not (set::in v (aig-vars (aig-and x y)))))
    :hints(("Goal" :in-theory (enable aig-and))))

  (defthm member-aig-vars-aig-and-dumb
    (implies (and (not (set::in v (aig-vars x)))
                  (not (set::in v (aig-vars y))))
             (not (set::in v (aig-vars (aig-and-dumb x y)))))
    :hints(("Goal" :in-theory (enable aig-and-dumb))))

  (defthm member-aig-vars-aig-restrict
    (implies (and (not (and (set::in v (aig-vars x))
                            (not (member-equal v (alist-keys al)))))
                  (not (set::in v (aiglist-vars (alist-vals al)))))
             (not (set::in v (aig-vars (aig-restrict x al)))))
    :hints(("Goal" :in-theory (enable aig-restrict))))

  (defthm member-aig-vars-aig-partial-eval
    (implies (not (and (set::in v (aig-vars x))
                       (not (member-equal v (alist-keys al)))))
             (not (set::in v (aig-vars (aig-partial-eval x al)))))
    :hints(("Goal" :in-theory (enable aig-partial-eval)))))


