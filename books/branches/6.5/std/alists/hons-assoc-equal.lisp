; Standard Association Lists Library
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
; Original authors: Jared Davis <jared@centtech.com>
;                   Sol Swords <sswords@centtech.com>

(in-package "ACL2")
(include-book "../lists/equiv")
(local (in-theory (enable hons-assoc-equal)))

(defsection std/alists/hons-assoc-equal
  :parents (std/alists hons-assoc-equal hons-get)
  :short "Lemmas about @(see hons-assoc-equal) available in the @(see
std/alists) library."

  :long "<p><b>NOTE:</b> It is a good idea to be very clear on the relationship
between @('hons-get') and @('hons-assoc-equal'):</p>

<ul>

<li>To get hash table speeds out of @(see fast-alists) during execution, you
must write your functions in terms of @(see hons-get) instead of
@('hons-assoc-equal')!  But,</li>

<li>You should never write theorems about @('hons-get')!  It just rewrites into
@('hons-assoc-equal').  We always reason in terms of @('hons-assoc-equal'),
which is useful, e.g., to avoid spurious @(see slow-alist-warning)s during
proofs.</li>

</ul>

<p>@('hons-assoc-equal') is the \"modern\" alternative to @(see assoc), and
properly respect the non-alist convention; see @(see std/alists) for discussion
of this convention.</p>"

  (defthm hons-assoc-equal-when-atom
    (implies (atom alist)
             (equal (hons-assoc-equal a alist)
                    nil)))

  (defthm hons-assoc-equal-of-cons
    (equal (hons-assoc-equal key (cons entry map))
           (if (and (consp entry)
                    (equal key (car entry)))
               entry
             (hons-assoc-equal key map))))

  (encapsulate
    ()
    (local (defthmd l0
             (equal (hons-assoc-equal key (list-fix alist))
                    (hons-assoc-equal key alist))))

    (defcong list-equiv equal (hons-assoc-equal key alist) 2
      :hints(("Goal"
              :in-theory (enable list-equiv)
              :use ((:instance l0 (alist alist))
                    (:instance l0 (alist alist-equiv)))))))

  (defthm hons-assoc-equal-of-hons-acons
    (equal (hons-assoc-equal key (hons-acons key2 val map))
           (if (equal key key2)
               (cons key val)
             (hons-assoc-equal key map))))

  (defthm consp-of-hons-assoc-equal
    (equal (consp (hons-assoc-equal x alist))
           (if (hons-assoc-equal x alist)
               t
             nil)))

  (defthm car-hons-assoc-equal
    (implies (hons-assoc-equal k a)
             (equal (car (hons-assoc-equal k a))
                    k)))

  (defthm car-hons-assoc-equal-split
    (equal (car (hons-assoc-equal key alist))
           (if (hons-assoc-equal key alist)
               key
             nil)))

  (defthm hons-assoc-equal-append
    (equal (hons-assoc-equal x (append a b))
           (or (hons-assoc-equal x a)
               (hons-assoc-equal x b))))



  (defthm hons-assoc-equal-of-hons-shrink-alist
    (equal (hons-assoc-equal a (hons-shrink-alist x y))
           (or (hons-assoc-equal a y)
               (hons-assoc-equal a x))))

  (defthm cons-key-cdr-hons-assoc-equal
    (implies (hons-assoc-equal k a)
             (equal (cons k (cdr (hons-assoc-equal k a)))
                    (hons-assoc-equal k a)))))

