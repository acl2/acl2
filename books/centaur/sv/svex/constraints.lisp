; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2014-2015 Centaur Technology
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

(in-package "SV")

(include-book "vars")
(local (include-book "std/lists/sets" :dir :system))

(local (std::add-default-post-define-hook :fix))

(define constraintlist->conds ((x constraintlist-p))
  :returns (conds svexlist-p)
  (if (atom x)
      nil
    (cons (constraint->cond (car x))
          (constraintlist->conds (cdr x))))
  ///
  (defret len-of-constraintlist->conds
    (equal (len conds) (len x)))

  (defret vars-of-constraintlist->conds
    (implies (not (member v (constraintlist-vars x)))
             (not (member v (svexlist-vars conds))))
    :hints(("Goal" :in-theory (enable constraintlist-vars svexlist-vars)))))

(define constraintlist->names ((x constraintlist-p))
  :returns (names)
  (if (atom x)
      nil
    (cons (constraint->name (car x))
          (constraintlist->names (cdr x))))
  ///
  (defret len-of-constraintlist->names
    (equal (len names) (len x))))

(define constraintlist-update-conds ((x constraintlist-p)
                                     (conds svexlist-p))
  :guard (equal (len conds) (len x))
  :returns (new-x constraintlist-p)
  (if (atom x)
      nil
    (cons (change-constraint (car x) :cond (car conds))
          (constraintlist-update-conds (cdr x) (cdr conds))))
  ///
  (fty::deffixequiv constraintlist-update-conds
    :hints(("Goal" :expand ((svexlist-fix conds))
            :in-theory (enable default-car default-cdr)
            :induct t)))

  (defret vars-of-constraintlist-update-conds
    (implies (not (member v (svexlist-vars conds)))
             (not (member v (constraintlist-vars new-x))))
    :hints(("Goal" :in-theory (enable svexlist-vars constraintlist-vars
                                      default-car)))))



