; FGL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2019 Centaur Technology
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

(in-package "FGL")
(include-book "fgl-object")
(include-book "bfr")
(include-book "centaur/meta/term-vars" :dir :system)
(include-book "std/util/defenum" :dir :system)
(local (std::add-default-post-define-hook :fix))


;; CGRAPH type -- see ctrex-utils.lisp

(defenum ctrex-ruletype-p (:elim :property nil))

(defprod ctrex-rule
  ((name symbolp :rule-classes :type-prescription)
   (match pseudo-term-subst-p)
   (assign pseudo-termp)
   (assigned-var pseudo-var-p :rule-classes :type-prescription)
   (hyp pseudo-termp)
   (equiv pseudo-fnsym-p)
   (ruletype ctrex-ruletype-p))
  :layout :tree)

(defprod cgraph-edge
  ((match-vars pseudo-var-list-p :rule-classes :type-prescription)
   (rule ctrex-rule-p)
   (subst fgl-object-bindings))
  :layout :tree)

(fty::deflist cgraph-edgelist :elt-type cgraph-edge :true-listp t)

(fty::defmap cgraph :key-type fgl-object :val-type cgraph-edgelist :true-listp t)

(fty::defmap cgraph-alist :key-type fgl-object :true-listp t)



(define cgraph-edge-bfrlist ((x cgraph-edge-p))
  :enabled t
  (fgl-object-bindings-bfrlist (cgraph-edge->subst x)))

(define cgraph-edgelist-bfrlist ((x cgraph-edgelist-p))
  (if (atom x)
      nil
    (append (cgraph-edge-bfrlist (car x))
            (cgraph-edgelist-bfrlist (cdr x)))))

(define cgraph-bfrlist ((x cgraph-p))
  (if (atom x)
      nil
    (append (and (mbt (And (consp (car x))
                           (fgl-object-p (caar x))))
                 (cgraph-edgelist-bfrlist (cdar x)))
            (cgraph-bfrlist (cdr x))))
  ///
  (defthm lookup-in-cgraph-bfrlist
    (implies (and (not (member v (cgraph-bfrlist x)))
                  (fgl-object-p k))
             (not (member v (cgraph-edgelist-bfrlist (cdr (hons-assoc-equal k x))))))
    :hints(("Goal" :in-theory (enable hons-assoc-equal))))

  (defthm cgraph-bfrlist-of-fast-alist-fork
    (implies (and (not (member v (cgraph-bfrlist x)))
                  (not (member v (cgraph-bfrlist y))))
             (not (member v (cgraph-bfrlist (fast-alist-fork x y))))))

  (local (defthm cgraph-fix-of-bad-car
           (implies (not (And (consp (car x))
                              (fgl-object-p (caar x))))
                    (equal (cgraph-fix x)
                           (cgraph-fix (cdr x))))
           :hints(("Goal" :in-theory (enable cgraph-fix))))))
