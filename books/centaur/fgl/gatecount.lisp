; FGL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2008-2013 Centaur Technology
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

(include-book "add-primitives")
(include-book "gatecount-stub")
(include-book "gatecount-base")
(local (include-book "std/lists/resize-list" :dir :system))
(local (include-book "primitive-lemmas"))

(def-formula-checks gatecount-formula-checks
  (gatecount support-vars))

(define fgl-object-gatecount ((x fgl-object-p) interp-st)
  :guard (and (bfr-mode-is :aignet (interp-st-bfr-mode))
              (interp-st-bfr-listp (fgl-object-bfrlist x)))
  :returns (count natp :rule-classes :type-prescription)
  (with-local-stobj bitarr
    (mv-let (count bitarr)
      (stobj-let ((logicman (interp-st->logicman interp-st)))
                 (bitarr)
                 (b* ((bitarr (resize-bits (+ 1 (bfrstate->bound (logicman->bfrstate))) bitarr))
                      ((mv bitarr seen) (fgl-object-mark-gates x bitarr logicman nil)))
                   (fast-alist-free seen)
                   bitarr)
                 (b* ((count (bitarr-count bitarr)))
                   (mv count bitarr)))
      count)))
               
(define aignet-collect-marked-bvars ((n natp)
                                     bitarr
                                     bvar-db
                                     aignet)
  :returns (var-list)
  :guard (and (<= (base-bvar bvar-db) n)
              (<= n (aignet::num-ins aignet))
              (eql (next-bvar bvar-db) (aignet::num-ins aignet))
              (<= (aignet::num-fanins aignet) (bits-length bitarr)))
  :measure (nfix (- (aignet::num-ins aignet) (nfix n)))
  (b* (((when (mbe :logic (zp (- (aignet::num-ins aignet) (nfix n)))
                   :exec (eql (aignet::num-ins aignet) n)))
        nil)
       (id (aignet::innum->id n aignet))
       ((when (eql 0 (get-bit id bitarr)))
        (aignet-collect-marked-bvars (1+ (lnfix n)) bitarr bvar-db aignet))
       (var (get-bvar->term n bvar-db)))
    (cons var
          (aignet-collect-marked-bvars (1+ (lnfix n)) bitarr bvar-db aignet))))

(define fgl-object-support-vars ((x fgl-object-p) interp-st)
  :guard (and (bfr-mode-is :aignet (interp-st-bfr-mode))
              (interp-st-bfr-listp (fgl-object-bfrlist x))
              (interp-st-bfrs-ok interp-st))
  :returns (vars)
  :guard-hints (("goal" :in-theory (enable interp-st-bfrs-ok bfr-nvars)))
  (with-local-stobj bitarr
    (mv-let (vars bitarr)
      (stobj-let ((logicman (interp-st->logicman interp-st))
                  (bvar-db  (interp-st->bvar-db interp-st)))
                 (vars bitarr)
                 (b* ((bitarr (resize-bits (+ 1 (bfrstate->bound (logicman->bfrstate))) bitarr))
                      ((mv bitarr seen) (fgl-object-mark-gates x bitarr logicman nil)))
                   (fast-alist-free seen)
                   (stobj-let ((aignet (logicman->aignet logicman)))
                              (vars)
                              (aignet-collect-marked-bvars (base-bvar bvar-db)
                                                           bitarr bvar-db aignet)
                              (mv vars bitarr)))
                 (mv vars bitarr))
      vars)))
                       
                 
(local (defthm fgl-ev-context-equv-forall-extensions-trivial
         (implies (acl2::rewriting-negative-literal
                   `(fgl-ev-context-equiv-forall-extensions ,contexts ,obj ,term ,eval-alist))
                  (iff (fgl-ev-context-equiv-forall-extensions contexts obj term eval-alist)
                       (and 
                        (equal (fgl-ev-context-fix contexts (fgl-ev term eval-alist))
                               (fgl-ev-context-fix contexts obj))
                        (hide (fgl-ev-context-equiv-forall-extensions contexts obj term eval-alist)))))
         :hints (("goal" :expand ((:free (x) (hide x)))
                  :use ((:instance fgl-ev-context-equiv-forall-extensions-necc
                         (ext eval-alist)))
                  :in-theory (disable fgl-ev-context-equiv-forall-extensions-necc)))))

(local (in-theory (disable fgl-ev-context-equiv-forall-extensions)))


(def-fgl-binder-meta gatecount-binder
  (b* (((unless (bfr-mode-is :aignet (interp-st-bfr-mode)))
        (cw "Failed to compute gatecount -- not in aignet mode~%")
        (mv nil nil nil nil interp-st state))
       (count (fgl-object-gatecount arg interp-st)))
    (mv t (kwote count) nil nil interp-st state))
  :formula-check gatecount-formula-checks
  :prepwork ((local (in-theory (enable gatecount))))
  :origfn gatecount :formals (arg))

(def-fgl-binder-meta support-vars-binder
  (b* (((unless (bfr-mode-is :aignet (interp-st-bfr-mode)))
        (cw "Failed to compute gatecount -- not in aignet mode~%")
        (mv nil nil nil nil interp-st state))
       (vars (fgl-object-support-vars arg interp-st)))
    (mv t (kwote vars) nil nil interp-st state))
  :formula-check gatecount-formula-checks
  :prepwork ((local (in-theory (enable support-vars))))
  :origfn support-vars :formals (arg))



(def-fgl-program gatecount! (x)
  (gatecount no-var x))


(defmacro fgl-gatecount (name expr)
  `(let ((,name ,expr))
     (fgl-prog2 (cw "~x0 gatecount: ~x1~%" ',name (gatecount! ,name))
                     ,name)))

(defxdoc fgl-gatecount
  :parents (fgl-debugging)
  :short "Display how many AIG gates are used in the symbolic representation of an object"
  :long "<p>Logically, this returns its second argument; its first argument
should be a variable symbol.  This counts the number of AIG gates that are used
in the symbolic representation of the object (second argument) and prints that
out as a debugging message.</p>

<p>If you want to do anything else with the gatecount, you can get that count
using @('(gatecount! x)') under an @(see unequiv) context, or using the binder
form @('(gatecount free-var x)') in a rewrite rule.</p>")

(def-fgl-program support-vars! (x)
  (support-vars no-var x))


(defmacro fgl-support-vars (name expr)
  `(let ((,name ,expr))
     (fgl-prog2 (cw "~x0 support-vars: ~x1~%" ',name (support-vars! ,name))
                ,name)))

(defxdoc fgl-support-vars
  :parents (fgl-debugging)
  :short "Display the list of objects corresponding to the Boolean variables used in the symbolic representation of an object"
  :long "<p>Logically, this returns its second argument; its first argument
should be a variable symbol.  This finds which Boolean variables are used in
the representation of the object (second argument) and prints out the objects
from which those variables were generated.</p>

<p>If you want to do anything else with this list of objects, you can get that
list using @('(support-vars! x)') under an @(see unequiv) context, or using the binder
form @('(support-vars free-var x)') in a rewrite rule.</p>")
