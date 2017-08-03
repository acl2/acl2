; ACL2 interface to the ZZ system
; Copyright (C) 2011-2017 Centaur Technology
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

(include-book "zz-check")
(include-book "centaur/aig/induction" :dir :system)
(local (include-book "centaur/misc/hons-sets" :dir :system))

;; This book creates a macro that can generate a theorem of the form
;; (check-property <updates> <prop> <initst> inputs)
;; if an inductive invariant and resolution proofs for three required
;; properties of that invariant are stored in the state global zz-mc-invariants.


(defthm zzchk-check-implies-unsat-p
  (implies (not (unsat-p x))
           (not (zzchk-check (aig-norm x) proof)))
  :hints(("Goal" :in-theory (enable unsat-p))))


(defthm checked-conditions-imply-check-property
  (implies (and (hons-subset (aig-vars invar) (alist-keys updates))
                ;; The invariant is inductive, i.e. it is preserved by the update function
                (zzchk-check
                 (aig-norm
                  (aig-and
                   invar
                   (aig-not
                    (aig-restrict invar updates))))
                 inductivity-proof)
                ;; The invariant implies the property
                (zzchk-check
                 (aig-norm
                  (aig-and invar (aig-not prop)))
                 sufficiency-proof)
                ;; The invariant holds under the initial state.
                (zzchk-check
                 (aig-norm (aig-not (aig-partial-eval invar initst)))
                 initialization-proof))
           (check-property updates prop initst inputs)))

(defthm checked-conditions-imply-check-property-strong
  (implies (and (hons-subset (aig-vars invar)
                             (alist-keys updates))
                ;; The invariant is inductive, i.e. it is preserved by the update function
                (zzchk-check
                 (aig-norm
                  (aig-and
                   invar
                   (aig-not
                    (aig-restrict invar updates))))
                 inductivity-proof)
                ;; The invariant implies the property
                (zzchk-check
                 (aig-norm
                  (aig-and invar (aig-not prop)))
                 sufficiency-proof)
                ;; The invariant holds under the initial state.
                (zzchk-check
                 (aig-norm (aig-not (aig-partial-eval invar initst)))
                 initialization-proof))
           (check-property-strong updates prop initst inputs)))

(defthm checked-conditions-imply-check-ag-property
  (implies (and (hons-subset (aig-vars invar)
                             (alist-keys updates))
                ;; The invariant is inductive, i.e. it is preserved by the update function
                (zzchk-check
                 (aig-norm
                  (aig-and
                   invar
                   (aig-not
                    (aig-restrict invar updates))))
                 inductivity-proof)
                ;; The invariant implies the property
                (zzchk-check
                 (aig-norm
                  (aig-and invar (aig-not prop)))
                 sufficiency-proof)
                ;; The invariant holds under the initial state.
                (zzchk-check
                 (aig-norm (aig-not (aig-partial-eval invar initst)))
                 initialization-proof))
           (check-ag-property updates prop initst)))


(local
 (defthm alist-equiv-append-when-agree-lemma
   (implies (alists-agree (alist-keys a) a b)
            (alist-equiv (append a b c)
                         (append b c)))
   :hints (("goal" :in-theory (enable alist-equiv-iff-agree-on-bad-guy)
            :use ((:instance alists-agree-hons-assoc-equal
                   (keys (alist-keys a))
                   (x (alist-equiv-bad-guy (append a b c)
                                           (append b c)))))))))


(defthm checked-conditions-imply-check-property-of-compliant-initst
  (implies (and (hons-subset (aig-vars invar) (alist-keys updates))
                ;; The invariant is inductive, i.e. it is preserved by the update function
                (zzchk-check
                 (aig-norm
                  (aig-and
                   invar
                   (aig-not
                    (aig-restrict invar updates))))
                 inductivity-proof)
                ;; The invariant implies the property
                (zzchk-check
                 (aig-norm
                  (aig-and invar (aig-not prop)))
                 sufficiency-proof)
                ;; The invariant holds under the initial state.
                (zzchk-check
                 (aig-norm (aig-not (aig-partial-eval invar initst)))
                 initialization-proof)
                (alists-agree (alist-keys initst) initst ctrex-initst))
           (check-property updates prop ctrex-initst inputs))
  :hints (("goal" :use ((:instance checked-conditions-imply-check-property
                         (inputs (cons (append ctrex-initst (car inputs))
                                       (cdr inputs)))))
           :in-theory (disable hons-subset
                               checked-conditions-imply-check-property
                               inductive-invariant-impl-check-property
                               checked-conditions-imply-check-ag-property)
           :expand ((check-property updates prop ctrex-initst inputs))
           :do-not-induct t))
  :otf-flg t)



(defmacro def-proof-checked-zz-mc-thm (name updates prop initst
                                            &key checker)
  `(make-event
    (b* ((prop ,prop)
         (updates ,updates)
         (initst ,initst)
         (name ',name)
         ((list* invar
                 inductivity-proof
                 sufficiency-proof
                 initialization-proof)
          (cdr (hons-get (hons updates (hons prop initst))
                         (@ zz-mc-invariants)))))
      `(defthm ,name
         (,(case ,checker
             (:strong 'check-property-strong)
             (:ag 'check-ag-property)
             (otherwise 'check-property))
          ',updates ',prop ',initst . ,(and (not (eq ,checker :ag)) '(inputs)))
         :hints (("goal" :use ((:instance
                                ,(case ,checker
                                   (:strong
                                    'checked-conditions-imply-check-property-strong)
                                   (:ag
                                    'checked-conditions-imply-check-ag-property)
                                   (otherwise
                                    'checked-conditions-imply-check-property))
                                (invar ',invar)
                                (inductivity-proof ',inductivity-proof)
                                (sufficiency-proof ',sufficiency-proof)
                                (initialization-proof ',initialization-proof)
                                (updates ',updates)
                                (prop ',prop)
                                (initst ',initst)
                                . ,(and (not (eq ,checker :ag))
                                        '((inputs inputs)))))
                  :in-theory
                  (e/d** ((:rules-of-class :executable-counterpart :here)))))))))
