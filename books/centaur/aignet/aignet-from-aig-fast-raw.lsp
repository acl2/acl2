; AIGNET - And-Inverter Graph Networks
; Copyright (C) 2013 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Sol Swords <sswords@centtech.com>

(in-package "AIGNET")


(defun aig-to-aignet-fast-rec (x restore-arr varmap strash gatesimp aignet)
  (aig-cases
   x
   :true  (mv 1 restore-arr strash aignet)
   :false (mv 0 restore-arr strash aignet)
   :var   (b* ((look (hons-get x varmap)))
            (mv (if look
                    (lnfix (cdr look))
                  ;; For missing variables, produce TRUE to match semantics of
                  ;; aig-eval.
                  1)
                restore-arr strash aignet))
   :inv   (b* (((mv lit restore-arr strash aignet)
                (aig-to-aignet-fast-rec (car x) restore-arr varmap strash gatesimp aignet)))
            (mv (lit-negate lit) restore-arr strash aignet))
   ;; Subtlety:  A cons that has been visited will be marked with a CDR that is
   ;; (list nil).  Since the :inv case above looks for a cons with cdr NIL,
   ;; this is safe.  If the two cases could be confused, we'd need to do the
   ;; check for a visited cons before the check for an inversion.
   :and (b* (((when (acl2::cons-was-visited x restore-arr))
              (mv (car x) restore-arr strash aignet))
             ((mv lit restore-arr strash aignet)
              (b* (((mv lit1 restore-arr strash aignet)
                    (aig-to-aignet-fast-rec (car x) restore-arr varmap strash gatesimp aignet))
                   ((when (int= lit1 0))
                    (mv 0 restore-arr strash aignet))
                   ((mv lit2 restore-arr strash aignet)
                    (aig-to-aignet-fast-rec (cdr x) restore-arr varmap strash gatesimp aignet))
                   ((mv lit strash aignet)
                    (aignet-add-simp-gate lit1 lit2 strash gatesimp aignet)))
                (mv lit restore-arr strash aignet)))
             (restore-arr (acl2::mark-visited-cons x lit restore-arr)))
          (mv lit restore-arr strash aignet))))

(defun aiglist-to-aignet-fast-rec (x restore-arr varmap strash gatesimp aignet)
  (let* (lit
         (lits (loop while (consp x) collect
                     (progn (multiple-value-setq
                                (lit restore-arr strash aignet)
                              (aig-to-aignet-fast-rec
                               (car x) restore-arr varmap strash gatesimp aignet))
                            (setq x (cdr x))
                            lit))))
    (mv lits restore-arr strash aignet)))

;; (defun aiglist-to-aignet-fast-rec (x restore-arr varmap strash gatesimp aignet)
;;   (b* (((when (atom x))
;;         (mv nil restore-arr strash aignet))
;;        ((mv lit restore-arr strash aignet)
;;         (aig-to-aignet-fast-rec (car x) restore-arr varmap strash gatesimp aignet))
;;        ((mv rest restore-arr strash aignet)
;;         (aiglist-to-aignet-fast-rec (cdr x) restore-arr varmap strash gatesimp aignet)))
;;     (mv (cons lit rest) restore-arr strash aignet)))

(defun aiglist-to-aignet-top (x varmap strash gatesimp aignet)
  (acl2::with-fast-cons-memo
    :fnname aiglist-to-aignet-top
    :return-vals (lits strash aignet)
    :restore-array restore-arr
    :initial-size (* 10 (len x))
    :body (b* (((mv lits ?restore-arr strash aignet)
                (cwtime
                 (aiglist-to-aignet-fast-rec
                  x restore-arr varmap strash gatesimp aignet))))
            (mv lits strash aignet))))


