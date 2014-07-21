; AIGNET - And-Inverter Graph Networks
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "AIGNET")


(defun aig-to-aignet-fast-rec (x restore-arr varmap gatesimp strash aignet)
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
                (aig-to-aignet-fast-rec (car x) restore-arr varmap gatesimp strash aignet)))
            (mv (lit-negate lit) restore-arr strash aignet))
   ;; Subtlety:  A cons that has been visited will be marked with a CDR that is
   ;; (list nil).  Since the :inv case above looks for a cons with cdr NIL,
   ;; this is safe.  If the two cases could be confused, we'd need to do the
   ;; check for a visited cons before the check for an inversion.
   :and (b* (((when (acl2::cons-was-visited x restore-arr))
              (mv (car x) restore-arr strash aignet))
             ((mv lit restore-arr strash aignet)
              (b* (((mv lit1 restore-arr strash aignet)
                    (aig-to-aignet-fast-rec (car x) restore-arr varmap gatesimp strash aignet))
                   ((when (int= lit1 0))
                    (mv 0 restore-arr strash aignet))
                   ((mv lit2 restore-arr strash aignet)
                    (aig-to-aignet-fast-rec (cdr x) restore-arr varmap gatesimp strash aignet))
                   ((mv lit strash aignet)
                    (aignet-hash-and lit1 lit2 gatesimp strash aignet)))
                (mv lit restore-arr strash aignet)))
             (restore-arr (acl2::mark-visited-cons x lit restore-arr)))
          (mv lit restore-arr strash aignet))))

(defun aiglist-to-aignet-fast-rec (x restore-arr varmap gatesimp strash aignet)
  (let* (lit
         (lits (loop while (consp x) collect
                     (progn (multiple-value-setq
                                (lit restore-arr strash aignet)
                              (aig-to-aignet-fast-rec
                               (car x) restore-arr varmap gatesimp strash aignet))
                            (setq x (cdr x))
                            lit))))
    (mv lits restore-arr strash aignet)))

;; (defun aiglist-to-aignet-fast-rec (x restore-arr varmap gatesimp strash aignet)
;;   (b* (((when (atom x))
;;         (mv nil restore-arr strash aignet))
;;        ((mv lit restore-arr strash aignet)
;;         (aig-to-aignet-fast-rec (car x) restore-arr varmap gatesimp strash aignet))
;;        ((mv rest restore-arr strash aignet)
;;         (aiglist-to-aignet-fast-rec (cdr x) restore-arr varmap gatesimp strash aignet)))
;;     (mv (cons lit rest) restore-arr strash aignet)))

(defun aiglist-to-aignet-top (x varmap gatesimp strash aignet)
  (acl2::with-fast-cons-memo
    :fnname aiglist-to-aignet-top
    :return-vals (lits strash aignet)
    :restore-array restore-arr
    :initial-size (* 10 (len x))
    :body (b* (((mv lits ?restore-arr strash aignet)
                (cwtime
                 (aiglist-to-aignet-fast-rec
                  x restore-arr varmap gatesimp strash aignet))))
            (mv lits strash aignet))))



