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
 
; cert_param: (non-acl2r)

(in-package "FGL")

(include-book "pathcond-aig")
(include-book "pathcond-aignet")
(include-book "pathcond-stobj")
(include-book "bfr")
(local (include-book "theory"))



(defsection pathcondp
  (local (in-theory (enable pathcondp)))
  (defthm pathcondp-implies-ubddp
    (implies (pathcondp x)
             (acl2::ubddp (nth *pathcond-bdd* x))))

  (defthm pathcondp-implies-calistp
    (implies (pathcondp x)
             (calistp (nth *pathcond-aig* x))))

  (defthm pathcondp-implies-nbalistp
    (implies (pathcondp x)
             (aignet::nbalistp (nth *pathcond-aignet* x))))

  (defthm pathcondp-implies-ubdd-listp-checkpoint-ubdds
    (implies (pathcondp x)
             (acl2::ubdd-listp (nth *pathcond-checkpoint-ubdds* x))))

  (defthm pathcondp-implies-nat-listp-checkpoint-ptrs
    (implies (pathcondp x)
             (nat-listp (nth *pathcond-checkpoint-ptrs* x))))

  (local (in-theory (enable aignet::redundant-update-nth)))

  (defthm pathcondp-implies-update-bdd-equal
    (implies (and (pathcondp x)
                  (equal bdd (nth *pathcond-bdd* x)))
             (equal (update-nth *pathcond-bdd* bdd x) x)))

  (defthm pathcondp-implies-update-aig-equal
    (implies (and (pathcondp x)
                  (equal calist (nth *pathcond-aig* x)))
             (equal (update-nth *pathcond-aig* calist x) x)))

  (defthm pathcondp-implies-update-aignet-equal
    (implies (and (pathcondp x)
                  (equal nbalist (nth *pathcond-aignet* x)))
             (equal (update-nth *pathcond-aignet* nbalist x) x)))

  (defthm pathcondp-of-update-bdd
    (implies (and (pathcondp x)
                  (acl2::ubddp bdd))
             (pathcondp (update-nth *pathcond-bdd* bdd x))))

  (defthm pathcondp-of-update-aig
    (implies (and (pathcondp x)
                  (calistp calist))
             (pathcondp (update-nth *pathcond-aig* calist x))))

  (defthm pathcondp-of-update-aignet
    (implies (and (pathcondp x)
                  (aignet::nbalistp nbalist)
                  (not (equal (aignet::nbalist-lookup 0 nbalist) 0)))
             (pathcondp (update-nth *pathcond-aignet* nbalist x)))))

(define ubdd-list-fix ((x acl2::ubdd-listp))
  :returns (new-x acl2::ubdd-listp)
  (mbe :logic
       (if (atom x)
           nil
         (cons (acl2::ubdd-fix (car x))
               (ubdd-list-fix (cdr x))))
       :exec x)
  ///
  (defthm ubdd-list-fix-when-ubdd-listp
    (implies (acl2::ubdd-listp x)
             (equal (ubdd-list-fix x) x)))
  
  (defthm len-of-ubdd-list-fix
    (equal (len (ubdd-list-fix x))
           (len x))))


(define pathcond-fix (pathcond)
  :returns (new-pathcond pathcondp)
  :prepwork ((local (defthm len-equal-n
                      (implies (syntaxp (quotep n))
                               (equal (equal (len x) n)
                                      (if (zp n)
                                          (and (atom x) (equal n 0))
                                        (and (consp x)
                                             (equal (len (cdr x)) (1- n))))))))
             (local (in-theory (disable len acl2::nth-when-too-large-cheap
                                        nat-listp
                                        pathcondp-implies-calistp
                                        pathcondp-implies-nat-listp-checkpoint-ptrs
                                        pathcondp-implies-ubdd-listp-checkpoint-ubdds
                                        pathcondp-implies-ubddp
                                        pathcondp-implies-nbalistp))))
  ;; :guard-hints (("goal" :expand ((len pathcond)
  ;;                                (len (cdr pathcond))
  ;;                                (len (cddr pathcond))
  ;;                                (len (cdddr pathcond))
  ;;                                (len (cddddr pathcond)))))
  (mbe :logic (non-exec (list (acl2::ubdd-fix (pathcond-bdd pathcond))
                              (calist-fix (pathcond-aig pathcond))
                              (aignet::nbalist-fix (pathcond-aignet pathcond))
                              (bool-fix (pathcond-enabledp pathcond))
                              (acl2::nat-list-fix (pathcond-checkpoint-ptrs pathcond))
                              (ubdd-list-fix (pathcond-checkpoint-ubdds pathcond))))
       :exec pathcond)
  ///
  (defthm nth-of-pathcond-fix
    (and (equal (nth *pathcond-bdd* (pathcond-fix pathcond))
                (acl2::ubdd-fix (nth *pathcond-bdd* pathcond)))
         (equal (nth *pathcond-aig* (pathcond-fix pathcond))
                (calist-fix (nth *pathcond-aig* pathcond)))
         (equal (nth *pathcond-aignet* (pathcond-fix pathcond))
                (aignet::nbalist-fix (nth *pathcond-aignet* pathcond)))
         (equal (nth *pathcond-enabledp* (pathcond-fix pathcond))
                (acl2::bool-fix (nth *pathcond-enabledp* pathcond)))
         (equal (nth *pathcond-checkpoint-ptrs* (pathcond-fix pathcond))
                (acl2::nat-list-fix (nth *pathcond-checkpoint-ptrs* pathcond)))
         (equal (nth *pathcond-checkpoint-ubdds* (pathcond-fix pathcond))
                (ubdd-list-fix (nth *pathcond-checkpoint-ubdds* pathcond)))))

  (local (defthm equal-of-cons
           (equal (equal (cons a b) c)
                  (and (consp c)
                       (equal (car c) a)
                       (equal (cdr c) b)))))

  (defthm pathcond-fix-when-pathcondp
    (implies (pathcondp pathcond)
             (equal (pathcond-fix pathcond) pathcond))
    ;; :hints (("goal" :expand ((len pathcond)
    ;;                          (len (cdr pathcond))
    ;;                          (len (cddr pathcond))
    ;;                          (len (cdddr pathcond))
    ;;                          (len (cddddr pathcond))
    ;;                          (len (cddddr (cdr pathcond)))
    ;;                          (len (cddddr (cddr pathcond))))))
    )

  (defun-nx pathcond-equiv (x y)
    (equal (pathcond-fix x) (pathcond-fix y)))

  (defequiv pathcond-equiv)

  (fty::deffixtype pathcond :pred pathcondp :fix pathcond-fix :equiv pathcond-equiv)

  (in-theory (disable pathcondp)))

(define pathcond-rewind-stack-len ((bfr-mode bfr-mode-p)
                                   pathcond)
  (bfr-mode-case bfr-mode
    :bdd (len (pathcond-checkpoint-ubdds pathcond))
    :otherwise (len (pathcond-checkpoint-ptrs pathcond))))

(local (defthm ubdd-listp-of-cdr
         (implies (acl2::ubdd-listp x)
                  (acl2::ubdd-listp (cdr x)))))

(local (Defthm rationalp-when-natp
         (implies (natp x)
                  (rationalp x))))

(define pathcond-rewind-ok ((bfr-mode bfr-mode-p) pathcond)
  (or (not (pathcond-enabledp pathcond))
      (< 0 (pathcond-rewind-stack-len bfr-mode pathcond))))

(define pathcond-rewind ((bfr-mode bfr-mode-p)
                         pathcond)
  :guard (pathcond-rewind-ok bfr-mode pathcond)
  :guard-hints (("goal" :in-theory (enable pathcond-rewind-stack-len
                                           pathcond-rewind-ok)))
  :returns new-pathcond
  (b* ((pathcond (pathcond-fix pathcond))
       ((unless (pathcond-enabledp pathcond))
        pathcond))
    (bfr-mode-case
      :aig (let* ((ptrs (pathcond-checkpoint-ptrs pathcond))
                  (chp (lnfix (car ptrs)))
                  (pathcond (update-pathcond-checkpoint-ptrs (cdr ptrs) pathcond)))
             (stobj-let ((calist-stobj (pathcond-aig pathcond)))
                        (calist-stobj)
                        (let ((chp (if (<= chp (calist-stobj-len calist-stobj)) chp 0)))
                          (rewind-calist chp calist-stobj))
                        pathcond))
      :aignet (let* ((ptrs (pathcond-checkpoint-ptrs pathcond))
                  (chp (lnfix (car ptrs)))
                  (pathcond (update-pathcond-checkpoint-ptrs (cdr ptrs) pathcond)))
                (stobj-let ((aignet-pathcond (pathcond-aignet pathcond)))
                           (aignet-pathcond)
                           (let ((chp (if (<= chp (aignet-pathcond-len aignet-pathcond)) chp 0)))
                             (aignet-pathcond-rewind chp aignet-pathcond))
                           pathcond))
      :bdd (let* ((stack (pathcond-checkpoint-ubdds pathcond))
                  (chp (car stack))
                  (pathcond (update-pathcond-checkpoint-ubdds (cdr stack) pathcond)))
             (update-pathcond-bdd (acl2::ubdd-fix chp) pathcond))))
  ///
  (local (defthm update-nth-same
           (equal (update-nth n v1 (update-nth n v2 x))
                  (update-nth n v1 x))
           :hints(("Goal" :in-theory (enable update-nth)))))
  (local (defthm update-nth-lemma
           (implies (equal x (update-nth n val y))
                    (equal (update-nth n val1 x)
                           (update-nth n val1 y)))))

  (local (defthm len-of-ubdd-list-fix
           (equal (len (ubdd-list-fix x)) (len x))
           :hints(("Goal" :in-theory (enable len ubdd-list-fix)))))

  (local (defthm len-cdr-when-positive
           (equal (len (cdr x)) (+ -1 (pos-fix (len x))))
           :hints(("Goal" :in-theory (enable len pos-fix)))))

  (defthm rewind-stack-len-of-pathcond-rewind
    (implies (pathcond-enabledp pathcond)
             (equal (pathcond-rewind-stack-len bfr-mode (pathcond-rewind bfr-mode pathcond))
                    (1- (pos-fix (pathcond-rewind-stack-len bfr-mode pathcond)))))
    :hints(("Goal" :in-theory (e/d (pathcond-rewind-stack-len ubdd-list-fix pos-fix))))))



