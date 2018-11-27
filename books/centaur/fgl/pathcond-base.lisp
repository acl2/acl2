; GL - A Symbolic Simulation Framework for ACL2
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
                  (aignet::nbalistp nbalist))
             (pathcondp (update-nth *pathcond-aignet* nbalist x)))))

(define pathcond-fix (pathcond)
  :returns (new-pathcond pathcondp)
  :guard-hints (("goal" :expand ((len pathcond)
                                 (len (cdr pathcond))
                                 (len (cddr pathcond)))))
  (mbe :logic (non-exec (list (acl2::ubdd-fix (pathcond-bdd pathcond))
                              (calist-fix (pathcond-aig pathcond))
                              (aignet::nbalist-fix (pathcond-aignet pathcond))))
       :exec pathcond)
  ///
  (defthm nth-of-pathcond-fix
    (and (equal (nth *pathcond-bdd* (pathcond-fix pathcond))
                (acl2::ubdd-fix (nth *pathcond-bdd* pathcond)))
         (equal (nth *pathcond-aig* (pathcond-fix pathcond))
                (calist-fix (nth *pathcond-aig* pathcond)))
         (equal (nth *pathcond-aignet* (pathcond-fix pathcond))
                (aignet::nbalist-fix (nth *pathcond-aignet* pathcond)))))

  (local (defthm equal-of-cons
           (equal (equal (cons a b) c)
                  (and (consp c)
                       (equal (car c) a)
                       (equal (cdr c) b)))))

  (defthm pathcond-fix-when-pathcondp
    (implies (pathcondp pathcond)
             (equal (pathcond-fix pathcond) pathcond))
    :hints (("goal" :expand ((len pathcond)
                             (len (cdr pathcond))
                             (len (cddr pathcond))
                             (len (cdddr pathcond))))))

  (defun-nx pathcond-equiv (x y)
    (equal (pathcond-fix x) (pathcond-fix y)))

  (defequiv pathcond-equiv)

  (fty::deffixtype pathcond :pred pathcondp :fix pathcond-fix :equiv pathcond-equiv)

  (in-theory (disable pathcondp)))

(define pathcond-checkpoint-p (x (bfr-mode bfr-mode-p) pathcond)
  (bfr-mode-case
    :aig (and (natp x)
              (stobj-let ((calist-stobj (pathcond-aig pathcond)))
                         (ok)
                         (<= x (calist-stobj-len calist-stobj))
                         ok))
    :aignet (and (natp x)
                 (stobj-let ((aignet-pathcond (pathcond-aignet pathcond)))
                            (ok)
                            (<= x (aignet-pathcond-len aignet-pathcond))
                            ok))
    :bdd (acl2::ubddp x)))

(define pathcond-checkpoint ((bfr-mode bfr-mode-p) pathcond)
  :returns (chp (pathcond-checkpoint-p chp bfr-mode pathcond)
                :hints(("Goal" :in-theory (enable pathcond-checkpoint-p))))
  (bfr-mode-case
    :bdd (mbe :logic (acl2::ubdd-fix (pathcond-bdd pathcond))
              :exec (pathcond-bdd pathcond))
    :aig (stobj-let ((calist-stobj (pathcond-aig pathcond)))
                    (len)
                    (calist-stobj-len calist-stobj)
                    len)
    :aignet (stobj-let ((aignet-pathcond (pathcond-aignet pathcond)))
                       (len)
                       (aignet-pathcond-len aignet-pathcond)
                       len)))

(define pathcond-rewindable ((bfr-mode bfr-mode-p) (new pathcondp) (old pathcondp))
  :verify-guards nil
  :non-executable t
  (b* ((new (pathcond-fix new))
       (old (pathcond-fix old)))
    (bfr-mode-case
      :aig (and (equal new (update-nth *pathcond-aig* (nth *pathcond-aig* new) old))
                (calist-extension-p (nth *pathcond-aig* new) (nth *pathcond-aig* old)))
      :aignet (and (equal new (update-nth *pathcond-aignet* (nth *pathcond-aignet* new) old))
                   (aignet::nbalist-extension-p (nth *pathcond-aignet* new) (nth *pathcond-aignet* old)))
      :bdd (equal new (update-nth *pathcond-bdd* (nth *pathcond-bdd* new) old))))
  ///
  (defthm pathcond-checkpoint-p-when-rewindable
    (implies (and (pathcond-rewindable bfr-mode new old)
                  (pathcond-checkpoint-p chp bfr-mode old))
             (pathcond-checkpoint-p chp bfr-mode new))
    :hints(("Goal" :in-theory (enable pathcond-checkpoint-p))))

  (defthm pathcond-rewindable-of-self
    (pathcond-rewindable bfr-mode x x)
    :hints(("Goal" :in-theory (enable aignet::nbalist-extension-p
                                      calist-extension-p)))))

(define pathcond-rewind ((chp (pathcond-checkpoint-p chp bfr-mode pathcond))
                         (bfr-mode bfr-mode-p)
                         pathcond)
  :guard-hints (("goal" :in-theory (enable pathcond-checkpoint-p)))
  (b* ((pathcond (pathcond-fix pathcond)))
    (bfr-mode-case
      :aig (stobj-let ((calist-stobj (pathcond-aig pathcond)))
                      (calist-stobj)
                      (rewind-calist chp calist-stobj)
                      pathcond)
      :aignet (stobj-let ((aignet-pathcond (pathcond-aignet pathcond)))
                         (aignet-pathcond)
                         (aignet-pathcond-rewind chp aignet-pathcond)
                         pathcond)
      :bdd (update-pathcond-bdd (acl2::ubdd-fix chp) pathcond)))
  ///
  (local (defthm update-nth-same
           (equal (update-nth n v1 (update-nth n v2 x))
                  (update-nth n v1 x))
           :hints(("Goal" :in-theory (enable update-nth)))))
  (local (defthm update-nth-lemma
           (implies (equal x (update-nth n val y))
                    (equal (update-nth n val1 x)
                           (update-nth n val1 y)))))

  (defthm pathcond-rewind-when-rewindable
    (implies (pathcond-rewindable bfr-mode new old)
             (equal (pathcond-rewind (pathcond-checkpoint bfr-mode old) bfr-mode new)
                    (pathcond-fix old)))
    :hints(("Goal" :in-theory (enable pathcond-rewindable
                                      pathcond-checkpoint))))

  (defthm pathcond-rewind-when-rewindable-free
    (implies (and (pathcond-rewindable bfr-mode new old)
                  (equal (pathcond-checkpoint bfr-mode old) chp))
             (equal (pathcond-rewind chp bfr-mode new)
                    (pathcond-fix old)))))
  

