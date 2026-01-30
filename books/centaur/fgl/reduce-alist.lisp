; FGL - A Symbolic Simulation Framework for ACL2
;; SPDX-FileCopyrightText: Copyright 2025 Arm Limited and/or its affiliates <open-source-office@arm.com>
;; SPDX-License-Identifier: BSD-3-Clause
;; 
;; Redistribution and use in source and binary forms, with or without
;; modification, are permitted provided that the following conditions are
;; met:

;; o Redistributions of source code must retain the above copyright
;;   notice, this list of conditions and the following disclaimer.

;; o Redistributions in binary form must reproduce the above copyright
;;   notice, this list of conditions and the following disclaimer in the
;;   documentation and/or other materials provided with the distribution.

;; o Neither the name of the copyright holder nor the names of
;;   its contributors may be used to endorse or promote products derived
;;   from this software without specific prior written permission.

;; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
;; "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
;; LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
;; A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
;; HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
;; SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
;; LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
;; DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
;; THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
;; (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
;; OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

;; Author: Sol Swords <sol.swords@arm.com>

(in-package "FGL")

(include-book "def-fgl-rewrite")
(include-book "checks")
(include-book "std/alists/alist-equiv" :dir :system)
(include-book "fgl-object")
(local (include-book "std/alists/hons-assoc-equal" :dir :system))
(local (include-book "std/alists/fal-extract" :dir :system))
(local (xdoc::set-default-parents fgl-syntactic-checker-binders))


(define reduce-alist (ans x)
  :short "FGL binder that reduces the alist @('x') to an equivalent one possibly with fewer keys."
  :long "<p>This removes pairs that are syntactically known to be shadowed. That is, if
x is (syntactically) a list structure containing multiple pairs
with (syntactically) the same car, then this binder will produce a smaller list
structure where only the first of those pairs is kept.</p>

<p>The implementation of this binder, @('reduce-alist-binder'), is a
potentially slow rewrite rule; it could be sped up by making it a meta rule
that uses a fast alist to track seen keys.</p>"
  (if (acl2::alist-equiv ans x)
      ans
    x)
  ///
  (defthm reduce-alist-under-alist-equiv
    (acl2::alist-equiv (reduce-alist ans x)
                       x)))

(define reduce-alist-rec (ans x keys)
  (if (acl2::alist-equiv (append (acl2::fal-extract keys x) ans) x)
      ;; ans is equivalent to x, except on keys, where it doesn't matter
      ans
    x)
  ///
  (defthm lookup-of-reduce-alist-rec
    (implies (not (member-equal k keys))
             (equal (hons-assoc-equal k (reduce-alist-rec ans x keys))
                    (hons-assoc-equal k x)))
    :hints (("goal" :use ((:instance acl2::alist-equiv-implies-equal-hons-assoc-equal-2
                           (x k)
                           (a (append (acl2::fal-extract keys x) ans))
                           (a-equiv x)))
             :in-theory (disable acl2::alist-equiv-implies-equal-hons-assoc-equal-2)))))

(local (defthm fal-extract-when-not-consp
         (implies (not (consp x))
                  (equal (acl2::fal-extract keys x) nil))
         :hints(("Goal" :in-theory (enable acl2::fal-extract)))))

(local (defthm alist-equiv-nil-when-not-consp
         (implies (not (consp x))
                  (equal (acl2::alist-equiv nil x) t))
         :hints(("Goal" :in-theory (enable acl2::alist-equiv-when-agree-on-bad-guy)))))


(local (defthm fal-extract-cdr-when-not-consp-car
         (implies (and (consp x)
                       (not (consp (car x))))
                  (equal (acl2::fal-extract keys (cdr x))
                         (acl2::fal-extract keys x)))
         :hints(("Goal" :in-theory (enable acl2::fal-extract)))))

(local (defthm alist-equiv-cdr-when-not-consp-car
         (implies (and (consp x)
                       (not (consp (car X))))
                  (acl2::alist-equiv (cdr x) x))
         :hints(("Goal" :in-theory (enable acl2::alist-equiv-when-agree-on-bad-guy)))))

(local (defthm alist-equiv-append-extract-identity
         (acl2::alist-equiv (append (acl2::fal-extract keys x) x)
                            x)
         :hints(("Goal" :in-theory (enable acl2::alist-equiv-when-agree-on-bad-guy)))))


(local
 #!acl2
 (defthmd alist-equiv-iff-agree-on-bad-guy-rw
   (implies (acl2::rewriting-positive-literal `(alist-equiv ,al1 ,al2))
            (iff (alist-equiv al1 al2)
                 (let ((bg (alist-equiv-bad-guy al1 al2)))
                   (equal (hons-assoc-equal bg al1)
                          (hons-assoc-equal bg al2)))))
    :hints (("goal" :in-theory (e/d (alist-equiv-iff-agree-on-bad-guy))))))

(local (defun find-negated-alist-equiv (clause)
         (if (atom clause)
             nil
           (let ((lit (car clause)))
             (case-match lit
               (('not ('acl2::alist-equiv . &)) (cadr lit))
               (& (find-negated-alist-equiv (cdr clause))))))))


(def-fgl-brewrite reduce-alist-rec-binder
  (implies (equal ans (if (check-consp is-consp x)
                          (cond ((check-non-consp atom-car (car x))
                                 (reduce-alist-rec ans1 (cdr x) keys))
                                ((not (check-consp consp-car (car x)))
                                 (cons (car x)
                                       (reduce-alist-rec ans4 (cdr x) keys)))
                                ((check-memberp memp (caar x) keys)
                                 (reduce-alist-rec ans2 (cdr x) keys))
                                (t
                                 (cons (car x)
                                       (reduce-alist-rec
                                        ans3 (cdr x) (cons (caar x) keys)))))
                        x))
           (equal (reduce-alist-rec ans x keys)
                  ans))
  :hints(("Goal" :in-theory (enable reduce-alist-rec
                                    check-consp check-non-consp check-memberp)
          :do-not-induct t)
         (and stable-under-simplificationp
              (b* ((pos (assoc 'acl2::alist-equiv clause))
                   (neg (find-negated-alist-equiv clause))
                   (badguy `(acl2::alist-equiv-bad-guy . ,(cdr pos))))
                `(:in-theory (e/d (acl2::alist-equiv-iff-agree-on-bad-guy-rw)
                                  (acl2::alist-equiv-implies-equal-hons-assoc-equal-2))
                     :use ((:instance acl2::alist-equiv-implies-equal-hons-assoc-equal-2
                            (x ,badguy)
                            (a ,(cadr neg))
                            (a-equiv ,(caddr neg)))))))))

(local (in-theory (disable fast-alist-clean)))

(local (include-book "std/alists/fast-alist-clean" :dir :system))
(local (defthm fast-alist-clean-under-alist-equiv
         (acl2::alist-equiv (fast-alist-clean x) x)
         :hints(("Goal" :in-theory (enable acl2::alist-equiv-when-agree-on-bad-guy)))))

(def-fgl-brewrite reduce-alist-binder
  (implies (equal ans (cond ((syntax-bind cleanp
                                          (and (fgl-object-case x '(:g-map :g-concrete)) t))
                             (fast-alist-clean x))
                            (t (reduce-alist-rec ans1 x nil))))
           (equal (reduce-alist ans x)
                  ans))
  :hints(("Goal" :in-theory (enable reduce-alist-rec
                                    reduce-alist))))


