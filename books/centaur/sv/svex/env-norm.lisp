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

(include-book "centaur/misc/alist-canonicalize" :dir :system)
(include-book "alist-equiv")
(local (std::add-default-post-define-hook :fix))

(define svex-env-remove-xes ((x svex-env-p))
  :returns (new-x svex-env-p)
  (if (atom x)
      nil
    (if (and (mbt (and (consp (car x)) (svar-p (caar x))))
             (not (4vec-equiv (cdar x) (4vec-x))))
        (cons (cons (caar x) (4vec-fix (cdar x)))
              (svex-env-remove-xes (cdr x)))
      (svex-env-remove-xes (cdr x))))
  ///
  (local (defret hons-assoc-equal-of-<fn>
           (implies (no-duplicatesp-equal (alist-keys (svex-env-fix x)))
                    (equal (hons-assoc-equal key new-x)
                           (let ((look (hons-assoc-equal key (svex-env-fix x))))
                             (and (not (equal (cdr look) (4vec-x)))
                                  look))))
           :hints(("Goal" :in-theory (enable svex-env-fix alist-keys)))))

  (defret svex-env-lookup-of-<fn>
    (implies (no-duplicatesp-equal (alist-keys (svex-env-fix x)))
             (equal (svex-env-lookup key new-x)
                    (svex-env-lookup key x)))
    :hints(("Goal" :in-theory (enable svex-env-lookup svex-env-fix alist-keys))))

  (defret <fn>-under-svex-envs-similar
    (implies (no-duplicatesp-equal (alist-keys (svex-env-fix x)))
             (svex-envs-similar new-x x))
    :hints(("Goal" :in-theory (e/d (svex-envs-similar)
                                   (<fn>)))))

  (defret no-duplicate-keys-of-<fn>
    (implies (no-duplicatesp-equal (alist-keys (svex-env-fix x)))
             (no-duplicatesp-equal (alist-keys new-x)))
    :hints(("Goal" :in-theory (enable alist-keys svex-env-fix))))

  (local (defret not-svex-env-remove-xes-when-not-svex-env-fix
           (implies (not (svex-env-fix x))
                    (not new-x))
           :hints(("Goal" :in-theory (enable svex-env-fix)))))

  (local (defret car-<<-of-svex-env-remove-xes
           (implies (and (set::setp (svex-env-fix x))
                         (consp new-x))
                    (not (<< (car new-x) (car (svex-env-fix x)))))
           :hints(("Goal" :in-theory (enable svex-env-fix set::setp
                                             acl2::<<-transitive
                                             acl2::<<-irreflexive)))))

  (local (defthm <<-transitive-strong
           (implies (and (<< x y)
                         (not (<< z y)))
                    (<< x z))
           :hints (("goal" :use ((:instance acl2::<<-transitive)
                                 (:instance acl2::<<-trichotomy (x z)))))))

  (defret setp-of-<fn>
    (implies (set::setp (svex-env-fix x))
             (set::setp new-x))
    :hints(("Goal" :in-theory (enable svex-env-fix set::setp)
            :induct t)
           (and stable-under-simplificationp
                '(:use ((:instance car-<<-of-svex-env-remove-xes
                         (x (cdr x))))
                  :in-theory (disable car-<<-of-svex-env-remove-xes)))))

  (defthm svex-env-remove-xes-idempotent
    (equal (svex-env-remove-xes (svex-env-remove-xes x))
           (svex-env-remove-xes x)))

  (defretd hons-assoc-equal-non-x-of-<fn>
    (implies (hons-assoc-equal k new-x)
             (not (equal (4vec-fix (cdr (hons-assoc-equal k new-x))) (4vec-x)))))

  (local (in-theory (enable svex-env-fix))))


(defthm svex-env-p-of-alist-canonicalize
  (implies (svex-env-p x)
           (svex-env-p (acl2::alist-canonicalize x)))
  :hints (("goal" :use ((:functional-instance acl2::keyval-alist-p-of-alist-canonicalize
                         (acl2::keytype-p svar-p)
                         (acl2::keytype-example (lambda () 'x))
                         (acl2::valtype-p 4vec-p)
                         (acl2::valtype-example (lambda () (4vec-x)))
                         (acl2::keyval-alist-final-cdr-p (lambda (x) (eq x nil)))
                         (acl2::keyval-alist-p svex-env-p))))))


(local (defthm alistp-when-svex-env-p-rw
         (implies (svex-env-p x)
                  (alistp x))
         :hints(("Goal" :in-theory (enable svex-env-p)))))


(define svex-env-norm ((x svex-env-p))
  :returns (new-x svex-env-p)
  (svex-env-remove-xes (acl2::alist-canonicalize (svex-env-fix x)))
  ///
  (defthm svex-env-norm-idempotent
    (equal (svex-env-norm (svex-env-norm x))
           (svex-env-norm x))
    :hints(("Goal" :in-theory (enable acl2::canonical-alist-p-redef))))

  (defret canonical-alist-p-of-<fn>
    (acl2::canonical-alist-p new-x)
    :hints(("Goal" :in-theory (enable acl2::canonical-alist-p-redef))))

  (defret svex-env-lookup-of-<fn>
    (equal (svex-env-lookup k new-x)
           (svex-env-lookup k x))
    :hints((and stable-under-simplificationp
                '(:in-theory (enable svex-env-lookup)))))

  (defret <fn>-under-svex-envs-similar
    (svex-envs-similar new-x x)
    :hints(("Goal" :in-theory (e/d (svex-envs-similar) (<fn>)))))

  (defretd hons-assoc-equal-non-x-of-<fn>
    (implies (hons-assoc-equal k new-x)
             (not (equal (4vec-fix (cdr (hons-assoc-equal k new-x))) (4vec-x))))
    :hints(("Goal" :use ((:instance hons-assoc-equal-non-x-of-svex-env-remove-xes
                          (x (acl2::alist-canonicalize (svex-env-fix x)))))))))

(define svex-env-normedp ((x svex-env-p))
  (equal (svex-env-fix x) (svex-env-norm x))
  ///
  (defthm svex-env-normedp-of-svex-env-norm
    (svex-env-normedp (svex-env-norm x)))
  
  (defthm svex-env-norm-when-svex-env-normedp
    (implies (svex-env-normedp x)
             (equal (svex-env-norm x)
                    (svex-env-fix x))))

  ;; (defthmd svex-env-p-when-svex-env-normedp
  ;;   (implies (svex-env-normedp x)
  ;;            (svex-env-p x)))

  (defthmd canonical-alist-p-when-svex-env-normedp
    (implies (and (svex-env-normedp x)
                  (svex-env-p x))
             (acl2::canonical-alist-p x)))

  (defthmd hons-assoc-equal-non-x-when-svex-env-normed
    (implies (and (svex-env-normedp x)
                  (svar-p k)
                  (hons-assoc-equal k x))
             (not (equal (4vec-fix (cdr (hons-assoc-equal k x))) (4vec-x))))
    :hints(("Goal" :use ((:instance hons-assoc-equal-non-x-of-svex-env-norm
                          (x (svex-env-fix x))))
            :do-not-induct t))
    :otf-flg t))

(define svex-env-normedp-key-diff ((x svex-env-p)
                                   (y svex-env-p))
  :guard (and (svex-env-normedp x)
              (svex-env-normedp y)
              (not (equal x y)))
  :guard-hints (("goal" :in-theory (enable canonical-alist-p-when-svex-env-normedp)))
  :returns (key)
  (acl2::canonical-alist-key-diff (svex-env-fix x) (svex-env-fix y))
  ///
  (Std::defretd lookup-of-<fn>
    (implies (and (svex-env-normedp x)
                  (svex-env-normedp y)
                  (not (equal (svex-env-fix x) (svex-env-fix y))))
             (not (equal (svex-env-lookup key x) (svex-env-lookup key y))))
    :hints(("Goal" :in-theory (enable canonical-alist-p-when-svex-env-normedp
                                      svex-env-lookup
                                      hons-assoc-equal-non-x-when-svex-env-normed)
            :use ((:instance acl2::lookup-of-canonical-alist-key-diff
                   (x (svex-env-fix x))
                   (y (svex-env-fix y))))
            :do-not-induct t))
    :otf-flg t))


