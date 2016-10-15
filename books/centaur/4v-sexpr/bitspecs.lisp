; S-Expressions for 4-Valued Logic
; Copyright (C) 2010-2012 Centaur Technology
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
; Original authors: Sol Swords <sswords@centtech.com>
;                   Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "4v-logic")
(include-book "sexpr-equivs")
(include-book "centaur/misc/vecs-ints" :dir :system)
(include-book "centaur/misc/hons-sets" :dir :system)
(include-book "centaur/misc/fast-alists" :dir :system)
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "ihs/logops-lemmas" :dir :system))
(local (include-book "data-structures/no-duplicates" :dir :system))

(defun 4v-val-alistp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (equal x nil)
    (and (consp (car x))
         (atom (caar x))
         (4vp (cdar x))
         (4v-val-alistp (cdr x)))))

(defun 4v-bitspec-entryp (x)
  (and (consp x)
       (consp (cdr x))
       (equal (cddr x) nil)
       (case (car x)
         ((:natural :integer)
          (atom-listp (cadr x)))
         ((:4v :boolean) (atom (caadr x)))
         (:fixed (4v-val-alistp (cadr x))))))


(defun 4v-bitspecp (spec)
  (if (atom spec)
      (equal spec nil)
    (and (4v-bitspec-entryp (car spec))
         (4v-bitspecp (cdr spec)))))

(defun 4v-bitspec-entry-vars (x)
  (case (car x)
    ((:natural :integer) (cadr x))
    ((:4v :boolean) (list (cadr x)))
    (:fixed (alist-keys (cadr x)))))

(defun 4v-bitspec-vars (spec)
  (if (atom spec)
      nil
    (append
     (4v-bitspec-entry-vars (car spec))
     (4v-bitspec-vars (cdr spec)))))

(defun 4v-lookup-list (keys al)
  (declare (xargs :guard t))
  (if (atom keys)
      nil
    (cons (4v-lookup (car keys) al)
          (4v-lookup-list (cdr keys) al))))

(defun 4v-alist-for-bitspec-entryp (x alist)
  (case (car x)
    ((:natural :integer)
     (4v-bool-listp (4v-lookup-list (cadr x) alist)))
    (:4v t)
    (:boolean
     (4v-boolp (4v-lookup (cadr x) alist)))
    (:fixed (b* ((al (make-fal (cadr x) nil))
                 (ans (4v-alists-agree
                       (alist-keys (cadr x))
                       al alist))
                 (- (flush-hons-get-hash-table-link al)))
              ans))))

(defun 4v-alist-for-bitspecp (spec alist)
  (or (atom spec)
      (and (4v-alist-for-bitspec-entryp (car spec) alist)
           (4v-alist-for-bitspecp (cdr spec) alist))))




(defun 4v-alist-for-bitspec-entryp-verbose (x alist)
  (case
    (car x)
    ((:natural :integer)
     (or (4v-bool-listp (4v-lookup-list (cadr x) alist))
         (cw "~x0 keys are not all Boolean or are not all bound: ~x1~%"
             (car x) (cadr x))))
    (:4v t)
    (:boolean
     (or (4v-boolp (4v-lookup (cadr x) alist))
         (cw ":BOOLEAN key is not Boolean or is unbound: ~x0~%" (cadr x))))
    (:fixed
     (or (b* ((al (make-fal (cadr x) nil))
              (ans (4v-alists-agree
                    (alist-keys (cadr x))
                    al alist))
              (- (flush-hons-get-hash-table-link al)))
           ans)
         (cw ":FIXED entry does not agree with alist: ~x0~%" (cadr x))))))


(defun 4v-alist-for-bitspecp-verbose (spec alist)
  (or
   (atom spec)
   (and
    (4v-alist-for-bitspec-entryp-verbose (car spec) alist)
    (4v-alist-for-bitspecp-verbose (cdr spec) alist))))


(defun param-for-4v-bitspec-entryp (x param)
  (case (car x)
    ((:natural)
     (and (integerp param)
          (<= 0 param)
          (< param (expt 2 (len (cadr x))))))
    ((:integer)
     (and (integerp param)
          (<= (- (expt 2 (1- (len (cadr x))))) param)
          (< param (expt 2 (1- (len (cadr x)))))))
    ((:4v) (4vp param))
    ((:boolean) (booleanp param))
    ((:fixed) (equal param :fixed-ok))))


(defun params-for-4v-bitspecp (spec params)
  (if (atom spec)
      (equal params nil)
    (and (consp params)
         (param-for-4v-bitspec-entryp (car spec) (car params))
         (params-for-4v-bitspecp (cdr spec) (cdr params)))))

(defun 4v-to-nat (a)
  (declare (xargs :guard t))
  (if (atom a)
      0
    (let ((rest (4v-to-nat (cdr a))))
      (if (integerp rest)
          (case (car a)
            ((t) (+ 1 (* 2 rest)))
            ((f) (* 2 rest))
            (t 'x))
        rest))))

(defun 4v-to-int (a)
  (declare (xargs :guard t))
  (if (atom a)
      0
    (if (atom (cdr a))
        (case (car a)
          ((t) -1)
          ((f) 0)
          (t 'x))
      (let ((rest (4v-to-int (cdr a))))
        (if (integerp rest)
            (case (car a)
              ((t) (+ 1 (* 2 rest)))
              ((f) (* 2 rest))
              (t 'x))
          rest)))))






(defun 4v-alist-to-param (spec alist)
  (case (car spec)
    (:natural (let* ((bits (4v-to-nat (4v-lookup-list (cadr spec) alist)))
                     (n bits))
                (if (natp n) n 'x)))
    (:integer (let* ((bits (4v-to-int (4v-lookup-list (cadr spec) alist)))
                     (n bits))
                (if (integerp n) n 'x)))
    (:4v (4v-lookup (cadr spec) alist))
    (:boolean (case (4v-lookup (cadr spec) alist)
                ((t) t)
                ((f) nil)
                (t 'x)))
    (:fixed (if (b* ((al (make-fal (cadr spec) nil))
                     (ans (4v-alists-agree (alist-keys (cadr spec))
                                           al alist)))
                  (fast-alist-free al)
                  ans)
                :fixed-ok
              :fixed-bad))))

(defun 4v-from-bool (x)
  (declare (xargs :guard t))
  (if x 't 'f))

(defun 4v-from-bool-list (x)
  (declare (xargs :guard t))
  (if (atom x)
      nil
    (cons (4v-from-bool (car x))
          (4v-from-bool-list (cdr x)))))



(defun param-to-4v-alist (x param)
  (case (car x)
    ((:integer :natural)
     (pairlis$ (cadr x)
               (4v-from-bool-list (nat-to-v param (len (cadr x))))))
    (:4v (list (cons (cadr x) param)))
    (:boolean (list (cons (cadr x) (4v-from-bool param))))
    (:fixed (cadr x))))

(defun params-to-4v-alist (spec params)
  (if (atom spec)
      nil
    (append (param-to-4v-alist (car spec) (car params))
            (params-to-4v-alist (cdr spec) (cdr params)))))


(defun 4v-alist-to-params (spec alist)
  (if (atom spec)
      nil
    (cons (4v-alist-to-param (car spec) alist)
          (4v-alist-to-params (cdr spec) alist))))



(defun 4v-list-fix (x)
  (declare (xargs :guard t))
  (if (atom x)
      nil
    (cons (4v-fix (car x))
          (4v-list-fix (cdr x)))))

(defthm 4v-lookup-list-cons-non-val
  (implies (not (member-equal k keys))
           (equal (4v-lookup-list keys (cons (cons k v) rst))
                  (4v-lookup-list keys rst))))

(defthm 4v-lookup-list-pairlis$
  (implies (and (no-duplicatesp-equal lst)
                (equal (len lst) (len vals)))
           (equal (4v-lookup-list lst (pairlis$ lst vals))
                  (4v-list-fix vals)))
  :hints(("Goal" :in-theory (e/d (pairlis$) (4v-fix)))))

(defthm len-4v-from-bool-list
  (equal (len (4v-from-bool-list x))
         (len x)))

(defthm consp-4v-list-fix
  (equal (consp (4v-list-fix x))
         (consp x)))

(defthm consp-4v-from-bool-list
  (equal (consp (4v-from-bool-list x))
         (consp x)))

(defthm 4v-to-int-4v-list-fix
  (equal (4v-to-int (4v-list-fix x))
         (4v-to-int x)))

(defthm 4v-to-nat-4v-list-fix
  (equal (4v-to-nat (4v-list-fix x))
         (4v-to-nat x)))


(defun bool-from-4v (x)
  (declare (xargs :guard t))
  (if (eq x t) t nil))

(defun bool-from-4v-list (x)
  (declare (xargs :guard t))
  (if (atom x)
      nil
    (cons (bool-from-4v (car x))
          (bool-from-4v-list (cdr x)))))

(defthm boolean-listp-bool-from-4v-list
  (boolean-listp (bool-from-4v-list x)))

(defthm len-bool-from-4v-list
  (equal (len (bool-from-4v-list x))
         (len x)))

(defthm len-4v-lookup-list
  (equal (len (4v-lookup-list keys al))
         (len keys)))

(defthm bool-from-4v-4v-from-bool
  (implies (booleanp x)
           (equal (bool-from-4v (4v-from-bool x))
                  x)))

(defthm bool-from-4v-list-4v-from-bool-list
  (implies (boolean-listp x)
           (equal (bool-from-4v-list (4v-from-bool-list x))
                  x)))

(defthm 4v-to-nat-to-v-to-nat
  (implies (4v-bool-listp x)
           (equal (4v-to-nat x)
                  (v-to-nat (bool-from-4v-list x))))
  :hints(("Goal" :in-theory (enable 4v-boolp))))

(defthm 4v-to-int-to-v-to-int
  (implies (4v-bool-listp x)
           (equal (4v-to-int x)
                  (v-to-int (bool-from-4v-list x))))
  :hints(("Goal" :in-theory (enable 4v-boolp))))


(defthm 4v-bool-listp-4v-from-bool-list
  (4v-bool-listp (4v-from-bool-list x)))

(defthm 4v-from-bool-list-bool-from-4v-list
  (implies (4v-bool-listp x)
           (equal (4v-from-bool-list (bool-from-4v-list x))
                  x))
  :hints(("Goal" :in-theory (enable 4v-boolp))))


(defthm 4v-alist-to-param-param-to-4v-alist
  (implies (and (4v-bitspec-entryp x)
                (not (hons-dups-p (4v-bitspec-entry-vars x)))
                (param-for-4v-bitspec-entryp x param))
           (equal (4v-alist-to-param x (param-to-4v-alist x param))
                  param))
  :hints (("goal" :do-not-induct t))
  :otf-flg t)

(defthm alist-keys-pairlis$
  (implies (equal (len a) (len b))
           (equal (alist-keys (pairlis$ a b))
                  (append a nil))))

(defthm alist-keys-param-to-4v-alist
  (equal (alist-keys (param-to-4v-alist x param))
         (append (4v-bitspec-entry-vars x) nil)))

(defthm 4v-lookup-list-append-when-first-covers-vars
  (implies (subsetp-equal keys (alist-keys a))
           (equal (4v-lookup-list keys (append a b))
                  (4v-lookup-list keys a)))
  :hints(("Goal" :in-theory (enable subsetp-equal))))


(defthmd 4v-lookup-list-when-4v-alists-agree
  (implies (4v-alists-agree vars al1 al2)
           (equal (4v-lookup-list vars al1)
                  (4v-lookup-list vars al2))))

(defthmd 4v-alist-to-param-when-4v-alists-agree
  (implies (4v-alists-agree (4v-bitspec-entry-vars x) al1 al2)
           (equal (4v-alist-to-param x al1)
                  (4v-alist-to-param x al2)))
  :hints (("goal" :in-theory (enable 4v-lookup-list-when-4v-alists-agree
                                     4v-alists-agree-transitive1
                                     4v-alists-agree-transitive2
                                     4v-alists-agree-commutes))))

(defthmd 4v-alist-to-param-when-4v-alists-agree-rw
  (implies (4v-alists-agree (4v-bitspec-entry-vars x) al1 al2)
           (equal (equal (4v-alist-to-param x al1)
                         (4v-alist-to-param x al2))
                  t))
  :hints (("goal" :in-theory (enable 4v-lookup-list-when-4v-alists-agree
                                     4v-alists-agree-transitive1
                                     4v-alists-agree-transitive2
                                     4v-alists-agree-commutes))))

(defthmd 4v-alist-to-params-when-4v-alists-agree
  (implies (4v-alists-agree (4v-bitspec-vars spec) al1 al2)
           (equal (4v-alist-to-params spec al1)
                  (4v-alist-to-params spec al2)))
  :hints(("Goal" :in-theory (e/d (4v-alist-to-param-when-4v-alists-agree)
                                 (4v-alist-to-param 4v-bitspec-entry-vars)))))

(defthmd 4v-alist-to-params-when-4v-alists-agree-rw
  (implies (4v-alists-agree (4v-bitspec-vars spec) al1 al2)
           (equal (equal (4v-alist-to-params spec al1)
                         (4v-alist-to-params spec al2))
                  t))
  :hints(("Goal" :in-theory (e/d (4v-alist-to-params-when-4v-alists-agree)
                                 (4v-alists-agree-to-4v-env-equiv)))))

(defthmd 4v-alist-for-bitspec-entryp-when-4v-alists-agree
  (implies (4v-alists-agree (4v-bitspec-entry-vars x) al1 al2)
           (iff (4v-alist-for-bitspec-entryp x al1)
                (4v-alist-for-bitspec-entryp x al2)))
  :hints (("goal" :in-theory (e/d (4v-lookup-list-when-4v-alists-agree
                                   4v-alists-agree-commutes
                                   4v-alists-agree-transitive1
                                   4v-alists-agree-transitive2)
                                  (4v-fix 4v-lookup)))))

(defthmd 4v-alist-for-bitspecp-when-4v-alists-agree
  (implies (4v-alists-agree (4v-bitspec-vars spec) al1 al2)
           (equal (4v-alist-for-bitspecp spec al1)
                  (4v-alist-for-bitspecp spec al2)))
  :hints(("Goal" :in-theory (e/d (4v-alist-for-bitspec-entryp-when-4v-alists-agree)
                                 (4v-alist-for-bitspec-entryp
                                  4v-bitspec-entry-vars)))))

(defthmd 4v-alist-for-bitspecp-when-4v-alists-agree-rw
  (implies (4v-alists-agree (4v-bitspec-vars spec) al1 al2)
           (equal (equal (4v-alist-for-bitspecp spec al1)
                         (4v-alist-for-bitspecp spec al2))
                  t))
  :hints(("Goal" :in-theory (e/d (4v-alist-for-bitspecp-when-4v-alists-agree)
                                 (4v-alists-agree-to-4v-env-equiv)))))



(defthm 4v-alists-agree-append-when-first-covers-vars
  (implies (subsetp-equal vars (alist-keys a))
           (4v-alists-agree vars (append a b) a))
  :hints (("goal" :in-theory (e/d (hons-assoc-equal-when-not-member-alist-keys
                                   hons-assoc-equal-iff-member-alist-keys)
                                  (alist-keys-member-hons-assoc-equal)))
          (witness :ruleset 4v-alists-agree-witnessing)
          (witness :ruleset set-reasoning-no-consp)))


(defthm 4v-alist-to-param-append-when-first-covers-vars
  (implies (subsetp-equal (4v-bitspec-entry-vars x)
                          (alist-keys a))
           (equal (4v-alist-to-param x (append a b))
                  (4v-alist-to-param x a)))
  :hints(("Goal" :in-theory (e/d (4v-alist-to-param-when-4v-alists-agree-rw)
                                 (4v-alist-to-param 4v-bitspec-entry-vars)))))

(defthm 4v-alist-to-params-append-when-first-covers-vars
  (implies (subsetp-equal (4v-bitspec-vars x)
                          (alist-keys a))
           (equal (4v-alist-to-params x (append a b))
                  (4v-alist-to-params x a)))
  :hints(("Goal" :in-theory (enable 4v-alist-to-params-when-4v-alists-agree-rw))))


(defthm 4v-alists-agree-append-when-first-does-not-intersect-vars
  (implies (not (intersectp-equal vars (alist-keys a)))
           (4v-alists-agree vars (append a b) b))
  :hints (("goal" :in-theory (e/d (hons-assoc-equal-when-not-member-alist-keys
                                   hons-assoc-equal-iff-member-alist-keys)
                                  (alist-keys-member-hons-assoc-equal)))
          (witness :ruleset 4v-alists-agree-witnessing)
          (witness :ruleset set-reasoning-no-consp)))

(defthm 4v-alist-to-param-append-when-first-does-not-intersect-vars
  (implies (not (intersectp-equal (4v-bitspec-entry-vars x)
                                  (alist-keys a)))
           (equal (4v-alist-to-param x (append a b))
                  (4v-alist-to-param x b)))
  :hints(("Goal" :in-theory (e/d (4v-alist-to-param-when-4v-alists-agree-rw)
                                 (4v-alist-to-param 4v-bitspec-entry-vars)))))


(defthm 4v-alist-to-params-append-when-first-does-not-intersect-vars
  (implies (not (intersectp-equal (4v-bitspec-vars spec)
                                  (alist-keys a)))
           (equal (4v-alist-to-params spec (append a b))
                  (4v-alist-to-params spec b)))
  :hints(("Goal" :in-theory (e/d (4v-alist-to-params-when-4v-alists-agree-rw)
                                 (4v-alist-to-params 4v-bitspec-vars)))))


(defthm 4v-alist-to-params-params-to-4v-alist
  (implies (and (4v-bitspecp spec)
                ;; The following could be relaxed by hypothesizing
                ;; more about the params, but it wouldn't be simple
                (not (hons-dups-p (4v-bitspec-vars spec)))
                (params-for-4v-bitspecp spec params))
           (equal (4v-alist-to-params spec (params-to-4v-alist spec params))
                  params))
  :hints (("goal" :induct t
           :in-theory (disable 4v-alist-to-param
                               hons-dups-p
                               param-to-4v-alist
                               4v-bitspec-entryp
                               4vp
                               param-for-4v-bitspec-entryp
                               4v-bitspec-entry-vars))))








(defthm 4v-alist-extract-append
  (equal (4v-alist-extract (append a b) al)
         (append (4v-alist-extract a al)
                 (4v-alist-extract b al))))


(defthm 4v-env-equiv-cons
  (implies (and (set-equiv (alist-keys a) (alist-keys b))
                (equal (4v-fix a) (4v-fix b))
                (4v-env-equiv c d))
           (equal (4v-env-equiv (cons (cons k a) c)
                                (cons (cons k b) d))
                  t))
  :hints(("Goal" :in-theory (disable 4v-fix
                                     4v-env-equiv-to-key-and-env-equiv))
         (witness :ruleset 4v-env-equiv-witnessing)))


(defthm 4v-alist-for-bitspec-entryp-when-fixed
  (implies (equal (car x) :fixed)
           (equal (4v-alist-for-bitspec-entryp x alist)
                  (4v-alists-agree (alist-keys (cadr x))
                                   (cadr x) alist))))

(defthm not-4v-env-equiv-cons
  (implies (not (equal (4v-fix x) (4v-fix y)))
           (not (4v-env-equiv
                 (cons (cons k x) rst1)
                 (cons (cons k y) rst2))))
  :hints(("Goal" :in-theory (disable 4v-fix)
          :use ((:instance 4v-env-equiv-necc
                           (key k)
                           (x (cons (cons k x) rst1))
                           (y (cons (cons k y) rst2)))))))





(defthm pairlis-4v-lookup-list-is-4v-alist-extract
  (equal (pairlis$ keys (4v-lookup-list keys x))
         (4v-alist-extract keys x)))

(defthm 4v-alist-extract-self
  (4v-env-equiv (4v-alist-extract (alist-keys x) x)
                x)
  :hints(("Goal" :in-theory (e/d () (4v-env-equiv-to-key-and-env-equiv)))
         (witness :ruleset 4v-env-equiv-witnessing)))

(defthm param-to-4v-alist-4v-alist-to-param
  (implies (and (4v-bitspec-entryp x)
                (not (hons-dups-p (4v-bitspec-entry-vars x)))
                (4v-alist-for-bitspec-entryp x alist))
           (key-and-env-equiv
            (param-to-4v-alist x (4v-alist-to-param x alist))
            (4v-alist-extract
             (4v-bitspec-entry-vars x) alist)))
  :hints(("Goal" :in-theory (e/d (4v-boolp
                                  key-and-env-equiv
                                  4v-alists-agree-to-4v-env-equiv)
                                 (4v-env-equiv-to-key-and-env-equiv
                                  4v-fix)))))

(defthm params-to-4v-alist-4v-alist-to-params
  (implies (and (4v-bitspecp spec)
                (not (hons-dups-p (4v-bitspec-vars spec)))
                (4v-alist-for-bitspecp spec alist))
           (key-and-env-equiv
            (params-to-4v-alist spec (4v-alist-to-params spec alist))
            (4v-alist-extract
             (4v-bitspec-vars spec) alist)))

  :hints (("goal" :induct t
           :in-theory (e/d (key-and-env-equiv
                            4v-alists-agree-to-4v-env-equiv)
                           (4v-alist-to-param
                            hons-dups-p
                            param-to-4v-alist
                            4v-alist-for-bitspec-entryp
                            4v-bitspec-entryp
                            4v-env-equiv-to-key-and-env-equiv
                            4vp
                            param-for-4v-bitspec-entryp
                            4v-bitspec-entry-vars)))))




(defthm 4vp-4v-fix
  (4vp (4v-fix x)))

(defthm param-for-4v-bitspec-entryp-4v-alist-to-param
  (implies (and (4v-bitspec-entryp x)
                (4v-alist-for-bitspec-entryp x alist))
           (param-for-4v-bitspec-entryp
            x (4v-alist-to-param x alist)))
  :hints(("Goal" :in-theory (e/d (4v-boolp) (4v-fix 4vp)))))


(defthm params-for-4v-bitspecp-4v-alist-to-params
  (implies (and (4v-bitspecp spec)
                (4v-alist-for-bitspecp spec alist))
           (params-for-4v-bitspecp
            spec (4v-alist-to-params spec alist)))
  :hints(("Goal" :in-theory (disable 4v-bitspec-entryp
                                     4v-alist-for-bitspec-entryp
                                     param-for-4v-bitspec-entryp
                                     4v-alist-to-param))))






(defthm 4v-list-fix-4v-from-bool-list
  (equal (4v-list-fix (4v-from-bool-list x))
         (4v-from-bool-list x)))

(defthm 4v-alist-for-bitspec-entryp-param-to-4v-alist
  (implies (and (4v-bitspec-entryp x)
                (not (hons-dups-p (4v-bitspec-entry-vars x)))
                (param-for-4v-bitspec-entryp x param))
           (4v-alist-for-bitspec-entryp
            x (param-to-4v-alist x param)))
  :hints(("Goal" :in-theory (e/d (4v-alists-agree-to-4v-env-equiv)
                                 (4v-fix 4vp)))))








(defthm len-4v-alist-to-params
  (equal (len (4v-alist-to-params spec alist))
         (len spec)))

;; (defthm 4v-bitspec-param-len-append
;;   (equal (4v-bitspec-param-len (append a b))
;;          (+ (4v-bitspec-param-len a)
;;             (4v-bitspec-param-len b))))


(defthm 4v-bitspecp-append
  (implies (and (4v-bitspecp a)
                (4v-bitspecp b))
           (4v-bitspecp (append a b))))

(defcong 4v-env-equiv equal (4v-alist-extract keys al) 2
  :hints (("goal" :induct t :in-theory (disable 4v-lookup))
          (witness :ruleset 4v-env-equiv-4v-lookup-ex)))

(defthm 4v-alist-for-bitspecp-append
  (implies (and (4v-alist-for-bitspecp a al)
                (4v-alist-for-bitspecp b al))
           (4v-alist-for-bitspecp (append a b) al))
  :hints(("Goal" :in-theory (disable 4v-env-equiv-to-key-and-env-equiv))))


(defthm 4v-alist-to-params-append
  (equal (4v-alist-to-params (append a b) al)
         (append (4v-alist-to-params a al)
                 (4v-alist-to-params b al))))



(defthmd len-when-params-for-4v-bitspecp
  (implies (params-for-4v-bitspecp spec params)
           (equal (equal (len params)
                         (len spec))
                  t)))


(local (Defthm len-0-means-atom
         (equal (equal (len x) 0)
                (atom x))))

(defthm params-to-4v-alist-append
  (implies (and (equal (len pa) (len a))
                (equal (len pb) (len b)))
           (equal (params-to-4v-alist (append a b) (append pa pb))
                  (append (params-to-4v-alist a pa)
                          (params-to-4v-alist b pb))))
  :hints(("Goal" :in-theory (disable param-to-4v-alist))))



(defthm alist-keys-params-to-4v-alist
  (equal (alist-keys (params-to-4v-alist spec param))
         (append (4v-bitspec-vars spec) nil)))



(defthm  4v-alists-agree-append-when-vars-not-intersecting
  (implies (not (intersectp-equal (alist-keys b) keys))
           (iff (4v-alists-agree keys a (append b c))
                (4v-alists-agree keys a c)))
  :hints(("Goal" :in-theory (e/d* (4v-alists-agree)
                                  ((:rules-of-class :type-prescription :here)
                                   set::double-containment
                                   4v-alists-agree-to-4v-env-equiv
                                   append 4v-fix)))))


(defthm  4v-alists-agree-append-when-vars-subset
  (implies (subsetp-equal keys (alist-keys b))
           (iff (4v-alists-agree keys a (append b c))
                (4v-alists-agree keys a b)))
  :hints(("Goal" :in-theory (e/d* (4v-alists-agree
                                   subsetp-equal)
                                  ((:rules-of-class :type-prescription :here)
                                   4v-alists-agree-to-4v-env-equiv
                                   set::double-containment
                                   append 4v-fix)))))


(defthm 4v-alist-for-bitspec-entryp-append-when-vars-subset
  (implies (subsetp-equal (4v-bitspec-entry-vars x)
                          (alist-keys a))
           (equal (4v-alist-for-bitspec-entryp x (append a b))
                  (4v-alist-for-bitspec-entryp x a)))
  :hints(("Goal" :in-theory (e/d (subsetp-equal) (append))))
  :otf-flg t)

(defthm 4v-alist-for-bitspec-entryp-append-when-vars-not-intersecting
  (implies (not (intersectp-equal (4v-bitspec-entry-vars x)
                                  (alist-keys a)))
           (equal (4v-alist-for-bitspec-entryp x (append a b))
                  (4v-alist-for-bitspec-entryp x b)))
  :hints(("Goal" :in-theory (disable append)))
  :otf-flg t)



(defcong 4v-env-equiv equal (4v-lookup-list keys al) 2
  :hints(("Goal" :in-theory (disable 4v-lookup))))

(defcong 4v-env-equiv equal (4v-alist-for-bitspec-entryp x al) 2
  :hints(("Goal" :in-theory (enable 4v-alists-agree-to-4v-env-equiv))))

(defcong 4v-env-equiv equal (4v-alist-for-bitspecp spec al) 2
  :hints (("goal" :induct (len spec))))

(defthmd 4v-alists-agree-when-4v-env-equiv
  (implies (4v-env-equiv a b)
           (4v-alists-agree vars a b)))

(defcong 4v-env-equiv equal (4v-alist-to-param x al) 2
  :hints(("Goal" :in-theory (e/d (4v-alist-to-param-when-4v-alists-agree-rw
                                  4v-alists-agree-when-4v-env-equiv)
                                 (4v-lookup 4v-alist-to-param)))))

(defcong 4v-env-equiv equal (4v-alist-to-params spec al) 2
  :hints(("Goal" :in-theory (e/d (4v-alist-to-params-when-4v-alists-agree-rw
                                  4v-alists-agree-when-4v-env-equiv)
                                 (4v-lookup 4v-alist-to-params)))))




(defthmd 4v-lookup-list-to-4v-alist-extract
  (equal (4v-lookup-list keys al)
         (alist-vals (4v-alist-extract keys al))))













(defthm 4v-alist-for-bitspecp-append-when-first-not-intersecting
  (implies (not (intersectp-equal (4v-bitspec-vars spec) (alist-keys a)))
           (equal (4v-alist-for-bitspecp spec (append a b))
                  (4v-alist-for-bitspecp spec b)))
  :hints (("goal" :in-theory (e/d (4v-alist-for-bitspecp-when-4v-alists-agree-rw)
                                  (4v-alists-agree-to-4v-env-equiv)))))



(defthm 4v-alist-for-bitspecp-params-to-4v-alist
  (implies (and (4v-bitspecp spec)
                (not (hons-dups-p (4v-bitspec-vars spec)))
                (params-for-4v-bitspecp spec param))
           (4v-alist-for-bitspecp
            spec (params-to-4v-alist spec param)))
  :hints(("Goal" :in-theory (disable 4v-bitspec-entry-vars
                                     param-for-4v-bitspec-entryp
                                     4v-alist-for-bitspec-entryp
                                     param-to-4v-alist))))




(defthmd alists-compatible-when-witness-fails
  (implies (let ((key (alists-incompatible-on-keys-witness
                           (alist-keys a) a b)))
             (not (and (hons-assoc-equal key a)
                       (hons-assoc-equal key b)
                       (not (equal (cdr (hons-assoc-equal key a))
                                   (cdr (hons-assoc-equal key b)))))))
           (alists-compatible a b))
  :hints(("Goal" :in-theory (enable alists-compatible
                                    alists-incompatible-on-keys-witness-correct))))

(defthmd alists-compatible-necc
  (implies (and (alists-compatible a b)
                (hons-assoc-equal key a)
                (hons-assoc-equal key b))
           (equal (equal (cdr (hons-assoc-equal key a))
                         (cdr (hons-assoc-equal key b)))
                  t))
  :hints(("Goal" :in-theory (enable alists-compatible-hons-assoc-equal))))



(defthm alist-keys-append
  (equal (alist-keys (append a b))
         (append (alist-keys a) (alist-keys b))))

(defthm alists-compatible-append
  (implies (no-duplicatesp-equal (alist-keys (append a b)))
           (iff (alists-compatible (append a b) c)
                (and (alists-compatible a c)
                     (alists-compatible b c))))
  :hints (("goal" :do-not-induct t
           :in-theory (e/d (alist-keys-append)
                           (alists-compatible no-duplicatesp-equal
                                              alist-keys append)))
          (witness :ruleset (alists-compatible-hons-assoc-equal-example
                             alists-compatible-witnessing))
          (and stable-under-simplificationp
               '(:in-theory (e/d (hons-assoc-equal-iff-member-alist-keys)
                                 (alist-keys-member-hons-assoc-equal))))
          (set-reasoning)))

(defthmd alists-compatible-when-not-intersecting-vars
  (implies (not (intersectp-equal (alist-keys a) (alist-keys b)))
           (alists-compatible a b))
  :hints (("goal" :do-not-induct t
           :in-theory (e/d (hons-assoc-equal-iff-member-alist-keys)
                           (alist-keys-member-hons-assoc-equal)))
          (witness :ruleset alists-compatible-witnessing)
          (set-reasoning)))

(local (progn
(defthm alists-compatible-append-inv
  (implies (no-duplicatesp-equal (alist-keys (append a b)))
           (iff (alists-compatible c (append a b))
                (and (alists-compatible c a)
                     (alists-compatible c b))))
  :hints (("goal" :do-not-induct t
           :in-theory (e/d (alist-keys-append)
                           (alists-compatible no-duplicatesp-equal
                                              alist-keys append)))
          (witness :ruleset (alists-compatible-hons-assoc-equal-example
                             alists-compatible-witnessing))
          (and stable-under-simplificationp
               '(:in-theory (e/d (hons-assoc-equal-iff-member-alist-keys)
                                 (alist-keys-member-hons-assoc-equal))))
          (set-reasoning)))




(defthm not-params-for-4v-bitspec-entryp-when-cons-wrong
  (implies (and (consp spec) (not (consp params))
                (not (equal (caar spec) :fixed)))
           (not (params-for-4v-bitspecp spec params))))

(defthm alists-compatible-a-append-a-b
  (alists-compatible a (append a b))
  :hints (("goal" :do-not-induct t)
          (witness :ruleset alists-compatible-witnessing)))

(defthm not-alists-compatible-cons-diff
  (implies (not (equal v1 v2))
           (not (alists-compatible (cons (cons x v1) rest1)
                                   (cons (cons x v2) rest2))))
  :hints(("Goal" :in-theory (enable alists-compatible))))

(defthm not-alists-compatible-cons-same
  (implies (and (not (alists-compatible rest1 rest2))
                (not (member-equal k (alist-keys rest1)))
                (not (member-equal k (alist-keys rest2))))
           (not (alists-compatible (cons (cons k v) rest1)
                                   (cons (cons k v) rest2))))
  :hints (("goal" :do-not-induct t)
          (witness :ruleset (alists-compatible-witnessing
                             alists-compatible-hons-assoc-equal-example))))

(defthm not-alists-compatible-pairlis$-diff
  (implies (and (not (equal v1 v2))
                (true-listp v1)
                (true-listp v2)
                (no-duplicatesp-equal k)
                (equal (len v1) (len k))
                (equal (len v2) (len k)))
           (not (alists-compatible (pairlis$ k v1)
                                   (pairlis$ k v2))))
  :hints (("goal"
           :in-theory (enable pairlis$ alists-compatible)
           :induct t)
          (and stable-under-simplificationp
               '(:cases ((equal (car v1) (car v2)))))))

(defthm 4v-from-bool-lists-equal
  (implies (and (boolean-listp a)
                (boolean-listp b))
           (iff (equal (4v-from-bool-list a) (4v-from-bool-list b))
                (equal a b)))
  :hints (("goal"
           :in-theory (enable pairlis$)
           :induct (pairlis$ a b))))


(defthm not-equal-int-to-v
  (implies (and (not (equal a b))
                (integerp a)
                (integerp b)
                (<= 0 a)
                (<= 0 b)
                (natp n)
                (< a (expt 2 n))
                (< b (expt 2 n)))
           (iff (equal (int-to-v a n) (int-to-v b n))
                (equal a b)))
  :hints(("Goal" :in-theory (e/d (ash* logbitp*)
                                 (ash logbitp logcar logcdr)))))

(defthm n-when-between-expts
  (implies (and (integerp n)
                (integerp a)
                (< n 0)
                (<= (- (expt 2 n)) a)
                (< a (expt 2 n)))
           (equal a 0))
  :rule-classes nil)

(encapsulate
  nil
  (local (defthm expt-2-is-ash
           (implies (natp n)
                    (equal (expt 2 n) (ash 1 n)))))

  (local (defthm not-equal-int-to-v-2-lemma
           (implies (and (not (equal a b))
                         (integerp a)
                         (integerp b)
                         (<= (- (ash 1 (1- n))) a)
                         (<= (- (ash 1 (1- n))) b)
                         (natp n)
                         (< a (ash 1 (1- n)))
                         (< b (ash 1 (1- n))))
                    (iff (equal (int-to-v a n) (int-to-v b n))
                         (equal a b)))
           :hints(("Goal" :in-theory (e/d (ash* logbitp*)
                                          (ash logbitp logcar logcdr))
                   :induct (equal (int-to-v a n) (int-to-v b n))))))


  (defthm not-equal-int-to-v-2
    (implies (and (not (equal a b))
                  (integerp a)
                  (integerp b)
                  (<= (- (expt 2 (1- n))) a)
                  (<= (- (expt 2 (1- n))) b)
                  (natp n)
                  (< a (expt 2 (1- n)))
                  (< b (expt 2 (1- n))))
             (iff (equal (int-to-v a n) (int-to-v b n))
                  (equal a b)))
    :hints(("Goal" :cases ((posp n))
            :in-theory (e/d ()
                            (not-equal-int-to-v-2-lemma
                             ash expt)))
           (and stable-under-simplificationp
                '(:use ((:instance not-equal-int-to-v-2-lemma)
                        (:instance n-when-between-expts
                                   (n (1- n)))
                        (:instance n-when-between-expts
                                   (n (1- n)) (a b))))))))))

(defthm not-alists-compatible-param-to-4v-alist-when-params-not-equal
  (implies (and (param-for-4v-bitspec-entryp x param1)
                (param-for-4v-bitspec-entryp x param2)
                (4v-bitspec-entryp x)
                (no-duplicatesp-equal (4v-bitspec-entry-vars x))
                (not (equal (car x) :fixed)))
           (iff (alists-compatible (param-to-4v-alist x param1)
                                   (param-to-4v-alist x param2))
                (equal param1 param2)))
  :hints(("Goal" :in-theory (disable expt ash))))



;; (local (progn
;;          (defthm alists-compatible-param-to-4v-alist-when-not-intersecting-vars
;;   (implies (not (intersectp-equal (4v-bitspec-entry-vars x)
;;                                   (4v-bitspec-vars spec)))
;;            (alists-compatible (param-to-4v-alist x p1)
;;                               (params-to-4v-alist spec p2)))
;;   :hints (("goal" :use ((:instance alists-compatible-when-not-intersecting-vars
;;                                    (a (param-to-4v-alist x p1))
;;                                    (b (params-to-4v-alist spec p2)))))))


;; (defthm alists-compatible-param-to-4v-alist-when-not-intersecting-vars-2
;;   (implies (not (intersectp-equal (4v-bitspec-entry-vars x)
;;                                   (4v-bitspec-entry-vars y)))
;;            (alists-compatible (param-to-4v-alist x p1)
;;                               (param-to-4v-alist y p2)))
;;   :hints (("goal" :use ((:instance alists-compatible-when-not-intersecting-vars
;;                                    (a (param-to-4v-alist x p1))
;;                                    (b (param-to-4v-alist y p2)))))))


(defthm len-member-equal-linear
  (<= (len (member-equal x a)) (len a))
  :rule-classes :linear)

;; (defthm 4v-bitspec-param-len-member-equal-linear
;;   (<= (4v-bitspec-param-len (member-equal x a)) (4v-bitspec-param-len a))
;;   :rule-classes :linear)

(defthm member-x-impl-vars-subset
  (implies (member-equal x spec)
           (subsetp-equal (4v-bitspec-entry-vars x)
                          (4v-bitspec-vars spec)))
  :hints(("Goal" :in-theory (disable 4v-bitspec-entry-vars))))

(defthmd not-intersecting-impl-not-intersecting-subset
  (implies (and (not (intersectp-equal a c))
                (subsetp-equal b c))
           (and (not (intersectp-equal a b))
                (not (intersectp-equal b a))))
  :hints ((set-reasoning)))

(defthmd not-intersecting-impl-not-intersecting-subset2
  (implies (and (not (intersectp-equal c a))
                (subsetp-equal b c))
           (and (not (intersectp-equal a b))
                (not (intersectp-equal b a))))
  :hints ((set-reasoning)))

(defthm not-intersecting-when-member-and-other-not-intersecting
  (implies (and (not (intersectp-equal (4v-bitspec-entry-vars y)
                                       (4v-bitspec-vars spec)))
                (member-equal x spec))
           (not (intersectp-equal (4v-bitspec-entry-vars x)
                                  (4v-bitspec-entry-vars y))))
  :hints(("Goal" :in-theory (e/d
                             (not-intersecting-impl-not-intersecting-subset)
                             (4v-bitspec-entry-vars)))))

(defthm two-members-not-equal-and-no-duplicates
  (implies (and (no-duplicatesp-equal (4v-bitspec-vars spec))
                (member-equal x spec)
                (member-equal y spec)
                (not (equal x y)))
           (not (intersectp-equal (4v-bitspec-entry-vars x)
                                  (4v-bitspec-entry-vars y))))
  :hints(("Goal" :in-theory (e/d
                             (not-intersecting-impl-not-intersecting-subset)
                             (4v-bitspec-entry-vars)))))

(defthm not-intersecting-car-spec-special
  (implies (and (member-equal x (cdr spec))
                (not (intersectp-equal (4v-bitspec-entry-vars (car spec))
                                       (4v-bitspec-vars (cdr spec)))))
           (not (intersectp-equal (4v-bitspec-entry-vars x)
                                  (4v-bitspec-entry-vars (car spec)))))
  :hints(("Goal" :in-theory (disable not-intersecting-when-member-and-other-not-intersecting
                                     4v-bitspec-entry-vars)
          :use ((:instance not-intersecting-when-member-and-other-not-intersecting
                           (x x) (y (car spec)) (spec (cdr spec)))))))


(local (defthm true-listp-and-subset-and-no-intersect-impl-nil
         (implies (and (true-listp x)
                       (subsetp-equal x y)
                       (not (intersectp-equal x y)))
                  (Equal x nil))
         :hints (("Goal" :in-theory (enable intersectp-equal))
                 (set-reasoning))
         :rule-classes nil))

(defthm true-listp-4v-bitspec-entry-vars
  (implies (4v-bitspec-entryp x)
           (true-listp (4v-bitspec-entry-vars x))))

(defthm member-and-not-intersecting-means-vars-nil
  (implies (and (member-equal x spec)
                (4v-bitspec-entryp x))
           (iff (intersectp-equal (4v-bitspec-entry-vars x)
                                       (4v-bitspec-vars spec))
                (not (equal (4v-bitspec-entry-vars x) nil))))
  :hints (("goal"
           :use ((:instance true-listp-and-subset-and-no-intersect-impl-nil
                            (x (4v-bitspec-entry-vars x))
                            (y (4v-bitspec-vars spec))))
           :in-theory (disable 4v-bitspec-entry-vars))))

(defthm param-for-4v-bitspec-entryp-when-no-vars
  (implies (and (4v-bitspec-entryp x)
                (not (equal (car x) :fixed))
                (not (4v-bitspec-entry-vars x)))
           (iff (param-for-4v-bitspec-entryp x p)
                (and (member (car x) '(:integer :natural))
                     (equal p 0)))))



(defthm natp-4v-to-nat
  (implies (true-listp lst)
           (iff (natp (4v-to-nat lst))
                (4v-bool-listp lst))))

(defthm integerp-4v-to-int
  (implies (true-listp lst)
           (iff (integerp (4v-to-int lst))
                (4v-bool-listp lst))))


(defthm param-for-4v-bitspec-entryp-4v-alist-to-param-iff
  (iff (param-for-4v-bitspec-entryp spec (4v-alist-to-param spec alist))
       (4v-alist-for-bitspec-entryp spec alist))
  :hints ((and stable-under-simplificationp
               '(:in-theory (enable 4v-boolp)))))

(defthm params-for-4v-bitspec-4v-alist-to-params-iff
  (iff (params-for-4v-bitspecp spec (4v-alist-to-params spec alist))
       (4v-alist-for-bitspecp spec alist))
  :hints(("Goal" :in-theory (disable param-for-4v-bitspec-entryp
                                     4v-alist-to-param))))







;; (defthm alists-compatible-param-to-4v-alist-when-member
;;   (implies (and (member-equal p1 spec2)
;;                 (no-duplicatesp-equal (4v-bitspec-vars spec2))
;;                 (not (equal (car p1) :fixed))
;;                 (4v-bitspecp spec2)
;;                 (4v-bitspec-entryp p1)
;;                 (params-for-4v-bitspecp spec2 params2)
;;                 (param-for-4v-bitspec-entryp p1 param))
;;            (iff (alists-compatible
;;                  (param-to-4v-alist p1 param)
;;                  (params-to-4v-alist spec2 params2))
;;                 (equal param (nth (- (4v-bitspec-param-len spec2)
;;                                      (4v-bitspec-param-len
;;                                       (member-equal p1 spec2)))
;;                                   params2))))
;;   :hints(("Goal" :in-theory (e/d (alist-keys-append
;;                                   alist-keys-pairlis$
;;                                   not-intersecting-impl-not-intersecting-subset2
;;                                   alists-compatible-when-not-intersecting-vars)
;;                                  (4v-bitspec-entry-vars
;;                                   param-to-4v-alist
;;                                   param-for-4v-bitspec-entryp
;;                                   4v-bitspec-entryp
;;                                   append))
;;           :induct (params-for-4v-bitspecp spec2 params2)
;;           ;; :expand ((params-for-4v-bitspecp spec2 params2)
;;           ;;          (params-to-4v-alist spec2 params2))
;;           :do-not-induct t)))



;; (defthm alists-compatible-params-to-4v-alist-when-member-1
;;   (implies (and (member-equal p1 spec2)
;;                 (not (hons-dups-p (4v-bitspec-vars (cons p1 rest1))))
;;                 (not (hons-dups-p (4v-bitspec-vars spec2)))
;;                 (not (equal (car p1) :fixed))
;;                 (4v-bitspecp spec2)
;;                 (4v-bitspec-entryp p1)
;;                 (4v-bitspecp rest1)
;;                 (consp params1)
;;                 (param-for-4v-bitspec-entryp p1 (car params1))
;;                 (params-for-4v-bitspecp rest1 (cdr params1))
;;                 (params-for-4v-bitspecp spec2 params2))
;;            (iff (alists-compatible
;;                  (params-to-4v-alist (cons p1 rest1) params1)
;;                  (params-to-4v-alist spec2 params2))
;;                 (and (equal (nth 0 params1)
;;                             (nth (- (4v-bitspec-param-len spec2)
;;                                     (4v-bitspec-param-len (member-equal p1 spec2)))
;;                                  params2))
;;                      (alists-compatible
;;                       (params-to-4v-alist rest1 (cdr params1))
;;                       (params-to-4v-alist spec2 params2)))))
;;   :hints(("Goal" :in-theory (e/d (alist-keys-append
;;                                   alist-keys-pairlis$)
;;                                  (4v-bitspec-entry-vars
;;                                   param-to-4v-alist
;;                                   4v-bitspec-entryp param-for-4v-bitspec-entryp))
;;           :do-not-induct t))
;;   :otf-flg t)



;; (defthm alists-compatible-params-to-4v-alist-when-member
;;   (implies (and (member-equal (car spec1) spec2)
;;                 (not (hons-dups-p (4v-bitspec-vars spec1)))
;;                 (not (hons-dups-p (4v-bitspec-vars spec2)))
;;                 (consp spec1)
;;                 (not (equal (caar spec1) :fixed))
;;                 (4v-bitspecp spec2)
;;                 (4v-bitspecp spec1)
;;                 (params-for-4v-bitspecp spec1 params1)
;;                 (params-for-4v-bitspecp spec2 params2))
;;            (iff (alists-compatible
;;                  (params-to-4v-alist spec1 params1)
;;                  (params-to-4v-alist spec2 params2))
;;                 (and (equal (nth 0 params1)
;;                             (nth (- (4v-bitspec-param-len spec2)
;;                                     (4v-bitspec-param-len (member-equal (car spec1)
;;                                                                         spec2)))
;;                                  params2))
;;                      (alists-compatible
;;                       (params-to-4v-alist (cdr spec1) (cdr params1))
;;                       (params-to-4v-alist spec2 params2)))))
;;   :hints(("Goal" :use ((:instance
;;                         alists-compatible-params-to-4v-alist-when-member-1
;;                         (p1 (car spec1))
;;                         (rest1 (cdr spec1))))
;;           :in-theory (disable alists-compatible-params-to-4v-alist-when-member-1
;;                               4v-bitspec-entry-vars 4v-bitspec-entryp
;;                               append nth
;;                               param-for-4v-bitspec-entryp
;;                               param-to-4v-alist)
;;           :do-not-induct t))
;;   :otf-flg t)


;; (defthm alists-compatible-params-to-4v-alist-when-not-member
;;   (implies (and (not (hons-intersect-p (4v-bitspec-entry-vars (car spec1))
;;                                        (4v-bitspec-vars spec2)))
;;                 (not (hons-dups-p (4v-bitspec-vars spec1)))
;;                 (consp spec1)
;;                 (not (equal (caar spec1) :fixed)))
;;            (iff (alists-compatible
;;                  (params-to-4v-alist spec1 params1)
;;                  (params-to-4v-alist spec2 params2))
;;                 (alists-compatible
;;                  (params-to-4v-alist (cdr spec1) (cdr params1))
;;                  (params-to-4v-alist spec2 params2))))

;;   :hints(("Goal" :in-theory (e/d (alist-keys-append
;;                                   alist-keys-pairlis$
;;                                   not-intersecting-impl-not-intersecting-subset)
;;                                  (4v-bitspec-entry-vars
;;                                   param-to-4v-alist
;;                                   4v-bitspec-entryp param-for-4v-bitspec-entryp))
;;           :do-not-induct t))
;;   :otf-flg t)

;; (defthm alists-compatible-params-to-4v-alist-when-fixed-nonmember
;;   (implies (and (not (hons-intersect-p (4v-bitspec-entry-vars (car spec1))
;;                                        (4v-bitspec-vars spec2)))
;;                 (not (hons-dups-p (4v-bitspec-vars spec1)))
;;                 (consp spec1)
;;                 (equal (caar spec1) :fixed))
;;            (iff (alists-compatible
;;                  (params-to-4v-alist spec1 params1)
;;                  (params-to-4v-alist spec2 params2))
;;                 (alists-compatible
;;                  (params-to-4v-alist (cdr spec1) params1)
;;                  (params-to-4v-alist spec2 params2))))

;;   :hints(("Goal" :in-theory (e/d (alist-keys-append
;;                                   alist-keys-pairlis$
;;                                   not-intersecting-impl-not-intersecting-subset
;;                                   alists-compatible-when-not-intersecting-vars)
;;                                  (4v-bitspec-entry-vars
;;                                   param-to-4v-alist
;;                                   4v-bitspec-entryp param-for-4v-bitspec-entryp))
;;           :do-not-induct t))
;;   :otf-flg t)

;; (local
;;  (progn
;;    (defthm member-x-impl-vars-subset-fixed
;;      (implies (and (member-equal (list :fixed x) spec))
;;               (subsetp-equal (alist-keys x)
;;                              (4v-bitspec-vars spec)))
;;      :hints(("Goal" :in-theory (disable 4v-bitspec-entry-vars))))

;;    (defthm member-x-impl-vars-subset-fixed1
;;      (implies (and (member-equal x spec)
;;                    (equal (car x) :fixed))
;;               (subsetp-equal (alist-keys (cadr x))
;;                              (4v-bitspec-vars spec)))
;;      :hints(("Goal" :in-theory (disable 4v-bitspec-entry-vars))))

;;    (defthm alists-compatible-fixed-member1
;;      (implies (and (member-equal x spec)
;;                    (equal (car x) :fixed)
;;                    (not (hons-dups-p (4v-bitspec-vars spec))))
;;               (alists-compatible (cadr x) (params-to-4v-alist spec params)))
;;      :hints(("Goal" :in-theory (e/d (alists-compatible-when-not-intersecting-vars
;;                                      not-intersecting-impl-not-intersecting-subset
;;                                      not-intersecting-impl-not-intersecting-subset2)
;;                                     (param-to-4v-alist 4v-bitspec-entry-vars)))))))

;; (defthm alists-compatible-fixed-member
;;   (implies (and (member-equal (list :fixed x) spec)
;;                 (not (hons-dups-p (4v-bitspec-vars spec))))
;;            (alists-compatible x (params-to-4v-alist spec params)))
;;   :hints(("Goal" :in-theory (e/d (alists-compatible-when-not-intersecting-vars
;;                                   not-intersecting-impl-not-intersecting-subset
;;                                   not-intersecting-impl-not-intersecting-subset2)
;;                                  (param-to-4v-alist 4v-bitspec-entry-vars)))))


;; (defthm alists-compatible-params-to-4v-alist-when-fixed-member
;;   (implies (and (member-equal (car spec1) spec2)
;;                 (not (hons-dups-p (4v-bitspec-vars spec1)))
;;                 (not (hons-dups-p (4v-bitspec-vars spec2)))
;;                 (consp spec1)
;;                 (equal (caar spec1) :fixed))
;;            (iff (alists-compatible
;;                  (params-to-4v-alist spec1 params1)
;;                  (params-to-4v-alist spec2 params2))
;;                 (alists-compatible
;;                  (params-to-4v-alist (cdr spec1) params1)
;;                  (params-to-4v-alist spec2 params2))))

;;   :hints(("Goal" :in-theory (e/d (alist-keys-append
;;                                   alist-keys-pairlis$
;;                                   not-intersecting-impl-not-intersecting-subset
;;                                   alists-compatible-when-not-intersecting-vars)
;;                                  (4v-bitspec-entry-vars
;;                                   param-to-4v-alist
;;                                   4v-bitspec-entryp param-for-4v-bitspec-entryp))
;;           :do-not-induct t))
;;   :otf-flg t)




;; (defthm alists-compatible-append-cases
;;   (implies (not (intersectp-equal (alist-keys b)
;;                                   (alist-keys c)))
;;            (iff (alists-compatible a (append b c))
;;                 (and (alists-compatible a b)
;;                      (alists-compatible a c))))
;;   :hints (("goal" :do-not-induct t)
;;           (witness :ruleset (alists-compatible-witnessing
;;                              alists-compatible-hons-assoc-equal-ex))
;;           (and stable-under-simplificationp
;;                '(:in-theory (e/d (hons-assoc-equal-iff-member-alist-keys)
;;                                  (alist-keys-member-hons-assoc-equal))))
;;           (set-reasoning)))

