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
; Original authors: Sol Swords <sswords@centtech.com>


(in-package "SV")

(include-book "eval")
(include-book "centaur/fty/baselists" :dir :system)
(local (include-book "std/lists/take" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))
(local (std::add-default-post-define-hook :fix))

(fty::deflist svex-envlist :elt-type svex-env :true-listp t :elementp-of-nil t)
(fty::deflist svex-alistlist :elt-type svex-alist :true-listp t :elementp-of-nil t)
(fty::deflist svarlist-list :elt-type svarlist :true-listp t)
(fty::deflist svexlistlist :elt-type svexlist :true-listp t :elementp-of-nil t)
(fty::deflist 4veclistlist :elt-type 4veclist :true-listp t :elementp-of-nil t)


(define svexlistlist-eval ((x svexlistlist-p)
                             (env svex-env-p))
  :returns (4vecs 4veclistlist-p)
  (if (atom x)
      nil
    (cons (svexlist-eval (car x) env)
          (svexlistlist-eval (cdr x) env)))
  ///
  (defret len-of-<fn>
    (equal (len 4vecs) (len x)))

  (defret nth-of-<fn>
    (equal (nth n 4vecs)
           (svexlist-eval (nth n x) env))
    :hints (("goal" :induct (nth n x)
             :expand ((svexlist-eval nil env)))))

  (defret <fn>-of-cons
    :pre-bind ((x (cons a b)))
    (equal 4vecs
           (cons (svexlist-eval a env)
                 (<fn> b env))))

  (defret <fn>-of-nil
    :pre-bind ((x nil))
    (equal 4vecs nil)))


(define svex-alistlist-eval ((x svex-alistlist-p)
                             (env svex-env-p))
  :returns (envs svex-envlist-p)
  (if (atom x)
      nil
    (cons (svex-alist-eval (car x) env)
          (svex-alistlist-eval (cdr x) env)))
  ///
  (defret len-of-<fn>
    (equal (len envs) (len x)))

  (defret nth-of-<fn>
    (equal (nth n envs)
           (svex-alist-eval (nth n x) env))
    :hints (("goal" :induct (nth n x)
             :expand ((svex-alist-eval nil env)))))

  (defret <fn>-of-cons
    :pre-bind ((x (cons a b)))
    (equal envs
           (cons (svex-alist-eval a env)
                 (<fn> b env))))

  (defret <fn>-of-nil
    :pre-bind ((x nil))
    (equal envs nil)))


(define svexlist/env-list-eval ((x svexlistlist-p)
                                (envs svex-envlist-p))
  :guard (eql (len x) (len envs))
  :returns (4vecs 4veclistlist-p)
  (if (atom x)
      nil
    (cons (svexlist-eval (car x) (car envs))
          (svexlist/env-list-eval (cdr x) (cdr envs))))
  ///
  (defret len-of-<fn>
    (equal (len 4vecs) (len x)))

  (defret nth-of-<fn>
    (equal (nth n 4vecs)
           (svexlist-eval (nth n x) (nth n envs))))

  (defret <fn>-of-cons
    :pre-bind ((x (cons a b)))
    (equal 4vecs
           (cons (svexlist-eval a (car envs))
                 (svexlist/env-list-eval b (cdr envs)))))

  (defret <fn>-of-nil
    :pre-bind ((x nil))
    (equal 4vecs nil)))



(define sum-of-lengths (x)
  :returns (sum natp :rule-classes :type-prescription)
  (if (atom x)
      0
    (+ (len (car x))
       (sum-of-lengths (cdr x))))
  ///
  (defthm sum-of-lengths-of-cdr
    (implies (consp x)
             (= (sum-of-lengths (cdr x))
                (- (sum-of-lengths x) (len (car x)))))
    :rule-classes :linear))


(define binary-append-tr (x y)
  :enabled t
  (mbe :logic (append x y)
       :exec (revappend-without-guard (rev x) y))
  ///
  (defmacro append-tr (&rest args)
    (cond ((null args) nil)
          ((null (cdr args)) (car args))
          (t (xxxjoin 'binary-append-tr args)))))


(define element-listlist-p (x)
  :verify-guards nil
  (if (atom x)
      (eq x nil)
    (and (acl2::element-list-p (car x))
         (element-listlist-p (cdr x)))))



(define append-lists (x)
  :returns (list true-listp :rule-classes :type-prescription)
  (if (atom x)
      nil
    (append-tr (car x) (append-lists (cdr x))))
  ///
  (deffixequiv append-lists :args ((x true-list-listp)))

  (defret len-of-<fn>
    (equal (len list)
           (sum-of-lengths x))
    :hints(("Goal" :in-theory (enable sum-of-lengths))))

  (defret element-list-p-of-<fn>
    (implies (element-listlist-p x)
             (acl2::element-list-p (append-lists x)))
    :hints(("Goal" :in-theory (enable element-listlist-p)))))


(define elementlistlist-projection (x)
  :Verify-guards nil
  (if (atom x)
      nil
    (cons (acl2::elementlist-projection (car x))
          (elementlistlist-projection (cdr x)))))

(encapsulate
  ;; 
  (((pseudoproj-relation * *) => *)
   ((pseudoproj *) => *))

  (local (defun pseudoproj-relation (x y)
           (declare (ignore x y))
           t))

  (local (defun pseudoproj (x)
           (if (atom x)
               nil
             (cons t (pseudoproj (cdr x))))))

  (defthm pseudoproj-relation-of-pseudoproj
    (implies (< (nfix n) (len x))
             (pseudoproj-relation (nth n x) (nth n (pseudoproj x))))))

(define pseudoproj-relation-list (x y)
  :verify-guards nil
  (if (atom x)
      t
    (and (pseudoproj-relation (car x) (car y))
         (pseudoproj-relation-list (cdr x) (cdr y))))
  ///
  (local (defun count-up-to-len (n x)
           (declare (xargs :measure (nfix (- (len x) (nfix n)))))
           (if (zp (- (len x) (nfix n)))
               n
             (count-up-to-len (+ 1 (nfix n)) x))))
  (local (defthm nthcdr-of-too-many
           (implies (<= (len x) (nfix n))
                    (not (consp (nthcdr n x))))))

  (defthm pseudoproj-relation-list-of-nthcdr-pseudoproj
    (pseudoproj-relation-list (nthcdr n x) (nthcdr n (pseudoproj x)))
    :hints (("goal" :induct (count-up-to-len n x)
             :expand ((:free (x) (nthcdr (+ 1 (nfix n)) x))
                      (:free (y) (pseudoproj-relation-list (nthcdr n x) y))))
            (and stable-under-simplificationp
                 '(:use ((:instance pseudoproj-relation-of-pseudoproj
                          (n 0)))
                   :in-theory (disable pseudoproj-relation-of-pseudoproj)))))

  (defthm pseudoproj-relation-list-of-pseudoproj
    (pseudoproj-relation-list x (pseudoproj x))
    :hints (("goal" :use ((:instance pseudoproj-relation-list-of-nthcdr-pseudoproj
                           (n 0)))
             :in-theory (disable pseudoproj-relation-list-of-nthcdr-pseudoproj))))

  (defthm pseudoproj-relation-of-nthcdr
    (implies (pseudoproj-relation-list x y)
             (pseudoproj-relation-list (nthcdr n x) (nthcdr n y))))

  (defthm pseudoproj-relation-of-take
    (implies (and (pseudoproj-relation-list x y)
                  (<= (nfix n) (len x)))
             (pseudoproj-relation-list (take n x) (take n y)))
    :hints(("Goal" :in-theory (disable acl2::take-of-zero))))

  (deffixequiv pseudoproj-relation-list :args ((x true-listp) (y true-listp))))

(define pseudoproj-relation-listlist (x y)
  :verify-guards nil
  (if (atom x)
      t
    (and (pseudoproj-relation-list (car x) (car y))
         (pseudoproj-relation-listlist (cdr x) (cdr y))))
  ///
  (deffixequiv pseudoproj-relation-listlist :args ((x true-list-listp) (y true-list-listp))))

(define extract-lists (x (list true-listp))
  :returns (new-x)
  (b* (((when (atom x)) nil)
       (len1 (len (car x)))
       (first (take len1 list))
       (rest (nthcdr len1 list)))
    (cons first (extract-lists (cdr x) rest)))
  ///
  (deffixequiv extract-lists :args ((x true-listp) (list true-listp)))

  (defret len-of-<fn>
    (equal (len new-x) (len x)))

  (defret element-listlist-p-of-<fn>
    (implies (and (acl2::element-list-p list)
                  (<= (sum-of-lengths x) (len list)))
             (element-listlist-p new-x))
    :hints(("Goal" :in-theory (enable element-listlist-p))))

  (local (defthm nthcdr-of-append
           (implies (equal n (len x))
                    (equal (nthcdr n (append x y))
                           y))))

  (defret <fn>-of-append-lists
    (equal (extract-lists x (append-lists x))
           (true-list-list-fix x))
    :hints(("Goal" :in-theory (enable append-lists true-list-list-fix))))

  (local (defthm take-of-sum
           (implies (and (natp n) (natp m))
                    (equal (take (+ n m) x)
                           (append (take n x)
                                   (take m (nthcdr n x)))))
           :hints(("Goal" 
                   :induct (nthcdr n x)))))

  (defret append-lists-of-<fn>
    (equal (append-lists new-x)
           (take (sum-of-lengths x) list))
    :hints(("Goal" :in-theory (enable append-lists sum-of-lengths))))
           

  (local (defthm projection-of-nthcdr
           (equal (nthcdr n (acl2::elementlist-projection x))
                  (acl2::elementlist-projection (nthcdr n x)))
           :hints(("Goal" :in-theory (enable acl2::elementlist-projection nthcdr)))))

  (defret <fn>-of-projection
    (implies (<= (sum-of-lengths x) (len y))
             (equal (extract-lists x (acl2::elementlist-projection y))
                    (elementlistlist-projection (extract-lists x y))))
    :hints(("Goal" :in-theory (enable elementlistlist-projection)
            :induct (extract-lists x y)
            :expand ((:free (y) (extract-lists x y))))))

  (local (defun fn-of-pseudo-projection-lemma-ind (x a b)
           (if (atom x)
               (list a b)
             (fn-of-pseudo-projection-lemma-ind
              (cdr x) (nthcdr (len (car x)) a) (nthcdr (len (car x)) b)))))

  (local (defthm len-of-nthcdr
           (implies (<= (nfix n) (len x))
                    (equal (len (nthcdr n x))
                           (- (len x) (nfix n))))))

  (defret <fn>-when-pseudoproj-relation-list
    (implies (and (pseudoproj-relation-list a b)
                  (<= (sum-of-lengths x) (len a)))
             (pseudoproj-relation-listlist
              (extract-lists x a)
              (extract-lists x b)))
    :hints(("Goal" :in-theory (enable pseudoproj-relation-listlist sum-of-lengths)
            :induct (fn-of-pseudo-projection-lemma-ind x a b))))

  (defret <fn>-of-pseudoproj
    (pseudoproj-relation-listlist
     x
     (extract-lists x (pseudoproj (append-lists x))))
    :hints (("goal" :use ((:instance extract-lists-when-pseudoproj-relation-list
                           (a (append-lists x))
                           (b (pseudoproj (append-lists x)))))))))


(define lengths-equal (x y)
  (if (atom x)
      (atom y)
    (and (consp y)
         (equal (len (car x)) (len (car y)))
         (lengths-equal (cdr x) (cdr y))))
  ///
  (local (defthm lengths-equal-symm
           (implies (lengths-equal x y)
                    (lengths-equal y x))))
  (local (defthm lengths-equal-trans
           (implies (and (lengths-equal x y)
                         (lengths-equal y z))
                    (lengths-equal x z))))
  (defequiv lengths-equal)
  (defthm lenths-equal-of-extract-lists
    (lengths-equal (extract-lists x y) x)
    :hints(("Goal" :in-theory (enable lengths-equal extract-lists))))

  (defcong lengths-equal equal (sum-of-lengths x) 1
    :hints(("Goal" :in-theory (enable sum-of-lengths)))))

    




(defsection extract-lists-svex
  (local (std::set-define-current-function extract-lists))
  (local (in-theory (enable extract-lists)))
  (defret svexlistlist-p-extract-lists-of-svexlist
    (implies (and (svexlist-p list)
                  (<= (sum-of-lengths x) (len list)))
             (svexlistlist-p new-x))
    :hints (("goal" :use ((:functional-instance element-listlist-p-of-extract-lists
                           (acl2::element-p svex-p)
                           (acl2::element-list-p svexlist-p)
                           (acl2::element-list-final-cdr-p (lambda (x) (eq x nil)))
                           (element-listlist-p svexlistlist-p))))))

  (defret svex-alistlist-p-extract-lists-of-svex-alist
    (implies (and (svex-alist-p list)
                  (<= (sum-of-lengths x) (len list)))
             (svex-alistlist-p new-x))
    :hints (("goal" :use ((:functional-instance element-listlist-p-of-extract-lists
                           (acl2::element-p (lambda (x) (and (consp x) (svar-p (car x)) (svex-p (cdr x)))))
                           (acl2::element-list-p svex-alist-p)
                           (acl2::element-list-final-cdr-p (lambda (x) (eq x nil)))
                           (element-listlist-p svex-alistlist-p))))))

  (defret 4veclistlist-p-extract-lists-of-4veclist
    (implies (and (4veclist-p list)
                  (<= (sum-of-lengths x) (len list)))
             (4veclistlist-p new-x))
    :hints (("goal" :use ((:functional-instance element-listlist-p-of-extract-lists
                           (acl2::element-p 4vec-p)
                           (acl2::element-list-p 4veclist-p)
                           (acl2::element-list-final-cdr-p (lambda (x) (eq x nil)))
                           (element-listlist-p 4veclistlist-p))))))

  (defret svex-envlist-p-extract-lists-of-svex-env
    (implies (and (svex-env-p list)
                  (<= (sum-of-lengths x) (len list)))
             (svex-envlist-p new-x))
    :hints (("goal" :use ((:functional-instance element-listlist-p-of-extract-lists
                           (acl2::element-p (lambda (x) (and (consp x) (svar-p (car x)) (4vec-p (cdr x)))))
                           (acl2::element-list-p svex-env-p)
                           (acl2::element-list-final-cdr-p (lambda (x) (eq x nil)))
                           (element-listlist-p svex-envlist-p))))))

  (defret svarlist-list-p-extract-lists-of-svarlist
    (implies (and (svarlist-p list)
                  (<= (sum-of-lengths x) (len list)))
             (svarlist-list-p new-x))
    :hints (("goal" :use ((:functional-instance element-listlist-p-of-extract-lists
                           (acl2::element-p svar-p)
                           (acl2::element-list-p svarlist-p)
                           (acl2::element-list-final-cdr-p (lambda (x) (eq x nil)))
                           (element-listlist-p svarlist-list-p)))))))

(defsection append-lists-svex
  (local (std::set-define-current-function append-lists))
  (local (in-theory (enable append-lists)))

  (defret svexlist-p-<fn>-of-svexlistlist
    (implies (svexlistlist-p x)
             (svexlist-p (append-lists x))))

  (defret svex-alist-p-<fn>-of-svex-alistlist
    (implies (svex-alistlist-p x)
             (svex-alist-p (append-lists x))))

  (defret 4veclist-p-<fn>-of-4veclistlist
    (implies (4veclistlist-p x)
             (4veclist-p (append-lists x))))

  (defret svex-env-p-<fn>-of-svex-envlist
    (implies (svex-envlist-p x)
             (svex-env-p (append-lists x))))

  (defret svarlist-p-<fn>-of-svarlist-list
    (implies (svarlist-list-p x)
             (svarlist-p (append-lists x)))))

