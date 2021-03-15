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
(include-book "rsh-concat")
(include-book "env-ops")
(include-book "lists")
(include-book "std/basic/two-nats-measure" :dir :system)
(include-book "tools/templates" :dir :system)
(local (include-book "std/alists/hons-assoc-equal" :dir :system))
(local (include-book "std/basic/arith-equivs" :dir :system))
(local (std::add-default-post-define-hook :fix))


(defconst *svex-phase/cycle-varname-template*
  '(progn
     (defprod svex-<period>-varname
       ((name)
        (<period> natp))
       :layout :tree
       :tag :<period>)


     (define svex-<period>-var ((x svar-p) (<period> natp))
       :returns (cycvar svar-p)
       (b* (((svar x)))
         (change-svar x :name (make-svex-<period>-varname :name x.name :<period> <period>)))
       ///
       (defthm svex-<period>-var-unique
         (implies (not (and (svar-equiv x y)
                            (nat-equiv cyc1 cyc2)))
                  (not (equal (svex-<period>-var x cyc1)
                              (svex-<period>-var y cyc2))))
         :hints(("Goal" :in-theory (enable svar-fix-redef))))

       (defthmd svex-<period>-var-unique-split
         (iff (equal (svex-<period>-var x cyc1)
                     (svex-<period>-var y cyc2))
              (and (svar-equiv x y)
                   (nat-equiv cyc1 cyc2)))
         :hints(("Goal" :in-theory (enable svar-fix-redef)))))

     (define svex-<period>-var-p ((x svar-p))
       :returns (is-<period>)
       (b* (((svar x)))
         (svex-<period>-varname-p x.name))
       ///
       (defthm svex-<period>-var-p-of-svex-<period>-var
         (svex-<period>-var-p (svex-<period>-var x <period>))
         :hints(("Goal" :in-theory (enable svex-<period>-var))))

       (defret svex-<period>-var-differs-from-non<period>
         (implies (not (svex-<period>-var-p y))
                  (and (not (equal y (svex-<period>-var x <period>)))
                       (not (equal (svar-fix y) (svex-<period>-var x <period>)))))
         :hints(("Goal" :in-theory (enable svex-<period>-var)))))

     (define svex-<period>-var->svar ((x svar-p))
       :guard (svex-<period>-var-p x)
       :guard-hints (("goal" :in-theory (enable svex-<period>-var-p)))
       :returns (svar svar-p)
       (change-svar x :name (svex-<period>-varname->name (svar->name x)))
       ///
       (defthm svex-<period>-var->svar-of-svex-<period>-var
         (equal (svex-<period>-var->svar (svex-<period>-var x <period>))
                (svar-fix x))
         :hints(("Goal" :in-theory (enable svex-<period>-var)))))

     (define svex-<period>-var-><period> ((x svar-p))
       :guard (svex-<period>-var-p x)
       :guard-hints (("goal" :in-theory (enable svex-<period>-var-p)))
       :returns (<period> natp :rule-classes :type-prescription)
       (svex-<period>-varname-><period> (svar->name x))
       ///
       (defthm svex-<period>-var-><period>-of-svex-<period>-var
         (equal (svex-<period>-var-><period> (svex-<period>-var x <period>))
                (nfix <period>))
         :hints(("Goal" :in-theory (enable svex-<period>-var))))

       (defthmd equal-of-svex-<period>-var
         (equal (equal (svex-<period>-var v <period>) cvar)
                (and (svar-p cvar)
                     (svex-<period>-var-p cvar)
                     (equal (svex-<period>-var-><period> cvar) (nfix <period>))
                     (equal (svex-<period>-var->svar cvar) (svar-fix v))))
         :hints(("Goal" :in-theory (enable svex-<period>-var
                                           svex-<period>-var->svar
                                           svex-<period>-var-p)))))




     (define svarlist-has-svex-<period>-var ((x svarlist-p))
       :returns (has-<period>-var)
       (if (Atom x)
           nil
         (or (svex-<period>-var-p (car x))
             (svarlist-has-svex-<period>-var (cdr x))))
       ///
       (defret svex-<period>-var-not-member-when-has-no-<period>-var
         (implies (not has-<period>-var)
                  (and (not (member (svex-<period>-var v <period>) x))
                       (not (member (svex-<period>-var v <period>) (svarlist-fix x))))))

       (local (defun svarlist-has-svex-<period>-var-witness (x)
                (if (atom x)
                    nil
                  (if (svex-<period>-var-p (car x))
                      (car x)
                    (svarlist-has-svex-<period>-var-witness (cdr x))))))

       (local (defthm svarlist-has-svex-<period>-var-iff-witness
                (implies (acl2::rewriting-negative-literal `(svarlist-has-svex-<period>-var ,x))
                         (iff (svarlist-has-svex-<period>-var x)
                              (b* ((witness (svarlist-has-svex-<period>-var-witness x)))
                                (and (svex-<period>-var-p witness)
                                     (member witness x)))))))

       (local (defthm no-<period>-var-when-not-has-<period>-var
                (implies (and (not (svarlist-has-svex-<period>-var x))
                              (svex-<period>-var-p v))
                         (not (member v x)))))

       (local (defthm not-member-when-subset
                (implies (and (subsetp x y)
                              (not (member k y)))
                         (not (member k x)))))

       (local (defthm equal-of-bools
                (implies (and (booleanp x) (booleanp y))
                         (equal (equal x y) (iff x y)))))

       (defcong set-equiv equal (svarlist-has-svex-<period>-var x) 1
         :hints (("goal" :do-not-induct t))))))

(defmacro def-svex-phase/cycle-var-fns (period)
  (b* ((periodstr (symbol-name period)))
    (acl2::template-subst *svex-phase/cycle-varname-template*
                          :atom-alist `((<period> . ,period))
                          :str-alist `(("<PERIOD>" . ,periodstr))
                          :pkg-sym nil)))

(def-svex-phase/cycle-var-fns cycle)
(def-svex-phase/cycle-var-fns phase)



(local (defthm svex-lookup-of-append
         (equal (svex-lookup v (append x y))
                (or (svex-lookup v x)
                    (svex-lookup v y)))
         :hints(("Goal" :in-theory (enable svex-lookup)))))


(define svex-cycle-var-assigns ((x svarlist-p) (cycle natp))
  :prepwork ((local (in-theory (enable svarlist-p svarlist-fix))))
  :returns (assigns svex-alist-p)
  (if (atom x)
      nil
    (cons (let ((v (svar-fix (car x))))
            (cons v (svex-var (svex-cycle-var v cycle))))
          (svex-cycle-var-assigns (cdr x) cycle)))
  ///
  (defret lookup-in-svex-cycle-var-assigns
    (equal (svex-lookup v assigns)
           (and (member (svar-fix v) (svarlist-fix x))
                (svex-var (svex-cycle-var v cycle))))
    :hints(("Goal" :in-theory (enable svex-lookup)))))




(define svex-envs-update-nth ((var svar-p)
                              (val 4vec-p)
                              (n natp)
                              (envs svex-envlist-p))
  :returns (new-envs svex-envlist-p)
  (if (zp n)
      (cons (cons (cons (svar-fix var) (4vec-fix val))
                  (svex-env-fix (car envs)))
            (Svex-envlist-fix (cdr envs)))
    (cons (svex-env-fix (car envs))
          (svex-envs-update-nth var val (1- n) (cdr envs))))
  ///
  (defret len-of-svex-envs-update-nth
    (implies (< (nfix n) (len envs))
             (equal (len new-envs) (len envs))))

  (local (defun lookup-ind (n0 n1 envs)
           (declare (xargs :measure (nfix n0)))
           (if (or (zp n1) (zp n0))
               (list n0 envs)
             (lookup-ind (1- n0) (1- n1) (cdr envs)))))

  (defret lookup-in-svex-envs-update-nth
    (equal (svex-env-lookup v0 (nth n0 (svex-envs-update-nth v1 val n1 envs)))
           (if (and (svar-equiv v0 v1)
                    (nat-equiv n0 n1))
               (4vec-fix val)
             (svex-env-lookup v0 (nth n0 envs))))
    :hints (("goal" :induct (lookup-ind n0 n1 envs)
             :expand ((:free (a b) (nth n0 (cons a b)))
                      (svex-envs-update-nth v1 val n1 envs)))
            (and stable-under-simplificationp
                 '(:in-theory (enable svex-env-lookup)))))

  (defthm cdr-of-svex-envs-update-nth
    (equal (cdr (svex-envs-update-nth var val n envs))
           (if (zp n)
               (svex-envlist-fix (cdr envs))
             (svex-envs-update-nth var val (1- n) (cdr envs))))))


(local (defthmd svex-env-lookup-rec
         (equal (svex-env-lookup v x)
                (if (atom x)
                    (4vec-x)
                  (if (and (consp (car x))
                           (svar-p (caar x))
                           (equal (svar-fix v) (caar x)))
                      (4vec-fix (cdar x))
                    (svex-env-lookup v (cdr x)))))
         :hints(("Goal" :in-theory (enable svex-env-lookup)))
         :rule-classes :definition))

(define svex-env-to-cycle-envs-starting ((x svex-env-p)
                                         (start-cycle natp)
                                         (ncycles natp))
  :returns (cycle-envs svex-envlist-p)
  :hooks nil
  (b* (((when (atom x)) (make-list ncycles :initial-element nil))
       ((unless (mbt (and (consp (car x)) (svar-p (caar x)))))
        (svex-env-to-cycle-envs-starting (cdr x) start-cycle ncycles))
       (cycle-envs (svex-env-to-cycle-envs-starting (cdr x) start-cycle ncycles))
       ((cons var val) (car x))
       ((when (and (svex-cycle-var-p var)
                   (>= (svex-cycle-var->cycle var) (lnfix start-cycle))
                   (< (svex-cycle-var->cycle var) (+ (lnfix start-cycle) (lnfix ncycles)))))
        (svex-envs-update-nth (svex-cycle-var->svar var)
                              val
                              (- (svex-cycle-var->cycle var) (lnfix start-cycle))
                              cycle-envs)))
    cycle-envs)
  ///
  (deffixequiv svex-env-to-cycle-envs-starting
    :hints(("Goal" :in-theory (enable svex-env-fix))))

  (defret len-of-cycle-envs-of-svex-env-to-cycle-envs-starting
    (equal (len cycle-envs) (lnfix ncycles)))


  (local (defun nth-of-repeat-nil-ind (n m)
           (declare (xargs :measure (nfix n)))
           (if (or (zp n) (zp m))
               nil
             (nth-of-repeat-nil-ind (1- n) (1- m)))))

  (local (defthm nth-of-repeat-nil
           (equal (nth m (repeat n nil))
                  nil)
           :hints(("Goal" :in-theory (enable repeat nth)
                   :induct (nth-of-repeat-nil-ind n m)))))

  (defret lookup-in-cycle-envs-of-svex-env-to-cycle-envs-starting
    (implies (< (nfix m) (nfix n))
             (equal
              (svex-env-lookup
               v
               (nth m (svex-env-to-cycle-envs-starting env curr-cycle n)))
              (svex-env-lookup (svex-cycle-var v (+ (nfix m) (nfix curr-cycle)))
                               env)))
    :hints(("Goal" :induct (svex-env-to-cycle-envs-starting env curr-cycle n)
            :expand ((:with svex-env-lookup-rec
                      (:free (v) (svex-env-lookup v env)))))
           (and stable-under-simplificationp
                '(:in-theory (enable equal-of-svex-cycle-var)))))

  (defret lookup-in-car-cycle-envs-of-svex-env-to-cycle-envs-starting
    (implies (posp n)
             (equal
              (svex-env-lookup
               v
               (car (svex-env-to-cycle-envs-starting env curr-cycle n)))
              (svex-env-lookup (svex-cycle-var v (nfix curr-cycle)) env)))
    :hints (("goal" :use ((:instance lookup-in-cycle-envs-of-svex-env-to-cycle-envs-starting
                           (m 0)))
             :in-theory (e/d (nth) (lookup-in-cycle-envs-of-svex-env-to-cycle-envs-starting)))))


  (defthm cdr-cycle-envs-of-svex-env-to-cycle-envs-starting
    (implies (posp remaining-cycles)
             (equal (cdr (svex-env-to-cycle-envs-starting
                          env curr-cycle remaining-cycles))
                    (svex-env-to-cycle-envs-starting
                     env (+ 1 (nfix curr-cycle)) (1- remaining-cycles))))
    :hints (("goal" :induct t)
            (and stable-under-simplificationp
                 '(:expand ((repeat remaining-cycles nil)))))))

(define svex-env-to-cycle-envs ((x svex-env-p)
                                (ncycles natp))
  :returns (cycle-envs svex-envlist-p)
  :hooks nil
  (b* (((when (atom x)) (make-list ncycles :initial-element nil))
       ((unless (mbt (and (consp (car x)) (svar-p (caar x)))))
        (svex-env-to-cycle-envs (cdr x) ncycles))
       (cycle-envs (svex-env-to-cycle-envs (cdr x) ncycles))
       ((cons var val) (car x))
       ((when (and (svex-cycle-var-p var)
                   (< (svex-cycle-var->cycle var) (lnfix ncycles))))
        (svex-envs-update-nth (svex-cycle-var->svar var)
                              val
                              (svex-cycle-var->cycle var)
                              cycle-envs)))
    cycle-envs)
  ///
  (deffixequiv svex-env-to-cycle-envs
    :hints(("Goal" :in-theory (enable svex-env-fix))))

  (defthm svex-env-to-cycle-envs-starting-is-svex-env-to-cycle-envs
    (equal (svex-env-to-cycle-envs-starting x 0 ncycles)
           (svex-env-to-cycle-envs x ncycles))
    :hints(("Goal" :in-theory (enable svex-env-to-cycle-envs-starting))))

  (defthm len-of-svex-env-to-cycle-envs
    (Equal (len (svex-env-to-cycle-envs x ncycles))
           (nfix ncycles)))

  (defthm lookup-in-cycle-envs-of-svex-env-to-cycle-envs
    (implies (< (nfix m) (nfix ncycles))
             (equal
              (svex-env-lookup
               v
               (nth m (svex-env-to-cycle-envs env ncycles)))
              (svex-env-lookup (svex-cycle-var v m) env)))
    :hints (("goal" :use ((:instance svex-env-to-cycle-envs-starting-is-svex-env-to-cycle-envs
                           (x env)))
             :in-theory (disable svex-env-to-cycle-envs-starting-is-svex-env-to-cycle-envs)))))


(define svarlist-no-cycle-vars-below (n x)
  :verify-guards nil
  (if (atom x)
      t
    (and (or (not (svex-cycle-var-p (car x)))
             (>= (svex-cycle-var->cycle (car x)) (nfix n)))
         (svarlist-no-cycle-vars-below n (cdr x))))
  ///
  (defthm svarlist-no-cycle-vars-below-of-append
    (implies (and (svarlist-no-cycle-vars-below n a)
                  (svarlist-no-cycle-vars-below n b))
             (svarlist-no-cycle-vars-below n (append a b))))

  (defthm svarlist-no-cycle-vars-below-when-no-cycle-vars
    (implies (NOT (SVARLIST-HAS-SVEX-CYCLE-VAR x))
             (SVARLIST-NO-CYCLE-VARS-BELOW N x))
    :hints(("Goal" :in-theory (enable svarlist-has-svex-cycle-var)))))


(define svar-alist-add-cycle-num ((x svar-alist-p)
                                (cycle natp))
  :returns (cycle-x svar-alist-p)
  :hooks nil
  (if (atom x)
      nil
    (if (mbt (and (Consp (car x)) (svar-p (caar x))))
        (cons (cons (svex-cycle-var (caar x) cycle) (cdar x))
              (svar-alist-add-cycle-num (cdr x) cycle))
      (svar-alist-add-cycle-num (cdr x) cycle)))
  ///
  (deffixequiv svar-alist-add-cycle-num
    :hints(("Goal" :in-theory (enable svar-alist-fix))))

  (defthm svarlist-no-cycle-vars-below-of-svar-alist-add-cycle-num
    (implies (<= (nfix n) (nfix cycle))
             (svarlist-no-cycle-vars-below n (alist-keys (svar-alist-add-cycle-num x cycle))))
    :hints(("Goal" :in-theory (enable svarlist-no-cycle-vars-below alist-keys))))

  (defret svex-env-p-of-svar-alist-add-cycle-num
    (implies (svex-env-p x)
             (svex-env-p cycle-x)))

  (defret svex-alist-p-of-svar-alist-add-cycle-num
    (implies (svex-alist-p x)
             (svex-alist-p cycle-x))))


(local (defthm svar-alist-p-when-svex-env-p
         (implies (svex-env-p x)
                  (svar-alist-p x))
         :hints(("Goal" :in-theory (enable svex-env-p svar-alist-p)))))

(define svex-cycle-envs-to-single-env ((x svex-envlist-p)
                                       (curr-cycle natp)
                                       (rest svex-env-p))
  :returns (env svex-env-p)
  (b* (((when (atom x)) (svex-env-fix rest)))
    (Append (svar-alist-add-cycle-num (svex-env-fix (car x)) curr-cycle)
            (svex-cycle-envs-to-single-env (cdr x) (1+ (lnfix curr-cycle)) rest)))
  ///
  (local (defthm svex-envlist-fix-when-atom
           (implies (not (consp x))
                    (equal (svex-envlist-fix x) nil))
           :hints(("Goal" :in-theory (enable svex-envlist-fix)))))

  (local (defthm svex-env-to-cycle-envs-starting-0-cycles
           (equal (svex-env-to-cycle-envs-starting x curr-cycle 0)
                  nil)
           :hints(("Goal" :in-theory (enable svex-env-to-cycle-envs-starting)))))



  (local (Defthm alist-keys-of-append
           (equal (alist-keys (append a b))
                  (append (alist-keys a) (alist-keys b)))
           :hints(("Goal" :in-theory (enable alist-keys)))))

  (local (defret svarlist-no-cycle-vars-below-of-svex-cycle-envs-to-single-env
           (implies (and (<= (nfix n) (nfix curr-cycle))
                         (not (svarlist-has-svex-cycle-var (alist-keys (svex-env-fix rest)))))
                    (svarlist-no-cycle-vars-below n (alist-keys env)))))

  (local (defthm svex-envs-update-nth-is-update-nth
           (equal (svex-envs-update-nth var val n x)
                  (update-nth n (cons (cons (svar-fix var) (4vec-fix val))
                                      (svex-env-fix (nth n x)))
                              (svex-envlist-fix x)))
           :hints(("Goal" :in-theory (enable svex-envs-update-nth)))))

  (local (defthm svex-env-p-nth-of-svex-envlist
           (implies (svex-envlist-p x)
                    (svex-env-p (nth n x)))
           :hints(("Goal" :in-theory (enable svex-envlist-p)))))

  (local (defthm nth-of-update-nth-equiv
           (implies (equal x (update-nth n v y))
                    (equal (nth n x) v))))

  (local (defthm update-nth-of-update-nth-equiv
           (implies (equal x (update-nth n v y))
                    (equal (update-nth n v1 x)
                           (update-nth n v1 y)))))

  (local (Defthm update-nth-of-nth
           (implies (< (nfix n) (len x))
                    (equal (update-nth n (nth n x) x) x))))

  (local (defthm svex-env-to-cycle-envs-starting-of-append-add-cycle-num
           (implies (and (<= (nfix curr-cycle) (nfix cycle))
                         (< (nfix cycle) (+ (nfix ncycles) (nfix curr-cycle))))
                    (equal (svex-env-to-cycle-envs-starting
                            (append (svar-alist-add-cycle-num env cycle) rest)
                            curr-cycle ncycles)
                           (b* ((rest-envs (svex-env-to-cycle-envs-starting rest curr-cycle ncycles))
                                (n (- (nfix cycle) (nfix curr-cycle))))
                             (update-nth n
                                         (append (svex-env-fix env) (nth n rest-envs)) rest-envs))))
           :hints(("Goal" :in-theory (enable svar-alist-add-cycle-num
                                             svex-env-to-cycle-envs-starting
                                             svex-env-fix)
                   :induct (svar-alist-add-cycle-num env cycle)))))

  (local (defthm svex-envs-update-nth-car
           (implies (not (zp n))
                    (Equal (car (svex-envs-update-nth var val n x))
                           (svex-env-fix (car x))))
           :hints(("Goal" :in-theory (e/d (svex-envs-update-nth)
                                          (svex-envs-update-nth-is-update-nth))))))

  (local (defthm car-svex-env-to-cycle-envs-starting-when-no-cycle-vars-below
           (implies (svarlist-no-cycle-vars-below (+ 1 (nfix curr-cycle)) (alist-keys (svex-env-fix env)))
                    (equal (car (svex-env-to-cycle-envs-starting env curr-cycle ncycles)) nil))
           :hints(("Goal" :in-theory (e/d (svex-env-to-cycle-envs-starting
                                             svarlist-no-cycle-vars-below
                                             alist-keys svex-env-fix
                                             repeat)
                                          (svex-envs-update-nth-is-update-nth))
                   :induct t))))

  (local (include-book "std/lists/take" :dir :system))

  (local (defthm svex-env-to-cycle-envs-starting-when-no-cycle-vars
           (implies (not (svarlist-has-svex-cycle-var (alist-keys (svex-env-fix env))))
                    (equal (svex-env-to-cycle-envs-starting env curr-cycle ncycles)
                           (repeat ncycles nil)))
           :hints(("Goal" :in-theory (enable svex-env-to-cycle-envs-starting
                                             svarlist-has-svex-cycle-var
                                             svex-env-fix
                                             alist-keys)
                   :induct (svex-env-to-cycle-envs-starting env curr-cycle ncycles)))))

  (local (defthm svex-env-to-cycle-envs-starting-when-zp
           (implies (zp ncycles)
                    (equal (svex-env-to-cycle-envs-starting env curr-cycle ncycles)
                           nil))
           :hints(("Goal" :in-theory (enable svex-env-to-cycle-envs-starting)))))

  (local (defret svex-env-to-cycle-envs-of-svex-cycle-envs-to-single-env-starting-lemma
           (implies (and (not (svarlist-has-svex-cycle-var (alist-keys (svex-env-fix rest))))
                         (integerp extra-cycles))
                    (equal (svex-env-to-cycle-envs-starting env curr-cycle (+ extra-cycles (len x)))
                           (svex-envlist-fix (take (+ extra-cycles (len x)) x))))
           :hints (("goal" :induct t)
                   (and stable-under-simplificationp
                        '(:in-theory (enable repeat))))))

  (local (defthm dumb
           (equal (+ x (- x) y)
                  (fix y))))

  (defret svex-env-to-cycle-envs-of-svex-cycle-envs-to-single-env-starting
    (implies (not (svarlist-has-svex-cycle-var (alist-keys (svex-env-fix rest))))
             (equal (svex-env-to-cycle-envs-starting env curr-cycle ncycles)
                    (svex-envlist-fix (take ncycles x))))
    :hints (("goal" :use ((:instance svex-env-to-cycle-envs-of-svex-cycle-envs-to-single-env-starting-lemma
                           (extra-cycles (- (nfix ncycles) (len x)))))
             :in-theory (disable svex-env-to-cycle-envs-of-svex-cycle-envs-to-single-env-starting-lemma)
             :do-not-induct t)))

  (defret svex-env-to-cycle-envs-of-svex-cycle-envs-to-single-env
    (implies (not (svarlist-has-svex-cycle-var (alist-keys (svex-env-fix rest))))
             (equal (svex-env-to-cycle-envs (svex-cycle-envs-to-single-env x 0 rest) len)
                    (svex-envlist-fix (take len x))))
    :hints (("Goal" :use ((:instance svex-env-to-cycle-envs-of-svex-cycle-envs-to-single-env-starting
                           (curr-cycle 0) (ncycles len)))
             :in-theory (disable svex-env-to-cycle-envs-of-svex-cycle-envs-to-single-env-starting))))

  (local (defthmd member-alist-keys
           (iff (member v (alist-keys x))
                (hons-assoc-equal v x))
           :hints(("Goal" :in-theory (enable alist-keys)))))

  ;; (local (defthm svex-env-lookup-of-append
  ;;          (equal (svex-env-lookup v (append a b))
  ;;                 (if (member (svar-fix v) (alist-keys (svex-env-fix a)))
  ;;                     (svex-env-lookup v a)
  ;;                   (svex-env-lookup v b)))
  ;;          :hints(("Goal" :in-theory (enable svex-env-lookup member-alist-keys)))))

  (local (defthm noncycle-var-member-svex-add-cycle-num
           (implies (not (svex-cycle-var-p v))
                    (not (svex-env-boundp v (svar-alist-add-cycle-num env cycle)))
                    ;; (not (member (svar-fix v) (alist-keys (svar-alist-add-cycle-num env cycle))))
                    )
           :hints(("Goal" :in-theory (enable svar-alist-add-cycle-num
                                             ;; alist-keys
                                             svex-env-boundp
                                             svex-cycle-var-p)))))

  (defret lookup-in-svex-envs-to-single-env-when-not-cycle
    (implies (not (svex-cycle-var-p v))
             (equal (svex-env-lookup v (svex-cycle-envs-to-single-env ins curr-cycle rest))
                    (svex-env-lookup v rest))))

  (defthm member-cycle-var-of-env-add-cycle-num
    (iff (svex-env-boundp (svex-cycle-var name ncycle)
                          (svar-alist-add-cycle-num x cycle))
         (and (equal (nfix cycle) (nfix ncycle))
              (svex-env-boundp name x)))
    :hints(("Goal" :in-theory (enable svar-alist-add-cycle-num svex-env-fix alist-keys
                                      equal-of-svex-cycle-var
                                      svex-env-boundp))))

  (defthm env-lookup-of-cycle-var-in-env-add-cycle-num
    (implies (and (equal (nfix cycle) (nfix ncycle))
                  (svex-env-boundp name x))
             (equal (svex-env-lookup (svex-cycle-var name ncycle)
                                     (svar-alist-add-cycle-num x cycle))
                    (svex-env-lookup name x)))
    :hints(("Goal" :in-theory (enable svar-alist-add-cycle-num svex-env-fix alist-keys
                                      equal-of-svex-cycle-var
                                      svex-env-lookup
                                      svex-env-boundp))))

  ;; Move!
  (defthm svex-env-boundp-of-nil
    (not (svex-env-boundp k nil))
    :hints(("Goal" :in-theory (enable svex-env-boundp))))


  (local (defthm svex-env-boundp-when-not-member
           (implies (not (member (svar-fix v) (alist-keys (svex-env-fix x))))
                    (not (svex-env-boundp v x)))
           :hints(("Goal" :in-theory (enable svex-env-boundp member-alist-keys)))))

  (defret member-cycle-var-of-svex-cycle-envs-to-single-env
    (implies (not (svarlist-has-svex-cycle-var (alist-keys (svex-env-fix rest))))
             (iff (svex-env-boundp (svex-cycle-var name cycle) env)
                  (and (<= (nfix curr-cycle) (nfix cycle))
                       (<= (- (nfix cycle) (nfix curr-cycle)) (len x))
                       (svex-env-boundp name (nth (- (nfix cycle) (nfix curr-cycle)) x))))))

  (local (defthm svex-env-lookup-when-not-member-keys
           (implies (not (svex-env-boundp v x))
                    (equal (svex-env-lookup v x) (4vec-x)))
           :hints(("Goal" :in-theory (enable svex-env-boundp svex-env-lookup)))))

  (defret lookup-in-svex-cycle-envs-to-single-env
    (implies (and (<= (nfix curr-cycle) (nfix cycle))
                  (<= (- (nfix cycle) (nfix curr-cycle)) (len x))
                  (not (svarlist-has-svex-cycle-var (alist-keys (svex-env-fix rest)))))
             (equal (svex-env-lookup (svex-cycle-var name cycle) env)
                    (svex-env-lookup name (nth (- (nfix cycle) (nfix curr-cycle)) x))))))



(defines svex-eval-unroll-multienv
  :prepwork ((local (Defthm svex-env-p-nth-of-envlist
                      (implies (svex-envlist-p x)
                               (svex-env-p (nth n x))))))
  :flag-local nil
  (define svex-eval-unroll-multienv ((x svex-p)
                                     (cycle natp)
                                     (nextstates svex-alist-p)
                                     (in-envs svex-envlist-p)
                                     (orig-state svex-env-p))
    :guard (< cycle (len in-envs))
    :measure (two-nats-measure cycle (svex-count x))
    :returns (new-x 4vec-p)
    :verify-guards nil
    (b* ((x (svex-fix x)))
      (svex-case x
        :quote x.val
        :var (b* ((look (svex-fastlookup x.name nextstates))
                  ((when look)
                   ;; state var
                   (if (zp cycle)
                       (svex-env-lookup x.name orig-state)
                     (svex-eval-unroll-multienv look (1- cycle) nextstates in-envs orig-state))))
               ;; input var
               (svex-env-lookup x.name (nth cycle (svex-envlist-fix in-envs))))
        :call (svex-apply x.fn (svexlist-eval-unroll-multienv x.args cycle nextstates in-envs orig-state)))))
  (define svexlist-eval-unroll-multienv ((x svexlist-p)
                                         (cycle natp)
                                         (nextstates svex-alist-p)
                                         (in-envs svex-envlist-p)
                                         (orig-state svex-env-p))
    :guard (< cycle (len in-envs))
    :measure (two-nats-measure cycle (svexlist-count x))
    :returns (new-x 4veclist-p)
    (if (atom x)
        nil
      (cons (svex-eval-unroll-multienv (car x) cycle nextstates in-envs orig-state)
            (svexlist-eval-unroll-multienv (cdr x) cycle nextstates in-envs orig-state))))
  ///
  (verify-guards svex-eval-unroll-multienv)
  ;; (local (defthm svex-env-lookup-of-append
  ;;          (equal (svex-env-lookup var (append a b))
  ;;                 (if (member (svar-fix var) (alist-keys (svex-env-fix a)))
  ;;                     (svex-env-lookup var a)
  ;;                   (svex-env-lookup var b)))
  ;;          :hints(("Goal" :in-theory (enable svex-env-lookup alist-keys hons-assoc-equal svex-env-fix)))))

  (defthm nth-of-svex-envlist-fix-under-svex-env-equiv
    (svex-env-equiv (nth n (svex-envlist-fix x))
                    (nth n x))
    :hints(("Goal" :in-theory (enable svex-envlist-fix nth))))

  (local (defthm nth-of-cons
           (Equal (nth n (cons a b))
                  (if (zp n)
                      a
                    (nth (+ -1 n) b)))))

  (local (in-theory (disable nth)))

  (deffixequiv-mutual svex-eval-unroll-multienv)


  (defthm-svex-eval-unroll-multienv-flag
    (defthm svex-eval-unroll-multienv-at-cycle-0
      (equal (svex-eval-unroll-multienv x 0 nextstates in-envs orig-state)
             (svex-eval x (append (svex-env-extract (svex-alist-keys nextstates)
                                                    orig-state)
                                  (car in-envs))))
      :hints ('(:expand ((svex-eval-unroll-multienv x 0 nextstates in-envs orig-state)
                         (:free (env) (svex-eval x env))
                         (nth 0 in-envs))))
      :flag svex-eval-unroll-multienv)
    (defthm svexlist-eval-unroll-multienv-at-cycle-0
      (equal (svexlist-eval-unroll-multienv x 0 nextstates in-envs orig-state)
             (svexlist-eval x (append (svex-env-extract (svex-alist-keys nextstates)
                                                        orig-state)
                                      (car in-envs))))
      :hints ('(:expand ((svexlist-eval-unroll-multienv x 0 nextstates in-envs orig-state)
                         (:free (env) (svexlist-eval x env)))))
      :flag svexlist-eval-unroll-multienv))

  (local (Defthm nth-of-nil
           (equal (nth n nil) nil)
           :hints(("Goal" :in-theory (enable nth)))))

  (defthm-svex-eval-unroll-multienv-flag
    (defthm svex-eval-unroll-multienv-expand-cycle
      (implies (posp cycle)
               (equal (svex-eval-unroll-multienv x cycle nextstates in-envs orig-state)
                      (svex-eval-unroll-multienv x (1- cycle)
                                                 nextstates
                                                 (cdr in-envs)
                                                 (svex-alist-eval nextstates
                                                                  (append (svex-env-extract (svex-alist-keys nextstates)
                                                                                            orig-state)
                                                                          (car in-envs))))))
      :hints ('(:expand ((:free (cycle in-envs orig-state)
                          (svex-eval-unroll-multienv x cycle nextstates in-envs orig-state))
                         (nth cycle in-envs))))
      :flag svex-eval-unroll-multienv)
    (defthm svexlist-eval-unroll-multienv-expand-cycle
      (implies (posp cycle)
               (equal (svexlist-eval-unroll-multienv x cycle nextstates in-envs orig-state)
                      (svexlist-eval-unroll-multienv x (1- cycle)
                                                     nextstates
                                                     (cdr in-envs)
                                                     (svex-alist-eval nextstates
                                                                      (append (svex-env-extract (svex-alist-keys nextstates)
                                                                                                orig-state)
                                                                              (car in-envs))))))
      :hints ('(:expand ((:free (cycle in-envs orig-state)
                          (svexlist-eval-unroll-multienv x cycle nextstates in-envs orig-state)))))
      :flag svexlist-eval-unroll-multienv))

  (in-theory (disable svex-eval-unroll-multienv-expand-cycle
                      svexlist-eval-unroll-multienv-expand-cycle
                      svex-eval-unroll-multienv-at-cycle-0
                      svexlist-eval-unroll-multienv-at-cycle-0)))


(local (in-theory (disable acl2::hons-dups-p)))

(defthm alist-keys-of-svex-alist-eval
  (equal (alist-keys (svex-alist-eval x env))
         (svex-alist-keys x))
  :hints(("Goal" :in-theory (enable svex-alist-keys svex-alist-eval alist-keys))))

;; (defthm svex-env-lookup-of-append
;;   (equal (svex-env-lookup v (append a b))
;;          (if (member (svar-fix v) (alist-keys (svex-env-fix a)))
;;              (svex-env-lookup v a)
;;            (svex-env-lookup v b)))
;;   :hints(("Goal" :in-theory (enable svex-env-lookup svex-env-fix alist-keys))))







(define svex-unroll-state ((nextstates svex-alist-p)
                           (in-envs svex-envlist-p)
                           (orig-state svex-env-p))
  :guard (and (equal (alist-keys orig-state)
                     (svex-alist-keys nextstates))
              (not (acl2::hons-dups-p (svex-alist-keys nextstates))))
  :returns (final-state svex-env-p)
  (b* ((curr-state (mbe :logic (svex-env-extract (svex-alist-keys nextstates) orig-state)
                        :exec orig-state))
       ((when (atom in-envs)) curr-state)
       (env (append curr-state (car in-envs))))
    (svex-unroll-state nextstates (cdr in-envs)
                       (with-fast-alist env (svex-alist-eval nextstates env))))
  ///

  (local (defthm alist-keys-of-svex-unroll-state
           (equal (alist-keys (svex-unroll-state nextstates in-envs orig-state))
                  (svex-alist-keys nextstates))))

  (defthm svex-env-boundp-of-svex-unroll-state
    (iff (svex-env-boundp key (svex-unroll-state nextstates in-envs orig-state))
         (svex-lookup key nextstates)))

  (local (in-theory (enable ;; svex-eval-unroll-multienv-expand-cycle
                     ;; svexlist-eval-unroll-multienv-expand-cycle
                     svex-eval-unroll-multienv-at-cycle-0
                     svexlist-eval-unroll-multienv-at-cycle-0)))

  (local (include-book "std/lists/take" :dir :system))

  (defthmd svex-unroll-state-unroll-backward
    (implies (consp in-envs)
             (equal (svex-unroll-state nextstates in-envs orig-state)
                    (svex-alist-eval (svex-alist-extract (svex-alist-keys nextstates)  nextstates)
                                     (append (svex-unroll-state nextstates (take (1- (len in-envs)) in-envs)
                                                                orig-state)
                                             (nth (1- (len in-envs)) in-envs))))))

  (local (defthm nth-of-take
           (implies (< (nfix n) (nfix m))
                    (equal (nth n (take m x)) (nth n x)))
           :hints(("Goal" :in-theory (enable nth)))))

  (defthm-svex-eval-unroll-multienv-flag
    (defthm svex-eval-unroll-multienv-in-terms-of-svex-unroll-state
      (equal (svex-eval-unroll-multienv x cycle nextstates in-envs orig-state)
             (svex-eval x (append (svex-unroll-state nextstates (take cycle in-envs) orig-state)
                                  (nth cycle in-envs))))
      :hints ('(:expand
                ((svex-eval-unroll-multienv x cycle nextstates in-envs orig-state)
                 (:free (env) (svex-eval x env))))
              (and stable-under-simplificationp
                   '(:in-theory (enable svex-unroll-state-unroll-backward))))
      :flag svex-eval-unroll-multienv)
    (defthm svexlist-eval-unroll-multienv-in-terms-of-svex-unroll-state
      (equal (svexlist-eval-unroll-multienv x cycle nextstates in-envs orig-state)
             (svexlist-eval x (append (svex-unroll-state nextstates (take cycle in-envs) orig-state)
                                      (nth cycle in-envs))))
      :hints ('(:expand
                ((svexlist-eval-unroll-multienv x cycle nextstates in-envs orig-state)
                 (:free (env) (svexlist-eval x env)))))
      :flag svexlist-eval-unroll-multienv))

  (local (include-book "std/lists/sets" :dir :system))

  (defthm svex-env-extract-states-from-unroll-state
    (equal (svex-env-extract (svex-alist-keys nextstate)
                             (svex-unroll-state nextstate ins prev-st))
           (svex-unroll-state nextstate ins prev-st))
    :hints(("Goal" :in-theory (enable svex-unroll-state))))

  (in-theory (disable svex-eval-unroll-multienv-in-terms-of-svex-unroll-state
                      svexlist-eval-unroll-multienv-in-terms-of-svex-unroll-state)))


(defines svex-eval-unroll
  (define svex-eval-unroll ((x svex-p)
                            (cycle natp)
                            (nextstates svex-alist-p)
                            (env svex-env-p))
    :measure (two-nats-measure cycle (svex-count x))
    :returns (new-x 4vec-p)
    :verify-guards nil
    (b* ((x (svex-fix x)))
      (svex-case x
        :quote x.val
        :var (b* ((look (svex-fastlookup x.name nextstates))
                  ((when look)
                   ;; state var
                   (if (zp cycle)
                       (svex-env-lookup x.name env)
                     (svex-eval-unroll look (1- cycle) nextstates env))))
               ;; input var
               (svex-env-lookup (svex-cycle-var x.name cycle) env))
        :call (svex-apply x.fn (svexlist-eval-unroll x.args cycle nextstates env)))))
  (define svexlist-eval-unroll ((x svexlist-p)
                                (cycle natp)
                                (nextstates svex-alist-p)
                                (env svex-env-p))
    :measure (two-nats-measure cycle (svexlist-count x))
    :returns (new-x 4veclist-p)
    (if (atom x)
        nil
      (cons (svex-eval-unroll (car x) cycle nextstates env)
            (svexlist-eval-unroll (cdr x) cycle nextstates env))))
  ///
  (verify-guards svex-eval-unroll)

  (local (defthm not-svex-cycle-var-when-lookup-in-noncycle
           (implies (and (svex-lookup v x)
                         (not (svarlist-has-svex-cycle-var (svex-alist-keys x))))
                    (not (svex-cycle-var-p v)))
           :hints(("Goal" :in-theory (enable svex-lookup svarlist-has-svex-cycle-var svex-alist-keys)))))

  (defthm-svex-eval-unroll-flag
    (defthm svex-eval-unroll-multienv-is-unroll
      (implies (and (<= (nfix cycle) (len in-envs))
                    (not (svarlist-has-svex-cycle-var (alist-keys (svex-env-fix orig-state))))
                    (not (svarlist-has-svex-cycle-var (svex-alist-keys nextstates))))
               (equal (svex-eval-unroll-multienv x cycle nextstates in-envs orig-state)
                      (svex-eval-unroll x cycle nextstates (svex-cycle-envs-to-single-env in-envs 0 orig-state))))
      :hints ('(:expand ((:free (cycle) (svex-eval-unroll-multienv x cycle nextstates in-envs orig-state))
                         (:free (env cycle) (svex-eval-unroll x cycle nextstates env)))
                :in-theory (disable svex-eval-unroll-multienv-at-cycle-0)))
      :flag svex-eval-unroll)
    (defthm svexlist-eval-unroll-multienv-is-unroll
      (implies (and (<= (nfix cycle) (len in-envs))
                    (not (svarlist-has-svex-cycle-var (alist-keys (svex-env-fix orig-state))))
                    (not (svarlist-has-svex-cycle-var (svex-alist-keys nextstates))))
               (equal (svexlist-eval-unroll-multienv x cycle nextstates in-envs orig-state)
                      (svexlist-eval-unroll x cycle nextstates (svex-cycle-envs-to-single-env in-envs 0 orig-state))))
      :hints ('(:expand ((svexlist-eval-unroll-multienv x cycle nextstates in-envs orig-state)
                         (:free (env) (svexlist-eval-unroll x cycle nextstates env)))))
      :flag svexlist-eval-unroll))


  (in-theory (disable svex-eval-unroll-multienv-is-unroll
                      svexlist-eval-unroll-multienv-is-unroll))

  (defthm-svex-eval-unroll-flag
    (defthm svex-eval-unroll-is-unroll-multienv
      (implies (and (bind-free '((ncycles . (binary-+ '1 (nfix cycle)))) (ncycles))
                    (< (nfix cycle) (nfix ncycles)))
               (equal (svex-eval-unroll x cycle nextstates env)
                      (svex-eval-unroll-multienv x cycle nextstates
                                                 (svex-env-to-cycle-envs env ncycles)
                                                 (svex-env-extract (svex-alist-keys nextstates) env))))
      :hints ('(:expand ((:free (cycle in-envs orig-state)
                          (svex-eval-unroll-multienv x cycle nextstates in-envs orig-state))
                         (:free (env cycle) (svex-eval-unroll x cycle nextstates env)))
                :in-theory (disable svex-eval-unroll-multienv-at-cycle-0)))
      :flag svex-eval-unroll)
    (defthm svexlist-eval-unroll-is-unroll-multienv
      (implies (and (bind-free '((ncycles . (binary-+ '1 (nfix cycle)))) (ncycles))
                    (< (nfix cycle) (nfix ncycles)))
               (equal (svexlist-eval-unroll x cycle nextstates env)
                      (svexlist-eval-unroll-multienv x cycle nextstates
                                                     (svex-env-to-cycle-envs env ncycles)
                                                     (svex-env-extract (svex-alist-keys nextstates) env))))
      :hints ('(:expand ((:free (in-envs orig-state)
                          (svexlist-eval-unroll-multienv x cycle nextstates in-envs orig-state))
                         (:free (env) (svexlist-eval-unroll x cycle nextstates env)))))
      :flag svexlist-eval-unroll))

  (in-theory (disable svex-eval-unroll-is-unroll-multienv
                      svexlist-eval-unroll-is-unroll-multienv))

  (deffixequiv-mutual svex-eval-unroll))


(defines svex-compose-unroll
  (define svex-compose-unroll ((x svex-p)
                               (cycle natp)
                               (nextstates svex-alist-p))
    :measure (two-nats-measure cycle (svex-count x))
    :returns (new-x svex-p)
    :verify-guards nil
    (b* ((x (svex-fix x)))
      (svex-case x
        :quote x
        :var (b* ((look (svex-fastlookup x.name nextstates))
                  ((when look)
                   ;; state var
                   (if (zp cycle)
                       x
                     (svex-compose-unroll look (1- cycle) nextstates))))
               ;; input var
               (svex-var (svex-cycle-var x.name cycle)))
        :call (svex-call x.fn (svexlist-compose-unroll x.args cycle nextstates)))))
  (define svexlist-compose-unroll ((x svexlist-p)
                                   (cycle natp)
                                   (nextstates svex-alist-p))
    :measure (two-nats-measure cycle (svexlist-count x))
    :returns (new-x svexlist-p)
    (if (atom x)
        nil
      (cons (svex-compose-unroll (car x) cycle nextstates)
            (svexlist-compose-unroll (cdr x) cycle nextstates))))
  ///
  (verify-guards svex-compose-unroll)
  (memoize 'svex-compose-unroll :condition '(not (svex-case x :quote)))

  (defthm-svex-compose-unroll-flag
    (defthm svex-compose-unroll-correct
      (equal (svex-eval (svex-compose-unroll x cycle nextstates) env)
             (svex-eval-unroll x cycle nextstates env))
      :hints ('(:expand ((:free (cycle) (svex-compose-unroll x cycle nextstates))
                         (:free (cycle) (svex-eval-unroll x cycle nextstates env))))
              (and stable-under-simplificationp
                   '(:in-theory (enable svex-eval))))
      :flag svex-compose-unroll)
    (defthm svexlist-compose-unroll-correct
      (equal (svexlist-eval (svexlist-compose-unroll x cycle nextstates) env)
             (svexlist-eval-unroll x cycle nextstates env))
      :hints ('(:expand ((svexlist-compose-unroll x cycle nextstates)
                         (svexlist-eval-unroll x cycle nextstates env))))
      :flag svexlist-compose-unroll))

  (deffixequiv-mutual svex-compose-unroll))


(defines svex-compose*-unroll
  (define svex-compose*-unroll ((x svex-p)
                               (cycle natp)
                               (nextstates svex-alist-p))
    :measure (two-nats-measure cycle (svex-count x))
    :returns (new-x svex-p)
    :verify-guards nil
    (b* ((x (svex-fix x)))
      (svex-case x
        :quote x
        :var (b* ((look (svex-fastlookup x.name nextstates))
                  ((when look)
                   ;; state var
                   (if (zp cycle)
                       x
                     (svex-compose*-unroll look (1- cycle) nextstates))))
               ;; input var
               (svex-var (svex-cycle-var x.name cycle)))
        :call (svex-call* x.fn (svexlist-compose*-unroll x.args cycle nextstates)))))
  (define svexlist-compose*-unroll ((x svexlist-p)
                                   (cycle natp)
                                   (nextstates svex-alist-p))
    :measure (two-nats-measure cycle (svexlist-count x))
    :returns (new-x svexlist-p)
    (if (atom x)
        nil
      (cons (svex-compose*-unroll (car x) cycle nextstates)
            (svexlist-compose*-unroll (cdr x) cycle nextstates))))
  ///
  (verify-guards svex-compose*-unroll)
  (memoize 'svex-compose*-unroll :condition '(not (svex-case x :quote)))

  (defthm-svex-compose*-unroll-flag
    (defthm svex-compose*-unroll-correct
      (equal (svex-eval (svex-compose*-unroll x cycle nextstates) env)
             (svex-eval-unroll x cycle nextstates env))
      :hints ('(:expand ((svex-compose*-unroll x cycle nextstates)
                         (:free (cycle) (svex-eval-unroll x cycle nextstates env))))
              (and stable-under-simplificationp
                   '(:in-theory (enable svex-eval))))
      :flag svex-compose*-unroll)
    (defthm svexlist-compose*-unroll-correct
      (equal (svexlist-eval (svexlist-compose*-unroll x cycle nextstates) env)
             (svexlist-eval-unroll x cycle nextstates env))
      :hints ('(:expand ((svexlist-compose*-unroll x cycle nextstates)
                         (svexlist-eval-unroll x cycle nextstates env))))
      :flag svexlist-compose*-unroll))

  (deffixequiv-mutual svex-compose*-unroll))




