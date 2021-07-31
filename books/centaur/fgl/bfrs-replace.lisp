; FGL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2021 Centaur Technology
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
(include-book "logicman")


(defines fgl-object-replace-bfrlist
  (define fgl-object-replace-bfrlist ((x fgl-object-p)
                                      (bfrs true-listp))
    :measure (acl2::two-nats-measure (fgl-object-count x) 0)
    ;; :guard (<= (len (fgl-object-bfrlist x)) (len bfrs))
    :verify-guards nil
    :returns (mv (new-x fgl-object-p)
                 (rest-bfrs true-listp))
    (b* ((x (fgl-object-fix x))
         (bfrs (true-list-fix bfrs)))
      (fgl-object-case x
        :g-concrete (mv x bfrs)
        :g-boolean (mv (g-boolean (car bfrs)) (cdr bfrs))
        :g-integer (b* ((len (len x.bits)))
                     (mv (g-integer (take len bfrs))
                         (nthcdr len bfrs)))
        :g-ite (b* (((mv test bfrs) (fgl-object-replace-bfrlist x.test bfrs))
                    ((mv then bfrs) (fgl-object-replace-bfrlist x.then bfrs))
                    ((mv else bfrs) (fgl-object-replace-bfrlist x.else bfrs)))
                 (mv (g-ite test then else) bfrs))
        :g-apply (b* (((mv args bfrs) (fgl-objectlist-replace-bfrlist x.args bfrs)))
                   (mv (g-apply x.fn args) bfrs))
        :g-var (mv x bfrs)
        :g-cons (b* (((mv car bfrs) (fgl-object-replace-bfrlist x.car bfrs))
                     ((mv cdr bfrs) (fgl-object-replace-bfrlist x.cdr bfrs)))
                  (mv (g-cons car cdr) bfrs))
        :g-map (b* (((mv alist bfrs) (fgl-object-alist-replace-bfrlist x.alist bfrs)))
                 (mv (change-g-map x :alist alist) bfrs)))))

  (define fgl-objectlist-replace-bfrlist ((x fgl-objectlist-p)
                                          (bfrs true-listp))
    :measure (acl2::two-nats-measure (fgl-objectlist-count x) 0)
    :returns (mv (new-x fgl-objectlist-p)
                 (rest-bfrs true-listp))
    (b* (((when (atom x))
          (mv nil (true-list-fix bfrs)))
         ((mv car bfrs) (fgl-object-replace-bfrlist (car x) bfrs))
         ((mv cdr bfrs) (fgl-objectlist-replace-bfrlist (cdr x) bfrs)))
      (mv (cons car cdr) bfrs)))

  (define fgl-object-alist-replace-bfrlist ((x fgl-object-alist-p)
                                            (bfrs true-listp))
    :measure (acl2::two-nats-measure (fgl-object-alist-count x) (len x))
    :returns (mv (new-x fgl-object-alist-p)
                 (rest-bfrs true-listp))
    (b* (((when (atom x))
          (mv x (true-list-fix bfrs)))
         ((unless (mbt (consp (car x))))
          (fgl-object-alist-replace-bfrlist (cdr x) bfrs))
         ((mv val1 bfrs) (fgl-object-replace-bfrlist (cdar x) bfrs))
         ((mv cdr bfrs) (fgl-object-alist-replace-bfrlist (cdr x) bfrs)))
      (mv (cons (cons (caar x) val1) cdr) bfrs)))
  ///

  (local (defthm nthcdr-of-equal-nthcdr
           (implies (equal x (nthcdr n y))
                    (equal (nthcdr m x)
                           (nthcdr (+ (nfix n) (nfix m)) y)))))

  (local (defthm append-take-take-nthcdr-free
           (implies (equal y (nthcdr n (true-list-fix x)))
                    (equal (append (take n x)
                                   (take m y))
                           (take (+ (nfix n) (nfix m)) x)))
           :hints (("goal" :induct (take n x)
                    :expand ((nthcdr n x))))))

  (defret-mutual bfrlist-of-<fn>
    (defret bfrlist-of-<fn>
      (and (equal (fgl-object-bfrlist new-x)
                  (take (len (fgl-object-bfrlist x)) bfrs))
           (equal rest-bfrs
                  (nthcdr (len (fgl-object-bfrlist x)) (true-list-fix bfrs))))
      :hints ('(:expand (<call>
                         (fgl-object-bfrlist x))))
      :fn fgl-object-replace-bfrlist)

    (defret bfrlist-of-<fn>
      (and (equal (fgl-objectlist-bfrlist new-x)
                  (take (len (fgl-objectlist-bfrlist x)) bfrs))
           (equal rest-bfrs
                  (nthcdr (len (fgl-objectlist-bfrlist x)) (true-list-fix bfrs))))
      :hints ('(:expand (<call>
                         (fgl-objectlist-bfrlist x))))
      :fn fgl-objectlist-replace-bfrlist)

    (defret bfrlist-of-<fn>
      (and (equal (fgl-object-alist-bfrlist new-x)
                  (take (len (fgl-object-alist-bfrlist x)) bfrs))
           (equal rest-bfrs
                  (nthcdr (len (fgl-object-alist-bfrlist x)) (true-list-fix bfrs))))
      :hints ('(:expand (<call>
                         (fgl-object-alist-bfrlist x))))
      :fn fgl-object-alist-replace-bfrlist))

  (local (defthm bfr-list-eval-of-cons
           (equal (bfr-list-eval (cons x y) env logicman)
                  (cons (bfr-eval x env logicman)
                        (bfr-list-eval y env logicman)))
           :hints(("Goal" :in-theory (enable bfr-list-eval)))))

  (local (defthm bfr-list-eval-of-append
           (equal (bfr-list-eval (append x y) env logicman)
                  (append (bfr-list-eval x env logicman)
                          (bfr-list-eval y env logicman)))
           :hints(("Goal" :in-theory (enable bfr-list-eval)))))

  ;; (local (in-theory (disable acl2::take-of-too-many
  ;;                            acl2::take-when-atom)))

  (local (defthm bfr-list-eval-of-repeat
           (equal (bfr-list-eval (acl2::repeat n x) env logicman)
                  (acl2::repeat n (bfr-eval x env logicman)))
           :hints(("Goal" :in-theory (enable bfr-list-eval acl2::repeat)))))

  (local (defthm bfr-list-eval-of-take
           (equal (bfr-list-eval (take n x) env logicman)
                  (take n (bfr-list-eval x env logicman)))
           :hints(("Goal" :in-theory (enable bfr-list-eval)))))

  (local (defthm nthcdr-of-nil
           (equal (nthcdr n nil) nil)))

  (local (defthm bfr-list-eval-of-nthcdr
           (equal (bfr-list-eval (nthcdr n x) env logicman)
                  (nthcdr n (bfr-list-eval x env logicman)))
           :hints(("Goal" :in-theory (enable bfr-list-eval)))))

  (local (defun ind (x y)
           (if (atom x)
               y
             (ind (cdr x) (cdr y)))))

  (local (defthm equal-of-append
           (equal (equal x (append y z))
                  (and (<= (len y) (len x))
                       (equal (take (len y) x) (true-list-fix y))
                       (equal (nthcdr (len y) x) z)))
           :hints(("Goal" :induct (ind x y)))))

  (local (defthm nthcdr-less-of-take
           (implies (<= (nfix n) (nfix m))
                    (equal (nthcdr n (take m x))
                           (take (- (nfix m) (nfix n)) (nthcdr n x))))))
                  
  (local (defthm cancel-blah
           (equal (+ x (- x) y)
                  (fix y))))

  (local (defthm len-of-bfr-list-eval
           (equal (len (bfr-list-eval x env logicman))
                  (len x))
           :hints(("Goal" :in-theory (enable bfr-list-eval)))))

  (local (Defthm bfr-list-eval-of-nil
           (equal (Bfr-list-eval nil env logicman)
                  nil)
           :hints(("Goal" :in-theory (enable bfr-list-eval)))))

  (local (defthm car-of-bfr-list-eval
           (equal (car (bfr-list-eval bfrs env logicman))
                  (and (consp bfrs)
                       (bfr-eval (car bfrs) env logicman)))
           :hints(("Goal" :in-theory (enable bfr-list-eval)))))

  (local (defthm true-list-fix-of-nthcdr
           (equal (true-list-fix (nthcdr n x))
                  (nthcdr n (true-list-fix x)))))
           

  (local (in-theory (enable gobj-bfr-list-eval-is-bfr-list-eval gobj-bfr-eval)))

  (defret-mutual eval-of-<fn>
    (defret eval-of-<fn>
      (b* ((orig-bfrs (fgl-object-bfrlist x))
           (bfr-env (fgl-env->bfr-vals env)))
        (implies (equal (bfr-list-eval (take (len orig-bfrs) bfrs) bfr-env logicman)
                        (bfr-list-eval orig-bfrs bfr-env logicman))
                 (equal (fgl-object-eval new-x env logicman)
                        (fgl-object-eval x env logicman))))
      :hints ('(:expand (<call>
                         (fgl-object-bfrlist x)
                         (fgl-object-eval x env logicman))))
      :fn fgl-object-replace-bfrlist)

    (defret eval-of-<fn>
      (b* ((orig-bfrs (fgl-objectlist-bfrlist x))
           (bfr-env (fgl-env->bfr-vals env)))
        (implies (equal (bfr-list-eval (take (len orig-bfrs) bfrs) bfr-env logicman)
                        (bfr-list-eval orig-bfrs bfr-env logicman))
                 (equal (fgl-objectlist-eval new-x env logicman)
                        (fgl-objectlist-eval x env logicman))))
      :hints ('(:expand (<call>
                         (fgl-objectlist-bfrlist x)
                         (fgl-objectlist-eval x env logicman))))
      :fn fgl-objectlist-replace-bfrlist)

    (defret eval-of-<fn>
      (b* ((orig-bfrs (fgl-object-alist-bfrlist x))
           (bfr-env (fgl-env->bfr-vals env)))
        (implies (equal (bfr-list-eval (take (len orig-bfrs) bfrs) bfr-env logicman)
                        (bfr-list-eval orig-bfrs bfr-env logicman))
                 (equal (fgl-object-alist-eval new-x env logicman)
                        (fgl-object-alist-eval x env logicman))))
      :hints ('(:expand (<call>
                         (fgl-object-alist-bfrlist x)
                         (fgl-object-alist-eval x env logicman))))
      :fn fgl-object-alist-replace-bfrlist))

  (verify-guards fgl-object-replace-bfrlist))


      
