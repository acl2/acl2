; GL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2008-2013 Centaur Technology
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

(in-package "GL")
(include-book "gtypes")
(local (include-book "gtype-thms"))
(local (include-book "tools/mv-nth" :dir :system))

(defun hide-if (x) x)

(defund gl-args-split-ite-cond (test args)
  (declare (xargs :guard t))
  (b* (((when (atom args)) (mv nil nil))
       (obj (car args))
       ((mv rest-then rest-else)
        (gl-args-split-ite-cond test (cdr args)))
       ((when (and (consp obj)
                   (eq (tag obj) :g-ite)
                   (hons-equal (g-ite->test obj) test)))
        (mv (cons (g-ite->then obj) rest-then)
            (cons (g-ite->else obj) rest-else))))
    (mv (cons obj rest-then)
        (cons obj rest-else))))


(defund gl-args-split-ite (args)
  (declare (xargs :guard t))
  (b* (((when (atom args))
        (mv nil nil nil nil))
       (obj (car args))
       ((when (and (consp obj)
                   (eq (tag obj) :g-ite)))
        (b* ((test (g-ite->test obj))
             (then (g-ite->then obj))
             (else (g-ite->else obj))
             ((mv then-rest else-rest)
              (gl-args-split-ite-cond test (cdr args))))
          (mv t test (cons then then-rest) (cons else else-rest))))
       ((mv has-if test then else)
        (gl-args-split-ite (cdr args)))
       ((unless has-if)
        (mv nil nil nil nil)))
    (mv has-if test (cons obj then) (cons obj else))))

(defund g-ite-depth (x)
  (declare (xargs :guard t))
  (if (mbe :logic (eq (tag x) :g-ite)
           :exec (and (consp x)
                      (eq (tag x) :g-ite)))
      (+ 1 (max (g-ite-depth (g-ite->then x))
                (g-ite-depth (g-ite->else x))))
    0))

(defthm posp-g-ite-depth
  (implies (equal (tag x) :g-ite)
           (posp (g-ite-depth x)))
  :hints(("Goal" :in-theory (enable g-ite-depth)))
  :rule-classes :type-prescription)


(defthm g-ite-depth-of-g-ite->then
  (implies (eq (tag x) :g-ite)
           (< (g-ite-depth (g-ite->then x))
              (g-ite-depth x)))
  :hints(("Goal" :expand ((g-ite-depth x))))
  :rule-classes :linear)

(defthm g-ite-depth-of-g-ite->else
  (implies (eq (tag x) :g-ite)
           (< (g-ite-depth (g-ite->else x))
              (g-ite-depth x)))
  :hints(("Goal" :expand ((g-ite-depth x))))
  :rule-classes :linear)

(defund g-ite-depth-sum (x)
  (declare (xargs :guard t))
  (if (atom x)
      0
    (+ (g-ite-depth (car x))
       (g-ite-depth-sum (cdr x)))))

(defthm g-ite-depth-of-g-concrete
  (equal (g-ite-depth (g-concrete x)) 0)
  :hints(("Goal" :in-theory (enable g-ite-depth))))

(defthm g-ite-depth-sum-of-gl-args-split-ite-cond-0
  (<= (g-ite-depth-sum (mv-nth 0 (gl-args-split-ite-cond test args)))
      (g-ite-depth-sum args))
  :hints(("Goal" :in-theory (enable gl-args-split-ite-cond
                                    g-ite-depth-sum gl-cons)))
  :rule-classes :linear)

(defthm g-ite-depth-sum-of-gl-args-split-ite-cond-1
  (<= (g-ite-depth-sum (mv-nth 1 (gl-args-split-ite-cond test args)))
      (g-ite-depth-sum args))
  :hints(("Goal" :in-theory (enable gl-args-split-ite-cond
                                    g-ite-depth-sum gl-cons)))
  :rule-classes :linear)

(defthm g-ite-depth-sum-of-gl-args-split-ite-then
  (b* (((mv has-ite ?test ?then ?else)
        (gl-args-split-ite args)))
    (implies has-ite
             (< (g-ite-depth-sum then) (g-ite-depth-sum args))))
  :hints(("Goal" :in-theory (enable gl-args-split-ite
                                    g-ite-depth-sum gl-cons)))
  :rule-classes :linear)

(defthm g-ite-depth-sum-of-gl-args-split-ite-else
  (b* (((mv has-ite ?test ?then ?else)
        (gl-args-split-ite args)))
    (implies has-ite
             (< (g-ite-depth-sum else) (g-ite-depth-sum args))))
  :hints(("Goal" :in-theory (enable gl-args-split-ite
                                    g-ite-depth-sum gl-cons)))
  :rule-classes :linear)





(defsection gl-args-split-ite-cond
  (local (in-theory (enable gl-args-split-ite-cond)))

  (defthm gl-args-split-ite-cond-correct
    (b* (((mv then else)
          (gl-args-split-ite-cond test args)))
      (and (implies (generic-geval test env)
                    (equal (generic-geval-list then env)
                           (generic-geval-list args env)))
           (implies (not (generic-geval test env))
                    (equal (generic-geval-list else env)
                           (generic-geval-list args env)))))
    :hints (("goal" :induct (gl-args-split-ite-cond test args)
             :expand ((generic-geval-list args env)
                      (generic-geval-list nil env)
                      (:free (a b) (generic-geval-list (cons a b) env))
                      (:with generic-geval (generic-geval (car args)
                                                                    env))))))

  (defthm gobj-listp-gl-args-split-ite-cond
    (b* (((mv then else)
          (gl-args-split-ite-cond test args)))
      (and (true-listp then)
           (true-listp else))))

  (defthm gobj-list-depends-on-of-gl-args-split-ite-cond
    (b* (((mv then else)
          (gl-args-split-ite-cond test args)))
      (implies (not (gobj-list-depends-on k p args))
               (and (not (gobj-list-depends-on k p then))
                    (not (gobj-list-depends-on k p else)))))))

(defsection gl-args-split-ite
  (local (in-theory (enable gl-args-split-ite)))

  (defthm gl-args-split-ite-correct
    (b* (((mv has-ite test then else)
          (gl-args-split-ite args)))
      (implies has-ite
               (and (implies (generic-geval test env)
                             (equal (generic-geval-list then env)
                                    (generic-geval-list args env)))
                    (implies (not (generic-geval test env))
                             (equal (generic-geval-list else env)
                                    (generic-geval-list args env))))))
    :hints (("goal"
             :induct (gl-args-split-ite args)
             :expand ((generic-geval-list args env)
                      (generic-geval-list nil env)
                      (:free (a b) (generic-geval-list (cons a b) env))
                      (gobj-listp args)
                      (:with generic-geval (generic-geval (car args) env))))))

  (defthm gobj-listp-gl-args-split-ite
    (b* (((mv ?has-ite ?test then else)
          (gl-args-split-ite args)))
      (and (true-listp then)
           (true-listp else))))


  (defthm gobj-list-depends-on-of-gl-args-split-ite
    (b* (((mv ?has-if test then else)
          (gl-args-split-ite args)))
      (implies (not (gobj-list-depends-on k p args))
               (and (not (gobj-depends-on k p test))
                    (not (gobj-list-depends-on k p then))
                    (not (gobj-list-depends-on k p else)))))))



(defsection gl-fncall-split-ite
  (defun debug-fncall-split-ite (fn args)
    (declare (xargs :guard t)
             (ignore fn args))
    nil)

  (defund gl-fncall-split-ite (fn args)
    (declare (xargs :guard t
                    :measure (g-ite-depth-sum args)))
    (b* (((mv has-ite test then else)
          (gl-args-split-ite args))
         ((unless has-ite) (g-apply fn args)))
      (debug-fncall-split-ite fn args)
      (g-ite test
             (gl-fncall-split-ite fn then)
             (gl-fncall-split-ite fn else))))

  (local (in-theory (enable gl-fncall-split-ite)))

  (defthm gl-fncall-split-ite-correct
    (equal (generic-geval (gl-fncall-split-ite fn args) env)
           (generic-geval (g-apply fn args) env))
    :hints(("Goal" :in-theory (enable generic-geval))))

  (defthm gobj-depends-on-of-gl-args-split-ite
    (implies (not (gobj-list-depends-on k p args))
             (not (gobj-depends-on k p (gl-fncall-split-ite fn args))))))

(defsection gl-cons-split-ite
  (defun debug-cons-split-ite (car cdr)
    (declare (xargs :guard t)
             (ignore car cdr))
    nil)
  (defund gl-cons-split-ite (car cdr)
    (declare (xargs :guard t
                    :hints(("Goal" :in-theory (enable g-ite-depth-sum)))
                    :measure (g-ite-depth-sum (list car cdr))))
    (if (and (not (and (consp car) (eq (tag car) :g-ite)))
             (not (and (consp cdr) (eq (tag cdr) :g-ite))))
        (gl-cons car cdr)
      (progn$
       (debug-cons-split-ite car cdr)
       ;; (break$)
       (if (and (consp car) (eq (tag car) :g-ite))
           (if (and (consp cdr)
                    (eq (tag cdr) :g-ite)
                    (hons-equal (g-ite->test cdr) (g-ite->test car)))
               (g-ite (g-ite->test car)
                      (gl-cons-split-ite (g-ite->then car)
                                         (g-ite->then cdr))
                      (gl-cons-split-ite (g-ite->else car)
                                         (g-ite->else cdr)))
             (g-ite (g-ite->test car)
                    (gl-cons-split-ite (g-ite->then car) cdr)
                    (gl-cons-split-ite (g-ite->else car) cdr)))
         (g-ite (g-ite->test cdr)
                (gl-cons-split-ite car (g-ite->then cdr))
                (gl-cons-split-ite car (g-ite->else cdr)))))))

  (local (in-theory (enable gl-cons-split-ite)))

  (defthm gl-cons-split-ite-correct
    (equal (generic-geval (gl-cons-split-ite car cdr) env)
           (cons (generic-geval car env)
                 (generic-geval cdr env)))
    :hints(("Goal" :in-theory (e/d (generic-geval) (gl-cons)))))

  (defthm gobj-depends-on-of-gl-cons-split-ite
    (implies (and (not (gobj-depends-on k p car))
                  (not (gobj-depends-on k p cdr)))
             (not (gobj-depends-on k p (gl-cons-split-ite car cdr))))
    :hints(("Goal" :in-theory (e/d () (gl-cons gobj-depends-on))))))


(defsection gl-cons-maybe-split
  (defund gl-cons-maybe-split (car cdr split-flg w)
    (declare (xargs :guard (plist-worldp w)))
    (if (and split-flg
             (not (cdr (hons-assoc-equal 'cons (table-alist 'gl-if-opaque-fns w)))))
        (gl-cons-split-ite car cdr)
      (gl-cons car cdr)))

  (local (in-theory (enable gl-cons-maybe-split)))

  (defthm gl-cons-maybe-split-correct
    (equal (generic-geval (gl-cons-maybe-split car cdr flg w) env)
           (cons (generic-geval car env)
                 (generic-geval cdr env)))
    :hints(("Goal" :in-theory (e/d (generic-geval) (gl-cons)))))

  (defthm gobj-depends-on-of-gl-cons-maybe-split
    (implies (and (not (gobj-depends-on k p car))
                  (not (gobj-depends-on k p cdr)))
             (not (gobj-depends-on k p (gl-cons-maybe-split car cdr flg w))))
    :hints(("Goal" :in-theory (e/d () (gl-cons gobj-depends-on))))))

(defsection gl-fncall-maybe-split

  (defund gl-fncall-maybe-split (fn args flg w)
    (declare (xargs :guard (plist-worldp w)))
    (if (and flg
             (not (cdr (hons-assoc-equal 'fn (table-alist 'gl-if-opaque-fns w)))))
        (gl-fncall-split-ite fn args)
      (g-apply fn args)))

  (local (in-theory (enable gl-fncall-maybe-split)))

  (defthm gl-fncall-maybe-split-correct
    (equal (generic-geval (gl-fncall-maybe-split fn args flg w) env)
           (generic-geval (g-apply fn args) env))
    :hints(("Goal" :in-theory (enable generic-geval))))

  (defthm gobj-depends-on-of-gl-args-maybe-split
    (implies (not (gobj-list-depends-on k p args))
             (not (gobj-depends-on k p (gl-fncall-maybe-split fn args flg w))))))

