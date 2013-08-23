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

;; Obsolete
(include-book "gobjectp")

;; (encapsulate
;;   nil

;;   (local (defthm nth-open1
;;            (equal (nth n x)
;;                   (and (consp x)
;;                        (if (zp n)
;;                            (car x)
;;                          (nth (1- n) (cdr x)))))))

;;   (local (defthm equal-len-0
;;            (equal (equal (len x) 0)
;;                   (not (consp x)))))

;;   (defthm wf-g-numberp-simpler-def
;;     (equal (wf-g-numberp x)
;;            (and (true-listp x)
;;                 (consp x)
;;                 (<= (len x) 4)
;;                 (bfr-listp (nth 0 x))
;;                 (bfr-listp (nth 1 x))
;;                 (bfr-listp (nth 2 x))
;;                 (bfr-listp (nth 3 x))))
;;     :hints (("goal" :do-not-induct t
;;              :in-theory (enable wf-g-numberp)))
;;     :rule-classes :definition))

;; (defthm wf-g-numberp-true-listp
;;   (implies (wf-g-numberp x)
;;            (true-listp x))
;;   :rule-classes :compound-recognizer)

;; (in-theory (disable wf-g-numberp-simpler-def))




;; (defthmd gobject-hierarchy-impl-not-g-keyword-symbolp
;;   (implies (gobject-hierarchy x)
;;            (not (g-keyword-symbolp x)))
;;   :hints(("Goal" :in-theory (enable gobject-hierarchy))))


;; (defthm gobjectp-def
;;   (equal (gobjectp x)
;;          (if (atom x)
;;              (not (g-keyword-symbolp x))
;;            (cond
;;             ((g-concrete-p x))
;;             ((g-boolean-p x)   (bfr-p (g-boolean->bool x)))
;;             ((g-number-p x)    (wf-g-numberp (g-number->num x)))
;;             ((g-ite-p x)       (and (gobjectp (g-ite->test x))
;;                                     (gobjectp (g-ite->then x))
;;                                     (gobjectp (g-ite->else x))))
;;             ((g-apply-p x)     (and (symbolp (g-apply->fn x))
;;                                     (gobjectp (g-apply->args x))))
;;             ((g-var-p x))
;;             (t (and (gobjectp (car x))
;;                     (gobjectp (cdr x)))))))
;;   :hints(("Goal" :in-theory (enable gobjectp gobject-hierarchy)))
;;   :rule-classes :definition)



;; (defun gobjectp-ind (x)
;;   (if (atom x)
;;       x
;;     (cond
;;      ((g-concrete-p x))
;;      ((g-boolean-p x))
;;      ((g-number-p x)    (wf-g-numberp (g-number->num x)))
;;      ((g-ite-p x)       (list (gobjectp-ind (g-ite->test x))
;;                               (gobjectp-ind (g-ite->then x))
;;                               (gobjectp-ind (g-ite->else x))))
;;      ((g-apply-p x)     (list (symbolp (g-apply->fn x))
;;                               (gobjectp-ind (g-apply->args x))))
;;      ((g-var-p x))
;;      (t (list (gobjectp-ind (car x))
;;               (gobjectp-ind (cdr x)))))))

;; (defthm gobjectp-induct
;;   t
;;   :rule-classes ((:induction
;;                   :pattern (gobjectp x)
;;                   :scheme (gobjectp-ind x))))




;; (defthm gobjectp-tag-rw-to-types
;;   (implies (gobjectp x)
;;            (and (equal (equal (tag x) :g-concrete)
;;                        (g-concrete-p x))
;;                 (equal (equal (tag x) :g-boolean)
;;                        (g-boolean-p x))
;;                 (equal (equal (tag x) :g-number)
;;                        (g-number-p x))
;;                 (equal (equal (tag x) :g-ite)
;;                        (g-ite-p x))
;;                 (equal (equal (tag x) :g-apply)
;;                        (g-apply-p x))
;;                 (equal (equal (tag x) :g-var)
;;                        (g-var-p x))))
;;   :hints (("goal" :expand ((gobjectp x))
;;            :do-not-induct t)
;;           (and stable-under-simplificationp
;;                '(:in-theory (enable tag g-keyword-symbolp-def))))
;;   :otf-flg t)



;; (defthm gobjectp-ite-case
;;   (implies (and (gobjectp x)
;;                 (g-ite-p x))
;;            (and (gobjectp (g-ite->test x))
;;                 (gobjectp (g-ite->then x))
;;                 (gobjectp (g-ite->else x)))))

;; (defthm gobjectp-number-case
;;   (implies (and (gobjectp x)
;;                 (g-number-p x))
;;            (wf-g-numberp (g-number->num x))))
           

;; (defthm gobjectp-boolean-case
;;   (implies (and (gobjectp x)
;;                 (g-boolean-p x))
;;            (bfr-p (g-boolean->bool x))))

;; (defthm gobjectp-apply-case
;;   (implies (and (gobjectp x)
;;                 (g-apply-p x))
;;            (and (symbolp (g-apply->fn x))
;;                 (gobjectp (g-apply->args x)))))



;; (defthm gobjectp-cons-case
;;   (implies (and (gobjectp x)
;;                 (consp x)
;;                 (not (g-boolean-p x))
;;                 (not (g-number-p x))
;;                 (not (g-concrete-p x))
;;                 (not (g-ite-p x))
;;                 (not (g-apply-p x))
;;                 (not (g-var-p x)))
;;            (and (gobjectp (car x))
;;                 (gobjectp (cdr x)))))



;; (defthm gobjectp-gobj-fix
;;   (gobjectp (gobj-fix x))
;;   :hints(("Goal" :in-theory (enable gobjectp gobject-hierarchy gobj-fix))))

;; (defthm gobj-fix-when-gobjectp
;;   (implies (gobjectp x)
;;            (equal (gobj-fix x) x))
;;   :hints(("Goal" :in-theory (enable gobj-fix))))

;; (defthm gobj-fix-when-not-gobjectp
;;   (implies (not (gobjectp x))
;;            (equal (gobj-fix x)
;;                   (g-concrete x)))
;;   :hints(("Goal" :in-theory (enable gobj-fix))))


;; (defthm gobj-equiv-gobj-fix
;;   (gobj-equiv (gobj-fix x) x))

;; (table prove-congruence-theory-table
;;        'gobj-equiv '(gobjectp-gobj-fix gobj-fix-when-gobjectp))




;; (defthmd gobjectp-car-impl-not-g-types
;;   (implies (gobjectp (car x))
;;            (and (not (g-boolean-p x))
;;                 (not (g-number-p x))
;;                 (not (g-concrete-p x))
;;                 (not (g-ite-p x))
;;                 (not (g-apply-p x))
;;                 (not (g-var-p x))))
;;   :hints(("Goal" :in-theory (enable g-boolean-p
;;                                     g-number-p
;;                                     g-concrete-p
;;                                     g-ite-p
;;                                     g-apply-p
;;                                     g-var-p))))

;; (defthmd gobject-listp-impl-gobjectp
;;   (implies (gobject-listp x)
;;            (gobjectp x))
;;   :hints(("Goal" :in-theory
;;           (enable gobjectp-car-impl-not-g-types
;;                   gobjectp-def gobject-listp))))




;; (defthmd gobject-hierarchy-possibilities
;;   (implies (and (gobject-hierarchy x)
;;                 (not (equal (gobject-hierarchy x) 'gobject))
;;                 (not (equal (gobject-hierarchy x) 'general)))
;;            (equal (equal (gobject-hierarchy x) 'concrete) t))
;;   :hints(("Goal" :in-theory (enable gobject-hierarchy)))
;;   :rule-classes ((:rewrite :backchain-limit-lst 0)))


;; (in-theory (disable gobjectp-def))
