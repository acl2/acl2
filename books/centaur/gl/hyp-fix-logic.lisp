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
(include-book "hyp-fix")
; cert-param: (reloc_stub)
(local (in-theory (disable (force))))

;; The interface for these three functions is summed up by the theorem below.
;; The implementation may change.  The theorem maybe should also say that if
;; neither true-under-hyp or false-under-hyp hold, then there are envs under
;; which both (implies hyp x) and (implies hyp (not x)) hold.


;; (defthm bfr-and-t
;;   (and (equal (bfr-and t x) x)
;;        (equal (bfr-and x t) x))
;;   :hints (("goal" :in-theory (enable bfr-binary-and
;;                                      acl2::aig-and))))

;; (defthm hyp-fix-bfr-p
;;   (bfr-p (hyp-fix x hyp)))

;; (defthm hyp-fix-hyp-fix
;;   (equal (hyp-fix (hyp-fix x hyp) hyp)
;;          (hyp-fix x hyp)))


;; (encapsulate nil
;;   (local (bfr-reasoning-mode t))
;;   (defthm hyp-fix-correct
;;     (implies (bfr-eval hyp env)
;;              (equal (bfr-eval (hyp-fix x hyp) env)
;;                     (bfr-eval x env)))
;;     :hints ((and stable-under-simplificationp
;;                  (member-equal '(not (bfr-mode)) clause)
;;                  '(:in-theory (enable bfr-eval)))))


;;   (defthmd hyp-ops-correct
;;     (implies (bfr-eval hyp env)
;;              (and (implies (true-under-hyp (hyp-fix x hyp) hyp)
;;                            (bfr-eval x env))
;;                   (implies (false-under-hyp (hyp-fix x hyp) hyp)
;;                            (not (bfr-eval x env)))))
;;     :hints (("goal" :use ((:instance hyp-fix-correct))
;;              :in-theory (disable hyp-fix-correct)))))



;; (defthm hyp-fixedp-hyp-fix
;;   (hyp-fixedp (hyp-fix x hyp) hyp)
;;   :hints(("Goal" :in-theory (enable bfr-binary-and))))

;; (defthm hyp-fix-of-hyp-fixedp
;;   (implies (hyp-fixedp x hyp)
;;            (equal (hyp-fix x hyp)
;;                   x)))

;; (defthm pbfr-depends-on-of-hyp-fix
;;   (implies (not (pbfr-depends-on k p x))
;;            (not (pbfr-depends-on k p (hyp-fix x hyp))))
;;   :hints(("Goal" :in-theory (enable hyp-fix))))


;; ;; (local (bfr-reasoning-mode t))


;; ;; (defthmd true-under-hyp-rw
;; ;;   (implies (and (bfr-p x) (bfr-p hyp) hyp)
;; ;;            (equal (true-under-hyp (hyp-fix x hyp) hyp)
;; ;;                   (equal (q-implies hyp x) t))))



;; ;; (defthmd false-under-hyp-rw
;; ;;   (implies (and (bfr-p x) (bfr-p hyp) hyp)
;; ;;            (equal (false-under-hyp (hyp-fix x hyp) hyp)
;; ;;                   (equal (q-implies hyp (bfr-not x)) t))))


;; ;; (defthmd true-under-hyp-when-hyp-fixedp-rw
;; ;;   (implies (and (bfr-p x) (bfr-p hyp) hyp (hyp-fixedp x hyp))
;; ;;            (equal (true-under-hyp x hyp)
;; ;;                   (equal (q-implies hyp x) t))))


;; ;; (defthmd false-under-hyp-when-hyp-fixedp-rw
;; ;;   (implies (and (bfr-p x) (bfr-p hyp) hyp (hyp-fixedp x hyp))
;; ;;            (equal (false-under-hyp x hyp)
;; ;;                   (equal (q-implies hyp (bfr-not x)) t))))



;; (in-theory (disable hyp-fix))



;; (defthmd true-under-hyp-point
;;   (implies (and (true-under-hyp x hyp)
;;                 (hyp-fixedp x hyp)
;;                 (bfr-eval hyp v))
;;            (bfr-eval x v)))

;; (defthmd false-under-hyp-point
;;   (implies (and (false-under-hyp x hyp)
;;                 (hyp-fixedp x hyp)
;;                 (bfr-eval hyp v))
;;            (not (bfr-eval x v))))






;; (defthm false-under-hyp-hyp-fix-bfr-not
;;   (implies (and (bfr-p c) (hyp-fixedp c hyp) (bfr-p hyp) hyp)
;;            (equal (false-under-hyp (hyp-fix (bfr-not c) hyp) hyp)
;;                   (true-under-hyp c hyp)))
;;   :hints (("Goal" :in-theory (e/d (hyp-fix)
;;                                   (len max max-depth
;;                                        hyp-ops-correct)))))

;; (defthm true-under-hyp-hyp-fix-bfr-not
;;   (implies (and (bfr-p c) (hyp-fixedp c hyp) (bfr-p hyp) hyp)
;;            (equal (true-under-hyp (hyp-fix (bfr-not c) hyp) hyp)
;;                   (false-under-hyp c hyp)))
;;   :hints (("Goal" :in-theory (e/d (hyp-fix)
;;                                   (len max max-depth
;;                                        hyp-ops-correct)))
;;           (equal-by-bfr-evals-hint-heavy)))



;; (in-theory (disable true-under-hyp false-under-hyp hyp-fix))



;; (encapsulate nil
;;   (local (bfr-reasoning-mode t))
;;   (defthmd hyp-fixed-ops-correct
;;     (implies (and (bfr-eval hyp env)
;;                   (hyp-fixedp x hyp))
;;              (and (implies (true-under-hyp x hyp)
;;                            (bfr-eval x env))
;;                   (implies (false-under-hyp x hyp)
;;                            (not (bfr-eval x env)))))
;;     :hints(("Goal" :in-theory (enable hyp-ops-correct
;;                                       true-under-hyp
;;                                       false-under-hyp)))))

;; (in-theory (disable hyp-fixedp hyp-fixed-ops-correct hyp-ops-correct))








