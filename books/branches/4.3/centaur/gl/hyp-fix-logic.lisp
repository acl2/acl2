

(in-package "GL")


(include-book "hyp-fix")

(local (in-theory (disable (force))))

;; The interface for these three functions is summed up by the theorem below.
;; The implementation may change.  The theorem maybe should also say that if
;; neither true-under-hyp or false-under-hyp hold, then there are envs under
;; which both (implies hyp x) and (implies hyp (not x)) hold.


(defthm bfr-and-t
  (and (equal (bfr-and t x) (bfr-fix x))
       (equal (bfr-and x t) (bfr-fix x)))
  :hints (("goal" :in-theory (enable bfr-binary-and
                                     acl2::aig-and
                                     bfr-fix))))

(defthm hyp-fix-bfr-p
  (bfr-p (hyp-fix x hyp)))

(defthm hyp-fix-hyp-fix
  (equal (hyp-fix (hyp-fix x hyp) hyp)
         (hyp-fix x hyp)))


(encapsulate nil
  (local (bfr-reasoning-mode t))
  (add-bfr-pat (bfr-fix . &))
  (defthm hyp-fix-correct
    (implies (bfr-eval hyp env)
             (equal (bfr-eval (hyp-fix x hyp) env)
                    (bfr-eval x env))))


  (defthmd hyp-ops-correct
    (implies (bfr-eval hyp env)
             (and (implies (true-under-hyp (hyp-fix x hyp) hyp)
                           (bfr-eval x env))
                  (implies (false-under-hyp (hyp-fix x hyp) hyp)
                           (not (bfr-eval x env)))))
    :hints (("goal" :use ((:instance hyp-fix-correct))
             :in-theory (disable hyp-fix-correct)))))



(defthm hyp-fixedp-hyp-fix
  (hyp-fixedp (hyp-fix x hyp) hyp))

(defthm hyp-fix-of-hyp-fixedp
  (implies (hyp-fixedp x hyp)
           (equal (hyp-fix x hyp)
                  (bfr-fix x))))




;; (local (bfr-reasoning-mode t))


;; (defthmd true-under-hyp-rw
;;   (implies (and (bfr-p x) (bfr-p hyp) hyp)
;;            (equal (true-under-hyp (hyp-fix x hyp) hyp)
;;                   (equal (q-implies hyp x) t))))



;; (defthmd false-under-hyp-rw
;;   (implies (and (bfr-p x) (bfr-p hyp) hyp)
;;            (equal (false-under-hyp (hyp-fix x hyp) hyp)
;;                   (equal (q-implies hyp (bfr-not x)) t))))


;; (defthmd true-under-hyp-when-hyp-fixedp-rw
;;   (implies (and (bfr-p x) (bfr-p hyp) hyp (hyp-fixedp x hyp))
;;            (equal (true-under-hyp x hyp)
;;                   (equal (q-implies hyp x) t))))


;; (defthmd false-under-hyp-when-hyp-fixedp-rw
;;   (implies (and (bfr-p x) (bfr-p hyp) hyp (hyp-fixedp x hyp))
;;            (equal (false-under-hyp x hyp)
;;                   (equal (q-implies hyp (bfr-not x)) t))))



(in-theory (disable hyp-fix))



(defthmd true-under-hyp-point
  (implies (and (true-under-hyp x hyp)
                (hyp-fixedp x hyp)
                (bfr-eval hyp v))
           (bfr-eval x v)))

(defthmd false-under-hyp-point
  (implies (and (false-under-hyp x hyp)
                (hyp-fixedp x hyp)
                (bfr-eval hyp v))
           (not (bfr-eval x v))))




(add-bfr-fn-pat hyp-fix)

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



(in-theory (disable true-under-hyp false-under-hyp hyp-fix))



(encapsulate nil
  (local (bfr-reasoning-mode t))
  (defthmd hyp-fixed-ops-correct
    (implies (and (bfr-eval hyp env)
                  (hyp-fixedp x hyp))
             (and (implies (true-under-hyp x hyp)
                           (bfr-eval x env))
                  (implies (false-under-hyp x hyp)
                           (not (bfr-eval x env)))))
    :hints(("Goal" :in-theory (enable hyp-ops-correct
                                      true-under-hyp
                                      false-under-hyp)))))

(in-theory (disable hyp-fixedp hyp-fixed-ops-correct hyp-ops-correct))








