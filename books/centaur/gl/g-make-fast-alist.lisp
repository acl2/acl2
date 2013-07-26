

(in-package "GL")

(include-book "centaur/gl/g-primitives-help" :dir :system)
(include-book "centaur/gl/eval-g-base" :dir :system)
(include-book "centaur/gl/g-if" :dir :system)
(local (include-book "centaur/gl/eval-g-base-help" :dir :system))


(def-g-fn acl2::make-fast-alist
  `(let ((x acl2::alist))
     (if (general-concretep x)
         (mk-g-concrete
          (acl2::make-fast-alist (general-concrete-obj x)))
       (pattern-match x
         ((g-ite test then else)
          (if (zp clk)
              x
            (g-if test
                  (,gfn then . ,params)
                  (,gfn else . ,params))))
         ((g-apply & &) x)
         ((g-var &) x)
         ((g-boolean &) x)
         ((g-number &) x)
         (& (acl2::make-fast-alist x))))))

;; (def-gobjectp-thm acl2::make-fast-alist)

;; (defthm gobjectp-impl-not-g-keyword-symbolp
;;   (implies (gobjectp x)
;;            (not (g-keyword-symbolp x)))
;;   :hints(("Goal" :in-theory (enable gobject-hierarchy-impl-not-g-keyword-symbolp
;;                                     gobjectp))))

(verify-g-guards acl2::make-fast-alist)

(def-gobj-dependency-thm acl2::make-fast-alist
  :hints `(("goal" :induct ,gcall
            :expand (,gcall)
            :in-theory (disable (:d ,gfn)))))

(def-g-correct-thm acl2::make-fast-alist eval-g-base
  :hints `(("Goal" :induct (,gfn acl2::alist . ,params)
            :expand (,gfn acl2::alist . ,params)
            :in-theory (disable (:definition ,gfn)))
           (and stable-under-simplificationp
                '(:expand ((:with eval-g-base (eval-g-base acl2::alist
                                                           env)))))))
