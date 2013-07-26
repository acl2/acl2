
(in-package "GL")

(include-book "g-if")
(include-book "g-primitives-help")
(include-book "symbolic-arithmetic-fns")
(include-book "eval-g-base")
;(include-book "tools/with-arith5-help" :dir :system)
(local (include-book "symbolic-arithmetic"))
(local (include-book "eval-g-base-help"))
(local (include-book "hyp-fix-logic"))
(local (include-book "centaur/misc/arith-equivs" :dir :system))
;(local (allow-arith5-help))


(defun g-binary-logior-of-numbers (x y)
  (declare (xargs :guard (and (general-numberp x)
                              (general-numberp y))))
  (b* (((mv xrn xrd xin xid)
        (general-number-components x))
       ((mv yrn yrd yin yid)
        (general-number-components y))
       ((mv xintp xintp-known)
        (if (equal xrd '(t))
            (mv (bfr-or (bfr-=-ss xin nil)
                      (bfr-=-uu xid nil)) t)
          (mv nil nil)))
       ((mv yintp yintp-known)
        (if (equal yrd '(t))
            (mv (bfr-or (bfr-=-ss yin nil)
                      (bfr-=-uu yid nil)) t)
          (mv nil nil))))
    (if (and xintp-known yintp-known)
        (mk-g-number
         (bfr-logior-ss (bfr-ite-bss-fn xintp xrn nil)
                    (bfr-ite-bss-fn yintp yrn nil)))
      (g-apply 'binary-logior (gl-list x y)))))

(in-theory (disable (g-binary-logior-of-numbers)))

(defthm deps-of-g-binary-logior-of-numbers
  (implies (and (not (gobj-depends-on k p x))
                (not (gobj-depends-on k p y))
                (general-numberp x)
                (general-numberp y))
           (not (gobj-depends-on k p (g-binary-logior-of-numbers x y)))))

(local (defthm logior-non-integers
         (and (implies (not (integerp i))
                       (equal (logior i j) (logior 0 j)))
              (implies (not (integerp j))
                       (equal (logior i j) (logior i 0))))))

(local (include-book "arithmetic/top-with-meta" :dir :system))

(local
 (progn
   ;; (defthm gobjectp-g-binary-logior-of-numbers
   ;;   (implies (and (gobjectp x)
   ;;                 (general-numberp x)
   ;;                 (gobjectp y)
   ;;                 (general-numberp y))
   ;;            (gobjectp (g-binary-logior-of-numbers x y)))
   ;;   :hints(("Goal" :in-theory (disable general-numberp
   ;;                                      general-number-components))))

   (defthm g-binary-logior-of-numbers-correct
     (implies (and (general-numberp x)
                   (general-numberp y))
              (equal (eval-g-base (g-binary-logior-of-numbers x y) env)
                     (logior (eval-g-base x env)
                             (eval-g-base y env))))
     :hints (("goal" :in-theory (e/d* ((:ruleset general-object-possibilities))
                                      (general-numberp
                                       general-number-components))
              :do-not-induct t)))))

(in-theory (disable g-binary-logior-of-numbers))


(def-g-binary-op binary-logior
  (b* ((i-num (if (general-numberp i) i 0))
       (j-num (if (general-numberp j) j 0)))
    (g-binary-logior-of-numbers i-num j-num)))



(verify-g-guards
 binary-logior
 :hints `(("Goal" :in-theory (disable* ,gfn
                                       general-concretep-def))))

(def-gobj-dependency-thm binary-logior
  :hints `(("goal" :induct ,gcall
            :expand (,gcall)
            :in-theory (disable (:d ,gfn)))))

(local (defthm logior-non-acl2-numbers
         (and (implies (not (acl2-numberp i))
                       (equal (logior i j) (logior 0 j)))
              (implies (not (acl2-numberp j))
                       (equal (logior i j) (logior i 0))))))

(def-g-correct-thm binary-logior eval-g-base
  :hints `(("Goal" :in-theory (e/d* (general-concretep-atom
                                     (:ruleset general-object-possibilities)
                                     not-general-numberp-not-acl2-numberp)
                                    ((:definition ,gfn)
                                     general-concretep-def
                                     binary-logior
                                     components-to-number-alt-def
                                     hons-assoc-equal
                                     eval-g-base-non-cons
                                     default-car default-cdr
                                     (:rules-of-class :type-prescription :here)))
            :induct (,gfn i j . ,params)
            :do-not-induct t
            :expand ((,gfn i j . ,params)))))
