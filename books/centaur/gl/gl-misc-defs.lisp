

(in-package "ACL2")

;; Note: Putting an entry FUNCTION -> DEF-RULE in the  GL::PREFERRED-DEFS table
;; causes MAKE-G-WORLD to assume that DEF-RULE is the name of a :definition
;; rule for FUNCTION and use that definition rule as the definition instead of
;; the original definition of FUNCTION.

;; In this instance, we'd like to change the definition of EVENP used in
;; MAKE-G-WORLD from its original definition, (INTEGERP (* X (/ 2))), to:
;; (or (not (acl2-numberp x))
;;     (and (integerp x)
;;          (equal (logbitp 0 x) nil)))
;;
;; This is better, currently, because the GL system doesn't deal well with
;; rationals at the moment, so (* X 1/2) doesn't work well.  Therefore we prove
;; the rule EVENP-IS-LOGBITP which shows that these are equivalent, and then
;; add the entry to the PREFERRED-DEFS table.

(encapsulate nil
  (local (include-book "arithmetic/top-with-meta" :dir :system))
  (local (defthm integerp-1/2-x-requires-integerp-x
           (implies (and (acl2-numberp x)
                         (not (integerp x)))
                    (not (integerp (* 1/2 x))))
           :hints (("goal" :cases ((equal (imagpart x) 0))))))

  (defthmd evenp-is-logbitp
    (equal (evenp x)
           (or (not (acl2-numberp x))
               (and (integerp x)
                    (equal (logbitp 0 x) nil))))
    :hints(("Goal" :in-theory (enable logbitp)))
    :rule-classes :definition))

(table gl::preferred-defs 'evenp 'evenp-is-logbitp)
