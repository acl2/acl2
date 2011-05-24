

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




; Below we tweak the definition that GL uses for EXPT so that (EXPT 2 N) is
; treated as a shift instead, where N is a natural number.  This might be a bad
; idea when the base is a variable that is sometimes 2, since it will lead us
; to consider both the ASH and regular EXPT-style definitions.  But it seems
; nice for hardware models where (EXPT 2 N) may be the most frequent use of
; EXPT.

(defund expt-fallback (r i)
  (declare (xargs :guard (and (acl2-numberp r)
                              (integerp i)
                              (not (and (eql r 0) (< i 0))))
                  :measure (abs (ifix i))))
  (cond ((zip i) 1)
        ((= (fix r) 0) 0)
        ((> i 0) (* r (expt-fallback r (+ i -1))))
        (t (* (/ r) (expt-fallback r (+ i 1))))))

(defthm expt-fallback-is-expt
  (equal (expt-fallback r i)
         (expt r i))
  :hints(("Goal" :in-theory (enable expt-fallback expt))))

(encapsulate
  ()
  (local (include-book "arithmetic/top-with-meta" :dir :system))

  (defthmd optimize-expt-2-for-gl
    (equal (expt r i)
           (if (and (equal r 2)
                    (natp i))
               (ash 1 i)
             (expt-fallback r i)))))

(table gl::preferred-defs 'expt 'optimize-expt-2-for-gl)
