

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






(encapsulate
  ()

; [Jared]: I ran into performance problems trying to simulate with ACL2's
; ordinary definition of logcount, so this is a faster replacement.
;
; One probably important tweak is to not use NONNEGATIVE-INTEGER-QUOTIENT;
; instead I use ASH to strip off the bits as we recur.  I can imagine that this
; might help quite a bit.
;
; Another problem with ACL2's logical definition of LOGCOUNT is that we end up
; checking whether the number is negative at each recursive step.  This seems
; to get quite expensive.  My replacement definition avoids these checks on the
; recursive steps since we know that once the number has been coerced to a
; natural, it will stay positive as we recur.

  (local (include-book "unicode/two-nats-measure" :dir :system))
  (local (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system))

  (local (in-theory (enable ash logbitp acl2-count)))

  (local (defthm ash-of-negative-1
           (implies (posp x)
                    (equal (ash x -1)
                           (floor x 2)))))

  (local (defthm nonnegative-integer-quotient-of-2
           (implies (natp x)
                    (equal (nonnegative-integer-quotient x 2)
                           (floor x 2)))))

  (defun logcount-of-natural (n)
    (if (zp n)
        0
      (+ (if (logbitp 0 n) 1 0)
         (logcount-of-natural (ash n -1)))))

  (defthm logcount-of-natural-correct
    (implies (natp n)
             (equal (logcount-of-natural n)
                    (logcount n)))
    :hints(("Goal"
            :in-theory (enable logcount)
            :induct (logcount n))))

  (defun logcount-for-gl (x)
    (cond ((zip x)
           0)
          ((< x 0)
           (logcount-of-natural (lognot x)))
          (t
           (logcount-of-natural x))))

  (local (defthm crock
           (implies (and (integerp a)
                         (< a 0))
                    (natp (lognot a)))))

  (defthmd logcount-for-gl-correct
    (equal (logcount x)
           (logcount-for-gl x))
    :rule-classes :definition))

(table gl::preferred-defs 'logcount 'logcount-for-gl-correct)
