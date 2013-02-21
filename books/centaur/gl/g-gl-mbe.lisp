
(in-package "GL")
(include-book "bfr-sat")
(include-book "g-always-equal")
(include-book "gl-mbe")
(local (include-book "eval-g-base-help"))


;; [Jared] uses of sneaky-save for the time being.  I don't think we often care
;; about this.  This scheme lets us include gl-mbe in the top-level gl.lisp,
;; without needing a ttag.  We can always redefine the function if we need to
;; debug something.

;; (include-book "../misc/sneaky-load")


(def-g-fn gl-mbe
  `(b* ((equal? (glr acl2::always-equal spec impl hyp clk))
        (tests (gtests equal? hyp))
        (false (bfr-and hyp
                        (bfr-not (gtests-unknown tests))
                        (bfr-not (gtests-nonnil tests))))
        ((mv false-sat false-succ ?false-ctrex)
         (bfr-sat false))
        ((when (and false-sat false-succ))
         ;; (acl2::sneaky-save 'gl-mbe-ctrex false-ctrex)
         (er hard? 'gl-mbe "GL-MBE assertion failed.")
         spec)
        ((when (not false-succ))
         (er hard? 'gl-mbe "GL-MBE assertion failed to prove.")
         spec)
        (unk (bfr-and hyp (gtests-unknown tests)))
        ((mv unk-sat unk-succ ?unk-ctrex)
         (bfr-sat unk))
        ((when (and unk-sat unk-succ))
         ;; (acl2::sneaky-save 'gl-mbe-ctrex unk-ctrex)
         (er hard? 'gl-mbe "GL-MBE assertion failed with unknown.")
         spec)
        ((when (not unk-succ))
         (er hard? 'gl-mbe "GL-MBE assertion failed to prove absence of unknowns.")
         spec))
     impl))

(def-gobjectp-thm gl-mbe)

(verify-g-guards gl-mbe)

(local
 (defun instantiate-bfr-sat-hint (clause env)
   (if (atom clause)
       nil
     (let ((lit (car clause)))
       (case-match lit
         (('mv-nth ''0 ('bfr-sat term))
          (cons `(:instance bfr-sat-unsat
                            (prop ,term)
                            (env ,env))
                (instantiate-bfr-sat-hint (cdr clause) env)))
         (& (instantiate-bfr-sat-hint (cdr clause) env)))))))

(def-g-correct-thm gl-mbe eval-g-base
  :hints '(("goal" :do-not-induct t
            :in-theory (disable bfr-sat-unsat))
           (and stable-under-simplificationp
                (let ((insts (instantiate-bfr-sat-hint clause '(car env))))
                  (if insts
                      `(:computed-hint-replacement
                        t
                        :use ,insts)
                    (cw "clause: ~x0~%" clause))))))
