
(in-package "GL")

(set-inhibit-warnings "theory")

(include-book "g-if")
(include-book "g-primitives-help")
(include-book "symbolic-arithmetic-fns")
(include-book "eval-g-base")
;(include-book "tools/with-arith5-help" :dir :system)
(local (include-book "symbolic-arithmetic"))
(local (include-book "eval-g-base-help"))
(local (include-book "hyp-fix-logic"))
;(local (allow-arith5-help))
 


(def-g-fn lognot
  `(let ((x i))
     (if (atom x)
         (lognot (ifix x))
       (pattern-match x
         ((g-ite test then else)
          (if (zp clk)
              (g-apply 'lognot (gl-list x))
            (g-if test
                  (,gfn then hyp clk)
                  (,gfn else hyp clk))))
         ((g-apply & &)
          (g-apply 'lognot (gl-list x)))
         ((g-concrete obj)
          (lognot (ifix obj)))
         ((g-var &)
          (g-apply 'lognot (gl-list x)))
         ((g-boolean &) -1)
         ((g-number num)
          (b* (((mv rn rd in id)
                (break-g-number num))
               ((mv intp intp-known)
                (if (equal rd '(t))
                    (mv (bfr-or (=-ss in nil) (=-uu id nil)) t)
                  (mv nil nil))))
            (if intp-known
                (mk-g-number (lognot-s (bfr-ite-bss-fn intp rn nil)))
              (g-apply 'lognot (gl-list x)))))
         (& -1)))))



;; (local (defthm gobjectp-lognot
;;          (gobjectp (lognot x))
;;          :hints(("Goal" :in-theory (enable gobjectp-def)))))

;; (def-gobjectp-thm lognot
;;   :hints `(("Goal" :in-theory (e/d ()
;;                                    ((:definition ,gfn) lognot))
;;             :induct (,gfn i hyp clk)
;;             :expand ((,gfn i hyp clk)
;;                      (:free (x) (gobjectp (- x)))))))

(verify-g-guards
 lognot
 :hints `(("Goal" :in-theory (disable ,gfn))))

(local
 (progn
   (defthm lognot-non-acl2-numberp
     (implies (not (acl2-numberp n))
              (equal (lognot n) (lognot 0))))

   (defthm lognot-non-integer
     (implies (not (integerp n))
              (equal (lognot n) (lognot 0))))

   (local (include-book "arithmetic/top-with-meta" :dir :system))))

(def-g-correct-thm lognot eval-g-base
   :hints `(("Goal" :in-theory (e/d* (components-to-number-alt-def
                                      general-concrete-obj)
                                    ((:definition ,gfn) (force)
                                     general-number-components-ev
                                     general-numberp-eval-to-numberp
                                     lognot))
             :induct (,gfn i hyp clk)
             :expand ((,gfn i hyp clk)
                      (:with eval-g-base (eval-g-base i env))))))

