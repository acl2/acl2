; CHB Media Unit MINT Proofs
; Original author: Jared Davis <jared@centtech.com>
;
; Centaur Internal Use Only

(in-package "FGL")


(include-book "def-fgl-rewrite")
(include-book "greedy-max-sat")
(include-book "top-bare")

(local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))

(local (in-theory (disable (tau-system))))


(define slice-miter-list ((nslices natp)
                          (slice-width posp)
                          (x integerp)
                          (y integerp))
  :returns (miters)
  (if (zp nslices)
      nil
    (cons (not (equal (loghead (lposfix slice-width) x)
                      (loghead (lposfix slice-width) y)))
          (slice-miter-list (1- nslices) slice-width
                            (logtail (lposfix slice-width) x)
                            (logtail (lposfix slice-width) y))))
  ///
  (defret len-of-<fn>
    (equal (len miters) (nfix nslices)))

  (local (defun nth-of-slice-miter-list-implies-not-equal-ind (n nslices slice-width x y)
           (if (zp n)
               (list nslices slice-width x y)
             (nth-of-slice-miter-list-implies-not-equal-ind
              (1- n)
              (1- nslices) slice-width
              (logtail (lposfix slice-width) x)
              (logtail (lposfix slice-width) y)))))

  (defthm nth-of-slice-miter-list-implies-not-equal
    (implies (nth n (slice-miter-list nslices slice-width x y))
             (not (equal x y)))
    :hints (("goal" :induct (nth-of-slice-miter-list-implies-not-equal-ind
                             n nslices slice-width x y)
             :expand ((:free (y) (slice-miter-list nslices slice-width x y))))))
  (local (defthm natp-lemma
           (implies (and (natp p)
                         (posp n))
                    (natp (+ (* -1 p)
                             (* n p))))
           :hints(("Goal" :in-theory (enable natp))
                  (and stable-under-simplificationp
                       '(:nonlinearp t)))
           :rule-classes :type-prescription))

  (local (defthm cancel-lemma
           (equal (+ p (* -1 p) n) (fix n))))
  (local (defthm loghead-of-logtail-unequal
           (implies (and (not (equal (loghead (+ (nfix n) (nfix m)) x)
                                     (loghead (+ (nfix n) (nfix m)) y)))
                         (equal (loghead m x)
                                (loghead m y)))
                    (not (equal (loghead n (logtail m x))
                                (loghead n (logtail m y)))))
           :hints ((bitops::logbitp-reasoning :prune-examples nil))))

  (defthm member-t-of-slice-miter-list-when-not-equal
    (implies (not (equal (loghead (* (nfix nslices) (pos-fix slice-width)) x)
                         (loghead (* (nfix nslices) (pos-fix slice-width)) y)))
             
             (member t (slice-miter-list nslices slice-width x y)))))


(def-fgl-rewrite indices-all-true-open
  (iff (indices-all-true indices x)
       (if (atom indices)
           t
         (and (nth (car indices) x)
              (indices-all-true (cdr indices) x))))
  :hints (("goal" :use ((:instance indices-all-true-of-cons
                         (a (car indices)) (b (cdr indices)) (x x)))
           :in-theory (disable indices-all-true-of-cons
                               indices-all-true))
          (and stable-under-simplificationp
               '(:expand ((indices-all-true indices x))))))


(disable-definition indices-all-true)

;; BOZO temporary

(defmacro fgl-validity-check (params x)
  `(not (fgl-sat-check ,params (not ,x))))


(define greedy-max-int-slice-diffs ((x integerp)
                                         (y integerp)
                                         (sat-config)
                                         (nslices natp)
                                         (slice-width posp))
  (declare (ignore sat-config nslices slice-width))
  (equal x y)
  ;; (loghead (* (nfix nslices) (pos-fix slice-width)) x)
  ;;        (loghead (* (nfix nslices) (pos-fix slice-width)) y)
         
  ///
  (def-fgl-rewrite greedy-max-int-slice-diffs-fgl
    (equal (greedy-max-int-slice-diffs x y sat-config nslices slice-width)
           (b* ((width (* (nfix nslices) (pos-fix slice-width)))
                (ins-ok (fgl-validity-check sat-config (and (unsigned-byte-p width x)
                                                                 (unsigned-byte-p width y))))
                ((unless (and (syntax-bind ins-ok! (eq ins-ok t)) ins-ok))
                 (fgl-prog2 (syntax-interp (cw "greedy-max-int-slice-diffs malformed inputs! x: ~x0 y: ~x1~%" x y))
                            (equal x y)))
                (miters (slice-miter-list nslices slice-width x y))
                (max-sat-indices
                 (greedy-max-sat!
                  max-sat-indices
                  miters
                  sat-config))
                ((when (not max-sat-indices))
                 (fgl-prog2 (syntax-interp (cw "greedy-max-int-slice-diffs says true!~%"))
                            t))
                (all-diff (indices-all-true max-sat-indices miters))
                (all-diff-sat (sat-check! all-diff-sat sat-config all-diff))
                (real-cond (equal x y))
                ((when (eq all-diff-sat :sat))
                 (fgl-prog2 (fgl-prog2 (syntax-interp (cw "greedy-max-int-slice-diffs sat!~%"))
                                       (syntax-interp
                                        (b* (((mv err ?ist)
                                              (interp-st-run-ctrex (g-concrete->val sat-config)
                                                                   'interp-st 'state)))
                                          (and err (cw "interp-st-run-ctrex error: ~@0~%" err)))))
                            real-cond)))
             (fgl-prog2 (syntax-interp (cw "greedy-max-int-slice-diffs failed!~%"))
                        real-cond)))
    :hints (("goal" :use ((:instance greedy-max-sat-empty-implies
                           (ans max-sat-indices)
                           (x (slice-miter-list nslices slice-width x y))
                           (sat-config sat-config)
                           (n (acl2::index-of t (slice-miter-list nslices slice-width x y)))))
             :in-theory (e/d (fgl-sat-check) (greedy-max-sat-empty-implies)))))
  (disable-definition greedy-max-int-slice-diffs))

