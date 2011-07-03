
(in-package "GL")

(include-book "general-objects")

(local (include-book "general-object-thms"))

(local (include-book "hyp-fix-logic"))

(include-book "bvec-ite")
(include-book "hyp-fix")
(include-book "unicode/two-nats-measure" :dir :system)

(include-book "tools/mv-nth" :dir :system)
(local (include-book "misc/invariants" :dir :system))

(verify-guards general-concrete-obj-aig
 :hints (("goal" :in-theory (enable general-concrete-gobject-car-and-cdr))))

(verify-guards general-concrete-obj-bdd
 :hints (("goal" :in-theory (enable general-concrete-gobject-car-and-cdr))))

(verify-guards
 general-concrete-obj
 :hints
 (("goal" :in-theory (enable general-concrete-gobject-car-and-cdr))))

(memoize 'general-concrete-obj-bdd :condition
         '(and (consp x) (not (or (g-concrete-p x) (concrete-gobjectp x)))))

(memoize 'general-concrete-obj-aig :condition
         '(and (consp x) (not (or (g-concrete-p x) (concrete-gobjectp x)))))



(defn merge-general-numbers (c x y)
  (declare (xargs :guard (and (gobjectp x) (general-numberp x)
                              (gobjectp y) (general-numberp y)
                              (bfr-p c))))
  (b* ((c (bfrfix c))
       ((mv xrn xrd xin xid)
        (general-number-components x))
       ((mv yrn yrd yin yid)
        (general-number-components y)))
    (flet ((ubv-ite (c a b)
                    (let ((res (bfr-ite-bvv-fn c a b)))
                      (if (boolean-listp res)
                          (v2n res)
                        res)))
           (sbv-ite (c a b)
                    (let ((res (bfr-ite-bss-fn c a b)))
                      (if (boolean-listp res)
                          (v2i res)
                        res))))
      (mk-g-number (sbv-ite c xrn yrn)
                     (ubv-ite c xrd yrd)
                     (sbv-ite c xin yin)
                     (ubv-ite c xid yid)))))

(in-theory (disable merge-general-numbers))






(defun merge-general-booleans (c a b)
  (declare (xargs :guard (and (bfr-p c)
                              (gobjectp a) (gobjectp b)
                              (general-booleanp a)
                              (general-booleanp b))))
  (let* ((av (general-boolean-value a))
         (bv (general-boolean-value b))
         (c (bfrfix c))
         (val (bfr-ite c av bv)))
    (mk-g-boolean val)))

(in-theory (disable merge-general-booleans))




(defun hlexorder (x y)
  (declare (xargs :guard t))
  (cond ((atom x)
         (if (atom y) (alphorder x y) t))
        ((atom y) nil)
        ((hqual (car x) (car y))
         (hlexorder (cdr x) (cdr y)))
        (t (hlexorder (car x) (car y)))))


(defun ite-merge-ordering (x y)
  (declare (xargs :guard (and (gobjectp x) (gobjectp y))
                  :guard-hints (("goal" :in-theory (e/d (general-booleanp
                                                         general-numberp
                                                         general-concrete-atom
                                                         general-concrete-atom-val
                                                         general-consp
                                                         gobject-hierarchy
                                                         gobjectp)
                                                        ((force)))))))
  (cond ((hqual x y) 'equal)
        ((general-booleanp x)
         (if (general-booleanp y)
             'booleans
           '<))
        ((general-booleanp y) '>)
        ((general-numberp x)
         (if (general-numberp y)
             'numbers
           '<))
        ((general-numberp y) '>)
        ((general-concrete-atom x)
         (if (general-concrete-atom y)
             (if (alphorder (general-concrete-atom-val x)
                            (general-concrete-atom-val y)) '< '>)
           '<))
        ((general-concrete-atom y) '>)
        ((general-consp x)
         (if (general-consp y)
             'conses
           '<))
        ((general-consp y) '>)
        ((eq (tag x) :g-var)
         (if (eq (tag y) :g-var)
             (if (hlexorder (g-var->name x) (g-var->name y)) '< '>)
           '<))
        ((eq (tag y) :g-var) '>)
        ((eq (tag x) :g-apply)
         (if (eq (tag y) :g-apply)
             (if (eq (g-apply->fn x) (g-apply->fn y))
                 'applies
               (if (hlexorder (cdr x) (cdr y)) '< '>))
           '<))
        ((eq (tag y) :g-apply) '>)
        (t ;; Both :g-ites
         (if (hlexorder (cdr x) (cdr y)) '< '>))))


(in-theory (disable ite-merge-ordering))



(defn ite-merge-guard (c x y hyp)
  (and (bfr-p c)
       (gobjectp x)
       (gobjectp y)
       (bfr-p hyp)
;;       hyp
;;        (hyp-fixedp c hyp)
       ))

(defn maybe-merge-guard (c x y xhyp yhyp hyp)
  (and (bfr-p c) (bfr-p hyp)
       (bfr-p xhyp) (bfr-p yhyp)
       (gobjectp x) (gobjectp y)))

(defn merge-rest-guard (firstcond first c rest-x rest-y hyp)
  (and (bfr-p c) (bfr-p firstcond) (bfr-p hyp)
;;       hyp ;; (hyp-fixedp c hyp)
;;        (hyp-fixedp firstcond hyp)
       (not (fh c)) (not (th c))
       (gobjectp first)
       (gobjectp rest-x)
       (gobjectp rest-y)))


(defn ite-merge-measure (c x y hyp)
  (if (ite-merge-guard c x y hyp)
      (two-nats-measure
       (+ 1 (acl2-count x) (acl2-count y))
       1)
    (two-nats-measure 0 0)))

(defn maybe-merge-measure (c x y xhyp yhyp hyp)
  (if (maybe-merge-guard c x y xhyp yhyp hyp)
      (two-nats-measure
       (+ 1 (acl2-count x) (acl2-count y))
       0)
    (two-nats-measure 0 0)))

(defn merge-rest-measure (firstcond first c x y hyp)
  (if (merge-rest-guard firstcond first c x y hyp)
      (two-nats-measure
       (+ 1
          (acl2-count x)
          (acl2-count y))
       2)
    (two-nats-measure 0 0)))

(defun breakdown-ite-by-cond (x)
  (declare (xargs :guard (gobjectp x)))
  (if (bool-cond-itep x)
      (mv (bool-cond-itep-cond x)
          (bool-cond-itep-truebr x)
          (bool-cond-itep-falsebr x))
    (mv t x nil)))




(local
 (defthm ite-merge-ordering-cases
   (and (equal (equal (ite-merge-ordering x y) 'equal)
               (equal x y))
        (equal (equal (ite-merge-ordering x y) 'booleans)
               (and (not (equal x y))
                    (general-booleanp x)
                    (general-booleanp y)))
        (equal (equal (ite-merge-ordering x y) 'numbers)
               (and (not (equal x y))
                    (general-numberp x)
                    (general-numberp y)))
        (equal (equal (ite-merge-ordering x y) 'conses)
               (and (not (equal x y))
                    (general-consp x)
                    (general-consp y)))
        (equal (equal (ite-merge-ordering x y) 'applies)
               (and (not (equal x y))
                    (equal (tag x) :g-apply)
                    (equal (tag y) :g-apply)
                    (equal (g-apply->fn x) (g-apply->fn y)))))
   :hints (("goal" :in-theory (enable general-booleanp general-numberp
                                      general-consp general-concrete-atom
                                      tag ite-merge-ordering)))))


(local
 (defthm nfix-natp
   (implies (natp n)
            (equal (nfix n) n))
   :rule-classes ((:rewrite :backchain-limit-lst 0))))

(local
 (encapsulate nil
   (local (add-bfr-pat (hyp-fix . ?)))
   (local (in-theory (disable* acl2-count integer-abs bfr-p-of-boolean
                               equal-of-booleans-rewrite not
                               hyp-fix-of-hyp-fixedp
                               g-apply-p-when-wrong-tag
                               
;                               bfr-eval-nonnil-forward
                               default-+-2 o<
                               default-<-1
                               default-+-1
                               default-<-2 nfix
                               ;;                                true-under-hyp-rw
                               ;;                                false-under-hyp-rw
                               iff-implies-equal-not
                               bfr-eval-booleanp
                               gobjectp-def
                               (:ruleset gl-tag-rewrites)
                               (:rules-of-class
                                :type-prescription :here))))

;    (local (bfr-reasoning-mode t))

   (local (in-theory (enable (:type-prescription acl2-count))))

   (defthm merge-rest-measure-thm
     (and (o-p (merge-rest-measure firstcond first c x y hyp))
          (implies (and (merge-rest-guard firstcond first c x y hyp)
                        (not (th firstcond))
                        hyp)
                   (let ((old-measure
                          (merge-rest-measure firstcond first c x y hyp)))
                     (and (implies (fh firstcond)
                                   (o< (ite-merge-measure c x y hyp)
                                       old-measure))
                          (let ((hyp (bfr-and (bfr-not firstcond) hyp)))
                            (o< (ite-merge-measure (hf c) x y hyp)
                                old-measure))))))
     :hints (("goal" :do-not-induct t
              :in-theory nil)
             (and stable-under-simplificationp
                  '(:in-theory (enable)))
             (and stable-under-simplificationp
                  '(:in-theory
                    (enable hyp-fix hyp-fixedp
                            true-under-hyp
                            false-under-hyp)))))

   (defthm maybe-merge-measure-thm
     (let ((old-measure (maybe-merge-measure c x y xhyp yhyp hyp)))
       (and (o-p old-measure)
            (implies
             (maybe-merge-guard c x y xhyp yhyp hyp)
             (and (implies (eql (ite-merge-ordering x y) 'conses)
                           (let ((hyp (bfr-and hyp (hf (bfr-ite c xhyp yhyp)))))
                             (and (o< (ite-merge-measure (hf c)
                                                         (general-consp-car x)
                                                         (general-consp-car y)
                                                         hyp)
                                      old-measure)
                                  (o< (ite-merge-measure (hf c)
                                                         (general-consp-cdr x)
                                                         (general-consp-cdr y)
                                                         hyp)
                                      old-measure))))
                  (implies (eql (ite-merge-ordering x y) 'applies)
                           (let ((hyp (bfr-and hyp (hf (bfr-ite c xhyp yhyp)))))
                             (o< (ite-merge-measure (hf c)
                                                    (g-apply->args x)
                                                    (g-apply->args y)
                                                    hyp)
                                 old-measure)))))))
     :hints ((and stable-under-simplificationp
                  '(:in-theory
                    (enable hyp-fix hyp-fixedp
                            true-under-hyp
                            false-under-hyp)))))

   (defthm ite-merge-measure-thm
     (and (o-p (ite-merge-measure c x y hyp))
          (implies
           (and (ite-merge-guard c x y hyp)
                (not (th c)) (not (fh c))
                hyp)
           (b* ((old-measure (ite-merge-measure c x y hyp))
                ((mv first-x-cond first-x rest-x)
                 ;; x is (if first-x-cond first-x rest-x)
                 (breakdown-ite-by-cond x))
                ((mv first-y-cond first-y rest-y)
                 (breakdown-ite-by-cond y)))
             (and ;;  (implies (and (fh first-x-cond)
              ;;                                 (fh first-y-cond))
              ;;                            (o< (ite-merge-measure c rest-x rest-y hyp)
              ;;                                old-measure))
              ;;                   (implies (and (fh first-x-cond)
              ;;                                 (not (fh first-y-cond)))
              ;;                            (o< (ite-merge-measure c rest-x y hyp)
              ;;                                old-measure))
              ;;                   (implies (and (not (fh first-x-cond))
              ;;                                 (fh first-y-cond))
              ;;                            (o< (ite-merge-measure c x rest-y hyp)
              ;;                                old-measure))
              ;;                   (implies
              ;;                    (and (not (fh first-x-cond))
              ;;                         (not (fh first-y-cond)))
              (let ((firstcond (hf (bfr-ite-fn c first-x-cond first-y-cond))))
                (and (implies (and (not (and (eq first-x-cond t)
                                             (eq first-y-cond t)))
                                   (equal fc firstcond))
                              (o< (merge-rest-measure
                                   fc anything c rest-x rest-y hyp)
                                  old-measure))
                     (o< (maybe-merge-measure c first-x first-y first-x-cond
                                             first-y-cond hyp)
                         old-measure)
                     (implies (not (eq first-x-cond t))
                              (o< (merge-rest-measure
                                   (bfr-and c first-x-cond) first-x c rest-x y hyp)
                                  old-measure))
                     (implies (not (eq first-y-cond t))
                              (o< (merge-rest-measure
                                   (bfr-and (bfr-not c) first-y-cond) first-y c x rest-y hyp)
                                  old-measure))))))))
     :hints (("goal" :do-not-induct t
              :in-theory '(breakdown-ite-by-cond))
             (and stable-under-simplificationp
                  '(:in-theory (enable)))
             (and stable-under-simplificationp
                  '(:in-theory
                    (enable hyp-fix hyp-fixedp
                            true-under-hyp
                            false-under-hyp)))))))




(mutual-recursion
 (defun merge-rest (firstcond first c x y hyp)
   ;; (if firstcond first (if c x y))
   (declare (xargs :guard (merge-rest-guard firstcond first c x y hyp) 
                   :verify-guards nil
                   :measure (merge-rest-measure firstcond first c x y hyp)))
   (if (mbt (merge-rest-guard firstcond first c x y hyp))
       (cond ((not hyp) nil)
             ((th firstcond)
              first)
             ((fh firstcond)
              (ite-merge c x y hyp))
             (t (mk-g-ite (mk-g-boolean firstcond)
                          first
                          (let ((hyp (bfr-and (bfr-not firstcond) hyp)))
                            (ite-merge (hf c) x
                                       y
                                       hyp)))))
     nil))

 (defun maybe-merge (c x y xhyp yhyp hyp)
   (declare (xargs :guard (maybe-merge-guard c x y xhyp yhyp hyp)
                   :measure (maybe-merge-measure c x y xhyp yhyp hyp)))
   (if (mbt (maybe-merge-guard c x y xhyp yhyp hyp))
       (let ((ordersym (ite-merge-ordering x y)))
         (case ordersym
           (equal (mv t x))
           (booleans (mv 'merged (merge-general-booleans c x y)))
           (numbers (mv 'merged (merge-general-numbers c x y)))
           (conses (let ((hyp (bfr-and hyp (hf (bfr-ite c xhyp yhyp)))))
                     (mv 'merged (cons (ite-merge (hf c)
                                                  (general-consp-car x)
                                                  (general-consp-car y)
                                                  hyp)
                                       (ite-merge (hf c)
                                                  (general-consp-cdr x)
                                                  (general-consp-cdr y)
                                                  hyp)))))
           (applies (let ((hyp (bfr-and hyp (hf (bfr-ite c xhyp yhyp)))))
                      (mv 'merged (g-apply (g-apply->fn x)
                                           (ite-merge (hf c)
                                                      (g-apply->args x)
                                                      (g-apply->args y)
                                                      hyp)))))
           (otherwise (mv ordersym nil))))
     (mv nil nil)))



 (defun ite-merge (c x y hyp)
   ;; (if c x y)
   (declare (xargs :guard (ite-merge-guard c x y hyp)
                   :measure (ite-merge-measure c x y hyp)
                   :hints (("goal" :do-not-induct t
                            :in-theory '(ite-merge-measure-thm
                                         merge-rest-measure-thm
                                         maybe-merge-measure-thm)))))
   (if (mbt (ite-merge-guard c x y hyp))
       (cond ((not hyp) nil)
             ((hons-equal x y) x)
             ((th c) x)
             ((fh c) y)
             (t (b* (((mv first-x-cond first-x rest-x)
                      (breakdown-ite-by-cond x))
                     ((mv first-y-cond first-y rest-y)
                      (breakdown-ite-by-cond y))
                     ((mv merge-flg first)
                      (maybe-merge c first-x first-y first-x-cond first-y-cond hyp)))
                  (case merge-flg
                    (merged
                     (if (and (eq first-x-cond t)
                              (eq first-y-cond t))
                         first
                       (merge-rest (hf (bfr-ite c first-x-cond first-y-cond))
                                   first c rest-x rest-y hyp)))
                    (< (if (eq first-x-cond t)
                           (mk-g-ite (mk-g-boolean c) first-x y)
                         (merge-rest (bfr-and c first-x-cond)
                                     first-x c rest-x y hyp)))
                    (t ;; >
                     (if (eq first-y-cond t)
                         (mk-g-ite (mk-g-boolean c) x first-y)
                       (merge-rest (bfr-and (bfr-not c) first-y-cond)
                                   first-y c x rest-y hyp)))))))
     nil)))


(in-theory (disable ite-merge merge-rest))

(local (in-theory (disable  hyp-fix-of-hyp-fixedp)))







(local
 (defthm merge-general-numbers-gobjectp
   (implies (and (gobjectp a) (gobjectp b)
                 (general-numberp a) (general-numberp b)
                 (bfr-p c))
            (gobjectp (merge-general-numbers c a b)))
   :hints(("Goal" :in-theory (enable boolean-listp-bfr-listp
                                     merge-general-numbers)))))


(local
 (defthm merge-general-numbers-correct
   (implies (and (gobjectp a) (gobjectp b)
                 (general-numberp a) (general-numberp b)
                 (bfr-p c))
            (equal (generic-geval (merge-general-numbers c a b) env)
                   (if (bfr-eval c (car env))
                       (generic-geval a env)
                     (generic-geval b env))))
   :hints (("goal"
            :in-theory
            (enable boolean-listp-bfr-ite-bvv-fn-v2n-bind-env-car-env
                    boolean-listp-bfr-ite-bss-fn-v2i-bind-env-car-env
                    merge-general-numbers)))))





(local
 (defthm merge-general-booleans-gobjectp
   (implies (and (bfr-p c)
                 (gobjectp a) (gobjectp b)
                 (general-booleanp a)
                 (general-booleanp b))
            (gobjectp (merge-general-booleans c a b)))
   :hints (("goal" :in-theory (enable gobjectp merge-general-booleans)))))


(local
 (defthm merge-general-booleans-correct
   (implies (and (bfr-p c)
                 (gobjectp a) (gobjectp b)
                 (general-booleanp a)
                 (general-booleanp b))
            (equal (generic-geval (merge-general-booleans c a b) env)
                   (if (bfr-eval c (car env))
                       (generic-geval a env)
                     (generic-geval b env))))
   :hints (("goal" :in-theory
            (e/d (generic-geval booleanp merge-general-booleans))))))



(local
 (defthm breakdown-ite-by-cond-wfp
   (mv-let (cond first rest)
     (breakdown-ite-by-cond x)
     (and (implies (gobjectp x)
                   (and (gobjectp first)
                        (gobjectp rest)))
          (implies (gobjectp x)
                   (bfr-p cond))))))


(local
 (defthm breakdown-ite-by-cond-correct
   (mv-let (cond first rest)
     (breakdown-ite-by-cond x)
     (and (implies (and (bfr-eval cond (car env))
                        (gobjectp x))
                   (equal (generic-geval first env)
                          (generic-geval x env)))
          (implies (and (not (bfr-eval cond (car env)))
                        (gobjectp x))
                   (equal (generic-geval rest env)
                          (generic-geval x env)))))
   :hints(("Goal" :in-theory (enable hyp-fix)
           :do-not-induct t))
   :otf-flg t))



;; (local
;;  (defthm breakdown-ite-by-cond-conditions-exclude
;;    (implies (and (bfr-eval (mv-nth 0 (breakdown-ite-by-cond c y hyp)) env)
;;                  (bfr-eval hyp env))
;;             (not (bfr-eval (mv-nth 0 (breakdown-ite-by-cond (bfr-not c) x hyp))
;;                            env)))
;;    :hints(("Goal" :in-theory (enable hyp-fix hyp-fixedp)))))

            
;; (local
;;  (defthm breakdown-ite-by-cond-nonnil
;;    (implies (and hyp (bfr-and c hyp)
;;                  (bfr-p c) (bfr-p hyp) (gobjectp x))
;;             (iff (bfr-and hyp (mv-nth 0 (breakdown-ite-by-cond c x hyp)))
;;                  (mv-nth 0 (breakdown-ite-by-cond c x hyp))))
;;    :hints(("Goal" :in-theory (enable hyp-fixedp hyp-fix)))))

;; (local
;;  (defthm breakdown-ite-by-cond-nonnil2
;;    (implies (and hyp (not (equal (bfr-and c hyp) hyp))
;;                  (bfr-p c) (bfr-p hyp) (gobjectp x))
;;             (iff (bfr-and hyp (mv-nth 0 (breakdown-ite-by-cond (bfr-not c) x hyp)))
;;                  (mv-nth 0 (breakdown-ite-by-cond (bfr-not c) x hyp))))
;;    :hints(("Goal" :in-theory (enable hyp-fixedp hyp-fix)))))

(in-theory (disable breakdown-ite-by-cond))




(local
 (defthm hlexorder-is-lexorder
   (equal (hlexorder x y) (lexorder x y))
   :hints (("goal" :in-theory (enable lexorder)))))






(local
 (flag::make-flag ite-merge-ind ite-merge
                  :defthm-macro-name def-ite-merge-thm
                  :hints (("goal" :do-not-induct t
                           :in-theory '(ite-merge-measure-thm
                                        merge-rest-measure-thm
                                        maybe-merge-measure-thm)))))




(local
 (def-ite-merge-thm gobjectp-ite-merge-lemma
   (merge-rest (gobjectp (merge-rest firstcond first c x y hyp))
               :name gobjectp-merge-rest)
   (maybe-merge (gobjectp (mv-nth 1 (maybe-merge c x y xhyp yhyp hyp))))
   (ite-merge (gobjectp (ite-merge c x y hyp))
              :name gobjectp-ite-merge)
   :hints (("goal" :induct
            (ite-merge-ind flag firstcond first xhyp yhyp c x y hyp)
;;             :in-theory (disable ite-merge maybe-merge merge-rest)
;;             :expand ((ite-merge c x y hyp)
;;                      (maybe-merge c x y xhyp yhyp hyp)
;;                      (merge-rest firstcond first c x y hyp))
            :do-not-induct t)
           (and (subgoal-of "Subgoal *1/" id)
                ;; '(:expand ((ite-merge c x y hyp)
                ;;                           (merge-rest firstcond first c x y hyp)))
                '(:in-theory nil))
           (and (subgoal-of "Subgoal *1/" id)
                stable-under-simplificationp
                (prog2$ (cw " a ")
                        (flag::expand-calls-computed-hint clause '(ite-merge
                                                                   merge-rest
                                                                   maybe-merge))))
           (and (subgoal-of "Subgoal *1/" id)
                stable-under-simplificationp
                (prog2$ (cw " b ") '(:in-theory ;; (disable ite-merge-guard merge-rest-guard)
                                     (enable))))
           (and (subgoal-of "Subgoal *1/" id)
                stable-under-simplificationp
                (prog2$ (cw " c ")
                        '(:in-theory (enable false-under-hyp
                                             true-under-hyp
                                             hyp-fix hyp-fixedp)))))))


(local
 (def-ruleset! minimal-rules (set-difference-theories
                              (theory 'minimal-theory) '((force)))))

(local (bfr-reasoning-mode t))

(local
 (defthm gobjectp-impl-not-g-keyword-symbolp
   (implies (gobjectp x)
            (not (g-keyword-symbolp x)))
   :hints(("Goal" :in-theory (enable
                              gobject-hierarchy-impl-not-g-keyword-symbolp
                              gobjectp)))))

(local (add-bfr-pat (mv-nth '0 (breakdown-ite-by-cond . &) . &)))


(local
 (encapsulate nil
   (local (in-theory (disable* gobjectp-def
                               (:rules-of-class :type-prescription :here)
                               bfr-eval-booleanp
                               equal-of-booleans-rewrite
                               (:ruleset gl-wrong-tag-rewrites)
                               (:ruleset gl-tag-forward)
                               (:ruleset gl-tag-rewrites))))
   (local (in-theory (enable bfr-p)))
   (local (bfr-reasoning-mode nil))
   (prove-guard-invariants
    ite-merge
    :simplify-hints (("Goal"
                      :in-theory (ruleset-theory 'minimal-rules)))
    :hints ((and stable-under-simplificationp
                 '(:in-theory (e/d* (false-under-hyp
                                     true-under-hyp
                                     hyp-fixedp
                                     hyp-fix
                                     breakdown-ite-by-cond))))))))


(local
 (defthm ite-merge-guard-forward
   (implies (ite-merge-guard c x y hyp)
            (and (bfr-p c)
                 (gobjectp x)
                 (gobjectp y)
                 (bfr-p hyp)
;;                  hyp
;;                  (hyp-fixedp c hyp)
                 ))
   :rule-classes :forward-chaining))

(local
 (defthm maybe-merge-merge-guard-forward
   (implies (maybe-merge-guard c x y xhyp yhyp hyp)
            (and (bfr-p c) (bfr-p hyp)
                 (bfr-p xhyp) (bfr-p yhyp)
                 (gobjectp x)
                 (gobjectp y)))
   :rule-classes :forward-chaining))


(local
 (defthm merge-rest-guard-forward
   (implies (merge-rest-guard firstcond first c rest-x rest-y hyp)
            (and (bfr-p c) (bfr-p firstcond) (bfr-p hyp)
;;                  hyp (hyp-fixedp c hyp)
;;                  (hyp-fixedp firstcond hyp)
                 (not (fh c)) (not (th c))
                 (gobjectp first)
                 (gobjectp rest-x)
                 (gobjectp rest-y)))
   :rule-classes :forward-chaining))


(in-theory (disable ite-merge-guard merge-rest-guard maybe-merge-guard))


(local
 (defthm ite-merge-ordering-not-merged
   (not (equal (ite-merge-ordering x y) 'merged))
   :hints(("Goal" :in-theory (enable ite-merge-ordering)))))

(local
 (encapsulate
   nil
   (local (in-theory (e/d* (generic-geval-g-apply-p)
                           ((force) member-equal gobjectp-cons-case
                            gobjectp-merge-rest ite-merge merge-rest maybe-merge
                            general-number-components-ev
                            
                            boolean-list-bfr-eval-list
                            gobjectp-def mv-nth
                            generic-geval-non-gobjectp
                            (:ruleset gl-wrong-tag-rewrites)
                            (:ruleset gl-tag-rewrites)
                            (:ruleset gl-tag-forward)
                            (:type-prescription len)
                            default-car default-cdr
                            hons-assoc-equal
                            (:rewrite bfr-eval-booleanp)
                            break-g-number
                            generic-geval
                            hyp-fix-of-hyp-fixedp
                            tag-when-g-var-p
                            eval-concrete-gobjectp
                            acl2-numberp-v2n
                            tag-when-g-apply-p
                            tag-when-g-ite-p
                            default-unary-/
                            tag-when-g-number-p
                            tag-when-g-boolean-p
                            tag-when-g-concrete-p
                            
                            (:type-prescription v2n)
                            (:type-prescription v2i)
                            bfr-eval-list-consts
                            default-*-1 default-*-2
                            (:type-prescription booleanp)
                            (:type-prescription hons-assoc-equal)
                            default-complex-1 default-complex-2
                            gobjectp-cons
                            g-apply-p-when-wrong-tag
                            g-var-p-when-wrong-tag
                            g-number-p-when-wrong-tag
                            g-concrete-p-when-wrong-tag
                            g-boolean-p-when-wrong-tag
                            ; bfr-eval-nonnil-forward
                            (:type-prescription ite-merge-guard)
                            (:type-prescription hyp-fix)
                            (:type-prescription bfr-eval)
                            (:type-prescription bfr-p)
                            (:type-prescription q-implies-fn)
                            (:type-prescription bool-cond-itep)
                            (:type-prescription false-under-hyp)
                            (:type-prescription hyp-fixedp)
                            (:type-prescription gobjectp)
                            (:type-prescription bfr-binary-and)
                            (:type-prescription general-consp)
                            (:type-prescription ite-merge-ordering)
                            equal-of-booleans-rewrite
                            not bfr-p-of-boolean))))
   ; (local (bfr-reasoning-mode nil))
   ;;  (defthm ite-merge-c-nil
   ;;    (equal (ite-merge nil x y hyp)
   ;;           (and (ite-merge-guard nil x y hyp)
   ;;                y))
   ;;    :hints(("Goal" :expand ((ite-merge nil x y hyp))
   ;;            :in-theory (enable false-under-hyp true-under-hyp))))

   (def-ite-merge-thm ite-merge-correct-lemma
     (ite-merge (implies (and (bfr-eval (double-rewrite hyp) (car env))
                              (ite-merge-guard c x y hyp))
                         (equal (generic-geval (ite-merge c x y hyp) env)
                                (if (bfr-eval c (car env))
                                    (generic-geval x env)
                                  (generic-geval y env))))
                :name ite-merge-correct)
     (maybe-merge (mv-let (flg ans)
                    (maybe-merge c x y xhyp yhyp hyp)
                    (implies (and (equal flg 'merged)
                                  (bfr-eval hyp (car env)))
                             (and (implies (and (bfr-eval c (car env))
                                                (bfr-eval xhyp (car env)))
                                           (equal (generic-geval ans env)
                                                  (generic-geval x env)))
                                  (implies (and (not (bfr-eval c (car env)))
                                                (bfr-eval yhyp (car env)))
                                           (equal (generic-geval ans env)
                                                  (generic-geval y env))))))
                  :name maybe-merge-correct)
                                
     (merge-rest (implies (and (bfr-eval hyp (car env))
                               (merge-rest-guard firstcond first c x y hyp))
                          (equal (generic-geval (merge-rest firstcond first c x y hyp) env)
                                 (if (bfr-eval firstcond (car env))
                                     (generic-geval first env)
                                   (if (bfr-eval c (car env))
                                       (generic-geval x env)
                                     (generic-geval y env)))))
                 :name merge-rest-correct)
     :hints (("goal" :induct (ite-merge-ind flag firstcond first xhyp yhyp c x y hyp)
              :do-not-induct t
              :in-theory (set-difference-theories
                          (list* '(:induction ite-merge-ind)
                                 '(:rewrite ite-merge-ind-equivalences)
                                 (union-theories (ruleset-theory 'minimal-rules)
                                                 (theory 'ite-merge-invariants)))
                          '(force (force) member-equal)))
             ;;            ("Subgoal *1/15" :by nil)
             ;;            ("Subgoal *1/14" :by nil)
             ;;            ("Subgoal *1/13" :by nil)
             ;;            ("Subgoal *1/12" :by nil)
             ;;            ("Subgoal *1/11" :by nil)
             (and ;;(subgoal-of "Subgoal *1/" id)
              stable-under-simplificationp
              (flag::expand-calls-computed-hint
               clause '(ite-merge merge-rest maybe-merge)))
             (and ;;(subgoal-of "Subgoal *1/" id)
              stable-under-simplificationp
              (or (cw "enabling~%")
                  '(:in-theory (e/d))))
             (and ;;(subgoal-of "Subgoal *1/" id)
              stable-under-simplificationp
              (or (cw "enabling hf-of-hfp~%")
                  '(:in-theory (e/d (hyp-fix-of-hyp-fixedp)))))
             (and ;;(subgoal-of "Subgoal *1/" id)
              stable-under-simplificationp
              (or (cw "enabling more~%")
                  '(:in-theory (e/d (false-under-hyp
                                     true-under-hyp
                                     ite-merge-guard merge-rest-guard
                                     maybe-merge-guard
                                     hyp-fix hyp-fixedp)
                                    ()))))))))



(verify-guards ite-merge
               :hints (("Goal" :in-theory (e/d** ((:ruleset minimal-rules))))
                       (and stable-under-simplificationp
                            '(:in-theory 
                              (e/d** ((:ruleset minimal-rules)
                                      ite-merge-invariants))))
                       (and stable-under-simplificationp
                            '(:in-theory
                                (e/d* ()
                                      (equal-of-booleans-rewrite
                                       (:ruleset gl-tag-rewrites)))))
                       (and stable-under-simplificationp
                            '(:cases ((equal (mv-nth 0 (breakdown-ite-by-cond
                                                        x)) t))))))






(local
 (defthm ite-merge-when-true-under-hyp
   (implies (and (ite-merge-guard c x y hyp)
                 (true-under-hyp c hyp)
                 hyp)
            (equal (ite-merge c x y hyp) x))
   :hints(("Goal" :in-theory (enable ite-merge)))))

(local
 (defthm ite-merge-when-false-under-hyp
   (implies (and (ite-merge-guard c x y hyp)
                 (false-under-hyp c hyp)
                 hyp)
            (equal (ite-merge c x y hyp) y))
   :hints (("goal" :in-theory (enable true-under-hyp false-under-hyp
                                      ite-merge-guard
                                      ite-merge)))))





(local
 (defthm ite-merge-guard-suff
   (implies (and (bfr-p c)
                 (gobjectp x)
                 (gobjectp y)
                 (bfr-p hyp))
            (ite-merge-guard c x y hyp))
   :hints (("goal" :in-theory (enable ite-merge-guard)))))

(defund gobj-ite-merge (c x y hyp)
  (declare (xargs :guard (and (bfr-p c)
                              (gobjectp x)
                              (gobjectp y)
                              (bfr-p hyp))))
  (let ((hyp (bfrfix hyp))
        (c (bfrfix c))
        (x (mbe :logic (gobj-fix x) :exec x))
        (y (mbe :logic (gobj-fix y) :exec y)))
    (ite-merge (hf c) x y hyp)))

(defthm gobjectp-gobj-ite-merge
  (gobjectp (gobj-ite-merge c x y hyp))
  :hints(("Goal" :in-theory (enable gobj-ite-merge))))

(defthm gobj-ite-merge-correct
  (implies (bfr-eval hyp (car env))
           (equal (generic-geval (gobj-ite-merge c x y hyp) env)
                  (if (bfr-eval c (car env))
                      (generic-geval x env)
                    (generic-geval y env))))
  :hints(("Goal" :in-theory (e/d (gobj-ite-merge)))))

(prove-congruences (bfr-equiv gobj-equiv gobj-equiv bfr-equiv) gobj-ite-merge)
