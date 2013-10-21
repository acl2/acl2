
(in-package "GL")

(include-book "g-if")
(include-book "g-primitives-help")
(include-book "symbolic-arithmetic-fns")
(include-book "eval-g-base")
;(include-book "tools/with-arith5-help" :dir :system)
(local (include-book "symbolic-arithmetic"))
(local (include-book "eval-g-base-help"))
(local (include-book "hyp-fix-logic"))
;(local (allow-arith5-help))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))

(defun s-take (n x)
  (declare (xargs :guard (natp n)))
  (b* (((when (zp n)) (bfr-sterm nil))
       ((mv first rest &) (first/rest/end x)))
    (bfr-ucons first (s-take (1- n) rest))))


(defthm s-take-correct
  (equal (bfr-list->u (s-take n x) env)
         (loghead n (bfr-list->s x env)))
  :hints (("goal" :induct (s-take n x)
           :in-theory (enable* acl2::ihsext-recursive-redefs))))
    


;; (local (defthm v2i-of-append
;;          (implies (consp y)
;;                   (equal (v2i (append x y))
;;                          (logapp (len x) (v2n x) (v2i y))))
;;          :hints (("goal" :induct (append x y)
;;                   :in-theory (enable* acl2::ihsext-recursive-redefs
;;                                       v2i v2n)))))

;; (defthm bfr-eval-list-of-append
;;   (equal (bfr-eval-list (append a b) env)
;;          (append (bfr-eval-list a env)
;;                  (bfr-eval-list b env))))

;; (defthm len-of-bfr-eval-list
;;   (equal (len (bfr-eval-list x env))
;;          (len x)))

;; (defthm len-of-s-take
;;   (equal (len (s-take w x))
;;          (nfix w)))

;; (defun append-us (x y)
;;   (declare (xargs :guard (true-listp x)))
;;   (append x (if (consp y) y '(nil))))

;; (defthm append-us-correct
;;   (equal (bfr-list->s (append-us x y) env)
;;          (logapp (len x) (bfr-list->u x env)
;;                  (bfr-list->s y env)))
;;   :hints(("Goal" :in-theory (enable append-us))))


(defun logapp-uss (w n x y)
  (declare (xargs :measure (len n)
                  :guard (natp w)))
  (if (atom n)
      y
    (bfr-ite-bss
     (car n)
     (bfr-logapp-nus (lnfix w) (s-take w x)
                 (logapp-uss (ash (lnfix w) 1) (cdr n) (logtail-ns w x)
                             y))
     (logapp-uss (ash (lnfix w) 1) (cdr n) x y))))

(local
 (progn
   (defthm logapp-of-logapp
     (implies (equal w (logapp m y z))
              (equal (logapp n x w)
                     (logapp (+ (nfix n) (nfix m)) (logapp n x y) z)))
     :hints(("Goal" :in-theory (enable* acl2::ihsext-inductions
                                        acl2::ihsext-recursive-redefs)
             :induct (loghead n x))))

   (defthm logcar-non-integer
     (implies (not (integerp x))
              (equal (logcar x) 0))
     :hints(("Goal" :in-theory (enable logcar)))
     :rule-classes ((:rewrite :backchain-limit-lst 0)))

   (defthm logcdr-non-integer
     (implies (not (integerp x))
              (equal (logcdr x) 0))
     :hints(("Goal" :in-theory (enable logcdr)))
     :rule-classes ((:rewrite :backchain-limit-lst 0)))

   (defthm remake-*-n-w
     (and (implies (equal (logcar n) 1)
                   (equal (+ (nfix w) (* 2 (logcdr n) (nfix w)))
                          (* (ifix n) (nfix w))))
          (implies (equal (logcar n) 0)
                   (equal (* 2 (logcdr n) (nfix w))
                          (* (ifix n) (nfix w)))))
     :hints(("Goal" :in-theory (e/d (logcons)
                                    (acl2::logcons-destruct))
             :use ((:instance acl2::logcar-logcdr-elim
                    (i n))))))


   (defthm logapp-loghead-logtail
     (equal (logapp n (loghead n x) (logtail n x))
            (ifix x))
     :hints(("Goal" :in-theory (enable* acl2::ihsext-inductions
                                        acl2::ihsext-recursive-redefs)
             :induct (loghead n x))))))

;; (defthm true-listp-append-us
;;   (implies (true-listp y)
;;            (true-listp (append-us x y)))
;;   :hints(("Goal" :in-theory (enable append-us)))
;;   :rule-classes :type-prescription)

;; (defthm true-listp-logapp-uss
;;   (implies (true-listp y)
;;            (true-listp (logapp-uss w n x y)))
;;   :rule-classes :type-prescription)

;; (defun logapp-uss-conc (w n x y)
;;   (if (zp n)
;;       (ifix y)
;;     (if (equal (logcar n) 1)
;;         (logapp w (loghead w x)
;;                 (logapp-uss-conc (* 2 (nfix w)) (logcdr n)
;;                                  (logtail w x) y))
;;       (logapp-uss-conc (* 2 (nfix w)) (logcdr n) x y))))

;; (defthm logapp-uss-conc-correct
;;   (equal (logapp-uss-conc w n x y)
;;          (logapp (* (nfix w) (nfix n)) x y)))






;; (local (in-theory (disable append-us)))



(defthm logapp-uss-correct
  (equal (bfr-list->s (logapp-uss w n x y) env)
         (logapp (* (bfr-list->u n env)
                    (nfix w))
                 (bfr-list->s x env)
                 (bfr-list->s y env)))
  :hints(("Goal" :in-theory (enable acl2::ash** logcons))))

(local (in-theory (disable logapp-uss)))

    

(defun g-logapp-of-numbers (n x y)
  (declare (xargs :guard (and (general-numberp n)
                              (general-numberp x)
                              (general-numberp y))))
  (b* (((mv nrn nrd nin nid)
        (general-number-components n))
       ((mv xrn xrd xin xid)
        (general-number-components x))
       ((mv yrn yrd yin yid)
        (general-number-components y))
       ((mv nintp nintp-known)
        (if (equal nrd '(t))
            (mv (bfr-or (bfr-=-ss nin nil)
                        (bfr-=-uu nid nil)) t)
          (mv nil nil)))
       ((mv xintp xintp-known)
        (if (equal xrd '(t))
            (mv (bfr-or (bfr-=-ss xin nil)
                      (bfr-=-uu xid nil)) t)
          (mv nil nil)))
       ((mv yintp yintp-known)
        (if (equal yrd '(t))
            (mv (bfr-or (bfr-=-ss yin nil)
                      (bfr-=-uu yid nil)) t)
          (mv nil nil)))
       ((unless (and nintp-known xintp-known yintp-known))
        (g-apply 'logapp (gl-list n x y)))
       ;; nfix
       (nbits (bfr-ite-bvv-fn (bfr-and (bfr-not (s-sign nrn)) nintp)
                              nrn nil))
       ;; ifix
       (xbits (bfr-ite-bss-fn xintp xrn nil))
       (ybits (bfr-ite-bss-fn yintp yrn nil))
       (resbits (logapp-uss 1 nbits xbits ybits)))
    (mk-g-number (rlist-fix resbits))))


(in-theory (disable (g-logapp-of-numbers)))

(local (defthm logapp-zp-n
         (implies (zp n)
                  (equal (logapp n x y)
                         (ifix y)))
         :hints(("Goal" :in-theory (enable acl2::logapp**)))
         :rule-classes ((:rewrite :backchain-limit-lst 0))))
(local (defthm logapp-zip-x
         (implies (and (syntaxp (not (equal x ''0)))
                       (zip x))
                  (equal (logapp n x y)
                         (logapp n 0 y)))
         :hints(("Goal" :in-theory (enable acl2::logapp**)))
         :rule-classes ((:rewrite :backchain-limit-lst 0))))
(local (defthm logapp-zip-y
         (implies (and (syntaxp (not (equal y ''0)))
                       (zip y))
                  (equal (logapp n x y)
                         (logapp n x 0)))
         :hints(("Goal" :in-theory (enable acl2::logapp**)))
         :rule-classes ((:rewrite :backchain-limit-lst 0))))

(local (defthm bfr-list->s-when-gte-0
         (implies (<= 0 (bfr-list->s x env))
                  (equal (bfr-list->s x env)
                         (bfr-list->u x env)))
         :hints(("Goal" :in-theory (enable scdr s-endp)))))

(defthm g-logapp-of-numbers-correct
  (implies (and (general-numberp n)
                (general-numberp x)
                (general-numberp y))
           (equal (eval-g-base (g-logapp-of-numbers n x y) env)
                  (logapp (eval-g-base n env)
                          (eval-g-base x env)
                          (eval-g-base y env))))
  :hints (("goal" :in-theory (e/d* ((:ruleset general-object-possibilities)
                                    )
                                   (general-numberp
                                    bfr-list->s
                                    general-number-components))
           :do-not-induct t)))

(in-theory (disable g-logapp-of-numbers))

(def-g-fn logapp
  `(let ((size acl2::size))
     (b* (((when (and (general-concretep size)
                      (general-concretep i)
                      (general-concretep j)))
           (ec-call (logapp (general-concrete-obj size)
                            (general-concrete-obj i)
                            (general-concrete-obj j))))
          ((unless (or (atom size)
                       (not (member-eq (tag size) '(:g-ite :g-var :g-apply)))))
           (if (and (eq (tag size) :g-ite)
                    (not (zp clk)))
               (let* ((test (g-ite->test size))
                      (then (g-ite->then size))
                      (else (g-ite->else size)))
                 (g-if test
                       (,gfn then i j hyp clk)
                       (,gfn else i j hyp clk)))
             (g-apply 'logapp (gl-list size i j))))
          ((unless (or (atom i)
                       (not (member-eq (tag i) '(:g-ite :g-var :g-apply)))))
           (if (and (eq (tag i) :g-ite)
                    (not (zp clk)))
               (let* ((test (g-ite->test i))
                      (then (g-ite->then i))
                      (else (g-ite->else i)))
                 (g-if test
                       (,gfn size then j hyp clk)
                       (,gfn size else j hyp clk)))
             (g-apply 'logapp (gl-list size i j))))
          ((unless (or (atom j)
                       (not (member-eq (tag j) '(:g-ite :g-var :g-apply)))))
           (if (and (eq (tag j) :g-ite)
                    (not (zp clk)))
               (let* ((test (g-ite->test j))
                      (then (g-ite->then j))
                      (else (g-ite->else j)))
                 (g-if test
                       (,gfn size i then hyp clk)
                       (,gfn size i else hyp clk)))
             (g-apply 'logapp (gl-list size i j))))
          (size (if (general-numberp size) size 0))
          (i (if (general-numberp i) i 0))
          (j (if (general-numberp j) j 0)))
       (g-logapp-of-numbers size i j))))

(verify-g-guards logapp
                 :hints `(("Goal" :in-theory (disable* ,gfn
                                                       general-concretep-def))))

(local (defthm logapp-non-acl2-numbers
         (and (implies (not (acl2-numberp size))
                       (equal (logapp size i j) (ifix j)))
              (implies (not (acl2-numberp i))
                       (equal (logapp size i j) (logapp size 0 j)))
              (implies (not (acl2-numberp j))
                       (equal (logapp size i j) (logapp size i 0))))))



(def-g-correct-thm logapp eval-g-base
  :hints `(("Goal" :in-theory (e/d* (general-concretep-atom
                                     (:ruleset general-object-possibilities)
                                     not-general-numberp-not-acl2-numberp
                                     eval-g-base-non-cons)
                                    ((:definition ,gfn)
                                     general-concretep-def
                                     logapp
                                     member-equal
                                     eval-g-base-alt-def
                                     components-to-number-alt-def
                                     hons-assoc-equal
                                     sets::double-containment
                                     equal-of-booleans-rewrite
                                     bfr-eval-list
                                     acl2::cancel_times-equal-correct
                                     acl2::cancel_plus-equal-correct
                                     default-car default-cdr
                                     (:rules-of-class :type-prescription
                                      :here))
                                    ((:t logapp)))
            :induct (,gfn acl2::size i j hyp clk)
            :do-not-induct t
            :expand ((,gfn acl2::size i j hyp clk)))
           (and stable-under-simplificationp
                (intersectp-equal '((not (equal (tag$inline acl2::size) ':g-ite))
                                    (not (general-concretep acl2::size)))
                                  clause)
                '(:expand ((eval-g-base acl2::size env))))
           (and stable-under-simplificationp
                (intersectp-equal '((not (equal (tag$inline i) ':g-ite))
                                    (not (general-concretep i)))
                                  clause)
                '(:expand ((eval-g-base i env))))
           (and stable-under-simplificationp
                (intersectp-equal '((not (equal (tag$inline j) ':g-ite))
                                    (not (general-concretep j)))
                                  clause)
                '(:expand ((eval-g-base j env))))))






(defun g-int-set-sign-of-number (negp y hyp)
  (declare (xargs :guard (general-numberp y)))
  (b* (((mv yrn yrd yin yid)
        (general-number-components y))
       ((mv yintp yintp-known)
        (if (equal yrd '(t))
            (mv (bfr-or (bfr-=-ss yin nil)
                        (bfr-=-uu yid nil)) t)
          (mv nil nil)))
       (negtest (gtests negp hyp))
       ((unless (and yintp-known
                     (not (gtests-unknown negtest))))
        (g-apply 'int-set-sign (gl-list negp y)))
       (negbfr (gtests-nonnil negtest))
       (ybits (bfr-ite-bss-fn yintp yrn nil))
       (ylen (bfr-integer-length-s ybits))
       (resbits (logapp-uss 1 ylen ybits (bfr-ite-bss-fn negbfr '(t) '(nil)))))
    (mk-g-number (rlist-fix resbits))))


(local (defthm bfr-integer-length-s-correct-v2n
         (equal (bfr-list->u (bfr-integer-length-s x) env)
                (integer-length (bfr-list->s x env)))
         :hints(("Goal" :use ((:instance bfr-integer-length-s-correct))
                 :in-theory (disable bfr-integer-length-s-correct)))))

(local (defthm integer-length-zip
         (implies (zip x)
                  (equal (integer-length x) 0))))


(defthm g-int-set-sign-of-number-correct
  (implies (and (bfr-eval hyp (car env))
                (general-numberp y))
           (equal (eval-g-base (g-int-set-sign-of-number negp y hyp) env)
                  (int-set-sign (eval-g-base negp env)
                                (eval-g-base y env))))
  :hints (("goal" :in-theory (e/d* ((:ruleset general-object-possibilities)
                                    int-set-sign)
                                   (general-numberp
                                    bfr-list->s-when-gte-0
                                    general-number-components))
           :do-not-induct t)))

(in-theory (disable g-int-set-sign-of-number))


(def-g-binary-op int-set-sign
  (b* ((i-num (if (general-numberp i) i 0)))
    (g-int-set-sign-of-number negp i-num hyp)))

(verify-g-guards
 int-set-sign
 :hints `(("Goal" :in-theory
           (disable* ,gfn
                     (:rules-of-class :type-prescription :here)))))

(local (defthm int-set-sign-non-acl2-number
         (implies (not (acl2-numberp i))
                  (equal (int-set-sign negp i)
                         (int-set-sign negp 0)))
         :hints(("Goal" :in-theory (enable int-set-sign)))))

(def-g-correct-thm int-set-sign eval-g-base
   :hints `(("Goal" :in-theory (e/d* (general-concretep-atom
                                      (:ruleset general-object-possibilities))
                                     ((:definition ,gfn)
                                      general-numberp-eval-to-numberp
                                      general-boolean-value-correct
                                      bool-cond-itep-eval
                                      boolean-listp
                                      eval-g-base-alt-def
                                      components-to-number-alt-def
                                      member-equal
                                      general-number-components-ev
                                      general-concretep-def
                                      general-concretep-def
                                      rationalp-implies-acl2-numberp
                                      hons-assoc-equal
                                      default-car default-cdr
                                      bfr-eval-list-consts
                                      mv-nth-cons-meta
                                      possibilities-for-x-5
                                      possibilities-for-x-3
                                      general-boolean-value-cases
                                      (:rules-of-class :type-prescription :here))
                                     ((:type-prescription bfr-eval)
                                      eval-g-base-non-cons))
             :induct (,gfn negp i hyp clk)
             :expand ((,gfn negp i hyp clk)))
           (and stable-under-simplificationp
                (intersectp-equal '((not (equal (tag$inline negp) ':g-ite))
                                    (not (general-concretep negp)))
                                  clause)
                '(:expand ((eval-g-base negp env))))
           (and stable-under-simplificationp
                (intersectp-equal '((not (equal (tag$inline i) ':g-ite))
                                    (not (general-concretep i)))
                                  clause)
                '(:expand ((eval-g-base i env))))))

  

(defund g-ifix-of-number (i)
  (declare (xargs :guard (general-numberp i)))
  (b* (((mv irn ird iin iid)
        (general-number-components i))
       ((mv iintp iintp-known)
        (if (equal ird '(t))
            (mv (bfr-or (bfr-=-ss iin nil)
                        (bfr-=-uu iid nil)) t)
          (mv nil nil)))
       ((unless iintp-known) (mv t nil)) ;; error
       ;; ifix
       (ibits (bfr-ite-bss-fn iintp irn nil)))
    (mv nil (mk-g-number ibits))))

(defthm g-ifix-of-number-correct
  (b* (((mv erp res) (g-ifix-of-number i)))
    (implies (and (not erp)
                  (general-numberp i))
             (equal (eval-g-base res env)
                    (ifix (eval-g-base i env)))))
  :hints(("Goal" :in-theory (enable g-ifix-of-number))))



(def-g-fn maybe-integer
  `(b* (((when (and (general-concretep i)
                    (general-concretep x)
                    (general-concretep intp)))
         (g-concrete-quote
          (ec-call (maybe-integer (general-concrete-obj i)
                                  (general-concrete-obj x)
                                  (general-concrete-obj intp)))))
        ;; ((unless (or (atom intp)
        ;;              (not (member-eq (tag intp) '(:g-ite :g-var :g-apply)))))
        ;;  (if (and (eq (tag intp) :g-ite)
        ;;           (not (zp clk)))
        ;;      (let* ((test (g-ite->test intp))
        ;;             (then (g-ite->then intp))
        ;;             (else (g-ite->else intp)))
        ;;        (g-if test
        ;;              (,gfn i x then hyp clk)
        ;;              (,gfn i x else hyp clk)))
        ;;    (g-apply 'maybe-integer (gl-list i x intp))))
        ((when (and (consp i)
                    (member (tag i) '(:g-ite :g-var :g-apply))))
         (if (and (eq (tag i) :g-ite)
                  (not (zp clk)))
             (let* ((test (g-ite->test i))
                    (then (g-ite->then i))
                    (else (g-ite->else i)))
               (g-if test
                     (,gfn then x intp hyp clk)
                     (,gfn else x intp hyp clk)))
           (g-apply 'maybe-integer (gl-list i x intp))))
        ;; ((when (and (consp x) (eq (tag x) :g-ite)))
        ;;  (if (not (zp clk))
        ;;      (let* ((test (g-ite->test x))
        ;;             (then (g-ite->then x))
        ;;             (else (g-ite->else x)))
        ;;        (g-if test
        ;;              (,gfn i then intp hyp clk)
        ;;              (,gfn i else intp hyp clk)))
        ;;    (g-apply 'maybe-integer (gl-list i x intp))))
        (i (if (general-numberp i) i 0))
        ((mv undef ifix) (g-ifix-of-number i))
        ((when undef)
         (g-apply 'maybe-integer (gl-list i x intp))))
     (g-if intp
           ifix
           (g-apply 'maybe-integer (gl-list i x intp)))))



(verify-g-guards
 maybe-integer
 :hints `(("Goal" :in-theory
           (disable* ,gfn
                     (:rules-of-class :type-prescription :here)))))

(def-g-correct-thm maybe-integer eval-g-base
   :hints `(("Goal" :in-theory (e/d* (general-concretep-atom
                                      maybe-integer
                                      (:ruleset general-object-possibilities))
                                     ((:definition ,gfn)
                                      (g-ifix-of-number)
                                      general-numberp-eval-to-numberp
                                      general-boolean-value-correct
                                      bool-cond-itep-eval
                                      boolean-listp
                                      eval-g-base-alt-def
                                      components-to-number-alt-def
                                      member-equal
                                      general-number-components-ev
                                      general-concretep-def
                                      general-concretep-def
                                      rationalp-implies-acl2-numberp
                                      hons-assoc-equal
                                      default-car default-cdr
                                      bfr-eval-list-consts
                                      mv-nth-cons-meta
                                      possibilities-for-x-5
                                      possibilities-for-x-3
                                      general-boolean-value-cases
                                      (:rules-of-class :type-prescription :here))
                                     ((:type-prescription bfr-eval)
                                      eval-g-base-non-cons))
             :induct (,gfn i x intp hyp clk)
             :expand ((,gfn i x intp hyp clk)))
           (and stable-under-simplificationp
                (intersectp-equal '((not (equal (tag$inline i) ':g-ite))
                                    (not (general-concretep i))
                                    (general-numberp i))
                                  clause)
                '(:expand ((eval-g-base i env))))
           (and stable-under-simplificationp
                (intersectp-equal '((not (equal (tag$inline intp) ':g-ite))
                                    (not (general-concretep intp)))
                                  clause)
                '(:expand ((eval-g-base intp env))))
           (and stable-under-simplificationp
                (intersectp-equal '((not (equal (tag$inline x) ':g-ite))
                                    (not (general-concretep x)))
                                  clause)
                '(:expand ((eval-g-base x env))))))

