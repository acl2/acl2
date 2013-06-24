


(in-package "GL")

(include-book "bfr")

;; (include-book "tools/with-arith5-help" :dir :system)

;; (allow-arith5-help)

;; (local (include-book "ihs/quotient-remainder-lemmas" :dir :system))
;; (local (include-book "ihs/math-lemmas" :dir :system))
(local (in-theory (disable floor)))
(include-book "ihs/logops-definitions" :dir :system)
(include-book "centaur/misc/arith-equiv-defs" :dir :system)
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))

;; (defun bfr-listp1 (x)
;;   (declare (Xargs :guard t))
;;   (if (atom x)
;;       (eq x nil)
;;     (and (bfr-p (car x))
;;          (bfr-listp1 (cdr x)))))

;; (defun bfr-listp (x)
;;   (declare (xargs :guard t))
;;   (mbe :logic (if (atom x)
;;                   (eq x nil)
;;                 (and (bfr-p (car x))
;;                      (bfr-listp (cdr x))))
;;        :exec (or (boolean-listp x)
;;                  (bfr-listp1 x))))

;; (defthm bfr-p-car-when-bfr-listp
;;   (implies (bfr-listp x)
;;            (bfr-p (car x))))

;; (defthm bfr-listp-cdr-when-bfr-listp
;;   (implies (bfr-listp x)
;;            (bfr-listp (cdr x))))

;; (defthm bfr-listp-cons
;;   (implies (and (bfr-p x) (bfr-listp y))
;;            (bfr-listp (cons x y))))

;; (defthm boolean-list-bfr-listp
;;   (implies (and (syntaxp (quotep x))
;;                 (boolean-listp x))
;;            (bfr-listp x)))


(defun bfr-eval-list (x env)
  (declare (xargs :guard t))
  (if (atom x)
      nil
    (cons (bfr-eval (car x) env)
          (bfr-eval-list (cdr x) env))))

(defthmd boolean-list-bfr-eval-list
  (implies (boolean-listp x)
           (equal (bfr-eval-list x env) x))
  :hints (("goal" :in-theory (enable bfr-eval-list boolean-listp))))

(defthm boolean-list-bfr-eval-list-const
  (implies (and (syntaxp (quotep x))
                (boolean-listp x))
           (equal (bfr-eval-list x env) x))
  :hints (("goal" :in-theory (enable bfr-eval-list boolean-listp))))

(defthm bfr-eval-list-of-list-fix
  (equal (bfr-eval-list (acl2::list-fix x) env)
         (bfr-eval-list x env)))


(defund bfr-max-nat-var-list (x)
  (declare (xargs :guard t))
  (if (atom x)
      0
    (max (bfr-max-nat-var (car x))
         (bfr-max-nat-var-list (cdr x)))))

(defthm bfr-eval-list-of-bfr-set-var-past-max-nat
  (implies (and (<= (bfr-max-nat-var-list x) var)
                (natp var))
           (equal (bfr-eval-list x (bfr-set-var var val env))
                  (bfr-eval-list x env)))
  :hints(("Goal" :in-theory (enable bfr-max-nat-var-list))))


(defthm bfr-max-nat-var-of-car
  (<= (bfr-max-nat-var (car x)) (bfr-max-nat-var-list x))
  :hints(("Goal" :in-theory (enable bfr-max-nat-var-list)))
  :rule-classes :linear)

(defthm bfr-max-nat-var-list-of-car-rw
  (implies (<= (bfr-max-nat-var-list x) n)
           (<= (bfr-max-nat-var (car x)) n)))

(defthm bfr-max-nat-var-of-cdr
  (<= (bfr-max-nat-var-list (cdr x)) (bfr-max-nat-var-list x))
  :hints(("Goal" :in-theory (enable bfr-max-nat-var-list)))
  :rule-classes :linear)

(defthm bfr-max-nat-var-list-of-cdr-rw
  (implies (<= (bfr-max-nat-var-list x) n)
           (<= (bfr-max-nat-var-list (cdr x)) n)))







(defund-inline scdr (v)
  (declare (xargs :guard t))
  (mbe :logic (if (atom (cdr v)) v (cdr v))
       :exec (if (or (atom v) (atom (cdr v))) v (cdr v))))

(defthm bfr-max-nat-var-list-of-scdr
  (<= (bfr-max-nat-var-list (scdr x)) (bfr-max-nat-var-list x))
  :hints(("Goal" :in-theory (enable bfr-max-nat-var-list scdr)))
  :rule-classes :linear)

(defthm bfr-max-nat-var-list-of-scdr-rw
  (implies (<= (bfr-max-nat-var-list x) n)
           (<= (bfr-max-nat-var-list (scdr x)) n)))

(defthm scdr-of-list-fix
  (equal (scdr (acl2::list-fix x))
         (acl2::list-fix (scdr x)))
  :hints(("Goal" :in-theory (enable scdr))))


(defund-inline s-endp (v)
  (declare (xargs :guard t))
  (mbe :logic (atom (cdr v)) :exec (or (atom v) (atom (cdr v)))))

(defun-inline first/rest/end (x)
  (declare (xargs :guard t
                  :guard-hints ('(:in-theory (enable scdr s-endp)))))
  (mbe :logic (mv (car x) (scdr x) (s-endp x))
       :exec (cond ((atom x)       (mv nil x t))
                   ((atom (cdr x)) (mv (car x) x t))
                   (t              (mv (car x) (cdr x) nil)))))

(defthm s-endp-of-list-fix
  (equal (s-endp (acl2::list-fix x))
         (s-endp x))
  :hints(("Goal" :in-theory (enable s-endp))))

(defthm scdr-count-strong
  (implies (not (s-endp v))
           (< (acl2-count (scdr v)) (acl2-count v)))
  :hints(("Goal" :in-theory (enable s-endp scdr)))
  :rule-classes :linear)

(defthm scdr-count-weak
  (<= (acl2-count (scdr v)) (acl2-count v))
  :hints(("Goal" :in-theory (enable s-endp scdr)))
  :rule-classes :linear)

(defthm scdr-len-strong
  (implies (not (s-endp v))
           (< (len (scdr v)) (len v)))
  :hints(("Goal" :in-theory (enable s-endp scdr)))
  :rule-classes :linear)

(defthm scdr-len-weak
  (<= (len (scdr v)) (len v))
  :hints(("Goal" :in-theory (enable s-endp scdr)))
  :rule-classes :linear)



(defthm s-endp-of-scdr
  (implies (s-endp b)
           (s-endp (scdr b)))
  :hints(("Goal" :in-theory (enable s-endp scdr))))

(defun bool->sign (x)
  (declare (xargs :guard t))
  (if x -1 0))


(defun bfr-list->s (x env)
  (declare (xargs :guard t))
  (b* (((mv first rest end) (first/rest/end x)))
    (if end
        (bool->sign (bfr-eval first env))
      (logcons (acl2::bool->bit (bfr-eval first env))
               (bfr-list->s rest env)))))


(defthm bfr-list->s-of-list-fix
  (equal (bfr-list->s (acl2::list-fix x) env)
         (bfr-list->s x env)))

(defund bfr-snorm (v)
  (declare (xargs :guard t))
  (if (atom v) '(nil) v))

(defthm s-endp-of-bfr-snorm
  (equal (s-endp (bfr-snorm v))
         (s-endp v))
  :hints(("Goal" :in-theory (enable s-endp bfr-snorm))))

(defthm scdr-of-bfr-snorm
  (equal (scdr (bfr-snorm v))
         (bfr-snorm (scdr v)))
  :hints(("Goal" :in-theory (enable scdr bfr-snorm))))

(defthm car-of-bfr-snorm
  (equal (car (bfr-snorm v))
         (car v))
  :hints(("Goal" :in-theory (enable bfr-snorm))))

(defthm bfr-list->s-of-bfr-snorm
  (equal (bfr-list->s (bfr-snorm v) env)
         (bfr-list->s v env)))

(defund bfr-scons (b v)
  (declare (xargs :guard t))
  (if (atom v)
      (if b (list b nil) '(nil))
    (if (and (atom (cdr v))
             (hons-equal (car v) b))
        v
      (cons b v))))

(defthm scdr-of-bfr-scons
  (equal (scdr (bfr-scons b v))
         (bfr-snorm v))
  :hints(("Goal" :in-theory (enable bfr-snorm bfr-scons scdr))))

(defthm s-endp-of-bfr-scons
  (equal (s-endp (bfr-scons b v))
         (and (s-endp v)
              (hqual b (car v))))
  :hints(("Goal" :in-theory (enable s-endp bfr-scons))))

(defthm car-of-bfr-scons
  (equal (car (bfr-scons b v))
         b)
  :hints(("Goal" :in-theory (enable bfr-scons))))

(defthm bfr-list->s-of-bfr-scons
  (equal (bfr-list->s (bfr-scons b x) env)
         (logcons (acl2::bool->bit (bfr-eval b env))
                  (bfr-list->s x env)))
  :hints(("Goal" ;:in-theory (enable bfr-scons scdr s-endp)
          :expand ((bfr-list->s (bfr-scons b x) env))
          :do-not-induct t)))

(defthm bfr-max-nat-var-list-of-bfr-scons
  (implies (and (<= (bfr-max-nat-var b) n)
                (<= (bfr-max-nat-var-list x) n))
           (<= (bfr-max-nat-var-list (bfr-scons b x)) n))
  :hints(("Goal" :in-theory (e/d (bfr-scons bfr-max-nat-var-list)
                                 ((bfr-max-nat-var-list)))))
  :rule-classes (:rewrite (:linear :match-free :all)))

(defund bfr-sterm (b)
  (declare (xargs :guard t))
  (list b))

(defthm s-endp-of-bfr-sterm
  (equal (s-endp (bfr-sterm b)) t)
  :hints(("Goal" :in-theory (enable s-endp bfr-sterm))))

(defthm scdr-of-bfr-sterm
  (equal (scdr (bfr-sterm b))
         (bfr-sterm b))
  :hints(("Goal" :in-theory (enable scdr bfr-sterm))))

(defthm car-of-bfr-sterm
  (equal (car (bfr-sterm b))
         b)
  :hints(("Goal" :in-theory (enable bfr-sterm))))


(defthm bfr-list->s-of-bfr-sterm
  (equal (bfr-list->s (bfr-sterm b) env)
         (bool->sign (bfr-eval b env))))

(defthm bfr-max-nat-var-list-of-bfr-sterm
  (equal (bfr-max-nat-var-list (bfr-sterm b))
         (bfr-max-nat-var b))
  :hints(("Goal" :in-theory (enable bfr-sterm bfr-max-nat-var-list))))

(defthm scdr-when-s-endp
  (implies (s-endp x)
           (equal (scdr x) x))
  :hints(("Goal" :in-theory (enable scdr s-endp)))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthmd bfr-list->s-of-scdr
  (equal (bfr-list->s (scdr x) env)
         (logcdr (bfr-list->s x env))))

(defthm logcdr-of-bfr-list->s
  (equal (logcdr (bfr-list->s x env))
         (bfr-list->s (scdr x) env)))

(defthm logcar-of-bfr-list->s
  (equal (logcar (bfr-list->s x env))
         (acl2::bool->bit (bfr-eval (car x) env))))

(defthm bfr-list->s-when-s-endp
  (implies (s-endp x)
           (equal (bfr-list->s x env)
                  (bool->sign (bfr-eval (car x) env))))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))


(defn i2v (n)
  (declare (xargs :measure (integer-length n)
                  :hints(("Goal" :in-theory (enable acl2::integer-length**)))))
  (cond ((eql 0 (ifix n)) '(nil))
        ((eql n -1) '(t))
        (t (bfr-scons (equal (logcar n) 1) (i2v (logcdr n))))))

(defthm bfr-list->s-of-i2v
  (equal (bfr-list->s (i2v n) env)
         (ifix n)))

(defthm bfr-max-nat-var-list-of-i2v
  (equal (bfr-max-nat-var-list (i2v n)) 0)
  :hints(("Goal" :in-theory (e/d (bfr-max-nat-var-list bfr-scons bfr-max-nat-var)
                                 ((bfr-max-nat-var-list))))))



(defthm bfr-list->s-of-bfr-set-var-past-max-nat
  (implies (and (<= (bfr-max-nat-var-list x) var)
                (natp var))
           (equal (bfr-list->s x (bfr-set-var var val env))
                  (bfr-list->s x env)))
  :hints(("Goal" :in-theory (enable bfr-max-nat-var-list))))












(defmacro car/cdr (x)
  `(let* ((a ,x))
     (mbe :logic (mv (car a) (cdr a))
          :exec (if (atom a) (mv nil nil) (mv (car a) (cdr a))))))

(defun bfr-list->u (x env)
  (declare (xargs :guard t))
  (if (atom x)
      0
    (logcons (acl2::bool->bit (bfr-eval (car x) env))
             (bfr-list->u (cdr x) env))))

(defthm bfr-list->u-of-list-fix
  (equal (bfr-list->u (acl2::list-fix x) env)
         (bfr-list->u x env)))

(defthm bfr-list->u-type
  (natp (bfr-list->u x env))
  :rule-classes :type-prescription)

(in-theory (disable (:t bfr-list->u)))

(defthm bfr-list->u-of-bfr-set-var-past-max-nat
  (implies (and (<= (bfr-max-nat-var-list x) var)
                (natp var))
           (equal (bfr-list->u x (bfr-set-var var val env))
                  (bfr-list->u x env)))
  :hints(("Goal" :in-theory (enable bfr-max-nat-var-list))))

;; (in-theory (disable (bfr-listp)))

(add-bfr-eval-pat (bfr-eval-list & env))
(add-bfr-eval-pats (bfr-list->u & env))
(add-bfr-eval-pats (bfr-list->s & env))

(defund bfr-ucons (b x)
  (declare (xargs :guard t))
  (if (and (atom x) (not b))
      nil
    (cons b x)))

(defthm bfr-list->u-of-bfr-ucons
  (equal (bfr-list->u (bfr-ucons b x) env)
         (logcons (acl2::bool->bit (bfr-eval b env))
                  (bfr-list->u x env)))
  :hints(("Goal" :in-theory (enable bfr-ucons))))

(defthm bfr-max-nat-var-list-of-bfr-ucons
  (implies (and (<= (bfr-max-nat-var b) n)
                (<= (bfr-max-nat-var-list x) n))
           (<= (bfr-max-nat-var-list (bfr-ucons b x)) n))
  :hints(("Goal" :in-theory (enable bfr-ucons bfr-max-nat-var-list)))
  :rule-classes (:rewrite (:linear :match-free :all)))


(defn n2v (n)
  (if (eql (nfix n) 0)
      nil
    (bfr-ucons (equal 1 (logcar n))
               (n2v (logcdr n)))))

(defthm bfr-list->u-of-n2v
  (equal (bfr-list->u (n2v n) env)
         (nfix n)))

(defthm bfr-max-nat-var-list-of-n2v
  (equal (bfr-max-nat-var-list (n2v n)) 0)
  :hints(("Goal" :in-theory (e/d (bfr-max-nat-var-list bfr-ucons bfr-max-nat-var)
                                 ((bfr-max-nat-var-list))))))



;; (defun bfr-list-fix (x)
;;   (declare (xargs :guard t))
;;   (if (atom x)
;;       nil
;;     (cons (bfr-fix (car x))
;;           (bfr-list-fix (cdr x)))))

;; (defthm bfr-listp-bfr-list-fix
;;   (bfr-listp (bfr-list-fix x)))

;; (defthm bfr-list-fix-when-bfr-listp
;;   (implies (bfr-listp x)
;;            (equal (bfr-list-fix x) x)))

;; (defthm bfr-eval-list-bfr-list-fix
;;   (equal (bfr-eval-list (bfr-list-fix x) env)
;;          (bfr-eval-list x env))
;;   :rule-classes nil)

;; (defthm consp-bfr-list-fix
;;   (equal (consp (bfr-list-fix x))
;;          (consp x)))

;; (defthm car-bfr-list-fix
;;   (equal (car (bfr-list-fix x))
;;          (bfr-fix (car x))))

;; (defthm cdr-bfr-list-fix
;;   (equal (cdr (bfr-list-fix x))
;;          (bfr-list-fix (cdr x))))

;; (defthm len-bfr-list-fix
;;   (equal (len (bfr-list-fix x)) (len x)))

;; (in-theory (disable bfr-list-fix bfr-listp))

;; (acl2::def-universal-equiv
;;  bfr-list-equiv
;;  :qvars (env)
;;  :equiv-terms ((equal (bfr-eval-list acl2::x env))))

;; (defcong bfr-list-equiv equal (bfr-eval-list x env) 1
;;   :hints (("goal" :in-theory (enable bfr-list-equiv-necc))))


(defun bfr-eval-alist (al vals)
  (declare (xargs :guard t))
  (if (atom al)
      nil
    (if (consp (car al))
        (cons (cons (caar al)
                    (bfr-eval (cdar al) vals))
              (bfr-eval-alist (cdr al) vals))
      (bfr-eval-alist (cdr al) vals))))



(defun boolfix (x)
  (declare (xargs :guard t))
  (if x t nil))

(defcong iff equal (boolfix x) 1)

(defthm boolfix-under-iff
  (iff (boolfix x) x))
  




;; useful for dealing with unsigned and signed bit vectors, resp.



;; (defund scons (b v)
;;   (declare (xargs :guard t))
;;   (let* ((b (boolfix b)))
;;     (if (atom v)
;;         (if b '(t nil) '(nil))
;;       (if (and (atom (cdr v))
;;                (eq (boolfix (car v)) b))
;;           v
;;         (cons b v)))))

;; (defthm car-of-scons
;;   (iff (car (scons b v))
;;        b)
;;   :hints(("Goal" :in-theory (enable scons))))

;; (defcong iff equal (scons b v) 1
;;   :hints(("Goal" :in-theory (enable scons))))





;; (defund sterm (x)
;;   (declare (xargs :guard t))
;;   (if x '(t) '(nil)))

;; (defthm car-of-sterm
;;   (equal (car (sterm x))
;;          (boolfix x))
;;   :hints(("Goal" :in-theory (enable sterm))))

;; (defcong iff equal (sterm x) 1
;;   :hints(("Goal" :in-theory (enable sterm))))


;; (defn sfix (v)
;;   (declare (xargs :verify-guards nil))
;;   (mbe :logic (if (s-endp v)
;;                   (sterm (car v))
;;                 (scons (car v)
;;                        (sfix (scdr v))))
;;        :exec (if (atom v)
;;                  (list nil)
;;                (if (atom (cdr v))
;;                    (list (if (car v) t nil))
;;                  (let ((rst (sfix (cdr v)))
;;                        (car (if (car v) t nil)))
;;                    (if (and (atom (cdr rst)) (eq (car rst) car))
;;                        rst
;;                      (cons car rst)))))))

;; (defthm consp-sfix
;;   (consp (sfix v))
;;   :hints(("Goal" :in-theory (enable scons s-endp)))
;;   :rule-classes :type-prescription)

;; (defthmd boolean-listp-sfix
;;   (boolean-listp (sfix v))
;;   :hints(("Goal" :in-theory (enable scons sterm))))

;; (local (defthm booleanp-car-sfix
;;          (booleanp (car (sfix v)))
;;          :hints (("goal" :use boolean-listp-sfix))
;;          :rule-classes :type-prescription))

;; (verify-guards sfix :hints(("Goal" :in-theory (enable sterm scons scdr s-endp))))

;; (defun sv-equiv (x y)
;;   (declare (xargs :guard t))
;;   (equal (sfix x) (sfix y)))

;; (defequiv sv-equiv)

;; (defthm sfix-of-scons
;;   (equal (sfix (scons b v))
;;          (scons b (sfix v)))
;;   :hints(("Goal" :in-theory (enable scons scdr s-endp sterm))))

;; (defthm sfix-of-sterm
;;   (equal (sfix (sterm b))
;;          (sterm b))
;;   :hints(("Goal" :in-theory (enable sterm s-endp))))

;; (defthm sfix-of-sfix
;;   (equal (sfix (sfix x)) (sfix x)))

;; (defthm sfix-under-sv-equiv
;;   (sv-equiv (sfix x) x))

;; (defthm car-of-sfix
;;   (equal (car (sfix x))
;;          (boolfix (car x)))
;;   :hints(("Goal" :in-theory (enable scons))))

;; (defcong sv-equiv iff (car x) 1
;;   :hints(("Goal" :in-theory (enable car-of-sfix))))

;; (defcong sv-equiv sv-equiv (scdr x) 1
;;   :hints(("Goal" :in-theory (enable scdr s-endp sterm scons))))


;; (defthm sv-equiv-repeat-last
;;   (sv-equiv (append v (last v))
;;             v)
;;   :hints(("Goal" :in-theory (enable append s-endp scdr scons sterm)
;;           :induct (last v))))


;; ;; (defthm sv-equiv-of-cdr-sfix
;; ;;   (implies (consp (cdr (sfix x)))
;; ;;            (sv-equiv (cdr (sfix x))
;; ;;                      (cdr x)))
;; ;;   :hints(("Goal" :in-theory (enable scons scdr s-endp sterm))))


;; (defthm sterm-when-s-endp
;;   (implies (s-endp x)
;;            (sv-equiv (sterm (car x)) x))
;;   :hints(("Goal" :in-theory (enable s-endp sterm)))
;;   :rule-classes ((:rewrite :backchain-limit-lst 0)))

;; (defthm scons-car-cdr
;;   (sv-equiv (scons (car x) (scdr x))
;;             x)
;;   :hints(("Goal" :in-theory (enable scons scdr s-endp sterm))))

;; (defcong sv-equiv sv-equiv (scons a b) 2)


;; (defthm scdr-of-scons
;;   (sv-equiv (scdr (scons a b))
;;             b)
;;   :hints(("Goal" :in-theory (e/d (scdr scons s-endp)
;;                                  (boolfix sfix))
;;           :use ((:instance sfix (v b))))))



;; (defthmd sv-equiv-of-scons
;;   (equal (sv-equiv (scons a b) c)
;;          (and (iff (car c) a)
;;               (sv-equiv (scdr c) b)))
;;   :hints(("Goal" :in-theory (disable sv-equiv scons-car-cdr)
;;           :use ((:instance scons-car-cdr
;;                  (x (scons a b)))
;;                 (:instance scons-car-cdr
;;                  (x c))))))

;; (defthmd scdr-when-equiv-to-endp
;;   (implies (and (sv-equiv a b)
;;                 (s-endp b))
;;            (sv-equiv (scdr a) b))
;;   :hints(("Goal" :in-theory (disable sv-equiv)))
;;   :rule-classes ((:rewrite :backchain-limit-lst 0)))

;; (defthm scons-sterm
;;   (equal (scons b (sterm b))
;;          (sterm b))
;;   :hints(("Goal" :in-theory (enable scons sterm))))

;; (defthm scdr-sterm
;;   (equal (scdr (sterm b))
;;          (sterm b))
;;   :hints(("Goal" :in-theory (enable scdr sterm))))

;; (defthm scons-equiv-sterm
;;   (and (equal (sv-equiv (scons a b) (sterm c))
;;               (and (iff a c)
;;                    (sv-equiv b (sterm c))))
;;        (equal (sv-equiv (sterm c) (scons a b))
;;               (and (iff a c)
;;                    (sv-equiv b (sterm c)))))
;;   :hints(("Goal" :in-theory (enable sterm scons s-endp sfix scdr))))

;; (defthm sv-equiv-of-sconses
;;   (equal (sv-equiv (scons a b) (scons c d))
;;          (and (iff a c)
;;               (sv-equiv b d)))
;;   :hints(("Goal" :in-theory (enable sterm scons s-endp sfix scdr))))




;; (defn v2i (v)
;;   (declare (xargs :guard-hints (("goal" :in-theory (enable logcons s-endp scdr
;;                                                            acl2::bool->bit)))))
;;   (mbe :logic (if (s-endp v)
;;                   (bool->sign (car v))
;;                 (logcons (acl2::bool->bit (car v))
;;                          (v2i (scdr v))))
;;        :exec
;;        (if (atom v)
;;            0
;;          (if (atom (cdr v))
;;              (if (car v) -1 0)
;;            (logcons (acl2::bool->bit (car v))
;;                     (v2i (cdr v)))))))



;; ;; (defthmd v2i-of-scons
;; ;;   (equal (v2i (scons b v))
;; ;;          (v2i (cons b v)))
;; ;;   :hints(("Goal" :in-theory (enable scons))))








;; (local (defthmd cons-equals-scons-in-i2v
;;          (implies (and (not (zip (logcons b n)))
;;                        (not (equal (logcons b n) -1)))
;;                   (equal (cons (equal b 1) (i2v n))
;;                          (scons (equal b 1) (i2v n))))
;;          :hints(("Goal" :in-theory (enable scons i2v)))))

;; (verify-guards i2v
;;   :hints(("Goal" :in-theory (enable cons-equals-scons-in-i2v))))

;;   ;; (if (eql (ifix n) 0)
;;   ;;     '(nil)
;;   ;;   (if (eql n -1)
;;   ;;       '(t)
;;   ;;     (cons (logbitp 0 n)
;;   ;;           (i2v (ash n -1))))))




;; (defthm v2i-scons
;;   (equal (v2i (scons a b))
;;          (logcons (acl2::bool->bit a) (v2i b)))
;;   :hints(("Goal" :in-theory (enable scons s-endp scdr))))

;; (defthm v2i-i2v
;;   (equal (v2i (i2v i)) (ifix i))
;;   :hints (("goal" :in-theory (e/d () ((:definition i2v)))
;;            :induct (i2v i)
;;            :expand ((i2v i)))))


;; (defthm v2i-sterm
;;   (equal (v2i (sterm x))
;;          (bool->sign x))
;;   :hints(("Goal" :in-theory (enable sterm))))


;; (defthm v2i-sfix
;;   (equal (v2i (sfix n))
;;          (v2i n)))

;; (defcong sv-equiv equal (sfix x) 1)

;; (defcong sv-equiv equal (v2i x) 1
;;   :hints (("goal" :use ((:instance v2i-sfix (n x))
;;                         (:instance v2i-sfix (n x-equiv)))
;;            :in-theory (disable v2i-sfix))))


;; (defthm i2v-v2i
;;   (equal (i2v (v2i v)) (sfix v)))




;; (defn v2n (v)
;;   (if (atom v)
;;       0
;;     (logcons (acl2::bool->bit (car v))
;;              (v2n (cdr v)))))

;; (defund ucons (b x)
;;   (declare (xargs :guard t))
;;   (if (and (atom x) (not b))
;;       nil
;;     (cons (boolfix b) x)))

;; (defthm v2n-of-ucons
;;   (equal (v2n (ucons b v))
;;          (logcons (acl2::bool->bit b)
;;                   (v2n v)))
;;   :hints(("Goal" :in-theory (enable ucons))))

;; (defthm car-of-ucons
;;   (equal (car (ucons b v))
;;          (boolfix b))
;;   :hints(("Goal" :in-theory (enable ucons))))

;; (defcong iff equal (ucons b v) 1
;;   :hints(("Goal" :in-theory (enable ucons))))




;; (local (defthm cons-is-ucons-in-n2v
;;          (implies (not (zp (logcons b n)))
;;                   (equal (cons (equal 1 b) (n2v n))
;;                          (ucons (equal 1 b) (n2v n))))
;;          :hints(("Goal" :in-theory (enable ucons)))))

;; (verify-guards n2v)


;; (defthm v2n-n2v
;;   (equal (v2n (n2v n)) (nfix n)))



;; (defn ufix (v)
;;   (declare (xargs :verify-guards nil))
;;   (mbe :logic (if (atom v)
;;                   nil
;;                 (ucons (car v) (ufix (cdr v))))
;;        :exec
;;        (if (atom v)
;;            nil
;;          (let ((rst (ufix (cdr v)))
;;                (car (if (car v) t nil)))
;;            (if (and (eq rst nil) (eq car nil))
;;                nil
;;              (cons car rst))))))

;; (verify-guards ufix :hints (("goal" :in-theory (enable ucons))))

;; (defthm ufix-of-ucons
;;   (equal (ufix (ucons a b))
;;          (ucons a (ufix b)))
;;   :hints(("Goal" :in-theory (enable ucons))))

;; (defthm v2n-ufix
;;   (equal (v2n (ufix v))
;;          (v2n v)))

;; (defun uv-equiv (x y)
;;   (declare (xargs :guard t))
;;   (equal (ufix x) (ufix y)))

;; (defequiv uv-equiv)

;; (defcong uv-equiv equal (ufix x) 1)

;; (defcong uv-equiv equal (v2n x) 1
;;   :hints (("goal" :use ((:instance v2n-ufix (v x))
;;                         (:instance v2n-ufix (v x-equiv)))
;;            :in-theory (disable v2n-ufix))))

;; (defthm ufix-of-ufix
;;   (equal (ufix (ufix x)) (ufix x)))


;; (defcong uv-equiv uv-equiv (cdr x) 1
;;   :hints(("Goal" :in-theory (enable ucons))))

;; (defcong uv-equiv iff (car a) 1
;;   :hints(("Goal" :in-theory (enable ucons))))

;; (defthmd uv-equiv-implies-cars-equiv
;;   (implies (not (iff (car a) (car b)))
;;            (not (uv-equiv a b)))
;;   :hints(("Goal" :in-theory (enable ucons))))

;; (defthmd equal-of-ucons
;;   (equal (uv-equiv (ucons x y) z)
;;          (and (iff (car z) x)
;;               (uv-equiv y (cdr z))))
;;   :hints(("Goal" :in-theory (enable ucons))))



;; (defthm v2n-nonneg
;;   (<= 0 (v2n v))
;;   :rule-classes (:rewrite :linear :type-prescription))

;; (in-theory (disable (:rewrite v2n-nonneg)
;;                     (:linear v2n-nonneg)))

;; (defthm n2v-v2n
;;   (equal (n2v (v2n v)) (ufix v)))


;; (in-theory (disable v2n n2v v2i i2v ash logbitp))





;; ;; (defthm us-to-num
;; ;;   (equal (v2n (bfr-eval-list (n2v n) env))
;; ;;          (nfix n))
;; ;;   :hints(("Goal" :in-theory (enable n2v v2n logbitp ash natp))))

;; ;; (defthm i2v-to-num
;; ;;   (equal (v2i (bfr-eval-list (i2v n) env))
;; ;;          (ifix n))
;; ;;   :hints(("Goal" :in-theory (enable i2v v2i logbitp
;; ;;                                     ash natp))))

;; (defthm bfr-max-nat-var-list-of-i2v
;;   (equal (bfr-max-nat-var-list (i2v n)) 0)
;;   :hints(("Goal" :in-theory (e/d (bfr-max-nat-var-list i2v scons)
;;                                  ((bfr-max-nat-var-list) (bfr-max-nat-var))))))

;; (defthm bfr-max-nat-var-list-of-n2v
;;   (equal (bfr-max-nat-var-list (n2v n)) 0)
;;   :hints(("Goal" :in-theory (e/d (bfr-max-nat-var-list n2v ucons)
;;                                  ((bfr-max-nat-var-list) (bfr-max-nat-var))))))

;; (defthm bfr-max-nat-var-list-of-ufix
;;   (equal (bfr-max-nat-var-list (ufix x)) 0)
;;   :hints(("Goal" :in-theory (e/d (bfr-max-nat-var-list ufix ucons)
;;                                  ((bfr-max-nat-var-list) (bfr-max-nat-var))))))

;; (defthm bfr-max-nat-var-list-of-sfix
;;   (equal (bfr-max-nat-var-list (sfix x)) 0)
;;   :hints(("Goal" :in-theory (e/d (bfr-max-nat-var-list sfix scons sterm)
;;                                  ((bfr-max-nat-var-list) (bfr-max-nat-var))))))

;; (defthm bfr-max-nat-var-of-car-when-s-endp
;;   (implies (s-endp x)
;;            (equal (bfr-max-nat-var (car x))
;;                   (bfr-max-nat-var-list x)))
;;   :hints(("Goal" :in-theory (enable s-endp bfr-max-nat-var-list)))
;;   :rule-classes ((:rewrite :backchain-limit-lst 0)))

;; (defthm bfr-max-nat-var-list-of-append
;;   (equal (bfr-max-nat-var-list (append x y))
;;          (max (bfr-max-nat-var-list x)
;;               (bfr-max-nat-var-list y)))
;;   :hints(("Goal" :in-theory (e/d (bfr-max-nat-var-list)))))

;; (defthm bfr-max-nat-var-list-of-last
;;   (<= (bfr-max-nat-var-list (last x)) (bfr-max-nat-var-list x))
;;   :hints(("Goal" :in-theory (enable bfr-max-nat-var-list)))
;;   :rule-classes (:rewrite :linear))



;; (acl2::def-universal-equiv
;;  bfr-sv-equiv
;;  :qvars (env)
;;  :equiv-terms ((sv-equiv (bfr-eval-list x env))))

;; (acl2::def-universal-equiv
;;  bfr-uv-equiv
;;  :qvars (env)
;;  :equiv-terms ((uv-equiv (bfr-eval-list x env))))

;; (defcong bfr-sv-equiv sv-equiv (bfr-eval-list x env) 1
;;   :hints(("Goal" :in-theory (disable sv-equiv)
;;           :use ((:instance bfr-sv-equiv-necc (y x-equiv))))))

;; (defcong bfr-uv-equiv uv-equiv (bfr-eval-list x env) 1
;;   :hints(("Goal" :in-theory (disable uv-equiv)
;;           :use ((:instance bfr-uv-equiv-necc (y x-equiv))))))

;; (defthm scdr-when-endp-under-bfr-sv-equiv
;;   (implies (s-endp x)
;;            (bfr-sv-equiv (scdr x) x))
;;   :hints(("Goal" :in-theory (e/d (bfr-sv-equiv bfr-eval-list)))))

;; (defthm scdr-when-endp
;;   (implies (s-endp b)
;;            (sv-equiv (scdr b) b))
;;   :hints(("Goal" :in-theory (enable s-endp scdr)))
;;   :rule-classes ((:rewrite :backchain-limit-lst 0)))
