


(in-package "GL")

(include-book "bfr")

;; (include-book "tools/with-arith5-help" :dir :system)

;; (allow-arith5-help)

;; (local (include-book "ihs/quotient-remainder-lemmas" :dir :system))
;; (local (include-book "ihs/math-lemmas" :dir :system))
(local (in-theory (disable floor)))
(include-book "ihs/logops-definitions" :dir :system)
(include-book "centaur/misc/arith-equivs" :dir :system)
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

;; (in-theory (disable (bfr-listp)))

(add-bfr-eval-pat (bfr-eval-list & env))

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





(defn v2i (v)
  (declare (xargs :guard-hints (("goal" :in-theory (enable logcons)))))
  (mbe :logic (if (atom (cdr v))
                  (if (car v) -1 0)
                (logcons (acl2::bool->bit (car v))
                         (v2i (cdr v))))
       :exec
       (if (atom v)
           0
         (if (atom (cdr v))
             (if (car v) -1 0)
           (logcons (acl2::bool->bit (car v))
                         (v2i (cdr v)))))))

(defn i2v (n)
  (declare (xargs :measure (integer-length n)
                  :hints(("Goal" :in-theory (enable acl2::integer-length**)))))
  (cond ((eql 0 (ifix n)) '(nil))
        ((eql n -1) '(t))
        (t (cons (equal (logcar n) 1) (i2v (logcdr n))))))
      
  ;; (if (eql (ifix n) 0)
  ;;     '(nil)
  ;;   (if (eql n -1)
  ;;       '(t)
  ;;     (cons (logbitp 0 n)
  ;;           (i2v (ash n -1))))))


(defthm v2i-repeat-last
  (equal (v2i (append v (last v)))
         (v2i v))
  :hints(("Goal" :in-theory (enable append))))

(defthm v2i-i2v
  (equal (v2i (i2v i)) (ifix i))
  :hints (("goal" :in-theory (e/d () ((:definition i2v)))
           :induct (i2v i)
           :expand ((i2v i)))))

(defn sfix (v)
  (mbe :logic (if (atom (cdr v))
                  (list (if (car v) t nil))
                (let ((rst (sfix (cdr v)))
                      (car (if (car v) t nil)))
                  (if (and (atom (cdr rst)) (eq (car rst) car))
                      rst
                    (cons car rst))))
       :exec (if (atom v)
                 (list nil)
               (if (atom (cdr v))
                   (list (if (car v) t nil))
                 (let ((rst (sfix (cdr v)))
                       (car (if (car v) t nil)))
                   (if (and (atom (cdr rst)) (eq (car rst) car))
                       rst
                     (cons car rst)))))))

(defthm v2i-sfix
  (equal (v2i (sfix n))
         (v2i n)))

(defthmd car-of-sfix
  (equal (car (sfix x))
         (if (car x) t nil)))
           

(defthm i2v-v2i
  (equal (i2v (v2i v)) (sfix v))
  :hints (("goal" :in-theory (e/d (car-of-sfix)))))




(defn v2n (v)
  (if (atom v)
      0
    (logcons (acl2::bool->bit (car v))
             (v2n (cdr v)))))

(defn n2v (n)
  (if (eql (nfix n) 0)
      nil
    (cons (equal 1 (logcar n))
          (n2v (logcdr n)))))


(defthm v2n-n2v
  (equal (v2n (n2v n)) (nfix n)))


(defn ufix (v)
  (if (atom v)
      nil
    (let ((rst (ufix (cdr v)))
          (car (if (car v) t nil)))
      (if (and (eq rst nil) (eq car nil))
          nil
        (cons car rst)))))

(defthm v2n-ufix
  (equal (v2n (ufix v))
         (v2n v)))

(defthm v2n-nonneg
  (<= 0 (v2n v))
  :rule-classes (:rewrite :linear :type-prescription))

(in-theory (disable (:rewrite v2n-nonneg)
                    (:linear v2n-nonneg)))

(defthm n2v-v2n
  (equal (n2v (v2n v)) (ufix v)))


(in-theory (disable v2n n2v v2i i2v ash logbitp))



(defthm us-to-num
  (equal (v2n (bfr-eval-list (n2v n) env))
         (nfix n))
  :hints(("Goal" :in-theory (enable n2v v2n logbitp ash natp))))

(defthm i2v-to-num
  (equal (v2i (bfr-eval-list (i2v n) env))
         (ifix n))
  :hints(("Goal" :in-theory (enable i2v v2i logbitp
                                    ash natp))))


