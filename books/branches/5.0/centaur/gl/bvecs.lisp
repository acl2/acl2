


(in-package "GL")

(include-book "bfr")

;; (include-book "tools/with-arith5-help" :dir :system)

;; (allow-arith5-help)

(local (include-book "ihs/quotient-remainder-lemmas" :dir :system))
(local (include-book "ihs/math-lemmas" :dir :system))
(local (in-theory (disable floor)))



(defun bfr-listp1 (x)
  (declare (Xargs :guard t))
  (if (atom x)
      (eq x nil)
    (and (bfr-p (car x))
         (bfr-listp1 (cdr x)))))

(defun bfr-listp (x)
  (declare (xargs :guard t))
  (mbe :logic (if (atom x)
                  (eq x nil)
                (and (bfr-p (car x))
                     (bfr-listp (cdr x))))
       :exec (or (boolean-listp x)
                 (bfr-listp1 x))))

(defthm bfr-p-car-when-bfr-listp
  (implies (bfr-listp x)
           (bfr-p (car x))))

(defthm bfr-listp-cdr-when-bfr-listp
  (implies (bfr-listp x)
           (bfr-listp (cdr x))))

(defthm bfr-listp-cons
  (implies (and (bfr-p x) (bfr-listp y))
           (bfr-listp (cons x y))))

(defthm boolean-list-bfr-listp
  (implies (and (syntaxp (quotep x))
                (boolean-listp x))
           (bfr-listp x)))


(defun bfr-eval-list (x env)
  (declare (xargs :guard (bfr-listp x)))
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

(in-theory (disable (bfr-listp)))

(add-bfr-eval-pat (bfr-eval-list & env))

(defun bfr-list-fix (x)
  (declare (xargs :guard t))
  (if (atom x)
      nil
    (cons (bfr-fix (car x))
          (bfr-list-fix (cdr x)))))

(defthm bfr-listp-bfr-list-fix
  (bfr-listp (bfr-list-fix x)))

(defthm bfr-list-fix-when-bfr-listp
  (implies (bfr-listp x)
           (equal (bfr-list-fix x) x)))

(defthm bfr-eval-list-bfr-list-fix
  (equal (bfr-eval-list (bfr-list-fix x) env)
         (bfr-eval-list x env))
  :rule-classes nil)

(defthm consp-bfr-list-fix
  (equal (consp (bfr-list-fix x))
         (consp x)))

(defthm car-bfr-list-fix
  (equal (car (bfr-list-fix x))
         (bfr-fix (car x))))

(defthm cdr-bfr-list-fix
  (equal (cdr (bfr-list-fix x))
         (bfr-list-fix (cdr x))))

(defthm len-bfr-list-fix
  (equal (len (bfr-list-fix x)) (len x)))

(in-theory (disable bfr-list-fix bfr-listp))

(defun bfr-list-equiv (x y)
  (equal (bfr-list-fix x) (bfr-list-fix y)))

(defequiv bfr-list-equiv)

(defthm bfr-list-equiv-bfr-list-fix
  (bfr-list-equiv (bfr-list-fix x) x))

(defcong bfr-list-equiv equal (bfr-eval-list x env) 1
  :hints (("goal" :use ((:instance bfr-eval-list-bfr-list-fix)
                        (:instance bfr-eval-list-bfr-list-fix
                         (x x-equiv))))))

(table prove-congruence-theory-table
       'bfr-list-equiv 
       '(bfr-list-fix-when-bfr-listp
         bfr-listp-bfr-list-fix))

(defun bfr-list-fix-vars-bindings (vars)
  (if (atom vars)
      nil
    (let ((x (car vars)))
      (cons `(,x (mbe :logic (bfr-list-fix ,x) :exec ,x))
            (bfr-list-fix-vars-bindings (cdr vars))))))

(defmacro bfr-list-fix-vars (vars body)
  `(let ,(bfr-list-fix-vars-bindings vars)
     (declare (ignorable . ,vars))
     ,body))



(defun bfr-alistp (x)
  (declare (xargs :guard t))
  (or (atom x)
      (and (or (atom (car x))
               (bfr-p (cdar x)))
           (bfr-alistp (cdr x)))))

(defun bfr-eval-alist (al vals)
  (declare (xargs :guard (gl::bfr-alistp al)))
  (if (atom al)
      nil
    (if (consp (car al))
        (cons (cons (caar al)
                    (bfr-eval (cdar al) vals))
              (bfr-eval-alist (cdr al) vals))
      (bfr-eval-alist (cdr al) vals))))





(defn v2i (v)
  (if (atom v)
      0
    (if (atom (cdr v))
        (if (car v) -1 0)
      (let ((rst (ash (v2i (cdr v)) 1)))
        (+ (if (car v) 1 0) rst)))))

(defn i2v (n)
  (if (eql (ifix n) 0)
      '(nil)
    (if (eql n -1)
        '(t)
      (cons (logbitp 0 n)
            (i2v (ash n -1))))))


(defthm v2i-repeat-last
  (equal (v2i (append v (last v)))
         (v2i v))
  :hints(("Goal" :in-theory (enable append))))

(defthm v2i-i2v
  (equal (v2i (i2v i)) (ifix i))
  :hints (("goal" :in-theory (e/d (logbitp) ((:definition i2v)))
           :induct (i2v i)
           :expand ((i2v i)))))

(defn sfix (v)
  (if (atom v)
      (list nil)
    (if (atom (cdr v))
        (list (if (car v) t nil))
      (let ((rst (sfix (cdr v)))
            (car (if (car v) t nil)))
        (if (and (atom (cdr rst)) (eq (car rst) car))
            rst
          (cons car rst))))))

(defthm v2i-sfix
  (equal (v2i (sfix n))
         (v2i n)))

(defthm i2v-singleton
  (implies (and (atom (cdr (i2v x)))
                (integerp x))
           (equal x (if (car (i2v x)) -1 0)))
  :rule-classes nil)

(defthm i2v-v2i
  (equal (i2v (v2i v)) (sfix v))
  :hints (("goal" :in-theory (e/d (logbitp) ((:definition v2i)))
           :induct (v2i v)
           :expand ((v2i v)))
          ("subgoal *1/4"
           :use ((:instance i2v-singleton
                            (x (v2i (cdr v))))))))




(defn v2n (v)
  (if (atom v)
      0
    (let ((rst (ash (v2n (cdr v)) 1)))
      (+ (if (car v) 1 0) rst))))

(defn n2v (n)
  (if (eql (nfix n) 0)
      nil
    (cons (logbitp 0 n)
          (n2v (ash n -1)))))


(defthm v2n-n2v
  (equal (v2n (n2v n)) (nfix n))
  :hints(("Goal" :in-theory (e/d (logbitp) ((:definition n2v)))
          :induct (n2v n)
          :expand ((n2v n)))))


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
  (equal (n2v (v2n v)) (ufix v))
  :hints(("Goal" :in-theory (e/d (v2n-nonneg logbitp)
                                 ((:definition v2n)))
          :induct (v2n v)
          :expand ((v2n v)))))


(in-theory (disable v2n n2v v2i i2v ash logbitp))




(defthm bfr-listp-n2v
  (bfr-listp (n2v n))
  :hints(("Goal" :in-theory (enable n2v logbitp))))

(defthm bfr-listp-i2v
  (bfr-listp (i2v i))
  :hints(("Goal" :in-theory (enable i2v logbitp))))

(defthm us-to-num
  (implies (natp n)
           (equal (v2n (bfr-eval-list (n2v n) env))
                  n))
  :hints(("Goal" :in-theory (enable n2v v2n logbitp ash natp))))

(defthm i2v-to-num
  (implies (integerp n)
           (equal (v2i (bfr-eval-list (i2v n) env)) n))
  :hints(("Goal" :in-theory (enable i2v v2i logbitp
                                    ash natp))))


