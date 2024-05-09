;; Mayank Manjrekar <mankmonjre@gmail.com>

;; June 2023

(in-package "RTL")

(include-book "rtl/rel11/lib/top-alt" :dir :system)
(local (include-book "arithmetic-5/top" :dir :system))

(local
 (in-theory
  #!acl2(disable |(mod (+ x y) z) where (<= 0 z)|
                 |(mod (+ x (- (mod a b))) y)|
                 |(mod (mod x y) z)|
                 |(mod (+ x (mod a b)) y)|
                 mod-cancel-*-const
                 cancel-mod-+
                 reduce-additive-constant-<
                 ash-to-floor
                 |(floor x 2)|
                 |(equal x (if a b c))|
                 |(equal (if a b c) x)|
                 |(logior 1 x)|
                 mod-theorem-one-b
                 |(mod (- x) y)|)))

(defevaluator bits-evl bits-evl-lst
  ((bits x i j)
   (binary-+ x y)
   (if x y z)
   (integerp x)
   (not x)
   (< x y)
   (unary-- x)
   (unary-/ x)
   (binary-* x y)
   (bvecp x k)
   (expt x y)
   (mod x y)
   (floor x y)
   (fl x)))

(set-state-ok t)
(set-irrelevant-formals-ok t)

(defun find-bits-tail-in-sum-fn1 (sum i mfc state)
  (declare (xargs :guard (pseudo-termp sum)))
  ;; Find an addend of the form (bits x k 0) in a summation "sum", such that
  ;; k>=i. If the there is such a addend, the return value is a multiple value
  ;; containing the same same summation with x in place of (bits x k 0), x, k,
  ;; and the sign with which (bits x k 0) appears in the summation (nil for +ve
  ;; and t for -ve).
  (cond ((and (consp sum)
              (eql (car sum) 'binary-+))
         (b* ((laddend (cadr sum))
              (raddend (caddr sum))
              ((mv lterm x k sgn) (find-bits-tail-in-sum-fn1 laddend i mfc state))
              ((when x) (mv (list 'binary-+ lterm raddend) x k sgn))
              ((mv rterm x k sgn) (find-bits-tail-in-sum-fn1 raddend i mfc state))
              ((when x) (mv (list 'binary-+ laddend rterm) x k sgn)))
           (mv sum nil nil nil)))
        ((and (consp sum)
              (eql (car sum) 'unary--))
         (mv-let (sum x k sgn)
           (find-bits-tail-in-sum-fn1 (cadr sum) i mfc state)
           (mv `(unary-- ,sum) x k (not sgn))))
        ((and (consp sum)
              (eql (car sum) 'bits))
         (b* ((x (cadr sum))
              (k (caddr sum))
              (j (cadddr sum)))
           (if (and (quotep j)
                    (eql (unquote j) '0)
                    (equal (mfc-rw `(if (integerp ,k) (if (integerp ,x) (not (< ,k ,i)) 'nil) 'nil) t t mfc state) acl2::*t*))
               (mv x x k nil)
             (mv sum nil nil nil))))
        (t (mv sum nil nil nil))))

(defun bits-bits-sum-meta-fn (term mfc state)
  (declare (xargs :guard (pseudo-termp term)))
  ;; Check if term is of the form (bits *summation* i j), and if so, simplify
  ;; the addends of the form (bits x k 0), k>=i.
  (if (and (consp term)
           (consp (cdr term))
           (eql (car term) 'bits)
           (consp (cddr term))
           (consp (cdddr term))
           (not (cddddr term)))
      (b* ((sum (cadr term))
           (i (caddr term))
           (j (cadddr term))
           ((unless (equal (mfc-rw `(if (integerp ,i)
                                        (if (integerp ,j)
                                            (not (< ,j '0))
                                          'nil)
                                      'nil) t t mfc state) acl2::*t*))
            term)
           ((mv new-sum x k ?sgn) (find-bits-tail-in-sum-fn1 sum i mfc state)))
        (if x
            `(if (if (integerp ,new-sum)
                     (if (integerp ,i)
                         (if (integerp ,j)
                             (if (not (< ,j '0))
                                 (if (integerp ,k)
                                     (if (integerp ,x)
                                         (not (< ,k ,i))
                                       'nil)
                                   'nil)
                               'nil)
                           'nil)
                       'nil)
                   'nil)
                 (bits ,new-sum ,i ,j)
               ,term)
          term))
    term))

(local-defthmd bits-bits-sum-bf-aux-1
  (b* (((mv term x k sgn) (find-bits-tail-in-sum-fn1 sum i mfc state)))
    (implies (acl2-numberp (bits-evl x a))
             (equal (bits-evl term a)
                    (if sgn
                        (+ (bits-evl sum a)
                           (- (bits (bits-evl x a) (bits-evl k a) 0) (bits-evl x a)))
                      (+ (bits-evl sum a)
                           (- (bits-evl x a) (bits (bits-evl x a) (bits-evl k a) 0)))))))
  :hints (("Goal" :in-theory (e/d () ()))))

(local-defthmd mod-minus
  (implies (and (integerp x)
                (rationalp l))
           (equal (mod (- x) l)
                  (if (equal (mod x l) 0)
                      0
                    (- l (mod x l)))))
  :hints (("Goal" :in-theory (e/d () ())
                  :use ((:instance mod-def
                         (x (- x)) (y l))
                        (:instance mod-def
                         (x x) (y l))
                        (:instance minus-fl
                         (x (/ x l)))))))

(local-defthmd bits-bits-sum-lemma-1
  (implies (and (integerp x)
                (integerp y)
                (integerp k)
                (integerp i)
                (integerp j)
                (>= j 0)
                (>= k i))
           (equal (bits (+ y (- x (bits x k 0))) i j)
                  (bits y i j)))
  :hints (("Goal" :in-theory (e/d (bits mod)
                                  ((:DEFINITION NOT)
                                   (:REWRITE ACL2::|(* (if a b c) x)|)
                                   (:REWRITE ACL2::|(+ x (if a b c))|)
                                   (:REWRITE ACL2::|(- (if a b c))|)
                                   (:REWRITE ACL2::|(floor (+ x y) z) where (< 0 z)| . 1)
                                   (:REWRITE ACL2::|(floor (- x) y)| . 1))))))

(local-defthmd bits-bits-sum-lemma-2
  (implies (and (integerp x)
                (integerp y)
                (integerp k)
                (integerp i)
                (integerp j)
                (>= j 0)
                (>= k i))
           (equal (bits (+ y (- (bits x k 0) x)) i j)
                  (bits y i j)))
  :hints (("Goal" :in-theory (e/d (bits mod)
                                  ((:DEFINITION NOT)
                                   (:REWRITE ACL2::|(* (if a b c) x)|)
                                   (:REWRITE ACL2::|(+ x (if a b c))|)
                                   (:REWRITE ACL2::|(- (if a b c))|)
                                   (:REWRITE ACL2::|(floor (+ x y) z) where (< 0 z)| . 1)
                                   (:REWRITE ACL2::|(floor (- x) y)| . 1))))))

(local-defthm not-numberp-bits
  (implies (not (acl2-numberp x))
           (and (equal (bits x i j) 0)
                (equal (bits (- x) i j) 0)))
  :hints (("Goal" :in-theory (e/d (bits) ()))))

(local-defthm acl2-numberp-new-term
  (implies (acl2-numberp (bits-evl (mv-nth 1 (find-bits-tail-in-sum-fn1 sum i mfc state)) a))
           (equal (acl2-numberp (bits-evl (mv-nth 0 (find-bits-tail-in-sum-fn1 sum i mfc state)) a))
                  (acl2-numberp (bits-evl sum a))))
  :hints (("Goal" :in-theory (e/d () ()))))

(local-defthm aux
  (implies (not x)
           (equal (bits-evl x a) nil))
  :hints (("Goal" :in-theory (e/d () ()))))

(local-defthm aux-1
  (implies (acl2-numberp x)
           (equal (integerp (- x))
                  (integerp x)))
  :hints (("Goal" :in-theory (e/d () ())))
  :rule-classes nil)

(local-defthm aux-2
  (implies (acl2-numberp (- x y))
           (equal (integerp (- x y))
                  (integerp (- y x))))
  :hints (("Goal" :use ((:instance aux-1
                         (x (- x y))))))
  :rule-classes nil)

(local-defthmd integerp-new-term
  (implies (integerp (bits-evl (mv-nth 1 (find-bits-tail-in-sum-fn1 sum i mfc state)) a))
           (integerp (- (bits-evl sum a) (bits-evl (mv-nth 0 (find-bits-tail-in-sum-fn1 sum i mfc state)) a))))
  :hints (("Goal" :in-theory (e/d () ()))


          ("Subgoal *1/24" :use (:instance aux-2
                                 (x (BITS-EVL (MV-NTH 0
                                                      (FIND-BITS-TAIL-IN-SUM-FN1 (CADR SUM)
                                                                                 I MFC STATE))
                                              A))
                                 (y (BITS-EVL (CADR SUM) A))))))

(local-defthmd integerp-new-term-alt
  (implies (integerp (bits-evl (mv-nth 1 (find-bits-tail-in-sum-fn1 sum i mfc state)) a))
           (equal (integerp (bits-evl (mv-nth 0 (find-bits-tail-in-sum-fn1 sum i mfc state)) a))
                  (integerp (bits-evl sum a))))
  :hints (("Goal" :in-theory (e/d () (find-bits-tail-in-sum-fn1
                                      acl2-numberp-new-term))
                  :use (integerp-new-term
                        acl2-numberp-new-term))))

(local-defthmd bits-bits-sum-bf-aux
  (b* (((mv new-term x k ?sgn) (find-bits-tail-in-sum-fn1 sum i mfc state)))
    (implies (and x
                  (integerp (bits-evl x a))
                  (integerp (bits-evl new-term a))
                  (integerp (bits-evl i a))
                  (integerp (bits-evl j a))
                  (integerp (bits-evl k a))
                  (<= 0 (bits-evl j a))
                  (<= (bits-evl i a)
                      (bits-evl k a)))
             (equal (bits (bits-evl new-term a)
                          (bits-evl i a)
                          (bits-evl j a))
                    (bits (bits-evl sum a)
                          (bits-evl i a)
                          (bits-evl j a)))))
  :hints (("Goal" :in-theory (e/d (integerp-new-term-alt)
                                  (find-bits-tail-in-sum-fn1
                                   (:REWRITE ACL2::DEFAULT-PLUS-1)
                                   (:REWRITE ACL2::DEFAULT-PLUS-2)
                                   (:REWRITE ACL2::DEFAULT-MINUS)))
                  :use (bits-bits-sum-bf-aux-1
                        (:instance bits-bits-sum-lemma-1
                         (y (bits-evl sum a))
                         (x (bits-evl (mv-nth 1
                                              (find-bits-tail-in-sum-fn1 sum i mfc state)) a))
                         (k (bits-evl (mv-nth 2
                                              (find-bits-tail-in-sum-fn1 sum i mfc state)) a))
                         (i (bits-evl i a))
                         (j (bits-evl j a)))
                        (:instance bits-bits-sum-lemma-2
                         (y (bits-evl sum a))
                         (x (bits-evl (mv-nth 1
                                              (find-bits-tail-in-sum-fn1 sum i mfc state)) a))
                         (k (bits-evl (mv-nth 2
                                              (find-bits-tail-in-sum-fn1 sum i mfc state)) a))
                         (i (bits-evl i a))
                         (j (bits-evl j a)))))))

;; Meta rule to automatically handle simplifications performed by
;; bits-bits-sum, bits-bits-sum-alt, and bits-bits-diff

(defthmd bits-bits-sum-meta
  (implies (and (pseudo-termp x)
                (alistp a))
           (equal (bits-evl x a)
                  (bits-evl (bits-bits-sum-meta-fn x mfc state) a)))
  :hints (("Goal" :in-theory (e/d (bits-bits-sum-bf-aux) ())
                  :do-not-induct t))
  :rule-classes ((:meta :trigger-fns (bits))))

#|
;; For example:
(thm
 (implies (and (integerp x)
               (integerp y)
               (integerp z)
               (integerp n)
               (natp i)
               (>= n i))
          (equal (bits (+ z (- (bits x 3 0) (bits y n 0))) i 0)
                 (bits (+ z (bits x 3 0) (- y)) i 0)))
 :hints (("Goal" :in-theory (e/d (bits-bits-sum-meta) ()))))
|#

;;======================================================================

(defun find-power-of-2-gt-n (prod n mfc state)
  (declare (xargs :guard (and (pseudo-termp prod)
                              (pseudo-termp n))))
  (cond ((and (consp prod)
              (eql (car prod) 'binary-*))
         (b* ((left (cadr prod))
              (right (caddr prod))
              ((mv kl yl) (find-power-of-2-gt-n left n mfc state))
              ((when kl) (mv kl `(binary-* ,yl ,right)))
              ((mv kr yr) (find-power-of-2-gt-n right n mfc state))
              ((when kr) (mv kr `(binary-* ,left ,yr))))
           (mv nil prod)))
        ((and (consp prod)
              (eql (car prod) 'expt)
              (equal (cadr prod) ''2)
              (equal (mfc-rw `(< ,n ,(caddr prod)) t t mfc state) acl2::*t*))
         (mv (caddr prod) ''1))
        ((and (quotep prod)
              (rationalp (unquote prod))
              (equal (mfc-rw `(not (equal (fl (binary-* ,prod (unary-/ (expt '2 (binary-+ '1 ,n))))) '0))
                             t t mfc state) acl2::*t*))
         (mv `(binary-+ '1 ,n) `(fl (binary-* ,prod (unary-/ (expt '2 (binary-+ '1 ,n)))))))
        (t (mv nil prod))))

(defun remove-addend-gt-n (sum n mfc state)
  (declare (xargs :guard (and (pseudo-termp sum)
                              (pseudo-termp n))
                  :guard-debug t))
  (cond ((and (consp sum)
              (equal (car sum) 'binary-+))
         (b* ((left (cadr sum))
              (right (caddr sum))
              ((mv term pow factor sgn) (remove-addend-gt-n left n mfc state))
              ((when pow) (mv `(binary-+ ,term ,right) pow factor sgn))
              ((mv term pow factor sgn) (remove-addend-gt-n right n mfc state))
              ((when pow) (mv `(binary-+ ,left ,term) pow factor sgn)))
           (mv sum nil nil nil)))
        ((and (consp sum)
              (equal (car sum) 'unary--))
         (b* (((mv term pow factor sgn)
               (remove-addend-gt-n (cadr sum) n mfc state)))
           (mv `(unary-- ,term) pow factor (not sgn))))
        (t (b* (((mv pow factor) (find-power-of-2-gt-n sum n mfc state)))
             (if (and pow
                      (mfc-rw `(integerp ,factor) t t mfc state))
                 (mv `(binary-+ ,sum (unary-- (binary-* ,factor (expt '2 ,pow)))) pow factor nil)
               (mv sum nil nil nil))))))

(defun bits-plus-mult-2-fn (term mfc state)
  (declare (xargs :guard (pseudo-termp term)))
  (cond ((and (consp term)
              (eql (car term) 'bits))
         (b* ((n (caddr term))
              (m (cadddr term))
              (sum (cadr term))
              ((mv new-sum k y ?sgn) (remove-addend-gt-n sum n mfc state)))
           (if k
               `(if (if (< ,n ,k)
                        (if (integerp ,y)
                            (integerp ,k)
                          'nil)
                      'nil)
                    (bits ,new-sum ,n ,m)
                  ,term)
             term)))
        (t term)))

(local-defthm not-consp-sum-power
  (implies (not (consp sum))
           (not (mv-nth 0 (find-power-of-2-gt-n sum n mfc state)))))

(local-defthmd no-pow-when-sum-not-acl2-numberp
  (implies (not (acl2-numberp (bits-evl sum a)))
           (not (mv-nth 0 (find-power-of-2-gt-n sum n mfc state)))))

(local-defthmd remove-addend-gt-n-lemma
  (b* (((mv new-sum k factor sgn) (remove-addend-gt-n sum n mfc state)))
    (implies k
             (equal (bits-evl sum a)
                    (+ (bits-evl new-sum a) (* (if sgn -1 1)
                                               (expt 2 (bits-evl k a))
                                               (bits-evl factor a))))))
  :hints (("Goal" :in-theory (e/d (no-pow-when-sum-not-acl2-numberp)
                                  ()))))

(local-defthm bits-idx-not-numberp
  (implies (or (not (acl2-numberp i))
               (not (acl2-numberp j))
               (not (acl2-numberp x)))
           (equal (bits x i j) 0))
  :hints (("Goal" :in-theory (e/d (bits) ()))))

(defthmd bits-plus-mult-2-meta
  (implies (and (pseudo-termp x)
                (alistp a))
           (equal (bits-evl x a)
                  (bits-evl (bits-plus-mult-2-fn x mfc state) a)))
  :hints (("Goal" :do-not-induct t
                  :use ((:instance remove-addend-gt-n-lemma
                         (sum (cadr x))
                         (n (caddr x)))
                        (:instance bits-plus-mult-2
                         (n (bits-evl (caddr x) a))
                         (m (bits-evl (cadddr x) a))
                         (y (* (if (mv-nth 3 (remove-addend-gt-n (cadr x) (caddr x) mfc state)) -1 1)
                               (bits-evl (mv-nth 2 (remove-addend-gt-n (cadr x) (caddr x) mfc state)) a)))
                         (k (bits-evl (mv-nth 1 (remove-addend-gt-n (cadr x) (caddr x) mfc state)) a))
                         (x (bits-evl (mv-nth 0 (remove-addend-gt-n (cadr x) (caddr x) mfc state)) a))))))
  :rule-classes ((:meta :trigger-fns (bits))))

#|
For example:
(thm
 (implies (integerp z)
          (EQUAL (BITS (+ X (* 513/2 z)) 7 1)
                 (BITS (+ X (* 1/2 z)) 7 1)))
 :hints (("Goal" :in-theory (e/d (bits-plus-mult-2-meta) ()))))

(thm
 (implies (and (integerp k)
               (integerp y)
               (< n k))
          (equal (bits (+ x (* (expt 2 k) y) (* (expt 2 l) z)) n m)
                 (bits (+ x (* (expt 2 l) z)) n m)))
 :hints (("Goal" :in-theory (e/d (bits-plus-mult-2-meta) ()))))
|#

;;======================================================================

(defun addend-count (sum)
  (declare (xargs :guard (pseudo-termp sum)))
  (cond ((and (consp sum)
              (equal (car sum) 'binary-+))
         (+ (addend-count (cadr sum)) (addend-count (caddr sum))))
        ((and (consp sum)
              (equal (car sum) 'unary--))
         (addend-count (cadr sum)))
        (t 1)))

(defun find-power-of-2-le-m (sum m gsum mfc state)
  (declare (xargs :guard (and (pseudo-termp sum)
                              (pseudo-termp gsum)
                              (pseudo-termp m))))
  (cond ((and (consp sum)
              (or (eql (car sum) 'binary-+)
                  (eql (car sum) 'binary-*)))
         (b* ((left (cadr sum))
              (right (caddr sum))
              ((mv pow rem) (find-power-of-2-le-m left m gsum mfc state))
              ((when pow) (mv pow rem)))
           (find-power-of-2-le-m right m gsum mfc state)))
        ((and (consp sum)
              (eql (car sum) 'unary--))
         (find-power-of-2-le-m (cadr sum) m gsum mfc state))
        ((and (consp sum)
              (eql (car sum) 'expt)
              (equal (cadr sum) ''2)
              (equal (mfc-rw `(not (< ,m ,(caddr sum))) t t mfc state) acl2::*t*))
         (b* ((term  `(bits ,gsum (binary-+ '-1 ,(caddr sum)) '0))
              (rem (mfc-rw term 'acl2::? nil mfc state))
              ;; subtracting rem and simplifying should result in fewer terms
              (simp (mfc-rw `(binary-+ ,gsum (unary-- ,rem)) 'acl2::? nil mfc state)))
           (if (and (pseudo-termp simp)
                    (<= (addend-count simp)
                        (addend-count gsum)))
             (mv (caddr sum) rem)
             (mv nil nil))))
        ((and (quotep sum)
              (rationalp (unquote sum))
              (equal (mfc-rw `(not (< ,m ,(kwote (expo (unquote sum))))) t t mfc state) acl2::*t*))
         (b* ((term  `(bits ,gsum (binary-+ '-1 ,(kwote (expo (unquote sum)))) '0))
              (rem (mfc-rw term 'acl2::? nil mfc state))
              ;; subtracting rem and simplifying should result in fewer terms
              (simp (mfc-rw `(binary-+ ,gsum (unary-- ,rem)) 'acl2::? nil mfc state)))
           (if (and (pseudo-termp simp)
                    (<= (addend-count simp)
                  (addend-count gsum)))
             (mv (caddr sum) rem)
             (mv nil nil))))
        (t (mv nil nil))))

(defun bits-plus-mult-1-meta-fn (term mfc state)
  (declare (xargs :guard (pseudo-termp term)))
  (cond ((and (consp term)
              (eql (car term) 'bits))
         (b* ((n (caddr term))
              (m (cadddr term))
              (sum (cadr term))
              ((mv pow rem) (find-power-of-2-le-m sum m sum mfc state))
              (y `(binary-* (expt '2 (unary-- ,pow)) (binary-+ ,sum (unary-- ,rem)))))
           (if pow
               `(if (if (bvecp ,rem ,pow)
                        (if (not (< ,m ,pow))
                            (if (integerp ,y)
                                (if (integerp ,m)
                                    (if (integerp ,n)
                                        (integerp ,pow)
                                      'nil)
                                  'nil)
                              'nil)
                          'nil)
                      'nil)
                    (bits ,y
                          (binary-+ ,n (unary-- ,pow))
                          (binary-+ ,m (unary-- ,pow)))
                  ,term)
             term)))
        (t term)))

(defthmd bits-plus-mult-1-meta-aux
  (implies (and (pseudo-termp x)
                (alistp a))
           (equal (bits-evl x a)
                  (bits-evl (bits-plus-mult-1-meta-fn x mfc state) a)))
  :hints (("Goal" :in-theory (e/d ()
                                  ((:REWRITE ACL2::DEFAULT-EXPT-2)
                                   (:REWRITE ACL2::DEFAULT-LESS-THAN-1)
                                   (:REWRITE ACL2::DEFAULT-LESS-THAN-2)
                                   (:REWRITE ACL2::DEFAULT-MINUS)
                                   (:REWRITE ACL2::DEFAULT-PLUS-1)
                                   (:REWRITE ACL2::DEFAULT-TIMES-1)))
                  :use ((:instance bits-plus-mult-1
                         (y (* (EXPT 2 (- (BITS-EVL (MV-NTH 0 (FIND-POWER-OF-2-LE-M (CADR X) (CADDDR X) (CADR X) MFC STATE)) A)))
                               (- (BITS-EVL (CADR X) A)
                                  (BITS-EVL (MV-NTH 1 (FIND-POWER-OF-2-LE-M (CADR X) (CADDDR X) (CADR X) MFC STATE)) A))))
                         (k (BITS-EVL (MV-NTH 0 (FIND-POWER-OF-2-LE-M (CADR X) (CADDDR X) (CADR X) MFC STATE)) A))
                         (n (BITS-EVL (CADDR X) A))
                         (m (bits-evl (CADDDR X) A))
                         (x (BITS-EVL (MV-NTH 1 (FIND-POWER-OF-2-LE-M (CADR X) (CADDDR X) (CADR X) MFC STATE)) A))))
                  :do-not-induct t))
  :rule-classes ((:meta :trigger-fns (bits))))

;; bits-plus-mult-1-meta-aux works when bits-plus-mult-2-meta is enabled. Note:
;; bits-plus-mult-1-meta also simplifies expressions simplified by the the
;; rewrite rule bits-shift-up-1.
(deftheory bits-plus-mult-1-meta
  '(bits-plus-mult-2-meta bits-plus-mult-1-meta-aux))

#|
For example:
(thm
 (IMPLIES (AND (integerp l)
               (<= K M)
               (bvecp (+ x (* (expt 2 l) z)) k)
               (INTEGERP Y)
               (CASE-SPLIT (INTEGERP M))
               (CASE-SPLIT (INTEGERP N))
               (CASE-SPLIT (natp K)))
          (EQUAL (BITS (+ x (* Y (EXPT 2 K)) (* (expt 2 l) z)) N M)
                 (BITS Y (- N K) (- M K))))
 :hints (("Goal" :in-theory (e/d (bits-plus-mult-1-meta) ()))))
|#

;;======================================================================

(mutual-recursion
 (defun bits-shatter-contains-term (cls x n m)
   (declare (xargs :guard (pseudo-termp cls)))
  (if (or (atom cls) (quotep cls))
      nil
    (if (and (eql (car cls) 'bits)
             (quotep (caddr cls))
             (quotep (cadddr cls))
             (equal (cadr cls) x))
        (b* ((h (unquote (caddr cls)))
             (l (unquote (cadddr cls))))
          (if (and (equal h n)
                   (integerp l)
                   (integerp m)
                   (> l m))
              (cons (cons 'p (kwote l)) nil)
            (if (and (equal l m)
                     (integerp n)
                     (integerp h)
                     (> n h))
                (cons (cons 'p (kwote (1+ h))) nil)
              nil)))
      (if (and (eql (car cls) 'bitn)
               (quotep (caddr cls))
               (equal (cadr cls) x))
        (b* ((h (unquote (caddr cls)))
             (l (unquote (caddr cls))))
          (if (and (equal h n)
                   (integerp l)
                   (integerp m)
                   (> l m))
              (cons (cons 'p (kwote l)) nil)
            (if (and (equal l m)
                     (integerp n)
                     (integerp h)
                     (> n h))
                (cons (cons 'p (kwote (1+ h))) nil)
              nil)))
        (bits-shatter-contains-term-lst (cdr cls) x n m)))))

 (defun bits-shatter-contains-term-lst (lst x n m)
   (declare (xargs :guard (pseudo-term-listp lst)))
   (if (atom lst)
       nil
     (or (bits-shatter-contains-term (car lst) x n m)
         (bits-shatter-contains-term-lst (cdr lst) x n m)))))

(defun bits-shatter-walk-clauses (clss x n m)
  (declare (xargs :guard (pseudo-term-listp clss)))
  (if (atom clss)
      nil
    (or (bits-shatter-contains-term (car clss) x n m)
        (bits-shatter-walk-clauses (cdr clss) x n m))))

(defun bits-shatter-fn (x n m mfc state)
  (declare (xargs :guard t)
           (ignore state))
  (if (and (quotep n)
           (quotep m)
           (consp (cdr n))
           (consp (cdr m)))
      (bits-shatter-walk-clauses (mfc-clause mfc) x (unquote n) (unquote m))
    nil))

(defthmd bits-plus-bits-shatter
  (implies (and (bind-free (bits-shatter-fn x n m mfc state) (p))
                (integerp m)
                (integerp n)
                (integerp p)
                (<= m p)
                (<= p n))
           (equal (bits x n m)
                  (+ (bits x (1- p) m)
                     (* (expt 2 (- p m)) (bits x n p)))))
  :hints (("Goal" :use (bits-plus-bits))))

(defthmd bits-bits-shatter
  (implies (and (syntaxp (and (quotep c)
                              (quotep i)
                              (quotep j)))
                (bind-free (bits-shatter-fn x i j mfc state) (p))
                (integerp p)
                (integerp i)
                (integerp j)
                (<= j p)
                (<= p i))
           (equal (equal (bits x i j) c)
                  (and (bvecp c (1+ (- i j)))
                       (equal (bits x i p) (bits c (- i j) (- p j)))
                       (equal (bits x (1- p) j) (bits c (1- (- p j)) 0)))))
  :hints (("Goal" :in-theory (e/d () ())
                  :use ((:instance bits-plus-bits
                         (x x) (n i) (m j) (p p))
                        (:instance bits-plus-bits
                         (x c) (n (- i j)) (m 0) (p (- p j)))
                        (:instance bits-bits
                         (x x) (i i) (j j) (k (1- (- p j))) (l 0))
                        (:instance bits-bits
                         (x x) (i i) (j j) (k (- i j)) (l (- p j)))))))

#| For example:
(thm
 (implies (and (bvecp x 32)
               (equal (bits x 30 0) 0))
          (zerp x (sp)))
 :hints (("Goal" :in-theory (e/d (zerp encodingp expf sp sigf
                                  bits-bits-shatter) ()))))
|#
