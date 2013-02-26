

(in-package "GL")


(include-book "symbolic-arithmetic-fns")

;; (include-book "tools/with-arith5-help" :dir :system)
;; (local (allow-arith5-help))

(local (include-book "arithmetic/top-with-meta" :dir :system))


(defthm equal-complexes-rw
  (implies (and (acl2-numberp x)
                (rationalp a)
                (rationalp b))
           (equal (equal (complex a b) x)
                  (and (equal a (realpart x))
                       (equal b (imagpart x)))))
  :hints (("goal" :use ((:instance realpart-imagpart-elim)))))


(local (include-book "ihs/logops-lemmas" :dir :system))

(local (in-theory (disable acl2::logapp acl2::logcar acl2::logcdr acl2::logtail
                           acl2::logtail-identity
                           acl2::logapp-0
                           bfr-ite-bss-fn)))

(local
 (progn
   (defthm logapp-0-n-m
     (implies (and (integerp m)
                   (integerp n))
              (equal (acl2::logapp 0 m n)
                     n))
     :hints(("Goal" :in-theory (enable acl2::logapp*))))

   (defthm logapp-1-0
     (implies (integerp n)
              (equal (acl2::logapp 1 0 n)
                     (* 2 n)))
     :hints(("Goal" :in-theory (enable acl2::logapp-0))))


   (local (defthm minus-norm-to-*-minus-one
            (equal (- x) (* -1 x))))

   (local (in-theory (disable acl2::functional-commutativity-of-minus-*-left)))

   (defun ash*-ind (n sh)
     (if (zip sh)
         n
       (if (< sh 0)
           (ash*-ind (acl2::logcdr n) (1+ sh))
         (ash*-ind n (1- sh)))))

   (defthm logcar-possibilities
     (or (equal (acl2::logcar n) 0)
         (equal (acl2::logcar n) 1))
     :hints (("goal" :in-theory (e/d (acl2::logcar) (mod))
              :use ((:instance acl2::bitp-mod-2 (i (ifix n))))))
     :rule-classes nil)

   (defthm logcdr-logcar
     (equal (acl2::logcdr (acl2::logcar n)) 0)
     :hints(("Goal"
             :use logcar-possibilities)))

   (defthm acl2::logcdr-logapp
     (implies (and (integerp sz)
                   (integerp n)
                   (integerp m)
                   (< 0 sz))
              (equal (acl2::logcdr (acl2::logapp sz n m))
                     (acl2::logapp (1- sz) (acl2::logcdr n) m)))
     :hints(("Goal" :in-theory (enable acl2::logapp*))))

   (defthm ash-pos-to-logapp
     (implies (and (integerp n)
                   (integerp sh)
                   (<= 0 sh))
              (equal (ash n sh)
                     (acl2::logapp sh 0 n)))
     :hints(("Goal" :in-theory (e/d (acl2::ash* acl2::logapp*)
                                    (ash acl2::logapp
                                         acl2::logcons
                                         acl2::logapp-0
                                         acl2::logcdr))
             :induct (ash*-ind n sh))))

   (defthm ash-neg-to-logtail
     (implies (and (integerp n)
                   (integerp sh)
                   (<= sh 0))
              (equal (ash n sh)
                     (acl2::logtail (- sh) n)))
     :hints (("goal" :in-theory (e/d (acl2::ash* acl2::logtail*)
                                     (ash acl2::logtail
                                          acl2::logcdr))
              :expand ((:with acl2::ash* (ash n sh))
                       (:with acl2::logtail* (acl2::logtail (- sh) n)))
              :induct (ash*-ind n sh))))




   (defthmd n2v-nonzero
     (implies (and (integerp x) (< 0 x))
              (n2v x))
     :hints(("Goal" :in-theory (enable (:induction n2v))
             :expand ((n2v x)))))



   (defthm n2v-when-nonzero
     (implies (and (integerp x)
                   (< 0 x))
              (n2v x))
     :hints(("Goal" :in-theory (enable n2v))))

   (defthm right-shift-nonzero
     (implies (and (integerp x)
                   (< 1 x))
              (< 0 (acl2::logtail 1 x)))
     :hints(("Goal" :in-theory (e/d (acl2::logtail*)))))))

(defthm |equal-n2v-(t)|
  (equal (equal (n2v x) '(t))
         (equal x 1))
  :hints(("Goal" :induct (n2v x)
          :expand ((n2v x))
          :in-theory
          (e/d ((:induction n2v)
                n2v-nonzero)))))




(defthm =-uu-correct
  (equal (bfr-eval (=-uu a b) env)
         (equal (v2n (bfr-eval-list a env))
                (v2n (bfr-eval-list b env))))
  :hints(("Goal" :in-theory (e/d (v2n bfr-eval-list =-uu)))))






(defthm =-ss-correct
  (equal (bfr-eval (=-ss a b) env)
         (equal (v2i (bfr-eval-list a env))
                (v2i (bfr-eval-list b env))))
  :hints(("Goal" :in-theory (enable bfr-eval-list v2i
                                    =-ss))))






(defthm rationalp-complex
  (equal (rationalp (complex a b))
         (equal (rfix b) 0)))


(defthm realpart-rationalp
  (implies (rationalp x)
           (equal (realpart x) x)))

(defthm realpart-complex-completion
  (equal (realpart (complex a b))
         (rfix a))
  :hints (("goal" :cases ((rationalp b)))))

(defthm imagpart-complex-completion
  (equal (imagpart (complex a b))
         (rfix b))
  :hints (("goal" :cases ((rationalp a)))))




(local
 (progn
   (in-theory (enable s-nthcdr))

   (defun logtail*-ind (pos i)
     (cond
      ((zp pos) i)
      (t (logtail*-ind (1- pos) (acl2::logcdr i)))))

   (defthm logtail-minus-one
     (implies (natp n)
              (equal (acl2::logtail n -1) -1))
     :hints(("Goal" :expand ((:with acl2::logtail* (acl2::logtail n -1)))
             :induct (logtail*-ind n -1))))))

(defthm s-nthcdr-correct
  (implies (natp place)
           (equal (v2i (bfr-eval-list (s-nthcdr place n) env))
                  (ash (v2i (bfr-eval-list n env)) (- place))))
  :hints(("Goal" :in-theory (e/d (bfr-eval-list v2i s-nthcdr)
                                 ((:definition s-nthcdr)))
          :induct (s-nthcdr place n)
          :expand ((:free (n) (s-nthcdr place n))
                   (:free (place) (s-nthcdr place n))
                   (:free (n) (acl2::logtail place n))))))



(defthm s-nthcdr-0
  (equal (s-nthcdr 0 n) (bfr-list-fix n)))

(local (in-theory (disable s-nthcdr)))


(defthm s-sign-correct
  (equal (bfr-eval (s-sign x) env)
         (< (v2i (bfr-eval-list x env)) 0))
  :hints(("Goal" :in-theory (enable v2i bfr-eval-list last s-sign))))


(defthm v2n-is-v2i-when-sign-nil
  (implies (not (bfr-eval (s-sign x) env))
           (equal (v2n (bfr-eval-list x env))
                  (v2i (bfr-eval-list x env))))
  :hints(("Goal" :in-theory (enable v2i v2n bfr-eval-list s-sign last))))



;; (defthm bfr-listp-bfr-p-car
;;   (implies (and (consp x)
;;                 (bfr-listp x))
;;            (bfr-p (car x)))
;;   :rule-classes ((:rewrite :backchain-limit-lst 0)))



;; ------------------ +-ss -------------------------------


(local (bfr-reasoning-mode t))
(local (in-theory (disable (force))))

(defthm +-ss-correct
  (equal (v2i (bfr-eval-list (+-ss c v1 v2) env))
         (+ (if (bfr-eval c env) 1 0)
            (v2i (bfr-eval-list v1 env))
            (v2i (bfr-eval-list v2 env))))
  :hints (("Goal"
           :in-theory (enable (:induction +-ss))
           :induct (+-ss c v1 v2)
           :expand ((+-ss c v1 v2)
                    (:free (a b) (v2i (cons a b)))
                    (:free (a b) (bfr-eval-list (cons a b) env))
                    (bfr-eval-list v1 env)
                    (bfr-eval-list v2 env)))))

(local (bfr-reasoning-mode nil))

(defthm boolean-listp-+-ss-v2i-bind-env-car-env
  (implies (and (bind-free '((env . (car env))) (env))
;                 (bfr-p c) (bfr-listp v1) (bfr-listp v2)
                (boolean-listp (+-ss c v1 v2)))
           (equal (v2i (+-ss c v1 v2))
                  (+ (if (bfr-eval c env) 1 0)
                     (v2i (bfr-eval-list v1 env))
                     (v2i (bfr-eval-list v2 env)))))
  :hints (("goal" :use ((:instance bfr-eval-list-consts
                                   (x (+-ss c v1 v2)))
                        +-ss-correct)
           :in-theory (disable +-ss +-ss-correct
                               bfr-eval-list-consts))))

;; ------------------ unary-minus-s ------------------------

(local (in-theory (enable lognot-bv unary-minus-s)))

(defthm v2i-lognot-bv
  (implies (consp x)
           (equal (v2i (bfr-eval-list (lognot-bv x) env))
                  (+ -1 (- (v2i (bfr-eval-list x env))))))
  :hints(("Goal" :in-theory (enable bfr-eval-list v2i))))

(local (in-theory (disable lognot-bv +-ss)))



(defthm v2i-unary-minus-s
  (equal (v2i (bfr-eval-list (unary-minus-s x) env))
         (- (v2i (bfr-eval-list x env)))))

(local (in-theory (disable unary-minus-s)))

;; ------------------ *-ss ------------------------

(local (in-theory (enable *-ss)))

(encapsulate nil
 (local (in-theory (disable bfr-ite-bss-fn v2i 
                            (:definition *-ss))))
 (local (bfr-reasoning-mode t))
 (defthm *-ss-correct
   (equal (v2i (bfr-eval-list (*-ss v1 v2) env))
          (* (v2i (bfr-eval-list v1 env))
             (v2i (bfr-eval-list v2 env))))
   :hints(("Goal" :induct (*-ss v1 v2)
           :expand ((*-ss v1 v2)
                    (*-ss nil v2)
                    (:free (a b) (v2i (cons a b))))))))


(defthm boolean-listp-*-ss-v2i-bind-env-car-env
  (implies (and (bind-free '((env . (car env))) (env))
                (boolean-listp (*-ss v1 v2)))
           (equal (v2i (*-ss v1 v2))
                  (* (v2i (bfr-eval-list v1 env))
                     (v2i (bfr-eval-list v2 env)))))
  :hints (("goal" :use ((:instance bfr-eval-list-consts
                                   (x (*-ss v1 v2)))
                        *-ss-correct)
           :in-theory (disable *-ss *-ss-correct
                               bfr-eval-list-consts))))

(local (in-theory (disable *-ss)))





;; ------------------- <-=-ss ----------------------------

(local (in-theory (enable <-=-ss <-ss)))

(defthm complex-<-1
  (equal (< (complex a b) c)
         (or (< (rfix a) (realpart c))
             (and (equal (rfix a) (realpart c))
                  (< (rfix b) (imagpart c)))))
  :hints (("goal" :use ((:instance completion-of-<
                                   (x (complex a b)) (y c))))))

(defthm complex-<-2
  (equal (< a (complex b c))
         (or (< (realpart a) (rfix b))
             (and (equal (realpart a) (rfix b))
                  (< (imagpart a) (rfix c)))))
  :hints (("goal" :use ((:instance completion-of-<
                                   (x a) (y (complex b c)))))))


(encapsulate nil
 (local (in-theory (disable v2i bfr-eval-list
                            (:definition <-=-ss))))
 (defthm <-=-ss-correct
   (and (equal (bfr-eval (mv-nth 0 (<-=-ss a b)) env)
               (< (v2i (bfr-eval-list a env))
                  (v2i (bfr-eval-list b env))))
        (equal (bfr-eval (mv-nth 1 (<-=-ss a b)) env)
               (equal (v2i (bfr-eval-list a env))
                      (v2i (bfr-eval-list b env)))))
   :hints(("Goal"
           :induct (<-=-ss a b)
           :expand ((<-=-ss a b)
                    (:free (a b) (v2i (cons a b)))
                    (:free (a b) (bfr-eval-list (cons a b) env))
                    (bfr-eval-list a env)
                    (bfr-eval-list b env))))))

(local (in-theory (disable <-=-ss)))



(defthm <-ss-correct
  (equal (bfr-eval (<-ss a b) env)
         (< (v2i (bfr-eval-list a env))
            (v2i (bfr-eval-list b env))))
  :hints(("Goal" :in-theory (e/d ())
          :expand ((bfr-eval-list a env)
                   (bfr-eval-list b env)
                   (:free (a b) (v2i (cons a b))))
          :do-not-induct t)))

(local (in-theory (disable <-ss)))


;; ------------------ ash-ss ------------------------

(local (in-theory (enable ash-ss)))



(local
 (progn
   (defthm make-list-ac-nil-v2i-eval
     (equal (v2i (bfr-eval-list (make-list-ac n nil m) env))
            (acl2::logapp (nfix n) 0 (v2i (bfr-eval-list m env))))
     :hints(("Goal" :in-theory (enable bfr-eval-list v2i acl2::logapp-0))))

   (defthm mk-bfr-list-ac-nil-v2i-eval
     (equal (v2i (bfr-eval-list (mk-bfr-list-ac n nil m) env))
            (acl2::logapp (nfix n) 0 (v2i (bfr-eval-list m env))))
     :hints(("Goal" :in-theory (enable mk-bfr-list-ac))))))


(local
 (defthm reverse-distrib-1
   (and (equal (+ n n) (* 2 n))
        (implies (syntaxp (quotep k))
                 (equal (+ n (* k n)) (* (+ 1 k) n)))
        (implies (syntaxp (and (quotep a) (quotep b)))
                 (equal (+ (* a n) (* b n)) (* (+ a b) n)))
        (equal (+ n n m) (+ (* 2 n) m))
        (implies (syntaxp (quotep k))
                 (equal (+ n (* k n) m) (+ (* (+ 1 k) n) m)))
        (implies (syntaxp (and (quotep a) (quotep b)))
                 (equal (+ (* a n) (* b n) m) (+ (* (+ a b) n) m))))))




(encapsulate nil
  (local (in-theory (disable acl2::logtail-identity
                             bfr-ite-bss-fn
                             equal-of-booleans-rewrite)))
  (local (bfr-reasoning-mode t))
  (defthm ash-ss-correct
    (implies (and 
                  (posp place))
             (equal (v2i (bfr-eval-list (ash-ss place n shamt) env))
                    (ash (v2i (bfr-eval-list n env))
                         (+ -1 place (* place (v2i (bfr-eval-list shamt env)))))))
    :hints (("goal" :induct (ash-ss place n shamt)
             :in-theory (e/d (logapp-1-0) ((:definition ash-ss)))
             :expand ((ash-ss place n shamt)
                      (ash-ss place n nil)
                      (bfr-eval-list shamt env)
                      (:free (a b) (v2i (cons a b)))))
            (and stable-under-simplificationp
                 '(:cases ((<= 0 (+ -1 PLACE
                                    (* 2 PLACE
                                       (V2I (BFR-EVAL-LIST (CDR SHAMT)
                                                           ENV))))))))
            (and stable-under-simplificationp
                 '(:cases ((<= 0 (+ -1 (* 2 PLACE)
                                    (* 2 PLACE
                                       (V2I (BFR-EVAL-LIST (CDR SHAMT) ENV)))))))))))
                 
(local (in-theory (disable ash-ss)))




;; ------------------ logbitp-n2v -------------------------------

(local (in-theory (enable logbitp-n2v)))

(local
 (progn
   (defun logbitp*-ind (pos i)
     (cond ((zp pos) (equal (acl2::logcar i) 1))
           (t (logbitp*-ind (1- pos) (acl2::logcdr i)))))

   (encapsulate nil
     (local (defthm logbitp-0-natp
              (implies (natp n)
                       (equal (logbitp n 0) nil))
              :hints(("Goal" 
                      :expand ((:with acl2::logbitp* (logbitp n 0)))
                      :induct (logbitp*-ind n 0)))
              :rule-classes nil))
     (defthm logbitp-0
       (equal (logbitp n 0) nil)
       :hints (("goal" :use ((:instance logbitp-0-natp (n (nfix n))))
                :in-theory (enable logbitp))))

     (local (defthm logbitp-minus-1-natp
              (implies (natp n)
                       (equal (logbitp n -1) t))
              :hints(("Goal" 
                      :expand ((:with acl2::logbitp* (logbitp n -1)))
                      :induct (logbitp*-ind n -1)))))

     (defthm logbitp-minus-1
       (equal (logbitp n -1) t)
       :hints (("goal" :use ((:instance logbitp-minus-1-natp (n (nfix n))))
                :in-theory (enable logbitp)))))

   (defthm logbitp-to-logcar-logtail
     (implies (and (natp n) (integerp i))
              (equal (logbitp n i)
                     (equal (acl2::logcar (acl2::logtail n i)) 1)))
     :hints (("goal" :induct (logtail*-ind n i)
              :expand ((:with acl2::logbitp* (:free (n) (logbitp n i)))
                       (:with acl2::logtail* (acl2::logtail n i))))))))


(defthm logbitp-n2v-correct
    (implies (and
                  (posp place))
             (equal (bfr-eval (logbitp-n2v place digit n) env)
                    (logbitp (* place (v2n (bfr-eval-list digit env)))
                             (v2i (bfr-eval-list n env)))))
    :hints(("Goal" :in-theory (e/d (bfr-eval-list logapp-1-0)
                                   ((:definition logbitp-n2v) floor
                                    boolean-listp))
            :induct (logbitp-n2v place digit n)
            :expand ((logbitp-n2v place digit n)
                     (logbitp-n2v place nil n)
                     (logbitp-n2v place digit nil)
                     (:free (a b) (v2i (cons a b)))
                     (:free (a b) (v2n (cons a b)))))))

(local (in-theory (disable logbitp-n2v)))




;; ---------------- integer-length-s -----------------

(local (in-theory (enable integer-length-s1 integer-length-s)))

(local
 (progn

   (encapsulate nil
     (local (defthm equal-by-evenp
              (implies (not (equal (evenp x) (evenp y)))
                       (not (equal x y)))))

     (defthmd v2i-of-list-implies-car
       (implies (and (equal (v2i (bfr-eval-list x env)) n)
                     (syntaxp (quotep n)))
                (equal (bfr-eval (car x) env) (logbitp 0 n)))
       :hints (("goal" :expand ((bfr-eval-list x env)
                                (:free (a b) (v2i (cons a b))))))))))

(local (bfr-reasoning-mode t))
(local (defthm integer-length-s1-correct1
         (implies (and 
                       (posp offset))
                  (and (equal (bfr-eval (mv-nth 0 (integer-length-s1 offset x)) env)
                              (not (or (equal (v2i (bfr-eval-list x env)) 0)
                                       (equal (v2i (bfr-eval-list x env)) -1))))
                       (equal (v2i (bfr-eval-list (mv-nth 1 (integer-length-s1 offset
                                                                               x))
                                                  env))
                              (if (or (equal (v2i (bfr-eval-list x env)) 0)
                                      (equal (v2i (bfr-eval-list x env)) -1))
                                  0
                                (+ -1 offset (integer-length (v2i (bfr-eval-list x env))))))))
         :hints(("Goal" :induct (integer-length-s1 offset x)
                 :in-theory (enable v2i-of-list-implies-car)
                 :expand ((integer-length-s1 offset x)
                          (integer-length-s1 offset nil)
                          (bfr-eval-list x env)
                          (:free (a b) (v2i (cons a b)))
                          (:free (a B) (bfr-eval-list (cons a b) env))
                          (:free (x) (:with acl2::integer-length* (integer-length (* 2 x))))
                          (:free (x) (:with acl2::integer-length*
                                            (integer-length (+ 1 (* 2 x))))))))))


(defthm integer-length-s-correct
  (equal (v2i (bfr-eval-list (integer-length-s x) env))
         (integer-length (v2i (bfr-eval-list x env))))
  :hints(("Goal" :in-theory (disable integer-length-s1))))


(local
 (defthm not-integerp-integer-length-s1-1
   (not (integerp (mv-nth 1 (integer-length-s1 offs x))))
   :hints(("Goal" :in-theory (enable integer-length-s1)))))

(local (in-theory (disable integer-length-s1)))


(defthm not-integerp-integer-length-s
  (not (integerp (integer-length-s x)))
  :hints(("Goal" :in-theory (enable integer-length-s))))

(local (in-theory (disable integer-length-s)))







;; ---------------- logand-ss ------------------------

(local (in-theory (enable logand-ss)))

(local (in-theory (disable acl2::logmaskp integer-length)))

(defthm logand-ss-correct
   (equal (v2i (bfr-eval-list (logand-ss a b) env))
          (logand (v2i (bfr-eval-list a env))
                  (v2i (bfr-eval-list b env))))
   :hints(("Goal"
           :in-theory (disable binary-logand)
           :expand ((logand-ss a b)
                    (:free (a b) (v2i (cons a b)))
                    (bfr-eval-list a env)
                    (bfr-eval-list b env)
                    (bfr-eval-list nil env)
                    (:free (a b) (bfr-eval-list (cons a b) env))
                    (:with acl2::logand*
                           (:free (x y) (logand (* 2 x) (* 2 y))))
                    (:with acl2::logand*
                           (:free (x y) (logand (* 2 x) (+ 1 (* 2 y)))))
                    (:with acl2::logand*
                           (:free (x y) (logand (+ 1 (* 2 x)) (* 2 y))))
                    (:with acl2::logand*
                           (:free (x y) (logand (+ 1 (* 2 x)) (+ 1 (* 2 y))))))
           :induct (logand-ss a b))
          (and stable-under-simplificationp
               '(:in-theory (e/d (bfr-eval-list) (binary-logand))))))


(local (in-theory (disable logand-ss)))





;; ---------------- floor-mod-ss ---------------------

(local (in-theory (enable floor-mod-ss floor-ss mod-ss truncate-ss rem-ss)))





(local
 (defthm car-last-when-nonnegative
   (equal (bfr-eval (car (last b)) env)
          (< (v2i (bfr-eval-list b env)) 0))
   :hints(("Goal" :in-theory (enable v2i)))))



(local (include-book "ihs/quotient-remainder-lemmas" :dir :system))

(local
 (progn
   (defthm floor-between-b-and-2b
     (implies (and (integerp a)
                   (integerp b)
                   (< 0 b)
                   (<= b a)
                   (< a (* 2 b)))
              (equal (floor a b) 1))
     :hints(("Goal" :in-theory (disable floor acl2::floor-bounds
                                        acl2::<-*-/-left)
             :use ((:instance acl2::floor-bounds
                              (x a) (y b))
                   (:theorem (implies (and (integerp a)
                                           (integerp b)
                                           (< 0 b)
                                           (< a (* 2 b)))
                                      (< (* a (/ b)) 2)))))
            (and stable-under-simplificationp
                 '(:in-theory (disable floor)))))

   (defthm floor-less-than-b
     (implies (and (integerp a)
                   (integerp b)
                   (< 0 b)
                   (<= 0 a)
                   (< a b))
              (equal (floor a b) 0))
     :hints(("Goal" :in-theory (disable floor acl2::floor-bounds
                                        acl2::<-*-/-left)
             :use ((:instance acl2::floor-bounds
                              (x a) (y b))
                   (:theorem (implies (and (integerp a)
                                           (integerp b)
                                           (< 0 b)
                                           (< a b))
                                      (< (* a (/ b)) 1)))))
            (and stable-under-simplificationp
                 '(:in-theory (disable floor)))))

   (defthm mod-between-b-and-2-b
     (implies (and (integerp a)
                   (integerp b)
                   (< 0 b)
                   (<= b a)
                   (< a (* 2 b)))
              (equal (mod a b) (- a b)))
     :hints(("Goal" :in-theory (disable floor acl2::floor-bounds
                                        acl2::<-*-/-left)
             :use ((:instance acl2::floor-bounds
                              (x a) (y b))
                   (:theorem (implies (and (integerp a)
                                           (integerp b)
                                           (< 0 b)
                                           (< a (* 2 b)))
                                      (< (* a (/ b)) 2)))))
            (and stable-under-simplificationp
                 '(:in-theory (disable floor)))))

   (defthm mod-less-than-b
     (implies (and (integerp a)
                   (integerp b)
                   (< 0 b)
                   (<= 0 a)
                   (< a b))
              (equal (mod a b) a))
     :hints(("Goal" :in-theory (disable floor acl2::floor-bounds
                                        acl2::<-*-/-left)
             :use ((:instance acl2::floor-bounds
                              (x a) (y b))
                   (:theorem (implies (and (integerp a)
                                           (integerp b)
                                           (< 0 b)
                                           (< a (* 2 b)))
                                      (< (* a (/ b)) 2)))))
            (and stable-under-simplificationp
                 '(:in-theory (disable floor)))))

   (defthm mod-rewrite-+-1-*-2-a
     (implies (and (integerp a) (integerp b)
                   (< 0 b))
              (equal (mod (+ 1 (* 2 a)) b)
                     (if (<= b (+ 1 (* 2 (mod a b))))
                         (+ 1 (* -1  b)
                            (* 2 (mod a b)))
                       (+ 1 (* 2 (mod a b))))))
     :hints (("goal" :in-theory (disable mod))))

   (defthm mod-rewrite-*-2-a
     (implies (and (integerp a) (integerp b)
                   (< 0 b))
              (equal (mod (* 2 a) b)
                     (if (<= b (* 2 (mod a b)))
                         (+ (* -1  b)
                            (* 2 (mod a b)))
                       (* 2 (mod a b)))))
     :hints (("goal" :in-theory (disable mod))))

   (defthm floor-rewrite-+-1-*-2-a
     (implies (and (integerp a) (integerp b)
                   (< 0 b))
              (equal (floor (+ 1 (* 2 a)) b)
                     (if (<= b (+ 1 (* 2 (mod a b))))
                         (+ 1 (* 2 (floor a b)))
                       (* 2 (floor a b)))))
     :hints(("Goal" :in-theory (disable floor))))

   (defthm floor-rewrite-*-2-a
     (implies (and (integerp a) (integerp b)
                   (< 0 b))
              (equal (floor (* 2 a) b)
                     (if (<= b (* 2 (mod a b)))
                         (+ 1 (* 2 (floor a b)))
                       (* 2 (floor a b)))))
     :hints(("Goal" :in-theory (disable floor))))

   (in-theory (disable mod-between-b-and-2-b
                       mod-less-than-b
                       floor-between-b-and-2b
                       floor-less-than-b))

   (defthm denominator-of-unary-/
     (implies (and (integerp n) (< 0 n))
              (equal (denominator (/ n)) n))
     :hints (("goal" :use ((:instance rational-implies2
                                      (x (/ n)))))))

   (defthm <-1-not-integer-recip
     (implies (and (integerp n)
                   (< 1 n))
              (not (integerp (/ n))))
     :hints (("goal"
              :use ((:instance denominator-of-unary-/))
              :in-theory (disable denominator-of-unary-/))))

   (defthm integer-and-integer-recip
     (implies (and (integerp n)
                   (< 0 n))
              (equal (integerp (/ n))
                     (equal n 1))))))

(local (bfr-reasoning-mode t))
(local (add-bfr-pat (<-ss . &)))
(local (add-bfr-pat (bfr-fix . &)))

(local
 (defthm floor-mod-ss-correct
   (implies
    (and
         (< 0 (v2i (bfr-eval-list b env))))
    (and (equal (v2i (bfr-eval-list
                      (mv-nth 0 (floor-mod-ss
                                 a b (unary-minus-s b)))
                      env))
                (floor (v2i (bfr-eval-list a env))
                       (v2i (bfr-eval-list b env))))
         (equal (v2i (bfr-eval-list
                      (mv-nth 1 (floor-mod-ss a b (unary-minus-s b)))
                      env))
                (mod (v2i (bfr-eval-list a env))
                     (v2i (bfr-eval-list b env))))))
   :hints (("goal" :induct (floor-mod-ss a b (unary-minus-s b))
            :in-theory (disable floor mod bfr-listp
                                bfr-fix-when-bfr-p
                                equal-of-booleans-rewrite
                                (:definition floor-mod-ss)
                                (:type-prescription acl2::floor-type-3 . 2))
            :do-not-induct t
            :expand ((floor-mod-ss a b (unary-minus-s b))
                     (floor-mod-ss nil b (unary-minus-s b))
                     (:free (a b) (v2i (cons a b)))
                     (:free (a b) (bfr-eval-list (cons a b) env))
                     (bfr-eval-list a env))))))

(local (bfr-reasoning-mode nil))


(local (in-theory (disable floor-mod-ss)))

(local (bfr-reasoning-mode t))
(local (add-bfr-pat (=-ss . &)))
(local (add-bfr-pat (s-sign . &)))

(local (in-theory (disable floor mod truncate rem)))

(local (defthm floor-0
         (equal (floor i 0) 0)
         :hints(("Goal" :in-theory (enable floor)))))

(defthm floor-ss-correct
  (equal (v2i (bfr-eval-list (floor-ss a b) env))
         (floor (v2i (bfr-eval-list a env))
                (v2i (bfr-eval-list b env))))
   :hints (("goal" :do-not-induct t)))



(defthm mod-ss-correct
  (implies (and (bfr-listp a)
                (bfr-listp b))
           (equal (v2i (bfr-eval-list (mod-ss a b) env))
                  (mod (v2i (bfr-eval-list a env))
                       (v2i (bfr-eval-list b env)))))
  :hints (("goal" :do-not-induct t)))

(local (in-theory (disable floor-ss mod-ss)))

(local (bfr-reasoning-mode nil))



(local
 (defthm truncate-is-floor
   (implies (and (integerp a) (integerp b)
                 (not (equal b 0)))
            (equal (truncate a b)
                   (if (acl2::xor (< a 0) (< b 0))
                       (- (floor (abs a) (abs b)))
                     (floor (abs a) (abs b)))))
   :hints(("Goal" :in-theory (disable truncate floor)))))

(local (bfr-reasoning-mode t))

(local (defthm truncate-0
         (equal (truncate x 0) 0)
         :hints(("Goal" :in-theory (enable truncate)))))

(local (Defthm truncate-0-x
         (equal (truncate 0 x) 0)
         :hints(("Goal" :in-theory (enable truncate)))))

(defthm truncate-ss-correct
  (implies (and (bfr-listp a)
                (bfr-listp b))
           (equal (v2i (bfr-eval-list (truncate-ss a b) env))
                  (truncate (v2i (bfr-eval-list a env))
                            (v2i (bfr-eval-list b env)))))
  :hints (("goal" :do-not-induct t
           :in-theory (disable floor truncate bfr-eval-list))))



(local
 (defthm rem-is-mod
   (implies (and (integerp a) (integerp b)
                 (not (equal b 0)))
            (equal (rem a b)
                   (if (< a 0)
                       (- (mod (abs a) (abs b)))
                     (mod (abs a) (abs b)))))
   :hints(("Goal" :in-theory (e/d (rem mod) (floor truncate))))))


(local (bfr-reasoning-mode t))
(local (defthm rem-0
         (implies (acl2-numberp x) (equal (rem x 0) x))
         :hints(("Goal" :in-theory (enable rem)))))
(local (defthm rem-0-x
         (equal (rem 0 x) 0)
         :hints(("Goal" :in-theory (enable rem)))))

(defthm rem-ss-correct
  (implies (and (bfr-listp a)
                (bfr-listp b))
           (equal (v2i (bfr-eval-list (rem-ss a b) env))
                  (rem (v2i (bfr-eval-list a env))
                       (v2i (bfr-eval-list b env)))))
  :hints (("goal" :do-not-induct t
           :in-theory (disable mod rem))))

(local (in-theory (disable truncate-ss rem-ss)))




;; ---------------- lognot-s -------------------------

(local (in-theory (enable lognot-s)))

(defthm lognot-s-correct
   (equal (v2i (bfr-eval-list (lognot-s a) env))
          (lognot (v2i (bfr-eval-list a env))))
 :hints (("goal" :in-theory (e/d (v2i bfr-eval-list lognot)
                                 (boolean-list-bfr-eval-list
                                  (:definition lognot-s)))
          :induct (lognot-s a)
          :expand ((lognot-s a)))))


(local (in-theory (disable lognot-s)))

;; ---------------- logior-ss ------------------------

(local (in-theory (enable logior-ss)))

(local (add-bfr-pat (car (logior-ss . &) . &)))

(local
 (defthm bfr-eval-list-not-consp-cdr
   (implies (and (not (consp (cdr lst)))
                 (consp lst))
            (equal (bfr-eval-list lst env)
                   (list (bfr-eval (car lst) env))))
   :hints(("Goal" :expand ((bfr-eval-list lst env))))
   :rule-classes ((:rewrite :backchain-limit-lst 0))))

(defthm logior-ss-correct
  (equal (v2i (bfr-eval-list (logior-ss a b) env))
         (logior (v2i (bfr-eval-list a env))
                 (v2i (bfr-eval-list b env))))
  :hints(("Goal" :in-theory (e/d () (logior (:definition logior-ss)))
          :induct (logior-ss a b)
          :expand ((logior-ss a b)
                   (:free (a b) (v2i (cons a b)))
                   (bfr-eval-list a env)
                   (bfr-eval-list b env)
                   (bfr-eval-list nil env)
                   (:free (x y) (:with acl2::logior*
                                       (logior (* 2 x) (* 2 y))))
                   (:free (x y) (:with acl2::logior*
                                       (logior (* 2 x) (+ 1 (* 2 y)))))
                   (:free (x y) (:with acl2::logior*
                                       (logior (+ 1 (* 2 x)) (* 2 y))))
                   (:free (x y) (:with acl2::logior*
                                       (logior (+ 1 (* 2 x)) (+ 1 (* 2 y)))))))))


(local (in-theory (disable logior-ss)))

