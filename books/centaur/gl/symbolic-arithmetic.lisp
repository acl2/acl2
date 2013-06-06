

(in-package "GL")


(include-book "symbolic-arithmetic-fns")
(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
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


(local (in-theory (disable bfr-ite-bss-fn)))


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

(defthm s-nthcdr-correct
  (equal (v2i (bfr-eval-list (s-nthcdr place n) env))
         (ash (v2i (bfr-eval-list n env)) (- (nfix place))))
  :hints(("Goal" :in-theory (e/d (bfr-eval-list v2i s-nthcdr)
                                 ((:definition s-nthcdr)))
          :induct (s-nthcdr place n)
          :expand ((:free (n) (s-nthcdr place n))
                   (:free (place) (s-nthcdr place n))
                   (:free (n) (acl2::logtail place n))))))


(defthm s-sign-correct
  (equal (bfr-eval (s-sign x) env)
         (< (v2i (bfr-eval-list x env)) 0))
  :hints(("Goal" :in-theory (enable v2i bfr-eval-list last s-sign))))

(defthm +-ss-correct
  (equal (v2i (bfr-eval-list (+-ss c v1 v2) env))
         (+ (if (bfr-eval c env) 1 0)
            (v2i (bfr-eval-list v1 env))
            (v2i (bfr-eval-list v2 env))))
  :hints (("Goal"
           :in-theory (enable (:induction +-ss) logcons)
           :induct (+-ss c v1 v2)
           :expand ((+-ss c v1 v2)
                    (:free (a b) (v2i (cons a b)))
                    (:free (a b) (bfr-eval-list (cons a b) env))
                    (bfr-eval-list v1 env)
                    (bfr-eval-list v2 env)))
          (bfr-reasoning)))


(defthm lognot-bv-correct
  (implies (consp x)
           (equal (v2i (bfr-eval-list (lognot-bv x) env))
                  (lognot (v2i (bfr-eval-list x env)))))
  :hints(("Goal" :in-theory (enable bfr-eval-list v2i lognot-bv))))

(defthm unary-minus-s-correct
  (equal (v2i (bfr-eval-list (unary-minus-s x) env))
         (- (v2i (bfr-eval-list x env))))
  :hints(("Goal" :in-theory (enable unary-minus-s lognot))))

(encapsulate nil
  (local (in-theory (disable bfr-ite-bss-fn v2i 
                             (:definition *-ss))))
  (local (bfr-reasoning-mode t))
  (defthm *-ss-correct
    (equal (v2i (bfr-eval-list (*-ss v1 v2) env))
           (* (v2i (bfr-eval-list v1 env))
              (v2i (bfr-eval-list v2 env))))
    :hints(("Goal" :induct (*-ss v1 v2)
            :in-theory (enable *-ss logcons)
            :expand ((*-ss v1 v2)
                     (*-ss nil v2)
                     (:free (a b) (v2i (cons a b))))))))


(encapsulate nil
 (local (in-theory (e/d (<-=-ss)
                        (v2i bfr-eval-list
                             (:definition <-=-ss)))))
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


(defthm <-ss-correct
  (equal (bfr-eval (<-ss a b) env)
         (< (v2i (bfr-eval-list a env))
            (v2i (bfr-eval-list b env))))
  :hints(("Goal" :in-theory (e/d (<-ss) (<-=-ss))
          :expand ((bfr-eval-list a env)
                   (bfr-eval-list b env)
                   (:free (a b) (v2i (cons a b))))
          :do-not-induct t)))

(encapsulate nil
  (local (defthm ash-of-logcons-0
           (implies (<= 0 (ifix m))
                    (equal (ash (logcons 0 n) m)
                           (logcons 0 (ash n m))))
           :hints(("Goal" :in-theory (enable* acl2::ihsext-inductions
                                              acl2::ihsext-recursive-redefs)))))
  
  (local
   (defthm make-list-ac-nil-v2i-eval
     (equal (v2i (bfr-eval-list (make-list-ac n nil m) env))
            (acl2::logapp (nfix n) 0 (v2i (bfr-eval-list m env))))
     :hints(("Goal" :in-theory (enable bfr-eval-list v2i acl2::ash**)))))

  (local (in-theory (disable acl2::logtail-identity
                             bfr-ite-bss-fn
                             equal-of-booleans-rewrite
                             acl2::right-shift-to-logtail)))
  (local (in-theory (enable ash-ss logcons)))

  (local
   (defthm reverse-distrib-1
     (and (equal (+ n n) (* 2 n))
          (implies (syntaxp (quotep k))
                   (equal (+ n (* k n)) (* (+ 1 k) n)))
          (implies (syntaxp (quotep k))
                   (equal (+ (- n) (* k n)) (* (+ -1 k) n)))
          (implies (syntaxp (quotep k))
                   (equal (+ (- n) (* k n) m) (+ (* (+ -1 k) n) m)))
          (implies (syntaxp (and (quotep a) (quotep b)))
                   (equal (+ (* a n) (* b n)) (* (+ a b) n)))
          (equal (+ n n m) (+ (* 2 n) m))
          (implies (syntaxp (quotep k))
                   (equal (+ n (* k n) m) (+ (* (+ 1 k) n) m)))
          (implies (syntaxp (and (quotep a) (quotep b)))
                   (equal (+ (* a n) (* b n) m) (+ (* (+ a b) n) m))))))
  ;; (local (bfr-reasoning-mode t))
  (defthm ash-ss-correct
    (implies (and 
              (posp place))
             (equal (v2i (bfr-eval-list (ash-ss place n shamt) env))
                    (ash (v2i (bfr-eval-list n env))
                         (+ -1 place (* place (v2i (bfr-eval-list shamt env)))))))
    :hints (("goal" :induct (ash-ss place n shamt)
             :in-theory (e/d () ((:definition ash-ss)))
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

(encapsulate nil
  (local (in-theory (enable logbitp-n2v logcons acl2::ash**)))

  (defthm logbitp-n2v-correct
    (implies (and
              (posp place))
             (equal (bfr-eval (logbitp-n2v place digit n) env)
                    (logbitp (* place (v2n (bfr-eval-list digit env)))
                             (v2i (bfr-eval-list n env)))))
    :hints(("Goal" :in-theory (e/d (bfr-eval-list acl2::bool->bit)
                                   ((:definition logbitp-n2v) floor
                                    boolean-listp))
            :induct (logbitp-n2v place digit n)
            :expand ((logbitp-n2v place digit n)
                     (logbitp-n2v place nil n)
                     (logbitp-n2v place digit nil)
                     (:free (n) (logbitp 0 n))
                     (:free (a b) (v2i (cons a b)))
                     (:free (a b) (v2n (cons a b))))))))


(encapsulate nil
  (local (in-theory (enable integer-length-s1 integer-length-s)))
  (local (bfr-reasoning-mode t))
  (local (defthm integer-length-s1-correct1
           (implies (posp offset)
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
                   :in-theory (enable acl2::integer-length**)
                   ;; :in-theory (enable v2i-of-list-implies-car)
                   :expand ((integer-length-s1 offset x)
                            (integer-length-s1 offset nil)
                            (bfr-eval-list x env)
                            (:free (a b) (v2i (cons a b)))
                            (:free (a B) (bfr-eval-list (cons a b) env)))))))


  (defthm integer-length-s-correct
    (equal (v2i (bfr-eval-list (integer-length-s x) env))
           (integer-length (v2i (bfr-eval-list x env))))
    :hints(("Goal" :in-theory (disable integer-length-s1)))))

(defthm logand-ss-correct
  (equal (v2i (bfr-eval-list (logand-ss a b) env))
         (logand (v2i (bfr-eval-list a env))
                 (v2i (bfr-eval-list b env))))
  :hints(("Goal"
          :in-theory (enable acl2::logand** (:i logand-ss))
          :expand ((logand-ss a b)
                   (:free (a b) (v2i (cons a b)))
                   (bfr-eval-list a env)
                   (bfr-eval-list b env)
                   (bfr-eval-list nil env)
                   (:free (a b) (bfr-eval-list (cons a b) env)))
          :induct (logand-ss a b))
         (and stable-under-simplificationp
              '(:in-theory (e/d (bfr-eval-list) (binary-logand))))))

(defthm lognot-s-correct
   (equal (v2i (bfr-eval-list (lognot-s a) env))
          (lognot (v2i (bfr-eval-list a env))))
 :hints (("goal" :in-theory (e/d (v2i bfr-eval-list lognot-s)
                                 (boolean-list-bfr-eval-list
                                  (:definition lognot-s)))
          :induct (lognot-s a)
          :expand ((lognot-s a)))))

(defthm logior-ss-correct
  (equal (v2i (bfr-eval-list (logior-ss a b) env))
         (logior (v2i (bfr-eval-list a env))
                 (v2i (bfr-eval-list b env))))
  :hints(("Goal" :in-theory (e/d ((:i logior-ss)) (logior))
          :induct (logior-ss a b)
          :expand ((logior-ss a b)
                   (:free (a b) (v2i (cons a b)))
                   (bfr-eval-list a env)
                   (bfr-eval-list b env)
                   (bfr-eval-list nil env)))))

;; ------




(defthm s-nthcdr-0
  (equal (s-nthcdr 0 n) n)
  :hints(("Goal" :in-theory (enable s-nthcdr))))



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




(encapsulate nil
  (local
   (defthm rationalp-complex
     (equal (rationalp (complex a b))
            (equal (rfix b) 0))
     :hints (("goal" :use ((:instance
                            (:theorem (implies (rationalp x)
                                               (equal (imagpart x) 0)))
                            (x (complex a b))))))))


  (defthm realpart-of-complex
    (equal (realpart (complex a b))
           (rfix a))
    :hints (("goal" :cases ((rationalp b)))))

  (defthm imagpart-of-complex
    (equal (imagpart (complex a b))
           (rfix b))
    :hints (("goal" :cases ((rationalp a)))))


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
                           (x a) (y (complex b c))))))))



;; ---------------- floor-mod-ss ---------------------

(local (in-theory (enable floor-mod-ss floor-ss mod-ss truncate-ss rem-ss)))





(local
 (defthm car-last-when-nonnegative
   (equal (bfr-eval (car (last b)) env)
          (< (v2i (bfr-eval-list b env)) 0))
   :hints(("Goal" :in-theory (enable v2i)))))



(local (include-book "ihs/quotient-remainder-lemmas" :dir :system))

(local
 (encapsulate nil
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
     :hints(("Goal" :in-theory (e/d (mod)
                                    (floor acl2::floor-bounds
                                        acl2::<-*-/-left))
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
                 '(:in-theory (disable floor)))))))


   ;; (defthm floor-rewrite-+-1-*-2-a
   ;;   (implies (and (integerp a) (integerp b)
   ;;                 (< 0 b))
   ;;            (equal (floor (+ 1 (* 2 a)) b)
   ;;                   (if (<= b (+ 1 (* 2 (mod a b))))
   ;;                       (+ 1 (* 2 (floor a b)))
   ;;                     (* 2 (floor a b)))))
   ;;   :hints(("Goal" :in-theory (disable floor))))

   ;; (defthm floor-rewrite-*-2-a
   ;;   (implies (and (integerp a) (integerp b)
   ;;                 (< 0 b))
   ;;            (equal (floor (* 2 a) b)
   ;;                   (if (<= b (* 2 (mod a b)))
   ;;                       (+ 1 (* 2 (floor a b)))
   ;;                     (* 2 (floor a b)))))
   ;;   :hints(("Goal" :in-theory (disable floor))))

   (defthm floor-rewrite-+-bit-*-2-a
     (implies (and (integerp a) (integerp b)
                   (< 0 b))
              (equal (floor (logcons c a) b)
                     (if (<= b (logcons c (mod a b)))
                         (logcons 1 (floor a b))
                       (logcons 0 (floor a b)))))
     :hints(("Goal" :in-theory (e/d (logcons bfix) (floor)))))

   ;; (defthm mod-rewrite-*-2-a
   ;;   (implies (and (integerp a) (integerp b)
   ;;                 (< 0 b))
   ;;            (equal (mod (* 2 a) b)
   ;;                   (if (<= b (* 2 (mod a b)))
   ;;                       (+ (* -1  b)
   ;;                          (* 2 (mod a b)))
   ;;                     (* 2 (mod a b)))))
   ;;   :hints (("goal" :in-theory (disable mod))))

   ;; (defthm mod-rewrite-+-1-*-2-a
   ;;   (implies (and (integerp a) (integerp b)
   ;;                 (< 0 b))
   ;;            (equal (mod (+ 1 (* 2 a)) b)
   ;;                   (if (<= b (+ 1 (* 2 (mod a b))))
   ;;                       (+ 1 (* -1  b)
   ;;                          (* 2 (mod a b)))
   ;;                     (+ 1 (* 2 (mod a b))))))
   ;;   :hints (("goal" :in-theory (e/d (mod) (floor)))))

   (defthm mod-rewrite-+-bit-*-2-a
     (implies (and (integerp a) (integerp b)
                   (< 0 b))
              (equal (mod (logcons c a) b)
                     (if (<= b (logcons c (mod a b)))
                         (+ (- b)
                            (logcons c (mod a b)))
                       (logcons c (mod a b)))))
     :hints (("goal" :in-theory (e/d (logcons bfix mod) (floor)))))



   ;; (in-theory (disable mod-between-b-and-2-b
   ;;                     mod-less-than-b
   ;;                     floor-between-b-and-2b
   ;;                     floor-less-than-b))

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

(local (defthm bfr-eval-list-non-cons
         (implies (not (consp b))
                  (equal (bfr-eval-list b env) nil))
         :rule-classes ((:rewrite :backchain-limit-lst 0))))

(local (in-theory (disable <-=-ss <-ss)))

(local (defthm +-1-logcons-0
         (equal (+ 1 (logcons 0 a))
                (logcons 1 a))
         :hints(("Goal" :in-theory (enable logcons)))))

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
            :in-theory (e/d* ()
                             (floor mod v2i
                                    bfr-eval-list
                                    equal-of-booleans-rewrite
                                    (:definition floor-mod-ss)
                                    acl2::mod-type
                                    acl2::floor-type-3 acl2::floor-type-1
                                    acl2::logcons-posp-1 acl2::logcons-posp-2
                                    acl2::logcons-negp
                                    acl2::rationalp-mod (:t floor) (:t mod)))
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

(local (in-theory (disable floor mod truncate rem acl2::floor-type-3)))

(local (defthm floor-0
         (equal (floor i 0) 0)
         :hints(("Goal" :in-theory (enable floor)))))

(defthm floor-ss-correct
  (equal (v2i (bfr-eval-list (floor-ss a b) env))
         (floor (v2i (bfr-eval-list a env))
                (v2i (bfr-eval-list b env))))
   :hints (("goal" :do-not-induct t)))

(local (in-theory (disable ACL2::MOD-X-Y-=-X)))


(defthm mod-ss-correct
  (equal (v2i (bfr-eval-list (mod-ss a b) env))
         (mod (v2i (bfr-eval-list a env))
              (v2i (bfr-eval-list b env))))
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

(local (in-theory (disable acl2::truncate-type)))

(defthm truncate-ss-correct
  (equal (v2i (bfr-eval-list (truncate-ss a b) env))
         (truncate (v2i (bfr-eval-list a env))
                   (v2i (bfr-eval-list b env))))
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

(local (in-theory (disable acl2::rem-type acl2::rem-=-0
                           acl2::rem-x-y-=-x)))

(local (bfr-reasoning-mode t))
(local (defthm rem-0
         (implies (acl2-numberp x) (equal (rem x 0) x))
         :hints(("Goal" :in-theory (enable rem)))))
(local (defthm rem-0-x
         (equal (rem 0 x) 0)
         :hints(("Goal" :in-theory (enable rem)))))

(defthm rem-ss-correct
  (equal (v2i (bfr-eval-list (rem-ss a b) env))
         (rem (v2i (bfr-eval-list a env))
              (v2i (bfr-eval-list b env))))
  :hints (("goal" :do-not-induct t
           :in-theory (disable mod rem))))

(local (in-theory (disable truncate-ss rem-ss)))

