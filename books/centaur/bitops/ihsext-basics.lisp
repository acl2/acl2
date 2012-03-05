
(in-package "ACL2")

;; BOZO Some of the rules from logops-lemmas that are made redundant by rules
;; here are left still enabled.  Perhaps accumulated-persistence will find the
;; important ones.


(include-book "ihs/logops-definitions" :dir :system)
(include-book "cutil/defsection" :dir :system)

(include-book "tools/rulesets" :dir :system)

(defconst *ihs-extensions-disables*
  '(floor mod expt ash evenp oddp
          logbitp logior logand lognot logxor
          logcons logcar logcdr loghead
          integer-length
          logmaskp logext))

(make-event
 (prog2$ (cw "Note (from ihs-extensions): disabling ~&0.~%~%"
             *ihs-extensions-disables*)
         '(value-triple :invisible))
 :check-expansion t)

(in-theory (set-difference-theories (current-theory :here)
                                    *ihs-extensions-disables*))

(include-book "ihs/logops-lemmas" :dir :system)


(local (include-book "arithmetic/top-with-meta" :dir :system))

 
(def-ruleset! ihsext-basic-thms nil)
(def-ruleset! ihsext-advanced-thms nil)
(def-ruleset! ihsext-bad-type-thms nil)
(def-ruleset! ihsext-redefs nil)
(def-ruleset! ihsext-recursive-redefs nil)
(def-ruleset! ihsext-inductions nil)
(def-ruleset! ihsext-bounds-thms nil)
(def-ruleset! ihsext-arithmetic nil)

(defsection logcons-car-cdr

  (local (in-theory (enable logcar logcons logcdr)))

  (defthm logcons-when-zip
    (implies (zip x)
             (equal (logcons b x)
                    (bfix b))))

  (defthm logcons-when-not-bit
    (implies (not (bitp b))
             (equal (logcons b x)
                    (logcons 0 x))))

  (defthm logcar-when-zip
    (implies (zip i)
             (equal (logcar i) 0)))

  (defthm logcdr-when-zip
    (implies (zip i)
             (equal (logcdr i) 0)))

  (add-to-ruleset ihsext-bad-type-thms
                  '(logcons-when-zip
                    logcons-when-not-bit
                    logcar-when-zip
                    logcdr-when-zip))

  ;; These are a special case since we don't produce definition rules
  ;; for logcar/logcdr/logcons
  (add-to-ruleset ihsext-basic-thms
                  '(logcons-when-zip
                    logcons-when-not-bit
                    logcar-when-zip
                    logcdr-when-zip))

  (local (in-theory (enable* ihsext-bad-type-thms)))
  (local (in-theory (disable logcar logcdr logcons)))

  (defthm logcar-logcons-fix
    (equal (logcar (logcons b x))
           (bfix b))
    :hints(("Goal" :cases ((integerp x)))
           (and stable-under-simplificationp
                '(:cases ((bitp b))))))

  (defthm logcdr-logcons-fix
    (equal (logcdr (logcons b x))
           (ifix x))
    :hints (("goal" :cases ((bitp b)))))

  ;; like the above but with integerp hyps
  (in-theory (disable logcar-logcons
                      logcdr-logcons))

  (defthm logcons-destruct
    (equal (logcons (logcar x) (logcdr x))
           (ifix x)))

  ;; from ihs, like the above but with integerp hyp.  Leaving it enabled as an
  ;; elim rule.
  (in-theory (disable (:rewrite logcar-logcdr-elim)))

  (defthmd equal-logcons-strong
    (equal (equal (logcons a b) i)
           (and (integerp i)
                (equal (logcar i) (bfix a))
                (equal (logcdr i) (ifix b))))
    :hints (("goal" :cases ((bitp a)))
            (and stable-under-simplificationp
                 '(:cases ((integerp b))))))

  ;; like the above but with integerp hyps.  Note: since this was enabled by
  ;; default before, should we instead enable the above?
  (in-theory (disable equal-logcons))

  (local (in-theory (enable equal-logcons-strong)))

  (defthm equal-logcons-weak
    (equal (equal (logcons a b) (logcons c d))
           (and (equal (bfix a) (bfix c))
                (equal (ifix b) (ifix d)))))

  (defthm logcons-equal-constant
    (implies (syntaxp (quotep i))
             (equal (equal (logcons a b) i)
                    (and (integerp i)
                         (equal (logcar i) (bfix a))
                         (equal (logcdr i) (ifix b))))))

  (add-to-ruleset ihsext-basic-thms
                  '(logcar-logcons-fix
                    logcdr-logcons-fix
                    logcons-destruct
                    equal-logcons-weak
                    logcons-equal-constant))

  (add-to-ruleset ihsext-advanced-thms '(equal-logcons-strong))


  (defthmd logcons-<-0-linear
    (implies (and (integerp i) (< i 0))
             (< (logcons b i) 0))
    :rule-classes :linear)

  (defthmd logcons->=-0-linear
    (implies (or (not (integerp i))
                 (<= 0 i))
             (<= 0 (logcons b i)))
    :rule-classes :linear)

  (defthmd logcdr-<-0-linear
    (implies (and (integerp i) (< i 0))
             (< (logcdr i) 0))
    :rule-classes :linear)

  (defthmd logcdr->=-0-linear
    (implies (or (not (integerp i))
                 (<= 0 i))
             (<= 0 (logcdr i)))
    :rule-classes :linear)

  ;; from logops-definitions
  (add-to-ruleset ihsext-bounds-thms '(logcons-<-0
                                       logcdr-<-0
                                       logcons-<-0-linear
                                       logcons->=-0-linear
                                       logcdr-<-0-linear
                                       logcdr->=-0-linear))
  
  (defthmd logcons-<-n-strong
    (implies (integerp j)
             (equal (< (logcons b i) j)
                    (or (< (ifix i) (logcdr j))
                        (and (= (ifix i) (logcdr j))
                             (< (bfix b) (logcar j))))))
    :hints(("Goal" :in-theory (enable logcons))))

  (defthmd logcons->-n-strong
    (implies (integerp j)
             (equal (> (logcons b i) j)
                    (or (> (ifix i) (logcdr j))
                        (and (= (ifix i) (logcdr j))
                             (> (bfix b) (logcar j))))))
    :hints(("Goal" :in-theory (enable logcons))))

  (add-to-ruleset ihsext-advanced-thms '(logcons-<-n-strong
                                          logcons->-n-strong))

  (defthm logcons-<-constant
    (implies (and (syntaxp (quotep j))
                  (integerp j))
             (equal (< (logcons b i) j)
                    (or (< (ifix i) (logcdr j))
                        (and (= (ifix i) (logcdr j))
                             (< (bfix b) (logcar j))))))
    :hints(("Goal" :in-theory (enable logcons-<-n-strong))))

  (defthm logcons->-constant
    (implies (and (syntaxp (quotep j))
                  (integerp j))
             (equal (> (logcons b i) j)
                    (or (> (ifix i) (logcdr j))
                        (and (= (ifix i) (logcdr j))
                             (> (bfix b) (logcar j))))))
    :hints(("Goal" :in-theory (enable logcons->-n-strong))))

  (defthm logcons-<-logcons
    (equal (< (logcons a i) (logcons b j))
           (or (< (ifix i) (ifix j))
               (and (= (ifix i) (ifix j))
                    (< (bfix a) (bfix b)))))
    :hints(("Goal" :in-theory (enable logcons-<-n-strong))))

  (add-to-ruleset ihsext-basic-thms '(logcons-<-constant
                                      logcons->-constant
                                      logcons-<-logcons))

  (defthm logcdr-<=-logcdr
    (implies (<= (ifix a) (ifix b))
             (<= (logcdr a) (logcdr b)))
    :rule-classes (:rewrite :linear))

  (add-to-ruleset ihsext-bounds-thms '(logcdr-<=-logcdr))

  (defthm logcdr-<-const
    (implies (and (syntaxp (quotep c))
                  (integerp c))
             (equal (< (logcdr x) c)
                    (< (ifix x) (logcons 0 c))))
    :hints(("Goal" :in-theory (enable logcons->-n-strong))))

  (defthm logcdr->-const
    (implies (and (syntaxp (quotep c))
                  (integerp c))
             (equal (> (logcdr x) c)
                    (> (ifix x) (logcons 1 c))))
    :hints(("Goal" :in-theory (enable logcons->-n-strong))))

  (add-to-ruleset ihsext-basic-thms '(logcdr-<-const logcdr->-const)))


(defsection logbitp**

  (local (in-theory (enable logbitp)))

  (defthmd logbitp-when-not-natp
    (implies (not (natp i))
             (equal (logbitp i j)
                    (logbitp 0 j))))

  (local (defthmd logbitp-when-not-integer
           (implies (not (integerp j))
                    (equal (logbitp i j)
                           (logbitp i 0)))))

  (defthmd logbitp-when-zip
    (implies (zip j)
             (equal (logbitp i j)
                    nil))
    :hints(("Goal" :in-theory (enable logbitp-when-not-integer
                                      floor zip))))

  (add-to-ruleset ihsext-bad-type-thms
                  '(logbitp-when-not-natp
                    logbitp-when-zip))

  (local (in-theory (enable logbitp-when-zip
                            logbitp-when-not-natp
                            logcar-when-zip
                            logcdr-when-zip)))
  (local (in-theory (disable logbitp)))

  (defthmd logbitp**
    ;; This is a better replacement for logbitp* that doesn't have unnecessary
    ;; type restrictions.
    (equal (logbitp pos i)
           (cond ((zp pos)
                  (equal (logcar i) 1))
                 (t
                  (logbitp (1- pos) (logcdr i)))))
    :hints(("Goal" :use ((:instance logbitp*
                          (pos (nfix pos)) (i (ifix i))))))
    :rule-classes ((:definition :clique (logbitp)
                    :controller-alist ((logbitp t t)))))

  (add-to-ruleset ihsext-redefs '(logbitp**))
  (add-to-ruleset ihsext-recursive-redefs '(logbitp**))

  (theory-invariant (not (active-runep '(:definition logbitp*)))
                    :key |Use LOGBITP** instead of LOGBITP*|)

  (defun logbitp-ind (pos i)
    (if (zp pos)
        (= (logcar i) 1)
      (logbitp-ind (1- pos) (logcdr i))))

  (defthmd logbitp-induct
    t
    :rule-classes ((:induction
                    :pattern (logbitp pos i)
                    :scheme (logbitp-ind pos i))))

  (add-to-ruleset ihsext-inductions '(logbitp-induct))

  (local (in-theory (enable* ihsext-recursive-redefs)))

  (defthm logbitp-of-logcons
    (equal (logbitp pos (logcons b i))
           (if (zp pos)
               (= b 1)
             (logbitp (1- pos) i)))
    :hints (("goal" :expand ((logbitp pos (logcons b i)))))))

(defsection integer-length*

  (defthmd integer-length-when-zip
    (implies (zip i)
             (equal (integer-length i)
                    0)))

  (add-to-ruleset ihsext-bad-type-thms '(integer-length-when-zip))

  ;; Integer-length* is already defined in logops-lemmas:
  ;;(defthm integer-length*
  ;;  (equal (integer-length i)
  ;;         (cond ((zip i) 0)
  ;;               ((equal i -1) 0)
  ;;               (t (1+ (integer-length (logcdr i))))))
  ;;  :rule-classes
  ;;  ((:definition :clique (integer-length)
  ;;    :controller-alist ((integer-length t)))))
  


  (add-to-ruleset ihsext-redefs '(integer-length*))
  (add-to-ruleset ihsext-recursive-redefs '(integer-length*))

  (local (in-theory (enable integer-length*)))

  (defun integer-length-ind (i)
    (declare (Xargs :measure (integer-length i)))
    (cond ((zip i) 0)
          ((= i -1) 0)
          (t (+ 1 (integer-length-ind (logcdr i))))))

  (defthmd integer-length-induct
    t
    :rule-classes ((:induction
                    :pattern (integer-length i)
                    :scheme (integer-length-ind i))))

  (add-to-ruleset ihsext-inductions '(integer-length-induct)))

(defsection logand**

  (local (in-theory (enable logand)))

  (defthmd logand-when-zip
    (implies (or (zip i) (zip j))
             (equal (logand i j) 0)))

  (add-to-ruleset ihsext-bad-type-thms '(logand-when-zip))

  (local (in-theory (enable* ihsext-bad-type-thms)))
  (local (in-theory (disable logand)))

  (defthmd logand**
    ;; Better than logand* since there are no hyps.
    (equal (logand i j)
           (logcons (b-and (logcar i) (logcar j))
                    (logand (logcdr i) (logcdr j))))
    :hints(("Goal" :use ((:instance logand*
                          (i (ifix i)) (j (ifix j))))))
    :rule-classes
    ((:definition :clique (binary-logand)
      :controller-alist ((binary-logand t t)))))

  (add-to-ruleset ihsext-redefs '(logand**))

  (defthmd logand$
    (equal (logand i j)
           (cond ((or (zip i) (zip j)) 0)
                 ((= i -1) j)
                 ((= j -1) i)
                 (t (logcons (b-and (logcar i) (logcar j))
                             (logand (logcdr i) (logcdr j))))))
    :hints (("goal" :in-theory (disable logcons logcar logcdr
                                        logand* logand)
             :use ((:instance logand*
                    (i (ifix i)) (j (ifix j))))))
    :rule-classes ((:definition
                    :clique (binary-logand)
                    :controller-alist ((binary-logand t t)))))

  (add-to-ruleset ihsext-recursive-redefs '(logand$))

  (theory-invariant (not (active-runep '(:definition logand*)))
                    :key |Use LOGAND** or LOGAND$ instead of LOGAND*|)

  (local (in-theory (enable integer-length*)))

  (defun logand-ind (i j)
    (declare (xargs :measure (integer-length i)))
    (cond ((or (zip i) (zip j)) 0)
          ((= i -1) j)
          ((= j -1) i)
          (t (logcons (b-and (logcar i) (logcar j))
                      (logand-ind (logcdr i) (logcdr j))))))

  (defthmd logand-induct
    t
    :rule-classes ((:induction
                    :pattern (logand i j)
                    :scheme (logand-ind i j))))

  (add-to-ruleset ihsext-inductions '(logand-induct))

  (local (in-theory (enable* ihsext-recursive-redefs
                             ihsext-inductions)))

  (defthm logcar-of-logand
    (equal (logcar (logand x y))
           (b-and (logcar x) (logcar y)))
    :hints (("Goal" :expand (logand x y))))


  (defthm logcdr-of-logand
    (equal (logcdr (logand x y))
           (logand (logcdr x) (logcdr y))))

  (defthm logbitp-of-logand
    (equal (logbitp a (logand x y))
           (and (logbitp a x)
                (logbitp a y))))

  (add-to-ruleset ihsext-basic-thms '(logcar-of-logand
                                      logcdr-of-logand
                                      logbitp-of-logand))

  (defthmd logand-commutes
    (equal (logand a b)
           (logand b a)))

  (add-to-ruleset ihsext-advanced-thms '(logand-commutes))

  (defthm logand-<-0
    (equal (< (logand x y) 0)
           (and (< (ifix x) 0)
                (< (ifix y) 0))))

  (add-to-ruleset ihsext-bounds-thms '(logand-<-0)))



(defsection lognot**

  (defthmd lognot-when-zip
    (implies (zip x)
             (equal (lognot x) -1)))

  (add-to-ruleset ihsext-bad-type-thms '(lognot-when-zip))

  (local (in-theory (enable* ihsext-bad-type-thms)))

  (defthmd lognot**
    ;; Better than lognot* since there are no hyps.
    (equal (lognot i)
           (logcons (b-not (logcar i))
                    (lognot (logcdr i))))
    :hints(("Goal"
            :use ((:instance lognot*
                   (i (ifix i))))))
    :rule-classes ((:definition :clique (lognot)
                    :controller-alist ((lognot t)))))

  (add-to-ruleset ihsext-redefs '(lognot**))

  (defthmd lognot$
    (equal (lognot i)
           (cond ((zip i) -1)
                 ((= i -1) 0)
                 (t (logcons (b-not (logcar i))
                             (lognot (logcdr i))))))
    :hints (("goal" :use ((:instance lognot*
                           (i (ifix i))))
             :in-theory (disable lognot lognot*)))
    :rule-classes ((:definition
                    :clique (lognot)
                    :controller-alist ((lognot t)))))

  (add-to-ruleset ihsext-recursive-redefs '(lognot$))

  (theory-invariant (not (active-runep '(:definition lognot*)))
                    :key |Use LOGNOT** or LOGNOT$instead of LOGNOT*|)

  (defthmd lognot-induct
    t
    :rule-classes ((:induction
                    :pattern (lognot i)
                    :scheme (integer-length-ind i))))

  (add-to-ruleset ihsext-inductions '(lognot-induct))


  (local (in-theory (enable* ihsext-recursive-redefs
                             ihsext-inductions)))

  (defthm logcar-of-lognot
    (equal (logcar (lognot x))
           (b-not (logcar x))))

  (defthm logcdr-of-lognot
    (equal (logcdr (lognot x))
           (lognot (logcdr x))))

  (defthm logbitp-of-lognot
    (equal (logbitp a (lognot x))
           (not (logbitp a x))))

  (add-to-ruleset ihsext-basic-thms '(logcar-of-lognot
                                      logcdr-of-lognot
                                      logbitp-of-lognot))

  (defthm lognot-<-0
    (equal (< (lognot x) 0)
           (not (< (ifix x) 0))))

  (add-to-ruleset ihsext-bounds-thms '(lognot-<-0))

  (defthm lognot-<-const
    (implies (and (syntaxp (quotep j))
                  (integerp j))
             (equal (< (lognot i) j)
                    (> (ifix i) (lognot j))))
    :hints(("Goal" :in-theory (enable lognot)
            :use ((:instance <-on-others
                   (x (lognot i)) (y j))
                  (:instance <-on-others
                   (x (lognot k)) (y (ifix i)))))))

  (defthm lognot->-const
    (implies (and (syntaxp (quotep j))
                  (integerp j))
             (equal (> (lognot i) j)
                    (< (ifix i) (lognot j))))
    :hints(("Goal" :in-theory (enable lognot)
            :use ((:instance <-on-others
                   (y (lognot i)) (x j))
                  (:instance <-on-others
                   (y (lognot j)) (x (ifix i)))))))

  (defthm lognot-equal-const
    (implies (and (syntaxp (quotep j))
                  (integerp j))
             (equal (equal (lognot i) j)
                    (equal (ifix i) (lognot j))))
    :hints(("Goal" :in-theory (enable lognot))))

  (add-to-ruleset ihsext-basic-thms '(lognot-<-const
                                      lognot->-const
                                      lognot-equal-const)))


(defsection logior**

  (local (in-theory (enable* logior
                             ihsext-recursive-redefs
                             ihsext-inductions
                             ihsext-advanced-thms)))

  (defthmd logior**
    ;; Better than logand* since there are no hyps.
    (equal (logior i j)
           (logcons (b-ior (logcar i) (logcar j))
                    (logior (logcdr i) (logcdr j))))
    :rule-classes
    ((:definition :clique (binary-logior)
      :controller-alist ((binary-logior t t)))))

  (add-to-ruleset ihsext-redefs '(logior**))

  (defthmd logior$
    (equal (logior i j)
           (cond ((zip i) (ifix j))
                 ((zip j) i)
                 ((or (= j -1) (= i -1)) -1)
                 (t (logcons (b-ior (logcar i) (logcar j))
                             (logior (logcdr i) (logcdr j))))))
    :rule-classes
    ((:definition :clique (binary-logior)
      :controller-alist ((binary-logior t t)))))

  (add-to-ruleset ihsext-recursive-redefs '(logior$))

  (theory-invariant (not (active-runep '(:definition logior*)))
                    :key |Use LOGIOR** or LOGIOR$ instead of LOGIOR*|)

  ;; LOGAND-IND is the same induction scheme.
  (defthmd logior-induct
    t
    :rule-classes ((:induction
                    :pattern (logior i j)
                    :scheme (logand-ind i j))))

  (add-to-ruleset ihsext-inductions '(logior-induct))

  (local (in-theory (enable* ihsext-bad-type-thms
                             logior-induct
                             logior$)))
  (local (in-theory (disable logior)))

  (defthm logcar-of-logior
    (equal (logcar (logior x y))
           (b-ior (logcar x) (logcar y)))
    :hints (("goal" :expand (logior x y))))


  (defthm logcdr-of-logior
    (equal (logcdr (logior x y))
           (logior (logcdr x) (logcdr y))))

  (defthm logbitp-of-logior
    (equal (logbitp a (logior x y))
           (or (logbitp a x)
               (logbitp a y))))

  (add-to-ruleset ihsext-basic-thms '(logcar-of-logior
                                      logcdr-of-logior
                                      logbitp-of-logior))

  (defthmd logior-commutes
    (equal (logior a b)
           (logior b a)))

  (add-to-ruleset ihsext-advanced-thms '(logior-commutes))

  (defthm logior-<-0
    (equal (< (logior x y) 0)
           (or (< (ifix x) 0)
               (< (ifix y) 0))))

  (add-to-ruleset ihsext-bounds-thms '(logior-<-0))

  (local (in-theory (disable logior-=-0)))

  (defthm logior-equal-0
    (equal (equal (logior i j) 0)
           (and (equal (ifix i) 0)
                (equal (ifix j) 0))))

  (add-to-ruleset ihsext-basic-thms '(logior-equal-0)))


(defsection logxor**

  (local (in-theory (enable* logxor logeqv logorc1
                             ihsext-inductions
                             ihsext-advanced-thms)))

  (defthmd logxor**
    ;; Better than logxor* since there are no hyps.
    (equal (logxor i j)
           (logcons (b-xor (logcar i) (logcar j))
                    (logxor (logcdr i) (logcdr j))))
    :rule-classes
    ((:definition :clique (binary-logxor)
      :controller-alist ((binary-logxor t t)))))

  (add-to-ruleset ihsext-redefs '(logxor**))

  (local (in-theory (enable* ihsext-recursive-redefs)))
  (local (in-theory (disable bfix zbp)))

  (defthmd logxor$
    ;; Better than logxor* since there are no hyps.
    (equal (logxor i j)
           (cond ((zip i) (ifix j))
                 ((zip j) (ifix i))
                 ((= i -1) (lognot j))
                 ((= j -1) (lognot i))
                 (t (logcons (b-xor (logcar i) (logcar j))
                             (logxor (logcdr i) (logcdr j))))))
    :rule-classes
    ((:definition :clique (binary-logxor)
      :controller-alist ((binary-logxor t t)))))

  (add-to-ruleset ihsext-recursive-redefs '(logxor$))

  (theory-invariant (not (active-runep '(:definition logxor*)))
                    :key |Use LOGXOR** or LOGXOR$ instead of LOGXOR*|)

  (defthm logxor-induct
    t
    :rule-classes ((:induction
                    :pattern (logxor i j)
                    :scheme (logand-ind i j))))

  (add-to-ruleset ihsext-inductions '(logxor-induct))

  (local (in-theory (enable* ihsext-bad-type-thms
                             logxor-induct
                             logxor$)))
  (local (in-theory (disable logxor)))

  (defthm logcar-of-logxor
    (equal (logcar (logxor x y))
           (b-xor (logcar x) (logcar y)))
    :hints (("goal" :expand (logxor x y))))


  (defthm logcdr-of-logxor
    (equal (logcdr (logxor x y))
           (logxor (logcdr x) (logcdr y))))

  (defthm logbitp-of-logxor
    (equal (logbitp a (logxor x y))
           (xor (logbitp a x)
                (logbitp a y))))

  (add-to-ruleset ihsext-basic-thms '(logcar-of-logxor
                                      logcdr-of-logxor
                                      logbitp-of-logxor))

  (defthmd logxor-commutes
    (equal (logxor a b)
           (logxor b a)))

  (add-to-ruleset ihsext-advanced-thms '(logxor-commutes))


  (defthm logxor-<-0
    (equal (< (logxor x y) 0)
           (xor (< (ifix x) 0)
               (< (ifix y) 0))))

  (add-to-ruleset ihsext-bounds-thms '(logxor-<-0))

  (defthm logxor-equal-0
    (equal (equal (logxor x y) 0)
           (equal (ifix x) (ifix y))))

  (add-to-ruleset ihsext-basic-thms '(logxor-equal-0)))



(defsection ash*
  ;; Ash* is already defined in logops-lemmas.
  ;;(defthmd ash*
  ;;  (equal (ash i count)
  ;;         (cond ((zip count) (ifix i))
  ;;               ((< count 0)
  ;;                (ash (logcdr i) (1+ count)))
  ;;               (t (logcons 0 (ash i (1- count))))))
  ;;  :rule-classes ((:definition :clique (ash)
  ;;                  :controller-alist ((ash nil t)))))

  (add-to-ruleset ihsext-recursive-redefs '(ash*))
  (add-to-ruleset ihsext-redefs '(ash*))

  (defun ash-ind (i count)
    (declare (xargs :measure (abs (ifix count))))
    (cond ((zip count) (ifix i))
          ((< count 0)
           (ash-ind (logcdr i) (1+ count)))
          (t (logcons 0 (ash-ind i (1- count))))))

  (defthmd ash-induct
    t
    :rule-classes ((:induction
                    :pattern (ash i count)
                    :scheme (ash-ind i count))))

  (add-to-ruleset ihsext-inductions '(ash-induct))

  (in-theory (disable ash))
  
  (local (in-theory (enable* ihsext-inductions
                             ihsext-recursive-redefs)))

  (defthmd ash-when-zip-i
    (implies (zip i)
             (equal (ash i count) 0)))

  (add-to-ruleset ihsext-basic-thms '(ash-when-zip-i))

  (defthmd ash-when-zip-count
    (implies (zip count)
             (equal (ash i count)
                    (ifix i))))

  (add-to-ruleset ihsext-bad-type-thms '(ash-when-zip-count))

  (defthmd logcar-of-ash
    (equal (logcar (ash i count))
           (if (<= (ifix count) 0)
               (if (logbitp (- count) i) 1 0)
             0))
    :hints (("goal" :induct t
             :do-not-induct t
             :expand ((logbitp (- count) i)))))
  
  (add-to-ruleset ihsext-advanced-thms '(logcar-of-ash))

  (local (in-theory (enable logcar-of-ash)))

  (defthm logcdr-of-ash
    (equal (logcdr (ash i count))
           (ash i (1- (ifix count)))))

  (defun logbitp-of-ash-ind (pos i count)
    (declare (xargs :measure (abs (ifix count))))
    (cond ((or (zp pos)
               (zip count)) (list pos i))
          ((< count 0)
           (logbitp-of-ash-ind pos (logcdr i) (1+ count)))
          (t (logbitp-of-ash-ind (1- pos) i (1- count)))))
 

  (defthm logbitp-of-ash
    (equal (logbitp pos (ash i count))
           (and (<= (ifix count) (nfix pos))
                (logbitp (- (nfix pos) (ifix count)) i)))
    :hints (("goal" :induct (logbitp-of-ash-ind
                             pos i count)
             :do-not-induct t)))

  (add-to-ruleset ihsext-basic-thms '(logcdr-of-ash
                                      logbitp-of-ash))


  (defthm ash-<-0
    (equal (< (ash i count) 0)
           (< (ifix i) 0)))

  (defthmd ash-<-0-linear
    (implies (and (integerp i)
                  (< i 0))
             (< (ash i count) 0))
    :rule-classes :linear)

  (defthmd ash->=-0-linear
    (implies (or (not (integerp i))
                 (<= 0 i))
             (<= 0 (ash i count)))
    :rule-classes :linear)

  (add-to-ruleset ihsext-bounds-thms '(ash-<-0
                                       ash-<-0-linear
                                       ash->=-0-linear))


  (encapsulate nil
    (local
     (progn
       (defthm ash-of-ash-1
         (implies (and (<= 0 (ifix sh1))
                       (<= 0 (ifix sh2)))
                  (equal (ash (ash x sh1) sh2)
                         (ash x (+ (ifix sh1) (ifix sh2)))))
         :hints (("goal" :induct (acl2::ash-ind x sh1))))

       (defthm ash-of-ash-2
         (implies (and (<= (ifix sh1) 0)
                       (<= (ifix sh2) 0))
                  (equal (ash (ash x sh1) sh2)
                         (ash x (+ (ifix sh1) (ifix sh2)))))
         :hints (("goal" :induct (acl2::ash-ind x sh1))))

       (defthm ash-of-ash-3
         (implies (<= 0 (ifix sh1))
                  (equal (ash (ash x sh1) (+ (- (ifix sh1)) (ifix sh)))
                         (ash x sh)))
         :hints (("goal" :induct (acl2::ash-ind x sh1))))))

    (defthm ash-of-ash
      (implies (or (<= 0 (ifix sh1))
                   (<= (ifix sh2) 0))
               (equal (ash (ash x sh1) sh2)
                      (ash x (+ (ifix sh1) (ifix sh2)))))
      :hints ('(:cases ((<= 0 (ifix sh1))))
              '(:cases ((<= (ifix sh2) 0)))
              (and stable-under-simplificationp
                   '(:use ((:instance ash-of-ash-3
                            (sh (+ sh1 sh2)))))))))

  (add-to-ruleset ihsext-basic-thms ash-of-ash))

(defsection expt

  (defthmd expt-2-is-ash
    (implies (natp n)
             (equal (expt 2 n)
                    (ash 1 n)))
    :hints(("Goal" :in-theory (enable ash floor))))

  (add-to-ruleset ihsext-arithmetic '(expt-2-is-ash)))



(defsection unsigned-byte-p**


  (local (in-theory (enable* ihsext-recursive-redefs
                             ihsext-inductions)))

  (local (in-theory (enable expt-2-is-ash)))

  (defthmd unsigned-byte-p**
    (equal (unsigned-byte-p bits x)
           (and (integerp x)
                (natp bits)
                (cond ((= x 0) t)
                      ((or (= bits 0) (= x -1)) nil)
                      (t (unsigned-byte-p (1- bits) (logcdr x))))))
    :rule-classes ((:definition
                    :clique (unsigned-byte-p)
                    :controller-alist ((unsigned-byte-p t t)))))

  (local (in-theory (enable unsigned-byte-p**)))
  (local (in-theory (disable unsigned-byte-p)))

  (add-to-ruleset ihsext-recursive-redefs '(unsigned-byte-p**))

  (defun unsigned-byte-p-ind (bits x)
    (and (integerp x)
         (natp bits)
         (cond ((= x 0) t)
               ((or (= bits 0) (= x -1)) nil)
               (t (unsigned-byte-p-ind (1- bits) (logcdr x))))))

  (defthm unsigned-byte-p-induct
    t
    :rule-classes ((:induction
                    :pattern (unsigned-byte-p bits x)
                    :scheme (unsigned-byte-p-ind bits x))))
    
  (defthmd unsigned-byte-p-incr
    (implies (and (unsigned-byte-p a x)
                  (natp b)
                  (<= a b))
             (unsigned-byte-p b x)))

  (local (in-theory (enable unsigned-byte-p-incr)))

  (defthmd unsigned-byte-p-logcons
    (implies (and (unsigned-byte-p (1- b) x)
                  (natp b))
             (unsigned-byte-p b (logcons bit x)))
    :hints (("goal" :expand ((unsigned-byte-p b (logcons bit x))))))

  (defthmd unsigned-byte-p-logcons-free
    (implies (and (unsigned-byte-p a x)
                  (natp b)
                  (<= a (1- b)))
             (unsigned-byte-p b (logcons bit x)))
    :hints (("goal" :expand ((unsigned-byte-p b (logcons bit x))))))

  (defthmd unsigned-byte-p-logcdr
    (implies (and (unsigned-byte-p a x)
                  (natp b)
                  (<= a (1+ b)))
             (unsigned-byte-p b (logcdr x))))

  (add-to-ruleset ihsext-bounds-thms '(unsigned-byte-p-incr
                                       unsigned-byte-p-logcons
                                       unsigned-byte-p-logcons-free
                                       unsigned-byte-p-logcdr))

  (local (in-theory (disable unsigned-byte-p-logand
                             unsigned-byte-p-logior
                             logior-=-0)))

  (defthmd unsigned-byte-p-logand-fix
    (implies (or (unsigned-byte-p b x)
                 (unsigned-byte-p b y))
             (unsigned-byte-p b (logand x y))))

  (defun unsigned-byte-p-logior-ind (b x y)
    (cond ((zp b) (list x y))
          (t (unsigned-byte-p-logior-ind
              (1- b) (logcdr x) (logcdr y)))))

  (defthmd unsigned-byte-p-logior-fix
    (equal (unsigned-byte-p b (logior x y))
           (and (unsigned-byte-p b (ifix x))
                (unsigned-byte-p b (ifix y))))
    :hints (("goal" :induct (unsigned-byte-p-logior-ind b x y))))

  (add-to-ruleset ihsext-basic-thms '(unsigned-byte-p-logand-fix
                                      unsigned-byte-p-logior-fix)))


(defsection signed-byte-p**

  (local (in-theory (enable* ihsext-recursive-redefs
                             ihsext-inductions
                             ihsext-bounds-thms
                             ihsext-advanced-thms
                             ihsext-arithmetic
                             )))

  (defthmd minus-to-lognot
    (implies (integerp x)
             (equal (- x)
                    (+ 1 (lognot x))))
    :hints(("Goal" :in-theory (enable lognot)))
    :rule-classes ((:rewrite :backchain-limit-lst (0))))

  (defthmd elim-plus-one
    (implies (and (integerp x)
                  (integerp y))
             (equal (< x (+ 1 y))
                    (<= x y)))
    :rule-classes ((:rewrite :backchain-limit-lst (0 0))))

  (add-to-ruleset ihsext-advanced-thms '(minus-to-lognot
                                          elim-plus-one))

  (local (in-theory (enable minus-to-lognot elim-plus-one)))

  (local (defthm ash-zero-fwd
           (implies (and (equal (ash x bits) 0)
                         (not (zip x)))
                    (< bits 0))
           :rule-classes :forward-chaining))


  (defthmd signed-byte-p**
    (equal (signed-byte-p bits x)
           (and (integerp x)
                (natp bits)
                (cond ((= bits 0) nil)
                      ((or (= x 0) (= x -1)) t)
                      (t (signed-byte-p (1- bits) (logcdr x))))))
    :rule-classes ((:definition
                    :clique (signed-byte-p)
                    :controller-alist ((signed-byte-p t t)))))

  (local (in-theory (enable signed-byte-p**)))
  (local (in-theory (disable signed-byte-p)))

  (add-to-ruleset ihsext-recursive-redefs '(signed-byte-p**))

  (defun signed-byte-p-ind (bits x)
    (and (integerp x)
         (natp bits)
         (cond ((= bits 0) nil)
               ((or (= x 0) (= x -1)) t)
               (t (signed-byte-p-ind (1- bits) (logcdr x))))))

  (defthm signed-byte-p-induct
    t
    :rule-classes ((:induction
                    :pattern (signed-byte-p bits x)
                    :scheme (signed-byte-p-ind bits x))))
    
  (defthmd signed-byte-p-incr
    (implies (and (signed-byte-p a x)
                  (natp b)
                  (<= a b))
             (signed-byte-p b x)))

  (local (in-theory (enable signed-byte-p-incr)))

  (defthmd signed-byte-p-logcons
    (implies (and (signed-byte-p a x)
                  (natp b)
                  (<= a (1- b)))
             (signed-byte-p b (logcons bit x)))
    :hints (("goal" :expand ((signed-byte-p b (logcons bit x))))))

  (defthmd signed-byte-p-logcdr
    (implies (and (signed-byte-p a x)
                  (posp b)
                  (<= a (1+ b)))
             (signed-byte-p b (logcdr x))))

  (add-to-ruleset ihsext-bounds-thms '(signed-byte-p-incr
                                       signed-byte-p-logcons
                                       signed-byte-p-logcdr))

  ;; from logops-lemmas
  (add-to-ruleset ihsext-bounds-thms '(signed-byte-p-logops)))



(defsection loghead**

  (local (defthm loghead-when-not-integerp
           (implies (not (integerp i))
                    (equal (loghead size i)
                           (loghead size 0)))
           :hints(("Goal" :in-theory (enable loghead)))))

  (local (defthm loghead-when-not-natp
           (implies (not (natp size))
                    (equal (loghead size i)
                           (loghead 0 i)))
           :hints(("Goal" :in-theory (enable loghead)))))

  (defthmd loghead**
    (equal (loghead size i)
           (if (zp size)
               0
             (logcons (logcar i)
                      (loghead (1- size) (logcdr i)))))
    :hints (("goal" :use ((:instance loghead*
                           (size (nfix size))
                           (i (ifix i))))))
    :rule-classes ((:definition
                    :clique (loghead)
                    :controller-alist ((loghead t nil)))))

  (add-to-ruleset ihsext-recursive-redefs '(loghead**))
  (add-to-ruleset ihsext-redefs '(loghead**))

  (local (in-theory (enable loghead**)))

  (defthmd loghead-when-zp
    (implies (zp size)
             (equal (loghead size i) 0)))

  (defthmd loghead-when-zip
    (implies (zip i)
             (equal (loghead size i) 0)))

  (add-to-ruleset ihsext-bad-type-thms '(loghead-when-zp
                                         loghead-when-zip))

  (defthmd loghead-induct
    t
    :rule-classes ((:induction
                    :pattern (loghead size i)
                    :scheme (logbitp-ind size i))))

  (add-to-ruleset ihsext-inductions '(loghead-induct))

  (defthm logcar-of-loghead
    (equal (logcar (loghead size i))
           (if (zp size) 0 (logcar i)))
    :hints (("goal" :expand ((loghead size i)))))

  (add-to-ruleset ihsext-basic-thms '(logcar-of-loghead))

  (defthmd logcdr-of-loghead
    (equal (logcdr (loghead size i))
           (if (zp size)
               0
             (loghead (1- size) (logcdr i))))
    :hints (("goal" :expand ((loghead size i)))))

  (add-to-ruleset ihsext-advanced-thms logcdr-of-loghead)

  (local (in-theory (enable* ihsext-recursive-redefs
                             ihsext-inductions)))

  (local (in-theory (disable logbitp-loghead)))

  (defthm logbitp-of-loghead
    (equal (logbitp pos (loghead size i))
           (and (< (nfix pos) (nfix size))
                (logbitp pos i))))

  (add-to-ruleset ihsext-basic-thms logbitp-of-loghead)

  (defthm unsigned-byte-p-of-loghead
    (implies (and (integerp size1)
                  (<= (nfix size) size1))
             (unsigned-byte-p size1 (loghead size i)))))

(defsection logtail**

  (local (defthm logtail-when-not-integerp
           (implies (not (integerp i))
                    (equal (logtail pos i)
                           (logtail pos 0)))
           :hints(("Goal" :in-theory (enable logtail)))))

  (local (defthm logtail-when-not-natp
           (implies (not (natp pos))
                    (equal (logtail pos i)
                           (logtail 0 i)))
           :hints(("Goal" :in-theory (enable logtail)))))

  (defthmd logtail**
    (equal (logtail pos i)
           (if (zp pos)
               (ifix i)
             (logtail (1- pos) (logcdr i))))
    :hints (("goal" :use ((:instance logtail*
                           (pos (nfix pos))
                           (i (ifix i))))))
    :rule-classes ((:definition
                    :clique (logtail)
                    :controller-alist ((logtail t nil)))))

  (add-to-ruleset ihsext-recursive-redefs '(logtail**))
  (add-to-ruleset ihsext-redefs '(logtail**))

  (local (in-theory (e/d* (logtail**) (logtail))))

  (defthmd logtail-when-zp
    (implies (zp pos)
             (equal (logtail pos i)
                    (ifix i))))

  (defthmd logtail-when-zip
    (implies (zip i)
             (equal (logtail pos i) 0)))

  (add-to-ruleset ihsext-bad-type-thms '(logtail-when-zp
                                         logtail-when-zip))

  (defthmd logtail-induct
    t
    :rule-classes ((:induction
                    :pattern (logtail pos i)
                    :scheme (logbitp-ind pos i))))

  (add-to-ruleset ihsext-inductions '(logtail-induct))


  (local (in-theory (enable* ihsext-recursive-redefs
                             ihsext-inductions)))

  (defthm logcdr-of-logtail
    (equal (logcdr (logtail pos i))
           (logtail (1+ (nfix pos)) i))
    :hints (("goal" :expand ((logtail pos i)))))

  (add-to-ruleset ihsext-basic-thms logcdr-of-logtail)

  (defthm logcar-of-logtail
    (equal (logcar (logtail pos i))
           (if (logbitp pos i) 1 0))
    :hints (("goal" :expand ((logtail pos i)))))

  (add-to-ruleset ihsext-basic-thms logcar-of-logtail)

  (local (in-theory (disable logbitp-logtail)))

  (defthm logbitp-of-logtail
    (equal (logbitp pos (logtail pos2 i))
           (logbitp (+ (nfix pos) (nfix pos2))
                    i)))

  (add-to-ruleset ihsext-basic-thms logbitp-of-logtail))


(defsection mod

  (defthmd mod-to-loghead
    (implies (and (integerp i)
                  ;; n is expected to be a natural, but it could really be
                  ;; anything except for a negative integer, since ash and
                  ;; loghead treat only those differently
                  (not (and (integerp n)
                            (< n 0))))
             (equal (mod i (ash 1 n))
                    (loghead n i)))
    :hints(("Goal" :in-theory (enable* ihsext-bad-type-thms
                                       loghead expt-2-is-ash))))

  (add-to-ruleset ihsext-arithmetic '(mod-to-loghead)))

(defsection floor

  (defthmd floor-to-logtail
    (implies (and (integerp i)
                  ;; n is expected to be a natural, but it could really be
                  ;; anything except for a negative integer, since ash and
                  ;; logtail treat only those differently
                  (not (and (integerp n)
                            (< n 0))))
             (equal (floor i (ash 1 n))
                    (logtail n i)))
    :hints(("Goal" :in-theory (enable* ihsext-bad-type-thms
                                       logtail expt-2-is-ash))))

  (add-to-ruleset ihsext-arithmetic '(floor-to-logtail)))






(defsection logext**

  (local (in-theory (enable* ihsext-bad-type-thms
                             logext)))

  (defthm logext-when-not-posp
    (implies (not (posp size))
             (equal (logext size i)
                    (if (= (logcar i) 1) -1 0)))
    :hints(("Goal" :in-theory (enable* logext))))

  (defthm logext-when-zip
    (implies (zip i)
             (equal (logext size i)
                    0))
    :hints(("Goal" :in-theory (e/d (logext) (logapp-0)))))

  (defthm logext**
    (equal (logext size i)
           (cond ((or (not (posp size))
                      (= size 1))
                  (if (= (logcar i) 1) -1 0))
                 (t (logcons (logcar i)
                             (logext (1- size) (logcdr i))))))
    ::hints(("Goal" :in-theory (disable logext)
             :use ((:instance logext*
                    (size (if (posp size) size 1))
                    (i (ifix i))))))
    :rule-classes ((:definition
                    :clique (logext)
                    :controller-alist ((logext t nil)))))

  (add-to-ruleset ihsext-recursive-redefs logext**)
  (add-to-ruleset ihsext-redefs logext**)

  (defun logext-ind (size i)
    (declare (xargs :measure (nfix size)))
    (cond ((or (not (posp size))
               (= size 1))
           (if (= (logcar i) 1) -1 0))
          (t (logcons (logcar i)
                      (logext-ind (1- size) (logcdr i))))))

  (defthmd logext-induct
    t
    :rule-classes ((:induction
                    :pattern (logext pos i)
                    :scheme (logext-ind pos i))))

  (add-to-ruleset ihsext-inductions logext-induct)

  (in-theory (disable logext-when-not-posp
                      logext-when-zip))

  (add-to-ruleset ihsext-bad-type-thms
                  '(logext-when-not-posp
                    logext-when-zip))

  (local (in-theory (e/d* (ihsext-recursive-redefs
                           ihsext-inductions)
                          (logext signed-byte-p))))

  (defthm logbitp-of-logext
    (equal (logbitp pos (logext size i))
           (if (< (nfix pos) (nfix size))
               (logbitp pos i)
             (logbitp (1- size) i))))

  (defthm signed-byte-p-of-logext
    (implies (and (integerp size1)
                  (>= size1 (if (posp size) size 1)))
             (signed-byte-p size1 (logext size i))))

  (add-to-ruleset ihsext-basic-thms signed-byte-p-of-logext)

  ;; ihs rule with unnecessary type hyps
  (in-theory (disable signed-byte-p-logext)))
