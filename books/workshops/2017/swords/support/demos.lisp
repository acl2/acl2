

(in-package "ACL2")

(include-book "centaur/gl/gl" :dir :system)
(include-book "centaur/gl/bfr-satlink" :dir :system)
(include-book "misc/records" :dir :system)
(include-book "std/testing/eval" :dir :system)
(include-book "centaur/bitops/install-bit" :dir :system)
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))

; cert_param: (uses-glucose)
(gl::gl-satlink-mode)
(value-triple (tshell-start))

(defun my-satlink-config ()
  (declare (Xargs :guard t))
  (satlink::make-config
   :cmdline "glucose -model"
   :verbose t
   :mintime 1))

(defattach gl::gl-satlink-config my-satlink-config)

(gl::def-gl-rewrite expand-loghead-bits
  (implies (syntaxp (integerp n))
           (equal (loghead n x)
                  (if (zp n)
                      0
                    (logcons (if (logbitp 0 x) 1 0)
                             (loghead (1- n) (ash x -1))))))
  :hints(("Goal" :expand ((loghead n x)
                          (logtail 1 x)
                          (logbitp 0 x)))))


;; this theorem needs expand-loghead-bits, but works with or without logbitp-of-ash-minus1
(gl::def-gl-thm lognot-lognot-of-loghead-1
    :hyp t
    :concl (equal (lognot (lognot (loghead 5 x))) (loghead 5 x))
    :g-bindings nil
    :rule-classes nil)

(encapsulate nil
  (local (gl::def-gl-rewrite logbitp-of-ash-minus1
           (implies (syntaxp (integerp n))
                    (equal (logbitp n (ash x -1))
                           (logbitp (+ 1 (nfix n)) x)))))

  (gl::def-gl-thm lognot-lognot-of-loghead-2
    :hyp t
    :concl (equal (lognot (lognot (loghead 5 x))) (loghead 5 x))
    :g-bindings nil
    :rule-classes nil))

;; (gl::def-gl-rewrite expand-logext-bits
;;   (implies (syntaxp (integerp n))
;;            (equal (logext n x)
;;                   (if (<= (nfix n) 1)
;;                       (if (logbitp 0 x) -1 0)
;;                     (logcons (if (logbitp 0 x) 1 0)
;;                              (logext (1- n) (ash x -1))))))
;;   :hints(("Goal" :expand ((logext n x)
;;                           (logtail 1 x)
;;                           (logbitp 0 x)))))

(encapsulate nil
  ;; clear the ctrex-rewrite table to demo this getting a false counterexample
  (local (table gl::glcp-ctrex-rewrite nil nil :clear))

  (must-fail
   ;; generates a false counterexample
   (gl::def-gl-thm minus-logext-minus-loghead-is-logext-loghead
     :hyp t
     :concl (equal (- (logext 5 (- (loghead 5 x))))
                   (logext 5 (loghead 5 x)))
     :g-bindings nil
     :rule-classes nil)))

(encapsulate nil
  ;; clear the ctrex-rewrite table and install the two necessary rules to get a real counterexample
  (local (table gl::glcp-ctrex-rewrite nil nil :clear))



  (gl::def-glcp-ctrex-rewrite
    ((ash x -1) y)
    (x (logapp 1 x y)))

  (gl::def-glcp-ctrex-rewrite
    ((logbitp n x) y)
    (x (bitops::install-bit n (bool->bit y) x)))

  (must-fail
   ;; generates a real counterexample
   (gl::def-gl-thm minus-logext-minus-loghead-is-logext-loghead
     :hyp t
     :concl (equal (- (logext 5 (- (loghead 5 x))))
                   (logext 5 (loghead 5 x)))
     :g-bindings nil
     :rule-classes nil)))


;; These don't work without the logbitp => integerp constraint
(must-fail
 (gl::def-gl-thm loghead-when-not-integer
   :hyp t
   :concl (equal (and (integerp x)
                      (equal (loghead 5 x) 16))
                 (equal (loghead 5 x) 16))
   :g-bindings nil))

(must-fail
 (gl::def-gl-thm loghead-4-of-ifix
   :hyp t
   :concl (equal (loghead 4 (ifix x)) (loghead 4 x))
   :g-bindings nil))

(encapsulate nil

  ;; use the (logbitp n x) normal form for bits
  (local (gl::def-gl-rewrite logbitp-of-ash-minus1
           (implies (syntaxp (integerp n))
                    (equal (logbitp n (ash x -1))
                           (logbitp (+ 1 (nfix n)) x)))))
  
  ;; this constraint suffices when using the (logbitp n x) form:
  (local
   (gl::def-gl-boolean-constraint logbitp-implies-integerp
     :bindings ((bit0 (logbitp n x))
                (intp (integerp x)))
     :body (implies bit0 intp)
     :hints (("goal" :expand ((logbitp n x) (logcar x) (logcdr x))))))
  
  (gl::def-gl-thm loghead-when-not-integer-1
    :hyp t
    :concl (equal (and (integerp x)
                       (equal (loghead 5 x) 16))
                  (equal (loghead 5 x) 16))
    :g-bindings nil)

  (gl::def-gl-thm loghead-4-of-ifix-1
    :hyp t
    :concl (equal (loghead 4 (ifix x)) (loghead 4 x))
    :g-bindings nil))

(encapsulate nil

  ;; don't use the (logbitp n x) normal form for bits -- stick with
  ;; (logbitp 0 (ash .... -1))

  ;; need both of these when using (logbitp 0 (ash ... -1)) normal form:
  (local (gl::def-gl-boolean-constraint logbitp-implies-nonzero
           :bindings ((bit0 (logbitp n x)))
           :body (implies bit0 (and (not (equal 0 x)) (integerp x)))
           :hints (("goal" :expand ((logbitp n x) (logcar x) (logcdr x))))))

  (local (gl::def-gl-boolean-constraint nonzero-rsh-implies-nonzero
           :bindings ((iszero (equal 0 (ash x -1))))
           :body (implies (not iszero) (and (not (equal 0 x)) (integerp x)))
           :hints (("goal" :expand ((logbitp n x) (logcar x) (logcdr x) (logtail 1 x))))))

  
  (gl::def-gl-thm loghead-when-not-integer-2
    :hyp t
    :concl (equal (and (integerp x)
                       (equal (loghead 5 x) 12))
                  (equal (loghead 5 x) 12))
    :g-bindings nil)

  (gl::def-gl-thm loghead-4-of-ifix-2
    :hyp t
    :concl (equal (loghead 4 (ifix x)) (loghead 4 x))
    :g-bindings nil))






(defun plus (st dest src1 src2)
  (s dest (loghead 10 (+ (g src1 st) (g src2 st))) st))

(gl::def-gl-rewrite g-of-s
  (equal (g k1 (s k2 v x))
         (if (equal k1 k2)
             v
           (g k1 x))))

(gl::gl-set-uninterpreted g)
(gl::gl-set-uninterpreted s)

(local (defthmd nth-const-of-cons
         (implies (syntaxp (quotep n))
                  (equal (nth n (cons a b))
                         (if (zp n)
                             a
                           (nth (1- n) b))))
         :hints(("Goal" :in-theory (enable nth)))))

(defun s-inverse (key obj)
  (list key (g key obj) obj))

(gl::def-gl-thm plus-c-a-b-correct
  :hyp (and (unsigned-byte-p 9 (g :a st))
            (unsigned-byte-p 9 (g :b st))
            (consp st))
  :concl (b* ((new-st (plus st :c :a :b))
              (a (g :a st))
              (b (g :b st))
              (new-c (g :c new-st)))
           (equal new-c (+ a b)))
  :g-bindings `((st ,(gl::g-call 's
                                 (list :a
                                       (gl::g-int 0 1 10)
                                       (gl::g-call 's
                                                   (list :b
                                                         (gl::g-int 10 1 10)
                                                         (gl::g-var 'rest-of-st))
                                                   '(lambda (x) (s-inverse ':b x))))
                                 '(lambda (x) (s-inverse ':a x)))))
  :cov-theory-add '(nth-const-of-cons
                    s-same-g
                    s-inverse))

(gl::def-gl-thm plus-c-a-b-correct-2
  :hyp (and (unsigned-byte-p 9 (g :a (cdr st)))
            (unsigned-byte-p 9 (g :b (cdr st)))
            (consp st))
  :concl (b* ((st (cdr st))
              (new-st (plus st :c :a :b))
              (a (g :a st))
              (b (g :b st))
              (new-c (g :c new-st)))
           (equal new-c (+ a b)))
  :g-bindings `((st ,(cons (gl::g-var 'foo)
                           (gl::g-call 's
                                       (list :a
                                             (gl::g-int 0 1 10)
                                             (gl::g-call 's
                                                         (list :b
                                                               (gl::g-int 10 1 10)
                                                               (gl::g-var 'rest-of-st))
                                                         '(lambda (x) (s-inverse ':b x))))
                                       '(lambda (x) (s-inverse ':a x))))))
  :cov-theory-add '(nth-const-of-cons
                    s-same-g s-inverse))





(gl::gl-set-uninterpreted g :concrete-only)
(gl::gl-set-uninterpreted s :concrete-only)

(gl::def-gl-rewrite g-of-s-casesplit
  (equal (g k1 (s k2 v x))
         (if (equal k1 k2)
             v
           (g k1 x))))

(gl::def-gl-rewrite s-of-s-normalize
  (implies (syntaxp (and (gl::general-concretep k1)
                         (gl::general-concretep k2)
                         (not (<< (gl::general-concrete-obj k1)
                                  (gl::general-concrete-obj k2)))))
           (equal (s k1 v1 (s k2 v2 x))
                  (if (equal k1 k2)
                      (s k1 v1 x)
                    (s k2 v2 (s k1 v1 x))))))

(gl::def-glcp-ctrex-rewrite
  ((g k x) v)
  (x (s k v x)))

(gl::def-gl-branch-merge merge-if-of-s
  (equal (if test (s k v x) y)
         (s k (if test v (g k y)) (if test x y))))




(defun gs-equal-except (lst x y)
  (if (atom lst)
      (equal x y)
    (gs-equal-except (cdr lst)
                     (s (car lst) nil x)
                     (s (car lst) nil y))))

(gl::gl-set-uninterpreted gs-equal-except)

;; (in-theory (disable gs-equal-except))



(local (defthm s-same-equal-implies-s-any-equal
         (implies (equal (s k a x) (s k a y))
                  (equal (equal (s k b x) (s k b y))
                         t))
         :hints (("goal" :use ((:instance s-same-s
                                (a k) (r x) (y b) (x a))
                               (:instance s-same-s
                                (a k) (r y) (y b) (x a)))
                  :in-theory (disable s-same-s)))))

(gl::def-gl-rewrite equal-of-s
  (equal (equal (s k v x) y)
         (and (equal v (g k y))
              (gs-equal-except (list k) x y)))
  :hints (("goal" :use ((:instance s-same-equal-implies-s-any-equal
                         (a nil) (b (g k y))))
           :in-theory (disable s-same-equal-implies-s-any-equal))))

(gl::def-gl-rewrite equal-of-s-2
  (equal (equal y (s k v x))
         (and (equal v (g k y))
              (gs-equal-except (list k) x y)))
  :hints (("goal" :use ((:instance s-same-equal-implies-s-any-equal
                         (a nil) (b (g k y))))
           :in-theory (disable s-same-equal-implies-s-any-equal))))

(local (defthm gs-equal-except-of-s-member
         (implies (member k lst)
                  (equal (gs-equal-except lst (s k v x) y)
                         (gs-equal-except lst x y)))
         :hints (("goal" :induct (gs-equal-except lst x y))
                 (and stable-under-simplificationp
                      '(:use ((:instance s-diff-s
                               (a k) (x v) (b (car lst)) (y nil) (r x)))
                        :in-theory (disable s-diff-s))))))

(gl::def-gl-rewrite gs-equal-except-of-s
  (equal (gs-equal-except lst (s k v x) y)
         (if (member k lst)
             (gs-equal-except lst x y)
           (and (equal v (g k y))
                (gs-equal-except (cons k lst) x y))))
  :hints (("goal" :induct (gs-equal-except lst x y))
          (and stable-under-simplificationp
               (cond ((member-equal '(not (member-equal k (cdr lst))) clause)
                     '(:use ((:instance s-diff-s
                              (a k) (x v) (b (car lst)) (y nil) (r x)))
                       :in-theory (disable s-diff-s)))
                     (t '(:use ((:instance s-same-equal-implies-s-any-equal
                                 (a nil) (b (g k y))))
                          :in-theory (disable s-same-equal-implies-s-any-equal)))))))

(gl::def-gl-rewrite gs-equal-except-of-s-2
  (equal (gs-equal-except lst y (s k v x))
         (if (member k lst)
             (gs-equal-except lst y x)
           (and (equal v (g k y))
                (gs-equal-except (cons k lst) y x))))
  :hints (("goal" :induct (gs-equal-except lst y x))
          (and stable-under-simplificationp
               (cond ((member-equal '(not (member-equal k (cdr lst))) clause)
                     '(:use ((:instance s-diff-s
                              (a k) (x v) (b (car lst)) (y nil) (r x)))
                       :in-theory (disable s-diff-s)))
                     (t '(:use ((:instance s-same-equal-implies-s-any-equal
                                 (a nil) (b (g k y))))
                          :in-theory (disable s-same-equal-implies-s-any-equal)))))))

(gl::def-gl-rewrite gs-equal-except-of-s-base-case
  (implies (and (syntaxp (and (not (and (consp x)
                                        (eq (gl::tag x) :g-apply)
                                        (eq (gl::g-apply->fn x) 's)))
                              (not (and (consp y)
                                        (eq (gl::tag y) :g-apply)
                                        (eq (gl::g-apply->fn y) 's)))))
                (equal x y))
           (equal (gs-equal-except lst x y) t)))


(defun simple-machine-step (instr st)
  (case-match instr
    (('add dest src1 src2) (s dest
                              (loghead 32 (+ (loghead 32 (g src1 st))
                                             (loghead 32 (g src2 st))))
                              st))
    (('sub dest src1 src2) (s dest
                              (loghead 32 (- (loghead 32 (g src1 st))
                                             (loghead 32 (g src2 st))))
                              st))
    (('mask dest src maskval) (s dest
                                 (logand (loghead 32 (g src st)) maskval)
                                 st))
    (('rsh dest src shamt) (s dest
                              (logtail shamt (loghead 32 (g src st)))
                              st))
    (('cmul dest src const) (s dest
                               (loghead 32 (* (loghead 32 (g src st)) const))
                               st))
    (& st)))

(defun simple-machine-run (prog st)
  (if (atom prog)
      st
    (simple-machine-run (cdr prog) (simple-machine-step (car prog) st))))

(defconst *simple-machine-bitcount*
  '((rsh tmp1 v 1)
    (mask tmp1 tmp1 #x55555555)
    (sub v v tmp1)
    (mask tmp1 v #x33333333)
    (rsh tmp2 v 2)
    (mask tmp2 tmp2 #x33333333)
    (add v tmp1 tmp2)
    (rsh tmp1 v 4)
    (add tmp1 v tmp1)
    (mask tmp1 tmp1 #x0f0f0f0f)
    (cmul tmp1 tmp1 #x01010101)
    (rsh c tmp1 24)))
    

(gl::def-gl-thm simple-machine-computes-logcount
  :hyp t
  :concl (b* ((v (g 'v initst))
              (finalst (simple-machine-run *simple-machine-bitcount* initst))
              (c (g 'c finalst)))
           (equal c (logcount (loghead 32 v))))
  :g-bindings nil)

(defconst *simple-machine-bitcount-cleanup*
  (append *simple-machine-bitcount*
          '((sub tmp1 tmp1 tmp1)
            (sub tmp2 tmp2 tmp2)
            (sub v v v))))

(gl::def-gl-thm simple-machine-logcount-final-st
  :hyp t
  :concl (b* ((v (g 'v initst))
              (finalst (simple-machine-run *simple-machine-bitcount-cleanup* initst)))
           (equal finalst
                  (s 'tmp1 0
                     (s 'tmp2 0
                        (s 'v 0
                           (s 'c (logcount (loghead 32 v))
                              initst))))))
  :g-bindings nil)

;; Validcounterexamples:
(must-fail
 (gl::def-gl-thm simple-machine-logcount-final-st-ctrex
   :hyp t
   :concl (b* ((v (g 'v initst))
               (finalst (simple-machine-run *simple-machine-bitcount-cleanup* initst)))
            (equal finalst
                   (s 'tmp1 0
                      (s 'tmp2 0
                         (s 'v 0
                            (s 'c (logcount (logand (loghead 32 v) (lognot 16)))
                               initst))))))
   :g-bindings nil))
    


(fty::deftagsum simple-machterm
  (:var ((name symbolp)))
  (:let ((name symbolp)
         (val simple-machterm)
         (body simple-machterm)))
  (:binary ((op symbolp)
            (src1 simple-machterm)
            (src2 simple-machterm)))
  (:immed  ((op symbolp)
            (src simple-machterm)
            (imm natp)))
  :layout :list)


(define simple-machterm-eval ((term simple-machterm-p)
                              env)
  :measure (simple-machterm-count term)
  (simple-machterm-case term
    :var (mbe :logic (loghead 32 (g term.name env))
              :exec (loghead 32 (ifix (g term.name env))))
    :let (simple-machterm-eval
          term.body
          (s term.name (simple-machterm-eval term.val env) env))
    :binary (b* ((src1 (simple-machterm-eval term.src1 env))
                 (src2 (simple-machterm-eval term.src2 env)))
              (case term.op
                (add (loghead 32 (+ src1 src2)))
                (otherwise (loghead 32 (- src1 src2)))))
    :immed (b* ((src (simple-machterm-eval term.src env)))
              (case term.op
                (mask (loghead 32 (logand src term.imm)))
                (rsh  (loghead 32 (logtail term.imm src)))
                (otherwise (loghead 32 (* src term.imm)))))))

(defconst *simple-machterm-count*
  (simple-machterm-let
   'v
   (simple-machterm-binary 'sub
                           (simple-machterm-var 'v)
                           (simple-machterm-immed 'mask
                                                  (simple-machterm-immed 'rsh
                                                                         (simple-machterm-var 'v)
                                                                         1)
                                                  #x55555555))
   (simple-machterm-let
    'v
    (simple-machterm-binary 'add
                            (simple-machterm-immed 'mask
                                                   (simple-machterm-var 'v)
                                                   #x33333333)
                            (simple-machterm-immed 'mask
                                                   (simple-machterm-immed 'rsh
                                                                          (simple-machterm-var 'v)
                                                                          2)
                                                   #x33333333))
    (simple-machterm-immed 'rsh
                           (simple-machterm-immed 'cmul
                                                  (simple-machterm-immed 'mask
                                                                         (simple-machterm-binary 'add
                                                                                                 (simple-machterm-var 'v)
                                                                                                 (simple-machterm-immed 'rsh
                                                                                                                        (simple-machterm-var 'v)
                                                                                                                        4))
                                                                         #x0f0f0f0f)
                                                  #x01010101)
                           24))))


(def-gl-thm simple-machterm-count-correct
  :hyp t
  :concl (equal (simple-machterm-eval *simple-machterm-count* env)
                (logcount (loghead 32 (g 'v env))))
  :g-bindings nil)

(defun simple-machine-symstep (instr st)
  (case-match instr
    (('add dest src1 src2) (s dest
                              (simple-machterm-binary 'add
                                                      (g src1 st)
                                                      (g src2 st))
                              st))
    (('sub dest src1 src2) (s dest
                              (simple-machterm-binary 'sub
                                                      (g src1 st)
                                                      (g src2 st))
                              st))
    (('mask dest src maskval) (s dest
                                 (simple-machterm-immed 'mask
                                                        (g src st)
                                                        maskval)
                                 st))
    (('rsh dest src shamt) (s dest
                              (simple-machterm-immed 'rsh
                                                     (g src st)
                                                     shamt)
                              st))
    (('cmul dest src const) (s dest
                               (simple-machterm-immed 'cmul
                                                      (g src st)
                                                      const)
                               st))
    (& st)))



(defun simple-machine-symrun (prog st)
  (if (atom prog)
      st
    (simple-machine-symrun (cdr prog) (simple-machine-symstep (car prog) st))))


#||
(trace$ (simple-machterm-p :entry (list 'simple-machterm-p (car x)) :exit (list 'simple-machterm-p (car x))))
||#

;; this demos how often simple-machterm-p gets called during symbolic execution by default
(def-gl-thm simple-machine-symrun-of-simple-machine-bitcount-correct
  :hyp t
  :concl (b* ((initst (s 'v (simple-machterm-var 'v) emptyst))
              (finalst (simple-machine-symrun *simple-machine-bitcount* initst))
              (c-term (g 'c finalst)))
           (equal (simple-machterm-eval c-term env)
                  (logcount (loghead 32 (g 'v env)))))
  :g-bindings nil)                                 


(gl::gl-set-uninterpreted simple-machterm-fix)
(gl::gl-set-uninterpreted simple-machterm-p)
(gl::gl-set-uninterpreted simple-machterm-kind)

(gl::gl-set-uninterpreted simple-machterm-var)
(gl::gl-set-uninterpreted simple-machterm-var->name)

(gl::gl-set-uninterpreted simple-machterm-let)
(gl::gl-set-uninterpreted simple-machterm-let->name)
(gl::gl-set-uninterpreted simple-machterm-let->val)
(gl::gl-set-uninterpreted simple-machterm-let->body)

(gl::gl-set-uninterpreted simple-machterm-binary)
(gl::gl-set-uninterpreted simple-machterm-binary->op)
(gl::gl-set-uninterpreted simple-machterm-binary->src1)
(gl::gl-set-uninterpreted simple-machterm-binary->src2)

(gl::gl-set-uninterpreted simple-machterm-immed)
(gl::gl-set-uninterpreted simple-machterm-immed->op)
(gl::gl-set-uninterpreted simple-machterm-immed->src)
(gl::gl-set-uninterpreted simple-machterm-immed->imm)

(gl::add-gl-rewrite simple-machterm-p-of-simple-machterm-fix)
(gl::add-gl-rewrite return-type-of-simple-machterm-var)
(gl::add-gl-rewrite return-type-of-simple-machterm-let)
(gl::add-gl-rewrite return-type-of-simple-machterm-binary)
(gl::add-gl-rewrite return-type-of-simple-machterm-immed)

(gl::add-gl-rewrite simple-machterm-fix-when-simple-machterm-p)

(gl::add-gl-rewrite simple-machterm-var->name-of-simple-machterm-var)

(gl::add-gl-rewrite simple-machterm-let->name-of-simple-machterm-let)
(gl::add-gl-rewrite simple-machterm-let->val-of-simple-machterm-let)
(gl::add-gl-rewrite simple-machterm-let->body-of-simple-machterm-let)

(gl::add-gl-rewrite simple-machterm-binary->op-of-simple-machterm-binary)
(gl::add-gl-rewrite simple-machterm-binary->src1-of-simple-machterm-binary)
(gl::add-gl-rewrite simple-machterm-binary->src2-of-simple-machterm-binary)

(gl::add-gl-rewrite simple-machterm-immed->op-of-simple-machterm-immed)
(gl::add-gl-rewrite simple-machterm-immed->src-of-simple-machterm-immed)
(gl::add-gl-rewrite simple-machterm-immed->imm-of-simple-machterm-immed)


(def-gl-thm simple-machine-symrun-of-simple-machine-bitcount-correct-2
  :hyp t
  :concl (b* ((initst (s 'v (simple-machterm-var 'v) emptyst))
              (finalst (simple-machine-symrun *simple-machine-bitcount* initst))
              (c-term (g 'c finalst)))
           (equal (simple-machterm-eval c-term env)
                  (logcount (loghead 32 (g 'v env)))))
  :g-bindings nil)


