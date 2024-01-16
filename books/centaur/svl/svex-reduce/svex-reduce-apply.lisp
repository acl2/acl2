; SVL - Listener-based Hierachical Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2021 Centaur Technology
; Copyright (C) 2022 Intel Corporation
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Mertcan Temel <mert@centtech.com>

(in-package "SVL")

(include-book "base")

(include-book "projects/rp-rewriter/top" :dir :system)
(include-book "../fnc-defs")

(local
 (include-book "../4vec-lemmas"))

(local
 (include-book "../bits-sbits"))

(local
 (rp::fetch-new-events
  (include-book "centaur/bitops/ihs-extensions" :dir :system)
  use-ihs-extensions
  :disabled t))

(local
 (rp::fetch-new-events
  (include-book "ihs/logops-lemmas" :dir :system)
  use-ihs-logops-lemmas
  :disabled t))

(local
 (rp::fetch-new-events
  (include-book "arithmetic-5/top" :dir :system)
  use-arithmetic-5
  :disabled t))

(local
 (rp::fetch-new-events
  (include-book "ihs/quotient-remainder-lemmas" :dir :system)
  use-qr-lemmas
  :disabled t))

(local
 (rp::fetch-new-events
  (include-book "centaur/bitops/equal-by-logbitp" :dir :system)
  use-equal-by-logbitp
  :disabled t))

(define nth-4vec (n argsvar)
  :guard (natp n)
  (if (atom argsvar)
      (SV::4VEC-X)
    (if (zp n)
        (car argsvar)
      (nth-4vec (1- n) (cdr argsvar))))
  ///
  (defthm nth-4vec-opener
    (implies (natp n)
             (equal (nth-4vec n argsvar)
                    (if (atom argsvar)
                        (SV::4VEC-X)
                      (if (zp n)
                          (car argsvar)
                        (nth-4vec (1- n) (cdr argsvar))))))
    :hints (("Goal"
             :in-theory (e/d (nth-4vec) ())))))

(defund svex-apply-constants-collect-arg-meta (n max argsvar)
  (declare (xargs :measure (nfix (- (nfix max) (nfix n)))))
  (let* ((n (nfix n)) (max (nfix max)))
    (if (zp (- max n))
        nil
      (b* ((rest (svex-apply-CONSTANTS-collect-arg-meta (+ 1 n) max argsvar)))
        (cons `(nth-4vec ,n ,argsvar) rest)))))

(defund svex-apply-constant-cases-fn (argsvar optable)
  (b* (((when (atom optable))
        '((otherwise
           (hons fn args)
           #|(or (hard-error
           'svex-apply-cases-wog-fn-meta
           "attempting to apply unknown function ~x0~%"
           (list (cons #\0 fn)))
           (sv::4vec-x))|#)))
       ((list sym fn args) (car optable))
       (entry-for-quoted
        (svex-apply-CONSTANTS-collect-arg-meta 0 (len args) argsvar ))
       (call
        `(,fn . ,entry-for-quoted)))
    (cons (cons sym (cons call 'nil))
          (svex-apply-constant-cases-fn argsvar (cdr optable)))))

;; (define bit?!-resolve ((test sv::4vec-p) then else (shift-amount natp))
;;   (cond ((equal test -1) then)
;;         ((or (equal test 0)
;;              (equal test (sv::4vec-x))
;;              (equal test (sv::4vec-z)))
;;          else)
;;         (t
;;          (if (equal (4vec-part-select 0 1 test) 1)
;;              (hons-list
;;               'sv::concat 1

(define calc-bit-repetition ((the-bit sv::4vec-p)
                             (num sv::4vec-p)
                             (limit natp))
  :measure (nfix limit)
  :returns (res natp)
  (cond ((zp limit) 0)
        ((not (equal (4vec-part-select 0 1 num)
                     (4vec-part-select 0 1 the-bit)))
         0)
        (t (b* ((rest (calc-bit-repetition the-bit
                                           (4vec-rsh 1 num)
                                           (1- limit))))
             (1+ rest)))))

(local
 (defthm sv::4vec->upper-and-lower-equivalance
   (implies (integerp x)
            (equal (sv::4vec->lower x)
                   (sv::4vec->upper x)))
   :hints (("goal"
            :in-theory (e/d (sv::4vec->upper
                             sv::4vec->lower
                             ) ())))))

(local
 (defthm svex-p-of-consed
   (implies (and (not (equal fn ':var))
                 (not (integerp fn)))
            (equal (svex-p (cons fn args))
                   (and (FNSYM-P fn)
                        (SVEXLIST-P args))))
   :hints (("Goal"
            :in-theory (e/d (svex-p) ())))))
(local
 (defthm natp-implies-svex-p
   (implies (natp x)
            (svex-p x))
   :rule-classes :type-prescription
   :hints (("Goal"
            :in-theory (e/d (svex-p) ())))))

(local
 (defthm 4vec-p-implies-svex-p
   (implies (4vec-p x)
            (svex-p x))
   :rule-classes :type-prescription
   :hints (("Goal"
            :in-theory (e/d (svex-p
                             4vec-p)
                            ())))))

(define bit?-resolve ((test 4vec-p)
                      then
                      else
                      (limit natp))

  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (4vec-rsh
                            4VEC-P
                            sv::3vec-p
                            SV::4VEC->LOWER
                            SV::4VEC->upper
                            4vec-shift-core)
                           (4vec))))
  :measure (nfix limit)
  :returns (res svex-p :hyp (and (4vec-p test)
                                 (svex-p then)
                                 (svex-p else)))
  (cond
   ((zp limit) (hons-list 'sv::bit? test then else)) ;; for measure
   ((equal test -1) then)
   ((or (equal test 0))
    else)
   ((or (equal test (sv::4vec-x))
        (equal test (sv::4vec-z)))
    (if (and (4vec-p test) (4vec-p then) (4vec-p else))
        (sv::4vec-bit? test then else)
      (hons-list 'sv::bit? test then else)))
   (t
    (b* ((first-size (calc-bit-repetition test test (expt 2 30)))
         ((unless (posp first-size)) ;; should never happen
          `(sv::bit? ,test ,then ,else))
         (test-cut (4vec-part-select 0 first-size test))
         (rest (bit?-resolve (4vec-rsh first-size test)
                             (if (4vec-p then)
                                 (4vec-rsh first-size then)
                               (hons-list 'sv::rsh first-size then))
                             (if (4vec-p else)
                                 (4vec-rsh first-size else)
                               (hons-list 'sv::rsh first-size else))
                             (1- limit))))
      (cond ((equal test-cut 0)
             (if (and (4vec-p else)
                      (4vec-p rest))
                 (4vec-concat first-size else rest)
               (hons-list 'sv::concat first-size else rest)))
            ((equal test-cut (4vec-part-select 0 first-size -1))
             (if (and (4vec-p then)
                      (4vec-p rest))
                 (4vec-concat first-size then rest)
               (hons-list 'sv::concat first-size then rest)))
            (t
             (if (and (4vec-p else)
                      (4vec-p then)
                      (4vec-p rest))
                 (4vec-concat first-size (sv::4vec-bit? test-cut then else) rest)
               (hons-list 'sv::concat
                          first-size
                          (hons-list 'sv::bit? test-cut then else)
                          rest))))))))

(define bit?!-resolve ((test sv::4vec-p)
                       then
                       else
                       (limit natp))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (4vec-rsh
                            4VEC-P
                            SV::4VEC->LOWER
                            SV::4VEC->upper
                            4vec-shift-core)
                           (4vec))))
  :measure (nfix limit)
  :returns (res svex-p :hyp (and (4vec-p test)
                                 (svex-p then)
                                 (svex-p else)))
  (cond
   ((zp limit) (hons-list 'sv::bit?! test then else)) ;; for measure
   ((equal test -1) then)
   ((or (equal test 0)
        (equal test (sv::4vec-x))
        (equal test (sv::4vec-z)))
    else)
   (t
    (b* ((first-size (calc-bit-repetition test test (expt 2 30)))
         ((unless (posp first-size)) ;; should never happen
          `(sv::bit?! ,test ,then ,else))
         (test-cut (4vec-part-select 0 first-size test))
         (rest (bit?!-resolve (4vec-rsh first-size test)
                              (if (4vec-p then)
                                  (4vec-rsh first-size then)
                                (hons-list 'sv::rsh first-size then))
                              (if (4vec-p else)
                                  (4vec-rsh first-size else)
                                (hons-list 'sv::rsh first-size else))
                              (1- limit))))
      (cond ((or (equal test-cut (4vec-part-select 0 first-size (sv::4vec-x)))
                 (equal test-cut (4vec-part-select 0 first-size (sv::4vec-z)))
                 (equal test-cut 0))
             (if (and (4vec-p else)
                      (4vec-p rest))
                 (4vec-concat first-size else rest)
               (hons-list 'sv::concat first-size else rest)))
            ((equal test-cut (4vec-part-select 0 first-size -1))
             (if (and (4vec-p then)
                      (4vec-p rest))
                 (4vec-concat first-size then rest)
               (hons-list 'sv::concat first-size then rest)))
            (t ;; should never come here
             `(sv::bit?! ,test ,then ,else)))))))

(local
 (defthm svex-p-of-fn-call-reconstructed
   (implies (and (fnsym-p fn)
                 (svexlist-p args))
            (svex-p (cons fn args)))
   :hints (("goal"
            :in-theory (e/d (svex-p) ())))))

(defmacro and*-exec (&rest x)
  `(mbe :logic (and* ,@x)
        :exec (and ,@x)))

(define concat-reduce ((svex))
  :returns (res sv::svex-p :hyp (sv::svex-p svex)
                :hints (("Goal"
                         :in-theory (e/d (svex-p
                                          SVEXLIST-P)
                                         ()))))
  :guard-hints (("Goal"
                 :in-theory (e/d (svex-p
                                  SVEXLIST-P)
                                 ())))
  :prepwork ((create-case-match-macro concat-of-unfloat-pattern
                                      ('sv::concat size ('sv::unfloat x) ('sv::unfloat y))
                                      (natp size))

             (create-case-match-macro concat-of-conseq-partsel-pattern
                                      ('sv::concat size
                                                   ('sv::partsel st1 sz1 x)
                                                   ('sv::partsel st2 sz2 x))
                                      (and (natp size)
                                           (natp st1) (natp st2)
                                           (natp sz1) (natp sz2)
                                           (equal sz1 size)
                                           (equal (+ st1 sz1) st2)))

             (set-ignore-ok t))
  (cond ((concat-of-unfloat-pattern-p svex)
         (concat-of-unfloat-pattern-body
          svex
          (hons-list
           'sv::unfloat
           (concat-reduce (hons-list 'sv::concat size x y)))))
        ((concat-of-conseq-partsel-pattern-p svex)
         (concat-of-conseq-partsel-pattern-body
          svex
          (hons-list 'sv::partsel st1 (+ sz1 sz2) x)))
        (t svex)))


(define rsh-reduce ((svex))
  :returns (res sv::svex-p :hyp (sv::svex-p svex)
                :hints (("Goal"
                         :in-theory (e/d (svex-p
                                          SVEXLIST-P)
                                         ()))))
  :guard-hints (("Goal"
                 :in-theory (e/d (svex-p
                                  SVEXLIST-P)
                                 ())))
  :prepwork ((create-case-match-macro rsh-of-partsel
                                      ('sv::rsh size ('sv::partsel start2 size2 var))
                                      (and (natp size)
                                           (natp start2)
                                           (natp size2)))

             (set-ignore-ok t))
  (cond ((rsh-of-partsel-p svex)
         (rsh-of-partsel-body
          svex
          (b* (((when (<= size2 size))
                0)
               (new-start (+ start2 size))
               (new-size (+ size2 (- size))))
            (hons-list 'sv::partsel new-start new-size var))))
        (t svex)))

(local
 (defthm and*-of-repeated
   (equal (and* x x)
          x)
   :hints (("Goal"
            :in-theory (e/d (and*) ())))))

(define svex-reduce-w/-env-apply-specials (fn args)
  :returns (res svex-p :hyp (and (FNSYM-P fn)
                                 (SVEXLIST-P args))
                :hints (("Goal"
                         :expand ((SVEXLIST-P ARGS)
                                  (SVEX-P (CAR ARGS)))
                         :in-theory (e/d () ()))))
  (cond
   ((and* (or* (equal fn 'sv::?)
               (equal fn 'sv::?*))
          (equal-len args 3))
    (b* ((test (first args))
         (then (second args))
         (else (third args))
         ((when (and*-exec (equal then else)
                           (integerp then)))
          then)
         ((unless (4vec-p test)) (hons fn args))
         (test (sv::3vec-fix test))
         
         ((sv::4vec test))
         ((when (eql test.upper 0))
          else)
         ((when (not (eql test.lower 0)))
          then))
      (hons fn args)))

   ((and* (equal fn 'sv::?!)
          (equal-len args 3))
    (b* ((test (first args))
         ((unless (4vec-p test)) (hons fn args))
         ((sv::4vec test))
         (testvec (logand test.upper test.lower))
         ((when (eql testvec 0)) (third args)))
      (second args)))

   ((and* (equal fn 'sv::bit?)
          (equal-len args 3))
    (b* ((test (first args))
         ((unless (4vec-p test)) (hons fn args))
         (test (sv::3vec-fix test))
         ((when (eql test 0))
          (third args))
         ((when (eql test -1))
          (second args)))
      (bit?-resolve (sv::3vec-fix test) (second args) (third args) (expt 2 30))))

   ((and* (equal fn 'sv::bit?!)
          (equal-len args 3))
    (b* ((test (first args))
         ((unless (4vec-p test)) (hons fn args))
         ((when (eql test -1))
          (second args))
         ((sv::4vec test))
         ((when (eql (logand test.upper test.lower) 0))
          (third args)))
      (bit?!-resolve test (second args) (third args) (expt 2 30))))

   ((and* (or* (equal fn 'sv::bitor)
               (equal fn 'sv::bitand)
               (equal fn 'sv::bitxor))
          (equal-len args 2))
    (b* ((arg1 (first args))
         (arg2 (second args))
         ((when (and (equal fn 'sv::bitor)
                     (or (equal arg1 -1)
                         (equal arg2 -1))))
          -1)
         ((when (and (equal fn 'sv::bitand)
                     (or (equal arg1 0)
                         (equal arg2 0))))
          0)
         (arg1 (case-match arg1
                 (('sv::unfloat x) x)
                 (& arg1)))
         (arg2 (case-match arg2
                 (('sv::unfloat x) x)
                 (& arg2))))
      (hons-list fn arg1 arg2)))

   ((and* (equal fn 'sv::unfloat)
          (equal-len args 1))
    (if (and (consp (car args))
             (member-equal (caar args) '(sv::unfloat
                                         sv::bitand
                                         sv::bitnot
                                         sv::bitor
                                         sv::bitxor)))
        (car args)
      (hons fn args)))

   ((and* (equal fn 'sv::concat)
          (equal-len args 3))
    (b* ((res (hons fn args)))
      (concat-reduce res)))

   ((and* (equal fn 'sv::rsh)
          (equal-len args 2))
    (b* ((res (hons fn args)))
      (rsh-reduce res)))

   (t (hons fn args))))

(defmacro svex-apply-constant-cases (fn args)
  `(b* ((quoted (sv::4veclist-p args))
        ((when quoted)
         (case ,fn
           ,@(svex-apply-constant-cases-fn args
                                           (cons '(ID sv::4VEC-FIX$INLINE (ACL2::X)
                                                      "identity function") ;; had to
                                                 ;; change this because 4vec-fix is
                                                 ;; the only function that is inlined
                                                 (cdr
                                                  sv::*svex-op-table*))))))
     (svex-reduce-w/-env-apply-specials
      ,fn ,args)))

(define svex-reduce-w/-env-apply (fn args)
  :guard (true-listp args)
  :returns (res svex-p
                :hyp (and (FNSYM-P fn)
                          (SVEXLIST-P args))
                :hints (("Goal"
                         :expand (SVEX-P (LIST FN ARGS))
                         :in-theory (e/d () ()))))
  (let* ((fn (fnsym-fix fn)))
    (svex-apply-constant-cases fn args)))

(verify-guards svex-reduce-w/-env-apply
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d () ()))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Proofs
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defthm sv::4vec-bit?!-of-constants
   (and (equal (sv::4vec-bit?! -1 then else)
               (4vec-fix then))
        (equal (sv::4vec-bit?! 0 then else)
               (4vec-fix else))
        (equal (sv::4vec-bit?! '(0 . -1) then else)
               (4vec-fix else))
        (equal (sv::4vec-bit?! '(-1 . 0) then else)
               (4vec-fix else)))
   :hints (("goal"
            :expand ((:free (x y) (sv::4vec-bit?! 0 x y))
                     (:free (x y) (sv::4vec-bit?! -1 x y))
                     (:free (x y) (sv::4vec-bit?! '(0 . -1) x y))
                     (:free (x y) (sv::4vec-bit?! '(-1 . 0) x y)))
            :in-theory (e/d ()
                            (4vec-bit?!-when-test-is-quoted))))))

(local
 (defthm sv::4vec-bit?-of-constants
   (and (equal (sv::4vec-bit? -1 then else)
               (4vec-fix then))
        (equal (sv::4vec-bit? 0 then else)
               (4vec-fix else)))
   :hints (("goal"
            :expand ((:free (x y) (sv::4vec-bit? 0 x y))
                     (:free (x y) (sv::4vec-bit? -1 x y))
                     (:free (x y) (sv::4vec-bit? '(0 . -1) x y))
                     (:free (x y) (sv::4vec-bit? '(-1 . 0) x y)))
            :in-theory (e/d (sv::3vec-bit?)
                            ())))))

(local
 (svex-eval-lemma-tmpl
  (defthm svex-eval-opener-when-call
    (implies (and (syntaxp (and (consp fn)
                                (quotep fn)))
                  (fnsym-p fn))
             (equal (svex-eval (cons fn args) env)
                    (sv::svex-apply fn
                                    (svexlist-eval args env))))
    :hints (("goal"
             :expand (svex-eval (cons fn args) env)
             :in-theory (e/d (svex-call->fn
                              svex-var->name
                              svex-kind
                              svex-call->args)
                             ()))))))

(local
 (svex-eval-lemma-tmpl
  (defthm svex-eval-when-4vec-p
    (implies (4vec-p x)
             (equal (svex-eval x env)
                    x))
    :hints (("Goal"
             :expand ((SVEX-EVAL X ENV)
                      (4VEC-P X))
             :in-theory (e/d (SVEX-KIND
                              SV::SVEX-QUOTE->VAL)
                             ()))))))

(local
 (in-theory (disable sv::svex-apply$-is-svex-apply)))

(svex-eval-lemma-tmpl
 (defthm svex-eval-of-bit?!-resolve-correct
   (implies (sv::4vec-p test)
            (equal
             (svex-eval (bit?!-resolve test then else limit) env)
             (svex-eval `(sv::bit?! ,test ,then ,else) env)))
   :hints (("goal"
            :expand ((bit?!-resolve test then else limit)
                     (bit?!-resolve 0 then else limit)
                     (bit?!-resolve -1 then else limit)
                     (bit?!-resolve '(0 . -1)
                                    then else limit)
                     (bit?!-resolve '(-1 . 0)
                                    then else limit)
                     (:free (x y)
                            (sv::svex-apply x y)))
            :induct (bit?!-resolve test then else limit)
            :do-not-induct t
            :in-theory (e/d (bit?!-resolve)
                            ())))))


(svex-eval-lemma-tmpl
 (defthm svex-eval-of-bit?-resolve-correct
   (implies (and (sv::4vec-p test)
                 (sv::3vec-p test))
            (equal
             (svex-eval (bit?-resolve test then else limit) env)
             (svex-eval `(sv::bit? ,test ,then ,else) env)))
   :hints (("subgoal *1/11"
            :use ((:instance 4vec-concat-of-part-select-and-rsh
                             (size (calc-bit-repetition test test 1073741824))
                             (y (sv::4vec-bit? test (svex-eval then env)
                                               (svex-eval else env))))))
           ("subgoal *1/6"
            :use ((:instance 4vec-concat-of-part-select-and-rsh
                             (size (calc-bit-repetition test test 1073741824))
                             (y (sv::4vec-bit? test (svex-eval then env) (svex-eval else env))))))
           ("subgoal *1/7"
            :use ((:instance 4vec-concat-of-part-select-and-rsh
                             (size (calc-bit-repetition test test 1073741824))
                             (y (sv::4vec-bit? test (svex-eval then env) (svex-eval else env))))))
           ("subgoal *1/8"
            :use ((:instance 4vec-concat-of-part-select-and-rsh
                             (size (calc-bit-repetition test test 1073741824))
                             (y (sv::4vec-bit? test (svex-eval then env) (svex-eval else env))))))
           ("subgoal *1/9"
            :use ((:instance 4vec-concat-of-part-select-and-rsh
                             (size (calc-bit-repetition test test 1073741824))
                             (y (sv::4vec-bit? test (svex-eval then env) (svex-eval else env))))))
           ("subgoal *1/10"
            :use ((:instance 4vec-concat-of-part-select-and-rsh
                             (size (calc-bit-repetition test test 1073741824))
                             (y (sv::4vec-bit? test (svex-eval then env) (svex-eval else env))))))
           ("goal"
            :expand (
                     (bit?-resolve test then else limit)
                     (bit?-resolve 0 then else limit)
                     (bit?-resolve -1 then else limit)
                     (bit?-resolve '(0 . -1)
                                   then else limit)
                     (bit?-resolve '(-1 . 0)
                                   then else limit)
                     (:free (x y)
                            (sv::svex-apply x y)))
            :induct (bit?-resolve test then else limit)
            :do-not-induct t
            :in-theory (e/d (bit?-resolve
                             bits
                             convert-4vec-concat-to-4vec-concat$)
                            (4vec-concat-of-part-select-and-rsh
                             equal-of-4vec-concat$-with-posp-size))))))

(local
 (svex-eval-lemma-tmpl
  (defthm bit?!-resolve-is-svex-apply-when-4vec-p
    (implies (and (sv::4vec-p test)
                  (4vec-p (bit?!-resolve test then else limit)))
             (equal
              (svex-eval (bit?!-resolve test then else limit) env)
              (sv::svex-apply 'sv::bit?! (list (svex-eval test env)
                                               (svex-eval then env)
                                               (svex-eval else env)))))
    :hints (("goal"
             :use ((:instance svex-eval-of-bit?!-resolve-correct))
             :expand (
                      #|(:free (x y)
                      (sv::svex-apply x y))|#
                      (:free (x y)
                             (sv::4vec-p (cons 'SV::BIT?!  y)))
                      (:free (x y)
                             (sv::4vec-p (cons 'CONCAT  y))))

             :do-not-induct t
             :in-theory (e/d (bit?!-resolve

                              )
                             (svex-eval-of-bit?!-resolve-correct)))))))

(local
 (defthm 4VEC-BITOR-of-1
   (equal (4VEC-BITOR -1 then)
          -1)
   :hints (("Goal"
            :expand (4VEC-BITOR -1 then)
            :in-theory (e/d (SV::3VEC-BITOR) ())))))

(defthm 4vec-p-of-SVEX-EVAL$-forward-chaining-1
  (and (implies (not (consp (svex-eval$ svex env)))
                (integerp (svex-eval$ svex env))))
  :rule-classes :forward-chaining
  :hints (("Goal"
           :use ((:instance SV::RETURN-TYPE-OF-SVEX-EVAL$.VAL
                            (sv::x svex)
                            (sv::env env)))
           :in-theory (e/d (4vec-p)
                           (SV::RETURN-TYPE-OF-SVEX-EVAL$.VAL)))))

(defthm 4vec-p-of-SVEX-EVAL$-forward-chaining-2
  (implies (consp (svex-eval$ svex env))
           (and (integerp (car (svex-eval$ svex env)))
                (integerp (cdr (svex-eval$ svex env)))))
  :rule-classes :forward-chaining
  :hints (("Goal"
           :use ((:instance SV::RETURN-TYPE-OF-SVEX-EVAL$.VAL
                            (sv::x svex)
                            (sv::env env)))
           :in-theory (e/d (4vec-p)
                           (SV::RETURN-TYPE-OF-SVEX-EVAL$.VAL)))))



(svex-eval-lemma-tmpl
 (defret svex-eval-of-concat-reduce-correct
   (equal (svex-eval res env)
          (svex-eval svex env))
   :fn concat-reduce
   :otf-flg t
   :hints (("goal"
            :expand ((svex-eval svex env))
            :induct (concat-reduce svex)
            :do-not-induct t
            :in-theory (e/d (svex-apply
                             svex-kind
                             svex-call->fn
                             svex-call->args
                             svexlist-eval
                             svex-eval
                             concat-reduce
                             concat-of-conseq-partsel-pattern-p
                             3vec-fix-of-4vec-concat-reverse)
                            ((:rewrite sv::4veclist-nth-safe-out-of-bounds)
                             (:definition acl2::apply$-badgep)
                             (:linear acl2::apply$-badgep-properties . 1)
                             (:definition subsetp-equal)
                             (:definition member-equal)))))))

(svex-eval-lemma-tmpl
 (defret svex-eval-of-<fn>-correct
   (equal (svex-eval res env)
          (svex-eval svex env))
   :fn rsh-reduce
   :otf-flg t
   :hints (("goal"
            :expand ((svex-eval svex env)
                     (SVEXLIST-EVAL (CDDR (CADDR SVEX)) ENV)
                     (SVEXLIST-EVAL (CDR (CADDR SVEX)) ENV)
                     (SVEXLIST-EVAL (CDDR SVEX) ENV)
                     (SVEXLIST-EVAL (CDR SVEX) ENV)
                     (SVEXLIST-EVAL (CDDDR (CADDR SVEX)) ENV))
            :do-not-induct t
            :in-theory (e/d (svex-apply
                             svex-kind
                             svex-call->fn
                             svex-call->args
                             sv::svex-quote->val
                             svexlist-eval
                             svex-eval
                             RSH-REDUCE
                             concat-of-conseq-partsel-pattern-p
                             3vec-fix-of-4vec-concat-reverse)
                            ((:rewrite sv::4veclist-nth-safe-out-of-bounds)
                             (:definition acl2::apply$-badgep)
                             (:linear acl2::apply$-badgep-properties . 1)
                             (:definition subsetp-equal)
                             (:definition member-equal)))))))


(local
 (defthm 4vec-?/?*-of-repeated-then-else
   (implies (and (integerp then)
                 (equal then else))
            (and (equal (sv::4vec-? test then else)
                        then)
                 (equal (sv::4vec-?* test then else)
                        then)))
   :hints (("goal"
            :in-theory '((:definition sv::3vec-?)
                         (:definition sv::3vec-?*)
                         (:definition 4vec-?)
                         (:definition 4vec-?*)
                         (:definition acl2::binary-logeqv)
                         (:definition ifix)
                         (:definition logorc1)
                         (:definition synp)
                         (:executable-counterpart acl2::binary-logand)
                         (:rewrite acl2::|(equal (if a b c) x)|)
                         (:rewrite acl2::|(logior y x)|)
                         (:rewrite sv::4vec->upper-and-lower-equivalance)
                         (:rewrite 4vec->upper-and-lower-when-integerp)
                         (:rewrite sv::4vec-equal)
                         (:rewrite sv::4vec-fix-of-4vec)
                         (:rewrite integerp-implies-4vecp)
                         (:rewrite acl2::logand--1-x)
                         (:rewrite acl2::logand-x-x)
                         (:rewrite acl2::logior-0-x)
                         (:rewrite bitops::logior-x-lognot-x . 1)
                         (:rewrite acl2::logior-x-x)
                         (:rewrite acl2::logxor-x-x))))))

(svex-eval-lemma-tmpl
 (defthm svex-eval-of-svex-reduce-w/-env-apply-specials-correct
   (equal (svex-eval (svex-reduce-w/-env-apply-specials fn args) env)
          (svex-eval `(,fn . ,args) env))
   :hints (("Goal"
            :do-not-induct t
            :expand ((svexlist-eval args env)
                     (svex-eval (car args) env)
                     (svex-kind (car args))
                     (svex-call->fn (car args))
                     (:free (x y) (sv::4vec-bit? -1 x y))
                     (:free (x y) (sv::4vec-bit? 0 x y))
                     (:free (x y) (4veclist-nth-safe x y))
                     (:free (x y) (nth x y))
                     (:free (x) (sv::svex-apply 'bitand x))
                     (:free (x) (sv::svex-apply 'sv::unfloat x))
                     (:free (x) (sv::svex-apply 'sv::bitor x))
                     (:free (x) (sv::svex-apply 'sv::bitxor x))
                     (:free (x) (sv::svex-apply 'sv::bitnot x))
                     (:free (x) (sv::svex-apply 'sv::? x))
                     (:free (x) (sv::svex-apply 'sv::?* x))
                     (:free (x) (sv::svex-apply 'sv::?! x))
                     (:free (x) (sv::svex-apply 'sv::bit?! x))
                     (:free (x) (sv::svex-apply 'sv::bit? x)))
            :in-theory (e/d (svex-reduce-w/-env-apply-specials
                             ;;4vec-?
                             sv::4vec-bitmux
                             sv::4vec-1mask
                             acl2::logite
                             or*
                             svex-call->args
                             sv::4vec-bit?!
                             4vec-p
                             ;;4vec-?*
                             sv::3vec-bit?
                             sv::3vec-?*
                             ;;sv::4vec-bit?!
                             sv::4vec-?!
                             ;;sv::4vec->upper
                             sv::3vec-?
                             )
                            ((:TYPE-PRESCRIPTION 4VECLIST-NTH-SAFE)
                             (:DEFINITION ACL2::APPLY$-BADGEP)
                             (:REWRITE BITP-IMPLIES-4VECP)
                             (:TYPE-PRESCRIPTION 4VEC)
                             (:TYPE-PRESCRIPTION NATP-4VEC-LSH)

                             (:TYPE-PRESCRIPTION
                              SV::INTEGERP-OF-4VEC->LOWER)
                             (:TYPE-PRESCRIPTION
                              SV::INTEGERP-OF-4VEC->UPPER)
                             (:TYPE-PRESCRIPTION SV::4VEC-FIX$INLINE)
                             (:TYPE-PRESCRIPTION ACL2::BINARY-LOGAND))))
           (and stable-under-simplificationp
                '(:expand ((SVEX-CALL->FN (CADR ARGS))
                           (SVEX-KIND (CADR ARGS))
                           (SVEX-EVAL (CADR ARGS) ENV)
                           (:free (x) (sv::svex-apply 'sv::unfloat x))
                           
                           (:free (x y z) (sv::4vec-? x y z))
                           (:free (x y z) (sv::4vec-?* x y z))))))))

(local
 (defthm svex-eval-when-fn-is-absent
   (implies (and (fnsym-p fn)
                 (not (member fn (strip-cars sv::*svex-op-table*))))
            (equal (svex-eval (cons fn args) env)
                   '(-1 . 0)))
   :hints (("goal"
            :expand ((svex-eval (cons fn args) env)
                     (:free (x y)
                            (sv::svex-apply x y)))
            :in-theory (e/d (svex-call->fn
                             svex-kind
                             svex-call->args)
                            ())))))

(local
 (defthm svex-apply-when-fn-is-absent
   (implies (and (fnsym-p fn)
                 (not (member fn (strip-cars sv::*svex-op-table*))))
            (equal (sv::SVEX-APPLY fn args)
                   '(-1 . 0)))
   :hints (("goal"
            :expand ((sv::SVEX-APPLY fn args)
                     (:free (x y)
                            (sv::svex-apply x y)))
            :in-theory (e/d (svex-call->fn
                             svex-kind
                             svex-call->args)
                            ())))))

(svex-eval-lemma-tmpl
 (defthm svex-eval-svex-reduce-w/-env-apply-correct
   (implies (and (force (fnsym-p fn)))
            (equal (svex-eval (svex-reduce-w/-env-apply fn args) env)
                   (svex-eval `(,fn . ,args) env)))
   :hints (("goal"
            :do-not-induct t
            :expand ((:free (x y)
                            (sv::svex-apply x y)))
            :in-theory (e/d (svex-reduce-w/-env-apply)
                            (4VEC-OVERRIDE-WHEN-INTEGERP))))))

#|(svex-eval-lemma-tmpl
 (defthm svex-eval-svex-reduce-w/-env-apply-correct-when-4vec-p
   (implies (and (4vec-p (svex-reduce-w/-env-apply fn args))
                 (force (fnsym-p fn)))
            (equal (svex-reduce-w/-env-apply fn args)
                   (svex-eval `(,fn . ,args) (RP-EVLT ENV-TERM A))))
   :hints (("goal"
            :do-not-induct t
            :use ((:instance svex-eval-svex-reduce-w/-env-apply-correct
                             (env (RP-EVLT ENV-TERM A))))
            :in-theory (e/d ()
                            (svex-eval-svex-reduce-w/-env-apply-correct))))))|#

;;;;;;;;
