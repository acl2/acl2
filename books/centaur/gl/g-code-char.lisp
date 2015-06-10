; GL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2008-2013 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "GL")
(include-book "g-if")
(include-book "g-primitives-help")
(include-book "eval-g-base")
(include-book "symbolic-arithmetic")
(include-book "g-lessthan")

(local (include-book "eval-g-base-help"))
(local (include-book "hyp-fix"))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "tools/trivial-ancestors-check" :dir :system))
(local (acl2::use-trivial-ancestors-check))

;; (defaxiom completion-of-code-char
;;   (equal (code-char x)
;;          (if (and (integerp x)
;;                   (>= x 0)
;;                   (< x 256))
;;              (code-char x)
;;            (code-char 0)))
;;   :rule-classes nil)

(defun g-code-char-concrete (x)
  (declare (xargs :guard (or (atom x)
                             (and (not (g-number-p x))
                                  (not (g-ite-p x))))))
  (cond ((atom x)
         (ec-call (code-char x)))
        ((g-boolean-p x)
         (code-char 0))
        ((g-concrete-p x)
         (ec-call (code-char (g-concrete->obj x))))
        ((g-apply-p x)
         (g-apply 'code-char (list x)))
        ((g-var-p x)
         (g-apply 'code-char (list x)))
        (t ;; cons
         (code-char 0))))

(defthm deps-of-g-code-char-concrete
  (implies (not (gobj-depends-on k p x))
           (not (gobj-depends-on k p (g-code-char-concrete x)))))

(local
 (progn
   ;; (defthm gobjectp-characterp
   ;;   (implies (characterp x)
   ;;            (gobjectp x))
   ;;   :hints(("Goal" :in-theory
   ;;           (enable gobjectp gobject-hierarchy))))

   ;; (defthm gobjectp-g-code-char-concrete
   ;;   (gobjectp (g-code-char-concrete x)))

   (defthm code-char-booleanp
     (implies (booleanp x)
              (equal (code-char x)
                     (code-char 0)))
     :hints (("goal" :use completion-of-code-char)))

   (defthm general-concrete-obj-of-atom
     (implies (and (not (consp x))
                   (not (g-keyword-symbolp x)))
              (equal (general-concrete-obj x) x))
     :hints(("Goal" :in-theory (enable general-concrete-obj))))

   ;; (defthm gobjectp-not-g-keyword-symbolp
   ;;   (implies (gobjectp x)
   ;;            (not (g-keyword-symbolp x)))
   ;;   :hints(("Goal" :in-theory (enable gobjectp gobject-hierarchy
   ;;                                     g-keyword-symbolp))))

   (defthm general-concerete-obj-of-g-concrete-p
     (implies (g-concrete-p x)
              (equal (general-concrete-obj x)
                     (g-concrete->obj x)))
     :hints(("Goal" :in-theory (enable general-concrete-obj))))

   (defthm consp-when-general-concretep
     (implies (and (consp x)
                   (not (g-concrete-p x))
                   (general-concretep x))
              (consp (general-concrete-obj x)))
     :hints(("Goal" :in-theory (enable general-concrete-obj))))

   (defthm code-char-of-consp
     (implies (consp x)
              (equal (code-char x) (code-char 0)))
     :hints (("goal" :use completion-of-code-char)))

   ;; (defthm g-number-p-gobj-fix
   ;;   (implies (not (g-number-p x))
   ;;            (not (g-number-p (gobj-fix x))))
   ;;   :hints(("Goal" :in-theory (enable gobj-fix))))

   ;; (defthm g-ite-p-gobj-fix
   ;;   (implies (not (g-ite-p x))
   ;;            (not (g-ite-p (gobj-fix x))))
   ;;   :hints(("Goal" :in-theory (enable gobj-fix))))

   (defthm g-code-char-concrete-correct
     (implies (and (not (g-number-p x))
                   (not (g-ite-p x)))
              (equal (eval-g-base (g-code-char-concrete x) env)
                     (code-char (eval-g-base x env))))
     :hints(("Goal" :in-theory (e/d (general-numberp
                                     general-booleanp
                                     general-consp
                                     eval-g-base
                                     eval-g-base-list
                                     g-keyword-symbolp)
                                    ((code-char)
                                     eval-g-base-alt-def))
             :do-not-induct t)
            (and stable-under-simplificationp
                 '(:expand ((:with eval-g-base (eval-g-base x env)))))))



   ;; (defthm bfr-p-nth
   ;;   (implies (bfr-listp x)
   ;;            (bfr-p (nth n x))))

   ;; (defthm true-listp-when-bfr-listp
   ;;   (implies (bfr-listp x)
   ;;            (True-listp x))
   ;;   :hints(("Goal" :in-theory (enable bfr-listp))))
   ))

(local (defthm floor-1
         (implies (integerp n)
                  (equal (floor n 1) n))
         :hints(("Goal" :in-theory (enable floor)))))

(define code-char-s (n x acc hyp)
  :guard (and (natp n)
              (true-listp x)
              (< n 9)
              (natp acc)
              (<= acc (- 256 (ash 1 n))))
  :verify-guards nil
  (b* ((hyp (lbfr-hyp-fix hyp)))
    (if (zp n)
        (gret (code-char acc))
      (g-if-mbe (gret (mk-g-boolean (nth (1- n) x)))
                (code-char-s (1- n) x (+ (ash 1 (1- n)) acc) hyp)
                (code-char-s (1- n) x acc hyp))))
  ///
  (def-hyp-congruence code-char-s)
  (verify-guards code-char-s
    :hints (("goal" :in-theory (enable g-if-fn))
            (and stable-under-simplificationp
                 '(:in-theory (enable ash expt)))))

  (local

   (defthm pbfr-depends-on-nth
     (implies (not (pbfr-list-depends-on k p x))
              (not (pbfr-depends-on k p (nth n x))))))

  (defthm deps-of-code-char-s
    (implies (not (pbfr-list-depends-on k p x))
             (not (gobj-depends-on k p (mv-nth 0 (code-char-s n x acc hyp)))))
    :hints (("goal" :induct (code-char-s n x acc hyp)
             :in-theory (disable (:d code-char-s))
             :expand ((code-char-s n x acc hyp))))))

;; (local (defun first-n (n x)
;;          (if (zp n)
;;              nil
;;            (cons (car x) (first-n (1- n) (cdr X))))))

(local
 (progn
   (defun first-n (n x)
     (if (zp n)
         nil
       (append (first-n (1- n) x) (list (nth (1- n) X)))))

   (Defthm len-append
     (equal (len (append a b))
            (+ (len a) (len b))))

   (defthm len-first-n
     (equal (len (first-n n x))
            (nfix n)))

   (defthm bfr-eval-list-append
     (equal (bfr-eval-list (append a b) env)
            (append (bfr-eval-list a env)
                    (bfr-eval-list b env))))

   ;; (defthm v2n-append
   ;;   (equal (v2n (append a b))
   ;;          (+ (v2n a)
   ;;             (* (v2n b) (expt 2 (len a)))))
   ;;   :hints(("Goal" :in-theory (enable v2n ash))))
   (defthm bfr-list->u-of-append
     (equal (bfr-list->u (append a b) env)
            (+ (bfr-list->u a env)
               (* (bfr-list->u b env) (expt 2 (len a)))))
     :hints(("Goal" :in-theory (e/d* (acl2::logapp** logcons
                                                     acl2::bool->bit)
                                     (logapp)))))

;; (defthm bfr-eval-list-first-n
;;   (implies (not (zp n))
;;            (equal (bfr-list->u (first-n n x) env)
;;                   (+ (if (bfr-eval (nth (1- n) x) env) (expt 2 (1- n)) 0)
;;                      (bfr-list->u (first-n (1- n) x) env))))
;;   :hints (("goal" :induct (first-n n x)
;;            :in-theory (e/d (ash) ((:definition first-n)))
;;            :expand ((first-n n x)
;;                     (:free (a b) (v2n (cons a b)))
;;                     (:free (x) (first-n 0 x))))))

   (defthm floor-1
     (implies (integerp n)
              (equal (floor n 1) n))
     :hints(("Goal" :in-theory (enable floor))))

   (defthm len-bfr-eval-list
     (equal (len (Bfr-eval-list x env))
            (len x)))

   (defthm code-char-s-correct1
     (implies (and (< (+ acc (bfr-list->u (first-n n x) (car env))) 256)
                   (integerp acc)
                   (bfr-hyp-eval hyp (car env)))
              (equal (eval-g-base (mv-nth 0 (code-char-s n x acc hyp)) env)
                     (code-char (+ acc (bfr-list->u (first-n n x) (car env))))))
     :hints (("goal" :induct (code-char-s n x acc hyp)
              :expand ((code-char-s n x acc hyp)
                       (code-char-s 0 x acc hyp))
              :in-theory (e/d (ash (:i code-char-s)) (floor)))))

   (defthm bfr-list->s-when-<=-0
     (implies (<= 0 (bfr-list->s x env))
              (equal (bfr-list->s x env) (bfr-list->u x env)))
     :hints(("Goal" :in-theory (enable scdr s-endp))))



   (defthm bfr-eval-list-nth
     (equal (nth n (bfr-eval-list x env))
            (bfr-eval (nth n x) env)))

   (defthm bfr-eval-first-n
     (equal (bfr-eval-list (first-n n x) env)
            (first-n n (bfr-eval-list x env))))

   (defun first-n-alt (n x)
     (if (zp n)
         nil
       (cons (car x)
             (first-n-alt (1- n) (cdr x)))))

   (defthmd first-n-is-first-n-alt
     (equal (first-n n x)
            (first-n-alt n x)))

   (defthm bfr-list->u-of-first-n
     (implies (< (bfr-list->u x env) (expt 2 (nfix n)))
              (equal (bfr-list->u (first-n n x) env)
                     (bfr-list->u x env)))
     :hints(("Goal" :in-theory (enable first-n-is-first-n-alt
                                       logcons acl2::bool->bit
                                       expt))))

   ;; (defthm v2n-first-n
   ;;   (implies (< (v2n x) (expt 2 (nfix n)))
   ;;            (equal (v2n (first-n n x))
   ;;                   (v2n x)))
   ;;   :hints(("Goal" :in-theory (enable v2n ash first-n-is-first-n-alt)
   ;;           :induct (first-n-alt n x)
   ;;           :expand ( ;; (v2n x)
   ;;                    (:free (a b) (v2n (cons a b)))))))

   (defthm code-char-s-correct
     (implies (and (bfr-hyp-eval hyp (car env))
                   (<= 0 (bfr-list->s x (car env)))
                   (< (bfr-list->s x (car env)) 256))
              (equal (eval-g-base (mv-nth 0 (code-char-s 8 x 0 hyp)) env)
                     (code-char (bfr-list->s x (car env)))))
     :hints(("Goal" :in-theory (disable code-char-s))))))


;; (defun g-code-char-of-integer (x hyp clk)
;;   (declare (xargs :guard (and (gobjectp x) (g-number-p x)
;;                               (natp clk) (bfr-p hyp))))
;;   (g-if (glr < x 0 hyp clk)
;;         nil
;;         (glr < x 256 hyp clk))

(define g-code-char-of-number (x hyp clk config bvar-db state)
  :guard (and (consp x)
              (g-number-p x)
              (glcp-config-p config)
              (natp clk))
  :verify-guards nil
  ;; :guard-hints(("Goal" :in-theory
  ;;               (e/d (g-if-fn) (code-char-s))))
  (replace-g-ifs
   (b* ((hyp (lbfr-hyp-fix hyp))
        ((mv xrn xrd xin xid)
         (break-g-number (g-number->num x))))
     (if (equal xrd '(t))
         (g-if (g-if (gret (mk-g-boolean (bfr-or (bfr-=-ss xin nil)
                                                 (bfr-=-uu xid nil))))
                     (g-if (glr < x 0 hyp clk config bvar-db state)
                           (gret nil)
                           (glr < x 256 hyp clk config bvar-db state))
                     (gret nil))
               (code-char-s 8 (list-fix xrn) 0 hyp)
               (gret (code-char 0)))
       (gret (g-apply 'code-char (list x))))))
  ///
  (def-hyp-congruence g-code-char-of-number)
  (verify-guards g-code-char-of-number
    :hints(("Goal" :in-theory
            (e/d* (g-if-fn)
                  (not code-char-s
                   equal-of-booleans-rewrite
                   set::double-containment
                   g-code-char-of-number
                   mv-nth-cons-meta
                   bfr-assume-correct
                   true-listp len
                   (:rules-of-class :forward-chaining :here)
                   (:rules-of-class :type-prescription :here))))))

  (defthm deps-of-g-code-char-of-number
    (implies (and (not (gobj-depends-on k p x))
                  (g-number-p x))
             (not (gobj-depends-on k p (mv-nth 0 (g-code-char-of-number x hyp clk config
                                                                        bvar-db state)))))
    :hints (("goal" :in-theory (e/d ((force))
                                    (gobj-depends-on
                                     code-char-s))))))


;; (defun g-code-char-of-number (x hyp clk)
;;   (declare (xargs :guard (and (gobjectp x)
;;                               (g-number-p x)
;;                               (natp clk)
;;                               (bfr-p hyp))
;;                   :guard-hints(("Goal" :in-theory
;;                                 (disable code-char-s)))))
;;   (mv-let (xrn xrd xin xid)
;;     (break-g-number (g-number->num x))
;;     (if (equal xrd '(t))
;;         (g-if (mk-g-boolean (bfr-or (bfr-=-ss xin nil)
;;                                     (bfr-=-uu xid nil)))
;;               (g-if (glr < x 0 hyp clk)
;;                     (code-char 0)
;;                     (g-if (glr < x 256 hyp clk)
;;                           (code-char-s 8 xrn 0 hyp)
;;                           (code-char 0)))
;;               (code-char 0))
;;       (g-apply 'code-char (list x)))))



(local
 (progn
   (defthm code-char-when->=-256
     (implies (<= 256 x)
              (equal (code-char x) (code-char 0)))
     :hints (("goal" :use completion-of-code-char)))

   (defthm code-char-when-<-0
     (implies (< x 0)
              (equal (code-char x) (code-char 0)))
     :hints (("goal" :use completion-of-code-char)))

   (defthm integerp-complex
     (equal (integerp (complex a b))
            (and (or (integerp a) (not (rationalp a)))
                 (or (equal b 0) (not (rationalp b))))))

   (defthm equal-recip-0
     (implies (and (acl2-numberp x)
                   (not (equal x 0)))
              (not (equal (/ x) 0))))

   (defthm not-integerp-when-imag-parts-nonzero
     (implies (and (not (equal (bfr-list->s
                                     (mv-nth 2 (break-g-number (g-number->num x)))
                                     (car env))
                               0))
                   (not (equal (bfr-list->u
                                     (mv-nth 3 (break-g-number (g-number->num x)))
                                     (car env))
                               0))
                   (g-number-p x))
              (not (integerp (eval-g-base x env))))
     :hints(("Goal" :in-theory
             (e/d (eval-g-base) (eval-g-base-alt-def))
             :do-not-induct t)))

   (defthm code-char-when-non-integer
     (implies (not (integerp x))
              (equal (code-char x) (code-char 0)))
     :hints (("goal" :use completion-of-code-char)))

   (encapsulate
     nil
     (set-ignore-ok t)
     ;; (local (DEFTHM
     ;;          G-IF-FN-CORRECT-FOR-EVAL-G-BASE-casesplit
     ;;          (IMPLIES
     ;;           (case-split (BFR-HYP-EVAL HYP (CAR ENV)))
     ;;           (EQUAL (EVAL-G-BASE (MV-NTH 0 (G-IF-FN TEST THEN ELSE HYP))
     ;;                               ENV)
     ;;                  (IF (EVAL-G-BASE TEST ENV)
     ;;                      (EVAL-G-BASE THEN ENV)
     ;;                      (EVAL-G-BASE ELSE ENV))))))

     ;; (local (defthm bfr-list->u-when-bfr-list->s
     ;;          (implies (equal (bfr-list->s n env) 0)
     ;;                   (equal (bfr-list->u n env) 0))
     ;;          :hints(("Goal" :in-theory (enable bfr-list->s bfr-list->u s-endp scdr)
     ;;                  :induct (len n)))))


     (defthm g-code-char-of-number-correct
       (implies (and (bfr-hyp-eval hyp (car env))
                     (g-number-p x))
                (equal (eval-g-base (mv-nth 0 (g-code-char-of-number x hyp clk config
                                                                     bvar-db state)) env)
                       (code-char (eval-g-base x env))))
       :hints(("Goal" :in-theory (e/d (eval-g-base
                                       eval-g-base-list
                                       g-code-char-of-number)
                                      (code-char-s
                                       equal-of-booleans-rewrite
                                       code-char-s-correct1
                                       code-char-s-correct
                                       bfr-eval-list
                                       bfr-list->s-when-<=-0
                                       eval-g-base-alt-def))
               :do-not-induct t
               :expand ((:with eval-g-base (eval-g-base x env)))
               :do-not '(generalize fertilize eliminate-destructors))
              (and stable-under-simplificationp
                   (let ((lit (car (last clause))))
                     (case-match lit
                       (('equal ('eval-g-base
                                 ('mv-nth ''0 ('code-char-s
                                               & x & hyp))
                                 env)
                                . &)
                        (prog2$ (cw "using code-char-s-correct~%")
                                `(:use ((:instance code-char-s-correct
                                         (hyp ,hyp)
                                         (env ,env)
                                         (x ,x))))))))))))))


(def-g-fn code-char
  `(cond ((atom x) (gret (g-code-char-concrete x)))
         ((g-number-p x) (g-code-char-of-number x hyp clk config bvar-db state))
         ((g-ite-p x)
          (if (zp clk)
              (gret (g-apply 'code-char (gl-list x)))
            (g-if (gret (g-ite->test x))
                  (,gfn (g-ite->then x) hyp clk config bvar-db state)
                  (,gfn (g-ite->else x) hyp clk config bvar-db state))))
         (t (gret (g-code-char-concrete x)))))

;;(def-gobjectp-thm code-char)

(verify-g-guards code-char
                 :hints `(("goal" :in-theory (Disable ,gfn))))

(def-gobj-dependency-thm code-char
  :hints `(("goal" :induct ,gcall
            :expand (,gcall)
            :in-theory (disable (:d ,gfn) gobj-depends-on
                                g-code-char-of-number))))


(def-g-correct-thm code-char eval-g-base
  :hints `(("goal" :in-theory (e/d ()
                                   (g-code-char-concrete
                                    g-code-char-of-number
                                    eval-g-base-alt-def
                                    (:definition ,gfn)))
            :expand (,gcall)
            :induct ,gcall)
           (and stable-under-simplificationp
                '(:expand ((:with eval-g-base (eval-g-base x env))
                           (:with eval-g-base (eval-g-base nil env)))))))
