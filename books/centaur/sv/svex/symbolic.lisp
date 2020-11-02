; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2014-2015 Centaur Technology
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

(in-package "SV")
(include-book "eval")
(include-book "a4vec-ops")
(include-book "rewrite")
(include-book "lists")
(include-book "env-ops")
(include-book "centaur/gl/gl-mbe" :dir :system)
(include-book "centaur/gl/def-gl-rewrite" :dir :system)
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "std/alists/alist-keys" :dir :System))
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))
(local (include-book "clause-processors/just-expand" :dir :system))
(local (std::add-default-post-define-hook :fix))

(local (std::deflist svarlist-p (x)
         (svar-p x)
         :true-listp t
         :elementp-of-nil nil))

(local (defthm true-listp-nthcdr
         (implies (true-listp x)
                  (true-listp (nthcdr n x)))
         :hints(("Goal" :in-theory (e/d (nthcdr)
                                        (acl2::cdr-nthcdr))
                 :induct (nthcdr n x)))
         :rule-classes :type-prescription))

(local (defthm nthcdr-of-append-equal-len
         (implies (equal (nfix n) (len x))
                  (equal (nthcdr n (append x y))
                         y))
         :hints(("Goal" :in-theory (e/d (nthcdr)
                                        (acl2::cdr-nthcdr))
                 :induct (nthcdr n x)))))

(local (defthm take-of-append-equal-len
         (implies (equal (nfix n) (len x))
                  (equal (take n (append x y))
                         (list-fix x)))
         :hints(("Goal" :in-theory (e/d (acl2::take))
                 :induct (nthcdr n x)))))

(local (in-theory (disable double-containment)))

(local (defthm 3vec-p-of-4vec-mask
         (implies (3vec-p x)
                  (3vec-p (4vec-mask mask x)))
         :hints(("Goal" :in-theory (enable 4vec-mask 3vec-p))
                (acl2::logbitp-reasoning))))

(local (defthm true-listp-of-scdr
         (implies (true-listp x)
                  (true-listp (gl::scdr x)))
         :hints(("Goal" :in-theory (enable gl::scdr)))
         :rule-classes :type-prescription))

(local (in-theory (disable gl::s-endp-of-bfr-scons
                           aig-list->s)))



(local (defthm aig-list->s-open-quote
         (implies (syntaxp (quotep x))
                  (equal (aig-list->s x env)
                         (B* (((MV FIRST REST GL::END)
                               (GL::FIRST/REST/END X)))
                           (IF GL::END
                               (GL::BOOL->SIGN (AIG-EVAL FIRST ENV))
                               (BITOPS::LOGCONS (BOOL->BIT (AIG-EVAL FIRST ENV))
                                                (AIG-LIST->S REST ENV))))))
         :hints(("Goal" :in-theory (enable aig-list->s)))))


(local (defthm aig-list->s-of-bfr-snorm
         (equal (aig-list->s (gl::bfr-snorm x) env)
                (aig-list->s x env))
         :hints(("Goal" :in-theory (enable aig-list->s gl::bfr-snorm)))))

(local (defthm aig-list->s-of-bfr-scons
         (equal (aig-list->s (gl::bfr-scons a b) env)
                (bitops::logcons (bool->bit (aig-eval a env))
                                 (aig-list->s b env)))
         :hints(("Goal" :expand ((aig-list->s (gl::bfr-scons a b) env)
                                 (aig-list->s b env))
                 :in-theory (enable gl::s-endp-of-bfr-scons)
                 :do-not-induct t))))




(defxdoc bit-blasting
  :parents (expressions)
  :short "We implement an efficient translation from @(see svex) expressions
into @(see acl2::aig)s, to support symbolic simulation with @(see acl2::gl).")

(local (xdoc::set-default-parents bit-blasting))



(defalist svex-a4vec-env
  :key-type svar
  :val-type a4vec)

(define svex-a4vec-env-eval ((x svex-a4vec-env-p) env)
  :returns (xx svex-env-p)
  :measure (len (svex-a4vec-env-fix x))
  (b* ((x (svex-a4vec-env-fix x)))
    (if (atom x)
        nil
      (cons (cons (svar-fix (caar x))
                  (a4vec-eval (cdar x) env))
            (svex-a4vec-env-eval (cdr x) env))))
  ///
  (defret alist-keys-of-svex-a4vec-env-eval
    (equal (alist-keys xx)
           (alist-keys (svex-a4vec-env-fix x)))
    :hints(("Goal" :in-theory (enable svex-a4vec-env-fix alist-keys)))))




(define a4veclist-nth ((n natp) (x a4veclist-p))
  :returns (elt a4vec-p)
  :guard-hints (("goal" :in-theory (enable nth a4veclist-p)))
  (mbe :logic (if (< (nfix n) (len x))
                  (a4vec-fix (nth n x))
                (a4vec-x))
       :exec (or (nth n x) (a4vec-x)))
  ///
  (defthm a4veclist-nth-out-of-bounds
    (implies (<= (len x) (nfix n))
             (equal (a4veclist-nth n x) (a4vec-x))))
  (defthm a4veclist-nth-in-of-bounds
    (implies (< (nfix n) (len x))
             (equal (a4veclist-nth n x) (a4vec-fix (nth n x))))))

(define svexlist-nth ((n natp) (x svexlist-p))
  :returns (elt svex-p)
  :guard-hints (("goal" :in-theory (enable nth svexlist-p)))
  (mbe :logic (if (< (nfix n) (len x))
                  (svex-fix (nth n x))
                (svex-x))
       :exec (or (nth n x) (svex-x)))
  ///
  (defthm svexlist-nth-out-of-bounds
    (implies (<= (len x) (nfix n))
             (equal (svexlist-nth n x) (svex-x))))
  (defthm svexlist-nth-in-of-bounds
    (implies (< (nfix n) (len x))
             (equal (svexlist-nth n x) (svex-fix (nth n x))))))

(local (defthm nth-of-svexlist-eval
         (equal (nth n (svexlist-eval x env))
                (and (< (nfix n) (len x))
                     (svex-eval (nth n x) env)))
         :hints(("Goal" :in-theory (enable nth svexlist-eval)
                 :induct (nth n x)))))

(local (defthm nth-of-a4veclist-eval
         (equal (nth n (a4veclist-eval x env))
                (and (< (nfix n) (len x))
                     (a4vec-eval (nth n x) env)))
         :hints(("Goal" :in-theory (enable nth a4veclist-eval)
                 :induct (nth n x)))))

(define maybe-a3vec-fix ((v (a4vec-p v)) (x svex-p))
  :returns (vv a4vec-p)
  (if (3valued-syntaxp (svex-fix x))
      (a4vec-fix v)
    (a3vec-fix v))
  ///
  (local (defthm nth-under-iff-when-a4veclist-p
           (implies (a4veclist-p x)
                    (iff (nth n x)
                         (< (nfix n) (len x))))
           :hints(("Goal" :in-theory (enable a4veclist-p nth)))))

  (local (defthm nth-out-of-bounds
           (implies (<= (len x) (nfix n))
                    (not (nth n x)))
           :hints(("Goal" :in-theory (enable nth)))))

  (defthm maybe-a3vec-fix-when-implies
    (implies (case-split (implies (3valued-syntaxp x)
                                  (3vec-p (a4vec-eval v env))))
             (equal (a4vec-eval (maybe-a3vec-fix v x) env)
                    (3vec-fix (a4vec-eval v env)))))

  (defthm maybe-a3vec-fix-of-nths
    (implies (equal (a4veclist-eval vals env)
                    (svexlist-eval x (svex-a4vec-env-eval a4env env)))
             (equal (a4vec-eval (maybe-a3vec-fix (nth n vals) (nth n x)) env)
                    (3vec-fix (a4vec-eval (nth n vals) env))))
    :hints(("Goal" :in-theory (e/d (a4veclist-nth)
                                   (nth-of-svexlist-eval)
                                   (nth-of-a4veclist-eval))
            :use ((:instance nth-of-svexlist-eval
                   (env (svex-a4vec-env-eval a4env env)))
                  (:instance nth-of-a4veclist-eval)))))

  (defthm maybe-a3vec-fix-of-a3vec
    (implies (a4vec-syntactic-3vec-p v)
             (equal (maybe-a3vec-fix v x)
                    (a4vec-fix v)))
    :hints(("Goal" :in-theory (enable a3vec-fix)))))










;; (define 4vmask-nth ((n natp) (x 4vmasklist-p))
;;   :returns (mask 4vmask-p :rule-classes (:rewrite :type-prescription))
;;   (b* ((x (4vmasklist-fix x)))
;;     (if (< (lnfix n) (len x))
;;         (4vmask-fix (nth n x))
;;       -1)))


;; (define maybe-a4vec-fix ((v (or (a4vec-p v) (not v))))
;;   :returns (vv a4vec-p)
;;   (if v (a4vec-fix v) (a4vec-x)))

(defconst *svex-aig-op-table*
  ;; fn name, non-3vec-fixing function, args (with notation for 3vec-fixed ones and masks)
  '((id        a4vec-fix            (x)                         "identity function")
    (bitsel    a4vec-bit-extract    (index x)                   "bit select")
    (unfloat   a4vec-fix            ((3v x))                    "change Z bits to Xes")
    (bitnot    a3vec-bitnot         ((3v x))                    "bitwise negation")
    (onp       a4vec-onset          (x)                         "bitwise onset")
    (offp      a4vec-offset         (x)                         "bitwise offset")
    (bitand    a3vec-bitand         ((3v x) (3v y))             "bitwise AND")
    (bitor     a3vec-bitor          ((3v x) (3v y))             "bitwise OR")
    (bitxor    a3vec-bitxor         ((3v x) (3v y))             "bitwise XOR")
    (res       a4vec-res            (x y)                       "resolve (short together)")
    (resand    a4vec-resand         (x y)                       "resolve wired AND")
    (resor     a4vec-resor          (x y)                       "resolve wired OR")
    (override  a4vec-override       (x y)                       "resolve different strengths")
    (uand      a3vec-reduction-and  ((3v x))                    "unary (reduction) AND")
    (uor       a3vec-reduction-or   ((3v x))                    "unary (reduction) OR")
    (uxor      a4vec-parity         (x)                         "reduction XOR, i.e. parity")
    (zerox     a4vec-zero-ext       (width x (mask m))          "zero extend")
    (signx     a4vec-sign-ext       (width x (mask m))          "sign extend")
    (concat    a4vec-concat         (width x y (mask m))        "concatenate at a given bit width")
    (partsel   a4vec-part-select    (lsb width in (mask m))     "part select")
    (partinst  a4vec-part-install   (lsb width in val (mask m)) "part install")
    (blkrev    a4vec-rev-blocks     (width blksz x)             "reverse block order")
    (rsh       a4vec-rsh            (shift x (mask m))          "right shift")
    (lsh       a4vec-lsh            (shift x (mask m))          "left shift")
    (+         a4vec-plus           (x y)                       "addition")
    (b-        a4vec-minus          (x y)                       "subtraction")
    (u-        a4vec-uminus         (x)                         "unary minus")
    (xdet      a4vec-xdet           (x)                         "x detect")
    (countones a4vec-countones      (x)                         "count of set bits")
    (onehot    a4vec-onehot         (x)                         "one-hot check")
    (onehot0   a4vec-onehot0        (x)                         "one-hot check (zero-hot allowed)")
    (*         a4vec-times          (x y)                       "multiplication")
    (/         a4vec-quotient       (x y)                       "division")
    (%         a4vec-remainder      (x y)                       "modulus")
    (<         a4vec-<              (x y)                       "less than")
    (clog2     a4vec-clog2          (x)                         "ceiling of log2")
    (pow       a4vec-pow            (x y)                       "exponentiation")
    (==        a3vec-==             ((3v x) (3v y))             "equality")
    (===       a4vec-===            (x y)                       "case equality")
    (==?       a4vec-wildeq         (x y)                       "wildcard equality")
    (safer-==? a4vec-wildeq-safe    (x y)                       "wildcard equality (monotonic version)")
    (==??      a4vec-symwildeq      (x y)                       "symmetric wildcard equality")
    (?         a3vec-?              ((3v test) (3vp then) (3vp else)) "if-then-else")
    (?*        a3vec-?*             ((3v test) (3vp then) (3vp else)) "if-then-else")
    (bit?      a3vec-bit?           ((3v test) (3vp then) (3vp else)) "bitwise if-then-else")
    (bit?!     a4vec-bit?!          ((3v test) (3vp then) (3vp else)) "bitwise if-then-else")))

#||
(loop for lst in sv::*svex-aig-op-table* do
      (let ((fn (cadr lst)))
        (unless (eq fn 'sv::a4vec-fix) (profile-fn fn))))
||#


(defun svex-apply-aig-collect-args (n restargs argsvar svvar maskvar ;; argmasks-var
                                      )
  (let* ((n (nfix n)))
    (if (atom restargs)
        nil
      (append (if (consp (car restargs))
                  (case (caar restargs)
                    (3v
                     `((maybe-a3vec-fix ;; (a4vec-mask (4vmask-nth ,n ,argmasks-var)
                        (a4veclist-nth ,n ,argsvar)
                        (svexlist-nth ,n ,svvar))))
                    (3vp
                     `(;; (a4vec-mask (4vmask-nth ,n ,argmasks-var)
                       (a4veclist-nth ,n ,argsvar)
                       (3valued-syntaxp (svexlist-nth ,n ,svvar))))
                    (mask
                     `(,maskvar))
                    (t (prog2$
                        (er hard? 'svex-apply-aig-collect-args "bad formal expr")
                        `((a4veclist-nth ,n ,argsvar)))))
                `((a4veclist-nth ,n ,argsvar)))
              (svex-apply-aig-collect-args (+ 1 n) (cdr restargs) argsvar svvar maskvar ;; argmasks-var
                                           )))))


;; (defun svex-apply-aig-uses-argmasks (args)
;;   (if (atom args)
;;       nil
;;     (or (and (consp (car args))
;;              (or (eq (caar args) '3v)
;;                  (eq (caar args) '3vp)))
;;         (svex-apply-aig-uses-argmasks (cdr args)))))

(defun svex-apply-aig-cases-fn (argsvar svvar maskvar optable)
  (b* (((when (atom optable)) '((otherwise (a4vec-x))))
       ((list sym fn args) (car optable))
       (acc-args (svex-apply-aig-collect-args 0 args argsvar svvar maskvar ;; 'tmp-argmasks
                                              ))
       (call `(,fn . ,acc-args))
       (full ;; (if (svex-apply-aig-uses-argmasks args)
             ;;     `(let ((tmp-argmasks (svex-argmasks ,maskvar ',sym ,svvar)))
             ;;        ,call)
               call))
    (cons `(,sym ,full)
          (svex-apply-aig-cases-fn argsvar svvar maskvar (cdr optable)))))

(defmacro svex-apply-aig-cases (fn args svex mask)
  `(case ,fn
     . ,(svex-apply-aig-cases-fn args svex mask *svex-aig-op-table*)))


(defthm svex-p-when-nth
  (implies (and (svexlist-p x)
                (nth n x))
           (svex-p (nth n x)))
  :hints(("Goal" :in-theory (enable nth svexlist-p))))

(defthm a4vec-p-when-nth
  (implies (and (a4veclist-p x)
                (nth n x))
           (a4vec-p (nth n x)))
  :hints(("Goal" :in-theory (enable nth svexlist-p))))

;; (defthm a4vec-eval-of-maybe-a4vec-fix-nth-out-of-bounds
;;   (implies (<= (len x) (nfix n))
;;            (equal (a4vec-eval (maybe-a4vec-fix (nth n x)) env)
;;                   (4vec-x)))
;;   :hints(("Goal" :in-theory (enable maybe-a4vec-fix nth))))


(local (in-theory (disable nth)))




(local (defthm 4vec-bit?!-of-3vec-fix
         (equal (4vec-bit?! (3vec-fix test) then else)
                (4vec-bit?! test then else))
         :hints(("Goal" :in-theory (enable 4vec-bit?! 3vec-fix)))))




(define svex-apply-aig ((fn fnsym-p) (args a4veclist-p) (terms svexlist-p) (mask 4vmask-p))
  :prepwork ((local (Defthm 4veclist-nth-safe-of-a4veclist-eval
                      (equal (a4vec-eval (a4veclist-nth n x) aigenv)
                             (4veclist-nth-safe n (a4veclist-eval x aigenv)))
                      :hints(("Goal" :in-theory (enable a4veclist-eval a4veclist-nth 4veclist-nth-safe)))))
             (local (defun ind (n vals x)
                      (if (zp n)
                          (list vals x)
                        (ind (1- n) (cdr vals) (cdr x)))))
             (local (defthm 3vec-p-when-3valued-syntaxp-nth
                      (implies (and (EQUAL (A4VECLIST-EVAL VALS AIGENV)
                                           (SVEXLIST-EVAL X (SVEX-A4VEC-ENV-EVAL A4ENV AIGENV)))
                                    (3valued-syntaxp (svexlist-nth n x)))
                               (3vec-p (a4vec-eval (nth n vals) aigenv)))
                      :hints(("Goal" :in-theory (enable a4veclist-eval
                                                        svexlist-eval
                                                        svexlist-nth
                                                        nth)
                              :induct (ind n vals x)
                              :expand ((a4veclist-eval vals aigenv)
                                       (:free (env) (svexlist-eval x env))))
                             (and stable-under-simplificationp
                                  '(:use ((:instance 3vec-p-of-eval-when-3valued-syntaxp
                                           (x (car x))
                                           (env (svex-a4vec-env-eval a4env aigenv)))))))))
             (local (encapsulate nil
                      (local (defun ind2 (n masks vals x)
                               (if (zp n)
                                   (list masks vals x)
                                 (ind2 (1- n) (cdr masks) (cdr vals) (cdr x)))))

                      ;; BOZO do we need this?
                      ;; (defthm 4vmask-of-nths
                      ;;   (implies (equal (len masks) (len vecs))
                      ;;            (equal (4vec-mask (4vmask-nth n masks)
                      ;;                              (4veclist-nth-safe n vecs))
                      ;;                   (4veclist-nth-safe n (4veclist-mask masks vecs))))
                      ;;   :hints(("Goal" :in-theory (enable 4vmask-nth 4veclist-nth-safe 4veclist-mask nth
                      ;;                                     4vmasklist-fix)
                      ;;           :induct (ind2 n masks vecs nil))))

                      (defthm svex-eval-of-nth-rev
                        (equal (svex-eval (nth n x) env)
                               (4veclist-nth-safe n (svexlist-eval x env))))

                      (in-theory (disable svex-eval-of-nth
                                          4veclist-nth-safe-of-svexlist-eval))

                      (local (defthm 3vec-p-of-eval-by-equal
                               (implies (and (equal x (svex-eval y env))
                                             (3valued-syntaxp y))
                                        (3vec-p x))))

                      (local (defthm 3vec-p-of-eval-by-equal-with-mask
                               (implies (and (equal x (4vec-mask mask (svex-eval y env)))
                                             (3valued-syntaxp y))
                                        (3vec-p x))))

                      (defthm 4veclist-masked-idempotent
                        (implies (equal x (4veclist-mask masks y))
                                 (equal (4veclist-mask masks x) x)))


                      (defthm dumb
                        (implies (and (EQUAL (A4VECLIST-EVAL VALS AIGENV)
                                             (4VECLIST-MASK masks
                                                            (SVEXLIST-EVAL X (SVEX-A4VEC-ENV-EVAL A4ENV AIGENV))))
                                      (3valued-syntaxp (svexlist-nth n x)))
                                 (3vec-p (4veclist-nth-safe n (a4veclist-eval vals aigenv)))
                                 ;; (3vec-p (4vec-mask (4vmask-nth n masks)
                                 ;;                    (a4vec-eval (a4veclist-nth n vals) aigenv)))
                                 )
                        :hints (("goal" :in-theory (e/d (nth len 4veclist-nth-safe a4veclist-eval
                                                             4veclist-mask svexlist-eval
                                                             a4veclist-eval svexlist-nth)
                                                        (4veclist-nth-safe-of-a4veclist-eval))
                                 :expand ((:free (env) (svexlist-eval x env))
                                          (a4veclist-eval vals aigenv)
                                          (:free (a b) (4veclist-mask masks (cons a b))))
                                 :induct (ind2 n masks vals x))))
                      )))
  :verbosep t
  :guard-debug t
  :returns (res a4vec-p)
  (b* ((fn (fnsym-fix fn))
       (args (a4veclist-fix args))
       (res (svex-apply-aig-cases fn args terms mask)))
    ;; ;; This cleverly masks out any bits of the result that we don't care about,
    ;; ;; replacing them with Xes.  This might be a great way to get a lot more
    ;; ;; constant propagation...
    (a4vec-mask mask res))
  ///

  (defthm svex-apply-aig-correct
    (implies (and (fnsym-p fn)
                  (bind-free '((a4env . env)) (a4env))
                  (equal (a4veclist-eval vals aigenv)
                         (4veclist-mask argmasks
                                         (svexlist-eval x (svex-a4vec-env-eval a4env aigenv))))
                  (svex-argmasks-okp (svex-call fn x) mask argmasks))
             (equal (a4vec-eval (svex-apply-aig fn vals x mask) aigenv)
                    (4vec-mask mask
                              (svex-apply fn (svexlist-eval x (svex-a4vec-env-eval a4env aigenv))))))
    :hints(("Goal" :in-theory (disable len-of-4veclist-mask
                                      svex-apply-aig)
                  ;; Establish that (len vals) = (len x).
                  :use ((:instance len-of-4veclist-mask
                         (masks (svex-argmasks mask fn x))
                         (values (a4veclist-eval vals aigenv)))
                        (:instance len-of-4veclist-mask
                         (masks (svex-argmasks mask fn x))
                         (values (svexlist-eval x (svex-a4vec-env-eval a4env aigenv))))))
           (and stable-under-simplificationp
                '(
                  :in-theory (e/d (svex-apply svexlist-eval ;; 4veclist-nth-safe ;; 4veclist-mask
                                              4veclist-mask?
                                              4vec-bitnot
                                              4vec-bitand
                                              4vec-bitor
                                              4vec-bitxor-redef
                                              4vec-reduction-and
                                              4vec-reduction-or
                                              4vec-?
                                              4vec-?*
                                              4vec-bit?
                                              4vec-==)
                                  (;; len-of-svexlist-eval
                                   ;; len-of-a4veclist-eval
                                   ;; len-of-4veclist-mask
                                   svex-argmasks-correct
                                   svex-argmasks-remove-mask))
                  :use ;; ((:instance len-of-svexlist-eval
                  ;;   (env (svex-a4vec-env-eval a4env aigenv)))
                  ;;  (:instance len-of-a4veclist-eval
                  ;;   (x vals) (env aigenv)))
                  ((:instance svex-argmasks-okp-necc
                    (x (svex-call fn x))
                    (vals (a4veclist-eval vals aigenv))
                    (env (svex-a4vec-env-eval a4env aigenv)))
                   ;; (:instance svex-argmasks-remove-mask
                   ;;  (fn fn)
                   ;;  (args x)
                   ;;  (env (svex-a4vec-env-eval a4env aigenv)))


                   )
                  :do-not-induct t
                  :do-not '(fertilize generalize eliminate-destructors)
                  )))
    :otf-flg t))


(defalist svex-aig-memotable :key-type svex :val-type a4vec)

(defthm a4vec-p-of-svex-a4vec-env-lookup
  (implies (and (svex-a4vec-env-p x)
                (hons-assoc-equal k x))
           (a4vec-p (cdr (hons-assoc-equal k x)))))

(defthm a4vec-p-of-svex-aig-memotable-lookup
  (implies (and (svex-aig-memotable-p x)
                (hons-assoc-equal k x))
           (a4vec-p (cdr (hons-assoc-equal k x)))))

;; (SVEX->A4VEC
;;  '(RSH (? (< 0 (* 32 (B- (CONCAT 16 CNST 0) 0))) (* 32 (B- (CONCAT 16 CNST 0) 0)) 0) '(-71265535176078871931497435759850128999 . 269016831744859591531877171671918082457))
;;  (make-fast-alist `((cnst ,(acl2::numlist 0 2 16) . ,(acl2::numlist 1 2 16))))
;;  nil)

(define svex-is-const-concat ((x svex-p))
  :returns (is-concat)
  :guard-hints (("goal" :in-theory (enable nth)))
  (svex-case x
    :call (and (eq x.fn 'concat)
               (eql (len x.args) 3)
               (let ((arg1 (mbe :logic (nth 0 x.args)
                                :exec (car x.args))))
                 (svex-case arg1 :quote)))
    :otherwise nil))

(define svex-const-concat-args ((x svex-p))
  :guard (svex-is-const-concat x)
  :guard-hints (("goal" :expand ((:free (n) (nth n (svex-call->args x)))
                                 (:free (n) (nth n (cdr (svex-call->args x))))
                                 (:free (n) (nth n (cddr (svex-call->args x)))))))
  :prepwork ((local (in-theory (enable svex-is-const-concat))))
  :returns (mv (width 4vec-p)
               (lsbs svex-p)
               (msbs svex-p))
  (b* (((svex-call x)))
    (mv (svex-quote->val (mbe :logic (svex-fix (nth 0 x.args))
                              :exec (first x.args)))
        (mbe :logic (svex-fix (nth 1 x.args))
             :exec (second x.args))
        (mbe :logic (svex-fix (nth 2 x.args))
             :exec (third x.args))))
  ///
  (local (defthm nth-when-n-too-big
           (implies (<= (len x) (nfix n))
                    (equal (nth n x) nil))
           :hints(("Goal" :in-theory (enable nth)))))


  (local (defthm 4vec-zero-ext-is-concat
           (equal (4vec-zero-ext n x)
                  (4vec-concat n x 0))
           :hints(("Goal" :in-theory (enable 4vec-zero-ext 4vec-concat)))))

  (defretd svex-const-concat-args-correct-rw
    (implies (svex-is-const-concat x)
             (equal (svex-eval x env)
                    (4vec-concat width (svex-eval lsbs env) (svex-eval msbs env))))
    :hints(("Goal" :in-theory (enable svex-apply svexlist-eval))))

  (local (defthm svex-count-of-nth
           (<= (svex-count (nth n x)) (svexlist-count x))
           :hints(("Goal" :in-theory (enable nth svexlist-count)))
           :rule-classes :linear))

  (local (defthm svex-count-of-svexlist-nth
           (<= (svex-count (svexlist-nth n x)) (svexlist-count x))
           :hints(("Goal" :in-theory (enable svexlist-nth)))
           :rule-classes :linear))

  (defret svex-count-of-svex-const-concat-args-lsbs
    (implies (svex-is-const-concat x)
             (< (svex-count lsbs) (svex-count x)))
    :rule-classes :linear)

  (defret svex-count-of-svex-const-concat-args-msbs
    (implies (svex-is-const-concat x)
             (< (svex-count msbs) (svex-count x)))
    :hints ((and stable-under-simplificationp
                 '(:expand ((svex-count x)))))
    :rule-classes :linear))



(progn
  (local (defthm 4vec-zero-ext-of-4vec-mask?
           (equal (4vec-zero-ext w (4vec-mask? mask x y))
                  (4vec-mask? (if (and (2vec-p w) (<= 0 (2vec->val w)))
                                  (sparseint-concatenate (2vec->val w) (4vmask-fix mask) 0)
                                mask)
                              (4vec-zero-ext w x)
                              (4vec-zero-ext w y)))
           :hints(("Goal" :in-theory (enable 4vec-mask? 4vec-bit? 3vec-bit?
                                             4vec-zero-ext))
                  (logbitp-reasoning))))

  (local (defthm 4vec-zero-ext-of-equal-4vec-mask?
           (implies (equal z (4vec-mask? mask x y))
                    (equal (4vec-zero-ext w z)
                           (4vec-mask? (if (and (2vec-p w) (<= 0 (2vec->val w)))
                                           (sparseint-concatenate (2vec->val w) (4vmask-fix mask) 0)
                                         mask)
                                       (4vec-zero-ext w x)
                                       (4vec-zero-ext w y))))))


  (local (defthm 4vec-zero-ext-of-zero-ext
           (equal (4vec-zero-ext w (4vec-zero-ext w x))
                  (4vec-zero-ext w x))
           :hints(("Goal" :in-theory (enable 4vec-zero-ext))))))


(defines svex->a4vec
  ;; Self-memoized version of svex-eval, for GL
  :verify-guards nil
  :ruler-extenders :all
  (define svex->a4vec ((x svex-p)
                       (env svex-a4vec-env-p)
                       (masks svex-mask-alist-p))
    :returns (res a4vec-p)
    :measure (two-nats-measure (svex-count x) 1)
    (b* ((env (svex-a4vec-env-fix env)))
      (svex-case x
        :quote (b* ((mask (svex-mask-lookup x masks)))
                 (4vec->a4vec (4vec-mask mask x.val)))
        :var (let ((look (hons-get x.name env))
                   (mask (svex-mask-lookup x masks)))
               (a4vec-mask mask (if look (cdr look) (a4vec-x))))
        :call (b* ((x (svex-fix x))
                         ((when (svex-is-const-concat x))
                          (b* (((mv upper lower)
                                (svex-concat->a4vec x env masks))
                               (mask (svex-mask-lookup x masks)))
                            (a4vec-mask mask (a4vec upper lower))))
                         (args (svexlist->a4vec x.args env masks))
                         (mask (svex-mask-lookup x masks)))
                      (svex-apply-aig x.fn args x.args mask)))))

  (define svexlist->a4vec ((x svexlist-p)
                                  (env svex-a4vec-env-p)
                                  (masks svex-mask-alist-p))
    :returns (res a4veclist-p)
    :measure (two-nats-measure (svexlist-count x) 0)
    (if (atom x)
        nil
      (cons (svex->a4vec (car x) env masks)
            (svexlist->a4vec (cdr x) env masks))))

  (define svex-concat->a4vec ((x svex-p)
                                     (env svex-a4vec-env-p)
                                     (masks svex-mask-alist-p))
    :returns (mv (upper true-listp)
                 (lower true-listp))
    :measure (two-nats-measure (svex-count x)
                               (if (svex-is-const-concat x) 0 2))
    (b* (((unless (svex-is-const-concat x))
          (b* ((res (svex->a4vec x env masks)))
            (mv (a4vec->upper res) (a4vec->lower res))))
         ((mv width lsbs msbs)
          (svex-const-concat-args x))
         ((unless (and (2vec-p width) (natp (2vec->val width))))
          (mv (a4vec->upper (a4vec-x)) (a4vec->lower (a4vec-x))))
         (width (2vec->val width))
         (mask (svex-mask-lookup x masks))
         ((unless (sparseint-test-bitand (sparseint-concatenate width 0 -1) mask))
          (svex-concat->a4vec lsbs env masks))
         ((mv upper2 lower2)
          (svex-concat->a4vec msbs env masks)))
      (svex-concat->a4vec-lower lsbs width upper2 lower2 env masks)))

  (define svex-concat->a4vec-lower ((x svex-p)
                                    (width natp)
                                    (upper-acc true-listp)
                                    (lower-acc true-listp)
                                    (env svex-a4vec-env-p)
                                    (masks svex-mask-alist-p))
    :returns (mv (upper true-listp)
                 (lower true-listp))
    :measure (two-nats-measure (svex-count x)
                               (if (svex-is-const-concat x) 0 2))
    (b* ((upper-acc (llist-fix upper-acc))
         (lower-acc (llist-fix lower-acc))
         ((When (zp width))
          (mv upper-acc lower-acc))
         ((unless (svex-is-const-concat x))
          (b* ((res (svex->a4vec x env masks)))
            (mv (aig-logapp-nss width (a4vec->upper res) upper-acc)
                (aig-logapp-nss width (a4vec->lower res) lower-acc))))
         ((mv sub-width lsbs msbs)
          (svex-const-concat-args x))
         ((unless (and (2vec-p sub-width) (natp (2vec->val sub-width))))
          (mv (aig-logapp-nss width (a4vec->upper (a4vec-x)) upper-acc)
              (aig-logapp-nss width (a4vec->lower (a4vec-x)) lower-acc)))
         (sub-width (2vec->val sub-width))
         (lsbs-width (min width sub-width))
         (msbs-width (- width lsbs-width))
         ((mv upper-acc lower-acc)
          (svex-concat->a4vec-lower msbs msbs-width upper-acc lower-acc env masks)))
      (svex-concat->a4vec-lower lsbs lsbs-width upper-acc lower-acc env masks)))


  ///
  (verify-guards svex->a4vec :guard-debug t)
  (local (in-theory (disable svex->a4vec svexlist->a4vec)))

  (encapsulate nil
    (local (defthm lookup-in-svex-a4vec-env-eval-lemma
             (implies (svex-a4vec-env-p env)
                      (equal (hons-assoc-equal k (svex-a4vec-env-eval env aigenv))
                             (and (hons-assoc-equal k env)
                                  (cons k (a4vec-eval (cdr (hons-assoc-equal k env))
                                                      aigenv)))))
             :hints(("Goal" :in-theory (enable svex-a4vec-env-eval
                                               svex-a4vec-env-p)
                     :induct (svex-a4vec-env-eval env aigenv)
                     :do-not-induct t))
             :rule-classes nil))

    (defthm lookup-in-svex-a4vec-env-eval
      (equal (hons-assoc-equal k (svex-a4vec-env-eval env aigenv))
             (and (hons-assoc-equal k (svex-a4vec-env-fix env))
                  (cons k (a4vec-eval (cdr (hons-assoc-equal k (svex-a4vec-env-fix env)))
                                      aigenv))))
      :hints(("Goal" :use ((:instance lookup-in-svex-a4vec-env-eval-lemma
                            (env (svex-a4vec-env-fix env))))))))

  (defthm svex-env-lookup-in-svex-a4vec-env-eval
    (equal (svex-env-lookup k (svex-a4vec-env-eval env aigenv))
           (if (hons-assoc-equal (svar-fix k) (svex-a4vec-env-fix env))
               (a4vec-eval (cdr (hons-assoc-equal (svar-fix k) (svex-a4vec-env-fix env)))
                           aigenv)
             (4vec-x)))
    :hints(("Goal" :in-theory (enable svex-env-lookup))))

  ;; (local (defthm svex-apply-aig-correct-rw
  ;;        (implies (and (fnsym-p fn)
  ;;                (bind-free '((a4env . env)) (a4env))
  ;;                (equal (a4veclist-eval vals aigenv)
  ;;                       (4veclist-mask argmasks (svexlist-eval x (svex-a4vec-env-eval a4env aigenv))))
  ;;                (svex-argmasks-okp (svex-call fn x) mask argmasks))
  ;;           (equal (a4vec-eval (svex-apply-aig fn vals x mask) aigenv)
  ;;                  (4vec-mask mask (svex-apply fn (svexlist-eval x (svex-a4vec-env-eval a4env aigenv))))))


  (local (in-theory (enable svex-mask-alist-complete-necc)))


  (local (defthm 4vec-concat-when-not-2vec
           (implies (not (equal (4vec->upper width)
                                (4vec->lower width)))
                    (equal (4vec-concat width x y) (4vec-x)))
           :hints(("Goal" :in-theory (enable 4vec-concat)))))

  (local (defthm 4vec-concat-when-not-natp
           (implies (< (4vec->lower width) 0)
                    (equal (4vec-concat width x y) (4vec-x)))
           :hints(("Goal" :in-theory (enable 4vec-concat)))))

  (local (defthm 4vec-mask-idempotence-rw
           (implies (equal y (4vec-mask mask x))
                    (equal (4vec-mask mask y)
                           y))))

  (local (defthm 4vec-concat-when-width-0
           (implies (and (equal 0 (4vec->upper width))
                         (equal 0 (4vec->lower width)))
                    (equal (4vec-concat width x y) (4vec-fix y)))
           :hints(("Goal" :in-theory (enable 4vec-concat)))))


  (local (define 4vec-change-all-bits ((x 4vec-p))
           :returns (new-x 4vec-p)
           (4vec (lognot (4vec->upper x))
                 (lognot (4vec->lower x)))))



  (local
   (encapsulate nil
     (local (in-theory (disable* (:rules-of-class :linear :here)
                                 bitops::logand-natp-type-2
                                 bitops::logand-natp-type-1
                                 bitops::logior-natp-type
                                 bitops::lognot-negp
                                 bitops::lognot-natp
                                 member-svex-mask-alist-keys
                                 acl2::loghead-identity)))
     (defthm mask-of-bit?-logand-lognot
       (implies (4vmask-p mask)
                (equal (4vec-mask mask (4vec-bit? (2vec (logand a (lognot (sparseint-val mask)))) x y))
                       (4vec-mask mask y)))
       :hints(("Goal" :in-theory (e/d* (4vec-mask 4vec-bit? 3vec-bit?)))
              (logbitp-reasoning)))

     (defthm mask-of-bit?-logand-lognot2
       (implies (4vmask-p mask)
                (equal (4vec-mask mask (4vec-bit? (2vec (logand (lognot (sparseint-val mask)) a)) x y))
                       (4vec-mask mask y)))
       :hints(("Goal" :in-theory (e/d* (4vec-mask 4vec-bit? 3vec-bit?)))
              (logbitp-reasoning)))

     (defthm argmasks-okp-for-const-concat-implies-lsb-mask-subsumes-outer
       (b* (((mv width lsbs msbs) (svex-const-concat-args x)))
         (implies (and (svex-is-const-concat x)
                       (svex-mask-alist-complete masks)
                       (2vec-p width)
                       (<= (nfix w) (2vec->val width)))
                  (4vmask-subsumes (sparseint-concatenate w (svex-mask-lookup lsbs masks) 0)
                                   (sparseint-concatenate w (svex-mask-lookup x masks) 0))))
       :hints (("goal" :use ((:instance svex-mask-alist-complete-necc
                              (y x) (mask-al masks))
                             (:instance svex-argmasks-okp-necc
                              (vals (b* (((mv width lsbs msbs) (svex-const-concat-args x)))
                                      (list width
                                            (4vec-bit?
                                             (2vec (logandc1 (sparseint-val (svex-mask-lookup lsbs masks))
                                                             (sparseint-val (svex-mask-lookup x masks))))
                                             (4vec-change-all-bits (svex-eval lsbs env))
                                             (svex-eval lsbs env))
                                            (svex-eval msbs env))))
                              (mask (svex-mask-lookup x masks))
                              (argmasks (svex-argmasks-lookup (svex-call->args x) masks))))
                :in-theory (enable svex-argmasks-lookup
                                   svex-apply
                                   4vmask-subsumes
                                   svexlist-eval
                                   4veclist-mask
                                   len nth)
                :expand ((svex-is-const-concat x)
                         (svex-const-concat-args x)
                         (len (svex-call->args x))
                         (len (cdr (svex-call->args x)))
                         (len (cddr (svex-call->args x)))
                         (len (cdddr (svex-call->args x)))
                         (:free (n) (nth n (svex-call->args x)))
                         (:free (n) (nth n (cdr (svex-call->args x))))
                         (:free (n) (nth n (cddr (svex-call->args x))))
                         (:free (n) (nth n (cdddr (svex-call->args x))))))
               (and stable-under-simplificationp
                    '(:in-theory (enable 4vec-mask 4vec-bit? 3vec-bit? 4vec-change-all-bits 4vec-concat)))
               (logbitp-reasoning
                :add-hints (:in-theory (enable* logbitp-case-splits))
                :simp-hint (:in-theory (enable* logbitp-case-splits)))
               )
       :otf-flg t)

     (local (in-theory (disable iff not)))
     (defthm argmasks-okp-for-const-concat-implies-msb-mask-subsumes-outer
       (b* (((mv width lsbs msbs) (svex-const-concat-args x)))
         (implies (and (svex-is-const-concat x)
                       (svex-mask-alist-complete masks)
                       (2vec-p width)
                       (<= 0 (2vec->val width)))
                  (4vmask-subsumes (svex-mask-lookup msbs masks)
                                   (sparseint-rightshift (4vec->lower width) (svex-mask-lookup x masks)))))
       :hints (("goal" :use ((:instance svex-mask-alist-complete-necc
                              (y x) (mask-al masks))
                             (:instance svex-argmasks-okp-necc
                              (vals (b* (((mv width lsbs msbs) (svex-const-concat-args x)))
                                      (list width
                                            (svex-eval lsbs env)
                                            (4vec-bit?
                                             (2vec (logandc1 (sparseint-val (svex-mask-lookup msbs masks))
                                                             (logtail (2vec->val width)
                                                                      (sparseint-val (svex-mask-lookup x masks)))))
                                             (4vec-change-all-bits (svex-eval msbs env))
                                             (svex-eval msbs env)))))
                              (mask (svex-mask-lookup x masks))
                              (argmasks (svex-argmasks-lookup (svex-call->args x) masks))))
                :in-theory (enable svex-argmasks-lookup
                                   svex-apply
                                   4vmask-subsumes
                                   svexlist-eval
                                   4veclist-mask
                                   len nth)
                :expand ((svex-is-const-concat x)
                         (svex-const-concat-args x)
                         (len (svex-call->args x))
                         (len (cdr (svex-call->args x)))
                         (len (cddr (svex-call->args x)))
                         (len (cdddr (svex-call->args x)))
                         (:free (n) (nth n (svex-call->args x)))
                         (:free (n) (nth n (cdr (svex-call->args x))))
                         (:free (n) (nth n (cddr (svex-call->args x))))
                         (:free (n) (nth n (cdddr (svex-call->args x))))))
               (and stable-under-simplificationp
                    '(:in-theory (enable 4vec-mask 4vec-bit? 3vec-bit? 4vec-change-all-bits 4vec-concat)))
               (logbitp-reasoning
                :add-hints (:in-theory (enable* logbitp-case-splits))
                :simp-hint (:in-theory (enable* logbitp-case-splits)))
               )
       :otf-flg t)


     (defthm argmasks-okp-for-const-concat-implies-lsb-mask-subsumes-outer-when-tail-0
       (b* (((mv width lsbs msbs) (svex-const-concat-args x)))
         (implies (and (svex-is-const-concat x)
                       (svex-mask-alist-complete masks)
                       (2vec-p width) (<= 0 (2vec->val width))
                       (equal 0 (logtail (2vec->val width) (sparseint-val (svex-mask-lookup x masks)))))
                  (4vmask-subsumes (svex-mask-lookup lsbs masks)
                                   (svex-mask-lookup x masks))))
       :hints (("goal" :use ((:instance argmasks-okp-for-const-concat-implies-lsb-mask-subsumes-outer (w (2vec->val (mv-nth 0 (svex-const-concat-args x))))))
                :in-theory (e/d (4vmask-subsumes)
                                (argmasks-okp-for-const-concat-implies-lsb-mask-subsumes-outer)))
               (logbitp-reasoning :prune-examples nil)
               )
       :otf-flg t)))


  (local (defthmd 4vec-mask-over-4vec-zero-ext
           (implies (and (2vec-p width)
                         (<= 0 (2vec->val width)))
                    (equal (4vec-mask mask (4vec-zero-ext width x))
                           (4vec-concat width (4vec-mask mask x)
                                        (4vec-mask (sparseint-rightshift (2vec->val width) (4vmask-fix mask))
                                                   0))))
           :hints(("Goal" :in-theory (enable 4vec-mask 4vec-zero-ext 4vec-concat))
                  (logbitp-reasoning :prune-examples nil))))

  (local (defthmd 4vec-mask-over-4vec-concat
           (implies (and (2vec-p width)
                         (<= 0 (2vec->val width)))
                    (equal (4vec-mask mask (4vec-concat width x y))
                           (4vec-concat width
                                        (4vec-mask mask x)
                                        (4vec-mask (sparseint-rightshift (2vec->val width) (4vmask-fix mask))
                                                   y))))
           :hints(("Goal" :in-theory (enable 4vec-mask 4vec-concat))
                  (logbitp-reasoning :prune-examples nil))))

  (local (defthmd 4vec-concat-of-4vec-mask-identity
           (implies (and (equal mask1 (4vmask-fix mask))
                         (2vec-p w)
                         (<= 0 (2vec->val w))
                         (equal w1 (2vec->val w)))
                    (equal (4vec-concat w
                                        (4vec-mask mask x)
                                        (4vec-mask (sparseint-rightshift w1 mask1)
                                                   (4vec-rsh w x)))
                           (4vec-mask mask x)))
           :hints(("Goal" :in-theory (enable 4vec-mask 4vec-concat 4vec-rsh 4vec-shift-core))
                  (logbitp-reasoning :prune-examples nil))))

  (local (defthmd 4vec-concat-of-equal-4vec-conct
           (implies (and (equal x (4vec-concat w a b))
                         (2vec-p w)
                         (<= 0 (2vec->val w)))
                    (equal (4vec-concat w x y)
                           (4vec-concat w a y)))))

  (local (defthm min-gte-zero
           (implies (and (<= 0 x)
                         (<= 0 y))
                    (<= 0 (min x y)))))

  (local (defthm 2vec-of-4vec-acc
           (implies (2vec-p x)
                    (and (equal (2vec (4vec->lower x)) (4vec-fix x))
                         (equal (2vec (4vec->upper x)) (4vec-fix x))))
           :hints(("Goal" :in-theory (enable 2vec)))))

  (local (defthmd 4vec-concat-identity
           (implies (and (2vec-p w) (<= 0 (2vec->val w)))
                    (equal (4vec-concat w x (4vec-rsh w x))
                           (4vec-fix x)))
           :hints(("Goal" :in-theory (enable 4vec-concat 4vec-rsh 4vec-shift-core))
                  (logbitp-reasoning :prune-examples nil))))

  (local (defthmd equal-of-4vec-concat2
           (implies (and (2vec-p w) (<= 0 (2vec->val w)))
                    (equal (equal (4vec-concat w x y) z)
                           (and (4vec-p z)
                                (equal (4vec-zero-ext w x) (4vec-zero-ext w z))
                                (equal (4vec-fix y) (4vec-rsh w z)))))
           :hints(("Goal" :in-theory (enable 4vec-concat 4vec-zero-ext 4vec-rsh 4vec-shift-core))
                  (logbitp-reasoning))
           :otf-flg t))


  (local (defthm 4vec-zero-ext-of-concat
           (implies (and (2vec-p w1) (2vec-p w2)
                         (<= 0 (2vec->val w1))
                         (<= (2vec->val w1) (2vec->val w2)))
                    (equal (4vec-zero-ext w1 (4vec-concat w2 x y))
                           (4vec-zero-ext w1 x)))
           :hints(("Goal" :in-theory (enable 4vec-zero-ext 4vec-concat)))))

  (local (defthm 4vec-rsh-of-4vec-mask
           (implies (and (2vec-p shift) (<= 0 (2vec->val shift)))
                    (equal (4vec-rsh shift (4vec-mask mask x))
                           (4vec-mask (sparseint-rightshift (2vec->val shift) (4vmask-fix mask))
                                      (4vec-rsh shift x))))
           :hints(("Goal" :in-theory (enable 4vec-mask 4vec-rsh 4vec-shift-core)))))

  (local (defthm equal-zero-ext-of-mask
           (implies (and (2vec-p w)
                         (<= 0 (2vec->val w)))
                    (equal (equal (4vec-zero-ext w (4vec-mask m x))
                                  (4vec-zero-ext w (4vec-mask m y)))
                           (equal (4vec-mask (sparseint-concatenate (2vec->val w) (4vmask-fix m) 0) x)
                                  (4vec-mask (sparseint-concatenate (2vec->val w) (4vmask-fix m) 0) y))))
           :hints(("Goal" :in-theory (enable 4vec-zero-ext 4vec-mask))
                  (logbitp-reasoning))))


  (local (defthmd 4vec-mask-of-4vec-concat-under-mask
           (implies (and (equal (logtail (2vec->val width) (sparseint-val (4vmask-fix mask)))
                                0)
                         (2vec-p width)
                         (<= 0 (2vec->val width)))
                    (equal (4vec-mask mask (4vec-concat width x y))
                           (4vec-mask mask x)))
           :hints(("Goal" :in-theory (enable 4vec-mask 4vec-concat))
                  (logbitp-reasoning :prune-examples nil))))

  (local (defthmd 4vec-concat-of-4vec
           (equal (4vec (logapp w a b)
                        (logapp w c d))
                  (4vec-concat (2vec (nfix w)) (4vec a c) (4vec b d)))
           :hints(("Goal" :in-theory (enable 4vec-concat)))))

  (local (defthmd 4vec-zero-ext-of-4vec
           (equal (4vec (loghead w a)
                        (loghead w c))
                  (4vec-zero-ext (2vec (nfix w)) (4vec a c)))
           :hints(("Goal" :in-theory (enable 4vec-zero-ext)))))

  (local (defthmd 4vec-zero-ext-of-4vec/0
           (equal (4vec (loghead w a) 0)
                  (4vec-zero-ext (2vec (nfix w)) (4vec a 0)))
           :hints(("Goal" :in-theory (enable 4vec-zero-ext)))))

  (local (defthmd 4vec-of-aig-list->s-of-upper/lower
           (equal (4vec (aig-list->s (a4vec->upper x) env)
                        (aig-list->s (a4vec->lower x) env))
                  (a4vec-eval x env))
           :hints(("Goal" :in-theory (enable a4vec-eval)))))


  (local (defthm aig-list->s-of-list-fix
           (equal (aig-list->s (list-fix x) env)
                  (aig-list->s x env))
           :hints(("Goal" :in-theory (enable aig-list->s)))))



  (local (defthm 4vec-mask-of-loghead-4vec-mask
           (implies (equal mask1 (4vmask-fix mask))
                    (Equal (4vec-mask (sparseint-concatenate n mask1 0) (4vec-mask mask x))
                           (4vec-mask (sparseint-concatenate n mask1 0) x)))
           :hints(("Goal" :in-theory (enable 4vec-mask))
                  (logbitp-reasoning))))


  (local (defun aig-logapp-nss-ind (w1 w2 x y)
           (declare (xargs :measure (nfix w1)))
           (if (or (zp w1) (zp w2))
               (list x y)
             (aig-logapp-nss-ind (1- w1) (1- w2) (gl::scdr x) y))))

  (local (defthm aig-logapp-nss-of-nfix
           (Equal (aig-logapp-nss (nfix w) x y)
                  (aig-logapp-nss w x y))
           :hints(("Goal" :in-theory (enable aig-logapp-nss)))))

  (local (defthm aig-logapp-nss-of-list-fix
           (Equal (aig-logapp-nss w (list-fix x) y)
                  (aig-logapp-nss w x y))
           :hints(("Goal" :in-theory (enable aig-logapp-nss)))))

  (local (defthm aig-logapp-nss-of-snorm
           (Equal (aig-logapp-nss w (gl::bfr-snorm x) y)
                  (aig-logapp-nss w x y))
           :hints(("Goal" :in-theory (enable aig-logapp-nss)))))

  (local (defthm aig-logapp-nss-of-aig-logapp-nss
           (equal (aig-logapp-nss w1 (aig-logapp-nss w2 x y) z)
                  (let* ((wa (min (nfix w1) (nfix w2)))
                         (wb (- (nfix w1) wa)))
                    (aig-logapp-nss wa x (aig-logapp-nss wb y z))))
           :hints(("Goal" :in-theory (enable aig-logapp-nss)
                   :induct (aig-logapp-nss-ind w1 w2 x y)
                   :expand ((:free (x y) (aig-logapp-nss w1 x y))
                            (:free (x y) (aig-logapp-nss w2 x y)))))))

  (local (defthm aig-logapp-nss-when-zp
           (implies (zp w)
                    (equal (aig-logapp-nss w x y) (list-fix y)))
           :hints(("Goal" :in-theory (enable aig-logapp-nss)))))


  (local
   (defun-sk svex-concat->a4vec-lower-acc-elim-correct (x width env masks)
     (forall (upper-acc lower-acc)
             (implies (syntaxp (not (and (equal upper-acc ''nil)
                                         (equal lower-acc ''nil))))
                      (b* (((mv upper-impl lower-impl)
                            (svex-concat->a4vec-lower x width upper-acc lower-acc env masks))
                           ((mv upper-spec lower-spec)
                            (svex-concat->a4vec-lower x width nil nil env masks)))
                        (and (equal upper-impl (aig-logapp-nss width upper-spec (list-fix upper-acc)))
                             (equal lower-impl (aig-logapp-nss width lower-spec (list-fix lower-acc)))))))
     :rewrite :direct))
  (local (in-theory (disable svex-concat->a4vec-lower-acc-elim-correct)))

  (local (std::defret-mutual svex-concat->a4vec-lower-acc-elim-lemma
           (defret svex-concat->a4vec-lower-acc-elim-lemma
             (svex-concat->a4vec-lower-acc-elim-correct x width env masks)
             :hints ((and stable-under-simplificationp
                          `(:expand (,(car (last clause))
                                     (:free (upper-acc lower-acc) <call>)))))
             :fn svex-concat->a4vec-lower
             :rule-classes nil)
           :skip-others t))

  (defthm svex-concat->a4vec-lower-acc-elim
    (implies (syntaxp (not (and (equal upper-acc ''nil)
                                (equal lower-acc ''nil))))
             (b* (((mv upper-impl lower-impl)
                   (svex-concat->a4vec-lower x width upper-acc lower-acc env masks))
                  ((mv upper-spec lower-spec)
                   (svex-concat->a4vec-lower x width nil nil env masks)))
               (and (equal upper-impl (aig-logapp-nss width upper-spec (list-fix upper-acc)))
                    (equal lower-impl (aig-logapp-nss width lower-spec (list-fix lower-acc))))))
    :hints (("goal" :use svex-concat->a4vec-lower-acc-elim-lemma)))


  ;; (define svex-concat->a4vec-lower-zero ((x svex-p)
  ;;                                        (width natp)
  ;;                                        (env svex-a4vec-env-p)
  ;;                                        (masks svex-mask-alist-p)
  ;;                                        (memo svex-aig-memotable-p))
  ;;   :returns (mv (upper true-listp)
  ;;                (lower true-listp)
  ;;                (memo1 svex-aig-memotable-p))
  ;;   :measure (svex-count x)
  ;;   :hooks nil
  ;;   :verify-guards nil
  ;;   (b* ((memo (svex-aig-memotable-fix memo))
  ;;        ((When (zp width))
  ;;         (mv nil nil memo))
  ;;        ((unless (svex-is-const-concat x))
  ;;         (b* (((mv res memo) (svex->a4vec x env masks memo)))
  ;;           (mv (aig-logapp-nss width (a4vec->upper res) nil)
  ;;               (aig-logapp-nss width (a4vec->lower res) nil)
  ;;               memo)))
  ;;        ((mv sub-width lsbs msbs)
  ;;         (svex-const-concat-args x))
  ;;        ((unless (and (2vec-p sub-width) (natp (2vec->val sub-width))))
  ;;         (mv (aig-logapp-nss width (a4vec->upper (a4vec-x)) nil)
  ;;             (aig-logapp-nss width (a4vec->lower (a4vec-x)) nil)
  ;;             (svex-aig-memotable-fix memo)))
  ;;        (sub-width (2vec->val sub-width))
  ;;        (lsbs-width (min width sub-width))
  ;;        (msbs-width (- width lsbs-width))
  ;;        ((mv upper2 lower2 memo)
  ;;         (svex-concat->a4vec-lower-zero msbs msbs-width env masks memo))
  ;;        ((mv upper1 lower1 memo)
  ;;         (svex-concat->a4vec-lower-zero lsbs lsbs-width env masks memo)))
  ;;     (mv (aig-logapp-nss lsbs-width upper1 upper2)
  ;;         (aig-logapp-nss lsbs-width lower1 lower2)
  ;;         memo))
  ;;   ///
  ;;   (defthm-svex->a4vec-flag
  ;;     (defthm svex-concat->a4vec-lower-in-terms-of-zero
  ;;       (b* (((mv upper-impl lower-impl memo-impl)
  ;;             (svex-concat->a4vec-lower x width upper-acc lower-acc env masks memo))
  ;;            ((mv upper-spec lower-spec memo-spec)
  ;;             (svex-concat->a4vec-lower-zero x width env masks memo)))
  ;;         (and (equal memo-impl memo-spec)
  ;;              (equal upper-impl (aig-logapp-nss width upper-spec (list-fix upper-acc)))
  ;;              (equal lower-impl (aig-logapp-nss width lower-spec (list-fix lower-acc)))))
  ;;       :flag svex-concat->a4vec-lower
  ;;       :hints ('(:expand ((svex-concat->a4vec-lower x width upper-acc lower-acc env masks memo)
  ;;                          (svex-concat->a4vec-lower-zero x width env masks memo)))))
  ;;     :skip-others t))


  (local (defthm 4vec-mask-of-loghead-zero-ext
           (implies (natp width)
                    (equal (4vec-mask (sparseint-concatenate width mask 0) (4vec-zero-ext (2vec width) x))
                           (4vec-mask (sparseint-concatenate width mask 0) x)))
           :hints(("Goal" :in-theory (enable 4vec-mask 4vec-zero-ext))
                  (logbitp-reasoning))))

  (local (defthm 4vec-mask-zero-ext-mask
           (equal (4vec-mask mask (4vec-zero-ext w (4vec-mask mask x)))
                  (4vec-mask mask (4vec-zero-ext w x)))
           :hints(("Goal" :in-theory (enable 4vec-mask 4vec-zero-ext))
                  (logbitp-reasoning))))


  (local (defthm 4vec-zero-ext-0
           (equal (4vec-zero-ext 0 x) 0)
           :hints(("Goal" :in-theory (enable 4vec-zero-ext)))))



  ;; (local (Defthm 4vec-zero-ext-of-zp
  ;;                   (equal (4vec-zero-ext (2vec width) x) 0))
  ;;          :hints(("Goal" :in-theory (enable* 4vec-zero-ext
  ;;                                             ihsext-recursive-redefs))))

  (local (defthm 4vec-concat-0
           (equal (4vec-concat width x 0)
                  (4vec-zero-ext width x))
           :hints(("Goal" :in-theory (enable 4vec-concat 4vec-zero-ext)))))

  (local (defthm 4vec-of-equal-upper-lower
           (implies (and (equal a (4vec->upper x))
                         (equal b (4vec->lower x)))
                    (equal (4vec a b) (4vec-fix x)))))



  (local (defthm 4vec-mask?-of-4vec-mask?-when-subsumes
           (implies (4vmask-subsumes m1 m2)
                    (equal (4vec-mask? m2 a (4vec-mask? m1 a b))
                           (4vec-mask? m1 a b)))
           :hints(("Goal" :in-theory (enable 4vec-mask? 4vec-bit? 3vec-bit? 4vmask-subsumes))
                  (logbitp-reasoning))))

  (local (defthm zero-ext-of-zero-ext
           (implies (and (2vec-p a) (2vec-p b)
                         (<= 0 (2vec->val a))
                         (<= (2vec->val a) (2vec->val b)))
                    (and (equal (4vec-zero-ext a (4vec-zero-ext b x))
                                (4vec-zero-ext a x))
                         (equal (4vec-zero-ext b (4vec-zero-ext a x))
                                (4vec-zero-ext a x))))
           :hints(("Goal" :in-theory (enable 4vec-zero-ext)))))


  (local (Defthm 4vec-rsh-of-4vec-mask?
           (implies (and (2vec-p sh) (<= 0 (2vec->val sh)))
                    (equal (4vec-rsh sh (4vec-mask? mask a b))
                           (4vec-mask? (sparseint-rightshift (2vec->val sh) (4vmask-fix mask))
                                       (4vec-rsh sh a)
                                       (4vec-rsh sh b))))
           :hints(("Goal" :in-theory (enable 4vec-rsh 4vec-shift-core 4vec-mask?
                                             4vec-bit? 3vec-bit?)))))

  (local (defthm 4vec-rsh-of-4vec-zero-ext
           (implies (and (2vec-p a) (2vec-p b)
                         (<= 0 (2vec->val a))
                         (<= (2vec->val a) (2vec->val b)))
                    (and (equal (4vec-rsh a (4vec-zero-ext b x))
                                (4vec-zero-ext (2vec (- (2vec->val b) (2vec->val a)))
                                               (4vec-rsh a x)))
                         (equal (4vec-rsh b (4vec-zero-ext a x)) 0)))
           :hints(("Goal" :in-theory (enable 4vec-rsh 4vec-shift-core 4vec-zero-ext))
                  (and stable-under-simplificationp
                       '(:in-theory (enable* ihsext-recursive-redefs))))))

  (local (defthm 4vmask-subsumes-of-loghead
           (implies (and (4vmask-subsumes a b)
                         (4vmask-p a) (4vmask-p b))
                    (4vmask-subsumes (sparseint-concatenate w a 0) (sparseint-concatenate w b 0)))
           :hints(("Goal" :in-theory (enable 4vmask-subsumes))
                  (logbitp-reasoning))))

  (local (defthm 4vec-mask?-of-concat-same
           (implies (and (2vec-p w) (<= 0 (2vec->val w)))
                    (equal (4vec-mask? mask (4vec-concat w a b) (4vec-concat w c d))
                           (4vec-concat w
                                        (4vec-mask? (sparseint-concatenate (2vec->val w) (4vmask-fix mask) 0)
                                                    (4vec-zero-ext w a)
                                                    (4vec-zero-ext w c))
                                        (4vec-mask? (sparseint-rightshift (2vec->val w) (4vmask-fix mask)) b d))))
           :hints(("Goal" :in-theory (enable 4vec-mask? 4vec-bit? 3vec-bit?
                                             4vec-concat 4vec-zero-ext))
                  (logbitp-reasoning))))

  (local (defthm 4vec-mask?-of-concat-when-logtail-0
           (implies (and (equal 0 (logtail (2vec->val w) (sparseint-val (4vmask-fix mask))))
                         (2vec-p w) (<= 0 (2vec->val w)))
                    (equal (4vec-mask? mask (4vec-concat w a b) c)
                           (4vec-mask? mask a c)))
           :hints(("Goal" :in-theory (enable 4vec-mask? 4vec-bit? 3vec-bit? 4vec-concat))
                  (logbitp-reasoning :prune-examples nil))))

  ;; (local (defthm 4vec-mask?-of-zero-ext-when-logtail-0
  ;;          (implies (and (equal 0 (logtail (2vec->val w) (sparseint-val (4vmask-fix mask))))
  ;;                        (2vec-p w) (<= 0 (2vec->val w)))
  ;;                   (equal (4vec-mask? mask (4vec-zero-ext w a) c)
  ;;                          (4vec-mask? mask a c)))
  ;;          :hints(("Goal" :in-theory (enable 4vec-mask? 4vec-bit? 3vec-bit? 4vec-zero-ext))
  ;;                 (logbitp-reasoning :prune-examples nil))))

  ;; (local (defthm 4vec-mask?-of-zero-ext-when-logtail-0-2
  ;;          (implies (and (equal 0 (logtail (2vec->val w) (sparseint-val (4vmask-fix mask))))
  ;;                        (2vec-p w) (<= 0 (2vec->val w)))
  ;;                   (equal (4vec-mask? mask a (4vec-zero-ext w c))
  ;;                          (4vec-mask? mask a c)))
  ;;          :hints(("Goal" :in-theory (enable 4vec-mask? 4vec-bit? 3vec-bit? 4vec-zero-ext))
  ;;                 (logbitp-reasoning :prune-examples nil))))

  (local (defthm 4veclist-mask?-of-conses
           (equal (4veclist-mask? (cons c1 c2) (cons t1 t2) (cons f1 f2))
                  (cons (4vec-mask? c1 t1 f1)
                        (4veclist-mask? c2 t2 f2)))
           :hints(("Goal" :in-theory (enable 4veclist-mask?)))))


  (local
   (progn
     (defcong 4vmask-equal equal (4vec-mask? mask a b) 1
       :hints(("Goal" :in-theory (enable 4vec-mask?))))
     (defthm sparseint-concatenate-self-under-4vmask-equal
       (4vmask-equal (sparseint-concatenate width (sparseint-concatenate width a b) c)
                     (sparseint-concatenate width a c))
       :hints(("Goal" :in-theory (enable bitops::logapp-right-assoc))))

     (defcong sparseint-equal 4vmask-equal (sparseint-concatenate width a b) 2)
     (defcong sparseint-equal 4vmask-equal (sparseint-concatenate width a b) 3)

     (defthm sparseint-equal-rightshift-0
       (sparseint-equal (sparseint-rightshift 0 x) x))))


  (local (defthm logand-ash-neg1-equal-0
           (implies (natp n)
                    (equal (equal 0 (logand (ash -1 n) x))
                           (equal 0 (logtail n x))))
           :hints ((logbitp-reasoning :prune-examples nil))))

  (local (defthm loghead-when-width-zp
           (implies (zp width)
                    (equal (loghead width x) 0))))

  (local (defthm 4vec-mask-of-4vec-mask?-when-subsumes
           (implies (4vmask-subsumes m1 m2)
                    (equal (4vec-mask m2 (4vec-mask? m1 b c))
                           (4vec-mask m2 b)))
           :hints(("Goal" :in-theory (enable 4vec-mask? 4vec-mask 4vec-bit? 3vec-bit? 4vmask-subsumes))
                  (logbitp-reasoning))))


  ;; (local (defthm 4vec-zero-ext-to-concat
  ;;          (equal (4vec-zero-ext w x)
  ;;                 (4vec-concat w x 0))))

  ;; (local (in-theory (disable 4vec-concat-0)))

  (std::defret-mutual svex->a4vec-correct
    (defret svex->a4vec-correct
      (implies (svex-mask-alist-complete masks)
               (equal (a4vec-eval res aigenv)
                      (4vec-mask (svex-mask-lookup x masks)
                                 (svex-eval x (svex-a4vec-env-eval env aigenv)))))
      :hints ('(:expand (<call>
                         (:free (env) (svex-eval x env)))))
      :fn svex->a4vec)
    (defret svexlist->a4vec-correct
      (implies (svex-mask-alist-complete masks)
               (equal (a4veclist-eval res aigenv)
                      (4veclist-mask (svex-argmasks-lookup x masks)
                                     (svexlist-eval x (svex-a4vec-env-eval env aigenv)))))
      :hints ('(:expand (<call>
                         (:free (env) (svexlist-eval x env))
                         (a4veclist-eval nil aigenv)
                         (svex-argmasks-lookup x masks)
                         (:free (a b) (a4veclist-eval (cons a b) aigenv)))
                :in-theory (enable 4veclist-mask)))
      :fn svexlist->a4vec)
    (defret svex-concat->a4vec-correct
      (implies (svex-mask-alist-complete masks)
               (4vec-mask-equiv (a4vec-eval (a4vec upper lower) aigenv)
                                (svex-eval x (svex-a4vec-env-eval env aigenv))
                                (svex-mask-lookup x masks)))
      :hints ((acl2::just-expand ((:free (x) (hide x))) :last-only t :lambdasp t)
              '(:expand (<call>)
                :in-theory (e/d (svex-const-concat-args-correct-rw
                                 4vec-concat-of-4vec))))
      :fn svex-concat->a4vec)

    (defret svex-concat->a4vec-lower-correct
      :pre-bind ((lower-acc nil) (upper-acc nil))
      (implies (svex-mask-alist-complete masks)
               (let ((ans (a4vec-eval (a4vec upper lower) aigenv)))
                 (equal ans
                        (4vec-zero-ext
                         (2vec (nfix width))
                         (4vec-mask? (svex-mask-lookup x masks)
                                     (svex-eval x (svex-a4vec-env-eval env aigenv))
                                     (hide ans))))))
      :hints ((acl2::just-expand ((:free (x) (hide x))) :last-only t :lambdasp t)
              '(:expand ((svex-concat->a4vec-lower x width nil nil env masks))
                :in-theory (e/d (svex-const-concat-args-correct-rw
                                 4vec-concat-of-4vec
                                 4vec-zero-ext-of-4vec
                                 4vec-zero-ext-of-4vec/0
                                 4vec-of-aig-list->s-of-upper/lower
                                 ;; 4vec-mask-over-4vec-concat
                                 ;; 4vec-mask-over-4vec-zero-ext
                                 )
                                (BITOPS::LOGAPP-OF-I-0
                                 a4vec-eval-of-var)))
              (and stable-under-simplificationp
                   '(:in-theory (e/d (equal-of-4vec-concat2
                                      4vec-mask-of-4vec-concat-under-mask
                                      svex-const-concat-args-correct-rw
                                      4vec-concat-of-4vec
                                      4vec-zero-ext-of-4vec
                                      4vec-zero-ext-of-4vec/0
                                      4vec-of-aig-list->s-of-upper/lower)
                                     (a4vec-eval-of-var))
                     :do-not-induct t)))
      :fn svex-concat->a4vec-lower)
    )


  (std::defret-mutual svexlist->a4vec-true-listp
    (defret svexlist->a4vec-true-listp
      (true-listp res)
      :hints ('(:expand (<call>)))
      :fn svexlist->a4vec)
    :skip-others t)

  (std::defret-mutual len-of-svexlist->a4vec
    (defret len-of-svexlist->a4vec
      (equal (len res)
             (len x))
      :hints ('(:expand (<call>)))
      :fn svexlist->a4vec)
    :skip-others t)

  (deffixequiv-mutual svex->a4vec))


(define svex->a4vec-memotable-correctp ((memo svex-aig-memotable-p)
                                        (env svex-a4vec-env-p)
                                        (masks svex-mask-alist-p))
  (if (atom memo)
      t
    (and (or (not (mbt (consp (car memo))))
             (equal (svex->a4vec (caar memo) env masks)
                    (a4vec-fix (cdar memo))))
         (svex->a4vec-memotable-correctp (cdr memo) env masks)))
  ///
  (defthm svex->a4vec-memotable-correctp-implies-lookup
    (implies (and (svex->a4vec-memotable-correctp memo env masks)
                  (hons-assoc-equal x memo))
             (a4vec-equiv (cdr (hons-assoc-equal x memo))
                          (svex->a4vec x env masks))))

  (defthm svex->a4vec-memotable-correctp-implies-lookup-fix
    (implies (and (svex->a4vec-memotable-correctp memo env masks)
                  (hons-assoc-equal x (svex-aig-memotable-fix memo)))
             (equal (cdr (hons-assoc-equal x (svex-aig-memotable-fix memo)))
                    (svex->a4vec x env masks)))
    :hints(("Goal" :in-theory (enable svex-aig-memotable-fix))))

  (defthm svex->a4vec-memotable-correctp-of-cons
    (implies (and (svex->a4vec-memotable-correctp memo env masks)
                  (a4vec-equiv val (svex->a4vec x env masks)))
             (svex->a4vec-memotable-correctp
              (cons (cons x val) memo)
              env masks)))

  (defthm svex->a4vec-memotable-correctp-of-nil
    (svex->a4vec-memotable-correctp nil env masks))

  (local (in-theory (enable svex-aig-memotable-fix))))



(defines svex->a4vec-memo
  ;; Self-memoized version of svex-eval, for GL
  :verify-guards nil
  :ruler-extenders :all
  (define svex->a4vec-memo ((x svex-p)
                       (env svex-a4vec-env-p)
                       (masks svex-mask-alist-p)
                       (memo svex-aig-memotable-p))
    :returns (mv (res a4vec-p)
                 (memo1 svex-aig-memotable-p))
    :measure (two-nats-measure (svex-count x) 1)
    (b* ((memo (svex-aig-memotable-fix memo))
         (env (svex-a4vec-env-fix env)))
      (svex-case x
        :quote (b* ((mask (svex-mask-lookup x masks)))
                 (mv (4vec->a4vec (4vec-mask mask x.val)) memo))
        :var (mv (let ((look (hons-get x.name env))
                       (mask (svex-mask-lookup x masks)))
                   (a4vec-mask mask (if look (cdr look) (a4vec-x))))
                 memo)
        :call (b* ((x (svex-fix x))
                   (look (hons-get x memo))
                   ((when look) (mv (cdr look) memo))
                   ((mv res memo)
                    (b* (((when (svex-is-const-concat x))
                          (b* (((mv upper lower memo)
                                (svex-concat->a4vec-memo x env masks memo))
                               (mask (svex-mask-lookup x masks)))
                            (mv (a4vec-mask mask (a4vec upper lower))
                                memo)))
                         ((mv args memo) (svexlist->a4vec-memo x.args env masks memo))
                         (mask (svex-mask-lookup x masks))
                         (res (svex-apply-aig x.fn args x.args mask)))
                      (mv res memo)))
                   (memo (hons-acons x res memo)))
                (mv res memo)))))
  (define svexlist->a4vec-memo ((x svexlist-p)
                           (env svex-a4vec-env-p)
                           (masks svex-mask-alist-p)
                           (memo svex-aig-memotable-p))
    :returns (mv (res a4veclist-p)
                 (memo1 svex-aig-memotable-p))
    :measure (two-nats-measure (svexlist-count x) 0)
    (b* (((when (atom x)) (mv nil (svex-aig-memotable-fix memo)))
         ((mv first memo) (svex->a4vec-memo (car x) env masks memo))
         ((mv rest memo) (svexlist->a4vec-memo (cdr x) env masks memo)))
      (mv (cons first rest) memo)))

  (define svex-concat->a4vec-memo ((x svex-p)
                              (env svex-a4vec-env-p)
                              (masks svex-mask-alist-p)
                              (memo svex-aig-memotable-p))
    :returns (mv (upper true-listp)
                 (lower true-listp)
                 (memo1 svex-aig-memotable-p))
    :measure (two-nats-measure (svex-count x)
                               (if (svex-is-const-concat x) 0 2))
    (b* (((unless (svex-is-const-concat x))
          (b* (((mv res memo) (svex->a4vec-memo x env masks memo)))
            (mv (a4vec->upper res) (a4vec->lower res) memo)))
         ((mv width lsbs msbs)
          (svex-const-concat-args x))
         ((unless (and (2vec-p width) (natp (2vec->val width))))
          (mv (a4vec->upper (a4vec-x)) (a4vec->lower (a4vec-x))
              (svex-aig-memotable-fix memo)))
         (width (2vec->val width))
         (mask (svex-mask-lookup x masks))
         ((unless (sparseint-test-bitand (sparseint-concatenate width 0 -1) mask))
          (svex-concat->a4vec-memo lsbs env masks memo))
         ((mv upper2 lower2 memo)
          (svex-concat->a4vec-memo msbs env masks memo)))
      (svex-concat->a4vec-memo-lower lsbs width upper2 lower2 env masks memo)))

  (define svex-concat->a4vec-memo-lower ((x svex-p)
                                    (width natp)
                                    (upper-acc true-listp)
                                    (lower-acc true-listp)
                                    (env svex-a4vec-env-p)
                                    (masks svex-mask-alist-p)
                                    (memo svex-aig-memotable-p))
    :returns (mv (upper true-listp)
                 (lower true-listp)
                 (memo1 svex-aig-memotable-p))
    :measure (two-nats-measure (svex-count x)
                               (if (svex-is-const-concat x) 0 2))
    (b* ((upper-acc (llist-fix upper-acc))
         (lower-acc (llist-fix lower-acc))
         (memo (svex-aig-memotable-fix memo))
         ((When (zp width))
          (mv upper-acc lower-acc memo))
         ((unless (svex-is-const-concat x))
          (b* (((mv res memo) (svex->a4vec-memo x env masks memo)))
            (mv (aig-logapp-nss width (a4vec->upper res) upper-acc)
                (aig-logapp-nss width (a4vec->lower res) lower-acc)
                memo)))
         ((mv sub-width lsbs msbs)
          (svex-const-concat-args x))
         ((unless (and (2vec-p sub-width) (natp (2vec->val sub-width))))
          (mv (aig-logapp-nss width (a4vec->upper (a4vec-x)) upper-acc)
              (aig-logapp-nss width (a4vec->lower (a4vec-x)) lower-acc)
              (svex-aig-memotable-fix memo)))
         (sub-width (2vec->val sub-width))
         (lsbs-width (min width sub-width))
         (msbs-width (- width lsbs-width))
         ((mv upper-acc lower-acc memo)
          (svex-concat->a4vec-memo-lower msbs msbs-width upper-acc lower-acc env masks memo)))
      (svex-concat->a4vec-memo-lower lsbs lsbs-width upper-acc lower-acc env masks memo)))


  ///
  (verify-guards svex->a4vec-memo :guard-debug t)

  (local (in-theory (disable svex-concat->a4vec-lower-acc-elim)))

  (std::defret-mutual svex->a4vec-memo-correct
    (defret svex->a4vec-memo-correct
      (implies (svex->a4vec-memotable-correctp memo env masks)
               (and (equal res (svex->a4vec x env masks))
                    (svex->a4vec-memotable-correctp memo1 env masks)))
      :hints ('(:expand (<call>
                         (svex->a4vec x env masks))))
      :fn svex->a4vec-memo)
    (defret svexlist->a4vec-memo-correct
      (implies (svex->a4vec-memotable-correctp memo env masks)
               (and (equal res (svexlist->a4vec x env masks))
                    (svex->a4vec-memotable-correctp memo1 env masks)))
      :hints ('(:expand (<call>
                         (svexlist->a4vec x env masks))))
      :fn svexlist->a4vec-memo)
    (defret svex-concat->a4vec-memo-correct
      (implies (svex->a4vec-memotable-correctp memo env masks)
               (b* (((mv upper-spec lower-spec) (svex-concat->a4vec x env masks)))
                 (and (equal upper upper-spec)
                      (equal lower lower-spec)
                      (svex->a4vec-memotable-correctp memo1 env masks))))
      :hints ('(:expand (<call>
                         (svex-concat->a4vec x env masks))))
      :fn svex-concat->a4vec-memo)

    (defret svex-concat->a4vec-memo-lower-correct
      (implies (svex->a4vec-memotable-correctp memo env masks)
               (b* (((mv upper-spec lower-spec)
                     (svex-concat->a4vec-lower x width upper-acc lower-acc env masks)))
                 (and (equal upper upper-spec)
                      (equal lower lower-spec)
                      (svex->a4vec-memotable-correctp memo1 env masks))))
      :hints ('(:expand ((:free (width) <call>)
                         (:free (width)
                          (svex-concat->a4vec-lower x width upper-acc lower-acc env masks)))))
      :fn svex-concat->a4vec-memo-lower))

  (deffixequiv-mutual svex->a4vec-memo))

(define svexlist->a4vec-nrev ((x svexlist-p)
                              (env svex-a4vec-env-p)
                              (masks svex-mask-alist-p)
                              (memo svex-aig-memotable-p)
                              (acl2::nrev))
  :returns (mv (new-nrev)
               (memo1 svex-aig-memotable-p))
  (if (atom x)
      (b* ((acl2::nrev (acl2::nrev-fix acl2::nrev)))
        (mv acl2::nrev (svex-aig-memotable-fix memo)))
    (b* (((mv first memo) (svex->a4vec-memo (car x) env masks memo))
         (acl2::nrev (acl2::nrev-push first acl2::nrev)))
      (svexlist->a4vec-nrev (cdr x) env masks memo acl2::nrev)))
  ///
  (defret svexlist->a4vec-nrev-removal
    (b* (((mv out-spec memo1-spec)
          (svexlist->a4vec-memo x env masks memo)))
      (and (equal new-nrev
                  (append acl2::nrev out-spec))
           (equal memo1 memo1-spec)))
    :hints(("Goal" :induct t
            :expand ((svexlist->a4vec-memo x env masks memo))))))

(define svexlist->a4vec-top ((x svexlist-p) (env svex-a4vec-env-p) (masks svex-mask-alist-p))
  ;; note: env must be fast
  ;; :prepwork ((local (defthm svexlist->a4vec-decomp
  ;;                     (equal (list (mv-nth 0 (svexlist->a4vec x env masks memo))
  ;;                                  (mv-nth 1 (svexlist->a4vec x env masks memo)))
  ;;                            (svexlist->a4vec x env masks memo))
  ;;                     :hints (("goal" :expand ((svexlist->a4vec x env masks memo)))))))
  :enabled t
  (mbe :logic (svexlist->a4vec x env masks)
       :exec
       (b* (((mv res memo)
             (with-local-stobj acl2::nrev
               (mv-let (res memo acl2::nrev)
                 (b* (((mv acl2::nrev memo)
                       (svexlist->a4vec-nrev x env masks nil acl2::nrev))
                      ((mv res acl2::nrev) (acl2::nrev-finish acl2::nrev)))
                   (mv res memo acl2::nrev))
                 (mv res memo)))))
         (fast-alist-free memo)
         res)))


;; There are a few possible approaches to generating the a4vec-env to use in
;; building AIGs.  Basically, we're going to generate a pair of Boolean
;; variables for each bit that matters (mask-wise) in x; the masks for the
;; variables of x must be finite so that we can determine which bits matter.
;; (The don't-care bits will be assigned X.)
;; But there are still a few options:

;; 1. Always assign AIG variables to every care bit of every variable.  This
;; has the advantage that the input and output to svexlist->a4vec is always
;; identical for a given svexlist, so we can memoize, which may improve
;; performance if we run several simulations with the same svex but different
;; environments.  But the complete set of variables might be overkill,
;; e.g. svtvs have lots of variables for don't-care inputs and initial
;; states.

;; 2. Assign AIG variables to the care bits of all the variables bound in the
;; environment.  This could still allow good memoization as long as the same
;; variables are going to be assigned basically all the time.  We can extract
;; and sort the variables so that the order of the bindings doesn't matter.

;; 3. In between 1 and 2: Take a list of variables as an extra argument,
;; ignored in the logic, which should be a superset of the variables in the
;; environment; only generate AIG vars for these variables.  This care list
;; could be provided e.g. by the SVTV.  This has the advantage over 2 that
;; memoization still works if different subsets of the care variables are
;; used in different runs.

;; The implementations of 1,2,3 would be quite similar and could basically
;; all be based on 3.

;; 4. More extreme than 2, more difficult to implement, and little chance of
;; memoization working: in the symbolic environment provided, we only really
;; need AIG variables for non-constant bits.  So ignore masks and just
;; produce an a4vec environment that replicates the constants assigned in env
;; and generates AIG variables for the non-constant bits.  This would mean
;; we'd need to get a hold of the symbolic environment, which probably would
;; mean we'd need a symbolic counterpart function, not just an alternate
;; definition.


;; The following implements option 3 above.  We provide the svexlist and the
;; list of care vars.  The function returns the a4veclist and the a4vec-env.

(define nat-bool-listp (x)
  (if (atom x)
      (eq x nil)
    (and (or (natp (car x))
             (booleanp (car x)))
         (nat-bool-listp (cdr x))))
  ///
  (defthm nat-bool-listp-of-aig-sterm
    (implies (or (booleanp x) (natp x))
             (nat-bool-listp (aig-sterm x)))
    :hints(("Goal" :in-theory (enable gl::bfr-sterm))))

  (defthm nat-bool-listp-of-aig-scons
    (implies (and (or (booleanp x) (natp x))
                  (nat-bool-listp y))
             (nat-bool-listp (aig-scons x y)))
    :hints(("Goal" :in-theory (enable gl::bfr-scons))))

  (defthm nat-bool-listp-of-list-fix
    (implies (nat-bool-listp x)
             (nat-bool-listp (list-fix x)))))

(define nat-bool-list-nats ((x nat-bool-listp))
  :prepwork ((local (in-theory (enable nat-bool-listp))))
  (if (atom x)
      nil
    (if (booleanp (car x))
        (nat-bool-list-nats (cdr x))
      (cons (lnfix (car x))
            (nat-bool-list-nats (cdr x)))))
  ///
  (defthm nat-bool-list-nats-of-list-fix
    (equal (nat-bool-list-nats (list-fix x))
           (nat-bool-list-nats x)))

  (defthm nat-bool-list-nats-of-aig-sterm
    (equal (nat-bool-list-nats (aig-sterm x))
           (if (booleanp x)
               nil
             (list (nfix x))))
    :hints(("Goal" :in-theory (enable gl::bfr-sterm))))

  (defthm nat-bool-list-nats-of-aig-scons-bool
    (implies (booleanp x)
             (equal (nat-bool-list-nats (aig-scons x y))
                    (nat-bool-list-nats y)))
    :hints(("Goal" :in-theory (enable gl::bfr-scons))))

  (defthm nat-bool-list-nats-of-aig-scons-nat
    (implies (and (natp x)
                  (not (member x (nat-bool-list-nats y))))
             (equal (nat-bool-list-nats (aig-scons x y))
                    (cons x (nat-bool-list-nats y))))
    :hints(("Goal" :in-theory (enable gl::bfr-scons)))))

(define nat-bool-list-lower-boundp ((bound natp) (x nat-bool-listp))
  :prepwork ((local (in-theory (enable nat-bool-listp))))
  (if (atom x)
      t
    (and (or (booleanp (car x))
             (<= (lnfix bound) (lnfix (car x))))
         (nat-bool-list-lower-boundp bound (cdr x))))
  ///
  (defthm nat-bool-list-lower-boundp-of-list-fix
    (equal (nat-bool-list-lower-boundp bound (list-fix x))
           (nat-bool-list-lower-boundp bound x)))

  (defthm nat-bool-list-nonmember-by-lower-bound
    (implies (and (nat-bool-list-lower-boundp bound x)
                  (< v (nfix bound))
                  (nat-bool-listp x))
             (not (member v (nat-bool-list-nats x))))
    :hints(("Goal" :in-theory (enable nat-bool-list-nats))))

  (Defthm nat-bool-list-lower-boundp-lower
    (implies (and (nat-bool-list-lower-boundp bound x)
                  (<= (nfix n) (nfix bound)))
             (nat-bool-list-lower-boundp n x))))

(define nat-bool-list-upper-boundp ((bound natp) (x nat-bool-listp))
  :prepwork ((local (in-theory (enable nat-bool-listp))))
  (if (atom x)
      t
    (and (or (booleanp (car x))
             (< (lnfix (car x)) (lnfix bound)))
         (nat-bool-list-upper-boundp bound (cdr x))))
  ///
  (defthm nat-bool-list-upper-boundp-of-list-fix
    (equal (nat-bool-list-upper-boundp bound (list-fix x))
           (nat-bool-list-upper-boundp bound x)))

  (defthm nat-bool-list-nonmember-by-upper-bound
    (implies (and (nat-bool-list-upper-boundp bound x)
                  (<= (nfix bound) v)
                  (nat-bool-listp x))
             (not (member v (nat-bool-list-nats x))))
    :hints(("Goal" :in-theory (enable nat-bool-list-nats))))

  (defthm nat-bool-list-no-intersection-by-bounds
    (implies (and (nat-bool-list-upper-boundp bound0 x0)
                  (nat-bool-list-lower-boundp bound1 x1)
                  (<= (nfix bound0) (nfix bound1))
                  (nat-bool-listp x0)
                  (nat-bool-listp x1))
             (not (intersectp (nat-bool-list-nats x0)
                              (nat-bool-list-nats x1))))
    :hints(("Goal" :in-theory (e/d (intersectp-equal
                                    nat-bool-listp
                                    nat-bool-list-nats)
                                   (acl2::intersectp-equal-commute)))))

  (Defthm nat-bool-list-upper-boundp-higher
    (implies (and (nat-bool-list-upper-boundp bound x)
                  (<= (nfix bound) (nfix n)))
             (nat-bool-list-upper-boundp n x))))


(define nat-bool-a4vec-p ((x a4vec-p))
  (b* (((a4vec x) x))
    (and (nat-bool-listp x.upper)
         (nat-bool-listp x.lower)))
  ///
  (deffixtype nba4vec :pred nat-bool-a4vec-p! :fix a4vec-fix :equiv a4vec-equiv))

(defmacro nat-bool-a4vec-p! (x)
  `(and (a4vec-p ,x)
        (nat-bool-a4vec-p ,x)))

(define nat-bool-a4vec-vars ((x nat-bool-a4vec-p!))
  :prepwork ((local (in-theory (enable nat-bool-a4vec-p))))
  (b* (((a4vec x) x))
    (append (nat-bool-list-nats x.upper)
            (nat-bool-list-nats x.lower))))

(define nat-bool-a4vec-lower-boundp ((bound natp) (x nat-bool-a4vec-p!))
  :prepwork ((local (in-theory (enable nat-bool-a4vec-p))))
  (b* (((a4vec x) x))
    (and (nat-bool-list-lower-boundp bound x.upper)
         (nat-bool-list-lower-boundp bound x.lower)))
  ///
  (defthm nat-bool-a4vec-vars-nonmember-by-lower-bound
    (implies (and (nat-bool-a4vec-lower-boundp bound x)
                  (< v (nfix bound))
                  (nat-bool-a4vec-p x))
             (not (member v (nat-bool-a4vec-vars x))))
    :hints(("Goal" :in-theory (enable nat-bool-a4vec-vars
                                      nat-bool-a4vec-p
                                      nat-bool-list-nonmember-by-lower-bound))))

  (Defthm nat-bool-a4vec-lower-boundp-lower
    (implies (and (nat-bool-a4vec-lower-boundp bound x)
                  (<= (nfix n) (nfix bound)))
             (nat-bool-a4vec-lower-boundp n x))))

(define nat-bool-a4vec-upper-boundp ((bound natp) (x nat-bool-a4vec-p!))
  :prepwork ((local (in-theory (enable nat-bool-a4vec-p))))
  (b* (((a4vec x) x))
    (and (nat-bool-list-upper-boundp bound x.upper)
         (nat-bool-list-upper-boundp bound x.lower)))
  ///
  (defthm nat-bool-a4vec-vars-nonmember-by-upper-bound
    (implies (and (nat-bool-a4vec-upper-boundp bound x)
                  (<= (nfix bound) v)
                  (nat-bool-a4vec-p x))
             (not (member v (nat-bool-a4vec-vars x))))
    :hints(("Goal" :in-theory (enable nat-bool-a4vec-vars
                                      nat-bool-a4vec-p
                                      nat-bool-list-nonmember-by-upper-bound))))

  (defthm nat-bool-a4vec-no-intersection-by-bounds
    (implies (and (nat-bool-a4vec-upper-boundp bound0 x0)
                  (nat-bool-a4vec-lower-boundp bound1 x1)
                  (<= (nfix bound0) (nfix bound1))
                  (nat-bool-a4vec-p x0)
                  (nat-bool-a4vec-p x1))
             (not (intersectp (nat-bool-a4vec-vars x0)
                              (nat-bool-a4vec-vars x1))))
    :hints(("Goal" :in-theory (e/d (intersectp-equal
                                    nat-bool-a4vec-p
                                    nat-bool-a4vec-vars
                                    nat-bool-a4vec-upper-boundp
                                    nat-bool-a4vec-lower-boundp)
                                   (acl2::intersectp-equal-commute)))))

  (Defthm nat-bool-a4vec-upper-boundp-higher
    (implies (and (nat-bool-a4vec-upper-boundp bound x)
                  (<= (nfix bound) (nfix n)))
             (nat-bool-a4vec-upper-boundp n x))))


(define nat-bool-a4env-p ((x svex-a4vec-env-p))
  :prepwork ((local (in-theory (enable svex-a4vec-env-fix))))
  (if (atom x)
      t
    (and (if (mbt (consp (car x)))
             (nat-bool-a4vec-p (cdar x))
           t)
         (nat-bool-a4env-p (cdr x))))
  ///
  (deffixtype nba4env :pred nat-bool-a4env-p! :fix svex-a4vec-env-fix :equiv svex-a4vec-env-equiv))

(defmacro nat-bool-a4env-p! (x)
  `(and (svex-a4vec-env-p ,x)
        (nat-bool-a4env-p ,x)))

(define nat-bool-a4env-vars ((x nat-bool-a4env-p!))
  :prepwork ((local (in-theory (enable nat-bool-a4env-p
                                       svex-a4vec-env-fix))))
  (if (atom x)
      nil
    (append (and (mbt (consp (car x)))
                 (nat-bool-a4vec-vars (cdar x)))
            (nat-bool-a4env-vars (cdr x)))))

(define nat-bool-a4env-lower-boundp ((bound natp) (x nat-bool-a4env-p!))
  :prepwork ((local (in-theory (enable nat-bool-a4env-p
                                       svex-a4vec-env-fix))))
  (if (atom x)
      t
    (and (if (mbt (consp (car x)))
             (nat-bool-a4vec-lower-boundp bound (cdar x))
           t)
         (nat-bool-a4env-lower-boundp bound (cdr x))))
  ///
  (defthm nat-bool-a4env-vars-nonmember-by-lower-bound
    (implies (and (nat-bool-a4env-lower-boundp bound x)
                  (< v (nfix bound))
                  (nat-bool-a4env-p x))
             (not (member v (nat-bool-a4env-vars x))))
    :hints(("Goal" :in-theory (enable nat-bool-a4env-vars
                                      nat-bool-a4env-p
                                      nat-bool-list-nonmember-by-lower-bound))))

  (Defthm nat-bool-a4env-lower-boundp-lower
    (implies (and (nat-bool-a4env-lower-boundp bound x)
                  (<= (nfix n) (nfix bound)))
             (nat-bool-a4env-lower-boundp n x))))

(define nat-bool-a4env-upper-boundp ((bound natp) (x nat-bool-a4env-p!))
  :prepwork ((local (in-theory (enable nat-bool-a4env-p
                                       svex-a4vec-env-fix))))
  (if (atom x)
      t
    (and (if (mbt (consp (car x)))
             (nat-bool-a4vec-upper-boundp bound (cdar x))
           t)
         (nat-bool-a4env-upper-boundp bound (cdr x))))
  ///
  (defthm nat-bool-a4env-vars-nonmember-by-upper-bound
    (implies (and (nat-bool-a4env-upper-boundp bound x)
                  (<= (nfix bound) v)
                  (nat-bool-a4env-p x))
             (not (member v (nat-bool-a4env-vars x))))
    :hints(("Goal" :in-theory (enable nat-bool-a4env-vars
                                      nat-bool-a4env-p
                                      nat-bool-list-nonmember-by-upper-bound))))

  (defthm nat-bool-a4vec/env-no-intersection-by-bounds
    (implies (and (nat-bool-a4vec-upper-boundp bound0 x0)
                  (nat-bool-a4env-lower-boundp bound1 x1)
                  (<= (nfix bound0) (nfix bound1))
                  (nat-bool-a4vec-p x0)
                  (nat-bool-a4env-p x1))
             (not (intersectp (nat-bool-a4vec-vars x0)
                              (nat-bool-a4env-vars x1))))
    :hints(("Goal" :in-theory (e/d (intersectp-equal
                                    nat-bool-a4env-p
                                    nat-bool-a4env-lower-boundp)
                                   (acl2::intersectp-equal-commute))
            :expand ((nat-bool-a4env-vars x1))
            :induct (nat-bool-a4env-lower-boundp bound1 x1))))

  (defthm nat-bool-a4env-no-intersection-by-bounds
    (implies (and (nat-bool-a4env-upper-boundp bound0 x0)
                  (nat-bool-a4env-lower-boundp bound1 x1)
                  (<= (nfix bound0) (nfix bound1))
                  (nat-bool-a4env-p x0)
                  (nat-bool-a4env-p x1))
             (not (intersectp (nat-bool-a4env-vars x0)
                              (nat-bool-a4env-vars x1))))
    :hints(("Goal" :in-theory (e/d (intersectp-equal
                                    nat-bool-a4env-p
                                    nat-bool-a4env-vars
                                    nat-bool-a4env-upper-boundp
                                    nat-bool-a4env-lower-boundp)
                                   (acl2::intersectp-equal-commute)))))

  (defthm nat-bool-a4env-a4vec-no-intersection-by-bounds
    (implies (and (nat-bool-a4env-upper-boundp bound0 x0)
                  (nat-bool-a4vec-lower-boundp bound1 x1)
                  (<= (nfix bound0) (nfix bound1))
                  (nat-bool-a4env-p x0)
                  (nat-bool-a4vec-p x1))
             (not (intersectp (nat-bool-a4env-vars x0)
                              (nat-bool-a4vec-vars x1))))
    :hints(("Goal" :in-theory (e/d (intersectp-equal
                                    nat-bool-a4env-p
                                    nat-bool-a4env-vars
                                    nat-bool-a4env-upper-boundp
                                    nat-bool-a4env-lower-boundp)
                                   (acl2::intersectp-equal-commute)))))

  (Defthm nat-bool-a4env-upper-boundp-higher
    (implies (and (nat-bool-a4env-upper-boundp bound x)
                  (<= (nfix bound) (nfix n)))
             (nat-bool-a4env-upper-boundp n x))))




(local (defthm logcount-of-logand
         (implies (natp y)
                  (<= (logcount (logand x y))
                      (logcount y)))
         :hints(("Goal" :in-theory (e/d* (bitops::logcount**
                                          bitops::logand**
                                          bitops::ihsext-inductions))))
         :rule-classes :linear))

(define sparseint-nfix ((x sparseint-p))
  :guard (not (sparseint-< x 0))
  :returns (new-x sparseint-p)
  :inline t
  (mbe :logic (if (sparseint-< x 0) 0 (sparseint-fix x))
       :exec x)
  ///
  (defret <fn>-correct
    (equal (sparseint-val new-x) (nfix (sparseint-val x)))))

(define 4vmask-to-a4vec-varcount ((mask 4vmask-p) (boolmask integerp))
  :guard (not (sparseint-< mask 0))
  :returns (count natp :rule-classes :type-prescription)
  (b* ((mask (sparseint-nfix (4vmask-fix mask))))
    (- (* 2 (sparseint-bitcount mask))
       (sparseint-bitcount (sparseint-bitand mask (int-to-sparseint boolmask))))))

(local (defcong sparseint-equal sparseint-equal (sparseint-nfix x) 1))

(local (defthm integer-length-posp
         (implies (posp x)
                  (posp (integer-length x)))
         :hints(("Goal" :in-theory (enable* ihsext-recursive-redefs
                                            ihsext-inductions)))
         :rule-classes :type-prescription))

(define 4vmask-to-a4vec-rec ((mask 4vmask-p) (boolmask integerp) (nextvar natp))
  :guard (not (sparseint-< mask 0))
  :returns (mv (upper nat-bool-listp)
               (lower nat-bool-listp))
  :verify-guards nil
  :measure (sparseint-length (sparseint-nfix mask))
  :hints(("Goal" :in-theory (enable bitops::integer-length**
                                    4vmask-fix)))
  (b* ((mask (sparseint-nfix (4vmask-fix mask)))
       (nextvar (lnfix nextvar))
       ((when (sparseint-equal mask 0))
        (mv (aig-sterm t) (aig-sterm nil)))
       ((mv ubit0 ubit1 nextvar)
        (if (eql 1 (sparseint-bit 0 mask))
            (if (logbitp 0 boolmask)
                (mv nextvar nextvar (+ 1 nextvar))
              (mv nextvar (1+ nextvar) (+ 2 nextvar)))
          (mv t nil nextvar)))
       ((mv rest-upper rest-lower)
        (4vmask-to-a4vec-rec (sparseint-rightshift 1 mask) (logcdr boolmask) nextvar)))
    (mv (aig-scons ubit0 rest-upper)
        (aig-scons ubit1 rest-lower)))
  ///
  ;; (defthm 4vmask-to-a4vec-rec-nextvar
  ;;   (equal (mv-nth 2 (4vmask-to-a4vec-rec mask nextvar))
  ;;          (+ (* 2 (logcount (nfix mask))) (nfix nextvar)))
  ;;   :hints(("Goal" :in-theory (enable bitops::logcount**))))

  (defret true-listp-of-<fn>-upper
    (true-listp upper)
    :rule-classes :type-prescription)
  (defret true-listp-of-<fn>-lower
    (true-listp lower)
    :rule-classes :type-prescription)

  (verify-guards 4vmask-to-a4vec-rec)

  (defthm 4vmask-to-a4vec-rec-lower-bounds
    (and (nat-bool-list-lower-boundp nextvar (mv-nth 0 (4vmask-to-a4vec-rec mask boolmask nextvar)))
         (nat-bool-list-lower-boundp nextvar (mv-nth 1 (4vmask-to-a4vec-rec mask boolmask nextvar))))
    :hints(("Goal" :in-theory (enable nat-bool-list-lower-boundp gl::bfr-scons)))
    :rule-classes ((:forward-chaining :trigger-terms ((4vmask-to-a4vec-rec mask boolmask nextvar)))))

  (defthm 4vmask-to-a4vec-rec-upper-bounds
    (and (nat-bool-list-upper-boundp (+ (nfix nextvar)
                                        (4vmask-to-a4vec-varcount mask boolmask))
                                     (mv-nth 0 (4vmask-to-a4vec-rec mask boolmask nextvar)))
         (nat-bool-list-upper-boundp (+ (nfix nextvar)
                                        (4vmask-to-a4vec-varcount mask boolmask))
                                     (mv-nth 1 (4vmask-to-a4vec-rec mask boolmask nextvar))))
    :hints(("Goal" :in-theory (enable gl::bfr-scons
                                      4vmask-to-a4vec-varcount
                                      bitops::logand**
                                      bitops::logbitp**
                                      bitops::logcount**)
            :induct (4vmask-to-a4vec-rec mask boolmask nextvar)
            :expand ((:free (bound a b) (nat-bool-list-upper-boundp bound (cons a b)))
                     (:free (bound) (nat-bool-list-upper-boundp bound nil))
                     (:free (x) (logtail 1 x)))
            :do-not-induct t))
    :rule-classes ((:forward-chaining :trigger-terms ((4vmask-to-a4vec-rec mask boolmask nextvar)))))

  ;; (defthm 4vmask-to-a4vec-rec-no-duplicate-vars
  ;;   (b* (((mv upper lower)
  ;;         (4vmask-to-a4vec-rec mask boolmask nextvar)))
  ;;     (and (no-duplicatesp (nat-bool-list-nats upper))
  ;;          (no-duplicatesp (nat-bool-list-nats lower))
  ;;          (not (intersectp (nat-bool-list-nats upper)
  ;;                           (nat-bool-list-nats lower)))))
  ;;   :hints(("Goal" :in-theory (enable nat-bool-list-nats
  ;;                                     intersectp-equal))))

  (defthm member-4vmask-to-a4vec-rec-vars
    ;; not a good rewrite rule but useful for the next phase
    (iff (member v (append (nat-bool-list-nats (mv-nth 0 (4vmask-to-a4vec-rec mask boolmask nextvar)))
                           (nat-bool-list-nats (mv-nth 1 (4vmask-to-a4vec-rec mask boolmask nextvar)))))
         (and (natp v)
              (<= (nfix nextvar) v)
              (< v (+ (nfix nextvar)
                      (4vmask-to-a4vec-varcount mask boolmask)))))
    :hints(("Goal" :in-theory (enable nat-bool-list-nats
                                      4vmask-to-a4vec-varcount
                                      bitops::logand**
                                      bitops::logcount**
                                      bitops::logbitp**)
            :induct (4vmask-to-a4vec-rec mask boolmask nextvar))
           (and stable-under-simplificationp
                '(:expand ((logcount (sparseint-val (4vmask-fix mask)))
                           (:free (x) (logtail 1 x))))))
    :rule-classes nil))

  ;; (defthm eval-4vmask-to-a4vec-rec-cons-greater
  ;;   (b* (((mv ?err upper lower nextvar1)
  ;;         (4vmask-to-a4vec-rec mask nextvar)))
  ;;     (implies (<= nextvar1 var)
  ;;              (and (equal (aig-list->s upper (cons (cons var val) env))
  ;;                          (aig-list->s upper env))
  ;;                   (equal (aig-list->s lower (cons (cons var val) env))
  ;;                          (aig-list->s lower env))))))

  ;; (defthm eval-4vmask-to-a4vec-rec-cons-lesser
  ;;   (b* (((mv ?err upper lower ?nextvar1)
  ;;         (4vmask-to-a4vec-rec mask nextvar)))
  ;;     (implies (< var (nfix nextvar))
  ;;              (and (equal (aig-list->s upper (cons (cons var val) env))
  ;;                          (aig-list->s upper env))
  ;;                   (equal (aig-list->s lower (cons (cons var val) env))
  ;;                          (aig-list->s lower env)))))))

(define 4vmask-to-a4vec-rec-env ((mask 4vmask-p)
                                 (boolmask integerp)
                                 (upper integerp)
                                 (lower integerp)
                                 (nextvar natp))
  :guard (not (sparseint-< mask 0))
  :returns (env "environment for the resulting 4vmask")
  :measure (sparseint-length (sparseint-nfix (4vmask-fix mask)))
  :hints(("Goal" :in-theory (enable bitops::integer-length**
                                    4vmask-fix)))
  (b* ((mask (sparseint-nfix (4vmask-fix mask)))
       (nextvar (lnfix nextvar))
       ((when (sparseint-equal mask 0)) nil)
       (rest-env
        (4vmask-to-a4vec-rec-env (sparseint-rightshift 1 mask)
                                 (logcdr boolmask)
                                 (logcdr upper)
                                 (logcdr lower)
                                 (if (eql 1 (sparseint-bit 0 mask))
                                     (if (logbitp 0 boolmask)
                                         (+ 1 nextvar)
                                       (+ 2 nextvar))
                                   nextvar))))
    (if (eql 1 (sparseint-bit 0 mask))
        (cons (cons nextvar (logbitp 0 upper))
              (if (logbitp 0 boolmask)
                  rest-env
                (cons (cons (1+ nextvar) (logbitp 0 lower))
                      rest-env)))
      rest-env))
  ///

  (defthm key-exists-in-4vmask-to-a4vec-rec-env
    (iff (hons-assoc-equal v (4vmask-to-a4vec-rec-env mask boolmask upper lower nextvar))
         (and (natp v)
              (<= (nfix nextvar) v)
              (< v (+ (nfix nextvar)
                      (4vmask-to-a4vec-varcount mask boolmask)))))
    :hints(("Goal" :in-theory (enable bitops::logcount**
                                      bitops::logbitp**
                                      4vmask-to-a4vec-varcount
                                      bitops::logand**)
            :do-not-induct t
            :induct (4vmask-to-a4vec-rec-env mask boolmask upper lower nextvar))
           (and stable-under-simplificationp
                '(:expand ((:free (x) (logtail 1 x))
                           (logcount (sparseint-val (4vmask-fix mask))))))))

  (defthm nat-bool-aig-list->s-of-cons-nonmember
    (implies (and (nat-bool-listp x)
                  (not (member n (nat-bool-list-nats x))))
             (equal (aig-list->s x (cons (cons n v) env))
                    (aig-list->s x env)))
    :hints(("Goal" :in-theory (enable aig-list->s nat-bool-listp
                                      nat-bool-list-nats
                                      gl::scdr
                                      gl::s-endp)
            :induct (aig-list->s x env)
            :expand ((:Free (env) (aig-list->s x env))))))

  (local (defthm equal-nfix-plus-1
           (not (equal x (+ 1 (nfix x))))
           :hints(("Goal" :in-theory (enable nfix)))))

  (defthm eval-4vmask-to-a4vec-rec-with-env
    (b* (((mv uppera lowera)
          (4vmask-to-a4vec-rec mask boolmask nextvar))
         (env
          (4vmask-to-a4vec-rec-env mask boolmask upper lower nextvar)))
      (and (equal (logand (nfix (sparseint-val (4vmask-fix mask))) (aig-list->s uppera env))
                  (logand (nfix (sparseint-val (4vmask-fix mask))) upper))
           (implies (eql 0 (logand boolmask (logxor upper lower)))
                    (equal (logand (nfix (sparseint-val (4vmask-fix mask))) (aig-list->s lowera env))
                           (logand (nfix (sparseint-val (4vmask-fix mask))) lower)))))
    :hints(("Goal" :in-theory (enable 4vmask-to-a4vec-rec
                                      bitops::logand**
                                      bitops::logxor**
                                      bitops::logbitp**
                                      4vmask-fix)
            :induct (4vmask-to-a4vec-rec-env mask boolmask upper lower nextvar)
            :expand ((:free (x) (logtail 1 x))))
           (and stable-under-simplificationp
                '(:in-theory (enable bitops::b-xor)))
           (and stable-under-simplificationp
                '(:in-theory (enable nfix))))))

(define 4vec-boolmaskp ((x 4vec-p) (mask integerp))
  (b* (((4vec x) x))
    (eql 0 (logand mask (logxor x.upper x.lower)))))

(define 4vmask-to-a4vec ((mask 4vmask-p) (boolmask integerp) (nextvar natp))
  :guard (not (sparseint-< mask 0))
  :returns (res nat-bool-a4vec-p!
                :hints(("Goal" :in-theory (enable nat-bool-a4vec-p))))
  :prepwork ((local (defthm true-listp-when-nat-bool-listp
                      (implies (nat-bool-listp x)
                               (true-listp x))
                      :hints(("Goal" :in-theory (enable nat-bool-listp))))))
  (b* (((mv upper lower)
        (4vmask-to-a4vec-rec mask boolmask nextvar)))
    (a4vec upper lower))
  ///
  ;; (defthm 4vmask-to-a4vec-nextvar
  ;;   (equal (mv-nth 1 (4vmask-to-a4vec mask nextvar))
  ;;          (+ (* 2 (logcount (nfix mask))) (nfix nextvar))))

  (defthm member-vars-of-4vmask-to-a4vec
    (iff (member v (nat-bool-a4vec-vars (4vmask-to-a4vec mask boolmask nextvar)))
         (and (natp v)
              (<= (nfix nextvar) v)
              (< v (+ (nfix nextvar) (4vmask-to-a4vec-varcount mask boolmask)))))
    :hints (("goal" :use member-4vmask-to-a4vec-rec-vars
             :in-theory (enable nat-bool-a4vec-vars))))

  (defthm 4vmask-to-a4vec-lower-bounds
    (nat-bool-a4vec-lower-boundp nextvar (4vmask-to-a4vec mask boolmask nextvar))
    :hints(("Goal" :in-theory (enable nat-bool-a4vec-lower-boundp)))
    :rule-classes ((:forward-chaining :trigger-terms ((4vmask-to-a4vec mask boolmask nextvar)))))

  (defthm 4vmask-to-a4vec-upper-bounds
    (nat-bool-a4vec-upper-boundp (+ (nfix nextvar) (4vmask-to-a4vec-varcount mask boolmask))
                                 (4vmask-to-a4vec mask boolmask nextvar))
    :hints(("Goal" :in-theory (enable nat-bool-a4vec-upper-boundp)))
    :rule-classes ((:forward-chaining :trigger-terms ((4vmask-to-a4vec mask boolmask nextvar))))))


(define 4vmask-to-a4vec-env ((mask 4vmask-p) (boolmask integerp) (val 4vec-p) (nextvar natp))
  :guard (not (sparseint-< mask 0))
  :returns env
  :prepwork ((local (defthm true-listp-when-nat-bool-listp
                      (implies (nat-bool-listp x)
                               (true-listp x))
                      :hints(("Goal" :in-theory (enable nat-bool-listp))))))
  (4vmask-to-a4vec-rec-env mask boolmask (4vec->upper val) (4vec->lower val) nextvar)
  ///

  (defthm key-exists-in-4vmask-to-a4vec-env
    (iff (hons-assoc-equal v (4vmask-to-a4vec-env mask boolmask val nextvar))
         (and (natp v)
              (<= (nfix nextvar) v)
              (< v (+ (nfix nextvar) (4vmask-to-a4vec-varcount mask boolmask))))))

  (local (defthm mask-lemma
           (IMPLIES
            (AND
             (EQUAL (LOGAND mask a)
                    (LOGAND b mask)))
            (EQUAL (LOGIOR b (lognot mask))
                   (LOGIOR (LOGNOT mask) a)))
     :hints ((bitops::logbitp-reasoning))))

  (defthm eval-4vmask-to-a4vec-with-env
    (b* ((vala (4vmask-to-a4vec mask boolmask nextvar))
         (env (4vmask-to-a4vec-env mask boolmask val nextvar)))
      (implies (and (4vec-boolmaskp val boolmask)
                    (4vmask-p mask)
                    (natp (sparseint-val mask)))
               (equal (4vec-mask mask (a4vec-eval vala env))
                      (4vec-mask mask val))))
    :hints(("Goal" :in-theory (e/d (4vmask-to-a4vec
                                    4vec-boolmaskp
                                      4vmask-fix
                                      4vec-mask
                                      a4vec-eval)
                                   (eval-4vmask-to-a4vec-rec-with-env))
            :use ((:instance eval-4vmask-to-a4vec-rec-with-env
                   (upper (4vec->upper val))
                   (lower (4vec->lower val)))))
           ;; (bitops::logbitp-reasoning)
           ;; (and stable-under-simplificationp
           ;;      '(:bdd (:vars nil)))
           ))

  ;; (defthm eval-4vmask-to-a4vec-with-env-mask-natp
  ;;   (b* ((vala (4vmask-to-a4vec mask boolmask nextvar))
  ;;        (env (4vmask-to-a4vec-env mask boolmask val nextvar)))
  ;;     (implies (and (4vec-boolmaskp val boolmask))
  ;;              (equal (4vec-mask mask (a4vec-eval vala env))
  ;;                     (4vec-mask mask val))))
  ;;   :hints (("Goal" :use eval-4vmask-to-a4vec-with-env
  ;;            :in-theory (disable eval-4vmask-to-a4vec-with-env))))
  )




(local (in-theory (disable PICK-A-POINT-SUBSET-STRATEGY)))



(define svex-maskbits-for-vars ((vars svarlist-p)
                                (masks svex-mask-alist-p)
                                (boolmasks svar-boolmasks-p))
  :prepwork ((local (in-theory (enable svarlist-p svarlist-fix))))
  :returns (incr natp :rule-classes :type-prescription)
  (b* (((when (atom vars)) 0)
       (mask (svex-mask-lookup (svex-var (car vars)) masks))
       (boolmask (svar-boolmasks-lookup (car vars) boolmasks))
       ((when (sparseint-< mask 0)) 0))
    (+ (4vmask-to-a4vec-varcount mask boolmask)
       (svex-maskbits-for-vars (cdr vars) masks boolmasks))))

(define svex-maskbits-ok ((vars svarlist-p)
                          (masks svex-mask-alist-p))
  :prepwork ((local (in-theory (enable svarlist-p svarlist-fix))))
  (b* (((when (atom vars)) t)
       (mask (svex-mask-lookup (svex-var (car vars)) masks))
       ((when (sparseint-< mask 0)) nil))
    (svex-maskbits-ok (cdr vars) masks)))

(define svex-varmasks->a4env-rec ((vars svarlist-p)
                                  (masks svex-mask-alist-p)
                                  (boolmasks svar-boolmasks-p)
                                  (nextvar natp)
                                  (acc nat-bool-a4env-p!))
  :prepwork ((local (in-theory (enable svarlist-p svarlist-fix
                                       nat-bool-a4env-p
                                       svex-mask-alist-fix
                                       svex-a4vec-env-fix))))
  :returns (mv (err "some mask was negative"
                    (iff err (not (svex-maskbits-ok vars masks)))
                    :hints(("Goal" :in-theory (enable svex-maskbits-ok))))
               (a4env nat-bool-a4env-p! :hyp (nat-bool-a4env-p! acc))
               (nextvar1 (equal nextvar1 (+ (nfix nextvar)
                                            (svex-maskbits-for-vars vars masks boolmasks)))

                         :hints(("Goal" :in-theory (enable svex-maskbits-for-vars)))))
  (b* ((acc (svex-a4vec-env-fix acc))
       ((when (atom vars))
        (mv nil acc (lnfix nextvar)))
       (mask (svex-mask-lookup (svex-var (car vars)) masks))
       ((when (sparseint-< mask 0))
        (mv (msg "Negative mask: ~x0~%" (svar-fix (car vars))) acc (lnfix nextvar)))
       (boolmask (svar-boolmasks-lookup (car vars) boolmasks))
       (a4vec (4vmask-to-a4vec mask boolmask nextvar))
       (nextvar (+ (lnfix nextvar)
                   (4vmask-to-a4vec-varcount mask boolmask))))
    (svex-varmasks->a4env-rec
     (cdr vars) masks boolmasks nextvar (cons (cons (svar-fix (car vars)) a4vec)
                                    acc)))
  ///

  (local (defun-sk svex-varmasks->a4env-rec-accumulator-elim-correct (vars masks boolmasks nextvar)
           (forall acc
                   (implies (syntaxp (not (equal acc ''nil)))
                            (b* (((mv err1 a4env1 nextvar1)
                                  (svex-varmasks->a4env-rec vars masks boolmasks nextvar acc))
                                 ((mv err2 a4env2 nextvar2)
                                  (svex-varmasks->a4env-rec vars masks boolmasks nextvar nil)))
                              (and (equal err1 err2)
                                   (equal a4env1 (append a4env2 (svex-a4vec-env-fix acc)))
                                   (equal nextvar1 nextvar2)))))
           :rewrite :direct))
  (local (in-theory (disable svex-varmasks->a4env-rec-accumulator-elim-correct)))
  (local (defthmd svex-varmasks->a4env-rec-accumulator-elim-lemma
           (svex-varmasks->a4env-rec-accumulator-elim-correct vars masks boolmasks nextvar)
    :hints (("goal" :induct (svex-varmasks->a4env-rec
                             vars masks boolmasks nextvar acc))
            (and stable-under-simplificationp
                 `(:expand (,(car (last clause))
                            (:free (acc)
                             (svex-varmasks->a4env-rec
                              vars masks boolmasks nextvar acc))))))))

  (defthmd svex-varmasks->a4env-rec-accumulator-elim
    (implies (syntaxp (not (equal acc ''nil)))
             (b* (((mv err1 a4env1 nextvar1)
                   (svex-varmasks->a4env-rec vars masks boolmasks nextvar acc))
                  ((mv err2 a4env2 nextvar2)
                   (svex-varmasks->a4env-rec vars masks boolmasks nextvar nil)))
               (and (equal err1 err2)
                    (equal a4env1 (append a4env2 (svex-a4vec-env-fix acc)))
                    (equal nextvar1 nextvar2))))
    :hints (("goal" :use svex-varmasks->a4env-rec-accumulator-elim-lemma)))

  (defthm member-vars-of-svex-varmasks->a4env-rec
    (iff (member v (nat-bool-a4env-vars
                    (mv-nth 1 (svex-varmasks->a4env-rec vars masks boolmasks nextvar acc))))
         (or (member v (nat-bool-a4env-vars acc))
             (and (natp v)
                  (<= (nfix nextvar) v)
                  (< v (+ (nfix nextvar) (svex-maskbits-for-vars vars masks boolmasks))))))
    :hints(("Goal" :in-theory (enable svex-maskbits-for-vars
                                      nat-bool-a4env-vars))))

  (defthm svex-varmasks->a4env-rec-lower-bounds
    (implies (and (nat-bool-a4env-lower-boundp bound acc)
                  (<= (nfix bound) (nfix nextvar)))
             (nat-bool-a4env-lower-boundp bound (mv-nth 1 (svex-varmasks->a4env-rec vars masks boolmasks nextvar acc))))
    :hints(("Goal" :in-theory (enable nat-bool-a4env-lower-boundp))))

  (defthm svex-varmasks->a4env-rec-upper-bounds
    (implies (and (nat-bool-a4env-upper-boundp bound acc)
                  (<= (+ (nfix nextvar) (svex-maskbits-for-vars vars masks boolmasks))
                      (nfix bound)))
             (nat-bool-a4env-upper-boundp bound (mv-nth 1 (svex-varmasks->a4env-rec vars masks boolmasks nextvar acc))))
    :hints(("Goal" :in-theory (enable nat-bool-a4env-upper-boundp
                                      svex-maskbits-for-vars))))

  (defret key-exists-in-svex-varmasks->a4env-rec
    (implies (not err)
             (iff (hons-assoc-equal v a4env)
                  (or (member v (svarlist-fix vars))
                      (hons-assoc-equal v (svex-a4vec-env-fix acc))))))

  (defret alist-keys-of-svex-varmasks->a4env-rec
    (implies (not err)
             (equal (alist-keys a4env)
                    (append (rev (svarlist-fix vars))
                            (alist-keys (svex-a4vec-env-fix acc)))))
    :hints(("Goal" :in-theory (enable svex-maskbits-ok)))))

;; (defsection svex-envs-masks-partly-equiv

;;   (defquant svex-envs-masks-partly-equiv (vars masks env1 env2)
;;     (forall v
;;             (implies (not (member (svar-fix v) (svarlist-fix vars)))
;;                      (equal (4vec-mask (svex-mask-lookup (svex-var v) masks)
;;                                        (svex-env-lookup v env1))
;;                             (4vec-mask (svex-mask-lookup (svex-var v) masks)
;;                                        (svex-env-lookup v env2)))))
;;     :rewrite :direct)

;;   (defexample svex-envs-masks-partly-equiv-example
;;     :pattern (equal (4vec-mask (svex-mask-lookup (svex-var v) masks)
;;                                val1)
;;                     (4vec-mask mask2 val2))
;;     :templates (v)
;;     :instance-rulename svex-envs-masks-partly-equiv-instancing))


(defsection svex-envs-mask-equiv-on-vars

  (defquant svex-envs-mask-equiv-on-vars (vars masks env1 env2)
    (forall v
            (implies (member (svar-fix v) (svarlist-fix vars))
                     (equal (4vec-mask (svex-mask-lookup (svex-var v) masks)
                                       (svex-env-lookup v env1))
                            (4vec-mask (svex-mask-lookup (svex-var v) masks)
                                       (svex-env-lookup v env2)))))
    :rewrite :direct)

  (defexample svex-envs-mask-equiv-on-vars-example
    :pattern (equal (4vec-mask (svex-mask-lookup (svex-var v) masks)
                               val1)
                    (4vec-mask mask2 val2))
    :templates (v)
    :instance-rulename svex-envs-mask-equiv-on-vars-instancing)

  (local (defexample svex-envs-mask-equiv-on-vars-mask-look-example
           :pattern (svex-mask-lookup (svex-var var) masks)
           :templates (var)
           :instance-rulename svex-envs-mask-equiv-on-vars-instancing))

  (local (defexample svex-envs-mask-equiv-on-vars-env-look-example
           :pattern (svex-env-lookup var env)
           :templates (var)
           :instance-rulename svex-envs-mask-equiv-on-vars-instancing))

  (local (defexample svex-argmasks-okp-example
           :pattern (equal (4vec-mask mask (svex-apply fn (svexlist-eval args env1)))
                           (4vec-mask mask (svex-apply fn (svexlist-eval args env2))))
           :templates (env1 (svexlist-eval args env2))
           :instance-rulename svex-argmasks-okp-instancing))

  (local (acl2::def-witness-ruleset svex-mask-alist-reasoning
           '(svex-mask-alist-complete-witnessing
             svex-mask-alist-complete-instancing
             svex-mask-alist-complete-example
             svex-mask-alist-partly-complete-witnessing
             svex-mask-alist-partly-complete-instancing
             svex-mask-alist-partly-complete-example)))

  (local (acl2::def-witness-ruleset svex-env-reasoning
           '(svex-envs-mask-equiv-on-vars-instancing
             svex-envs-mask-equiv-on-vars-witnessing
             svex-envs-mask-equiv-on-vars-mask-look-example
             svex-envs-mask-equiv-on-vars-env-look-example
             svex-mask-alist-reasoning
             SVEX-ARGMASKS-OKP-WITNESSING
             SVEX-ARGMASKS-OKP-INSTANCING
             SVEX-ARGMASKS-OKP-EXAMPLE
             )))


  (defthm-svex-eval-flag
    (defthm svex-eval-of-mask-equiv-on-vars-envs
      (implies (and (svex-mask-alist-complete masks)
                    (svex-envs-mask-equiv-on-vars vars masks env1 env2)
                    (subsetp-equal (intersection-equal (svex-vars x)
                                                       (union-equal (alist-keys (svex-env-fix env1))
                                                                    (alist-keys (svex-env-fix env2))))
                                   (svarlist-fix vars)))
               (equal (equal (4vec-mask (svex-mask-lookup x masks)
                                        (svex-eval x env1))
                             (4vec-mask (svex-mask-lookup x masks)
                                        (svex-eval x env2)))
                      t))
      :hints ('(:expand ((:free (env) (svex-eval x env))
                         (svex-vars x))
                :do-not-induct t)
              (witness :ruleset svex-env-reasoning)
              (witness :ruleset svex-env-reasoning)
              (set-reasoning)
              (and stable-under-simplificationp
                   '(:in-theory (enable svex-env-lookup)))
              ;; (and stable-under-simplificationp
              ;;      '(:use ((:instance svex-argmasks-okp-necc
              ;;               (mask (svex-mask-lookup x masks))
              ;;               (argmasks (svex-argmasks-lookup
              ;;                          (svex-call->args x) masks))
              ;;               (env env1)
              ;;               (vals (svexlist-eval (svex-call->args x) env2))))))
              )
      :flag expr)
    (defthm svexlist-eval-of-mask-equiv-on-vars-envs
      (implies (and (svex-mask-alist-complete masks)
                    (svex-envs-mask-equiv-on-vars vars masks env1 env2)
                    (subsetp-equal (intersection-equal (svexlist-vars x)
                                                       (union-equal (alist-keys (svex-env-fix env1))
                                                                    (alist-keys (svex-env-fix env2))))
                                   (svarlist-fix vars)))
               (equal (equal (4veclist-mask (svex-argmasks-lookup x masks)
                                            (svexlist-eval x env1))
                             (4veclist-mask (svex-argmasks-lookup x masks)
                                            (svexlist-eval x env2)))
                      t))
      :hints ('(:expand ((:free (env) (svexlist-eval x env))
                         (svexlist-vars x)
                         (svex-argmasks-lookup x masks))))
      :flag list))

  )

(local (defthm hons-assoc-equal-of-append
         (equal (hons-assoc-equal k (append a b))
                (or (hons-assoc-equal k a)
                    (hons-assoc-equal k b)))))

(defthm aig-list->s-of-append-when-first-superset
  (implies (and (nat-bool-listp x)
                (subsetp (nat-bool-list-nats x)
                         (alist-keys env)))
           (equal (aig-list->s x (append env rest))
                  (aig-list->s x env)))
  :hints(("Goal" :in-theory (e/d* (aig-list->s
                                   nat-bool-listp
                                   nat-bool-list-nats
                                   gl::scdr
                                   gl::s-endp)
                                 ((:rules-of-class :type-prescription :here)))
          :induct (aig-list->s x env)
          :expand ((:free (env) (aig-list->s x env))))))

(defthm a4vec-eval-of-append-when-first-superset
  (implies (and (nat-bool-a4vec-p x)
                (subsetp (nat-bool-a4vec-vars x)
                         (alist-keys env)))
           (equal (a4vec-eval x (append env rest))
                  (a4vec-eval x env)))
  :hints(("Goal" :in-theory (enable a4vec-eval
                                    nat-bool-a4vec-p
                                    nat-bool-a4vec-vars))))

(defthm aig-list->s-of-append-when-first-not-intersect
  (implies (and (nat-bool-listp x)
                (not (intersectp (nat-bool-list-nats x)
                                 (alist-keys prev))))
           (equal (aig-list->s x (append prev env))
                  (aig-list->s x env)))
  :hints(("Goal" :in-theory (e/d* (aig-list->s
                                   nat-bool-listp
                                   nat-bool-list-nats
                                   gl::scdr
                                   gl::s-endp)
                                 ((:rules-of-class :type-prescription :here)))
          :induct (aig-list->s x env)
          :expand ((:free (env) (aig-list->s x env))))))


(defthm a4vec-eval-of-append-when-first-not-intersect
  (implies (and (nat-bool-a4vec-p x)
                (not (intersectp (nat-bool-a4vec-vars x)
                                 (alist-keys prev))))
           (equal (a4vec-eval x (append prev env))
                  (a4vec-eval x env)))
  :hints(("Goal" :in-theory (enable a4vec-eval
                                    nat-bool-a4vec-p
                                    nat-bool-a4vec-vars))))

(defthm nat-bool-a4vec-p-of-nat-bool-a4env
  (implies (and (nat-bool-a4env-p x)
                (hons-assoc-equal k x))
           (nat-bool-a4vec-p (cdr (hons-assoc-equal k x))))
  :hints(("Goal" :in-theory (enable nat-bool-a4env-p))))


;; (define svex-env-lookup-nofix (x env)
;;   (or (cdr (hons-get x env)) (4vec-x))
;;   ///
;;   (defthm svex-env-lookup-nofix-when-right-types
;;     (implies (and (svar-p x)
;;                   (svex-env-p env))
;;              (equal (svex-env-lookup-nofix x env)
;;                     (svex-env-lookup x env)))
;;     :hints(("Goal" :in-theory (enable svex-env-lookup
;;                                       svex-env-p))))

;;   ;; (local (defthm lookup-in-svex-env-fix-when-svar-p
;;   ;;          (implies (and (svar-p x)
;;   ;;                        (not (cdr (hons-assoc-equal x env))))
;;   ;;                   (4vec-equiv (cdr (hons-assoc-equal x (svex-env-fix env)))
;;   ;;                               (4vec-x)))
;;   ;;          :hints(("Goal" :in-theory (enable svex-env-fix)))))

;;   (defthm svex-env-lookup-nofix-when-right-types-weak
;;     (implies (svar-p x)
;;              (4vec-equiv (svex-env-lookup-nofix x env)
;;                          (svex-env-lookup x env)))
;;     :hints(("Goal" :in-theory (enable svex-env-lookup svex-env-fix)))))







(define svex-mask-alist-extract-vars ((x svex-mask-alist-p))
  :returns (new-x svex-mask-alist-p)
  :hooks nil
  (if (atom x)
      nil
    (if (and (mbt (svex-p (caar x)))
             (eq (svex-kind (caar x)) :var))
        (hons-acons (caar x) (4vmask-fix (cdar x))
                    (svex-mask-alist-extract-vars (cdr x)))
      (svex-mask-alist-extract-vars (cdr x))))
  ///
  (defret lookup-in-svex-mask-alist-extract-vars
    (equal (hons-assoc-equal s new-x)
           (and (svex-p s)
                (equal (svex-kind s) :var)
                (hons-assoc-equal s (svex-mask-alist-fix x)))))

  (local (defthm assoc-in-svex-mask-alist-p
           (implies (svex-mask-alist-p x)
                    (equal (assoc k x)
                           (hons-assoc-equal k x)))
           :hints(("Goal" :in-theory (enable svex-mask-alist-p)))))

  (defret svex-mask-lookup-in-svex-mask-alist-extract-vars
    (equal (svex-mask-lookup s new-x)
           (if (equal (svex-kind s) :var)
               (svex-mask-lookup s x)
             0))
    :hints(("Goal" :in-theory (enable svex-mask-lookup))))

  (defret svex-maskbits-ok-of-svex-mask-alist-extract-vars
    (iff (svex-maskbits-ok vars new-x)
         (svex-maskbits-ok vars x))
    :hints(("Goal" :in-theory (enable svex-maskbits-ok)
            :induct (svex-maskbits-ok vars x)
            :do-not-induct t)))

  (defret svex-maskbits-for-vars-of-svex-mask-alist-extract-vars
    (equal (svex-maskbits-for-vars vars new-x boolmasks)
           (svex-maskbits-for-vars vars x boolmasks))
    :hints(("Goal" :in-theory (e/d (svex-maskbits-for-vars)
                                   (svex-mask-alist-extract-vars)))))

  (deffixequiv svex-mask-alist-extract-vars :hints(("Goal" :in-theory (enable svex-mask-alist-fix)))))



(define svex-varmasks/env->aig-env-rec ((vars svarlist-p)
                                        (masks svex-mask-alist-p)
                                        (boolmasks svar-boolmasks-p)
                                        (env svex-env-p "look up variables in env to get 4vecs to assign -- symbolic")
                                        (nextvar natp)
                                        (acc "aig environment accumulator"))
  :prepwork ((local (in-theory (enable svarlist-p svarlist-fix))))
  :returns (mv (err "some mask was negative"
                    (implies (svex-mask-alist-p masks)
                             (iff err (not (svex-maskbits-ok vars masks))))
                    :hints(("Goal" :in-theory (enable svex-maskbits-ok))))
               (env) ;; binds AIG vars to Boolean values
               (nextvar1
                (implies (and (svex-mask-alist-p masks)
                              (svar-boolmasks-p boolmasks))
                         (equal nextvar1
                                (+ (nfix nextvar)
                                   (svex-maskbits-for-vars vars masks boolmasks))))
                :hints(("Goal" :in-theory (enable svex-maskbits-for-vars)))))
  ;; :hooks ((:fix :args (vars nextvar)))
  (b* (((when (atom vars))
        (mv nil acc (lnfix nextvar)))
       (mask (svex-mask-lookup (svex-var (car vars)) masks))
       ((when (sparseint-< mask 0))
        (mv (msg "Negative mask: ~x0~%" (svar-fix (car vars)))
            acc (lnfix nextvar)))
       (boolmask (svar-boolmasks-lookup (car vars) boolmasks))
       (4vec (4vec-fix (svex-env-lookup (svar-fix (car vars)) env)))
       (env-part
        (4vmask-to-a4vec-env mask boolmask 4vec nextvar))
       (nextvar (+ (lnfix nextvar)
                   (4vmask-to-a4vec-varcount mask boolmask))))
    (svex-varmasks/env->aig-env-rec
     (cdr vars) masks boolmasks env nextvar (append env-part acc)))
  ///

  (defthm key-exists-in-svex-varmasks/env->aig-env-rec
    (implies (and (svex-mask-alist-p masks)
                  (svar-boolmasks-p boolmasks))
             (iff (hons-assoc-equal v (mv-nth 1 (svex-varmasks/env->aig-env-rec
                                                 vars masks boolmasks env nextvar acc)))
                  (or (hons-assoc-equal v acc)
                      (and (natp v)
                           (<= (nfix nextvar) v)
                           (< v (+ (nfix nextvar) (svex-maskbits-for-vars vars masks boolmasks)))))))
    :hints(("Goal" :in-theory (enable svex-maskbits-for-vars))))

  (local (defun-sk svex-varmasks/env->aig-env-accumulator-elim-correct (vars masks boolmasks env nextvar)
           (forall acc
                   (implies (syntaxp (not (equal acc ''nil)))
                            (equal (mv-nth 1 (svex-varmasks/env->aig-env-rec
                                              vars masks boolmasks env nextvar acc))
                                   (append (mv-nth 1 (svex-varmasks/env->aig-env-rec
                                                      vars masks boolmasks env nextvar nil))
                                           acc))))
           :rewrite :direct))
  (local (in-theory (disable svex-varmasks/env->aig-env-accumulator-elim-correct)))
  (local (defthmd svex-varmasks/env->aig-env-accumulator-elim-lemma
           (svex-varmasks/env->aig-env-accumulator-elim-correct vars masks boolmasks env nextvar)
           :hints (("goal" :induct (svex-varmasks/env->aig-env-rec vars masks boolmasks env nextvar acc))
                   (and stable-under-simplificationp
                        `(:expand (,(car (last clause))
                                   (:free (acc)
                                    (svex-varmasks/env->aig-env-rec vars masks boolmasks env nextvar acc))))))))

  (defthm svex-varmasks/env->aig-env-accumulator-elim
    (implies (syntaxp (not (equal acc ''nil)))
             (equal (mv-nth 1 (svex-varmasks/env->aig-env-rec
                               vars masks boolmasks env nextvar acc))
                    (append (mv-nth 1 (svex-varmasks/env->aig-env-rec
                                       vars masks boolmasks env nextvar nil))
                            acc)))
    :hints (("goal" :use svex-varmasks/env->aig-env-accumulator-elim-lemma)))


  (defthm 4vmask-to-a4vec-vars-subset-of-keys
    (SUBSETP-EQUAL
     (NAT-BOOL-A4VEC-VARS
      (4vmask-to-a4vec mask boolmask nextvar))
     (ALIST-KEYS
      (4vmask-to-a4vec-env mask boolmask val nextvar)))
    :hints ((acl2::set-reasoning)))

  (defthm member-nat-bool-a4vec-vars-of-lookup-when-upper-bounded
    (implies (and (nat-bool-a4env-p a4acc)
                  (nat-bool-a4env-upper-boundp nextvar a4acc)
                  (<= (nfix nextvar) k))
             (not (member k (nat-bool-a4vec-vars (cdr (hons-assoc-equal v a4acc))))))
    :hints(("Goal" :in-theory (enable nat-bool-a4env-p
                                      nat-bool-a4env-upper-boundp))))

  (defthm 4vmask-to-a4vec-env-vars-not-intersect-when-upper-bounded
    (implies (and (nat-bool-a4env-p a4acc)
                  (double-rewrite (nat-bool-a4env-upper-boundp nextvar a4acc)))
             (not (intersectp (nat-bool-a4vec-vars
                               (cdr (hons-assoc-equal v a4acc)))
                              (alist-keys (4vmask-to-a4vec-env mask boolmask val nextvar)))))
    :hints ((acl2::set-reasoning)))

  (local (defthm 4vmask-to-a4vec-vars-not-intersect-svex-varmsks/env->aig-env-rec-keys
           (implies (and (svex-mask-alist-p masks)
                         (svar-boolmasks-p boolmasks))
                    (NOT
                     (INTERSECTP-EQUAL
                      (NAT-BOOL-A4VEC-VARS
                       (4VMASK-TO-A4VEC mask
                                        boolmask
                                        NEXTVAR))
                      (ALIST-KEYS
                       (MV-NTH
                        1
                        (SVEX-VARMASKS/ENV->AIG-ENV-REC
                         vars masks BOOLMASKS GOALENV
                         (+ (NFIX NEXTVAR)
                            (4VMASK-TO-A4VEC-VARCOUNT mask boolmask))
                         NIL))))))
           :hints ((set-reasoning))))

  (local (defthm not-member-a4vec-vars-lookup-when-not-member-a4env-vars
           (implies (not (member v (nat-bool-a4env-vars a4env)))
                    (not (member v (nat-bool-a4vec-vars (cdr (hons-assoc-equal v0 a4env))))))
           :hints(("Goal" :in-theory (enable nat-bool-a4env-vars)))))

  (local (defthm 4vmask-to-a4vec-vars-subset-svex-varmsks/env->aig-env-rec-keys-2
           (implies (and (svex-mask-alist-p masks)
                         (svar-boolmasks-p boolmasks))
                    (SUBSETP-EQUAL
                     (NAT-BOOL-A4VEC-VARS
                      (CDR
                       (HONS-ASSOC-EQUAL
                        v0
                        (MV-NTH
                         1
                         (SVEX-VARMASKS->A4ENV-REC
                          vars
                          MASKS BOOLMASKS
                          nextvar
                          NIL)))))
                     (ALIST-KEYS
                      (MV-NTH
                       1
                       (SVEX-VARMASKS/ENV->AIG-ENV-REC
                        vars
                        (SVEX-MASK-ALIST-EXTRACT-VARS MASKS)
                        BOOLMASKS GOALENV
                        nextvar
                        NIL)))))
           :hints ((set-reasoning))))

  (acl2::defquant svex-env-boolmasks-ok (env boolmasks)
    (forall v
            (4vec-boolmaskp (svex-env-lookup v env)
                            (svar-boolmasks-lookup v boolmasks)))
    :rewrite :direct)

  (local (defthm svex-env-lookup-of-cons
           (equal (svex-env-lookup k (cons (cons k0 v0) rest))
                  (if (and (svar-p k0) (equal (svar-fix k) k0))
                      (4vec-fix v0)
                    (svex-env-lookup k rest)))
           :hints(("Goal" :in-theory (enable svex-env-lookup
                                             svex-env-fix)))))

  (local (in-theory (enable svex-env-boolmasks-ok-necc
                            svex-varmasks->a4env-rec-accumulator-elim)))

  (defthm eval-svex-varmasks->a4env-rec-with-env
    (b* (((mv err a4env ?nextvar1)
          ;; Assigns AIG variable numbers to each SVEX var. Ignores goalenv (does
          ;; not need to know anything about the values of the svex vars to do
          ;; this, just their caremasks/boolmasks).
          (svex-varmasks->a4env-rec vars masks boolmasks nextvar nil))
         ((mv ?err1 env ?nextvar1)
          ;; Binds AIG variable numbers to (symbolic) bits extracted from the goalenv.
          (svex-varmasks/env->aig-env-rec
           vars (svex-mask-alist-extract-vars masks) boolmasks goalenv nextvar nil)))
      (implies (and (not err)
                    ;; (nat-bool-a4env-p a4acc)
                    ;; (nat-bool-a4env-upper-boundp nextvar a4acc)
                    (svex-mask-alist-p masks)
                    (svar-boolmasks-p boolmasks)
                    (svex-env-boolmasks-ok goalenv boolmasks)
                    ;; (svex-env-p goalenv)
                    ;; (svex-envs-masks-partly-equiv
                    ;;  vars masks
                    ;;  (svex-a4vec-env-eval a4acc envacc)
                    ;;  goalenv)
                    ;; (subsetp (alist-keys (svex-env-fix goalenv))
                    ;;          (append (svarlist-fix vars)
                    ;;                  (alist-keys (svex-a4vec-env-fix a4acc))))
                    )
               (svex-envs-mask-equiv-on-vars
                vars masks
                (svex-a4vec-env-eval a4env env)
                goalenv)))
    :hints(("Goal" :in-theory (enable svex-varmasks->a4env-rec
                                      svarlist-fix
                                      svex-maskbits-ok
                                      nat-bool-a4env-p
                                      nat-bool-a4env-upper-boundp
                                      svex-a4vec-env-fix
                                      svex-a4vec-env-eval
                                      alist-keys
                                      svex-alist-keys)
            :induct (svex-varmasks->a4env-rec vars masks boolmasks nextvar nil)

 ;; (svex-varmasks->a4env-rec-induct
                    ;;  vars masks boolmasks nextvar a4acc goalenv envacc)
            :expand ((:free (a4acc) (svex-varmasks->a4env-rec vars masks boolmasks nextvar a4acc))
                     (:free (envacc masks)
                      (svex-varmasks/env->aig-env-rec
                       vars masks boolmasks goalenv nextvar envacc))))
           (and stable-under-simplificationp
                (cond ((assoc 'subsetp-equal clause) ;; has a (not (subsetp-equal... lit
                       (acl2::set-reasoning))
                      ;; ((assoc 'svex-envs-masks-partly-equiv clause)
                      ;;  '(:computed-hint-replacement
                      ;;    ((acl2::witness :ruleset (svex-envs-masks-partly-equiv-witnessing))
                      ;;     (acl2::witness :ruleset (svex-envs-masks-partly-equiv-example)))
                      ;;    :in-theory (enable ;; svex-env-lookup
                      ;;                       svex-env-fix)))
                      ;; (t '(:computed-hint-replacement
                      ;;      ((acl2::witness :ruleset (svex-envs-mask-equiv-witnessing))
                      ;;       (acl2::witness :ruleset (svex-envs-masks-partly-equiv-example)))
                      ;;      :no-op t))
                      (t '(:computed-hint-replacement
                           ((acl2::witness :ruleset (svex-envs-mask-equiv-on-vars-witnessing))
                            (acl2::witness :ruleset (svex-envs-mask-equiv-on-vars-example)))
                           :no-op t))
                      )))))


(define svex-varmasks->a4env ((vars svarlist-p)
                              (masks svex-mask-alist-p)
                              (boolmasks svar-boolmasks-p))
  :returns (mv (err "some mask was negative"
                    (iff err (not (svex-maskbits-ok vars masks))))
               (a4env nat-bool-a4env-p!))
  (b* (((mv err res &)
        (svex-varmasks->a4env-rec vars masks boolmasks 0 nil)))
    (mv err res))
  ///
  (defret alist-keys-of-svex-varmasks->a4env
    (implies (not err)
             (equal (alist-keys a4env)
                    (rev (svarlist-fix vars))))))


(define svex-varmasks/env->aig-env ((vars svarlist-p)
                                    (masks svex-mask-alist-p)
                                    (boolmasks svar-boolmasks-p)
                                    (env svex-env-p "look up variables in env to get 4vecs to assign"))
  :returns (mv (err "some mask was negative"
                    (implies (svex-mask-alist-p masks)
                             (iff err (not (svex-maskbits-ok vars masks))))
                    :hints(("Goal" :in-theory (enable svex-maskbits-ok))))
               (env "binds AIG vars to Boolean values"))
    :hooks ((:fix :args (vars)))
  (b* (((mv err res &)
        (svex-varmasks/env->aig-env-rec vars masks boolmasks env 0 nil)))
    (mv err res))
  ///
  (defthm eval-svex-varmasks->a4env-with-env
    (b* (((mv err a4env)
          (svex-varmasks->a4env vars masks boolmasks1))
         ((mv ?err1 env)
          (svex-varmasks/env->aig-env
           vars (svex-mask-alist-extract-vars masks) boolmasks goalenv)))
      (implies (and (not err)
                    (svex-mask-alist-p masks)
                    (equal boolmasks (svar-boolmasks-fix boolmasks1))
                    ;; (svex-env-p goalenv)
                    (svex-env-boolmasks-ok goalenv boolmasks))
               (svex-envs-mask-equiv-on-vars vars masks
                                             (svex-a4vec-env-eval a4env env)
                                             goalenv)))
    :hints (("goal" :use ((:instance eval-svex-varmasks->a4env-rec-with-env
                           (nextvar 0)))
             :in-theory (e/d (svex-varmasks->a4env
                              svex-env-lookup
                              svex-lookup)
                             (eval-svex-varmasks->a4env-rec-with-env)))
            ;; (acl2::witness :ruleset (svex-envs-mask-equiv-on-vars))
            ;; (acl2::set-reasoning)
            )))

(define svexlist-full-masks-p ((x svexlist-p)
                               (masks svex-mask-alist-p))
  (if (atom x)
      t
    (and (equal -1 (sparseint-val (svex-mask-lookup (car x) masks)))
         (svexlist-full-masks-p (cdr x) masks)))
  ///
  (defthm svexlist-full-masks-p-of-take
    (implies (and (svexlist-full-masks-p x masks)
                  (<= (nfix n) (len x)))
             (svexlist-full-masks-p (take n x) masks)))

  (defthm svexlist-full-masks-p-of-nthcdr
    (implies (svexlist-full-masks-p x masks)
             (svexlist-full-masks-p (nthcdr n x) masks)))

  (defthmd svexlist-full-masks-p-of-svexlist-mask-alist-lemma
    (implies (subsetp (svexlist-fix y) (svexlist-fix x))
             (svexlist-full-masks-p y (svexlist-mask-alist x)))
    :hints(("Goal" :in-theory (enable subsetp svexlist-fix))))


  (defthm svexlist-full-masks-p-of-svexlist-mask-alist
    (svexlist-full-masks-p x (svexlist-mask-alist x))
    :hints(("Goal" :in-theory (enable svexlist-full-masks-p-of-svexlist-mask-alist-lemma))))

  (local (defun cdr2 (x y)
           (if (atom x)
               y
             (cdr2 (Cdr x) (cdr y)))))

  (defthm 4veclist-mask-when-full-masksp
    (implies (and (svexlist-full-masks-p x masks)
                  (equal (len 4vecs) (len x)))
             (equal (4veclist-mask (svex-argmasks-lookup x masks) 4vecs)
                    (4veclist-fix 4vecs)))
    :hints(("Goal" :in-theory (enable 4veclist-mask svex-argmasks-lookup 4veclist-fix 4vec-mask)
            :induct (cdr2 x 4vecs)))))



(defsection general-correctness-theorems
  (local (defthm subsetp-intersection
           (subsetp (intersection$ x y) y)
           :hints ((set-reasoning))))

  (defthm svexlist->a4vec-correct-for-varmasks-aig-env
    (b* (((mv err a4env)
          (svex-varmasks->a4env vars masks boolmasks1))
         ((mv ?err1 env)
          (svex-varmasks/env->aig-env
           vars (svex-mask-alist-extract-vars masks) boolmasks goalenv))
         (a4vecs (svexlist->a4vec x a4env masks)))
      (implies (and (not err)
                    (svex-mask-alist-p masks)
                    (svex-mask-alist-complete masks)
                    (equal boolmasks (svar-boolmasks-fix boolmasks1))
                    (svex-env-boolmasks-ok goalenv boolmasks)
                    (subsetp (intersection-equal (svexlist-vars x)
                                                 (alist-keys (svex-env-fix goalenv)))
                             (svarlist-fix vars)))
               (equal (4veclist-mask (svex-argmasks-lookup x masks)
                                     (a4veclist-eval a4vecs env))
                      (4veclist-mask (svex-argmasks-lookup x masks)
                                     (svexlist-eval x goalenv)))))
    :hints (("goal" :use ((:instance svexlist-eval-of-mask-equiv-on-vars-envs
                           (env2 goalenv)
                           (env1 (svex-a4vec-env-eval
                                  (mv-nth 1 (svex-varmasks->a4env vars masks boolmasks))
                                  (mv-nth 1 (svex-varmasks/env->aig-env
                                             vars (svex-mask-alist-extract-vars masks) boolmasks goalenv))))))
             :in-theory (disable svexlist-eval-of-mask-equiv-on-vars-envs))))

  (defthm svexlist->a4vec-correct-for-varmasks-aig-env-top
    (b* (((mv err a4env)
          (svex-varmasks->a4env vars masks boolmasks1))
         ((mv ?err1 env)
          (svex-varmasks/env->aig-env
           vars (svex-mask-alist-extract-vars masks) boolmasks goalenv))
         (a4vecs (svexlist->a4vec x a4env masks)))
      (implies (and (not err)
                    (svexlist-full-masks-p x masks)
                    (svex-mask-alist-p masks)
                    (svex-mask-alist-complete masks)
                    (equal boolmasks (svar-boolmasks-fix boolmasks1))
                    (svex-env-boolmasks-ok goalenv boolmasks)
                    (subsetp (intersection-equal (svexlist-vars x)
                                                 (alist-keys (svex-env-fix goalenv)))
                             (svarlist-fix vars)))
               (equal (a4veclist-eval a4vecs env)
                      (svexlist-eval x goalenv))))
    :hints (("goal" :use svexlist->a4vec-correct-for-varmasks-aig-env
             :in-theory (disable svexlist->a4vec-correct-for-varmasks-aig-env)))))

(define svex-env-check-boolmasks ((boolmasks svar-boolmasks-p)
                                  (env svex-env-p))
  :prepwork ((local (in-theory (enable svar-boolmasks-p svar-boolmasks-fix))))
  ;; :hooks nil
  (b* (((when (atom boolmasks)) t)
       ((unless (mbt (svar-p (caar boolmasks))))
        (svex-env-check-boolmasks (cdr boolmasks) env))
       ((cons var mask) (car boolmasks))
       (val (svex-env-lookup var env))
       (ok (4vec-boolmaskp val mask))
       (?ign (and (not ok)
                  (cw "not 4vec-boolmaskp: ~x0~%" var))))
    (and (svex-env-check-boolmasks (cdr boolmasks) env)
         ok))
  ///
  (acl2::defexample svex-env-boolmasks-ok-example
    :pattern (svex-env-lookup v env)
    :templates (v)
    :instance-rulename svex-env-boolmasks-ok-instancing)

  (defthm svex-env-check-boolmasks-correct
    (implies (and (svex-env-check-boolmasks boolmasks env)
                  ;; (svex-env-p env)
                  (svar-boolmasks-p boolmasks))
             (svex-env-boolmasks-ok env boolmasks))
    :hints (("goal" :induct (svex-env-check-boolmasks boolmasks env))
            (acl2::witness :ruleset (svex-env-boolmasks-ok-witnessing
                                     svex-env-boolmasks-ok-example))
            (and stable-under-simplificationp
                 '(:in-theory (enable svar-boolmasks-lookup)
                   :expand ((:free (x) (4vec-boolmaskp x 0))))))))

(define svexlist-mask-alist-memo ((x svexlist-p))
  :enabled t
  (svexlist-mask-alist x)
  ///
  (memoize 'svexlist-mask-alist-memo))

(define svexlist-vars-memo ((x svexlist-p))
  :enabled t
  (svexlist-collect-vars x)
  ///
  (memoize 'svexlist-vars-memo))


(define svexlist->a4vecs-for-varlist ((x svexlist-p)
                                      (vars svarlist-p)
                                      (boolmasks svar-boolmasks-p))
  :returns (mv (err (iff err (not (svex-maskbits-ok vars (svexlist-mask-alist x)))))
               (a4vecs a4veclist-p))
  :short "Creates a symbolic bit-level representation for x, assuming that vars
          are the only vars relevant to x and that the bits of vars given in boolmasks
          are Boolean-valued."
  :long "<p>Steps: First creates a symbolic environment mapping the variables
to a4vec structures, each bit of which is a free variable.  (For bits
constrained to be Boolean by boolmasks, the same variable is shared for
upper/lower.)  Then uses @('svexlist->a4vec-top') to generate a4vecs corresponding
to the svexes.</p>"

  (b* (;; (- (sneaky-push 'svexlist x))
       (masks (svexlist-mask-alist-memo x))
       ((mv err a4env) (svex-varmasks->a4env vars masks boolmasks))
       ((when err) (mv err nil))
       (a4env (make-fast-alist a4env))
       (res (svexlist->a4vec-top x a4env masks))
       (?ign (fast-alist-free a4env)))
    (mv nil res))
  ///
  (memoize 'svexlist->a4vecs-for-varlist))




(define svexlist-variable-mask-alist ((x svexlist-p))
  ;; We've seen problems in GL where we get a stack overflow in
  ;; gobject-hierarchy-lite traversing the full masks inside
  ;; svexlist->a4vec-aig-env-for-varlist.  But we don't need the full set of
  ;; masks there, only those for the variables.  So to work around this
  ;; problem, this function extracts only the variables from the mask alist,
  ;; producing a much smaller alist.
  :returns (varmasks svex-mask-alist-p)
  :enabled t
  (b* ((masks-full (svexlist-mask-alist-memo x)))
    (svex-mask-alist-extract-vars masks-full))
  ///
  (memoize 'svexlist-variable-mask-alist))


(define svexlist->a4vec-aig-env-for-varlist ((x svexlist-p)
                                             (vars svarlist-p)
                                             (boolmasks svar-boolmasks-p)
                                             (env svex-env-p))
  :returns (mv (err (iff err (not (svex-maskbits-ok vars (svexlist-mask-alist x)))))
               (aig-env))
  :hooks ((:fix :args (x vars)))
  ;; We use svexlist-variable-mask-alist here rather than
  ;; svexlist-mask-alist-memo so that GL won't have to traverse the full mask
  ;; alist with gobject-hierarchy-lite, which we've seen cause stack overflows.
  (b* ((masks (svexlist-variable-mask-alist x)))
    (svex-varmasks/env->aig-env vars masks boolmasks env))
  ///
  ;; (local (defthm svex-envs-mask-equiv-lemma
  ;;          (iff (svex-envs-mask-equiv
  ;;                (svexlist-mask-alist x) y z)
  ;;               (svex-envs-mask-equiv
  ;;                (svexlist-variable-mask-alist x) y z))
  ;;          :hints ((witness))))

  ;; This is directly proved by svexlist->a4vec-top-correct-for-varmasks-aig-env-top
  (defthm svexlist->a4vec-for-varlist-correct
    (b* (((mv err a4vecs) (svexlist->a4vecs-for-varlist x vars boolmasks))
         ((mv ?err1 aig-env) (svexlist->a4vec-aig-env-for-varlist x vars boolmasks env)))
      (implies (and (not err)
                    ;; (svex-env-p env)
                    (svar-boolmasks-p boolmasks)
                    (svex-env-boolmasks-ok env boolmasks)
                    (subsetp (intersection-equal (svexlist-vars x)
                                                 (alist-keys (svex-env-fix env)))
                             (svarlist-fix vars)))
               (equal (a4veclist-eval a4vecs aig-env)
                      (svexlist-eval x env))))
    :hints(("Goal" :in-theory (e/d (svexlist->a4vecs-for-varlist)
                                   (svexlist-eval-of-mask-equiv-on-vars-envs))))
    :otf-flg t))


(local (defthm subset-of-mergesorts-is-subsetp
         (iff (subset (mergesort a) (mergesort b))
              (subsetp a b))
         :hints(("Goal" :in-theory (enable* set::definitions)))))


(define svexlist-rewrite-fixpoint-memo ((x svexlist-p))
  :enabled t
  (time$ (svexlist-rewrite-fixpoint x :verbosep t :count 2)
         :msg "; svex rewriting: ~st sec, ~sa bytes.~%")
  ///
  (memoize 'svexlist-rewrite-fixpoint-memo))

(define maybe-svexlist-rewrite-fixpoint ((x svexlist-p) (do-it))
  :returns (new-x svexlist-p)
  (if do-it
      (svexlist-rewrite-fixpoint-memo x)
    (hons-copy (svexlist-fix x)))
  ///
  (defret maybe-svexlist-rewrite-fixpoint-correct
    (equal (svexlist-eval new-x env)
           (svexlist-eval x env)))
  (defret maybe-svexlist-rewrite-fixpoint-len
    (equal (len new-x)
           (len x)))

  (defret vars-of-maybe-svexlist-rewrite-fixpoint
    (implies (not (member v (svexlist-vars x)))
             (not (member v (svexlist-vars new-x))))))


(local (defthm svarlist-p-of-alist-keys-when-svex-env-p
         (implies (svex-env-p env)
                  (svarlist-p (alist-keys env)))
         :hints(("Goal" :in-theory (enable svex-env-p svarlist-p alist-keys)))))


(define svexlist-vars-for-symbolic-eval ((x svexlist-p)
                                         (env svex-env-p)
                                         (symbolic-params alistp))
  :returns (vars svarlist-p)
  :guard-hints (("goal" :in-theory (e/d (SET::UNION-WITH-SUBSET-LEFT
                                         double-containment
                                         set::subset-to-subsetp)
                                        (SUBSET-OF-MERGESORTS-IS-SUBSETP))))
  (b* ((allvars (assoc :allvars symbolic-params))
       (vars (if allvars
                 (svexlist-vars-memo x)
               (ec-call (svarlist-fix (cdr (assoc :vars symbolic-params))))))
       (svars (mbe :logic (set::mergesort vars)
                   :exec (if (set::setp vars) vars (set::mergesort vars))))
       ((when allvars) (hons-copy svars))
       (keys (svarlist-filter (alist-keys env)))
       (keys (mbe :logic (set::mergesort keys)
                  :exec (if (set::setp keys) keys (set::mergesort keys)))))
    (hons-copy
     (mbe :logic (union keys svars)
          :exec (if (set::subset keys svars)
                    svars
                  (if (eq svars nil)
                      keys
                    (union keys svars))))))
  ///
  (local (defthm alist-keys-of-svex-env-fix
           (equal (alist-keys (svex-env-fix env))
                  (svarlist-filter (alist-keys env)))
           :hints(("Goal" :in-theory (enable svex-env-fix svarlist-filter)))))

  (defret svexlist-vars-for-symbolic-eval-sufficient
    (subsetp (intersection-equal (svexlist-vars x)
                                 (alist-keys (svex-env-fix env)))
             vars)
    :hints ((set-reasoning)))

  (defret member-of-svexlist-vars-for-symbolic-eval
    (implies (and (member v (svexlist-vars x))
                  (hons-assoc-equal v (svex-env-fix env)))
             (member v vars))
    :hints (("goal" :use svexlist-vars-for-symbolic-eval-sufficient
             :in-theory (disable svexlist-vars-for-symbolic-eval-sufficient
                                 svexlist-vars-for-symbolic-eval
                                 alist-keys-of-svex-env-fix))
            (set-reasoning))))


(defines svex-fastsubst
  :verify-guards nil
  (define svex-fastsubst
    :parents (svex-subst)
    :short "Substitution for @(see svex)es, identical to @(see svex-subst),
except that we memoize the results and we use fast alist lookups."
    ((pat svex-p)
     (al  svex-alist-p))
    :returns (x (equal x (svex-subst pat al))
                :hints ((and stable-under-simplificationp
                             '(:expand ((svex-subst pat al))))))
    :measure (svex-count pat)
    (svex-case pat
      :var (or (svex-fastlookup pat.name al)
               (svex-quote (4vec-x)))
      :quote (svex-fix pat)
      :call (svex-call pat.fn (svexlist-fastsubst pat.args al))))
  (define svexlist-fastsubst ((pat svexlist-p) (al svex-alist-p))
    :returns (x (equal x (svexlist-subst pat al))
                :hints ((and stable-under-simplificationp
                             '(:expand ((svexlist-subst pat al))))))
    :measure (svexlist-count pat)
    (if (atom pat)
        nil
      (cons (svex-fastsubst (car pat) al)
            (svexlist-fastsubst (cdr pat) al))))
  ///
  (verify-guards svex-fastsubst)
  (memoize 'svex-fastsubst :condition '(eq (svex-kind pat) :call)))


(define svexlist-x-out-unused-vars ((x svexlist-p)
                                    (svars svarlist-p)
                                    (do-it))
  :returns (new-x svexlist-p)
  (if do-it
      (b* ((subst (make-fast-alist (pairlis$ (svarlist-fix svars) (svarlist-svex-vars svars))))
           (ans (svexlist-fastsubst x subst)))
        (clear-memoize-table 'svex-fastsubst)
        (fast-alist-free subst)
        ans)
    (svexlist-fix x))
  ///
  (defthm svex-alist-eval-of-svarlist-svex-vars
    (equal (svex-alist-eval (pairlis$ (svarlist-fix svars)
                                      (svarlist-svex-vars svars))
                            env)
           (svex-env-extract svars env))
    :hints(("Goal" :in-theory (enable svex-env-extract svex-alist-eval svarlist-fix
                                      svarlist-svex-vars)
            :induct (len svars)
            :expand ((:free (x) (svex-eval (svex-var x) env))))))


  (defthm-svex-eval-flag
    (defthm svex-eval-of-svex-env-extract-when-intersection-subset
      (implies (subsetp (intersection$ (svex-vars x)
                                       (alist-keys (svex-env-fix env)))
                        (svarlist-fix svars))
               (equal (svex-eval x (svex-env-extract svars env))
                      (svex-eval x env)))
      :hints ('(:expand ((:free (env) (svex-eval x env))
                         (svex-vars x)))
              (and stable-under-simplificationp
                   '(:in-theory (enable svex-env-lookup)
                     :expand ((:free (x y) (subsetp-equal (list x) y))
                              (:free (x y) (intersection-equal (list x) y))))))
      :flag expr)
    (defthm svexlist-eval-of-svex-env-extract-when-intersection-subset
      (implies (subsetp (intersection$ (svexlist-vars x)
                                       (alist-keys (svex-env-fix env)))
                        (svarlist-fix svars))
               (equal (svexlist-eval x (svex-env-extract svars env))
                      (svexlist-eval x env)))
      :hints ('(:expand ((:free (env) (svexlist-eval x env))
                         (svexlist-vars x))))
      :flag list))

  (defret svex-eval-of-svexlist-x-out-unused-vars
    (implies (subsetp (intersection-equal (svexlist-vars x)
                                          (alist-keys (svex-env-fix env)))
                      (svarlist-fix svars))
             (equal (svexlist-eval new-x env)
                    (svexlist-eval x env))))


  (local (defthm hons-assoc-equal-of-pair-svex-vars
           (equal (hons-assoc-equal v (pairlis$ (svarlist-fix vars1) (svarlist-svex-vars vars1)))
                  (and (member v (svarlist-fix vars1))
                       (cons v (svex-var (svar-fix v)))))
           :hints(("Goal" :in-theory (enable hons-assoc-equal pairlis$ svarlist-svex-vars svarlist-fix)))))

  (local (defthm svex-lookup-of-pair-svex-vars
           (implies (equal vars (svarlist-fix vars1))
                    (equal (svex-lookup v (pairlis$ vars (svarlist-svex-vars vars1)))
                           (and (member (svar-fix v) vars)
                                (svex-var (svar-fix v)))))
           :hints(("Goal" :in-theory (enable svex-lookup)))))

  (local (defthm-svex-eval-flag
           (defthm vars-of-svex-subst-lemma
             (implies (and (not (member v (svex-vars x)))
                           (equal vars (svarlist-fix vars1)))
                      (not (member v (svex-vars (svex-subst x (pairlis$ vars (svarlist-svex-vars vars1)))))))
             :flag expr
             :hints ('(:expand ((:free (al) (svex-subst x al))))))
           (defthm vars-of-svexlist-subst-lemma
             (implies (and (not (member v (svexlist-vars x)))
                           (equal vars (svarlist-fix vars1)))
                      (not (member v (svexlist-vars (svexlist-subst x (pairlis$ vars (svarlist-svex-vars vars1)))))))
             :flag list
             :hints ('(:expand ((:free (al) (svexlist-subst x al))))))))

  (defret svex-vars-of-svexlist-x-out-unused-vars
    (implies (not (member v (svexlist-vars x)))
             (not (member v (svexlist-vars new-x)))))

  (local (defthm len-of-svexlist-subst
           (equal (len (svexlist-subst x subst))
                  (len x))
           :hints (("goal" :induct (len x)
                    :in-theory (enable svexlist-subst)))))

  (defret len-of-<fn>
    (equal (len new-x) (len x))))


(define symbolic-params-x-out-cond ((symbolic-params alistp))
  ;; Only makes sense to x out unused variables if
  ;;  - we're simplifying, so they'll get constant propagated, and
  ;;  - we're not using all vars, so there will be some substitutions.
  (and (cdr (assoc :simplify symbolic-params))
       (not (cdr (assoc :all-vars symbolic-params)))))



(define svexlist-eval-gl
  ((x svexlist-p     "Svex expressions to evaluate.")
   (env svex-env-p   "Bindings of variables to @(see 4vec) values.")
   (symbolic-params alistp
                    "Alist giving symbolic execution parameters; see below."))
  :short "Equivalent of svexlist-eval intended to work well under GL symbolic execution."
  :long "

<p>This function is provably equivalent to @(see svexlist-eval), but is
tailored to perform well under symbolic execution.  For symbolic execution, we
assume that the inputs to this function other than @('env') are fully concrete,
and that @('env') is symbolic only in its values, not its keys or its shape.</p>


<p>The @('symbolic-params') input is logically irrelevant, but allows important
optimizations for symbolic execution performance, discussed further below.  It
is safe (but not necessarily optimal) to call this with symbolic-params equal
@('NIL').</p>

<h4>Behavior under Symbolic Execution</h4>

<ol>

<li>Applies rewriting to the supplied svex expressions, if @(':SIMPLIFY') is
bound to a non-nil value in the @('symbolic-params') input -- see @(see
svexlist-rewrite-fixpoint).</li>

<li>If @(':boolmasks') is bound in the symbolic-params, compares the given
@('env') with the bound value, which should be an alist.  If there is a pair
@('(name . mask)') in the boolmasks alist for which the binding for @('name')
in env is not Boolean-valued on the bits set to 1 in @('mask'), then fail out
of symbolic simulation.  (In AIG mode, the masked bits must be
<i>syntactically</i> Boolean-valued -- practically speaking, this means the
upper/lower parts should result from the same computation.)</li>

<li>If @(':VARS') is bound in symbolic-params, it should be bound to a list of
input variables of the SVTV.  Unions this list with the variables bound in
@('env') to obtain the full list of variables to bind as inputs to the SVTV.
Or if @(':ALLVARS') is bound in symbolic params, all the variables in the svex
expressions are used instead.</li>

<li>Compiles the svex list @('x') into @(see a4vec) objects, a symbolic
analogue of @(see 4vec) but with each bit an AIG -- see @(see
svexlist->a4vecs-for-varlist).  This computation uses the assumptions, checked
in the two steps above, that only the variables in @('vars') are non-X, and
that the masked bits in @('boolmasks') are Boolean-valued. These assumptions
can reduce the complexity of the generated AIGs.  (Note everything used in this
computation is concrete -- the @('env') isn't involved.)</li>

<li>Creates an alist binding the AIG variables used in the above step to the
appropriate symbolic bits from @('env').</li>

<li>Symbolically evaluates each of the a4vec objects from step 4 under the
bindings from step 5 using GL's symbolic simulator of @(see acl2::aig-eval).
This results in GL-native symbolic 4vec objects, which is the result we
want.</li>

</ol>

<h4>Optimization using the Extra Arguments</h4>

<p>Performance of symbolic execution (and SAT solving, when in AIG mode) is
related to the size of the AIGs produced by the svex to AIG
transformation (step 4, above).  Two ways to decrease that size are (1) to turn
certain variables into constant Xes, if it is known that they're irrelevant,
and (2) to assume certain bits of some variables are Boolean-valued, which
means it can be represented by just one AIG variable rather than two.</p>

<p>Another performance consideration is that the transformation to AIGs is
itself sometimes significant.  Especially for theorems proved by
case-splitting, it is important not to need to repeat this transformation for
each case.  The function that does the transformation is memoized, but it is
important in this case that it always be called with the same arguments.</p>

<p>The @('vars') list pertains to optimization (1): if not present in the list,
a variable in the svex expressions will just be replaced with an X.  Therefore,
in general it's best to use exactly the set of variables bound in the
environment.  However, it may not be worth it to redo the AIG conversion each
time the environment's bound variables changes, so we take @('vars')
separately.</p>

<p>The @('boolmasks') allows optimization (2).  It is best for symbolic
execution performance to bind every variable in @('vars') to -1, but this may
fail if the @('env') is not constructed in such a way that the values are
obviously 2-vectors.</p>"
  :guard-hints (("goal" :in-theory (e/d (SET::UNION-WITH-SUBSET-LEFT)
                                        (SUBSET-OF-MERGESORTS-IS-SUBSETP))))
  (b* ((env (make-fast-alist (svex-env-fix env)))
       (svars (svexlist-vars-for-symbolic-eval x env symbolic-params))
       (x (svexlist-x-out-unused-vars x svars
                                      (symbolic-params-x-out-cond symbolic-params)))
       (x (maybe-svexlist-rewrite-fixpoint x (cdr (assoc :simplify symbolic-params))))
       (boolmasks (make-fast-alist
                   (hons-copy
                    (ec-call
                     (svar-boolmasks-fix (cdr (assoc :boolmasks symbolic-params)))))))
       ((unless (svex-env-check-boolmasks boolmasks env))
        (b* ((?ign (cw "ERROR: some bits assumed to be Boolean were not~%"))
             (?ign (gl::gl-error 'boolcheck-failed)))
          (gl::gl-hide (svexlist-eval x env))))
       ;; (?ign (cw "Boolmasks: ~x0~%" boolmasks))
       ;; (?ign (bitops::sneaky-push 'boolmasks boolmasks))
       ;; (?ign (bitops::sneaky-push 'vars vars))
       ;; (?ign (bitops::sneaky-push 'x x))
       ((mv err a4vecs) (time$ (svexlist->a4vecs-for-varlist x svars boolmasks)
                               :msg "; svex->aigs: ~st sec, ~sa bytes.~%"))
       ((when err)
        (b* ((?ign (cw "ERROR gathering AIG bits for variables: ~@0~%" err))
             (?ign (gl::gl-error 'a4env-failed)))
          (gl::gl-hide (svexlist-eval x env))))
       ((mv ?err aig-env)
        ;; ignore the error; it can't exist if the above doesn't
        (time$ (svexlist->a4vec-aig-env-for-varlist x svars boolmasks env)
               :msg "; env -> aig env: ~st sec, ~sa bytes.~%"))
       (?ign (fast-alist-free env))
       (aig-env (make-fast-alist aig-env))
       (ans (a4veclist-eval a4vecs aig-env)))
    (fast-alist-free aig-env)
    ans)
  ///
  (defthm svexlist-eval-gl-is-svexlist-eval
    (equal (svexlist-eval-gl x env symbolic-params)
           (svexlist-eval x env))
    :hints (("goal" :use ((:instance svexlist->a4vec-for-varlist-correct
                           (boolmasks
                            (svar-boolmasks-fix (cdr (assoc :boolmasks symbolic-params))))
                           (vars (svexlist-vars-for-symbolic-eval
                                  x env symbolic-params))
                           (x (maybe-svexlist-rewrite-fixpoint
                               (svexlist-x-out-unused-vars
                                x
                                (svexlist-vars-for-symbolic-eval x env symbolic-params)
                                (symbolic-params-x-out-cond symbolic-params))
                               (cdr (assoc :simplify symbolic-params))))
                           (env (svex-env-fix env))))
             :in-theory (disable svexlist->a4vec-for-varlist-correct
                                 SVEXLIST->A4VECS-FOR-VARLIST-SVAR-BOOLMASKS-EQUIV-CONGRUENCE-ON-BOOLMASKS))
            (set-reasoning)
            (and stable-under-simplificationp
                 '(:cases ((member acl2::k0 (svexlist-vars x)))))))

  (gl::def-gl-rewrite svexlist-eval-for-symbolic-redef
    (equal (svexlist-eval-for-symbolic x env symbolic-params)
           (svexlist-eval-gl x env symbolic-params))))



;;; Now rework a4veclist-eval to phrase it in terms of a single call to aig-eval-list

(define a4vec->aiglist ((x a4vec-p))
  :returns (lst true-listp :rule-classes :type-prescription)
  (b* (((a4vec x) x))
    (append x.upper x.lower)))



;; (define v2i-alt ((v true-listp))
;;   :returns (v2i (equal v2i (gl::v2i v))
;;                 :hints(("Goal" :in-theory (enable gl::scdr gl::s-endp))))
;;   :hooks nil
;;   (if (atom (cdr v))
;;       (gl::bool->sign (car v))
;;     (logcons (acl2::bool->bit (car v))
;;              (v2i-alt (cdr v)))))


(local (defthm v2i-of-aig-eval-list
         (equal (gl::v2i (aig-eval-list x env))
                (aig-list->s x env))
         :hints(("Goal" :in-theory (enable (:i aig-list->s) gl::v2i gl::scdr gl::s-endp)
                 :induct (aig-list->s x env)
                 :expand ((aig-list->s x env)
                          (aig-eval-list x env)
                          (:free (A b) (gl::v2i (cons a b))))))))

(define v2i-first-n ((n natp) (v true-listp))
  :returns (v2i (equal v2i (gl::v2i (take n v)))
                :hints(("Goal" :in-theory (e/d (acl2::take)
                                               (acl2::take-of-too-many))
                        :induct t)))
  :prepwork ((local (defthm v2i-of-singleton
                      (equal (gl::v2i (list x))
                             (gl::bool->sign x))
                      :hints(("Goal" :in-theory (enable gl::s-endp gl::v2i)))))
             (local (defthm v2i-of-cons
                      (implies (consp y)
                               (equal (gl::v2i (cons x y))
                                      (logapp 1 (bool->bit x) (gl::v2i y))))
                      :hints(("Goal" :in-theory (enable gl::v2i logapp** gl::s-endp gl::scdr))))))
  (cond ((zp n)
         (gl::bool->sign nil))
        ((eql n 1)
         (gl::bool->sign (car v)))
        (t (logapp 1 (acl2::bool->bit (car v))
                    (v2i-first-n (1- n) (cdr v))))))


(define 4vec-from-bitlist ((upper-len natp) (lower-len natp) (bits true-listp))
  :hooks ((:fix :omit (bits)))
  :returns (mv (vec 4vec-p)
               (rest true-listp
                     :hyp (true-listp bits)
                     :rule-classes :type-prescription))
  ;; note: list-fixing bits is bad here because it's not even linear in the
  ;; number of bits we're operating on
  (b* ((upper (v2i-first-n upper-len bits))
       (rest (nthcdr upper-len bits))
       (lower (v2i-first-n lower-len rest))
       (rest (nthcdr lower-len rest)))
    (mv (4vec upper lower)
        rest))
  ///
  (defthm 4vec-from-bitlist-correct
    (b* (((a4vec x) x))
      (equal (4vec-from-bitlist (len x.upper) (len x.lower)
                                (append (aig-eval-list (a4vec->aiglist x) env)
                                        rest))
             (mv (a4vec-eval x env) rest)))
    :hints(("Goal" :in-theory (enable a4vec->aiglist)))))

(define a4veclist->aiglist ((x a4veclist-p))
  :returns (aigs true-listp :rule-classes :type-prescription)
  (if (atom x)
      nil
    (append (a4vec->aiglist (car x))
            (a4veclist->aiglist (cdr x)))))

(define 4veclist-from-bitlist ((origs a4veclist-p) (bits true-listp))
  :returns (4vecs 4veclist-p)
  :hooks ((:fix :omit (bits)))
  (b* (((when (atom origs)) nil)
       ((a4vec x) (car origs))
       ((mv first restbits)
        (4vec-from-bitlist (len x.upper) (len x.lower) bits)))
    (cons first (4veclist-from-bitlist (cdr origs) restbits)))
  ///
  (defthm 4veclist-from-bitlist-correct
    (equal (4veclist-from-bitlist x (aig-eval-list (a4veclist->aiglist x) env))
           (a4veclist-eval x env))
    :hints(("Goal" :in-theory (enable a4veclist-eval
                                      a4veclist->aiglist)))))


(define a4veclist-eval-gl ((x a4veclist-p) (env))
  :returns (res 4veclist-p)
  (b* ((aiglist (time$ (a4veclist->aiglist x)
                       :msg "; SV bit-blasting: a4veclist->aiglist: ~st sec, ~sa bytes.~%"))
       (bitlist (time$ (aig-eval-list aiglist env)
                       :msg "; SV bit-blasting: aig-eval-list: ~st sec, ~sa bytes.~%")))
    (time$ (4veclist-from-bitlist x bitlist)
           :msg "; bits->4vecs: ~st sec, ~sa bytes.~%"))
  ///
  (defthm a4veclist-eval-gl-correct
    (equal (a4veclist-eval-gl x env)
           (a4veclist-eval x env)))

  (gl::def-gl-rewrite a4veclist-eval-redef
    (equal (a4veclist-eval x env)
           (a4veclist-eval-gl x env))))





(gl::def-gl-rewrite svex-alist-eval-gl-rewrite
    (equal (svex-alist-eval x env)
           (pairlis$ (svex-alist-keys x)
                     (svexlist-eval-for-symbolic
                      (svex-alist-vals x) env nil)))
    :hints(("Goal" :in-theory (enable svex-alist-eval pairlis$ svex-alist-keys
                                      svex-alist-vals svexlist-eval))))

(gl::def-gl-rewrite svex-eval-gl-rewrite
  (equal (svex-eval x env)
         (car (svexlist-eval-for-symbolic (list x) env nil))))





(define svex-envlist-keyset ((x svex-envlist-p))
  :returns (keys (and (svarlist-p keys)
                      (set::setp keys)))
  (if (atom x)
      nil
    (set::union (set::mergesort (svarlist-filter (alist-keys (car x))))
                (svex-envlist-keyset (cdr x))))
  ///
  (local (defthm alist-keys-of-svex-env-fix
           (equal (alist-keys (svex-env-fix env))
                  (svarlist-filter (alist-keys env)))
           :hints(("Goal" :in-theory (enable svex-env-fix svarlist-filter)))))

  (defret svex-envlist-keyset-sufficient
    (implies (member env x)
             (subsetp (alist-keys (svex-env-fix env))
                      keys))))


(define svexlist/env-list-vars-for-symbolic-eval ((x svexlist-p)
                                                  (envs svex-envlist-p)
                                                  (symbolic-params alistp))
  :returns (vars svarlist-p)
  :guard-hints (("goal" :in-theory (e/d (SET::UNION-WITH-SUBSET-LEFT
                                         double-containment
                                         set::subset-to-subsetp)
                                        (SUBSET-OF-MERGESORTS-IS-SUBSETP))))
  (b* ((allvars (assoc :allvars symbolic-params))
       (vars (if allvars
                 (svexlist-vars-memo x)
               (ec-call (svarlist-fix (cdr (assoc :vars symbolic-params))))))
       (svars (mbe :logic (set::mergesort vars)
                   :exec (if (set::setp vars) vars (set::mergesort vars))))
       ((when allvars) (hons-copy svars))
       (keys (svex-envlist-keyset envs)))
    (hons-copy
     (mbe :logic (union keys svars)
          :exec (if (set::subset keys svars)
                    svars
                  (if (eq svars nil)
                      keys
                    (union keys svars))))))
  ///

  (defret svexlist/env-list-vars-for-symbolic-eval-sufficient
    (subsetp (intersection-equal (svexlist-vars x)
                                 (svex-envlist-keyset envs))
             vars)
    :hints ((set-reasoning))))

(define svex-envlist-check-boolmasks ((boolmasks svar-boolmasks-p)
                                      (envs svex-envlist-p))
  (if (atom envs)
      t
    (and (svex-env-check-boolmasks boolmasks (make-fast-alist (car envs)))
         (svex-envlist-check-boolmasks boolmasks (cdr envs))))

  ///

  (defthm svex-envlist-check-boolmasks-correct
    (implies (and (svex-envlist-check-boolmasks boolmasks envs)
                  (member env envs)
                  ;; (svex-env-p env)
                  (svar-boolmasks-p boolmasks))
             (svex-env-boolmasks-ok env boolmasks))))

(fty::deflist a4veclistlist :elt-type a4veclist :true-listp t)

(define a4veclist/env-list-eval ((x a4veclistlist-p)
                                 (envs))
  :guard (equal (len envs) (len x))
  :returns (4vecs 4veclistlist-p)
  (if (atom x)
      nil
    (cons (a4veclist-eval (car x) (car envs))
          (a4veclist/env-list-eval (cdr x) (cdr envs)))))


(define svexlistlist->a4vec ((x svexlistlist-p)
                             (env svex-a4vec-env-p)
                             (masks svex-mask-alist-p))
  :returns (a4vecs a4veclistlist-p)
  (if (atom x)
      nil
    (cons (svexlist->a4vec (car x) env masks)
          (svexlistlist->a4vec (cdr x) env masks))))


(define a4vec/svex-env-eval ((x a4veclist-p)
                             (env svex-env-p)
                             (svexes svexlist-p)
                             (svars svarlist-p)
                             (boolmasks svar-boolmasks-p))
  :guard (svex-maskbits-ok svars (svexlist-mask-alist svexes))
  :returns (4vecs 4veclist-p)
  :hooks ((:fix :args (x svexes svars)))
  (b* ((env (make-fast-alist env))
       ((mv ?err aig-env)
        ;; ignore the error; it can't exist svex-maskbits-ok
        (svexlist->a4vec-aig-env-for-varlist svexes svars boolmasks env))
       (?ign (fast-alist-free env))
       (aig-env (make-fast-alist aig-env))
       (ans (a4veclist-eval x aig-env)))
    (fast-alist-free aig-env)
    ans)
  ///
  (local (defthm not-svexlist-full-masks-p-by-member
           (implies (And (not (equal (sparseint-val (svex-mask-lookup x masks)) -1))
                         (member x svexes))
                    (not (svexlist-full-masks-p svexes masks)))
           :hints(("Goal" :in-theory (enable member svexlist-full-masks-p)))))

  (defthm svexlist-full-masks-p-when-subset
    (implies (and (subsetp-equal some-svexes svexes)
                  (svexlist-full-masks-p svexes masks))
             (svexlist-full-masks-p some-svexes masks))
    :hints(("Goal" :in-theory (enable subsetp-equal svexlist-full-masks-p))))

  (defret a4vec/svex-env-eval-correct
    :pre-bind ((masks (svexlist-mask-alist svexes))
               ((mv ?err a4env) (svex-varmasks->a4env svars masks boolmasks1))
               (x (svexlist->a4vec some-svexes a4env masks)))
    (implies (and (svex-maskbits-ok svars masks)
                  (subsetp some-svexes svexes)
                  (equal boolmasks (svar-boolmasks-fix boolmasks1))
                  (svex-env-boolmasks-ok env boolmasks)
                  (subsetp (intersection-equal (svexlist-vars some-svexes)
                                               (alist-keys (svex-env-fix env)))
                           (svarlist-fix svars)))
             (equal 4vecs
                    (svexlist-eval some-svexes env)))
    :hints(("Goal" :in-theory (e/d (svexlist->a4vec-aig-env-for-varlist)
                                   (SVEXLIST->A4VEC-CORRECT))))))

(define a4veclist/svex-env-list-eval ((x a4veclistlist-p)
                                      (envs svex-envlist-p)
                                      (svexes svexlist-p)
                                      (svars svarlist-p)
                                      (boolmasks svar-boolmasks-p))
  :guard (and (equal (len envs) (len x))
              (svex-maskbits-ok svars (svexlist-mask-alist svexes)))
  :returns (4vecs 4veclistlist-p)
  :hooks ((:fix :args (x svexes svars)))
  (if (atom x)
      nil
    (cons (a4vec/svex-env-eval (car x) (car envs) svexes svars boolmasks)
          (a4veclist/svex-env-list-eval (cdr x) (cdr envs) svexes svars boolmasks)))
  ///
  (local (defthm alist-keys-of-svex-env-fix
           (equal (alist-keys (svex-env-fix env))
                  (svarlist-filter (alist-keys env)))
           :hints(("Goal" :in-theory (enable svex-env-fix svarlist-filter)))))

  (defret a4veclist/svex-env-list-eval-correct
    :pre-bind ((masks (svexlist-mask-alist svexes))
               ((mv ?err a4env) (svex-varmasks->a4env svars masks boolmasks1))
               (x (svexlistlist->a4vec some-svexes a4env masks)))
    (implies (and (svex-maskbits-ok svars masks)
                  (equal (len envs) (len some-svexes))
                  (subsetp (append-lists some-svexes) svexes)
                  (equal boolmasks (svar-boolmasks-fix boolmasks1))
                  (svex-envlist-check-boolmasks boolmasks envs)
                  (subsetp (intersection-equal (svexlist-vars (append-lists some-svexes))
                                               (svex-envlist-keyset envs))
                           (svarlist-fix svars)))
             (equal 4vecs
                    (svexlist/env-list-eval some-svexes envs)))
    :hints (("goal" :induct (svexlist/env-list-eval some-svexes envs)
             :in-theory (e/d (svexlist/env-list-eval
                              svex-envlist-check-boolmasks
                              append-lists
                              svex-envlist-keyset
                              svexlistlist->a4vec))))))

(local (in-theory (enable svexlist->a4vecs-for-varlist)))

(local (defthm a4veclistlist-p-of-extract-lists
         (implies (and (a4veclist-p list)
                       (<= (sum-of-lengths x) (len list)))
                  (a4veclistlist-p (extract-lists x list)))
    :hints (("goal" :use ((:functional-instance element-listlist-p-of-extract-lists
                           (acl2::element-p a4vec-p)
                           (acl2::element-list-p a4veclist-p)
                           (acl2::element-list-final-cdr-p (lambda (x) (eq x nil)))
                           (element-listlist-p a4veclistlist-p)))))))



(defsection svexlist/env-list-eval-of-extract-of-rewrite
  (local (include-book "svex-equivs"))

  (local (define svex-eval-same-on-envs (x y envs)
           :verify-guards nil
           (if (atom envs)
               t
             (and (equal (svex-eval x (car envs))
                         (svex-eval y (car envs)))
                  (svex-eval-same-on-envs x y (cdr envs))))
           ///
           (defthm svex-eval-same-on-envs-implies-eval-same-with-member
             (implies (and (svex-eval-same-on-envs x y envs)
                           (member env envs))
                      (equal (svex-eval x env)
                             (svex-eval y env))))

           (defthm svex-eval-same-on-envs-when-svex-eval-equiv
             (implies (svex-eval-equiv x y)
                      (svex-eval-same-on-envs x y envs)))))

  (local (define svexlist-eval-same-on-envs (x y envs)
           :verify-guards nil
           (if (atom x)
               t
             (and (svex-eval-same-on-envs (car x) (car y) envs)
                  (svexlist-eval-same-on-envs (cdr x) (cdr y) envs)))
           ///
           (defthm svexlist-eval-same-on-envs-implies-svexlist-eval-same-with-member
             (implies (and (svexlist-eval-same-on-envs x y envs)
                           (member env envs)
                           (equal (len x) (len y)))
                      (equal (svexlist-eval x env)
                             (svexlist-eval y env))))
           (local (defun ind (n x y)
                    (if (zp n)
                        (list x y)
                      (ind (1- n) (cdr x) (cdr y)))))

           (defthm svex-eval-same-on-envs-of-nth-when-svexlist-eval-same-on-envs
             (implies (and (svexlist-eval-same-on-envs x y envs)
                           (< (nfix n) (len x)))
                      (svex-eval-same-on-envs (nth n x) (nth n y) envs))
             :hints(("Goal" :in-theory (enable nth svex-eval-same-on-envs)
                     :induct (ind n x y))))

           (local (defthm svexlist-eval-equiv-implies-svex-eval-equiv-car
                    (implies (and (svexlist-eval-equiv x y)
                                  (consp x))
                             (equal (svex-eval-equiv (car x) (car y)) t))
                    :hints (("goal" :in-theory (enable svex-eval-equiv)))))

           (defthm svexlist-eval-same-on-envs-when-svexlist-eval-equiv
             (implies (svexlist-eval-equiv x y)
                      (svexlist-eval-same-on-envs x y envs)))

           (defthm svexlist-eval-same-on-envs-of-atom
             (implies (atom envs)
                      (svexlist-eval-same-on-envs x y envs))
             :hints(("Goal" :in-theory (enable svex-eval-same-on-envs))))

           (defthm svexlist-eval-same-on-envs-of-consp
             (implies (and (consp envs)
                           (equal (len x) (len y))
                           (svexlist-eval-same-on-envs x y (cdr envs)))
                      (iff (svexlist-eval-same-on-envs x y envs)
                           (equal (svexlist-eval x (car envs))
                                  (svexlist-eval y (car envs)))))
             :hints(("Goal" :in-theory (enable svex-eval-same-on-envs))))))



  (local (define svexlistlist-eval-same-on-envs (x y envs)
           :verify-guards nil
           (if (atom x)
               t
             (and (svexlist-eval-same-on-envs (car x) (car y) envs)
                  (svexlistlist-eval-same-on-envs (cdr x) (cdr y) envs)))
           ///
           (local (defun ind (x y envs1)
                    (if (atom x)
                        (list y envs1)
                      (ind (cdr x) (cdr y) (cdr envs1)))))

           ;; (defthm svexlistlist-eval-same-on-envs-implies-svexlist-eval-same-with-member
           ;;   (implies (and (svexlistlist-eval-same-on-envs x y envs)
           ;;                 (member env envs)
           ;;                 (equal (len x) (len y)))
           ;;            (equal (svexlist-eval x env)
           ;;                   (svexlist-eval y env))))

           (defthm svexlist/env-list-eval-when-svexlistlist-eval-same-on-envs
             (implies (and (svexlistlist-eval-same-on-envs x y envs)
                           (subsetp envs1 envs)
                           (equal (len x) (len y))
                           (lengths-equal x y)
                           (equal (len x) (len envs1)))
                      (equal (svexlist/env-list-eval x envs1)
                             (svexlist/env-list-eval y envs1)))
             :hints(("Goal" :in-theory (enable svexlist/env-list-eval
                                               subsetp-equal
                                               lengths-equal)
                     :induct (ind x y envs1))))))



  (local (defthm svexlist-eval-equiv-of-maybe-svexlist-rewrite-fixpoint
           (svexlist-eval-equiv (maybe-svexlist-rewrite-fixpoint x do-it) x)
           :hints(("Goal" :in-theory (enable svexlist-eval-equiv)))))


  (local (defthm alist-keys-of-svex-env-fix
           (equal (alist-keys (svex-env-fix env))
                  (svarlist-filter (alist-keys env)))
           :hints(("Goal" :in-theory (enable svex-env-fix svarlist-filter)))))

  (local (defthm svexlist-eval-equiv-of-svexlist-x-out-unused-vars
           (implies (subsetp (intersection-equal (svexlist-vars x)
                                                 (svex-envlist-keyset envs))
                             (svarlist-fix svars))
                    (svexlist-eval-same-on-envs
                     x
                     (maybe-svexlist-rewrite-fixpoint
                      (svexlist-x-out-unused-vars x svars do-it)
                      do-it1)
                     envs))
           :hints(("Goal" :in-theory (e/d (svex-envlist-keyset)
                                          ())
                   :induct (len envs)))))


  (local (defthm svex-eval-equiv-listlist-of-extract-lists-of-rewrite
           (implies (subsetp (intersection-equal (svexlist-vars (append-lists x))
                                                 (svex-envlist-keyset envs))
                             (svarlist-fix svars))
                    (svexlistlist-eval-same-on-envs
                     x
                     (extract-lists x (maybe-svexlist-rewrite-fixpoint
                                       (svexlist-x-out-unused-vars
                                        (append-lists x)
                                        svars
                                        do-it1)
                                       do-it))
                     envs))
           :hints (("goal" :use ((:functional-instance
                                  extract-lists-of-pseudoproj
                                  (pseudoproj (lambda (x)
                                                (if (subsetp (intersection-equal (svexlist-vars x)
                                                                                 (svex-envlist-keyset envs))
                                                             (svarlist-fix svars))
                                                    (maybe-svexlist-rewrite-fixpoint
                                                     (svexlist-x-out-unused-vars x svars do-it1) do-it)
                                                  x)))
                                  (pseudoproj-relation
                                   (lambda (x y)
                                     (svex-eval-same-on-envs x y envs)))
                                  (pseudoproj-relation-list
                                   (lambda (x y)
                                     (svexlist-eval-same-on-envs x y envs)))
                                  (pseudoproj-relation-listlist
                                   (lambda (x y)
                                     (svexlistlist-eval-same-on-envs x y envs))))))
                   (and stable-under-simplificationp
                        '(:in-theory (enable svexlist-eval-same-on-envs
                                             svexlistlist-eval-same-on-envs))))))

  (defthm svexlist/env-list-eval-of-extract-lists-of-rewrite
    (implies (and (subsetp (intersection-equal (svexlist-vars (append-lists x))
                                               (svex-envlist-keyset envs))
                           (svarlist-fix svars))
                  (equal (len envs) (len x)))
             (equal (svexlist/env-list-eval (extract-lists x (maybe-svexlist-rewrite-fixpoint
                                                              (svexlist-x-out-unused-vars
                                                               (append-lists x)
                                                               svars
                                                               do-it1)
                                                              do-it))
                                            envs)
                    (svexlist/env-list-eval x envs)))
    :hints (("goal" :use ((:instance svexlist/env-list-eval-when-svexlistlist-eval-same-on-envs
                           (x x)
                           (y (extract-lists x (maybe-svexlist-rewrite-fixpoint
                                                              (svexlist-x-out-unused-vars
                                                               (append-lists x)
                                                               svars
                                                               do-it1)
                                                              do-it)))
                           (envs envs)
                           (envs1 envs)))
             :in-theory (disable svexlist/env-list-eval-when-svexlistlist-eval-same-on-envs)
             :do-not-induct t))))




(define svexlist/env-list-eval-gl
  ((x svexlistlist-p     "Svex expressions to evaluate.")
   (envs svex-envlist-p   "Bindings of variables to @(see 4vec) values.")
   (symbolic-params alistp
                    "Alist giving symbolic execution parameters; see below."))
  :short "Equivalent of svexlist/env-list-eval intended to work well under GL symbolic execution."
  :long "

<p>This function is provably equivalent to @('svexlist/env-list-eval'), but is
tailored to perform well under symbolic execution.  For symbolic execution, we
assume that the inputs to this function other than @('envs') are fully concrete,
and that each @('envs') are symbolic only in its values, not its keys or its shape.</p>

<p>It is analogous to @(see svexlist-eval-gl), but the individual lists of
svexes within @('x') are each evaluated with the corresponding element of
@('envs').  Symbolic execution is set up so that the svexes are all rendered
into AIGs in a batch with memoization between all the lists.</p>

<p>The @('symbolic-params') input behaves as it does in @(see
svexlist-eval-gl).  However, the @(':boolmasks') and @(':vars') entries must be
applicable to all environments in the list.  That is, for each entry in the
boolmasks, the corresponding key must be bound in every entry in the envs to a
symbolic 4vec value that is (syntactically) Boolean-valued in the masked
bits. Similarly, the @(':vars') entry, if given, is unioned with the variables
bound in all environments.</p>"
  :guard-hints (("goal" :in-theory (e/d (SET::UNION-WITH-SUBSET-LEFT)
                                        (SUBSET-OF-MERGESORTS-IS-SUBSETP))))
  :guard-debug t
  (b* ((envs (take (len x) envs))
       (x (svexlistlist-fix x))
       (svexes (append-lists x))
       (svars (svexlist/env-list-vars-for-symbolic-eval svexes envs symbolic-params))
       (svexes (svexlist-x-out-unused-vars svexes svars
                                           (symbolic-params-x-out-cond symbolic-params)))
       (svexes (maybe-svexlist-rewrite-fixpoint svexes (cdr (assoc :simplify symbolic-params))))
       (boolmasks (make-fast-alist
                   (hons-copy
                    (ec-call
                     (svar-boolmasks-fix (cdr (assoc :boolmasks symbolic-params)))))))
       ((unless (svex-envlist-check-boolmasks boolmasks envs))
        (b* ((?ign (cw "ERROR: some bits assumed to be Boolean were not~%"))
             (?ign (gl::gl-error 'boolcheck-failed)))
          (gl::gl-hide (svexlist/env-list-eval x envs))))
       ((mv err a4vecs) (time$ (svexlist->a4vecs-for-varlist svexes svars boolmasks)
                               :msg "; svex->aigs: ~st sec, ~sa bytes.~%"))
       ((when err)
        (b* ((?ign (cw "ERROR gathering AIG bits for variables: ~@0~%" err))
             (?ign (gl::gl-error 'a4env-failed)))
          (gl::gl-hide (svexlist/env-list-eval x envs))))
       (a4veclist-list (extract-lists x a4vecs)))
    (a4veclist/svex-env-list-eval a4veclist-list
                                  envs
                                  svexes
                                  svars
                                  boolmasks))
  ///
  (local (defthm svexlist/env-list-eval-of-take
           (equal (svexlist/env-list-eval x (take (len x) envs))
                  (svexlist/env-list-eval x envs))
           :hints(("Goal" :in-theory (enable svexlist/env-list-eval)))))

  (local (defthm extract-lists-of-svexlist->a4vec
           (implies (<= (sum-of-lengths x) (len y))
                    (equal (extract-lists x (svexlist->a4vec y env masks))
                           (svexlistlist->a4vec (extract-lists x y) env masks)))
           :hints (("goal" :use ((:functional-instance extract-lists-of-projection
                                  (acl2::element-p (lambda (x) t))
                                  (acl2::outelement-p (lambda (x) t))
                                  (acl2::outelement-example (lambda () t))
                                  (acl2::element-xformer (lambda (x) (svex->a4vec x env masks)))
                                  (acl2::elementlist-projection (lambda (x) (svexlist->a4vec x env masks)))
                                  (elementlistlist-projection (lambda (x) (svexlistlist->a4vec x env masks)))))
                    :in-theory (enable svexlistlist->a4vec
                                       svexlist->a4vec)))))

  (local (defthm vars-subset-lemma
           (b* ((vars (SVEXLIST/ENV-LIST-VARS-FOR-SYMBOLIC-EVAL
                       svexes
                       envs
                       params)))
             (SUBSETP-EQUAL (INTERSECTION-EQUAL
                             (SVEXLIST-VARS
                              (MAYBE-SVEXLIST-REWRITE-FIXPOINT
                               (SVEXLIST-X-OUT-UNUSED-VARS svexes
                                                           vars
                                                           x-out)
                               simp))
                             (SVEX-ENVLIST-KEYSET envs))
                            vars))
           :hints (("goal" :use ((:instance svexlist/env-list-vars-for-symbolic-eval-sufficient
                                  (x svexes) (symbolic-params params)))
                    :in-theory (disable svexlist/env-list-vars-for-symbolic-eval-sufficient))
                   (set-reasoning))))


  (defthm svexlist/env-list-eval-gl-correct
    (equal (svexlist/env-list-eval-gl x envs symbolic-params)
           (svexlist/env-list-eval x envs))
    :hints (("goal" :do-not-induct t)))

  (gl::def-gl-rewrite svexlist/env-list-eval-for-symbolic-redef
    (equal (svexlist/env-list-eval x envs)
           (svexlist/env-list-eval-gl x envs nil))))
