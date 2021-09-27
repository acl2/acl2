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
(include-book "address")
(include-book "../svex/eval")
(include-book "../svex/4vmask")
(include-book "../svex/vars")
(include-book "../svex/rsh-concat")
(include-book "../svex/nrev")
(include-book "std/stobjs/1d-arr" :dir :system)
(include-book "std/alists/hons-remove-assoc" :dir :system) ;; bozo
(include-book "defsort/defsort" :dir :system)
(local (include-book "std/lists/sets" :dir :system))
(local (include-book "std/lists/update-nth" :dir :system))
(local (include-book "std/lists/acl2-count" :dir :system))
(local (include-book "std/basic/arith-equivs" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "std/alists/fast-alist-clean" :dir :system))
(local (include-book "centaur/vl/util/default-hints" :dir :system))

(local (std::add-default-post-define-hook :fix))

(local (acl2::ruletable-delete-tags! acl2::listp-rules (:osets :duplicated-members)))

(defxdoc lhs.lisp :parents (lhs))
(local (xdoc::set-default-parents lhs.lisp))

(local (defthm equal-of-len
         (implies (syntaxp (quotep n))
                  (equal (equal (len x) n)
                         (if (atom x)
                             (eql n 0)
                           (and (posp n)
                                (eql (len (cdr x)) (1- n))))))))

(define lhssvex-unbounded-p ((x svex-p))
  :measure (svex-count x)
  :hints ('(:in-theory (enable equal-of-len)))
  :guard-hints (("goal" :in-theory (enable equal-of-len)))
  (svex-case x
    :var t
    :quote (equal x.val (4vec-z))
    :call
    (case x.fn
      (concat (b* (((unless (eql (len x.args) 3)) nil)
                   ((list w lo hi) x.args))
                (and (eq (svex-kind w) :quote)
                     (4vec-index-p (svex-quote->val w))
                     (lhssvex-unbounded-p lo)
                     (lhssvex-unbounded-p hi))))
      (rsh (b* (((unless (eql (len x.args) 2)) nil)
                ((list sh xx) x.args))
             (and (eq (svex-kind sh) :quote)
                  (4vec-index-p (svex-quote->val sh))
                  (lhssvex-unbounded-p xx)))))))


(define lhssvex-range-p ((rsh natp) (w natp) (x svex-p))
  :measure (svex-count x)
  :hints ('(:in-theory (enable equal-of-len)))
  :guard-hints (("goal" :in-theory (enable equal-of-len)))
  (if (zp w)
      t
    (svex-case x
      :var t
      :quote (equal x.val (4vec-z))
      :call
      (case x.fn
        (concat (b* (((unless (eql (len x.args) 3)) nil)
                     ((list w1 lo hi) x.args))
                  (and (eq (svex-kind w1) :quote)
                       (4vec-index-p (svex-quote->val w1))
                       (b* ((w1 (2vec->val (svex-quote->val w1))))
                         (cond ((<= w1 (lnfix rsh))
                                (lhssvex-range-p (- (lnfix rsh) w1) w hi))
                               ((<= (+ (lnfix rsh) w) w1)
                                (lhssvex-range-p rsh w lo))
                               (t (and (lhssvex-range-p rsh (- w1 (lnfix rsh)) lo)
                                       (lhssvex-range-p 0 (- (+ w (lnfix rsh)) w1) hi))))))))
        (rsh (b* (((unless (eql (len x.args) 2)) nil)
                  ((list sh xx) x.args))
               (and (eq (svex-kind sh) :quote)
                    (4vec-index-p (svex-quote->val sh))
                    (lhssvex-range-p (+ (lnfix rsh) (2vec->val (svex-quote->val sh))) w xx))))))))

(define lhssvex-bounded-p ((w natp) (x svex-p))
  (lhssvex-range-p 0 w x))

;; (define lhssvex-bounded-p ((w natp) (x svex-p))
;;   :measure (svex-count x)
;;   :hints ('(:in-theory (enable equal-of-len)))
;;   :guard-hints (("goal" :in-theory (enable equal-of-len)))
;;   (if (zp w)
;;       t
;;     (svex-case x
;;       :var t
;;       :quote (equal x.val (4vec-z))
;;       :call
;;       (case x.fn
;;         (concat (b* (((unless (eql (len x.args) 3)) nil)
;;                      ((list w1 lo hi) x.args))
;;                   (and (eq (svex-kind w1) :quote)
;;                        (4vec-index-p (svex-quote->val w1))
;;                        (b* ((w1 (2vec->val (svex-quote->val w1))))
;;                          (if (< w1 w)
;;                              (and (lhssvex-bounded-p w1 lo)
;;                                   (lhssvex-bounded-p (- w w1) hi))
;;                            (lhssvex-bounded-p w lo))))))
;;         (rsh (b* (((unless (eql (len x.args) 2)) nil)
;;                   ((list sh xx) x.args))
;;                (and (eq (svex-kind sh) :quote)
;;                     (4vec-index-p (svex-quote->val sh))
;;                     (lhssvex-bounded-p (+ w (2vec->val (svex-quote->val sh))) xx))))))))


;; (define lhssvex-p ((x svex-p))
;;   :parents (lhs)
;;   :short "Recognizer for an svex that can be straightforwardly converted to a LHS object."
;;   :measure (svex-count x)
;;   :hints ('(:in-theory (enable equal-of-len)))
;;   :guard-hints (("goal" :in-theory (enable equal-of-len)))
;;   (svex-case x
;;     :var nil
;;     :quote (equal x.val (4vec-z))
;;     :call
;;     (case x.fn
;;       (concat (b* (((unless (eql (len x.args) 3)) nil)
;;                    ((list w lo hi) x.args))
;;                 (and (eq (svex-kind w) :quote)
;;                      (4vec-index-p (svex-quote->val w))
;;                      (lhssvex-bounded-p (2vec->val (svex-quote->val w)) lo)
;;                      (lhssvex-p hi))))
;;       (rsh (b* (((unless (eql (len x.args) 2)) nil)
;;                 ((list sh xx) x.args))
;;              (and (eq (svex-kind sh) :quote)
;;                   (4vec-index-p (svex-quote->val sh))
;;                   (lhssvex-p xx)))))))


(encapsulate nil
  (local (defthm car-of-svar
           (implies (and (svar-p x)
                         (consp x))
                    (equal (car x) :var))
           :hints(("Goal" :in-theory (enable svar-p)))))
  (local (defthm cdr-of-svar
           (implies (and (svar-p x)
                         (consp x))
                    (consp (cdr x)))
           :hints(("Goal" :in-theory (enable svar-p)))))

;; var         rsh       0             1
;; :z                  (:z . 0)    (:z . 1)
;; :var                :var        (:var . 1)
;; atom                atom        (atom . 1)
;; (:var . rest)   (:var . rest)  ((:var . rest) . 1)

  (fty::defflexsum lhatom
    (:z
     :cond (eq x :z)
     :fields nil
     :ctor-body ':z)
    (:var
     :cond t
     :shape (or (atom x)
                (and (eq (car x) :var)
                     (svar-p x))
                (or (eq (car x) :z)
                    (not (eql 0 (cdr x)))))
     :fields ((name :acc-body (if (or (atom x)
                                      (and (eq (car x) :var)
                                           (consp (cdr x))))
                                  x
                                (car x))
                    :type svar)
              (rsh :acc-body (if (or (atom x)
                                     (and (eq (car x) :var)
                                          (consp (cdr x))))
                                 0
                               (cdr x))
                   :type natp
                   :rule-classes (:rewrite :type-prescription)))
     :ctor-body (if (and (eql 0 rsh)
                         (not (eq name :z)))
                    name
                  (cons name rsh)))))


(local (defthm lhatom-z-by-kind
           (implies (lhatom-p x)
                    (equal (equal :z x)
                           (equal (lhatom-kind x) :z)))
           :hints (("goal" :use lhatom-fix-when-z
                    :in-theory (disable lhatom-fix-when-z)))))

  ;; (:z :cond (atom x) (equal x (4vec-z)) :ctor-body (4vec-z))
  ;; (:var :cond t
  ;;  :fields ((name :acc-body x :type svar))
  ;;  :ctor-body name))

(define lhatom-eval ((x lhatom-p) (env svex-env-p))
  :parents (lhatom)
  :returns (val 4vec-p)
  (lhatom-case x
    :z (4vec-z)
    :var (4vec-rsh (2vec x.rsh) (svex-env-fastlookup x.name env)))
  ///
  (deffixequiv lhatom-eval))

(define lhatom->svex ((x lhatom-p))
  :parents (lhatom)
  :returns (xx svex-p)
  (lhatom-case x
    :z (svex-quote (4vec-z))
    :var (svex-rsh x.rsh (svex-var x.name)))
  ///
  (deffixequiv lhatom->svex)

  (defthm lhatom->svex-correct
    (equal (svex-eval (lhatom->svex x) env)
           (lhatom-eval x env))
    :hints(("Goal" :in-theory (enable lhatom-eval svex-eval svex-apply
                                      4veclist-nth-safe svexlist-eval)))))

(encapsulate nil
  (local
   (defthm integerp-car-of-lhatom
     (implies (lhatom-p x)
              (not (integerp (car x))))
     :hints(("Goal" :in-theory (enable lhatom-p svar-p)))))

  (defflexsum lhrange
    :parents (lhs)
    :kind nil
    (:lhrange
     :cond t
     :shape (or (and (consp x)
                     (integerp (car x))
                     (not (eql (car x) 1)))
                (lhatom-p x))
     :fields ((w :acc-body (if (and (consp x)
                                    (integerp (car x)))
                               (car x)
                             1)
                 :type posp
                 :rule-classes (:rewrite :type-prescription))
              (atom :acc-body (if (and (consp x)
                                       (integerp (car x)))
                                  (cdr x)
                                x)
                    :type lhatom))
     :ctor-body (if (eql w 1)
                    atom
                  (cons w atom))
     :type-name lhrange))

  (defthm lhrange-type
    (let ((x (lhrange w atom)))
      (or (consp x)
          (and (symbolp x)
               (not (booleanp x)))
          (stringp x)))
    :hints(("Goal" :in-theory (enable lhatom-fix)))
    :rule-classes :type-prescription))

(define lhrange-eval ((x lhrange-p) (env svex-env-p))
  :parents (lhrange)
  :returns (val 4vec-p)
  (b* (((lhrange x) x))
    (4vec-concat (2vec x.w)
                 (lhatom-eval x.atom env)
                 (4vec-z)))
  ///
  (deffixequiv lhrange-eval))

(define lhrange->svex ((x lhrange-p))
  :parents (lhrange)
  :returns (s svex-p)
  (b* (((lhrange x) x))
    (svcall* concat (svex-quote (2vec x.w))
             (lhatom->svex x.atom)
             (svex-quote (4vec-z))))
  ///
  (deffixequiv lhrange->svex)

  (defthm lhrange->svex-correct
    (equal (svex-eval (lhrange->svex x) env)
           (lhrange-eval x env))
    :hints(("Goal" :in-theory (enable lhrange-eval svex-eval svex-apply
                                      4veclist-nth-safe svexlist-eval)))))



(deflist lhs :elt-type lhrange :true-listp t
  :parents (svmods)
  :short "A shorthand format for an expression consisting of a concatenation of parts of variables."
  :long "<p>LHS objects are used in flattening the module hierarchy.  They are
called LHS objects because they are also used to represent the left-hand sides
of assignments.</p>

<p>An LHS object is simply a list of @(see lhrange) objects.  The meaning of an
LHS object is the concatenations of the bits of all of its lhrange objects, in
the order given (LSBs-first).</p>")



(define lhs-eval ((x lhs-p) (env svex-env-p))
  :parents (lhs)
  :returns (val 4vec-p)
  (if (atom x)
      (4vec-z)
    (4vec-concat (2vec (lhrange->w (car x)))
                 (lhrange-eval (car x) env)
                 (lhs-eval (cdr x) env)))
  ///
  (deffixequiv lhs-eval))

(define lhs-eval-zero ((x lhs-p) (env svex-env-p))
  :parents (lhs)
  :returns (val 4vec-p)
  (if (atom x)
      0
    (4vec-concat (2vec (lhrange->w (car x)))
                 (lhrange-eval (car x) env)
                 (lhs-eval-zero (cdr x) env)))
  ///
  (deffixequiv lhs-eval-zero)

  (defthm lhs-eval-zero-of-cons
    (equal (lhs-eval-zero (cons a x) env)
           (4vec-concat (2vec (lhrange->w a))
                        (lhrange-eval a env)
                        (lhs-eval-zero x env))))

  (defthm lhs-eval-zero-of-nil
    (equal (lhs-eval-zero nil env) 0)))





(define lhs-width ((x lhs-p))
  :returns (w natp :rule-classes :type-prescription)
  (if (atom x)
      0
    (+ (lhrange->w (car x))
       (lhs-width (cdr x))))
  ///
  (deffixequiv lhs-width)

  (defthm lhs-width-bounds-eval-width
    (equal (4vec-concat (2vec (lhs-width x))
                        (lhs-eval x env)
                        (4vec-z))
           (lhs-eval x env))
    :hints(("Goal" :in-theory (enable lhs-eval)))))

(define lhrange-nextbit ((x lhrange-p))
  "returns an atom representing the next bit of the range's atom after the range ends."
  :returns (next lhatom-p)
  (b* (((lhrange x) x)
       (xkind (lhatom-kind x.atom))
       ((when (eq xkind :z)) (lhatom-z))
       ((lhatom-var x.atom) x.atom))
    (lhatom-var x.atom.name (+ x.w x.atom.rsh)))
  ///
  (deffixequiv lhrange-nextbit)

  (defthm lhrange-nextbit-when-z
    (implies (equal (lhatom-kind (lhrange->atom x)) :z)
             (equal (lhrange-nextbit x)
                    (lhatom-z))))

  (defthm lhrange-nextbit-when-var
    (implies (equal (lhatom-kind (lhrange->atom x)) :var)
             (equal (lhrange-nextbit x)
                    (lhatom-var
                     (lhatom-var->name (lhrange->atom x))
                     (+ (lhatom-var->rsh (lhrange->atom x))
                        (lhrange->w x)))))))

(define lhrange-combinable ((x lhrange-p) (y lhatom-p))
  :enabled t
  :guard-hints (("goal" :in-theory (enable lhrange-nextbit)))
  (mbe :logic (equal (lhatom-fix y) (lhrange-nextbit x))
       :exec (b* (((lhrange x) x)
                  (xkind (lhatom-kind x.atom))
                  (ykind (lhatom-kind y)))
               (and (eq xkind ykind)
                    (or (eq xkind :z)
                        (and (equal (lhatom-var->name x.atom)
                                    (lhatom-var->name y))
                             (eql (lhatom-var->rsh y)
                                  (+ (lhatom-var->rsh x.atom)
                                     x.w))))))))

(define lhrange-combinable-dec ((x.w posp) (x.atom lhatom-p) (y lhatom-p))
  :enabled t
  :guard-hints (("goal" :in-theory (enable lhrange-nextbit)))
  (mbe :logic (equal (lhatom-fix y) (lhrange-nextbit (lhrange x.w x.atom)))
       :exec (b* ((xkind (lhatom-kind x.atom))
                  (ykind (lhatom-kind y)))
               (and (eq xkind ykind)
                    (or (eq xkind :z)
                        (and (equal (lhatom-var->name x.atom)
                                    (lhatom-var->name y))
                             (eql (lhatom-var->rsh y)
                                  (+ (lhatom-var->rsh x.atom)
                                     x.w))))))))


; Matt K.: Avoid ACL2(p) error in logapps-of-logtails-lemma below pertaining to
; LOGBITP-REASONING.
(local (set-waterfall-parallelism nil))

(define lhrange-combine ((x lhrange-p) (y lhrange-p))
  :returns (val (iff (lhrange-p val) val))
  (b* (((lhrange x) x)
       ((lhrange y) y)
       (xkind (lhatom-kind x.atom))
       (ykind (lhatom-kind y.atom))
       ((unless (eq xkind ykind)) nil)
       ((when (eq xkind :z)) (lhrange (+ x.w y.w) (lhatom-z)))
       ((lhatom-var x.atom) x.atom)
       ((lhatom-var y.atom) y.atom)
       ((unless (and (equal x.atom.name y.atom.name)
                     (eql y.atom.rsh (+ x.w x.atom.rsh))))
        nil))
    (lhrange (+ x.w y.w) x.atom))
  ///
  (deffixequiv lhrange-combine)

  (local (defthm equal-when-lhatom-p
           (implies (and (lhatom-p x)
                         (lhatom-p y))
                    (Equal (equal x y)
                           (if (equal (lhatom-kind x) :z)
                               (equal (lhatom-kind y) :z)
                             (and (equal (lhatom-kind y) :var)
                                  (equal (lhatom-var->name x)
                                         (lhatom-var->name y))
                                  (equal (lhatom-var->rsh x)
                                         (lhatom-var->rsh y))))))
           :hints(("Goal" :use ((:instance lhatom-fix-when-z (x x))
                                (:instance lhatom-fix-when-z (x y))
                                (:instance lhatom-fix-when-var (x x))
                                (:instance lhatom-fix-when-var (x y)))
                   :in-theory (disable lhatom-fix-when-z
                                       lhatom-fix-when-var
                                       equal-of-lhatom-var
                                       lhatom-z-by-kind
                                       lhatom-var-of-fields)))))

  (defthm lhrange-combine-under-iff
    (iff (lhrange-combine x y)
         (lhatom-equiv (lhrange-nextbit x) (lhrange->atom y)))
    :hints(("Goal" :in-theory (enable lhrange-nextbit))))

  (defthm lhrange-combine-when-combinable
    (implies (lhatom-equiv (lhrange-nextbit x) (lhrange->atom y))
             (equal (lhrange-combine x y)
                    (lhrange (+ (lhrange->w x) (lhrange->w y))
                             (lhrange->atom x))))
    :hints(("Goal" :in-theory (enable lhrange-nextbit))))

  ;; (defthm logapp-of-logtail-norm
  ;;   (equal (logapp w x (logtail w x))
  ;;          (ifix x))
  ;;   :hints ((acl2::logbitp-reasoning)))

  ;; (defthm logapp-of-logtail-norm-more
  ;;   (equal (logapp w x (logapp w2 (logtail w x) y))
  ;;          (logapp (+ (nfix w) (nfix w2)) x y))
  ;;   :hints ((acl2::logbitp-reasoning)))

  ;; (local (defthm logapp-of-logtail-norm2-lemma
  ;;          (equal (logapp w (logtail w1 x) (logtail (+ (nfix w1) (nfix w)) x))
  ;;                 (logtail w1 x))
  ;;          :hints ((acl2::logbitp-reasoning))))

  ;; (defthm logapp-of-logtail-norm2
  ;;   (implies (equal (nfix w2) (+ (nfix w1) (nfix w)))
  ;;            (equal (logapp w (logtail w1 x) (logtail w2 x))
  ;;                   (logtail w1 x)))
  ;;   :hints (("goal" :use logapp-of-logtail-norm2-lemma
  ;;            :in-theory (disable logapp-of-logtail-norm2-lemma))))

  (local (defthm logapps-of-logtails-lemma
           (equal (logapp w (logtail w1 x)
                          (logapp w3 (logtail (+ (nfix w1) (nfix w)) x) y))
                  (logapp (+ (nfix w) (nfix w3)) (logtail w1 x) y))
           :hints ((acl2::logbitp-reasoning))))

  (defthm logapps-of-logtails
    (implies (equal (nfix w2) (+ (nfix w1) (nfix w)))
             (equal (logapp w (logtail w1 x) (logapp w3 (logtail w2 x) y))
                    (logapp (+ (nfix w) (nfix w3)) (logtail w1 x) y)))
    :hints (("goal" :use ((:instance logapps-of-logtails-lemma))
             :in-theory (disable logapps-of-logtails-lemma))))

  (defthm logapp-of-logapp-same-width
    (equal (logapp w (logapp w x z) y)
           (logapp w x y))
    :hints ((acl2::logbitp-reasoning)))

  (defthm lhrange-combine-correct
    (implies (lhrange-combine x y)
             (equal (lhrange-eval (lhrange-combine x y) env)
                    (lhs-eval (list x y) env)))
    :hints(("Goal" :in-theory (e/d (lhrange-eval
                                    lhs-eval lhatom-eval
                                      4vec-concat 4vec-rsh 4vec-shift-core)
                                   (bitops::logapp-of-j-0)))))

  (local (defthm logapp-norm
           (equal (logapp w1 (logapp w2 x y) z)
                  (if (<= (nfix w1) (nfix w2))
                      (logapp w1 x z)
                    (logapp w2 x (logapp (- (nfix w1) (nfix w2)) y z))))
           :hints ((bitops::logbitp-reasoning))))

  (defthm lhrange-combine-correct-zero
    (implies (lhrange-combine x y)
             (equal (lhrange-eval (lhrange-combine x y) env)
                    (4vec-concat (2vec (+ (lhrange->w x) (lhrange->w y)))
                                 (lhs-eval-zero (list x y) env)
                                 (4vec-z))))
    :hints(("Goal" :in-theory (e/d (lhrange-eval
                                    lhs-eval-zero lhatom-eval
                                      4vec-concat 4vec-rsh 4vec-shift-core)
                                   (bitops::logapp-of-j-0))))))

  ;; (defthm lhrange-combine-width
  ;;   (implies (lhrange-combine x y)
  ;;            (equal (lhrange->w (lhrange-combine x y))
  ;;                   (+ (lhrange->w x) (lhrange->w y)))))

  ;; (defthm lhrange-combine-associative
  ;;   (implies (lhrange-combine a b)
  ;;            (equal (lhrange-combine (lhrange-combine a b) c)
  ;;                   (and (lhrange-combine b c)
  ;;                        (lhrange-combine a (lhrange-combine b c))))))



  ;; (defthm lhrange-atom-of-lhrange-combine
  ;;   (implies (lhrange-combine x y)
  ;;            (equal (lhrange->atom (lhrange-combine x y))
  ;;                   (lhrange->atom x))))

  ;; (local (defthm lhrange-under-iff
  ;;          (iff (lhrange w a) t)))

  ;; (defthm lhrange-combine-assoc
  ;;   (implies (lhrange-combine y z)
  ;;            (iff (lhrange-combine x (lhrange-combine y z))
  ;;                 (lhrange-combine x y))))

  ;; (defthmd lhatom-kind-when-combine
  ;;   (implies (lhrange-combine x y)
  ;;            (equal (lhatom-kind (lhrange->atom y))
  ;;                   (lhatom-kind (lhrange->atom x)))))

  ;; (defthmd lhatom-var->name-when-combine
  ;;   (implies (lhrange-combine x y)
  ;;            (equal (lhatom-var->name (lhrange->atom y))
  ;;                   (lhatom-var->name (lhrange->atom x))))
  ;;   :hints(("Goal" :in-theory (enable lhatom-var->name-when-wrong-kind))))

  ;; (defthm lhrange-combine-when-both-z
  ;;   (implies (and (equal (lhatom-kind (lhrange->atom x)) :z)
  ;;                 (equal (lhatom-kind (lhrange->atom y)) :z))
  ;;            (equal (lhrange-combine x y)
  ;;                   (lhrange (+ (lhrange->w x) (lhrange->w y))
  ;;                            (lhatom-z)))))

  ;; (defthm lhrange-combine-when-diff-kinds
  ;;   (implies (not (equal (lhatom-kind (lhrange->atom x))
  ;;                        (lhatom-kind (lhrange->atom y))))
  ;;            (equal (lhrange-combine x y) nil)))

  ;; (defthm lhrange-combine-when-exists
  ;;   (implies (lhrange-combine x y)
  ;;            (equal (lhrange-combine x y)
  ;;                   (lhrange (+ (lhrange->w x) (lhrange->w y))
  ;;                            (lhrange->atom x))))))



(local (defthmd lhrange->atom-when-z
         (implies (equal (lhatom-kind (lhrange->atom x)) :z)
                  (equal (lhrange->atom x) :z))
         :hints (("goal" :use ((:instance lhatom-fix-when-z
                                (x (lhrange->atom x))))
                  :in-theory (disable lhatom-fix-when-z)))))

(define lhs-cons ((x lhrange-p) (y lhs-p))
  :returns (cons lhs-p)
  (if (atom y)
      (list (lhrange-fix x))
    (let ((comb (lhrange-combine x (car y))))
      (if comb
          (cons comb (lhs-fix (cdr y)))
        (cons (lhrange-fix x) (lhs-fix y)))))
  ///
  (deffixequiv lhs-cons)

  (local (defthm lhrange-eval-when-z
           (implies (equal (lhatom-kind (lhrange->atom x)) :z)
                    (equal (lhrange-eval x env) (4vec-z)))
           :hints(("Goal" :in-theory (enable lhrange-eval lhatom-eval 4vec-concat)))))

  (local (defthm 4vec-concat-zs
           (implies (and (2vec-p w)
                         (<= 0 (2vec->val w)))
                    (equal (4vec-concat w (4vec-z) (4vec-z))
                           (4vec-z)))
           :hints(("Goal" :in-theory (enable 4vec-concat)))))

  (defthm lhs-cons-correct
    (equal (lhs-eval (lhs-cons x y) env)
           (lhs-eval (cons x y) env))
    :hints(("Goal" :in-theory (e/d (lhs-eval) (lhrange-combine-correct))
            :use ((:instance lhrange-combine-correct
                   (x x) (y (car y))))
            :do-not-induct t))
    :otf-flg t)

  (defthm lhs-cons-correct-zero
    (equal (lhs-eval-zero (lhs-cons x y) env)
           (lhs-eval-zero (cons x y) env))
    :hints(("Goal" :in-theory (e/d (lhs-eval-zero) (lhrange-combine-correct))
            :use ((:instance lhrange-combine-correct-zero
                   (x x) (y (car y))))
            :do-not-induct t))
    :otf-flg t)

  (defthm lhs-width-of-lhs-cons
    (<= (lhs-width (lhs-cons x y))
        (+ (lhrange->w x)
           (lhs-width y)))
    :hints(("Goal" :in-theory (enable lhs-width)))
    :rule-classes :linear)

  ;; (defthm lhs-cons-idempotent
  ;;   (implies (eql (len (lhs-cons x y)) (+ 1 (len y)))
  ;;            (equal (lhs-cons (car (lhs-cons x y)) (cdr (lhs-cons x y)))
  ;;                   (lhs-cons x y))))

  (defthm lhs-cons-of-lhs-cons
    (implies (lhrange-combine x y)
             (equal (lhs-cons x (lhs-cons y z))
                    (lhs-cons (lhrange-combine x y) z)))
;;             (cons (lhrange-fix x) (lhs-cons y z))))
    :hints(("Goal" :in-theory (enable lhrange->atom-when-z))
           (and stable-under-simplificationp
                '(:in-theory (enable lhrange-nextbit)))))

  (defthm lhs-cons-of-lhs-cons-when-not-combinable
    (implies (not (lhrange-combine x y))
             (equal (lhs-cons x (lhs-cons y z))
                    (cons (lhrange-fix x) (lhs-cons y z))))
    :hints(("Goal" :in-theory (enable lhrange->atom-when-z))
           (and stable-under-simplificationp
                '(:in-theory (enable lhrange-nextbit)))))

  (defthmd consp-of-lhs-cons ;
    (equal (consp (lhs-cons x y)) t))

  (defthm lhrange->atom-car-lhs-cons
    (equal (lhrange->atom (car (lhs-cons x y)))
           (lhrange->atom x)))

  (defthm lhrange->w-of-car-lhs-cons
    (<= (lhrange->w x) (lhrange->w (car (lhs-cons x y))))
    :rule-classes :linear))


(define lhs-norm ((x lhs-p))
  :returns (xx lhs-p)
  :hooks nil
  (if (atom x)
      nil
    (lhs-cons (car x) (lhs-norm (cdr x))))
  ///
  (deffixequiv lhs-norm)

  (defthm lhs-norm-when-not-consp
    (implies (not (consp x))
             (equal (lhs-norm x) nil))
    :rule-classes ((:rewrite :backchain-limit-lst 0)))


  (defthm lhs-norm-of-lhs-cons
    (equal (lhs-norm (lhs-cons x y))
           (lhs-cons x (lhs-norm y)))
    :hints (("goal" :Expand ((lhs-cons x y)
                             (lhs-cons x nil))
             :do-not-induct t)
            (and stable-under-simplificationp
                 '(:expand ((:free (x) (lhs-cons x nil))))))
    :otf-flg t)

  (defthm lhs-norm-idempotent
    (equal (lhs-norm (lhs-norm x))
           (lhs-norm x))
    :hints (("goal" :induct (len x))))

  (defthm lhs-norm-atom-of-car
    (implies (consp (lhs-norm x))
             (equal (lhrange->atom (car (lhs-norm x)))
                    (lhrange->atom (car x))))
    :hints(("Goal" :in-theory (enable lhs-norm))))

  (define lhs-normp ((x lhs-p))
    :hooks nil
    (equal x (lhs-norm x))
    ///
    (deffixtype lhs-norm :fix lhs-norm :pred lhs-normp
      :equiv lhs-norm-equiv :define t :forward t :executablep nil)

    (defrefinement lhs-equiv lhs-norm-equiv)

    (fty::deffixcong lhs-norm-equiv lhs-norm-equiv (lhs-cons x y) y)
    (fty::deffixcong lhs-norm-equiv equal (lhs-eval x env) x
      :hints (("goal" :expand ((lhs-eval x env)
                               (lhs-eval nil env)
                               (:free (x y) (lhs-eval (cons x y) env)))
               :induct (lhs-norm x))))

    (fty::deffixcong lhs-norm-equiv equal (lhs-eval-zero x env) x
      :hints (("goal" :expand ((lhs-eval-zero x env)
                               (lhs-eval-zero nil env)
                               (:free (x y) (lhs-eval-zero (cons x y) env)))
               :induct (lhs-norm x))))

    (defthm lhs-norm-cdr-lhs-norm
      (implies (lhs-normp x)
               (lhs-normp (cdr x)))
      :hints(("Goal" :in-theory (enable lhs-cons))))

    (defthm lhs-normp-of-lhs-norm
      (lhs-normp (lhs-norm x)))

    (defthm lhs-normp-of-lhs-cons
      (implies (lhs-normp x)
               (lhs-normp (lhs-cons a x))))

    (defthm lhs-norm-when-lhs-normp
      (implies (lhs-normp x)
               (equal (lhs-norm x) x)))

    (defthm lhs-normp-of-lhs-fix
      (implies (lhs-normp x)
               (lhs-normp (lhs-fix x))))))


(define lhs-concat ((w natp) (x lhs-p) (y lhs-p))
  :returns (concat lhs-p)
  :measure (len x)
  (b* (((when (zp w)) (lhs-fix y))
       ((when (atom x))
        (lhs-cons (lhrange w (lhatom-z)) y))
       ((lhrange xf) (car x))
       ((when (<= xf.w w))
        (lhs-cons (car x) (lhs-concat (- w xf.w) (cdr x) y))))
    (lhs-cons (lhrange w xf.atom) y))
  ///
  (deffixequiv lhs-concat)

  (local (defthm lhrange-identity
           (implies (equal a (lhrange->atom x))
                    (equal (lhrange (lhrange->w x) a)
                           (lhrange-fix x)))))

  (defthm lhs-concat-of-lhs-cons-under-norm-equiv
    (equal (lhs-concat w (lhs-cons x y) z)
           (lhs-concat w (cons x y) z))
    :hints (("goal" :expand ((lhs-cons x y)
                             (lhs-concat w (cons x y) z))
             :in-theory (e/d () (lhs-cons-of-lhs-cons-when-not-combinable
                                 cons-equal not))
             :do-not-induct t)
            (and stable-under-simplificationp
                 '(:in-theory (e/d (consp-of-lhs-cons
                                    lhrange->atom-when-z)
                                   (cons-equal
                                    not
                                    lhs-cons-of-lhs-cons-when-not-combinable))))
            (and stable-under-simplificationp
                 '(:expand ((:free (w)
                             (lhs-concat w y z))))))
    :otf-flg t)
  (fty::deffixcong lhs-norm-equiv equal (lhs-concat w x y) x
    :hints (("goal" :induct (lhs-concat w x y)
             ;; :in-theory (enable consp-of-lhs-cons)
             :expand ((lhs-norm x)))))
  (fty::deffixcong lhs-norm-equiv lhs-norm-equiv (lhs-concat w x y) y)

  (defthm lhs-concat-correct
    (equal (lhs-eval (lhs-concat w x y) env)
           (4vec-concat (2vec (nfix w))
                        (lhs-eval x env)
                        (lhs-eval y env)))
    :hints (("Goal" :induct (lhs-concat w x y)
             :expand ((lhs-concat w x y)
                      (lhs-concat 0 x y))
             :in-theory (e/d (lhs-eval lhrange-eval lhatom-eval)
                             ((:d lhs-concat))))))

  (defthm lhs-concat-correct-zero
    (equal (lhs-eval-zero (lhs-concat w x y) env)
           (4vec-concat (2vec (nfix w))
                        (lhs-eval x env)
                        (lhs-eval-zero y env)))
    :hints (("Goal" :induct (lhs-concat w x y)
             :expand ((lhs-concat w x y)
                      (lhs-concat 0 x y))
             :in-theory (e/d (lhs-eval-zero lhs-eval lhrange-eval lhatom-eval)
                             ((:d lhs-concat))))))

  (defthm lhs-width-of-lhs-concat
    (<= (lhs-width (lhs-concat w x y))
        (+ (nfix w) (lhs-width y)))
    :rule-classes :linear))

(define lhs-rsh ((sh natp) (x lhs-p))
  :returns (rsh lhs-p)
  :measure (len x)
  (b* (((when (zp sh)) (lhs-fix x))
       ((when (atom x)) nil)
       ((lhrange xf) (car x))
       ((when (<= xf.w sh))
        (lhs-rsh (- sh xf.w) (cdr x)))
       (newatom (lhatom-case xf.atom
                  :z (lhatom-z)
                  :var (lhatom-var xf.atom.name (+ xf.atom.rsh sh)))))
    (lhs-cons (lhrange (- xf.w sh) newatom) (cdr x)))
  ///
  (deffixequiv lhs-rsh)

  (defthm lhs-rsh-correct
    (equal (lhs-eval (lhs-rsh sh x) env)
           (4vec-rsh (2vec (nfix sh)) (lhs-eval x env)))
    :hints(("Goal" :induct (lhs-rsh sh x)
            :expand ((lhs-rsh sh x)
                     (lhs-rsh 0 x))
            :in-theory (e/d (lhs-eval lhrange-eval lhatom-eval)
                            ((:d lhs-rsh))))
           (and stable-under-simplificationp
                '(:in-theory (e/d (4vec-rsh 4vec-concat 4vec-shift-core)
                                  (lhs-rsh))))))

  (defthm lhs-rsh-correct-zero
    (equal (lhs-eval-zero (lhs-rsh sh x) env)
           (4vec-rsh (2vec (nfix sh)) (lhs-eval-zero x env)))
    :hints(("Goal" :induct (lhs-rsh sh x)
            :expand ((lhs-rsh sh x)
                     (lhs-rsh 0 x))
            :in-theory (e/d (lhs-eval-zero lhrange-eval lhatom-eval)
                            ((:d lhs-rsh))))
           (and stable-under-simplificationp
                '(:in-theory (e/d (4vec-rsh 4vec-concat 4vec-shift-core)
                                  (lhs-rsh))))))

  (defthm lhs-width-of-lhs-rsh
    (<= (lhs-width (lhs-rsh sh x))
        (nfix (- (lhs-width x) (nfix sh))))
    :hints(("Goal" :in-theory (enable lhs-width)))
    :rule-classes :linear)

  (local (defthm lhrange-identity
           (implies (equal a (lhrange->atom x))
                    (equal (lhrange (lhrange->w x) a)
                           (lhrange-fix x)))))

  (defthm lhs-rsh-of-lhs-cons
    (lhs-norm-equiv (lhs-rsh sh (lhs-cons x y))
                    (lhs-rsh sh (cons x y)))
    :hints (("goal" :expand ((lhs-cons x y)
                             (:free (x) (lhs-cons x nil))
                             (:free (x y z) (lhs-cons x (cons y z)))
                             (:free (w) (lhs-rsh w y))
                             (:free (a b) (lhs-norm (cons a b)))
                             )
             :in-theory (e/d () ((lhs-norm-equiv)))
             :do-not-induct t))
    :otf-flg t)

  (fty::deffixcong lhs-norm-equiv lhs-norm-equiv (lhs-rsh sh x) x
    :hints (("goal" :induct (lhs-rsh sh x)
             :expand ((lhs-norm x)))))

  (defthm len-of-lhs-rsh
    (<= (len (lhs-rsh sh x)) (len x))
    :hints (("goal" :induct (lhs-rsh sh x)
             :in-theory (enable lhs-cons)
             :expand ((lhs-rsh sh x))))
    :rule-classes :linear))

;; (defthm lhssvex-p-implies-lhssvex-unbounded-p
;;   (implies (lhssvex-p x)
;;            (lhssvex-unbounded-p x))
;;   :hints(("Goal" :in-theory (enable lhssvex-p
;;                                     lhssvex-unbounded-p))))

(defthm 2vec-of-same
  (implies (2vec-p x)
           (equal (2vec (4vec->lower x))
                  (4vec-fix x))))

(define lhatom-vars ((x lhatom-p))
  :returns (vars svarlist-p)
  :hooks (:fix)
  (lhatom-case x
    :z nil
    :var (list x.name))
  ///
  (defthm vars-of-lhrange-combine
    (implies (lhrange-combine x y)
             (iff (member v (lhatom-vars (lhrange->atom (lhrange-combine x y))))
                  (member v (lhatom-vars (lhrange->atom x)))))))

(define lhs-vars ((x lhs-p))
  :returns (vars svarlist-p)
  :measure (len x)
  (b* (((when (atom x)) nil)
       ((lhrange first) (car x)))
    (append (lhatom-vars first.atom)
            (lhs-vars (cdr x))))
  ///
  (defthm lhs-vars-of-cons
    (equal (lhs-vars (cons a b))
           (append (lhatom-vars (lhrange->atom a))
                   (lhs-vars b))))

  (defthm lhs-vars-when-consp
    (implies (consp x)
             (equal (lhs-vars x)
                    (append (lhatom-vars (lhrange->atom (car x)))
                            (lhs-vars (cdr x)))))
    :rule-classes ((:rewrite :backchain-limit-lst 0)))

  (deffixequiv lhs-vars)

  (defthm vars-of-lhs-cons
    (iff (member v (lhs-vars (lhs-cons a b)))
         (or (member v (lhs-vars b))
             (member v (lhatom-vars (lhrange->atom a)))))
    :hints(("Goal" :in-theory (enable lhs-cons))
           (and stable-under-simplificationp
                '(:in-theory (enable lhatom-vars)))))

  (defthm vars-of-lhs-norm
    (iff (member v (lhs-vars (lhs-norm x)))
         (member v (lhs-vars x)))
  :hints(("Goal" :in-theory (e/d (lhs-norm)
                                 (lhs-vars
                                  lhs-vars-when-consp))
          :expand ((lhs-vars x))
          :induct (lhs-norm x))))

  (defthm vars-of-lhs-concat
    (implies (and (not (member v (lhs-vars x)))
                  (not (member v (lhs-vars y))))
             (not (member v (lhs-vars (lhs-concat w x y)))))
    :hints(("Goal" :in-theory (e/d (lhs-concat)
                                   (lhs-vars-when-consp lhs-vars)))))

  (defthm vars-of-lhs-rsh
    (implies (not (member v (lhs-vars x)))
             (not (member v (lhs-vars (lhs-rsh sh x)))))
    :hints(("Goal" :in-theory (e/d (lhs-rsh lhatom-vars)
                                   (lhs-vars
                                    lhs-vars-when-consp))))))

(define svex->lhs-range ((rsh natp) (w natp) (x svex-p))
  :guard (lhssvex-range-p rsh w x)
  :verify-guards nil
  :measure (svex-count x)
  :returns (lhs lhs-p)
  (if (zp w)
      nil
    (svex-case x
      :var (list (lhrange w (lhatom-var x.name rsh)))
      :quote (list (lhrange w (lhatom-z)))
      :call
      (case x.fn
        (concat (b* (((unless (mbt (eql (len x.args) 3))) nil)
                     ((list x.w x.lo x.hi) x.args)
                     (x.wval (2vec->val (svex-quote->val x.w)))
                     ((when (<= x.wval (lnfix rsh)))
                      (svex->lhs-range (- (lnfix rsh) x.wval) w x.hi))
                     ((when (<= (+ (lnfix rsh) w) x.wval))
                      (svex->lhs-range rsh w x.lo))
                     (lo-width (- x.wval (lnfix rsh))))
                  (lhs-concat lo-width (svex->lhs-range rsh lo-width x.lo)
                              (svex->lhs-range 0 (- w lo-width) x.hi))))
        (rsh (b* (((unless (mbt (eql (len x.args) 2))) nil)
                  ((list x.sh x.sub) x.args)
                  (x.shval (2vec->val (svex-quote->val x.sh))))
               (svex->lhs-range (+ x.shval (lnfix rsh)) w x.sub))))))
  ///
  (local (in-theory (disable (:d svex->lhs-range))))

  (defret vars-of-svex->lhs-range
    (implies (not (member v (svex-vars x)))
             (not (member v (lhs-vars lhs))))
    :hints(("Goal" :in-theory (e/d (lhatom-vars)
                                   ((:d svex->lhs-range)
                                    append default-car default-cdr not
                                    member))
            :induct <call>
            :expand (<call>))))

  (deffixequiv svex->lhs-range
    :hints (("goal" :Expand ((svex->lhs-range rsh w (svex-fix x))
                             (svex->lhs-range (nfix rsh) w x)
                             (svex->lhs-range rsh (nfix w) x)
                             (svex->lhs-range rsh w x)))))

  (verify-guards svex->lhs-range
    :hints (("goal" :expand ((lhssvex-range-p rsh w x))
             :in-theory (enable 4vec-index-p))))

  (local (in-theory (disable acl2::loghead-identity not 4vec-equal len)))

  (defret svex->lhs-range-correct
    (implies (lhssvex-range-p rsh w x)
             (equal (lhs-eval lhs env)
                    (4vec-concat (2vec (nfix w))
                                 (4vec-rsh (2vec (nfix rsh)) (svex-eval x env))
                                 (4vec-z))))
    :hints (("goal" :induct <call>
             :expand (<call>
                      (lhssvex-range-p rsh w x)
                      (lhs-eval nil env)
                      (svex->lhs-range rsh 0 x)
                      (svex-eval x env)
                      (:free (a b) (lhs-eval (cons a b) env)))
             :in-theory (e/d ( ;; svex-eval
                              svex-apply svexlist-eval 4veclist-nth-safe
                              lhrange-eval lhatom-eval
                              4vec-index-p)))
            (and stable-under-simplificationp
                 '(:in-theory (e/d (4vec-rsh 4vec-concat 4vec-shift-core))))))

  (defret svex->lhs-range-correct-zero
    (implies (lhssvex-range-p rsh w x)
             (equal (lhs-eval-zero lhs env)
                    (4vec-concat (2vec (nfix w))
                                 (4vec-rsh (2vec (nfix rsh)) (svex-eval x env))
                                 0)))
    :hints (("goal" :induct <call>
             :expand (<call>
                      (lhssvex-range-p rsh w x)
                      (lhs-eval-zero nil env)
                      (svex->lhs-range rsh 0 x)
                      (svex-eval x env)
                      (:free (a b) (lhs-eval-zero (cons a b) env)))
             :in-theory (e/d ( ;; svex-eval
                              svex-apply svexlist-eval 4veclist-nth-safe
                                         lhrange-eval lhatom-eval
                                         4vec-index-p)))
            (and stable-under-simplificationp
                 '(:in-theory (e/d (4vec-rsh 4vec-concat 4vec-shift-core)))))))

(define svex->lhs-bound ((w natp) (x svex-p))
  :guard (lhssvex-bounded-p w x)
  :guard-hints (("goal" :in-theory (enable lhssvex-bounded-p)))
  :returns (lhs lhs-p)
  (svex->lhs-range 0 w x)
  ///
  (defthm vars-of-svex->lhs-bound
    (implies (not (member v (svex-vars x)))
             (not (member v (lhs-vars (svex->lhs-bound w x))))))

  (deffixequiv svex->lhs-bound
    :hints (("goal" :Expand ((svex->lhs-bound w (svex-fix x))))))

  (verify-guards svex->lhs-bound
    :hints (("goal" :expand ((lhssvex-unbounded-p x))
             :in-theory (enable 4vec-index-p))))

  (defthm svex->lhs-bound-correct
    (implies (lhssvex-bounded-p w x)
             (equal (lhs-eval (svex->lhs-bound w x) env)
                    (4vec-concat (2vec (nfix w))
                                 (svex-eval x env)
                                 (4vec-z))))
    :hints (("goal" :in-theory (enable lhssvex-bounded-p))))

  (defthm svex->lhs-bound-correct-zero
    (implies (lhssvex-bounded-p w x)
             (equal (lhs-eval-zero (svex->lhs-bound w x) env)
                    (4vec-concat (2vec (nfix w))
                                 (svex-eval x env)
                                 0)))
    :hints (("goal" :in-theory (enable lhssvex-bounded-p)))))

;; ;; Problematic wrt lhs-eval-zero.  We have changed everything to use  svex->lhs-bound.
;; (define svex->lhs ((x svex-p))
;;   :guard (lhssvex-p x)
;;   :verify-guards nil
;;   :measure (svex-count x)
;;   :returns (lhs lhs-p)
;;   (svex-case x
;;     :var (mbt nil)
;;     :quote nil
;;     :call
;;     (case x.fn
;;       (concat (b* (((unless (mbt (eql (len x.args) 3))) nil)
;;                    ((list x.w x.lo x.hi) x.args)
;;                    (x.wval (2vec->val (svex-quote->val x.w))))
;;                 (lhs-concat x.wval (svex->lhs-bound x.wval x.lo)
;;                             (svex->lhs x.hi))))
;;       (rsh (b* (((unless (mbt (eql (len x.args) 2))) nil)
;;                 ((list x.sh x.sub) x.args)
;;                 (x.shval (2vec->val (svex-quote->val x.sh))))
;;              (lhs-rsh x.shval (svex->lhs x.sub))))))
;;   ///

;;   (defthm vars-of-svex->lhs
;;     (implies (not (member v (svex-vars x)))
;;              (not (member v (lhs-vars (svex->lhs x)))))
;;     :hints(("Goal" :in-theory (e/d (lhatom-vars)
;;                                    ((:d svex->lhs)
;;                                     append default-car default-cdr not
;;                                     member))
;;             :induct (svex->lhs x)
;;             :expand ((svex->lhs x)))))

;;   (deffixequiv svex->lhs
;;     :hints (("goal" :Expand ((svex->lhs (svex-fix x))))))

;;   (verify-guards svex->lhs
;;     :hints (("goal" :expand ((lhssvex-p x))
;;              :in-theory (enable 4vec-index-p))))

;;   (defthm svex->lhs-correct
;;     (implies (lhssvex-p x)
;;              (equal (lhs-eval (svex->lhs x) env)
;;                     (svex-eval x env)))
;;     :hints (("goal" :induct (svex->lhs x)
;;              :expand ((svex->lhs x)
;;                       (lhssvex-p x)
;;                       (lhs-eval nil env)
;;                       (:free (a b) (lhs-eval (cons a b) env)))
;;              :in-theory (e/d (svex-eval
;;                               svex-apply svexlist-eval 4veclist-nth-safe
;;                               lhrange-eval lhatom-eval
;;                               4vec-index-p)
;;                              ((:d svex->lhs))))
;;             (and stable-under-simplificationp
;;                  '(:in-theory (e/d (4vec-rsh 4vec-concat 4vec-shift-core) (svex->lhs)))))))


(fty::deftagsum lhbit
  (:z nil)
  (:var ((name svar)
         (idx natp))
   :layout :tree
   :hons t))

(define lhbit-eval ((x lhbit-p) (env svex-env-p))
  (lhbit-case x
    :z (4vec-1z)
    :var (4vec-bit-index x.idx (svex-env-lookup x.name env)))
  ///
  (deffixequiv lhbit-eval))

(define lhatom-bitproj ((idx natp) (x lhatom-p))
  :returns (bit lhbit-p)
  (lhatom-case x
    :z (lhbit-z)
    :var (lhbit-var x.name (+ (lnfix idx) x.rsh)))
  ///
  (deffixequiv lhatom-bitproj)
  (defthm lhatom-bitproj-correct
    (equal (lhbit-eval (lhatom-bitproj idx x) env)
           (4vec-bit-index idx (lhatom-eval x env)))
    :hints(("Goal" :in-theory (enable lhbit-eval lhatom-eval
                                      4vec-bit-index 4vec-rsh 4vec-shift-core)))))

(define lhrange-bitproj ((idx natp) (x lhrange-p))
  :returns (bit lhbit-p)
  (b* (((lhrange x) x)
       (idx (lnfix idx)))
    (if (<= x.w idx)
        (lhbit-z)
      (lhatom-bitproj idx x.atom)))
  ///
  (deffixequiv lhrange-bitproj)

  (defthm lhrange-bitproj-correct
    (equal (lhbit-eval (lhrange-bitproj idx x) env)
           (4vec-bit-index idx (lhrange-eval x env)))
    :hints(("Goal" :in-theory (enable lhrange-eval 4vec-bit-index 4vec-concat))
           (and stable-under-simplificationp
                '(:in-theory (enable lhbit-eval)))))

  (defthm lhrange-bitproj-of-lhrange-combine
    (implies (lhrange-combine x y)
             (equal (lhrange-bitproj idx (lhrange-combine x y))
                    (if (< (nfix idx) (lhrange->w x))
                        (lhrange-bitproj idx x)
                      (lhrange-bitproj (- (nfix idx) (lhrange->w x)) y))))
    :hints(("Goal" :in-theory (enable lhrange-combine
                                      lhatom-bitproj))))

  (defthm lhatom-bitproj-of-lhrange-combine-atom
    (implies (lhrange-combine x y)
             (equal (lhatom-bitproj idx (lhrange->atom (lhrange-combine x y)))
                    (if (< (nfix idx) (lhrange->w x))
                        (lhatom-bitproj idx (lhrange->atom x))
                      (lhatom-bitproj (- (nfix idx) (lhrange->w x)) (lhrange->atom y)))))
    :hints(("Goal" :in-theory (enable lhrange-combine
                                      lhatom-bitproj)))))

(define lhs-bitproj ((idx natp) (x lhs-p))
  :returns (bit lhbit-p)
  :measure (len x)
  (if (atom x)
      (lhbit-z)
    (b* (((lhrange xf) (car x))
         (idx (lnfix idx)))
      (if (< idx xf.w)
          (lhatom-bitproj idx xf.atom)
        (lhs-bitproj (- idx xf.w) (cdr x)))))
  ///
  (deffixequiv lhs-bitproj)

  (defthm lhs-bitproj-correct
    (equal (lhbit-eval (lhs-bitproj idx x) env)
           (4vec-bit-index idx (lhs-eval x env)))
    :hints(("Goal" :in-theory (enable lhs-eval))
           (and stable-under-simplificationp
                '(:in-theory (enable 4vec-bit-index 4vec-concat lhrange-eval)))
           (and stable-under-simplificationp
                '(:in-theory (enable lhbit-eval)))))

  (defthm lhs-bitproj-of-lhs-cons
    (equal (lhs-bitproj idx (lhs-cons x y))
           (if (< (nfix idx) (lhrange->w x))
               (lhrange-bitproj idx x)
             (lhs-bitproj (- (nfix idx) (lhrange->w x)) y)))
    :hints(("Goal" :in-theory (enable lhs-cons lhrange-bitproj lhatom-bitproj)
            :do-not-induct t)
           (and stable-under-simplificationp
                '(:expand ((:free (idx) (lhs-bitproj idx y))))))
    :otf-flg t)

  (local (defun ind (idx w x y)
           (declare (xargs :measure (len x)))
           (b* (((when (zp w)) (list y))
                ((when (atom x)) (list idx))
                ((lhrange xf) (car x))
                ((when (<= xf.w w))
                 (ind (- (nfix idx) xf.w) (- (nfix w) xf.w) (cdr x) y)))
             (list x))))

  (defthm lhs-bitproj-of-lhs-concat
    (equal (lhs-bitproj idx (lhs-concat w x y))
           (if (< (nfix idx) (nfix w))
               (lhs-bitproj idx x)
             (lhs-bitproj (- (nfix idx) (nfix w)) y)))
    :hints(("Goal" :in-theory (enable lhs-concat lhrange-bitproj)
            :induct (ind idx w x y)
            :do-not-induct t)
           (and stable-under-simplificationp
                '(:expand ((lhatom-bitproj idx :z)))))
    :otf-flg t)

  (defthm lhs-bitproj-of-lhs-rsh
    (equal (lhs-bitproj idx (lhs-rsh sh x))
           (lhs-bitproj (+ (nfix idx) (nfix sh)) x))
    :hints (("goal" :induct (lhs-rsh sh x)
             :in-theory (enable lhs-rsh lhrange-bitproj lhatom-bitproj))))


  (fty::deffixcong lhs-norm-equiv equal (lhs-bitproj idx x) x
    :hints (("goal" :induct (lhs-bitproj idx x)
             :expand ((lhs-norm x)
                      (lhrange-bitproj idx (car x)))))))


(define lhs-first-aux ((w posp) (prev lhatom-p) (x lhs-p))
  :returns (first (iff (lhrange-p first) first))
  :verify-guards nil
  :measure (len x)
  (if (atom x)
      (lhrange w prev)
    (if (lhrange-combinable-dec w prev (lhrange->atom (car x)))
        (lhs-first-aux (+ (acl2::pos-fix w) (lhrange->w (car x))) prev (cdr x))
      (lhrange w prev)))
  ///
  (deffixequiv lhs-first-aux)

  (verify-guards lhs-first-aux
    :hints(("Goal" :in-theory (enable lhrange-nextbit))))

  (defthm lhs-first-aux-in-terms-of-lhs-norm
    (equal (lhs-first-aux w prev x)
           (car (lhs-cons (lhrange w prev) (lhs-norm x))))
    :hints(("Goal" :induct (lhs-first-aux w prev x))
           (and stable-under-simplificationp
                '(:expand ((lhs-norm x))
                  :in-theory (enable lhs-cons)))
           (and stable-under-simplificationp
                '(:in-theory (enable lhrange-nextbit))))))

(define lhs-first ((x lhs-p))
  ;; :returns (first (iff (lhrange-p first) first))
  :enabled t
  :guard-hints (("goal" :expand ((lhs-norm x)
                                 (lhs-norm (cdr x)))
                 :in-theory (enable lhs-cons lhrange-nextbit)))
  ; :verify-guards nil
  (mbe :logic (car (lhs-norm x))
       :exec
       (and (consp x)
            (if (consp (cdr x))
                (if (lhrange-combinable (car x) (lhrange->atom (cadr x)))
                    (lhs-first-aux (+ (lhrange->w (car x))
                                      (lhrange->w (cadr x)))
                                   (lhrange->atom (car x))
                                   (cddr x))
                  (car x))
              (car x))))
  ///
  (defthm lhs-norm-car-under-iff
    (iff (car (lhs-norm x))
         (consp (lhs-norm x)))
    :hints(("Goal" :use ((:instance lhs-p-of-lhs-norm))
            :expand ((lhs-p (lhs-norm x)))
            :in-theory (disable lhs-p-of-lhs-norm)))))

(define lhs-rest-aux ((w posp) (prev lhatom-p) (x lhs-p))
  :returns (rest lhs-p)
  :verify-guards nil
  :measure (len x)
  (if (and (consp x)
           (lhrange-combinable-dec w prev (lhrange->atom (car x))))
      (lhs-rest-aux (+ (acl2::pos-fix w) (lhrange->w (car x))) prev (cdr x))
    (lhs-fix x))
  ///
  (deffixequiv lhs-rest-aux)

  (verify-guards lhs-rest-aux
    :hints(("Goal" :in-theory (enable lhrange-nextbit))))

  (defthm lhs-rest-aux-in-terms-of-lhs-norm
    (lhs-norm-equiv (lhs-rest-aux w prev x)
                    (cdr (lhs-cons (lhrange w prev) (lhs-norm x))))
    :hints(("Goal" :induct (lhs-rest-aux w prev x))
           (and stable-under-simplificationp
                '(:expand ((lhs-norm x)
                           (:free (x) (lhs-cons (lhrange w prev) x))))))))


(define lhs-rest ((x lhs-p))
  :returns (rest lhs-p)
  :verify-guards nil
  (mbe :logic (if (or (atom x) (atom (cdr x)))
                  nil
                (if (lhrange-combine (car x) (cadr x))
                    (lhs-rest (cdr x))
                  (lhs-fix (cdr x))))
       :exec
       (if (consp x)
           (if (and (consp (cdr x))
                    (lhrange-combinable (car x) (lhrange->atom (cadr x))))
               (lhs-rest-aux (+ (lhrange->w (car x))
                                (lhrange->w (cadr x)))
                             (lhrange->atom (car x))
                             (cddr x))
             (cdr x))
         x))
  ///
  (deffixequiv lhs-rest)
  (defthm lhs-rest-aux-elim
    (equal (lhs-rest-aux w prev x)
           (lhs-rest (cons (lhrange w prev) x)))
    :hints (("goal" :induct (lhs-rest-aux w prev x)
             :in-theory (enable (:i lhs-rest-aux))
             :expand ((lhs-rest-aux w prev x)
                      (lhs-first x)))
            (and stable-under-simplificationp
                 '(:in-theory (enable lhrange-nextbit)))
            (and stable-under-simplificationp
                 '(:expand ((lhs-fix x))))))

  (verify-guards lhs-rest
    :hints ((and stable-under-simplificationp
                 '(:in-theory (enable lhrange-nextbit
                                      lhs-first)))))

  (defthm lhs-rest-in-terms-of-lhs-norm
    (lhs-norm-equiv (lhs-rest x)
                    (cdr (lhs-norm x)))
    :hints (("goal" :induct (lhs-rest x))
            (and stable-under-simplificationp
                 '(:expand ((lhs-norm x)
                            (lhs-norm (cdr x)))
                   :in-theory (enable lhs-cons
                                      lhrange-nextbit)))))

  (defthm lhs-normp-of-lhs-rest
    (implies (lhs-normp x)
             (lhs-normp (lhs-rest x)))
    :hints(("Goal" :in-theory (enable lhs-rest)
            :induct t)))

  (defthm lhs-rest-of-lhs-norm
    (equal (lhs-rest (lhs-norm x))
           (cdr (lhs-norm x)))
    :hints (("goal" :use ((:instance lhs-rest-in-terms-of-lhs-norm
                           (x (lhs-norm x))))
             :in-theory (disable lhs-rest-in-terms-of-lhs-norm))))

  (defthm len-of-lhs-rest
    (implies (consp x)
             (< (len (lhs-rest x)) (len x)))
    :rule-classes :linear)

  (local (defthm lhs-fix-of-atom
           (implies (atom x)
                    (equal (lhs-fix x) nil))
           :hints(("Goal" :in-theory (enable lhs-fix)))
           :rule-classes ((:rewrite :backchain-limit-lst 0))))

  (defthm cons-first-rest-when-first-is-car
    (implies (and (equal (car (lhs-norm x)) (car x))
                  (consp (lhs-norm x)))
             (equal (cons (car x) (lhs-rest x))
                    (lhs-fix x)))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (enable lhs-cons)
             :expand ((lhs-norm x)
                      (lhs-rest x)
                      (lhs-fix x)
                      (lhs-norm (cdr x)))))
    :otf-flg t)

  (defthm vars-of-lhs-rest
    (implies (not (member v (lhs-vars x)))
             (not (member v (lhs-vars (lhs-rest x)))))
    :hints(("Goal" :in-theory (enable lhs-rest)))))

(define lhs-decomp-aux ((w posp) (prev lhatom-p) (x lhs-p))
; Removed after v7-2 by Matt K. since logically, the definition is
; non-recursive:
; :measure (len x)
  :verify-guards nil
  :enabled t
  (mbe :logic (mv (lhs-first-aux w prev x)
                  (lhs-rest-aux w prev x))
       :exec
       (if (atom x)
           (mv (lhrange w prev)
               (lhs-fix x))
         (if (lhrange-combinable-dec w prev (lhrange->atom (car x)))
             (lhs-decomp-aux (+ w (lhrange->w (car x))) prev (cdr x))
           (mv (lhrange w prev) (lhs-fix x)))))
  ///
  (verify-guards lhs-decomp-aux
    :hints(("Goal" :in-theory (e/d (lhs-first-aux lhs-rest-aux)
                                   (lhs-rest-aux-elim
                                    lhs-first-aux-in-terms-of-lhs-norm))))))


(define lhs-decomp ((x lhs-p))
  :enabled t
  :guard-hints (("goal" :in-theory (e/d (lhs-first lhs-rest)
                                        (equal-of-lhatom-var
                                         equal-of-lhrange)))
                (and stable-under-simplificationp
                     '(:expand ((lhs-norm x)
                                (lhs-norm (cdr x))
                                (:free (x) (lhs-cons x nil))
                                (:free (x y z) (lhs-cons x (cons y z))))
                       :in-theory (e/d (lhrange-nextbit)
                                       (equal-of-lhatom-var
                                        equal-of-lhrange))
                       ;; :in-theory (e/d (lhs-cons lhrange-nextbit)
                       ;;                 (equal-of-lhatom-var
                       ;;                  equal-of-lhrange))
                       )))
  (mbe :logic (mv (lhs-first x)
                  (lhs-rest x))
       :exec (if (consp x)
                 (if (consp (cdr x))
                     (if (lhrange-combinable (car x) (lhrange->atom (cadr x)))
                         (lhs-decomp-aux (+ (lhrange->w (car x))
                                            (lhrange->w (cadr x)))
                                         (lhrange->atom (car x))
                                         (cddr x))
                       (mv (car x) (cdr x)))
                   (mv (car x) nil))
               (mv nil nil)))
  ///

  (local (include-book "centaur/misc/equal-sets" :dir :system))

  (local (in-theory (disable ACL2::SET-EQUIV-OF-NIL)))

  (defthmd lhs-vars-of-decomp-redef
    (set-equiv (lhs-vars x)
               (b* (((mv first rest) (lhs-decomp x))
                    ((unless first) nil))
                 (append (lhatom-vars (lhrange->atom first))
                         (lhs-vars rest))))
    :hints((acl2::witness :ruleset acl2::set-reasoning-no-consp)
           (and stable-under-simplificationp
                '(:use ((:instance vars-of-lhs-norm (v acl2::k0))
                        (:instance vars-of-lhs-norm (v acl2::k0)
                         (x (lhs-rest x))))
                  :in-theory (disable vars-of-lhs-norm)
                  :do-not-induct t)))
    :rule-classes ((:definition :install-body nil))))


(defprod driver
  ((value svex)
   (strength natp :default 6
             "Drive strength, using the values in SV2012 Table 28-7.  The default
              of 6 corresponds to @('strong0')/@('strong1'), which is also the
              default in Verilog when not specified."
             :rule-classes :type-prescription))
  :layout :tree)

;; (defprod assignment
;;   ((lhs lhs)
;;    (rhs svex)
;;    (strength1 natp :default 6
;;               "Drive strength to 1, using the values in SV2012 Table 28-7."
;;               :rule-classes :type-prescription)
;;    (strength0 natp :default 6
;;               "Drive strength to 0, using the values in SV2012 Table 28-7."
;;               :rule-classes :type-prescription))
;;   :layout :tree)

(defalist assigns :key-type lhs :val-type driver)
(defalist lhspairs :key-type lhs :val-type lhs)

(define assigns-vars ((x assigns-p))
  :measure (len (assigns-fix x))
  :returns (vars svarlist-p)
  (b* ((x (assigns-fix x))
       ((when (atom x)) nil)
       ((driver x1) (cdar x)))
    (append (lhs-vars (caar x))
            (svex-vars x1.value)
            (assigns-vars (cdr x)))))

(define lhspairs-vars ((x lhspairs-p))
  :measure (len (lhspairs-fix x))
  :returns (vars svarlist-p)
  (b* ((x (lhspairs-fix x)))
    (if (atom x)
        nil
      (append (lhs-vars (caar x))
              (lhs-vars (cdar x))
              (lhspairs-vars (cdr x))))))

(define svar-map-vars ((x svar-map-p))
  :measure (len (svar-map-fix x))
  :returns (vars svarlist-p)
  (b* ((x (svar-map-fix x)))
    (if (atom x)
        nil
      (append (list (caar x))
              (list (cdar x))
              (svar-map-vars (cdr x))))))

(defcong lhspairs-equiv lhspairs-equiv (append a b) 1)
(defcong lhspairs-equiv lhspairs-equiv (append a b) 2)


(defthm lhspairs-vars-of-append
  (equal (lhspairs-vars (append a b))
         (append (lhspairs-vars a)
                 (lhspairs-vars b)))
  :hints(("Goal" :in-theory (enable lhspairs-vars lhspairs-fix)
          :induct (lhspairs-vars a)
          :expand ((:free (a b) (lhspairs-vars (cons a b)))
                   (append a b)))))

(defcong assigns-equiv assigns-equiv (append a b) 1)
(defcong assigns-equiv assigns-equiv (append a b) 2)


(defthm assigns-vars-of-append
  (equal (assigns-vars (append a b))
         (append (assigns-vars a)
                 (assigns-vars b)))
  :hints(("Goal" :in-theory (enable assigns-vars assigns-fix)
          :induct (assigns-vars a)
          :expand ((:free (a b) (assigns-vars (cons a b)))
                   (append a b)))))

(defcong svar-map-equiv svar-map-equiv (append a b) 1)
(defcong svar-map-equiv svar-map-equiv (append a b) 2)


(defthm svar-map-vars-of-append
  (equal (svar-map-vars (append a b))
         (append (svar-map-vars a)
                 (svar-map-vars b)))
  :hints(("Goal" :in-theory (enable svar-map-vars svar-map-fix)
          :induct (svar-map-vars a)
          :expand ((:free (a b) (svar-map-vars (cons a b)))
                   (append a b)))))






(define svex-lhsrewrite-aux ((x svex-p) (shift natp) (w natp))
  :returns (xx svex-p)
  :verify-guards nil
  :measure (svex-count x)
  :hints ((and stable-under-simplificationp
               '(:expand ((svex-count x)))))
  (svex-case x
    :var (svex-fix x)
    :quote (svex-fix x)
    :call
    (b* ((shift (lnfix shift))
         (w (lnfix w)))
      (case x.fn
        (concat (b* (((unless (and (eql (len x.args) 3)
                                   (eq (svex-kind (first x.args)) :quote)
                                   (4vec-index-p (svex-quote->val (first x.args)))))
                      (svex-fix x))
                     (xw (2vec->val (svex-quote->val (first x.args))))
                     ((when (<= xw shift))
                      (svex-concat xw (svex-quote (4vec-z))
                                   (svex-lhsrewrite-aux (third x.args)
                                                    (- shift xw)
                                                    w)))
                     ((when (<= (+ shift w) xw))
                      (svex-lhsrewrite-aux (second x.args) shift w))
                     (low (svex-lhsrewrite-aux (second x.args) shift (- xw shift)))
                     (high (svex-lhsrewrite-aux (third x.args) 0 (- (+ shift w) xw))))
                  (svex-concat xw low high)))
        (signx
         (b* (((unless (and (eql (len x.args) 2)
                            (eq (svex-kind (first x.args)) :quote)
                            (4vec-index-p (svex-quote->val (first x.args)))))
               (svex-fix x))
              (xw (2vec->val (svex-quote->val (first x.args))))
              ((when (<= xw shift))
               (svex-fix x))
              ((when (<= (+ shift w) xw))
               (svex-lhsrewrite-aux (second x.args) shift w)))
           (svex-fix x)))
        (rsh (b* (((unless (and (eql (len x.args) 2)
                                (eq (svex-kind (first x.args)) :quote)
                                (4vec-index-p (svex-quote->val (first x.args)))))
                   (svex-fix x))
                  (xsh (2vec->val (svex-quote->val (first x.args)))))
               (svex-rsh xsh (svex-lhsrewrite-aux (second x.args) (+ shift xsh) w))))
        (otherwise (svex-fix x)))))
  ///
  (deffixequiv svex-lhsrewrite-aux
    :hints (("goal" :induct t
             :expand ((svex-lhsrewrite-aux (svex-fix x) shift w)
                      (svex-lhsrewrite-aux x (nfix shift) w)
                      (svex-lhsrewrite-aux x shift (nfix w))))))
  (verify-guards svex-lhsrewrite-aux)

  (local (defthm 4vec-zero-ext-is-concat
           (equal (4vec-zero-ext n x)
                  (4vec-concat n x 0))
           :hints(("Goal" :in-theory (enable 4vec-zero-ext
                                             4vec-concat)))))

  (local (defthm logapp-logtail-logext
           (implies (<= (+ (nfix shift) (nfix w)) (nfix extw))
                    (equal (logapp w (logtail shift (logext extw x)) y)
                           (logapp w (logtail shift x) y)))
           :hints ((acl2::logbitp-reasoning))))

  (local (defthm concat-of-rsh-of-sign-ext
           (implies (and (2vec-p extw)
                         (2vec-p w)
                         (2vec-p shift)
                         (natp (2vec->val w))
                         (natp (2vec->val shift))
                         (<= (+ (2vec->val shift) (2vec->val w))
                             (2vec->val extw)))
                    (equal (4vec-concat w (4vec-rsh shift (4vec-sign-ext extw x)) y)
                           (4vec-concat w (4vec-rsh shift x) y)))
           :hints(("Goal" :in-theory (enable 4vec-concat 4vec-rsh 4vec-shift-core 4vec-sign-ext)))))


  (defthm svex-lhsrewrite-aux-correct-lemma
    (equal (4vec-concat (2vec (nfix w)) (4vec-rsh (2vec (nfix shift)) (svex-eval (svex-lhsrewrite-aux x shift w) env)) (4vec-z))
           (4vec-concat (2vec (nfix w)) (4vec-rsh (2vec (nfix shift)) (svex-eval x env)) (4vec-z)))
    :hints (("goal" :expand ((svex-eval x env)
                             (:free (fn args) (svex-eval (svex-call fn args) env))
                             (svexlist-eval (svex-call->args x) env)
                             (svexlist-eval (cdr (svex-call->args x)) env)
                             (svexlist-eval (cddr (svex-call->args x)) env))
             :in-theory (enable svex-apply 4veclist-nth-safe svexlist-eval
                                4vec-index-p nth
                                equal-of-4vec-concat)
             :induct t)))

  (defthm svex-lhsrewrite-aux-vars
    (implies (not (member v (svex-vars x)))
             (not (member v (svex-vars (svex-lhsrewrite-aux x sh w)))))
    :hints (("goal" :induct (svex-lhsrewrite-aux x sh w)
             :expand ((svex-lhsrewrite-aux x sh w)
                      (svex-vars x))
             :in-theory (disable (:d svex-lhsrewrite-aux)
                                 member)))))

(define svex-int ((x integerp))
  :returns (svex svex-p)
  :inline t
  (svex-quote (2vec (lifix x)))
  ///
  (defret svex-int-correct
    (equal (svex-eval svex env) (2vec (ifix x))))

  (defret svex-int-vars
    (equal (svex-vars (svex-int x)) nil)))



(define svex-lhs-preproc-blkrev ((nbits natp)
                                 (blocksz posp)
                                 (x svex-p))
  :returns (blkrev svex-p)
  :measure (nfix nbits)
  :verify-guards nil
  (b* ((nbits (lnfix nbits))
       (blocksz (lposfix blocksz))
       ((when (< nbits blocksz))
        (svcall concat (svex-int nbits) x 0))
       (next-nbits (- nbits blocksz))
       (rest (svex-lhs-preproc-blkrev next-nbits blocksz (svcall rsh (svex-int blocksz) x))))
    (svcall concat (svex-quote (2vec next-nbits)) rest
            (svcall concat (svex-int blocksz) x 0)))
  ///
  (verify-guards svex-lhs-preproc-blkrev)
  (defret svex-lhs-preproc-blkrev-correct
    (equal (svex-eval blkrev env)
           (4vec-rev-blocks (2vec (nfix nbits)) (2vec (pos-fix blocksz))
                            (svex-eval x env)))
    :hints (("goal" :induct t)
            (and stable-under-simplificationp
                 '(:in-theory (enable svex-apply svexlist-eval 4vec-concat 4vec-rsh 4vec-shift-core
                                      4vec-rev-blocks rev-blocks)))))

  (defret svex-lhs-preproc-blkrev-vars
    (equal (svex-vars blkrev)
           (svex-vars x))
    :hints(("Goal" :in-theory (enable svexlist-vars)))))

(defines svex-lhs-preproc
  :verify-guards nil
  (define svex-lhs-preproc ((x svex-p))
    :short "Preprocesses an expression into one that only contains concat, rsh, and
          signx operators."
    :long "<p>Handles zerox, blkrev, bitsel operators.</p>"
    :measure (svex-count x)
    :returns (new-x svex-p)
    (b* ((x (svex-fix x)))
      (svex-case x
        :call (case x.fn
                ((concat rsh signx)
                 (change-svex-call x :args (svexlist-lhs-preproc x.args)))

                ((partsel)
                 (b* (((unless (and (eql (len x.args) 3)
                                    (svex-case (first x.args) :quote)
                                    (4vec-index-p (svex-quote->val (first x.args)))))
                       x))
                   (svcall concat
                           (second x.args)
                           (svcall rsh (first x.args)
                                   (svex-lhs-preproc (third x.args)))
                           0)))

                (zerox
                 (b* (((unless (eql (len x.args) 2)) x))
                   (svcall concat
                           (svex-lhs-preproc (first x.args))
                           (svex-lhs-preproc (second x.args))
                           0)))

                (blkrev
                 (b* (((unless (and (eql (len x.args) 3)
                                    (svex-case (first x.args) :quote)
                                    (4vec-index-p (svex-quote->val (first x.args)))
                                    (svex-case (second x.args) :quote)
                                    (2vec-p (svex-quote->val (second x.args)))
                                    (< 0 (2vec->val (svex-quote->val (second x.args))))))
                       x))
                   (svex-lhs-preproc-blkrev
                    (2vec->val (svex-quote->val (first x.args)))
                    (2vec->val (svex-quote->val (second x.args)))
                    (svex-lhs-preproc (third x.args)))))

                (bitsel
                 (b* (((unless (and (eql (len x.args) 2)
                                    (svex-case (first x.args) :quote)
                                    (4vec-index-p (svex-quote->val (first x.args)))))
                       x))
                   (svcall concat 1 (svcall rsh (first x.args)
                                            (svex-lhs-preproc (second x.args)))
                           0)))
                (otherwise x))
      :otherwise x)))

  (define svexlist-lhs-preproc ((x svexlist-p))
    :measure (svexlist-count x)
    :returns (new-x svexlist-p)
    (if (atom x)
        nil
      (cons (svex-lhs-preproc (car x))
            (svexlist-lhs-preproc (cdr x)))))
  ///
  (local (in-theory (disable svex-lhs-preproc svexlist-lhs-preproc)))

  (local (defthm 4vec-zero-ext-to-concat
           (equal (4vec-zero-ext n x) (4vec-concat n x 0))
           :hints(("Goal" :in-theory (enable 4vec-zero-ext 4vec-concat)))))

  (local (defthm 4vec-bit-extract-to-concat
           (implies (4vec-index-p n)
                    (equal (4vec-bit-extract n x) (4vec-concat 1 (4vec-rsh n x) 0)))
           :hints(("Goal" :in-theory (enable 4vec-bit-extract 4vec-concat 4vec-rsh 4vec-shift-core
                                             4vec-bit-index)))))

  (local (defthm 4vec-part-select-to-concat
           (implies (4vec-index-p lsb)
                    (equal (4vec-part-select lsb width x)
                           (4vec-concat width (4vec-rsh lsb x) 0)))
           :hints(("Goal" :in-theory (enable 4vec-part-select))
                  (and stable-under-simplificationp
                       '(:in-theory (enable 4vec-concat))))))

  (defthm-svex-lhs-preproc-flag
    (defthm svex-lhs-preproc-correct
      (equal (svex-eval (svex-lhs-preproc x) env)
             (svex-eval x env))
      :hints ((and stable-under-simplificationp
                   '(:in-theory (enable svex-apply 4veclist-nth-safe)
                     :expand ((:free (x) (nth 2 x))))))
      :flag svex-lhs-preproc)
    (defthm svexlist-lhs-preproc-correct
      (equal (svexlist-eval (svexlist-lhs-preproc x) env)
             (svexlist-eval x env))
      :flag svexlist-lhs-preproc)
    :hints ((acl2::just-expand-mrec-default-hint 'svex-lhs-preproc id t world)))

  (defthm-svex-lhs-preproc-flag
    (defthm svex-lhs-preproc-vars
      (equal (svex-vars (svex-lhs-preproc x))
             (svex-vars x))
      :hints ((and stable-under-simplificationp
                   '(:in-theory (enable svexlist-vars))))
      :flag svex-lhs-preproc)
    (defthm svexlist-lhs-preproc-vars
      (equal (svexlist-vars (svexlist-lhs-preproc x))
             (svexlist-vars x))
      :hints ((and stable-under-simplificationp
                   '(:in-theory (enable svexlist-vars))))
      :flag svexlist-lhs-preproc)
    :hints ((acl2::just-expand-mrec-default-hint 'svex-lhs-preproc id t world)))

  (deffixequiv-mutual svex-lhs-preproc)
  (verify-guards svex-lhs-preproc))



(define svex-lhsrewrite ((x svex-p)
                         (width natp))
  :returns (new-x svex-p)
  (b* ((preproc (svex-lhs-preproc x)))
    (svex-lhsrewrite-aux preproc 0 width))
  ///
  (defthm svex-lhsrewrite-correct-lemma
    (equal (4vec-concat (2vec (nfix w)) (svex-eval (svex-lhsrewrite x w) env) (4vec-z))
           (4vec-concat (2vec (nfix w)) (svex-eval x env) (4vec-z)))
    :hints (("goal" :use ((:instance svex-lhsrewrite-aux-correct-lemma
                           (shift 0) (x (svex-lhs-preproc x))))
             :in-theory (disable svex-lhsrewrite-aux-correct-lemma))))

  (defthm svex-lhsrewrite-vars
    (implies (not (member v (svex-vars x)))
             (not (member v (svex-vars (svex-lhsrewrite x w)))))))





;; { a[3:0], b[2:1] } = foo

;; (var w=2 rsh=1 b) (var w=4 rsh=0 a) = foo

;; (defprod netassign
;;   ((name svar)
;;    (rhs  svex)
;;    (strength1 natp :default 6
;;               :rule-classes :type-prescription)
;;    (strength0 natp :default 6
;;               :rule-classes :type-prescription))
;;   :layout :tree)

(deflist driverlist :elt-type driver)

(define driverlist-vars ((x driverlist-p))
  :returns (vars svarlist-p)
  (if (atom x)
      nil
    (append (svex-vars (driver->value (car x)))
            (driverlist-vars (cdr x))))
  ///
  (defthm driverlist-vars-of-cons
    (equal (driverlist-vars (cons x y))
           (append (svex-vars (driver->value x))
                   (driverlist-vars y)))))

(defalist netassigns :key-type svar :val-type driverlist
  ///
  (defthm netassigns-p-of-hons-remove-assoc
    (implies (netassigns-p x)
             (netassigns-p (acl2::hons-remove-assoc k x)))
    :hints(("Goal" :in-theory (enable netassigns-p acl2::hons-remove-assoc))))
  (defthm netassigns-p-of-fast-alist-clean
    (implies (netassigns-p x)
             (netassigns-p (fast-alist-clean x)))
    :hints(("Goal" :in-theory (e/d (acl2::fast-alist-clean-by-remove-assoc)
                                   (acl2::fast-alist-clean))))))

(define netassigns-vars ((x netassigns-p))
  :measure (len (netassigns-fix x))
  :returns (vars svarlist-p)
  (b* ((x (netassigns-fix x))
       ((when (atom x)) nil))
    (cons (caar x)
          (append (driverlist-vars (cdar x))
                  (netassigns-vars (cdr x)))))
  ///
  (defthm netassigns-vars-of-acons
    (equal (netassigns-vars (cons (cons a b) c))
           (cons (svar-fix a)
                 (append (driverlist-vars b)
                         (netassigns-vars c)))))

  (defthm netassigns-vars-of-append
    (equal (netassigns-vars (append a b))
           (append (netassigns-vars a)
                   (netassigns-vars b)))
  :hints(("Goal" :in-theory (enable netassigns-vars netassigns-fix append)
          :induct (netassigns-vars a)
          :expand ((:free (a b) (netassigns-vars (cons a b)))
                   (append a b)))))

  (defthm member-lookup-in-netassigns
    (implies (and (not (member v (netassigns-vars x)))
                  (netassigns-p x))
             (not (member v (driverlist-vars (cdr (hons-assoc-equal name x))))))
    :hints(("Goal" :in-theory (enable hons-assoc-equal))))

  (defthm netassign-vars-of-remove-assoc
    (implies (and (not (member v (netassigns-vars x)))
                  (netassigns-p x))
             (not (member v (netassigns-vars (acl2::hons-remove-assoc k x)))))
    :hints(("Goal" :in-theory (enable acl2::hons-remove-assoc))))

  (defthm netassign-vars-of-fast-alist-clean
    (implies (and (not (member v (netassigns-vars x)))
                  (netassigns-p x))
             (not (member v (netassigns-vars (fast-alist-clean x)))))
    :hints(("Goal" :in-theory (e/d (acl2::fast-alist-clean-by-remove-assoc)
                                   (acl2::fast-alist-clean))))))


(define assign->netassigns ((lhs lhs-p) (offset natp) (dr driver-p)
                            (acc netassigns-p "accumulator"))
  :parents (svex-compilation)
  :short "Turns an assignment (possibly to parts of wires) into several assignments
          to whole wires."
  :long "

<p>For example, suppose we have the following Verilog code:</p>

@({
 wire [10:0] a;
 wire [8:1] b;
 wire [3:2] c;
 wire [12:0] foo;
 assign { a[8:3], b[5:1] c } = foo;
 })

<p>We would turn this assignment into three separate assignments, essentially
like this:</p>

@({
 assign a = { 2'bz, foo[12:7], 3'bz };
 assign b = { 3'bz, foo[6:2] };
 assign c = foo[1:0];
 })

<p>The representation in SVEX is a bit different than the Verilog notation
suggests: we don't know each variable's width and we don't have a part-select
operator -- instead, on the left-hand side, we have an @(see lhs) structure
forming the concatenation, and on the right-hand side use shifts concatenations
to emulate part-selecting from the RHS expression.  So a more accurate view
would be as follows, where @('a[3+:6]') is meant to represent an @(see lhatom)
of width 6 and right-shift 3; @('inf') is used to signify an infinite-width
constant; and @('{ ... , 2'foo }') signifies concatenating the @('...') with 2
bits of @('foo'):</p>

@({
 assign { a[3+:6], b[1+:5], c[2+:2] } = foo;
 })
<p>becomes</p>
@({
 assign c = { 'z, 2'foo };
 assign b = { 'z, 5'(foo >> 2) };
 assign a = { 'z, 6'(foo >> 7), 3'bz };
 })"
  :returns (assigns netassigns-p)
  :measure (len lhs)
  (b* (((mv first rest) (lhs-decomp lhs))
       (acc (netassigns-fix acc))
       ((unless first) acc)
       ((lhrange first) first)
       (offset (lnfix offset))
       ((driver dr))
       ((when (eq (lhatom-kind first.atom) :z))
        (assign->netassigns rest (+ offset first.w) dr acc))
       ((lhatom-var first.atom))
       (new-driver (change-driver
                    dr :value (svex-concat first.atom.rsh
                                           (svex-z)
                                           (svex-concat first.w
                                                        (svex-rsh offset dr.value)
                                                        (svex-z)))))
       (rest-drivers (cdr (hons-get first.atom.name acc)))
       (acc (hons-acons first.atom.name (cons new-driver rest-drivers) acc)))
    (assign->netassigns rest (+ offset first.w) dr acc))
  ///
  (deffixequiv assign->netassigns)

  (defthm vars-of-assign->netassigns
    (implies (and (not (member v (lhs-vars lhs)))
                  (not (member v (svex-vars (driver->value dr))))
                  (not (member v (netassigns-vars acc))))
             (not (member v (netassigns-vars (assign->netassigns lhs offset dr acc)))))
    :hints (("goal" :induct (assign->netassigns lhs offset dr acc)
             :expand ((lhs-vars lhs))
             :in-theory (enable svex-alist-vars lhatom-vars)))))

(define assigns->netassigns-aux ((x assigns-p) (acc netassigns-p))
  :measure (len (assigns-fix x))
  :returns (netassigns netassigns-p)
  (b* ((x (assigns-fix x))
       (acc (netassigns-fix acc))
       ((when (atom x)) acc))
    (assigns->netassigns-aux (cdr x)
                             (assign->netassigns (caar x) 0 (cdar x) acc)))
  ///
  (defthm vars-of-assigns->netassigns-aux
    (implies (and (not (member v (assigns-vars x)))
                  (not (member v (netassigns-vars acc))))
             (not (member v (netassigns-vars (assigns->netassigns-aux x acc)))))
    :hints (("goal" :induct (assigns->netassigns-aux x acc)
             :expand ((assigns-vars x))))))

(define assigns->netassigns ((x assigns-p))
  :returns (netassigns netassigns-p)
  (fast-alist-free (fast-alist-clean (assigns->netassigns-aux x nil)))
  ///
  (defthm vars-of-assigns->netassigns
    (implies (not (member v (assigns-vars x)))
             (not (member v (netassigns-vars (assigns->netassigns x)))))
    :hints(("Goal" :in-theory (disable fast-alist-clean)))))



(acl2::defsort drivestrength-sort
  :prefix drivestrength
  :comparablep driver-p
  :comparable-listp driverlist-p
  :compare< (lambda (x y) (< (driver->strength y) (driver->strength x))))

(deffixequiv drivestrength-ordered-p
  :hints(("Goal" :in-theory (enable drivestrength-ordered-p)))
  :args ((x driverlist)))

(define svexlist-resolve ((x svexlist-p))
  :returns (res svex-p)
  (if (atom x)
      (svex-z)
    (if (atom (cdr x))
        (svex-fix (car x))
      (svcall* res (car x) (svexlist-resolve (cdr x)))))
  ///
  (defthm svex-vars-of-svexlist-resolve
    (set-equiv (svex-vars (svexlist-resolve x))
               (svexlist-vars x))
    :hints(("Goal" :in-theory (enable svexlist-vars svex-call* svexlist-quotesp))))

  (local (in-theory (enable svexlist-fix))))

(define driverlist-values-of-strength ((x driverlist-p) (strength natp))
  ;; Works only when sorted!
  :guard (drivestrength-ordered-p x)
  :guard-hints (("goal" :in-theory (enable drivestrength-ordered-p)))
  :returns (values svexlist-p)
  (b* (((when (atom x)) nil)
       ((driver x1) (car x))
       (strength (lnfix strength))
       ((when (eql strength x1.strength))
        (cons x1.value (driverlist-values-of-strength (cdr x) strength))))
    nil)
  ///
  (defthm svex-vars-of-driverlist-values-of-strength
    (implies (not (member v (driverlist-vars x)))
             (not (member v (svexlist-vars (driverlist-values-of-strength x strength)))))
    :hints(("Goal" :in-theory (enable svexlist-vars)))))

(define driverlist-rest-after-strength ((x driverlist-p) (strength natp))
  :guard (drivestrength-ordered-p x)
  :guard-hints (("goal" :in-theory (enable drivestrength-ordered-p)))
  :returns (rest driverlist-p)
  (b* (((when (atom x)) nil)
       ((driver x1) (car x))
       (strength (lnfix strength))
       ((when (< x1.strength strength))
        (driverlist-fix x)))
    (driverlist-rest-after-strength (cdr x) strength))
  ///
  (defthm vars-of-driverlist-rest-after-strength
    (implies (not (member v (driverlist-vars x)))
             (not (member v (driverlist-vars (driverlist-rest-after-strength x strength))))))

  (local (defthm len-of-driverlist-rest-after-strength-weak
           (<= (len (driverlist-rest-after-strength x strength)) (len x))
           :rule-classes :linear))

  (defthm len-of-driverlist-rest-after-strength
    (implies (consp x)
             (< (len (driverlist-rest-after-strength x (driver->strength (car x))))
                (len x)))
    :rule-classes :linear)

  (defthm drivestrength-ordered-p-of-driverlist-rest-after-strength
    (implies (drivestrength-ordered-p x)
             (drivestrength-ordered-p
              (driverlist-rest-after-strength x strength)))
    :hints(("Goal" :in-theory (enable drivestrength-ordered-p)))))

(define driverlist->svex ((x driverlist-p))
  :measure (len x)
  :guard (drivestrength-ordered-p x)
  :verify-guards nil
  :returns (value svex-p)
  (b* (((when (atom x)) (svex-z))
       (strength1 (driver->strength (car x)))
       (vals1 (driverlist-values-of-strength x strength1))
       (rest1 (driverlist-rest-after-strength x strength1))
       (res1 (svexlist-resolve vals1))
       ((when (atom rest1)) res1))
    (svcall* override res1 (driverlist->svex rest1)))
  ///
  (verify-guards driverlist->svex)
  (defthm vars-of-driverlist->svex
    (implies (not (member v (driverlist-vars x)))
             (not (member v (svex-vars (driverlist->svex x)))))))




(define netassigns->resolves-nrev ((x netassigns-p) (nrev))
  :measure (len (netassigns-fix x))
  (b* ((x (netassigns-fix x))
       ((when (atom x)) (acl2::nrev-fix nrev))
       ((cons name drivers) (car x))
       (value (driverlist->svex (drivestrength-sort (driverlist-fix drivers))))
       (nrev (acl2::nrev-push (cons name value) nrev)))
    (netassigns->resolves-nrev (cdr x) nrev)))


(define netassigns->resolves ((x netassigns-p))
  :measure (len (netassigns-fix x))
  :returns (assigns svex-alist-p)
  :verify-guards nil
  (mbe :logic
       (b* ((x (netassigns-fix x))
            ((when (atom x)) nil)
            ((cons name drivers) (car x))
            (value (driverlist->svex (drivestrength-sort (driverlist-fix drivers)))))
         (cons (cons name value)
               (netassigns->resolves (cdr x))))
       :exec
       (if (atom x)
           nil
         (acl2::with-local-nrev
           (netassigns->resolves-nrev x acl2::nrev))))
  ///
  (local (defthm netassigns->resolves-nrev-elim
           (equal (netassigns->resolves-nrev x nrev)
                  (append nrev (netassigns->resolves x)))
           :hints(("Goal" :in-theory (enable netassigns->resolves-nrev)))))

  (verify-guards netassigns->resolves)

  (defthm vars-of-drivestrength-insert
    (implies (and (not (member v (driverlist-vars x)))
                  (not (member v (svex-vars (driver->value elt)))))
             (not (member v (driverlist-vars (drivestrength-insert elt x)))))
    :hints(("Goal" :in-theory (enable drivestrength-insert))))

  (defthm vars-of-drivestrength-insertsort
    (implies (not (member v (driverlist-vars x)))
             (not (member v (driverlist-vars (drivestrength-insertsort x)))))
    :hints(("Goal" :in-theory (enable drivestrength-insertsort))))

  (defthm vars-of-netassigns->resolves
    (implies (not (member v (netassigns-vars x)))
             (and (not (member v (svex-alist-keys (netassigns->resolves x))))
                  (not (member v (svex-alist-vars (netassigns->resolves x))))))
    :hints(("Goal" :in-theory (enable netassigns-vars svex-alist-vars svex-alist-keys)))))


;; (define svar-indexedp ((x svar-p))
;;   (and (svar-addr-p x)
;;        (address->index (svar->address x))
;;        t)
;;   ///
;;   (defthmd svar-addr-p-when-svar-indexedp
;;     (implies (svar-indexedp x)
;;              (svar-addr-p x))))

(define svar-indexedp ((x svar-p))
  (natp (svar->name x)))

(define svar-index ((x svar-p))
  :guard (svar-indexedp x)
  :guard-hints (("goal" :in-theory (enable svar-indexedp)))
  :returns (idx natp :rule-classes :type-prescription)
  :inline t
  (lnfix (svar->name x))
  ///
  (deffixequiv svar-index
    :hints(("Goal" :in-theory (enable svar-fix svar-p)))))

(define svar-set-index ((x svar-p) (idx natp))
  ;; :guard (svar-addr-p x)
  :Returns (xx (and (svar-p xx)
                    (svar-indexedp xx))
               :hints(("Goal" :in-theory (enable svar-indexedp
                                                 svar->address
                                                 svar-addr-p))))
  (change-svar x :name (lnfix idx))
  ///
  (defthm svar-index-of-svar-set-index
    (equal (svar-index (svar-set-index x idx))
           (nfix idx))
    :hints(("Goal" :in-theory (enable svar-index svar->address)))))



(acl2::def-1d-arr lhsarr
  :slotname lhs
  :pred lhs-p
  :fix lhs-fix$inline
  :type-decl (satisfies lhs-p)
  :pkg-sym sv::svex
  :default-val nil)

(deflist lhslist :elt-type lhs :true-listp t :elementp-of-nil t)

(define lhslist-vars ((x lhslist-p))
  :measure (len x)
  :returns (vars svarlist-p)
  (if (atom x)
      nil
    (append (lhs-vars (car x))
            (lhslist-vars (cdr x))))
  ///
  (defthm lhslist-vars-of-append
    (equal (lhslist-vars (append a b))
           (append (lhslist-vars a)
                   (lhslist-vars b)))))

(defthm lhsarrp-is-lhslist-p
  (equal (lhsarr$ap x)
         (lhslist-p x)))

(define lhsarr-fix (lhsarr)
  :enabled t
  :inline t
  (mbe :logic (non-exec (lhslist-fix lhsarr))
       :exec lhsarr))

(fty::deffixcong lhslist-equiv lhs-equiv (nth n x) x)

(fty::deffixcong lhslist-equiv lhslist-equiv (update-nth n v x) x
  :hints(("Goal" :in-theory (enable update-nth))))

(fty::deffixcong lhs-equiv lhslist-equiv (update-nth n v x) v
  :hints(("Goal" :in-theory (enable update-nth))))

(defthm lhslist-fix-of-update-nth
  (equal (lhslist-fix (update-nth n v x))
         (update-nth n (lhs-fix v) (lhslist-fix x)))
  :hints(("Goal" :in-theory (enable lhslist-fix update-nth))))

(fty::deffixtype lhsarr :pred lhslist-p :fix lhslist-fix :equiv lhslist-equiv)


(define aliases-vars-aux ((n natp) lhsarr)
  :returns (vars svarlist-p)
  :guard (<= (lnfix n) (lhss-length lhsarr))
  (if (zp n)
      nil
    (append (lhs-vars (get-lhs (1- n) lhsarr))
            (aliases-vars-aux (1- n) lhsarr)))
  ///
  (defthmd vars-of-get-lhs-aux
    (implies (and (not (member v (aliases-vars-aux n lhsarr)))
                  (< (nfix m) (nfix n)))
             (not (member v (lhs-vars (nth m lhsarr)))))))

(define aliases-vars (lhsarr)
  :returns (vars svarlist-p)
  (aliases-vars-aux (lhss-length lhsarr) lhsarr)
  ///
  (local (include-book "std/lists/nth" :dir :system))
  (defthm vars-of-get-lhs
    (implies (not (member v (aliases-vars lhsarr)))
             (not (member v (lhs-vars (nth n lhsarr)))))
    :hints (("goal" :cases ((< (nfix n) (len lhsarr)))
             :in-theory (enable vars-of-get-lhs-aux)))))







;; An alias table is an array with one entry for every wire.  Each entry is a
;; lnsvex (a concatenation of right-shifts of variables) where each variable is
;; an index.  (Actually we don't require that they all are indices, but we
;; operate under the assumption that non-index variables don't have any
;; aliases.)  Initially, each wire should be aliased to itself; more
;; specifically, a wire declared as wname[8:4] would be aliased to
;; (CONCAT 4 '(0 . -1) (CONCAT 5 (RSH 4 WNAME) '(0 . -1)))

;;  -- except that in place of wname we'd see its index -- this signifies that
;; bits 3:0 and 9+ don't exist.  Following this initialization we examine a
;; series of pairs of lnsvex expressions denoting aliases among
;; wires/concatenations/selects of wires.  To process each such pair, we first
;; normalize each one; for each wire in the expresion, we look up that wire's
;; alias expression and recur on the pertinent parts of it, building up a
;; normalized expression as we find wires that are aliased to themselves.  Then
;; we scan over the normalized expressions, correlating the parts of each of
;; them; for each pair of wire ranges (wireidx,rshift,width) that are aliased,
;; we update the greater of the two wireidxes to alias that range with the
;; lesser one.  When we are done updating the canonical aliases, we then update
;; the rest of the wires that we traversed in order to canonicalize our
;; original expressions -- this ensures good amortized performance.  (Keeping
;; all wires constantly canonicalized would be expensive, as would traversing
;; the same non-canonicalized wires many times -- our approach is a form of the
;; disjoint-sets union/find algorithm.)

(acl2::defstobj-clone aliases lhsarr :strsubst (("LHS" . "ALIAS")))
  ;; :arrname aliases
  ;; :slotname alias
  ;; :pred lhs-p
  ;; :fix lhs-fix
  ;; :type-decl (satisfies lhs-p)
  ;; :pkg-sym sv::svex
  ;; :default-val nil)

;; (deflist lhslist :elt-type lhs :true-listp t)

;; (defthm aliasesp-is-lhslist-p
;;   (equal (aliasesp x)
;;          (lhslist-p x)))


(defthm lhslist-p-of-resize-list
  (implies (lhslist-p x)
           (lhslist-p (resize-list x n nil)))
  :hints(("Goal" :in-theory (e/d (resize-list)))))

;; (defthm lhslist-p-of-replicate
;;   (lhslist-p (replicate n nil))
;;   :hints(("Goal" :in-theory (e/d (replicate)))))

;; (defthm lhslist-p-of-update-nth
;;   (implies (and (lhslist-p x)
;;                 (lhs-p v))
;;            (lhslist-p (update-nth n v x)))
;;   :hints(("Goal" :in-theory (enable update-nth))))





(acl2::def-1d-arr svexarr
  :slotname svex
  :pred svex-p
  :fix svex-fix$inline
  :type-decl (satisfies svex-p)
  :pkg-sym sv::svex
  :default-val (-1 . 0))

(defthm svexarrp-is-svexlist-p
  (equal (svexarrp x)
         (svexlist-p x)))

(define svexarr-fix (svexarr)
  :enabled t
  :inline t
  (mbe :logic (non-exec (svexlist-fix svexarr))
       :exec svexarr))


(define svexarr-vars-aux ((n natp) svexarr)
  :returns (vars svarlist-p)
  :guard (<= (lnfix n) (svexs-length svexarr))
  (if (zp n)
      nil
    (append (svex-vars (get-svex (1- n) svexarr))
            (svexarr-vars-aux (1- n) svexarr)))
  ///
  (defthmd vars-of-get-svex-aux
    (implies (and (not (member v (svexarr-vars-aux n svexarr)))
                  (< (nfix m) (nfix n)))
             (not (member v (svex-vars (nth m svexarr))))))

  (define svexarr-vars-witness-aux (v (n natp) svexarr)
    :returns (idx (iff (natp idx) idx))
    :guard (<= (nfix n) (svexs-length svexarr))
    (if (zp n)
        nil
      (if (member-equal v (svex-vars (get-svex (1- n) svexarr)))
          (1- n)
        (svexarr-vars-witness-aux v (1- n) svexarr)))
    ///

    (defthm type-of-svexarr-vars-witness-aux
      (or (not (svexarr-vars-witness-aux v n svexarr))
          (natp (svexarr-vars-witness-aux v n svexarr)))
      :rule-classes :type-prescription)

    (defthm bound-of-svexarr-vars-witness-aux
      (implies (svexarr-vars-witness-aux v n svexarr)
               (< (svexarr-vars-witness-aux v n svexarr) (nfix n)))
      :rule-classes :linear)

    (defthm svexarr-vars-aux-witness-under-iff
      (implies (not (member v (svex-vars (nth (svexarr-vars-witness-aux v n svexarr) svexarr))))
               (not (svexarr-vars-witness-aux v n svexarr))))

    (defthmd member-svexarr-vars-aux
      (implies (not (svexarr-vars-witness-aux v n svexarr))
               (not (member v (svexarr-vars-aux n svexarr)))))))

(define svexarr-vars (svexarr)
  :returns (vars svarlist-p)
  (svexarr-vars-aux (svexs-length svexarr) svexarr)
  ///
  (local (include-book "std/lists/nth" :dir :system))
  (defthm vars-of-get-svex
    (implies (not (member v (svexarr-vars svexarr)))
             (not (member v (svex-vars (nth n svexarr)))))
    :hints (("goal" :cases ((< (nfix n) (len svexarr)))
             :in-theory (enable vars-of-get-svex-aux))))

  (define svexarr-vars-witness (v svexarr)
    :returns (idx (iff (natp idx) idx))
    (svexarr-vars-witness-aux v (svexs-length svexarr) svexarr)
    ///

    (defthm type-of-svexarr-vars-witness
      (or (not (svexarr-vars-witness v svexarr))
          (natp (svexarr-vars-witness v svexarr)))
      :rule-classes :type-prescription)

    (defthm type-of-svexarr-vars-witness2
      (implies (svexarr-vars-witness v svexarr)
               (natp (svexarr-vars-witness v svexarr))))

    (defthm bound-of-svexarr-vars-witness
      (implies (svexarr-vars-witness v svexarr)
               (< (svexarr-vars-witness v svexarr) (len svexarr)))
      :rule-classes ((:rewrite :corollary
                      (implies (and (svexarr-vars-witness v svexarr)
                                    (equal y (len svexarr)))
                               (< (svexarr-vars-witness v svexarr) y)))
                     ;; :linear
                     ))

    (defthm svexarr-vars-witness-under-iff
      (implies (not (member v (svex-vars (nth (svexarr-vars-witness v svexarr) svexarr))))
               (not (svexarr-vars-witness v svexarr))))

    (defthm member-svexarr-vars
      (implies (not (svexarr-vars-witness v svexarr))
               (not (member v (svexarr-vars svexarr))))
      :hints(("Goal" :in-theory (enable member-svexarr-vars-aux))))))


(define lhs->svex ((x lhs-p))
  :parents (lhs)
  :returns (xx svex-p)
  (if (atom x)
      (svex-quote (4vec-z))
    (b* (((lhrange xf) (car x)))
      (svex-concat xf.w
                   (lhatom->svex xf.atom)
                   (lhs->svex (cdr x)))))
  ///
  (deffixequiv lhs->svex)

  (defthm lhs->svex-correct
    (equal (svex-eval (lhs->svex x) env)
           (lhs-eval x env))
    :hints(("Goal" :in-theory (enable svex-eval svex-apply svexlist-eval 4veclist-nth-safe
                                      lhs-eval lhrange-eval))))

  (defthm vars-of-lhs->svex
    (implies (not (member v (lhs-vars x)))
             (not (member v (svex-vars (lhs->svex x)))))
    :hints(("Goal" :in-theory (enable lhatom-vars lhatom->svex)))))



(define lhs->svex-zero ((x lhs-p))
  :returns (xx svex-p)
  :prepwork ((local (in-theory (enable lhs-fix))))
  (if (atom x)
      (svex-quote 0)
    (b* (((lhrange xf) (car x)))
      (svex-concat xf.w
                   (lhatom->svex xf.atom)
                   (lhs->svex-zero (cdr x)))))
  ///
  (deffixequiv lhs->svex-zero)

  (defthm lhs->svex-zero-correct
    (equal (svex-eval (lhs->svex-zero x) env)
           (lhs-eval-zero x env))
    :hints(("Goal" :in-theory (enable svex-eval svex-apply svexlist-eval 4veclist-nth-safe
                                      lhs-eval-zero lhrange-eval))))

  (defthm vars-of-lhs->svex-zero
    (implies (not (member v (lhs-vars x)))
             (not (member v (svex-vars (lhs->svex-zero x)))))
    :hints(("Goal" :in-theory (enable lhatom-vars lhatom->svex)))))


(define lhsarr-to-svexarr ((n natp) lhsarr svexarr)
  :guard (and (<= n (lhss-length lhsarr))
              (<= (lhss-length lhsarr) (svexs-length svexarr)))
  :measure (nfix (- (lhss-length lhsarr) (nfix n)))
  (b* (((when (mbe :logic (zp (- (lhss-length lhsarr) (nfix n)))
                   :exec (eql n (lhss-length lhsarr))))
        (svexarr-fix svexarr))
       (lhs (get-lhs n lhsarr))
       (svex (lhs->svex lhs))
       (svexarr (set-svex n svex svexarr)))
    (lhsarr-to-svexarr (1+ (lnfix n)) lhsarr svexarr))
  ///
  (defthm len-of-lhsarr-to-svexarr
    (<= (len svexarr) (len (lhsarr-to-svexarr n lhsarr svexarr)))
    :rule-classes :linear)

  (defthm len-of-lhsarr-to-svexarr-equal
    (implies (<= (len lhsarr) (len svexarr))
             (equal (len (lhsarr-to-svexarr n lhsarr svexarr))
                    (len svexarr))))

  (deffixequiv lhsarr-to-svexarr)

  (defthm lookup-in-lhsarr-to-svexarr
    (svex-equiv (nth m (lhsarr-to-svexarr n lhsarr svexarr))
                (if (or (< (nfix m) (nfix n))
                        (<= (lhss-length lhsarr) (nfix m)))
                    (nth m svexarr)
                  (lhs->svex (nth m lhsarr))))
    :hints(("Goal" :in-theory (enable* acl2::arith-equiv-forwarding)))))











(define svar-boundedp ((x svar-p) (bound natp))
  (and (svar-indexedp x)
       (b* ((i (svar-index x)))
         (< i (lnfix bound))))
  ///
  (deffixequiv svar-boundedp)

  (defthm svar-boundedp-of-greater
    (implies (and (svar-boundedp x bound1)
                  (<= (nfix bound1) (nfix bound2)))
             (svar-boundedp x bound2)))

  (defthm svar-boundedp-implies-svar-indexedp
    (implies (svar-boundedp x bound)
             (and (svar-indexedp x)
                  (< (svar-index x) (nfix bound))
                  (implies (natp bound)
                           (< (svar-index x) (nfix bound)))))
    :rule-classes :forward-chaining)

  (defthm svar-boundedp-of-svar-set-index
    (iff (svar-boundedp (svar-set-index x idx) bound)
         (< (nfix idx) (nfix bound)))))


(std::deflist svarlist-boundedp (x bound)
  :guard (and (svarlist-p x)
              (natp bound))
  (svar-boundedp x bound)
  ///
  (deffixequiv svarlist-boundedp :args ((x svarlist) (bound natp))
    :hints(("Goal" :in-theory (enable svarlist-boundedp))))

  (defthmd svarlist-boundedp-of-greater
    (implies (and (svarlist-boundedp x bound1)
                  (<= (nfix bound1) (nfix bound2)))
             (svarlist-boundedp x bound2))))

(local (defthmd svarlist-boundedp-implies-not-member-when-not-svar-boundedp
         (implies (and (svarlist-boundedp x bound)
                       (not (svar-boundedp v bound)))
                  (not (member v x)))))



(define svarlist-boundedp-badguy ((x svarlist-p) (bound natp))
  :returns (badguy (iff (svar-p badguy) badguy)
                   :hints (("goaL" :induct t)
                           (and stable-under-simplificationp
                                '(:in-theory (enable svar-p)))))
  (if (atom x)
      (svar-set-index (address->svar (make-address :path "")) bound)
    (if (svar-boundedp (car x) bound)
        (svarlist-boundedp-badguy (cdr x) bound)
      (svar-fix (car x))))
  ///
  (defthm svarlist-boundedp-badguy-not-bounded
    (not (svar-boundedp (svarlist-boundedp-badguy x bound) bound))
    :hints (("goal" :induct t)))

  (defthmd svarlist-boundedp-badguy-rw
    (implies (acl2::rewriting-positive-literal `(svarlist-boundedp ,x ,bound))
             (equal (svarlist-boundedp x bound)
                    (let ((badguy (svarlist-boundedp-badguy x bound)))
                      (not (member badguy (svarlist-fix x))))))
    :hints(("Goal" :in-theory (enable svarlist-fix)
            :induct t)
           (and stable-under-simplificationp
                '(:use ((:instance svarlist-boundedp-implies-not-member-when-not-svar-boundedp
                         (v (svarlist-boundedp-badguy (cdr x) bound))
                         (x (svarlist-fix x))))
                  :in-theory (disable svarlist-boundedp-implies-not-member-when-not-svar-boundedp)))))

  (local (in-theory (enable svarlist-boundedp-badguy-rw)))

  (defthm svarlist-boundedp-badguy-1
    (implies (not (member (svarlist-boundedp-badguy x bound) (svarlist-fix x)))
             (svarlist-boundedp x bound)))

  (defthm svarlist-boundedp-badguy-not-member-when-bounded
    (implies (and (svarlist-boundedp x bound)
                  (svarlist-p x))
             (not (member (svarlist-boundedp-badguy y bound) x)))
    :hints(("Goal" :in-theory (enable svarlist-boundedp-implies-not-member-when-not-svar-boundedp))))

  (defthm svarlist-boundedp-badguy-not-equal-svar-addr
    (implies (svar-boundedp y bound)
             (not (equal (svarlist-boundedp-badguy x bound) y)))))



;; (defines svex-boundedp
;;   :verify-guards nil
;;   (define svex-boundedp ((x svex-p) (bound natp))
;;     :measure (svex-count x)
;;     (svex-case x
;;       :var (svar-boundedp x.name bound)
;;       :quote t
;;       :call (svexlist-boundedp x.args bound)))
;;   (define svexlist-boundedp ((x svexlist-p) (bound natp))
;;     :measure (svexlist-count x)
;;     (if (atom x)
;;         t
;;       (and (svex-boundedp (car x) bound)
;;            (svexlist-boundedp (cdr x) bound))))
;;   ///
;;   (deffixequiv-mutual svex-boundedp)
;;   (verify-guards svex-boundedp)

;;   (defthm-svex-boundedp-flag
;;     (defthm svex-boundedp-of-greater
;;       (implies (and (svex-boundedp x bound1)
;;                     (<= (nfix bound1) (nfix bound)))
;;                (svex-boundedp x bound))
;;       :flag svex-boundedp)
;;     (defthm svexlist-boundedp-of-greater
;;       (implies (and (svexlist-boundedp x bound1)
;;                     (<= (nfix bound1) (nfix bound)))
;;                (svexlist-boundedp x bound))
;;       :flag svexlist-boundedp)))

;; (define lhs-boundedp ((x lhs-p) (bound natp))
;;   (b* (((when (atom x)) t)
;;        ((lhrange xf) (car x))
;;        (rest (lhs-boundedp (cdr x) bound)))
;;     (lhatom-case xf.atom
;;       :z rest
;;       :var (and (svar-boundedp xf.atom.name bound)
;;                 rest)))
;;   ///
;;   (deffixequiv lhs-boundedp)

;;   (defthm lhs-boundedp-of-greater
;;     (implies (and (lhs-boundedp x bound1)
;;                   (<= (nfix bound1) (nfix bound2)))
;;              (lhs-boundedp x bound2)))

;;   (defthm lhs-boundedp-of-lhs-rest
;;     (implies (lhs-boundedp x bound)
;;              (lhs-boundedp (lhs-rest x) bound))
;;     :hints(("Goal" :in-theory (enable lhs-rest)))))

;; (define assigns-boundedp ((x assigns-p) (bound natp))
;;   :measure (len (assigns-fix x))
;;   (b* ((x (assigns-fix x))
;;        ((when (atom x)) t)
;;        ((cons lhs rhs) (car x)))
;;     (and (lhs-boundedp lhs bound)
;;          (svex-boundedp rhs bound)
;;          (assigns-boundedp (cdr x) bound)))
;;   ///
;;   (deffixequiv assigns-boundedp)

;;   (defthm assigns-boundedp-of-greater
;;     (implies (and (assigns-boundedp x bound1)
;;                   (<= (nfix bound1) (nfix bound2)))
;;              (assigns-boundedp x bound2))))

;; (define svar-map-boundedp ((x svar-map-p) (bound natp))
;;   :measure (len (svar-map-fix x))
;;   (b* ((x (svar-map-fix x))
;;        ((when (atom x)) t)
;;        ((cons lhs rhs) (car x)))
;;     (and (svar-boundedp lhs bound)
;;          (svar-boundedp rhs bound)
;;          (svar-map-boundedp (cdr x) bound)))
;;   ///
;;   (deffixequiv svar-map-boundedp)

;;   (defthm svar-map-boundedp-of-greater
;;     (implies (and (svar-map-boundedp x bound1)
;;                   (<= (nfix bound1) (nfix bound2)))
;;              (svar-map-boundedp x bound2))))

;; (define svex-alist-boundedp ((x svex-alist-p) (bound natp))
;;   :measure (len (svex-alist-fix x))
;;   (b* ((x (svex-alist-fix x))
;;        ((when (atom x)) t)
;;        ((cons lhs rhs) (car x)))
;;     (and (svar-boundedp lhs bound)
;;          (svex-boundedp rhs bound)
;;          (svex-alist-boundedp (cdr x) bound)))
;;   ///
;;   (local (in-theory (enable svex-alist-fix)))
;;   (fty::deffixcong svex-alist-equiv svex-alist-equiv (append a b) a)
;;   (fty::deffixcong svex-alist-equiv svex-alist-equiv (append a b) b)
;;   ;; (defthm svex-alist-fix-of-append
;;   ;;   (equal (svex-alist-fix (append x y))
;;   ;;          (append (svex-alist-fix x)
;;   ;;                  (svex-alist-fix y)))
;;   ;;   :hints(("Goal" :in-theory (enable svex-alist-fix))))

;;   (deffixequiv svex-alist-boundedp)

;;   (defthm svex-alist-boundedp-of-append
;;     (implies (and (svex-alist-boundedp x bound)
;;                   (svex-alist-boundedp y bound))
;;              (svex-alist-boundedp (append x y) bound))
;;     :hints(("Goal" :in-theory (enable append svex-alist-fix)
;;             :induct (append x y)
;;             :expand ((svex-alist-boundedp x bound)))))

;;   (defthm svex-alist-boundedp-of-assign->netassigns
;;     (implies (and (lhs-boundedp lhs bound)
;;                   (svex-boundedp rhs bound))
;;              (svex-alist-boundedp (assign->netassigns lhs rhs n) bound))
;;     :hints(("Goal" :in-theory (enable assign->netassigns
;;                                       lhs-boundedp svex-boundedp
;;                                       svexlist-boundedp
;;                                       svex-concat svex-rsh)
;;             :expand ((:free (f a) (svex-boundedp (svex-call f a) bound))))))

;;   (defthm svex-alist-boundedp-of-assigns->netassigns
;;     (implies (assigns-boundedp x bound)
;;              (svex-alist-boundedp (assigns->netassigns x) bound))
;;     :hints(("Goal" :in-theory (enable assigns->netassigns
;;                                       assigns-boundedp))))

;;   (defthm svex-alist-boundedp-of-hohs-shrink-alist
;;     (implies (and (svex-alist-boundedp x bound)
;;                   (svex-alist-boundedp y bound))
;;              (svex-alist-boundedp (hons-shrink-alist x y) bound))
;;     :hints(("Goal" :in-theory (enable hons-shrink-alist
;;                                       svex-alist-fix)
;;             :induct (hons-shrink-alist x y)
;;             :expand ((svex-alist-boundedp x bound)))))

;;   (defthm svex-boundedp-of-hons-assoc-equal-when-svex-alist-boundedp
;;     (implies (and (svex-alist-boundedp x bound)
;;                   (hons-assoc-equal k x))
;;              (svex-boundedp (cdr (hons-assoc-equal k x)) bound))
;;     :hints (("goal" :induct (hons-assoc-equal k x)
;;              :in-theory (enable svex-alist-fix)
;;              :expand ((svex-alist-boundedp x bound)))))

;;   (defthm svex-alist-boundedp-of-netassigns-collect-resolves
;;     (implies (and (svex-alist-boundedp x bound)
;;                   (svex-alist-boundedp acc bound))
;;              (svex-alist-boundedp (netassigns-collect-resolves x acc) bound))
;;     :hints(("Goal" :in-theory (enable netassigns-collect-resolves
;;                                       svexlist-boundedp)
;;             :induct (netassigns-collect-resolves x acc)
;;             :expand ((:free (f a) (svex-boundedp (svex-call f a) bound)))))))


;; (define lhspairs-boundedp ((x lhspairs-p) (bound natp))
;;   :measure (len (lhspairs-fix x))
;;   (b* ((x (lhspairs-fix x))
;;        ((when (atom x)) t)
;;        ((cons lhs rhs) (car x)))
;;     (and (lhs-boundedp lhs bound)
;;          (lhs-boundedp rhs bound)
;;          (lhspairs-boundedp (cdr x) bound)))
;;   ///
;;   (deffixequiv lhspairs-boundedp)

;;   (defthm lhspairs-boundedp-of-greater
;;     (implies (and (lhspairs-boundedp x bound1)
;;                   (<= (nfix bound1) (nfix bound2)))
;;              (lhspairs-boundedp x bound2))))



;; misc data structures used later
(defprod svex-override
  ((wire svex-p)
   (test svex-p)
   (val svex-p)))

(deflist svex-overridelist :elt-type svex-override)

(defprod lhs-override
  ((lhs lhs-p)
   (test svex-p)
   (val svex-p))
  :layout :tree)

(deflist lhs-overridelist :elt-type lhs-override)

(define lhs-override-vars ((x lhs-override-p))
  :returns (vars svarlist-p)
  (b* (((lhs-override x)))
    (append (svex-vars x.test)
            (svex-vars x.val)))
  ///
  (defthm vars-of-lhs-override->test
    (implies (not (member v (lhs-override-vars x)))
             (not (member v (svex-vars (lhs-override->test x))))))
  (defthm vars-of-lhs-override->val
    (implies (not (member v (lhs-override-vars x)))
             (not (member v (svex-vars (lhs-override->val x))))))

  (defthm vars-of-lhs-override
    (implies (and (not (member v (svex-vars test)))
                  (not (member v (svex-vars val))))
             (not (member v (lhs-override-vars (lhs-override lhs test val)))))))

(define lhs-overridelist-vars ((x lhs-overridelist-p))
  :returns (vars svarlist-p)
  (if (atom x)
      nil
    (append (lhs-override-vars (car x))
            (lhs-overridelist-vars (cdr x)))))

(define lhs-overridelist-keys ((x lhs-overridelist-p))
  :returns (vars svarlist-p)
  (if (atom x)
      nil
    (append (lhs-vars (lhs-override->lhs (car x)))
            (lhs-overridelist-keys (cdr x)))))







(define lhatom-normorderedp ((bound integerp) (offset natp) (x lhatom-p))
  (or (eq (lhatom-kind x) :z)
      (and (svar-indexedp (lhatom-var->name x))
           (let ((idx (svar-index (lhatom-var->name x))))
             (or (< idx (lifix bound))
                 (and (eql idx (lifix bound))
                      (<= (lhatom-var->rsh x)
                          (lnfix offset)))))))
  ///
  (deffixequiv lhatom-normorderedp)

  (defthm lhatom-normorderedp-implies-index
    (implies (and (lhatom-normorderedp bound offset x)
                  (equal (lhatom-kind x) :var))
             (svar-index (lhatom-var->name x)))
    :rule-classes (:rewrite :type-prescription))

  (defthm lhatom-normorderedp-implies-index-bound
    (implies (and (lhatom-normorderedp bound offset x)
                  (equal (lhatom-kind x) :var))
             (<= (svar-index (lhatom-var->name x)) (ifix bound)))
    :hints (("goal" :cases ((svar-index (lhatom-var->name x)))))
    :rule-classes :linear)

  (defthm lhatom-normorderedp-implies-rsh-when-at-bound
    (implies (and (lhatom-normorderedp bound offset x)
                  (equal (lhatom-kind x) :var)
                  (equal (svar-index (lhatom-var->name x)) (ifix bound)))
             (<= (lhatom-var->rsh x) (nfix offset)))
    :rule-classes :linear)

  (defthm lhatom-normorderedp-of-greater
    (implies (and (lhatom-normorderedp bound1 offset1 x)
                  (<= (ifix bound1) (ifix bound))
                  (<= (nfix offset1) (nfix offset)))
             (lhatom-normorderedp bound offset x)))

  (defthm lhatom-normorderedp-of-greater-bound
    (implies (and (lhatom-normorderedp bound1 offset1 x)
                  (< (ifix bound1) (ifix bound)))
             (lhatom-normorderedp bound offset x)))

  (defthm lhatom-normorderedp-of-z
    (lhatom-normorderedp bound offset :z))

  (defthm lhatom-normorderedp-implies-svarlist-bounded
    (implies (lhatom-normorderedp bound offset x)
             (svarlist-boundedp (lhatom-vars x) (+ 1 (ifix bound))))
    :hints(("Goal" :in-theory (enable svarlist-boundedp lhatom-vars svar-boundedp))))

  (defthm lhatom-normorderedp-implies-svar-indexedp
    (implies (and (lhatom-normorderedp idx offset x)
                  (equal (lhatom-kind x) :var))
             (svar-indexedp (lhatom-var->name x)))
    :rule-classes :forward-chaining))

(define lhs-vars-normorderedp ((bound integerp) (offset natp) (x lhs-p))
  :measure (len x)
  (if (atom x)
      t
    (and (lhatom-normorderedp bound offset (lhrange->atom (car x)))
         (lhs-vars-normorderedp bound (+ (lhrange->w (car x))
                                    (lnfix offset))
                           (cdr x))))
  ///
  (deffixequiv lhs-vars-normorderedp)

  (defthm lhs-vars-normorderedp-of-lhs-cons
    (equal (lhs-vars-normorderedp bound offset (lhs-cons x y))
           (lhs-vars-normorderedp bound offset (cons x y)))
    :hints(("Goal" :in-theory (enable lhs-cons lhrange-nextbit
                                      lhatom-normorderedp))))

  (fty::deffixcong lhs-norm-equiv equal (lhs-vars-normorderedp bound offset x) x
    :hints(("Goal" :in-theory (enable lhs-norm ; lhs-cons lhrange-nextbit
                                      ;; lhatom-normorderedp
                                      )
            :induct (lhs-vars-normorderedp bound offset x))
           (and stable-under-simplificationp
                '(:in-theory (enable lhatom-normorderedp lhs-norm lhs-cons)))
           ;; (and stable-under-simplificationp
           ;;      '(:expand ((LHS-VARS-NORMORDEREDP BOUND
           ;;                                   (+ (NFIX OFFSET) (LHRANGE->W (CAR X)))
           ;;                                   (LHS-NORM (CDR X))))))
           ))

  (defthm lhs-vars-normorderedp-implies-rest
    (implies (and (lhs-vars-normorderedp bound offset x)
                  (equal (nfix offset1)
                         (+ (nfix offset) (lhrange->w (car x)))))
             (lhs-vars-normorderedp bound offset1 (cdr x))))

  (defthm lhs-vars-normorderedp-implies-rest-strict
    (implies (and (<= (lhrange->w (car x)) (nfix offset))
                  (lhs-vars-normorderedp bound (- (nfix offset) (lhrange->w (car x))) x))
             (lhs-vars-normorderedp bound offset (cdr x)))
    :hints (("goal" :use ((:instance lhs-vars-normorderedp-implies-rest
                           (offset (- (nfix offset1) (lhrange->w (car x))))
                           (offset1 offset)))
             :in-theory (disable lhs-vars-normorderedp-implies-rest))))

  (defthm lhs-vars-normorderedp-implies-atom-normorderedp-of-car
    (implies (and (lhs-vars-normorderedp bound offset x)
                  (consp x))
             (lhatom-normorderedp bound offset (lhrange->atom (car x)))))

  (defthm lhs-vars-normorderedp-implies-index-bound
    (implies (and (lhs-vars-normorderedp bound offset x)
                  (consp x)
                  (eq (lhatom-kind (lhrange->atom (car x))) :var))
             (<= (svar-index (lhatom-var->name (lhrange->atom (car x))))
                 (ifix bound)))
    :rule-classes :linear)

  (defthm lhs-vars-normorderedp-implies-rsh-when-index-equal
    (implies (and (lhs-vars-normorderedp bound offset x)
                  (consp x)
                  (eq (lhatom-kind (lhrange->atom (car x))) :var)
                  (equal (svar-index (lhatom-var->name (lhrange->atom (car x))))
                         (ifix bound)))
             (<= (lhatom-var->rsh (lhrange->atom (car x))) (nfix offset)))
    :rule-classes :linear)

  (local (defun bitproj-ind ( offset idx x)
           (if (atom x)
               (list offset idx)
             (if (< (nfix idx) (lhrange->w (car x)))
                 offset
               (bitproj-ind (+ (lhrange->w (car x)) (nfix offset))
                            (- (nfix idx) (lhrange->w (car x)))
                            (cdr x))))))

  (defthm lhs-vars-normorderedp-implies-lhs-bitproj-index
    (implies (and (lhs-vars-normorderedp bound offset x)
                  (eq (lhbit-kind (lhs-bitproj idx x)) :var))
             (svar-index (lhbit-var->name (lhs-bitproj idx x))))
    :hints (("goal" :induct (bitproj-ind offset idx x)
             :in-theory (enable lhatom-bitproj)
             :expand ((lhs-bitproj idx x)
                      (lhs-vars-normorderedp bound offset x)))))

  (defthm lhs-vars-normorderedp-implies-lhs-bitproj-index-bound
    (implies (and (lhs-vars-normorderedp bound offset x)
                  (eq (lhbit-kind (lhs-bitproj idx x)) :var))
             (<= (svar-index (lhbit-var->name (lhs-bitproj idx x)))
                 (ifix bound)))
    :hints (("goal" :induct (bitproj-ind offset idx x)
             :in-theory (enable lhatom-bitproj)
             :expand ((lhs-bitproj idx x)
                      (lhs-vars-normorderedp bound offset x))))
    :rule-classes :linear)

  (defthm lhs-vars-normorderedp-implies-lhs-bitproj-idx-when-index-bound
    (implies (and (lhs-vars-normorderedp bound offset x)
                  (eq (lhbit-kind (lhs-bitproj idx x)) :var)
                  (equal (svar-index (lhbit-var->name (lhs-bitproj idx x)))
                         (ifix bound)))
             (<= (lhbit-var->idx (lhs-bitproj idx x))
                 (+ (nfix idx) (nfix offset))))
    :hints (("goal" :induct (bitproj-ind offset idx x)
             :in-theory (enable lhatom-bitproj)
             :expand ((lhs-bitproj idx x)
                      (lhs-vars-normorderedp bound offset x))))
    :rule-classes :linear)

  (local (defun normorderedp-of-greater-ind (offset offset1 x)
           (if (atom x)
               (list offset offset1)
             (normorderedp-of-greater-ind
              (+ (nfix offset) (lhrange->w (car x)))
              (+ (nfix offset1) (lhrange->w (car x)))
              (cdr x)))))

  (defthm lhs-vars-normorderedp-of-greater
    (implies (and (lhs-vars-normorderedp bound1 offset1 x)
                  (<= (ifix bound1) (ifix bound))
                  (<= (nfix offset1) (nfix offset)))
             (lhs-vars-normorderedp bound offset x))
    :hints (("goal" :induct (normorderedp-of-greater-ind offset offset1 x)
             :expand ((:free (bound offset) (lhs-vars-normorderedp bound offset x))))))

  (defthm lhs-vars-normorderedp-of-greater-bound
    (implies (and (lhs-vars-normorderedp bound1 offset1 x)
                  (< (ifix bound1) (ifix bound)))
             (lhs-vars-normorderedp bound offset x)))

  (local (defun normorderedp-of-rsh-ind (offset sh x)
           (if (or (atom x)
                   (< (nfix sh) (lhrange->w (car x))))
               offset
             (normorderedp-of-rsh-ind (+ (nfix offset)
                                    (lhrange->w (car x)))
                                 (- sh (lhrange->w (car x)))
                                 (cdr x)))))

  (local (defthmd lhs-vars-normorderedp-of-rsh-lemma
           (implies (lhs-vars-normorderedp bound offset x)
                    (lhs-vars-normorderedp bound (+ (nfix offset)
                                               (nfix sh)) (lhs-rsh sh x)))
           :hints(("Goal" :in-theory (enable lhs-rsh)
                   :induct ; (lhs-rsh sh x)
                   (normorderedp-of-rsh-ind offset sh x)
                   :expand ((lhs-rsh sh x)
                            (:free (offseT) (lhs-vars-normorderedp bound offset x))))
                  (and stable-under-simplificationp
                       '(:in-theory (enable lhatom-normorderedp))))))

  (defthm lhs-vars-normorderedp-of-rsh
    (implies (and (lhs-vars-normorderedp bound offset x)
                  (<= (+ (nfix offset) (nfix sh)) (nfix offset1)))
             (lhs-vars-normorderedp bound offset1 (lhs-rsh sh x)))
    :hints (("goal" :use lhs-vars-normorderedp-of-rsh-lemma)))

  (defthm lhs-vars-normorderedp-of-rsh-strict
    (implies (and (<= (nfix sh) (nfix offset1))
                  (equal offset (- (nfix offset1) (nfix sh)))
                  (lhs-vars-normorderedp bound offset x))
             (lhs-vars-normorderedp bound offset1 (lhs-rsh sh x)))
    :hints (("goal" :use ((:instance lhs-vars-normorderedp-of-rsh-lemma)))))

  (local (defun rsh-greater-bound-ind (offset offset1 sh x)
           (if (or (atom x)
                   (< (nfix sh) (lhrange->w (car x))))
               (list offset offset1)
             (rsh-greater-bound-ind (+ (nfix offset)
                                       (lhrange->w (car x)))
                                    (+ (nfix offset1)
                                       (lhrange->w (car x)))
                                    (- sh (lhrange->w (car x)))
                                    (cdr x)))))

  (defthm lhs-vars-normorderedp-of-rsh-greater-bound
    (implies (and (lhs-vars-normorderedp bound offset x)
                  (< (ifix bound) (ifix bound1)))
             (lhs-vars-normorderedp bound1 offset1 (lhs-rsh sh x)))
    :hints (("goal" :induct (normorderedp-of-rsh-ind offset sh x)
             :expand ((lhs-rsh sh x)
                      (:free (bound offset) (lhs-vars-normorderedp bound offset x))))
            (and stable-under-simplificationp
                 '(:in-theory (enable lhatom-normorderedp)))))

  (defthm lhs-vars-normorderedp-of-concat-strict
    (implies (and (lhs-vars-normorderedp bound offset x1)
                  (lhs-vars-normorderedp bound (+ (nfix offset)
                                             (nfix w)) x2))
             (lhs-vars-normorderedp bound offset (lhs-concat w x1 x2)))
    :hints (("goal" :induct (normorderedp-of-rsh-ind offset w x1)
             :expand ((lhs-concat w x1 x2)
                      (:free (offset) (lhs-vars-normorderedp bound offset x1))))))

  (defthm lhs-vars-normorderedp-of-concat
    (implies (and (lhs-vars-normorderedp bound offset x1)
                  (lhs-vars-normorderedp bound offset2 x2)
                  (<= (nfix offset2) (+ (nfix offset) (nfix w))))
             (lhs-vars-normorderedp bound offset (lhs-concat w x1 x2)))
    :hints (("goal" :use lhs-vars-normorderedp-of-concat-strict
             :in-theory (disable lhs-vars-normorderedp-of-concat-strict))))

  (defthm lhs-vars-normorderedp-implies-svarlist-boundedp
    (implies (lhs-vars-normorderedp bound offset x)
             (svarlist-boundedp (lhs-vars x) (+ 1 (ifix bound))))
    :hints(("Goal" :in-theory (enable lhs-vars)))))

(define aliases-normorderedp-aux ((n natp) aliases)
  :guard (<= n (aliass-length aliases))
  (if (zp n)
      t
    (and (lhs-vars-normorderedp (1- n) 0 (get-alias (1- n) aliases))
         (aliases-normorderedp-aux (1- n) aliases)))
  ///
  (deffixequiv aliases-normorderedp-aux)

  ;; (defthm aliases-normorderedp-aux-of-resize
  ;;   (implies (aliases-normorderedp-aux n aliases)
  ;;            (aliases-normorderedp-aux n (resize-list aliases m nil)))
  ;;   :hints(("Goal" :in-theory (enable resize-list)
  ;;           :induct (aliases-normorderedp-aux n aliases)
  ;;           :expand ((:free (n) (lhs-vars-normorderedp n 0 nil))))))

  (defchoose aliases-unnormorderedp-idx (idx) (aliases)
    (and (natp idx)
         (not (lhs-vars-normorderedp idx 0 (get-alias idx aliases)))))

  (defthmd not-aliases-normorderedp-aux-implies-unnormorderedp-idx
    (implies (not (aliases-normorderedp-aux n aliases))
             (let ((idx (aliases-unnormorderedp-idx aliases)))
               (not (lhs-vars-normorderedp (nfix idx) 0 (nth idx aliases)))))
    :hints (("goal" :induct (aliases-normorderedp-aux n aliases))
            (and stable-under-simplificationp
                 '(:use ((:instance aliases-unnormorderedp-idx (idx (1- n))))))))

  (defthmd aliases-normorderedp-aux-implies-get-alias
    (implies (and (aliases-normorderedp-aux m aliases)
                  (< (nfix n) (nfix m))
                  (<= (nfix n) (ifix nn)))
             (lhs-vars-normorderedp nn 0 (nth n aliases)))
    :hints(("Goal" :in-theory (enable aliases-normorderedp-aux)))))


(define aliases-normorderedp (aliases)
  :hooks nil
  (and (aliasesp aliases)
       (aliases-normorderedp-aux (aliass-length aliases) aliases))
  ///
  (local (in-theory (enable aliases-normorderedp-aux-implies-get-alias)))
  (local (include-book "std/lists/nth" :dir :system))
  (local (include-book "std/lists/resize-list" :dir :system))

  (defthm aliases-normorderedp-implies-get-alias
    (implies (and (aliases-normorderedp aliases)
                  (<= (nfix n) (ifix nn)))
             (lhs-vars-normorderedp nn 0 (nth n aliases)))
    :hints (("goal" :cases ((< (nfix n) (len aliases)))
             :expand ((lhs-vars-normorderedp nn 0 nil))
             :do-not-induct t)))

  (defthmd aliases-not-normorderedp-implies-unnormorderedp-idx
    (implies (and (not (aliases-normorderedp aliases))
                  (lhslist-p aliases))
             (let ((idx (aliases-unnormorderedp-idx aliases)))
               (not (lhs-vars-normorderedp (nfix idx) 0 (nth idx aliases)))))
    :hints(("Goal" :in-theory (enable not-aliases-normorderedp-aux-implies-unnormorderedp-idx))))

  (defthm aliases-normorderedp-of-resize
    (implies (aliases-normorderedp aliases)
             (aliases-normorderedp (resize-list aliases n nil)))
    :hints (("goal" :use ((:instance aliases-not-normorderedp-implies-unnormorderedp-idx
                           (aliases (resize-list aliases n nil))))
             :in-theory (disable aliases-normorderedp)
             :do-not-induct t
             :expand ((:free (n) (lhs-vars-normorderedp n 0 nil))
                      (aliases-normorderedp aliases)))))

  (defthm aliases-normorderedp-of-update-nth
    (implies (and (aliases-normorderedp aliases)
                  (lhs-p x)
                  (lhs-vars-normorderedp (nfix n) 0 x))
             (aliases-normorderedp (update-nth n x aliases)))
    :hints (("goal" :use ((:instance aliases-not-normorderedp-implies-unnormorderedp-idx
                           (aliases (update-nth n x aliases))))
             :in-theory (disable aliases-normorderedp)
             :expand ((:free (n) (lhs-vars-normorderedp n 0 nil))
                      (aliases-normorderedp aliases)))))

  (defthm aliases-normorderedp-of-replicate
    (aliases-normorderedp (replicate n nil))
    :hints (("goal" :use ((:instance aliases-not-normorderedp-implies-unnormorderedp-idx
                           (aliases (replicate n nil))))
             :in-theory (disable aliases-normorderedp)
             :expand ((:free (n) (lhs-vars-normorderedp n 0 nil))
                      (aliases-normorderedp aliases))))))


(define lhs-check-masks ((x lhs-p) (mask-acc 4vmask-alist-p) (conf-acc 4vmask-alist-p))
  :prepwork ((local (include-book "centaur/vl/util/default-hints" :dir :system)))
  :verbosep t
  :measure (len x)
  :returns (mv (mask-acc1 4vmask-alist-p)
               (conf-acc1 4vmask-alist-p))
  (b* ((mask-acc (4vmask-alist-fix mask-acc))
       (conf-acc (4vmask-alist-fix conf-acc))
       ((mv first rest) (lhs-decomp x))
       ((unless first) (mv mask-acc conf-acc))
       ((lhrange first) first)
       ((when (eq (lhatom-kind first.atom) :z))
        (lhs-check-masks rest mask-acc conf-acc))
       ((lhatom-var first.atom) first.atom)
       (firstmask (sparseint-concatenate first.atom.rsh 0 (sparseint-concatenate first.w -1 0)))
       (varmask (or (cdr (hons-get first.atom.name mask-acc)) 0))
       (conflict (sparseint-bitand varmask firstmask))
       (mask-acc (hons-acons first.atom.name (sparseint-bitor firstmask varmask) mask-acc))
       (conf-acc (if (sparseint-bit 0 conflict)
                     conf-acc
                   (hons-acons first.atom.name
                               (sparseint-bitor conflict
                                                (or (cdr (hons-get first.atom.name conf-acc))
                                                    0))
                               conf-acc))))
    (lhs-check-masks rest mask-acc conf-acc)))


(define assigns-check-masks ((x assigns-p) (mask-acc 4vmask-alist-p) (conf-acc 4vmask-alist-p))
  :returns (mv (mask-acc1 4vmask-alist-p)
               (conf-acc1 4vmask-alist-p))
  :measure (len (assigns-fix x))
  :hints(("Goal" :in-theory (enable len)))
  (b* ((x (assigns-fix x))
       (mask-acc (4vmask-alist-fix mask-acc))
       (conf-acc (4vmask-alist-fix conf-acc))
       ((when (atom x))
        (mv mask-acc conf-acc))
       ((mv mask-acc conf-acc) (lhs-check-masks (caar x) mask-acc conf-acc)))
    (assigns-check-masks (cdr x) mask-acc conf-acc)))




(define make-simple-lhs (&key (width posp)
                              ((rsh natp) '0)
                              (var svar-p))
  :returns (lhs lhs-p)
  (list (sv::make-lhrange :w width :atom (sv::make-lhatom-var :name var :rsh rsh)))
  ///
  (defret vars-of-make-simple-lhs
    (equal (lhs-vars lhs) (list (svar-fix var)))
    :hints(("Goal" :in-theory (enable lhatom-vars)))))

;; This is used in vl/expr.lisp as well as now svstmt.lisp, so it needs to be in a
;; book that both include...
(defconst *svex-longest-static-prefix-var*
  :svex-longest-static-prefix)
