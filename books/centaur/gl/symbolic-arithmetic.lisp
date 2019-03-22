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

; cert_param: (non-acl2r)

(in-package "GL")
(include-book "bvecs")
(include-book "bfr-reasoning")
(local (include-book "clause-processors/find-subterms" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "arith-lemmas"))

; Matt K. mod to avoid ACL2(p) errors from (bfr-reasoning).
#+acl2-par
(set-waterfall-parallelism nil)

(local (defthm equal-complexes-rw
         (implies (and (acl2-numberp x)
                       (rationalp a)
                       (rationalp b))
                  (equal (equal (complex a b) x)
                         (and (equal a (realpart x))
                              (equal b (imagpart x)))))
         :hints (("goal" :use ((:instance realpart-imagpart-elim))))))


(defsection symbolic-arithmetic
  :parents (reference)
  :short "Internal operations for computing on symbolic bit vectors."
  :long "<p>Naming convention:</p>
<ul>
<li>B stands for a boolean variable.</li>
<li>S stands for a signed bvec.</li>
<li>U stands for an unsigned bvec.</li>
<li>V stands for a generic bvec where signedness doesn't matter.</li>
<li>N stands for a known natural constant.</li>
</ul>

<p>For instance, @('bfr-ite-bss-fn') has @('bss'), indicating that it's
for computing:</p>

@({
     (ite Boolean Signed-Bvec Signed-Bvec)
})")

(local (xdoc::set-default-parents symbolic-arithmetic))

;;---------------- Misc function definitions and lemmas -------------------

(define int-set-sign ((negp "True if we should set the sign bit to 1.")
                      (i    integerp "The integer to modify."))
  :short "Change the sign bit of an integer to a new value."
  :returns (new-i integerp :rule-classes :type-prescription)
  (let ((i (lifix i)))
    (acl2::logapp (integer-length i) i (if negp -1 0)))
  ///
  (defthm sign-of-int-set-sign
    (iff (< (int-set-sign negp i) 0)
         negp)
    :hints(("Goal" :in-theory (e/d* (int-set-sign)
                                    (acl2::logapp
                                     acl2::ifix-under-int-equiv))))))

(define non-int-fix (x)
  :short "Identity for non-integers; coerces any integers to @('nil')."
  (declare (xargs :guard t))
  (and (not (integerp x))
       x)
  ///
  (defthm non-int-fix-when-non-integer
    (implies (not (integerp x))
             (equal (non-int-fix x) x))
    :hints(("Goal" :in-theory (enable non-int-fix)))
    :rule-classes ((:rewrite :backchain-limit-lst 0))))

(define maybe-integer ((i integerp) x intp)
  (if intp
      (ifix i)
    (non-int-fix x))
  ///
  (defthm maybe-integer-t
    (equal (maybe-integer i x t)
           (ifix i))
    :hints(("Goal" :in-theory (enable maybe-integer))))

  (defthm maybe-integer-nil
    (equal (maybe-integer i x nil)
           (non-int-fix x))
    :hints(("Goal" :in-theory (enable maybe-integer)))))

;;-------------------------- DEFSYMBOLIC -----------------------------------

(defun extract-some-keywords
  (legal-kwds ; what keywords the args are allowed to contain
   args       ; args that the user supplied
   kwd-alist  ; accumulator alist of extracted keywords to values
   )
  "Returns (mv kwd-alist other-args other-keywords)"
  (declare (xargs :guard (and (symbol-listp legal-kwds)
                              (no-duplicatesp legal-kwds)
                              (alistp kwd-alist))))
  (b* (((when (atom args))
        (mv kwd-alist nil args))
       (arg1 (first args))
       ((unless (and (keywordp arg1)
                     (consp (cdr args))))
        (b* (((mv kwd-alist other-kws other-args)
              (extract-some-keywords legal-kwds (cdr args) kwd-alist)))
          (mv kwd-alist other-kws (cons arg1 other-args))))
       ((unless (member arg1 legal-kwds))
        (b* (((mv kwd-alist other-kws other-args)
              (extract-some-keywords legal-kwds (cddr args) kwd-alist)))
          (mv kwd-alist (cons arg1 (cons (cadr args) other-kws))
              other-args)))
       (value (second args))
       (kwd-alist (acons arg1 value kwd-alist)))
    (extract-some-keywords legal-kwds (cddr args) kwd-alist)))

(defun defsymbolic-check-formals (x)
  (if (atom x)
      t
    (if (and (consp (car x))
             (eql (len (car x)) 2)
             (symbolp (caar x))
             (member (cadar x) '(n i p b u s ru rs)))
        (defsymbolic-check-formals (cdr x))
      (er hard? 'defsymbolic-check-formals
          "Bad formal: ~x0" (car x)))))

(defun defsymbolic-check-returns (x)
  (if (atom x)
      t
    (if (and (consp (car x))
             (>= (len (car x)) 2)
             (symbolp (caar x))
             (member (cadar x) '(n i p b u s ru rs))
             (or (member (cadar x) '(n i))
                 (eql (len (car x)) 3)))
        (defsymbolic-check-returns (cdr x))
      (er hard? 'defsymbolic-check-returns
          "Bad return: ~x0" (car x)))))

(defun defsymbolic-formals-pair-with-evals (x)
  (if (atom x)
      nil
    (cons (cons (caar x)
                (case (cadar x)
                  (n `(nfix ,(caar x)))
                  (i `(ifix ,(caar x)))
                  (p `(acl2::pos-fix ,(caar x)))
                  (b `(bfr-eval ,(caar x) env))
                  (u `(bfr-list->u ,(caar x) env))
                  (s `(bfr-list->s ,(caar x) env))
                  (ru `(bfr-list->u (acl2::rev ,(caar x)) env))
                  (rs `(bfr-list->s (acl2::rev ,(caar x)) env))))
          (defsymbolic-formals-pair-with-evals (cdr x)))))

(defun defsymbolic-define-formals (x)
  (if (atom x)
      nil
    (cons (case (cadar x)
            (n `(,(caar x) natp))
            (i `(,(caar x) integerp))
            (p `(,(caar x) posp))
            ((u s ru rs) `(,(caar x) true-listp))
            (t (caar x)))
          (defsymbolic-define-formals (cdr x)))))

(defun defsymbolic-guards (x)
  (if (atom x)
      nil
    (append (case (cadar x)
              (n `((natp ,(caar x))))
              (i `((integerp ,(caar x))))
              (p `((posp ,(caar x))))
              ((u s ru rs) `((true-listp ,(caar x)))))
            (defsymbolic-guards (cdr x)))))

(defun defsymbolic-define-returns1 (x)
  (if (atom x)
      nil
    (cons (case (cadar x)
            (n `(,(caar x) natp :rule-classes :type-prescription))
            (i `(,(caar x) integerp :rule-classes :type-prescription))
            (p `(,(caar x) posp :rule-classes :type-prescription))
            (b `(,(caar x) t))
            (t `(,(caar x) true-listp :rule-classes :type-prescription)))
          (defsymbolic-define-returns1 (cdr x)))))

(defun defsymbolic-define-returns (x)
  (let ((rets (defsymbolic-define-returns1 x)))
    (if (atom (cdr rets))
        (car rets)
      (cons 'mv rets))))

(defun defsymbolic-spec-term (formal-evals retspec)
  (if (eql (len retspec) 3)
      (sublis formal-evals (third retspec))
    (if (and (eql (len retspec) 5)
             (eq (fourth retspec) :cond))
        `(implies ,(sublis formal-evals (fifth retspec))
                  ,(sublis formal-evals (third retspec)))
      (er hard? 'defsymbolic "bad return-spec: ~x0~%" retspec))))

(defun defsymbolic-return-specs (x formal-evals)
  (if (atom x)
      nil
    (append (b* ((spec-term (defsymbolic-spec-term formal-evals (car x))))
              (case (cadar x)
                ((n i p) (and (third (car x))
                              `((equal ,(caar x)
                                       ,spec-term))))
                (b `((equal (bfr-eval ,(caar x) env)
                            ,spec-term)))
                (u `((equal (bfr-list->u ,(caar x) env)
                            ,spec-term)))
                (s `((equal (bfr-list->s ,(caar x) env)
                            ,spec-term)))
                (ru `((equal (bfr-list->u (acl2::rev ,(caar x)) env)
                             ,spec-term)))
                (rs `((equal (bfr-list->s (acl2::rev ,(caar x)) env)
                             ,spec-term)))))
            (defsymbolic-return-specs (cdr x) formal-evals))))

(defun defsymbolic-not-depends-on (x)
  (if (atom x)
      nil
    (append (case (cadar x)
              (b `((not (pbfr-depends-on varname param ,(caar x)))))
              ((u s ru rs) `((not (pbfr-list-depends-on varname param ,(caar x))))))
            (defsymbolic-not-depends-on (cdr x)))))

(defun induct/expand-fn (fn id world)
  (declare (xargs :mode :program))
  (and (not (acl2::access acl2::clause-id id :pool-lst))
       (let ((formals (formals fn world)))
         (append (and (recursivep fn t world)
                      `(:induct (,fn . ,formals)))
                 `(:expand ((,fn . ,formals))
                   :in-theory (disable (:d ,fn)))))))

(defmacro induct/expand (fn)
  `(induct/expand-fn ',fn id world))

(defun defsymbolic-fn (name args)
  (declare (xargs :mode :program))
  (b* (((mv kwd-alist other-kws other-args)
        (extract-some-keywords
         '(:spec :returns :correct-hints :depends-hints :correct-hyp :abstract :guard-hints)
         args nil))
       ((unless (eql (len other-args) 2))
        (er hard? 'defsymbolic-fn "Need formals and body in addition to keyword args"))
       (formals (car other-args))
       (body (cadr other-args))
       (abstractp (std::getarg :abstract nil kwd-alist))
       (returns (cdr (assoc :returns kwd-alist)))
       ((unless (consp returns))
        (er hard? 'defsymbolic-fn "Need a returns list"))
       (returns (if (eq (car returns) 'mv)
                    (cdr returns)
                  (list returns)))
       (- (defsymbolic-check-formals formals))
       (- (defsymbolic-check-returns returns))
       ((when (intersectp-eq (strip-cars formals)
                             (strip-cars returns)))
        (er hard? 'defsymbolic-fn "Formals and returns overlap"))
       (return-binder (if (consp (cdr returns))
                          `(mv . ,(strip-cars returns))
                        (caar returns)))
       (formal-vars (strip-cars formals))
       (exec-name (if abstractp
                      (intern-in-package-of-symbol
                       (concatenate 'string (symbol-name name) "-EXEC")
                       name)
                    name)))
    `(progn
       (define ,exec-name ,(defsymbolic-define-formals formals)
         ,@other-kws
         :verify-guards nil
         :returns ,(defsymbolic-define-returns returns)
         ,(subst exec-name name body)
         ///
         (verify-guards ,exec-name
           :hints ,(cdr (assoc :guard-hints kwd-alist)))
         (defthm ,(intern-in-package-of-symbol
                   (concatenate 'string (symbol-name exec-name) "-CORRECT")
                   exec-name)
           (b* ((,return-binder (,exec-name . ,formal-vars)))
             ,(let ((concl `(and . ,(defsymbolic-return-specs returns
                                      (defsymbolic-formals-pair-with-evals formals))))
                    (correct-hyp (cdr (assoc :correct-hyp kwd-alist))))
                (if correct-hyp
                    `(implies ,correct-hyp ,concl)
                  concl)))
           :hints ((induct/expand ,exec-name)
                   . ,(subst exec-name name (cdr (assoc :correct-hints kwd-alist)))))

         (defthm ,(intern-in-package-of-symbol
                   (concatenate 'string (symbol-name exec-name) "-DEPS")
                   exec-name)
           (b* ((,return-binder (,exec-name . ,formal-vars)))
             (implies (and . ,(defsymbolic-not-depends-on formals))
                      (and . ,(defsymbolic-not-depends-on returns))))
           :hints ((induct/expand ,exec-name)
                   . ,(subst exec-name name (cdr (assoc :depends-hints kwd-alist))))))
       ,@(and abstractp
              `((encapsulate
                  (((,name . ,(acl2::replicate (len formals) '*))
                    => ,(if (consp (cdr returns))
                            `(mv . ,(acl2::replicate (len returns) '*))
                          '*)
                    :formals ,formal-vars
                    :guard (and ,@(let ((guard (cadr (assoc-keyword :guard other-kws))))
                                    (and guard `(,guard)))
                                . ,(defsymbolic-guards formals))))

                  (local (defun ,name ,formal-vars
                           (,exec-name . ,formal-vars)))

                  (defthm ,(intern-in-package-of-symbol
                            (concatenate 'string (symbol-name name) "-CORRECT")
                            name)
                    (b* ((,return-binder (,name . ,formal-vars)))
                      ,(let ((concl `(and . ,(defsymbolic-return-specs returns
                                               (defsymbolic-formals-pair-with-evals formals))))
                             (correct-hyp (cdr (assoc :correct-hyp kwd-alist))))
                         (if correct-hyp
                             `(implies ,correct-hyp ,concl)
                           concl))))
                  (defthm ,(intern-in-package-of-symbol
                            (concatenate 'string (symbol-name name) "-DEPS")
                            name)
                    (b* ((,return-binder (,name . ,formal-vars)))
                      (implies (and . ,(defsymbolic-not-depends-on formals))
                               (and . ,(defsymbolic-not-depends-on returns))))))
                (defattach ,name ,exec-name)))

       (table defsymbolic-forms ',name ',args))))

(defmacro defsymbolic (name &rest args)
  (defsymbolic-fn name args))



(local (in-theory (e/d* (acl2::ihsext-redefs
                         acl2::ihsext-inductions
                         pbfr-list-depends-on))))

(local (in-theory (disable (force) acl2::logext**
                           acl2::logext-identity
                           truncate)))


(defmacro car/cdr (x)
  `(let* ((a ,x))
     (mbe :logic (mv (car a) (cdr a))
          :exec (if (atom a) (mv nil nil) (mv (car a) (cdr a))))))

(defsymbolic bfr-ite-bvv-fn-aux ((c b) ;; name c, type b (boolean)
                                 (v1 u) ;; unsigned
                                 (v0 u))
  :returns (vv u (if c v1 v0))
  :abstract nil
  :measure (+ (acl2-count v1) (acl2-count v0))
  (b* (((when (and (atom v1) (atom v0)))
        nil)
       ((mv v11 v1r) (car/cdr v1))
       ((mv v01 v0r) (car/cdr v0))
       (tail (bfr-ite-bvv-fn-aux c v1r v0r))
       (head (bfr-ite c v11 v01)))
    (bfr-ucons head tail)))

(defsymbolic bfr-ite-bvv-fn ((c b) ;; name c, type b (boolean)
                             (v1 u) ;; unsigned
                             (v0 u))
  :returns (vv u (if c v1 v0))
  :abstract nil
  (if c
      (if (eq c t)
          (llist-fix v1)
        (bfr-ite-bvv-fn-aux c v1 v0))
    (llist-fix v0)))

(defthm bfr-ite-bvv-fn-of-const-tests
  (and (equal (bfr-ite-bvv-fn t v1 v0) (list-fix v1))
       (equal (bfr-ite-bvv-fn nil v1 v0) (list-fix v0)))
  :hints(("Goal" :in-theory (enable bfr-ite-bvv-fn))))

(defthm bfr-ite-bvv-fn-aux-elim
  (implies (and (not (equal c t))
                c)
           (equal (bfr-ite-bvv-fn-aux c v1 v0)
                  (bfr-ite-bvv-fn c v1 v0)))
  :hints(("Goal" :in-theory (enable bfr-ite-bvv-fn))))

(defmacro bfr-ite-bvv (c v1 v0)
  `(mbe :logic (bfr-ite-bvv-fn ,c ,v1 ,v0)
        :exec (let ((bfr-ite-bvv-test ,c))
                (if bfr-ite-bvv-test
                    (if (eq bfr-ite-bvv-test t)
                        (llist-fix ,v1)
                      (bfr-ite-bvv-fn-aux bfr-ite-bvv-test ,v1 ,v0))
                  (llist-fix ,v0)))))

(add-macro-alias bfr-ite-bvv bfr-ite-bvv-fn)

(defsymbolic bfr-ite-bss-fn-aux ((c  b) ;; name c, type b (boolean)
                                 (v1 s) ;; signed
                                 (v0 s))
  :returns (vv s (if c v1 v0))
  :abstract nil
  :measure (+ (acl2-count v1) (acl2-count v0))
  (b* (((mv head1 tail1 end1) (first/rest/end v1))
       ((mv head0 tail0 end0) (first/rest/end v0))
       ((when (and end1 end0))
        (bfr-sterm (bfr-ite-fn c head1 head0)))
       (rst (bfr-ite-bss-fn-aux c tail1 tail0))
       (head (bfr-ite c head1 head0)))
    (bfr-scons head rst)))

(defsymbolic bfr-ite-bss-fn ((c  b) ;; name c, type b (boolean)
                             (v1 s) ;; signed
                             (v0 s))
  :returns (vv s (if c v1 v0))
  :abstract nil
  (if c
      (if (eq c t)
          (llist-fix v1)
        (bfr-ite-bss-fn-aux c v1 v0))
    (llist-fix v0)))

(defthm bfr-ite-bss-fn-of-const-tests
  (and (equal (bfr-ite-bss-fn t v1 v0) (list-fix v1))
       (equal (bfr-ite-bss-fn nil v1 v0) (list-fix v0)))
  :hints(("Goal" :in-theory (enable bfr-ite-bss-fn))))

(defthm bfr-ite-bss-fn-aux-elim
  (implies (and (not (equal c t))
                c)
           (equal (bfr-ite-bss-fn-aux c v1 v0)
                  (bfr-ite-bss-fn c v1 v0)))
  :hints(("Goal" :in-theory (enable bfr-ite-bss-fn))))

(defmacro bfr-ite-bss (c v1 v0)
  `(mbe :logic (bfr-ite-bss-fn ,c ,v1 ,v0)
        :exec (let ((bfr-ite-bss-test ,c))
                (if bfr-ite-bss-test
                    (if (eq bfr-ite-bss-test t)
                        (llist-fix ,v1)
                      (bfr-ite-bss-fn-aux bfr-ite-bss-test ,v1 ,v0))
                  (llist-fix ,v0)))))

(add-macro-alias bfr-ite-bss bfr-ite-bss-fn)

(defsymbolic bfr-loghead-ns ((n n)  ;; name n, type n (natp)
                             (x s)) ;; name x, type s (signed bvec)
  :returns (xx s (loghead n x))     ;; return name, type (signed bvec), spec
  (b* (((when (zp n))
        (bfr-sterm nil))
       ((mv head tail ?end) (first/rest/end x)))
    (bfr-scons head (bfr-loghead-ns (1- n) tail))))

(defsymbolic bfr-logext-ns ((n p)  ;; name n, type p (posp)
                            (x s)) ;; name x, type s (signed bvec)
  :returns (xx s (acl2::logext n x))     ;; return name, type (signed bvec), spec
  :measure (acl2::pos-fix n)
  (b* ((n (lposfix n))
       ((mv head tail ?end) (first/rest/end x))
       ((when end) (llist-fix x))
       ((when (eql n 1)) (bfr-sterm head)))
    (bfr-scons head (bfr-logext-ns (1- n) tail)))
  :correct-hints (("goal" :induct (bfr-logext-ns n x))
                  (And stable-under-simplificationp
                       '(:expand ((:free (x) (logext (pos-fix n) x)))))))

(defsymbolic bfr-logtail-ns ((place n)
                             (x s))
  :returns (xx s (logtail place x))
  (if (or (zp place) (s-endp x))
      (llist-fix x)
    (bfr-logtail-ns (1- place) (scdr x))))

(defsymbolic bfr-+-ss ((c b)
                       (v1 s)
                       (v2 s))
  :returns (sum s (+ (acl2::bool->bit c) v1 v2))
  :measure (+ (len v1) (len v2))
  (b* (((mv head1 tail1 end1) (first/rest/end v1))
       ((mv head2 tail2 end2) (first/rest/end v2))
       (axorb (bfr-xor head1 head2))
       (s     (bfr-xor c axorb))
       ((when (and end1 end2))
        (let ((last (bfr-ite axorb (bfr-not c) head1)))
          (bfr-scons s (bfr-sterm last))))
       ;; BOZO think about this.  Using axorb here seems like a good idea since
       ;; we're already computing it anyway in order to compute S.  However, we
       ;; could instead do something like:
       ;;    (c   (bfr-or  (bfr-and c head1)
       ;;                  (bfr-and c head2)
       ;;                  (bfr-and head1 head2)))
       ;; This wouldn't share the same structure but might result in a simpler
       ;; carry in being delivered to the rest of the sum, which might be a win.
       ;; It's hard to guess whether this would be better or worse, so for now
       ;; we'll just leave it alone...
       (c (bfr-or (bfr-and c axorb)
                  (bfr-and head1 head2)))
       (rst (bfr-+-ss c tail1 tail2)))
    (bfr-scons s rst))
  :correct-hints ('(:in-theory (enable logcons))))



(defsymbolic bfr-lognot-s ((x s))
  :returns (nx s (lognot x))
  (b* (((mv head tail end) (first/rest/end x))
       ((when end)
        (bfr-sterm (bfr-not head))))
    (bfr-scons (bfr-not head)
               (bfr-lognot-s tail))))

(defsymbolic bfr-unary-minus-s ((x s))
  :returns (ms s (- x))
  (bfr-+-ss t nil (bfr-lognot-s x))
  :correct-hints ('(:in-theory (enable lognot))))

(defsymbolic bfr-logxor-ss ((a s)
                            (b s))
  :returns (xab s (logxor a b))
  :measure (+ (len a) (len b))
  (b* (((mv af ar aend) (first/rest/end a))
       ((mv bf br bend) (first/rest/end b))
       (c (bfr-xor af bf))
       ((when (and aend bend))
        (bfr-sterm c))
       (r (bfr-logxor-ss ar br)))
    (bfr-scons c r)))

(defsymbolic bfr-sign-s ((x s))
  :returns (sign b (< x 0))
  (b* (((mv first rest endp) (first/rest/end x))
       ((when endp)
        first))
    (bfr-sign-s rest)))

(defsymbolic bfr-integer-length-s1 ((offset p)
                                    (x s))
  :measure (len x)
  :returns (mv (not-done b (and (not (equal x 0))
                                (not (equal x -1))))
               (ilen s (if (or (equal x 0)
                               (equal x -1))
                           0
                         (+ -1 offset (integer-length x)))))
  :prepwork ((local (defthm bfr-eval-of-car-when-bfr-list->s
                      (implies (and (equal (bfr-list->s x env) c)
                                    (syntaxp (quotep c)))
                               (equal (bfr-eval (car x) env)
                                      (equal 1 (logcar c)))))))
  (b* (((mv first rest end) (first/rest/end x))
       (offset (lposfix offset))
       ((when end)
        (mv nil nil))
       ((mv changed res)
        (bfr-integer-length-s1 (1+ offset) rest))
       ((when (eq changed t))
        (mv t res))
       (change (bfr-xor first (car rest))))
    (mv (bfr-or changed change)
        (bfr-ite-bss changed
                     res
                     (bfr-ite-bss change (i2v offset) nil))))
  :correct-hints ((bfr-reasoning)))

(defsymbolic bfr-integer-length-s ((x s))
  :returns (ilen s (integer-length x))
  (b* (((mv ?changed res) (bfr-integer-length-s1 1 x)))
    res))

(define integer-length-bound-s (x)
  :returns (bound posp :rule-classes :type-prescription)
  (max (len x) 1)
  ///
  (local
   (defthm s-endp-true-by-len
     (implies (<= (len x) 1)
              (s-endp x))
     :hints(("Goal" :in-theory (enable s-endp)))))
  (defthm integer-length-bound-s-correct
    (< (integer-length (bfr-list->s x env))
       (integer-length-bound-s x))
    :rule-classes :linear))

(defsymbolic bfr-abs-s ((x s))
  :returns (xabs s (abs x))
  :prepwork ((local (in-theory (enable loghead-of-integer-length-nonneg)))
             (local (defthm loghead-of-abs-2
                      (implies (and (< (integer-length x) (nfix n))
                                    (integerp x)
                                    (< x 0))
                               (equal (loghead n (- x))
                                      (- x)))
                      :hints(("Goal" :induct (loghead n x)
                              :expand ((loghead n (- x)))
                              :in-theory (disable acl2::loghead**))
                             (and stable-under-simplificationp
                                  '(:in-theory (e/d (logcons
                                                     bitops::minus-to-lognot)
                                                    (acl2::loghead**))))))))
  (let ((sign (bfr-sign-s x)))
    (bfr-loghead-ns (integer-length-bound-s x)
                    (bfr-+-ss sign nil
                              (bfr-logxor-ss (bfr-sterm sign) x))))

  :correct-hints ('(:use (integer-length-bound-s-correct
                          bfr-sign-s-correct)
                    :in-theory (e/d* (lognot)
                                     (integer-length-bound-s-correct
                                      bfr-sign-s-correct
                                      acl2::ihsext-redefs)))))

(defsymbolic bfr-=-uu ((a u) (b u))
  :returns (a=b b (equal a b))
  :measure (+ (len a) (len b))
  (b* (((when (and (atom a) (atom b)))
        t)
       ((mv head1 tail1) (car/cdr a))
       ((mv head2 tail2) (car/cdr b))
       (first-eq (bfr-iff head1 head2)))
    (bfr-and first-eq
             (bfr-=-uu tail1 tail2))))

(defsymbolic bfr-=-ss ((a s) (b s))
  :returns (a=b b (equal a b))
  :measure (+ (len a) (len b))
  (b* (((mv head1 tail1 end1) (first/rest/end a))
       ((mv head2 tail2 end2) (first/rest/end b))
       ((when (and end1 end2))
        (bfr-iff head1 head2))
       (first-eq (bfr-iff head1 head2)))
    (bfr-and first-eq
             (bfr-=-ss tail1 tail2))))

(local (add-bfr-pat (bfr-sign-s . &)))
(local (add-bfr-pat (bfr-=-ss . &)))


(defsymbolic bfr-*-ss ((v1 s) (v2 s))
  :measure (+ (len v1) (len v2))
  :returns (prod s (* v1 v2))
  (b* (((mv dig1 rest end1) (first/rest/end v1))
       ((when end1)
        (bfr-ite-bss dig1
                     (bfr-unary-minus-s v2)
                     nil))
       (rest (bfr-*-ss rest v2)))
    (bfr-+-ss nil
              (bfr-ite-bss dig1 v2 nil)
              (bfr-scons nil rest)))
  :correct-hints ('(:in-theory (enable logcons))))

(define syntactically-true-p (x)
  :returns (true-p booleanp)
  (eq x t)
  ///
  (std::defretd syntactically-true-p-implies
    (implies (syntactically-true-p x)
             (equal (bfr-eval x env) t)))

  (std::defretd syntactically-true-p-rewrite
    (implies (and (acl2::rewriting-negative-literal `(syntactically-true-p ,x))
                  (bind-free '((env . env)) (env)))
             (iff (syntactically-true-p x)
                  (and (equal (bfr-eval x env) t)
                       (hide (syntactically-true-p x)))))
    :hints (("goal" :expand ((:free (x) (hide x)))))))


(defsymbolic bfr-<-=-ss ((a s) (b s))
  :measure (+ (len a) (len b))
  :returns (mv (a<b b (< a b))
               (a=b b (= a b)))
  :correct-hints ('(:in-theory (e/d (syntactically-true-p-rewrite))
                    :do-not-induct t))
  (b* (((mv head1 tail1 end1) (first/rest/end a))
       ((mv head2 tail2 end2) (first/rest/end b))
       ((when (and end1 end2))
        (b* ((less (bfr-and head1 (bfr-not head2))))
          (mv less
              (if (syntactically-true-p less) nil (bfr-iff head1 head2)))))
       ((mv rst< rst=)
        (bfr-<-=-ss tail1 tail2))
       (less (bfr-or rst< (bfr-and rst= head2 (bfr-not head1)))))
    (mv less
        (if (syntactically-true-p less) nil (bfr-and rst= (bfr-iff head1 head2))))))

(define syntactically-zero-p ((x true-listp))
  :returns (result booleanp)
  (b* (((mv head tail end) (first/rest/end x)))
    (and (eq head nil)
         (or end
             (syntactically-zero-p tail))))
  ///
  (std::defretd syntactically-zero-p-implies
    (implies (syntactically-zero-p x)
             (equal (bfr-list->s x env) 0))))

(defsymbolic bfr-<-ss ((a s) (b s))
  :returns (a<b b (< a b))
  :correct-hints ('(:in-theory (enable syntactically-zero-p-implies)))
  (b* (((when (syntactically-zero-p b))
        ;; Special case for (< x 0) -- very common
        (bfr-sign-s a))
       ((mv head1 tail1 end1) (first/rest/end a))
       ((mv head2 tail2 end2) (first/rest/end b))
       ((when (and end1 end2))
        (bfr-and head1 (bfr-not head2)))
       ((mv rst< rst=) (bfr-<-=-ss tail1 tail2)))
    (bfr-or rst< (bfr-and rst= head2 (bfr-not head1)))))

(defsymbolic bfr-logapp-nss ((n n)
                             (a s)
                             (b s))
  :returns (a-app-b s (logapp n a b))
  (b* (((when (zp n))
        (llist-fix b))
       ((mv first rest &) (first/rest/end a)))
    (bfr-scons first (bfr-logapp-nss (1- n) rest b))))

(defsymbolic bfr-logapp-nus-aux ((n n)
                             (a u)
                             (b s))
  :returns (a-app-b s (logapp n a b))
  (b* (((when (zp n))
        (llist-fix b))
       ((mv first rest) (car/cdr a)))
    (bfr-scons first (bfr-logapp-nus-aux (1- n) rest b))))

(defsymbolic bfr-loghead-nu ((n n)
                             (a u))
  :returns (head s (loghead n a))
  (b* (((when (or (zp n) (atom a))) '(nil))
       ((mv first rest) (car/cdr a)))
    (bfr-scons first (bfr-loghead-nu (1- n) rest))))

(defsymbolic bfr-logapp-nus ((n n)
                             (a u)
                             (b s))
  :returns (a-app-b s (logapp n a b))
  :correct-hints ('(:in-theory (enable syntactically-zero-p-implies)))
  (b* (((when (syntactically-zero-p b))
        (bfr-loghead-nu n a)))
    (bfr-logapp-nus-aux n a b)))

(defsymbolic bfr-ash-ss ((place p)
                    (n s)
                    (shamt s))
  :returns (sh s (ash n (+ -1 place (* place shamt))))
  :measure (len shamt)
  :prepwork ((local
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
                              (equal (+ (* a n) (* b n) m) (+ (* (+ a b) n) m)))
                     (equal (+ n (- (* 2 n)) m)
                            (+ (- n) m))))))
  (b* (((mv shdig shrst shend) (first/rest/end shamt))
       (place (lposfix place))
       ((when shend)
        (bfr-ite-bss shdig
                     (bfr-logtail-ns 1 n)
                     (bfr-logapp-nss (1- place) nil n)))
       (rst (bfr-ash-ss (* 2 place) n shrst)))
    (bfr-ite-bss shdig
                 rst
                 (bfr-logtail-ns place rst)))
  :correct-hints ('(:expand ((:free (b) (logcons b (bfr-list->s (scdr shamt) env)))
                             (bfr-ash-ss place n shamt))
                    :in-theory (disable acl2::logtail-identity
                                        unsigned-byte-p))))

(defsymbolic bfr-logbitp-n2v ((place p)
                              (digit u)
                              (n s))
  :returns (bit b (logbitp (* place digit) n))
  :measure (len digit)
  (b* (((mv first & end) (first/rest/end n))
       (place (lposfix place))
       ((when (or (atom digit) end))
        first))
    (bfr-ite (car digit)
             (bfr-logbitp-n2v (* 2 place) (cdr digit) (bfr-logtail-ns place n))
             (bfr-logbitp-n2v (* 2 place) (cdr digit) n)))
  :correct-hints ((and stable-under-simplificationp
                       '(:in-theory (enable logcons acl2::bool->bit)))))

(defsymbolic bfr-logand-ss ((a s)
                            (b s))
  :returns (a&b s (logand a b))
  :measure (+ (len a) (len b))
  (b* (((mv af ar aend) (first/rest/end a))
       ((when aend)
        (bfr-ite-bss af b '(nil)))
       ((mv bf br bend) (first/rest/end b))
       ((when bend)
        (bfr-ite-bss bf a '(nil)))
       (c (bfr-and af bf))
       ;; ((when (and aend bend))
       ;;  (bfr-sterm c))
       (r (bfr-logand-ss ar br)))
    (bfr-scons c r)))

(defsymbolic bfr-logior-ss ((a s)
                            (b s))
  :returns (avb s (logior a b))
  :measure (+ (len a) (len b))
  (b* (((mv af ar aend) (first/rest/end a))
       ((when aend)
        (bfr-ite-bss af '(t) b))
       ((mv bf br bend) (first/rest/end b))
       ((when bend)
        (bfr-ite-bss bf '(t) a))
       (c (bfr-or af bf))
       ;; ((when (and aend bend))
       ;;  (bfr-sterm c))
       (r (bfr-logior-ss ar br)))
    (bfr-scons c r)))

(defsymbolic bfr-logeqv-ss ((a s)
                            (b s))
  :returns (a=b s (logeqv a b))
  :measure (+ (len a) (len b))
  (b* (((mv af ar aend) (first/rest/end a))
       ((mv bf br bend) (first/rest/end b))
       (c (bfr-iff af bf))
       ((when (and aend bend))
        (bfr-sterm c))
       (r (bfr-logeqv-ss ar br)))
    (bfr-scons c r)))

(defsymbolic bfr-floor-ss-aux ((a s)
                             (b s)
                             (not-b s))
  :returns (mv (f s (floor a b))
               (m s (mod a b)))
  :correct-hyp (< 0 (bfr-list->s b env))
  :guard (equal not-b (bfr-lognot-s b))
  :prepwork ((local (include-book "ihs/quotient-remainder-lemmas" :dir :system)) ;

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
                     :hints(("Goal" :in-theory (disable floor acl2::floor-bounded-by-/
                                                        acl2::<-*-/-left)
                             :use ((:instance acl2::floor-bounded-by-/
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
                     :hints(("Goal" :in-theory (disable floor acl2::floor-bounded-by-/
                                                        acl2::<-*-/-left)
                             :use ((:instance acl2::floor-bounded-by-/
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
                                                    (floor acl2::floor-bounded-by-/
                                                           acl2::<-*-/-left))
                             :use ((:instance acl2::floor-bounded-by-/
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
                     :hints(("Goal" :in-theory (disable floor acl2::floor-bounded-by-/
                                                        acl2::<-*-/-left)
                             :use ((:instance acl2::floor-bounded-by-/
                                    (x a) (y b))
                                   (:theorem (implies (and (integerp a)
                                                           (integerp b)
                                                           (< 0 b)
                                                           (< a (* 2 b)))
                                                      (< (* a (/ b)) 2)))))
                            (and stable-under-simplificationp
                                 '(:in-theory (disable floor)))))))


                (defthm floor-rewrite-+-bit-*-2-a
                  (implies (and (integerp a) (integerp b)
                                (< 0 b))
                           (equal (floor (logcons c a) b)
                                  (if (<= b (logcons c (mod a b)))
                                      (logcons 1 (floor a b))
                                    (logcons 0 (floor a b)))))
                  :hints(("Goal" :in-theory (e/d* (logcons bfix)
                                                  (floor
                                                   (:rules-of-class
                                                    :generalize :here))
                                                  ((:generalize acl2::mod-bounded-by-modulus))))))


                (defthm mod-rewrite-+-bit-*-2-a
                  (implies (and (integerp a) (integerp b)
                                (< 0 b))
                           (equal (mod (logcons c a) b)
                                  (if (<= b (logcons c (mod a b)))
                                      (+ (- b)
                                         (logcons c (mod a b)))
                                    (logcons c (mod a b)))))
                  :hints (("goal" :in-theory (e/d* (logcons bfix mod)
                                                  (floor
                                                   (:rules-of-class
                                                    :generalize :here))
                                                  ((:generalize acl2::mod-bounded-by-modulus))))))


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
                                  (equal n 1))))

                (defthm loghead-of-bfr-integer-length-bound
                  (implies (and (bind-free '((env . env)))
                                (<= 0 (ifix a))
                                (<= (ifix a) (bfr-list->s b env)))
                           (equal (loghead (integer-length-bound-s b) a)
                                  (ifix a)))
                  :hints (("goal" :use ((:instance loghead-of-integer-length-nonneg
                                         (n (integer-length-bound-s b))
                                         (x a))
                                        (:instance integer-length-lte-by-compare-nonneg
                                         (a a) (b (bfr-list->s b env))))
                           :in-theory (disable loghead-of-integer-length-nonneg))))

                (defthm logcons-onto-mod-b-bound
                  (implies (and (integerp b)
                                (integerp a)
                                (< 0 b))
                           (< (logcons bit (mod a b)) (* 2 b)))
                  :hints(("Goal" :in-theory (enable logcons)))
                  :rule-classes :linear)))

             (local (add-bfr-pat (bfr-<-ss . &)))

             (local (defthm +-1-logcons-0
                      (equal (+ 1 (logcons 0 a))
                             (logcons 1 a))
                      :hints(("Goal" :in-theory (enable logcons)))))

             (local (defthm boolean-listp-of-scdr
                      (implies (boolean-listp x)
                               (boolean-listp (scdr x)))
                      :hints(("Goal" :in-theory (enable scdr)))))

             (local (defthm bfr-list->s-of-quoted-boolean-list
                      (implies (and (syntaxp (quotep x))
                                    (boolean-listp x))
                               (equal (bfr-list->s x env)
                                      (v2i x)))
                      :hints(("Goal" :in-theory (enable bfr-list->s v2i)
                              :expand ((boolean-listp x))
                              :induct (bfr-list->s x env)))))

             (local (in-theory (e/d* ()
                                     (floor
                                      mod
                                      acl2::loghead**
                                      acl2::loghead-identity
                                      bfr-eval-list
                                      bfr-list->s
                                      equal-of-booleans-rewrite
                                      acl2::mod-type
                                      acl2::floor-type-3 acl2::floor-type-1
                                      bitops::logcons-posp-1
                                      bitops::logcons-posp-2
                                      bitops::logcons-negp
                                      acl2::rationalp-mod (:t floor) (:t mod))))))
  (b* (((mv first rest endp) (first/rest/end a))
       (not-b (mbe :logic (bfr-lognot-s b) :exec not-b)))
    (if endp
        (mv (bfr-sterm first) ;; (floor  0  b) = 0
            (bfr-ite-bss
             first
             (bfr-+-ss nil '(t) b) ;; (mod -1 b) = b-1 with b > 0
             '(nil))) ;; (mod  0  b) = 0
      (b* (((mv rf rm)
            (bfr-floor-ss-aux rest b not-b))
           (rm (bfr-scons first rm))
           (less (bfr-<-ss rm b)))
        (mv (bfr-scons (bfr-not less) rf)
            (bfr-ite-bss
             less rm
             (bfr-loghead-ns (integer-length-bound-s b)
                             (bfr-+-ss t not-b rm)))))))
  :correct-hints ('(:expand ((:free (not-b) (bfr-floor-ss-aux a b not-b))
                             (:free (not-b) (bfr-floor-ss-aux nil b not-b))
                             (:free (a b) (bfr-list->s (bfr-scons a b) env))
                             (bfr-list->s a env)))
                  (bfr-reasoning)
                  (and stable-under-simplificationp
                       '(:in-theory (enable lognot)))
                  (and stable-under-simplificationp
                       '(:error t))))

(defsymbolic bfr-mod-ss-aux ((a s)
                             (b s)
                             (not-b s))
  :returns (m s (mod a b))
  :correct-hyp (< 0 (bfr-list->s b env))
  :guard (equal not-b (bfr-lognot-s b))
  :guard-hints ('(:expand ((:free (not-b) (bfr-floor-ss-aux a b not-b)))))
  (mbe :logic (non-exec (mv-nth 1 (bfr-floor-ss-aux a b not-b)))
       :exec (b* (((mv first rest endp) (first/rest/end a))
                  (not-b (mbe :logic (bfr-lognot-s b) :exec not-b))
                  ((when endp)
                   (bfr-ite-bss
                    first
                    (bfr-+-ss nil '(t) b) ;; (mod -1 b) = b-1 with b > 0
                    '(nil)))               ;; (mod  0  b) = 0
                  (rm (bfr-mod-ss-aux rest b not-b))
                  (rm (bfr-scons first rm))
                  (less (bfr-<-ss rm b)))
               (bfr-ite-bss
                less rm
                (bfr-loghead-ns (integer-length-bound-s b)
                                (bfr-+-ss t not-b rm))))))

(defsymbolic bfr-sign-abs-not-s ((x s))
  :returns (mv (s b (< x 0))
               (a s (abs x))
               (n s (lognot (abs x))))
  (let ((abs (bfr-abs-s x)))
    (mv (bfr-sign-s x)
        abs
        (bfr-lognot-s abs))))

(defsymbolic bfr-floor-ss ((a s)
                           (b s))
  :returns (f s (floor a b))
  :prepwork ((local (in-theory (enable bfr-sign-abs-not-s))))
  (bfr-ite-bss (bfr-=-ss b nil)
               nil
               (b* (((mv bsign babs bneg) (bfr-sign-abs-not-s b))
                    (anorm (bfr-ite-bss bsign (bfr-unary-minus-s a) a))
                    ((mv f &) (bfr-floor-ss-aux anorm babs bneg)))
                 f))
  :correct-hints ((bfr-reasoning)))

(defsymbolic bfr-mod-ss ((a s)
                         (b s))
  :returns (m s (mod a b))
  :prepwork ((local (in-theory (enable bfr-sign-abs-not-s))))
  (bfr-ite-bss (bfr-=-ss b nil)
               (llist-fix a)
               (bfr-logext-ns (integer-length-bound-s b)
                              (b* (((mv bsign babs bneg) (bfr-sign-abs-not-s b))
                                   (anorm (bfr-ite-bss bsign (bfr-unary-minus-s a) a))
                                   (m (bfr-mod-ss-aux anorm babs bneg)))
                                (bfr-ite-bss bsign (bfr-unary-minus-s m) m))))
  :correct-hints ((bfr-reasoning)))

(defsymbolic bfr-truncate-ss ((a s)
                              (b s))
  :returns (tr s (truncate a b))
  :prepwork ((local (in-theory (enable bfr-sign-abs-not-s))))
  (bfr-ite-bss (bfr-=-ss b nil)
               nil
               (b* (((mv bsign babs bneg) (bfr-sign-abs-not-s b))
                    ((mv asign aabs &) (bfr-sign-abs-not-s a))
                    ((mv f &) (bfr-floor-ss-aux aabs babs bneg)))
                 (bfr-ite-bss (bfr-xor bsign asign)
                              (bfr-unary-minus-s f) f)))
  :correct-hints ((bfr-reasoning)))

(defsymbolic bfr-rem-ss ((a s)
                         (b s))
  :returns (r s (rem a b))
  :prepwork ((local (in-theory (disable integer-length-of-between-abs-and-minus-abs
                                        logext-of-integer-length-bound
                                        rem
                                        acl2::integer-length**)))
             (local (in-theory (enable bfr-sign-abs-not-s))))
  (bfr-ite-bss (bfr-=-ss b nil)
               (llist-fix a)
               (b* (((mv & babs bneg) (bfr-sign-abs-not-s b))
                    ((mv asign aabs &) (bfr-sign-abs-not-s a))
                    (m (bfr-mod-ss-aux aabs babs bneg)))
                 (bfr-logext-ns (integer-length-bound-s b)
                                (bfr-ite-bss asign (bfr-unary-minus-s m) m))))
  :correct-hints ((bfr-reasoning)
                  (and stable-under-simplificationp
                       '(:use ((:instance integer-length-of-rem
                                (a (bfr-list->s a env))
                                (b (bfr-list->s b env))))
                         :in-theory (e/d (logext-of-integer-length-bound)
                                         (integer-length-of-rem
                                          integer-length-of-mod))))))


(define s-take ((n natp) (x true-listp))
  (b* (((when (zp n)) (bfr-sterm nil))
       ((mv first rest end) (first/rest/end x))
       ((when (and end (eq first nil)))
        '(nil)))
    (bfr-ucons first (s-take (1- n) rest)))
  ///
  (defthm deps-of-s-take
    (implies (not (pbfr-list-depends-on k p x))
             (not (pbfr-list-depends-on k p (s-take n x)))))


  (defthm s-take-correct
    (equal (bfr-list->u (s-take n x) env)
           (loghead n (bfr-list->s x env)))
    :hints (("goal" :induct (s-take n x)
             :in-theory (enable* acl2::ihsext-recursive-redefs)))))


(defsymbolic bfr-logapp-russ ((n ru)
                              (x s)
                              (y s))
  :returns (app s (logapp n x y))
  :prepwork ((local (in-theory (enable logcons acl2::rev)))
             (local (defthm logapp-loghead-logtail
                      (implies (equal z (logapp w1 (logtail w x) y))
                               (equal (logapp w (loghead w x) z)
                                      (logapp (+ (nfix w) (nfix w1)) x y)))
                      :hints(("Goal" :in-theory (enable* bitops::ihsext-recursive-redefs
                                                         bitops::ihsext-inductions)))))
             (local (defthm loghead-of-len-of-bfr-list
                      (implies (<= (len lst) (nfix n))
                               (equal (loghead n (bfr-list->u lst env))
                                      (bfr-list->u lst env)))
                      :hints(("Goal" :in-theory (enable* bitops::ihsext-recursive-redefs
                                                         bitops::ihsext-inductions
                                                         (:i nthcdr))
                              :induct (nthcdr n lst)
                              :expand ((bfr-list->u lst env)
                                       (:free (x) (loghead n x)))))))
             (local (defthm logapp-1-is-plus-ash
                      (equal (logapp n x 1)
                             (+ (ash 1 (nfix n)) (loghead n x)))
                      :hints(("Goal" :in-theory (enable logapp bitops::ash-is-expt-*-x)))))
             (local (defthm bfr-list->u-of-append
                      (Equal (bfr-list->u (append a b) env)
                             (logapp (len a)
                                     (bfr-list->u a env)
                                     (bfr-list->u b env)))
                      :hints(("Goal" :in-theory (enable* bitops::ihsext-recursive-redefs
                                                         bitops::ihsext-inductions
                                                         append))))))
  (if (atom n)
      (llist-fix y)
    (if (b* (((mv x1 & xend) (first/rest/end x))
             ((mv y1 & yend) (first/rest/end y)))
          (and xend
               yend
               (equal x1 y1)))
        (llist-fix x)
      (bfr-ite-bss
       (car n)
       (b* ((w (ash 1 (len (cdr n)))))
         (bfr-logapp-nus w (s-take w x)
                         (bfr-logapp-russ (cdr n) (bfr-logtail-ns w x) y)))
       (bfr-logapp-russ (cdr n) x y)))))


;; (defsymbolic bfr-logapp-uss ((w n)
;;                              (n u)
;;                              (x s)
;;                              (y s))
;;   :returns (app s (logapp (* n w) x y))
;;   :prepwork ((local (in-theory (enable logcons)))
;;              (local (defthm logapp-loghead-logtail
;;                       (implies (equal z (logapp w1 (logtail w x) y))
;;                                (equal (logapp w (loghead w x) z)
;;                                       (logapp (+ (nfix w) (nfix w1)) x y)))
;;                       :hints(("Goal" :in-theory (enable* bitops::ihsext-recursive-redefs
;;                                                          bitops::ihsext-inductions))))))
;;   (if (atom n)
;;       (llist-fix y)
;;     (if (b* (((mv x1 & xend) (first/rest/end x))
;;              ((mv y1 & yend) (first/rest/end y)))
;;           (and xend
;;                yend
;;                (equal x1 y1)))
;;         (llist-fix x)
;;       (bfr-ite-bss
;;        (car n)
;;        (bfr-logapp-nus (lnfix w) (s-take w x)
;;                        (bfr-logapp-uss
;;                         (ash (lnfix w) 1) (cdr n) (bfr-logtail-ns w x)
;;                         y))
;;        (bfr-logapp-uss (ash (lnfix w) 1) (cdr n) x y)))))



(local
 (defsection expt-lemmas
   (defthm expt-of-0
     (equal (expt base 0) 1)
     :hints(("Goal" :in-theory (enable expt))))


   (defthm expt-of-*-2
     (implies (natp exp)
              (equal (expt base (* 2 exp))
                     (* (expt base exp)
                        (expt base exp))))
     :hints(("Goal" :in-theory (enable expt))))))


;; (local
;;  (defthm expt-base-decompose
;;    (implies (and (posp exp) (integerp base))
;;             (equal (expt base exp)
;;                    (* (if (eql (logcar exp) 1) base 1)
;;                       (expt (* base base) (logcdr exp)))))
;;    :hints (("goal" :use ((:instance acl2::logcar-logcdr-elim
;;                           (i exp))
;;                          (:instance acl2::exponents-add-for-nonneg-exponents
;;                           (r base) (i (* 2 (logcdr exp))) (j (logcar exp)))
;;                          (:instance acl2::exponents-add-for-nonneg-exponents
;;                           (r base) (i (logcdr exp)) (j (logcdr exp))))
;;             :in-theory (e/d (logcons) (acl2::logcar-logcdr-elim
;;                                        bitops::logcons-destruct
;;                                        acl2::exponents-add-for-nonneg-exponents))))))

;; (define expt-impl ((base integerp)
;;                    (exp natp))
;;   :measure (nfix exp)
;;   (if (mbe :logic (or (zp exp) (zp (logcdr exp)))
;;            :exec (zp (logcdr exp)))
;;       (if (eql (logcar exp) 1) base 1)
;;     (let ((rest (expt-impl (* base base) (logcdr exp))))
;;       (if (eql (logcar exp) 1)
;;           (* base rest)
;;         rest)))
;;   ///

;;   (defthm expt-impl-correct
;;     (implies (and (integerp base) (natp exp))
;;              (equal (expt-impl base exp)
;;                     (expt base exp)))))


(define all-nil ((x))
  (if (atom x)
      t
    (and (eq (car x) nil)
         (all-nil (cdr x))))
  ///
  (defthm all-nil-when-atom
    (implies (atom x) (all-nil x)))

  (defthmd zero-when-all-nil
    (implies (all-nil x)
             (equal (bfr-list->u x env) 0))))

;; Note: We don't have a symbolic counterpart for expt yet, but this is used in
;; SV and it could easily be used in GL as well so we wrote it here.
(defsymbolic bfr-expt-su ((b s)
                          (e u))
  :measure (len e)
  :returns (b^e s (expt b e))
  (b* (((when (all-nil e)) '(t nil))
       ((when (all-nil (cdr e)))
        (bfr-ite-bss (car e) b '(t nil)))
       (rest (bfr-expt-su (bfr-*-ss b b) (cdr e))))
    (bfr-ite-bss (car e)
                 (bfr-*-ss b rest)
                 rest))
  :correct-hints ('(:in-theory (enable zero-when-all-nil
                                       logcons))))

