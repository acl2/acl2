; GL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2008-2013 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Sol Swords <sswords@centtech.com>

; cert_param: (non-acl2r)

(in-package "GL")
(include-book "bvec-ite")
(include-book "tools/mv-nth" :dir :system)
(include-book "ihs/logops-definitions" :dir :system)
(local (include-book "clause-processors/find-subterms" :dir :system))
(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))


;;---------------- Misc function definitions and lemmas -------------------

(defthm equal-complexes-rw
  (implies (and (acl2-numberp x)
                (rationalp a)
                (rationalp b))
           (equal (equal (complex a b) x)
                  (and (equal a (realpart x))
                       (equal b (imagpart x)))))
  :hints (("goal" :use ((:instance realpart-imagpart-elim)))))

(defun binary-- (x y)
  (declare (xargs :guard (and (acl2-numberp x)
                              (acl2-numberp y))))
  (- x y))

(defund int-set-sign (negp i)
  (declare (xargs :guard (integerp i)))
  (let ((i (lifix i)))
    (acl2::logapp (integer-length i) i (if negp -1 0))))

(defthm sign-of-int-set-sign
  (iff (< (int-set-sign negp i) 0)
       negp)
  :hints(("Goal" :in-theory (e/d* (int-set-sign)
                                  (acl2::logapp
                                   acl2::ifix-under-int-equiv)))))

(defthm int-set-sign-integerp
  (integerp (int-set-sign negp i))
  :rule-classes :type-prescription)

(defund non-int-fix (x)
  (declare (xargs :guard t))
  (and (not (integerp x)) x))

(defthm non-int-fix-when-non-integer
  (implies (not (integerp x))
           (equal (non-int-fix x) x))
  :hints(("Goal" :in-theory (enable non-int-fix)))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defund maybe-integer (i x intp)
  (declare (xargs :guard (integerp i)))
  (if intp
      (ifix i)
    (non-int-fix x)))

(defthm maybe-integer-t
  (equal (maybe-integer i x t)
         (ifix i))
  :hints(("Goal" :in-theory (enable maybe-integer))))

(defthm maybe-integer-nil
  (equal (maybe-integer i x nil)
         (non-int-fix x))
  :hints(("Goal" :in-theory (enable maybe-integer))))

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
             (member (cadar x) '(n i p b u s)))
        (defsymbolic-check-formals (cdr x))
      (er hard? 'defsymbolic-check-formals
          "Bad formal: ~x0" (car x)))))

(defun defsymbolic-check-returns (x)
  (if (atom x)
      t
    (if (and (consp (car x))
             (>= (len (car x)) 2)
             (symbolp (caar x))
             (member (cadar x) '(n i p b u s))
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
                  (s `(bfr-list->s ,(caar x) env))))
          (defsymbolic-formals-pair-with-evals (cdr x)))))

(defun defsymbolic-define-formals (x)
  (if (atom x)
      nil
    (cons (case (cadar x)
            (n `(,(caar x) natp))
            (i `(,(caar x) integerp))
            (p `(,(caar x) posp))
            (t (caar x)))
          (defsymbolic-define-formals (cdr x)))))

(defun defsymbolic-guards (x)
  (if (atom x)
      nil
    (append (case (cadar x)
              (n `((natp ,(caar x))))
              (i `((integerp ,(caar x))))
              (p `((posp ,(caar x)))))
            (defsymbolic-guards (cdr x)))))

(defun defsymbolic-define-returns1 (x)
  (if (atom x)
      nil
    (cons (case (cadar x)
            (n `(,(caar x) natp :rule-classes :type-prescription))
            (i `(,(caar x) integerp :rule-classes :type-prescription))
            (p `(,(caar x) posp :rule-classes :type-prescription))
            (b (caar x))
            (t (caar x)))
          (defsymbolic-define-returns1 (cdr x)))))

(defun defsymbolic-define-returns (x)
  (let ((rets (defsymbolic-define-returns1 x)))
    (if (atom (cdr rets))
        (car rets)
      (cons 'mv rets))))

(defun defsymbolic-return-specs (x formal-evals)
  (if (atom x)
      nil
    (append (case (cadar x)
              ((n i p) (and (third (car x))
                            `((equal ,(caar x)
                                     ,(sublis formal-evals (third (car x)))))))
              (b `((equal (bfr-eval ,(caar x) env)
                          ,(sublis formal-evals (third (car x))))))
              (u `((equal (bfr-list->u ,(caar x) env)
                          ,(sublis formal-evals (third (car x))))))
              (s `((equal (bfr-list->s ,(caar x) env)
                          ,(sublis formal-evals (third (car x)))))))
            (defsymbolic-return-specs (cdr x) formal-evals))))

(defun defsymbolic-not-depends-on (x)
  (if (atom x)
      nil
    (append (case (cadar x)
              (b `((not (pbfr-depends-on varname param ,(caar x)))))
              ((u s) `((not (pbfr-list-depends-on varname param ,(caar x))))))
            (defsymbolic-not-depends-on (cdr x)))))

(defun induct/expand-fn (fn id world)
  (declare (xargs :mode :program))
  (and (not (acl2::access acl2::clause-id id :pool-lst))
       (let ((formals (formals fn world)))
         (append (and (recursivep fn world)
                      `(:induct (,fn . ,formals)))
                 `(:expand ((,fn . ,formals))
                   :in-theory (disable (:d ,fn)))))))

(defmacro induct/expand (fn)
  `(induct/expand-fn ',fn id world))

(defun defsymbolic-fn (name args)
  (declare (xargs :mode :program))
  (b* (((mv kwd-alist other-kws other-args)
        (extract-some-keywords
         '(:spec :returns :correct-hints :depends-hints :correct-hyp :abstract) args nil))
       ((unless (eql (len other-args) 2))
        (er hard? 'defsymbolic-fn "Need formals and body in addition to keyword args"))
       (formals (car other-args))
       (body (cadr other-args))
       (abstractp (std::getarg :abstract t kwd-alist))
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
         :returns ,(defsymbolic-define-returns returns)
         ,(subst exec-name name body)
         ///
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
                (defattach ,name ,exec-name))))))
                  
(defmacro defsymbolic (name &rest args)
  (defsymbolic-fn name args))



(local (in-theory (e/d* (acl2::ihsext-redefs
                         acl2::ihsext-inductions
                         pbfr-list-depends-on))))
                        
(defsymbolic bfr-loghead-ns ((n n)  ;; name n, type n (natp)
                             (x s)) ;; name x, type s (signed bvec)
  :returns (xx s (loghead n x))     ;; return name, type (signed bvec), spec
  (b* (((when (zp n)) (bfr-sterm nil))
       ((mv head tail ?end) (first/rest/end x)))
    (bfr-scons head (bfr-loghead-ns (1- n) tail))))

(defsymbolic bfr-logext-ns ((n p)  ;; name n, type p (posp)
                            (x s)) ;; name x, type s (signed bvec)
  :returns (xx s (acl2::logext n x))     ;; return name, type (signed bvec), spec
  :measure (acl2::pos-fix n)
  (b* ((n (mbe :logic (acl2::pos-fix n) :exec n))
       ((mv head tail ?end) (first/rest/end x))
       ((when end) x)
       ((when (eql n 1)) (bfr-sterm head)))
    (bfr-scons head (bfr-logext-ns (1- n) tail))))

(defsymbolic bfr-logtail-ns ((place n)
                             (x s))
  :returns (xx s (logtail place x))
  (if (or (zp place) (s-endp x))
      x
    (bfr-logtail-ns (1- place) (scdr x))))

(defsymbolic bfr-+-ss ((c b)
                       (v1 s)
                       (v2 s))
  :returns (sum s (+ (acl2::bool->bit c) v1 v2))
  :measure (+ (len v1) (len v2))
  (b* (((mv head1 tail1 end1) (first/rest/end v1))
       ((mv head2 tail2 end2) (first/rest/end v2))
       (axorb (bfr-xor head1 head2))
       (s (bfr-xor c axorb)))
    (if (and end1 end2)
        (let ((last (bfr-ite axorb (bfr-not c) head1)))
          (bfr-scons s (bfr-sterm last)))
      (let* ((c (bfr-or (bfr-and c axorb)
                        (bfr-and head1 head2)))
             (rst (bfr-+-ss c tail1 tail2)))
        (bfr-scons s rst))))
  :correct-hints ('(:in-theory (enable logcons))))

(defsymbolic bfr-lognot-s ((x s))
  :returns (nx s (lognot x))
  (b* (((mv head tail end) (first/rest/end x)))
    (if end
        (bfr-sterm (bfr-not head))
      (bfr-scons (bfr-not head)
                 (bfr-lognot-s tail)))))

(defsymbolic bfr-unary-minus-s ((x s))
  :returns (ms s (- x))
  (bfr-+-ss t nil (bfr-lognot-s x))
  :correct-hints ('(:in-theory (enable lognot))))

(defsymbolic bfr-logxor-ss ((a s)
                            (b s))
  :returns (xab s (logxor a b))
  :measure (+ (len a) (len b))
  (b* (((mv af ar aend) (first/rest/end a))
       ((mv bf br bend) (first/rest/end b)))
    (if (and aend bend)
        (bfr-sterm (bfr-xor af bf))
      (b* ((c (bfr-xor af bf))
           (r (bfr-logxor-ss ar br)))
        (bfr-scons c r)))))

(defsymbolic bfr-sign-s ((x s))
  :returns (sign b (< x 0))
  (b* (((mv first rest endp) (first/rest/end x)))
    (if endp
        first
      (bfr-sign-s rest))))

(defthm not-s-endp-compound-recognizer
  (implies (not (s-endp x))
           (consp x))
  :hints(("Goal" :in-theory (enable s-endp)))
  :rule-classes :compound-recognizer)

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
       (offset (mbe :logic (acl2::pos-fix offset) :exec offset)))
    (if end
        (mv nil nil)
      (mv-let (changed res)
        (bfr-integer-length-s1 (1+ offset) rest)
        (if (eq changed t)
            (mv t res)
          (let ((change (bfr-xor first (car rest))))
            (mv (bfr-or changed change)
                (bfr-ite-bss changed
                             res
                             (bfr-ite-bss change
                                          (i2v offset)
                                          nil))))))))
  :correct-hints ((bfr-reasoning)))

(defsymbolic bfr-integer-length-s ((x s))
  :returns (ilen s (integer-length x))
  (mv-let (ign res)
    (bfr-integer-length-s1 1 x)
    (declare (ignore ign))
    res))

(define bfr-integer-length-bound-s (x)
  :returns (bound posp :rule-classes :type-prescription)
  (max (len x) 1)
  ///
  (defthm bfr-integer-length-bound-s-correct
    (< (integer-length (bfr-list->s x env))
       (bfr-integer-length-bound-s x))
    :rule-classes :linear))

(local (defthmd loghead-of-integer-length-nonneg
         (implies (and (<= (integer-length x) (nfix n))
                       (<= 0 (ifix x)))
                  (equal (loghead n x)
                         (ifix x)))))

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
                                                     acl2::minus-to-lognot)
                                                    (acl2::loghead**))))))))
  (let ((sign (bfr-sign-s x)))
    (bfr-loghead-ns (bfr-integer-length-bound-s x)
                    (bfr-+-ss sign nil
                              (bfr-logxor-ss (bfr-sterm sign) x))))

  :correct-hints ('(:use (bfr-integer-length-bound-s-correct
                          bfr-sign-s-correct)
                    :in-theory (e/d* (lognot)
                                     (bfr-integer-length-bound-s-correct
                                      bfr-sign-s-correct
                                      acl2::ihsext-redefs)))))
                   
(defsymbolic bfr-=-uu ((a u) (b u))
  :returns (a=b b (equal a b))
  :measure (+ (len a) (len b))
  (if (and (atom a) (atom b))
      t
    (b* (((mv head1 tail1) (car/cdr a))
         ((mv head2 tail2) (car/cdr b)))
      (bfr-and (bfr-iff head1 head2)
               (bfr-=-uu tail1 tail2)))))

(defsymbolic bfr-=-ss ((a s) (b s))
  :returns (a=b b (equal a b))
  :measure (+ (len a) (len b))
  (b* (((mv head1 tail1 end1) (first/rest/end a))
       ((mv head2 tail2 end2) (first/rest/end b)))
    (if (and end1 end2)
        (bfr-iff head1 head2)
      (bfr-and (bfr-iff head1 head2)
               (bfr-=-ss tail1 tail2)))))

(defsymbolic bfr-*-ss ((v1 s) (v2 s))
  :measure (+ (len v1) (len v2))
  :returns (prod s (* v1 v2))
  (b* (((mv dig1 rest end1) (first/rest/end v1)))
    (if end1
        (bfr-ite-bss dig1
                     (bfr-unary-minus-s v2)
                     nil)
      (let ((rest (bfr-*-ss rest v2)))
        (bfr-+-ss nil
              (bfr-ite-bss dig1 v2 nil)
              (bfr-scons nil rest)))))
  :correct-hints ('(:in-theory (enable logcons))))

(defsymbolic bfr-<-=-ss ((a s) (b s))
  :measure (+ (len a) (len b))
  :returns (mv (a<b b (< a b))
               (a=b b (= a b)))
  (b* (((mv head1 tail1 end1) (first/rest/end a))
       ((mv head2 tail2 end2) (first/rest/end b)))
    (if (and end1 end2)
        (mv (bfr-and head1 (bfr-not head2))
            (bfr-iff head1 head2))
      (mv-let (rst< rst=)
        (bfr-<-=-ss tail1 tail2)
        (mv (bfr-or rst< (bfr-and rst= head2 (bfr-not head1)))
            (bfr-and rst= (bfr-iff head1 head2)))))))

(defsymbolic bfr-<-ss ((a s) (b s))
  :returns (a<b b (< a b))
  (b* (((mv head1 tail1 end1) (first/rest/end a))
       ((mv head2 tail2 end2) (first/rest/end b)))
    (if (and end1 end2)
        (bfr-and head1 (bfr-not head2))
      (mv-let (rst< rst=)
        (bfr-<-=-ss tail1 tail2)
        (bfr-or rst< (bfr-and rst= head2 (bfr-not head1)))))))

(defsymbolic bfr-logapp-nss ((n n)
                             (a s)
                             (b s))
  :returns (a-app-b s (logapp n a b))
  (if (zp n)
      b
    (b* (((mv first rest &) (first/rest/end a)))
      (bfr-scons first (bfr-logapp-nss (1- n) rest b)))))

(defsymbolic bfr-logapp-nus ((n n)
                        (a u)
                        (b s))
  :returns (a-app-b s (logapp n a b))
  (if (zp n)
      b
    (b* (((mv first rest) (car/cdr a)))
      (bfr-scons first (bfr-logapp-nus (1- n) rest b)))))

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
       (place (mbe :logic (acl2::pos-fix place) :exec place)))
    (if shend
        (bfr-ite-bss shdig
                     (bfr-logtail-ns 1 n)
                     (bfr-logapp-nss (1- place) nil n))
      (let ((rst (bfr-ash-ss (* 2 place) n shrst)))
        (bfr-ite-bss shdig
                     rst
                     (bfr-logtail-ns place rst)))))
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
       (place (mbe :logic (acl2::pos-fix place) :exec place)))
    (if (or (atom digit) end)
        first
      (bfr-ite (car digit)
               (bfr-logbitp-n2v (* 2 place) (cdr digit) (bfr-logtail-ns place n))
               (bfr-logbitp-n2v (* 2 place) (cdr digit) n))))
  :correct-hints ((and stable-under-simplificationp
                       '(:in-theory (enable logcons acl2::bool->bit)))))

(defsymbolic bfr-logand-ss ((a s)
                            (b s))
  :returns (a&b s (logand a b))
  :measure (+ (len a) (len b))
  (b* (((mv af ar aend) (first/rest/end a))
       ((mv bf br bend) (first/rest/end b)))
    (if (and aend bend)
        (bfr-sterm (bfr-and af bf))
      (b* ((c (bfr-and af bf))
           (r (bfr-logand-ss ar br)))
        (bfr-scons c r)))))

(defsymbolic bfr-logior-ss ((a s)
                            (b s))
  :returns (avb s (logior a b))
  :measure (+ (len a) (len b))
  (b* (((mv af ar aend) (first/rest/end a))
       ((mv bf br bend) (first/rest/end b)))
    (if (and aend bend)
        (bfr-sterm (bfr-or af bf))
      (b* ((c (bfr-or af bf))
           (r (bfr-logior-ss ar br)))
        (bfr-scons c r)))))

(defsymbolic bfr-logeqv-ss ((a s)
                            (b s))
  :returns (a=b s (logeqv a b))
  :measure (+ (len a) (len b))
  (b* (((mv af ar aend) (first/rest/end a))
       ((mv bf br bend) (first/rest/end b)))
    (if (and aend bend)
        (bfr-sterm (bfr-not (bfr-xor af bf)))
      (b* ((c (bfr-not (bfr-xor af bf)))
           (r (bfr-logeqv-ss ar br)))
        (bfr-scons c r)))))

(local ;; integer-length lemmas
 (progn
   (include-book "ihs/quotient-remainder-lemmas" :dir :system)

   (defthmd integer-length-lte-by-compare-nonneg
     (implies (and (<= 0 (ifix a))
                   (<= (ifix a) (ifix b)))
              (<= (integer-length a) (integer-length b)))
     :hints (("goal" :induct (logxor a b))))

   (defthmd integer-length-lte-by-compare-neg
     (implies (and (<= (ifix a) 0)
                   (<= (ifix b) (ifix a)))
              (<= (integer-length a) (integer-length b)))
     :hints (("goal" :induct (logxor a b))))

   (add-bfr-pat (bfr-sign-s . &))
   (add-bfr-pat (bfr-=-ss . &))

   (in-theory (disable (force)))))

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
                                                  ((:generalize acl2::mod-bounds))))))


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
                                                  ((:generalize acl2::mod-bounds))))))


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
                           (equal (loghead (bfr-integer-length-bound-s b) a)
                                  (ifix a)))
                  :hints (("goal" :use ((:instance loghead-of-integer-length-nonneg
                                         (n (bfr-integer-length-bound-s b))
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
                                      acl2::logcons-posp-1 acl2::logcons-posp-2
                                      acl2::logcons-negp
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
             (bfr-loghead-ns (bfr-integer-length-bound-s b)
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
  :guard-hints ('(:expand ((:free (not-b) (bfr-floor-ss-aux-exec a b not-b)))))
  (mbe :logic (non-exec (mv-nth 1 (bfr-floor-ss-aux-exec a b not-b)))
       :exec (b* (((mv first rest endp) (first/rest/end a))
                  (not-b (mbe :logic (bfr-lognot-s b) :exec not-b)))
               (if endp
                   (bfr-ite-bss
                    first
                    (bfr-+-ss nil '(t) b) ;; (mod -1 b) = b-1 with b > 0
                    '(nil)) ;; (mod  0  b) = 0
                 (b* ((rm (bfr-mod-ss-aux rest b not-b))
                      (rm (bfr-scons first rm))
                      (less (bfr-<-ss rm b)))
                   (bfr-ite-bss
                    less rm
                    (bfr-loghead-ns (bfr-integer-length-bound-s b)
                                    (bfr-+-ss t not-b rm))))))))

(defun bfr-sign-abs-not-s (x)
  (declare (xargs :guard t))
  (let ((abs (bfr-abs-s x)))
    (mv (bfr-sign-s x)
        abs
        (bfr-lognot-s abs))))

(local ;; integer-length, floor/mod/rem/truncate lemmas
 (progn

   (defthm floor-of-negations
     (equal (floor (- a) (- b))
            (floor a b))
     :hints(("Goal" :in-theory (enable floor))))

   (defthm logext-of-integer-length-bound
     (implies (< (integer-length x) (ifix n))
              (equal (acl2::logext n x)
                     (ifix x))))

   (local (in-theory (disable acl2::mod-minus
                              ACL2::/R-WHEN-ABS-NUMERATOR=1)))

   (defthm mod-of-negatives
     (implies (and (integerp a) (integerp b)
                   (not (equal 0 b)))
              (equal (mod (- a) (- b))
                     (- (mod a b))))
     :hints(("Goal" :in-theory (enable mod))))

   (defthm integer-length-of-mod
     (implies (and (integerp b)
                   (integerp a)
                   (not (equal b 0)))
              (<= (integer-length (mod a b))
                  (integer-length b)))
     :hints (("goal" :in-theory (enable integer-length-lte-by-compare-nonneg
                                        integer-length-lte-by-compare-neg)
              :cases ((< 0 b))))
     :rule-classes :linear)

   (defthm integer-length-of-plus-1
     (implies (integerp x)
              (<= (integer-length (+ 1 x)) (+ 1 (integer-length x)))))

   (defthm integer-length-of-lognot
     (equal (integer-length (lognot x))
            (integer-length x)))

   (defthm integer-length-of-abs
     (implies (integerp x)
              (<= (integer-length (abs x)) (+ 1 (integer-length x))))
     :hints (("goal" :use ((:instance integer-length-of-lognot)
                           (:instance integer-length-of-plus-1
                            (x (+ -1 (- x)))))
              :in-theory (enable lognot))))
   


   (defthm integer-length-of-between-abs-and-minus-abs
     (implies (and (integerp x)
                   (integerp y)
                   (< y (abs x))
                   (< (- (abs x)) y))
              (<= (integer-length y) (integer-length x)))
     :hints (("goal" :use ((:instance integer-length-of-lognot)
                           (:instance integer-length-lte-by-compare-nonneg
                            (a y) (b (abs x)))
                           (:instance integer-length-lte-by-compare-neg
                            (a y) (b (1- (- (abs x)))))
                           (:instance integer-length-lte-by-compare-neg
                            (a y) (b (- (abs x)))))
              :cases ((<= 0 y))
              :do-not-induct t
              :in-theory (e/d (lognot)
                              (integer-length-of-plus-1))))
     :otf-flg t)

   (defthm integer-length-of-rem
     (implies (and (integerp b)
                   (integerp a)
                   (not (equal b 0)))
              (<= (integer-length (rem a b))
                  (integer-length b)))
     :hints (("goal" :in-theory (e/d (integer-length-lte-by-compare-nonneg
                                      integer-length-lte-by-compare-neg)
                                     (acl2::rem-bounds
                                      rem abs))
              :use ((:instance acl2::rem-bounds (x a) (y b)))
              :do-not-induct t
              :cases ((< 0 b))))
     :otf-flg t
     :rule-classes :linear)

   (defthm truncate-is-floor
     (implies (and (integerp a) (integerp b))
              (equal (truncate a b)
                     (if (equal b 0)
                         0
                       (if (acl2::xor (< a 0) (< b 0))
                           (- (floor (abs a) (abs b)))
                         (floor (abs a) (abs b))))))
     :hints(("Goal" :in-theory (enable truncate floor))))

   (defthm rem-is-mod
     (implies (and (integerp a) (integerp b))
              (equal (rem a b)
                     (if (equal b 0)
                         a
                       (if (< a 0)
                           (- (mod (- a) (abs b)))
                         (mod a (abs b))))))
     :hints(("Goal" :in-theory (enable rem mod))))

   (in-theory (disable (force) acl2::logext**
                       acl2::logext-identity
                       bfr-list->s
                       truncate))))

(defsymbolic bfr-floor-ss ((a s)
                           (b s))
  :returns (f s (floor a b))
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
  (bfr-ite-bss (bfr-=-ss b nil)
               a
               (bfr-logext-ns (bfr-integer-length-bound-s b)
                              (b* (((mv bsign babs bneg) (bfr-sign-abs-not-s b))
                                   (anorm (bfr-ite-bss bsign (bfr-unary-minus-s a) a))
                                   (m (bfr-mod-ss-aux anorm babs bneg)))
                                (bfr-ite-bss bsign (bfr-unary-minus-s m) m))))
  :correct-hints ((bfr-reasoning)))

(defsymbolic bfr-truncate-ss ((a s)
                              (b s))
  :returns (tr s (truncate a b))
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
                                        acl2::logbitp-upper-bound
                                        acl2::integer-length**))))
  (bfr-ite-bss (bfr-=-ss b nil)
               a
               (b* (((mv & babs bneg) (bfr-sign-abs-not-s b))
                    ((mv asign aabs &) (bfr-sign-abs-not-s a))
                    (m (bfr-mod-ss-aux aabs babs bneg)))
                 (bfr-logext-ns (bfr-integer-length-bound-s b)
                                (bfr-ite-bss asign (bfr-unary-minus-s m) m))))
  :correct-hints ((bfr-reasoning)
                  (and stable-under-simplificationp
                       '(:use ((:instance integer-length-of-rem
                                (a (bfr-list->s a env))
                                (b (bfr-list->s b env))))
                         :in-theory (e/d (logext-of-integer-length-bound)
                                         (integer-length-of-rem
                                          integer-length-of-mod))))))









