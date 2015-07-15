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
(include-book "symbolic-arithmetic")
(include-book "eval-g-base")

(local (include-book "eval-g-base-help"))
(local (include-book "hyp-fix"))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))



;; (local (defthm v2i-of-append
;;          (implies (consp y)
;;                   (equal (v2i (append x y))
;;                          (logapp (len x) (v2n x) (v2i y))))
;;          :hints (("goal" :induct (append x y)
;;                   :in-theory (enable* acl2::ihsext-recursive-redefs
;;                                       v2i v2n)))))

;; (defthm bfr-eval-list-of-append
;;   (equal (bfr-eval-list (append a b) env)
;;          (append (bfr-eval-list a env)
;;                  (bfr-eval-list b env))))

;; (defthm len-of-bfr-eval-list
;;   (equal (len (bfr-eval-list x env))
;;          (len x)))

;; (defthm len-of-s-take
;;   (equal (len (s-take w x))
;;          (nfix w)))

;; (defun append-us (x y)
;;   (declare (xargs :guard (true-listp x)))
;;   (append x (if (consp y) y '(nil))))

;; (defthm append-us-correct
;;   (equal (bfr-list->s (append-us x y) env)
;;          (logapp (len x) (bfr-list->u x env)
;;                  (bfr-list->s y env)))
;;   :hints(("Goal" :in-theory (enable append-us))))




(defun g-logapp-of-numbers (n x y)
  (declare (xargs :guard (and (general-numberp n)
                              (general-numberp x)
                              (general-numberp y))))
  (b* (((mv nrn nrd nin nid)
        (general-number-components n))
       ((mv xrn xrd xin xid)
        (general-number-components x))
       ((mv yrn yrd yin yid)
        (general-number-components y))
       ((mv nintp nintp-known)
        (if (equal nrd '(t))
            (mv (bfr-or (bfr-=-ss nin nil)
                        (bfr-=-uu nid nil)) t)
          (mv nil nil)))
       ((mv xintp xintp-known)
        (if (equal xrd '(t))
            (mv (bfr-or (bfr-=-ss xin nil)
                      (bfr-=-uu xid nil)) t)
          (mv nil nil)))
       ((mv yintp yintp-known)
        (if (equal yrd '(t))
            (mv (bfr-or (bfr-=-ss yin nil)
                      (bfr-=-uu yid nil)) t)
          (mv nil nil)))
       ((unless (and nintp-known xintp-known yintp-known))
        (g-apply 'logapp (gl-list n x y)))
       ;; nfix
       (nbits (bfr-ite-bvv-fn (bfr-and (bfr-not (bfr-sign-s nrn)) nintp)
                              nrn nil))
       ;; ifix
       (xbits (bfr-ite-bss-fn xintp xrn nil))
       (ybits (bfr-ite-bss-fn yintp yrn nil))
       (resbits (bfr-logapp-uss 1 nbits xbits ybits)))
    (mk-g-number (list-fix resbits))))


(in-theory (disable (g-logapp-of-numbers)))

(defthm deps-of-g-logapp-of-numbers
  (implies (and (not (gobj-depends-on k p n))
                (not (gobj-depends-on k p x))
                (not (gobj-depends-on k p y))
                (general-numberp n)
                (general-numberp x)
                (general-numberp y))
           (not (gobj-depends-on k p (g-logapp-of-numbers n x y)))))

(local (defthm logapp-zp-n
         (implies (zp n)
                  (equal (logapp n x y)
                         (ifix y)))
         :hints(("Goal" :in-theory (enable acl2::logapp**)))
         :rule-classes ((:rewrite :backchain-limit-lst 0))))
(local (defthm logapp-zip-x
         (implies (and (syntaxp (not (equal x ''0)))
                       (zip x))
                  (equal (logapp n x y)
                         (logapp n 0 y)))
         :hints(("Goal" :in-theory (enable acl2::logapp**)))
         :rule-classes ((:rewrite :backchain-limit-lst 0))))
(local (defthm logapp-zip-y
         (implies (and (syntaxp (not (equal y ''0)))
                       (zip y))
                  (equal (logapp n x y)
                         (logapp n x 0)))
         :hints(("Goal" :in-theory (enable acl2::logapp**)))
         :rule-classes ((:rewrite :backchain-limit-lst 0))))

(local (defthm bfr-list->s-when-gte-0
         (implies (<= 0 (bfr-list->s x env))
                  (equal (bfr-list->s x env)
                         (bfr-list->u x env)))
         :hints(("Goal" :in-theory (enable scdr s-endp)))))

(defthm g-logapp-of-numbers-correct
  (implies (and (general-numberp n)
                (general-numberp x)
                (general-numberp y))
           (equal (eval-g-base (g-logapp-of-numbers n x y) env)
                  (logapp (eval-g-base n env)
                          (eval-g-base x env)
                          (eval-g-base y env))))
  :hints (("goal" :in-theory (e/d* ((:ruleset general-object-possibilities)
                                    )
                                   (general-numberp
                                    bfr-list->s
                                    general-number-components))
           :do-not-induct t)))

(in-theory (disable g-logapp-of-numbers))

(def-g-fn logapp
  `(let ((size acl2::size))
     (b* (((when (and (general-concretep size)
                      (general-concretep i)
                      (general-concretep j)))
           (gret (ec-call (logapp (general-concrete-obj size)
                                  (general-concrete-obj i)
                                  (general-concrete-obj j)))))
          ((unless (or (atom size)
                       (not (member-eq (tag size) '(:g-ite :g-var :g-apply)))))
           (if (and (eq (tag size) :g-ite)
                    (not (zp clk)))
               (let* ((test (g-ite->test size))
                      (then (g-ite->then size))
                      (else (g-ite->else size)))
                 (g-if (gret test)
                       (,gfn then i j . ,params)
                       (,gfn else i j . ,params)))
             (gret (g-apply 'logapp (gl-list size i j)))))
          ((unless (or (atom i)
                       (not (member-eq (tag i) '(:g-ite :g-var :g-apply)))))
           (if (and (eq (tag i) :g-ite)
                    (not (zp clk)))
               (let* ((test (g-ite->test i))
                      (then (g-ite->then i))
                      (else (g-ite->else i)))
                 (g-if (gret test)
                       (,gfn size then j . ,params)
                       (,gfn size else j . ,params)))
             (gret (g-apply 'logapp (gl-list size i j)))))
          ((unless (or (atom j)
                       (not (member-eq (tag j) '(:g-ite :g-var :g-apply)))))
           (if (and (eq (tag j) :g-ite)
                    (not (zp clk)))
               (let* ((test (g-ite->test j))
                      (then (g-ite->then j))
                      (else (g-ite->else j)))
                 (g-if (gret test)
                       (,gfn size i then . ,params)
                       (,gfn size i else . ,params)))
             (gret (g-apply 'logapp (gl-list size i j)))))
          (size (if (general-numberp size) size 0))
          (i (if (general-numberp i) i 0))
          (j (if (general-numberp j) j 0)))
       (gret (g-logapp-of-numbers size i j)))))

(verify-g-guards logapp
                 :hints `(("Goal" :in-theory (disable* ,gfn
                                                       general-concretep-def))))

(def-gobj-dependency-thm logapp
  :hints `(("goal" :induct ,gcall
            :expand (,gcall)
            :in-theory (disable (:d ,gfn)))))

(local (defthm logapp-non-acl2-numbers
         (and (implies (not (acl2-numberp size))
                       (equal (logapp size i j) (ifix j)))
              (implies (not (acl2-numberp i))
                       (equal (logapp size i j) (logapp size 0 j)))
              (implies (not (acl2-numberp j))
                       (equal (logapp size i j) (logapp size i 0))))))



(def-g-correct-thm logapp eval-g-base
  :hints `(("Goal" :in-theory (e/d* (general-concretep-atom
                                     (:ruleset general-object-possibilities)
                                     not-general-numberp-not-acl2-numberp
                                     eval-g-base-non-cons)
                                    ((:definition ,gfn)
                                     general-concretep-def
                                     logapp
                                     member-equal
                                     eval-g-base-alt-def
                                     components-to-number-alt-def
                                     hons-assoc-equal
                                     set::double-containment
                                     equal-of-booleans-rewrite
                                     bfr-eval-list
                                     acl2::cancel_times-equal-correct
                                     acl2::cancel_plus-equal-correct
                                     default-car default-cdr
                                     (:rules-of-class :type-prescription
                                      :here))
                                    ((:t logapp)))
            :induct (,gfn acl2::size i j . ,params)
            :do-not-induct t
            :expand ((,gfn acl2::size i j . ,params)))
           (and stable-under-simplificationp
                (intersectp-equal '((not (equal (tag$inline acl2::size) ':g-ite))
                                    (not (general-concretep acl2::size)))
                                  clause)
                '(:expand ((eval-g-base acl2::size env))))
           (and stable-under-simplificationp
                (intersectp-equal '((not (equal (tag$inline i) ':g-ite))
                                    (not (general-concretep i)))
                                  clause)
                '(:expand ((eval-g-base i env))))
           (and stable-under-simplificationp
                (intersectp-equal '((not (equal (tag$inline j) ':g-ite))
                                    (not (general-concretep j)))
                                  clause)
                '(:expand ((eval-g-base j env))))))






(define g-int-set-sign-of-number (negp y hyp)
  :guard (general-numberp y)
  (b* (((mv yrn yrd yin yid)
        (general-number-components y))
       ((mv yintp yintp-known)
        (if (equal yrd '(t))
            (mv (bfr-or (bfr-=-ss yin nil)
                        (bfr-=-uu yid nil)) t)
          (mv nil nil)))
       ((mv negbfr unknown & hyp) (gtests negp hyp))
       ((unless (and yintp-known
                     (not unknown)))
        (gret (g-apply 'int-set-sign (gl-list negp y))))
       (ybits (bfr-ite-bss-fn yintp yrn nil))
       (ylen (bfr-integer-length-s ybits))
       (resbits (bfr-logapp-uss 1 ylen ybits (bfr-ite-bss-fn negbfr '(t) '(nil)))))
    (gret (mk-g-number (list-fix resbits))))
  ///
  (def-hyp-congruence g-int-set-sign-of-number)

  (defthm deps-of-g-int-set-sign-of-number
    (implies (and (not (gobj-depends-on k p negp))
                  (not (gobj-depends-on k p y))
                  (general-numberp y))
             (not (gobj-depends-on k p (mv-nth 0 (g-int-set-sign-of-number negp y hyp))))))


  (local (defthm bfr-integer-length-s-correct-v2n
           (equal (bfr-list->u (bfr-integer-length-s x) env)
                  (integer-length (bfr-list->s x env)))
           :hints(("Goal" :use ((:instance bfr-integer-length-s-correct))
                   :in-theory (disable bfr-integer-length-s-correct)))))

  (local (defthm integer-length-zip
           (implies (zip x)
                    (equal (integer-length x) 0))))


  (defthm g-int-set-sign-of-number-correct
    (implies (and (bfr-hyp-eval hyp (car env))
                  (general-numberp y))
             (equal (eval-g-base (mv-nth 0 (g-int-set-sign-of-number negp y hyp)) env)
                    (int-set-sign (eval-g-base negp env)
                                  (eval-g-base y env))))
    :hints (("goal" :in-theory (e/d* ((:ruleset general-object-possibilities)
                                      int-set-sign)
                                     (general-numberp
                                      bfr-list->s-when-gte-0
                                      general-number-components))
             :do-not-induct t))))


(def-g-binary-op int-set-sign
  (b* ((i-num (if (general-numberp i) i 0)))
    (g-int-set-sign-of-number negp i-num hyp)))

(verify-g-guards
 int-set-sign
 :hints `(("Goal" :in-theory
           (disable* ,gfn
                     (:rules-of-class :type-prescription :here)))))

(def-gobj-dependency-thm int-set-sign
  :hints `(("goal" :induct ,gcall
            :expand (,gcall)
            :in-theory (disable (:d ,gfn)))))

(local (defthm int-set-sign-non-acl2-number
         (implies (not (acl2-numberp i))
                  (equal (int-set-sign negp i)
                         (int-set-sign negp 0)))
         :hints(("Goal" :in-theory (enable int-set-sign)))))

(def-g-correct-thm int-set-sign eval-g-base
   :hints `(("Goal" :in-theory (e/d* (general-concretep-atom
                                      (:ruleset general-object-possibilities))
                                     ((:definition ,gfn)
                                      general-numberp-eval-to-numberp
                                      general-boolean-value-correct
                                      bool-cond-itep-eval
                                      boolean-listp
                                      eval-g-base-alt-def
                                      components-to-number-alt-def
                                      member-equal
                                      general-number-components-ev
                                      general-concretep-def
                                      general-concretep-def
                                      rationalp-implies-acl2-numberp
                                      hons-assoc-equal
                                      default-car default-cdr
                                      mv-nth-cons-meta
                                      possibilities-for-x-5
                                      possibilities-for-x-3
                                      general-boolean-value-cases
                                      (:rules-of-class :type-prescription :here))
                                     ((:type-prescription bfr-eval)
                                      eval-g-base-non-cons))
             :induct (,gfn negp i . ,params)
             :expand ((,gfn negp i . ,params)))
           (and stable-under-simplificationp
                (intersectp-equal '((not (equal (tag$inline negp) ':g-ite))
                                    (not (general-concretep negp)))
                                  clause)
                '(:expand ((eval-g-base negp env))))
           (and stable-under-simplificationp
                (intersectp-equal '((not (equal (tag$inline i) ':g-ite))
                                    (not (general-concretep i)))
                                  clause)
                '(:expand ((eval-g-base i env))))))



(defund g-ifix-of-number (i)
  (declare (xargs :guard (general-numberp i)))
  (b* (((mv irn ird iin iid)
        (general-number-components i))
       ((mv iintp iintp-known)
        (if (equal ird '(t))
            (mv (bfr-or (bfr-=-ss iin nil)
                        (bfr-=-uu iid nil)) t)
          (mv nil nil)))
       ((unless iintp-known) (mv t nil)) ;; error
       ;; ifix
       (ibits (bfr-ite-bss-fn iintp irn nil)))
    (mv nil (mk-g-number (list-fix ibits)))))

(defthm deps-of-g-ifix-of-number
  (implies (and (not (gobj-depends-on k p i))
                (general-numberp i))
           (not (gobj-depends-on k p (mv-nth 1 (g-ifix-of-number i)))))
  :hints(("Goal" :in-theory (enable g-ifix-of-number))))

(defthm g-ifix-of-number-correct
  (b* (((mv erp res) (g-ifix-of-number i)))
    (implies (and (not erp)
                  (general-numberp i))
             (equal (eval-g-base res env)
                    (ifix (eval-g-base i env)))))
  :hints(("Goal" :in-theory (enable g-ifix-of-number))))



(def-g-fn maybe-integer
  `(b* (((when (and (general-concretep i)
                    (general-concretep x)
                    (general-concretep intp)))
         (gret
          (g-concrete-quote
           (ec-call (maybe-integer (general-concrete-obj i)
                                   (general-concrete-obj x)
                                   (general-concrete-obj intp))))))
        ;; ((unless (or (atom intp)
        ;;              (not (member-eq (tag intp) '(:g-ite :g-var :g-apply)))))
        ;;  (if (and (eq (tag intp) :g-ite)
        ;;           (not (zp clk)))
        ;;      (let* ((test (g-ite->test intp))
        ;;             (then (g-ite->then intp))
        ;;             (else (g-ite->else intp)))
        ;;        (g-if test
        ;;              (,gfn i x then . ,params)
        ;;              (,gfn i x else . ,params)))
        ;;    (g-apply 'maybe-integer (gl-list i x intp))))
        ((when (and (consp i)
                    (member (tag i) '(:g-ite :g-var :g-apply))))
         (if (and (eq (tag i) :g-ite)
                  (not (zp clk)))
             (let* ((test (g-ite->test i))
                    (then (g-ite->then i))
                    (else (g-ite->else i)))
               (g-if (gret test)
                     (,gfn then x intp . ,params)
                     (,gfn else x intp . ,params)))
           (gret (g-apply 'maybe-integer (gl-list i x intp)))))
        ;; ((when (and (consp x) (eq (tag x) :g-ite)))
        ;;  (if (not (zp clk))
        ;;      (let* ((test (g-ite->test x))
        ;;             (then (g-ite->then x))
        ;;             (else (g-ite->else x)))
        ;;        (g-if test
        ;;              (,gfn i then intp . ,params)
        ;;              (,gfn i else intp . ,params)))
        ;;    (g-apply 'maybe-integer (gl-list i x intp))))
        (i (if (general-numberp i) i 0))
        ((mv undef ifix) (g-ifix-of-number i))
        ((when undef)
         (gret (g-apply 'maybe-integer (gl-list i x intp)))))
     (g-if (gret intp)
           (gret ifix)
           (gret (g-apply 'maybe-integer (gl-list i x intp))))))



(verify-g-guards
 maybe-integer
 :hints `(("Goal" :in-theory
           (disable* ,gfn
                     (:rules-of-class :type-prescription :here)))))

(def-gobj-dependency-thm maybe-integer
  :hints `(("goal" :induct ,gcall
            :expand (,gcall)
            :in-theory (disable (:d ,gfn)
                                (g-ifix-of-number)))))


(def-g-correct-thm maybe-integer eval-g-base
   :hints `(("Goal" :in-theory (e/d* (general-concretep-atom
                                      maybe-integer
                                      (:ruleset general-object-possibilities))
                                     ((:definition ,gfn)
                                      (g-ifix-of-number)
                                      general-numberp-eval-to-numberp
                                      general-boolean-value-correct
                                      bool-cond-itep-eval
                                      boolean-listp
                                      eval-g-base-alt-def
                                      components-to-number-alt-def
                                      member-equal
                                      general-number-components-ev
                                      general-concretep-def
                                      general-concretep-def
                                      rationalp-implies-acl2-numberp
                                      hons-assoc-equal
                                      default-car default-cdr
                                      mv-nth-cons-meta
                                      possibilities-for-x-5
                                      possibilities-for-x-3
                                      general-boolean-value-cases
                                      (:rules-of-class :type-prescription :here))
                                     ((:type-prescription bfr-eval)
                                      eval-g-base-non-cons))
             :induct (,gfn i x intp . ,params)
             :expand ((,gfn i x intp . ,params)))
           (and stable-under-simplificationp
                (intersectp-equal '((not (equal (tag$inline i) ':g-ite))
                                    (not (general-concretep i))
                                    (general-numberp i))
                                  clause)
                '(:expand ((eval-g-base i env))))
           (and stable-under-simplificationp
                (intersectp-equal '((not (equal (tag$inline intp) ':g-ite))
                                    (not (general-concretep intp)))
                                  clause)
                '(:expand ((eval-g-base intp env))))
           (and stable-under-simplificationp
                (intersectp-equal '((not (equal (tag$inline x) ':g-ite))
                                    (not (general-concretep x)))
                                  clause)
                '(:expand ((eval-g-base x env))))))

