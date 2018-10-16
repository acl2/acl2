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




(defun g-logapp-of-integers (n x y)
  (declare (xargs :guard (and (general-integerp n)
                              (general-integerp x)
                              (general-integerp y))))
  (b* ((nbits (general-integer-bits n))
       (negp (bfr-sign-s nbits)))
    (mk-g-integer
     (bfr-ite-bss-fn negp
                     (general-integer-bits y)
                     (bfr-logapp-russ (acl2::rev nbits)
                                      (general-integer-bits x)
                                      (general-integer-bits y))))))


(in-theory (disable (g-logapp-of-integers)))

(local (defthm depends-on-of-append
         (implies (and (not (pbfr-list-depends-on k p x))
                       (not (pbfr-list-depends-on k p y)))
                  (not (pbfr-list-depends-on k p (append x y))))
         :hints(("Goal" :in-theory (enable pbfr-list-depends-on)))))

(local (defthm depends-on-of-rev
         (implies (not (pbfr-list-depends-on k p x))
                  (not (pbfr-list-depends-on k p (acl2::Rev x))))
         :hints(("Goal" :in-theory (enable acl2::rev pbfr-list-depends-on)))))

(defthm deps-of-g-logapp-of-integers
  (implies (and (not (gobj-depends-on k p n))
                (not (gobj-depends-on k p x))
                (not (gobj-depends-on k p y))
                (general-integerp n)
                (general-integerp x)
                (general-integerp y))
           (not (gobj-depends-on k p (g-logapp-of-integers n x y)))))

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

(defthm g-logapp-of-integers-correct
  (implies (and (general-integerp n)
                (general-integerp x)
                (general-integerp y))
           (equal (eval-g-base (g-logapp-of-integers n x y) env)
                  (logapp (eval-g-base n env)
                          (eval-g-base x env)
                          (eval-g-base y env))))
  :hints (("goal" :in-theory (e/d* ((:ruleset general-object-possibilities)
                                    )
                                   (general-integerp
                                    bfr-list->s))
           :do-not-induct t)))

(in-theory (disable g-logapp-of-integers))

(def-g-fn logapp
  `(let ((size acl2::size))
     (b* (((when (and (general-concretep size)
                      (general-concretep i)
                      (general-concretep j)))
           (gret (ec-call (logapp (general-concrete-obj size)
                                  (general-concrete-obj i)
                                  (general-concrete-obj j)))))
          ((when (mbe :logic (eq (tag size) :g-ite)
                      :exec (and (consp size) (eq (tag size) :g-ite))))
           (let* ((test (g-ite->test size))
                  (then (g-ite->then size))
                  (else (g-ite->else size)))
             (g-if (gret test)
                   (,gfn then i j . ,params)
                   (,gfn else i j . ,params))))
          ((when (mbe :logic (eq (tag i) :g-ite)
                      :exec (and (consp i) (eq (tag i) :g-ite))))
           (if (zp clk)
               (gret (g-apply 'logapp (gl-list size i j)))
             (let* ((test (g-ite->test i))
                    (then (g-ite->then i))
                    (else (g-ite->else i)))
               (g-if (gret test)
                     (,gfn size then j . ,params)
                     (,gfn size else j . ,params)))))
          ((when (mbe :logic (eq (tag j) :g-ite)
                      :exec (and (consp j) (eq (tag j) :g-ite))))
           (if (zp clk)
               (gret (g-apply 'logapp (gl-list size i j)))
             (let* ((test (g-ite->test j))
                    (then (g-ite->then j))
                    (else (g-ite->else j)))
               (g-if (gret test)
                     (,gfn size i then . ,params)
                     (,gfn size i else . ,params)))))
          ((unless (mbe :logic (not (member-eq (tag size) '(:g-var :g-apply)))
                        :exec (or (atom size)
                                  (not (member-eq (tag size) '(:g-var :g-apply))))))
           (gret (g-apply 'logapp (gl-list size i j))))
          ((unless (mbe :logic (not (member-eq (tag i) '(:g-var :g-apply)))
                        :exec (or (atom i)
                                  (not (member-eq (tag i) '(:g-var :g-apply))))))
           (gret (g-apply 'logapp (gl-list size i j))))
          ((unless (mbe :logic (not (member-eq (tag j) '(:g-var :g-apply)))
                        :exec (or (atom j)
                                  (not (member-eq (tag j) '(:g-var :g-apply))))))
           (gret (g-apply 'logapp (gl-list size i j))))
          (size (if (general-integerp size) size 0))
          (i (if (general-integerp i) i 0))
          (j (if (general-integerp j) j 0)))
       (gret (g-logapp-of-integers size i j)))))

(verify-g-guards logapp
                 :hints `(("Goal" :in-theory (disable* ,gfn
                                                       general-concretep-def))))

(def-gobj-dependency-thm logapp
  :hints `(("goal" :induct ,gcall
            :expand (,gcall)
            :in-theory (disable (:d ,gfn)))))

(local (defthm logapp-non-integers
         (and (implies (not (integerp size))
                       (equal (logapp size i j) (ifix j)))
              (implies (not (integerp i))
                       (equal (logapp size i j) (logapp size 0 j)))
              (implies (not (integerp j))
                       (equal (logapp size i j) (logapp size i 0))))))



(def-g-correct-thm logapp eval-g-base
  :hints `(("goal" :in-theory (e/d* (eval-g-base-list))
            :induct ,gcall
            :expand (,gcall)
            :do-not-induct t)))
