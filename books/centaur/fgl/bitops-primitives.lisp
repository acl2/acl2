; FGL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2018 Centaur Technology
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "FGL")

(include-book "primitives")
(include-book "bitops")
(include-book "centaur/sv/svex/4vec" :dir :system)
(local (include-book "primitive-lemmas"))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (std::add-default-post-define-hook :fix))
(local (in-theory (disable w (tau-system))))

(def-formula-checks bitops-formula-checks
  (logapp
   acl2::logmask$inline
   acl2::logtail$inline
   acl2::loghead$inline
   logbitp
   integer-length
   lognot
   acl2::binary-logand
   acl2::binary-logxor
   acl2::binary-logior
   acl2::binary-logeqv
   +carry
   +carry-trunc
   +carry-ext
   floor
   mod
   truncate
   rem
   sv::4vec))




(local (defthm gobj-bfr-list-eval-of-append
         (equal (gobj-bfr-list-eval (append x y) env)
                (append (gobj-bfr-list-eval x env)
                        (gobj-bfr-list-eval y env)))
         :hints(("Goal" :in-theory (enable gobj-bfr-list-eval)))))

(local (defthm gobj-bfr-list-eval-of-repeat
         (equal (gobj-bfr-list-eval (acl2::repeat n x) env)
                (acl2::repeat n (gobj-bfr-eval x env)))
         :hints(("Goal" :in-theory (enable gobj-bfr-list-eval acl2::repeat)))))

(local (defthm gobj-bfr-list-eval-of-take
         (equal (gobj-bfr-list-eval (take n x) env)
                (take n (gobj-bfr-list-eval x env)))
         :hints(("Goal" :in-theory (e/d (gobj-bfr-list-eval take acl2::default-cdr)
                                        (acl2::take-of-zero
                                         acl2::take-of-too-many))))))

(local (defthm bools->int-of-append
         (implies (consp y)
                  (equal (bools->int (append x y))
                         (logapp (len x) (bools->int x) (bools->int y))))
         :hints(("Goal" :in-theory (enable bools->int
                                           bitops::logapp**
                                           bitops::loghead**
                                           append len)))))

(local (defthm logcons-bit-identity
         (implies (bitp b)
                  (equal (logcons b (- b))
                         (- b)))
         :hints(("Goal" :in-theory (enable bitp)))))

(local (defthm logcdr-neg-bit-identity
         (implies (bitp b)
                  (equal (logcdr (- b))
                         (- b)))
         :hints(("Goal" :in-theory (enable bitp)))))


(local (defthm bools->int-of-repeat
         (equal (bools->int (acl2::repeat n x))
                (if (zp n)
                    0
                  (- (bool->bit x))))
         :hints(("Goal" :in-theory (enable bools->int acl2::repeat)))))

(local (defthm logapp-bools->int-of-extend-bits
         (equal (logapp n (bools->int (extend-bits n x)) y)
                (logapp n (bools->int x) y))
         :hints(("Goal" :in-theory (enable bools->int
                                           bitops::logapp**
                                           bitops::logext**
                                           take)))))

(local (defthm fgl-object-eval-when-atom-gobj-syntactic-integer->bits
         (b* (((mv ok fix) (gobj-syntactic-integer-fix x)))
           (implies (and ok
                         (not (gobj-syntactic-integer->bits fix)))
                    (acl2::int-equiv (fgl-object-eval x env) 0)))
         :hints (("goal" :use ((:instance fgl-object-eval-of-gobj-syntactic-integer-fix))
                  :in-theory (disable fgl-object-eval-of-gobj-syntactic-integer-fix)))))

(local (in-theory (enable bitops::logapp** bitops::loghead** bitops::logtail**)))

(local (in-theory (disable member-equal boolean-listp integer-listp append
                           equal-of-booleans-rewrite)))

(set-ignore-ok t)

(define nest-logconses-for-logapp ((n posp))
  :returns (term pseudo-termp
                 :hints(("Goal" :in-theory (enable length))))
  :measure (pos-fix n)
  :hints(("Goal" :in-theory (enable pos-fix)))
  :ruler-extenders (cons)
  :hooks ((:fix :hints(("Goal" :in-theory (enable pos-fix)))))
  `(intcons (if (intcar x) 't 'nil)
            ,(if (eql (lposfix n) 1)
                 'y
               `((lambda (x y)
                   ,(nest-logconses-for-logapp (1- n)))
                 (intcdr x) y)))
  ///
  (local (defun ind (n a)
           (declare (xargs :measure (pos-fix n)
                           :hints(("Goal" :in-theory (enable pos-fix)))))
           (if (equal (pos-fix n) 1)
               a
             (ind (1- n) `((x . ,(intcdr (cdr (hons-assoc-equal 'x a))))
                           (y . ,(cdr (hons-assoc-equal 'y a))))))))
  (defret fgl-ev-of-nest-logconses-for-logapp
    (equal (fgl-ev term a)
           (logapp (pos-fix n)
                   (fgl-ev 'x a)
                   (fgl-ev 'y a)))
    :hints(("Goal" :in-theory (enable bitops::logapp** pos-fix)
            :induct (ind n a)))))

(local (defthm logapp-when-zp
         (implies (zp n)
                  (equal (logapp n x y)
                         (ifix y)))
         :hints(("Goal" :in-theory (enable bitops::logapp**)))))
    

(def-fgl-meta logapp-expand
  (b* (((unless (fgl-object-case n :g-concrete))
        (mv nil nil nil interp-st state))
       (n (g-concrete->val n))
       ((unless (posp n))
        (mv t '(ifix y) `((y . ,y)) interp-st state)))
    (mv t (nest-logconses-for-logapp n)
        `((x . ,x) (y . ,y))
        interp-st state))
  :origfn logapp :formals (n x y)
  :formula-check bitops-formula-checks)

;; (LOCAL (FGL::INSTALL-FGL-PRIMITIVES FGL::BITOPS-PRIMITIVES))
;; (LOCAL (FGL::INSTALL-FGL-METAFNS FGL::BITOPS-METAFNS))
;; (FGL::ADD-FGL-META LOGAPP FGL::LOGAPP-expand)
;; (FGL::ADD-FGL-META ACL2::LOGTAIL$INLINE
;;                   FGL::LOGTAIL-EXPAND)
;; (FGL::REMOVE-FGL-PRIMITIVE ACL2::LOGTAIL$INLINE
;;                           FGL::FGL-LOGTAIL$INLINE-PRIMITIVE)
;; (FGL::REMOVE-FGL-PRIMITIVE LOGAPP FGL::FGL-LOGAPP-PRIMITIVE)
;; (FGL::ADD-FGL-PRIMITIVE ACL2::LOGTAIL$INLINE
;;                        FGL::FGL-LOGTAIL$INLINE-PRIMITIVE)
;; (FGL::ADD-FGL-PRIMITIVE LOGAPP FGL::FGL-LOGAPP-PRIMITIVE)


                           


(def-fgl-primitive logapp (width lsbs msbs)
  (b* (((unless (fgl-object-case width :g-concrete))
        (mv nil nil interp-st))
       ((mv ok lsbs) (gobj-syntactic-integer-fix lsbs))
       ((unless ok) (mv nil nil interp-st))
       ((mv ok msbs) (gobj-syntactic-integer-fix msbs))
       ((unless ok) (mv nil nil interp-st))
       (lsb-bits (gobj-syntactic-integer->bits lsbs))
       (msb-bits (gobj-syntactic-integer->bits msbs))
       (widthval (nfix (g-concrete->val width)))
       ;; If the length of LSB-BITS is <= width and all MSB-BITS are
       ;; syntactically equal to the last LSB-BIT, then as a special case we
       ;; can just return LSB-BITS.
       ((when (and (<= (len lsb-bits) widthval)
                   (b* ((last-lsb (car (last lsb-bits))))
                     (and (equal (car msb-bits) last-lsb)
                          (not (remove-equal last-lsb msb-bits))))))
        (mv t (mk-g-integer lsb-bits) interp-st)))
    (mv t (mk-g-integer (s-append (extend-bits widthval
                                               lsb-bits)
                                  (if (atom msb-bits) '(nil) msb-bits)))
        interp-st))
  :prepwork ((local (in-theory (disable fgl-object-eval-of-gobj-syntactic-integer-fix
                                        acl2::logapp** acl2::loghead**)))
             (local (defthm fgl-object-eval-when-gobj-syntactic-integer-fix
                      (b* (((mv ok fix) (gobj-syntactic-integer-fix x)))
                        (implies ok
                                 (acl2::int-equiv (fgl-object-eval x env)
                                                  (bools->int (gobj-bfr-list-eval (gobj-syntactic-integer->bits fix)
                                                                                  env)))))
                      :hints (("goal" :use ((:instance fgl-object-eval-of-gobj-syntactic-integer-fix))))))
             (local (defthm logcons-bit-when-neg-bit
                      (implies (equal (ifix cdr) (- (bfix car)))
                               (equal (logcons car cdr)
                                      (- (bfix car))))
                      :hints(("Goal" :in-theory (enable bfix)))))
             (local (in-theory (disable unsigned-byte-p
                                        acl2::loghead-upper-bound)))
             (local (defthm bools->int-of-eval-when-not-remove-equal
                      (implies (and (not (remove-equal bit x))
                                    (equal (car x) bit))
                               (equal (bools->int (gobj-bfr-list-eval x env))
                                      (- (bool->bit (gobj-bfr-eval bit env)))))
                      :hints(("Goal" :in-theory (e/d (gobj-bfr-list-eval bools->int remove-equal)
                                                     (bools->int-redef))))))
             (local (defthm logapp-neg-bits
                      (implies (bitp b)
                               (equal (logapp w (- b) (- b))
                                      (- b)))
                      :hints(("Goal" :in-theory (enable bitp)))))
             (local (defthm logapp-special-case
                      (implies (and (<= (len lsbs) (nfix w)))
                               (equal (logapp w
                                              (bools->int (gobj-bfr-list-eval lsbs env))
                                              (- (bool->bit (gobj-bfr-eval (car (last lsbs)) env))))
                                      (bools->int (gobj-bfr-list-eval lsbs env))))
                      :hints(("Goal" :in-theory (e/d (gobj-bfr-list-eval bools->int bitops::logapp**)
                                                     (bools->int-redef))
                              :induct (nthcdr w lsbs))))))
  :formula-check bitops-formula-checks)


;; NOTE: It's helpful to have a meta rule that changes (logtail N x) to (intcdr
;; (intcdr ... (n times) (intcdr x))) when x is not a g-integer. For the case
;; when x is a g-integer, the primitive below is better; therefore, we'll add
;; the meta rule first and then the primitive so the primitive will be tried
;; first.
(define nest-intcdrs ((n natp) (x pseudo-termp))
  :returns (new-x pseudo-termp)
  (if (zp n)
      (pseudo-term-fix x)
    (nest-intcdrs (1- n) `(intcdr ,(pseudo-term-fix x))))
  ///
  (defret fgl-ev-of-nest-intcdrs-int-equiv
    (acl2::int-equiv (fgl-ev new-x a)
                     (logtail n (fgl-ev x a)))
    :hints(("Goal" :in-theory (enable bitops::logtail**))))

  (defret fgl-ev-of-nest-intcdrs-posp
    (implies (posp n)
             (equal (fgl-ev new-x a)
                    (logtail n (fgl-ev x a))))
    :hints(("Goal" :in-theory (enable bitops::logtail**)
            :induct <call>
            :expand ((nest-intcdrs 1 x))))))

(local (defthm logtail-when-zp
         (implies (zp n)
                  (equal (logtail n x) (ifix x)))))

(def-fgl-meta logtail-expand
  (b* (((unless (fgl-object-case n :g-concrete))
        (mv nil nil nil interp-st state))
       (n (g-concrete->val n))
       ((unless (posp n))
        (mv t '(ifix x) `((x . ,x)) interp-st state)))
    (mv t (nest-intcdrs n 'x)
        `((x . ,x))
        interp-st state))
  :origfn acl2::logtail$inline :formals (n x)
  :formula-check bitops-formula-checks)


(define tail-bits ((n natp) x)
  (b* (((when (zp n)) x)
       ((when (mbe :logic (atom (cdr x))
                   :exec (or (atom x) (atom (cdr x)))))
        x))
    (tail-bits (1- n) (cdr x)))
  ///
  (local (defthm logtail-neg-bit
           (implies (bitp b)
                    (equal (logtail n (- b))
                           (- b)))
           :hints(("Goal" :in-theory (enable* bitops::logtail**
                                              bitops::ihsext-inductions)))))

  (defthm bools->int-of-tail-bits
    (equal (bools->int (tail-bits n x))
           (logtail n (bools->int x)))
    :hints(("Goal" :in-theory (enable bools->int bitops::logtail**))))

  

  (defthm gobj-bfr-list-eval-of-tail-bits
    (equal (gobj-bfr-list-eval (tail-bits n x) env)
           (tail-bits n (gobj-bfr-list-eval x env)))
    :hints(("Goal" :in-theory (enable gobj-bfr-list-eval))))

  (defthm member-of-tail-bits
    (implies (not (member v x))
             (not (member v (tail-bits n x)))))

  (defthm true-listp-of-tail-bits
    (iff (true-listp (tail-bits n x))
         (true-listp x))))

(def-fgl-primitive acl2::logtail$inline (n x)
  (b* (((unless (fgl-object-case n :g-concrete))
        (mv nil nil interp-st))
       ((mv ok x) (gobj-syntactic-integer-fix x))
       ((unless ok) (mv nil nil interp-st))
       (x-bits (gobj-syntactic-integer->bits x)))
    (mv t (mk-g-integer (tail-bits (nfix (g-concrete->val n)) x-bits))
        interp-st))
  :formula-check bitops-formula-checks)


(def-fgl-primitive < (x y)
  (b* ((ok (gobj-syntactic-integerp x))
       ((unless ok) (mv nil nil interp-st))
       (ok (gobj-syntactic-integerp y))
       ((unless ok) (mv nil nil interp-st))
       (x-bits (gobj-syntactic-integer->bits x))
       (y-bits (gobj-syntactic-integer->bits y)))
    (stobj-let ((logicman (interp-st->logicman interp-st)))
               (ans logicman)
               (bfr-<-ss x-bits y-bits logicman)
               (mv t (mk-g-boolean ans) interp-st))))

(def-fgl-primitive integer-length (x)
  (b* (((mv ok x) (gobj-syntactic-integer-fix x))
       ((unless ok) (mv nil nil interp-st))
       (x-bits (gobj-syntactic-integer->bits x)))
    (stobj-let ((logicman (interp-st->logicman interp-st)))
               (ans logicman)
               (bfr-integer-length-s x-bits logicman)
               (mv t (mk-g-integer ans) interp-st)))
  :formula-check bitops-formula-checks)


(local (defthm fgl-objectlist-fix-when-consp
         (implies (consp x)
                  (equal (fgl-objectlist-fix x)
                         (cons (fgl-object-fix (car x))
                               (fgl-objectlist-fix (cdr x)))))))

(local (defthm equal-of-g-concrete->val
         (implies (and (fgl-object-case x :g-concrete)
                       (fgl-object-case y :g-concrete))
                  (equal (equal (g-concrete->val x)
                                (g-concrete->val y))
                         (equal (fgl-object-fix x)
                                (fgl-object-fix y))))
         :hints(("Goal" :in-theory (e/d (fgl-object-fix-when-g-concrete)
                                        (g-concrete-of-fields))))))

(local (defthmd g-concrete->val-type-when-not-syntactic-integer
         (implies (and (not (gobj-syntactic-integerp x))
                       (fgl-object-case x :g-concrete))
                  (not (integerp (g-concrete->val x))))
         :hints(("Goal" :in-theory (enable gobj-syntactic-integerp)))
         :rule-classes :type-prescription))

(local (defthmd g-concrete->val-type-when-not-syntactic-boolean
         (implies (and (not (gobj-syntactic-booleanp x))
                       (fgl-object-case x :g-concrete))
                  (not (booleanp (g-concrete->val x))))
         :hints(("Goal" :in-theory (enable gobj-syntactic-booleanp)))
         :rule-classes :type-prescription))

(local (defthmd g-concrete->val-type-when-not-syntactic-cons
         (implies (and (not (gobj-syntactic-consp x))
                       (fgl-object-case x :g-concrete))
                  (not (consp (g-concrete->val x))))
         :hints(("Goal" :in-theory (enable gobj-syntactic-consp)))
         :rule-classes :type-prescription))

(local (in-theory (enable g-concrete->val-type-when-not-syntactic-boolean
                          g-concrete->val-type-when-not-syntactic-integer
                          g-concrete->val-type-when-not-syntactic-cons)))

(local (in-theory (disable acl2::member-equal-append
                           acl2::member-of-append
                           boolean-listp
                           (tau-system))))

;; (local (in-theory (enable gobj-bfr-eval)))
(local (in-theory (disable gobj-bfr-eval-reduce-by-bfr-eval)))

(define fgl-nice-4vec-call-p ((x fgl-object-p))
  (fgl-object-case x
    :g-apply (and (eq x.fn 'sv::4vec)
                  (eql (len x.args) 2)
                  (gobj-syntactic-integerp (first x.args))
                  (gobj-syntactic-integerp (second x.args)))
    :otherwise nil))

(define fgl-equal-int/4vec ((x fgl-object-p)
                            (y fgl-object-p)
                            &optional (logicman 'logicman))
  :guard (and (gobj-syntactic-integerp x)
              (fgl-nice-4vec-call-p y)
              (lbfr-listp (fgl-object-bfrlist x))
              (lbfr-listp (fgl-object-bfrlist y)))
  :returns (mv ans new-logicman)
  :verify-guards nil
  (b* ((xbits (gobj-syntactic-integer->bits x))
       ((g-apply y))
       ((mv ans1 logicman)
        (bfr-=-ss xbits
                  (gobj-syntactic-integer->bits (first y.args))
                  logicman))
       ((mv ans2 logicman)
        (bfr-=-ss xbits
                  (gobj-syntactic-integer->bits (second y.args))
                  logicman)))
    (bfr-and ans1 ans2 logicman))
  ///
  (local (include-book "tools/trivial-ancestors-check" :dir :system))
  (local (acl2::use-trivial-ancestors-check))
  (defret logicman-extension-of-<fn>
    (logicman-extension-plus new-logicman logicman))

  (local (in-theory (enable fgl-nice-4vec-call-p)))
  
  (defret bfr-p-of-<fn>
    (implies (and (lbfr-listp (fgl-object-bfrlist x))
                  (lbfr-listp (fgl-object-bfrlist y))
                  (gobj-syntactic-integerp x)
                  (fgl-nice-4vec-call-p y))
             (lbfr-p ans new-logicman)))
  ;; (local (defthm equal-atom-when-syntactic-consp
  ;;          (implies (and (gobj-syntactic-consp x)
  ;;                        (atom y))
  ;;                   (not (equal y (fgl-object-eval x env))))
  ;;          :hints(("Goal" :in-theory (enable fgl-object-eval
  ;;                                            gobj-syntactic-consp)))))

  
  (verify-guards fgl-equal-int/4vec-fn)

  (local (in-theory (enable sv::4vec-p-when-integerp)))

  (local (defthm 4vec->lower-when-integerp
           (implies (integerp x)
                    (equal (sv::4vec->lower x) x))
           :hints(("Goal" :in-theory (enable sv::4vec->lower sv::4vec-fix)))))

  (local (defthm 4vec->upper-when-integerp
           (implies (integerp x)
                    (equal (sv::4vec->upper x) x))
           :hints(("Goal" :in-theory (enable sv::4vec->upper sv::4vec-fix)))))
  
  (defret eval-of-<fn>
    (implies (and ok
                  (lbfr-listp (fgl-object-bfrlist x))
                  (lbfr-listp (fgl-object-bfrlist y))
                  (gobj-syntactic-integerp x)
                  (fgl-nice-4vec-call-p y)
                  (FGL-EV-META-EXTRACT-GLOBAL-FACTS :STATE ST)
                  (bitops-formula-checks st))
             (equal (gobj-bfr-eval ans env new-logicman)
                    (equal (fgl-object-eval x env logicman)
                           (fgl-object-eval y env logicman))))))



(define fgl-equal-4vec/4vec ((x fgl-object-p)
                             (y fgl-object-p)
                             &optional (logicman 'logicman))
  :guard (and (fgl-nice-4vec-call-p x)
              (fgl-nice-4vec-call-p y)
              (lbfr-listp (fgl-object-bfrlist x))
              (lbfr-listp (fgl-object-bfrlist y)))
  :returns (mv ans new-logicman)
  :verify-guards nil
  (b* (((g-apply x))
       ((g-apply y))
       ((mv ans1 logicman)
        (bfr-=-ss (gobj-syntactic-integer->bits (first x.args))
                  (gobj-syntactic-integer->bits (first y.args))
                  logicman))
       ((mv ans2 logicman)
        (bfr-=-ss (gobj-syntactic-integer->bits (second x.args))
                  (gobj-syntactic-integer->bits (second y.args))
                  logicman)))
    (bfr-and ans1 ans2 logicman))
  ///
  (local (include-book "tools/trivial-ancestors-check" :dir :system))
  (local (acl2::use-trivial-ancestors-check))
  (defret logicman-extension-of-<fn>
    (logicman-extension-plus new-logicman logicman))

  (local (in-theory (enable fgl-nice-4vec-call-p)))
  
  (defret bfr-p-of-<fn>
    (implies (and (lbfr-listp (fgl-object-bfrlist x))
                  (lbfr-listp (fgl-object-bfrlist y))
                  (fgl-nice-4vec-call-p x)
                  (fgl-nice-4vec-call-p y))
             (lbfr-p ans new-logicman)))
  ;; (local (defthm equal-atom-when-syntactic-consp
  ;;          (implies (and (gobj-syntactic-consp x)
  ;;                        (atom y))
  ;;                   (not (equal y (fgl-object-eval x env))))
  ;;          :hints(("Goal" :in-theory (enable fgl-object-eval
  ;;                                            gobj-syntactic-consp)))))

  
  (verify-guards fgl-equal-4vec/4vec-fn)

  (local (in-theory (enable sv::4vec-p-when-integerp)))

  (local (defthm 4vec->lower-when-integerp
           (implies (integerp x)
                    (equal (sv::4vec->lower x) x))
           :hints(("Goal" :in-theory (enable sv::4vec->lower sv::4vec-fix)))))

  (local (defthm 4vec->upper-when-integerp
           (implies (integerp x)
                    (equal (sv::4vec->upper x) x))
           :hints(("Goal" :in-theory (enable sv::4vec->upper sv::4vec-fix)))))
  
  (defret eval-of-<fn>
    (implies (and ok
                  (lbfr-listp (fgl-object-bfrlist x))
                  (lbfr-listp (fgl-object-bfrlist y))
                  (fgl-nice-4vec-call-p x)
                  (fgl-nice-4vec-call-p y)
                  (FGL-EV-META-EXTRACT-GLOBAL-FACTS :STATE ST)
                  (bitops-formula-checks st))
             (equal (gobj-bfr-eval ans env new-logicman)
                    (equal (fgl-object-eval x env logicman)
                           (fgl-object-eval y env logicman))))))


(define fgl-equal-const/4vec (x
                              (y fgl-object-p)
                              &optional (logicman 'logicman))
  :guard (and (fgl-nice-4vec-call-p y)
              (lbfr-listp (fgl-object-bfrlist y)))
  :returns (mv ans new-logicman)
  :verify-guards nil
  (b* (((unless (sv::4vec-p x)) (mv nil logicman))
       ((g-apply y))
       ((mv ans1 logicman)
        (bfr-=-ss (int->bools (sv::4vec->upper x))
                  (gobj-syntactic-integer->bits (first y.args))
                  logicman))
       ((mv ans2 logicman)
        (bfr-=-ss (int->bools (sv::4vec->lower x))
                  (gobj-syntactic-integer->bits (second y.args))
                  logicman)))
    (bfr-and ans1 ans2 logicman))
  ///
  (local (include-book "tools/trivial-ancestors-check" :dir :system))
  (local (acl2::use-trivial-ancestors-check))
  (defret logicman-extension-of-<fn>
    (logicman-extension-plus new-logicman logicman))

  (local (in-theory (enable fgl-nice-4vec-call-p)))
  
  (defret bfr-p-of-<fn>
    (implies (and (lbfr-listp (fgl-object-bfrlist y))
                  (fgl-nice-4vec-call-p y))
             (lbfr-p ans new-logicman)))
  ;; (local (defthm equal-atom-when-syntactic-consp
  ;;          (implies (and (gobj-syntactic-consp x)
  ;;                        (atom y))
  ;;                   (not (equal y (fgl-object-eval x env))))
  ;;          :hints(("Goal" :in-theory (enable fgl-object-eval
  ;;                                            gobj-syntactic-consp)))))

  
  (verify-guards fgl-equal-const/4vec-fn)

  (local (in-theory (enable sv::4vec-p-when-integerp)))

  (local (defthm 4vec->lower-when-integerp
           (implies (integerp x)
                    (equal (sv::4vec->lower x) x))
           :hints(("Goal" :in-theory (enable sv::4vec->lower sv::4vec-fix)))))

  (local (defthm 4vec->upper-when-integerp
           (implies (integerp x)
                    (equal (sv::4vec->upper x) x))
           :hints(("Goal" :in-theory (enable sv::4vec->upper sv::4vec-fix)))))
  
  (defret eval-of-<fn>
    (implies (and ok
                  (lbfr-listp (fgl-object-bfrlist y))
                  (fgl-nice-4vec-call-p y)
                  (FGL-EV-META-EXTRACT-GLOBAL-FACTS :STATE ST)
                  (bitops-formula-checks st))
             (equal (gobj-bfr-eval ans env new-logicman)
                    (equal x (fgl-object-eval y env logicman))))))



(define fgl-equal-aux ((x fgl-object-p)
                       (y fgl-object-p)
                       logicman)
  :guard (and (lbfr-listp (fgl-object-bfrlist x))
              (lbfr-listp (fgl-object-bfrlist y)))
  :returns (mv ok ans new-logicman)
  :verify-guards nil
  :measure (+ (fgl-object-count x)
              (fgl-object-count y))
  :prepwork ((local (defthm fgl-object-count-of-syntactic-list->car
                      (implies (gobj-syntactic-consp x)
                               (<= (fgl-object-count (gobj-syntactic-list->car x))
                                   (fgl-object-count x)))
                      :hints(("Goal" :in-theory (enable gobj-syntactic-consp
                                                        gobj-syntactic-list->car
                                                        fgl-object-count)))
                      :rule-classes :linear))
             (local (defthm fgl-object-count-of-syntactic-list->car-strong
                      (implies (and (gobj-syntactic-consp x)
                                    (not (fgl-object-case x :g-concrete)))
                               (< (fgl-object-count (gobj-syntactic-list->car x))
                                  (fgl-object-count x)))
                      :hints(("Goal" :in-theory (enable gobj-syntactic-consp
                                                        gobj-syntactic-list->car
                                                        fgl-object-count)))
                      :rule-classes :linear))
             (local (defthm fgl-object-count-of-syntactic-list->cdr
                      (implies (gobj-syntactic-consp x)
                               (<= (fgl-object-count (gobj-syntactic-list->cdr x))
                                   (fgl-object-count x)))
                      :hints(("Goal" :in-theory (enable gobj-syntactic-consp
                                                        gobj-syntactic-list->cdr
                                                        fgl-object-count)))
                      :rule-classes :linear))
             (local (defthm fgl-object-count-of-syntactic-list->cdr-strong
                      (implies (and (gobj-syntactic-consp x)
                                    (not (fgl-object-case x :g-concrete)))
                               (< (fgl-object-count (gobj-syntactic-list->cdr x))
                                  (fgl-object-count x)))
                      :hints(("Goal" :in-theory (enable gobj-syntactic-consp
                                                        gobj-syntactic-list->cdr
                                                        fgl-object-count)))
                      :rule-classes :linear)))

  (b* (((when (fgl-object-equiv x y)) (mv t t logicman))
       ((when (and (fgl-object-case x :g-concrete)
                   (fgl-object-case y :g-concrete)))
        (mv t nil logicman))
       ((when (gobj-syntactic-integerp x))
        (cond ((gobj-syntactic-integerp y)
               (b* (((mv ans logicman)
                     (bfr-=-ss (gobj-syntactic-integer->bits x)
                               (gobj-syntactic-integer->bits y)
                               logicman)))
                 (mv t ans logicman)))
              ((fgl-nice-4vec-call-p y)
               (b* (((mv ans logicman)
                     (fgl-equal-int/4vec x y)))
                 (mv t ans logicman)))
              ((fgl-object-case y '(:g-boolean :g-concrete :g-cons))
               (mv t nil logicman))
              (t (mv nil nil logicman))))
       ((when (gobj-syntactic-booleanp x))
        (cond ((gobj-syntactic-booleanp y)
               (b* (((mv ans logicman)
                     (bfr-iff (gobj-syntactic-boolean->bool x)
                              (gobj-syntactic-boolean->bool y)
                              logicman)))
                 (mv t ans logicman)))
              ((fgl-object-case y '(:g-integer :g-concrete :g-cons))
               (mv t nil logicman))
              (t (mv nil nil logicman))))
       ((when (gobj-syntactic-consp x))
        (cond ((gobj-syntactic-consp y)
               (b* (((mv ok1 ans1 logicman)
                     (fgl-equal-aux (gobj-syntactic-list->car x)
                                    (gobj-syntactic-list->car y)
                                    logicman))
                    ((when (and ok1 (eq ans1 nil)))
                     (mv t nil logicman))
                    ((mv ok2 ans2 logicman)
                     (fgl-equal-aux (gobj-syntactic-list->cdr x)
                                    (gobj-syntactic-list->cdr y)
                                    logicman))
                    ((when (and ok2 (eq ans2 nil)))
                     (mv t nil logicman))
                    ((unless (and ok1 ok2))
                     (mv nil nil logicman))
                    ((mv ans logicman) (bfr-and ans1 ans2 logicman)))
                 (mv t ans logicman)))
              ((fgl-object-case y '(:g-boolean :g-integer :g-concrete))
               (mv t nil logicman))
              (t (mv nil nil logicman))))
       ((when (fgl-nice-4vec-call-p x))
        (cond ((gobj-syntactic-integerp y)
               (b* (((mv ans logicman) (fgl-equal-int/4vec y x)))
                 (mv t ans logicman)))
              ((fgl-nice-4vec-call-p y)
               (b* (((mv ans logicman) (fgl-equal-4vec/4vec y x)))
                 (mv t ans logicman)))
              ((fgl-object-case y :g-concrete)
               (b* (((mv ans logicman) (fgl-equal-const/4vec (g-concrete->val y) x)))
                 (mv t ans logicman)))
              (t (mv (fgl-object-case y :g-boolean) nil logicman))))
       ((when (gobj-syntactic-integerp y))
        (mv (fgl-object-case x '(:g-boolean :g-concrete :g-cons))
            nil logicman))
       ((when (gobj-syntactic-booleanp y))
        (mv (fgl-object-case x '(:g-integer :g-concrete :g-cons))
            nil logicman))
       ((when (gobj-syntactic-consp y))
        (mv (fgl-object-case x '(:g-boolean :g-integer :g-concrete)) nil logicman))
       ((when (fgl-nice-4vec-call-p y))
        (cond ((fgl-object-case x :g-concrete)
               (b* (((mv ans logicman) (fgl-equal-const/4vec (g-concrete->val x) y)))
                 (mv t ans logicman)))
              (t (mv (fgl-object-case x :g-boolean) nil logicman)))))
    ;; BOZO add support for recursive primitives and add CONS case
    (mv nil nil logicman))
  ///
  (defret logicman-extension-of-<fn>
    (logicman-extension-plus new-logicman logicman))

  (defret bfr-p-of-<fn>
    (implies (and (lbfr-listp (fgl-object-bfrlist x))
                  (lbfr-listp (fgl-object-bfrlist y)))
             (lbfr-p ans new-logicman)))

  (verify-guards fgl-equal-aux)

  ;; (local (defthm equal-atom-when-syntactic-consp
  ;;          (implies (and (gobj-syntactic-consp x)
  ;;                        (atom y))
  ;;                   (not (equal y (fgl-object-eval x env))))
  ;;          :hints(("Goal" :in-theory (enable fgl-object-eval
  ;;                                            gobj-syntactic-consp)))))

  
  (local (in-theory (enable fgl-object-eval-when-gobj-syntactic-consp)))


  (local (defthm equal-boolean-when-fgl-nice-4vec-call
           (implies (and (fgl-nice-4vec-call-p y)
                         (FGL-EV-META-EXTRACT-GLOBAL-FACTS :STATE ST)
                         (bitops-formula-checks st)
                         (booleanp x))
                    (not (equal x (fgl-object-eval y env))))
           :hints(("Goal" :in-theory (enable fgl-nice-4vec-call-p)))))
  
  (defret eval-of-<fn>
    (implies (and ok
                  (lbfr-listp (fgl-object-bfrlist x))
                  (lbfr-listp (fgl-object-bfrlist y))
                  (FGL-EV-META-EXTRACT-GLOBAL-FACTS :STATE ST)
                  (bitops-formula-checks st))
             (equal (gobj-bfr-eval ans env new-logicman)
                    (equal (fgl-object-eval x env logicman)
                           (fgl-object-eval y env logicman))))
    :hints (("goal" :induct <call>
             :expand (<call>)
             :do-not-induct t))))



(def-fgl-primitive equal (x y)
  (stobj-let ((logicman (interp-st->logicman interp-st)))
             (ok ans logicman)
             (fgl-equal-aux x y logicman)
             (mv ok (mk-g-boolean ans) interp-st))
  :formula-check bitops-formula-checks)

(local (in-theory (disable g-concrete->val-type-when-not-syntactic-boolean
                           g-concrete->val-type-when-not-syntactic-cons
                           g-concrete->val-type-when-not-syntactic-integer)))
       ;; ((when (gobj-syntactic-consp x))
       ;;  (cond ((gobj-syntactic-consp y)
       ;;         (b* (((mv ok car-equal
       ;;         (stobj-let ((logicman (interp-st->logicman interp-st)))
       ;;                    (ans logicman)
       ;;                    (bfr-iff (gobj-syntactic-boolean->bool x)
       ;;                             (gobj-syntactic-boolean->bool y))
       ;;                    (mv t (mk-g-boolean ans) interp-st)))
       ;;        ((fgl-object-case y '(:g-integer :g-concrete :g-cons))
       ;;         (mv t nil interp-st))
       ;;        (t (mv nil nil interp-st)))
          

(def-fgl-primitive lognot (x)
  (b* (((mv xok x) (gobj-syntactic-integer-fix x))
       ((unless xok) (mv nil nil interp-st))
       (x-bits (gobj-syntactic-integer->bits x)))
    (stobj-let ((logicman (interp-st->logicman interp-st)))
               (ans-bits)
               (bfr-lognot-s x-bits logicman)
               (mv t (mk-g-integer ans-bits) interp-st)))
  :formula-check bitops-formula-checks)


(def-fgl-primitive acl2::binary-logand (x y)
  (b* (((mv xok x) (gobj-syntactic-integer-fix x))
       ((unless xok) (mv nil nil interp-st))
       ((mv yok y) (gobj-syntactic-integer-fix y))
       ((unless yok) (mv nil nil interp-st))
       (x-bits (gobj-syntactic-integer->bits x))
       (y-bits (gobj-syntactic-integer->bits y)))
    (stobj-let ((logicman (interp-st->logicman interp-st)))
               (ans-bits logicman)
               (bfr-logand-ss x-bits y-bits logicman)
               (mv t (mk-g-integer ans-bits) interp-st)))
  :formula-check bitops-formula-checks)

(def-fgl-primitive acl2::binary-logior (x y)
  (b* (((mv xok x) (gobj-syntactic-integer-fix x))
       ((unless xok) (mv nil nil interp-st))
       ((mv yok y) (gobj-syntactic-integer-fix y))
       ((unless yok) (mv nil nil interp-st))
       (x-bits (gobj-syntactic-integer->bits x))
       (y-bits (gobj-syntactic-integer->bits y)))
    (stobj-let ((logicman (interp-st->logicman interp-st)))
               (ans-bits logicman)
               (bfr-logior-ss x-bits y-bits logicman)
               (mv t (mk-g-integer ans-bits) interp-st)))
  :formula-check bitops-formula-checks)

(def-fgl-primitive acl2::binary-logxor (x y)
  (b* (((mv xok x) (gobj-syntactic-integer-fix x))
       ((unless xok) (mv nil nil interp-st))
       ((mv yok y) (gobj-syntactic-integer-fix y))
       ((unless yok) (mv nil nil interp-st))
       (x-bits (gobj-syntactic-integer->bits x))
       (y-bits (gobj-syntactic-integer->bits y)))
    (stobj-let ((logicman (interp-st->logicman interp-st)))
               (ans-bits logicman)
               (bfr-logxor-ss x-bits y-bits logicman)
               (mv t (mk-g-integer ans-bits) interp-st)))
  :formula-check bitops-formula-checks)

(def-fgl-primitive acl2::binary-logeqv (x y)
  (b* (((mv xok x) (gobj-syntactic-integer-fix x))
       ((unless xok) (mv nil nil interp-st))
       ((mv yok y) (gobj-syntactic-integer-fix y))
       ((unless yok) (mv nil nil interp-st))
       (x-bits (gobj-syntactic-integer->bits x))
       (y-bits (gobj-syntactic-integer->bits y)))
    (stobj-let ((logicman (interp-st->logicman interp-st)))
               (ans-bits logicman)
               (bfr-logeqv-ss x-bits y-bits logicman)
               (mv t (mk-g-integer ans-bits) interp-st)))
  :formula-check bitops-formula-checks)


(def-fgl-primitive binary-+ (x y)
  (b* (((unless (and (gobj-syntactic-integerp x)
                     (gobj-syntactic-integerp y)))
        (mv nil nil interp-st))
       (x-bits (gobj-syntactic-integer->bits x))
       (y-bits (gobj-syntactic-integer->bits y)))
    (stobj-let ((logicman (interp-st->logicman interp-st)))
               (ans-bits logicman)
               (bfr-+-ss nil x-bits y-bits logicman)
               (mv t (mk-g-integer ans-bits) interp-st))))

(def-fgl-primitive unary-- (x)
  (b* (((unless (gobj-syntactic-integerp x))
        (mv nil nil interp-st))
       (x-bits (gobj-syntactic-integer->bits x)))
    (stobj-let ((logicman (interp-st->logicman interp-st)))
               (ans-bits logicman)
               (bfr-unary-minus-s x-bits logicman)
               (mv t (mk-g-integer ans-bits) interp-st))))

(local (in-theory (enable +carry-trunc)))

(def-fgl-primitive +carry-trunc (width c x y)
  (b* (((unless (fgl-object-case width :g-concrete))
        (mv nil nil interp-st))
       ((mv cok c) (gobj-syntactic-boolean-fix c))
       ((unless cok) (mv nil nil interp-st))
       ((mv xok x) (gobj-syntactic-integer-fix x))
       ((unless xok) (mv nil nil interp-st))
       ((mv yok y) (gobj-syntactic-integer-fix y))
       ((unless yok) (mv nil nil interp-st))
       (cbit (gobj-syntactic-boolean->bool c))
       (x-bits (gobj-syntactic-integer->bits x))
       (y-bits (gobj-syntactic-integer->bits y)))
    (stobj-let ((logicman (interp-st->logicman interp-st)))
               (+bits logicman)
               (bfr-+-ss cbit x-bits y-bits logicman)
               (mv t
                   (mk-g-integer
                    (append (extend-bits (nfix (g-concrete->val width)) +bits)
                            '(nil)))
                   interp-st)))
  :formula-check bitops-formula-checks)

(local (in-theory (enable +carry)))

(def-fgl-primitive +carry (c x y)
  (b* (((mv cok c) (gobj-syntactic-boolean-fix c))
       ((unless cok) (mv nil nil interp-st))
       ((mv xok x) (gobj-syntactic-integer-fix x))
       ((unless xok) (mv nil nil interp-st))
       ((mv yok y) (gobj-syntactic-integer-fix y))
       ((unless yok) (mv nil nil interp-st))
       (cbit (gobj-syntactic-boolean->bool c))
       (x-bits (gobj-syntactic-integer->bits x))
       (y-bits (gobj-syntactic-integer->bits y)))
    (stobj-let ((logicman (interp-st->logicman interp-st)))
               (+bits logicman)
               (bfr-+-ss cbit x-bits y-bits logicman)
               (mv t
                   (mk-g-integer +bits)
                   interp-st)))
  :formula-check bitops-formula-checks)


(local (install-fgl-metafns bitops-metafns))


;; ;; Downgrade the rewrite rules concerning these to definitions so they'll be tried after the primitives.
;; ;; NOTE: Now rules (including rewrites and primitives) are tried in the
;; ;; reverse of the ordere they're introduced, so we shouldn't need this.
;; (remove-fgl-rewrite logapp-const-width)
;; (remove-fgl-rewrite logtail-const-shift)
;; (remove-fgl-rewrite integer-length-impl)
;; (remove-fgl-rewrite <-impl)
;; (remove-fgl-rewrite fgl-equal)
;; (remove-fgl-rewrite fgl-lognot)
;; (remove-fgl-rewrite fgl-logand)
;; (remove-fgl-rewrite fgl-logior)
;; (remove-fgl-rewrite fgl-logxor)
;; (remove-fgl-rewrite fgl-logeqv)
;; (remove-fgl-rewrite +-to-+carry)
;; (remove-fgl-rewrite minus-to-+carry)
;; (remove-fgl-rewrite fgl-+carry)
;; (remove-fgl-rewrite fgl-+carry-trunc)


;; (add-fgl-definition logapp-const-width)
;; (add-fgl-definition logtail-const-shift)
;; (add-fgl-definition integer-length-impl)
;; (add-fgl-definition <-impl)
;; (add-fgl-definition fgl-equal)
;; (add-fgl-definition fgl-lognot)
;; (add-fgl-definition fgl-logand)
;; (add-fgl-definition fgl-logior)
;; (add-fgl-definition fgl-logxor)
;; (add-fgl-definition fgl-logeqv)
;; (add-fgl-definition +-to-+carry)
;; (add-fgl-definition minus-to-+carry)
;; (add-fgl-definition fgl-+carry)
;; (add-fgl-definition fgl-+carry-trunc)



;; (def-fgl-rewrite logapp-const-width-allow-primitive
;;   (implies (syntaxp (and (integerp n)
;;                          ;; Allow this only when x is a g-var or g-apply, so
;;                          ;; that the primitive would fail but this can
;;                          ;; potentially generate bits for x.
;;                          (fgl-object-case x '(:g-var :g-apply))))
;;            (equal (logapp n x y)
;;                   (cond ((zp n) (int y))
;;                         (t (intcons (and (intcar x) t)
;;                                     (logapp (1- n) (intcdr x) y))))))
;;   :hints(("Goal" :in-theory (enable intcons intcar intcdr int-endp
;;                                     bitops::logapp**))))

;; (def-fgl-rewrite logtail-const-shift-allow-primitive
;;   (implies (syntaxp (and (integerp n)
;;                          (fgl-object-case x '(:g-var :g-apply))))
;;            (equal (logtail n x)
;;                   (if (or (zp n)
;;                           (check-int-endp x (syntax-bind xsyn (g-concrete x))))
;;                       (int x)
;;                     (logtail (1- n) (intcdr x)))))
;;   :hints(("Goal" :in-theory (enable intcons intcar intcdr int-endp
;;                                     bitops::logtail**))))



;; (def-fgl-rewrite fgl-equal-of-cons
;;   (equal (equal x y)
;;          (let ((xsyn (syntax-bind xsyn (g-concrete x)))
;;                (ysyn (syntax-bind ysyn (g-concrete y))))
;;            (cond ((check-consp x xsyn)
;;                   (cond ((check-consp y ysyn)
;;                          (and (equal (car x) (car y))
;;                               (equal (cdr x) (cdr y))))
;;                         ((check-non-consp y ysyn) nil)
;;                         (t (abort-rewrite (equal x y)))))
;;                  ((and (check-consp y ysyn)
;;                        (check-non-consp x xsyn)) nil)
;;                  (t (abort-rewrite (equal x y)))))))

(remove-fgl-rewrite loghead-to-logapp)
(def-fgl-rewrite loghead-to-logapp-always
  (equal (loghead n x)
         (logapp n x 0)))

(remove-fgl-rewrite logext-to-logapp)
(def-fgl-rewrite logext-to-logapp-always
  (equal (logext n x)
         (logapp n x (endint (logbitp (+ -1 (pos-fix n)) x))))
  :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                     bitops::ihsext-recursive-redefs
                                     pos-fix))))

;; (remove-fgl-rewrite logbitp-const-index)
;; (add-fgl-definition logbitp-const-index)
;; (def-fgl-rewrite logbitp-to-logtail
;;   (implies (syntaxp (and (integerp n)
;;                          (fgl-object-case x :g-integer)))
;;            (equal (logbitp n x)
;;                   (intcar (logtail n x)))))
                  
;; (remove-fgl-rewrite int-less-than-0)
;; (add-fgl-definition int-less-than-0)



(def-fgl-primitive floor (x y)
  (b* (((unless (and (gobj-syntactic-integerp x)
                     (gobj-syntactic-integerp y)))
        (mv nil nil interp-st))
       (x-bits (gobj-syntactic-integer->bits x))
       (y-bits (gobj-syntactic-integer->bits y)))
    (stobj-let ((logicman (interp-st->logicman interp-st)))
               (ans-bits logicman)
               (bfr-floor-ss x-bits y-bits logicman)
               (mv t (mk-g-integer ans-bits) interp-st)))
  :formula-check bitops-formula-checks)


(def-fgl-primitive mod (x y)
  (b* (((unless (and (gobj-syntactic-integerp x)
                     (gobj-syntactic-integerp y)))
        (mv nil nil interp-st))
       (x-bits (gobj-syntactic-integer->bits x))
       (y-bits (gobj-syntactic-integer->bits y)))
    (stobj-let ((logicman (interp-st->logicman interp-st)))
               (ans-bits logicman)
               (bfr-mod-ss x-bits y-bits logicman)
               (mv t (mk-g-integer ans-bits) interp-st)))
  :formula-check bitops-formula-checks)


(def-fgl-primitive truncate (x y)
  (b* (((unless (and (gobj-syntactic-integerp x)
                     (gobj-syntactic-integerp y)))
        (mv nil nil interp-st))
       (x-bits (gobj-syntactic-integer->bits x))
       (y-bits (gobj-syntactic-integer->bits y)))
    (stobj-let ((logicman (interp-st->logicman interp-st)))
               (ans-bits logicman)
               (bfr-truncate-ss x-bits y-bits logicman)
               (mv t (mk-g-integer ans-bits) interp-st)))
  :formula-check bitops-formula-checks)


(def-fgl-primitive rem (x y)
  (b* (((unless (and (gobj-syntactic-integerp x)
                     (gobj-syntactic-integerp y)))
        (mv nil nil interp-st))
       (x-bits (gobj-syntactic-integer->bits x))
       (y-bits (gobj-syntactic-integer->bits y)))
    (stobj-let ((logicman (interp-st->logicman interp-st)))
               (ans-bits logicman)
               (bfr-rem-ss x-bits y-bits logicman)
               (mv t (mk-g-integer ans-bits) interp-st)))
  :formula-check bitops-formula-checks)


