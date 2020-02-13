; FGL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2018 Centaur Technology
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

(in-package "FGL")

(include-book "primitives")
(include-book "bitops")
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
   +carry-ext))




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

(define extend-bits ((n natp) x)
  :guard-hints (("goal" :in-theory (enable default-car)))
  (b* (((when (zp n)) nil)
       (first (mbe :logic (car x)
                   :exec (and (consp x) (car x))))
       ((when (eql n 1)) (list first))
       ((when (or (atom x) (atom (cdr x))))
        (cons first (extend-bits (1- n) x))))
    (cons first (extend-bits (1- n) (cdr x))))
  ///
  (defthm len-of-extend-bits
    (Equal (len (extend-bits n x)) (nfix n)))

  (defthm consp-of-extend-bits
    (Equal (consp (extend-bits n x))
           (posp n)))

  (defthm bools->int-of-extend-bits
    (equal (bools->int (extend-bits n x))
           (if (zp n)
               0
             (logext n (bools->int x))))
    :hints(("Goal" :in-theory (enable bools->int bitops::logext**))))

  
  (local (defthm gobj-bfr-list-eval-under-iff
           (iff (gobj-bfr-list-eval x env)
                (consp x))
           :hints(("Goal" :in-theory (enable gobj-bfr-list-eval)))))

  (defthm gobj-bfr-list-eval-of-extend-bits
    (equal (gobj-bfr-list-eval (extend-bits n x) env)
           (extend-bits n (gobj-bfr-list-eval x env)))
    :hints(("Goal" :in-theory (enable gobj-bfr-list-eval))))

  (defthm member-of-extend-bits
    (implies (and (not (member v x))
                  v)
             (not (member v (extend-bits n x))))))

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
                           equal-of-booleans-rewrite set::empty-set-unique)))

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

(define s-append (lsb-bits (msb-bits true-listp))
  (if (atom lsb-bits)
      (if (atom msb-bits) '(nil)
        (mbe :logic (true-list-fix msb-bits)
             :exec msb-bits))
    (scons (car lsb-bits) (s-append (cdr lsb-bits) msb-bits)))
  ///
  (defthm eval-of-s-append
    (equal (bools->int (gobj-bfr-list-eval (s-append lsb-bits msb-bits) env))
           (logapp (len lsb-bits)
                   (bools->int (gobj-bfr-list-eval lsb-bits env))
                   (bools->int (gobj-bfr-list-eval msb-bits env))))
    :hints(("Goal" :in-theory (enable len)
            :induct (s-append lsb-bits msb-bits)
            :expand ((gobj-bfr-list-eval lsb-bits env)))
           (and stable-under-simplificationp
                '(:in-theory (e/d* (s-endp scdr))))))

  (defthm member-of-s-append
    (implies (and (not (member v msb-bits))
                  (not (member v lsb-bits))
                  v)
             (not (member v (s-append lsb-bits msb-bits))))))
                           


(def-fgl-primitive logapp (width lsbs msbs)
  (b* (((unless (fgl-object-case width :g-concrete))
        (mv nil nil interp-st))
       ((mv ok lsbs) (gobj-syntactic-integer-fix lsbs))
       ((unless ok) (mv nil nil interp-st))
       ((mv ok msbs) (gobj-syntactic-integer-fix msbs))
       ((unless ok) (mv nil nil interp-st))
       (lsb-bits (gobj-syntactic-integer->bits lsbs))
       (msb-bits (gobj-syntactic-integer->bits msbs)))
    (mv t (mk-g-integer (s-append (extend-bits (nfix (g-concrete->val width))
                                               lsb-bits)
                                  (if (atom msb-bits) '(nil) msb-bits)))
        interp-st))
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

(local (in-theory (enable g-concrete->val-type-when-not-syntactic-boolean
                          g-concrete->val-type-when-not-syntactic-integer)))

(local (in-theory (disable acl2::member-equal-append
                           acl2::member-of-append
                           boolean-listp
                           (tau-system))))

;; (local (in-theory (enable gobj-bfr-eval)))
(local (in-theory (disable gobj-bfr-eval-reduce-by-bfr-eval)))

(def-fgl-primitive equal (x y)
  (b* (((when (equal x y)) (mv t t interp-st))
       ((when (and (fgl-object-case x :g-concrete)
                   (fgl-object-case y :g-concrete)))
        (mv t nil interp-st))
       ((when (gobj-syntactic-integerp x))
        (cond ((gobj-syntactic-integerp y)
               (stobj-let ((logicman (interp-st->logicman interp-st)))
                          (ans logicman)
                          (bfr-=-ss (gobj-syntactic-integer->bits x)
                                    (gobj-syntactic-integer->bits y)
                                    logicman)
                          (mv t (mk-g-boolean ans) interp-st)))
              ((fgl-object-case y '(:g-boolean :g-concrete :g-cons))
               (mv t nil interp-st))
              (t (mv nil nil interp-st))))
       ((when (gobj-syntactic-booleanp x))
        (cond ((gobj-syntactic-booleanp y)
               (stobj-let ((logicman (interp-st->logicman interp-st)))
                          (ans logicman)
                          (bfr-iff (gobj-syntactic-boolean->bool x)
                                   (gobj-syntactic-boolean->bool y)
                                   logicman)
                          (mv t (mk-g-boolean ans) interp-st)))
              ((fgl-object-case y '(:g-integer :g-concrete :g-cons))
               (mv t nil interp-st))
              (t (mv nil nil interp-st))))
       ((when (gobj-syntactic-integerp y))
        (mv (fgl-object-case x '(:g-boolean :g-concrete :g-cons))
            nil interp-st))
       ((when (gobj-syntactic-booleanp y))
        (mv (fgl-object-case x '(:g-integer :g-concrete :g-cons))
            nil interp-st)))
    ;; BOZO add support for recursive primitives and add CONS case
    (mv nil nil interp-st)))

(local (in-theory (disable g-concrete->val-type-when-not-syntactic-boolean
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
