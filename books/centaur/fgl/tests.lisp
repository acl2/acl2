; GL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2019 Centaur Technology
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

(include-book "top")

(include-book "centaur/ipasir/ipasir-backend" :dir :system)









(defstub a () nil)
(defstub b () nil)
(defstub c () nil)


(thm
  (not (and (or (a) (b) (c))
            (or (not (a)) (b) (c))
            (or (a) (not (b)) (c))
            (or (not (a)) (not (b)) (c))
            (or (a) (b) (not (c)))
            (or (not (a)) (b) (not (c)))
            (or (a) (not (b)) (not (c)))
            (or (not (a)) (not (b)) (not (c)))))
  :hints (("goal" :clause-processor (gl-interp-cp clause
                                                      (default-glcp-config)
                                                      state))))



(include-book "centaur/bitops/ihsext-basics" :dir :system)

(def-gl-rewrite unsigned-byte-p-means-equal-loghead
  (implies (natp n)
           (iff (unsigned-byte-p n x)
                (equal x (loghead n x)))))

(def-gl-rewrite loghead-expand
  (implies (syntaxp (natp n))
           (equal (loghead n x)
                  (if (zp n)
                      0
                    (intcons (and (intcar x) t)
                             (loghead (1- n) (intcdr x))))))
  :hints(("Goal" :in-theory (enable intcons intcar intcdr
                                    bitops::loghead**))))

(def-gl-rewrite logtail-def
  (implies (syntaxp (natp n))
           (equal (logtail n x)
                  (if (zp n)
                      (int x)
                    (logtail (1- n) (intcdr x)))))
  :hints(("Goal" :in-theory (enable int intcdr bitops::logtail**))))




(table gl-fn-modes
       nil
       (let ((my-fn-mode (make-gl-function-mode :dont-expand-def t)))

         (list (cons 'unsigned-byte-p my-fn-mode)
               (cons 'acl2::loghead$inline my-fn-mode)
               (cons 'acl2::logtail$inline my-fn-mode)
               (cons 'intcdr my-fn-mode)
               (cons 'intcar my-fn-mode)
               (cons 'int my-fn-mode)
               (cons 'intcons my-fn-mode))) :clear)


  
(thm
 (if (unsigned-byte-p 5 x)
     (equal (logtail 7 x) 0)
   t)
 :hints (("goal" :clause-processor (gl-interp-cp clause (default-glcp-config) state)
          :in-theory nil)))


;; (def-gl-rewrite fgl-logand-of-ends
;;   (equal (logand (endint x) (endint y))
;;          (endint (and x y))))




;; (defmacro check-int-endp (x xsyn)
;;   `(let* ((x ,x)
;;           (xsyn (syntax-bind ,dummy-var (g-concrete x))))
;;      (check-int-endp-fn x xsyn)))


(def-gl-rewrite fgl-logand
  (equal (logand x y)
         (b* ((x (int x))
              (y (int y))
              (xsyn (syntax-bind xsyn (g-concrete x)))
              (ysyn (syntax-bind ysyn (g-concrete y)))
              ((when (and (check-int-endp x xsyn)
                          (check-int-endp y ysyn)))
               (endint (and (intcar x)
                            (intcar y)))))
           (intcons (and (intcar x)
                         (intcar y))
                    (logand (intcdr x) (intcdr y)))))
  :hints(("Goal" :in-theory (enable bitops::logand** int-endp))))


(def-gl-rewrite fgl-integerp-of-int
  (integerp (int x)))

(def-gl-rewrite fgl-consp-of-cons
  (consp (cons x y)))


(def-gl-rewrite fgl-booleanp-of-bool
  (booleanp (bool x)))



(defmacro syntactically-t (x dummy-var)
  `(let ((x ,x))
     (and (equal (syntax-bind ,dummy-var (g-concrete x)) t)
          (equal x t))))


;; (defthmd fgl-equal-ints
;;   (equal (equal (int x) (int y))
;;          (and (iff (intcar x) (intcar y))
;;               (or (and (syntactically-t (int-endp x) xendp)
;;                        (syntactically-t (int-endp y) xendp))
;;                   (equal (intcdr x) (intcdr y)))))
;;   :hints(("Goal" :in-theory (enable* acl2::arith-equiv-forwarding
;;                                      int-endp))))

;; (def-gl-rewrite fgl-equal-intconses-1
;;   (equal (equal (intcons* f1 r1) (intcons f2 r2))
;;          (and (iff f1 f2)
;;               (equal (int r1) (int r2)))))

;; (def-gl-rewrite fgl-equal-intconses-2
;;   (equal (equal (intcons f1 r1) (intcons* f2 r2))
;;          (and (iff f1 f2)
;;               (equal (int r1) (int r2)))))

;; (def-gl-rewrite fgl-equal-endints
;;   (equal (equal (endint x) (endint y))
;;          (iff x y)))

(def-gl-rewrite integerp-int
  (integerp (int x)))

(def-gl-rewrite integerp-bool
  (not (integerp (bool x))))

(def-gl-rewrite integerp-cons
  (not (integerp (cons x y))))

(def-gl-rewrite consp-cons
  (consp (cons x y)))

(def-gl-rewrite consp-int
  (not (consp (int x))))

(def-gl-rewrite consp-bool
  (not (consp (bool x))))

(def-gl-rewrite booleanp-bool
  (booleanp (bool x)))

(def-gl-rewrite booleanp-int
  (not (booleanp (int x))))

(def-gl-rewrite booleanp-cons
  (not (booleanp (cons x y))))


(define check-integerp (x xsyn)
  :verify-guards nil
  (and (gobj-syntactic-integerp xsyn)
       (integerp x))
  ///
  (defthm check-integerp-open
    (iff (check-integerp x xsyn)
         (and* (gobj-syntactic-integerp xsyn)
               (integerp x)))))







(def-gl-rewrite fgl-equal
  (equal (equal x y)
         (let ((xsyn (syntax-bind xsyn (g-concrete x)))
               (ysyn (syntax-bind ysyn (g-concrete y))))
           (cond ((check-integerp x xsyn)
                  (cond ((check-integerp y ysyn)
                         (and (iff (intcar x) (intcar y))
                              (or (and (check-int-endp x xsyn)
                                       (check-int-endp y ysyn))
                                  (equal (intcdr x) (intcdr y)))))
                        ((check-non-integerp y ysyn) nil)
                        (t (abort-rewrite (equal x y)))))
                 ((check-booleanp x xsyn)
                  (cond ((check-booleanp y ysyn)
                         (iff x y))
                        ((check-non-booleanp y ysyn) nil)
                        (t (abort-rewrite (equal x y)))))
                 ((check-consp x xsyn)
                  (cond ((check-consp y ysyn)
                         (and (equal (car x) (car y))
                              (equal (cdr x) (cdr y))))
                        ((check-non-consp y ysyn) nil)
                        (t (abort-rewrite (equal x y)))))
                 ((and (check-integerp y ysyn)
                       (check-non-integerp x xsyn)) nil)
                 ((and (check-booleanp y ysyn)
                       (check-non-booleanp x xsyn)) nil)
                 ((and (check-consp y ysyn)
                       (check-non-consp x xsyn)) nil)
                 (t (abort-rewrite (equal x y))))))
  :hints(("Goal" :in-theory (enable int-endp))))
               
                     
                     

;; (def-gl-rewrite fgl-equal-ints
;;   (equal (equal (int x) (int y))
;;          (if (and (check-int-endp x xend)
;;                   (check-int-endp y yend))
;;              (iff (intcar x) (intcar y))
;;            (and (iff (intcar x) (intcar y))
;;                 (equal (intcdr x) (intcdr y)))))
;;   :hints (("Goal" :use ((:instance acl2::logcar-logcdr-elim
;;                          (i (ifix x)))
;;                         (:instance acl2::logcar-logcdr-elim
;;                          (i (ifix y))))
;;            :in-theory (e/d (int-endp)
;;                            (acl2::logcar-logcdr-elim
;;                             bitops::logcons-destruct)))))

;; (def-gl-rewrite fgl-equal-conses
;;   (equal (equal (cons x1 y1) (cons x2 y2))
;;          (and (equal x1 x2)
;;               (equal y1 y2))))

;; (def-gl-rewrite fgl-equal-bools
;;   (equal (equal (bool x) (bool y))
;;          (iff x y)))


(thm
 (if (and (unsigned-byte-p 5 x)
          (unsigned-byte-p 5 y))
     (unsigned-byte-p 5 (logand x y))
   t)
 :hints (("goal" :clause-processor (gl-interp-cp clause (default-glcp-config) state)
          :in-theory nil)))

(thm
 (if (and (unsigned-byte-p 10 x)
          (unsigned-byte-p 10 y))
     (unsigned-byte-p 10 (logand x y))
   t)
 :hints (("goal" :clause-processor (gl-interp-cp clause (default-glcp-config) state)
          :in-theory nil)))

(thm
 (if (and (unsigned-byte-p 50 x)
          (unsigned-byte-p 50 y))
     (unsigned-byte-p 50 (logand x y))
   t)
 :hints (("goal" :clause-processor (gl-interp-cp clause (default-glcp-config) state)
          :in-theory nil)))

(thm
 (if (and (unsigned-byte-p 90 x)
          (unsigned-byte-p 90 y))
     (unsigned-byte-p 90 (logand x y))
   t)
 :hints (("goal" :clause-processor (gl-interp-cp clause (default-glcp-config) state)
          :in-theory nil)))


;; (trace$ (gl-rewrite-try-rule
;;          :cond (equal (acl2::rewrite-rule->rune rule)
;;                       '(:rewrite fgl-equal-ints))))



(def-gl-rewrite fgl-ash
  (implies (syntaxp (integerp shift))
           (equal (ash x shift)
                  (b* ((x (int x))
                       (shift (int shift)))
                    (cond ((eql shift 0) x)
                          ((< shift 0) (ash (intcdr x) (+ 1 shift)))
                          (t (intcons nil (ash x (+ -1 shift))))))))
  :hints(("Goal" :in-theory (enable bitops::ash**
                                    bitops::logtail**))))

(define +carry ((c booleanp)
                (x integerp)
                (y integerp))
  (+ (bool->bit c)
     (lifix x)
     (lifix y)))

(def-gl-rewrite fgl-+carry
  (equal (+carry c x y)
         (intcons (xor c (xor (intcar x) (intcar y)))
                  (if (and (check-int-endp x (syntax-bind xsyn (g-concrete x)))
                           (check-int-endp y (syntax-bind ysyn (g-concrete y))))
                      (endint (if c
                                  (and (intcar x) (intcar y))
                                (or (intcar x) (intcar y))))
                    (+carry (if c
                                (or (intcar x) (intcar y))
                              (and (intcar x) (intcar y)))
                            (intcdr x)
                            (intcdr y)))))
  :hints(("Goal" :in-theory (enable +carry int-endp
                                    bitops::equal-logcons-strong
                                    bitops::logxor** b-not))))

(def-gl-rewrite fgl-+
  (implies (and (integerp x) (integerp y))
           (equal (+ x y)
                  (+carry nil x y)))
  :hints(("Goal" :in-theory (enable +carry))))

(def-gl-rewrite fgl-unary-minus
  (implies (integerp x)
           (equal (- x)
                  (+carry t 0 (lognot x))))
  :hints(("Goal" :in-theory (enable lognot +carry))))

(encapsulate nil
  (local (defthm replace-mult
           (implies (equal (+ 1 z) x)
                    (equal (* x y)
                           (+ y (* z y))))))
  (local (defthm commute-*-2
           (equal (* y x z) (* x y z))
           :hints (("goal" :use ((:instance associativity-of-*)
                                 (:instance associativity-of-*
                                  (x y) (y x)))
                    :in-theory (disable associativity-of-*)))))

  (def-gl-rewrite fgl-*
    (implies (and (integerp x) (integerp y))
             (equal (* x y)
                    (if (check-int-endp x (syntax-bind xsyn (g-concrete x)))
                        (if (intcar x) (- y) 0)
                      (+ (if (intcar x) y 0)
                         (intcons nil
                                  (* (intcdr x) y))))))
    :hints(("Goal" :in-theory (e/d (int-endp logcons)
                                   (acl2::logcar-logcdr-elim
                                    bitops::logcons-destruct))
            :use ((:instance acl2::logcar-logcdr-elim
                   (i x)))))))

(def-gl-rewrite fgl-lognot
  (equal (lognot x)
         (if (check-int-endp x (syntax-bind xsyn (g-concrete x)))
             (endint (not (intcar x)))
           (intcons (not (intcar x))
                    (lognot (intcdr x)))))
  :hints(("Goal" :in-theory (enable bitops::lognot** int-endp))))

(def-gl-rewrite fgl-negp
  (implies (integerp x)
           (equal (acl2::negp x)
                  (if (check-int-endp x (syntax-bind xsyn (g-concrete x)))
                      (intcar x)
                    (acl2::negp (intcdr x)))))
  :hints(("Goal" :in-theory (enable int-endp))))

;; (define count-nat-bits ((x natp))
;;   :measure (integer-length x)
;;   :hints(("Goal" :in-theory (enable bitops::integer-length**)))
;;   (if (zp x)
;;       0
;;     (+ (logcar x)
;;        (count-nat-bits (intcdr x))))
;;   ///
;;   (def-gl-rewrite fgl-count-nat-bits
;;     (equal (count-nat-bits x)
;;            (cond ((check-int-endp x xendp)
;;                   0)
;;                  ((eql x 0) 0)
;;                  (t (+ (bool->bit (intcar x))
;;                        (count-nat-bits (intcdr x))))))
;;     :hints(("Goal" :in-theory (enable int-endp)))))

;; (define count-int-bits ((sign booleanp)
;;                         (x integerp))
;;   :measure (integer-length x)
;;   :hints(("Goal" :in-theory (enable bitops::integer-length** int-endp)))
;;   (if (int-endp x)
;;       0
;;     (+ (bool->bit (xor (intcar x) sign))
;;        (count-int-bits sign (intcdr x))))
;;   ///
;;   (def-gl-rewrite fgl-count-int-bits
;;     (equal (count-int-bits val x)
;;            (if (check-int-endp x xendp)
;;                0
;;              (+ (bool->bit (iff (intcar x) val))
;;                 (count-int-bits val (intcdr x)))))
;;     :hints(("Goal" :in-theory (enable int-endp)))))

(def-gl-rewrite fgl-logcount
  (equal (logcount x)
         (b* ((x (int x)))
           (if (check-int-endp x (syntax-bind xsyn (g-concrete x)))
               0
             (if (acl2::negp x)
                 (if (eql x -1)
                     0
                   (+ (bool->bit (not (intcar x)))
                      (logcount (intcdr x))))
               (if (eql x 0)
                   0
                 (+ (bool->bit (intcar x))
                    (logcount (intcdr x))))))))
  :hints(("Goal" :in-theory (enable int-endp
                                    bitops::logcount**))))
                  

(defun 32* (x y)
  (logand (* x y) (1- (expt 2 32))))

(defun fast-logcount-32 (v)
  (let* ((v (- v (logand (ash v -1) #x55555555)))
         (v (+ (logand v #x33333333)
               (logand (ash v -2) #x33333333))))
    (ash (32* (logand (+ v (ash v -4))
                      #xF0F0F0F)
              #x1010101)
         -24)))

(thm
 (if (unsigned-byte-p 32 x)
     (equal (fast-logcount-32 x)
            (logcount x))
   t)
 :hints (("goal" :clause-processor (gl-interp-cp clause (default-glcp-config) state)
          :in-theory nil)))


  


(defun fast-logcount-32* (v)
  (let* ((v (- v (logand (ash v -1) #x55545555)))
         (v (+ (logand v #x33333333)
               (logand (ash v -2) #x33333333))))
    (ash (32* (logand (+ v (ash v -4))
                      #xF0F0F0F)
              #x1010101)
         -24)))




(defun show-counterexample ()
  nil)

(table gl-fn-modes 'show-counterexample
       (make-gl-function-mode :dont-concrete-exec t))

(def-gl-rewrite show-counterexample-rw
  (equal (show-counterexample)
         (b* (((list bindings vars)
               (syntax-bind alists
                            (mv-let (bindings-vals var-vals)
                              (interp-st-counterex-stack-prev-bindings/print-errors interp-st state)
                              (g-concrete (list bindings-vals var-vals))))))
           (cw "Counterexample -- bindings: ~x0 variables: ~x1~%"
               bindings vars))))
              
                                   

(make-event
 ;; The must-fail doesn't really do it
 '(:or (thm
        ;; (if (unsigned-byte-p 32 x)
        (b* ((x (loghead 32 xx))
             (impl (fast-logcount-32* x))
             (spec (logcount x))
             (eq (equal impl spec))
             (?uneq-sat (fgl-sat-check (make-fgl-sat-config) (not eq))))
          (show-counterexample))
        ;;    (alists (syntax-bind alists1
        ;;                         (mv-let (bindings-vals var-vals)
        ;;                           (interp-st-counterex-stack-bindings/print-errors interp-st state)
        ;;                           (g-concrete (list bindings-vals var-vals))))))
        ;; (cw "Counterexample!: alists: ~x0~%" alists))
        :hints (("goal" :clause-processor (gl-interp-cp clause (default-glcp-config) state)
                 :in-theory nil)))
   (value-triple :failed-as-expected)))


;; (thm
;;  (implies (unsigned-byte-p 32 x)
;;           (equal (fast-logcount-32 x)
;;                  (logcount x)))
;;  :hints (("goal" :clause-processor (gl-interp-cp clause (default-glcp-config) state)
;;           :in-theory nil)))
