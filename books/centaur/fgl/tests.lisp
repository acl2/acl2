; FGL - A Symbolic Simulation Framework for ACL2
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

(include-book "std/testing/eval" :dir :system)
(value-triple (acl2::tshell-ensure))

; cert_param: (uses-glucose)
(local
 (progn
   (defun my-glucose-config ()
     (declare (xargs :guard t))
     (satlink::make-config :cmdline "glucose -model"
                           :verbose t
                           :mintime 1/2
                           :remove-temps t))

   (defattach fgl-satlink-config my-glucose-config)))


(define alist-to-let-bindings ((x alistp))
  (b* (((When (atom x)) nil)
       ((unless (mbt (consp (car x))))
        (alist-to-let-bindings (cdr x))))
    (cons `(,(caar x) ',(cdar x))
          (alist-to-let-bindings (cdr x)))))

(defmacro check-counterexample (form)
  `(progn
     (acl2::must-fail
      (fgl-thm ,form)
      :with-output-off nil)
     (make-event
      (b* (((mv err (cons ?stobjs-out values) state)
            (with-guard-checking-error-triple nil
              (trans-eval `(let ,(alist-to-let-bindings (interp-st->debug-info interp-st))
                             ,',form)
                          '(check-counterexample ,form)
                          state t)))
           ((when err)
            (er hard? 'check-counterexample "Failed to evaluate the counterexample for ~x0~%" ',form)
            (mv t nil state))
           ((when values)
            (er hard? 'check-counterexample "False counterexample for ~x0~%" ',form)
            (mv t nil state)))
        (value '(value-triple :ok))))))

(check-counterexample
 (b* ((x1 (logcdr x)))
   (equal (loghead 3 x1) (+ 1 (loghead 3 x1)))))




(encapsulate nil
  (local (disable-definition assoc-equal))
  (check-counterexample
   (b* ((x1 (logcdr (cdr (assoc '(a . b) x)))))
     (equal (loghead 3 x1) (+ 1 (loghead 3 x1))))))

(check-counterexample
 (b* ((x1 (logcons b (logcdr x)))
       (x2 (logcons (logcar x1) y)))
    (equal (loghead 3 x2) (loghead 3 (logcons 1 y)))))






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
  :hints (("goal" :clause-processor (fgl-interp-cp clause
                                                  (change-fgl-config
                                                   (default-fgl-config)
                                                   :make-ites t)
                                                  interp-st state))))



;; (include-book "centaur/bitops/ihsext-basics" :dir :system)

;; (def-fgl-rewrite unsigned-byte-p-means-equal-loghead
;;   (implies (natp n)
;;            (iff (unsigned-byte-p n x)
;;                 (equal x (loghead n x)))))

;; (def-fgl-rewrite loghead-expand
;;   (implies (syntaxp (natp n))
;;            (equal (loghead n x)
;;                   (if (zp n)
;;                       0
;;                     (intcons (and (intcar x) t)
;;                              (loghead (1- n) (intcdr x))))))
;;   :hints(("Goal" :in-theory (enable intcons intcar intcdr
;;                                     bitops::loghead**))))

;; (def-fgl-rewrite logtail-def
;;   (implies (syntaxp (natp n))
;;            (equal (logtail n x)
;;                   (if (zp n)
;;                       (int x)
;;                     (logtail (1- n) (intcdr x)))))
;;   :hints(("Goal" :in-theory (enable int intcdr bitops::logtail**))))




;; (table fgl-fn-modes
;;        nil
;;        (let ((my-fn-mode (make-fgl-function-mode :dont-expand-def t)))

;;          (list (cons 'unsigned-byte-p my-fn-mode)
;;                (cons 'acl2::loghead$inline my-fn-mode)
;;                (cons 'acl2::logtail$inline my-fn-mode)
;;                (cons 'intcdr my-fn-mode)
;;                (cons 'intcar my-fn-mode)
;;                (cons 'int my-fn-mode)
;;                (cons 'intcons my-fn-mode))) :clear)


  
(fgl-thm
 :hyp (unsigned-byte-p 5 x)
 :concl (equal (logtail 7 x) 0))


;; (def-fgl-rewrite fgl-logand-of-ends
;;   (equal (logand (endint x) (endint y))
;;          (endint (and x y))))




;; (defmacro check-int-endp (x xsyn)
;;   `(let* ((x ,x)
;;           (xsyn (syntax-bind ,dummy-var (g-concrete x))))
;;      (check-int-endp-fn x xsyn)))


;; (def-fgl-rewrite fgl-logand
;;   (equal (logand x y)
;;          (b* ((x (int x))
;;               (y (int y))
;;               (xsyn (syntax-bind xsyn (g-concrete x)))
;;               (ysyn (syntax-bind ysyn (g-concrete y)))
;;               ((when (and (check-int-endp x xsyn)
;;                           (check-int-endp y ysyn)))
;;                (endint (and (intcar x)
;;                             (intcar y)))))
;;            (intcons (and (intcar x)
;;                          (intcar y))
;;                     (logand (intcdr x) (intcdr y)))))
;;   :hints(("Goal" :in-theory (enable bitops::logand** int-endp))))


;; (def-fgl-rewrite fgl-integerp-of-int
;;   (integerp (int x)))

;; (def-fgl-rewrite fgl-consp-of-cons
;;   (consp (cons x y)))


;; (def-fgl-rewrite fgl-booleanp-of-bool
;;   (booleanp (bool x)))



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

;; (def-fgl-rewrite fgl-equal-intconses-1
;;   (equal (equal (intcons* f1 r1) (intcons f2 r2))
;;          (and (iff f1 f2)
;;               (equal (int r1) (int r2)))))

;; (def-fgl-rewrite fgl-equal-intconses-2
;;   (equal (equal (intcons f1 r1) (intcons* f2 r2))
;;          (and (iff f1 f2)
;;               (equal (int r1) (int r2)))))

;; (def-fgl-rewrite fgl-equal-endints
;;   (equal (equal (endint x) (endint y))
;;          (iff x y)))

;; (def-fgl-rewrite integerp-int
;;   (integerp (int x)))

;; (def-fgl-rewrite integerp-bool
;;   (not (integerp (bool x))))

;; (def-fgl-rewrite integerp-cons
;;   (not (integerp (cons x y))))

;; (def-fgl-rewrite consp-cons
;;   (consp (cons x y)))

;; (def-fgl-rewrite consp-int
;;   (not (consp (int x))))

;; (def-fgl-rewrite consp-bool
;;   (not (consp (bool x))))

;; (def-fgl-rewrite booleanp-bool
;;   (booleanp (bool x)))

;; (def-fgl-rewrite booleanp-int
;;   (not (booleanp (int x))))

;; (def-fgl-rewrite booleanp-cons
;;   (not (booleanp (cons x y))))


;; (define check-integerp (x xsyn)
;;   :verify-guards nil
;;   (and (gobj-syntactic-integerp xsyn)
;;        (integerp x))
;;   ///
;;   (defthm check-integerp-open
;;     (iff (check-integerp x xsyn)
;;          (and* (gobj-syntactic-integerp xsyn)
;;                (integerp x)))))







;; (def-fgl-rewrite fgl-equal
;;   (equal (equal x y)
;;          (let ((xsyn (syntax-bind xsyn (g-concrete x)))
;;                (ysyn (syntax-bind ysyn (g-concrete y))))
;;            (cond ((check-integerp x xsyn)
;;                   (cond ((check-integerp y ysyn)
;;                          (and (iff (intcar x) (intcar y))
;;                               (or (and (check-int-endp x xsyn)
;;                                        (check-int-endp y ysyn))
;;                                   (equal (intcdr x) (intcdr y)))))
;;                         ((check-non-integerp y ysyn) nil)
;;                         (t (abort-rewrite (equal x y)))))
;;                  ((check-booleanp x xsyn)
;;                   (cond ((check-booleanp y ysyn)
;;                          (iff x y))
;;                         ((check-non-booleanp y ysyn) nil)
;;                         (t (abort-rewrite (equal x y)))))
;;                  ((check-consp x xsyn)
;;                   (cond ((check-consp y ysyn)
;;                          (and (equal (car x) (car y))
;;                               (equal (cdr x) (cdr y))))
;;                         ((check-non-consp y ysyn) nil)
;;                         (t (abort-rewrite (equal x y)))))
;;                  ((and (check-integerp y ysyn)
;;                        (check-non-integerp x xsyn)) nil)
;;                  ((and (check-booleanp y ysyn)
;;                        (check-non-booleanp x xsyn)) nil)
;;                  ((and (check-consp y ysyn)
;;                        (check-non-consp x xsyn)) nil)
;;                  (t (abort-rewrite (equal x y))))))
;;   :hints(("Goal" :in-theory (enable int-endp))))
               
                     
                     

;; (def-fgl-rewrite fgl-equal-ints
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

;; (def-fgl-rewrite fgl-equal-conses
;;   (equal (equal (cons x1 y1) (cons x2 y2))
;;          (and (equal x1 x2)
;;               (equal y1 y2))))

;; (def-fgl-rewrite fgl-equal-bools
;;   (equal (equal (bool x) (bool y))
;;          (iff x y)))
(make-event
 (er-progn (assign :fgl-trace-rewrites t)
           (assign :fgl-trace-rule-alist '(((:rewrite loghead-const-width))
                                           ((:rewrite loghead-to-logmask-helper))
                                           ((:rewrite fgl-equal))))
           (value '(value-triple :trace-on))))

(fgl-thm
 :hyp (and (unsigned-byte-p 5 x)
           (unsigned-byte-p 5 y))
 :concl (unsigned-byte-p 5 (logand x y)))

(make-event
 (er-progn (assign :fgl-trace-rewrites nil)
           (assign :fgl-trace-rule-alist nil)
           (value '(value-triple :trace-off))))


(fgl-thm
 :hyp (and (unsigned-byte-p 10 x)
           (unsigned-byte-p 10 y))
 :concl (unsigned-byte-p 10 (logand x y)))

(fgl-thm
 :hyp (and (unsigned-byte-p 50 x)
           (unsigned-byte-p 50 y))
 :concl (unsigned-byte-p 50 (logand x y)))

(fgl-thm
  :hyp (and (unsigned-byte-p 90 x)
            (unsigned-byte-p 90 y))
  :concl (unsigned-byte-p 90 (logand x y)))


;; (trace$ (fgl-rewrite-try-rule
;;          :cond (equal (acl2::rewrite-rule->rune rule)
;;                       '(:rewrite fgl-equal-ints))))



;; (def-fgl-rewrite fgl-ash
;;   (implies (syntaxp (integerp shift))
;;            (equal (ash x shift)
;;                   (b* ((x (int x))
;;                        (shift (int shift)))
;;                     (cond ((eql shift 0) x)
;;                           ((< shift 0) (ash (intcdr x) (+ 1 shift)))
;;                           (t (intcons nil (ash x (+ -1 shift))))))))
;;   :hints(("Goal" :in-theory (enable bitops::ash**
;;                                     bitops::logtail**))))

;; (define +carry ((c booleanp)
;;                 (x integerp)
;;                 (y integerp))
;;   (+ (bool->bit c)
;;      (lifix x)
;;      (lifix y)))

;; (def-fgl-rewrite fgl-+carry
;;   (equal (+carry c x y)
;;          (intcons (xor c (xor (intcar x) (intcar y)))
;;                   (if (and (check-int-endp x (syntax-bind xsyn (g-concrete x)))
;;                            (check-int-endp y (syntax-bind ysyn (g-concrete y))))
;;                       (endint (if c
;;                                   (and (intcar x) (intcar y))
;;                                 (or (intcar x) (intcar y))))
;;                     (+carry (if c
;;                                 (or (intcar x) (intcar y))
;;                               (and (intcar x) (intcar y)))
;;                             (intcdr x)
;;                             (intcdr y)))))
;;   :hints(("Goal" :in-theory (enable +carry int-endp
;;                                     bitops::equal-logcons-strong
;;                                     bitops::logxor** b-not))))

;; (def-fgl-rewrite fgl-+
;;   (implies (and (integerp x) (integerp y))
;;            (equal (+ x y)
;;                   (+carry nil x y)))
;;   :hints(("Goal" :in-theory (enable +carry))))

;; (def-fgl-rewrite fgl-unary-minus
;;   (implies (integerp x)
;;            (equal (- x)
;;                   (+carry t 0 (lognot x))))
;;   :hints(("Goal" :in-theory (enable lognot +carry))))

;; (encapsulate nil
;;   (local (defthm replace-mult
;;            (implies (equal (+ 1 z) x)
;;                     (equal (* x y)
;;                            (+ y (* z y))))))
;;   (local (defthm commute-*-2
;;            (equal (* y x z) (* x y z))
;;            :hints (("goal" :use ((:instance associativity-of-*)
;;                                  (:instance associativity-of-*
;;                                   (x y) (y x)))
;;                     :in-theory (disable associativity-of-*)))))

;;   (def-fgl-rewrite fgl-*
;;     (implies (and (integerp x) (integerp y))
;;              (equal (* x y)
;;                     (if (check-int-endp x (syntax-bind xsyn (g-concrete x)))
;;                         (if (intcar x) (- y) 0)
;;                       (+ (if (intcar x) y 0)
;;                          (intcons nil
;;                                   (* (intcdr x) y))))))
;;     :hints(("Goal" :in-theory (e/d (int-endp logcons)
;;                                    (acl2::logcar-logcdr-elim
;;                                     bitops::logcons-destruct))
;;             :use ((:instance acl2::logcar-logcdr-elim
;;                    (i x)))))))

;; (def-fgl-rewrite fgl-lognot
;;   (equal (lognot x)
;;          (if (check-int-endp x (syntax-bind xsyn (g-concrete x)))
;;              (endint (not (intcar x)))
;;            (intcons (not (intcar x))
;;                     (lognot (intcdr x)))))
;;   :hints(("Goal" :in-theory (enable bitops::lognot** int-endp))))

;; (def-fgl-rewrite fgl-negp
;;   (implies (integerp x)
;;            (equal (acl2::negp x)
;;                   (if (check-int-endp x (syntax-bind xsyn (g-concrete x)))
;;                       (intcar x)
;;                     (acl2::negp (intcdr x)))))
;;   :hints(("Goal" :in-theory (enable int-endp))))

;; (define count-nat-bits ((x natp))
;;   :measure (integer-length x)
;;   :hints(("Goal" :in-theory (enable bitops::integer-length**)))
;;   (if (zp x)
;;       0
;;     (+ (logcar x)
;;        (count-nat-bits (intcdr x))))
;;   ///
;;   (def-fgl-rewrite fgl-count-nat-bits
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
;;   (def-fgl-rewrite fgl-count-int-bits
;;     (equal (count-int-bits val x)
;;            (if (check-int-endp x xendp)
;;                0
;;              (+ (bool->bit (iff (intcar x) val))
;;                 (count-int-bits val (intcdr x)))))
;;     :hints(("Goal" :in-theory (enable int-endp)))))

;; (def-fgl-rewrite fgl-logcount
;;   (equal (logcount x)
;;          (b* ((x (int x)))
;;            (if (check-int-endp x (syntax-bind xsyn (g-concrete x)))
;;                0
;;              (if (acl2::negp x)
;;                  (if (eql x -1)
;;                      0
;;                    (+ (bool->bit (not (intcar x)))
;;                       (logcount (intcdr x))))
;;                (if (eql x 0)
;;                    0
;;                  (+ (bool->bit (intcar x))
;;                     (logcount (intcdr x))))))))
;;   :hints(("Goal" :in-theory (enable int-endp
;;                                     bitops::logcount**))))

(make-event
 (er-progn (assign :fgl-trace-rule-alist '(((:rewrite fgl-*))
                                           ((:rewrite <-impl))
                                           ((:rewrite fgl-logcount))
                                           ((:rewrite logcount-impl))
                                           ((:rewrite +-to-+carry-width))))
           (value '(value-triple :trace-rules))))

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

(fgl-thm
 :hyp (unsigned-byte-p 32 x)
 :concl (equal (fast-logcount-32 x)
               (logcount x)))


  


(defun fast-logcount-32* (v)
  (let* ((v (- v (logand (ash v -1) #x55545555)))
         (v (+ (logand v #x33333333)
               (logand (ash v -2) #x33333333))))
    (ash (32* (logand (+ v (ash v -4))
                      #xF0F0F0F)
              #x1010101)
         -24)))


(check-counterexample
 (implies (unsigned-byte-p 2 x)
          (not (equal x 2))))

(check-counterexample
 (implies (signed-byte-p 2 x)
          (not (equal x 1))))

(check-counterexample
 (implies (signed-byte-p 2 x)
          (not (equal x -2))))

(check-counterexample
 (implies (signed-byte-p 2 x)
          (not (equal x -1))))

(check-counterexample
 (implies (unsigned-byte-p 32 x)
          (equal (fast-logcount-32* x)
                 (logcount x))))







(include-book "member-equal")
(include-book "bitops-primitives")
(local (in-theory (disable w)))
(install-fgl-metafns tests)


       


(fgl-thm
 :hyp (unsigned-byte-p 7 x)
 :concl (if (logbitp 8 x)
            (fgl-error :msg "Logbitp 8!")
          t))

(make-event
 (b* (((mv err ?val state)
       (fgl-thm
        :hyp (unsigned-byte-p 7 x)
        :concl (if (logbitp 6 x)
                   (fgl-error :msg "Logbitp 6!")
                 t)))
      ((unless (and err
                    (equal (@ :fgl-interp-error-message) "Logbitp 6!")))
       (er soft 'test-fgl-error "Didn't work?")))
   (value '(value-triple :ok))))
   
      


(fgl-thm
 :hyp (unsigned-byte-p 7 x)
 :concl (fgl-prog2 (with-fgl-testbench!
                     (if (logbitp 8 x)
                         (syntax-interp (cw "Yes~%"))
                       (syntax-interp (cw "No~%"))))
                   t))


(fancy-ev-add-primitive interp-st->flags$inline t)
(fancy-ev-add-primitive update-interp-st->flags$inline (interp-flags-p flags))
(def-fancy-ev-primitives new)

(make-event
 (b* (((mv err ?val state)
       (fgl-thm
        :hyp (unsigned-byte-p 7 x)
        :concl (fgl-prog2 (with-fgl-testbench!
                            (if (logbitp 6 x)
                                (syntax-interp (cw "Yes~%"))
                              (syntax-interp (cw "No~%"))))
                          t)))
      ((unless (and err
                    (fgl-object-case (@ :fgl-interp-error-debug-obj) :g-boolean)))
       (er soft 'test-with-fgl-testbench "Didn't work? err: ~x0 debug-obj: ~x1" err (@ :fgl-interp-error-debug-obj))))
   (value '(value-triple :ok))))


(fgl-thm
 (implies (and (unsigned-byte-p 5 width)
               (unsigned-byte-p 64 x)
               (unsigned-byte-p 64 y))
          (equal (time$ (logtail width (logapp width x y)))
                 y)))

(fgl-thm
 (implies (and (unsigned-byte-p 5 width)
               (unsigned-byte-p 64 x)
               (unsigned-byte-p 64 y))
          (equal (fgl-time (time$ (logtail width (logapp width x y))))
                 y)))

(include-book "centaur/bitops/merge" :dir :system)

(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))


(encapsulate nil
  (local
   (progn
     (fgl::disable-definition unsigned-byte-p)
     (fgl::remove-fgl-rewrite UNSIGNED-BYTE-P-CONST-WIDTH)
     (define unsigned-width (x)
       (declare (ignore x))
       nil
       ///
       (fgl::disable-definition unsigned-width))


     (define u32-fix (x)
       :verify-guards nil
       (loghead 32 x)
       ///
       (fgl::disable-definition u32-fix)

       (fgl::def-fgl-rewrite u32-fix-unsigned-width
         (unequiv (unsigned-width (u32-fix x)) 32))
       (in-theory (enable u32-fix-unsigned-width))

       (fgl::def-fgl-rewrite u32-fix-unsigned-byte-p
         (unsigned-byte-p 32 (u32-fix x)))

       (in-theory (enable u32-fix-unsigned-byte-p)))

     (fgl::def-fgl-rewrite unsigned-byte-p-by-unsigned-width
       (implies (and (unequiv width (double-rewrite (unsigned-width x)))
                     (syntaxp (not (equal width width2)))
                     (unsigned-byte-p width x)
                     (natp width2)
                     (<= width width2))
                (unsigned-byte-p width2 x))
       :hints(("Goal" :in-theory (disable unsigned-byte-p))))

     (in-theory (enable unsigned-byte-p-by-unsigned-width))

     (defthm unsigned-byte-p-64-of-u32-fix-acl2
       (unsigned-byte-p 64 (u32-fix x)))

     (fgl::def-fgl-thm unsigned-byte-p-64-of-u32-fix
       (unsigned-byte-p 64 (u32-fix x))))))




;; (local (defun my-fgl-satlink-config ()
;;          (declare (xargs :guard t))
;;          (make-fgl-satlink-monolithic-sat-config :transform t)))

;; (local (defattach fgl-toplevel-sat-check-config my-fgl-satlink-config))



(define simd-mult-spec ((lane natp)
                        (src1 integerp)
                        (src2 integerp)
                        (mask integerp))
  (let* ((maskbit (logbitp lane mask))
         (src1-lane (bitops::nth-slice32 lane src1))
         (src2-lane (bitops::nth-slice32 lane src2)))
    (if maskbit (* src1-lane src2-lane) 0)))

(define simd-mult-impl ((lane natp)
                        (src1 integerp)
                        (src2 integerp)
                        (mask integerp))
  (let* ((maskbit (logbitp lane mask))
         (src1-lane (if maskbit (bitops::nth-slice32 lane src1) 0))
         (src2-lane (if maskbit (bitops::nth-slice32 lane src2) 0)))
    (if maskbit (* src1-lane src2-lane) 0)))

(include-book "std/testing/eval" :dir :system)


(local
 (progn
   (defun glucose-config-10sec ()
     (declare (xargs :guard t))
     (satlink::make-config :cmdline "glucose -cpu-lim=10"
                           :verbose t
                           :mintime 1/2
                           :remove-temps t))

   (defattach fgl-satlink-config glucose-config-10sec)))

(acl2::must-fail
 (def-fgl-thm simd-multiply-correct
   (implies (and (unsigned-byte-p 128 src1)
                 (unsigned-byte-p 128 src2)
                 (unsigned-byte-p 4 writemask))
            (let ((spec (bitops::merge-4-u32s (simd-mult-spec 3 src1 src2 writemask)
                                              (simd-mult-spec 2 src1 src2 writemask)
                                              (simd-mult-spec 1 src1 src2 writemask)
                                              (simd-mult-spec 0 src1 src2 writemask)))
                  (impl (bitops::merge-4-u32s (simd-mult-impl 3 src1 src2 writemask)
                                              (simd-mult-impl 2 src1 src2 writemask)
                                              (simd-mult-impl 1 src1 src2 writemask)
                                              (simd-mult-impl 0 src1 src2 writemask))))
              (equal impl spec)))))

(encapsulate nil
  (local (def-fgl-rewrite top-level-equal-solve-lane-by-lane-masked
           (equal (top-level-equal x y)
                  (solve-lane-by-lane-masked
                   x y
                   (syntax-bind mask (lookup-previous-stack-frame-binding 'writemask 'interp-st))
                   32))))

  (def-fgl-thm simd-multiply-correct
    (implies (and (unsigned-byte-p 128 src1)
                  (unsigned-byte-p 128 src2)
                  (unsigned-byte-p 4 writemask))
             (let ((spec (bitops::merge-4-u32s (simd-mult-spec 3 src1 src2 writemask)
                                               (simd-mult-spec 2 src1 src2 writemask)
                                               (simd-mult-spec 1 src1 src2 writemask)
                                               (simd-mult-spec 0 src1 src2 writemask)))
                   (impl (bitops::merge-4-u32s (simd-mult-impl 3 src1 src2 writemask)
                                               (simd-mult-impl 2 src1 src2 writemask)
                                               (simd-mult-impl 1 src1 src2 writemask)
                                               (simd-mult-impl 0 src1 src2 writemask))))
               (equal impl spec)))
    :hints ('(:clause-processor replace-equal-with-top-level-equal))))



;; Counterexample tests.

(encapsulate nil
  (local (disable-definition assoc-equal))
  (check-counterexample
   (b* ((a (cdr (assoc-equal 'a x)))
        (b (cdr (assoc-equal 'b x))))
     (implies (unsigned-byte-p 3 a)
              (not (and (equal (loghead 2 a) 2)
                        (equal (loghead 4 b) 1)))))))

(check-counterexample
 (not (equal (+ (loghead 3 x) (loghead 4 y)) 9)))
 
