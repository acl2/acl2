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
  :hints (("goal" :clause-processor (top-gl-interp-cp clause
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
 :hints (("goal" :clause-processor (top-gl-interp-cp clause (default-glcp-config) state)
          :in-theory nil)))


;; (def-gl-rewrite fgl-logand-of-ends
;;   (equal (logand (endint x) (endint y))
;;          (endint (and x y))))


(defund gl-int-endp (x)
  (gl-object-case x
    :g-integer (atom (cdr x.bits))
    :g-boolean t
    :g-cons t
    :g-concrete (or (zip x.val) (eql x.val -1))
    :otherwise nil))

(define check-int-endp (x xsyn)
  :verify-guards nil
  (and (gl-int-endp xsyn)
       (int-endp x))
  ///
  (defthm check-int-endp-open
    (iff (check-int-endp x xsyn)
         (and* (gl-int-endp xsyn)
               (int-endp x)))))

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



(define check-integerp (x xsyn)
  :verify-guards nil
  (and (gobj-syntactic-integerp xsyn)
       (integerp x))
  ///
  (defthm check-integerp-open
    (iff (check-integerp x xsyn)
         (and* (gobj-syntactic-integerp xsyn)
               (integerp x)))))

(define check-consp (x xsyn)
  :verify-guards nil
  (and (gobj-syntactic-consp xsyn)
       (consp x))
  ///
  (defthm check-consp-open
    (iff (check-consp x xsyn)
         (and* (gobj-syntactic-consp xsyn)
               (consp x)))))

(define check-booleanp (x xsyn)
  :verify-guards nil
  (and (gobj-syntactic-booleanp xsyn)
       (booleanp x))
  ///
  (defthm check-booleanp-open
    (iff (check-booleanp x xsyn)
         (and* (gobj-syntactic-booleanp xsyn)
               (booleanp x)))))

(define gobj-non-integerp ((x gl-object-p))
  (gl-object-case x
    :g-boolean t
    :g-concrete (not (integerp x.val))
    :g-cons t
    :otherwise nil))

(define check-non-integerp (x xsyn)
  :verify-guards nil
  (and (gobj-non-integerp xsyn)
       (not (integerp x)))
  ///
  (defthm check-non-integerp-open
    (iff (check-non-integerp x xsyn)
         (and* (gobj-non-integerp xsyn)
               (not (integerp x))))))


(define gobj-non-booleanp ((x gl-object-p))
  (gl-object-case x
    :g-integer t
    :g-concrete (not (booleanp x.val))
    :g-cons t
    :otherwise nil))

(define check-non-booleanp (x xsyn)
  :verify-guards nil
  (and (gobj-non-booleanp xsyn)
       (not (booleanp x)))
  ///
  (defthm check-non-booleanp-open
    (iff (check-non-booleanp x xsyn)
         (and* (gobj-non-booleanp xsyn)
               (not (booleanp x))))))

(define gobj-non-consp ((x gl-object-p))
  (gl-object-case x
    :g-integer t
    :g-concrete (not (consp x.val))
    :g-boolean t
    :otherwise nil))

(define check-non-consp (x xsyn)
  :verify-guards nil
  (and (gobj-non-consp xsyn)
       (not (consp x)))
  ///
  (defthm check-non-consp-open
    (iff (check-non-consp x xsyn)
         (and* (gobj-non-consp xsyn)
               (not (consp x))))))



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
 :hints (("goal" :clause-processor (top-gl-interp-cp clause (default-glcp-config) state)
          :in-theory nil)))

(thm
 (if (and (unsigned-byte-p 10 x)
          (unsigned-byte-p 10 y))
     (unsigned-byte-p 10 (logand x y))
   t)
 :hints (("goal" :clause-processor (top-gl-interp-cp clause (default-glcp-config) state)
          :in-theory nil)))

(thm
 (if (and (unsigned-byte-p 50 x)
          (unsigned-byte-p 50 y))
     (unsigned-byte-p 50 (logand x y))
   t)
 :hints (("goal" :clause-processor (top-gl-interp-cp clause (default-glcp-config) state)
          :in-theory nil)))

(thm
 (if (and (unsigned-byte-p 90 x)
          (unsigned-byte-p 90 y))
     (unsigned-byte-p 90 (logand x y))
   t)
 :hints (("goal" :clause-processor (top-gl-interp-cp clause (default-glcp-config) state)
          :in-theory nil)))


;; (trace$ (top-gl-rewrite-try-rule
;;          :cond (equal (acl2::rewrite-rule->rune rule)
;;                       '(:rewrite fgl-equal-ints))))


