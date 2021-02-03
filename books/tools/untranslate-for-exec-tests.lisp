; Untranslate for Execution
; Copyright (C) 2015 Kestrel Institute (http://www.kestrel.edu)
;
; License: (An MIT license):
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
; Original authors: Jared Davis <jared@kookamara.com>

(in-package "ACL2")
(include-book "untranslate-for-exec")

(defmacro assert-same-stobjs-out (old-fn new-fn)
  `(make-event
    (b* ((world (w state))
         (old-stobjs-out (getprop ',old-fn 'acl2::stobjs-out nil 'acl2::current-acl2-world world))
         (new-stobjs-out (getprop ',new-fn 'acl2::stobjs-out nil 'acl2::current-acl2-world world))
         ((when (equal old-stobjs-out new-stobjs-out))
          (value '(value-triple :success))))
      (er soft ',new-fn
          "Stobjs-out mismatch: expected ~x0, found ~x1.~%"
          old-stobjs-out new-stobjs-out))))

(defun rebuild-function-fn (fn world)
  (b* ((new-fn (intern-in-package-of-symbol
                (concatenate 'string (symbol-name fn) "-NEW")
                fn))
       (new-fn-correct (intern-in-package-of-symbol
                        (concatenate 'string (symbol-name new-fn) "-CORRECT")
                        fn))
       (body       (getprop fn 'acl2::unnormalized-body nil 'acl2::current-acl2-world world))
       (formals    (getprop fn 'acl2::formals nil 'acl2::current-acl2-world world))
       (stobjs-out (getprop fn 'acl2::stobjs-out nil 'acl2::current-acl2-world world))
       (- (cw "Original body:  ~x0~%" body))
       ((mv errmsg new-body)
        (untranslate-for-execution body stobjs-out world))
       ((when errmsg)
        (er hard? 'rebuild-function "Error with untranslate-for-execution for ~x0: ~@1.~%"
            fn errmsg))
       (- (cw "Rewritten body: ~x0~%" new-body)))
    `(progn
       (defun ,new-fn ,formals
         ,new-body)
       (defthm ,new-fn-correct
         (equal (,new-fn . ,formals)
                (,fn . ,formals)))
       (assert-same-stobjs-out ,fn ,new-fn))))

(defmacro rebuild-function (fn)
  `(make-event
    (rebuild-function-fn ',fn (w state))))


;; Basic tests without much MV stuff.

(defun f1 () 5)
(rebuild-function f1)

(defun f2 (x) x)
(rebuild-function f2)

(defun f3 (x) (list x x))
(rebuild-function f3)

(defun f4 (x) (mv x x))
(rebuild-function f4)

(defun f5 (x) (let ((y x)) y))   ;; Basic non-MV lambda.
(rebuild-function f5)

(defun f6 (x) (let* ((y x)       ;; Nested non-MV lambdas.
                     (z y))
                (+ y z)))
(rebuild-function f6)

(defun f7 (x) (f4 x))   ;; Call of an MV function
(rebuild-function f7)

(defun f8 (x)  ;; IF with MVs in the branches
  (if x
      (f4 x)
    (mv x x)))
(rebuild-function f8)


(defun f9 (x)  ;; More IFs
  (cond
   ((equal x 1)
    (f4 x))
   ((equal x 2)
    (mv 1 2))
   (t
    (mv x 3))))

(rebuild-function f9)




;; ;; BOZO want to insert ignorable declarations as appropriate...

(set-ignore-ok t)

(defun f10 (x)  ;; IFs with Lambdas and MVs within MV-Lets.
  (cond
   ((equal x 1)
    (let ((x 1))
      (f4 x)))
   ((equal x 2)
    (mv-let (x y)
      (f4 6)
      (mv 1 2)))
   (t
    (mv x 3))))

(rebuild-function f10)


(defun f11 (x)
  (mv-let (a b c)
    (mv 1 2 x)
    (mv (+ a b c) x)))

(rebuild-function f11)



(defun f12 (x)
  (mv 1 2 x 3))

(rebuild-function f12)


(defun f13 (x y)
  (mv-let (a b)
    (mv y x)
    (mv a b x)))

(rebuild-function f13)

(defun f13 (x y)
  (mv-let (a b)
    (mv y x)
    (mv a b x)))

(rebuild-function f13)


(defun f14 (x y)
  (mv (mv-let (a b)
        (mv x y)
        (+ a b))
      y))

(rebuild-function f14)

(defun f14 (x y)
  (mv (mv-let (a b)
        (mv x y)
        (+ a b))
      y))

(rebuild-function f14)


(defun f15 (x y)
  (mv (mv-let (a b)
        (mv x y)
        (+ a b x))
      y))

(rebuild-function f15)


(defun f16 (x y)
  (let ((a (+ x y)))
    (mv-let (b c)
      (mv y x)
      (+ a b c))))

(rebuild-function f16)


(defun f17 (x y)
  (let ((a (+ x y)))
    (mv-let (a c)
      (mv y a)
      (+ a x c))))

(rebuild-function f17)


(defun f18 (x)
  ;; This one is special and has a different expansion: we end up with
  ;;   ((LAMBDA (MV X)
  ;;            ((LAMBDA (Y Z X) (CONS X (CONS Y 'NIL)))
  ;;             (MV-NTH '0 MV)
  ;;             (MV-NTH '1 MV)
  ;;             X))
  ;;    (F4 X)
  ;;  X)
  (mv-let (y z)
    (f4 x)
    (mv x y)))

(rebuild-function f18)

(defun f19 (x)
  (let ((y (f2 x)))
    (mv-let (y z)
      (f4 y)
      (mv-let (a b c)
        (mv z y x)
        (mv-let (w x y z)
          (f12 a)
          (mv a b c w x y z))))))

(rebuild-function f19)
