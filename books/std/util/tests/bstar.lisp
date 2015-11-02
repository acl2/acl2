; b* -- pluggable sequencing/binding macro thing
; Copyright (C) 2007-2014 Centaur Technology
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

(in-package "ACL2")
(include-book "../bstar")
(set-state-ok t)

(defun return-two-values (a b)
  (mv a b))

(defun transl-equal-tests-fn (tests)
  (if (atom tests)
      `(mv nil state)
    `(mv-let (err val state)
       (transl-equal ',(caar tests) ',(cadar tests))
       (if (or err (not val))
           (mv ',(car tests) state)
         ,(transl-equal-tests-fn (cdr tests))))))

(defmacro transl-equal-tests (&rest tests)
  (transl-equal-tests-fn tests))


(defstobj st1 (arr1 :type (array t (0)) :resizable t))
(defstobj st2 (arr2 :type (array t (0)) :resizable t))


(defun patbind-tests-fn (tests state)
  (declare (xargs :mode :program))
  (if (atom tests)
      (value '(value-triple :invisible))
    (mv-let (erp val state)
      (thm-fn `(equal ,(caar tests) ,(cadar tests))
              state '(("goal" :in-theory nil)) nil)
      (if erp
          (mv (msg "~% ****** ERROR ******~%~
Testing of the patbind macro failed on expression ~x0~%~%" (car tests))
              val state)
        (patbind-tests-fn (cdr tests) state)))))

(defmacro patbind-run-tests (&rest tests)
  `(make-event
    (patbind-tests-fn ',tests state)))
    ;;        (mv-let (err val state)
    ;;          (transl-equal-tests ,@tests)
    ;;          (declare (ignore val))
    ;;          (if err
    ;;              (mv t
    ;;                  (er hard? 'patbind-run-tests
    ;;                      "~% ****** ERROR ******~%~
    ;; Testing of the patbind macro failed on expression ~x0~%~%" err)
    ;;                  state)
    ;;            (value (prog2$ (cw "
    ;; Testing of the patbind macro passed.~%")
    ;;                           `(value-triple 'tests-ok)))))
    ;;        :check-expansion (value-triple 'tests-ok)))


(patbind-run-tests
 ;; TEST CASES

 ((patbind (cons (cons a b) c) (x) (list a b c))
  (let* ((|(CAR X)| (car x))
         (c (cdr x)))
    (let* ((a (car |(CAR X)|))
           (b (cdr |(CAR X)|)))
      (list a b c))))

 ((patbind x ((cons 'a 'b)) x)
  (let ((x (cons 'a 'b))) x))

 ((patbind (mv a b) ((mv 'a 'b)) (list a b))
  (mv-let (a b) (mv 'a 'b) (list a b)))

 ((patbind & ((cw "Hello")) nil)
  nil)

 ((patbind - ((cw "Hello")) nil)
  (prog2$ (cw "Hello")
          nil))

 ((patbind (cons a &) ('(a b)) a)
  (let ((a (car '(a b))))
    a))

 ((patbind (cons (cons a b) c) (x)
           (list a b c))
  (let ((|(CONS A B)| (car x))
        (c (cdr x)))
    (let ((a (car |(CONS A B)|))
          (b (cdr |(CONS A B)|)))
      (list a b c))))

 ((patbind (cons (cons a b) c) ((cons x y))
           (list a b c))
  (let ((|(CONS (CONS A B) C)| (cons x y)))
    (let ((|(CONS A B)| (car |(CONS (CONS A B) C)|))
          (c (cdr |(CONS (CONS A B) C)|)))
      (let ((a (car |(CONS A B)|))
            (b (cdr |(CONS A B)|)))
        (list a b c)))))

 ((patbind (cons (cons & b) c) ((cons x y))
           (list b c))
  (let ((|(CONS (CONS & B) C)| (cons x y)))
    (let ((|(CONS & B)| (car |(CONS (CONS & B) C)|))
          (c (cdr |(CONS (CONS & B) C)|)))
      (let ((b (cdr |(CONS & B)|)))
        (list b c)))))

 ((patbind (cons (cons a &) c) ((cons x y))
           (list a c))
  (let ((|(CONS (CONS A &) C)| (cons x y)))
    (let ((|(CONS A &)| (car |(CONS (CONS A &) C)|))
          (c (cdr |(CONS (CONS A &) C)|)))
      (let ((a (car |(CONS A &)|)))
        (list a c)))))


 ((patbind (mv (cons a (cons b c)) d)
           ((return-two-values x y))
           (list a b c d))
  (mv-let (|(CONS A (CONS B C))| d)
    (return-two-values x y)
    (let ((a (car |(CONS A (CONS B C))|))
          (|(CONS B C)|
           (cdr |(CONS A (CONS B C))|)))
      (let ((b (car |(CONS B C)|))
            (c (cdr |(CONS B C)|)))
        (list a b c d)))))

 ((patbind (mv (cons a (cons b c)) &)
           ((return-two-values x y))
           (list a b c d))
  (mv-let (|(CONS A (CONS B C))| ignore-0)
    (return-two-values x y)
    (declare (ignore ignore-0))
    (let ((a (car |(CONS A (CONS B C))|))
          (|(CONS B C)|
           (cdr |(CONS A (CONS B C))|)))
      (let ((b (car |(CONS B C)|))
            (c (cdr |(CONS B C)|)))
        (list a b c d)))))

 ((patbind (mv (cons a (cons & c)) &)
           ((return-two-values x y))
           (list a c d))
  (mv-let (|(CONS A (CONS & C))| ignore-0)
    (return-two-values x y)
    (declare (ignore ignore-0))
    (let ((a (car |(CONS A (CONS & C))|))
          (|(CONS & C)|
           (cdr |(CONS A (CONS & C))|)))
      (let ((c (cdr |(CONS & C)|)))
        (list a c d)))))

 ((patbind `(,a ,b) ((cons x y)) (list a b))
  (let ((|(CONS A (CONS B (QUOTE NIL)))| (cons x y)))
    (let ((a (car |(CONS A (CONS B (QUOTE NIL)))|))
          (|(CONS B (QUOTE NIL))|
           (cdr |(CONS A (CONS B (QUOTE NIL)))|)))
      (let ((b (car |(CONS B (QUOTE NIL))|)))
        (list a b)))))

 )

(defthm len-resize-list
  (equal (len (resize-list a b c))
         (nfix b)))

(defun localstobjtest (a b c)
  (declare (xargs :guard t))
  (b* ((d (cons b c))
       ((local-stobjs st1 st2)
        (mv g st2 h st1))
       (a (nfix a))
       (st1 (resize-arr1 (+ 1 a) st1))
       (st2 (resize-arr2 (+ 1 (nfix b)) st2))
       (st1 (update-arr1i a d st1))
       (st2 (update-arr2i (nfix b) a st2)))
    (mv (arr2i (nfix b) st2)
        st2
        (arr1i a st1)
        st1)))

(make-event
 (mv-let (res1 res2)
   (localstobjtest nil 10 'c)
   (if (and (equal res1 0)
            (equal res2 '(10 . c)))
       '(value-triple :passed)
     (er hard 'test-local-stobj
         "test failed"))))
