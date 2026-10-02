; Tests for annotate-c-locals
;
; Copyright (C) 2021-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)
; Supporting Author: Karthik Nukala (nukala@kestrel.edu)
; Supporting Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "../annotate-c-locals")
(include-book "kestrel/c/representation/integer-operations" :dir :system)
(include-book "kestrel/c/atc/arrays" :dir :system)
(include-book "kestrel/c/atc/pointed-integers" :dir :system)
(include-book "std/testing/must-be-redundant" :dir :system)
(include-book "kestrel/utilities/deftest" :dir :system)


;; Test exclusion of array write operators
(deftest
  (defun foo (i j x y arr)
    (let* ((arr (c::uchar-array-write arr i x))
           (x y)
           (arr (c::uchar-array-write arr j x)))
      arr))

  (annotate-c-locals foo :print :all)

  (must-be-redundant
   ;; Array writes are not wrapped with assign, as expected
   (DEFUN FOO$1 (I J X Y ARR)
     (DECLARE (XARGS :VERIFY-GUARDS NIL))
     (LET ((ARR (C::UCHAR-ARRAY-WRITE ARR I X)))
          (LET ((X (C::ASSIGN Y)))
               (LET ((ARR (C::UCHAR-ARRAY-WRITE ARR J X)))
                    ARR))))))


;; Test exclusion of array write operators
(deftest
  (defun foo (i j x y arr)
    (let* ((arr (c::uchar-array-write arr i x))
           (x y)
           (arr (c::uchar-array-write arr j x)))
      arr))

  (annotate-c-locals foo :print :all)

  (must-be-redundant
   ;; The deprecated array operators are also handled correctly
   (DEFUN FOO$1 (I J X Y ARR)
     (DECLARE (XARGS :VERIFY-GUARDS NIL))
     (LET ((ARR (C::UCHAR-ARRAY-WRITE ARR I X)))
          (LET ((X (C::ASSIGN Y)))
               (LET ((ARR (C::UCHAR-ARRAY-WRITE ARR J X)))
                    ARR))))))

;; Test exclusion of scalar write operators
(deftest
  (defun foo (x y)
    (declare (ignore x))
    (let ((x (c::uint-write y)))
      x))

  (annotate-c-locals foo :print :all)

  (must-be-redundant
   (DEFUN FOO$1 (X Y)
     (DECLARE (IGNORE X)
              (XARGS :VERIFY-GUARDS NIL))
     (LET ((X (C::UINT-WRITE Y))) X))))


;; Repeat occurences of variables
(deftest
  (defun foo (x)
    (let* ((y (c::add-sint-sint x x))
           (x (c::add-sint-sint y y))
           (y (c::add-sint-sint x x)))
      y))

  (annotate-c-locals foo :print :all)

  (must-be-redundant
   (DEFUN FOO$1 (X)
     (DECLARE (XARGS :VERIFY-GUARDS NIL))
     (LET ((Y (C::DECLAR (C::ADD-SINT-SINT X X)))) ; first ocurrence of y gets DECLAR
          (LET ((X (C::ASSIGN (C::ADD-SINT-SINT Y Y))))
               (LET ((Y (C::ASSIGN (C::ADD-SINT-SINT X X))))
                    Y))))))


;; If test with an mbt
(deftest
  (defun foo (x)
    (if (mbt t)
        (let* ((y (c::add-sint-sint x x))
               (x (c::add-sint-sint y y))
               (y (c::add-sint-sint x x)))
          y)
      (let* ((y (c::add-sint-sint x x))
               (x (c::add-sint-sint y y))
               (y (c::add-sint-sint x x)))
          y)))

  (annotate-c-locals foo :print :all)

  (must-be-redundant
   (DEFUN FOO$1 (X)
     (DECLARE (XARGS :VERIFY-GUARDS NIL))
     (IF (RETURN-LAST 'MBE1-RAW 'T 'T)
         ;; Only the mbt branch is annotated
         (LET ((Y (C::DECLAR (C::ADD-SINT-SINT X X))))
           (LET ((X (C::ASSIGN (C::ADD-SINT-SINT Y Y))))
             (LET ((Y (C::ASSIGN (C::ADD-SINT-SINT X X))))
               Y)))
       (LET ((Y (C::ADD-SINT-SINT X X)))
         (LET ((X (C::ADD-SINT-SINT Y Y)))
           (LET ((Y (C::ADD-SINT-SINT X X))) Y)))))))


;; Test unserialized lambdas
(deftest
  (defun foo (x)
    (let ((y (c::add-sint-sint x x))
          (x (c::uint-dec-const 0)))
      (c::add-sint-sint x y)))

  (annotate-c-locals foo :print :all)

  (must-be-redundant
   (DEFUN FOO$1 (X)
     (DECLARE (XARGS :VERIFY-GUARDS NIL))
     (LET ((Y (C::DECLAR (C::ADD-SINT-SINT X X)))
           (X (C::ASSIGN (C::UINT-DEC-CONST '0))))
       (C::ADD-SINT-SINT X Y)))))


;; Test let binding of an if statement
(deftest
  ;; Example taken from books/kestrel/c/atc/tests/assign.lisp
  (defun |j| (|x|)
    (declare
     (xargs
      :guard (c::sintp |x|)
      :guard-hints (("Goal" :in-theory (enable c::declar c::assign)))))
    (let ((|y| (c::sint-dec-const 0)))
      (let ((|y| (if (c::boolean-from-sint
                      (c::lt-sint-sint |x| (c::sint-dec-const 100)))
                     (let ((|y| (c::bitior-sint-sint
                                 |y|
                                 (c::sint-dec-const 6666))))
                       |y|)
                   (let ((|y| (c::bitxor-sint-sint
                               |y|
                               (c::sint-dec-const 7777))))
                     |y|))))
        (c::bitand-sint-sint |x| |y|))))

  (annotate-c-locals |j| :print :all)

  (must-be-redundant
   (DEFUN |j|$1 (|x|)
     (DECLARE
      (XARGS
       :GUARD (C::SINTP |x|)
       :GUARD-HINTS (("Goal" :IN-THEORY (ENABLE C::DECLAR C::ASSIGN)))))
     (LET ((|y| (C::DECLAR (C::SINT-DEC-CONST '0))))
          (LET ((|y| (IF (C::BOOLEAN-FROM-SINT
                          (C::LT-SINT-SINT |x| (C::SINT-DEC-CONST '100)))
                         (LET ((|y| (C::ASSIGN
                                     (C::BITIOR-SINT-SINT
                                      |y|
                                      (C::SINT-DEC-CONST '6666)))))
                              |y|)
                         (LET ((|y| (C::ASSIGN
                                     (C::BITXOR-SINT-SINT
                                      |y|
                                      (C::SINT-DEC-CONST '7777)))))
                              |y|))))
               (C::BITAND-SINT-SINT |x| |y|)))))

  ;; `mv` terms are not fully supported. Here we get a signature mismatch when
  ;; the `mv` is translated into a cons.
  ;; (defun |k| (|x| |y|)
  ;;   (declare
  ;;    (xargs :guard (and (c::sintp |x|)
  ;;                       (c::sintp |y|))
  ;;           :guard-hints (("Goal" :in-theory (enable c::declar c::assign)))))
  ;;   (let* ((|a| (c::lognot-sint |x|))
  ;;          (|b| (c::bitnot-sint |x|)))
  ;;     (mv-let (|a| |b|)
  ;;       (if (c::boolean-from-sint |y|)
  ;;           (let ((|a| (c::bitnot-sint |a|)))
  ;;             (mv |a| |b|))
  ;;         (let* ((|b| (c::sint-dec-const 2))
  ;;                (|a| (c::sint-dec-const 14)))
  ;;           (mv |a| |b|)))
  ;;       (c::bitxor-sint-sint |a| |b|))))

  ;; (annotate-c-locals |k| :print :all)
  )

;; Test bindings of calls representing loops
(deftest
  (encapsulate ()
    (local (include-book "kestrel/arithmetic-light/mod" :dir :system))
    (defun foo-loop (x)
      (declare (xargs :guard (c::uintp x)
                      :guard-hints
                      (("Goal" :in-theory (e/d (c::assign)
                                               ((:e c::uint-dec-const)))))
                      :measure (c::integer-from-uint x)
                      :hints
                      (("Goal" :in-theory (enable c::boolean-from-sint
                                                  c::lt-uint-uint
                                                  c::uint-dec-const
                                                  c::assign
                                                  c::sub-uint-uint
                                                  c::integer-from-uint
                                                  c::uint-from-integer-mod
                                                  c::uint-max
                                                  c::int-bits
                                                  c::uint-integer-fix)))
                      ))
      (if (c::boolean-from-sint (c::lt-uint-uint (c::uint-dec-const 0) x))
          (let ((x (c::assign (c::sub-uint-uint x (c::uint-dec-const 1)))))
            (foo-loop x))
        x)))

  (defun foo ()
    (declare (xargs :guard t))
    (let* ((x (c::uint-dec-const 10))
           (x (foo-loop x)))
      (c::bitnot-uint x)))

  (annotate-c-locals foo :print :all)

  (must-be-redundant
   (DEFUN FOO$1 ()
     (DECLARE (XARGS :GUARD T))
     (LET ((X (C::DECLAR (C::UINT-DEC-CONST '10))))
          (LET ((X (FOO-LOOP X)))
               (C::BITNOT-UINT X))))))


;; Test bindings of calls representing loops with multiple variables
(deftest
  (encapsulate ()
    (local (include-book "kestrel/arithmetic-light/mod" :dir :system))
    (defun foo-loop (x y)
      (declare (xargs :guard (and (c::uintp x)
                                  (c::uintp y))
                      :guard-hints
                      (("Goal" :in-theory (e/d (c::assign)
                                               ((:e c::uint-dec-const)))))
                      :measure (c::integer-from-uint x)
                      :hints
                      (("Goal" :in-theory (enable c::boolean-from-sint
                                                  c::lt-uint-uint
                                                  c::uint-dec-const
                                                  c::assign
                                                  c::sub-uint-uint
                                                  c::integer-from-uint
                                                  c::uint-from-integer-mod
                                                  c::uint-max
                                                  c::int-bits
                                                  c::uint-integer-fix)))
                      ))
      (if (c::boolean-from-sint (c::lt-uint-uint (c::uint-dec-const 0) x))
          (let ((x (c::assign (c::sub-uint-uint x (c::uint-dec-const 1))))
                (y (c::assign (c::bitnot-uint y))))
            (foo-loop x y))
        (mv x y))))

  (defun foo ()
    (declare (xargs :guard t))
    (let* ((x (c::uint-dec-const 10))
           (y (c::uint-dec-const 42)))
      (mv-let (x y)
        (foo-loop x y)
        (c::add-uint-uint x y))))

  (annotate-c-locals foo :print :all)

  (must-be-redundant
   (DEFUN FOO$1 ()
     (DECLARE (XARGS :GUARD T))
     (LET ((X (C::DECLAR (C::UINT-DEC-CONST '10))))
       (LET ((Y (C::DECLAR (C::UINT-DEC-CONST '42))))
         (MV-LET (X Y)
           (FOO-LOOP X Y)
           (C::ADD-UINT-UINT X Y)))))))


;; Test void function call
(deftest
  (defun add-one (x)
    (declare (xargs :guard (c::star (c::uintp x))
                    :guard-hints (("Goal" :in-theory (enable c::declar)))))
    (let* ((x (c::uint-write (c::add-uint-uint (c::uint-read x)
                                               (c::uint-dec-const 1)))))
      x))

  (defun foo (x y)
    (declare (xargs :guard (and (c::star (c::uintp x))
                                (c::star (c::uintp y)))))
    (let ((x (add-one x)))
      (mv x y)))

  (annotate-c-locals foo :print :all)

  (must-be-redundant
   (DEFUN FOO$1 (X Y)
     (DECLARE (XARGS :GUARD (AND (C::STAR (C::UINTP X))
                                 (C::STAR (C::UINTP Y)))))
     (LET ((X (ADD-ONE X)))
          (MV X Y)))))


;; Test another void function call
(deftest
  ;; Subroutine #1 (will be void).
  (defun inc (x result)
    (declare (xargs :guard (and (c::uintp x)
                                (c::star (c::uintp result))))
             (ignore result))
    (let ((result (c::uint-write (c::add-uint-uint (c::uint-dec-const 1) x))))
      result))

  ;; Caller #1.  No ASSIGN allowed or needed here.
  (defun inc_wrapper (x result)
    (declare (xargs :guard (and (c::uintp x)
                                (c::star (c::uintp result)))))
    (let ((result (inc x result)))
      result))

  (annotate-c-locals inc_wrapper :print :all)

  (must-be-redundant
   (defun inc_wrapper$1 (x result)
     (declare (xargs :guard (and (c::uintp x)
                                 (c::star (c::uintp result)))))
     (let ((result (inc x result)))
       result))))


;; Test mv-let support
(deftest
  (defun add-and-swap (x y)
    (declare (xargs :guard (and (c::star (c::uintp x))
                                (c::star (c::uintp y)))
                    :guard-hints (("Goal" :in-theory (enable c::declar)))))
    (let* ((temp (c::declar (c::uint-read x)))
           (x (c::uint-write (c::uint-read y)))
           (y (c::uint-write temp)))
      (mv (c::add-uint-uint x y) x y)))

  (defun foo (x y)
    (declare (xargs :guard (and (c::star (c::uintp x))
                                (c::star (c::uintp y)))))
    (mv-let (ret x y)
      (add-and-swap x y)
      (mv (c::add-uint-uint ret x) x y)))

  (annotate-c-locals foo :print :all)

  (must-be-redundant
   (DEFUN FOO$1 (X Y)
     (DECLARE (XARGS :GUARD (AND (C::STAR (C::UINTP X))
                                 (C::STAR (C::UINTP Y)))))
     (MV-LET (RET X Y)
       (C::DECLAR2 (ADD-AND-SWAP X Y))
       (MV (C::ADD-UINT-UINT RET X) X Y)))))


;; Test mv-let support with void function
(deftest
  (defun swap-uints (x y)
    (declare (xargs :guard (and (c::star (c::uintp x))
                                (c::star (c::uintp y)))
                    :guard-hints (("Goal" :in-theory (enable c::declar)))))
    (let* ((temp (c::declar (c::uint-read x)))
           (x (c::uint-write (c::uint-read y)))
           (y (c::uint-write temp)))
      (mv x y)))

  (defun foo (x y)
    (declare (xargs :guard (and (c::star (c::uintp x))
                                (c::star (c::uintp y)))))
    (mv-let (x y)
      (swap-uints x y)
      (mv (c::add-uint-uint x y) x y)))

  (annotate-c-locals foo :print :all)

  (must-be-redundant
   (DEFUN FOO$1 (X Y)
     (DECLARE (XARGS :GUARD (AND (C::STAR (C::UINTP X))
                                 (C::STAR (C::UINTP Y)))))
     (MV-LET (X Y)
       (SWAP-UINTS X Y)
       (MV (C::ADD-UINT-UINT X Y) X Y)))))


;; Test mv-let with ignored variable
(deftest
  (defun swap-uints (x y)
    (declare (xargs :guard (and (c::star (c::uintp x))
                                (c::star (c::uintp y)))
                    :guard-hints (("Goal" :in-theory (enable c::declar)))))
    (let* ((temp (c::declar (c::uint-read x)))
           (x (c::uint-write (c::uint-read y)))
           (y (c::uint-write temp)))
      (mv x y)))

  (defun foo (x y)
    (declare (xargs :guard (and (c::star (c::uintp x))
                                (c::star (c::uintp y)))))
    (mv-let (x y)
      (swap-uints x y)
      (declare (ignore x y))
      (let ((x (c::uint-write (c::uint-dec-const 0)))
            (y (c::uint-write (c::uint-dec-const 0))))
        (mv x y))))

  (annotate-c-locals foo :print :all)

  (must-be-redundant
   (DEFUN FOO$1 (X Y)
     (DECLARE (XARGS :GUARD (AND (C::STAR (C::UINTP X))
                                 (C::STAR (C::UINTP Y)))))
     (MV-LET (X Y)
       (SWAP-UINTS X Y)
       (DECLARE (IGNORE X Y))
       (LET ((X (C::UINT-WRITE (C::UINT-DEC-CONST '0)))
             (Y (C::UINT-WRITE (C::UINT-DEC-CONST '0))))
         (MV X Y))))))
