; Tests of remove-nesting
;
; Copyright (C) 2021-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "../remove-nesting")

(include-book "std/testing/assert-equal" :dir :system)
(include-book "kestrel/utilities/deftest" :dir :system)

;; Simple test: Remove nested calls to WR:
(assert-equal
 (remove-nesting-in-body '(wr a
                              aval
                              (wr b
                                  bval
                                  arr))
                         'wr
                         3)
 '(LET* ((ARR (WR B BVAL ARR))
         (ARR (WR A AVAL ARR)))
        ARR))

(assert-equal
 (remove-nesting-in-body '(if t1
                              (wr a
                                  aval
                                  (wr b
                                      bval
                                      arr))
                            (wr c
                                cval
                                (wr d
                                    dval
                                    arr)))
                         'wr
                         3)
 '(if t1
      (LET* ((ARR (WR B BVAL ARR))
             (ARR (WR A AVAL ARR)))
            ARR)
    (LET* ((ARR (WR d dVAL ARR))
           (ARR (WR c cVAL ARR)))
          ARR)))


;; simple test with different write function name
(assert-equal
 (remove-nesting-in-body '(write a
                                 aval
                                 (write b
                                        bval
                                        arr))
                         'write
                         3)
 '(LET* ((ARR (WRITE B BVAL ARR))
         (ARR (WRITE A AVAL ARR)))
        ARR))

(assert-equal
 (remove-nesting-in-body '(wr a
                              aval
                              (wr b
                                  bval
                                  (wr c
                                      cval
                                      arr)))
                         'wr
                         3)
 '(LET* ((ARR (WR C CVAL ARR))
         (ARR (WR B BVAL ARR))
         (ARR (WR A AVAL ARR)))
        ARR))

;;A test where another arg of a write depends on arr
(assert-equal
 (remove-nesting-in-body '(wr a
                              aval
                              (wr (i arr)
                                  bval
                                  (wr c
                                      cval
                                      arr)))
                         'wr
                         3)
 '(LET* ((X (I ARR))
         (ARR (WR C CVAL ARR))
         (ARR (WR X BVAL ARR))
         (ARR (WR A AVAL ARR)))
        ARR))

;;A test where a different arg of a write depends on arr
(assert-equal
 (remove-nesting-in-body '(wr a
                              (v arr)
                              (wr b
                                  bval
                                  (wr c
                                      cval
                                      arr)))
                         'wr
                         3)
 '(LET* ((X (V ARR))
         (ARR (WR C CVAL ARR))
         (ARR (WR B BVAL ARR))
         (ARR (WR A X ARR)))
        ARR))

;; a test where the array arg comes first
(assert-equal
 (remove-nesting-in-body '(wr (wr arr
                                  b
                                  bval)
                              a
                              aval)
                         'wr
                         1)
 '(LET* ((ARR (WR ARR B BVAL))
         (ARR (WR ARR A AVAL)))
        ARR))



;; Tests of the whole transformation

(deftest
  (defstub wr (x y z) t)
  (defun foo (a aval b bval arr)
    (wr a
        aval
        (wr b
            bval
            arr)))
  (remove-nesting foo wr 3)
  (must-be-redundant
   (DEFUN FOO$1 (A AVAL B BVAL ARR)
     (DECLARE (XARGS :VERIFY-GUARDS NIL))
     (LET* ((ARR (WR B BVAL ARR))
            (ARR (WR A AVAL ARR)))
           ARR))
   (DEFTHM FOO-BECOMES-FOO$1
     (EQUAL (FOO A AVAL B BVAL ARR)
            (FOO$1 A AVAL B BVAL ARR)))))

;; Test of a single write
;; TODO: Should this work? There is no nesting, but we want the LET. See let-bind-writes.
;; (deftest
;;   (defstub wr (x y z) t)
;;   (defun foo (a aval arr)
;;     (wr a aval arr))
;;   (remove-nesting foo wr 3)
;;   (must-be-redundant
;;    (DEFUN FOO$1 (A AVAL ARR)
;;      (DECLARE (XARGS :VERIFY-GUARDS NIL))
;;      (LET* ((ARR (WR A AVAL ARR)))
;;            ARR))
;;    (DEFTHM FOO-BECOMES-FOO$1
;;      (EQUAL (FOO A AVAL ARR)
;;             (FOO$1 A AVAL ARR)))))

;; Test when the nested writes are in a lambda arg (and thus are not at the
;; top-level of the body).
(deftest
  (defstub wr (x y z) t)
  (defstub bar (x) t)
  (defun foo (a aval b bval arr)
    (let ((arr (wr a
                   aval
                   (wr b
                       bval
                       arr))))
      (bar arr)))
  (remove-nesting foo wr 3)
  ;; Expected results:
  (must-be-redundant
   (defun foo$1 (a aval b bval arr)
     (declare (xargs :verify-guards nil))
     (let* ((arr (wr b bval arr))
            (arr (wr a aval arr)))
       (bar arr)))
   (defthm foo-becomes-foo$1
     (equal (foo a aval b bval arr)
            (foo$1 a aval b bval arr)))))

;; We may also wish to unnest write terms appearing as arguments:
;; (Currently unsupported)
(deftest
  (defstub wr (x y z) t)
  (defstub bar (x) t)
  (defun foo (a aval b bval arr)
    (bar (wr a
             aval
             (wr b
                 bval
                 arr))))
  (remove-nesting foo wr 3)
  ;; Expected:
  ;; (must-be-redundant
  ;;  (defun foo$1 (a aval b bval arr)
  ;;    (let* ((arr (wr b bval arr))
  ;;           (arr (wr a aval arr)))
  ;;      (bar arr)))
  )

;; When the nested write term occurs in a let binding, we use the name of the formal
;; as opposed to the name of the original array variable:
;; TODO: This currently causes an error, as the inner array "arr" is replaced with
;; "baz", which does not exist.
(deftest
  (defstub wr (x y z) t)
  (defstub bar (x) t)
  (defun foo (a aval b bval arr)
    (let ((baz (wr a
                   aval
                   (wr b
                       bval
                       arr))))
      (bar baz)))
  ;; (remove-nesting foo wr 3)
  ;; Expected results:
  ;; (must-be-redundant
  ;;  (defun foo$1 (a aval b bval arr)
  ;;    (declare (xargs :verify-guards nil))
  ;;    (let* ((baz (wr b bval arr))
  ;;           (baz (wr a aval arr)))
  ;;      (bar baz)))
  ;;  (defthm foo-becomes-foo$1
  ;;    (equal (foo a aval b bval arr)
  ;;           (foo$1 a aval b bval arr))))
  )

;; Test multiple (unserialized) let-bindings, where only one contains a nested write term
(deftest
  (defstub wr (x y z) t)
  (defstub bar (x y z) t)
  (defun foo (a aval b bval arr)
    (let ((x 0))
      (let ((arr (wr a aval (wr b bval arr))))
        (let ((y 1)) (bar x arr y)))))
  (remove-nesting foo wr 3)
  (must-be-redundant
   (defun foo$1 (a aval b bval arr)
     (declare (xargs :verify-guards nil))
     ((lambda (x arr bval b aval a)
        (let* ((arr (wr b bval arr))
               (arr (wr a aval arr)))
          ((lambda (y arr x) (bar x arr y))
           '1
           arr x)))
      '0
      arr bval b aval a))
   (defthm foo-becomes-foo$1
     (equal (foo a aval b bval arr)
            (foo$1 a aval b bval arr)))))

;; Test multiple (unserialized) let-bindings, where only one contains a nested write term:
;; (Currently unsupported)
(deftest
  (defstub wr (x y z) t)
  (defstub bar (x y z) t)
  (defun foo (a aval b bval arr)
    (let ((x 0)
          (arr (wr a
                   aval
                   (wr b
                       bval
                       arr)))
          (y 1))
      (bar x arr y)))
  (remove-nesting foo wr 3)
  ;; ;; Expected results:
  ;; (must-be-redundant
  ;;  (defun foo$1 (a aval b bval arr)
  ;;    (declare (xargs :verify-guards nil))
  ;;    (let* ((x 0)
  ;;           (arr (wr b bval arr))
  ;;           (arr (wr a aval arr))
  ;;           (y 1))
  ;;      (bar x arr y)))
  ;;  (defthm foo-becomes-foo$1
  ;;    (equal (foo a aval b bval arr)
  ;;           (foo$1 a aval b bval arr))))
  )
