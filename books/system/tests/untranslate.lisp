; Copyright (C) 2018, Regents of the University of Texas
; Written by Matt Kaufmann and J Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "std/testing/assert-bang" :dir :system)

;;; cw

(assert!
 (equal
  (untranslate
   '(FMT-TO-COMMENT-WINDOW
     '"Hello ~x0 ~x1"
     (PAIRLIS2 '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9)
               (CONS A (CONS B 'NIL)))
     '0
     'NIL
     'NIL)
   nil (w state))
  '(CW "Hello ~x0 ~x1" A B)))

(assert!
 (equal
  (untranslate
   '(FMT-TO-COMMENT-WINDOW '"Hello ~x0 ~x1"
                           (PAIRLIS2 '(#\0 #\1 #\2 #\3)
                                     (CONS A (CONS B 'NIL)))
                           '0
                           'NIL
                           'NIL)
   nil (w state))
  '(FMT-TO-COMMENT-WINDOW "Hello ~x0 ~x1"
                          (PAIRLIS2 '(#\0 #\1 #\2 #\3) (LIST A B))
                          0 NIL NIL)))

(assert!
 (equal
  (untranslate
   '(FMT-TO-COMMENT-WINDOW
     '"Hello ~x0 ~x1"
     (PAIRLIS2 '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9)
               (CONS A (CONS 'B 'NIL)))
     '0
     'NIL
     'NIL)
   nil (w state))
  '(CW "Hello ~x0 ~x1" A 'B)))

(assert!
 (equal
  (untranslate
   '(FMT-TO-COMMENT-WINDOW
     '"Hello ~x0 ~x1"
     (PAIRLIS2 '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9)
               (CONS A (CONS 'B 'NIL)))
     '0
     'NIL
     'NIL)
   nil (w state))
  '(CW "Hello ~x0 ~x1" A 'B)))

(assert!
 (equal
  (untranslate
   '(FMT-TO-COMMENT-WINDOW '"Hello ~x0 ~x1"
                           (PAIRLIS2 '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9)
                                     (CONS 'A '(b)))
                           '0
                           'NIL
                           'NIL)
   nil (w state))
  '(CW "Hello ~x0 ~x1" 'A 'B)))

(assert!
 (equal
  (untranslate
   '(FMT-TO-COMMENT-WINDOW
     '"Hello ~x0 ~x1"
     (PAIRLIS2 '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9)
               '(a b))
     '0
     'NIL
     'NIL)
   nil (w state))
  '(CW "Hello ~x0 ~x1" 'A 'B)))

(assert!
 (equal
  (untranslate
   '(FMT-TO-COMMENT-WINDOW
     '"Hello ~x0 ~x1"
     (PAIRLIS2 '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9)
               '(a b c))
     '0
     'NIL
     'NIL)
   nil (w state))
  '(CW "Hello ~x0 ~x1" 'A 'B 'C)))

(assert!
 (equal
  (untranslate
   '(FMT-TO-COMMENT-WINDOW
     '"Hello ~x0 ~x1"
     (PAIRLIS2 '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9)
               `(a b ,c))
     '0
     'NIL
     'NIL)
   nil (w state))
  '(CW "Hello ~x0 ~x1" 'A 'B C)))

(assert!
 (equal
  (untranslate
   '(FMT-TO-COMMENT-WINDOW
     '"Hello ~x0 ~x1"
     (PAIRLIS2 '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9)
               (CONS 'A (CONS 'B 'NIL)))
     '0
     'NIL
     'NIL)
   nil (w state))
  '(CW "Hello ~x0 ~x1" 'A 'B)))

(assert!
 (equal
  (untranslate
   '(FMT-TO-COMMENT-WINDOW
     '"Hello ~x0 ~x1"
     (cons '(#\0 . a)
           (PAIRLIS2 '(#\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9)
                     `(b ,c)))
     '0
     'NIL
     'NIL)
   nil (w state))
  '(CW "Hello ~x0 ~x1" 'A 'B C)))

(assert!
 (equal
  (untranslate
   '(FMT-TO-COMMENT-WINDOW '"Hello ~x0 ~x1"
                           (cons '(#\7 . a)
                                 (PAIRLIS2 '(#\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9)
                                           `(b ,c)))
                           '0
                           'NIL
                           'NIL)
   nil (w state))
  '(FMT-TO-COMMENT-WINDOW
    "Hello ~x0 ~x1"
    (cons '(#\7 . a)
          (PAIRLIS2 '(#\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9)
                    (list 'b c)))
    0 NIL NIL)))

(assert!
 (equal
  (untranslate
   '(FMT-TO-COMMENT-WINDOW '"hello ~x0 ~x1~%"
                           '((#\0 . X) (#\1 . Y))
                           '0
                           'NIL
                           'NIL)
   nil (w state))
  '(CW "hello ~x0 ~x1~%" 'X 'Y)))

;;; cw!

(assert!
 (equal
  (untranslate
   '(FMT-TO-COMMENT-WINDOW!
     '"Hello ~x0 ~x1"
     (PAIRLIS2 '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9)
               (CONS A (CONS B 'NIL)))
     '0
     'NIL
     'NIL)
   nil (w state))
  '(CW! "Hello ~x0 ~x1" A B)))

;;; cw-print-base-radix

(assert!
 (equal
  (untranslate
   '(FMT-TO-COMMENT-WINDOW '"~x0~%"
                           (PAIRLIS2 '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9)
                                     (CONS '(3 12 16 17) 'NIL))
                           '0
                           'NIL
                           '16)
   nil (w state))
  '(cw-print-base-radix 16 "~x0~%" '(3 12 16 17))))

(assert!
 (equal
  (untranslate
   '(FMT-TO-COMMENT-WINDOW '"~x0~%"
                           '((#\0 . (3 12 16 17)))
                           '0
                           'NIL
                           '16)
   nil (w state))
  '(cw-print-base-radix 16 "~x0~%" '(3 12 16 17))))

;;; cw-print-base-radix!

(assert!
 (equal
  (untranslate
   '(FMT-TO-COMMENT-WINDOW! '"~x0~%"
                            (PAIRLIS2 '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9)
                                      (CONS '(3 12 16 17) 'NIL))
                            '0
                            'NIL
                            '16)
   nil (w state))
  '(cw-print-base-radix! 16 "~x0~%" '(3 12 16 17))))

(assert!
 (equal
  (untranslate
   '(FMT-TO-COMMENT-WINDOW! '"~x0~%"
                            '((#\0 . (3 12 16 17)))
                            '0
                            'NIL
                            '16)
   nil (w state))
  '(cw-print-base-radix! 16 "~x0~%" '(3 12 16 17))))

;;; time$

(assert!
 (equal
  (untranslate
   '(RETURN-LAST 'TIME$1-RAW
                 (CONS '0
                       (CONS 'NIL
                             (CONS 'NIL
                                   (CONS 'NIL (CONS 'NIL 'NIL)))))
                 (CONS X Y))
   nil (w state))
  '(time$ (cons x y))))

(assert!
 (equal
  (untranslate
   '(RETURN-LAST 'TIME$1-RAW
                 (CONS '0
                       (CONS 'NIL
                             (CONS 'NIL
                                   (CONS '"Hello ~s0, ~s1 World."
                                         (CONS (CONS '"Moon" (CONS '"Goodbye" 'NIL))
                                               'NIL)))))
                 (CONS X '17))
   nil (w state))
  '(time$ (cons x 17)
          :msg "Hello ~s0, ~s1 World."
          :args (list "Moon" "Goodbye"))))

(assert! ; Example from Eric Smith
 (equal
  (untranslate
   '(RETURN-LAST 'TIME$1-RAW
                 '(0 NIL NIL "~t0 seconds" (38))
                 (LEN X))
   nil (w state))
  '(time$ (len x)
          :msg "~t0 seconds"
          :args '(38))))

(assert!
 (equal
  (untranslate
   '(RETURN-LAST 'TIME$1-RAW
                 (CONS '23
                       (CONS 'NIL
                             (CONS 'NIL
                                   (CONS 'NIL (CONS 'NIL 'NIL)))))
                 (CONS X Y))
   nil (w state))
  '(time$ (cons x y) :real-mintime 23)))

(assert!
 (equal
  (untranslate '(FMT-TO-COMMENT-WINDOW
                 '"   ~x0 pairs~%"
                 (PAIRLIS2
                  '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9)
                  (CONS
                   (LEN (RETURN-LAST 'TIME$1-RAW
                                     '(0 NIL NIL
                                         "Value is: ~x0"
                                         (100))
                                     (cons x y)))
                   'NIL))
                 '0 'NIL 'NIL)
               nil (w state))
  '(cw "   ~x0 pairs~%"
       (len (time$ (cons x y)
                   :msg "Value is: ~x0"
                   :args '(100))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Next we test that untranslate does a reasonable job of
;;; preserving executability, especially with respect to mv,
;;; ignore declarations, and type declarations.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Note that there is no effort made by ACL2 for untranslate to preserve
; ignorable declarations.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Testing utilities
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun untrans-trans (form maybe-convert-to-mv state)
  (declare (xargs :mode :program :stobjs state))
  (let ((wrld (w state)))
    (mv-let (erp trans bindings state)
      (translate1 form
                  :stobjs-out
                  '((:stobjs-out . :stobjs-out))
                  t
                  'check-untrans-trans wrld state)
      (declare (ignore bindings))
      (cond (erp (silent-error state)) ; error already reported above
            (t (value
                (let ((untrans (untranslate trans nil wrld)))
                  (cond (maybe-convert-to-mv (maybe-convert-to-mv untrans))
                        (t untrans)))))))))

(defun check-untrans-trans-fn (form expected maybe-convert-to-mv state)
  (declare (xargs :mode :program :stobjs state))
  (er-let* ((untrans-trans (untrans-trans form maybe-convert-to-mv state)))
    (value `(assert-event (equal ',expected ',untrans-trans)))))

(defmacro check-untrans-trans (form &key expected maybe-convert-to-mv)
  (declare (xargs :guard (booleanp maybe-convert-to-mv)))
  (let ((expected (or expected form)))
    `(make-event
      (check-untrans-trans-fn ',form ',expected ,maybe-convert-to-mv state))))

(make-event
 (er-progn (set-evisc-tuple nil :iprint :same :sites :abbrev)
           (value '(value-triple :abbrev-evisc-tuple-set-to-nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; MV-LET: preserve mv and
;;; ignore, type declarations
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(check-untrans-trans
 (mv-let (x y)
   (mv b c)
   (cons x y)))

(check-untrans-trans
 (mv-let (x y)
   (mv b c)
   (declare (type integer x y))
   (cons x y)))

(check-untrans-trans
; As above, but different types.
 (mv-let (x y)
   (mv b c)
   (declare (type integer x)
            (type symbol y))
   (cons x y)))

(check-untrans-trans
; As above, but different types in different declare forms.
 (mv-let (x y)
   (mv b c)
   (declare (type integer x))
   (declare (type symbol y))
   (cons x y))
 :expected
 (mv-let (x y)
   (mv b c)
   (declare (type integer x)
            (type symbol y))
   (cons x y)))

(check-untrans-trans ; courtesy of Alessandro Coglio
 (mv-let (x y)
   (if a (mv b c) (mv d e))
   (cons x y)))

(check-untrans-trans
; As above, but with a type declaration.
 (mv-let (x y)
   (if a (mv b c) (mv d e))
   (declare (type integer x))
   (cons x y)))

(check-untrans-trans
; As above, but with different type declarations.
 (mv-let (x y)
   (if a (mv b c) (mv d e))
   (declare (type integer x)
            (type symbol y))
   (cons x y)))

(check-untrans-trans
 (mv-let (x y)
   (let ((c (car a))) (mv b c))
   (cons x y)))

(check-untrans-trans
; As above, but with type declarations.
 (mv-let (x y)
   (let ((c (car a))) (mv b c))
   (declare (type integer x)
            (type symbol y))
   (cons x y)))

(check-untrans-trans
 (mv-let (x y)
   (let* ((c (car a)) (d (cdr a))) (mv c d))
   (cons x y)))

(check-untrans-trans
 (mv-let (x y)
   (prog2$ a (mv b c))
   (cons x y)))

(check-untrans-trans
; As above, but with type declarations.
 (mv-let (x y)
   (prog2$ a (mv b c))
   (declare (type symbol y)
            (type integer x))
   (cons x y)))

(check-untrans-trans
 (mv-let (x y)
   (if a (mv b (prog2$ (cw "hi") c)) (mv d e))
   (declare (type symbol y)
            (type integer x))
   (cons x y)))

(check-untrans-trans
 (mv-let (x y)
   (mv (cons a a) 17)
   (declare (ignore y))
   (car x)))

(check-untrans-trans
 (mv-let (x y)
   (mv (cons a a) 17)
   (declare (ignore y)
            (type integer x))
   (car x)))

(check-untrans-trans
; variant of the preceding
 (mv-let (x y)
   (mv (cons a a) 17)
   (declare (type integer x)
            (ignore y))
   (car x))
 :expected
 (mv-let (x y)
   (mv (cons a a) 17)
   (declare (ignore y)
            (type integer x))
   (car x)))

(check-untrans-trans
; (another) variant of the preceding
 (mv-let (x y)
   (mv (cons a a) 17)
   (declare (type integer x))
   (declare (ignore y))
   (car x))
 :expected
 (mv-let (x y)
   (mv (cons a a) 17)
   (declare (ignore y)
            (type integer x))
   (car x)))

(check-untrans-trans
 (mv-let (x y)
   (if a (mv b (prog2$ (cw "hi") c)) (mv d e))
   (declare (type cons y)
            (type (integer 0 *) x))
   (mbt (mv-let (a z)
          (mv w (ec-call (nth x (mv-let (r s)
                                  (mv y y)
                                  (declare (type cons r s))
                                  (append r s)))))
          (list a z)))))

(check-untrans-trans
 (mv-let (x y)
   (mbe :logic (mv p (append (list x) y)) :exec (mv p (cons x y)))
   (cons x y)))

(check-untrans-trans
 (mv-let (x y)
   (if a (mv b (prog2$ (cw "hi") c)) (mv d e))
   (declare (type cons y)
            (type (integer 0 *) x))
   (mbt (mv-let (a z)
          (mv w (ec-call (nth x (mv-let (r s)
                                  (mv y y)
                                  (declare (type cons r s))
                                  (append r s)))))
          (list a z)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; ACL2 vs. ACL2(r)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(check-untrans-trans

; The indicated type translates to a rationalp call in ACL2 and a realp call in
; ACL2(r).  Untranslating back to ACL2 gives a rational type, but in ACL2(r) we
; get back a real type.

 (mv-let (x y)
   (if a (mv b (prog2$ (cw "hi") c)) (mv d e))
   (declare (type real y))
   (cons x y))
 #-non-standard-analysis
 :expected
 #-non-standard-analysis
 (mv-let (x y)
   (if a (mv b (prog2$ (cw "hi") c)) (mv d e))
   (declare (type rational y))
   (cons x y)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; LET: preserve ignore,
;;; type declarations
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(check-untrans-trans
 (let ((x a) (y b))
   (declare (ignore y))
   (cons x x)))

(check-untrans-trans
 (let ((x a) (y b))
   (declare (type (integer -10 20) x))
   (cons x y)))

(check-untrans-trans
 (let* ((x a) (y b))
   (declare (type (integer -10 20) x))
   (cons x y)))

(check-untrans-trans
 (let ((x a) (y b))
   (declare (ignore y)
            (type (integer -10 20) x))
   (cons x x)))

(check-untrans-trans
 (let ((x a) (y b))
   (declare (ignore y)
            (type (and (rational 5/2 30)
                       (integer -10 20))
                  x))
   (prog2$ (cw "hi") (cons x x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Call maybe-convert-to-mv explicitly
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; First we note that mv isn't preserved in general -- only in an MV-LET body
; (see earlier tests above).

(check-untrans-trans
 (let ((x a) (y b))
   (declare (ignore y)
            (type (and (rational 5/2 30)
                       (integer -10 20))
                  x))
   (prog2$ (cw "hi") (mv x x)))
 :expected
 (let ((x a) (y b))
   (declare (ignore y)
            (type (and (rational 5/2 30)
                       (integer -10 20))
                  x))
   (prog2$ (cw "hi") (list x x))))

; But if we wrap maybe-convert-to-mv around the untranslation, then we get an
; mv call.

(check-untrans-trans
 (let ((x a) (y b))
   (declare (ignore y)
            (type (and (rational 5/2 30)
                       (integer -10 20))
                  x))
   (prog2$ (cw "hi") (mv x x)))
 :maybe-convert-to-mv t)

(check-untrans-trans
; same as just above, but with let* instead of let
 (let* ((x a) (y b))
   (declare (ignore y)
            (type (and (rational 5/2 30)
                       (integer -10 20))
                  x))
   (prog2$ (cw "hi") (mv x x)))
 :maybe-convert-to-mv t)
