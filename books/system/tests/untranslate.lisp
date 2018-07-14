; Copyright (C) 2018, Regents of the University of Texas
; Written by Matt Kaufmann and J Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "misc/assert" :dir :system)

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
