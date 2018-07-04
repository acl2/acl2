; Copyright (C) 2018, Regents of the University of Texas
; Written by Matt Kaufmann and J Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "misc/assert" :dir :system)

(assert!
 (equal
  (untranslate
   '(FMT-TO-COMMENT-WINDOW
     '"Hello ~x0 ~x1"
     (PAIRLIS2 '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9)
               (CONS A (CONS B 'NIL)))
     '0
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
                           'NIL)
   nil (w state))
  '(FMT-TO-COMMENT-WINDOW "Hello ~x0 ~x1"
                          (PAIRLIS2 '(#\0 #\1 #\2 #\3) (LIST A B))
                          0 NIL)))

(assert!
 (equal
  (untranslate
   '(FMT-TO-COMMENT-WINDOW
     '"Hello ~x0 ~x1"
     (PAIRLIS2 '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9)
               (CONS A (CONS 'B 'NIL)))
     '0
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
                           'NIL)
   nil (w state))
  '(FMT-TO-COMMENT-WINDOW
    "Hello ~x0 ~x1"
    (cons '(#\7 . a)
          (PAIRLIS2 '(#\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9)
                    (list 'b c)))
    0
    NIL)))

(assert!
 (equal
  (untranslate
   '(FMT-TO-COMMENT-WINDOW '"hello ~x0 ~x1~%"
                           '((#\0 . X) (#\1 . Y))
                           '0
                           'NIL)
   nil (w state))
  '(CW "hello ~x0 ~x1~%" 'X 'Y)))

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

