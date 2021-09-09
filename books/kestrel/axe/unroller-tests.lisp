; Tests of the unroller
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "unroller")
(include-book "std/testing/assert-equal" :dir :system)
(include-book "std/testing/must-be-redundant" :dir :system)

(assert-equal (unroll-events 'len 3 nil state)
              '((SKIP-PROOFS
                 (DEFUN
                   LEN-UNROLLED-BY-3 (X)
                   (DECLARE (XARGS :NORMALIZE NIL))
                   (IF
                    (CONSP X)
                    (IF
                     (CONSP (CDR X))
                     (IF (CONSP (CDR (CDR X)))
                         (BINARY-+
                          '1
                          (BINARY-+ '1
                                    (BINARY-+ '1
                                              (LEN-UNROLLED-BY-3 (CDR (CDR (CDR X)))))))
                         (BINARY-+ '1 (BINARY-+ '1 '0)))
                     (BINARY-+ '1 '0))
                    '0)))
                (DEFTHM
                  LEN-BECOMES-LEN-UNROLLED-BY-3
                  (EQUAL (LEN X) (LEN-UNROLLED-BY-3 X))
                  :HINTS (("Goal" :INDUCT (LEN X)
                           :DO-NOT '(GENERALIZE ELIMINATE-DESTRUCTORS)
                           :EXPAND NIL
                           :IN-THEORY (UNION-THEORIES '(LEN LEN-UNROLLED-BY-3)
                                                      (THEORY 'MINIMAL-THEORY)))))
                (DEFTHM LEN-UNROLLED-BY-3-BASE-CASE-LEMMA-0
                  (IMPLIES (IF (CONSP X)
                               (IF (CONSP (CDR X))
                                   (NOT (CONSP (CDR (CDR X))))
                                   'NIL)
                               'NIL)
                           (EQUAL (LEN-UNROLLED-BY-3 X)
                                  (BINARY-+ '1 (BINARY-+ '1 '0))))
                  :HINTS (("Goal" :IN-THEORY (UNION-THEORIES (THEORY 'MINIMAL-THEORY)
                                                             '(LEN-UNROLLED-BY-3)))))
                (DEFTHM LEN-UNROLLED-BY-3-BASE-CASE-LEMMA-1
                  (IMPLIES (IF (CONSP X)
                               (NOT (CONSP (CDR X)))
                               'NIL)
                           (EQUAL (LEN-UNROLLED-BY-3 X)
                                  (BINARY-+ '1 '0)))
                  :HINTS (("Goal" :IN-THEORY (UNION-THEORIES (THEORY 'MINIMAL-THEORY)
                                                             '(LEN-UNROLLED-BY-3)))))
                (DEFTHM LEN-UNROLLED-BY-3-BASE-CASE-LEMMA-2
                  (IMPLIES (NOT (CONSP X))
                           (EQUAL (LEN-UNROLLED-BY-3 X) '0))
                  :HINTS (("Goal" :IN-THEORY (UNION-THEORIES (THEORY 'MINIMAL-THEORY)
                                                             '(LEN-UNROLLED-BY-3)))))))

(make-event
 `(progn ,@(unroll-events 'len 3 nil state)))

(defun sz (tree)
  (if (atom tree)
      1
    (+ (sz (car tree))
       (sz (cdr tree)))))

(make-event
 `(progn ,@(unroll-events 'sz 3 nil state)))

;; todo: can the form of this be improved?
(must-be-redundant
 (DEFUN
   SZ-UNROLLED-BY-3 (TREE)
   (DECLARE (XARGS :NORMALIZE NIL))
   (IF
    (ATOM TREE)
    '1
    (IF
     (ATOM (CAR TREE))
     (IF
      (ATOM (CDR TREE))
      (BINARY-+ '1 '1)
      (IF
       (ATOM (CAR (CDR TREE)))
       (IF
        (ATOM (CDR (CDR TREE)))
        (BINARY-+ '1 (BINARY-+ '1 '1))
        (BINARY-+
         '1
         (BINARY-+
          '1
          (BINARY-+
           (SZ-UNROLLED-BY-3 (CAR (CDR (CDR TREE))))
           (SZ-UNROLLED-BY-3 (CDR (CDR (CDR TREE))))))))
       (IF
        (ATOM (CDR (CDR TREE)))
        (BINARY-+
         '1
         (BINARY-+
          (BINARY-+ (SZ-UNROLLED-BY-3 (CAR (CAR (CDR TREE))))
                    (SZ-UNROLLED-BY-3 (CDR (CAR (CDR TREE)))))
          '1))
        (BINARY-+
         '1
         (BINARY-+
          (BINARY-+ (SZ-UNROLLED-BY-3 (CAR (CAR (CDR TREE))))
                    (SZ-UNROLLED-BY-3 (CDR (CAR (CDR TREE)))))
          (BINARY-+
           (SZ-UNROLLED-BY-3 (CAR (CDR (CDR TREE))))
           (SZ-UNROLLED-BY-3 (CDR (CDR (CDR TREE))))))))))
     (IF
      (ATOM (CAR (CAR TREE)))
      (IF
       (ATOM (CDR (CAR TREE)))
       (IF
        (ATOM (CDR TREE))
        (BINARY-+ (BINARY-+ '1 '1) '1)
        (IF
         (ATOM (CAR (CDR TREE)))
         (IF
          (ATOM (CDR (CDR TREE)))
          (BINARY-+ (BINARY-+ '1 '1)
                    (BINARY-+ '1 '1))
          (BINARY-+
           (BINARY-+ '1 '1)
           (BINARY-+
            '1
            (BINARY-+
             (SZ-UNROLLED-BY-3 (CAR (CDR (CDR TREE))))
             (SZ-UNROLLED-BY-3 (CDR (CDR (CDR TREE))))))))
         (IF
          (ATOM (CDR (CDR TREE)))
          (BINARY-+
           (BINARY-+ '1 '1)
           (BINARY-+
            (BINARY-+ (SZ-UNROLLED-BY-3 (CAR (CAR (CDR TREE))))
                      (SZ-UNROLLED-BY-3 (CDR (CAR (CDR TREE)))))
            '1))
          (BINARY-+
           (BINARY-+ '1 '1)
           (BINARY-+
            (BINARY-+ (SZ-UNROLLED-BY-3 (CAR (CAR (CDR TREE))))
                      (SZ-UNROLLED-BY-3 (CDR (CAR (CDR TREE)))))
            (BINARY-+
             (SZ-UNROLLED-BY-3 (CAR (CDR (CDR TREE))))
             (SZ-UNROLLED-BY-3 (CDR (CDR (CDR TREE))))))))))
       (IF
        (ATOM (CDR TREE))
        (BINARY-+
         (BINARY-+
          '1
          (BINARY-+ (SZ-UNROLLED-BY-3 (CAR (CDR (CAR TREE))))
                    (SZ-UNROLLED-BY-3 (CDR (CDR (CAR TREE))))))
         '1)
        (IF
         (ATOM (CAR (CDR TREE)))
         (IF
          (ATOM (CDR (CDR TREE)))
          (BINARY-+
           (BINARY-+
            '1
            (BINARY-+
             (SZ-UNROLLED-BY-3 (CAR (CDR (CAR TREE))))
             (SZ-UNROLLED-BY-3 (CDR (CDR (CAR TREE))))))
           (BINARY-+ '1 '1))
          (BINARY-+
           (BINARY-+
            '1
            (BINARY-+
             (SZ-UNROLLED-BY-3 (CAR (CDR (CAR TREE))))
             (SZ-UNROLLED-BY-3 (CDR (CDR (CAR TREE))))))
           (BINARY-+
            '1
            (BINARY-+
             (SZ-UNROLLED-BY-3 (CAR (CDR (CDR TREE))))
             (SZ-UNROLLED-BY-3 (CDR (CDR (CDR TREE))))))))
         (IF
          (ATOM (CDR (CDR TREE)))
          (BINARY-+
           (BINARY-+
            '1
            (BINARY-+
             (SZ-UNROLLED-BY-3 (CAR (CDR (CAR TREE))))
             (SZ-UNROLLED-BY-3 (CDR (CDR (CAR TREE))))))
           (BINARY-+
            (BINARY-+ (SZ-UNROLLED-BY-3 (CAR (CAR (CDR TREE))))
                      (SZ-UNROLLED-BY-3 (CDR (CAR (CDR TREE)))))
            '1))
          (BINARY-+
           (BINARY-+
            '1
            (BINARY-+
             (SZ-UNROLLED-BY-3 (CAR (CDR (CAR TREE))))
             (SZ-UNROLLED-BY-3 (CDR (CDR (CAR TREE))))))
           (BINARY-+
            (BINARY-+ (SZ-UNROLLED-BY-3 (CAR (CAR (CDR TREE))))
                      (SZ-UNROLLED-BY-3 (CDR (CAR (CDR TREE)))))
            (BINARY-+
             (SZ-UNROLLED-BY-3 (CAR (CDR (CDR TREE))))
             (SZ-UNROLLED-BY-3 (CDR (CDR (CDR TREE)))))))))))
      (IF
       (ATOM (CDR (CAR TREE)))
       (IF
        (ATOM (CDR TREE))
        (BINARY-+
         (BINARY-+
          (BINARY-+ (SZ-UNROLLED-BY-3 (CAR (CAR (CAR TREE))))
                    (SZ-UNROLLED-BY-3 (CDR (CAR (CAR TREE)))))
          '1)
         '1)
        (IF
         (ATOM (CAR (CDR TREE)))
         (IF
          (ATOM (CDR (CDR TREE)))
          (BINARY-+
           (BINARY-+
            (BINARY-+ (SZ-UNROLLED-BY-3 (CAR (CAR (CAR TREE))))
                      (SZ-UNROLLED-BY-3 (CDR (CAR (CAR TREE)))))
            '1)
           (BINARY-+ '1 '1))
          (BINARY-+
           (BINARY-+
            (BINARY-+ (SZ-UNROLLED-BY-3 (CAR (CAR (CAR TREE))))
                      (SZ-UNROLLED-BY-3 (CDR (CAR (CAR TREE)))))
            '1)
           (BINARY-+
            '1
            (BINARY-+
             (SZ-UNROLLED-BY-3 (CAR (CDR (CDR TREE))))
             (SZ-UNROLLED-BY-3 (CDR (CDR (CDR TREE))))))))
         (IF
          (ATOM (CDR (CDR TREE)))
          (BINARY-+
           (BINARY-+
            (BINARY-+ (SZ-UNROLLED-BY-3 (CAR (CAR (CAR TREE))))
                      (SZ-UNROLLED-BY-3 (CDR (CAR (CAR TREE)))))
            '1)
           (BINARY-+
            (BINARY-+ (SZ-UNROLLED-BY-3 (CAR (CAR (CDR TREE))))
                      (SZ-UNROLLED-BY-3 (CDR (CAR (CDR TREE)))))
            '1))
          (BINARY-+
           (BINARY-+
            (BINARY-+ (SZ-UNROLLED-BY-3 (CAR (CAR (CAR TREE))))
                      (SZ-UNROLLED-BY-3 (CDR (CAR (CAR TREE)))))
            '1)
           (BINARY-+
            (BINARY-+ (SZ-UNROLLED-BY-3 (CAR (CAR (CDR TREE))))
                      (SZ-UNROLLED-BY-3 (CDR (CAR (CDR TREE)))))
            (BINARY-+
             (SZ-UNROLLED-BY-3 (CAR (CDR (CDR TREE))))
             (SZ-UNROLLED-BY-3 (CDR (CDR (CDR TREE))))))))))
       (IF
        (ATOM (CDR TREE))
        (BINARY-+
         (BINARY-+
          (BINARY-+ (SZ-UNROLLED-BY-3 (CAR (CAR (CAR TREE))))
                    (SZ-UNROLLED-BY-3 (CDR (CAR (CAR TREE)))))
          (BINARY-+ (SZ-UNROLLED-BY-3 (CAR (CDR (CAR TREE))))
                    (SZ-UNROLLED-BY-3 (CDR (CDR (CAR TREE))))))
         '1)
        (IF
         (ATOM (CAR (CDR TREE)))
         (IF
          (ATOM (CDR (CDR TREE)))
          (BINARY-+
           (BINARY-+
            (BINARY-+ (SZ-UNROLLED-BY-3 (CAR (CAR (CAR TREE))))
                      (SZ-UNROLLED-BY-3 (CDR (CAR (CAR TREE)))))
            (BINARY-+
             (SZ-UNROLLED-BY-3 (CAR (CDR (CAR TREE))))
             (SZ-UNROLLED-BY-3 (CDR (CDR (CAR TREE))))))
           (BINARY-+ '1 '1))
          (BINARY-+
           (BINARY-+
            (BINARY-+ (SZ-UNROLLED-BY-3 (CAR (CAR (CAR TREE))))
                      (SZ-UNROLLED-BY-3 (CDR (CAR (CAR TREE)))))
            (BINARY-+
             (SZ-UNROLLED-BY-3 (CAR (CDR (CAR TREE))))
             (SZ-UNROLLED-BY-3 (CDR (CDR (CAR TREE))))))
           (BINARY-+
            '1
            (BINARY-+
             (SZ-UNROLLED-BY-3 (CAR (CDR (CDR TREE))))
             (SZ-UNROLLED-BY-3 (CDR (CDR (CDR TREE))))))))
         (IF
          (ATOM (CDR (CDR TREE)))
          (BINARY-+
           (BINARY-+
            (BINARY-+ (SZ-UNROLLED-BY-3 (CAR (CAR (CAR TREE))))
                      (SZ-UNROLLED-BY-3 (CDR (CAR (CAR TREE)))))
            (BINARY-+
             (SZ-UNROLLED-BY-3 (CAR (CDR (CAR TREE))))
             (SZ-UNROLLED-BY-3 (CDR (CDR (CAR TREE))))))
           (BINARY-+
            (BINARY-+ (SZ-UNROLLED-BY-3 (CAR (CAR (CDR TREE))))
                      (SZ-UNROLLED-BY-3 (CDR (CAR (CDR TREE)))))
            '1))
          (BINARY-+
           (BINARY-+
            (BINARY-+ (SZ-UNROLLED-BY-3 (CAR (CAR (CAR TREE))))
                      (SZ-UNROLLED-BY-3 (CDR (CAR (CAR TREE)))))
            (BINARY-+
             (SZ-UNROLLED-BY-3 (CAR (CDR (CAR TREE))))
             (SZ-UNROLLED-BY-3 (CDR (CDR (CAR TREE))))))
           (BINARY-+
            (BINARY-+ (SZ-UNROLLED-BY-3 (CAR (CAR (CDR TREE))))
                      (SZ-UNROLLED-BY-3 (CDR (CAR (CDR TREE)))))
            (BINARY-+ (SZ-UNROLLED-BY-3 (CAR (CDR (CDR TREE))))
                      (SZ-UNROLLED-BY-3
                       (CDR (CDR (CDR TREE))))))))))))))))
