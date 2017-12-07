; Copyright (C) 2014, ForrestHunt, Inc.
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
; Symbolic State Management -- Version 22
; J Strother Moore
; Fall/Winter, 2014/2015
; Georgetown, TX and Edinburgh, Scotland
;
; Stateman: Using Metafunctions to Manage Large Terms Representing Machine States
; J Strother Moore
; July, 2015

; The paper above gives several examples of the Stateman state management book.
; This file contains those examples in a form allowing the reader to
; interactively reproduce them.  This is NOT a book.  The reader interested in
; learning about the metafunctions in Stateman is urged simply to execute each
; of the commands below while or after reading the above paper and/or the code.

; The main motivation behind this file is to help users extend Stateman.  It is
; helpful to see how to call and interpret the results of some of the functions
; in Stateman.  By experimenting with the inputs provided below you can better
; understand some of the limitations of Stateman.

; Note: Before executing the next command you will need to connect to the
; directory containing stateman22.lisp or edit the command below to include the
; path.

(include-book "stateman22")

; Section 4. Examples

; This section of the paper shows 12 example executions, numbered (1) through
; (12).  The first 7 are shown twice, first in untranslated form and then in a
; shorter notation.  Here are all 12 of the examples suitable for execution at
; the top-level of ACL2 after including the Stateman book.

(meta-!I '(!I '123 st))                                         ;(1)
; (HIDE (!I '123 ST))

(meta-!R '(!R '0 '4 (R '16 '4 st) (HIDE (!I '123 ST)))          ;(2)
                nil state)
; (HIDE (!R '0 '4 (R '16 '4 ST) (!I '123 ST)))                  ;(st')

(meta-I '(I (HIDE (!R '0 '4 (R '16 '4 st)  (!I '123 ST)))))     ;(3)
; '123

(meta-R '(R '0 '4 (HIDE (!R '0 '4 (R '16 '4 st) (!I '123 ST)))) ;(4)
               nil state)
; (R '16 '4 ST)

(meta-R '(R '2 '2 (HIDE (!R '0 '4 (R '16 '4 st) (!I '123 ST)))) ;(5)
               nil state)
; (HIDE (ASH (R '16 '4 ST) '-16))

(meta-R '(R '8 '4 (HIDE (!R '0 '4 (R '16 '4 st) (!I '123 ST)))) ;(6)
               nil state)
; (R '8 '4 ST)

(meta-R '(R '2 '4 (HIDE (!R '0 '4 (R '16 '4 st) (!I '123 ST)))) ;(7)
               nil state)
; (HIDE (BINARY-+ (ASH (R '4 '2 ST) '16)
;                 (ASH (R '16 '4 ST) '-16)))

(meta-!R '(!R '8 '4 v st) nil state)                            ;(8)
; (HIDE (!R 8 4 v st))

(meta-R '(R '8 '4 (HIDE (!R '8 '4 v st))) nil state)            ;(9)
; (HIDE (MOD (IFIX v) 4294967296))

; Before example (10) the paper says ``Now let the metafunction context encode
; the assumption that (R 16 4 st) is less than 16.''  To express this
; assumption, we create a fake metafunction context, mfc.  The type-alist,
; which encodes our assumptions, is the second component of the mfc and all
; other components are irrelevant to Stateman.  Our fake mfc is here
; stored in a state global variable:

(assign mfc (list nil `(((< (R '16 '4 st) '16) ,*ts-t*))))

; The type-alist shown above could have been written alternatively
; as ``(<= (R 16 4 st) 15)'', but that in fully translated form
; that is (NOT (< '15 (R '16 '4 ST))) and to be an effective type-alist
; entry the NOT is stripped off and encoded in the assigned type, i.e.,
; we say ``(< 15 (R 16 4 st)) has the false type-set'' or
; use the type-alsist `(((< '15 (R '16 '4 st)) ,*ts-nil*)).

; Under the assuption above the paper goes on to show the input to example (10)
; using our ``==>+'' notation (with a ``dagger''), where the left-hand side of
; the ``==>+'' is:

; (R (+ 3200 (* 8 (R 16 4 st))) 8                                ;(10)
;    (HIDE (!R 3600 4 v (!R 8 4 w st))))
; ==>+
; ...

; Given the meaning of the adopted notation, you should meta-R to the fully
; translated version of the term shown above, our mfc, and state.  That is,
; evaluate:

(meta-R '(R (BINARY-+ '3200 (BINARY-* '8 (R '16 '4 st))) '8     ;(10)
            (HIDE (!R '3600 '4 v (!R '8 '4 w st))))
        (@ mfc)
        state)

; The paper then shows:

; ==>+
; (R (+ 3200 (* 8 (R 16 4 st))) 8 st)

; and goes on to say ``The ``+'' [``dagger''] on the transformation in (10)
; indicates that a side condition was generated. That side condition is (<= (R
; 16 4 st) 15), and it must be established before the replacement is made.''

; If you evaluate the meta-R expression above the result is:

; (IF (FORCE (NOT (< '15 (R '16 '4 ST))))            ; (IF (FORCE test)
;     (R (BINARY-+ '3200                             ;     x'
;                  (BINARY-* '8 (R '16 '4 ST)))
;        '8
;        ST)
;     (R (BINARY-+ '3200                             ;     x
;                  (BINARY-* '8 (R '16 '4 ST)))
;        '8
;        (HIDE (!R '3600 '4 V (!R '8 '4 W ST)))))    ;      )

; Recall that when a metafunction applied to x produces (IF test x' x) it is
; interpreted to mean ``if test can be established, replace x by x', else do
; not use the output of the metafunction.''  That is the situation here.  The
; term playing the role of x' above is the term shown on the right-hand side of
; the ``==>+'' in the paper.  The test is the translated form of (<= (R 16 4
; st) 15), however Stateman additionally FORCEs it because we know the test to
; be true.

; In a similar fashion, here is example (11)

(meta-!R
 '(!R (BINARY-+ '3200 (BINARY-* '8 (R '16 '4 st))) '8 u         ;(11)
      (HIDE (!R '3600 '4 v 
                (!R '8 '4 w
                    (!R (BINARY-+ '3200 (BINARY-* '8 (R '16 '4 st))) '8 x
                        st)))))
 (@ mfc)
 state)

; The output will be:

; (HIDE (!R (BINARY-+ '3200
;                     (BINARY-* '8 (R '16 '4 ST)))
;           '8
;           U
;           (!R '3600 '4 V (!R '8 '4 W ST))))

; As noted in the paper and for the reasons given, no side condition is
; necessary.

; Finally, example (12) of the paper is reproduced with:

(meta-R
  '(R '3 '8                                                     ;(12)
      (HIDE 
       (!R '14 '5 x
           (!R '0 '4 u 
               (!R '19 '8 y
                   (!R '9 '2 w
                       (!R '2 '4 v st)))))))
  nil
  state)

; and the output is:

; (HIDE (BINARY-+ (ASH (R '6 '3 ST) '24)
;                 (BINARY-+ (MOD (ASH (IFIX U) '-24) '256)
;                           (BINARY-+ (ASH (MOD (IFIX W) '65536) '48)
;                                     (ASH (MOD (ASH (IFIX V) '-16) '65536)
;                                          '8)))))

; Section 5: Ainni: Abstract Interpreter for Natural Number Intervals

; There are several examples given in this section.

; The first example considers the translation of the term:

; (+ 288 (* 8 (LOGAND 31 (ASH (R 4520 8 st) -3))))

; which is

; (BINARY-+ '288
;           (BINARY-* '8
;                     (BINARY-LOGAND '31
;                                    (ASH (R '4520 '8 ST) '-3))))

; The paper says, ``In the absence of any contextual information, Ainni returns
; the natural number interval [288,536].''  Here is how you confirm that:

(ainni '(BINARY-+ '288
                  (BINARY-* '8
                            (BINARY-LOGAND '31
                                           (ASH (R '4520 '8 ST) '-3))))
       nil  ; accumulated hypotheses so far
       nil) ; type-alist containing assumptions

; the result is:

; (T NIL (INTEGERP (NIL . 288) NIL . 536))

; which (mv flg hyps interval), where flg is T meaning Ainni succeeded, the
; returned hyps is nil meaning there are no side conditions to relieve, and
; (INTEGERP (NIL . 288) NIL . 536) is a tau interval over the integers
; representing [288, 536].  A tau interval has five components: the domain
; (here INTEGERP), the lower relation (here nil, meaning ``<='', as opposed to
; t meaning ``<''), the lower bound (here 288), the upper relation (here nil)
; and the upper bound (here 536).

; The paper then says that the type-alist ``might assert that (R 4520 8 st) <
; 24, in which case Ainni determines that the term above lies in the interval
; [288,304].''  Here is that example:

(ainni '(BINARY-+ '288
                  (BINARY-* '8
                            (BINARY-LOGAND '31
                                           (ASH (R '4520 '8 ST) '-3))))
       nil  ; accumulated hypotheses so far
       `(((< (R '4520 '8 st) '24) ,*ts-t*)))

; and the output is:

; (T ((FORCE (NOT (< '23 (R '4520 '8 ST))))) ; flag and list of side conditions
;    (INTEGERP (NIL . 288) NIL . 304))       ; interval

; where now we see one forced side condition and the interval [288,304].

; Three theorems are used to establish that Ainni is correct.  Their names
; are:

;    name                    informal interpretation

;  ainni-correct-part-1      returned hyps are all pseudo-terms
;  ainni-correct-part-2a     returned interval is really an interval
;  ainni-correct-part-2b     value of input term lies in the returned interval

; and they correspond to the three bullets in the informal characterization of
; Ainni's correctness.  By the way, the name of the actual evaluator used in
; Stateman is STATEMAN-EVAL, not the ``script E'' shown in the paper.

; Finally the paper, just for fun, shows a relatively large term.  That term
; looks like (LOGIOR big-arg1 big-arg2 big-arg3).  Below we show the translated
; forms of the three big-argi and use them to assemble big-term, where
; big-arg1, big-arg2, big-arg3, and big-term are state globals here:

(assign big-arg1
        '(BINARY-LOGAND
          '32
          (ASH
           (MOD
            (ASH
             (BINARY-LOGXOR
              (BINARY-LOGIOR
               (ASH
                (ASH
                 (BINARY-LOGIOR
                  (ASH (MOD (ASH (R '4520 '8 ST) '0) '2)
                       '31)
                  (BINARY-LOGIOR
                   (ASH (BINARY-LOGAND '4026531840
                                       (R '4520 '8 ST))
                        '-1)
                   (BINARY-LOGIOR
                    (ASH (MOD (ASH (R '4520 '8 ST) '-27) '2)
                         '26)
                    (BINARY-LOGIOR
                     (ASH (MOD (ASH (R '4520 '8 ST) '-28) '2)
                          '25)
                     (BINARY-LOGIOR
                      (ASH (BINARY-LOGAND '251658240
                                          (R '4520 '8 ST))
                           '-3)
                      (BINARY-LOGIOR
                       (ASH (MOD (ASH (R '4520 '8 ST) '-23) '2)
                            '20)
                       (BINARY-LOGIOR
                        (ASH (MOD (ASH (R '4520 '8 ST) '-24) '2)
                             '19)
                        (BINARY-LOGIOR
                         (ASH (BINARY-LOGAND '15728640
                                             (R '4520 '8 ST))
                              '-5)
                         (BINARY-LOGIOR
                          (ASH (MOD (ASH (R '4520 '8 ST) '-19) '2)
                               '14)
                          (BINARY-LOGIOR
                           (ASH (MOD (ASH (R '4520 '8 ST) '-20) '2)
                                '13)
                           (BINARY-LOGIOR (ASH (BINARY-LOGAND '983040 (R '4520 '8 ST))
                                               '-7)
                                          (ASH (MOD (ASH (R '4520 '8 ST) '-15) '2)
                                               '8))))))))))))
                 '-8)
                '24)
               (ASH
                (BINARY-LOGIOR
                 (ASH (MOD (ASH (R '4520 '8 ST) '-16) '2)
                      '31)
                 (BINARY-LOGIOR
                  (ASH (BINARY-LOGAND '61440 (R '4520 '8 ST))
                       '15)
                  (BINARY-LOGIOR
                   (ASH (MOD (ASH (R '4520 '8 ST) '-11) '2)
                        '26)
                   (BINARY-LOGIOR
                    (ASH (MOD (ASH (R '4520 '8 ST) '-12) '2)
                         '25)
                    (BINARY-LOGIOR
                     (ASH (BINARY-LOGAND '3840 (R '4520 '8 ST))
                          '13)
                     (BINARY-LOGIOR
                      (ASH (MOD (ASH (R '4520 '8 ST) '-7) '2)
                           '20)
                      (BINARY-LOGIOR
                       (ASH (MOD (ASH (R '4520 '8 ST) '-8) '2)
                            '19)
                       (BINARY-LOGIOR
                        (ASH (BINARY-LOGAND '240 (R '4520 '8 ST))
                             '11)
                        (BINARY-LOGIOR
                         (ASH (MOD (ASH (R '4520 '8 ST) '-3) '2)
                              '14)
                         (BINARY-LOGIOR
                          (ASH (MOD (ASH (R '4520 '8 ST) '-4) '2)
                               '13)
                          (BINARY-LOGIOR (ASH (MOD (R '4520 '8 ST) '16) '9)
                                         (ASH (ASH (R '4520 '8 ST) '-31)
                                              '8))))))))))))
                '-8))
              (R (BINARY-+ '4376
                           (BINARY-+ (BINARY-* '8 (R '4536 '8 ST))
                                     (BINARY-* '8
                                               (UNARY-- (R '4528 '8 ST)))))
                 '8
                 ST))
             '-40)
            '256)
           '-2)))

(assign big-arg2
        '(ASH
          (MOD
           (ASH
            (MOD
             (ASH
              (BINARY-LOGXOR
               (BINARY-LOGIOR
                (ASH
                 (ASH
                  (BINARY-LOGIOR
                   (ASH (MOD (ASH (R '4520 '8 ST) '0) '2)
                        '31)
                   (BINARY-LOGIOR
                    (ASH (BINARY-LOGAND '4026531840
                                        (R '4520 '8 ST))
                         '-1)
                    (BINARY-LOGIOR
                     (ASH (MOD (ASH (R '4520 '8 ST) '-27) '2)
                          '26)
                     (BINARY-LOGIOR
                      (ASH (MOD (ASH (R '4520 '8 ST) '-28) '2)
                           '25)
                      (BINARY-LOGIOR
                       (ASH (BINARY-LOGAND '251658240
                                           (R '4520 '8 ST))
                            '-3)
                       (BINARY-LOGIOR
                        (ASH (MOD (ASH (R '4520 '8 ST) '-23) '2)
                             '20)
                        (BINARY-LOGIOR
                         (ASH (MOD (ASH (R '4520 '8 ST) '-24) '2)
                              '19)
                         (BINARY-LOGIOR
                          (ASH (BINARY-LOGAND '15728640
                                              (R '4520 '8 ST))
                               '-5)
                          (BINARY-LOGIOR
                           (ASH (MOD (ASH (R '4520 '8 ST) '-19) '2)
                                '14)
                           (BINARY-LOGIOR
                            (ASH (MOD (ASH (R '4520 '8 ST) '-20) '2)
                                 '13)
                            (BINARY-LOGIOR
                             (ASH (BINARY-LOGAND '983040 (R '4520 '8 ST))
                                  '-7)
                             (ASH (MOD (ASH (R '4520 '8 ST) '-15) '2)
                                  '8))))))))))))
                  '-8)
                 '24)
                (ASH
                 (BINARY-LOGIOR
                  (ASH (MOD (ASH (R '4520 '8 ST) '-16) '2)
                       '31)
                  (BINARY-LOGIOR
                   (ASH (BINARY-LOGAND '61440 (R '4520 '8 ST))
                        '15)
                   (BINARY-LOGIOR
                    (ASH (MOD (ASH (R '4520 '8 ST) '-11) '2)
                         '26)
                    (BINARY-LOGIOR
                     (ASH (MOD (ASH (R '4520 '8 ST) '-12) '2)
                          '25)
                     (BINARY-LOGIOR
                      (ASH (BINARY-LOGAND '3840 (R '4520 '8 ST))
                           '13)
                      (BINARY-LOGIOR
                       (ASH (MOD (ASH (R '4520 '8 ST) '-7) '2)
                            '20)
                       (BINARY-LOGIOR
                        (ASH (MOD (ASH (R '4520 '8 ST) '-8) '2)
                             '19)
                        (BINARY-LOGIOR
                         (ASH (BINARY-LOGAND '240 (R '4520 '8 ST))
                              '11)
                         (BINARY-LOGIOR
                          (ASH (MOD (ASH (R '4520 '8 ST) '-3) '2)
                               '14)
                          (BINARY-LOGIOR
                           (ASH (MOD (ASH (R '4520 '8 ST) '-4) '2)
                                '13)
                           (BINARY-LOGIOR (ASH (MOD (R '4520 '8 ST) '16) '9)
                                          (ASH (ASH (R '4520 '8 ST) '-31)
                                               '8))))))))))))
                 '-8))
               (R (BINARY-+ '4376
                            (BINARY-+ (BINARY-* '8 (R '4536 '8 ST))
                                      (BINARY-* '8
                                                (UNARY-- (R '4528 '8 ST)))))
                  '8
                  ST))
              '-40)
             '256)
            '-2)
           '32)
          '-1))

(assign big-arg3
        '(ASH
          (MOD
           (ASH
            (MOD
             (ASH
              (BINARY-LOGXOR
               (BINARY-LOGIOR
                (ASH
                 (ASH
                  (BINARY-LOGIOR
                   (ASH (MOD (ASH (R '4520 '8 ST) '0) '2)
                        '31)
                   (BINARY-LOGIOR
                    (ASH (BINARY-LOGAND '4026531840
                                        (R '4520 '8 ST))
                         '-1)
                    (BINARY-LOGIOR
                     (ASH (MOD (ASH (R '4520 '8 ST) '-27) '2)
                          '26)
                     (BINARY-LOGIOR
                      (ASH (MOD (ASH (R '4520 '8 ST) '-28) '2)
                           '25)
                      (BINARY-LOGIOR
                       (ASH (BINARY-LOGAND '251658240
                                           (R '4520 '8 ST))
                            '-3)
                       (BINARY-LOGIOR
                        (ASH (MOD (ASH (R '4520 '8 ST) '-23) '2)
                             '20)
                        (BINARY-LOGIOR
                         (ASH (MOD (ASH (R '4520 '8 ST) '-24) '2)
                              '19)
                         (BINARY-LOGIOR
                          (ASH (BINARY-LOGAND '15728640
                                              (R '4520 '8 ST))
                               '-5)
                          (BINARY-LOGIOR
                           (ASH (MOD (ASH (R '4520 '8 ST) '-19) '2)
                                '14)
                           (BINARY-LOGIOR
                            (ASH (MOD (ASH (R '4520 '8 ST) '-20) '2)
                                 '13)
                            (BINARY-LOGIOR
                             (ASH (BINARY-LOGAND '983040 (R '4520 '8 ST))
                                  '-7)
                             (ASH (MOD (ASH (R '4520 '8 ST) '-15) '2)
                                  '8))))))))))))
                  '-8)
                 '24)
                (ASH
                 (BINARY-LOGIOR
                  (ASH (MOD (ASH (R '4520 '8 ST) '-16) '2)
                       '31)
                  (BINARY-LOGIOR
                   (ASH (BINARY-LOGAND '61440 (R '4520 '8 ST))
                        '15)
                   (BINARY-LOGIOR
                    (ASH (MOD (ASH (R '4520 '8 ST) '-11) '2)
                         '26)
                    (BINARY-LOGIOR
                     (ASH (MOD (ASH (R '4520 '8 ST) '-12) '2)
                          '25)
                     (BINARY-LOGIOR
                      (ASH (BINARY-LOGAND '3840 (R '4520 '8 ST))
                           '13)
                      (BINARY-LOGIOR
                       (ASH (MOD (ASH (R '4520 '8 ST) '-7) '2)
                            '20)
                       (BINARY-LOGIOR
                        (ASH (MOD (ASH (R '4520 '8 ST) '-8) '2)
                             '19)
                        (BINARY-LOGIOR
                         (ASH (BINARY-LOGAND '240 (R '4520 '8 ST))
                              '11)
                         (BINARY-LOGIOR
                          (ASH (MOD (ASH (R '4520 '8 ST) '-3) '2)
                               '14)
                          (BINARY-LOGIOR
                           (ASH (MOD (ASH (R '4520 '8 ST) '-4) '2)
                                '13)
                           (BINARY-LOGIOR (ASH (MOD (R '4520 '8 ST) '16) '9)
                                          (ASH (ASH (R '4520 '8 ST) '-31)
                                               '8))))))))))))
                 '-8))
               (R (BINARY-+ '4376
                            (BINARY-+ (BINARY-* '8 (R '4536 '8 ST))
                                      (BINARY-* '8
                                                (UNARY-- (R '4528 '8 ST)))))
                  '8
                  ST))
              '-40)
             '256)
            '-2)
           '2)
          '4))

(assign big-term
        `(BINARY-LOGIOR
          ,(@ big-arg1)
          (BINARY-LOGIOR
           ,(@ big-arg2)
           ,(@ big-arg3))))

; To see Ainni bound big-term, evaluate

(time$ (ainni (@ big-term) nil nil))

; the result is:

; (EV-REC *RETURN-LAST-ARG3* ...) took 
; 0.00 seconds realtime, 0.00 seconds runtime
; (125,536 bytes allocated).
; (T NIL (INTEGERP (NIL . 0) NIL . 63))

; Note that the returned interval is [0,63].

; To see Ainni bound the three arguments separately do

(ainni (@ big-arg1) nil nil)  ; (t nil [0,32])
(ainni (@ big-arg2) nil nil)  ; (t nil [0,15])
(ainni (@ big-arg3) nil nil)  ; (t nil [0,16])

; Because of Ainni the meta-< metafunction can easily prove that
; the big-term is less than 64.

(meta-< `(< ,(@ big-term) '64) nil state)

; returns 'T.

; Section 6: Syntactic Simplification of MOD Expressions

; This section introduces in passing the notion of a ``syntactic integer''
; expression.  The idea is that we need to quickly determine whether an
; expression always returns an integer.  Here are some examples and
; counterexamples:

(syntactic-integerp '(BINARY-+ '3 (R A B C))) ; = T
(syntactic-integerp '(BINARY-* '3 (R A B C))) ; = T
(syntactic-integerp '(MOD (R A B C) '123))    ; = T

(syntactic-integerp '(BINARY-+ X (R A B C)))  ; = NIL
(syntactic-integerp '(BINARY-* '3 X))          ; = NIL
(syntactic-integerp '(MOD (R A B C) X))       ; = NIL

(syntactic-integerp '(R X Y Z))                ; = T
(syntactic-integerp '(BINARY-LOGAND X Y))      ; = T
(syntactic-integerp '(BINARY-LOGXOR X Y))      ; = T
(syntactic-integerp '(BINARY-LOGIOR X Y))      ; = T

(syntactic-integerp '(ASH (R A B C) X))        ; = T
(syntactic-integerp '(ASH X (R A B C)))        ; = NIL

(syntactic-integerp (@ big-term))              ; = T

; The definition is quite simple.  See (pe 'syntactic-integerp)

; Here are examples of the 7 rewrite rules implemented by meta-MOD.  The second
; argument to meta-MOD is the metafunction context and it can tested with our
; previously set global variable (@ mfc) which assumes (R '16 '4 ST) < 16.  In
; these examples we use Z as a generic term not known to be a syntactic integer
; and we use (R ...) as generic terms known to be syntactic integers.

; In the first example below, meta-mod makes no change to the expression
; because it cannot determine that the first argument to MOD is always an
; integer -- that is, X is not a syntactic integer expression.  But in the next
; example the first argument to MOD is a syntactic integer so simplification
; occurs.

(meta-MOD '(MOD Z '0) nil state) ; no change
(meta-MOD '(MOD (R A B C) '0) nil state) ; simplifies
; = (R A B C)

(meta-MOD '(MOD '25 '7) nil state)
; = '4

(meta-MOD '(MOD (MOD Z '7) '17) nil state)
; = (MOD Z '7)

(meta-MOD '(MOD (MOD (R A B C) '15) '3) nil state)
; = (MOD (R A B C) '3)

(meta-MOD '(MOD (R A '2 C) '65536) nil state) ; 256^2 = 65536
; = (R A '2 C)

; In the following test, we use (R 16 4 ST) which is in general larger
; than 65536, but we specify (@ mfc) as the context and that context
; assumes (R 16 4 ST) < 16.  So (conditional) simplification occurs.

(meta-MOD '(MOD (R '16 '4 ST) '65536) (@ mfc) state)
; = (IF (FORCE (NOT (< '15 (R '16 '4 ST))))
;       (R '16 '4 ST)
;       (MOD (R '16 '4 ST) '65536))

(meta-MOD '(MOD (BINARY-+ (R U V W)
                          (BINARY-+ (MOD (R A B C) '15)
                                    (R I J K)))
                '3)
          nil state)
; = (MOD (BINARY-+ (R U V W) (BINARY-+ (R A B C) (R I J K))) '3)

; This last example illustrates the value of Ainni.  Recall that (@ big-term)
; is a quite large term and yet this simplification occurs very quickly.  We
; test the returned value rather than display it to save space in this file.

(equal (meta-MOD `(MOD ,(@ big-term) '64) nil state)
       (@ big-term))

