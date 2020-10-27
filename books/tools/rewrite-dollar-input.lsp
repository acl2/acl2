; Copyright (C) 2020, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This file contains tests for rewrite$, rewrite$-hyps, and rewrite$-context.
; We do only simple, basic tests here, noting that community book
; kestrel/apt/simplify-defun-impl.lisp exercises these utilities -- in
; particular advanced option rcnst -- and is tested rather extensively.

(in-package "ACL2")

(include-book "rewrite-dollar")
(include-book "std/testing/must-eval-to" :dir :system)
(include-book "std/testing/must-fail" :dir :system)

(defmacro mf (form &key (expected ':soft))
  `(must-fail ,form
              :expected
              ,expected
              :with-output-off ; leave prove and error on
              (proof-tree event summary proof-builder history)))

; basic
(must-eval-to
 (rewrite$ '(cons (car x) (cdr x)))
 '((IF (CONSP X) X '(NIL))
   ((:REWRITE CONS-CAR-CDR))))

; not a termp
(mf
 (rewrite$ '(append (append x y) z)))

; :translate
(must-eval-to
 (rewrite$ '(append (append x y) z)
           :translate t)
 '((BINARY-APPEND (BINARY-APPEND X Y) Z)
   NIL))

; :hyps
(must-eval-to
 (rewrite$ '(cons (car x) (cdr x)) :hyps '((consp x) (< '0 (car x))))
 '(X ((:REWRITE CONS-CAR-CDR))))

; :hyps not all terms
(mf
 (rewrite$ '(cons (car x) (cdr x)) :hyps '((consp x) (< 0 (car x)))))

; :expand
(must-eval-to
 (rewrite$ '(binary-append x y)
           :expand '((append x y)))
 '((IF (CONSP X)
       (CONS (CAR X) (BINARY-APPEND (CDR X) Y))
       Y)
   ((:DEFINITION BINARY-APPEND))))

; :translate and :untranslate
(must-eval-to
 (rewrite$ '(append (append x y) z)
           :translate t
           :untranslate t)
 '((APPEND (APPEND X Y) Z)
   NIL))

(with-output :off prove
  (defthm append-assoc
    (equal (append (append x y) z)
           (append x y z))))

; use new rule
(must-eval-to
 (rewrite$ '(binary-append (binary-append x y) z))
 '((BINARY-APPEND X (BINARY-APPEND Y Z))
   ((:REWRITE APPEND-ASSOC))))

; no rewriting because of :in-theory
(must-eval-to
 (rewrite$ '(binary-append (binary-append x y) z)
           :in-theory '(disable append-assoc))
 '((BINARY-APPEND (BINARY-APPEND X Y) Z)
   NIL))

(encapsulate
  ()

(add-default-hints ; local to the encapsulate
 '('(:in-theory (disable append-assoc))))

; test default-hints-p default of t
(must-eval-to
 (rewrite$ '(binary-append (binary-append x y) z))
 '((BINARY-APPEND (BINARY-APPEND X Y) Z)
   NIL))

; test default-hints-p set to nil
(must-eval-to
 (rewrite$ '(binary-append (binary-append x y) z)
           :default-hints-p nil)
 '((BINARY-APPEND X (BINARY-APPEND Y Z))
   ((:REWRITE APPEND-ASSOC))))

) ; end encapsulate

(with-output :off prove
  (defthm append-assoc-with-force
    (implies (force (true-listp x))
             (equal (append (append x y) z)
                    (append x y z)))))

; :in-theory
(must-eval-to
 (rewrite$ '(binary-append (binary-append x y) z)
           :in-theory '(disable append-assoc-with-force))
 '((BINARY-APPEND X (BINARY-APPEND Y Z))
   ((:REWRITE APPEND-ASSOC))))

; failure because of forcing
(mf
 (rewrite$ '(binary-append (binary-append x y) z)))

; :prove-forced-assumptions nil
(must-eval-to
 (rewrite$ '(binary-append (binary-append x y) z)
           :prove-forced-assumptions nil)
 '((BINARY-APPEND X (BINARY-APPEND Y Z))
   ((:REWRITE APPEND-ASSOC-WITH-FORCE)
    (:EXECUTABLE-COUNTERPART FORCE))
   (((((0) NIL . 0)
      (:REWRITE APPEND-ASSOC-WITH-FORCE)
      BINARY-APPEND (BINARY-APPEND X Y)
      Z))
    (TRUE-LISTP X))))

; use of forward-chaining (and check that assumptions weren't forced)
(must-eval-to
 (rewrite$ '(binary-append (binary-append x y) z)
           :hyps '((symbol-listp x))
           :prove-forced-assumptions :none-forced)
 '((BINARY-APPEND X (BINARY-APPEND Y Z))
   ((:REWRITE APPEND-ASSOC-WITH-FORCE)
    (:FORWARD-CHAINING SYMBOL-LISTP-FORWARD-TO-TRUE-LISTP)
    (:TYPE-PRESCRIPTION SYMBOL-LISTP))))

(must-eval-to
 (rewrite$ '(binary-append (binary-append x y) z)
           :alist '((x . (nth a b)))
           :hyps '((symbol-listp (nth a b))))
 '((BINARY-APPEND (NTH A B) (BINARY-APPEND Y Z))
   ((:REWRITE APPEND-ASSOC-WITH-FORCE)
    (:FORWARD-CHAINING SYMBOL-LISTP-FORWARD-TO-TRUE-LISTP)
    (:TYPE-PRESCRIPTION SYMBOL-LISTP))))

; uses forcing
(must-eval-to
 (rewrite$ '(append (append x y) z)
           :alist '((x . (reverse u)))
           :hyps '((consp u))
           :translate t
           :untranslate t)
 '((APPEND (REVERSE U) Y Z)
   ((:TYPE-PRESCRIPTION TRUE-LISTP-REVAPPEND-TYPE-PRESCRIPTION)
    (:EXECUTABLE-COUNTERPART TRUE-LISTP)
    (:DEFINITION REVERSE)
    (:DEFINITION NOT)
    (:REWRITE APPEND-ASSOC-WITH-FORCE)
    (:EXECUTABLE-COUNTERPART FORCE)
    (:DEFINITION TRUE-LISTP)
    (:FAKE-RUNE-FOR-TYPE-SET NIL)
    (:TYPE-PRESCRIPTION REVERSE))))

; as above (uses forcing), but with repeat 2; notice that reverse became
; revappend
(must-eval-to
 (rewrite$ '(append (append x y) z)
           :alist '((x . (reverse u)))
           :hyps '((consp u))
           :repeat 2
           :translate t
           :untranslate t)
 '((APPEND (REVAPPEND U NIL) Y Z)
   ((:TYPE-PRESCRIPTION TRUE-LISTP-REVAPPEND-TYPE-PRESCRIPTION)
    (:EXECUTABLE-COUNTERPART TRUE-LISTP)
    (:DEFINITION NOT)
    (:DEFINITION REVERSE)
    (:REWRITE APPEND-ASSOC-WITH-FORCE)
    (:EXECUTABLE-COUNTERPART FORCE)
    (:DEFINITION TRUE-LISTP)
    (:FAKE-RUNE-FOR-TYPE-SET NIL)
    (:TYPE-PRESCRIPTION REVERSE))))

; as above, but without allowing proof for forced assumptions
(mf ; uses forcing
 (rewrite$ '(append (append x y) z)
           :alist '((x . (reverse u)))
           :hyps '((consp u))
           :translate t
           :untranslate t
           :prove-forced-assumptions :none-forced))

; as above, but check :prove-forced-assumptions with :same-hints
; and explicit hints.
(encapsulate
  ()
  (local (in-theory (disable reverse)))
  (must-eval-to
   (rewrite$ '(append (append x y) z)
             :alist '((x . (reverse u)))
             :hyps '((consp u))
             :in-theory '(enable reverse)
             :prove-forced-assumptions :same-hints
             :repeat 2
             :translate t
             :untranslate t)
   '((APPEND (REVAPPEND U NIL) Y Z)
     ((:TYPE-PRESCRIPTION TRUE-LISTP-REVAPPEND-TYPE-PRESCRIPTION)
      (:EXECUTABLE-COUNTERPART TRUE-LISTP)
      (:DEFINITION NOT)
      (:DEFINITION REVERSE)
      (:REWRITE APPEND-ASSOC-WITH-FORCE)
      (:EXECUTABLE-COUNTERPART FORCE)
      (:DEFINITION TRUE-LISTP)
      (:FAKE-RUNE-FOR-TYPE-SET NIL)
      (:TYPE-PRESCRIPTION REVERSE))))
  (must-eval-to
   (rewrite$ '(append (append x y) z)
             :alist '((x . (reverse u)))
             :hyps '((consp u))
             :prove-forced-assumptions '(("Goal" :in-theory (enable reverse)))
             :repeat 2
             :translate t
             :untranslate t)
   '((APPEND (REVERSE U) Y Z)
     ((:TYPE-PRESCRIPTION TRUE-LISTP-REVAPPEND-TYPE-PRESCRIPTION)
      (:EXECUTABLE-COUNTERPART TRUE-LISTP)
      (:DEFINITION REVERSE)
      (:DEFINITION NOT)
      (:REWRITE APPEND-ASSOC-WITH-FORCE)
      (:EXECUTABLE-COUNTERPART FORCE)
      (:DEFINITION TRUE-LISTP)
      (:FAKE-RUNE-FOR-TYPE-SET NIL)
      (:TYPE-PRESCRIPTION REVERSE)))))

(with-output :off prove
  (defthm member-append
    (iff (member a (append x y))
         (or (member a x)
             (member a y)))))

; only trivial rewrite because equiv is 'equal
(must-eval-to
 (rewrite$ '(member b (append u v)) :translate t)
 '((MEMBER-EQUAL B (BINARY-APPEND U V))
   ((:DEFINITION MEMBER-EQL-EXEC$GUARD-CHECK)
    (:DEFINITION RETURN-LAST))))

; no change because equiv is 'equal
(must-eval-to
 (rewrite$ '(member-equal b (binary-append u v)))
 '((MEMBER-EQUAL B (BINARY-APPEND U V))
   NIL))

; as above, but fails because of :must-rewrite t
(mf
 (rewrite$ '(member-equal b (binary-append u v))
           :must-rewrite t))

; test :equiv and :must-rewrite
(must-eval-to
 (rewrite$ '(member-equal b (binary-append u v))
           :equiv 'iff
           :must-rewrite t)
 '((IF (MEMBER-EQUAL B U)
       'T
       (MEMBER-EQUAL B V))
   ((:EQUIVALENCE IFF-IS-AN-EQUIVALENCE)
    (:REWRITE MEMBER-APPEND))))

; as above, with non-nil alist
(must-eval-to
 (rewrite$ '(member-equal b (binary-append x v))
           :alist '((x . u))
           :equiv 'iff)
 '((IF (MEMBER-EQUAL B U)
       'T
       (MEMBER-EQUAL B V))
   ((:EQUIVALENCE IFF-IS-AN-EQUIVALENCE)
    (:REWRITE MEMBER-APPEND))))

; as above, using an alist this time but fails because :must-rewrite t is
; illegal with non-nil alist
(mf
 (rewrite$ '(member-equal b (binary-append x v))
           :alist '((x . u))
           :equiv 'iff
           :must-rewrite t))

; test :geneqv (equivalent to above, except *geneqv-iff* involves a fake rune)
(must-eval-to
 (rewrite$ '(member-equal b (binary-append u v))
           :geneqv *geneqv-iff*
           :untranslate t)
 '((IF (MEMBER-EQUAL B U)
       T
       (MEMBER-EQUAL B V))
   (;(:EQUIVALENCE IFF-IS-AN-EQUIVALENCE)
    (:REWRITE MEMBER-APPEND))))

; test :geneqv, this time with a non-fake rune
(must-eval-to
 (rewrite$ '(member-equal b (binary-append u v))
           :geneqv (find-rules-of-rune
                    '(:EQUIVALENCE IFF-IS-AN-EQUIVALENCE)
                    (w state))
           :untranslate t)
 '((IF (MEMBER-EQUAL B U)
       T
       (MEMBER-EQUAL B V))
   ((:EQUIVALENCE IFF-IS-AN-EQUIVALENCE)
    (:REWRITE MEMBER-APPEND))))

; with untranslate this time
(must-eval-to
 (rewrite$ '(member-equal b (binary-append u v))
           :equiv 'iff
           :untranslate t)
 '((IF (MEMBER-EQUAL B U)
       T
       (MEMBER-EQUAL B V))
   ((:EQUIVALENCE IFF-IS-AN-EQUIVALENCE)
    (:REWRITE MEMBER-APPEND))))

; :obj t invokes linear arithmetic
(must-eval-to
 (rewrite$ '(< x (1+ x))
           :hyps '((rationalp x))
           :obj t
           :translate t)
 '('T
   ((:FAKE-RUNE-FOR-LINEAR NIL)
    (:FAKE-RUNE-FOR-TYPE-SET NIL))))

; unlike example just above, no simplification for default :obj
(must-eval-to
 (rewrite$ '(< x (1+ x))
           :hyps '((rationalp x))
           :translate t)
 '((< X (BINARY-+ '1 X)) NIL))

; contradiction in hypotheses using type-set reasoning
(mf
 (rewrite$ '(car (cons x y))
           :hyps '((atom x) (consp x))))

; contradiction in hypotheses using linear arithmetic reasoning
(mf
 (rewrite$ '(car (cons x y))
           :hyps '((rationalp x) (< 7 (+ x y)) (< x 3) (< y 2))
           :translate t))

; Finally, let's test some syntactic failures.

; :hints not supported (macroexpansion error)
(mf
 (rewrite$ '(car (cons x y))
           :hints (("Goal" :in-theory (enable nth))))
 :expected :hard)

; no problem here
(must-eval-to
 (rewrite$ '(car (cons x y))
           :expand '((nth n z)))
 '(X ((:REWRITE CAR-CONS))))

; as above, but error because :rrec and :expand are both specified
(mf
 (rewrite$ '(car (cons x y))
           :expand '((nth n z))
           :rrec `(REWRITE$-RECORD ((:STANDARD NIL . :ATOM)
                                    ,(ens state)
                                    (NIL NIL
                                         ((EQUAL . :NONE)
                                          (NTH N Z)
                                          ((:DEFINITION NTH))
                                          (NTH N L)
                                          IF (CONSP L)
                                          (IF (ZP N)
                                              (CAR L)
                                              (NTH (BINARY-+ '-1 N) (CDR L)))
                                          'NIL))
                                    (T NIL)
                                    (NIL)
                                    ((T) . :CLEAR)
                                    (NIL)
                                    ((500 100)
                                     SYS-CALL+ SYS-CALL*
                                     SYS-CALL SET-TEMP-TOUCHABLE-VARS
                                     SET-TEMP-TOUCHABLE-FNS
                                     SET-RAW-MODE-ON REMOVE-UNTOUCHABLE-FN
                                     OPEN-OUTPUT-CHANNEL! HONS-CLEAR!
                                     HONS-WASH! COERCE-STATE-TO-OBJECT
                                     COERCE-OBJECT-TO-STATE CREATE-STATE
                                     USER-STOBJ-ALIST F-PUT-LD-SPECIALS
                                     EV-FNCALL EV EV-LST EV-FNCALL!
                                     EV-FNCALL-REC EV-REC EV-REC-LST
                                     EV-REC-ACL2-UNWIND-PROTECT EV-FNCALL-W
                                     EV-FNCALL-W-BODY EV-W EV-W-LST SET-W
                                     SET-W! CLOAKED-SET-W! INSTALL-EVENT
                                     DEFUNS-FN1 PROCESS-EMBEDDED-EVENTS
                                     ENCAPSULATE-PASS-2 INCLUDE-BOOK-FN1
                                     MAYBE-ADD-COMMAND-LANDMARK
                                     UBT-UBU-FN1 INSTALL-EVENT-DEFUNS
                                     DEFTHM-FN1 DEFUNS-FN0
                                     LD-READ-EVAL-PRINT LD-LOOP LD-FN-BODY
                                     LD-FN0 LD-FN1 UPDATE-USER-STOBJ-ALIST
                                     BIG-N DECREMENT-BIG-N ZP-BIG-N
                                     PROTECTED-EVAL SET-SITE-EVISC-TUPLE
                                     SET-EVISC-TUPLE-LST SET-EVISC-TUPLE-FN1
                                     SET-IPRINT-AR INIT-IPRINT-FAL
                                     UPDATE-IPRINT-FAL-REC UPDATE-IPRINT-FAL
                                     INIT-IPRINT-FAL+ UNTOUCHABLE-MARKER
                                     STOBJ-EVISCERATION-ALIST
                                     TRACE-EVISCERATION-ALIST
                                     UPDATE-ENABLED-STRUCTURE-ARRAY
                                     APPLY-USER-STOBJ-ALIST-OR-KWOTE
                                     DOPPELGANGER-APPLY$-USERFN
                                     DOPPELGANGER-BADGE-USERFN))
                                   ((((:STANDARD NIL . :ATOM)
                                      ,(ens state) (NIL NIL)
                                      (NIL NIL)
                                      (NIL)
                                      ((T) . :CLEAR)
                                      (NIL)
                                      ((500 100)
                                       SYS-CALL+ SYS-CALL*
                                       SYS-CALL SET-TEMP-TOUCHABLE-VARS
                                       SET-TEMP-TOUCHABLE-FNS
                                       SET-RAW-MODE-ON REMOVE-UNTOUCHABLE-FN
                                       OPEN-OUTPUT-CHANNEL! HONS-CLEAR!
                                       HONS-WASH! COERCE-STATE-TO-OBJECT
                                       COERCE-OBJECT-TO-STATE CREATE-STATE
                                       USER-STOBJ-ALIST F-PUT-LD-SPECIALS
                                       EV-FNCALL EV EV-LST EV-FNCALL!
                                       EV-FNCALL-REC EV-REC EV-REC-LST
                                       EV-REC-ACL2-UNWIND-PROTECT EV-FNCALL-W
                                       EV-FNCALL-W-BODY EV-W EV-W-LST SET-W
                                       SET-W! CLOAKED-SET-W! INSTALL-EVENT
                                       DEFUNS-FN1 PROCESS-EMBEDDED-EVENTS
                                       ENCAPSULATE-PASS-2 INCLUDE-BOOK-FN1
                                       MAYBE-ADD-COMMAND-LANDMARK
                                       UBT-UBU-FN1 INSTALL-EVENT-DEFUNS
                                       DEFTHM-FN1 DEFUNS-FN0
                                       LD-READ-EVAL-PRINT LD-LOOP LD-FN-BODY
                                       LD-FN0 LD-FN1 UPDATE-USER-STOBJ-ALIST
                                       BIG-N DECREMENT-BIG-N ZP-BIG-N
                                       PROTECTED-EVAL SET-SITE-EVISC-TUPLE
                                       SET-EVISC-TUPLE-LST SET-EVISC-TUPLE-FN1
                                       SET-IPRINT-AR INIT-IPRINT-FAL
                                       UPDATE-IPRINT-FAL-REC UPDATE-IPRINT-FAL
                                       INIT-IPRINT-FAL+ UNTOUCHABLE-MARKER
                                       STOBJ-EVISCERATION-ALIST
                                       TRACE-EVISCERATION-ALIST
                                       UPDATE-ENABLED-STRUCTURE-ARRAY
                                       APPLY-USER-STOBJ-ALIST-OR-KWOTE
                                       DOPPELGANGER-APPLY$-USERFN
                                       DOPPELGANGER-BADGE-USERFN))
                                     NIL)
                                    (NIL NIL)
                                    (NIL (NIL) (NIL) NIL)
                                    (REWRITE$-LAST-LITERAL-FN)
                                    NIL
                                    ((((0) NIL . 0)
                                      (:EXPAND ((EQUAL . :NONE)
                                                (NTH N Z)
                                                ((:DEFINITION NTH))
                                                (NTH N L)
                                                IF (CONSP L)
                                                (IF (ZP N)
                                                    (CAR L)
                                                    (NTH (BINARY-+ '-1 N) (CDR L)))
                                                'NIL))))))))

; as above, but for two keywords instead of one
(mf
 (rewrite$ '(car (cons x y))
           :expand '((nth n z))
           :in-theory '(enable nth)
           :rrec `(REWRITE$-RECORD ((:STANDARD NIL . :ATOM)
                                    ,(ens state)
                                    (NIL NIL
                                         ((EQUAL . :NONE)
                                          (NTH N Z)
                                          ((:DEFINITION NTH))
                                          (NTH N L)
                                          IF (CONSP L)
                                          (IF (ZP N)
                                              (CAR L)
                                              (NTH (BINARY-+ '-1 N) (CDR L)))
                                          'NIL))
                                    (T NIL)
                                    (NIL)
                                    ((T) . :CLEAR)
                                    (NIL)
                                    ((500 100)
                                     SYS-CALL+ SYS-CALL*
                                     SYS-CALL SET-TEMP-TOUCHABLE-VARS
                                     SET-TEMP-TOUCHABLE-FNS
                                     SET-RAW-MODE-ON REMOVE-UNTOUCHABLE-FN
                                     OPEN-OUTPUT-CHANNEL! HONS-CLEAR!
                                     HONS-WASH! COERCE-STATE-TO-OBJECT
                                     COERCE-OBJECT-TO-STATE CREATE-STATE
                                     USER-STOBJ-ALIST F-PUT-LD-SPECIALS
                                     EV-FNCALL EV EV-LST EV-FNCALL!
                                     EV-FNCALL-REC EV-REC EV-REC-LST
                                     EV-REC-ACL2-UNWIND-PROTECT EV-FNCALL-W
                                     EV-FNCALL-W-BODY EV-W EV-W-LST SET-W
                                     SET-W! CLOAKED-SET-W! INSTALL-EVENT
                                     DEFUNS-FN1 PROCESS-EMBEDDED-EVENTS
                                     ENCAPSULATE-PASS-2 INCLUDE-BOOK-FN1
                                     MAYBE-ADD-COMMAND-LANDMARK
                                     UBT-UBU-FN1 INSTALL-EVENT-DEFUNS
                                     DEFTHM-FN1 DEFUNS-FN0
                                     LD-READ-EVAL-PRINT LD-LOOP LD-FN-BODY
                                     LD-FN0 LD-FN1 UPDATE-USER-STOBJ-ALIST
                                     BIG-N DECREMENT-BIG-N ZP-BIG-N
                                     PROTECTED-EVAL SET-SITE-EVISC-TUPLE
                                     SET-EVISC-TUPLE-LST SET-EVISC-TUPLE-FN1
                                     SET-IPRINT-AR INIT-IPRINT-FAL
                                     UPDATE-IPRINT-FAL-REC UPDATE-IPRINT-FAL
                                     INIT-IPRINT-FAL+ UNTOUCHABLE-MARKER
                                     STOBJ-EVISCERATION-ALIST
                                     TRACE-EVISCERATION-ALIST
                                     UPDATE-ENABLED-STRUCTURE-ARRAY
                                     APPLY-USER-STOBJ-ALIST-OR-KWOTE
                                     DOPPELGANGER-APPLY$-USERFN
                                     DOPPELGANGER-BADGE-USERFN))
                                   ((((:STANDARD NIL . :ATOM)
                                      ,(ens state) (NIL NIL)
                                      (NIL NIL)
                                      (NIL)
                                      ((T) . :CLEAR)
                                      (NIL)
                                      ((500 100)
                                       SYS-CALL+ SYS-CALL*
                                       SYS-CALL SET-TEMP-TOUCHABLE-VARS
                                       SET-TEMP-TOUCHABLE-FNS
                                       SET-RAW-MODE-ON REMOVE-UNTOUCHABLE-FN
                                       OPEN-OUTPUT-CHANNEL! HONS-CLEAR!
                                       HONS-WASH! COERCE-STATE-TO-OBJECT
                                       COERCE-OBJECT-TO-STATE CREATE-STATE
                                       USER-STOBJ-ALIST F-PUT-LD-SPECIALS
                                       EV-FNCALL EV EV-LST EV-FNCALL!
                                       EV-FNCALL-REC EV-REC EV-REC-LST
                                       EV-REC-ACL2-UNWIND-PROTECT EV-FNCALL-W
                                       EV-FNCALL-W-BODY EV-W EV-W-LST SET-W
                                       SET-W! CLOAKED-SET-W! INSTALL-EVENT
                                       DEFUNS-FN1 PROCESS-EMBEDDED-EVENTS
                                       ENCAPSULATE-PASS-2 INCLUDE-BOOK-FN1
                                       MAYBE-ADD-COMMAND-LANDMARK
                                       UBT-UBU-FN1 INSTALL-EVENT-DEFUNS
                                       DEFTHM-FN1 DEFUNS-FN0
                                       LD-READ-EVAL-PRINT LD-LOOP LD-FN-BODY
                                       LD-FN0 LD-FN1 UPDATE-USER-STOBJ-ALIST
                                       BIG-N DECREMENT-BIG-N ZP-BIG-N
                                       PROTECTED-EVAL SET-SITE-EVISC-TUPLE
                                       SET-EVISC-TUPLE-LST SET-EVISC-TUPLE-FN1
                                       SET-IPRINT-AR INIT-IPRINT-FAL
                                       UPDATE-IPRINT-FAL-REC UPDATE-IPRINT-FAL
                                       INIT-IPRINT-FAL+ UNTOUCHABLE-MARKER
                                       STOBJ-EVISCERATION-ALIST
                                       TRACE-EVISCERATION-ALIST
                                       UPDATE-ENABLED-STRUCTURE-ARRAY
                                       APPLY-USER-STOBJ-ALIST-OR-KWOTE
                                       DOPPELGANGER-APPLY$-USERFN
                                       DOPPELGANGER-BADGE-USERFN))
                                     NIL)
                                    (NIL NIL)
                                    (NIL (NIL) (NIL) NIL)
                                    (REWRITE$-LAST-LITERAL-FN)
                                    NIL
                                    ((((0) NIL . 0)
                                      (:EXPAND ((EQUAL . :NONE)
                                                (NTH N Z)
                                                ((:DEFINITION NTH))
                                                (NTH N L)
                                                IF (CONSP L)
                                                (IF (ZP N)
                                                    (CAR L)
                                                    (NTH (BINARY-+ '-1 N) (CDR L)))
                                                'NIL))))))))

; illegal :repeat
(mf
 (rewrite$ '(car (cons x y))
           :repeat -1))

; both :equiv and :geneqv
(mf
 (rewrite$ '(member-equal b (binary-append u v))
           :equiv 'iff
           :geneqv *geneqv-iff*))

; :equiv is not symbol
(mf
 (rewrite$ '(member-equal b (binary-append u v))
           :equiv 17))

; :equiv is not equivalence relation
(mf
 (rewrite$ '(member-equal b (binary-append u v))
           :equiv 'foo))

; illegal value for :prove-forced-assumptions
(mf
 (rewrite$ '(car (cons x y))
           :prove-forced-assumptions 'foo))

; ill-formed rewrite$-record supplied to :rrec
(mf
 (rewrite$ '(car (cons x y))
           :rrec 17))

; weak rewrite$-record supplied to :rrec that has bad :rcnst field
(mf
 (rewrite$ '(car (cons x y))
           :rrec (make rewrite$-record :rcnst 23)))

(in-theory (disable append-assoc-with-force))

(make-event
 (b* (((er rrec)
       (make-rrec nil nil nil 'top (w state) state)))
   (value `(defconst *rrec-1* ',rrec))))

; valid rrec
(must-eval-to
 (rewrite$ '(append (append x y) z)
             :translate t
             :untranslate t
             :rrec *rrec-1*)
 '((APPEND X Y Z)
   ((:REWRITE APPEND-ASSOC))))

; Tests of simplifying hypotheses.

(defmacro must-eval-to-rh (form result)
  `(must-eval-to (b* (((er (list* hyps ?rrec ttree ?pairs))
                       ,form))
                   (value (list hyps ttree)))
                 ,result))

(defun p1 (x) (symbol-listp x))

(must-eval-to-rh
 (rewrite$-hyps '((p1 x)))
 '(((SYMBOL-LISTP X))
   ((LEMMA (:DEFINITION P1)))))

(defun p2 (x) (and (true-listp x) (eql (len x) 5)))

(must-eval-to-rh
 (rewrite$-hyps '((p1 x) (p2 x)))
 '(((SYMBOL-LISTP X)
    (TRUE-LISTP X)
    (EQUAL (LEN X) '5))
   ((LEMMA (:DEFINITION P2)
           (:DEFINITION P1))
;   (SPLITTER-IF-INTRO (:DEFINITION P2))
    )))

; As above, but two iterations lets us benefit by forward-chaining from
; symbol-listp to true-listp.
(must-eval-to-rh
 (rewrite$-hyps '((p1 x) (p2 x)) :repeat 2)
 '(((SYMBOL-LISTP X) (EQUAL (LEN X) '5))
   ((LEMMA (:FORWARD-CHAINING SYMBOL-LISTP-FORWARD-TO-TRUE-LISTP)
           (:TYPE-PRESCRIPTION SYMBOL-LISTP)
           (:DEFINITION P2)
           (:DEFINITION P1))
;   (SPLITTER-IF-INTRO (:DEFINITION P2))
    (PT 0))))

(defun p3 (x) (atom x))

(defun p4 (x) (p3 x))

(must-eval-to-rh
 (rewrite$-hyps '((consp x) (not (p4 x))))
 '(((CONSP X))
   ((LEMMA (:DEFINITION P4)
           (:DEFINITION P3)))))

(mf
 (rewrite$-hyps '((consp x) (p4 x))))

(mf
 (rewrite$-hyps '((p4 x) (consp x))))

(defthm p3-forward
  (implies (p3 x)
           (not (consp x)))
  :rule-classes :forward-chaining)

(in-theory (disable p3))

(mf
 (rewrite$-hyps '((p4 x) (consp x))))

(must-eval-to-rh
 (rewrite$-hyps '((and x y)) :translate t)
 '((X Y) NIL))

(must-eval-to-rh
 (rewrite$-hyps '((if x y 'nil)))
 '((X Y) NIL))

(must-eval-to-rh
 (rewrite$-hyps '((not (if x x y))))
 '(((NOT X) (NOT Y)) NIL))

(must-eval-to-rh
 (rewrite$-hyps '((not (if (not x) t y))) :translate t)
 '((X (NOT Y))
   ((LEMMA (:DEFINITION NOT))
;   (SPLITTER-IF-INTRO (:DEFINITION NOT))
    )))

; Tests of simplifying contexts.

(defmacro must-eval-to-context (form result)
  `(must-eval-to (er-let* ((x ,form))
                   (value (list* (car x)
                                 (access rewrite$-record (cadr x) :type-alist)
                                 (cddr x))))
                 ,result))

(make-event
 (b* (((er ; from rewrite$-hyps-return
        (list* ?hyps rrec ?ttree ?pairs))
       (rewrite$-hyps nil)))
   (value `(defconst *rrec-2* ',rrec))))

(must-eval-to-context
 (rewrite$-context '((consp (car (cons x x)))) *rrec-2*)
 '(((CONSP X))
   ((X 3072))
   ((LEMMA (:REWRITE CAR-CONS)))))

(defun p5 (x)
  (consp x))

(defun p6 (x)
  (and (consp x) (natp (car x))))

(make-event
 (b* (((er ; from rewrite$-hyps-return
        (list* hyps rrec ttree ?pairs))
       (rewrite$-hyps '((p5 x) (p5 y)) :translate t)))
   (value `(progn (assert-event (equal ',hyps '((consp x) (consp y))))
                  (assert-event (equal ',ttree '((LEMMA (:DEFINITION P5)))))
                  (defconst *rrec-3* ',rrec)))))

(must-eval-to-context
 (rewrite$-context '((p6 x) (p6 y) (p6 z)) *rrec-3*)
 '(((INTEGERP (CAR X))
    (NOT (< (CAR X) '0))
    (INTEGERP (CAR Y))
    (NOT (< (CAR Y) '0))
    (CONSP Z)
    (INTEGERP (CAR Z))
    (NOT (< (CAR Z) '0)))
   (((< (CAR Z) '0) 128)
    ((CAR Z) 7)
    ((CAR Z) 23)
    (Z 3072)
    ((< (CAR Y) '0) 128)
    ((CAR Y) 7)
    ((CAR Y) 23)
    ((< (CAR X) '0) 128)
    ((CAR X) 7)
    ((CAR X) 23)
    (Y 3072)
    (X 3072))
   ((SPLITTER-IF-INTRO (:DEFINITION P6)
                       (:DEFINITION NATP))
    (LEMMA (:DEFINITION P6)
           (:DEFINITION NATP)))))

; Next we check that a later member of the context can't be used when rewriting
; an earlier member.  See comments below.

(defthm p6-implies-p5
  (implies (p6 x)
           (p5 x)))

(in-theory (disable p5 p6))

(make-event
 (b* (((er ; from rewrite$-hyps-return
        (list* ?hyps rrec ?ttree ?pairs))
       (rewrite$-hyps nil)))
   (value `(defconst *rrec-4* ',rrec))))

; The first member of the context is used when rewriting the second.
(must-eval-to-context
 (rewrite$-context '((and (p6 x) (p6 x)) (p5 x)) *rrec-4*
                   :translate t)
 '(((P6 X))
   (((P6 X)
     256 (LEMMA (:TYPE-PRESCRIPTION P6))))
   ((LEMMA (:REWRITE P6-IMPLIES-P5)
           (:TYPE-PRESCRIPTION P6)))))

; Same as above; the use of :repeat doesn't change the result.
(must-eval-to-context
 (rewrite$-context '((and (p6 x) (p6 x)) (p5 x)) *rrec-4*
                   :translate t
                   :repeat 2)
 '(((P6 X))
   (((P6 X)
     256 (LEMMA (:TYPE-PRESCRIPTION P6))))
   ((LEMMA (:REWRITE P6-IMPLIES-P5)
           (:TYPE-PRESCRIPTION P6)))))

; Even with :repeat 2, we don't use (p6 x) to rewrite (p5 x).  The reason for
; using :repeat 2 is to check that we don't save the type-alist generated by
; the first pass when we start the second pass.
(must-eval-to-context
 (rewrite$-context '((p5 x) (and (p6 x) (p6 x))) *rrec-4*
                   :translate t
                   :repeat 2)
 '(((P5 X) (P6 X))
   (((P6 X)
     256 (LEMMA (:TYPE-PRESCRIPTION P6)))
    ((P5 X)
     256 (LEMMA (:TYPE-PRESCRIPTION P5))))
   ((LEMMA (:TYPE-PRESCRIPTION P6))
    (RW-CACHE-ANY-TAG T
                      (P6-IMPLIES-P5 ((536870909 1 REWROTE-TO P6 X)
                                      ((X . X))
                                      P6 X))))))

(defthm p6-implies-p5-forward
  (implies (p6 x)
           (p5 x))
  :rule-classes :forward-chaining)

(in-theory (disable p6-implies-p5))

(defun p7 (x)
  (and (p5 x)
       (integerp (car x))))

(make-event
 (b* (((er ; from rewrite$-hyps-return
        (list* ?hyps rrec ?ttree ?pairs))
       (rewrite$-hyps '((p6 x)))))
   (value `(defconst *rrec-5* ',rrec))))

(must-eval-to-context
 (rewrite$-context '((p6 x) (p7 x)) *rrec-5*)
 '(((INTEGERP (CAR X)))
   (((CAR X) 23)
    ((P5 X)
     256
     (LEMMA (:TYPE-PRESCRIPTION P5)
            (:FORWARD-CHAINING P6-IMPLIES-P5-FORWARD)
            (:TYPE-PRESCRIPTION P6))
     (PT 0))
    ((P6 X)
     256 (LEMMA (:TYPE-PRESCRIPTION P6))))
   ((LEMMA (:DEFINITION P7)
           (:TYPE-PRESCRIPTION P5)
           (:FORWARD-CHAINING P6-IMPLIES-P5-FORWARD)
           (:TYPE-PRESCRIPTION P6))
    (PT 0))))

; Using context to rewrite a term.

(must-eval-to
 (b* (((er (list* ?lst rrec ?ttree ?pairs))
       (rewrite$-context '((p7 x)) *rrec-5*)))
   (rewrite$ '(list (natp (car a)))
             :alist '((a . x))
             :rrec rrec
             :translate t
             :untranslate t))
 '((LIST (NOT (< (CAR X) 0)))
   ((:DEFINITION NATP))))

; Test that rewriting a true context produces the empty list.

(make-event
 (b* (((er ; from rewrite$-hyps-return
        (list* ?hyps rrec ?ttree ?pairs))
       (rewrite$-hyps '((p6 x) (natp (car x))))))
   (value `(defconst *rrec-6* ',rrec))))

(assert-event (equal *rewrite$-true-context* nil))

(must-eval-to-context
 (rewrite$-context '((p5 x) (p7 x)) *rrec-6*)
 '(NIL ; *rewrite$-true-context* (see assert-event above)
   (((P5 X)
     256
     (LEMMA (:TYPE-PRESCRIPTION P5)
            (:FORWARD-CHAINING P6-IMPLIES-P5-FORWARD)
            (:TYPE-PRESCRIPTION P6))
     (PT 0))
    ((< (CAR X) '0) 128)
    ((CAR X) 7)
    ((CAR X) 23)
    ((P6 X)
     256 (LEMMA (:TYPE-PRESCRIPTION P6))))
   ((LEMMA (:DEFINITION P7)
           (:TYPE-PRESCRIPTION P5)
           (:FORWARD-CHAINING P6-IMPLIES-P5-FORWARD)
           (:TYPE-PRESCRIPTION P6))
    (PT 0))))

; Test that rewriting a contradictory context produces an error or the list
; ('nil), depending on :contradiction-ok.

(make-event
 (b* (((er ; from rewrite$-hyps-return
        (list* ?hyps rrec ?ttree ?pairs))
       (rewrite$-hyps nil)))
   (value `(defconst *rrec-7* ',rrec))))

(mf
 (rewrite$-context '((natp x) (natp y) (symbolp x) (consp z)) *rrec-7*))

(assert-event (equal *rewrite$-false-context* '('nil)))

(must-eval-to-context
 (rewrite$-context '((natp x) (natp y) (symbolp x) (consp z)) *rrec-7*
                   :contradiction-ok t)
 '(('NIL) ; *rewrite$-false-context* (see assert-event above)
   NIL
   ((SPLITTER-IF-INTRO (:DEFINITION NATP))
    (LEMMA (:DEFINITION NATP)))))
