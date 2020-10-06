; Copyright (C) 2020, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Note that rewrite$ is used in community book
; kestrel/apt/simplify-defun-impl.lisp.  That book exercises advanced options
; rcnst and saved-pspv, and is tested extensively, so here we do very little
; testing pertaining to those options.

(in-package "ACL2")

(include-book "rewrite-dollar")
(include-book "std/testing/must-eval-to" :dir :system)
(include-book "std/testing/must-fail" :dir :system)

; basic
(must-eval-to
 (rewrite$ '(cons (car x) (cdr x)))
 '((IF (CONSP X) X '(NIL))
   ((:REWRITE CONS-CAR-CDR))))

; not a termp
(must-fail
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
(must-fail
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

(defthm append-assoc
  (equal (append (append x y) z)
         (append x y z)))

; use new rule
(must-eval-to
 (rewrite$ '(binary-append (binary-append x y) z))
 '((BINARY-APPEND X (BINARY-APPEND Y Z))
   ((:REWRITE APPEND-ASSOC))))

; as above, with sufficient :step-limit
(must-eval-to
 (rewrite$ '(binary-append (binary-append x y) z)
           :step-limit 100)
 '((BINARY-APPEND X (BINARY-APPEND Y Z))
   ((:REWRITE APPEND-ASSOC))))

; as above but with insufficient :step-limit
(must-fail
 (rewrite$ '(binary-append (binary-append x y) z)
           :step-limit 1)
 :expected :hard)

; no rewriting because of :in-theory
(must-eval-to
 (rewrite$ '(binary-append (binary-append x y) z)
           :in-theory '(disable append-assoc))
 '((BINARY-APPEND (BINARY-APPEND X Y) Z)
   NIL))

(add-default-hints 
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

(remove-default-hints 
 '('(:in-theory (disable append-assoc))))

(defthm append-assoc-with-force
  (implies (force (true-listp x))
           (equal (append (append x y) z)
                  (append x y z))))

; :in-theory
(must-eval-to
 (rewrite$ '(binary-append (binary-append x y) z)
           :in-theory '(disable append-assoc-with-force))
 '((BINARY-APPEND X (BINARY-APPEND Y Z))
   ((:REWRITE APPEND-ASSOC))))

; failure because of forcing
(must-fail
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
(must-fail ; uses forcing
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

(defthm member-append
  (iff (member a (append x y))
       (or (member a x)
           (member a y))))

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
(must-fail
 (rewrite$ '(member-equal b (binary-append u v))
           :must-rewrite t))

; test :equiv
(must-eval-to
 (rewrite$ '(member-equal b (binary-append u v))
           :equiv 'iff)
 '((IF (MEMBER-EQUAL B U)
       'T
       (MEMBER-EQUAL B V))
   ((:EQUIVALENCE IFF-IS-AN-EQUIVALENCE)
    (:REWRITE MEMBER-APPEND))))

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
(must-fail
 (rewrite$ '(car (cons x y))
           :hyps '((atom x) (consp x))))

; contradiction in hypotheses using linear arithmetic reasoning
(must-fail
 (rewrite$ '(car (cons x y))
           :hyps '((rationalp x) (< 7 (+ x y)) (< x 3) (< y 2))
           :translate t))

; Finally, let's test some syntactic failures.

; :hints not supported (macroexpansion error)
(must-fail
 (rewrite$ '(car (cons x y))
           :hints (("Goal" :in-theory (enable nth))))
 :expected :hard)

; illegal :step-limit
(must-fail
 (rewrite$ '(car (cons x y))
           :step-limit 'a))

; no problem here
(must-eval-to
 (rewrite$ '(car (cons x y))
           :expand '((nth n z)))
 '(X ((:REWRITE CAR-CONS))))

; as above, but error because :rcnst and :in-theory are both specified
; (where the rcnst came from evaluating the preceding form after
; (trace$ rewrite$-rcnst))
(must-fail
 (rewrite$ '(car (cons x y))
           :expand '((nth n z))
           :rcnst `((:STANDARD NIL . :ATOM)
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
                     DOPPELGANGER-BADGE-USERFN))))

; illegal :repeat
(must-fail
 (rewrite$ '(car (cons x y))
           :repeat -1))

; both :equiv and :geneqv
(must-fail
 (rewrite$ '(member-equal b (binary-append u v))
           :equiv 'iff
           :geneqv *geneqv-iff*))

; :equiv is not symbol
(must-fail
 (rewrite$ '(member-equal b (binary-append u v))
           :equiv 17))

; :equiv is not equivalence relation
(must-fail
 (rewrite$ '(member-equal b (binary-append u v))
           :equiv 'foo))

; illegal value for :prove-forced-assumptions
(must-fail
 (rewrite$ '(car (cons x y))
           :prove-forced-assumptions 'foo))

; ill-formed pspv supplied to :saved-pspv
(must-fail
 (rewrite$ '(car (cons x y))
           :saved-pspv 17))

(must-fail
 (rewrite$ '(car (cons x y))
           :alist '((x . (cons u v)))
           :must-rewrite t))
