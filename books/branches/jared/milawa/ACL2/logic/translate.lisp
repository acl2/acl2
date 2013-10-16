;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;           __    __        __    __                                        ;;
;;          /  \  /  \      (__)  |  |    ____   ___      __    ____         ;;
;;         /    \/    \      __   |  |   / _  |  \  \ __ /  /  / _  |        ;;
;;        /  /\    /\  \    |  |  |  |  / / | |   \  '  '  /  / / | |        ;;
;;       /  /  \__/  \  \   |  |  |  |  \ \_| |    \  /\  /   \ \_| |        ;;
;;      /__/          \__\  |__|  |__|   \____|     \/  \/     \____|        ;;
;; ~ ~~ \  ~ ~  ~_~~ ~/~ /~ | ~|~ | ~| ~ /~_ ~|~ ~  ~\  ~\~ ~  ~ ~  |~~    ~ ;;
;;  ~ ~  \~ \~ / ~\~ / ~/ ~ |~ | ~|  ~ ~/~/ | |~ ~~/ ~\/ ~~ ~ / / | |~   ~   ;;
;; ~ ~  ~ \ ~\/ ~  \~ ~/ ~~ ~__|  |~ ~  ~ \_~  ~  ~  .__~ ~\ ~\ ~_| ~  ~ ~~  ;;
;;  ~~ ~  ~\  ~ /~ ~  ~ ~  ~ __~  |  ~ ~ \~__~| ~/__~   ~\__~ ~~___~| ~ ~    ;;
;; ~  ~~ ~  \~_/  ~_~/ ~ ~ ~(__~ ~|~_| ~  ~  ~~  ~  ~ ~~    ~  ~   ~~  ~  ~  ;;
;;                                                                           ;;
;;            A   R e f l e c t i v e   P r o o f   C h e c k e r            ;;
;;                                                                           ;;
;;       Copyright (C) 2005-2009 by Jared Davis <jared@cs.utexas.edu>        ;;
;;                                                                           ;;
;; This program is free software; you can redistribute it and/or modify it   ;;
;; under the terms of the GNU General Public License as published by the     ;;
;; Free Software Foundation; either version 2 of the License, or (at your    ;;
;; option) any later version.                                                ;;
;;                                                                           ;;
;; This program is distributed in the hope that it will be useful, but       ;;
;; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABIL-  ;;
;; ITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public      ;;
;; License for more details.                                                 ;;
;;                                                                           ;;
;; You should have received a copy of the GNU General Public License along   ;;
;; with this program (see the file COPYING); if not, write to the Free       ;;
;; Software Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA    ;;
;; 02110-1301, USA.                                                          ;;
;;                                                                           ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "MILAWA")
(include-book "terms")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)



(defund logic.translate-and-term (args)
  ;; Args are a list of terms.  We build an if-expression corresponding to the
  ;; conjunction of these terms, lazily evaluated in order.  The result of this
  ;; if expression will be the value of the last argument, if all arguments are
  ;; non-nil, or nil otherwise.
  ;;
  ;; Examples
  ;;
  ;;   (AND) => T
  ;;   (AND X1) => X1
  ;;   (AND X1 X2) => (IF X1 X2 'NIL)
  ;;   (AND X1 X2 X3) => (IF X1 (IF X2 X3 'NIL) 'NIL)
  ;;   ...
  (declare (xargs :guard (logic.term-listp args)))
  (if (consp args)
      (if (consp (cdr args))
          ;; At least two arguments.
          (logic.function 'if (list (first args)
                                    (logic.translate-and-term (cdr args))
                                    ''nil))
        ;; Only a single argument.
        (first args))
    ;; No arguments.
    ''t))

(defthm logic.termp-of-logic.translate-and-term
  (implies (force (logic.term-listp args))
           (equal (logic.termp (logic.translate-and-term args))
                  t))
  :hints(("Goal" :in-theory (enable logic.translate-and-term))))



(defund logic.translate-let-term (vars terms body)
  ;; Body is a term, vars is a list of variables, and terms is a list of terms
  ;; with equal length to vars.  We want to translate:
  ;;
  ;;  (let ((var1 term1) (var2 term2) ... (varN termN)) body)
  ;;
  ;; into a lambda term, i.e.,
  ;;
  ;;  ((lambda (var1 ... varN) body) term1 ... termN)
  ;;
  ;; Except that, unlike lambdas, we don't require every variable used in body
  ;; to be bound by the let variables, so we need to "fill in" these extra
  ;; variables when we create the lambda.  Hence, the actual lambda we will
  ;; create is:
  ;;
  ;;  ((lambda (extra1 ... extraM var1 ... varN) body)
  ;;   extra1 ... extraM term1 ... termN)
  ;;
  ;; Where extra1, ..., extraM are the variables which occur in body other than
  ;; var1, ..., varN.  We just bind each of these variables to themselves in
  ;; the lambda we produce.
  (declare (xargs :guard (and (true-listp vars)
                              (logic.variable-listp vars)
                              (uniquep vars)
                              (logic.termp body)
                              (true-listp terms)
                              (logic.term-listp terms)
                              (same-lengthp vars terms))))
  (let* ((body-vars (remove-duplicates (logic.term-vars body)))
         (id-vars   (sort-symbols (difference body-vars vars)))
         (formals   (app id-vars vars))
         (actuals   (app id-vars terms)))
    (logic.lambda formals body actuals)))

(defthmd lemma-for-logic.termp-of-logic.translate-let-term
  (equal (subsetp x (app (sort-symbols (difference (remove-duplicates x) y)) y))
         t)
  :hints(("Goal"
          :use ((:instance subsetp-badguy-membership-property
                           (x x)
                           (y (app (sort-symbols (difference (remove-duplicates x) y))
                                   y)))))))

(defthm logic.termp-of-logic.translate-let-term
   (implies (and (force (true-listp vars))
                 (force (logic.variable-listp vars))
                 (force (uniquep vars))
                 (force (logic.termp body))
                 (force (true-listp terms))
                 (force (logic.term-listp terms))
                 (force (equal (len vars) (len terms))))
            (equal (logic.termp (logic.translate-let-term vars terms body))
                   t))
   :hints(("Goal"
           :in-theory (enable logic.translate-let-term
                              lemma-for-logic.termp-of-logic.translate-let-term))))



; SPECIAL ENHANCEMENT FOR MLISP
;
; As of my dissertation, logic.translate-or-term built its IF-expression in a
; relatively simple way.  In particular, we had:
;
;   (OR) => NIL
;   (OR X1) => X1
;   (OR X1 X2) => (IF X1 X1 X2)
;   (OR X1 X2 X3) => (IF X1 X1 (IF X2 X2 X3))
;   ...
;
; However, when we tried to port the system to MLISP, we wanted to avoid this
; naive expansion to avoid recomputation when X1 is expensive to compute.  The
; basic idea is to now interpret:
;
;   (OR X1 X2) => (LET ((SPECIAL-VAR-FOR-OR X1))
;                   (IF SPECIAL-VAR-FOR-OR
;                       SPECIAL-VAR-FOR-OR
;                     ...))
;
; For this to be sound, we need to ensure that SPECIAL-VAR-FOR-OR is not free
; within the dots.  If this is not the case, we default to the previous
; behavior, which is sub-optimal but sound.  We also print a warning message in
; this case.

(defund logic.translate-or-term (args)
  ;; Args are a list of terms.  We build an if-expression corresponding to the
  ;; disjunction of these terms, lazily evaluated in order.  The result of this
  ;; if expression is the value of the first non-nil argument, or nil if all of
  ;; the arguments are nil.
  (declare (xargs :guard (logic.term-listp args)))
  (if (consp args)
      (if (consp (cdr args))
          (let* ((else-term (logic.translate-or-term (cdr args)))
                 (cheap-p   (or (logic.variablep (car args))
                                (logic.constantp (car args)))))
            (if (or cheap-p
                    (memberp 'special-var-for-or (logic.term-vars else-term)))
                ;; Use (IF X1 X1 ...) style expansion
                (ACL2::prog2$
                 (or cheap-p
                     (ACL2::cw "TRANSLATE WARNING: using suboptimal 'or' translation.~%"))
                 (logic.function 'if (list (car args) (car args) else-term)))
              ;; Use (LET ((SPECIAL-VAR-FOR-OR X1))
              ;;       (IF SPECIAL-VAR-FOR-OR
              ;;           SPECIAL-VAR-FOR-OR
              ;;         ...))
              (logic.translate-let-term (list 'special-var-for-or)
                                        (list (car args))
                                        (logic.function 'if (list 'special-var-for-or
                                                                  'special-var-for-or
                                                                  else-term)))))
        ;; Only a single argument.
        (first args))
    ;; No arguments.
    ''nil))


(defthm logic.termp-of-logic.translate-or-term
  (implies (force (logic.term-listp args))
           (equal (logic.termp (logic.translate-or-term args))
                  t))
  :hints(("Goal" :in-theory (enable logic.translate-or-term))))




(defund logic.translate-list-term (args)
  ;; Args is a list of terms.  We build a term which corresponds to the expansion
  ;; of (list arg1 ... argN) into calls of cons.
  ;;
  ;; Examples
  ;;
  ;;   (LIST) => NIL
  ;;   (LIST X1) => (CONS X1 NIL)
  ;;   (LIST X1 X2) => (CONS X1 (CONS X2 NIL))
  ;;   (LIST X1 X2 X3) => (CONS X1 (CONS X2 (CONS X3 NIL)))
  ;;   ...
  (declare (xargs :guard (logic.term-listp args)))
  (if (consp args)
      (logic.function 'cons (list (car args)
                                  (logic.translate-list-term (cdr args))))
    ''nil))

(defthm logic.termp-of-logic.translate-list-term
  (implies (force (logic.term-listp args))
           (equal (logic.termp (logic.translate-list-term args))
                  t))
  :hints(("Goal" :in-theory (enable logic.translate-list-term))))




(defund logic.translate-cond-term (tests thens)
  ;; Tests and thens are equal-length lists of terms.  We build an
  ;; if-expression of the form, If TEST<1>, then THEN<1>, else if TEST<2>, then
  ;; THEN<2>, ..., otherwise NIL.
  ;;
  ;; (COND) => NIL
  ;;
  ;; (COND (TEST1 THEN1)) =>
  ;;  (IF TEST1 THEN1 NIL)
  ;;
  ;; (COND (TEST1 THEN1) (TEST2 THEN2)) =>
  ;;  (IF TEST1 THEN1 (IF TEST2 THEN2 NIL))
  ;;
  ;; (COND (TEST1 THEN1) (TEST2 THEN2) (TEST3 THEN3)) =>
  ;;  (IF TEST1 THEN1 (IF TEST2 THEN2 (IF TEST3 THEN3 NIL)))
  ;;
  ;; ...
  (declare (xargs :guard (and (logic.term-listp tests)
                              (logic.term-listp thens)
                              (equal (len tests) (len thens)))))
  (if (consp tests)
      (let ((test1 (car tests))
            (then1 (car thens)))
        ;; Previously we did an optimization, where if test1 is ''t then we just
        ;; use then1.  But now we'll go ahead and construct the if anyway, because
        ;; that makes this simpler and lets us explain cond more simply.
        ;(if (equal test1 ''t)
            ;; Optimization: if we encounter (t foo) as a pair, we know the
            ;; test will be true, so we just construct the term foo.
         ;   then1
          ;; Otherwise, we construct the whole if term.
        (logic.function 'if (list test1
                                  then1
                                  (logic.translate-cond-term (cdr tests) (cdr thens)))))
    ''nil))

(defthm logic.termp-of-logic.translate-cond-term
  (implies (and (force (logic.term-listp tests))
                (force (logic.term-listp thens))
                (force (equal (len tests) (len thens))))
           (equal (logic.termp (logic.translate-cond-term thens tests))
                  t))
  :hints(("Goal"
          :induct (cdr-cdr-induction thens tests)
          :in-theory (enable logic.translate-cond-term))))



(defund logic.translate-let*-term (vars terms body)
  ;; Body is a term, vars is a list of variables, and terms is a list of terms
  ;; with equal length to vars.  We want to translate:
  ;;
  ;;   (let* ((var1 term1) (var2 term2) ... (varN termN)) body)
  ;;
  ;; into
  ;;
  ;;   (let ((var1 term1))
  ;;     (let* ((var2 term2) ... (varN termN)) body))
  (declare (xargs :guard (and (true-listp vars)
                              (logic.variable-listp vars)
                              (true-listp terms)
                              (logic.term-listp terms)
                              (same-lengthp vars terms)
                              (logic.termp body))
                  :verify-guards nil))
  (if (consp vars)
      (logic.translate-let-term
       (list (car vars))
       (list (car terms))
       (logic.translate-let*-term (cdr vars)
                                  (cdr terms)
                                  body))
    body))

(defthm logic.termp-of-logic.translate-let*-term
   (implies (and (force (true-listp vars))
                 (force (logic.variable-listp vars))
                 (force (logic.termp body))
                 (force (true-listp terms))
                 (force (logic.term-listp terms))
                 (force (equal (len vars) (len terms))))
            (equal (logic.termp (logic.translate-let*-term vars terms body))
                   t))
   :hints(("Goal" :in-theory (enable logic.translate-let*-term))))

(verify-guards logic.translate-let*-term)





;; (defund logic.translate-lambda-term (vars body terms)
;;   ;; Body is a term; vars is a list of variables; terms is a list of terms with
;;   ;; equal length to vars.
;;   ;;
;;   ;; We are to create the lambda term which is essentially:
;;   ;;
;;   ;;   ((lambda vars body) terms)
;;   ;;
;;   ;; But we permit vars to not include all of the variables mentioned in the
;;   ;; body.  To fix this, we will actually write something like this instead:
;;   ;;
;;   ;;   ((lambda (var1 ... varN free1 ... freeM) body)
;;   ;;    (act1 ... actN free1 ... freeM))
;;   ;;
;;   ;; Where free1 ... freeM are the free variables in the body other than var1
;;   ;; ... varN.  In other words, we bind miscellaneous free variables to
;;   ;; themselves.
;;   (declare (xargs :guard (and (true-listp vars)
;;                               (logic.variable-listp vars)
;;                               (uniquep vars)
;;                               (logic.termp body)
;;                               (true-listp terms)
;;                               (logic.term-listp terms)
;;                               (same-lengthp vars terms))))
;;   (let* ((body-vars     (remove-duplicates (logic.term-vars body)))
;;          (identity-vars (fast-difference$ body-vars vars nil))
;;          (formals       (revappend identity-vars vars))
;;          (actuals       (revappend identity-vars terms)))
;;     (logic.lambda formals body actuals)))

;; (encapsulate
;;  ()
;;  (local (defthm lemma
;;           (subsetp (logic.term-vars body)
;;                    (app (difference (remove-duplicates (logic.term-vars body)) vars)
;;                         vars))
;;           :hints(("goal"
;;                   :use ((:instance subsetp-badguy-membership-property
;;                                    (x (logic.term-vars body))
;;                                    (y (app (difference
;;                                             (remove-duplicates (logic.term-vars body))
;;                                             vars)
;;                                            vars))))))))

;;  (defthm logic.termp-of-logic.translate-lambda-term
;;    (implies (and (force (true-listp vars))
;;                  (force (logic.variable-listp vars))
;;                  (force (uniquep vars))
;;                  (force (logic.termp body))
;;                  (force (true-listp actuals))
;;                  (force (logic.term-listp actuals))
;;                  (force (equal (len vars) (len actuals))))
;;             (equal (logic.termp (logic.translate-lambda-term vars body actuals))
;;                    t))
;;    :hints(("Goal" :in-theory (enable logic.translate-lambda-term)))))





(defun logic.flag-translate (flag x)
  ;; X is an "untranslated" term(-list), which are the same as terms except:
  ;;
  ;;   1. In untranslated terms, numbers, keyword symbols, and the symbols t and
  ;;      nil can be used as constants without quoting them.
  ;;
  ;;   2. In untranslated terms, the abbreviations first, second, third, fourth,
  ;;      fifth, and, or, list, cond, let, and let* may be used.
  ;;
  ;; Given an untranslated term(-list), we insert these missing quotes and
  ;; replace the abbreviations with their expansions.
  ;;
  ;; In the term case, we either return a genuine logic.termp corresponding to x
  ;; (when x is valid), or nil (when x is invalid).  For the list case, we return
  ;; (successp . x'), where x' are the translated terms if successp is true.
  (declare (xargs :guard (or (equal flag 'term)
                             (equal flag 'list))
                  :verify-guards nil
                  ;; yucky huge horrible thing, but oh well.  skip case for ACL2
                  ;; compatibility.
                  :export (if (equal flag 'term)
                              (cond ((natp x)
                                     ;; Automatically quote numbers.
                                     (list 'quote x))
                                    ((symbolp x)
                                     ;; Automatically quote t and nil, leave other variables alone.
                                     (if (or (equal x nil)
                                             (equal x t))
                                         (list 'quote x)
                                       x))
                                    ((symbolp (car x))
                                     (let ((fn (car x)))
                                       (cond ((equal fn 'quote)
                                              ;; Keep proper constants; other uses of quote are invalid.
                                              (if (tuplep 2 x)
                                                  x
                                                nil))
                                             ((memberp fn '(first second third fourth fifth))
                                              ;; Translate away "first", "second", "third', "fourth", and "fifth"
                                              (and (tuplep 2 x)
                                                   (let ((arg (logic.flag-translate 'term (second x))))
                                                     (and arg
                                                          (let* ((1cdr (logic.function 'cdr (list arg)))
                                                                 (2cdr (logic.function 'cdr (list 1cdr)))
                                                                 (3cdr (logic.function 'cdr (list 2cdr)))
                                                                 (4cdr (logic.function 'cdr (list 3cdr))))
                                                            (logic.function
                                                             'car
                                                             (list (cond ((equal fn 'first)  arg)
                                                                         ((equal fn 'second) 1cdr)
                                                                         ((equal fn 'third)  2cdr)
                                                                         ((equal fn 'fourth) 3cdr)
                                                                         (t                  4cdr)))))))))

                                             ((memberp fn '(and or list))
                                              ;; Translate away "and", "or", and "list"
                                              (and (true-listp (cdr x))
                                                   (let ((arguments+ (logic.flag-translate 'list (cdr x))))
                                                     (and (car arguments+)
                                                          (cond ((equal fn 'and)
                                                                 (logic.translate-and-term (cdr arguments+)))
                                                                ((equal fn 'or)
                                                                 (logic.translate-or-term (cdr arguments+)))
                                                                (t
                                                                 (logic.translate-list-term (cdr arguments+))))))))
                                             ((equal fn 'cond)
                                              ;; Translate away "cond"
                                              (and (true-listp (cdr x))
                                                   (tuple-listp 2 (cdr x))
                                                   (let* ((tests  (strip-firsts (cdr x)))
                                                          (thens  (strip-seconds (cdr x)))
                                                          (tests+ (logic.flag-translate 'list tests))
                                                          (thens+ (logic.flag-translate 'list thens)))
                                                     (and (car tests+)
                                                          (car thens+)
                                                          (logic.translate-cond-term (cdr tests+)
                                                                                     (cdr thens+))))))

                                             ((memberp fn '(let let*))
                                              ;; Translate away "let" and "let*"
                                              (and (tuplep 3 x)
                                                   (let ((pairs (second x))
                                                         (body  (logic.flag-translate 'term (third x))))
                                                     (and body
                                                          (true-listp pairs)
                                                          (tuple-listp 2 pairs)
                                                          (let* ((vars   (strip-firsts pairs))
                                                                 (terms  (strip-seconds pairs))
                                                                 (terms+ (logic.flag-translate 'list terms)))
                                                            (and (car terms+)
                                                                 (logic.variable-listp vars)
                                                                 (cond ((equal fn 'let)
                                                                        (and (uniquep vars)
                                                                             (logic.translate-let-term vars
                                                                                                       (cdr terms+)
                                                                                                       body)))
                                                                       (t (logic.translate-let*-term vars
                                                                                                     (cdr terms+)
                                                                                                     body)))))))))
                                             ((logic.function-namep fn)
                                              ;; Recursively translate the arguments to functions.
                                              (and (true-listp (cdr x))
                                                   (let ((arguments+ (logic.flag-translate 'list (cdr x))))
                                                     (and (car arguments+)
                                                          (logic.function fn (cdr arguments+))))))
                                             (t
                                              ;; Anything else is invalid.
                                              nil))))


                                    ((and (tuplep 3 (car x))
                                          (true-listp (cdr x)))
                                     ;; Lambdas are the only other valid possibility.
                                     (let* ((lambda-symbol (first (car x)))
                                            (vars          (second (car x)))
                                            (body          (third (car x)))
                                            (new-body      (logic.flag-translate 'term body))
                                            (actuals+      (logic.flag-translate 'list (cdr x))))
                                       (and (equal lambda-symbol 'lambda)
                                            (true-listp vars)
                                            (logic.variable-listp vars)
                                            (uniquep vars)
                                            new-body
                                            (subsetp (logic.term-vars new-body) vars)
                                            (car actuals+)
                                            (equal (len vars) (len (cdr actuals+)))
                                            (logic.lambda vars new-body (cdr actuals+)))))

                                    (t
                                     ;; Nothing else is a valid untranslated term.
                                     nil))
                            ;; List case.
                            (if (consp x)
                                (let ((first (logic.flag-translate 'term (car x)))
                                      (rest  (logic.flag-translate 'list (cdr x))))
                                  (if (and first (car rest))
                                      (cons t (cons first (cdr rest)))
                                    (cons nil nil)))
                              (cons t nil)))))
  (if (equal flag 'term)
      (cond ((natp x)
             ;; Automatically quote numbers.
             (list 'quote x))
            ((symbolp x)
             ;; Automatically quote t and nil, leave other variables alone.
             (if (or (equal x nil)
                     (equal x t))
                 (list 'quote x)
               x))
            #+acl2
            ((not (consp x))
             ;; HACK: Special case for ACL2 compatibility; we shouldn't need this
             ;; case in Milawa.
             nil)
            ((symbolp (car x))
             (let ((fn (car x)))
               (cond ((equal fn 'quote)
                      ;; Keep proper constants; other uses of quote are invalid.
                      (if (tuplep 2 x)
                          x
                        nil))
                     ((memberp fn '(first second third fourth fifth))
                      ;; Translate away "first", "second", "third', "fourth", and "fifth"
                      (and (tuplep 2 x)
                           (let ((arg (logic.flag-translate 'term (second x))))
                             (and arg
                                  (let* ((1cdr (logic.function 'cdr (list arg)))
                                         (2cdr (logic.function 'cdr (list 1cdr)))
                                         (3cdr (logic.function 'cdr (list 2cdr)))
                                         (4cdr (logic.function 'cdr (list 3cdr))))
                                    (logic.function
                                     'car
                                     (list (cond ((equal fn 'first)  arg)
                                                 ((equal fn 'second) 1cdr)
                                                 ((equal fn 'third)  2cdr)
                                                 ((equal fn 'fourth) 3cdr)
                                                 (t                  4cdr)))))))))

                     ((memberp fn '(and or list))
                      ;; Translate away "and", "or", and "list"
                      (and (true-listp (cdr x))
                           (let ((arguments+ (logic.flag-translate 'list (cdr x))))
                             (and (car arguments+)
                                  (cond ((equal fn 'and)
                                         (logic.translate-and-term (cdr arguments+)))
                                        ((equal fn 'or)
                                         (logic.translate-or-term (cdr arguments+)))
                                        (t
                                         (logic.translate-list-term (cdr arguments+))))))))
                     ((equal fn 'cond)
                      ;; Translate away "cond"
                      (and (true-listp (cdr x))
                           (tuple-listp 2 (cdr x))
                           (let* ((tests  (strip-firsts (cdr x)))
                                  (thens  (strip-seconds (cdr x)))
                                  (tests+ (logic.flag-translate 'list tests))
                                  (thens+ (logic.flag-translate 'list thens)))
                             (and (car tests+)
                                  (car thens+)
                                  (logic.translate-cond-term (cdr tests+)
                                                             (cdr thens+))))))

                     ((memberp fn '(let let*))
                      ;; Translate away "let" and "let*"
                      (and (tuplep 3 x)
                           (let ((pairs (second x))
                                 (body  (logic.flag-translate 'term (third x))))
                             (and body
                                  (true-listp pairs)
                                  (tuple-listp 2 pairs)
                                  (let* ((vars   (strip-firsts pairs))
                                         (terms  (strip-seconds pairs))
                                         (terms+ (logic.flag-translate 'list terms)))
                                    (and (car terms+)
                                         (logic.variable-listp vars)
                                         (cond ((equal fn 'let)
                                                (and (uniquep vars)
                                                     (logic.translate-let-term vars
                                                                               (cdr terms+)
                                                                               body)))
                                               (t (logic.translate-let*-term vars
                                                                             (cdr terms+)
                                                                             body)))))))))
                     ((logic.function-namep fn)
                      ;; Recursively translate the arguments to functions.
                      (and (true-listp (cdr x))
                           (let ((arguments+ (logic.flag-translate 'list (cdr x))))
                             (and (car arguments+)
                                  (logic.function fn (cdr arguments+))))))
                     (t
                      ;; Anything else is invalid.
                      nil))))


             ((and (tuplep 3 (car x))
                   (true-listp (cdr x)))
              ;; Lambdas are the only other valid possibility.
              (let* ((lambda-symbol (first (car x)))
                     (vars          (second (car x)))
                     (body          (third (car x)))
                     (new-body      (logic.flag-translate 'term body))
                     (actuals+      (logic.flag-translate 'list (cdr x))))
                (and (equal lambda-symbol 'lambda)
                     (true-listp vars)
                     (logic.variable-listp vars)
                     (uniquep vars)
                     new-body
                     (subsetp (logic.term-vars new-body) vars)
                     (car actuals+)
                     (equal (len vars) (len (cdr actuals+)))
                     (logic.lambda vars new-body (cdr actuals+)))))

            (t
             ;; Nothing else is a valid untranslated term.
             nil))
    ;; List case.
   (if (consp x)
       (let ((first (logic.flag-translate 'term (car x)))
             (rest  (logic.flag-translate 'list (cdr x))))
         (if (and first (car rest))
             (cons t (cons first (cdr rest)))
           (cons nil nil)))
     (cons t nil))))

(definlined logic.translate (x)
  (declare (xargs :guard t :verify-guards nil))
  (logic.flag-translate 'term x))

(definlined logic.translate-list (x)
  (declare (xargs :guard t :verify-guards nil))
  (logic.flag-translate 'list x))

(defthmd definition-of-logic.translate
  (equal (logic.translate x)
         (cond ((natp x)
                (list 'quote x))
               ((symbolp x)
                (if (or (equal x nil)
                        (equal x t))
                    (list 'quote x)
                  x))
               ((not (consp x))
                nil)
               ((symbolp (car x))
                (let ((fn (car x)))
                  (cond ((equal fn 'quote)
                         (if (tuplep 2 x)
                             x
                           nil))
                        ((memberp fn '(first second third fourth fifth))
                         (and (tuplep 2 x)
                              (let ((arg (logic.translate (second x))))
                                (and arg
                                     (let* ((1cdr (logic.function 'cdr (list arg)))
                                            (2cdr (logic.function 'cdr (list 1cdr)))
                                            (3cdr (logic.function 'cdr (list 2cdr)))
                                            (4cdr (logic.function 'cdr (list 3cdr))))
                                       (logic.function 'car (list (cond ((equal fn 'first)  arg)
                                                                        ((equal fn 'second) 1cdr)
                                                                        ((equal fn 'third)  2cdr)
                                                                        ((equal fn 'fourth) 3cdr)
                                                                        (t                  4cdr)))))))))
                        ((memberp fn '(and or list))
                         (and (true-listp (cdr x))
                              (let ((arguments+ (logic.translate-list (cdr x))))
                                (and (car arguments+)
                                     (cond ((equal fn 'and) (logic.translate-and-term (cdr arguments+)))
                                           ((equal fn 'or)  (logic.translate-or-term (cdr arguments+)))
                                           (t               (logic.translate-list-term (cdr arguments+))))))))
                        ((equal fn 'cond)
                         (and (true-listp (cdr x))
                              (tuple-listp 2 (cdr x))
                              (let* ((tests  (strip-firsts (cdr x)))
                                     (thens  (strip-seconds (cdr x)))
                                     (tests+ (logic.translate-list tests))
                                     (thens+ (logic.translate-list thens)))
                                (and (car tests+)
                                     (car thens+)
                                     (logic.translate-cond-term (cdr tests+) (cdr thens+))))))
                        ((memberp fn '(let let*))
                         (and (tuplep 3 x)
                              (let ((pairs (second x))
                                    (body  (logic.translate (third x))))
                                (and body
                                     (true-listp pairs)
                                     (tuple-listp 2 pairs)
                                     (let* ((vars   (strip-firsts pairs))
                                            (terms  (strip-seconds pairs))
                                            (terms+ (logic.translate-list terms)))
                                       (and (car terms+)
                                            (logic.variable-listp vars)
                                            (cond ((equal fn 'let)
                                                   (and (uniquep vars)
                                                        (logic.translate-let-term vars (cdr terms+) body)))
                                                  (t (logic.translate-let*-term vars (cdr terms+) body)))))))))
                        ((logic.function-namep fn)
                         (and (true-listp (cdr x))
                              (let ((arguments+ (logic.translate-list (cdr x))))
                                (and (car arguments+)
                                     (logic.function fn (cdr arguments+))))))
                        (t nil))))
            ((and (tuplep 3 (car x))
                  (true-listp (cdr x)))
             (let* ((lambda-symbol (first (car x)))
                    (vars          (second (car x)))
                    (body          (third (car x)))
                    (new-body      (logic.translate body))
                    (actuals+      (logic.translate-list (cdr x))))
               (and (equal lambda-symbol 'lambda)
                    (true-listp vars)
                    (logic.variable-listp vars)
                    (uniquep vars)
                    new-body
                    (subsetp (logic.term-vars new-body) vars)
                    (car actuals+)
                    (equal (len vars) (len (cdr actuals+)))
                    (logic.lambda vars new-body (cdr actuals+)))))
            (t nil)))
  :rule-classes :definition
  :hints(("Goal" :in-theory (e/d (logic.translate logic.translate-list)
                                 (forcing-true-listp-of-logic.function-args
                                  equal-of-cons-rewrite
                                  equal-of-logic.function-rewrite)))))

(defthmd definition-of-logic.translate-list
  (equal (logic.translate-list x)
         (if (consp x)
             (let ((first (logic.translate (car x)))
                   (rest  (logic.translate-list (cdr x))))
               (if (and first (car rest))
                   (cons t (cons first (cdr rest)))
                 (cons nil nil)))
           (cons t nil)))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable logic.translate logic.translate-list))))

(defthm logic.flag-translate-of-term-removal
  (equal (logic.flag-translate 'term x)
         (logic.translate x))
  :hints(("Goal" :in-theory (enable logic.translate))))

(defthm logic.flag-translate-of-list-removal
  (equal (logic.flag-translate 'list x)
         (logic.translate-list x))
  :hints(("Goal" :in-theory (enable logic.translate-list))))

(ACL2::theory-invariant (not (ACL2::active-runep '(:definition logic.translate))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition logic.translate-list))))

(defthm logic.translate-list-when-not-consp
  (implies (not (consp x))
           (equal (logic.translate-list x)
                  (cons t nil)))
  :hints(("Goal" :in-theory (enable definition-of-logic.translate-list))))

(defthm logic.translate-list-of-cons
  (equal (logic.translate-list (cons a x))
         (if (and (logic.translate a) (car (logic.translate-list x)))
             (cons t (cons (logic.translate a) (cdr (logic.translate-list x))))
           (cons nil nil)))
  :hints(("Goal" :in-theory (enable definition-of-logic.translate-list))))

(defthm consp-of-logic.translate-list
  (equal (consp (logic.translate-list x))
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm len-of-cdr-of-logic.translate-list
  (implies (car (logic.translate-list x))
           (equal (len (cdr (logic.translate-list x)))
                  (len x)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm true-listp-of-cdr-of-logic.translate-list
  (true-listp (cdr (logic.translate-list x)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm booleanp-of-car-of-logic.translate-list
  (equal (booleanp (car (logic.translate-list x)))
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(encapsulate
 ()
 (local (defthm logic.termp-when-symbolp-cheap
          (implies (symbolp x)
                   (equal (logic.termp x)
                          (and (not (equal x nil))
                               (not (equal x t)))))
          :rule-classes ((:rewrite :backchain-limit-lst 0))
          :hints(("Goal" :in-theory (enable logic.variablep
                                            definition-of-logic.termp)))))

 (local (defthm logic.termp-of-cons-quote
          (equal (logic.termp (cons 'quote x))
                 (tuplep 1 x))
          :hints(("Goal" :in-theory (enable definition-of-logic.termp
                                            logic.constantp
                                            logic.variablep)))))

 (local (defthm lemma
          (if (equal flag 'term)
              (implies (logic.translate x)
                       (logic.termp (logic.translate x)))
            (logic.term-listp (cdr (logic.translate-list x))))
          :rule-classes nil
          :hints(("Goal"
                  :in-theory (enable definition-of-logic.translate)
                  :induct (logic.flag-translate flag x)))))

 (defthm logic.termp-of-logic.translate
   (implies (logic.translate x)
            (equal (logic.termp (logic.translate x))
                   t))
   :hints(("Goal" :use ((:instance lemma (flag 'term))))))

 (defthm logic.term-listp-of-cdr-of-logic.translate-list
   (equal (logic.term-listp (cdr (logic.translate-list x)))
          t)
   :hints(("Goal" :use ((:instance lemma (flag 'list)))))))



(encapsulate
 ()
 (local (defthm natp-when-logic.lambdap
          (implies (logic.lambdap x)
                   (equal (natp x)
                          nil))
          :hints(("Goal" :in-theory (enable logic.lambdap)))))

 (local (defthm car-when-logic.lambdap
          (implies (and (logic.lambdap x)
                        (force (logic.termp x)))
                   (equal (car x)
                          (list 'lambda
                                (logic.lambda-formals x)
                                (logic.lambda-body x))))
          :hints(("Goal" :in-theory (enable logic.lambdap
                                            logic.lambda-formals
                                            logic.lambda-body
                                            definition-of-logic.termp)))))

 (local (defthm cdr-when-logic.lambdap
          (implies (logic.lambdap x)
                   (equal (cdr x)
                          (logic.lambda-actuals x)))
          :hints(("Goal" :in-theory (enable logic.lambdap
                                            logic.lambda-actuals
                                            definition-of-logic.termp)))))

 (local (defthm forcing-equal-of-logic.lambda-rewrite
          (implies (force (logic.termp x))
                   (equal (equal (logic.lambda formals body actuals) x)
                          (and (logic.lambdap x)
                               (equal (logic.lambda-formals x) formals)
                               (equal (logic.lambda-body x) body)
                               (equal (logic.lambda-actuals x) actuals))))))

 (local (defthm natp-when-logic.functionp
          (implies (logic.functionp x)
                   (equal (natp x)
                          nil))
          :hints(("Goal" :in-theory (enable logic.functionp)))))

 (local (defthm car-when-logic.functionp
          (implies (logic.functionp x)
                   (equal (car x)
                          (logic.function-name x)))
          :hints(("Goal" :in-theory (enable logic.function-name logic.functionp)))))

 (local (defthm cdr-when-logic.functionp
          (implies (logic.functionp x)
                   (equal (cdr x)
                          (logic.function-args x)))
          :hints(("Goal" :in-theory (enable logic.function-args logic.functionp)))))

 (local (defthm equal-of-logic.function-name-when-not-function-namep
          (implies (and (not (logic.function-namep name))
                        (force (logic.termp x))
                        (force (logic.functionp x)))
                   (equal (equal (logic.function-name x) name)
                          nil))))

 (local (defthm lemma
          (if (equal flag 'term)
              (implies (logic.termp x)
                       (equal (logic.translate x) x))
            (implies (logic.term-listp x)
                     (and (car (logic.translate-list x))
                          (equal (cdr (logic.translate-list x))
                                 (list-fix x)))))
          :rule-classes nil
          :hints(("Goal"
                  :in-theory (enable definition-of-logic.translate)
                  :induct (logic.term-induction flag x)
                  :expand (logic.translate x)
                  :do-not-induct t)
                 ("Subgoal *1/2"
                  :in-theory (enable logic.constantp)
                  :expand (logic.translate x))
                 ("Subgoal *1/1"
                  :in-theory (enable logic.variablep)
                  :expand (logic.translate x)))))

 (defthm logic.translate-when-logic.termp
   (implies (logic.termp x)
            (equal (logic.translate x)
                   x))
   :hints(("Goal" :use ((:instance lemma (flag 'term))))))

 (defthm logic.translate-when-logic.term-listp
   (implies (logic.term-listp x)
            (equal (logic.translate-list x)
                   (cons t (list-fix x))))
   :hints(("Goal" :use ((:instance lemma (flag 'list)))))))


(verify-guards logic.flag-translate)
(verify-guards logic.translate)
(verify-guards logic.translate-list)




(defmacro assert (thing-that-must-be-true)
  `(ACL2::make-event (if ,thing-that-must-be-true
                         '(ACL2::value-triple :assert-ok)
                       (ACL2::er hard 'assert "Assertation failed: ~x0~%" ',thing-that-must-be-true))))



;; We run some basic tests to make sure that translate seems to be working
;; correctly.  We might eventually want to expand this test suite.
(local
 (encapsulate
  ()

  (assert (equal (logic.translate nil) ''nil))
  (assert (equal (logic.translate t) ''t))
  (assert (equal (logic.translate 0) ''0))
  (assert (equal (logic.translate 3) ''3))
  (assert (equal (logic.translate ''4) ''4))
  (assert (equal (logic.translate 'foo) 'foo))
  (assert (equal (logic.translate ''foo) ''foo))
  (assert (equal (logic.translate ''t) ''t))
  (assert (equal (logic.translate ''(1 . 2)) ''(1 . 2)))

  ;; Malformed objects

  ;; (assert (not (logic.translate :foo)))  ;; heh, this actually broke when i unsoundly
  ;;                                           redefined symbolp.  taking it out.

  (assert (not (logic.translate (list 'quote 1 2))))
  (assert (not (logic.translate -1)))
  (assert (not (logic.translate "string")))
  (assert (not (logic.translate 3/2)))

  (assert (equal (logic.translate '(list))         ''nil))
  (assert (equal (logic.translate '(list 1))       '(cons '1 'nil)))
  (assert (equal (logic.translate '(list 1 2))     '(cons '1 (cons '2 'nil))))
  (assert (equal (logic.translate '(list 1 2 3))   '(cons '1 (cons '2 (cons '3 'nil)))))
  (assert (equal (logic.translate '(list 1 2 3 4)) '(cons '1 (cons '2 (cons '3 (cons '4 'nil))))))

  (assert (equal (logic.translate '(and))         ''t))
  (assert (equal (logic.translate '(and 1))       ''1))
  (assert (equal (logic.translate '(and 1 2))     '(if '1 '2 'nil)))
  (assert (equal (logic.translate '(and 1 2 3))   '(if '1 (if '2 '3 'nil) 'nil)))
  (assert (equal (logic.translate '(and 1 2 3 4)) '(if '1 (if '2 (if '3 '4 'nil) 'nil) 'nil)))

  (assert (equal (logic.translate '(or))         ''nil))
  (assert (equal (logic.translate '(or 1))       ''1))
  (assert (equal (logic.translate '(or 1 2))     '(if '1 '1 '2)))
  (assert (equal (logic.translate '(or 1 2 3))   '(if '1 '1 (if '2 '2 '3))))
  (assert (equal (logic.translate '(or 1 2 3 4)) '(if '1 '1 (if '2 '2 (if '3 '3 '4)))))

  (assert (equal (logic.translate '(or (f x) (f y)))
                 (logic.translate '(let ((special-var-for-or (f x)))
                                     (if special-var-for-or
                                         special-var-for-or
                                       (f y))))))

  (assert (equal (logic.translate '(or (f x) (f y) (f z)))
                 (logic.translate '(let ((special-var-for-or (f x)))
                                     (if special-var-for-or
                                         special-var-for-or
                                       (let ((special-var-for-or (f y)))
                                         (if special-var-for-or
                                             special-var-for-or
                                           (f z))))))))

  (assert (equal (logic.translate '(first x))    '(car x)))
  (assert (equal (logic.translate '(second x))   '(car (cdr x))))
  (assert (equal (logic.translate '(third x))    '(car (cdr (cdr x)))))
  (assert (equal (logic.translate '(fourth x))   '(car (cdr (cdr (cdr x))))))
  (assert (equal (logic.translate '(fifth x))    '(car (cdr (cdr (cdr (cdr x)))))))

  (assert (not (logic.translate '(cond x)))) ;; malformed cond

  (assert (equal (logic.translate '(cond))                         ''nil))
  (assert (equal (logic.translate '(cond (x 1)))                   '(if x '1 'nil)))
  (assert (equal (logic.translate '(cond (x 1) (y 2)))             '(if x '1 (if y '2 'nil))))
  (assert (equal (logic.translate '(cond (x 1) (y 2) (z 3)))       '(if x '1 (if y '2 (if z '3 'nil)))))
  (assert (equal (logic.translate '(cond (x 1) (y 2) (z 3) (t 4))) '(if x '1 (if y '2 (if z '3 (if 't '4 'nil))))))
  (assert (equal (logic.translate '(cond (x 1) (y 2) (t 3) (z 4))) '(if x '1 (if y '2 (if 't '3 (if z '4 'nil))))))

  ;; Malformed lets
  (assert (not (logic.translate '(let))))
  (assert (not (logic.translate '(let ()))))
  (assert (not (logic.translate '(let ((1 2)) (+ x y)))))
  (assert (not (logic.translate '(let ((x 1) (x 2)) (+ x y)))))

  (assert (equal (logic.translate '(let () nil))                      '((lambda () 'nil))))
  (assert (equal (logic.translate '(let ((a 1)) (+ x y)))             '((lambda (x y a) (+ x y)) x y '1)))
  (assert (equal (logic.translate '(let ((a 1) (b 2)) (+ x y)))       '((lambda (x y a b) (+ x y)) x y '1 '2)))
  (assert (equal (logic.translate '(let ((a 1) (b 2) (c 3)) (+ x y))) '((lambda (x y a b c) (+ x y)) x y '1 '2 '3)))

  ;; Malformed let*s
  (assert (not (logic.translate '(let*))))
  (assert (not (logic.translate '(let* ()))))
  (assert (not (logic.translate '(let* ((1 2)) (+ x y)))))

  (assert (equal (logic.translate '(let* () nil))                       ''nil))

  (assert (equal (logic.translate '(let* ((a 1)) (+ x y)))
                 '((lambda (x y a) (+ x y)) x y '1)))

  (assert (equal (logic.translate '(let* ((a 1) (b 2)) (+ x y)))
                 '((lambda (x y a) ((lambda (x y b) (+ x y)) x y '2)) x y '1)))

  (assert (equal (logic.translate '(let* ((a 1) (b 2) (c 3)) (+ x y)))
                 '((lambda (x y a) ((lambda (x y b) ((lambda (x y c) (+ x y)) x y '3)) x y '2)) x y '1)))

  (assert (equal (logic.translate '(let* ((x 1) (x 2)) (+ x y)))
                 '((lambda (y x) ((lambda (y x) (+ x y)) y '2)) y '1)))

  (assert (equal (logic.translate '(let* ((x 1) (x (+ x 1))) (+ x y)))
                 '((lambda (y x) ((lambda (y x) (+ x y)) y (+ x '1))) y '1)))

  (assert (equal (logic.translate '(foo x y z))       '(foo x y z)))
  (assert (equal (logic.translate '(foo x 1 nil y 2)) '(foo x '1 'nil y '2)))

  ))
