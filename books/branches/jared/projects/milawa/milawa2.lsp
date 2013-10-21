; launch ccl
; (load "milawa2.lisp")
; -- should produce 'milawa2'
; then, ccl -I [path to milawa2]
;  in the same directory as full.events

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

; INITIAL SETUP OF THE MILAWA PACKAGE

(in-package "CL-USER")
(declaim (optimize (speed 3) (space 0) (safety 0)))

#+clozure
(progn
  (setq ccl::*default-control-stack-size* (expt 2 27))
  (setq ccl::*default-value-stack-size* (expt 2 27))
  (setq ccl::*default-temp-stack-size* (expt 2 27))
  (setq ccl::*initial-listener-default-value-stack-size* (expt 2 27))
  (setq ccl::*initial-listener-default-control-stack-size* (expt 2 27))
  (setq ccl::*initial-listener-default-temp-stack-size* (expt 2 27))
  (CCL::egc nil)
  (CCL::set-lisp-heap-gc-threshold (expt 2 34))
  (CCL::gc-verbose t t))

(defmacro defun-comp (&rest args)
  `(compile (defun ,@args)))

(defpackage "MILAWA" (:use))

(import '(COMMON-LISP::nil
          COMMON-LISP::t
          COMMON-LISP::quote
          COMMON-LISP::if
          COMMON-LISP::equal
          COMMON-LISP::consp
          COMMON-LISP::cons
          COMMON-LISP::symbolp
          COMMON-LISP::let
          COMMON-LISP::let*
          COMMON-LISP::list
          COMMON-LISP::and
          COMMON-LISP::or
          COMMON-LISP::cond
          COMMON-LISP::lambda)
        "MILAWA")

(defun-comp MILAWA::natp (x)
  (integerp x))

(defun-comp MILAWA::symbol-< (x y)
  (let ((x-fix (if (symbolp x) x nil))
        (y-fix (if (symbolp y) y nil)))
    (if (string< (symbol-name x-fix) (symbol-name y-fix))
        t
      nil)))

(defun-comp MILAWA::< (x y)
  (let ((x-fix (if (integerp x) x 0))
        (y-fix (if (integerp y) y 0)))
    (< x-fix y-fix)))

(defun-comp MILAWA::+ (x y)
  (let* ((x-fix (if (integerp x) x 0))
         (y-fix (if (integerp y) y 0))
         (ret   (+ x-fix y-fix)))
    (if (< ret 1073741824)
        ret
      (progn
        (error "Overflow in +.")
        (quit)))))

(defun-comp MILAWA::- (x y)
  (let* ((x-fix (if (integerp x) x 0))
         (y-fix (if (integerp y) y 0))
         (ans   (- x-fix y-fix)))
    (if (< ans 0) 0 ans)))

(defun-comp MILAWA::car (x)
  (if (consp x) (car x) nil))

(defun-comp MILAWA::cdr (x)
  (if (consp x) (cdr x) nil))

(defmacro MILAWA::first  (x) `(MILAWA::car ,x))
(defmacro MILAWA::second (x) `(MILAWA::first  (MILAWA::cdr ,x)))
(defmacro MILAWA::third  (x) `(MILAWA::second (MILAWA::cdr ,x)))
(defmacro MILAWA::fourth (x) `(MILAWA::third  (MILAWA::cdr ,x)))
(defmacro MILAWA::fifth  (x) `(MILAWA::fourth (MILAWA::cdr ,x)))


; SAFE DEFINITION MECHANISM

(defun-comp MILAWA::define (name formals body)
  ;; Define a function in Raw Lisp.
  (eval `(compile (defun ,name ,formals
                    (declare (ignorable ,@formals))
                    ,body))))

(defun-comp MILAWA::error (description)
  ;; Abort execution with a run-time error
  (error "Milawa::error called: ~a" description)
  (quit))

(defun-comp MILAWA::print (obj)
  (format t "~a~%" obj)
  (finish-output)
  nil)

(in-package "MILAWA")

(define 'lookup '(a x)
  '(if (consp x)
       (if (equal a (car (car x)))
           (if (consp (car x))
               (car x)
             (cons (car (car x)) (cdr (car x))))
         (lookup a (cdr x)))
     nil))

(define 'define-safe '(ftbl name formals body)
  ;; Returns FTBL-PRIME or causes an error.
  '(let ((this-def (list name formals body))
         (prev-def (lookup name ftbl)))
     (if prev-def
         (if (equal prev-def this-def)
             ftbl
           (error (list 'redefinition-error prev-def this-def)))
       (let ((unused (define name formals body)))
         (cons this-def ftbl)))))

(define 'define-safe-list '(ftbl defs)
  ;; DEFS are 3-tuples of the form: (name formals body)
  ;; We define all of these functions, in order.
  ;; We return FTBL-PRIME or causes an error.
  '(if (consp defs)
       (let* ((def1 (car defs))
              (ftbl (define-safe ftbl (first def1) (second def1) (third def1))))
         (define-safe-list ftbl (cdr defs)))
     ftbl))

(define 'milawa-init '()
  '(define-safe-list

; We start with "ill-formed" definitions for any functions we don't want the
; user to be able to redefine.  This list includes (1) all of the primitive
; Milawa functions like IF, EQUAL, etc., and (2) any built-in system functions
; that the Lisp relies upon.
;
; The point of this is to ensure that any attempt by the user to define any of
; these functions will fail.  No matter what formals and body they try to use,
; the resulting call of DEFUN-SAFE will insist that (F FORMALS BODY) is in the
; FTBL, but the actual entry is just (F).

     '(;; Milawa Primitives
       (if)
       (equal)
       (symbolp)
       (symbol-<)
       (natp)
       (<)
       (+)
       (-)
       (consp)
       (cons)
       (car)
       (cdr)

       ;; Extralogical System Functions
       (error)
       (print)
       (define)
       (define-safe)
       (define-safe-list)
       (milawa-init)
       (milawa-main))

; We now extend the above FTBL wth definitions for all of the functions for our
; proof-checking system.  Note that the act of defining these functions does
; not "admit" them and add definitional axioms, but instead merely (1)
; introduces Lisp definitions of these functions and (2) installs FTBL entries
; for these functions so that the user may not define them in any other way.

     '((not (x) (if x nil t))

       (rank (x)
             (if (consp x)
                 (+ 1
                    (+ (rank (car x))
                       (rank (cdr x))))
               0))

       (ord< (x y)
             (cond ((not (consp x))
                    (if (consp y) t (< x y)))
                   ((not (consp y))
                    nil)
                   ((not (equal (car (car x)) (car (car y))))
                    (ord< (car (car x)) (car (car y))))
                   ((not (equal (cdr (car x)) (cdr (car y))))
                    (< (cdr (car x)) (cdr (car y))))
                   (t
                    (ord< (cdr x) (cdr y)))))

       (ordp (x)
             (if (not (consp x))
                 (natp x)
               (and (consp (car x))
                    (ordp (car (car x)))
                    (not (equal (car (car x)) 0))
                    (< 0 (cdr (car x)))
                    (ordp (cdr x))
                    (if (consp (cdr x))
                        (ord< (car (car (cdr x))) (car (car x)))
                      t))))

       (nfix (x) (if (natp x) x 0))

       (<= (a b) (not (< b a)))

       (zp (x) (if (natp x) (equal x 0) t))

       (true-listp (x)
                   (if (consp x)
                       (true-listp (cdr x))
                     (equal x nil)))

       (list-fix (x)
                 (if (consp x)
                     (cons (car x) (list-fix (cdr x)))
                   nil))

       (len (x)
            (if (consp x)
                (+ 1 (len (cdr x)))
              0))

       (memberp (a x)
                (if (consp x)
                    (or (equal a (car x))
                        (memberp a (cdr x)))
                  nil))

       (subsetp (x y)
                (if (consp x)
                    (and (memberp (car x) y)
                         (subsetp (cdr x) y))
                  t))

       (uniquep (x)
                (if (consp x)
                    (and (not (memberp (car x) (cdr x)))
                         (uniquep (cdr x)))
                  t))

       (app (x y)
            (if (consp x)
                (cons (car x) (app (cdr x) y))
              (list-fix y)))

       (rev (x)
            (if (consp x)
                (app (rev (cdr x)) (list (car x)))
              nil))

       (tuplep (n x)
               (if (zp n)
                   (equal x nil)
                 (and (consp x)
                      (tuplep (- n 1) (cdr x)))))

       (pair-lists (x y)
                   (if (consp x)
                       (cons (cons (car x) (car y))
                             (pair-lists (cdr x) (cdr y)))
                     nil))

       (lookup (a x)
               (if (consp x)
                   (if (equal a (car (car x)))
                       (if (consp (car x))
                           (car x)
                         (cons (car (car x)) (cdr (car x))))
                     (lookup a (cdr x)))
                 nil))

       ;; THE PROOF CHECKER - TERMS

       (logic.variablep (x)
                        (and (symbolp x)
                             (not (equal x t))
                             (not (equal x nil))))

       (logic.variable-listp (x)
                             (if (consp x)
                                 (and (logic.variablep (car x))
                                      (logic.variable-listp (cdr x)))
                               t))

       (logic.constantp (x)
                        (and (tuplep 2 x)
                             (equal (first x) 'quote)))

       (logic.constant-listp (x)
                             (if (consp x)
                                 (and (logic.constantp (car x))
                                      (logic.constant-listp (cdr x)))
                               t))

       (logic.function-namep
        (x)
        (and (symbolp x)
             (not (memberp x '(nil quote pequal* pnot*
                                   por* first second third
                                   fourth fifth and or list
                                   cond let let*)))))

       (logic.flag-term-vars
        (flag x acc)
        (if (equal flag 'term)
            (cond ((logic.constantp x) acc)
                  ((logic.variablep x) (cons x acc))
                  ((not (consp x))     acc)
                  (t
                   (logic.flag-term-vars 'list (cdr x) acc)))
          (if (consp x)
              (logic.flag-term-vars 'term (car x)
                                    (logic.flag-term-vars 'list (cdr x) acc))
            acc)))

       (logic.term-vars (x) (logic.flag-term-vars 'term x nil))

       (logic.flag-termp
        (flag x)
        (if (equal flag 'term)
            (or (logic.variablep x)
                (logic.constantp x)
                (and (consp x)
                     (if (logic.function-namep (car x))
                         (let ((args (cdr x)))
                           (and (true-listp args)
                                (logic.flag-termp 'list args)))
                       (and (tuplep 3 (car x))
                            (let ((lambda-symbol (first (car x)))
                                  (formals       (second (car x)))
                                  (body          (third (car x)))
                                  (actuals       (cdr x)))
                              (and (equal lambda-symbol 'lambda)
                                   (true-listp formals)
                                   (logic.variable-listp formals)
                                   (uniquep formals)
                                   (logic.flag-termp 'term body)
                                   (subsetp (logic.term-vars body) formals)
                                   (equal (len formals) (len actuals))
                                   (true-listp actuals)
                                   (logic.flag-termp 'list actuals)))))))
          (if (consp x)
              (and (logic.flag-termp 'term (car x))
                   (logic.flag-termp 'list (cdr x)))
            t)))

       (logic.termp (x) (logic.flag-termp 'term x))

       (logic.unquote (x) (second x))

       (logic.unquote-list (x)
                           (if (consp x)
                               (cons (logic.unquote (car x))
                                     (logic.unquote-list (cdr x)))
                             nil))

       (logic.functionp (x) (logic.function-namep (car x)))
       (logic.function-name (x) (car x))
       (logic.function-args (x) (cdr x))
       (logic.function (name args) (cons name args))

       (logic.lambdap (x) (consp (car x)))
       (logic.lambda-formals (x) (second (car x)))
       (logic.lambda-body    (x) (third (car x)))
       (logic.lambda-actuals (x) (cdr x))
       (logic.lambda (xs b ts) (cons (list 'lambda xs b) ts))

       (logic.flag-term-atblp
        (flag x atbl)
        (if (equal flag 'term)
            (cond ((logic.constantp x) t)
                  ((logic.variablep x) t)
                  ((logic.functionp x)
                   (let ((name (logic.function-name x))
                         (args (logic.function-args x)))
                     (and (equal (len args) (cdr (lookup name atbl)))
                          (logic.flag-term-atblp 'list args atbl))))
                  ((logic.lambdap x)
                   (let ((body (logic.lambda-body x))
                         (actuals (logic.lambda-actuals x)))
                     (and (logic.flag-term-atblp 'term body atbl)
                          (logic.flag-term-atblp 'list actuals atbl))))
                  (t nil))
          (if (consp x)
              (and (logic.flag-term-atblp 'term (car x) atbl)
                   (logic.flag-term-atblp 'list (cdr x) atbl))
            t)))

       (logic.term-atblp (x atbl)
                         (logic.flag-term-atblp 'term x atbl))


       ;; THE PROOF CHECKER - FORMULAS

       (logic.formulap (x)
                       (cond ((equal (first x) 'pequal*)
                              (and (tuplep 3 x)
                                   (logic.termp (second x))
                                   (logic.termp (third x))))
                             ((equal (first x) 'pnot*)
                              (and (tuplep 2 x)
                                   (logic.formulap (second x))))
                             ((equal (first x) 'por*)
                              (and (tuplep 3 x)
                                   (logic.formulap (second x))
                                   (logic.formulap (third x))))
                             (t nil)))

       (logic.formula-listp (x)
                            (if (consp x)
                                (and (logic.formulap (car x))
                                     (logic.formula-listp (cdr x)))
                              t))

       (logic.fmtype (x) (first x))

       (logic.=lhs (x) (second x))
       (logic.=rhs (x) (third x))
       (logic.~arg (x) (second x))
       (logic.vlhs (x) (second x))
       (logic.vrhs (x) (third x))

       (logic.pequal (a b) (list 'pequal* a b))
       (logic.pnot   (a)   (list 'pnot* a))
       (logic.por    (a b) (list 'por* a b))

       (logic.formula-atblp
        (x atbl)
        (let ((type (logic.fmtype x)))
          (cond ((equal type 'por*)
                 (and (logic.formula-atblp (logic.vlhs x) atbl)
                      (logic.formula-atblp (logic.vrhs x) atbl)))
                ((equal type 'pnot*)
                 (logic.formula-atblp (logic.~arg x) atbl))
                ((equal type 'pequal*)
                 (and (logic.term-atblp (logic.=lhs x) atbl)
                      (logic.term-atblp (logic.=rhs x) atbl)))
                (t nil))))

       (logic.disjoin-formulas
        (x)
        (if (consp x)
            (if (consp (cdr x))
                (logic.por (car x) (logic.disjoin-formulas (cdr x)))
              (car x))
          nil))

       ;; THE PROOF CHECKER - APPEALS

       (logic.flag-appealp
        (flag x)
        (if (equal flag 'proof)
            (and (true-listp x)
                 (<= (len x) 4)
                 (symbolp (first x))
                 (logic.formulap (second x))
                 (true-listp (third x))
                 (logic.flag-appealp 'list (third x)))
          (if (consp x)
              (and (logic.flag-appealp 'proof (car x))
                   (logic.flag-appealp 'list (cdr x)))
            t)))

       (logic.appealp (x) (logic.flag-appealp 'proof x))
       (logic.appeal-listp (x) (logic.flag-appealp 'list x))

       (logic.method (x) (first x))
       (logic.conclusion (x) (second x))
       (logic.subproofs (x) (third x))
       (logic.extras (x) (fourth x))

       (logic.strip-conclusions
        (x)
        (if (consp x)
            (cons (logic.conclusion (car x))
                  (logic.strip-conclusions (cdr x)))
          nil))

       ;; THE PROOF CHECKER - STEP CHECKING

       (logic.axiom-okp
        (x axioms atbl)
        (let ((method     (logic.method x))
              (conclusion (logic.conclusion x))
              (subproofs  (logic.subproofs x))
              (extras     (logic.extras x)))
          (and (equal method 'axiom)
               (equal subproofs nil)
               (equal extras nil)
               (memberp conclusion axioms)
               (logic.formula-atblp conclusion atbl))))

       (logic.theorem-okp
        (x thms atbl)
        (let ((method     (logic.method x))
              (conclusion (logic.conclusion x))
              (subproofs  (logic.subproofs x))
              (extras     (logic.extras x)))
          (and (equal method 'theorem)
               (equal subproofs nil)
               (equal extras nil)
               (memberp conclusion thms)
               (logic.formula-atblp conclusion atbl))))

       ;; Basic Rules

       (logic.associativity-okp
        (x)
        (let ((method     (logic.method x))
              (conclusion (logic.conclusion x))
              (subproofs  (logic.subproofs x))
              (extras     (logic.extras x)))
          (and (equal method 'associativity)
               (equal extras nil)
               (tuplep 1 subproofs)
               (let ((sub-or-a-or-b-c (logic.conclusion (first subproofs))))
                 (and (equal (logic.fmtype conclusion) 'por*)
                      (equal (logic.fmtype sub-or-a-or-b-c) 'por*)
                      (let ((conc-or-a-b (logic.vlhs conclusion))
                            (conc-c      (logic.vrhs conclusion))
                            (sub-a       (logic.vlhs sub-or-a-or-b-c))
                            (sub-or-b-c  (logic.vrhs sub-or-a-or-b-c)))
                        (and (equal (logic.fmtype conc-or-a-b) 'por*)
                             (equal (logic.fmtype sub-or-b-c) 'por*)
                             (let ((conc-a (logic.vlhs conc-or-a-b))
                                   (conc-b (logic.vrhs conc-or-a-b))
                                   (sub-b  (logic.vlhs sub-or-b-c))
                                   (sub-c  (logic.vrhs sub-or-b-c)))
                               (and (equal conc-a sub-a)
                                    (equal conc-b sub-b)
                                    (equal conc-c sub-c))))))))))

       (logic.contraction-okp
        (x)
        (let ((method     (logic.method x))
              (conclusion (logic.conclusion x))
              (subproofs  (logic.subproofs x))
              (extras     (logic.extras x)))
          (and (equal method 'contraction)
               (equal extras nil)
               (tuplep 1 subproofs)
               (let ((or-a-a (logic.conclusion (first subproofs))))
                 (and (equal (logic.fmtype or-a-a) 'por*)
                      (equal (logic.vlhs or-a-a) conclusion)
                      (equal (logic.vrhs or-a-a) conclusion))))))

       (logic.cut-okp
        (x)
        (let ((method     (logic.method x))
              (conclusion (logic.conclusion x))
              (subproofs  (logic.subproofs x))
              (extras     (logic.extras x)))
          (and (equal method 'cut)
               (equal extras nil)
               (tuplep 2 subproofs)
               (let ((or-a-b     (logic.conclusion (first subproofs)))
                     (or-not-a-c (logic.conclusion (second subproofs))))
                 (and (equal (logic.fmtype or-a-b) 'por*)
                      (equal (logic.fmtype or-not-a-c) 'por*)
                      (let ((a     (logic.vlhs or-a-b))
                            (b     (logic.vrhs or-a-b))
                            (not-a (logic.vlhs or-not-a-c))
                            (c     (logic.vrhs or-not-a-c)))
                        (and (equal (logic.fmtype not-a) 'pnot*)
                             (equal (logic.~arg not-a) a)
                             (equal (logic.fmtype conclusion) 'por*)
                             (equal (logic.vlhs conclusion) b)
                             (equal (logic.vrhs conclusion) c))))))))

       (logic.expansion-okp
        (x atbl)
        (let ((method     (logic.method x))
              (conclusion (logic.conclusion x))
              (subproofs  (logic.subproofs x))
              (extras     (logic.extras x)))
          (and (equal method 'expansion)
               (equal extras nil)
               (tuplep 1 subproofs)
               (let ((b (logic.conclusion (first subproofs))))
                 (and (equal (logic.fmtype conclusion) 'por*)
                      (equal (logic.vrhs conclusion) b)
                      (logic.formula-atblp (logic.vlhs conclusion) atbl))))))

       (logic.propositional-schema-okp
        (x atbl)
        (let ((method     (logic.method x))
              (conclusion (logic.conclusion x))
              (subproofs  (logic.subproofs x))
              (extras     (logic.extras x)))
          (and (equal method 'propositional-schema)
               (equal subproofs nil)
               (equal extras nil)
               (equal (logic.fmtype conclusion) 'por*)
               (let ((not-a (logic.vlhs conclusion))
                     (a     (logic.vrhs conclusion)))
                 (and (equal (logic.fmtype not-a) 'pnot*)
                      (equal (logic.~arg not-a) a)
                      (logic.formula-atblp a atbl))))))

       (logic.check-functional-axiom
        (x ti si)
        (if (equal (logic.fmtype x) 'pequal*)
            (and (logic.functionp (logic.=lhs x))
                 (logic.functionp (logic.=rhs x))
                 (equal (logic.function-name (logic.=lhs x))
                        (logic.function-name (logic.=rhs x)))
                 (equal (logic.function-args (logic.=lhs x)) (rev ti))
                 (equal (logic.function-args (logic.=rhs x)) (rev si)))
          (and (equal (logic.fmtype x) 'por*)
               (equal (logic.fmtype (logic.vlhs x)) 'pnot*)
               (equal (logic.fmtype (logic.~arg (logic.vlhs x))) 'pequal*)
               (logic.check-functional-axiom
                (logic.vrhs x)
                (cons (logic.=lhs (logic.~arg (logic.vlhs x))) ti)
                (cons (logic.=rhs (logic.~arg (logic.vlhs x))) si)))))

       (logic.functional-equality-okp
        (x atbl)
        (let ((method     (logic.method x))
              (conclusion (logic.conclusion x))
              (subproofs  (logic.subproofs x))
              (extras     (logic.extras x)))
          (and (equal method 'functional-equality)
               (equal subproofs nil)
               (equal extras nil)
               (logic.check-functional-axiom conclusion nil nil)
               (logic.formula-atblp conclusion atbl))))


       ;; Beta-Reduction, Instantiation

       (logic.sigmap (x)
                     (if (consp x)
                         (and (consp (car x))
                              (logic.variablep (car (car x)))
                              (logic.termp (cdr (car x)))
                              (logic.sigmap (cdr x)))
                       t))

       (logic.sigma-listp (x)
                          (if (consp x)
                              (and (logic.sigmap (car x))
                                   (logic.sigma-listp (cdr x)))
                            t))

       (logic.sigma-list-listp (x)
                               (if (consp x)
                                   (and (logic.sigma-listp (car x))
                                        (logic.sigma-list-listp (cdr x)))
                                 t))

       (logic.flag-substitute
        (flag x sigma)
        (if (equal flag 'term)
            (cond ((logic.variablep x)
                   (if (lookup x sigma)
                       (cdr (lookup x sigma))
                     x))
                  ((logic.constantp x)
                   x)
                  ((logic.functionp x)
                   (let ((fn   (logic.function-name x))
                         (args (logic.function-args x)))
                     (logic.function fn (logic.flag-substitute
                                         'list args sigma))))
                  ((logic.lambdap x)
                   (let ((formals (logic.lambda-formals x))
                         (body    (logic.lambda-body x))
                         (actuals (logic.lambda-actuals x)))
                     (logic.lambda formals body (logic.flag-substitute
                                                 'list actuals sigma))))
                  (t nil))
          (if (consp x)
              (cons (logic.flag-substitute 'term (car x) sigma)
                    (logic.flag-substitute 'list (cdr x) sigma))
            nil)))

       (logic.substitute (x sigma)
                         (logic.flag-substitute 'term x sigma))

       (logic.substitute-list (x sigma)
                              (logic.flag-substitute 'list x sigma))

       (logic.substitute-formula
        (formula sigma)
        (let ((type (logic.fmtype formula)))
          (cond ((equal type 'por*)
                 (logic.por
                  (logic.substitute-formula (logic.vlhs formula) sigma)
                  (logic.substitute-formula (logic.vrhs formula) sigma)))
                ((equal type 'pnot*)
                 (logic.pnot
                  (logic.substitute-formula (logic.~arg formula) sigma)))
                ((equal type 'pequal*)
                 (logic.pequal
                  (logic.substitute (logic.=lhs formula) sigma)
                  (logic.substitute (logic.=rhs formula) sigma)))
                (t nil))))

       (logic.instantiation-okp
        (x atbl)
        (let ((method     (logic.method x))
              (conclusion (logic.conclusion x))
              (subproofs  (logic.subproofs x))
              (extras     (logic.extras x)))
          (and (equal method 'instantiation)
               (logic.sigmap extras)
               (tuplep 1 subproofs)
               (equal (logic.substitute-formula
                       (logic.conclusion (first subproofs)) extras)
                      conclusion)
               (logic.formula-atblp conclusion atbl))))

       (logic.beta-reduction-okp
        (x atbl)
        (let ((method     (logic.method x))
              (conclusion (logic.conclusion x))
              (subproofs  (logic.subproofs x))
              (extras     (logic.extras x)))
          (and (equal method 'beta-reduction)
               (equal subproofs nil)
               (equal extras nil)
               (logic.formula-atblp conclusion atbl)
               (equal (logic.fmtype conclusion) 'pequal*)
               (let ((lhs (logic.=lhs conclusion))
                     (rhs (logic.=rhs conclusion)))
                 (and (logic.lambdap lhs)
                      (let ((formals (logic.lambda-formals lhs))
                            (body    (logic.lambda-body lhs))
                            (actuals (logic.lambda-actuals lhs)))
                        (equal (logic.substitute
                                body (pair-lists formals actuals))
                               rhs)))))))

       ;; Base Evaluation

       (logic.initial-arity-table
        ()
        '((if . 3)
          (equal . 2)
          (consp . 1)
          (cons . 2)
          (car . 1)
          (cdr . 1)
          (symbolp . 1)
          (symbol-< . 2)
          (natp . 1)
          (< . 2)
          (+ . 2)
          (- . 2)))

       (logic.base-evaluablep
        (x)
        (and (logic.functionp x)
             (let ((fn   (logic.function-name x))
                   (args (logic.function-args x)))
               (let ((entry (lookup fn (logic.initial-arity-table))))
                 (and entry
                      (logic.constant-listp args)
                      (tuplep (cdr entry) args))))))

       (logic.base-evaluator
        (x)
        (let ((fn   (logic.function-name x))
              (vals (logic.unquote-list (logic.function-args x))))
          (list 'quote
                (cond ((equal fn 'if)
                       (if (first vals)
                           (second vals)
                         (third vals)))
                      ((equal fn 'equal)
                       (equal (first vals) (second vals)))
                      ((equal fn 'consp)
                       (consp (first vals)))
                      ((equal fn 'cons)
                       (cons (first vals) (second vals)))
                      ((equal fn 'car)
                       (car (first vals)))
                      ((equal fn 'cdr)
                       (cdr (first vals)))
                      ((equal fn 'symbolp)
                       (symbolp (first vals)))
                      ((equal fn 'symbol-<)
                       (symbol-< (first vals) (second vals)))
                      ((equal fn 'natp)
                       (natp (first vals)))
                      ((equal fn '<)
                       (< (first vals) (second vals)))
                      ((equal fn '+)
                       (+ (first vals) (second vals)))
                      ((equal fn '-)
                       (- (first vals) (second vals)))))))

       (logic.base-eval-okp
        (x atbl)
        (let ((method     (logic.method x))
              (conclusion (logic.conclusion x))
              (subproofs  (logic.subproofs x))
              (extras     (logic.extras x)))
          (and (equal method 'base-eval)
               (equal subproofs nil)
               (equal extras nil)
               (equal (logic.fmtype conclusion) 'pequal*)
               (let ((lhs (logic.=lhs conclusion))
                     (rhs (logic.=rhs conclusion)))
                 (and (logic.base-evaluablep lhs)
                      (equal (logic.base-evaluator lhs) rhs)
                      (logic.term-atblp lhs atbl))))))


       ;; Induction

       (logic.make-basis-step (f qs)
                              (logic.disjoin-formulas (cons f qs)))

       (logic.substitute-each-sigma-into-formula
        (f x)
        (if (consp x)
            (cons (logic.substitute-formula f (car x))
                  (logic.substitute-each-sigma-into-formula f (cdr x)))
          nil))

       (logic.make-induction-step
        (f q-i sigmas-i)
        (logic.disjoin-formulas
         (cons f (cons (logic.pnot q-i)
                       (logic.substitute-each-sigma-into-formula
                        (logic.pnot f) sigmas-i)))))

       (logic.make-induction-steps
        (f qs all-sigmas)
        (if (consp qs)
            (cons (logic.make-induction-step f (car qs) (car all-sigmas))
                  (logic.make-induction-steps f (cdr qs) (cdr all-sigmas)))
          nil))

       (logic.make-ordinal-step
        (m)
        (logic.pequal (logic.function 'ordp (list m)) ''t))

       (logic.make-measure-step
        (m q-i sigma-i-j)
        (logic.por (logic.pnot q-i)
                   (logic.pequal
                    (logic.function 'ord<
                                    (list (logic.substitute m sigma-i-j) m))
                    ''t)))

       (logic.make-measure-steps
        (m q-i sigmas-i)
        (if (consp sigmas-i)
            (cons (logic.make-measure-step m q-i (car sigmas-i))
                  (logic.make-measure-steps m q-i (cdr sigmas-i)))
          nil))

       (logic.make-all-measure-steps
        (m qs all-sigmas)
        (if (consp all-sigmas)
            (app (logic.make-measure-steps m (car qs) (car all-sigmas))
                 (logic.make-all-measure-steps m (cdr qs) (cdr all-sigmas)))
          nil))

       (logic.induction-okp
        (x)
        (let ((method     (logic.method x))
              (conclusion (logic.conclusion x))
              (subproofs  (logic.subproofs x))
              (extras     (logic.extras x)))
          (and
           (equal method 'induction)
           (tuplep 3 extras)
           (let ((m          (first extras))
                 (qs         (second extras))
                 (all-sigmas (third extras))
                 (subconcs   (logic.strip-conclusions subproofs)))
             (and (logic.termp m)
                  (logic.formula-listp qs)
                  (logic.sigma-list-listp all-sigmas)
                  (equal (len qs) (len all-sigmas))
                  (memberp (logic.make-basis-step conclusion qs) subconcs)
                  (subsetp (logic.make-induction-steps conclusion qs all-sigmas)
                           subconcs)
                  (memberp (logic.make-ordinal-step m) subconcs)
                  (subsetp (logic.make-all-measure-steps m qs all-sigmas)
                           subconcs))))))


       ;; Proof Checking

       (logic.appeal-step-okp
        (x axioms thms atbl)
        (let ((how (logic.method x)))
          (cond ((equal how 'axiom)
                 (logic.axiom-okp x axioms atbl))
                ((equal how 'theorem)
                 (logic.theorem-okp x thms atbl))
                ((equal how 'propositional-schema)
                 (logic.propositional-schema-okp x atbl))
                ((equal how 'functional-equality)
                 (logic.functional-equality-okp x atbl))
                ((equal how 'beta-reduction)
                 (logic.beta-reduction-okp x atbl))
                ((equal how 'expansion)
                 (logic.expansion-okp x atbl))
                ((equal how 'contraction)
                 (logic.contraction-okp x))
                ((equal how 'associativity)
                 (logic.associativity-okp x))
                ((equal how 'cut)
                 (logic.cut-okp x))
                ((equal how 'instantiation)
                 (logic.instantiation-okp x atbl))
                ((equal how 'induction)
                 (logic.induction-okp x))
                ((equal how 'base-eval)
                 (logic.base-eval-okp x atbl))
                (t nil))))

       (logic.flag-proofp
        (flag x axioms thms atbl)
        (if (equal flag 'proof)
            (and (logic.appeal-step-okp x axioms thms atbl)
                 (logic.flag-proofp 'list (logic.subproofs x) axioms thms atbl))
          (if (consp x)
              (and (logic.flag-proofp 'proof (car x) axioms thms atbl)
                   (logic.flag-proofp 'list (cdr x) axioms thms atbl))
            t)))

       (logic.proofp (x axioms thms atbl)
                     (logic.flag-proofp 'proof x axioms thms atbl))

       (logic.provable-witness
        (x axioms thms atbl)
        (error '(logic.provable-witness
                 proof
                 (x axioms thms atbl)
                 (and (logic.appealp proof)
                      (logic.proofp proof axioms thms atbl)
                      (equal (logic.conclusion proof) x)))))

       (logic.provablep
        (x axioms thms atbl)
        (let ((proof (logic.provable-witness x axioms thms atbl)))
          (and (logic.appealp proof)
               (logic.proofp proof axioms thms atbl)
               (equal (logic.conclusion proof) x))))

       ;; SUPPORTING ABBREVIATIONS

       (remove-all (a x)
                   (if (consp x)
                       (if (equal a (car x))
                           (remove-all a (cdr x))
                         (cons (car x) (remove-all a (cdr x))))
                     nil))

       (remove-duplicates (x)
                          (if (consp x)
                              (if (memberp (car x) (cdr x))
                                  (remove-duplicates (cdr x))
                                (cons (car x) (remove-duplicates (cdr x))))
                            nil))

       (difference (x y)
                   (if (consp x)
                       (if (memberp (car x) y)
                           (difference (cdr x) y)
                         (cons (car x)
                               (difference (cdr x) y)))
                     nil))

       (strip-firsts (x)
                     (if (consp x)
                         (cons (first (car x))
                               (strip-firsts (cdr x)))
                       nil))

       (strip-seconds (x)
                      (if (consp x)
                          (cons (second (car x))
                                (strip-seconds (cdr x)))
                        nil))

       (tuple-listp (n x)
                    (if (consp x)
                        (and (tuplep n (car x))
                             (tuple-listp n (cdr x)))
                      t))

       (sort-symbols-insert
        (a x)
        (if (consp x)
            (if (symbol-< a (car x))
                (cons a x)
              (cons (car x)
                    (sort-symbols-insert a (cdr x))))
          (list a)))

       (sort-symbols
        (x)
        (if (consp x)
            (sort-symbols-insert (car x)
                                 (sort-symbols (cdr x)))
          nil))

       (logic.translate-and-term
        (args)
        (if (consp args)
            (if (consp (cdr args))
                (logic.function
                 'if
                 (list (first args)
                       (logic.translate-and-term (cdr args))
                       ''nil))
              (first args))
          ''t))

       (logic.translate-let-term
        (vars terms body)
        (let* ((body-vars (remove-duplicates (logic.term-vars body)))
               (id-vars   (sort-symbols (difference body-vars vars)))
               (formals   (app id-vars vars))
               (actuals   (app id-vars terms)))
          (logic.lambda formals body actuals)))

       (logic.translate-or-term
        (args)
        (if (consp args)
            (if (consp (cdr args))
                (let* ((else-term (logic.translate-or-term (cdr args)))
                       (cheap-p   (or (logic.variablep (car args))
                                      (logic.constantp (car args)))))
                  (if (or cheap-p
                          (memberp 'special-var-for-or
                                   (logic.term-vars else-term)))
                      (logic.function 'if (list (car args) (car args) else-term))
                    (logic.translate-let-term
                     (list 'special-var-for-or)
                     (list (car args))
                     (logic.function 'if (list 'special-var-for-or
                                               'special-var-for-or
                                               else-term)))))
              (first args))
          ''nil))

       (logic.translate-list-term
        (args)
        (if (consp args)
            (logic.function
             'cons
             (list (car args)
                   (logic.translate-list-term (cdr args))))
          ''nil))

       (logic.translate-cond-term
        (tests thens)
        (if (consp tests)
            (let ((test1 (car tests))
                  (then1 (car thens)))
              (logic.function
               'if
               (list test1
                     then1
                     (logic.translate-cond-term (cdr tests)
                                                (cdr thens)))))
          ''nil))

       (logic.translate-let*-term
        (vars terms body)
        (if (consp vars)
            (logic.translate-let-term
             (list (car vars))
             (list (car terms))
             (logic.translate-let*-term (cdr vars)
                                        (cdr terms)
                                        body))
          body))

       (logic.flag-translate
        (flag x)
        (if (equal flag 'term)
            (cond ((natp x)
                   (list 'quote x))
                  ((symbolp x)
                   (if (or (equal x nil)
                           (equal x t))
                       (list 'quote x)
                     x))
                  ((symbolp (car x))
                   (let ((fn (car x)))
                     (cond ((equal fn 'quote)
                            (if (tuplep 2 x)
                                x
                              nil))
                           ((memberp fn '(first second third fourth fifth))
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
                                                     (t
                                                      (logic.translate-let*-term vars
                                                                                 (cdr terms+)
                                                                                 body)))))))))
                           ((logic.function-namep fn)
                            (and (true-listp (cdr x))
                                 (let ((arguments+ (logic.flag-translate 'list (cdr x))))
                                   (and (car arguments+)
                                        (logic.function fn (cdr arguments+))))))
                           (t
                            nil))))
                  ((and (tuplep 3 (car x))
                        (true-listp (cdr x)))
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
                   nil))
          (if (consp x)
              (let ((first (logic.flag-translate 'term (car x)))
                    (rest  (logic.flag-translate 'list (cdr x))))
                (if (and first (car rest))
                    (cons t (cons first (cdr rest)))
                  (cons nil nil)))
            (cons t nil))))

       (logic.translate (x) (logic.flag-translate 'term x))


       ;; TERMINATION OBLIGATIONS

       (cons-onto-ranges
        (a x)
        (if (consp x)
            (cons (cons (car (car x))
                        (cons a (cdr (car x))))
                  (cons-onto-ranges a (cdr x)))
          nil))

       (logic.substitute-callmap
        (x sigma)
        (if (consp x)
            (let ((actuals (car (car x)))
                  (rulers  (cdr (car x))))
              (cons (cons (logic.substitute-list actuals sigma)
                          (logic.substitute-list rulers sigma))
                    (logic.substitute-callmap (cdr x) sigma)))
          nil))

       (logic.flag-callmap
        (flag f x)
        (if (equal flag 'term)
            (cond ((logic.constantp x)
                   nil)
                  ((logic.variablep x)
                   nil)
                  ((logic.functionp x)
                   (let ((name (logic.function-name x))
                         (args (logic.function-args x)))
                     (cond ((and (equal name 'if)
                                 (equal (len args) 3))
                            (let ((test-calls
                                   (logic.flag-callmap 'term f (first args)))
                                  (true-calls
                                   (cons-onto-ranges
                                    (first args)
                                    (logic.flag-callmap 'term f (second args))))
                                  (else-calls
                                   (cons-onto-ranges
                                    (logic.function 'not (list (first args)))
                                    (logic.flag-callmap 'term f (third args)))))
                              (app test-calls (app true-calls else-calls))))
                           ((equal name f)
                            (let ((this-call   (cons args nil))
                                  (child-calls (logic.flag-callmap 'list f args)))
                              (cons this-call child-calls)))
                           (t
                            (logic.flag-callmap 'list f args)))))
                  ((logic.lambdap x)
                   (let ((formals (logic.lambda-formals x))
                         (body    (logic.lambda-body x))
                         (actuals (logic.lambda-actuals x)))
                     (let ((actuals-calls (logic.flag-callmap 'list f actuals))
                           (body-calls    (logic.flag-callmap 'term f body))
                           (sigma         (pair-lists formals actuals)))
                       (app actuals-calls
                            (logic.substitute-callmap body-calls sigma))))))
          (if (consp x)
              (app (logic.flag-callmap 'term f (car x))
                   (logic.flag-callmap 'list f (cdr x)))
            nil)))

       (logic.callmap (f x)
                      (logic.flag-callmap 'term f x))

       (repeat (a n)
               (if (zp n)
                   nil
                 (cons a (repeat a (- n 1)))))

       (logic.pequal-list (x y)
                          (if (and (consp x)
                                   (consp y))
                              (cons (logic.pequal (car x) (car y))
                                    (logic.pequal-list (cdr x) (cdr y)))
                            nil))

       (logic.progress-obligation
        (measure formals actuals rulers)
        (let* ((sigma    (pair-lists formals actuals))
               (m/sigma  (logic.substitute measure sigma))
               (ord-term (logic.function 'ord< (list m/sigma measure))))
          (logic.disjoin-formulas
           (cons (logic.pequal ord-term ''t)
                 (logic.pequal-list rulers (repeat ''nil (len rulers)))))))

       (logic.progress-obligations
        (measure formals callmap)
        (if (consp callmap)
            (let* ((entry   (car callmap))
                   (actuals (car entry))
                   (rulers  (cdr entry)))
              (cons (logic.progress-obligation measure formals actuals rulers)
                    (logic.progress-obligations measure formals (cdr callmap))))
          nil))

       (logic.termination-obligations
        (name formals body measure)
        (let ((callmap (logic.callmap name body)))
          (if callmap
              (cons (logic.pequal (logic.function 'ordp (list measure)) ''t)
                    (logic.progress-obligations measure formals callmap))
            nil)))


       (core.initial-atbl ()
                          (app '((rank . 1)
                                 (ordp . 1)
                                 (ord< . 2))
                               (logic.initial-arity-table)))

       (core.initial-axioms
        ()
        (app '( ;; reflexivity
               (pequal* x x)

               ;; equality
               (por* (pnot* (pequal* x1 y1))
                     (por* (pnot* (pequal* x2 y2))
                           (por* (pnot* (pequal* x1 x2))
                                 (pequal* y1 y2))))

               ;; t-not-nil
               (pnot* (pequal* 't 'nil))

               ;; equal-when-same
               (por* (pnot* (pequal* x y))
                     (pequal* (equal x y) 't))

               ;; equal-when-diff
               (por* (pequal* x y)
                     (pequal* (equal x y) 'nil))

               ;; if-when-nil
               (por* (pnot* (pequal* x 'nil))
                     (pequal* (if x y z) z))

               ;; if-when-not-nil
               (por* (pequal* x 'nil)
                     (pequal* (if x y z) y))

               ;; consp-of-cons
               (pequal* (consp (cons x y)) 't)

               ;; car-of-cons
               (pequal* (car (cons x y)) x)

               ;; cdr-of-cons
               (pequal* (cdr (cons x y)) y)

               ;; consp-nil-or-t
               (por* (pequal* (consp x) 'nil)
                     (pequal* (consp x) 't))

               ;; car-when-not-consp
               (por* (pnot* (pequal* (consp x) 'nil))
                     (pequal* (car x) 'nil))

               ;; cdr-when-not-consp
               (por* (pnot* (pequal* (consp x) 'nil))
                     (pequal* (cdr x) 'nil))

               ;; cons-of-car-and-cdr
               (por* (pequal* (consp x) 'nil)
                     (pequal* (cons (car x) (cdr x)) x))

               ;; symbolp-nil-or-t
               (por* (pequal* (symbolp x) 'nil)
                     (pequal* (symbolp x) 't))

               ;; symbol-<-nil-or-t
               (por* (pequal* (symbol-< x y) 'nil)
                     (pequal* (symbol-< x y) 't))

               ;; irreflexivity-of-symbol-<
               (pequal* (symbol-< x x) 'nil)

               ;; antisymmetry-of-symbol-<
               (por* (pequal* (symbol-< x y) 'nil)
                     (pequal* (symbol-< y x) 'nil))

               ;; transitivity-of-symbol-<
               (por* (pequal* (symbol-< x y) 'nil)
                     (por* (pequal* (symbol-< y z) 'nil)
                           (pequal* (symbol-< x z) 't)))

               ;; trichotomy-of-symbol-<
               (por* (pequal* (symbolp x) 'nil)
                     (por* (pequal* (symbolp y) 'nil)
                           (por* (pequal* (symbol-< x y) 't)
                                 (por* (pequal* (symbol-< y x) 't)
                                       (pequal* x y)))))

               ;; symbol-<-completion-left
               (por* (pequal* (symbolp x) 't)
                     (pequal* (symbol-< x y)
                              (symbol-< 'nil y)))

               ;; symbol-<-completion-right
               (por* (pequal* (symbolp y) 't)
                     (pequal* (symbol-< x y)
                              (symbol-< x 'nil)))

               ;; disjoint-symbols-and-naturals
               (por* (pequal* (symbolp x) 'nil)
                     (pequal* (natp x) 'nil))

               ;; disjoint-symbols-and-conses
               (por* (pequal* (symbolp x) 'nil)
                     (pequal* (consp x) 'nil))

               ;; disjoint-naturals-and-conses
               (por* (pequal* (natp x) 'nil)
                     (pequal* (consp x) 'nil))

               ;; natp-nil-or-t
               (por* (pequal* (natp x) 'nil)
                     (pequal* (natp x) 't))

               ;; natp-of-plus
               (pequal* (natp (+ a b)) 't)

               ;; commutativity-of-+
               (pequal* (+ a b) (+ b a))

               ;; associativity-of-+
               (pequal* (+ (+ a b) c)
                        (+ a (+ b c)))

               ;; plus-when-not-natp-left
               (por* (pequal* (natp a) 't)
                     (pequal* (+ a b) (+ '0 b)))

               ;; plus-of-zero-when-natural
               (por* (pequal* (natp a) 'nil)
                     (pequal* (+ a '0) a))

               ;; <-nil-or-t
               (por* (pequal* (< x y) 'nil)
                     (pequal* (< x y) 't))

               ;; irreflexivity-of-<
               (pequal* (< a a) 'nil)

               ;; less-of-zero-right
               (pequal* (< a '0) 'nil)

               ;; less-of-zero-left-when-natp
               (por* (pequal* (natp a) 'nil)
                     (pequal* (< '0 a)
                              (if (equal a '0) 'nil 't)))

               ;; less-completion-left
               (por* (pequal* (natp a) 't)
                     (pequal* (< a b)
                              (< '0 b)))

               ;; less-completion-right
               (por* (pequal* (natp b) 't)
                     (pequal* (< a b)
                              'nil))

               ;; transitivity-of-<
               (por* (pequal* (< a b) 'nil)
                     (por* (pequal* (< b c) 'nil)
                           (pequal* (< a c) 't)))

               ;; trichotomy-of-<-when-natp
               (por* (pequal* (natp a) 'nil)
                     (por* (pequal* (natp b) 'nil)
                           (por* (pequal* (< a b) 't)
                                 (por* (pequal* (< b a) 't)
                                       (pequal* a b)))))

               ;; one-plus-trick
               (por* (pequal* (< a b) 'nil)
                     (pequal* (< b (+ '1 a)) 'nil))

               ;; natural-less-than-one-is-zero
               (por* (pequal* (natp a) 'nil)
                     (por* (pequal* (< a '1) 'nil)
                           (pequal* a '0)))

               ;; less-than-of-plus-and-plus
               (pequal* (< (+ a b) (+ a c))
                        (< b c))

               ;; natp-of-minus
               (pequal* (natp (- a b)) 't)

               ;; minus-when-subtrahend-as-large
               (por* (pequal* (< b a) 't)
                     (pequal* (- a b) '0))

               ;; minus-cancels-summand-right
               (pequal* (- (+ a b) b)
                        (if (natp a) a '0))

               ;; less-of-minus-left
               (por* (pequal* (< b a) 'nil)
                     (pequal* (< (- a b) c)
                              (< a (+ b c))))

               ;; less-of-minus-right
               (pequal* (< a (- b c))
                        (< (+ a c) b))

               ;; plus-of-minus-right
               (por* (pequal* (< c b) 'nil)
                     (pequal* (+ a (- b c))
                              (- (+ a b) c)))

               ;; minus-of-minus-right
               (por* (pequal* (< c b) 'nil)
                     (pequal* (- a (- b c))
                              (- (+ a c) b)))

               ;; minus-of-minus-left
               (pequal* (- (- a b) c)
                        (- a (+ b c)))

               ;; equal-of-minus-property
               (por* (pequal* (< b a) 'nil)
                     (pequal* (equal (- a b) c)
                              (equal a (+ b c))))

               ;; closed-universe
               (por* (pequal* (natp x) 't)
                     (por* (pequal* (symbolp x) 't)
                           (pequal* (consp x) 't))))

             (list
              ;; definition-of-not
              (logic.pequal '(not x)
                            (logic.translate '(if x nil t)))

              ;; definition-of-rank
              (logic.pequal '(rank x)
                            (logic.translate '(if (consp x)
                                                  (+ 1
                                                     (+ (rank (car x))
                                                        (rank (cdr x))))
                                                0)))

              ;; definition-of-ord<
              (logic.pequal '(ord< x y)
                            (logic.translate '(cond ((not (consp x))
                                                     (if (consp y)
                                                         t
                                                       (< x y)))
                                                    ((not (consp y))
                                                     nil)
                                                    ((not (equal (car (car x))
                                                                 (car (car y))))
                                                     (ord< (car (car x))
                                                           (car (car y))))
                                                    ((not (equal (cdr (car x))
                                                                 (cdr (car y))))
                                                     (< (cdr (car x))
                                                        (cdr (car y))))
                                                    (t
                                                     (ord< (cdr x) (cdr y))))))

              ;; definition-of-ordp
              (logic.pequal '(ordp x)
                            (logic.translate '(if (not (consp x))
                                                  (natp x)
                                                (and (consp (car x))
                                                     (ordp (car (car x)))
                                                     (not (equal (car (car x)) 0))
                                                     (< 0 (cdr (car x)))
                                                     (ordp (cdr x))
                                                     (if (consp (cdr x))
                                                         (ord< (car (car (cdr x)))
                                                               (car (car x)))
                                                       t))))))))

       (core.state (axioms thms atbl checker ftbl)
                   (list axioms thms atbl checker ftbl))

       (core.axioms  (x) (first x))
       (core.thms    (x) (second x))
       (core.atbl    (x) (third x))
       (core.checker (x) (fourth x))
       (core.ftbl    (x) (fifth x))

       (core.check-proof
        (checker proof axioms thms atbl)
        ;; BOZO for the verified lisp, this will be different.
        ;; BOZO for now, assume proofs are valid
        ;; t
        (CL-USER::funcall checker proof axioms thms atbl)
        )

       (core.check-proof-list
        (checker proofs axioms thms atbl)
        (if (consp proofs)
            (and (core.check-proof checker (car proofs) axioms thms atbl)
                 (core.check-proof-list checker (cdr proofs) axioms thms atbl))
          t))

       (logic.soundness-claim
        (name)
        (logic.por
         '(pequal* (logic.appealp x) 'nil)
         (logic.por
          (logic.pequal (logic.function name '(x axioms thms atbl))
                        ''nil)
          '(pnot* (pequal* (logic.provablep (logic.conclusion x)
                                            axioms thms atbl)
                           'nil)))))

       (core.admit-switch
        (cmd state)
        ;; Returns a new state or calls error.
        ;; CMD should be (SWITCH NAME)
        (if (or (not (tuplep 2 cmd))
                (not (equal (first cmd) 'switch)))
            (error (list 'admit-switch 'invalid-cmd cmd))
          (let ((axioms  (core.axioms state))
                (thms    (core.thms state))
                (atbl    (core.atbl state))
                (ftbl    (core.ftbl state))
                (name    (second cmd)))
            (cond ((not (logic.function-namep name))
                   (error (list 'admit-switch 'invalid-name name)))
                  ((not (memberp (logic.soundness-claim name) (core.thms state)))
                   (error (list 'admit-switch 'not-verified name)))
                  (t
                   (core.state axioms thms atbl name ftbl))))))

       (core.admit-theorem
        (cmd state)
        ;; Returns a new state or calls error.
        ;; CMD should be (VERIFY NAME FORMULA PROOF)
        (if (or (not (tuplep 4 cmd))
                (not (equal (first cmd) 'verify)))
            (error (list 'admit-theorem 'invalid-cmd cmd))
          (let ((axioms  (core.axioms state))
                (thms    (core.thms state))
                (atbl    (core.atbl state))
                (checker (core.checker state))
                (ftbl    (core.ftbl state))
                (name    (second cmd))
                (formula (third cmd))
                (proof   (fourth cmd)))
            (cond
             ((not (logic.formulap formula))
              (error (list 'admit-theorem 'not-formulap name)))
             ((not (logic.formula-atblp formula atbl))
              (error (list 'admit-theorem 'not-formula-atblp
                           name formula atbl)))
             ((not (logic.appealp proof))
              (error (list 'admit-theorem 'not-appealp name)))
             ((not (equal (logic.conclusion proof) formula))
              (error (list 'admit-theorem 'wrong-conclusion name)))
             ((not (core.check-proof checker proof axioms thms atbl))
              (error (list 'admit-theorem 'proof-rejected name)))
             (t
              (if (memberp formula thms)
                  state
                (core.state axioms (cons formula thms) atbl checker ftbl)))))))

       (core.admit-defun
        (cmd state)
        ;; Returns a new state or calls error.
        ;; CMD should be (DEFINE NAME FORMALS BODY MEASURE PROOF-LIST)
        (if (or (not (tuplep 6 cmd))
                (not (equal (car cmd) 'define)))
            (error (list 'admit-defun 'invalid-cmd cmd))
          (let* ((axioms      (core.axioms state))
                 (thms        (core.thms state))
                 (atbl        (core.atbl state))
                 (checker     (core.checker state))
                 (ftbl        (core.ftbl state))
                 (name        (second  cmd))
                 (formals     (third cmd))
                 (raw-body    (fourth cmd))
                 (raw-measure (fifth cmd))
                 (proofs      (fifth (cdr cmd)))
                 (body        (logic.translate raw-body))
                 (measure     (logic.translate raw-measure))
                 (arity       (len formals))
                 (new-atbl    (cons (cons name arity) atbl))
                 (obligations (logic.termination-obligations
                               name formals body measure)))
            (cond ((not (logic.function-namep name))
                   (error (list 'admit-defun 'bad-name name)))
                  ((not (logic.variable-listp formals))
                   (error (list 'admit-defun 'bad-formals name)))
                  ((not (uniquep formals))
                   (error (list 'admit-defun 'duplicated-formals name)))
                  ((not (logic.termp body))
                   (error (list 'admit-defun 'bad-body name)))
                  ((not (logic.termp measure))
                   (error (list 'admit-defun 'bad-measure name)))
                  ((not (subsetp (logic.term-vars body) formals))
                   (error (list 'admit-defun 'free-vars-in-body name)))
                  ((not (subsetp (logic.term-vars measure) formals))
                   (error (list 'admit-defun 'free-vars-in-measure name)))
                  ((not (logic.term-atblp body new-atbl))
                   (error (list 'admit-defun 'bad-arity-in-body name)))
                  ((not (logic.term-atblp measure new-atbl))
                   (error (list 'admit-defun 'bad-arity-in-measure name)))
                  ((not (logic.appeal-listp proofs))
                   (error (list 'admit-defun 'proofs-not-appeals name)))
                  ((not (equal (logic.strip-conclusions proofs) obligations))
                   (error (list 'admit-defun 'proofs-wrong-conclusions name)))
                  ((not (core.check-proof-list checker proofs axioms thms
                                               new-atbl))
                   (error (list 'admit-defun 'proof-rejected name)))
                  (t
                   (let* ((ftbl      (define-safe ftbl name formals raw-body))
                          (new-axiom (logic.pequal (logic.function name formals)
                                                   body))
                          (atbl      (if (lookup name atbl)
                                         atbl
                                       new-atbl))
                          (axioms    (if (memberp new-axiom axioms)
                                         axioms
                                       (cons new-axiom axioms))))
                     (core.state axioms thms atbl checker ftbl)))))))

       (core.admit-witness
        (cmd state)
        ;; Returns a new state or calls error
        ;; CMD should be (SKOLEM NAME BOUND-VAR FREE-VAR BODY)
        (if (or (not (tuplep 5 cmd))
                (not (equal (car cmd) 'skolem)))
            (error (list 'admit-witness 'invalid-cmd cmd))
          (let* ((axioms    (core.axioms state))
                 (thms      (core.thms state))
                 (atbl      (core.atbl state))
                 (checker   (core.checker state))
                 (ftbl      (core.ftbl state))
                 (name      (second cmd))
                 (bound-var (third cmd))
                 (free-vars (fourth cmd))
                 (raw-body  (fifth cmd))
                 (body      (logic.translate raw-body))
                 (all-vars  (cons bound-var free-vars)))
            (cond
             ((not (logic.function-namep name))
              (error (list 'admit-witness 'bad-name name)))
             ((not (logic.variablep bound-var))
              (error (list 'admit-witness 'bad-bound-var name)))
             ((not (logic.variable-listp free-vars))
              (error (list 'admit-witness 'bad-free-vars name)))
             ((not (uniquep (cons bound-var free-vars)))
              (error (list 'admit-witness 'duplicate-free-vars name)))
             ((not (logic.termp body))
              (error (list 'admit-witness 'bad-body name)))
             ((not (subsetp (logic.term-vars body) all-vars))
              (error (list 'admit-witness 'free-vars-in-body name)))
             ((not (logic.term-atblp body atbl))
              (error (list 'admit-witness 'bad-arity-in-body name)))
             (t
              (let* ((ftbl (define-safe ftbl name free-vars
                             (list 'error
                                   (list 'quote
                                         (list name bound-var
                                               free-vars raw-body)))))
                     (atbl (if (lookup name atbl)
                               atbl
                             (cons (cons name (len free-vars)) atbl)))
                     (new-axiom
                      (logic.por (logic.pequal body ''nil)
                                 (logic.pnot
                                  (logic.pequal
                                   (logic.lambda
                                    all-vars body
                                    (cons (logic.function name free-vars)
                                          free-vars))
                                   ''nil))))
                     (axioms (if (memberp new-axiom axioms)
                                 axioms
                               (cons new-axiom axioms))))
                (core.state axioms thms atbl checker ftbl)))))))

       (core.accept-command
        (cmd state)
        ;; Returns a new state or calls error
        (cond ((equal (car cmd) 'verify) (core.admit-theorem cmd state))
              ((equal (car cmd) 'define) (core.admit-defun cmd state))
              ((equal (car cmd) 'skolem) (core.admit-witness cmd state))
              ((equal (car cmd) 'switch) (core.admit-switch cmd state))
              (t
               (error (list 'accept-cmd 'invalid-command cmd)))))

       (core.accept-commands
        (cmds event-number state)
        ;; Returns a new state or calls error.
        (if (consp cmds)
            (let* ((unused (print (list event-number
                                        (first (car cmds))
                                        (second (car cmds)))))
                   (state (core.accept-command (car cmds) state)))
              (core.accept-commands (cdr cmds)
                                    (+ 1 event-number)
                                    state))
          state)))))

(milawa-init)

(define 'milawa-main '(cmds)
  '(let* ((ftbl      (milawa-init))
          (axioms    (core.initial-axioms))
          (thms      nil)
          (atbl      (core.initial-atbl))
          (checker   'logic.proofp)
          (state     (core.state axioms thms atbl checker ftbl)))
     (and (core.accept-commands cmds 1 state)
          'success)))



; READING THE PROOF FILE

(CL-USER::in-package "CL-USER")

(defun-comp aux-acceptable-objectp (x cache)
  (or (and (integerp x)
           (<= 0 x))
      (and (symbolp x)
           (equal x (intern (symbol-name x) "MILAWA")))
      (and (consp x)
           (let ((status (gethash x cache)))
             (cond ((eq status t)
                    t)
                   ((eq status nil)
                    (progn (setf (gethash x cache) 'exploring)
                           (and (aux-acceptable-objectp (car x) cache)
                                (aux-acceptable-objectp (cdr x) cache)
                                (setf (gethash x cache) t))))
                   (t
                    nil))))))

(defconstant rough-number-of-unique-conses-in-proofs 525000000)

(defun-comp acceptable-objectp (x)
  (let* ((size (ceiling (* 1.10 rough-number-of-unique-conses-in-proofs)))
         (cache (make-hash-table :size size :test 'eq)))
    (aux-acceptable-objectp x cache)))

(defvar *milawa-readtable* (copy-readtable *readtable*))
(declaim (readtable *milawa-readtable*))

(defvar *milawa-abbreviations-hash-table*)
(declaim (type hash-table *milawa-abbreviations-hash-table*))

(defun-comp milawa-sharp-equal-reader (stream subchar arg)
  (declare (ignore subchar))
  (multiple-value-bind
   (value presentp)
   (gethash arg *milawa-abbreviations-hash-table*)
   (declare (ignore value))
   (when presentp
     (error "#~A= is already defined." arg))
   (let ((object (read stream)))
     (setf (gethash arg *milawa-abbreviations-hash-table*) object))))

(defun-comp milawa-sharp-sharp-reader (stream subchar arg)
  (declare (ignore stream subchar))
  (or (gethash arg *milawa-abbreviations-hash-table*)
      (error "#~A# used but not defined." arg)))

(let ((*readtable* *milawa-readtable*))
  (set-dispatch-macro-character #\# #\# #'milawa-sharp-sharp-reader)
  (set-dispatch-macro-character #\# #\= #'milawa-sharp-equal-reader))

(defconstant unique-cons-for-eof (cons 'unique-cons 'for-eof))

(defun-comp milawa-read-file-aux (stream)
   (let ((obj (read stream nil unique-cons-for-eof)))
     (cond ((eq obj unique-cons-for-eof)
            nil)
           (t
            (cons obj (milawa-read-file-aux stream))))))

(defun-comp milawa-read-file (filename)
  (format t ";; Reading from ~A~%" filename)
  (finish-output)
  (let* ((size (ceiling (* 1.10 rough-number-of-unique-conses-in-proofs)))
         (*milawa-abbreviations-hash-table* (make-hash-table :size size
                                                             :test 'eql))
         (*readtable* *milawa-readtable*)
         (*package* (find-package "MILAWA"))
         (stream (open filename
                       :direction :input
                       :if-does-not-exist :error))
         (contents (time (milawa-read-file-aux stream))))
    (close stream)
    ;; Allow abbrevs table to get gc'd.
    (setq *milawa-abbreviations-hash-table* (make-hash-table :test 'eql))
    (ccl::gc)
    (format t ";; Skipping acceptable-object.")
;    (format t ";; Checking acceptable-objectp.~%")
;    (finish-output)
;    (unless (time (acceptable-objectp contents))
;      (error "unacceptable object encountered"))
    (ccl::gc)
    contents))


(defun main ()
  (handler-case
   (let ((events (car (milawa-read-file "full.events"))))
     (MILAWA::milawa-main events))
   (error (x)
    (progn
      (format t "Error: ~a" x)
      (quit)))))

;; (CCL::save-application "milawa2"
;;                        :toplevel-function #'main
;;                        :purify t)


#||


(defun unique-conses (x ht)
  ;; ht associates objects with their number of unique conses
  (if (atom x)
      nil
    (or (gethash x ht)
        (let ((car-count (unique-conses (car x) ht))
              (cdr-count (unique-conses (cdr x) ht)))
          (setf (gethash x ht) (+ car-count cdr-count))))))

(unique-conses *events* (make-hash-table
                         :test #'eq
                         :size (ceiling (* 1.1 525000000))))


(defparameter *events*
  (car (milawa-read-file "full.events")))

(defparameter *events*
  (time (car (milawa-read-file "ACL2/bootstrap/verified-lisp/full.events"))))

(- 753.0 (* 12 60.0))

(defun take (n x)
  (if (= n 0)
      nil
    (cons (car x)
          (take (- n 1) (cdr x)))))

(defparameter *st*
  (let* ((ftbl      (milawa::milawa-init))
         (axioms    (milawa::core.initial-axioms))
         (thms      nil)
         (atbl      (milawa::core.initial-atbl))
         (checker   'milawa::logic.proofp)
         (state     (milawa::core.state axioms thms atbl checker ftbl)))
    (milawa::core.accept-commands (take 1927 *events*) 0 state)))

(defvar *st2*
  (milawa::core.accept-commands (list (nth 1927 *events*)) 1927 *st*))

(defvar *st3*
  (milawa::core.accept-commands (list (nth 1928 *events*)) 1928 *st2*))

(defvar *st3*
  (milawa::core.accept-commands (list (nth 1928 *events*)) 1928 *st*))

||#