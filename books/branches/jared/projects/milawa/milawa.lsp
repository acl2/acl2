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


; SPECIAL LISP-SPECIFIC CONFIGURATION

#+allegro
(progn
  (defun quit () (exit))              ; "quit" is not defined in allegro
  (declaim (optimize (debug 0))))

#+clozure
(progn
  (setq ccl::*default-control-stack-size* (expt 2 27))
  (setq ccl::*default-value-stack-size* (expt 2 27))
  (setq ccl::*default-temp-stack-size* (expt 2 27))
  (setq ccl::*initial-listener-default-value-stack-size* (expt 2 27))
  (setq ccl::*initial-listener-default-control-stack-size* (expt 2 27))
  (setq ccl::*initial-listener-default-temp-stack-size* (expt 2 27))
  (CCL::egc nil)
  (CCL::set-lisp-heap-gc-threshold (expt 2 29))
  (CCL::gc-verbose t t)

  ;; avoid running into bug #622 on save-application
  (setq ccl::*print-process-whostate* nil))

#+cmucl
(progn
  (declaim (optimize (extensions:inhibit-warnings 3) (debug 0) (compilation-speed 0)))
  (setq extensions:*bytes-consed-between-gcs* (expt 2 29)))

#+sbcl
(progn
  ;; SBCL on linux-32 complains about 2^29 being just slightly too big.
  (setf (sb-ext:bytes-consed-between-gcs) (- (expt 2 29) 10)))

#+scl
(progn
  (setf (ext:bytes-consed-between-gcs) (expt 2 29)))


; PACKAGE SETUP AND LOGICAL PRIMITIVES

(in-package "CL-USER")
(declaim (optimize (speed 3) (safety 0) (space 0)))

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
          COMMON-LISP::list*
          COMMON-LISP::and
          COMMON-LISP::or
          COMMON-LISP::cond
          COMMON-LISP::lambda)
        "MILAWA")

(defconstant milawa-package (find-package "MILAWA"))


(defmacro defun-comp (&rest args)
  `(compile (defun ,@args)))




(defvar *acceptable-object-tbl*)
(declaim (type hash-table *acceptable-object-tbl*))

(defun-comp aux-acceptable-objectp (x)
  (or (and (integerp x)
           (<= 0 x))
      (and (symbolp x)
           (equal x (intern (symbol-name x) milawa-package)))
      (and (consp x)
           (let ((status (gethash x *acceptable-object-tbl*)))
             (cond ((eq status t)
                    t)
                   ((eq status nil)
                    (progn (setf (gethash x *acceptable-object-tbl*) 'exploring)
                           (and (aux-acceptable-objectp (car x))
                                (aux-acceptable-objectp (cdr x))
                                (setf (gethash x *acceptable-object-tbl*) t))))
                   (t
                    nil))))))

(defun-comp acceptable-objectp (x)
  (let ((*acceptable-object-tbl* (make-hash-table :test 'eq)))
    (aux-acceptable-objectp x)))





(declaim (inline MILAWA::natp
                 MILAWA::symbol-<
                 MILAWA::<
                 MILAWA::+
                 MILAWA::-
                 MILAWA::car
                 MILAWA::cdr))

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
  (let ((x-fix (if (integerp x) x 0))
        (y-fix (if (integerp y) y 0)))
    (+ x-fix y-fix)))

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
(defmacro MILAWA::second (x) `(MILAWA::first (MILAWA::cdr ,x)))
(defmacro MILAWA::third  (x) `(MILAWA::second (MILAWA::cdr ,x)))
(defmacro MILAWA::fourth (x) `(MILAWA::third (MILAWA::cdr ,x)))
(defmacro MILAWA::fifth  (x) `(MILAWA::fourth (MILAWA::cdr ,x)))



; THE PROOF CHECKER

(defvar *defined-functions-table* nil)

(defun-comp defun-safe-fn (name formals body inlinep)
  (let ((this-defun (list name formals body inlinep))
        (prev-defun (assoc name *defined-functions-table*)))
    (if prev-defun
        (unless (equal this-defun prev-defun)
          (error "Attempted redefinition of ~A.~%
                  Prev: ~A.~%
                  New: ~A~%"
                 name prev-defun this-defun))
      (progn
        (push this-defun *defined-functions-table*)

        (when inlinep
          (eval `(declaim (inline ,name))))

        (eval `(compile (defun ,name ,formals
                          (declare (ignorable ,@formals))
                          ,body)))
        ))))

(defmacro defun-safe (name formals body)
  `(defun-safe-fn ',name ',formals ',body nil))

(defmacro definline-safe (name formals body)
  `(defun-safe-fn ',name ',formals ',body t))


(in-package "MILAWA")

(CL-USER::definline-safe not (x)
 (if x nil t))

(CL-USER::defun-safe rank (x)
  (if (consp x)
      (+ 1
         (+ (rank (car x))
            (rank (cdr x))))
    0))

(CL-USER::defun-safe ord< (x y)
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

(CL-USER::defun-safe ordp (x)
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



; THE PROOF CHECKER - PRELIMINARIES

(CL-USER::definline-safe nfix (x)
  (if (natp x)
      x
    0))

(CL-USER::definline-safe <= (a b)
  (not (< b a)))

(CL-USER::definline-safe zp (x)
  (if (natp x)
      (equal x 0)
    t))

(CL-USER::defun-safe true-listp (x)
  (if (consp x)
      (true-listp (cdr x))
    (equal x nil)))

(CL-USER::defun-safe list-fix (x)
  (if (consp x)
      (cons (car x) (list-fix (cdr x)))
    nil))

(CL-USER::defun-safe len (x)
  (if (consp x)
      (+ 1 (len (cdr x)))
    0))

(CL-USER::defun-safe memberp (a x)
  (if (consp x)
      (or (equal a (car x))
          (memberp a (cdr x)))
    nil))

(CL-USER::defun-safe subsetp (x y)
  (if (consp x)
      (and (memberp (car x) y)
           (subsetp (cdr x) y))
    t))

(CL-USER::defun-safe uniquep (x)
  (if (consp x)
      (and (not (memberp (car x) (cdr x)))
           (uniquep (cdr x)))
    t))

(CL-USER::defun-safe app (x y)
  (if (consp x)
      (cons (car x) (app (cdr x) y))
    (list-fix y)))

(CL-USER::defun-safe rev (x)
  (if (consp x)
      (app (rev (cdr x)) (list (car x)))
    nil))

(CL-USER::defun-safe tuplep (n x)
  (if (zp n)
      (equal x nil)
    (and (consp x)
         (tuplep (- n 1) (cdr x)))))

(CL-USER::defun-safe pair-lists (x y)
  (if (consp x)
      (cons (cons (car x) (car y))
            (pair-lists (cdr x) (cdr y)))
    nil))

(CL-USER::defun-safe lookup (a x)
  (if (consp x)
      (if (equal a (car (car x)))
          (if (consp (car x))
              (car x)
            (cons (car (car x)) (cdr (car x))))
        (lookup a (cdr x)))
    nil))



; THE PROOF CHECKER - TERMS

(CL-USER::definline-safe logic.variablep (x)
  (and (symbolp x)
       (not (equal x t))
       (not (equal x nil))))

(CL-USER::defun-safe logic.variable-listp (x)
  (if (consp x)
      (and (logic.variablep (car x))
           (logic.variable-listp (cdr x)))
    t))

(CL-USER::definline-safe logic.constantp (x)
  (and (tuplep 2 x)
       (equal (first x) 'quote)))

(CL-USER::defun-safe logic.constant-listp (x)
  (if (consp x)
      (and (logic.constantp (car x))
           (logic.constant-listp (cdr x)))
    t))

(CL-USER::definline-safe logic.function-namep (x)
  (and (symbolp x)
       (not (memberp x '(nil quote pequal* pnot*
                         por* first second third
                         fourth fifth and or list
                         cond let let*)))))

(CL-USER::defun-safe logic.flag-term-vars (flag x acc)
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

(CL-USER::definline-safe logic.term-vars (x)
  (logic.flag-term-vars 'term x nil))

(CL-USER::defun-safe logic.flag-termp (flag x)
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

(CL-USER::definline-safe logic.termp (x)
  (logic.flag-termp 'term x))

(CL-USER::definline-safe logic.unquote (x)
  (second x))

(CL-USER::defun-safe logic.unquote-list (x)
  (if (consp x)
      (cons (logic.unquote (car x))
            (logic.unquote-list (cdr x)))
    nil))

(CL-USER::definline-safe logic.functionp (x)
  (logic.function-namep (car x)))

(CL-USER::definline-safe logic.function-name (x)
  (car x))

(CL-USER::definline-safe logic.function-args (x)
  (cdr x))

(CL-USER::definline-safe logic.function (name args)
  (cons name args))

(CL-USER::definline-safe logic.lambdap (x)
  (consp (car x)))

(CL-USER::definline-safe logic.lambda-formals (x)
  (second (car x)))

(CL-USER::definline-safe logic.lambda-body (x)
  (third (car x)))

(CL-USER::definline-safe logic.lambda-actuals (x)
  (cdr x))

(CL-USER::definline-safe logic.lambda (xs b ts)
  (cons (list 'lambda xs b) ts))

(CL-USER::defun-safe logic.flag-term-atblp (flag x atbl)
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

(CL-USER::definline-safe logic.term-atblp (x atbl)
  (logic.flag-term-atblp 'term x atbl))



; THE PROOF CHECKER - FORMULAS

(CL-USER::defun-safe logic.formulap (x)
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

(CL-USER::defun-safe logic.formula-listp (x)
  (if (consp x)
      (and (logic.formulap (car x))
           (logic.formula-listp (cdr x)))
    t))

(CL-USER::definline-safe logic.fmtype (x)
  (first x))

(CL-USER::definline-safe logic.=lhs (x)
  (second x))

(CL-USER::definline-safe logic.=rhs (x)
  (third x))

(CL-USER::definline-safe logic.~arg (x)
  (second x))

(CL-USER::definline-safe logic.vlhs (x)
  (second x))

(CL-USER::definline-safe logic.vrhs (x)
  (third x))

(CL-USER::definline-safe logic.pequal (a b)
  (list 'pequal* a b))

(CL-USER::definline-safe logic.pnot (a)
  (list 'pnot* a))

(CL-USER::definline-safe logic.por (a b)
  (list 'por* a b))

(CL-USER::defun-safe logic.formula-atblp (x atbl)
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

(CL-USER::defun-safe logic.disjoin-formulas (x)
  (if (consp x)
      (if (consp (cdr x))
          (logic.por (car x) (logic.disjoin-formulas (cdr x)))
        (car x))
    nil))



; THE PROOF CHECKER - APPEALS

(CL-USER::defun-safe logic.flag-appealp (flag x)
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

(CL-USER::definline-safe logic.appealp (x)
  (logic.flag-appealp 'proof x))

(CL-USER::definline-safe logic.appeal-listp (x)
  (logic.flag-appealp 'list x))

(CL-USER::definline-safe logic.method (x)
  (first x))

(CL-USER::definline-safe logic.conclusion (x)
  (second x))

(CL-USER::definline-safe logic.subproofs (x)
  (third x))

(CL-USER::definline-safe logic.extras (x)
  (fourth x))

(CL-USER::defun-safe logic.strip-conclusions (x)
  (if (consp x)
      (cons (logic.conclusion (car x))
            (logic.strip-conclusions (cdr x)))
    nil))



; THE PROOF CHECKER - STEP CHECKING

(CL-USER::defun-safe logic.axiom-okp (x axioms atbl)
  (let ((method     (logic.method x))
        (conclusion (logic.conclusion x))
        (subproofs  (logic.subproofs x))
        (extras     (logic.extras x)))
    (and (equal method 'axiom)
         (equal subproofs nil)
         (equal extras nil)
         (memberp conclusion axioms)
         (logic.formula-atblp conclusion atbl))))

(CL-USER::defun-safe logic.theorem-okp (x thms atbl)
  (let ((method     (logic.method x))
        (conclusion (logic.conclusion x))
        (subproofs  (logic.subproofs x))
        (extras     (logic.extras x)))
    (and (equal method 'theorem)
         (equal subproofs nil)
         (equal extras nil)
         (memberp conclusion thms)
         (logic.formula-atblp conclusion atbl))))


; Basic Rules

(CL-USER::defun-safe logic.associativity-okp (x)
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

(CL-USER::defun-safe logic.contraction-okp (x)
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

(CL-USER::defun-safe logic.cut-okp (x)
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

(CL-USER::defun-safe logic.expansion-okp (x atbl)
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

(CL-USER::defun-safe logic.propositional-schema-okp (x atbl)
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

(CL-USER::defun-safe logic.check-functional-axiom (x ti si)
  (if (equal (logic.fmtype x) 'pequal*)
      (and (logic.functionp (logic.=lhs x))
           (logic.functionp (logic.=rhs x))
           (equal (logic.function-name (logic.=lhs x)) (logic.function-name (logic.=rhs x)))
           (equal (logic.function-args (logic.=lhs x)) (rev ti))
           (equal (logic.function-args (logic.=rhs x)) (rev si)))
    (and (equal (logic.fmtype x) 'por*)
         (equal (logic.fmtype (logic.vlhs x)) 'pnot*)
         (equal (logic.fmtype (logic.~arg (logic.vlhs x))) 'pequal*)
         (logic.check-functional-axiom (logic.vrhs x)
                                       (cons (logic.=lhs (logic.~arg (logic.vlhs x))) ti)
                                       (cons (logic.=rhs (logic.~arg (logic.vlhs x))) si)))))

(CL-USER::defun-safe logic.functional-equality-okp (x atbl)
  (let ((method     (logic.method x))
        (conclusion (logic.conclusion x))
        (subproofs  (logic.subproofs x))
        (extras     (logic.extras x)))
    (and (equal method 'functional-equality)
         (equal subproofs nil)
         (equal extras nil)
         (logic.check-functional-axiom conclusion nil nil)
         (logic.formula-atblp conclusion atbl))))


; Beta-Reduction, Instantiation

(CL-USER::defun-safe logic.sigmap (x)
  (if (consp x)
      (and (consp (car x))
           (logic.variablep (car (car x)))
           (logic.termp (cdr (car x)))
           (logic.sigmap (cdr x)))
    t))

(CL-USER::defun-safe logic.sigma-listp (x)
  (if (consp x)
      (and (logic.sigmap (car x))
           (logic.sigma-listp (cdr x)))
    t))

(CL-USER::defun-safe logic.sigma-list-listp (x)
  (if (consp x)
      (and (logic.sigma-listp (car x))
           (logic.sigma-list-listp (cdr x)))
    t))

(CL-USER::defun-safe logic.flag-substitute (flag x sigma)
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
               (logic.function fn (logic.flag-substitute 'list args sigma))))
            ((logic.lambdap x)
             (let ((formals (logic.lambda-formals x))
                   (body    (logic.lambda-body x))
                   (actuals (logic.lambda-actuals x)))
               (logic.lambda formals body (logic.flag-substitute 'list actuals sigma))))
            (t nil))
    (if (consp x)
        (cons (logic.flag-substitute 'term (car x) sigma)
              (logic.flag-substitute 'list (cdr x) sigma))
     nil)))

(CL-USER::definline-safe logic.substitute (x sigma)
  (logic.flag-substitute 'term x sigma))

(CL-USER::definline-safe logic.substitute-list (x sigma)
  (logic.flag-substitute 'list x sigma))

(CL-USER::defun-safe logic.substitute-formula (formula sigma)
  (let ((type (logic.fmtype formula)))
    (cond ((equal type 'por*)
           (logic.por (logic.substitute-formula (logic.vlhs formula) sigma)
                      (logic.substitute-formula (logic.vrhs formula) sigma)))
          ((equal type 'pnot*)
           (logic.pnot (logic.substitute-formula (logic.~arg formula) sigma)))
          ((equal type 'pequal*)
           (logic.pequal (logic.substitute (logic.=lhs formula) sigma)
                         (logic.substitute (logic.=rhs formula) sigma)))
          (t nil))))

(CL-USER::defun-safe logic.instantiation-okp (x atbl)
  (let ((method     (logic.method x))
        (conclusion (logic.conclusion x))
        (subproofs  (logic.subproofs x))
        (extras     (logic.extras x)))
    (and (equal method 'instantiation)
         (logic.sigmap extras)
         (tuplep 1 subproofs)
         (equal (logic.substitute-formula (logic.conclusion (first subproofs)) extras) conclusion)
         (logic.formula-atblp conclusion atbl))))

(CL-USER::defun-safe logic.beta-reduction-okp (x atbl)
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
                  (equal (logic.substitute body (pair-lists formals actuals)) rhs)))))))


; Base Evaluation

(CL-USER::defun-safe logic.initial-arity-table ()
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

(CL-USER::defun-safe logic.base-evaluablep (x)
  (and (logic.functionp x)
       (let ((fn   (logic.function-name x))
             (args (logic.function-args x)))
         (let ((entry (lookup fn (logic.initial-arity-table))))
           (and entry
                (logic.constant-listp args)
                (tuplep (cdr entry) args))))))

(CL-USER::defun-safe logic.base-evaluator (x)
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

(CL-USER::defun-safe logic.base-eval-okp (x atbl)
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


; Induction

(CL-USER::definline-safe logic.make-basis-step (f qs)
  (logic.disjoin-formulas (cons f qs)))

(CL-USER::defun-safe logic.substitute-each-sigma-into-formula (f x)
  (if (consp x)
      (cons (logic.substitute-formula f (car x))
            (logic.substitute-each-sigma-into-formula f (cdr x)))
    nil))

(CL-USER::definline-safe logic.make-induction-step (f q-i sigmas-i)
  (logic.disjoin-formulas
   (cons f (cons (logic.pnot q-i) (logic.substitute-each-sigma-into-formula (logic.pnot f) sigmas-i)))))

(CL-USER::defun-safe logic.make-induction-steps (f qs all-sigmas)
  (if (consp qs)
      (cons (logic.make-induction-step f (car qs) (car all-sigmas))
            (logic.make-induction-steps f (cdr qs) (cdr all-sigmas)))
    nil))

(CL-USER::definline-safe logic.make-ordinal-step (m)
  (logic.pequal (logic.function 'ordp (list m)) ''t))

(CL-USER::definline-safe logic.make-measure-step (m q-i sigma-i-j)
  (logic.por (logic.pnot q-i)
             (logic.pequal (logic.function 'ord< (list (logic.substitute m sigma-i-j) m)) ''t)))

(CL-USER::defun-safe logic.make-measure-steps (m q-i sigmas-i)
  (if (consp sigmas-i)
      (cons (logic.make-measure-step m q-i (car sigmas-i))
            (logic.make-measure-steps m q-i (cdr sigmas-i)))
    nil))

(CL-USER::defun-safe logic.make-all-measure-steps (m qs all-sigmas)
  (if (consp all-sigmas)
      (app (logic.make-measure-steps m (car qs) (car all-sigmas))
           (logic.make-all-measure-steps m (cdr qs) (cdr all-sigmas)))
    nil))

(CL-USER::defun-safe logic.induction-okp (x)
  (let ((method     (logic.method x))
        (conclusion (logic.conclusion x))
        (subproofs  (logic.subproofs x))
        (extras     (logic.extras x)))
    (and (equal method 'induction)
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
                (subsetp (logic.make-induction-steps conclusion qs all-sigmas) subconcs)
                (memberp (logic.make-ordinal-step m) subconcs)
                (subsetp (logic.make-all-measure-steps m qs all-sigmas) subconcs))))))


; Proof Checking

(CL-USER::defun-safe logic.appeal-step-okp (x axioms thms atbl)
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

(CL-USER::defun-safe logic.flag-proofp (flag x axioms thms atbl)
  (if (equal flag 'proof)
      (and (logic.appeal-step-okp x axioms thms atbl)
           (logic.flag-proofp 'list (logic.subproofs x) axioms thms atbl))
    (if (consp x)
        (and (logic.flag-proofp 'proof (car x) axioms thms atbl)
             (logic.flag-proofp 'list (cdr x) axioms thms atbl))
      t)))

(CL-USER::definline-safe logic.proofp (x axioms thms atbl)
  (logic.flag-proofp 'proof x axioms thms atbl))

(CL-USER::defun-safe logic.provable-witness (x axioms thms atbl)
  (CL-USER::error "Called witnessing function ~A.~%"
                  '(logic.provable-witness
                    proof
                    (x axioms thms atbl)
                    (and (logic.appealp proof)
                         (logic.proofp proof axioms thms atbl)
                         (equal (logic.conclusion proof) x)))))

(CL-USER::defun-safe logic.provablep (x axioms thms atbl)
  (let ((proof (logic.provable-witness x axioms thms atbl)))
    (and (logic.appealp proof)
         (logic.proofp proof axioms thms atbl)
         (equal (logic.conclusion proof) x))))



; SUPPORTING ABBREVIATIONS

(CL-USER::defun-safe remove-all (a x)
  (if (consp x)
      (if (equal a (car x))
          (remove-all a (cdr x))
        (cons (car x) (remove-all a (cdr x))))
    nil))

(CL-USER::defun-safe remove-duplicates (x)
  (if (consp x)
      (if (memberp (car x) (cdr x))
          (remove-duplicates (cdr x))
        (cons (car x) (remove-duplicates (cdr x))))
    nil))

(CL-USER::defun-safe difference (x y)
  (if (consp x)
      (if (memberp (car x) y)
          (difference (cdr x) y)
        (cons (car x)
              (difference (cdr x) y)))
    nil))

(CL-USER::defun-safe strip-firsts (x)
  (if (consp x)
      (cons (first (car x))
            (strip-firsts (cdr x)))
      nil))

(CL-USER::defun-safe strip-seconds (x)
  (if (consp x)
      (cons (second (car x))
            (strip-seconds (cdr x)))
    nil))

(CL-USER::defun-safe tuple-listp (n x)
  (if (consp x)
      (and (tuplep n (car x))
           (tuple-listp n (cdr x)))
    t))

(CL-USER::defun-safe sort-symbols-insert (a x)
  (if (consp x)
      (if (symbol-< a (car x))
          (cons a x)
        (cons (car x)
              (sort-symbols-insert a (cdr x))))
    (list a)))

(CL-USER::defun-safe sort-symbols (x)
  (if (consp x)
      (sort-symbols-insert (car x)
                           (sort-symbols (cdr x)))
    nil))

(CL-USER::defun-safe logic.translate-list-term (args)
  (if (consp args)
      (logic.function
       'cons
       (list (car args)
             (logic.translate-list-term (cdr args))))
    ''nil))


(CL-USER::defun-safe logic.translate-and-term (args)
  (if (consp args)
      (if (consp (cdr args))
          (logic.function
           'if
           (list (first args)
                 (logic.translate-and-term (cdr args))
                 ''nil))
        (first args))
    ''t))

(CL-USER::defun-safe logic.translate-or-term (args)

; Difference from my dissertation: optimized this for Magnus's lisp, and had
; to back-port the change.

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

(CL-USER::defun-safe logic.translate-cond-term (tests thens)
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

(CL-USER::defun-safe logic.translate-let-term (vars terms body)
  (let* ((body-vars (remove-duplicates (logic.term-vars body)))
         (id-vars   (sort-symbols (difference body-vars vars)))
         (formals   (app id-vars vars))
         (actuals   (app id-vars terms)))
    (logic.lambda formals body actuals)))

(CL-USER::defun-safe logic.translate-let*-term (vars terms body)
  (if (consp vars)
      (logic.translate-let-term
       (list (car vars))
       (list (car terms))
       (logic.translate-let*-term (cdr vars)
                                  (cdr terms)
                                  body))
    body))

(CL-USER::defun-safe logic.flag-translate (flag x)
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


(CL-USER::definline-safe logic.translate (x)
  (logic.flag-translate 'term x))





; THE HISTORY

(CL-USER::in-package "CL-USER")

(defvar *arity-table* nil)
(defvar *axioms* nil)
(defvar *theorems* nil)

(CL-USER::in-package "MILAWA")

(CL-USER::setf CL-USER::*arity-table*
  (app '((rank . 1)
         (ordp . 1)
         (ord< . 2))
       (logic.initial-arity-table)))

(CL-USER::setf CL-USER::*axioms*
  (app '(;; reflexivity
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




; TERMINATION OBLIGATIONS

(CL-USER::in-package "MILAWA")

(CL-USER::defun-safe cons-onto-ranges (a x)
  (if (consp x)
      (cons (cons (car (car x))
                  (cons a (cdr (car x))))
            (cons-onto-ranges a (cdr x)))
    nil))

(CL-USER::defun-safe logic.substitute-callmap (x sigma)
  (if (consp x)
      (let ((actuals (car (car x)))
            (rulers  (cdr (car x))))
        (cons (cons (logic.substitute-list actuals sigma)
                    (logic.substitute-list rulers sigma))
              (logic.substitute-callmap (cdr x) sigma)))
    nil))

(CL-USER::defun-safe logic.flag-callmap (flag f x)
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

(CL-USER::definline-safe logic.callmap (f x)
  (logic.flag-callmap 'term f x))

(CL-USER::defun-safe repeat (a n)
  (if (zp n)
      nil
    (cons a (repeat a (- n 1)))))

(CL-USER::defun-safe logic.pequal-list (x y)
  (if (and (consp x)
           (consp y))
      (cons (logic.pequal (car x) (car y))
            (logic.pequal-list (cdr x) (cdr y)))
    nil))

(CL-USER::defun-safe logic.progress-obligation (measure formals actuals rulers)
  (let* ((sigma    (pair-lists formals actuals))
         (m/sigma  (logic.substitute measure sigma))
         (ord-term (logic.function 'ord< (list m/sigma measure))))
    (logic.disjoin-formulas
     (cons (logic.pequal ord-term ''t)
           (logic.pequal-list rulers (repeat ''nil (len rulers)))))))

(CL-USER::defun-safe logic.progress-obligations (measure formals callmap)
  (if (consp callmap)
      (let* ((entry   (car callmap))
             (actuals (car entry))
             (rulers  (cdr entry)))
        (cons (logic.progress-obligation measure formals actuals rulers)
              (logic.progress-obligations measure formals (cdr callmap))))
    nil))

(CL-USER::defun-safe logic.termination-obligations (name formals body measure)
   (let ((callmap (logic.callmap name body)))
     (if callmap
         (cons (logic.pequal (logic.function 'ordp (list measure)) ''t)
               (logic.progress-obligations measure formals callmap))
       nil)))



; ESTABLISHING PROVABILITY

(CL-USER::in-package "CL-USER")

(defvar *proof-checker* 'MILAWA::logic.proofp)

(defun-comp check-proof (x axioms thms atbl)
  (funcall *proof-checker* x axioms thms atbl))

(defun-comp check-proof-list (x axioms thms atbl)
  (if (consp x)
      (and (check-proof (car x) axioms thms atbl)
           (check-proof-list (cdr x) axioms thms atbl))
    t))

(CL-USER::in-package "MILAWA")

(CL-USER::defun-safe logic.fidelity-claim (name)
  (logic.por
   '(pequal* (logic.appealp x) 'nil)
   (logic.por
    (logic.pequal (logic.function name '(x axioms thms atbl))
                  ''nil)
    '(pnot* (pequal* (logic.provablep (logic.conclusion x)
                                      axioms thms atbl)
                     'nil)))))

(CL-USER::in-package "CL-USER")

(defun-comp switch-proof-checker (name)
  (unless (MILAWA::logic.function-namep name)
    (error "The name is invalid"))
  (unless (MILAWA::memberp (MILAWA::logic.fidelity-claim name)
                           *theorems*)
    (error "The fidelity claim has not been proven"))
  (setf *proof-checker* name)
  t)




; READING OBJECTS

(CL-USER::in-package "CL-USER")

(defmacro report-time (message form)
  `(let* ((start-time (get-internal-real-time))
          (value      ,form)
          (stop-time  (get-internal-real-time))
          (elapsed    (/ (coerce (- stop-time start-time) 'float)
                         internal-time-units-per-second)))
     (format t ";; ~A took ~$ seconds~%" ,message elapsed)
     value))

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
  (report-time "Reading the file"
    (let* ((*milawa-abbreviations-hash-table* (make-hash-table
                                               :size 10000
                                               :rehash-size 100000
                                               :test 'eql))
           (*readtable* *milawa-readtable*)
           (*package* milawa-package)
           (stream (open filename
                         :direction :input
                         :if-does-not-exist :error))
           (contents (milawa-read-file-aux stream)))
      (close stream)
      (if (acceptable-objectp contents)
          contents
        (error "unacceptable object encountered")))))





; EVENTS

(defun-comp admit-theorem (formula filename)
  (unless (MILAWA::logic.formulap formula)
    (error "The conclusion, ~A, is not a formula" formula))
  (unless (MILAWA::logic.formula-atblp formula *arity-table*)
    (error "The conclusion, ~A, is not well-formed" formula))
  #-skip
  (let ((proof (car (milawa-read-file filename))))
    (unless (MILAWA::logic.appealp proof)
      (error "The proof is not a valid appeal"))
    (unless (equal (MILAWA::logic.conclusion proof) formula)
      (error "The proof does not have the right conclusion"))
    (unless (report-time "Checking the proof"
                         (check-proof proof *axioms* *theorems* *arity-table*))
      (error "The proof was rejected")))
  (unless (MILAWA::memberp formula *theorems*)
    (push formula *theorems*))
  t)

(defun-comp admit-defun (name formals raw-body raw-measure inlinep filename)
  (let* ((body      (MILAWA::logic.translate raw-body))
         (measure   (MILAWA::logic.translate raw-measure))
         (arity     (MILAWA::len formals))
         (new-atbl  (cons (cons name arity) *arity-table*)))
    (unless (MILAWA::logic.function-namep name)
      (error "The name is invalid"))
    (unless (MILAWA::logic.variable-listp formals)
      (error "The formals are not variables"))
    (unless (MILAWA::uniquep formals)
      (error "The formals are not unique"))
    (unless (MILAWA::logic.termp body)
      (error "The body did not translate to a term"))
    (unless (MILAWA::logic.termp measure)
      (error "The measure did not translate to a term"))
    (unless (MILAWA::subsetp (MILAWA::logic.term-vars body) formals)
      (error "The body mentions variables besides the formals"))
    (unless (MILAWA::subsetp (MILAWA::logic.term-vars measure) formals)
      (error "The measure mentions variables besides the formals"))
    (unless (MILAWA::logic.term-atblp body new-atbl)
      (error "The body is not well-formed"))
    (unless (MILAWA::logic.term-atblp measure new-atbl)
      (error "The measure is not well-formed"))
    #-skip
    (let ((obligations (MILAWA::logic.termination-obligations
                        name formals body measure))
          (proofs (car (milawa-read-file filename))))
      (unless (MILAWA::logic.appeal-listp proofs)
        (error "The proofs are not a list of appeals"))
      (unless (equal (MILAWA::logic.strip-conclusions proofs) obligations)
        (error "The proofs have the wrong conclusions"))
      (unless (report-time "Checking the proofs"
                           (check-proof-list proofs *axioms* *theorems* new-atbl))
        (error "A proof was rejected")))
    (defun-safe-fn name formals raw-body inlinep)
    (unless (MILAWA::lookup name *arity-table*)
      (push (cons name arity) *arity-table*))
    (let ((new-axiom (MILAWA::logic.pequal (MILAWA::logic.function name formals)
                                           body)))
      (unless (MILAWA::memberp new-axiom *axioms*)
        (push new-axiom *axioms*))))
  t)

(defun-comp admit-witness (name bound-var free-vars raw-body)
  (let* ((body     (MILAWA::logic.translate raw-body))
         (all-vars (cons bound-var free-vars)))
    (unless (MILAWA::logic.function-namep name)
      (error "Invalid function name"))
    (unless (MILAWA::logic.variablep bound-var)
      (error "The bound-var is not a variable"))
    (unless (MILAWA::logic.variable-listp free-vars)
      (error "The free-vars are not variables"))
    (unless (MILAWA::uniquep (cons bound-var free-vars))
      (error "The variables are not unique"))
    (unless (MILAWA::logic.termp body)
      (error "The body did not translate to a term"))
    (unless (MILAWA::subsetp (MILAWA::logic.term-vars body) all-vars)
      (error "The body's variables are not legal"))
    (unless (MILAWA::logic.term-atblp body *arity-table*)
      (error "The body is not well-formed"))
    (defun-safe-fn name free-vars
      `(CL-USER::error "Called witnessing function ~A.~%"
                       '(,name ,bound-var ,free-vars ,raw-body))
      nil)
    (unless (MILAWA::lookup name *arity-table*)
      (push (cons name (MILAWA::len free-vars)) *arity-table*))
    (let ((new-axiom
           (MILAWA::logic.por
            (MILAWA::logic.pequal body ''nil)
            (MILAWA::logic.pnot
             (MILAWA::logic.pequal
              (MILAWA::logic.lambda
               all-vars body
               (cons (MILAWA::logic.function name free-vars)
                     free-vars))
              ''nil)))))
      (unless (MILAWA::memberp new-axiom *axioms*)
        (push new-axiom *axioms*))))
  t)


; CHECKPOINTING

(defun-comp save-and-exit (filename)

  #+allegro
  (progn
    (setq EXCL::*restart-init-function* 'main)
    (EXCL::dumplisp :name (concatenate 'string filename "." image-extension))
    (quit))

  #+clozure
  (CCL::save-application (concatenate 'string filename "." image-extension)
                         :toplevel-function #'main
                         :purify t)

  #+clisp
  (progn
    (EXT:saveinitmem (concatenate 'string filename "." image-extension)
                     :init-function #'main)
    (quit))

  #+cmu
  (EXTENSIONS::save-lisp (concatenate 'string filename "." image-extension)
                         :init-function #'main
                         :purify t
                         )

  #+sbcl
  (SB-EXT:save-lisp-and-die (concatenate 'string filename "." image-extension)
                            :toplevel #'main
                            :purify t)

  #+scl
  (ext:save-lisp (concatenate 'string filename "." image-extension)
                 :init-function #'main
                 :gc :full
                 :purify t)

  ;; handler for other lisps
  (error "implement save-and-exit on this lisp"))


; THE COMMAND LOOP

(defun-comp safe-tuplep (n x)
  (if (= n 0)
      (not x)
    (and (consp x)
         (safe-tuplep (- n 1) (cdr x)))))

(defvar *event-number* 1)

(defun-comp try-to-accept-command (cmd)
  (cond ((not (consp cmd))
         (error "Invalid command ~A.~%" cmd))

        ((eq (car cmd) 'MILAWA::verify)
         (unless (and (safe-tuplep 4 cmd)
                      (let ((name     (second cmd))
                            (formula  (third cmd))
                            (filename (fourth cmd)))
                        (format t "~A> VERIFY ~A~%" *event-number* name)
                        (report-time "VERIFY"
                                     (and (acceptable-objectp name)
                                          (acceptable-objectp formula)
                                          (stringp filename)
                                          (admit-theorem formula filename)))))
           (error "Invalid VERIFY: ~A" cmd)))

        ((eq (car cmd) 'MILAWA::DEFINE)
         (unless (and (safe-tuplep 7 cmd)
                      (let ((name     (second cmd))
                            (formals  (third cmd))
                            (body     (fourth cmd))
                            (measure  (fifth cmd))
                            (inlinep  (sixth cmd))
                            (filename (seventh cmd)))
                        (format t "~A> DEFINE ~A~%" *event-number* name)
                        (report-time "DEFINE"
                                     (and (acceptable-objectp name)
                                          (acceptable-objectp formals)
                                          (acceptable-objectp body)
                                          (acceptable-objectp measure)
                                          (stringp filename)
                                          (admit-defun name formals body measure inlinep filename)))))
           (error "Invalid DEFINE: ~A" cmd)))

        ((eq (car cmd) 'MILAWA::SKOLEM)
         (unless (and (safe-tuplep 5 cmd)
                      (let ((name      (second cmd))
                            (bound-var (third cmd))
                            (free-vars (fourth cmd))
                            (body      (fifth cmd)))
                        (format t "~A> SKOLEM ~A~%" *event-number* name)
                        (report-time "SKOLEM"
                                     (and (acceptable-objectp name)
                                          (acceptable-objectp bound-var)
                                          (acceptable-objectp free-vars)
                                          (acceptable-objectp body)
                                          (admit-witness name bound-var free-vars body)))))
           (error "Invalid SKOLEM: ~A" cmd)))

        ((eq (car cmd) 'MILAWA::SWITCH)
         (unless (and (safe-tuplep 2 cmd)
                      (let ((name (second cmd)))
                        (format t "~A > SWITCH ~A~%" *event-number* name)
                        (report-time "SWITCH"
                                     (switch-proof-checker name))))
           (error "Invalid SWITCH: ~A" cmd)))

        ((eq (car cmd) 'MILAWA::FINISH)
         (unless (and (safe-tuplep 2 cmd)
                      (let ((filename (second cmd)))
                        (format t "~A > FINISH ~A~%" *event-number* filename)
                        (and (stringp filename)
                             (save-and-exit filename))))
           (error "Invalid FINISH: ~A" cmd)))

        (t
         (error "Invalid command: ~A" cmd))))

(defun-comp try-to-accept-all-commands ()
  (let* ((*package* milawa-package)
         (cmd       (read *standard-input* nil unique-cons-for-eof)))
    (when (eq cmd unique-cons-for-eof)
      (format t "All commands have been accepted.~%")
      (quit))
    (try-to-accept-command cmd)
    (incf *event-number*))

  ;; CMUCL does not like to tail-call optimize when a special has been bound,
  ;; so keep this tail call outside of the let binding for *package*.

  ;; Apparently Allegro does the same?
  (try-to-accept-all-commands))

(defun-comp main ()
  (format t "Milawa Proof Checker.~%")

  #+allegro
  (SYSTEM::set-stack-cushion nil)

  (try-to-accept-all-commands))

(save-and-exit "base")



