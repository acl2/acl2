; A tool to make an axe-syntaxp evaluator for given functions
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

(include-book "std/util/bstar" :dir :system)
(include-book "kestrel/alists-light/acons-unique" :dir :system)
(include-book "kestrel/utilities/world" :dir :system)
(include-book "kestrel/alists-light/lookup" :dir :system)
(include-book "kestrel/utilities/pack" :dir :system)
(include-book "kestrel/utilities/vars-in-term" :dir :system)
(include-book "axe-syntax-functions") ;for axe-quotep, since we treat it specially here
(include-book "axe-rules") ;for LIST-OF-VARIABLES-AND-CONSTANTSP, todo: reduce?
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))

(local (in-theory (disable myquotep)))

;name clash with std
;move
(local
 (defthm symbol-listp-of-take-alt
   (implies (symbol-listp x)
            (symbol-listp (take n x)))))

(defthm integer-listp-of-strip-cars-of-acons-unique
  (implies (and (integer-listp (strip-cars alist))
                (integerp key))
           (integer-listp (strip-cars (acons-unique key val alist))))
  :hints (("Goal" :in-theory (enable acons-unique INTEGER-LISTP))))

(defthm symbol-list-listp-of-strip-cars-of-acons-unique
  (implies (and (symbol-list-listp (strip-cdrs alist))
                (symbol-listp val))
           (symbol-list-listp (strip-cdrs (acons-unique key val alist))))
  :hints (("Goal" :in-theory (enable acons-unique))))

(defthmd rational-listp-when-integer-listp
  (implies (integer-listp x)
           (rational-listp x)))

(local (in-theory (enable rational-listp-when-integer-listp)))

(defthm dargp-of-lookup-equal
  (implies (and (all-dargp (strip-cdrs alist))
                (assoc-equal key alist))
           (dargp (lookup-equal key alist))))

;todo, move and combine?
(defthmd assoc-equal-iff-two
  (implies (alistp alist)
           (iff (assoc-equal key alist)
                (member-equal key (strip-cars alist))))
  :hints (("Goal" :in-theory (enable assoc-equal member-equal))))

;(local (in-theory (enable assoc-equal-iff)))

(defthmd vars-in-terms-opener
  (implies (consp terms)
           (equal (vars-in-terms terms)
                  (union-equal (vars-in-term (first terms))
                               (vars-in-terms (rest terms)))))
  :hints (("Goal" :in-theory (enable vars-in-terms))))

;; Here, the arities exclude the final dag-array formal, if present.  This
;; arity thus corresponds to the number of args stored for the call in the
;; axe-syntaxp hyp.
(defund bind-fns-to-arities (fns wrld acc)
  (declare (xargs :guard (and (symbol-listp fns)
                              (plist-worldp wrld)
                              (alistp acc))))
  (if (endp fns)
      acc
    (let* ((fn (first fns))
           (arity (fn-arity fn wrld))
           (formals (fn-formals fn wrld))
           (fn-uses-dagp (and (consp formals)
                              (equal 'dag-array (car (last formals)))))
           (arity (if fn-uses-dagp
                      (+ -1 arity)
                    arity))
           (fns-with-arity (lookup arity acc)))
      (bind-fns-to-arities (rest fns)
                           wrld
                           (acons-unique arity (cons fn fns-with-arity) acc)))))

(defthm alistp-of-bind-fns-to-arities
  (implies (alistp acc)
           (alistp (bind-fns-to-arities fns wrld acc)))
  :hints (("Goal" :in-theory (enable bind-fns-to-arities))))

(defthm integer-listp-of-strip-cars-of-bind-fns-to-arities
  (implies (integer-listp (strip-cars acc))
           (integer-listp (strip-cars (bind-fns-to-arities fns wrld acc))))
  :hints (("Goal" :in-theory (enable bind-fns-to-arities))))

(defthmd symbol-listp-of-lookup-equal
  (implies (symbol-list-listp (strip-cdrs alist))
           (symbol-listp (lookup-equal key alist)))
  :hints (("Goal" :in-theory (enable lookup-equal))))

(local (in-theory (enable symbol-listp-of-lookup-equal)))

(defthm symbol-list-listp-of-strip-cdrs-of-bind-fns-to-arities
  (implies (and (symbol-list-listp (strip-cdrs acc))
                (symbol-listp fns))
           (symbol-list-listp (strip-cdrs (bind-fns-to-arities fns wrld acc))))
  :hints (("Goal" :in-theory (enable bind-fns-to-arities))))

(defund make-axe-syntaxp-evaluator-args (formals num)
  (declare (xargs :guard (and (symbol-listp formals)
                              (natp num))))
  (if (endp formals)
      nil
    (cons (let ((formal (first formals)))
            (if (eq 'dag-array formal)
                'dag-array ;todo: error?
              (let ((arg (pack$ 'arg num)))
                `(if (consp ,arg)
                     ,arg ;; (unquote ,arg)
                   ;; arg is a variable, so look it up:
                   (lookup-eq ,arg alist)))))
          (make-axe-syntaxp-evaluator-args (rest formals) (+ 1 num)))))

(defund make-axe-syntaxp-evaluator-case-for-arity-aux (arity fns wrld)
  (declare (xargs :guard (and (symbol-listp fns)
                              (natp arity)
                              (plist-worldp wrld))))
  (if (endp fns)
      nil
    (let* ((fn (first fns))
           (formals (fn-formals fn wrld))
           (fn-uses-dagp (and (consp formals)
                              (equal 'dag-array (car (last formals)))))
           (non-dag-array-formals (if fn-uses-dagp
                                      (butlast formals 1)
                                    formals))
           (dag-array-formals (if fn-uses-dagp '(dag-array) nil)))
      (cons ;the entry for FN in a case expression:
       `(,fn (,fn ,@(make-axe-syntaxp-evaluator-args non-dag-array-formals 0) ,@dag-array-formals))
       (make-axe-syntaxp-evaluator-case-for-arity-aux arity (rest fns) wrld)))))

(defund make-axe-syntaxp-evaluator-case-for-arity (arity fns eval-axe-syntaxp-function-application-fn wrld)
  (declare (xargs :guard (and (symbol-listp fns)
                              (natp arity)
                              (plist-worldp wrld))))
  (if fns
      `(case fn
         ,@(make-axe-syntaxp-evaluator-case-for-arity-aux arity fns wrld)
         (t (er hard? ',eval-axe-syntaxp-function-application-fn "Unrecognized function in axe-syntaxp rule: ~x0." fn)))
    ;; no fns of this arity:
    `(er hard? ',eval-axe-syntaxp-function-application-fn "Unrecognized function in axe-syntaxp rule: ~x0." fn)))

;; args up through arity-1 are bound to vars arg0 ... arg(arity-1) in the overarching term
(defund make-axe-syntaxp-evaluator-cases (current-arity max-arity arity-alist eval-axe-syntaxp-function-application-fn wrld)
  (declare (xargs :guard (and (natp current-arity)
                              (integerp max-arity)
                              (alistp arity-alist)
                              (symbol-list-listp (strip-cdrs arity-alist))
                              (plist-worldp wrld))
                  :measure (nfix (+ 1 (- max-arity current-arity)))))
  (if (or (not (mbt (natp current-arity)))
          (not (mbt (integerp max-arity)))
          (< max-arity current-arity))
      `(er hard? ',eval-axe-syntaxp-function-application-fn "Unrecognized function in axe-syntaxp rule: ~x0." fn)
    `(if (atom args)
         ,(make-axe-syntaxp-evaluator-case-for-arity current-arity (lookup current-arity arity-alist) eval-axe-syntaxp-function-application-fn wrld)
       (let* ((,(pack$ 'arg current-arity) (first args)) ;bind the next arg
              (args (rest args)))
         (declare (ignorable args ,(pack$ 'arg current-arity)))
         ,(make-axe-syntaxp-evaluator-cases (+ 1 current-arity) max-arity arity-alist eval-axe-syntaxp-function-application-fn wrld)))))

(defund max-val (vals current-max)
  (declare (xargs :guard (and (rational-listp vals)
                              (rationalp current-max))))
  (if (endp vals)
      current-max
    (max-val (rest vals) (max (first vals) current-max))))

(defthm integerp-of-max-val
  (implies (and (integerp current-max)
                (integer-listp vals))
           (integerp (max-val vals current-max)))
  :hints (("Goal" :in-theory (enable integer-listp max-val))))

(defthmd natp-of-lookup-equal-when-all-dargp-of-strip-cdrs-when-member-equal
  (implies (and (all-dargp (strip-cdrs alist))
                (member-equal key (strip-cars alist)))
           (equal (natp (lookup-equal key alist))
                  (not (myquotep (lookup-equal key alist))))))

(defthmd not-<-of-largest-non-quotep-of-strip-cdrs-and-lookup-equal-when-member-equal
  (implies (and (member-equal key (strip-cars alist))
                (all-dargp (strip-cdrs alist))
                (natp (lookup-equal key alist)))
           (not (< (largest-non-quotep (strip-cdrs alist))
                   (lookup-equal key alist))))
  :hints (("Goal" :in-theory (enable lookup-equal assoc-equal strip-cars largest-non-quotep))))

(defund make-axe-syntaxp-evaluator-fn (suffix fns wrld)
  (declare (xargs :guard (and (symbolp suffix)
                              (symbol-listp fns)
                              (plist-worldp wrld))))
  (b* ((eval-axe-syntaxp-function-application-fn (pack$ 'eval-axe-syntaxp-function-application- suffix))
       (eval-axe-syntaxp-expr-fn (pack$ 'eval-axe-syntaxp-expr- suffix))
       (arity-alist (bind-fns-to-arities fns wrld nil))
       (arity-0-fns (lookup 0 arity-alist))
       (arity-1-fns (lookup 1 arity-alist))
       (arities (strip-cars arity-alist))
       (max-arity (max-val arities -1)))
    `(encapsulate ()
       (local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))
       (local (include-book "kestrel/lists-light/union-equal" :dir :system))
       (local (include-book "kestrel/arithmetic-light/plus" :dir :system))
       (local (include-book "kestrel/lists-light/len" :dir :system))

       (local (in-theory (enable assoc-equal-iff-two
                                 natp-of-lookup-equal-when-all-dargp-of-strip-cdrs-when-member-equal
                                 not-<-of-largest-non-quotep-of-strip-cdrs-and-lookup-equal-when-member-equal
                                 natp-of-+-of-1)))
       (local (in-theory (disable myquotep
                                  natp
                                  ;; prevent induction:
                                  strip-cdrs
                                  strip-cars
                                  symbol-alistp
                                  alistp)))

       (defund ,eval-axe-syntaxp-function-application-fn (fn args alist dag-array)
         (declare (xargs :guard (and (symbolp fn)
                                     (list-of-variables-and-constantsp args)
                                     (symbol-alistp alist)
                                     (all-dargp (strip-cdrs alist))
                                     (subsetp-eq (vars-in-terms args) (strip-cars alist))
                                     ;; special treatment to optimize handling of axe-quotep:
                                     (implies (eq fn 'axe-quotep) (variablep (first args)))
                                     (pseudo-dag-arrayp 'dag-array dag-array (+ 1 (largest-non-quotep (strip-cdrs alist)))))
                         :guard-hints (("Goal" :in-theory (e/d (list-of-variables-and-constantsp
                                                                vars-in-terms-opener)
                                                               (dargp))
                                        :expand ((vars-in-terms args)
                                                 (vars-in-term (car args))))))
                  (ignorable dag-array))
         (if (atom args)
             ;; arity 0 case:
             ,(make-axe-syntaxp-evaluator-case-for-arity 0 arity-0-fns eval-axe-syntaxp-function-application-fn wrld)
           (let ((arg0 (first args))
                 (args (rest args)))
             (if (atom args)
                 ;; arity 1 case:
                 (case fn
                   ;; Axe-quotep is built into all axe-evaluators
                   (axe-quotep (axe-quotep
                                ;; arg0 is a variable (we check this only for axe-quotep), so look it up:
                                (lookup-eq arg0 alist)))
                   ,@(make-axe-syntaxp-evaluator-case-for-arity-aux 1 arity-1-fns wrld))
               (let ((arg1 (first args))
                     (args (rest args)))
                 (declare (ignorable args arg1))
                 ,(make-axe-syntaxp-evaluator-cases 2 max-arity arity-alist eval-axe-syntaxp-function-application-fn wrld))))))

       ;; todo: also make a version that takes the dag-array, or perhaps always pass it?
       (defund ,eval-axe-syntaxp-expr-fn (expr alist dag-array)
         (declare (xargs :guard (and (pseudo-termp expr)
                                     (axe-syntaxp-exprp expr)
                                     (symbol-alistp alist)
                                     (all-dargp (strip-cdrs alist))
                                     (subsetp-eq (vars-in-term expr) (strip-cars alist))
                                     (pseudo-dag-arrayp 'dag-array dag-array (+ 1 (largest-non-quotep (strip-cdrs alist)))))
                         :guard-hints (("Goal" :in-theory (enable vars-in-term axe-syntaxp-exprp axe-syntaxp-function-applicationp)
                                        :expand (axe-syntaxp-exprp expr)
                                        :do-not '(generalize eliminate-destructors)))))
         (let ((fn (ffn-symb expr)))
           (case fn
             (quote (unquote expr))
             (if (if (,eval-axe-syntaxp-expr-fn (farg1 expr) alist dag-array)
                     (,eval-axe-syntaxp-expr-fn (farg2 expr) alist dag-array)
                   (,eval-axe-syntaxp-expr-fn (farg3 expr) alist dag-array)))
             (not (not (,eval-axe-syntaxp-expr-fn (farg1 expr) alist dag-array)))
             (t (,eval-axe-syntaxp-function-application-fn fn (fargs expr) alist dag-array))))))))

(defmacro make-axe-syntaxp-evaluator (suffix fns)
  `(make-event (make-axe-syntaxp-evaluator-fn ,suffix ,fns (w state))))
