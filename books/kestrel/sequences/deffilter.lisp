; Tool to generate a function that filters a list.
;
; Copyright (C) 2014-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Main Author: Stephen Westfold (westfold@kestrel.edu)
; Contributing Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: Initial Working Version

;; See tests in deffilter-tests.lisp

(include-book "generics-utilities")
(include-book "defforall") ;since we call generic-forall below
(include-book "defexists") ;since we call generic-exists below
(include-book "subsequencep-equal")
;(include-book "kestrel/lists-light/reverse-list" :dir :system) ;todo
(local (include-book "kestrel/lists-light/memberp" :dir :system))
(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/reverse-list" :dir :system))

(defthmd deffilter-helper-reverse-list-of-cons
  (equal (reverse-list (cons a x))
         (append (reverse-list x) (list a)))
  :hints (("Goal" :by reverse-list-of-cons)))

(defthm deffilter-helper-append-associative
  (equal (append (append x y) z)
         (append x y z))
  :hints (("Goal" :in-theory (enable append))))
;
;This deffilter utility can help you define a function that takes a
;list and returns only those elements that satisfy a given predicate.
;You also get many theorems for free about such a function.

;This book also represents an experiment with slightly new syntax for generics.

;TODO: think about guards, use of MBE and reverse with an efficient tail-recursive version, etc.
;maybe an option to not reverse the result, when the order doesn't matter

;; TODO: Are all the theorems about the generic functions used?

;(local (include-book "coi/lists/memberp" :dir :system))

;move
;dup
(defthm memberp-of-reverse-list
  (equal (memberp a (reverse-list lst))
         (memberp a lst))
  :hints (("Goal" :in-theory (enable reverse-list))))

;move
(defthm subsetp-equal-of-reverse-list-arg1
  (equal (subsetp-equal (reverse-list x) y)
         (subsetp-equal x y))
  :hints (("Goal" :in-theory (enable subsetp-equal reverse-list))))

;move
(defthm subsetp-equal-of-reverse-list-arg2
  (equal (subsetp-equal x (reverse-list y))
         (subsetp-equal x y))
  :hints (("Goal" :in-theory (enable subsetp-equal reverse-list))))

(defund generic-filter (vals)
  (if (atom vals)
      nil ;empty-list
    (if (generic-predicate (first vals))
        (cons (first vals)
              (generic-filter (rest vals)))
      (generic-filter (rest vals)))))

(defthm subsetp-equal-of-generic-filter
  (subsetp-equal (generic-filter vals) vals)
  :hints (("Goal" :in-theory (enable generic-filter))))

(defthm generic-forall-of-generic-filter
  (generic-forall (generic-filter vals))
  :hints (("Goal" :in-theory (enable generic-filter))))

(defthm generic-filter-generic-forall-id
  (implies (and (true-listp vals)
                (generic-forall vals))
           (equal (generic-filter vals)
                  vals))
  :hints (("Goal" :in-theory (enable generic-filter))))

(defthm not-generic-exists-generic-filter
  (implies (not (generic-exists vals))
           (equal (generic-filter vals)
                  nil))
  :hints (("Goal" :in-theory (enable generic-filter))))

(defthm generic-filter-subsequencep-equal
  (subsequencep-equal (generic-filter vals) vals)
  :hints (("Goal" :in-theory (enable generic-filter))))

(defthm generic-filter-idempotent
  (equal (generic-filter (generic-filter vals))
         (generic-filter vals))
  :hints (("Goal" :in-theory (enable generic-filter))))

(defthm generic-filter-of-cons
  (equal (generic-filter (cons a x))
         (if (generic-predicate a)
             (cons a (generic-filter x))
           (generic-filter x)))
  :hints (("Goal" :in-theory (enable generic-filter))))

(defthm generic-filter-of-append
  (equal (generic-filter (append x y))
         (append (generic-filter x)
                 (generic-filter y)))
  :hints (("Goal" :in-theory (enable generic-filter))))

(defthm generic-filter-of-revappend
  (equal (generic-filter (revappend x y))
         (revappend (generic-filter x)
                    (generic-filter y)))
  :hints (("Goal" :in-theory (enable generic-filter revappend))))

(defthm generic-filter-of-true-list-fix
  (equal (generic-filter (true-list-fix x))
         (generic-filter x))
  :hints (("Goal" :in-theory (enable generic-filter))))

(defthm generic-filter-of-reverse-list
  (equal (generic-filter (reverse-list x))
         (reverse-list (generic-filter x)))
  :hints (("Goal" :in-theory (enable generic-filter reverse-list))))

(defthm generic-filter-when-not-consp
  (implies (not (consp x))
           (equal (generic-filter x)
                  nil))
  :hints (("Goal" :in-theory (enable generic-filter))))

(defthm generic-filter-of-nil
  (equal (generic-filter nil)
         nil)
  :hints (("Goal" :in-theory (enable generic-filter))))

;used for the use-XXX theorem below
(defthm generic-predicate-when-generic-filter
  (implies (memberp x (generic-filter free))
           (generic-predicate x))
  :hints (("Goal" :in-theory (enable memberp generic-filter))))

(defthm generic-filter-of-remove1
  (equal (generic-filter (remove1-equal a x))
         (if (generic-predicate a)
             (remove1-equal a (generic-filter x))
           (generic-filter x)))
  :hints (("Goal" :in-theory (enable generic-filter))))

(defthm generic-filter-of-remove-equal
  (equal (generic-filter (remove-equal a x))
         (if (generic-predicate a)
             (remove-equal a (generic-filter x))
           (generic-filter x)))
  :hints (("Goal" :in-theory (enable generic-filter))))

;; This version reverses the accumulator at the end.
(defund generic-filter-tail-aux (vals acc)
  (if (atom vals)
      (reverse-list acc)
    (if (generic-predicate (first vals))
        (generic-filter-tail-aux (rest vals) (cons (first vals) acc))
      (generic-filter-tail-aux (rest vals) acc))))

;(local (include-book "list-sets2"))

(defthm generic-filter-tail-aux-rewrite
  (equal (generic-filter-tail-aux vals acc)
         (append (reverse-list acc) (generic-filter vals)))
  :hints (("Goal" :in-theory (enable generic-filter-tail-aux generic-filter reverse))))

(defthm subsetp-equal-of-generic-filter-tail-aux
  (subsetp-equal (generic-filter-tail-aux vals acc)
                 (append vals acc)))

;; Tail recursive function equal to generic-filter
(defund generic-filter-tail (vals)
  (generic-filter-tail-aux vals nil))

(defthm subsetp-equal-of-generic-filter-tail
  (subsetp-equal (generic-filter-tail vals)
                 vals)
  :hints (("Goal" :use (:instance generic-filter-tail-aux-rewrite (acc nil))
           :in-theory (e/d (generic-filter generic-filter-tail)
                           (generic-filter-tail-aux-rewrite)))))

(defthm generic-filter-tail-rewrite
  (equal (generic-filter-tail vals)
         (generic-filter vals))
  :hints (("Goal" :in-theory (enable generic-filter-tail))))

;; This version does not reverse the accumulator at the end.
(defund generic-filter-tail-no-rev-aux (vals acc)
  (if (atom vals)
      acc
    (if (generic-predicate (first vals))
        (generic-filter-tail-no-rev-aux (rest vals) (cons (first vals) acc))
      (generic-filter-tail-no-rev-aux (rest vals) acc))))

(defthm generic-filter-tail-no-rev-aux-rewrite
  (equal (generic-filter-tail-no-rev-aux vals acc)
         (append (reverse-list (generic-filter vals)) acc))
  :hints (("Goal" :in-theory (enable generic-filter-tail-no-rev-aux generic-filter))))

;; Tail recursive function equal to generic-filter except we don't reverse the
;; accumulator, so the result is in reverse order.
(defund generic-filter-tail-no-rev (vals)
  (generic-filter-tail-no-rev-aux vals nil))

(defthm generic-filter-tail-no-rev-rewrite
  (equal (generic-filter-tail-no-rev vals)
         (reverse-list (generic-filter vals)))
  :hints (("Goal" :in-theory (enable generic-filter-tail-no-rev))))

;; TODO: Improve the macro to put in these tail-rec functions


;You can give an n-place predicate if the filter function being defined takes n args:
;the macro/make-event should go get the guard of the given predicate, and make an all-XXX function to use as the guard of the deffilter:
;(local (deffilter keep-nats (xs) natp))

;You can give an n-place lambda if the filter function being defined takes n args:
;(local (deffilter keep-nats (xs) (lambda (x) (natp x))))

(defun deffilter-fn (filter-fn-name all-formals term fixed declares guard forall-fn exists-fn tail-rec tail-rec-no-rev verbose)
  (declare (xargs :guard (and (symbolp filter-fn-name)
                              (symbol-listp all-formals)
                              ;; term
                              (or (symbolp fixed)
                                  (symbol-listp fixed))
                              ;; declares
                              (symbolp forall-fn)
                              (symbolp exists-fn)
                              (booleanp tail-rec)
                              (booleanp tail-rec-no-rev)
                              )
                  :verify-guards nil ;todo
                  ))
  (b* ((declares (if guard (cons `(xargs :guard ,guard) declares) declares)) ;i guess this excludes a guard of nil....
       (fixed-formals (if (and (symbolp fixed) fixed) (list fixed) fixed))
       ((when (not (subsetp-eq fixed-formals all-formals)))
        (er hard? 'deffilter-fn "The :fixed formals ~x0 are not among the formals." (set-difference-eq fixed-formals all-formals)))
       (list-formals (set-difference-eq all-formals fixed-formals))
       ((when (not (consp list-formals)))
        (er hard? 'deffilter-fn "There are no list formals."))
       (filter-fn filter-fn-name)
       (atom-tests (wrap-list '(atom x) 'x list-formals))
       (cars (wrap-list '(first x) 'x list-formals))
       (recursive-call-args (wrap-targets '(rest x) 'x all-formals list-formals))
       (termination-test (make-or atom-tests))
       (element-test (sublis-var-simple (pairlis$ list-formals cars) term)) ;might test several elements
       (defun `(defund ,filter-fn (,@all-formals)
                 ,@(if declares
                       `((declare ,@declares ;(xargs :normalize nil)
                                  ))
                     `(;(declare (xargs :normalize nil))
                       ))
                 (if ,termination-test
                     nil
                   ;; use a let in case a formal appears more than once?
                   (if ,element-test
                       (cons ,(first cars) (,filter-fn ,@recursive-call-args))
                     (,filter-fn ,@recursive-call-args)))))
       (tail-rec-aux-name (pack$ filter-fn '-tail-aux))
       (tail-rec-name (pack$ filter-fn '-tail))
       (tail-rec-no-rev-aux-name (pack$ filter-fn '-tail-no-rev-aux))
       (tail-rec-no-rev-name (pack$ filter-fn '-tail-no-rev))
       (tail-rec-defuns (and tail-rec
                             `( ;; This version reverses the accumulator at the end.
                               (defund ,tail-rec-aux-name (,@all-formals acc) ;todo: watch for name clash with formal named ACC
                                 (if ,termination-test
                                     (reverse-list acc)
                                   (if ,element-test
                                       (,tail-rec-aux-name ,@recursive-call-args (cons ,(first cars) acc))
                                     (,tail-rec-aux-name ,@recursive-call-args acc))))

                               ;; Tail recursive function equal to generic-filter
                               (defund ,tail-rec-name (,@all-formals)
                                 (,tail-rec-aux-name ,@all-formals nil)))))
       (tail-rec-theorems (and tail-rec
                               ;; todo: improve the proof (see what we do below and use some of that machinery)
                               `((defthm ,(pack$ tail-rec-aux-name '-rewrite)
                                   (equal (,tail-rec-aux-name ,@all-formals acc)
                                          (append (reverse-list acc)
                                                  (,filter-fn ,@all-formals)))
                                   :hints (("Goal" :induct (,tail-rec-aux-name ,@all-formals acc)
                                            :in-theory (enable ,tail-rec-aux-name
                                                                      ,filter-fn
                                                                      deffilter-helper-reverse-list-of-cons
                                                                      deffilter-helper-append-associative))))
                                 (defthm ,(pack$ tail-rec-name '-rewrite)
                                   (equal (,tail-rec-name ,@all-formals)
                                          (,filter-fn ,@all-formals))
                                   :hints (("Goal" :in-theory (enable ,tail-rec-name)))))))
       (tail-rec-no-rev-defuns (and tail-rec-no-rev
                                    `( ;; This version does not reverse the accumulator at the end.
                                      (defund ,tail-rec-no-rev-aux-name (,@all-formals acc)
                                        (if ,termination-test
                                            acc
                                          (if ,element-test
                                              (,tail-rec-no-rev-aux-name ,@recursive-call-args (cons ,(first cars) acc))
                                            (,tail-rec-no-rev-aux-name ,@recursive-call-args acc))))
                                      ;; Tail recursive function equal to generic-filter except we don't reverse the
                                      ;; accumulator, so the result is in reverse order.
                                      (defund ,tail-rec-no-rev-name (,@all-formals)
                                        (,tail-rec-no-rev-aux-name ,@all-formals nil)))))
       (tail-rec-no-rev-theorems (and tail-rec-no-rev
                                      `((defthm ,(pack$ tail-rec-no-rev-aux-name '-rewrite)
                                          (equal (,tail-rec-no-rev-aux-name ,@all-formals acc)
                                                 (append (reverse-list (,filter-fn ,@all-formals)) acc))
                                          :hints (("Goal" :induct (,tail-rec-no-rev-aux-name ,@all-formals acc)
                                                   :in-theory (enable ,tail-rec-no-rev-aux-name
                                                                      ,filter-fn
                                                                      deffilter-helper-reverse-list-of-cons
                                                                      deffilter-helper-append-associative))))
                                        (defthm ,(pack$ tail-rec-no-rev-name '-rewrite)
                                          (equal (,tail-rec-no-rev-name ,@all-formals)
                                                 (reverse-list (,filter-fn ,@all-formals)))
                                          :hints (("Goal" :in-theory (enable ,tail-rec-no-rev-name)))))))
       (theory `(:in-theory (union-theories '(,filter-fn) (theory 'minimal-theory))))
       (list-formal-count (len list-formals))

;for now, only generate these when there is exactly 1 list formal (any number of fixed formals is okay):
;theorem for iff?
       (defthms
         (and (equal 1 list-formal-count)
              (let* ((list-formal (first list-formals)) ;could have a function called only, which has a guard that the list if non-empty
                     (fresh-var (fresh-var-name list-formal 0 all-formals))
;have each name reflect the formal it's replacing?
                     (fresh-vars (fresh-var-names (len fixed-formals) 'tmp (cons fresh-var all-formals)))
                     (fresh-var-alist ;(acons list-formal fresh-var
                      (pairlis$ fixed-formals fresh-vars) ;)
                      )
                     (fresh-formals (sublis-var-simple-lst fresh-var-alist all-formals))
                     (fresh-term (sublis-var-simple fresh-var-alist term))
                     (fixed-formal-bindings (make-doublets fresh-vars fixed-formals))
                     (bindings `((generic-predicate (lambda (,list-formal) ,fresh-term))
                                 (generic-filter (lambda (,list-formal) (,filter-fn ,@fresh-formals)))
                                 ,@(if forall-fn
                                       `((generic-forall (lambda (,list-formal) (,forall-fn ,@fresh-formals))))
                                     nil)
                                 ,@(if exists-fn
                                       `((generic-exists (lambda (,list-formal) (,exists-fn ,@fresh-formals))))
                                     nil)))
                     (bindings-no-fresh `((generic-predicate (lambda (,list-formal) ,term))
                                          (generic-filter (lambda (,list-formal) (,filter-fn ,@all-formals)))
                                          ,@(if forall-fn
                                                `((generic-forall (lambda (,list-formal) (,forall-fn ,@all-formals))))
                                              nil)
                                          ,@(if exists-fn
                                                `((generic-exists (lambda (,list-formal) (,exists-fn ,@all-formals))))
                                              nil))))
                `(
                  ,@(if forall-fn
                        `((defthm ,(pack$ forall-fn '- filter-fn)
                            (,forall-fn ,@(sublis-var-simple-lst
                                           (acons list-formal `(,filter-fn ,@all-formals) nil)
                                           all-formals))
                            :hints (("Goal" :use (:instance (:functional-instance generic-forall-of-generic-filter ,@bindings)
                                                            (vals ,list-formal)
                                                            ,@fixed-formal-bindings)
                                     ,@theory)))

                          (defthm ,(pack$ filter-fn '- forall-fn '-id)
                            (implies (and (true-listp ,list-formal)
                                          (,forall-fn ,@all-formals))
                                     (equal (,filter-fn ,@all-formals)
                                            ,list-formal))
                            :hints (("Goal" :use (:instance (:functional-instance generic-filter-generic-forall-id ,@bindings)
                                                            (vals ,list-formal)
                                                            ,@fixed-formal-bindings)
                                     ,@theory))))
                      nil)

                  ,@(if exists-fn
                        `((defthm ,(pack$ 'not- exists-fn '- filter-fn)
                            (implies (not (,exists-fn ,@all-formals))
                                     (equal (,filter-fn ,@all-formals)
                                            nil))
                            :hints (("Goal" :use (:instance (:functional-instance not-generic-exists-generic-filter ,@bindings)
                                                            (vals ,list-formal)
                                                            ,@fixed-formal-bindings)
                                     ,@theory))))
                      nil)

                  (defthm ,(pack$ 'subsetp-equal-of- filter-fn)
                    (subsetp-equal (,filter-fn ,@all-formals)
                                   ,list-formal)
                    :hints (("Goal" :use (:instance (:functional-instance subsetp-equal-of-generic-filter ,@bindings)
                                                    (vals ,list-formal)
                                                    ,@fixed-formal-bindings)
                             ,@theory)))

                  (defthm ,(pack$ filter-fn '-subsequencep-equal)
                    (subsequencep-equal (,filter-fn ,@all-formals)
                               ,list-formal)
                    :hints (("Goal" :use (:instance (:functional-instance generic-filter-subsequencep-equal ,@bindings)
                                                    (vals ,list-formal)
                                                    ,@fixed-formal-bindings)
                             ,@theory)))

                  (defthm ,(pack$ filter-fn '-idempotent)
                    (equal (,filter-fn ,@(sublis-var-simple-lst
                                          (acons list-formal `(,filter-fn ,@all-formals) nil)
                                          all-formals))
                           (,filter-fn ,@all-formals))
                    :hints (("Goal" :use (:instance (:functional-instance generic-filter-idempotent ,@bindings)
                                                    (vals ,list-formal)
                                                    ,@fixed-formal-bindings)
                             ,@theory)))

                  (defthm ,(pack$ filter-fn '-of-cons)
                    (equal (,filter-fn ,@(sublis-var-simple-lst
                                          (acons list-formal `(cons ,fresh-var ,list-formal) nil)
                                          all-formals))
                           (if ,(sublis-var-simple (acons list-formal fresh-var nil)
                                               term)
                               (cons ,fresh-var (,filter-fn ,@all-formals))
                             (,filter-fn ,@all-formals)))
                    :hints (("Goal" :use (:instance (:functional-instance generic-filter-of-cons ,@bindings)
                                                    (a ,fresh-var)
                                                    (x ,list-formal)
                                                    ,@fixed-formal-bindings)
                             ,@theory)))

                  (defthm ,(pack$ filter-fn '-of-append)
                    (equal (,filter-fn ,@(sublis-var-simple-lst
                                          (acons list-formal `(append ,list-formal ,fresh-var) nil)
                                          all-formals))
                           (append (,filter-fn ,@all-formals)
                                   (,filter-fn ,@(sublis-var-simple-lst
                                                  (acons list-formal fresh-var nil)
                                                  all-formals))))
                    :hints (("Goal" :use (:instance (:functional-instance generic-filter-of-append ,@bindings)
                                                    (y ,fresh-var)
                                                    (x ,list-formal)
                                                    ,@fixed-formal-bindings)
                             ,@theory)))

                  (defthm ,(pack$ filter-fn '-of-revappend)
                    (equal (,filter-fn ,@(sublis-var-simple-lst
                                          (acons list-formal `(revappend ,list-formal ,fresh-var) nil)
                                          all-formals))
                           (revappend (,filter-fn ,@all-formals)
                                      (,filter-fn ,@(sublis-var-simple-lst
                                                     (acons list-formal fresh-var nil)
                                                     all-formals))))
                    :hints (("Goal" :use (:instance (:functional-instance generic-filter-of-revappend ,@bindings)
                                                    (y ,fresh-var)
                                                    (x ,list-formal)
                                                    ,@fixed-formal-bindings)
                             ,@theory)))

                  (defthm ,(pack$ filter-fn '-of-remove1)
                    (equal (,filter-fn ,@(sublis-var-simple-lst
                                          (acons list-formal `(remove1-equal ,fresh-var ,list-formal) nil)
                                          all-formals))
                           (if ,(sublis-var-simple (acons list-formal fresh-var nil)
                                               term)
                               (remove1-equal ,fresh-var (,filter-fn ,@all-formals))
                             (,filter-fn ,@all-formals)))
                    :hints (("Goal" :use (:instance (:functional-instance generic-filter-of-remove1 ,@bindings)
                                                    (a ,fresh-var)
                                                    (x ,list-formal)
                                                    ,@fixed-formal-bindings)
                             ,@theory)))

                  (defthm ,(pack$ filter-fn '-of-remove-equal)
                    (equal (,filter-fn ,@(sublis-var-simple-lst
                                          (acons list-formal `(remove-equal ,fresh-var ,list-formal) nil)
                                          all-formals))
                           (if ,(sublis-var-simple (acons list-formal fresh-var nil)
                                               term)
                               (remove-equal ,fresh-var (,filter-fn ,@all-formals))
                             (,filter-fn ,@all-formals)))
                    :hints (("Goal" :use (:instance (:functional-instance generic-filter-of-remove-equal ,@bindings)
                                                    (a ,fresh-var)
                                                    (x ,list-formal)
                                                    ,@fixed-formal-bindings)
                             ,@theory)))

                  (defthm ,(pack$ filter-fn '-of-true-list-fix)
                    (equal (,filter-fn ,@(sublis-var-simple-lst
                                          (acons list-formal `(true-list-fix ,list-formal) nil)
                                          all-formals))
                           (,filter-fn ,@all-formals))
                    :hints (("Goal" :use (:instance (:functional-instance generic-filter-of-true-list-fix ,@bindings)
                                                    (x ,list-formal)
                                                    ,@fixed-formal-bindings)
                             ,@theory)))

                  (defthm ,(pack$ filter-fn '-when-not-consp)
                    (implies (not (consp ,list-formal))
                             (equal (,filter-fn ,@all-formals)
                                    nil))
                    :hints (("Goal" :use (:instance (:functional-instance generic-filter-when-not-consp ,@bindings)
                                                    (x ,list-formal)
                                                    ,@fixed-formal-bindings)
                             ,@theory)))

                  (defthm ,(pack$ filter-fn '-of-nil)
                    (equal (,filter-fn ,@(sublis-var-simple-lst
                                          (acons list-formal nil nil)
                                          all-formals))
                           nil)
                    :hints (("Goal" :use (:instance (:functional-instance generic-filter-of-nil ,@bindings)
                                                    ;; (x ,list-formal)
                                                    ,@fixed-formal-bindings)
                             ,@theory)))

                  (defthm ,(pack$ 'use- filter-fn)
                    (implies (memberp x (,filter-fn ,@(sublis-var-simple-lst (acons list-formal (pack$ 'free- list-formal) nil) all-formals)))
                             ,(sublis-var-simple (acons list-formal 'x nil) term)) ;fixme what if term is not suitable to be a rewrite rule?
                    ;; avoid illegal rewrite rules (fixme print a warning) fixme: would like this test to apply to the macro-expanded body:
                    ,@(if (or (symbolp term) (member-eq (ffn-symb term) '(if or
;and ;I think and is actually okay
                                                                             ))) '(:rule-classes nil) nil)
;fffixme think about fresh formals!
                    :hints (("Goal" :do-not-induct t
                             :use (:instance (:functional-instance generic-predicate-when-generic-filter ,@bindings-no-fresh)
                                             (free ,(pack$ 'free- list-formal))
                                             ;;                                                      (x ,list-formal)
                                             ;;,@fixed-formal-bindings
                                             )
                             ,@theory))))))))
    (manage-screen-output
     verbose
     `(progn ,defun
             ,@tail-rec-defuns
             ,@tail-rec-theorems
             ,@tail-rec-no-rev-defuns
             ,@tail-rec-no-rev-theorems
             ,@defthms
             (value-triple ',filter-fn-name)))))

;simple version for the common case of a unary predicate over a single list
(defmacro deffilter-simple (pred ;the unary predicate to apply to each element in the list
                            &key
                            (name 'nil) ;the name to use for the generated function (defaults to keep- followed by pred)
                            (guard 'nil)
                            (forall-fn 'nil)
                            (exists-fn 'nil)
                            (tail-rec 'nil)
                            (tail-rec-no-rev 'nil)
                            (verbose 'nil))
  (declare (xargs :guard (member-eq verbose '(t nil)))) ;for now, since it's passed to manage-screen-output without being evaluated
  (deffilter-fn
    (or name ;use name if supplied
        (pack$ 'keep- pred) ;;(pack-in-package-of-symbol pred 'keep- fn) ;this was causing things to be put in the common lisp package, which was a problem for keep-rationalp  maybe use ACL2 if the symbol is in that package?
        )
    '(x) ;fixme: would really like this to be "xs" or "vals" or something indicating that this is a list
    `(,pred x)
    nil ;no fixed args
    nil ;no declares
    guard
    forall-fn
    exists-fn
    tail-rec
    tail-rec-no-rev
    verbose))

;; The :fixed option indicates which formals are fixed. All other formals are
;; lists that get cdred down.
(defmacro deffilter (name all-formals term
                          &key (fixed 'nil)
                               (declares 'nil)
                               (guard 'nil)
                               (forall-fn 'nil)
                               (exists-fn 'nil)
                               (tail-rec 'nil)
                               (tail-rec-no-rev 'nil)
                               (verbose 'nil))
  (declare (xargs :guard (member-eq verbose '(t nil)))) ;for now, since it's passed to manage-screen-output without being evaluated
  (deffilter-fn name all-formals term fixed declares guard forall-fn exists-fn tail-rec tail-rec-no-rev verbose))
