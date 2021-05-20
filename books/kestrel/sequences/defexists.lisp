; Generate a function to search a list for an item that satisfies a predicate
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

;; See tests in defexists-tests.lisp.

(include-book "generics-utilities")
(include-book "kestrel/lists-light/reverse-list-def" :dir :system)
(include-book "kestrel/lists-light/firstn-def" :dir :system)
(include-book "kestrel/lists-light/subrange-def" :dir :system)
;(include-book "kestrel/lists-light/memberp" :dir :system)
(include-book "kestrel/lists-light/perm" :dir :system)
(include-book "kestrel/utilities/doublets2" :dir :system)
;(include-book "../utilities/alists")
(include-book "../utilities/fresh-names")
(include-book "kestrel/utilities/make-or" :dir :system)
(include-book "kestrel/utilities/user-interface" :dir :system) ;for manage-screen-output
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/firstn" :dir :system))

(defund generic-exists (x)
  (if (endp x)
      nil
    (if (generic-predicate (car x))
        t
      (generic-exists (cdr x)))))

(defthm generic-exists-of-cons
  (equal (generic-exists (cons a x))
         (if (generic-predicate a)
             t
           (generic-exists x)))
  :hints (("Goal" :in-theory (enable generic-exists))))

(defthm generic-exists-of-append
  (equal (generic-exists (append x y))
         (or (generic-exists x)
             (generic-exists y)))
  :hints (("Goal" :in-theory (enable generic-exists))))

(defthm generic-exists-of-revappend
  (implies (or (generic-exists x)
               (generic-exists y))
           (generic-exists (revappend x y)))
  :hints (("Goal" :in-theory (enable generic-exists revappend))))

;; Are these useful?
(defthm generic-exists-of-cdr
  (implies (generic-exists (cdr x))
           (generic-exists x))
  :hints (("Goal" :in-theory (enable generic-exists))))

(defthm generic-exists-of-nthcdr
  (implies (generic-exists (nthcdr n x))
           (generic-exists x))
  :hints (("Goal" :in-theory (e/d (generic-exists nthcdr) (;NTHCDR-OF-CDR-COMBINE NTHCDR-OF-CDR-COMBINE-STRONG
                                                           )))))

(defthm generic-exists-of-firstn
  (implies (generic-exists (firstn n (double-rewrite x)))
           (generic-exists x))
  :hints (("Goal" :in-theory (e/d (generic-exists firstn) (firstn-becomes-take-gen)))))

(defthm generic-exists-of-take
  (implies (and (generic-exists (take n x))
                (<= n (len (double-rewrite x))))
           (generic-exists x))
  :hints (("Goal" :in-theory (e/d (generic-exists take) (;anti-subrange
                                                             )))))

(defthm generic-exists-of-true-list-fix
  (equal (generic-exists (true-list-fix x))
         (generic-exists x))
  :hints (("Goal" :in-theory (enable generic-exists))))

(defthm generic-exists-of-reverse-list
  (equal (generic-exists (reverse-list x))
         (generic-exists x))
  :hints (("Goal" :in-theory (enable generic-exists reverse-list))))

(defthm generic-exists-when-not-consp
  (implies (not (double-rewrite x))
           (equal (generic-exists x)
                  nil))
  :hints (("Goal" :in-theory (enable generic-exists))))

;used for the use-XXX theorem below
(defthm generic-predicate-when-generic-exists
  (implies (and (generic-predicate x)
                (memberp x free))
           (generic-exists free))
  :hints (("Goal" :in-theory (enable MEMBERP))))

(defthm generic-exists-of-remove1
  (implies (not (generic-predicate a))
           (equal (generic-exists (remove1 a x))
                  (generic-exists x)))
  :hints (("Goal" :in-theory (enable generic-exists))))

(defthm generic-exists-of-remove-equal
  (implies (not (generic-predicate a))
           (equal (generic-exists (remove-equal a x))
                  (generic-exists x)))
  :hints (("Goal" :in-theory (enable generic-exists))))

(defthmd generic-exists-when-perm
  (implies (perm x y)
           (equal (generic-exists x)
                  (generic-exists y)))
  :hints (("Goal" :in-theory (enable generic-exists perm))))

(defcong perm equal (generic-exists x) 1
  :package :function
  :hints (("Goal" :use (:instance generic-exists-when-perm (y x-equiv)))))

;fixme add this to the macro?!
(defthm generic-exists-of-subrange
  (implies (and (generic-exists (subrange start end x))
                (natp start) ;drop?
                (< end (len x)))
           (generic-exists x))
  :hints (("Goal"
           :use (:instance generic-exists-of-take (n (+ (- START) 1 END))
                           (x (NTHCDR START X)))
           :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (;generic-exists
                            subrange
                            LEN-OF-CDR)
                           (;generic-exists-of-take
                            ;anti-subrange
                            take
                            len)))))

;; Doesn't seem to be true
;; (defthm booleanp-of-generic-exists ;add to the macro
;;   (equal (booleanp (generic-exists x))
;;          t))

(defun defexists-fn (exists-fn-name all-formals term fixed declares guard verbose)
  (let* ((declares (if guard (cons `(xargs :guard ,guard) declares) declares)) ;i guess this excludes a guard of nil....
         (fixed-formals (if (and (symbolp fixed) fixed) (list fixed) fixed))
         (list-formals (set-difference-eq all-formals fixed-formals))
         (exists-fn exists-fn-name)
         (atom-tests (wrap-list '(atom x) 'x list-formals))
         (cars (wrap-list '(first x) 'x list-formals))
         (recursive-call-args (wrap-targets '(rest x) 'x all-formals list-formals))
         (defun `(defund ,exists-fn (,@all-formals)
                    ,@(if declares
                          `((declare ,@declares ;(xargs :normalize nil)
                                     ))
                        `(;(declare (xargs :normalize nil))
                        ))
                    (if ,(make-or atom-tests)
                        nil
;use a let incase a formal appears more than once?
                      (if ,(sublis-var-simple (pairlis$ list-formals cars) term)
                          t
                        (,exists-fn ,@recursive-call-args)))))
         (theory `(:in-theory (union-theories '(,exists-fn) (theory 'minimal-theory))))
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
                                   (generic-exists (lambda (,list-formal) (,exists-fn ,@fresh-formals)))))
                       (bindings-no-fresh `((generic-predicate (lambda (,list-formal) ,term))
                                            (generic-exists (lambda (,list-formal) (,exists-fn ,@all-formals))))))
                  `((defthm ,(pack$ exists-fn '-of-cons)
                      (equal (,exists-fn ,@(sublis-var-simple-lst
                                            (acons list-formal `(cons ,fresh-var ,list-formal) nil)
                                            all-formals))
                             (if ,(sublis-var-simple (acons list-formal fresh-var nil)
                                                 term)
                                 t
                               (,exists-fn ,@all-formals)))
                      :hints (("Goal" :use (:instance (:functional-instance generic-exists-of-cons ,@bindings)
                                                      (a ,fresh-var)
                                                      (x ,list-formal)
                                                      ,@fixed-formal-bindings)
                               ,@theory)))

                    (defthm ,(pack$ exists-fn '-of-append)
                      (equal (,exists-fn ,@(sublis-var-simple-lst
                                            (acons list-formal `(append ,list-formal ,fresh-var) nil)
                                            all-formals))
                             (or (,exists-fn ,@all-formals)
                                 (,exists-fn ,@(sublis-var-simple-lst
                                                (acons list-formal fresh-var nil)
                                                all-formals))))
                      :hints (("Goal" :use (:instance (:functional-instance generic-exists-of-append ,@bindings)
                                                      (y ,fresh-var)
                                                      (x ,list-formal)
                                                      ,@fixed-formal-bindings)
                               ,@theory)))

                    (defthm ,(pack$ exists-fn '-of-revappend)
                      (implies (or (,exists-fn ,@all-formals)
                                   (,exists-fn ,@(sublis-var-simple-lst
                                                  (acons list-formal fresh-var nil)
                                                  all-formals)))
                               (,exists-fn ,@(sublis-var-simple-lst
                                              (acons list-formal `(revappend ,list-formal ,fresh-var) nil)
                                              all-formals)))
                      :hints (("Goal" :use (:instance (:functional-instance generic-exists-of-revappend ,@bindings)
                                                      (y ,fresh-var)
                                                      (x ,list-formal)
                                                      ,@fixed-formal-bindings)
                               ,@theory)))

                    (defthm ,(pack$ exists-fn '-of-cdr)
                      (implies (,exists-fn ,@(sublis-var-simple-lst
                                              (acons list-formal `(cdr ,list-formal) nil)
                                              all-formals))
                               (,exists-fn ,@all-formals))
                      :hints (("Goal" :use (:instance (:functional-instance generic-exists-of-cdr ,@bindings)
                                                      (x ,list-formal)
                                                      ,@fixed-formal-bindings)
                               ,@theory)))

                    ;;from here down, the fresh var name should be nXXX?
                    (defthm ,(pack$ exists-fn '-of-nthcdr)
                      (implies (,exists-fn ,@(sublis-var-simple-lst
                                              (acons list-formal `(nthcdr ,fresh-var ,list-formal) nil)
                                              all-formals))
                               (,exists-fn ,@all-formals))
                      :hints (("Goal" :use (:instance (:functional-instance generic-exists-of-nthcdr ,@bindings)
                                                      (n ,fresh-var)
                                                      (x ,list-formal)
                                                      ,@fixed-formal-bindings)
                               ,@theory)))

                    (defthm ,(pack$ exists-fn '-of-firstn)
                      (implies (,exists-fn ,@(sublis-var-simple-lst
                                              (acons list-formal `(firstn ,fresh-var (double-rewrite ,list-formal)) nil)
                                              all-formals))
                               (,exists-fn ,@all-formals))
                      :hints (("Goal" :use (:instance (:functional-instance generic-exists-of-firstn ,@bindings)
                                                      (n ,fresh-var)
                                                      (x ,list-formal)
                                                      ,@fixed-formal-bindings)
                               ,@theory)))

                    (defthm ,(pack$ exists-fn '-of-take)
                      (implies (and (,exists-fn ,@(sublis-var-simple-lst
                                                   (acons list-formal `(take ,fresh-var ,list-formal) nil)
                                                   all-formals))
                                    (<= ,fresh-var (len (double-rewrite ,list-formal))))
                               (,exists-fn ,@all-formals))
                      :hints (("Goal" :use (:instance (:functional-instance generic-exists-of-take ,@bindings)
                                                      (n ,fresh-var)
                                                      (x ,list-formal)
                                                      ,@fixed-formal-bindings)
                               ,@theory)))

                    (defthmd ,(pack$ exists-fn '-when-perm)
                      (implies (perm ,list-formal ,fresh-var)
                               (equal (,exists-fn ,@all-formals)
                                      (,exists-fn ,@(sublis-var-simple-lst
                                                     (acons list-formal fresh-var nil)
                                                     all-formals))))
                      :hints (("Goal" :use (:instance (:functional-instance generic-exists-when-perm ,@bindings)
                                                      (x ,list-formal)
                                                      (y ,fresh-var)
                                                      ,@fixed-formal-bindings)
                               ,@theory)))

                    (defthm ,(pack$ exists-fn '-of-true-list-fix)
                      (equal (,exists-fn ,@(sublis-var-simple-lst
                                            (acons list-formal `(true-list-fix ,list-formal) nil)
                                            all-formals))
                             (,exists-fn ,@all-formals))
                      :hints (("Goal" :use (:instance (:functional-instance generic-exists-of-true-list-fix ,@bindings)
                                                      (x ,list-formal)
                                                      ,@fixed-formal-bindings)
                               ,@theory)))

                    ;;here we use the specific theorem proved just above (not a generic theorem)
                    ;; restore after proving generic-exists-when-perm
                    (defcong perm equal (,exists-fn ,@all-formals) ,(position-of list-formal all-formals)
                      :package :function
                      :hints (("Goal" :use (:instance ,(pack$ exists-fn '-when-perm)
                                                      ;(,list-formal x)
                                                      (,fresh-var ,(pack-in-package-of-symbol exists-fn list-formal '-equiv))
                                                      ))))
                    (defthm ,(pack$ exists-fn '-reverse-list)
                      (equal (,exists-fn ,@(sublis-var-simple-lst
                                              (acons list-formal `(reverse-list ,list-formal) nil)
                                              all-formals))
                             (,exists-fn ,@all-formals))
                      :hints (("Goal" :use (:instance (:functional-instance generic-exists-of-reverse-list ,@bindings)
                                                      (x ,list-formal)
                                                      ,@fixed-formal-bindings)
                               ,@theory)))

                    (defthm ,(pack$ exists-fn '-when-not-consp)
                      (implies (not (consp (double-rewrite ,list-formal)))
                               (equal (,exists-fn ,@all-formals)
                                      nil))
                      :hints (("Goal" :use (:instance (:functional-instance generic-exists-when-not-consp ,@bindings)
                                                      (x ,list-formal)
                                                      ,@fixed-formal-bindings)
                               ,@theory)))

                    (defthm ,(pack$ 'use- exists-fn)
                      (implies (and ,(sublis-var-simple (acons list-formal 'x nil) term)
                                    (memberp x ,(pack$ 'free- list-formal)))
                               (,exists-fn ,@(sublis-var-simple-lst (acons list-formal (pack$ 'free- list-formal) nil) all-formals))) ;fixme what if term is not suitable to be a rewrite rule?
                      ;; avoid illegal rewrite rules (fixme print a warning) fixme: would like this test to apply to the macro-expanded body:
                      ,@(if (or (symbolp term) (member-eq (ffn-symb term) '(if or
                                                                               ;and ;I think and is actually okay
                                                                               ))) '(:rule-classes nil) nil)
                      ;fffixme think about fresh formals!
                      :hints (("Goal" :do-not-induct t
                               :use (:instance (:functional-instance generic-predicate-when-generic-exists ,@bindings-no-fresh)
                                                      (free ,(pack$ 'free- list-formal))
;                                                      (x ,list-formal)
                                                      ;,@fixed-formal-bindings
                                                      )
                               ,@theory))))))))
    (manage-screen-output ;todo: expand manage-screen-output here?
     verbose
    `(progn ,defun
            ,@defthms
            (value-triple ',exists-fn-name)))))

;simple version for the common case of mapping a unary predicate over a single list
(defmacro defexists-simple (pred ;the unary predicate to apply to each element in the list
                            &key
                            (name 'nil) ;the name to use for the generated function (defaults to all- followed by pred)
                            (guard 'nil)
                            (verbose 'nil)
                            )
  (declare (xargs :guard (member-eq verbose '(t nil)))) ;for now, since it's passed to manage-screen-output without being evaluated
  (defexists-fn
    (or name ;use name if supplied
        (pack$ 'some- pred) ;;(pack-in-package-of-symbol pred 'all- fn) ;this was causing things to be put in the common lisp package, which was a problem for all-rationalp  maybe use ACL2 if the symbol is in that package?
        )
    '(x) ;fixme: would really like this to be "xs" or "vals" or something indicating that this is a list
    `(,pred x)
    nil ;no fixed args
    nil ;no declares
    guard
    verbose))

;FIXED indicates which formals are fixed  All other formals are lists that get cdred down.
;add more options?
;
(defmacro defexists (name all-formals term &key (fixed 'nil) (declares 'nil) (guard 'nil) (verbose 'nil))
  (declare (xargs :guard (member-eq verbose '(t nil)))) ;for now, since it's passed to manage-screen-output without being evaluated
  (defexists-fn name all-formals term fixed declares guard verbose))
