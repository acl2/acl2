; Generate a function to check if all items in a list satisfy a predicate
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Main Author: Eric Smith (eric.smith@kestrel.edu)
; Contributing Author: Stephen Westfold (westfold@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: IN-PROGRESS

;do more to avoid name clashes - add funny symbols (yuck)?
;add filter and reduce!

;Note: jared davis did something like the forall stuff below at rockwell in his sets library?

;add nth-of and type facts?

;TODO: Add the ability to prove the "forall theorems" or the "map theorems" for a pre-existing function that is essentially a forall or a map (possibly re-use existing theorems that say the same thing).

;TODO: Think about guards..

;TODO: Re-order the events for the true-list and non-true-list cases (both in the file and in the macro) to all be consistent.

;TODO: Consider using :by hints instead of :use hints here.

(include-book "generics-utilities")
(include-book "kestrel/lists-light/reverse-list-def" :dir :system)
(include-book "kestrel/lists-light/firstn-def" :dir :system)
(include-book "kestrel/lists-light/subrange-def" :dir :system)
(include-book "kestrel/lists-light/memberp-def" :dir :system)
(include-book "kestrel/lists-light/perm-def" :dir :system)
(include-book "kestrel/lists-light/perm" :dir :system) ;needed for the congruence rules?  could split out the defequiv
(include-book "kestrel/utilities/doublets2" :dir :system)
(include-book "../utilities/fresh-names")
(include-book "kestrel/utilities/make-or" :dir :system)
(include-book "kestrel/utilities/make-and" :dir :system)
(include-book "kestrel/utilities/user-interface" :dir :system) ;for manage-screen-output (TODO: reduce the stuff included in this book)
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/member-equal" :dir :system))
(local (include-book "kestrel/lists-light/memberp2" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "kestrel/lists-light/remove1-equal" :dir :system))
(local (include-book "kestrel/lists-light/perm" :dir :system))
(local (include-book "kestrel/alists-light/pairlis-dollar" :dir :system))

;move
(local
 (defthm symbol-listp-of-set-difference-equal
  (implies (symbol-listp x)
           (symbol-listp (set-difference-equal x y)))))

;move
;disable?
;make a cheap version
(local
 (defthm symbolp-of-car-when-symbol-listp
   (implies (symbol-listp x)
            (symbolp (car x)))))


; x is a list - allow non-true-lists?
;what should the guards be?
;like a universal quantifier
;force this to return boolean?
;should i be using (not (consp x)) instead of (atom x) for speed?
(defund generic-forall (x)
  (if (atom x) ;fixme option to use endp if we know a true-listp guard?
      t
    (and (generic-predicate (car x))
         (generic-forall (cdr x)))))

(defthm generic-forall-of-cons
  (equal (generic-forall (cons a x))
         (and (generic-predicate a)
              (generic-forall x)))
  :hints (("Goal" :in-theory (enable generic-forall))))

(defthm generic-forall-of-add-to-set-equal
  (equal (generic-forall (add-to-set-equal a x))
         (and (generic-predicate a)
              (generic-forall x)))
  :hints (("Goal" :in-theory (enable generic-forall add-to-set-equal))))

;used for the use-XXX theorem below
(defthm generic-predicate-when-generic-forall
  (implies (and (generic-forall free)
                (memberp (double-rewrite x) free))
           (generic-predicate x))
  :hints (("Goal" :in-theory (enable memberp))))

(defthm generic-forall-of-union-equal
  (equal (generic-forall (union-equal x y))
         (and (generic-forall x)
              (generic-forall y)))
  :hints (("Goal" :in-theory (enable generic-forall union-equal))))

(defthm generic-predicate-of-car-when-generic-forall
  (implies (and (generic-forall x)
                (consp (double-rewrite x))) ;can move to conclusion (details depend on whether the generic-predicate holds on nil)
           (generic-predicate (car x)))
  :hints (("Goal" :in-theory (enable generic-forall))))

(defthm generic-predicate-of-car-of-last-when-generic-forall
  (implies (and (generic-forall x)
                (consp (double-rewrite x))) ;can move to conclusion (details depend on whether the generic-predicate holds on nil)
           (generic-predicate (car (last x))))
  :hints (("Goal" :in-theory (enable generic-forall))))

(defthm generic-forall-of-append
  (equal (generic-forall (append x y))
         (and (generic-forall x)
              (generic-forall y)))
  :hints (("Goal" :in-theory (enable generic-forall))))

;todo: strengthen?
(defthm generic-forall-of-revappend
  (implies (and (generic-forall x)
                (generic-forall y))
           (generic-forall (revappend x y)))
  :hints (("Goal" :in-theory (enable generic-forall revappend))))

(defthm generic-forall-of-cdr
  (implies (generic-forall x)
           (equal (generic-forall (cdr x))
                  t))
  :hints (("Goal" :in-theory (enable generic-forall))))

(defthm generic-forall-of-nthcdr
  (implies (generic-forall x)
           (equal (generic-forall (nthcdr n x))
                  t))
  :hints (("Goal" :in-theory (e/d (generic-forall nthcdr) (;NTHCDR-OF-CDR-COMBINE NTHCDR-OF-CDR-COMBINE-STRONG
                                                           )))))

(defthm generic-forall-of-firstn
  (implies (generic-forall x)
           (equal (generic-forall (firstn n x))
                  t))
  :hints (("Goal" :in-theory (enable generic-forall firstn))))

(defthm generic-forall-of-take
  (implies (and (generic-forall x)
                (<= n (len (double-rewrite x))))
           (equal (generic-forall (take n x))
                  t))
  :hints (("Goal" :in-theory (e/d (generic-forall take) (;anti-subrange
                                                             )))))

(defthm generic-forall-of-true-list-fix
  (equal (generic-forall (true-list-fix x))
         (generic-forall x))
  :hints (("Goal" :in-theory (enable generic-forall))))

;version for map?
;add to macro
(defthm generic-forall-of-reverse-list
  (equal (generic-forall (reverse-list x))
         (equal (generic-forall x)
                t))
  :hints (("Goal" :in-theory (enable generic-forall reverse-list))))

(defthm generic-forall-when-not-consp
  (implies (not (consp (double-rewrite x)))
           (equal (generic-forall x)
                  t))
  :hints (("Goal" :in-theory (enable generic-forall))))

(defthm generic-forall-of-remove1-equal
  (implies (generic-forall x)
           (generic-forall (remove1-equal a x)))
  :hints (("Goal" :in-theory (enable generic-forall))))

(defthm generic-forall-of-remove-equal
  (implies (generic-forall x)
           (generic-forall (remove-equal a x)))
  :hints (("Goal" :in-theory (enable generic-forall))))

;fixme add to macro?
(defthm generic-forall-when-generic-forall-of-remove1-equal
  (implies (and (generic-forall (remove1-equal item y))
                (generic-predicate item))
           (generic-forall y))
  :hints (("Goal" :in-theory (enable generic-forall))))

(defthmd generic-forall-when-perm
  (implies (perm x y)
           (equal (generic-forall x)
                  (generic-forall y)))
  :hints (("Goal" :in-theory (enable generic-forall perm))))

(defcong perm equal (generic-forall x) 1
  :package :function
  :hints (("Goal" :use (:instance generic-forall-when-perm (y x-equiv)))))

;;(defcong set-equal equal (generic-forall x) 1)

(defthm generic-forall-of-last
  (implies (generic-forall (double-rewrite x))
           (generic-forall (last x))))

;version for map?
;fixme add this to the macro?!
(defthm generic-forall-of-subrange
  (implies (and (generic-forall (double-rewrite x))
                (natp start) ;drop?
                (< end (len x)))
           (generic-forall (subrange start end x)))
  :hints (("Goal"
           :use (:instance generic-forall-of-take (n (+ (- START) 1 END))
                           (x (NTHCDR START X)))
           :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (;generic-forall
                            subrange
                            ;;LIST::LEN-OF-CDR-BETTER
                            )
                           (;generic-forall-of-take
                            ;anti-subrange
                            take
                            len)))))

(defthm booleanp-of-generic-forall ;add to the macro
  (equal (booleanp (generic-forall x))
         t))

;;; Variant that implies true-list-p

(defund generic-forall-p (x)
  (if (atom x)
      (null x)
    (and (generic-predicate (car x))
         (generic-forall-p (cdr x)))))

(defthm generic-forall-p-of-cons
  (equal (generic-forall-p (cons a x))
         (and (generic-predicate a)
              (generic-forall-p x)))
  :hints (("Goal" :in-theory (enable generic-forall-p))))

(defthm generic-forall-p-of-add-to-set-equal
  (equal (generic-forall-p (add-to-set-equal a x))
         (and (generic-predicate a)
              (generic-forall-p x)))
  :hints (("Goal" :in-theory (enable generic-forall-p add-to-set-equal))))

;used for the use-XXX theorem below
(defthm generic-predicate-when-generic-forall-p
  (implies (and (generic-forall-p free)
                (memberp x (double-rewrite free)))
           (generic-predicate x))
  :hints (("Goal" :in-theory (enable memberp))))

;; Not quite as nice as the non-p version:
(defthm generic-forall-p-of-union-equal
  (equal (generic-forall-p (union-equal x y))
         (and (generic-forall-p (true-list-fix (double-rewrite x)))
              (generic-forall-p y)))
  :hints (("Goal" :expand (generic-forall-p (true-list-fix x))
:in-theory (enable generic-forall union-equal))))

;; non-standard name!
(defthm generic-predicate-p-of-car
  (implies (and (generic-forall-p x)
                (consp (double-rewrite x))) ;can move to conclusion (details depend on whether the generic-predicate holds on nil)
           (generic-predicate (car x)))
  :hints (("Goal" :in-theory (enable generic-forall))))

;; Different from the version in the non-true-list case:
(defthm generic-forall-p-of-append
  (equal (generic-forall-p (append x y))
         (and (generic-forall-p (true-list-fix x))
              (generic-forall-p y)))
  :hints (("Goal" :in-theory (enable generic-forall-p append))))

(defthm generic-forall-p-of-revappend
  (implies (and (generic-forall-p x)
                (generic-forall-p y))
           (generic-forall-p (revappend x y)))
  :hints (("Goal" :in-theory (enable generic-forall-p revappend))))

(defthm generic-forall-p-of-cdr
  (implies (generic-forall-p x)
           (equal (generic-forall-p (cdr x))
                  t))
  :hints (("Goal" :in-theory (enable generic-forall-p))))

(defthm generic-forall-p-of-nthcdr
  (implies (generic-forall-p x)
           (equal (generic-forall-p (nthcdr n x))
                  t))
  :hints (("Goal" :in-theory (e/d (generic-forall-p nthcdr) (;NTHCDR-OF-CDR-COMBINE NTHCDR-OF-CDR-COMBINE-STRONG
                                                           )))))

(defthm generic-forall-p-of-firstn
  (implies (generic-forall-p x)
           (equal (generic-forall-p (firstn n x))
                  t))
  :hints (("Goal" :in-theory (enable generic-forall-p firstn))))

(defthm generic-forall-p-of-take
  (implies (and (generic-forall-p x)
                (<= n (len (double-rewrite x))))
           (equal (generic-forall-p (take n x))
                  t))
  :hints (("Goal" :in-theory (e/d (generic-forall-p take) (;anti-subrange
                                                             )))))

;; Different from the version in the non-true-list case:
(defthm generic-forall-p-of-true-list-fix
  (implies (generic-forall-p x)
           (generic-forall-p (true-list-fix x)))
  :hints (("Goal" :in-theory (enable generic-forall-p))))

;version for map?
;add to macro
(defthm generic-forall-p-of-reverse-list
  (equal (generic-forall-p (reverse-list x))
         (equal (generic-forall-p (true-list-fix (double-rewrite x)))
                t))
  :hints (("Goal" :in-theory (enable generic-forall-p reverse-list))))

;; Different from the version in the non-true-list case:
(defthm generic-forall-p-when-not-consp
  (implies (not (consp (double-rewrite x)))
           (equal (generic-forall-p x)
                  (equal nil x)))
  :hints (("Goal" :in-theory (enable generic-forall-p))))

;used for the use-XXX theorem below
;; defined above!
;; (defthm generic-predicate-when-generic-forall-p
;;   (implies (and (generic-forall-p free)
;;                 (memberp x free))
;;            (generic-predicate x))
;;   :hints (("Goal" :in-theory (enable memberp))))

(defthm generic-predicate-of-car-when-generic-forall-p
  (implies (and (generic-forall-p x)
                (consp (double-rewrite x))) ;can move to conclusion (details depend on whether the generic-predicate holds on nil)
           (generic-predicate (car x)))
  :hints (("Goal" :in-theory (enable generic-forall-p))))

(defthm generic-predicate-of-car-of-last-when-generic-forall-p
  (implies (and (generic-forall-p x)
                (consp (double-rewrite x))) ;can move to conclusion (details depend on whether the generic-predicate holds on nil)
           (generic-predicate (car (last x))))
  :hints (("Goal" :in-theory (enable generic-forall-p))))

(defthm generic-forall-p-of-remove1-equal
  (implies (generic-forall-p x)
           (generic-forall-p (remove1-equal a x)))
  :hints (("Goal" :in-theory (enable generic-forall-p remove1-equal))))

(defthm generic-forall-p-of-remove-equal
  (implies (generic-forall-p x)
           (generic-forall-p (remove-equal a x)))
  :hints (("Goal" :in-theory (enable generic-forall-p))))

;fixme add to macro (and what else needs to be added)?
(defthm generic-forall-p-when-generic-forall-p-of-remove1-equal
  (implies (and (generic-forall-p (remove1-equal item y))
                (generic-predicate item))
           (equal (generic-forall-p y)
                  (true-listp y)))
  :hints (("Goal" :in-theory (enable generic-forall-p))))

(defthmd not-generic-forall-p-when-not-generic-predicate-and-member-equal
  (implies (and (not (generic-predicate item))
                (member-equal item x))
           (not (generic-forall-p x))))

(defthmd generic-forall-p-when-perm-helper
  (implies (and (true-listp x)
                ;(true-listp y)
                (perm x y))
           (equal (generic-forall-p x)
                  (generic-forall-p (true-list-fix (double-rewrite y)))))
  :hints (("Goal" :in-theory (enable generic-forall-p perm
                                     not-generic-forall-p-when-not-generic-predicate-and-member-equal))))

;add to macro?
(defthm not-generic-forall-p-when-not-true-listp
  (implies (not (true-listp x))
           (not (generic-forall-p x)))
  :hints (("Goal" :in-theory (enable generic-forall-p))))

;; we likely want this one disabled by default
(defthmd true-listp-when-generic-forall-p
  (implies (generic-forall-p x)
           (true-listp x))
  :hints (("Goal" :in-theory (enable generic-forall-p))))

;; Different from the version in the non-true-list case:
(defthmd generic-forall-p-when-perm
  (implies (perm x y)
           (equal (generic-forall-p x)
                  (and (true-listp x)
                       (generic-forall-p (true-list-fix y)))))
  :hints (("Goal" :use (:instance generic-forall-p-when-perm-helper (y (true-list-fix y)))
           :in-theory (disable generic-forall-p-when-perm-helper perm))))



;; Not true?
;; (defcong perm equal (generic-forall-p x) 1
;;   :hints (("Goal" :use (:instance generic-forall-p-when-perm (y bag::x-equiv)))))


(defthm generic-forall-p-of-last
  (implies (generic-forall-p x)
           (generic-forall-p (last x))))

;fixme add this to the macro?!
(defthm generic-forall-p-of-subrange
  (implies (and (generic-forall-p x)
                (natp start) ;drop?
                (< end (len x)))
           (generic-forall-p (subrange start end x)))
  :hints (("Goal"
           :use (:instance generic-forall-p-of-take (n (+ (- START) 1 END))
                           (x (NTHCDR START X)))
           :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (;generic-forall-p
                            subrange
;LIST::LEN-OF-CDR-BETTER
                            )
                           (;generic-forall-p-of-take
                            ;anti-subrange
                            take
                            len)))))

(defthm booleanp-of-generic-forall-p ;add to the macro
  (equal (booleanp (generic-forall-p x))
         t))

;; (defthm generic-forall-p-consp
;;   (implies (and (generic-forall-p x)
;;                 (not (consp x)))
;;            (equal (not x)
;;                   t)))

;;; end variant that is true-listp

;move
;dup
(defthm pseudo-term-listp-when-symbol-listp-cheap
  (implies (symbol-listp x)
           (pseudo-term-listp x))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable pseudo-term-listp))))

;it is an error to have no list formals - check for that?
(defun defforall-fn (forall-fn-name all-formals term fixed declares guard guard-hints true-listp verbose)
  (declare (xargs :guard (and (symbolp forall-fn-name)
                              (symbol-listp all-formals)
                              (pseudo-termp term)
                              (or (symbolp fixed)
                                  (symbol-listp fixed))
                              (true-listp declares)
                              (booleanp true-listp)
                              (booleanp verbose))))
  (let* ((declares (if guard (cons `(xargs :guard ,guard) declares) declares)) ;i guess this excludes a guard of nil....
         (declares (if guard-hints (cons `(xargs :guard-hints ,guard-hints) declares) declares)) ;todo: combine the xargs
         (fixed-formals (if (and (symbolp fixed) fixed) (list fixed) fixed))
         (list-formals (set-difference-eq all-formals fixed-formals))
         (forall-fn forall-fn-name ;(or forall-fn-name (pack$ 'map- fn))
                    )
         (atom-tests (wrap-list '(atom x) 'x list-formals))
         (null-tests (wrap-list '(null x) 'x list-formals))
         ;; true-listp variants
         (generic-forall (if true-listp 'generic-forall-p 'generic-forall))
         (cars (wrap-list '(first x) 'x list-formals))
         (recursive-call-args (wrap-targets '(rest x) 'x all-formals list-formals))
         (defun `(defund ,forall-fn (,@all-formals)
                   ,@(if declares ;todo: these are really declare-args?
                         `((declare ,@declares ;(xargs :normalize nil)
                                    ))
                       nil ;`((declare (xargs :normalize nil)))
                       )
                   (if ,(make-or atom-tests)
                       ,(if true-listp (make-and null-tests) t) ;if multiple list formals, require them all to be null
                     ;;use a let incase a formal appears more than once?
                     (and ,(sublis-var-simple (pairlis$ list-formals cars) term)
                          (,forall-fn ,@recursive-call-args)))))
         (theory `(:in-theory (union-theories '(,forall-fn) (theory 'minimal-theory))))
         (list-formal-count (len list-formals))

;for now, only generate these when there is exactly 1 list formal (any number of fixed formals is okay):
;theorem for iff?
         (theorems
          (if (not (equal 1 list-formal-count))
              nil ; no theorems if more than 1 list param
            (b* ((list-formal (first list-formals)) ;could have a function called only, which has a guard that the list if non-empty
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
                             (,generic-forall (lambda (,list-formal) (,forall-fn ,@fresh-formals)))))
                 (bindings-no-fresh `((generic-predicate (lambda (,list-formal) ,term))
                                      (,generic-forall (lambda (,list-formal) (,forall-fn ,@all-formals)))))
                 (theorems
                  `((defthm ,(pack$ forall-fn '-of-cons)
                      (equal (,forall-fn ,@(sublis-var-simple-lst
                                            (acons list-formal `(cons ,fresh-var ,list-formal) nil)
                                            all-formals))
                             (and ,(sublis-var-simple (acons list-formal fresh-var nil)
                                                  term)
                                  (,forall-fn ,@all-formals)))
                      :hints (("Goal" :use (:instance (:functional-instance ,(pack$ generic-forall '-of-cons) ,@bindings)
                                                      (a ,fresh-var)
                                                      (x ,list-formal)
                                                      ,@fixed-formal-bindings)
                               ,@theory)))

                    ;; TODO: Think about what name to use here (if the term representing the predicate is not a function call, the name is awkward).
                    (defthm ,(pack$ 'use- forall-fn '-for-car)
                      (implies (and (,forall-fn ,@all-formals)
                                    (consp (double-rewrite ,list-formal)))
                               ,(sublis-var-simple (acons list-formal `(car ,list-formal) nil)
                                               term))
                      :hints (("Goal" :use (:instance (:functional-instance ,(pack$ 'generic-predicate-of-car-when- generic-forall) ,@bindings)
                                                      (x ,list-formal)
                                                      ,@fixed-formal-bindings)
                               ,@theory)))

                    (defthm ,(pack$ 'use- forall-fn '-for-car-of-last)
                      (implies (and (,forall-fn ,@all-formals)
                                    (consp (double-rewrite ,list-formal)))
                               ,(sublis-var-simple (acons list-formal `(car (last ,list-formal)) nil)
                                               term))
                      :hints (("Goal" :use (:instance (:functional-instance ,(pack$ 'generic-predicate-of-car-of-last-when- generic-forall) ,@bindings)
                                                      (x ,list-formal)
                                                      ,@fixed-formal-bindings)
                               ,@theory)))

                    (defthm ,(pack$ forall-fn '-of-append)
                      (equal (,forall-fn ,@(sublis-var-simple-lst
                                            (acons list-formal `(append ,list-formal ,fresh-var) nil)
                                            all-formals))
                             (and (,forall-fn ,@(if true-listp
                                                    ;; for the true-list variant, wrap the list formal in true-list-fix
                                                    (sublis-var-simple-lst
                                                     (acons list-formal `(true-list-fix ,list-formal) nil)
                                                     all-formals)
                                                  all-formals))
                                  (,forall-fn ,@(sublis-var-simple-lst
                                                 (acons list-formal fresh-var nil)
                                                 all-formals))))
                      :hints (("Goal" :use (:instance (:functional-instance ,(pack$ generic-forall '-of-append) ,@bindings)
                                                      (y ,fresh-var)
                                                      (x ,list-formal)
                                                      ,@fixed-formal-bindings)
                               ,@theory)))

                    (defthm ,(pack$ forall-fn '-of-union-equal)
                      (equal (,forall-fn ,@(sublis-var-simple-lst
                                            (acons list-formal `(union-equal ,list-formal ,fresh-var) nil)
                                            all-formals))
                             (and (,forall-fn ,@(if true-listp
                                                    ;; for the true-list variant, wrap the list formal in true-list-fix
                                                    (sublis-var-simple-lst
                                                     (acons list-formal `(true-list-fix ,list-formal) nil)
                                                     all-formals)
                                                  all-formals))
                                  (,forall-fn ,@(sublis-var-simple-lst
                                                 (acons list-formal fresh-var nil)
                                                 all-formals))))
                      :hints (("Goal" :use (:instance (:functional-instance ,(pack$ generic-forall '-of-union-equal) ,@bindings)
                                                      (y ,fresh-var)
                                                      (x ,list-formal)
                                                      ,@fixed-formal-bindings)
                               ,@theory)))

                    (defthm ,(pack$ forall-fn '-when-not-consp)
                      (implies (not (consp (double-rewrite ,list-formal)))
                               ,(if true-listp
                                    `(equal (,forall-fn ,@all-formals)
                                            (equal nil ,list-formal))
                                  `(equal (,forall-fn ,@all-formals)
                                          t)))
                      :hints (("Goal" :use (:instance (:functional-instance ,(pack$ generic-forall '-when-not-consp) ,@bindings)
                                                      (x ,list-formal)
                                                      ,@fixed-formal-bindings)
                               ,@theory)))

                    ;; proven from the one just above
                    (defthm ,(pack$ forall-fn '-when-not-consp-cheap)
                      (implies (not (consp (double-rewrite ,list-formal)))
                               ,(if true-listp
                                    `(equal (,forall-fn ,@all-formals)
                                            (equal nil ,list-formal))
                                  `(equal (,forall-fn ,@all-formals)
                                          t)))
                      :rule-classes ((:rewrite :backchain-limit-lst (0)))
                      :hints (("Goal" :use ,(pack$ forall-fn '-when-not-consp)
                               :in-theory (theory 'minimal-theory))))

                    (defthm ,(pack$ forall-fn '-of-revappend)
                      (implies (and (,forall-fn ,@all-formals)
                                    (,forall-fn ,@(sublis-var-simple-lst
                                                   (acons list-formal fresh-var nil)
                                                   all-formals)))
                               (,forall-fn ,@(sublis-var-simple-lst
                                              (acons list-formal `(revappend ,list-formal ,fresh-var) nil)
                                              all-formals)))
                      :hints (("Goal" :use (:instance (:functional-instance ,(pack$ generic-forall '-of-revappend) ,@bindings)
                                                      (y ,fresh-var)
                                                      (x ,list-formal)
                                                      ,@fixed-formal-bindings)
                               ,@theory)))

                    (defthm ,(pack$ forall-fn '-of-cdr)
                      (implies (,forall-fn ,@all-formals)
                               (equal (,forall-fn ,@(sublis-var-simple-lst
                                                     (acons list-formal `(cdr ,list-formal) nil)
                                                     all-formals))
                                      t))
                      :hints (("Goal" :use (:instance (:functional-instance ,(pack$ generic-forall '-of-cdr) ,@bindings)
                                                      (x ,list-formal)
                                                      ,@fixed-formal-bindings)
                               ,@theory)))

                    ;;from here down, the fresh var name should be nXXX?
                    (defthm ,(pack$ forall-fn '-of-nthcdr)
                      (implies (,forall-fn ,@all-formals)
                               (equal (,forall-fn ,@(sublis-var-simple-lst
                                                     (acons list-formal `(nthcdr ,fresh-var ,list-formal) nil)
                                                     all-formals))
                                      t))
                      :hints (("Goal" :use (:instance (:functional-instance ,(pack$ generic-forall '-of-nthcdr) ,@bindings)
                                                      (n ,fresh-var)
                                                      (x ,list-formal)
                                                      ,@fixed-formal-bindings)
                               ,@theory)))

                    (defthm ,(pack$ forall-fn '-of-firstn)
                      (implies (,forall-fn ,@all-formals)
                               (equal (,forall-fn ,@(sublis-var-simple-lst
                                                     (acons list-formal `(firstn ,fresh-var ,list-formal) nil)
                                                     all-formals))
                                      t))
                      :hints (("Goal" :use (:instance (:functional-instance ,(pack$ generic-forall '-of-firstn) ,@bindings)
                                                      (n ,fresh-var)
                                                      (x ,list-formal)
                                                      ,@fixed-formal-bindings)
                               ,@theory)))

                    (defthm ,(pack$ forall-fn '-of-remove1-equal)
                      (implies (,forall-fn ,@all-formals)
                               (,forall-fn ,@(sublis-var-simple-lst
                                              (acons list-formal `(remove1-equal ,fresh-var ,list-formal) nil)
                                              all-formals)))
                      :hints (("Goal" :use (:instance (:functional-instance ,(pack$ generic-forall '-of-remove1-equal) ,@bindings)
                                                      (a ,fresh-var)
                                                      (x ,list-formal)
                                                      ,@fixed-formal-bindings)
                               ,@theory)))

                    (defthm ,(pack$ forall-fn '-of-remove-equal)
                      (implies (,forall-fn ,@all-formals)
                               (,forall-fn ,@(sublis-var-simple-lst
                                              (acons list-formal `(remove-equal ,fresh-var ,list-formal) nil)
                                              all-formals)))
                      :hints (("Goal" :use (:instance (:functional-instance ,(pack$ generic-forall '-of-remove-equal) ,@bindings)
                                                      (a ,fresh-var)
                                                      (x ,list-formal)
                                                      ,@fixed-formal-bindings)
                               ,@theory)))

                    (defthm ,(pack$ forall-fn '-of-last)
                      (implies (,forall-fn ,@all-formals)
                               (,forall-fn ,@(sublis-var-simple-lst
                                              (acons list-formal `(last ,list-formal) nil)
                                              all-formals)))
                      :hints (("Goal" :use (:instance (:functional-instance ,(pack$ generic-forall '-of-last) ,@bindings)
                                                      (x ,list-formal)
                                                      ,@fixed-formal-bindings)
                               ,@theory)))

                    (defthm ,(pack$ forall-fn '-of-take)
                      (implies (and (,forall-fn ,@all-formals)
                                    (<= ,fresh-var (len (double-rewrite ,list-formal))))
                               (equal (,forall-fn ,@(sublis-var-simple-lst
                                                     (acons list-formal `(take ,fresh-var ,list-formal) nil)
                                                     all-formals))
                                      t))
                      :hints (("Goal" :use (:instance (:functional-instance ,(pack$ generic-forall '-of-take) ,@bindings)
                                                      (n ,fresh-var)
                                                      (x ,list-formal)
                                                      ,@fixed-formal-bindings)
                               ,@theory)))

                    ,@(if true-listp
                          `((defthmd ,(pack$ 'true-listp-when- forall-fn) ;disabled by default
                              (implies (,forall-fn ,@all-formals)
                                       (true-listp ,list-formal))
                              :hints (("Goal" :use (:instance (:functional-instance ,(pack$ 'true-listp-when- generic-forall) ,@bindings)
                                                              (x ,list-formal)
                                                              ,@fixed-formal-bindings)
                                       ,@theory)))
                            (defthmd ,(pack$ 'true-listp-when- forall-fn '-forward)
                              (implies (,forall-fn ,@all-formals)
                                       (true-listp ,list-formal))
                              :rule-classes ((:forward-chaining))
                              :hints (("Goal" :use ,(pack$ 'true-listp-when- forall-fn) :in-theory nil))))
                        nil) ;this is not true in the non-true-listp case

                    (defthmd ,(pack$ forall-fn '-when-perm)
                      (implies (perm ,list-formal ,fresh-var)
                               (equal (,forall-fn ,@all-formals)
                                      ,(if true-listp
                                           `(and (true-listp ,list-formal)
                                                 (,forall-fn ,@(sublis-var-simple-lst
                                                                (acons list-formal `(true-list-fix ,fresh-var) nil)
                                                                all-formals)))
                                         `(,forall-fn ,@(sublis-var-simple-lst
                                                         (acons list-formal fresh-var nil)
                                                         all-formals)))))
                      :hints (("Goal" :use (:instance (:functional-instance ,(pack$ generic-forall '-when-perm) ,@bindings)
                                                      (x ,list-formal)
                                                      (y ,fresh-var)
                                                      ,@fixed-formal-bindings)
                               ,@theory)))

                    (defthm ,(pack$ forall-fn '-of-true-list-fix)
                      ,(if true-listp
                           `(implies (,forall-fn ,@all-formals)
                                     (,forall-fn ,@(sublis-var-simple-lst
                                                    (acons list-formal `(true-list-fix ,list-formal) nil)
                                                    all-formals)))
                         `(equal (,forall-fn ,@(sublis-var-simple-lst
                                                (acons list-formal `(true-list-fix ,list-formal) nil)
                                                all-formals))
                                 (,forall-fn ,@all-formals)))
                      :hints (("Goal" :use (:instance (:functional-instance ,(pack$ generic-forall '-of-true-list-fix) ,@bindings)
                                                      (x ,list-formal)
                                                      ,@fixed-formal-bindings)
                               ,@theory)))

                    ,@(and (not true-listp) ;; Suppress this in the true-listp case (its just not true)
                           ;;here we use the specific theorem proved just above (not a generic theorem)
                           `((defcong perm equal (,forall-fn ,@all-formals) ,(position-of list-formal all-formals)
                               :package :function
                               :hints (("Goal" :use (:instance ,(pack$ forall-fn '-when-perm)
;(,list-formal x)
                                                               (,fresh-var ,(pack-in-package-of-symbol forall-fn list-formal '-equiv))
                                                               ))))))

                    (defthm ,(pack$ 'use- forall-fn)
                      (implies (and (,forall-fn ,@(sublis-var-simple-lst (acons list-formal (pack$ 'free- list-formal) nil) all-formals))
                                    (memberp x ,(pack$ 'free- list-formal))
;                                    ,(cons-onto-all 'memberp (sublis-var-simple-lst (pairlis$ list-formals (pack-onto-all 'free list-formals)) all-formals)) ;overkill if there is oly 1 list formal
                                    )
                               ,(sublis-var-simple (acons list-formal 'x nil) term)) ;fixme what if term is not suitable to be a rewrite rule?
                      ;; avoid illegal rewrite rules (fixme print a warning) fixme: would like this test to apply to the macro-expanded body:
                      ,@(if (or (symbolp term) (member-eq (ffn-symb term) '(if or
;and ;I think and is actually okay
                                                                               )))
                            '(:rule-classes nil) nil)
;fffixme think about fresh formals!
                      :hints (("Goal" :do-not-induct t
                               :use (:instance (:functional-instance ,(pack$ 'generic-predicate-when- generic-forall) ,@bindings-no-fresh)
                                               (free ,(pack$ 'free- list-formal))
;                                                      (x ,list-formal)
;,@fixed-formal-bindings
                                               )
                               ,@theory)))

                    ;; same as above but with hyps reordered
                    (defthm ,(pack$ 'use- forall-fn "-2")
                      (implies (and (memberp x ,(pack$ 'free- list-formal))
                                    (,forall-fn ,@(sublis-var-simple-lst (acons list-formal (pack$ 'free- list-formal) nil) all-formals))
;                                    ,(cons-onto-all 'memberp (sublis-var-simple-lst (pairlis$ list-formals (pack-onto-all 'free list-formals)) all-formals)) ;overkill if there is oly 1 list formal
                                    )
                               ,(sublis-var-simple (acons list-formal 'x nil) term)) ;fixme what if term is not suitable to be a rewrite rule?
                      ;; avoid illegal rewrite rules (fixme print a warning) fixme: would like this test to apply to the macro-expanded body:
                      ,@(if (or (symbolp term) (member-eq (ffn-symb term) '(if or
;and ;I think and is actually okay
                                                                               )))
                            '(:rule-classes nil) nil)
                      ;; same hints as above:
                      :hints (("Goal" :do-not-induct t
                               :use (:instance (:functional-instance ,(pack$ 'generic-predicate-when- generic-forall) ,@bindings-no-fresh)
                                               (free ,(pack$ 'free- list-formal))
;                                                      (x ,list-formal)
;,@fixed-formal-bindings
                                               )
                               ,@theory)))
                    (defthm ,(pack$ forall-fn '-of-add-to-set-equal)
                      (equal (,forall-fn ,@(sublis-var-simple-lst
                                            (acons list-formal `(add-to-set-equal ,fresh-var ,list-formal) nil)
                                            all-formals))
                             (and ,(sublis-var-simple (acons list-formal fresh-var nil)
                                                  term)
                                  (,forall-fn ,@all-formals)))
                      :hints (("Goal" :use (:instance (:functional-instance ,(pack$ generic-forall '-of-add-to-set-equal) ,@bindings)
                                                      (a ,fresh-var)
                                                      (x ,list-formal)
                                                      ,@fixed-formal-bindings)
                               ,@theory))))))
              theorems))))
    (manage-screen-output ;todo: expand manage-screen-output here?
     verbose
     `(progn ,defun
             ,@theorems
             (value-triple ',forall-fn)))))

(defun defforall-simple-fn (pred name guard guard-hints true-listp verbose)
  (declare (xargs :mode :program))
  (defforall-fn
    (or name ;use name if supplied
        (pack$ 'all- pred) ;;(pack-in-package-of-symbol pred 'all- fn) ;this was causing things to be put in the common lisp package, which was a problem for all-rationalp  maybe use ACL2 if the symbol is in that package?
        )
    '(x) ;fixme: would really like this to be "xs" or "vals" or something indicating that this is a list
    `(,pred x)
    nil   ;no fixed args
    nil   ;no declares
    guard
    guard-hints
    true-listp
    verbose
    ))

;simple version for the common case of mapping a unary predicate over a single list
(defmacro defforall-simple (pred ;the unary predicate to apply to each element in the list
                            &key
                            (name 'nil) ;the name to use for the generated function (defaults to all- followed by pred)
                            (guard 'nil)
                            (guard-hints 'nil) ;todo: add a test of this
                            (true-listp 'nil)
                            (verbose 'nil)
                            )
  (defforall-simple-fn pred name guard guard-hints true-listp verbose))

;See examples in defforall-tests.lisp.  :FIXED indicates which formals are fixed  All other formals are lists that get cdred down.
;add more options?
;
(defmacro defforall (name all-formals term &key
                          (fixed 'nil)
                          (declares 'nil)
                          (guard 'nil)
                          (guard-hints 'nil) ;todo: add a test of this
                          (true-listp 'nil)
                          (verbose 'nil))
  (declare (xargs :guard (member-eq verbose '(t nil)))) ;for now, since it's passed to manage-screen-output without being evaluated
  (defforall-fn name all-formals term fixed declares guard guard-hints true-listp verbose))
