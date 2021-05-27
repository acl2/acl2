; Utility to make a function that applies a function to each item in a list
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

;Defmap map be similar to the (unfortunately named) defprojection in
;std/util/defprojection.lisp.

;TODO: prove a generic map of map theorem (for any two defmaps?)

(include-book "generics-utilities")
(include-book "kestrel/lists-light/reverse-list-def" :dir :system)
(include-book "kestrel/lists-light/firstn-def" :dir :system)
(include-book "kestrel/utilities/doublets2" :dir :system)
(include-book "../utilities/fresh-names")
(include-book "kestrel/utilities/make-or" :dir :system)
(include-book "kestrel/utilities/user-interface" :dir :system) ;for manage-screen-output (TODO: reduce the stuff included in this book)
;(local (include-book "coi/lists/memberp" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/firstn" :dir :system))


; x is a list - should we require it to be a true-list? option to call endp if so?
;should i be using (not (consp x)) instead of (atom x) for speed?
(defund generic-map (x)
  (declare (xargs :guard (true-listp x)))
  (if (atom x)
      nil ; or should we return x? make it an option to defmap and have two generic functions?
    (cons (generic-fn (car x))
          (generic-map (cdr x)))))

(defthmd generic-map-opener
  (implies (consp (double-rewrite x))
           (equal (generic-map x)
                  (cons (generic-fn (car (double-rewrite x)))
                        (generic-map (cdr x)))))
  :hints (("Goal" :in-theory (enable generic-map))))

(defthm generic-map-of-cons
  (equal (generic-map (cons a x))
         (cons (generic-fn a)
               (generic-map x)))
  :hints (("Goal" :in-theory (enable generic-map))))

(defthm generic-map-of-append
  (equal (generic-map (append x y))
         (append (generic-map x)
                 (generic-map y)))
  :hints (("Goal" :in-theory (enable generic-map))))

(defthm car-of-generic-map
  (equal (car (generic-map x))
         (if (consp (double-rewrite x))
             (generic-fn (car (double-rewrite x)))
           nil))
  :hints (("Goal" :in-theory (enable generic-map))))

(defthm cdr-of-generic-map
  (equal (cdr (generic-map x))
         (generic-map (cdr x)))
  :hints (("Goal" :in-theory (enable generic-map))))

(defthm len-of-generic-map
  (equal (len (generic-map x))
         (len (double-rewrite x)))
  :hints (("Goal" :in-theory (enable generic-map))))

(defthm consp-of-generic-map
  (equal (consp (generic-map x))
         (consp (double-rewrite x)))
  :hints (("Goal" :in-theory (enable generic-map))))

(defthm generic-map-iff
  (iff (generic-map x)
       (consp (double-rewrite x)))
  :hints (("Goal" :in-theory (enable generic-map))))

(defthm generic-map-when-not-consp
  (implies (not (consp (double-rewrite x)))
           (equal (generic-map x)
                  nil))
  :hints (("Goal" :in-theory (enable generic-map))))

(defthm firstn-of-generic-map
  (equal (firstn n (generic-map x))
         (generic-map (firstn n (double-rewrite x))))
  :hints (("Goal" :in-theory (e/d (generic-map firstn) (firstn-becomes-take-gen)))))

(defthm take-of-generic-map
  (implies (<= n (len (double-rewrite x)))
           (equal (take n (generic-map x))
                  (generic-map (take n (double-rewrite x)))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (generic-map take) (;anti-subrange
                                                   )))))

(defthm nth-of-generic-map
  (implies (natp n)
           (equal (nth n (generic-map x))
                  (if (< n (len x))
                      (generic-fn (nth n x))
                    nil)))
  :hints (("Goal" :in-theory (e/d (generic-map nth) (;anti-subrange
                                                     ;;nth-of-cdr
                                                     )))))

(defthm nthcdr-of-generic-map
  (equal (nthcdr n (generic-map x))
         (generic-map (nthcdr n x)))
  :hints (("Goal" :in-theory (e/d (generic-map nthcdr) (;NTHCDR-OF-CDR-COMBINE NTHCDR-OF-CDR-COMBINE-STRONG
                                                        )))))

(defthm true-listp-of-generic-map
  (equal (true-listp (generic-map x))
         t)
  :hints (("Goal" :in-theory (e/d (generic-map) ()))))

(defthm generic-map-of-nil
  (equal (generic-map nil)
         nil)
  :hints (("Goal" :in-theory (e/d (generic-map) ()))))

(defthm generic-map-of-true-list-fix
  (equal (generic-map (true-list-fix x))
         (generic-map x))
  :hints (("Goal" :in-theory (enable generic-map))))

;; subsequencep-equal not added yet
;; (defthm subsequencep-equal-generic-map-cons
;;   (implies (subsequencep-equal (generic-map x) (generic-map y))
;;            (subsequencep-equal (generic-map (cons a x)) (generic-map (cons a y)))))
;; (defthm subsequencep-equal-generic-map-cdr
;;   (implies (subsequencep-equal (generic-map x) (generic-map y))
;;            (subsequencep-equal (generic-map (cdr x)) (generic-map (cdr y)))))
;; (defthm subsequencep-equal-generic-map-cdr
;;   (implies (subsequencep-equal (generic-map (cdr x)) (generic-map (cdr y)))
;;            (subsequencep-equal (generic-map x) (generic-map y))))
;; ;; TODO: Prove
;; (defthm subsequencep-equal-generic-map
;;   (implies (subsequencep-equal x y)
;;            (subsequencep-equal (generic-map x) (generic-map y)))
;;   :hints (("Goal" :in-theory (enable generic-map))))

;fixed is a single symbol or a list of symbols
;formals in all-formals but not in list-formals are fixed formals
;it is an error to have no list formals - check for that?
(defun defmap-fn (map-fn-name all-formals term fixed declares theorems verbose)
  (declare (xargs :guard (and (symbolp map-fn-name)
                              (symbol-listp all-formals)
                              ;; guard on term?
                              (or (eq fixed nil)
                                  (if (symbolp fixed)
                                      (member-eq fixed all-formals)
                                    (subsetp-eq fixed all-formals))) ;t ;(pseudo-termp term) ;was too strong, since macros won't be expanded yet.
                              (booleanp verbose))
                  :verify-guards nil)) ;add more guards
  (let* ((fixed-formals (if (and (symbolp fixed) fixed) (list fixed) fixed))
         (list-formals (set-difference-eq all-formals fixed-formals)) ;luckily, this preserves the order
         (map-fn map-fn-name ;(or map-fn-name (pack$ 'map- fn))
                 )
         (atom-tests (wrap-list '(atom x) 'x list-formals))
         (cars-of-list-formals (wrap-list '(car x) 'x list-formals)) ;use wrap-all
         (recursive-call-args (wrap-targets '(cdr x) 'x all-formals list-formals))
         (defun `(defund ,map-fn (,@all-formals)
                   ,@(and declares `((declare ,@declares)))
                   (if ,(make-or atom-tests)
                       nil ;; empty list
                     ;;use a let in case a formal appears more than once?
                     (cons ,(sublis-var-simple (pairlis$ list-formals cars-of-list-formals) term)
                           (,map-fn ,@recursive-call-args)))))
         ;;fixme problems occur when we map a predicate that is known to be t, if we don't include the :type-prescription rule for the predicate here, but that is awkward:
         (theory `(:in-theory (union-theories '((:definition ,map-fn)) (theory 'minimal-theory)))) ;does this allow for induction??
         (list-formal-count (len list-formals))

;for now, only generate these when there is exactly 1 list formal (any number of fixed formals is okay):
;theorem for iff?
         (defthms
           (and theorems
                (equal 1 list-formal-count)
                (let* ((list-formal (first list-formals))
                       (fresh-var (fresh-var-name list-formal 0 all-formals))
                       ;;have each name reflect the formal it's replacing?
                       (fresh-vars (fresh-var-names (len fixed-formals) 'tmp (cons fresh-var all-formals)))
                       (fresh-var-alist (pairlis$ fixed-formals fresh-vars) )
                       (fresh-formals (sublis-var-simple-lst fresh-var-alist all-formals))
                       (fresh-term (sublis-var-simple fresh-var-alist term))
                       (fixed-formal-bindings (make-doublets fresh-vars fixed-formals))

                       (bindings `((generic-fn (lambda (,list-formal) ,fresh-term))
                                   (generic-map (lambda (,list-formal) (,map-fn ,@fresh-formals))))))
                  `((defthm ,(pack$ map-fn '-of-nil)
                      (equal (,map-fn ,@(sublis-var-simple-lst
                                         (acons list-formal *nil* nil)
                                         all-formals))
                             nil)
                      :hints (("Goal" :use (:instance (:functional-instance generic-map-of-nil ,@bindings
                                                                            )
;(a ,fresh-var)
;(x ,list-formal)
                                                      ,@fixed-formal-bindings)
                               ,@theory)))

                    (defthm ,(pack$ map-fn '-of-cons)
                      (equal (,map-fn ,@(sublis-var-simple-lst
                                         (acons list-formal `(cons ,fresh-var ,list-formal) nil)
                                         all-formals))
                             (cons ,(sublis-var-simple (acons list-formal fresh-var nil)
                                                   term)
                                   (,map-fn ,@all-formals)))
                      :hints (("Goal" :use (:instance (:functional-instance generic-map-of-cons ,@bindings)
                                                      (a ,fresh-var)
                                                      (x ,list-formal)
                                                      ,@fixed-formal-bindings)
                               ,@theory)))

                    (defthm ,(pack$ map-fn '-of-true-list-fix)
                      (equal (,map-fn ,@(sublis-var-simple-lst
                                         (acons list-formal `(true-list-fix ,list-formal) nil)
                                         all-formals))
                             (,map-fn ,@all-formals))
                      :hints (("Goal" :use (:instance (:functional-instance generic-map-of-true-list-fix ,@bindings)
                                                      (x ,list-formal)
                                                      ,@fixed-formal-bindings)
                               ,@theory)))

                    (defthmd ,(pack$ map-fn '-opener)
                      (implies (consp (double-rewrite ,list-formal))
                               (equal (,map-fn ,@all-formals)
                                      (cons ,(sublis-var-simple (acons list-formal `(car (double-rewrite ,list-formal)) nil)
                                                            term)
                                            (,map-fn ,@(sublis-var-simple-lst (acons list-formal `(cdr ,list-formal) nil)
                                                                          all-formals)))))
                      :hints (("Goal" :use (:instance (:functional-instance generic-map-opener ,@bindings)
;                                                      (a ,fresh-var)
                                                      (x ,list-formal)
                                                      ,@fixed-formal-bindings)
                               ,@theory)))

                    (defthm ,(pack$ map-fn '-of-append)
                      (equal (,map-fn ,@(sublis-var-simple-lst
                                         (acons list-formal `(append ,list-formal ,fresh-var) nil)
                                         all-formals))
                             (append (,map-fn ,@all-formals)
                                     (,map-fn ,@(sublis-var-simple-lst
                                                 (acons list-formal fresh-var nil)
                                                 all-formals))))
                      :hints (("Goal" :use (:instance (:functional-instance generic-map-of-append ,@bindings)
                                                      (y ,fresh-var)
                                                      (x ,list-formal)
                                                      ,@fixed-formal-bindings)
                               ,@theory)))

                    (defthm ,(pack$ 'car-of- map-fn)
                      (equal (car (,map-fn ,@all-formals))
                             (if (consp (double-rewrite ,list-formal))
                                 ,(sublis-var-simple (acons list-formal `(car (double-rewrite ,list-formal)) nil) term)
                               nil))
                      :hints (("Goal" :use (:instance (:functional-instance car-of-generic-map ,@bindings)
                                                      (x ,list-formal)
                                                      ,@fixed-formal-bindings)
                               ,@theory)))

                    (defthm ,(pack$ 'cdr-of- map-fn)
                      (equal (cdr (,map-fn ,@all-formals))
                             (,map-fn ,@(sublis-var-simple-lst
                                         (acons list-formal `(cdr ,list-formal) nil)
                                         all-formals)))
                      :hints (("Goal" :use (:instance (:functional-instance cdr-of-generic-map ,@bindings)
                                                      (x ,list-formal)
                                                      ,@fixed-formal-bindings)
                               ,@theory)))

                    (defthm ,(pack$ 'len-of- map-fn)
                      (equal (len (,map-fn ,@all-formals))
                             (len (double-rewrite ,list-formal)))
                      :hints (("Goal" :use (:instance (:functional-instance len-of-generic-map ,@bindings)
                                                      (x ,list-formal)
                                                      ,@fixed-formal-bindings)
                               ,@theory)))

                    (defthm ,(pack$ 'consp-of- map-fn)
                      (equal (consp (,map-fn ,@all-formals))
                             (consp (double-rewrite ,list-formal)))
                      :hints (("Goal" :use (:instance (:functional-instance consp-of-generic-map ,@bindings)
                                                      (x ,list-formal)
                                                      ,@fixed-formal-bindings)
                               ,@theory)))

                    (defthm ,(pack$ map-fn '-iff)
                      (iff (,map-fn ,@all-formals)
                           (consp (double-rewrite ,list-formal)))
                      :hints (("Goal" :use (:instance (:functional-instance generic-map-iff ,@bindings)
                                                      (x ,list-formal)
                                                      ,@fixed-formal-bindings)
                               ,@theory)))

                    (defthm ,(pack$ 'true-listp-of- map-fn)
                      (equal (true-listp (,map-fn ,@all-formals))
                             't)
                      :hints (("Goal" :use (:instance (:functional-instance true-listp-of-generic-map ,@bindings)
                                                      (x ,list-formal)
                                                      ,@fixed-formal-bindings)
                               ,@theory)))

                    (defthm ,(pack$ 'firstn-of- map-fn)
                      (equal (firstn ,fresh-var (,map-fn ,@all-formals))
                             (,map-fn ,@(sublis-var-simple-lst
                                         (acons list-formal `(firstn ,fresh-var (double-rewrite,list-formal)) nil)
                                         all-formals)))
                      :hints (("Goal" :use (:instance (:functional-instance firstn-of-generic-map ,@bindings)
                                                      (x ,list-formal)
                                                      (n ,fresh-var)
                                                      ,@fixed-formal-bindings)
                               ,@theory)))

                    (defthm ,(pack$ 'take-of- map-fn)
                      (implies (<= ,fresh-var (len (double-rewrite ,list-formal)))
                               (equal (take ,fresh-var (,map-fn ,@all-formals))
                                      (,map-fn ,@(sublis-var-simple-lst
                                                  (acons list-formal `(take ,fresh-var (double-rewrite ,list-formal)) nil)
                                                  all-formals))))
                      :hints (("Goal" :use (:instance (:functional-instance take-of-generic-map ,@bindings)
                                                      (x ,list-formal)
                                                      (n ,fresh-var)
                                                      ,@fixed-formal-bindings)
                               ,@theory)))

                    (defthm ,(pack$ 'nth-of- map-fn)
                      (implies (natp ,fresh-var)
                               (equal (nth ,fresh-var (,map-fn ,@all-formals))
                                      (if (< ,fresh-var (len (double-rewrite ,list-formal)))
                                          ,(sublis-var-simple (acons list-formal `(nth ,fresh-var (double-rewrite ,list-formal)) nil) term)
                                        'nil)))
                      :hints (("Goal" :use (:instance (:functional-instance nth-of-generic-map ,@bindings)
                                                      (x ,list-formal)
                                                      (n ,fresh-var)
                                                      ,@fixed-formal-bindings)
                               ,@theory)))

                    (defthm ,(pack$ 'nthcdr-of- map-fn)
                      (equal (nthcdr ,fresh-var (,map-fn ,@all-formals))
                             (,map-fn ,@(sublis-var-simple-lst
                                         (acons list-formal `(nthcdr ,fresh-var ,list-formal) nil)
                                         all-formals)))
                      :hints (("Goal" :use (:instance (:functional-instance nthcdr-of-generic-map ,@bindings)
                                                      (x ,list-formal)
                                                      (n ,fresh-var)
                                                      ,@fixed-formal-bindings)
                               ,@theory)))
                    )))))
    (manage-screen-output
     verbose
     `(progn ,defun
             ,@defthms
             (value-triple ',map-fn-name)))))

;fixme keep this up-to-date
;does not include the opener rule
;fixme what about name clashes (which eventually i'd like defmap to avoid).  maybe defmap should lay down a defconst with the actual rules names generated
(defun map-runes (map-fn)
  (declare (xargs :guard (symbolp map-fn)))
  (list `(:rewrite ,(pack$ map-fn '-of-nil))
        `(:rewrite ,(pack$ map-fn '-of-cons))
        `(:rewrite ,(pack$ map-fn '-of-true-list-fix))
        `(:rewrite ,(pack$ map-fn '-of-append))
        `(:rewrite ,(pack$ 'car-of- map-fn))
        `(:rewrite ,(pack$ 'cdr-of- map-fn))
        `(:rewrite ,(pack$ 'len-of- map-fn))
        `(:rewrite ,(pack$ 'consp-of- map-fn))
        `(:rewrite ,(pack$ map-fn '-iff))
        `(:rewrite ,(pack$ 'true-listp-of- map-fn))
        `(:rewrite ,(pack$ 'firstn-of- map-fn))
        `(:rewrite ,(pack$ 'take-of- map-fn))
        `(:rewrite ,(pack$ 'nth-of- map-fn))
        `(:rewrite ,(pack$ 'nthcdr-of- map-fn))))

;ffixme what about guards, defun mode, other xargs(?), and the parameter names?
;consider storing the binding between the new function and its body in a table, to support reasoning about
;higher order functions?
;extend this to take an n-ary function (or lambda?) with lists in any or all arguments?
;example call: (defmap-simple natp)
;option to skip the theorems (but have a way to prove them later?)
;ffixme can fn be a macro?
(defmacro defmap-simple (fn &key
                            (name 'nil)
                            (theorems 't)
                            (verbose 'nil))
  (declare (xargs :guard (member-eq verbose '(t nil)))) ;for now, since it's passed to manage-screen-output without being evaluated
  (defmap-fn (or name (pack$ 'map- fn)) '(x) `(,fn x) nil nil theorems verbose))

;; See tests in defmap-tests.lisp

;add more options?
;this requires that all the list formals come first - gross?
(defmacro defmap (name all-formals term &key (fixed 'nil) (declares 'nil) (theorems 't) (verbose 'nil))
  (declare (xargs :guard (member-eq verbose '(t nil)))) ;for now, since it's passed to manage-screen-output without being evaluated
  (defmap-fn name all-formals term fixed declares theorems verbose))

;fixme this: (local (defmap map-inc (x) (+ x 1)))
;causes an error because the 1 is not quoted.  should trans the term first?

;;in the case of more than 1 list-formal, if any list runs out, the computation finishes
;;ffixme what happens to the theorems when there's more than 1 list param?
