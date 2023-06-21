; lift-iso: A transformation to lift an isomorphism to a predicate that is true
; of some structure one or more components is subject to the original isomprphism
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Main Author: Stephen Westfold (westfold@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "APT")


(include-book "utilities/deftransformation")
(include-book "utilities/names")
(include-book "kestrel/std/system/irecursivep-plus" :dir :system)
(include-book "kestrel/std/util/defiso" :dir :system)
(include-book "kestrel/utilities/negate-form" :dir :system)
(include-book "kestrel/utilities/reconstruct-macros" :dir :system)
(include-book "kestrel/utilities/make-or-nice" :dir :system)
(include-book "kestrel/utilities/make-and-nice" :dir :system)
(include-book "kestrel/std/system/ubody" :dir :system)
(include-book "kestrel/untranslated-terms/untranslated-terms-old" :dir :system)

(set-state-ok t)

;; Support fns

(program)

(defun get-def (fn wrld ev)

; We return the definition of fn in wrld, if any, without the leading defun.
; If there is no such definition, we return nil.

; Ev is optional.  If supplied, it is the value of (get-event fn wrld), which
; ideally is non-nil (else the call of get-event below will duplicate the work
; to find nil).

; This code is based on the definition of guard-raw in the ACL2 sources.

  (let ((ev (or ev (get-event fn wrld))))
    (case (car ev)
      (defun (cdr ev))
      (mutual-recursion (assoc-eq fn (strip-cdrs (cdr ev))))
      (verify-termination-boot-strap
       (cdr (cltl-def-from-name fn wrld)))
      (otherwise nil))))

;; Temporarily renamed to avoid conflict with fn-ubody
(defun fn-ubody1 (fn fn-body wrld ev)

; Return a body of fn, preferably an untranslated body, else an unnormalized
; body.  Fn-body may be nil; otherwise it is an unnormalized body of fn in
; wrld, (body fn nil wrld).  Ev may be nil; otherwise it the value of (get-def
; fn wrld nil).

  (or (car (last (get-def fn wrld ev)))
      fn-body
      (body fn nil wrld)))
(logic)

(defun iso-info-elt-p (iso-info)
  (declare (xargs :guard t))
  (and (symbol-listp iso-info)
       (> (len iso-info) 4)))

(define iso-info-iso-name ((iso-info defmapping-infop))
  (let ((iso-rec (acl2::defmapping-info->call$ iso-info)))
    (case-match iso-rec
      (('defiso iso-name . &)
       iso-name))))

(define iso-info-old ((iso-info defmapping-infop))
  :returns (pred-name pseudo-termfnp :hyp :guard)
  (acl2::defmapping-info->doma iso-info))

(define iso-info-new ((iso-info defmapping-infop))
  :returns (pred-name pseudo-termfnp :hyp :guard)
  (acl2::defmapping-info->domb iso-info))

(define iso-info-pred ((iso-info defmapping-infop)
                       (new-p booleanp))
  :returns (pred-name pseudo-termfnp :hyp :guard)
  (if new-p
      (iso-info-new iso-info)
    (iso-info-old iso-info)))

(define iso-info-new-to-old ((iso-info defmapping-infop))
  :returns (pred-name pseudo-termfnp :hyp :guard)
  (acl2::defmapping-info->beta iso-info))

(define iso-info-old-to-new ((iso-info defmapping-infop))
  :returns (pred-name pseudo-termfnp :hyp :guard)
  (acl2::defmapping-info->alpha iso-info))

(define iso-info-convert-fn ((iso-info defmapping-infop)
                             (new-to-old-p booleanp))
  :returns (pred-name pseudo-termfnp :hyp :guard)
  (if new-to-old-p
      (iso-info-new-to-old iso-info)
    (iso-info-old-to-new iso-info)))

(define iso-info-alist-p (iso-infos)
  :guard t
  (or (null iso-infos)
      (and (consp iso-infos)
           (consp (first iso-infos))
           (symbolp (caar iso-infos))
           (defmapping-infop (cdar iso-infos))
           (iso-info-alist-p (rest iso-infos))))
  ///
  (defthm true-listp-iso-info-alist-p
    (implies (iso-info-alist-p l)
             (true-listp l))
    :rule-classes (:forward-chaining))
  (defthm iso-info-alist-p-car
    (implies (and (iso-info-alist-p iso-infos)
                  (consp iso-infos))
             (consp (car iso-infos))))
  (defthm iso-info-alist-p-caar
    (implies (and (iso-info-alist-p iso-infos)
                  (consp iso-infos))
             (symbolp (caar iso-infos))))
  (defthm iso-info-alist-p-cdar
    (implies (and (iso-info-alist-p iso-infos)
                  (consp iso-infos))
             (defmapping-infop (cdar iso-infos))))
  (defthm iso-info-alist-p-cdr
    (implies (iso-info-alist-p iso-infos)
             (iso-info-alist-p (cdr iso-infos))))
  (defthm iso-info-alist-p-alistp
    (implies (iso-info-alist-p l)
             (alistp l)))
  (defthm iso-info-alist-p-append
    (implies (and (iso-info-alist-p iso-infos)
                  (symbolp s)
                  (defmapping-infop o))
             (iso-info-alist-p (append iso-infos (list (cons s o))))))
) ; iso-info-alist-p

(define iso-info-fnp ((fn symbolp) (iso-infos iso-info-alist-p))
  (if (atom iso-infos)
      nil
    (or (let ((iso-info (cdar iso-infos)))
          (or (eq fn (iso-info-new-to-old iso-info))
              (eq fn (iso-info-old-to-new iso-info))
              (eq fn (iso-info-old iso-info))
              (eq fn (iso-info-new iso-info))))
        (iso-info-fnp fn (rest iso-infos)))))


(define renaming-from-iso-infos ((iso-infos iso-info-alist-p))
  :returns (subst alistp)
  :verify-guards nil
  (if (endp iso-infos)
      ()
    (acons (iso-info-old (cdar iso-infos))
           (iso-info-new (cdar iso-infos))
           (renaming-from-iso-infos (cdr iso-infos)))))

(verify-guards renaming-from-iso-infos
  :hints (("Goal" :in-theory (enable iso-info-alist-p))))


(define iso-convert-theorems ((iso-infos iso-info-alist-p))
  ;:returns (thms symbol-listp)
  :mode :program
  (if (endp iso-infos)
      ()
    (b* (((defmapping-info iso) (cdar iso-infos))
         (r-thms (iso-convert-theorems (rest iso-infos))))
      (list* iso.alpha-image
             iso.beta-image
             iso.beta-of-alpha
             iso.alpha-of-beta
             iso.alpha-injective
             iso.beta-injective
             (if iso.alpha-guard
                 (list* iso.alpha-guard iso.beta-guard r-thms)
               r-thms)))))

(define lookup-iso-info ((f symbolp) (iso-infos iso-info-alist-p))
  (cdr (assoc f iso-infos))
  ///
  (defthm defmapping-infop-lookup-iso-info
    (implies (and (iso-info-alist-p iso-infos)
                  (lookup-iso-info f iso-infos))
             (defmapping-infop (lookup-iso-info f iso-infos))))
)

(define lookup-osi-info ((f symbolp) (iso-infos iso-info-alist-p))
  (if (atom iso-infos)
      nil
    (if (equal f (iso-info-new (cdar iso-infos)))
        (cdar iso-infos)
      (lookup-osi-info f (rest iso-infos))))
  ///
  (defthm defmapping-infop-lookup-osi-info
    (implies (and (iso-info-alist-p iso-infos)
                  (lookup-osi-info f iso-infos))
             (defmapping-infop (lookup-osi-info f iso-infos))))
)

(define source-of-iso-p ((f symbolp) (iso-infos iso-info-alist-p))
  (assoc f iso-infos))

(define target-of-iso-p ((f symbolp) (iso-infos iso-info-alist-p))
  (and (consp iso-infos)
       (or (equal f (iso-info-new (cdar iso-infos)))
           (target-of-iso-p f (rest iso-infos)))))

(define iso-info-f-pred ((f symbolp) (iso-infos iso-info-alist-p) (new-p booleanp))
  (let ((iso-info (lookup-iso-info f iso-infos)))
    (if iso-info
        (if new-p
            (iso-info-new iso-info)
          (iso-info-old iso-info))
      (raise "Shouldn't happen! ~x0 not in~%~x1" f iso-infos))))

(define symbolp-or-lambdap (x)
  :returns (b booleanp)
  :enabled t
  (or (symbolp x)
      (and (consp x)
           (equal (car x) 'lambda)
           (equal (len x) 3))))

(define theorem-names (thms)
  :returns (l symbol-listp)
  (if (atom thms)
      ()
    (cons (and (true-listp (car thms))
               (symbolp (second (car thms)))
               (second (car thms)))
          (theorem-names (cdr thms)))))


(defconst *unhandled-case* '*unhandled-case*)
(defconst *unknown-value* '*unknown-value*)

(defines merge-convert-exprs-for-and-n
  (define merge-convert-exprs-for-and (exprs)
    (if (atom exprs)
        *unknown-value*
      (if (atom (cdr exprs))
          (car exprs)
        (merge-2-convert-exprs-for-and (car exprs) (merge-convert-exprs-for-and (cdr exprs))))))
  (define merge-2-convert-exprs-for-and (e1 e2)
    (let* ((pr (list e1 e2)))
      (case-match pr
        ((('CONS c1a c2a)
          ('CONS c1b c2b))
         `(cons ,(merge-2-convert-exprs-for-and c1a c1b)
                ,(merge-2-convert-exprs-for-and c2a c2b)))
        ((!*unknown-value* e2)
         e2)
        ((e1 !*unknown-value*)
         e1)
        ((!*unhandled-case* e2)         ; These 2 cases require more thought
         e2)
        ((e1 !*unhandled-case*)
         e1)
        ((('CONS & &)
          &)
         e1)
        ((&
          ('CONS & &))
         e2)
        (& (if (equal e1 e2)
               e1
             *unhandled-case*)))))
)  ; merge-convert-exprs-for-and-n

(define merge-convert-exprs-for-or (t1 e1 e2)
  (if (or (equal e1 *unhandled-case*)
          (equal e2 *unhandled-case*))
      *unhandled-case*
    `(if ,t1 ,e1 ,e2)))

(defines fill-in-unknowns-by-old
  (define fill-in-unknowns-by-old (tm old-val-tm)
    (case-match tm
      (!*unknown-value* old-val-tm)
      (('CONS x y)
       `(cons ,(fill-in-unknowns-by-old x `(car ,old-val-tm))
              ,(fill-in-unknowns-by-old y `(cdr ,old-val-tm))))
      (('IF p x y)
       `(if ,p ,(fill-in-unknowns-by-old x old-val-tm)
          ,(fill-in-unknowns-by-old y old-val-tm)))
      (('COND . cond-pairs)
       `(cond ,@(fill-in-unknowns-by-old-cond-pairs cond-pairs old-val-tm)))
      (& tm)))
  (define fill-in-unknowns-by-old-cond-pairs (cond-pairs old-val-tm)
    (if (or (atom cond-pairs)
            ; Shouldn't happen
            (not (and (consp (car cond-pairs))
                      (consp (cdar cond-pairs)))))
        nil
      (cons (list (fill-in-unknowns-by-old (first (car cond-pairs))
                                           old-val-tm)
                  (fill-in-unknowns-by-old (second (car cond-pairs))
                                           old-val-tm))
            (fill-in-unknowns-by-old-cond-pairs (cdr cond-pairs) old-val-tm)))))

(define partial-cons-form-from-destructors (d-term c-term (formal variablep))
  (if (equal d-term formal)
      c-term
    (if (not (= 2 (len d-term)))
        *unknown-value*
      (case (car d-term)
        ((CAR FIRST HEAD)
         (partial-cons-form-from-destructors (cadr d-term) `(cons ,c-term ,*unknown-value*) formal))
        ((CDR REST)
         (partial-cons-form-from-destructors (cadr d-term) `(cons ,*unknown-value* ,c-term) formal))
        (CAAR
          (partial-cons-form-from-destructors (cadr d-term) `(cons (cons ,c-term ,*unknown-value*)
                                                                   ,*unknown-value*)
                                              formal))
        ((CADR SECOND)
          (partial-cons-form-from-destructors (cadr d-term) `(cons ,*unknown-value*
                                                                   (cons ,c-term ,*unknown-value*))
                                              formal))
        (CDAR
          (partial-cons-form-from-destructors (cadr d-term) `(cons (cons ,*unknown-value* ,c-term)
                                                                   ,*unknown-value*)
                                              formal))
        (CDDR
          (partial-cons-form-from-destructors (cadr d-term) `(cons ,*unknown-value*
                                                                   (cons ,*unknown-value* ,c-term))
                                              formal))
        (CAAAR
          (partial-cons-form-from-destructors (cadr d-term) `(cons (cons (cons ,c-term ,*unknown-value*)
                                                                         ,*unknown-value*)
                                                                   ,*unknown-value*)
                                              formal))
        (CDAAR
          (partial-cons-form-from-destructors (cadr d-term) `(cons (cons (cons ,*unknown-value* ,c-term)
                                                                         ,*unknown-value*)
                                                                   ,*unknown-value*)
                                              formal))
        (CAADR
          (partial-cons-form-from-destructors (cadr d-term) `(cons ,*unknown-value*
                                                                   (cons (cons ,c-term ,*unknown-value*)
                                                                         ,*unknown-value*))
                                              formal))
        (CDADR
          (partial-cons-form-from-destructors (cadr d-term) `(cons ,*unknown-value*
                                                                   (cons (cons ,*unknown-value* ,c-term)
                                                                         ,*unknown-value*))
                                              formal))
        (CADAR
          (partial-cons-form-from-destructors (cadr d-term) `(cons (cons ,*unknown-value*
                                                                         (cons ,c-term ,*unknown-value*))
                                                                   ,*unknown-value*)
                                              formal))
        (CDDAR
          (partial-cons-form-from-destructors (cadr d-term) `(cons (cons ,*unknown-value*
                                                                         (cons ,*unknown-value* ,c-term))
                                                                   ,*unknown-value*)
                                              formal))
        ((CADDR THIRD)
          (partial-cons-form-from-destructors (cadr d-term) `(cons ,*unknown-value*
                                                                   (cons ,*unknown-value*
                                                                         (cons ,c-term ,*unknown-value*)))
                                              formal))
        (CDDDR
          (partial-cons-form-from-destructors (cadr d-term) `(cons ,*unknown-value*
                                                                   (cons ,*unknown-value*
                                                                         (cons ,*unknown-value* ,c-term)))
                                              formal))
        (otherwise *unknown-value*)))))

;;; Derived isomorphism functions
(defines convert-fn/s-for-new-iso-fn

  (define convert-fn-for-new-iso-fn (old-body
                                     (pred-name symbolp)
                                     (formal variablep)
                                     (convert-fn-name symbolp)
                                     (new-to-old-p booleanp) ; return convert from old to new, otherwise new to old
                                     (iso-infos iso-info-alist-p))
    (case-match old-body
      (T formal)
      (('NULL !formal)
       'nil)
      (('NOT !formal)
       'nil)
      (('NOT ('CDDR !formal))
       `(cons ,*unknown-value* (cons ,*unknown-value* 'nil)))
      (('OR t1 t2)
       (merge-convert-exprs-for-or
         t1
         (convert-fn-for-new-iso-fn t1 pred-name formal convert-fn-name new-to-old-p iso-infos)
         (convert-fn-for-new-iso-fn t2 pred-name formal convert-fn-name new-to-old-p iso-infos)))
      (('AND . r-tms)
       (merge-convert-exprs-for-and
        (convert-fns-for-new-iso-fn r-tms pred-name formal convert-fn-name new-to-old-p iso-infos)))
      (('IF t1 'T t2)
       (if (equal t2 'NIL)
           (convert-fn-for-new-iso-fn t1 pred-name formal convert-fn-name new-to-old-p iso-infos)
         (merge-convert-exprs-for-or
           t1
           (convert-fn-for-new-iso-fn t1 pred-name formal convert-fn-name new-to-old-p iso-infos)
           (convert-fn-for-new-iso-fn t2 pred-name formal convert-fn-name new-to-old-p iso-infos))))
      (('IF t1 t2 'NIL)  ; TODO: check if this is sufficient for n-ary AND. E.g. ('IF t1 ('IF t2 t3 'NIL) 'NIL)
       (if (equal t2 'T)
           (convert-fn-for-new-iso-fn t1 pred-name formal convert-fn-name new-to-old-p iso-infos)
         (merge-convert-exprs-for-and
          (convert-fns-for-new-iso-fn (list t1 t2) pred-name formal convert-fn-name new-to-old-p iso-infos))))
      (('IF p t1 t2)
       `(if ,p
            ,(convert-fn-for-new-iso-fn t1 pred-name formal convert-fn-name new-to-old-p iso-infos)
          ,(convert-fn-for-new-iso-fn t2 pred-name formal convert-fn-name new-to-old-p iso-infos)))
      (('COND . cond-pairs)
       `(cond ,@(convert-cond-pairs-for-new-iso-fn cond-pairs pred-name formal convert-fn-name
                                                   new-to-old-p iso-infos)))
      ;; (('LET binds . let-body-lst)
      ;;  (let ((subst-let-body (sublis-var-untranslated-term (doublets-to-alist binds) (car (last let-body-lst)))))
      ;;    (convert-fn-for-new-iso-fn subst-let-body pred-name formal convert-fn-name new-to-old-p iso-infos)))
      ;; (('LET* binds . let-body-lst)
      ;;  (convert-fn-for-new-iso-fn (subst-let*-vars binds (car (last let-body-lst)))
      ;;                             pred-name formal convert-fn-name new-to-old-p iso-infos))
      ((!pred-name arg)
       (partial-cons-form-from-destructors arg `(,convert-fn-name ,arg)
                                           formal))
      ((f arg)
       (let ((iso-info (and (symbolp f)
                            (lookup-osi-info f iso-infos))))
         (if (not (null iso-info))
             (partial-cons-form-from-destructors arg `(,(iso-info-convert-fn iso-info new-to-old-p) ,arg)
                                                 formal)
           *unhandled-case*)))
      (& *unhandled-case*)))

  (define convert-fns-for-new-iso-fn (old-body-tms
                                      (pred-name symbolp)
                                      (formal variablep)
                                      (convert-fn-name symbolp)
                                      (new-to-old-p booleanp) ; return convert from old to new, otherwise new to old
                                      (iso-infos iso-info-alist-p))
    (if (atom old-body-tms)  ; shouldn't happen
        *unhandled-case*
      (if (atom (cdr old-body-tms))
          (list (convert-fn-for-new-iso-fn (car old-body-tms)
                                           pred-name formal convert-fn-name new-to-old-p iso-infos))
        (cons (convert-fn-for-new-iso-fn (car old-body-tms)
                                         pred-name formal convert-fn-name new-to-old-p iso-infos)
              (convert-fns-for-new-iso-fn (cdr old-body-tms)
                                          pred-name formal convert-fn-name new-to-old-p iso-infos)))))

  (define convert-cond-pairs-for-new-iso-fn (cond-pairs
                                             (pred-name symbolp)
                                             (formal variablep)
                                             (convert-fn-name symbolp)
                                             (new-to-old-p booleanp) ; return convert from old to new, otherwise new to old
                                             (iso-infos iso-info-alist-p))
    (if (or (atom cond-pairs)
            ;; Shouldn't happen
            (not (and (consp (car cond-pairs))
                      (consp (cdar cond-pairs)))))
        nil
      (case-match cond-pairs
        (((t1 'T))                      ; == t1
         (list (list t (convert-fn-for-new-iso-fn t1 pred-name formal convert-fn-name new-to-old-p iso-infos))))
        (((t1 t2) ('T 'NIL))            ; (and t1 t2)
         (if (equal t2 'T)
             (list (list t (convert-fn-for-new-iso-fn t1 pred-name formal convert-fn-name new-to-old-p iso-infos)))
           (list (list t (merge-2-convert-exprs-for-and
                            (convert-fn-for-new-iso-fn t1 pred-name formal convert-fn-name new-to-old-p iso-infos)
                            (convert-fn-for-new-iso-fn t2 pred-name formal convert-fn-name new-to-old-p iso-infos))))))
        (((p1 p2) . r-cond-pairs)
         (cons (list p1 (convert-fn-for-new-iso-fn p2 pred-name formal convert-fn-name new-to-old-p iso-infos))
               (convert-cond-pairs-for-new-iso-fn r-cond-pairs pred-name formal convert-fn-name
                                                  new-to-old-p iso-infos))))))
) ; convert-fn/s-for-new-iso-fn

(define convert-fn-for-new-iso-fn0 (old-body
                                    (pred-name symbolp)
                                    (formal variablep)
                                    (convert-fn-name symbolp)
                                    (new-to-old-p booleanp) ; return convert from old to new, otherwise new to old
                                    (iso-infos iso-info-alist-p))
  (let ((raw-body (convert-fn-for-new-iso-fn old-body pred-name formal convert-fn-name new-to-old-p iso-infos)))
    (fill-in-unknowns-by-old raw-body formal)))

(defund restrict-body (body guard-term)
  (declare (xargs :guard t))
  (case-match body
    (('and . conds)
     `(and ,guard-term ,@conds))
    (& (or (case-match body
             (('if condn then-cl else-cl)
              (and (atom then-cl)
                   `(if (or (not (mbt ,guard-term))
                            ,condn)
                        ,then-cl ,else-cl))))
           `(if (mbt ,guard-term)
                ,body
              nil)))))

;; Match structure of restrict-body
(defund equal-ignoring-mbt (t1 t2)
  (declare (xargs :guard t))
  (or (equal t1 t2)
      (let ((t1-t2 (list t1 t2)))
        (case-match t1-t2
          ((('and ('mbt &). conds1) ('and ('mbt &). conds2))
           (equal conds1 conds2))
          (& (case-match t1-t2
               ((('if ('or ('not ('mbt &))
                           condn1)
                     then-cl1 else-cl1)
                 ('if ('or ('not ('mbt &))
                           condn2)
                     then-cl2 else-c2l))
                (and (equal condn1 condn2)
                     (equal then-cl1 then-cl2)
                     (equal else-cl1 else-c2l)))
               ((('if ('mbt &) body1 'nil)
                 ('if ('mbt &) body2 'nil))
                (equal body1 body2))))))))

(define name-from-term (tm)
  :returns (nm stringp)
  (if (symbolp tm)
      (symbol-name tm)
    (if (consp tm)
        (let ((name-from-car (name-from-term (car tm))))
          (if (and (consp (cdr tm))
                   (consp (cadr tm))
                   (consp (cdadr tm))
                   (consp (cadadr tm)))
              (concatenate 'string
                           name-from-car
                           "-"
                           (name-from-term (cadr tm)))
            name-from-car))
      "strange-term")))

(define implicit-theorems-for-new-iso (rhs-condns condn (thm-name symbolp) enabled)
  (if (atom rhs-condns)
      ()
    (cons `(defthm ,(pack$ thm-name "--" (name-from-term (car rhs-condns)))
             (implies ,condn
                      ,(car rhs-condns))
             :hints (("Goal" :in-theory (enable ,@enabled))))
          (implicit-theorems-for-new-iso (cdr rhs-condns) condn thm-name enabled))))

(defines term/s-with-subst-and-name
  (define term-with-subst-and-name (tm (formal variablep)
                                       (convert-fn-name symbolp)
                                       (thm-name stringp))
    :returns (mv args
                 (ret-thm-nm stringp :hyp :guard)
                 (condns true-listp))
    (if (equal tm formal)
        (mv `(,convert-fn-name ,formal)
            thm-name
            nil)
      (if (and (consp tm)
               (symbolp (car tm)))
          (mv-let (tms nm condns)
              (terms-with-subst-and-name (cdr tm) formal convert-fn-name
                                         (concatenate 'string thm-name "-"
                                                      (symbol-name (car tm))))
            (mv `(,(car tm) ,@tms)
                nm
                (if (member-eq (car tm) '(car first))
                    (cons `(consp ,@tms)
                          condns)
                  condns)))
        (mv tm thm-name nil))))
  (define terms-with-subst-and-name (tms (formal variablep)
                                         (convert-fn-name symbolp)
                                         (thm-name stringp))
    :returns (mv args
                 (ret-thm-nm stringp :hyp :guard)
                 (condns true-listp))
    (if (atom tms)
        (mv nil "" nil)
      (b* (((mv car-tm car-nm car-condns)
            (term-with-subst-and-name (car tms) formal convert-fn-name thm-name))
           ((mv cdr-tms cdr-nm cdr-conds)
            (terms-with-subst-and-name (cdr tms) formal convert-fn-name thm-name))
           ((unless (and (true-listp car-condns) ; temporary heavy-hand
                         (true-listp cdr-conds)))
            (mv (cons car-tm cdr-tms)
                (concatenate 'string (or car-nm "") (or cdr-nm ""))
                ())))
        (mv (cons car-tm cdr-tms)
            (concatenate 'string (or car-nm "") (or cdr-nm ""))
            (append car-condns cdr-conds)))))
  :verify-guards nil
  ///
  (verify-guards term-with-subst-and-name)
)  ; term/s-with-subst-and-name

(local (in-theory (disable default-cdr sublis assoc-equal default-car)))


(defines type-theorems-for-new-iso-fn/-lst
  (define type-theorems-for-new-iso-fn (old-body
                                        (formal variablep)
                                        (convert-fn-name symbolp)
                                        (renaming-pred symbolp)
                                        (use-old-convert-fns-p booleanp)
                                        condns
                                        (thm-name stringp)
                                        (new-to-old-p booleanp) ; return convert from old to new, otherwise new to old
                                        (iso-infos iso-info-alist-p))
    (case-match old-body
      (('OR t1 t2)
       (append (type-theorems-for-new-iso-fn t2 formal convert-fn-name renaming-pred use-old-convert-fns-p
                                             (cons (acl2::negate-form t1) condns)
                                             thm-name new-to-old-p iso-infos)
               (type-theorems-for-new-iso-fn t1 formal convert-fn-name renaming-pred use-old-convert-fns-p
                                             (cons t1 condns)
                                             thm-name new-to-old-p iso-infos)))
      (('OR . &) ())                    ; TODO: Handle n-ary case n>2
      (('AND . r-tms)
       (type-theorems-for-new-iso-fn-lst r-tms formal convert-fn-name renaming-pred use-old-convert-fns-p
                                         condns thm-name new-to-old-p iso-infos))
      (('IF p t1 'NIL)
       (type-theorems-for-new-iso-fn-lst (list p t1)
                                         formal convert-fn-name renaming-pred use-old-convert-fns-p
                                         condns thm-name new-to-old-p iso-infos))
      (('IF p t1 t2)
       (append (type-theorems-for-new-iso-fn t2 formal convert-fn-name renaming-pred use-old-convert-fns-p
                                             (cons (acl2::negate-form p) condns)
                                             thm-name new-to-old-p iso-infos)
               (type-theorems-for-new-iso-fn t1 formal convert-fn-name renaming-pred use-old-convert-fns-p
                                             (cons p condns)
                                             thm-name new-to-old-p iso-infos)))
      (('COND . cond-pairs) (and (doublet-listp cond-pairs)
                                 (type-theorems-for-new-iso-fn-cond-pairs
                                   cond-pairs formal convert-fn-name renaming-pred use-old-convert-fns-p
                                   condns thm-name new-to-old-p iso-infos)))
      ((p . args)
       (if (symbolp p)
           (b* ((iso-info (lookup-osi-info p iso-infos))
                (new-p (if iso-info
                           (iso-info-pred iso-info new-to-old-p)
                         p))
                ((mv new-args thm-nm ?rhs-condns)
                 (terms-with-subst-and-name args formal convert-fn-name thm-name))
                (condn `(and ,@(rev condns)))
                (enabled (list renaming-pred convert-fn-name))
                (thm-base-nm (if use-old-convert-fns-p
                                 (pack$ renaming-pred "-" convert-fn-name "-" new-p)
                               (pack$ convert-fn-name "-" new-p))))
             (list*
              `(defthm ,(pack$ thm-base-nm thm-nm)
                       (implies ,condn
                                (,new-p ,@new-args))
                       :hints (("Goal" :in-theory (enable ,@enabled))))
              (implicit-theorems-for-new-iso rhs-condns condn
                                             ; thm-base-nm
                                             (if use-old-convert-fns-p
                                                 (pack$ renaming-pred "-" convert-fn-name)
                                               convert-fn-name)
                                             enabled)
               ))
         ()))
      (& ())))
  (define type-theorems-for-new-iso-fn-cond-pairs ((cond-pairs doublet-listp)
                                                   (formal variablep)
                                                   (convert-fn-name symbolp)
                                                   (renaming-pred symbolp)
                                                   (use-old-convert-fns-p booleanp)
                                                   condns
                                                   (thm-name stringp)
                                                   (new-to-old-p booleanp) ; return convert from old to new, otherwise new to old
                                                   (iso-infos iso-info-alist-p))
    (if (atom cond-pairs)
        nil
      (case-match cond-pairs
        (((t1 t2) ('T 'NIL))            ; Equiv to (AND T1 T2)
         (type-theorems-for-new-iso-fn-lst (list t1 t2) formal convert-fn-name renaming-pred use-old-convert-fns-p
                                           condns thm-name new-to-old-p iso-infos))
        (& (append (type-theorems-for-new-iso-fn (second (car cond-pairs))
                                                 formal convert-fn-name renaming-pred use-old-convert-fns-p
                                                 (cons (first (car cond-pairs)) condns)
                                                 thm-name new-to-old-p iso-infos)
                   (type-theorems-for-new-iso-fn-cond-pairs
                     (cdr cond-pairs)
                     formal convert-fn-name renaming-pred use-old-convert-fns-p
                     (cons (acl2::negate-form (first (car cond-pairs))) condns)
                     thm-name new-to-old-p iso-infos))))))
  (define type-theorems-for-new-iso-fn-lst (old-body-tms
                                            (formal variablep)
                                            (convert-fn-name symbolp)
                                            (renaming-pred symbolp)
                                            (use-old-convert-fns-p booleanp)
                                            condns
                                            (thm-name stringp)
                                            (new-to-old-p booleanp) ; return convert from old to new, otherwise new to old
                                            (iso-infos iso-info-alist-p))
    (if (atom old-body-tms)
        ()
      (append (type-theorems-for-new-iso-fn-lst (cdr old-body-tms)
                                                formal convert-fn-name renaming-pred use-old-convert-fns-p
                                                condns thm-name new-to-old-p iso-infos)
              (type-theorems-for-new-iso-fn (car old-body-tms)
                                            formal convert-fn-name renaming-pred use-old-convert-fns-p
                                            condns thm-name new-to-old-p iso-infos))))
) ; type-theorems-for-new-iso-fn/-lst

;; Returns type theorems for new conversion function based on the predicate that generated it
#|
Example: int10-map-p-->-int20-map-p
(define int20-map-p (m)
  (if (atom m)
      (null m)
    (and (consp (car m))
         (int20 (caar m))
         (int20 (cdar m))
         (int20-map-p (cdr m)))))
(defthm int10-map-p-->-int20-map-p-atom
  (implies (and (int10-map-p m) (atom p))
           (null (int10-map-p-->-int20-map-p m))))
(defthm int10-map-p-->-int20-map-p-not-atom
  (implies (and (int10-map-p m) (not (atom p)))
           (consp (int10-map-p-->-int20-map-p m))))
(defthm int10-map-p-->-int20-map-p-not-atom-caar
  (implies (and (int10-map-p m) (not (atom p)))
           (int20 (caar (int10-map-p-->-int20-map-p m)))))
(defthm int10-map-p-->-int20-map-p-not-atom-cdar
  (implies (and (int10-map-p m) (not (atom p)))
           (int20 (cdar (int10-map-p-->-int20-map-p m)))))
(defthm int10-map-p-->-int20-map-p-not-atom-cdr
  (implies (and (int10-map-p m) (not (atom p)))
           (int20 (cdar (int10-map-p-->-int20-map-p m)))))
|#


(define find-definition-in-events ((fn symbolp) (events true-listp))
  (if (endp events)
      nil
    (let ((this-event (car events)))
      (case-match this-event
        (('defun !fn (v) & body)   ; Has to be unary with a single declare unless make-new-iso-pred-events changes
         (cons v body))
        (('encapsulate & . encap-events)
         (and (true-listp encap-events)
              (or (find-definition-in-events fn encap-events)
                  (find-definition-in-events fn (cdr events)))))
        (& (find-definition-in-events fn (cdr events)))))))

(define find-previous-iso-with-equivalent-definition ((convert-old-to-new-fn symbolp)
                                                      (convert-new-to-old-fn symbolp)
                                                      (formal symbolp)
                                                      convert-old-to-new-fn-body
                                                      (iso-infos iso-info-alist-p)
                                                      (events true-list-listp))
  :returns (mv (use-old-convert-fns-p booleanp)
               (ret-convert-old-to-new-fn symbolp :hyp (symbolp convert-old-to-new-fn))
               (ret-convert-new-to-old-fn symbolp :hyp (symbolp convert-new-to-old-fn)))
  (if (endp iso-infos)
      (mv nil convert-old-to-new-fn convert-new-to-old-fn)
    (b* ((iso (cdar iso-infos))
         (alpha (acl2::defmapping-info->alpha iso))
         (beta  (acl2::defmapping-info->beta  iso))
         ((unless (and (symbolp alpha)
                       (symbolp beta)))
          (find-previous-iso-with-equivalent-definition convert-old-to-new-fn convert-new-to-old-fn
                                                        formal convert-old-to-new-fn-body
                                                        (cdr iso-infos) events))
         (found-def (find-definition-in-events alpha events))
         ((unless (and (consp found-def)
                       (symbolp (car found-def))))
          (find-previous-iso-with-equivalent-definition convert-old-to-new-fn convert-new-to-old-fn
                                                        formal convert-old-to-new-fn-body
                                                        (cdr iso-infos) events))
         ((cons new-formal body) found-def))
      (if (equal-ignoring-mbt convert-old-to-new-fn-body
                              (sublis (list (cons new-formal formal)
                                            (cons alpha convert-old-to-new-fn))
                                      body))
          (mv t
              (acl2::defmapping-info->alpha iso)
              (acl2::defmapping-info->beta iso))
        (find-previous-iso-with-equivalent-definition convert-old-to-new-fn convert-new-to-old-fn
                                                      formal convert-old-to-new-fn-body
                                                      (cdr iso-infos) events)))))

;;; Try to reuse existing function either if body is just a fn call or iso fn defined in events
(define maybe-use-old-definitions ((convert-old-to-new-fn symbolp)
                                   (convert-new-to-old-fn symbolp)
                                   (formal symbolp)
                                   convert-old-to-new-fn-body
                                   convert-new-to-old-fn-body
                                   (iso-infos iso-info-alist-p)
                                   (events true-list-listp))
  :returns (mv (use-old-convert-fns-p booleanp)
               (existing-convert-old-to-new-fn symbolp :hyp (symbolp convert-old-to-new-fn))
               (existing-convert-new-to-old-fn symbolp :hyp (symbolp convert-new-to-old-fn)))
  (let ((bodies (list convert-old-to-new-fn-body convert-new-to-old-fn-body)))
    (case-match bodies
      (((f1 !formal) (f2 !formal))
       (if (and (symbolp f1) (symbolp f2))
           (mv t f1 f2)
         (find-previous-iso-with-equivalent-definition convert-old-to-new-fn convert-new-to-old-fn
                                                       formal convert-old-to-new-fn-body
                                                       iso-infos events)))
      (& (find-previous-iso-with-equivalent-definition convert-old-to-new-fn convert-new-to-old-fn
                                                       formal convert-old-to-new-fn-body
                                                       iso-infos events)))))


;; substitutes all occurrences of pat by repl in str
(define string-subst ((str stringp) (pat stringp) (repl stringp))
  ;:measure (length str)
  ;:returns (s stringp :hyp :guard)
  :mode :program
  (let ((pos-i (search pat str)))
    (if (or (null pos-i)
            (equal str ""))
        str
      (concatenate 'string (subseq str 0 pos-i)
                   repl
                   (string-subst (subseq str (+ pos-i (length pat))
                                         (length str))
                                 pat repl)))))

(define string-subst-remove-p ((str stringp) (pat stringp) (repl stringp))
  :mode :program
  (if (and (search "-P" pat :start2 (- (length pat) 2))
           (search "-P" repl :start2 (- (length repl) 2)))
      (string-subst str
                    (subseq pat 0 (- (length pat) 2))
                    (subseq repl 0 (- (length repl) 2)))
    (string-subst str pat repl)))

;; substitute iso domain name if it occurs and the result is not already used,
;; else use the current transformation index for THM
(define new-name-maybe-using-isos ((fun symbolp)
                                   (iso-infos iso-info-alist-p)
                                   (thmp booleanp)
                                   (world plist-worldp))
  ;:returns (nm symbolp)
  :mode :program
  (if (endp iso-infos)
      (acl2::increment-name-suffix fun)
    (or (b* ((iso-info (cdar iso-infos))
             (new-fun-name
              (string-subst-remove-p (symbol-name fun)
                                     (symbol-name (acl2::defmapping-info->doma iso-info))
                                     (symbol-name (acl2::defmapping-info->domb iso-info))))
             ((when (equal new-fun-name (symbol-name fun)))
              nil)
             (new-sym (intern new-fun-name "ACL2")))
          new-sym)
        (new-name-maybe-using-isos fun (rest iso-infos) thmp world))))

(define dependent-on-iso-types-p ((sig-list symbol-listp) (iso-infos iso-info-alist-p))
  (and (consp sig-list)
       (or (lookup-iso-info (first sig-list) iso-infos)
           (dependent-on-iso-types-p (rest sig-list) iso-infos))))


(local (in-theory (disable (tau-system))))

;;; Tries to create an isomorphism for from iso-source-pred given iso-target-pred iso-target-pred-defun.
;;; Does this by constructing the forward and backward isomorphism functions and creating a defiso event.
;;; Returns new events and the augmented iso-infos
(define make-new-iso-pred-events ((iso-source-pred symbolp)
                                  (iso-target-pred symbolp)
                                  (formals symbol-listp)
                                  old-pred-body
                                  new-pred-body
                                  (recursivep booleanp)
                                  (iso-infos iso-info-alist-p)
                                  (events true-list-listp))
  :returns (mv new-iso-pred-events
               (convert-old-to-new-fn symbolp)
               (convert-new-to-old-fn symbolp)
               new-iso-osi-theorems
               iso-infos)
  (b* (((unless (equal (length formals) 1))
        (cw "Warning: Can't handle generation of isomorphism for ~x0 (not a single formal)" iso-source-pred)
        (mv nil nil nil nil iso-infos))
       (formal (first formals))
       (convert-old-to-new-fn (pack$ iso-source-pred "-->-" iso-target-pred))
       (convert-new-to-old-fn (pack$ iso-target-pred  "-->-" iso-source-pred))
       (convert-old-to-new-fn-body
         (convert-fn-for-new-iso-fn0 new-pred-body iso-target-pred formal convert-old-to-new-fn nil iso-infos))
       (convert-new-to-old-fn-body
         (convert-fn-for-new-iso-fn0 new-pred-body iso-target-pred formal convert-new-to-old-fn t iso-infos))
       ((when (or (null convert-new-to-old-fn-body) ; if 1 is null they both should be
                  (null convert-old-to-new-fn-body)))
        (cw "Warning: Can't handle generation of isomorphism for ~x0" iso-source-pred)
        (mv nil nil nil nil iso-infos))
       (convert-new-to-old-fn-body (if recursivep
                                       (restrict-body convert-new-to-old-fn-body
                                                      `(,iso-target-pred ,formal))
                                     convert-new-to-old-fn-body))
       (convert-old-to-new-fn-body (if recursivep
                                       (restrict-body convert-old-to-new-fn-body
                                                      `(,iso-source-pred ,formal))
                                     convert-old-to-new-fn-body))
       ((mv use-old-convert-fns-p convert-old-to-new-fn convert-new-to-old-fn)
        (maybe-use-old-definitions convert-old-to-new-fn convert-new-to-old-fn
                                   formal convert-old-to-new-fn-body convert-new-to-old-fn-body
                                   iso-infos events))
       (convert-fn-defs (if use-old-convert-fns-p
                            ()
                          `((defun ,convert-new-to-old-fn ,formals ; enable ??
                              (declare (xargs :guard (,iso-target-pred ,formal)
                                              :guard-hints (("Goal" :in-theory (enable ,iso-target-pred)))
                                              ,@(if recursivep
                                                    `(:hints (("Goal" :in-theory (enable ,iso-target-pred))))
                                                  nil)))
                              ,convert-new-to-old-fn-body)
                            (defun ,convert-old-to-new-fn ,formals ; enable ??
                              (declare (xargs :guard (,iso-source-pred ,formal)
                                              :guard-hints (("Goal" :in-theory (enable ,iso-source-pred)))
                                              ,@(if recursivep
                                                    `(:hints (("Goal" :in-theory (enable ,iso-source-pred))))
                                                  nil)))
                              ,convert-old-to-new-fn-body))))
       (defiso-name (pack$ iso-source-pred "-ISO-" iso-target-pred))
       (defiso-form `(defiso ,defiso-name
                         ,iso-source-pred ,iso-target-pred ,convert-old-to-new-fn ,convert-new-to-old-fn
                       :thm-enable :all-nonguard
                       :hints (:beta-of-alpha
                               (("Goal" :in-theory (enable ,iso-source-pred ,iso-target-pred
                                                           ,convert-old-to-new-fn ,convert-new-to-old-fn)))
                               :alpha-of-beta (("Goal" :in-theory
                                                       (enable ,iso-source-pred ,iso-target-pred
                                                               ,convert-old-to-new-fn ,convert-new-to-old-fn)))
                               :alpha-image (("Goal" :in-theory (enable ,iso-source-pred ,iso-target-pred
                                                                        ,convert-old-to-new-fn)))
                               :beta-image (("Goal" :in-theory (enable ,iso-source-pred ,iso-target-pred
                                                                       ,convert-new-to-old-fn)))
                               ,@(and use-old-convert-fns-p
                                      `(:alpha-guard
                                        (("Goal" :in-theory (enable ,iso-source-pred ,iso-target-pred)))
                                        :beta-guard
                                        (("Goal" :in-theory (enable ,iso-source-pred ,iso-target-pred))))))))
       ((unless (and (acl2::pseudo-event-formp defiso-form) ; Just so guards check!
                     (acl2::pseudo-termfnp iso-source-pred)
                     (acl2::pseudo-termfnp iso-target-pred)
                     (acl2::pseudo-termfnp convert-old-to-new-fn)
                     (acl2::pseudo-termfnp convert-new-to-old-fn)))
        (cw "Warning: Not pseudo* \n ~x0: ~x1 \n ~x2: ~x3 \n ~x4: ~x5 \n ~x6: ~x7 \n ~x8: ~x9 \n"
            (acl2::pseudo-event-formp defiso-form) defiso-form
            (acl2::pseudo-termfnp iso-source-pred) iso-source-pred
            (acl2::pseudo-termfnp iso-target-pred) iso-target-pred
            (acl2::pseudo-termfnp convert-old-to-new-fn) convert-old-to-new-fn
            (acl2::pseudo-termfnp convert-new-to-old-fn) convert-new-to-old-fn)
        (mv nil nil nil nil iso-infos))
       (alpha-image (pack$ defiso-name ".ALPHA-IMAGE"))
       (beta-image (pack$ defiso-name ".BETA-IMAGE"))
       (beta-of-alpha (pack$ defiso-name ".BETA-OF-ALPHA"))
       (alpha-of-beta (pack$ defiso-name ".ALPHA-OF-BETA"))
       (alpha-injective (pack$ defiso-name ".ALPHA-INJECTIVE"))
       (beta-injective (pack$ defiso-name ".BETA-INJECTIVE"))
       (doma-guard (pack$ defiso-name ".DOMA-GUARD"))
       (domb-guard (pack$ defiso-name ".DOMB-GUARD"))
       (alpha-guard (pack$ defiso-name ".ALPHA-GUARD"))
       (beta-guard (pack$ defiso-name ".BETA-GUARD"))
       ;; Not all make-defmapping-info fields are necessary for this purpose. The defiso event will create the real one
       (new-iso-info (acl2::make-defmapping-info :call$ defiso-form
                                                 :expansion defiso-form ; place-holder to avoid guard error
                                                 :doma iso-source-pred
                                                 :domb iso-target-pred
                                                 :alpha convert-old-to-new-fn
                                                 :beta convert-new-to-old-fn
                                                 :alpha-image alpha-image
                                                 :beta-image beta-image
                                                 :beta-of-alpha beta-of-alpha
                                                 :alpha-of-beta alpha-of-beta
                                                 :alpha-injective alpha-injective
                                                 :beta-injective beta-injective
                                                 :doma-guard doma-guard
                                                 :domb-guard domb-guard
                                                 :alpha-guard alpha-guard
                                                 :beta-guard beta-guard
                                                 :unconditional nil))
       ;; Want to keep in order for new-name-maybe-using-isos
       (new-iso-infos (append iso-infos (list (cons iso-source-pred new-iso-info))))
       (convert-old-to-new-fn-type-thms (type-theorems-for-new-iso-fn new-pred-body
                                                                      formal ;; iso-source-pred
                                                                      convert-old-to-new-fn
                                                                      iso-source-pred
                                                                      use-old-convert-fns-p
                                                                      (list `(,iso-source-pred ,formal))
                                                                      "" t new-iso-infos))
       (convert-old-to-new-fn-thm-names (theorem-names convert-old-to-new-fn-type-thms))
       (convert-new-to-old-fn-type-thms (type-theorems-for-new-iso-fn old-pred-body
                                                                      formal ;; iso-target-pred
                                                                      convert-new-to-old-fn
                                                                      iso-target-pred
                                                                      use-old-convert-fns-p
                                                                      ;iso-target-pred
                                                                      (list `(,iso-target-pred ,formal))
                                                                      "" nil new-iso-infos))
       (convert-new-to-old-fn-thm-names (theorem-names convert-new-to-old-fn-type-thms)))
    (mv `(   ; order will be reversed
          ,@convert-new-to-old-fn-type-thms
          ,@convert-old-to-new-fn-type-thms
          ,defiso-form
          ,@convert-fn-defs)
        convert-old-to-new-fn
        convert-new-to-old-fn
        (list* alpha-image
               beta-image
               beta-of-alpha
               alpha-of-beta
               alpha-injective
               beta-injective
               ;; !! TODO: If these are trivial (normal case?) then this gives an error
               ;; doma-guard
               ;; domb-guard
               alpha-guard
               beta-guard
               (append convert-old-to-new-fn-thm-names
                       convert-new-to-old-fn-thm-names))
        new-iso-infos))
) ; make-new-iso-pred-events

;; Input-checking/processing

(define check-isos ((isos symbol-listp) (world plist-worldp))
  :mode :program
  (if (endp isos)
      ()
    (let* ((iso-name (first isos))
           (iso-info (defiso-lookup iso-name world)))
      (if (null iso-info)
          (raise "~x0 must be an isomorphism name." (first isos))
        (acons (acl2::defmapping-info->doma iso-info)
               iso-info
               (check-isos (rest isos) world))))))

;; Remove troublesome __function__ binding!
(define clean-body (body)
  (case-match body
    (('let (('__function__ &)) . real-body)
     (and (true-listp real-body)
          (car (last real-body))))
    ;; Temporarily removed until generalize-to-lambda put in community books
    ;; ((('lambda formals body) . actuals)
    ;;  (apt::generalize-to-lambda formals actuals body))
    ((('lambda ('__function__ &) . real-body)
      & &)
     (and (true-listp real-body)
          (car (last real-body))))
    (& body)))

(defines normalize-predicate-term
  (define normalize-predicate-term (tm)
    (if (atom tm)
        tm
      (let ((tm (if (equal (car tm) 'cond)
                    tm
                  (cons (car tm) (normalize-predicate-term-lst (cdr tm))))))
        (case-match tm
          (('if p 'nil r)
           (acl2::make-and-nice (list (acl2::negate-form p) r)))
          (('if p 't r)
           (acl2::make-or-nice (list p r)))
          (('if p p r)
           (acl2::make-or-nice (list p r)))
          (('or . disjs)
           (acl2::make-or-nice disjs))
          (('and . conjs)
           (acl2::make-and-nice conjs))
          (('cond) 'nil)
          (('cond ('t p) . &)
           (normalize-predicate-term p))
          (('cond (p 't) . r-cond-pairs)
           (acl2::make-or-nice (list p (normalize-predicate-term `(cond ,@r-cond-pairs)))))
          (('cond (p 'nil) . r-cond-pairs)
           (acl2::make-and-nice (list (acl2::negate-form p)
                                      (normalize-predicate-term `(cond ,@r-cond-pairs)))))
          (& tm)))))
  (define normalize-predicate-term-lst (tms)
    (if (atom tms)
        nil
      (cons (normalize-predicate-term (car tms))
            (normalize-predicate-term-lst (cdr tms)))))
  ) ; normalize-predicate-term

(define nice-body (tm world)
  :mode :program
  (normalize-predicate-term
    (untranslate (acl2::reconstruct-macros-in-term
                   (acl2::expand-lambdas-in-term (clean-body tm)))
                 nil world)))


(define lift-iso-event (pred isos iso-name iso-pred-name state)
  :mode :program
  (declare (ignorable iso-name))
  (b* ((world (w state))
       ((unless (and (symbolp pred)
                     (function-symbolp pred world)))
        (prog2$ (raise "~x0 must be a function." pred)
                (mv t nil state)))
       ((unless (or (symbolp isos)
                    (and (symbol-listp isos)
                         isos)))
        (raise "~x0 must be an isomorphism name or list of isomorphism names." isos)
        (mv t nil state))
       (iso-infos (check-isos (if (symbolp isos)
                                  (list isos)
                                isos)
                              world))
       ((unless iso-infos)
        (raise "No isomorphisms to apply!")
        (mv t nil state))
       ;; (propiso-info (propiso-info nil nil nil
       ;;                             (doublets-to-alist (if (and (listp hints-map)
       ;;                                                         (eql (len hints-map) 2)
       ;;                                                         (symbolp (car hints-map)))
       ;;                                                    ;; If just one allow extra parens to be omitted
       ;;                                                    (list hints-map)
       ;;                                                  hints-map))
       ;;                             world))
       (formals (formals pred world))
       (recursivep (acl2::irecursivep+ pred world))
       (new-pred (or iso-pred-name
                     (new-name-maybe-using-isos pred iso-infos nil world)))
       (renaming (acons pred new-pred (renaming-from-iso-infos iso-infos)))
       (pred-body0 (ubody pred world))
       (pred-body ; (clean-body ;; (fn-ubody1 pred pred-body0 world nil)
         (nice-body pred-body0 world))
       ;; (iso-pred-name (or (and (symbolp iso-pred-name) iso-pred-name)
       ;;                    (new-name-maybe-using-isos pred iso-infos nil world)))
       ;; (iso-name (or (and (symbolp iso-name) iso-name)
       ;;               (pack$ pred "-ISO-" iso-pred-name)))
       (new-pred-body (rename-fns-and-expand-lambdas-in-untranslated-term pred-body renaming))
       ((mv events & & & &)
        (make-new-iso-pred-events pred new-pred formals new-pred-body new-pred-body recursivep iso-infos nil))
       (old-guard (guard pred nil world))
       (old-guard (untranslate old-guard nil world))
       (new-guard (rename-fns-and-expand-lambdas-in-untranslated-term old-guard renaming))
       )
    (value `(encapsulate ()
              (logic)
              (set-ignore-ok t)
              (set-irrelevant-formals-ok t)
              (set-default-hints nil)
              (set-override-hints nil)
              (defun ,new-pred ,formals
                (declare (xargs ;; ,@(if measure1 `(:measure ,measure1) ())
                                ,@(if new-guard `(:guard ,new-guard) ())
                                ;; ,@(if guard-hints3 `(:guard-hints ,guard-hints3) ())
                                ;; ,@(if guard-verifiedp nil `(:verify-guards nil))
                                ))
                ,new-pred-body)
              ,@(reverse events)))))

(deftransformation lift-iso
  (pred isos)
  ((iso-name 'nil)
   (iso-pred-name 'nil)
   ;; (hints-map 'nil)
   ))

