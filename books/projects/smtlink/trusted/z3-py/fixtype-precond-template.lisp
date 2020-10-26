;; Copyright (C) 2015, University of British Columbia
;; Written (originally) by Yan Peng (Canada Day, 2019)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2

(in-package "SMT")
(include-book "centaur/fty/top" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "clause-processors/meta-extract-user" :dir :system)

(include-book "../../verified/hint-interface")
(include-book "../../verified/computed-hints")
(include-book "../../utils/basics")
(include-book "translate-constant")

(define precond-array ((rec symbolp)
                       (smt-type smt-type-p)
                       (precond pseudo-term-list-listp))
  :returns (term pseudo-term-list-listp)
  :ignore-ok t
  :irrelevant-formals-ok t
  (pseudo-term-list-list-fix precond))

(local
(defthm pseudo-termp-of-cdar-of-symbol-symbol-alist-fix
  (implies (consp (symbol-symbol-alist-fix x))
           (pseudo-termp (cdr (car (symbol-symbol-alist-fix x)))))
  :hints (("Goal" :in-theory (enable symbol-symbol-alist-fix))))
)

(local
 (defthm pseudo-term-listp-of-strip-cdrs-of-symbol-symbol-alist-fix
   (pseudo-term-listp (strip-cdrs (symbol-symbol-alist-fix x)))
   :hints (("Goal" :in-theory (enable symbol-symbol-alist-fix))))
 )

(local
 (defthm symbol-listp-of-strip-cdrs-of-symbol-symbol-alistp
   (implies (symbol-symbol-alistp x)
            (symbol-listp (strip-cdrs x)))
   :hints (("Goal" :in-theory (enable symbol-symbol-alist-fix))))
 )

(define precond-type-list ((destructor-alst symbol-symbol-alistp))
  :returns (term pseudo-term-listp)
  :measure (len destructor-alst)
  :hints (("Goal" :in-theory (enable symbol-symbol-alist-fix)))
  (b* ((destructor-alst (symbol-symbol-alist-fix destructor-alst))
       ((unless (consp destructor-alst)) nil)
       ((cons (cons type var) rest) destructor-alst))
    `((not (,type ,var))
      ,@(precond-type-list rest))))

(local
 (defthm append-of-pseudo-term-listp
   (implies (and (pseudo-term-listp x)
                 (pseudo-term-listp y))
            (pseudo-term-listp (append x y))))
 )

(define make-bindings ((left symbol-listp)
                       (right symbol-listp))
  :returns (binding symbol-list-listp)
  :measure (len left)
  (b* ((left (symbol-list-fix left))
       (right (symbol-list-fix right))
       ((unless (consp left)) nil)
       ((unless (consp right)) nil))
    (cons (list (car left) (car right))
          (make-bindings (cdr left) (cdr right)))))

(define theorem-hint ((hint type-thm-p)
                      (bindings symbol-list-listp))
  :returns (the-hint true-listp)
  (b* ((hint (type-thm-fix hint))
       (bindings (symbol-list-list-fix bindings))
       ((type-thm h) hint))
    (cond ((and (null h.name) (null h.hints))
           nil)
          ((and (null h.name) h.hints)
           (treat-in-theory-hint '(hint-please) h.hints))
          ((and h.name (null h.hints))
           `(:in-theory (e/d (hint-please)
                             (,h.name))
                        :use ((:instance ,h.name
                                         ,@bindings))))
          ((and h.name h.hints)
           (prog2$ (cw "Both a theorem name ~p0 and hints ~p1 is provided, we
                        will use the theorem name.~%" h.name h.hints)
                   `(:in-theory (e/d (hint-please)
                                     (,h.name))
                                :use ((:instance ,h.name
                                                 ,@bindings))))))))

(define free-var-of-theorem ((thm symbolp) state)
  :returns (var-lst symbol-listp)
  :guard-debug t
  (b* ((theorem (acl2::meta-extract-formula-w thm (w state)))
       ((unless (pseudo-termp theorem))
        (er hard? 'fixtype-precond-template=>free-var-of-theorem
            "Can't find theorem ~p0~%" thm))
       (var-lst (acl2::all-vars theorem))
       ((unless (symbol-listp var-lst))
        (er hard? 'fixtype-precond-template=>free-var-of-theorem
            "Free var of ~p0 is not a symbol-list: ~p1~%" thm var-lst)))
    (reverse var-lst)))

(define precond-prod-type-of-constructor ((constructor type-function-p)
                                          (arguments symbol-listp)
                                          (hypo pseudo-term-listp)
                                          (precond pseudo-term-list-listp)
                                          state)
  :returns (term pseudo-term-list-listp)
  (b* ((precond (pseudo-term-list-list-fix precond))
       (constructor (type-function-fix constructor))
       (arguments (symbol-list-fix arguments))
       (hypo (pseudo-term-list-fix hypo))
       ((type-function f) constructor)
       ((if (or (equal f.name 'quote) (equal f.return-type 'quote)))
        (er hard? 'fixtype-precond-template=>precond-prod-type-of-constructor
            "A constructor named 'quote?~%"))
       (thm-name (type-thm->name f.type-of-function-thm))
       (use-arguments (free-var-of-theorem thm-name state))
       (bindings (make-bindings use-arguments arguments))
       (the-hint (theorem-hint f.type-of-function-thm bindings)))
    (cons `((hint-please ',the-hint)
             ,@hypo
            (,f.return-type (,f.name ,@arguments)))
          precond)))

(define precond-prod-type-of-destructor-list ((rec symbolp)
                                              (destructors type-function-list-p)
                                              (precond pseudo-term-list-listp)
                                              state)
  :returns (term pseudo-term-list-listp)
  :measure (len destructors)
  :hints (("Goal"
           :in-theory (enable symbol-symbol-alist-fix)))
  (b* ((rec (symbol-fix rec))
       (precond (pseudo-term-list-list-fix precond))
       (destructors (type-function-list-fix destructors))
       ((if (equal rec 'quote))
        (er hard? 'fixtype-precond-template=>precond-prod-type-of-destructor-list
            "A constructor named 'quote?~%"))
       ((unless (consp destructors)) precond)
       ((cons first rest) destructors)
       ((type-function f) first)
       (thm-name (type-thm->name f.type-of-function-thm))
       (use-arguments (free-var-of-theorem thm-name state))
       (bindings (make-bindings use-arguments '(x)))
       (the-hint (theorem-hint f.type-of-function-thm bindings))
       (first-precond `((hint-please ',the-hint)
                        (not (,rec x))
                        (,f.return-type (,f.name x)))))
    (precond-prod-type-of-destructor-list rec rest
                                          (cons first-precond precond)
                                          state)))

(define precond-prod-destructor-of-constructors ((constructor type-function-p)
                                                 (destructors type-function-list-p)
                                                 (hypo pseudo-term-listp)
                                                 (var-lst symbol-listp)
                                                 (precond
                                                  pseudo-term-list-listp)
                                                 state)
  :returns (term pseudo-term-list-listp)
  :measure (len destructors)
  (b* ((precond (pseudo-term-list-list-fix precond))
       (constructor (type-function-fix constructor))
       ((type-function c) constructor)
       (destructors (type-function-list-fix destructors))
       ((if (or (equal c.name 'quote) (equal c.return-type 'quote)))
        (er hard? 'fixtype-precond-template=>precond-prod-destructor-of-constructors
            "A constructor named 'quote?~%"))
       (hypo (pseudo-term-list-fix hypo))
       ((unless (consp destructors)) precond)
       ((cons first rest) destructors)
       ((type-function d) first)
       (thm-name (type-thm->name d.destructor-of-constructor-thm))
       (use-arguments (free-var-of-theorem thm-name state))
       (bindings (make-bindings use-arguments var-lst))
       (the-hint (theorem-hint d.destructor-of-constructor-thm bindings))
       (var (symbol-append 'var- d.name))
       (first-precond `((hint-please ',the-hint)
                        ,@hypo
                        (equal (,d.name (,c.name ,@var-lst))
                               ,var))))
    (precond-prod-destructor-of-constructors constructor rest hypo var-lst
                                             (cons first-precond precond)
                                             state)))

(define precond-destructor-alist ((destructors type-function-list-p))
  :returns (destructor-alst symbol-symbol-alistp)
  :measure (len destructors)
  (b* ((destructors (type-function-list-fix destructors))
       ((unless (consp destructors)) nil)
       ((cons first rest) destructors)
       ((type-function f) first)
       (return-type (type-function->return-type f)))
    (acons return-type (symbol-append 'var- f.name)
           (precond-destructor-alist rest))))

(define precond-prod ((prod prod-p)
                      (precond pseudo-term-list-listp)
                      state)
  :returns (term pseudo-term-list-listp)
  :guard-debug t
  (b* ((prod (prod-fix prod))
       (precond (pseudo-term-list-list-fix precond))
       ((prod p) prod)
       (rec (type-function->return-type p.constructor))
       (destructor-alst (precond-destructor-alist p.destructors))
       (hypo (precond-type-list destructor-alst))
       (var-lst (strip-cdrs destructor-alst))
       (type-of-constructor
        (precond-prod-type-of-constructor p.constructor var-lst hypo
                                          precond state))
       (type-of-destructors
        (precond-prod-type-of-destructor-list rec p.destructors
                                              type-of-constructor state))
       (destructor-of-constructors
        (precond-prod-destructor-of-constructors p.constructor p.destructors
                                                 hypo var-lst
                                                 type-of-destructors state)))
    destructor-of-constructors))
