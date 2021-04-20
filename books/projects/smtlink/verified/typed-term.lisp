;; Copyright (C) 2015, University of British Columbia
;; Originally written by Yan Peng (December 30th 2019)
;; Edited by Mark Greenstreet
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")
(include-book "std/util/bstar" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/fty/top" :dir :system)
(include-book "tools/defevaluator-fast" :dir :system)
(include-book "clause-processors/just-expand" :dir :system)
(include-book "clause-processors/meta-extract-user" :dir :system)
(include-book "ordinals/lexicographic-ordering-without-arithmetic" :dir :system)

(include-book "../utils/pseudo-term")
(include-book "path-cond")

(encapsulate ()
  (local (in-theory (disable pseudo-termp)))

  (defprod typed-term
    ((term pseudo-termp :default ''nil)
     (path-cond pseudo-termp :default ''t)
     (judgements pseudo-termp :default '(if (if (symbolp 'nil)
                                                (if (booleanp 'nil) 't 'nil)
                                              'nil)
                                            't
                                          'nil))))

  (deflist typed-term-list
    :elt-type typed-term-p
    :true-listp t)

  (define typed-term-list->term-lst ((tterm-lst typed-term-list-p))
    :measure (len (typed-term-list-fix tterm-lst))
    :returns (term-lst pseudo-term-listp)
    (b* ((tterm-lst (typed-term-list-fix tterm-lst))
         ((unless (consp tterm-lst)) nil)
         ((cons tterm-hd tterm-tl) tterm-lst)
         ((typed-term tth) tterm-hd))
      (cons tth.term (typed-term-list->term-lst tterm-tl)))
    ///
    (more-returns
     (term-lst
      (equal (acl2-count
              (typed-term-list->term-lst (typed-term-list-fix tterm-lst)))
             (acl2-count term-lst))
      :name acl2-count-equal-of-typed-term-list-fix
      :hints (("Goal"
               :expand (typed-term-list->term-lst tterm-lst))))
     (term-lst
      (implies (consp tterm-lst)
               (< (acl2-count (typed-term->term (car tterm-lst)))
                  (acl2-count term-lst)))
      :name acl2-count-of-car-of-typed-term-list-p)
     (term-lst
      (implies (typed-term-list-p tterm-lst)
               (equal (len term-lst) (len tterm-lst)))
      :name typed-term-list->term-lst-maintains-len)
     ;; added by mrg
     (term-lst (implies (consp tterm-lst) (consp term-lst))
               :name consp-of-typed-term-lst->term-lst
               :hints(("Goal" :in-theory (enable typed-term-list->term-lst))))
     (term-lst (implies (not (consp tterm-lst)) (equal term-lst nil))
               :name null-of-typed-term-lst->term-lst
               :hints(("Goal" :in-theory (enable typed-term-list->term-lst))))))

  (defthm acl2-count-of-cdr-of-typed-term-list-p
    (implies (consp tterm-lst)
             (< (acl2-count (typed-term-list->term-lst (cdr tterm-lst)))
                (acl2-count (typed-term-list->term-lst tterm-lst))))
    :hints (("Goal"
             :expand (typed-term-list->term-lst tterm-lst))))

  (define typed-term-list->judgements ((tterm-lst typed-term-list-p))
    :measure (len (typed-term-list-fix tterm-lst))
    :returns (judges pseudo-termp)
    (b* ((tterm-lst (typed-term-list-fix tterm-lst))
         ((unless (consp tterm-lst)) ''t)
         ((cons tterm-hd tterm-tl) tterm-lst)
         ((typed-term tth) tterm-hd))
      `(if ,tth.judgements
           ,(typed-term-list->judgements tterm-tl)
         'nil)))

  ;; mrg:  I removed the check for uniform-path-cond? because it
  ;;   was forcing messy induction proofs when reasoning about
  ;;   make-typed-term-list.  I suspect that this simpler version
  ;;   typed-term-list->path-cond "works" for everything we need
  ;;   anyway.
  ;;     Then, I moved the definition of typed-term-list->path-cond
  ;;   *before* uniform-path-cond? so I could use it in the definition
  ;;   of uniform-path-cond?.  This makes subsequent proofs work
  ;;   with fewer hints.
  (define typed-term-list->path-cond ((tterm-lst typed-term-list-p))
    :returns (path-cond pseudo-termp)
    (b* ((tterm-lst (typed-term-list-fix tterm-lst))
         ((unless (consp tterm-lst)) ''t)
         ((cons tterm-hd &) tterm-lst)
         ((typed-term tth) tterm-hd))
      tth.path-cond))

  ;; mrg:  added uniform-path-help because it makes reasoning about
  ;;   uniform-path-cond? easier.  That's because uniform-path-help
  ;;   has a "better" induction schema (by keeping path-cond unchanged).
  (define uniform-path-help ((tterm-lst typed-term-list-p) (path-cond pseudo-termp))
    :returns (ok booleanp)
    (b* (((unless (consp tterm-lst)) t)
         ((unless (equal (typed-term-list->path-cond tterm-lst) path-cond)) nil))
      (uniform-path-help (cdr tterm-lst) path-cond))
    ///
    (more-returns
     (ok (implies (not (consp tterm-lst)) ok)
         :name uniform-path-help-of-atom)
     (ok (implies ok (uniform-path-help (cdr tterm-lst) path-cond))
         :name uniform-path-help-of-cdr
         :hints(("Goal" :in-theory (enable uniform-path-help))))
     (ok (implies (and ok (consp (cdr tterm-lst)))
                  (and (equal (typed-term-list->path-cond (cdr tterm-lst)) path-cond)
                       (equal (typed-term-list->path-cond tterm-lst) path-cond)))
         :name uniform-path-help-when-len-geq-2
         :hints(("Goal" :in-theory (enable uniform-path-help))))))

  (define uniform-path-cond? ((tterm-lst typed-term-list-p))
    :returns (ok booleanp)
    (uniform-path-help tterm-lst (typed-term-list->path-cond tterm-lst))
    ///
    (more-returns
     (ok (implies ok (uniform-path-cond? (cdr tterm-lst)))
         :name uniform-path-cond?-of-cdr
         :hints(("Goal" :cases(
                               (and (consp tterm-lst) (consp (cdr tterm-lst)))
                               (and (consp tterm-lst) (not (consp (cdr tterm-lst))))))))
     (ok (implies (and (typed-term-list-p tterm-lst)
                       (consp tterm-lst) (consp (cdr tterm-lst))
                       ok)
                  (equal (typed-term-list->path-cond (cdr tterm-lst))
                         (typed-term-list->path-cond tterm-lst)))
         :name equal-of-uniform-path-cond?)))

  ;; make-typed-term-list-guard -- state the relationship that
  ;; make-typed-term-list needs between term-lst and judges.
  ;; By moving this into the guard, the body of make-typed-term-list
  ;; doesn't need a bunch of ((if bad) (er ?hard ...)) bindings in its b*.
  ;; That makes reasoning about make-typed-term-list easier.
  (define make-typed-term-list-guard ((term-lst pseudo-term-listp)
                                      (path-cond pseudo-termp)
                                      (judges pseudo-termp))
    :returns (ok booleanp)
    :enabled t
    (b* (((unless (pseudo-term-listp term-lst)) nil)
         ((unless (pseudo-termp path-cond)) nil)
         ((unless (pseudo-termp judges)) nil)
         ((unless (is-conjunct? judges)) nil)
         ((if (and (null term-lst) (equal judges ''t))) t)
         ((if (or  (null term-lst) (equal judges ''t))) nil)
         (term-tl (cdr term-lst))
         ((list & & judge-tl &) judges)) ;; (if judge-hd judge-tl nil)
      (make-typed-term-list-guard term-tl path-cond judge-tl))
    ///
    (more-returns
     (ok (implies (and ok (consp term-lst))
                  (make-typed-term-list-guard (cdr term-lst) path-cond (caddr judges)))
         :name make-typed-term-list-guard-of-cdr
         :hints(("Goal" :in-theory (enable make-typed-term-list-guard))))
     (ok (implies (and ok (not (consp term-lst)))
                  (equal judges ''t))
         :name make-typed-term-list-guard-of-not-consp
         :hints(("Goal" :in-theory (enable make-typed-term-list-guard)))
         :rule-classes nil)))

  ;; make-typed-term-list-fix-judges
  ;;   A "fixing" function to make judges satisfy make-typed-term-list-guard.
  ;;   Takes about 20 seconds to define this function (2.6GHz, i5 Macbook Pro).
  ;;   The main culprit is the more-returns theorem
  ;;     make-typed-term-list-guard-of-make-typed-term-list-fix-judges
  (define make-typed-term-list-fix-judges ((term-lst pseudo-term-listp)
                                           (path-cond pseudo-termp)
                                           (judges pseudo-termp))
    :guard (make-typed-term-list-guard term-lst path-cond judges)
    :returns (j-fix pseudo-termp)
    :verify-guards nil
    (mbe
     :logic
     (b* ((term-lst (pseudo-term-list-fix term-lst))
          (path-cond (pseudo-term-fix path-cond))
          (judges (pseudo-term-fix judges))
          ((if (null term-lst)) ''t)
          ((mv judge-hd judge-tl)
           (if (and (is-conjunct? judges) (not (equal judges ''t)))
               (mv (cadr judges) (caddr judges))
             (mv ''t ''t)))
          (jtl-fix (make-typed-term-list-fix-judges (cdr term-lst)
                                                    path-cond
                                                    judge-tl)))
       `(if ,judge-hd ,jtl-fix 'nil))
     :exec judges)
    ///
    ;; mrg:  the proof of idempotence-of-make-typed-term-list-fix-judges
    ;;   fails when stated as a more-returns theorem but succeeds ;   this way
    (defthm idempotence-of-make-typed-term-list-fix-judges
      (let ((j-fix (make-typed-term-list-fix-judges tterm-lst path-cond judges)))
        (equal (make-typed-term-list-fix-judges tterm-lst path-cond j-fix) j-fix))
      :hints(("Goal"
              :in-theory (e/d (make-typed-term-list-fix-judges) (pseudo-termp)))))
    (more-returns
     (j-fix (make-typed-term-list-guard (pseudo-term-list-fix term-lst)
                                        (pseudo-term-fix path-cond)
                                        j-fix)
            :name
            make-typed-term-list-guard-of-make-typed-term-list-fix-judges)
     ;; make-typed-term-list-judges-fix-when-make-typed-term-list-guard
     ;; takes about 15 seconds to prove -- even if I give it a shorter name.
     ;; That's kind of annoying.  Might want to figure out why (i.e. why it
     ;; takes so long.  I know why waiting for the proof to finish is
     ;; annoying)
     ;; Yan: I disabled some rules, not it runs slightly faster
     (j-fix (implies (make-typed-term-list-guard term-lst path-cond judges)
                     (equal j-fix judges))
            :name make-typed-term-list-judges-fix-when-make-typed-term-list-guard
            :hints(("Goal" :in-theory (e/d (is-conjunct?
                                            make-typed-term-list-fix-judges)
                                           (symbol-listp
                                            acl2::symbolp-of-car-when-symbol-listp
                                            acl2::symbol-listp-of-cdr-when-symbol-listp))))))
    (verify-guards make-typed-term-list-fix-judges
      :hints(("Goal"
              :in-theory (disable make-typed-term-list-judges-fix-when-make-typed-term-list-guard)
              :use((:instance
                    make-typed-term-list-judges-fix-when-make-typed-term-list-guard)))))
    )

  (define make-typed-term-list ((term-lst pseudo-term-listp)
                                (path-cond pseudo-termp)
                                (judges pseudo-termp))
    :guard (make-typed-term-list-guard term-lst path-cond judges)
    :returns (tterm-lst typed-term-list-p)
    :guard-hints(("Goal"
                  :expand ((make-typed-term-list-guard term-lst path-cond judges))))
    (b* ((term-lst (pseudo-term-list-fix term-lst))
         (path-cond (pseudo-term-fix path-cond))
         (judges (make-typed-term-list-fix-judges term-lst path-cond judges))
         ((unless (consp term-lst)) nil)
         ((cons term-hd term-tl) term-lst)
         ((list & judge-hd judge-tl &) judges))
      (cons (make-typed-term :term term-hd :path-cond path-cond
                             :judgements judge-hd)
            (make-typed-term-list term-tl path-cond judge-tl)))
    ///
    ;; mrg: first, two lemmas about make-typed-term-list-fix-judges that
    ;;   are needed for the proof of
    ;;   typed-term-list->judgements-of-make-typed-term-list
    (local (defthm lemma-j1
             (implies (or (not (consp term-lst)) (not (consp (pseudo-term-list-fix term-lst))))
                      (equal (make-typed-term-list-fix-judges term-lst path-cond judges)
                             ''t))
             :hints(("Goal" :expand((make-typed-term-list-fix-judges term-lst path-cond judges))))))


    ;; mrg: lemma-j2 is a "cut-and-paste" lemma from a failed subgoal for
    ;;   typed-term-list->judgements-of-make-typed-term-list.  The proof
    ;;   feels a bit brittle.  See the comments in the theorem statement.
    (local (defthm lemma-j2
             (implies
              ;; the writer doesn't find lemma-j2 if the hypothesis is (consp term-lst)
              (consp (pseudo-term-list-fix term-lst))
              ;; the proof of typed-term-list->judgements-of-make-typed-term-list fails
              ;; with a rewrite loop if i don't use this (equal ... t) construction.
              (equal
               (equal (make-typed-term-list-fix-judges term-lst path-cond judges)
                      (list
                       'if
                       (pseudo-term-fix
                        (cadr (make-typed-term-list-fix-judges (pseudo-term-list-fix term-lst)
                                                               (pseudo-term-fix path-cond)
                                                               judges)))
                       (make-typed-term-list-fix-judges
                        (cdr (pseudo-term-list-fix term-lst))
                        (pseudo-term-fix path-cond)
                        (caddr (make-typed-term-list-fix-judges (pseudo-term-list-fix term-lst)
                                                                (pseudo-term-fix path-cond)
                                                                judges)))
                       ''nil))
               t))
             :hints(("Goal"
                     :expand(
                             (make-typed-term-list-fix-judges term-lst path-cond judges)
                             (make-typed-term-list-fix-judges (pseudo-term-list-fix term-lst)
                                                              (pseudo-term-fix path-cond)
                                                              judges))))))

    (more-returns
     ;; mrg: I changed acl2-count-of-typed-term-list->term-lst into a
     ;;   more-returns theorem (it had been a defthm) for consistency
     ;;   Note: we could also prove
     ;;     (equal (len (make-typed-term-list term-lst path-cond judges))
     ;;            (len term-lst))
     ;;   If that would be useful in subsequent measure proofs.
     (tterm-lst (<= (acl2-count (typed-term-list->term-lst tterm-lst))
                    (acl2-count term-lst))
                :name acl2-count-of-typed-term-list->term-lst
                :hints(("Goal" :in-theory (enable typed-term-list->term-lst)))
                :rule-classes :linear)
     ;; mrg: I added the more-returns theorems from here to the end of
     ;;      define make-typed-term-list.
     (tterm-lst (implies (consp term-lst) (consp tterm-lst))
                :name consp-of-make-typed-term-list
                :hints(("Goal"
                        :expand((make-typed-term-list term-lst path-cond judges)))))

     (tterm-lst (implies (not (consp term-lst)) (equal tterm-lst nil))
                :name null-of-make-typed-term-list
                :hints(("Goal"
                        :expand((make-typed-term-list term-lst path-cond judges)))))

     (tterm-lst (implies (pseudo-term-listp term-lst)
                         (equal (typed-term-list->term-lst tterm-lst) term-lst))
                :name typed-term-list->term-lst-of-make-typed-term-list
                :hints(("Goal" :in-theory (enable typed-term-list->term-lst))))

     (tterm-lst (equal (typed-term-list->path-cond tterm-lst)
                       (if (consp term-lst) (pseudo-term-fix path-cond) ''t))
                :name typed-term-list->path-cond-of-make-typed-term-list
                :hints(("Goal"
                        :in-theory (enable typed-term-list->path-cond))))

     (tterm-lst (equal (typed-term-list->judgements tterm-lst)
                       (make-typed-term-list-fix-judges term-lst path-cond judges))
                :name typed-term-list->judgements-of-make-typed-term-list
                :hints(("Goal" :in-theory (enable typed-term-list->judgements))))

     (tterm-lst (implies (pseudo-termp path-cond)
                         (uniform-path-help tterm-lst path-cond))
                :name uniform-path-help-of-make-typed-term-list
                :hints(("Goal"
                        :in-theory (enable uniform-path-help
                                           make-typed-term-list
                                           typed-term-list->path-cond))))

     (tterm-lst (implies (pseudo-termp path-cond)
                         (uniform-path-cond? tterm-lst))
                :name uniform-path-cond?-of-make-typed-term-list
                :hints(("Goal" :in-theory (enable uniform-path-cond?))))))
  )

(defsection make-typed-term-list-from-fields
  ;; mrg: my goal is to show that if tterm-lst is a typed-term-list-p
  ;;   and tterm-list satisfies uniform-path-cond?, then 
  ;;     (equal
  ;;       (make-typed-term-list
  ;;         (typed-term-list->term-lst tterm-lst)
  ;;         (typed-term-list->path-cond tterm-lst)
  ;;         (typed-term-list->judgements tterm-lst))
  ;;     tterm-lst)
  ;;   This is theorem make-typed-term-list-from-fields.
  ;;   
  ;;   Along the way, I prove a few other theorems that may be useful
  ;;   outside of this defsection:
  ;;     make-typed-term-list-guard-from-fields
  ;;       this theorem states that make-typed-term-list-guard is
  ;;       satisfied by
  ;;         (typed-term-list->term-lst tterm-lst)
  ;;         (typed-term-list->path-cond tterm-lst)
  ;;         (typed-term-list->judgements tterm-lst)
  ;;       no matter what tterm-lst is.  Aha, that's why I made the
  ;;       the changes that I did to those functions for the cases
  ;;       where tterm-lst is "bad".
  ;;
  ;;     car-of-make-typed-term-list
  ;;       If tterm-list is a non-nil typed-term-list-p, then
  ;;         (equal
  ;;           (car (make-typed-term-list
  ;;                 (typed-term-list->term-lst tterm-lst)
  ;;                 (typed-term-list->path-cond tterm-lst)
  ;;                 (typed-term-list->judgements tterm-lst)))
  ;;           (car tterm-lst))
  ;;       I don't need the uniform-path-cond? hypthesis here.

  (local (in-theory (disable pseudo-termp)))

  (local (defthm lemma-1
           (implies (pseudo-termp path-cond)
                    (make-typed-term-list-guard
                     (typed-term-list->term-lst tterm-lst)
                     path-cond
                     (typed-term-list->judgements tterm-lst)))
           :hints(("Goal"
                   :in-theory (enable
                               make-typed-term-list-guard
                               typed-term-list->term-lst
                               typed-term-list->judgements)))))

  (defthm make-typed-term-list-guard-from-fields
    (make-typed-term-list-guard
     (typed-term-list->term-lst tterm-lst)
     (typed-term-list->path-cond tterm-lst)
     (typed-term-list->judgements tterm-lst)))

  ;; I don't want to enable typed-term-list->judgements for the
  ;; proof of car-of-make-typed-term-list because it makes the
  ;; terms for the :expand hint much messier.
  (local (defthm lemma-2
           (implies
            (and (typed-term-list-p tterm-lst) (consp tterm-lst))
            (and (equal (cadr (typed-term-list->judgements tterm-lst))
                        (typed-term->judgements (car tterm-lst)))
                 (equal (caddr (typed-term-list->judgements tterm-lst))
                        (typed-term-list->judgements (cdr tterm-lst)))))
           :hints(("Goal" :in-theory (enable typed-term-list->judgements)))))

  (defthm car-of-make-typed-term-list
    (let ((tterm-lst2 (make-typed-term-list (typed-term-list->term-lst tterm-lst)
                                            (typed-term-list->path-cond tterm-lst)
                                            (typed-term-list->judgements tterm-lst))))
      (implies (and (typed-term-list-p tterm-lst) (consp tterm-lst))
               (equal (car tterm-lst2)(car tterm-lst))))
    :hints(("Goal"
            :in-theory (disable make-typed-term-list-guard-from-fields)
            :use((:instance make-typed-term-list-guard-from-fields))
            :expand(
                    (typed-term-list->term-lst tterm-lst)
                    (typed-term-list->path-cond tterm-lst)
                    (make-typed-term-list
                     (cons (typed-term->term (car tterm-lst))
                           (typed-term-list->term-lst (cdr tterm-lst)))
                     (typed-term->path-cond (car tterm-lst))
                     (typed-term-list->judgements tterm-lst))))))

  (local (defthmd lemma-3
           (implies (and (typed-term-list-p tterm-lst)
                         (uniform-path-help tterm-lst path-cond)
                         (pseudo-termp path-cond))
                    (let* ((term-lst1  (typed-term-list->term-lst tterm-lst))
                           (judges1    (typed-term-list->judgements tterm-lst))
                           (tterm-lst1 (make-typed-term-list term-lst1 path-cond judges1))
                           (term-lst2  (typed-term-list->term-lst (cdr tterm-lst)))
                           (judges2    (typed-term-list->judgements (cdr tterm-lst)))
                           (tterm-lst2 (make-typed-term-list term-lst2 path-cond judges2)))
                      (equal tterm-lst2 (cdr tterm-lst1))))
           :hints(("Goal"
                   :in-theory (disable lemma-1)
                   :use((:instance lemma-1))
                   :expand(
                           (typed-term-list->term-lst tterm-lst)
                           (typed-term-list->path-cond tterm-lst)
                           (typed-term-list->judgements tterm-lst)
                           (make-typed-term-list
                            (cons (typed-term->term (car tterm-lst))
                                  (typed-term-list->term-lst (cdr tterm-lst)))
                            path-cond
                            (list* 'if
                                   (typed-term->judgements (car tterm-lst))
                                   (typed-term-list->judgements (cdr tterm-lst))
                                   '('nil))))))))

  (local (defthm crock-pain-0
           (implies
            (uniform-path-help tterm-lst (typed-term-list->path-cond tterm-lst))
            (equal (make-typed-term-list (typed-term-list->term-lst (cdr tterm-lst))
                                         (typed-term-list->path-cond tterm-lst)
                                         (typed-term-list->judgements (cdr tterm-lst)))
                   (make-typed-term-list (typed-term-list->term-lst (cdr tterm-lst))
                                         (typed-term-list->path-cond (cdr tterm-lst))
                                         (typed-term-list->judgements (cdr tterm-lst)))))
           :hints(("Goal"
                   :cases((and (consp tterm-lst) (consp (cdr tterm-lst)))
                          (and (consp tterm-lst) (not (consp (cdr tterm-lst)))))))))

  (local (defthm crock-pain-1
           (let ((tterm-lst2 (make-typed-term-list (typed-term-list->term-lst tterm-lst)
                                                   (typed-term-list->path-cond tterm-lst)
                                                   (typed-term-list->judgements tterm-lst))))
             (implies
              (and (equal (make-typed-term-list (typed-term-list->term-lst (cdr tterm-lst))
                                                (typed-term-list->path-cond (cdr tterm-lst))
                                                (typed-term-list->judgements (cdr tterm-lst)))
                          (cdr tterm-lst))
                   (typed-term-list-p tterm-lst)
                   (uniform-path-help tterm-lst (typed-term-list->path-cond tterm-lst)))
              (equal (cdr tterm-lst2) (cdr tterm-lst))))
           :hints(
                  ("Goal"
                   :in-theory (disable lemma-3)
                   :use(
                        (:instance lemma-3 (path-cond (typed-term-list->path-cond tterm-lst))))))))

  (local (defthmd crock-pain-2
           (let ((tterm-lst2 (make-typed-term-list (typed-term-list->term-lst tterm-lst)
                                                   (typed-term-list->path-cond tterm-lst)
                                                   (typed-term-list->judgements tterm-lst))))
             (implies
              (and (typed-term-list-p tterm-lst) (consp tterm-lst) (consp tterm-lst2)
                   (equal (car tterm-lst2) (car tterm-lst))
                   (equal (cdr tterm-lst2) (cdr tterm-lst)))
              (equal tterm-lst2 tterm-lst)))
           :hints(("Goal"
                   :in-theory (disable car-of-make-typed-term-list consp-of-make-typed-term-list)))))

  (local (defthm crock-pain-3
           (let ((tterm-lst2 (make-typed-term-list (typed-term-list->term-lst tterm-lst)
                                                   (typed-term-list->path-cond tterm-lst)
                                                   (typed-term-list->judgements tterm-lst))))
             (implies
              (and (typed-term-list-p tterm-lst)
                   (equal (cdr tterm-lst2) (cdr tterm-lst)))
              (equal tterm-lst2 tterm-lst)))
           :hints(("Goal" :use((:instance crock-pain-2))))))

  (local (defthm crock-pain-4
           (let ((tterm-lst2 (make-typed-term-list (typed-term-list->term-lst tterm-lst)
                                                   (typed-term-list->path-cond tterm-lst)
                                                   (typed-term-list->judgements tterm-lst))))
             (implies
              (and (equal (make-typed-term-list (typed-term-list->term-lst (cdr tterm-lst))
                                                (typed-term-list->path-cond (cdr tterm-lst))
                                                (typed-term-list->judgements (cdr tterm-lst)))
                          (cdr tterm-lst))
                   (typed-term-list-p tterm-lst)
                   (uniform-path-help tterm-lst (typed-term-list->path-cond tterm-lst)))
              (equal tterm-lst2 tterm-lst)))))

  (defthm make-typed-term-list-from-fields
    (implies (and (typed-term-list-p tterm-lst)
                  (uniform-path-cond?  tterm-lst))
             (let* ((term-lst (typed-term-list->term-lst tterm-lst))
                    (path-cond (typed-term-list->path-cond tterm-lst))
                    (judges   (typed-term-list->judgements tterm-lst))
                    (tterm-lst2 (make-typed-term-list term-lst path-cond judges)))
               (equal tterm-lst2 tterm-lst)))
    :hints(("Goal"
            :in-theory (e/d (make-typed-term-list uniform-path-cond? uniform-path-help)
                            (crock-pain-0 crock-pain-1 crock-pain-2 crock-pain-3))))))


(define correct-typed-term ((tterm typed-term-p))
  :returns (res pseudo-termp)
  (b* ((tterm (typed-term-fix tterm)))
    `(implies ,(typed-term->path-cond tterm)
              ,(typed-term->judgements tterm))))

(define correct-typed-term-list ((tterm-lst typed-term-list-p))
  :returns (res pseudo-termp)
  (b* ((tterm-lst (typed-term-list-fix tterm-lst)))
    `(implies ,(typed-term-list->path-cond tterm-lst)
              ,(typed-term-list->judgements tterm-lst))))

(defthm correctness-of-make-typed-term
  (implies (and (ev-smtcp-meta-extract-global-facts)
                (alistp a))
           (ev-smtcp (correct-typed-term (make-typed-term)) a))
  :hints (("Goal"
           :in-theory (enable correct-typed-term))))
