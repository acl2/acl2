;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (June 25th 2019)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;
(in-package "SMT")
(include-book "centaur/fty/top" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "clause-processors/generalize" :dir :system)

(include-book "pseudo-term")

(defthm symbol-list-of-append
  (implies (and (symbol-listp x)
                (symbol-listp y))
           (symbol-listp (append x y))))

;; (defthm cdr-of-member-equal
;;   (implies (not (member-equal x s))
;;            (not (member-equal x (cdr s)))))

(define new-fresh-vars ((n natp)
                        (avoid symbol-listp))
  :returns (new-vars
            symbol-listp
            :hints (("Goal"
                     :in-theory (enable acl2::new-symbols-from-base))))
  (acl2::new-symbols-from-base n 'x avoid)
  ///
  (more-returns
   (new-vars (implies (and (natp n)
                           (symbol-listp avoid))
                      (equal (len new-vars) n))
             :name len-of-new-fresh-vars))

  (defthm new-fresh-vars-not-in-avoid
    (implies (member-equal v avoid)
             (not (member-equal v (new-fresh-vars n avoid)))))

  (defthm new-fresh-vars-no-duplicates
    (no-duplicatesp-equal (new-fresh-vars n avoid)))

  (defthm consp-of-new-fresh-vars
    (implies (and (natp n) (not (zp n)))
             (consp (new-fresh-vars n avoid)))
    :hints (("Goal"
             :in-theory (enable new-fresh-vars acl2::make-n-vars
                                acl2::new-symbols-from-base))))

  (defthm notnull-of-new-fresh-vars
    (implies (consp (new-fresh-vars n avoid))
             (car (new-fresh-vars n avoid)))
    :hints (("Goal"
             :in-theory (enable new-fresh-vars acl2::make-n-vars
                                acl2::new-symbols-from-base)))))

(defthm new-fresh-vars-not-in-avoid-corrolary
  (implies (and (natp n) (not (zp n)))
           (not (member-equal (car (new-fresh-vars n avoid)) avoid)))
  :hints (("Goal"
           :in-theory (e/d () (new-fresh-vars-not-in-avoid))
           :Use ((:instance new-fresh-vars-not-in-avoid
                            (v (car (new-fresh-vars n avoid))))))))

(define new-fresh-var ((avoid symbol-listp))
  :returns (new-var symbolp)
  (car (new-fresh-vars 1 avoid))
  ///
  (more-returns
   (new-var (not (null new-var))
            :name notnull-of-new-fresh-var))

  (defthm new-fresh-var-not-in-avoid
    (not (member-equal (new-fresh-var avoid) avoid))))

;; (acl2::make-flag flag-all-vars1
;;                  all-vars1
;;                  :flag-mapping ((all-vars1     . term)
;;                                 (all-vars1-lst . lst))
;;                  :defthm-macro-name defthm-all-vars1
;;                  :flag-var flag
;;                  )

;; (defthm-all-vars1
;;   (defthm type-of-all-vars1
;;     (implies (and (symbol-listp acl2::ans)
;;                   (pseudo-termp acl2::term))
;;              (symbol-listp (all-vars1 acl2::term acl2::ans)))
;;     :flag term
;;     :hints ((and stable-under-simplificationp
;;                  '(:in-theory (enable pseudo-termp pseudo-term-listp)
;;                               :expand (all-vars1 acl2::term acl2::ans)))))
;;   (defthm type-of-all-vars-lst
;;     (implies (and (symbol-listp acl2::ans)
;;                   (pseudo-term-listp acl2::lst))
;;              (symbol-listp (all-vars1-lst acl2::lst acl2::ans)))
;;     :flag lst
;;     :hints ((and stable-under-simplificationp
;;                  '(:expand (all-vars1-lst acl2::lst acl2::ans))))))
