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

(define new-fresh-vars ((n natp)
                        (current symbol-listp))
  :returns (new-vars
            symbol-listp
            :hints (("Goal"
                     :in-theory (enable acl2::new-symbols-from-base))))
  (acl2::new-symbols-from-base n 'x current)
  ///
  (more-returns
   (new-vars (implies (and (natp n)
                           (symbol-listp current))
                      (equal (len new-vars) n))
             :name len-of-new-fresh-vars)))

(defthm consp-of-make-n-vars
  (implies (and (natp n) (not (zp n)))
           (consp (acl2::make-n-vars n base m avoid)))
  :hints (("Goal"
           :in-theory (enable acl2::make-n-vars))))

(defthm notnull-of-make-n-vars
  (implies (consp (acl2::make-n-vars n base m avoid))
           (car (acl2::make-n-vars n base m avoid)))
  :hints (("Goal"
           :in-theory (enable acl2::make-n-vars))))

(define new-fresh-var ((current symbol-listp))
  :returns (new-var symbolp)
  (car (new-fresh-vars 1 current))
  ///
  (more-returns
   (new-var (not (null new-var))
            :name notnull-of-new-fresh-var
            :hints (("Goal"
                     :in-theory (enable new-fresh-vars
                                        acl2::new-symbols-from-base))))))

(acl2::make-flag flag-all-vars1
                 all-vars1
                 :flag-mapping ((all-vars1     . term)
                                (all-vars1-lst . lst))
                 :defthm-macro-name defthm-all-vars1
                 :flag-var flag
                 )

(defthm-all-vars1
  (defthm type-of-all-vars1
    (implies (and (symbol-listp acl2::ans)
                  (pseudo-termp acl2::term))
             (symbol-listp (all-vars1 acl2::term acl2::ans)))
    :flag term
    :hints ((and stable-under-simplificationp
                 '(:in-theory (enable pseudo-termp pseudo-term-listp)
                              :expand (all-vars1 acl2::term acl2::ans)))))
  (defthm type-of-all-vars-lst
    (implies (and (symbol-listp acl2::ans)
                  (pseudo-term-listp acl2::lst))
             (symbol-listp (all-vars1-lst acl2::lst acl2::ans)))
    :flag lst
    :hints ((and stable-under-simplificationp
                 '(:expand (all-vars1-lst acl2::lst acl2::ans))))))
