;; Copyright (C) 2015, University of British Columbia
;; Written (originally) by Yan Peng (19th October, 2021)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2

(in-package "SMT")
(include-book "centaur/fty/top" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/strings/top" :dir :system)

(include-book "../../utils/basics")

(local (in-theory (enable symbol-symbol-alist-fix)))

(local
 (defthm crock1
   (implies (consp (symbol-symbol-alist-fix formals))
            (pseudo-termp (car (car (symbol-symbol-alist-fix formals))))))
 )

(define construct-formal-types ((formals symbol-symbol-alistp))
  :returns (formal-decls pseudo-termp)
  :measure (len (symbol-symbol-alist-fix formals))
  (b* ((formals (symbol-symbol-alist-fix formals))
       ((unless (consp formals)) ''t)
       ((cons formal-hd formal-tl) formals)
       ((cons formal formal-type) formal-hd))
    `(if (,formal-type ,formal)
         ,(construct-formal-types formal-tl)
       ''nil)))

(local
 (defthm crock2
   (pseudo-term-listp (symbol-list-fix formals))
   :hints (("Goal" :in-theory (enable pseudo-term-listp
                                      pseudo-termp
                                      symbol-list-fix))))
 )

(define construct-uninterpreted ((name symbolp)
                                 (formals symbol-listp)
                                 (formal-types symbol-listp)
                                 (return-type symbolp))
  :returns (property pseudo-termp)
  (b* ((name (symbol-fix name))
       ((if (equal name 'quote))
        (er hard? 'construct-uninterpreted=>construct-uninterpreted
            "Function name should not be 'quote.~%"))
       (formals (symbol-list-fix formals))
       (formal-types (symbol-list-fix formal-types))
       (return-type (symbol-fix return-type)))
    `(implies ,(construct-formal-types (pairlis$ formals formal-types))
              (,return-type (,name ,@formals)))))
