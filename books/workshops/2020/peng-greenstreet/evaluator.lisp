;; Copyright (C) 2019, University of British Columbia
;; Written by Yan Peng (December 30th 2019)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "ACL2")
(include-book "xdoc/top" :dir :system)
(include-book "tools/defevaluator-fast" :dir :system)
(include-book "clause-processors/just-expand" :dir :system)
(include-book "clause-processors/meta-extract-user" :dir :system)

;; -----------------------------------------------------------------
;;       Define evaluators

(acl2::defevaluator-fast ev-smtcp ev-smtcp-lst
                         ((if a b c) (equal a b) (not a)
                          (cons a b) (binary-+ a b)
                          (typespec-check ts x)
                          (iff a b)
                          (implies a b))
                         :namedp t)

(acl2::def-ev-theoremp ev-smtcp)
(acl2::def-meta-extract ev-smtcp ev-smtcp-lst)
(acl2::def-unify ev-smtcp ev-smtcp-alist)

(defthm ev-smtcp-of-disjoin
  (iff (ev-smtcp (disjoin clause) a)
       (acl2::or-list (ev-smtcp-lst clause a)))
  :hints(("Goal" :in-theory (enable acl2::or-list len)
          :induct (len clause))))

(defthm ev-smtcp-alist-of-pairlis$
  (equal (ev-smtcp-alist (pairlis$ x y) a)
         (pairlis$ x (ev-smtcp-lst y a))))
