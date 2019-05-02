;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (May 2019)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2

(in-package "SMT")
(include-book "std/util/define" :dir :system)
(include-book "std/util/bstar" :dir :system)
(include-book "centaur/fty/top" :dir :system) ; for defalist, etc.
(include-book "../top")
(include-book "basictypes")

(defprod sig
  ((module symbolp)
   (index integerp)))

(deflist sig-path
  :elt-type sig-p
  :true-listp t)

(deflist sig-path-list
  :elt-type sig-path
  :pred sig-path-listp
  :true-listp t)

(defalist any-table
  :key-type sig-path-p
  :val-type booleanp
  :true-listp t)

(deflist any-trace
  :elt-type any-table
  :true-listp t)

(define sigs-in-bool-table ((sigs sig-path-listp)
                            (st any-table-p))
  :returns (ok booleanp)
  :measure (len sigs)
  :hints (("Goal" :in-theory (enable sig-path-list-fix)))
  (b* ((sigs (sig-path-list-fix sigs))
       (st (any-table-fix st))
       ((unless (consp (sig-path-list-fix sigs))) t)
       (first (car (sig-path-list-fix sigs)))
       (rest (cdr (sig-path-list-fix sigs)))
       (first-v (assoc-equal first (any-table-fix st)))
       ((unless (consp (smt::magic-fix 'sig-path_booleanp first-v)))
        nil))
    (sigs-in-bool-table rest st)))

(define sigs-in-bool-trace ((sigs sig-path-listp)
                            (tr any-trace-p))
  :returns (ok booleanp)
  :measure (len tr)
  (b* ((sigs (sig-path-list-fix sigs))
       (tr (any-trace-fix tr))
       ((unless (consp (sig-path-list-fix sigs))) t)
       ((unless (consp (any-trace-fix tr))) t)
       (first (car (any-trace-fix tr)))
       (rest (cdr (any-trace-fix tr)))
       ((unless (sigs-in-bool-table sigs first)) nil))
    (sigs-in-bool-trace sigs rest)))

(define boolval ((bit booleanp))
  :returns (n integerp)
  (if (equal bit nil)
      0
    1))
