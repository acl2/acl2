(in-package "ACL2")

(include-book "db")

;; analysis-id(s)

(defun get-trees-with-analysis-id (analysis-id tree-tbl)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns trees from the tree table whose entries have the given
;  analysis-id.~/
;  ~/
;  Arguments:
;    (1) analysis-id - an id
;    (2) tree-tbl - a tree table

;  "
  (declare (xargs :guard (good-tree-table tree-tbl)))
  (if (consp tree-tbl)
      (if (equal (get-analysis-id (car tree-tbl)) analysis-id)
          (cons (get-tree (car tree-tbl))
                (get-trees-with-analysis-id analysis-id
                                            (cdr tree-tbl)))
        (get-trees-with-analysis-id analysis-id
                                    (cdr tree-tbl)))
    nil))

(defun get-tree-ids-with-analysis-id (analysis-id tree-tbl)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns tree ids from the tree table whose entries have the given
;  analysis-id.~/
;  ~/
;  Arguments:
;    (1) analysis-id - an id
;    (2) tree-tbl - a tree table
;
;  "
  (declare (xargs :guard (good-tree-table tree-tbl)))
  (if (consp tree-tbl)
      (if (equal (get-analysis-id (car tree-tbl)) analysis-id)
          (cons (get-id (car tree-tbl))
                (get-tree-ids-with-analysis-id analysis-id
                                            (cdr tree-tbl)))
        (get-tree-ids-with-analysis-id analysis-id
                                       (cdr tree-tbl)))
    nil))

(defun get-trees-with-analysis-ids (analysis-ids tree-tbl)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns trees from the tree table whose entries have one of the given
;  analysis-ids.~/
;  ~/
;  Arguments:
;    (1) analysis-ids - a list of ids
;    (2) tree-tbl - a tree table

;  "
  (declare (xargs :guard (good-tree-table tree-tbl)))
  (if (consp tree-tbl)
      (let ((cur-analysis-id (get-analysis-id (car tree-tbl))))
        (if (member-gen cur-analysis-id analysis-ids)
            (cons (get-tree (car tree-tbl))
                  (get-trees-with-analysis-ids analysis-ids
                                               (cdr tree-tbl)))
          (get-trees-with-analysis-ids analysis-ids
                                       (cdr tree-tbl))))
    nil))

(defun get-tree-ids-with-analysis-ids (analysis-ids tree-tbl)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns tree ids from the tree table whose entries have one of the given
;  analysis-ids.~/
;  ~/
;  Arguments:
;    (1) analysis-ids - a list of ids
;    (2) tree-tbl - a tree table
;
;  "
  (declare (xargs :guard (good-tree-table tree-tbl)))
  (if (consp tree-tbl)
      (let ((cur-analysis-id (get-analysis-id (car tree-tbl))))
        (if (member-gen cur-analysis-id analysis-ids)
            (cons (get-id (car tree-tbl))
                  (get-tree-ids-with-analysis-ids analysis-ids
                                                  (cdr tree-tbl)))
          (get-tree-ids-with-analysis-ids analysis-ids
                                          (cdr tree-tbl))))
    nil))

(defthm get-trees-with-analysis-id-when-not-consp
  (implies (not (consp tree-tbl))
           (equal (get-trees-with-analysis-id analysis-id tree-tbl)
                  nil)))

(defthm get-trees-with-analysis-id-of-consp
  (equal (get-trees-with-analysis-id analysis-id (cons first rest))
         (if (equal (get-analysis-id first) analysis-id)
             (cons (get-tree first)
                   (get-trees-with-analysis-id analysis-id
                                               rest))
           (get-trees-with-analysis-id analysis-id
                                       rest))))

(dis+ind get-trees-with-analysis-id)

(defthm tree-listp-get-trees-with-analysis-id
  (implies (good-tree-table tree-tbl)
           (tree-listp (get-trees-with-analysis-id ids tree-tbl))))

(defthm taspip-nil-get-trees-with-analysis-id
  (implies (good-tree-table tree-tbl)
           (taspip nil (get-trees-with-analysis-id ids tree-tbl))))

(dis+ind get-trees-with-analysis-id)

(defthm get-trees-with-analysis-ids-when-not-consp
  (implies (not (consp tree-tbl))
           (equal (get-trees-with-analysis-ids analysis-ids tree-tbl)
                  nil)))

(defthm get-trees-with-analysis-ids-of-consp
  (equal (get-trees-with-analysis-ids analysis-ids (cons first rest))
         (if (member-gen (get-analysis-id first) analysis-ids)
             (cons (get-tree first)
                   (get-trees-with-analysis-ids analysis-ids
                                               rest))
           (get-trees-with-analysis-ids analysis-ids
                                       rest))))

(defthm tree-listp-get-trees-with-analysis-ids
  (implies (good-tree-table tree-tbl)
           (tree-listp (get-trees-with-analysis-ids ids tree-tbl))))

(defthm taspip-nil-get-trees-with-analysis-ids
  (implies (good-tree-table tree-tbl)
           (taspip nil (get-trees-with-analysis-ids ids tree-tbl))))

(in-theory (disable get-trees-with-analysis-ids))

;; taxon

(defun get-analysis-ids-with-taxon (taxon analysis-tbl)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns analysis ids from the analysis table whose entries have the given
;  taxon.~/
;  ~/
;  Arguments:
;    (1) taxon - a taxon name
;    (2) analysis-tbl - an analysis table
;
;  "
  (declare (xargs :guard (good-analysis-table analysis-tbl)))
  (if (consp analysis-tbl)
      (if (member-gen taxon (get-taxa-list (car analysis-tbl)))
          (cons (get-id (car analysis-tbl))
                (get-analysis-ids-with-taxon taxon
                                             (cdr analysis-tbl)))
        (get-analysis-ids-with-taxon taxon
                                     (cdr analysis-tbl)))
    nil))

(defun get-trees-with-taxon (taxon analysis-tbl tree-tbl)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns trees from the tree table that have the given taxon.~/
;  ~/
;  Arguments:
;    (1) taxon - a taxon name
;    (2) analysis-tbl - an analysis table
;    (3) tree-tbl - a tree table
;
;  "
  (declare (xargs :guard (and (good-analysis-table analysis-tbl)
                              (good-tree-table tree-tbl))))
  (let ((analysis-ids (get-analysis-ids-with-taxon taxon analysis-tbl)))
    (get-trees-with-analysis-ids analysis-ids tree-tbl)))

(defun get-tree-ids-with-taxon (taxon analysis-tbl tree-tbl)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns tree ids from the tree table that have the given taxon.~/
;  ~/
;  Arguments:
;    (1) taxon - a taxon name
;    (2) analysis-tbl - an analysis table
;    (3) tree-tbl - a tree table
;
;  "
  (declare (xargs :guard (and (good-analysis-table analysis-tbl)
                              (good-tree-table tree-tbl))))
  (let ((analysis-ids (get-analysis-ids-with-taxon taxon analysis-tbl)))
    (get-tree-ids-with-analysis-ids analysis-ids tree-tbl)))

(defthm tree-listp-get-trees-with-taxon
  (implies (good-tree-table tree-tbl)
           (tree-listp (get-trees-with-taxon taxon
                                             analysis-tbl
                                             tree-tbl))))

(defthm taspip-nil-get-trees-with-taxon
  (implies (good-tree-table tree-tbl)
           (taspip nil (get-trees-with-taxon taxon
                                             analysis-tbl
                                             tree-tbl))))

(in-theory (disable get-trees-with-taxon))

;; taxa

(defun get-analysis-ids-with-taxa (taxa analysis-tbl)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns analysis ids from the analysis table that have the given set of
;  taxa.~/
;  ~/
;  Arguments:
;    (1) taxa - a list of taxa name
;    (2) analysis-tbl - an analysis table
;
;  "
  (declare (xargs :guard (good-analysis-table analysis-tbl)))
  (if (consp analysis-tbl)
      (if (subset taxa (get-taxa-list (car analysis-tbl)))
          (cons (get-id (car analysis-tbl))
                (get-analysis-ids-with-taxa taxa (cdr analysis-tbl)))
        (get-analysis-ids-with-taxa taxa (cdr analysis-tbl)))
    nil))

(defun get-trees-with-taxa (taxa analysis-tbl tree-tbl)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns trees from the tree table that have the given set of
;  taxa.~/
;  ~/
;  Arguments:
;    (1) taxa - a list of taxa name
;    (2) analysis-tbl - an analysis table
;    (3) tree-tbl - a tree table
;
;  "
  (declare (xargs :guard (and (good-analysis-table analysis-tbl)
                              (good-tree-table tree-tbl))))
  (let ((analysis-ids (get-analysis-ids-with-taxa taxa analysis-tbl)))
    (get-trees-with-analysis-ids analysis-ids tree-tbl)))

(defun get-tree-ids-with-taxa (taxa analysis-tbl tree-tbl)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns trees from the tree table that have the given set of
;  taxa.~/
;  ~/
;  Arguments:
;    (1) taxa - a list of taxa name
;    (2) analysis-tbl - an analysis table
;    (3) tree-tbl - a tree table
;
;  "
  (declare (xargs :guard (and (good-analysis-table analysis-tbl)
                              (good-tree-table tree-tbl))))
  (let ((analysis-ids (get-analysis-ids-with-taxa taxa analysis-tbl)))
    (get-tree-ids-with-analysis-ids analysis-ids tree-tbl)))

(defun subset-each (x list)
  (declare (xargs :guard t))
  (if (consp list)
      (and (subset x (car list))
           (subset-each x (cdr list)))
    t))

(defun mytips-list (list)
  (declare (xargs :guard t))
  (if (consp list)
      (cons (mytips (car list))
            (mytips-list (cdr list)))
    nil))

(defthm not-member-get-ids-through-get-analysis-ids-with-taxa
  (implies (and (good-analysis-table y)
                (not (member-gen x (get-ids y))))
           (not (member-gen x (get-analysis-ids-with-taxa
                               taxa y))))
  :hints (("Goal" :in-theory (enable get-id))))

(defthm member-id-ids-with-taxa-subset-mytips
  (implies (and (good-analysis-table analysis-tbl)
                (member-gen
                 x
                 (get-analysis-ids-with-taxa taxa
                                             analysis-tbl)))
           (subset taxa (get-taxa-list
                         (get-entry-by-id x analysis-tbl))))
  :hints (("Goal" :in-theory (enable get-id))
          ("Subgoal *1/2'" :in-theory (disable perm-implies-subset
                                               subset-transitive))))

(in-theory (disable good-analysis-table
                    get-entry-by-id))

(defthm subset-taxa-mytips-trees-with-taxa
  (implies (and (good-tree-table tree-tbl)
                (good-analysis-table analysis-tbl)
                (check-for-good-tree-tl analysis-tbl tree-tbl))
           (subset-each taxa (mytips-list (get-trees-with-taxa
                                           taxa
                                           analysis-tbl
                                           tree-tbl))))
  :hints (("Subgoal *1/4.4'''" :in-theory
           (disable member-id-ids-with-taxa-subset-mytips)
           :use (:instance
                 member-id-ids-with-taxa-subset-mytips
                 (x (get-analysis-id (cons tree-tbl3
                                           tree-tbl4)))))
          ("Subgoal *1/4.3'''" :in-theory
           (disable member-id-ids-with-taxa-subset-mytips)
           :use (:instance
                 member-id-ids-with-taxa-subset-mytips
                 (x (get-analysis-id (cons tree-tbl3
                                           tree-tbl4)))))
          ("Subgoal *1/4.2'''" :in-theory
           (disable member-id-ids-with-taxa-subset-mytips)
           :use (:instance
                 member-id-ids-with-taxa-subset-mytips
                 (x (get-analysis-id (cons tree-tbl3
                                           tree-tbl4)))))
          ("Subgoal *1/4.1'''" :in-theory
           (disable member-id-ids-with-taxa-subset-mytips)
           :use (:instance
                 member-id-ids-with-taxa-subset-mytips
                 (x (get-analysis-id (cons tree-tbl3
                                           tree-tbl4)))))))

(defthm good-analysis-table-of-consp
  (implies (good-analysis-table (cons first rest))
           (and (good-analysis-entry first)
                (good-analysis-table rest)))
  :hints (("Goal" :in-theory (enable good-analysis-table))))

(defthm good-analysis-entry-consp
  (implies (good-analysis-entry entry)
           (consp entry))
  :rule-classes :forward-chaining)

(defthm good-analysis-table-gives-good-entry
  (implies (good-analysis-table (cons first rest))
           (good-analysis-entry first))
  :rule-classes :forward-chaining)

;; n taxa

(defun get-analysis-ids-with-n-taxa (n analysis-tbl)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns analysis ids from the analysis table that have the given number
;  taxa.~/
;  ~/
;  Arguments:
;    (1) n - an integer
;    (2) analysis-tbl - an analysis table
;
;  "
  (declare (xargs :guard (good-analysis-table analysis-tbl)))
  (if (consp analysis-tbl)
      (if (equal (len (get-taxa-list (car analysis-tbl)))
                 n)
          (cons (get-id (car analysis-tbl))
                (get-analysis-ids-with-n-taxa n (cdr analysis-tbl)))
        (get-analysis-ids-with-n-taxa n (cdr analysis-tbl)))
    nil))

(defun get-trees-with-n-taxa (n analysis-tbl tree-tbl)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns trees from the tree table that have the given number taxa.~/
;  ~/
;  Arguments:
;    (1) n - an integer
;    (2) analysis-tbl - an analysis table
;    (3) tree-tbl - a tree table

;  "
  (declare (xargs :guard (and (good-analysis-table analysis-tbl)
                              (good-tree-table tree-tbl))))
  (let ((analysis-ids (get-analysis-ids-with-n-taxa n analysis-tbl)))
    (get-trees-with-analysis-ids analysis-ids tree-tbl)))

(defun get-tree-ids-with-n-taxa (n analysis-tbl tree-tbl)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns tree ids from the tree table that have the given number taxa.~/
;  ~/
;  Arguments:
;    (1) n - an integer
;    (2) analysis-tbl - an analysis table
;    (3) tree-tbl - a tree table

;  "
  (declare (xargs :guard (and (good-analysis-table analysis-tbl)
                              (good-tree-table tree-tbl))))
  (let ((analysis-ids (get-analysis-ids-with-n-taxa n analysis-tbl)))
    (get-tree-ids-with-analysis-ids analysis-ids tree-tbl)))

;; method

(defun get-analysis-ids-with-method (method analysis-tbl)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns analysis ids from the analysis table that have the given method.~/
;  ~/
;  Arguments:
;    (1) method - a method name
;    (2) analysis-tbl - an analysis table
;
;  "
  (declare (xargs :guard (good-analysis-table analysis-tbl)))
  (if (consp analysis-tbl)
      (if (equal (get-method (car analysis-tbl))
                 method)
          (cons (get-id (car analysis-tbl))
                (get-analysis-ids-with-method method (cdr analysis-tbl)))
        (get-analysis-ids-with-method method (cdr analysis-tbl)))
    nil))

(defun get-trees-with-method (method analysis-tbl tree-tbl)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns trees from the tree table that have the given method.~/
;  ~/
;  Arguments:
;    (1) method - a method name
;    (2) analysis-tbl - an analysis table
;    (3) tree-tbl - a tree table
;
;  "
  (declare (xargs :guard (and (good-analysis-table analysis-tbl)
                              (good-tree-table tree-tbl))))
  (let ((analysis-ids (get-analysis-ids-with-method method analysis-tbl)))
    (get-trees-with-analysis-ids analysis-ids tree-tbl)))

(defun get-tree-ids-with-method (method analysis-tbl tree-tbl)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns tree ids from the tree table that have the given method.~/
;  ~/
;  Arguments:
;    (1) method - a method name
;    (2) analysis-tbl - an analysis table
;    (3) tree-tbl - a tree table
;
;  "
  (declare (xargs :guard (and (good-analysis-table analysis-tbl)
                              (good-tree-table tree-tbl))))
  (let ((analysis-ids (get-analysis-ids-with-method method analysis-tbl)))
    (get-tree-ids-with-analysis-ids analysis-ids tree-tbl)))

;; date

(defun get-analysis-ids-with-date (date analysis-tbl)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns tree ids from the tree table that have the given date.~/
;  ~/
;  Arguments:
;    (1) date - a date name
;    (2) analysis-tbl - an analysis table
;    (3) tree-tbl - a tree table
;
;  "
  (declare (xargs :guard (good-analysis-table analysis-tbl)))
  (if (consp analysis-tbl)
      (if (equal (get-date (car analysis-tbl))
                 date)
          (cons (get-id (car analysis-tbl))
                (get-analysis-ids-with-date date (cdr analysis-tbl)))
        (get-analysis-ids-with-date date (cdr analysis-tbl)))
    nil))

(defun get-trees-with-date (date analysis-tbl tree-tbl)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns trees from the tree table that have the given date.~/
;  ~/
;  Arguments:
;    (1) date - a date name
;    (2) analysis-tbl - an analysis table
;    (3) tree-tbl - a tree table
;
;  "
  (declare (xargs :guard (and (good-analysis-table analysis-tbl)
                              (good-tree-table tree-tbl))))
  (let ((analysis-ids (get-analysis-ids-with-date date analysis-tbl)))
    (get-trees-with-analysis-ids analysis-ids tree-tbl)))

(defun get-tree-ids-with-date (date analysis-tbl tree-tbl)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns tree ids from the tree table that have the given date.~/
;  ~/
;  Arguments:
;    (1) date - a date name
;    (2) analysis-tbl - an analysis table
;    (3) tree-tbl - a tree table
;
;  "
  (declare (xargs :guard (and (good-analysis-table analysis-tbl)
                              (good-tree-table tree-tbl))))
  (let ((analysis-ids (get-analysis-ids-with-date date analysis-tbl)))
    (get-tree-ids-with-analysis-ids analysis-ids tree-tbl)))

;; author

(defun get-analysis-ids-with-author (author analysis-tbl)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns tree ids from the tree table that have the given author.~/
;  ~/
;  Arguments:
;    (1) author - a author name
;    (2) analysis-tbl - an analysis table
;    (3) tree-tbl - a tree table
;
;  "
  (declare (xargs :guard (good-analysis-table analysis-tbl)))
  (if (consp analysis-tbl)
      (if (equal (get-author (car analysis-tbl))
                 author)
          (cons (get-id (car analysis-tbl))
                (get-analysis-ids-with-author author (cdr analysis-tbl)))
        (get-analysis-ids-with-author author (cdr analysis-tbl)))
    nil))

(defun get-trees-with-author (author analysis-tbl tree-tbl)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns trees from the tree table that have the given author.~/
;  ~/
;  Arguments:
;    (1) author - a author name
;    (2) analysis-tbl - an analysis table
;    (3) tree-tbl - a tree table
;
;  "
  (declare (xargs :guard (and (good-analysis-table analysis-tbl)
                              (good-tree-table tree-tbl))))
  (let ((analysis-ids (get-analysis-ids-with-author author analysis-tbl)))
    (get-trees-with-analysis-ids analysis-ids tree-tbl)))

(defun get-tree-ids-with-author (author analysis-tbl tree-tbl)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns tree ids from the tree table that have the given author.~/
;  ~/
;  Arguments:
;    (1) author - a author name
;    (2) analysis-tbl - an analysis table
;    (3) tree-tbl - a tree table
;
;  "
  (declare (xargs :guard (and (good-analysis-table analysis-tbl)
                              (good-tree-table tree-tbl))))
  (let ((analysis-ids (get-analysis-ids-with-author author analysis-tbl)))
    (get-tree-ids-with-analysis-ids analysis-ids tree-tbl)))

;; tool

(defun get-analysis-ids-with-tool (tool analysis-tbl)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns tree ids from the tree table that have the given tool.~/
;  ~/
;  Arguments:
;    (1) tool - a tool name
;    (2) analysis-tbl - an analysis table
;    (3) tree-tbl - a tree table
;
;  "
  (declare (xargs :guard (good-analysis-table analysis-tbl)))
  (if (consp analysis-tbl)
      (if (equal (get-tool (car analysis-tbl))
                 tool)
          (cons (get-id (car analysis-tbl))
                (get-analysis-ids-with-tool tool (cdr analysis-tbl)))
        (get-analysis-ids-with-tool tool (cdr analysis-tbl)))
    nil))

(defun get-trees-with-tool (tool analysis-tbl tree-tbl)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns trees from the tree table that have the given tool.~/
;  ~/
;  Arguments:
;    (1) tool - a tool name
;    (2) analysis-tbl - an analysis table
;    (3) tree-tbl - a tree table
;
;  "
  (declare (xargs :guard (and (good-analysis-table analysis-tbl)
                              (good-tree-table tree-tbl))))
  (let ((analysis-ids (get-analysis-ids-with-tool tool analysis-tbl)))
    (get-trees-with-analysis-ids analysis-ids tree-tbl)))

(defun get-tree-ids-with-tool (tool analysis-tbl tree-tbl)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns tree ids from the tree table that have the given tool.~/
;  ~/
;  Arguments:
;    (1) tool - a tool name
;    (2) analysis-tbl - an analysis table
;    (3) tree-tbl - a tree table
;
;  "
  (declare (xargs :guard (and (good-analysis-table analysis-tbl)
                              (good-tree-table tree-tbl))))
  (let ((analysis-ids (get-analysis-ids-with-tool tool analysis-tbl)))
    (get-tree-ids-with-analysis-ids analysis-ids tree-tbl)))

;; data-type

(defun get-analysis-ids-with-data-type (data-type analysis-tbl)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns tree ids from the tree table that have the given data type.~/
;  ~/
;  Arguments:
;    (1) data-type - a data type name
;    (2) analysis-tbl - an analysis table
;    (3) tree-tbl - a tree table
;
;  "
  (declare (xargs :guard (good-analysis-table analysis-tbl)))
  (if (consp analysis-tbl)
      (if (equal (get-data-type (car analysis-tbl))
                 data-type)
          (cons (get-id (car analysis-tbl))
                (get-analysis-ids-with-data-type data-type (cdr analysis-tbl)))
        (get-analysis-ids-with-data-type data-type (cdr analysis-tbl)))
    nil))

(defun get-trees-with-data-type (data-type analysis-tbl tree-tbl)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns trees from the tree table that have the given data type.~/
;  ~/
;  Arguments:
;    (1) data-type - a data type name
;    (2) analysis-tbl - an analysis table
;    (3) tree-tbl - a tree table
;
;  "
  (declare (xargs :guard (and (good-analysis-table analysis-tbl)
                              (good-tree-table tree-tbl))))
  (let ((analysis-ids (get-analysis-ids-with-data-type data-type analysis-tbl)))
    (get-trees-with-analysis-ids analysis-ids tree-tbl)))

(defun get-tree-ids-with-data-type (data-type analysis-tbl tree-tbl)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns tree ids from the tree table that have the given data type.~/
;  ~/
;  Arguments:
;    (1) data-type - a data-type name
;    (2) analysis-tbl - an analysis table
;    (3) tree-tbl - a tree table
;
;  "
  (declare (xargs :guard (and (good-analysis-table analysis-tbl)
                              (good-tree-table tree-tbl))))
  (let ((analysis-ids (get-analysis-ids-with-data-type data-type analysis-tbl)))
    (get-tree-ids-with-analysis-ids analysis-ids tree-tbl)))

;; model

(defun get-analysis-ids-with-model (model analysis-tbl)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns tree ids from the tree table that have the given model.~/
;  ~/
;  Arguments:
;    (1) model - a model name
;    (2) analysis-tbl - an analysis table
;    (3) tree-tbl - a tree table
;
;  "
  (declare (xargs :guard (good-analysis-table analysis-tbl)))
  (if (consp analysis-tbl)
      (if (equal (get-model (car analysis-tbl))
                 model)
          (cons (get-id (car analysis-tbl))
                (get-analysis-ids-with-model model (cdr analysis-tbl)))
        (get-analysis-ids-with-model model (cdr analysis-tbl)))
    nil))

(defun get-trees-with-model (model analysis-tbl tree-tbl)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns trees from the tree table that have the given model.~/
;  ~/
;  Arguments:
;    (1) model - a model name
;    (2) analysis-tbl - an analysis table
;    (3) tree-tbl - a tree table
;
;  "
  (declare (xargs :guard (and (good-analysis-table analysis-tbl)
                              (good-tree-table tree-tbl))))
  (let ((analysis-ids (get-analysis-ids-with-model model analysis-tbl)))
    (get-trees-with-analysis-ids analysis-ids tree-tbl)))

(defun get-tree-ids-with-model (model analysis-tbl tree-tbl)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns tree ids from the tree table that have the given model.~/
;  ~/
;  Arguments:
;    (1) model - a model name
;    (2) analysis-tbl - an analysis table
;    (3) tree-tbl - a tree table
;
;  "
  (declare (xargs :guard (and (good-analysis-table analysis-tbl)
                              (good-tree-table tree-tbl))))
  (let ((analysis-ids (get-analysis-ids-with-model model analysis-tbl)))
    (get-tree-ids-with-analysis-ids analysis-ids tree-tbl)))
