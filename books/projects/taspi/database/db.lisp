(in-package "ACL2")
(include-book "entry")
(include-book "../code/tree-manip/top")

;; change good db to check for consistency factors
;; ids must match up between tables
;;; model necessary for ml score
;; trees ordered by taxa-list

;; tables made up of appropriate good entries
(defun good-study-table-struct (tbl)
  (declare (xargs :guard t))
  (if (consp tbl)
      (and (good-study-entry (car tbl))
           (good-study-table-struct (cdr tbl)))
    t))

(defun good-analysis-table-struct (tbl)
  (declare (xargs :guard t))
  (if (consp tbl)
      (and (good-analysis-entry (car tbl))
           (good-analysis-table-struct (cdr tbl)))
    t))

(defun good-tree-table-struct (tbl)
  (declare (xargs :guard t))
  (if (consp tbl)
      (and (good-tree-entry (car tbl))
           (good-tree-table-struct (cdr tbl)))
    t))

;; function to get all primary keys
(defun get-ids (tbl)
  (declare (xargs :guard (or (good-study-table-struct tbl)
                             (good-analysis-table-struct tbl)
                             (good-tree-table-struct tbl))))
  (if (consp tbl)
      (cons (caar tbl) (get-ids (cdr tbl)))
    nil))

(defun good-study-table (tbl)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Recognizes a well-formed study table.~/
;  ~/
;  "
  (declare (xargs :guard t))
  (and (good-study-table-struct tbl)
       (no-dups-gen (get-ids tbl))))

(defun good-analysis-table (tbl)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Recognizes a well-formed analysis table.~/
;  ~/
;  "
  (declare (xargs :guard t))
  (and (good-analysis-table-struct tbl)
       (no-dups-gen (get-ids tbl))))

(defun good-tree-table (tbl)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Recognizes a well-formed tree table.~/
;  ~/
;  "
  (declare (xargs :guard t))
  (and (good-tree-table-struct tbl)
       (no-dups-gen (get-ids tbl))))

(defun get-study-ids (tbl)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns study ids present in an analysis table.~/
;  ~/
;  "
  (declare (xargs :guard (good-analysis-table-struct tbl)))
  (if (consp tbl)
      (cons (get-study-id (car tbl))
            (get-study-ids (cdr tbl)))
    nil))

(defun get-analysis-ids (tbl)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns analysis ids present in a tree table.~/
;  ~/
;  "
  (declare (xargs :guard (good-tree-table-struct tbl)))
  (if (consp tbl)
      (cons (get-analysis-id (car tbl))
            (get-analysis-ids (cdr tbl)))
    nil))

;; ids match up as required
(defun consistent-ids-all (study-tbl analysis-tbl tree-tbl)
  (declare (xargs :guard (and (good-study-table-struct study-tbl)
                              (good-analysis-table-struct analysis-tbl)
                              (good-tree-table-struct tree-tbl))))
  (let ((study-ids (get-ids study-tbl))
        (analysis-ids (get-ids analysis-tbl))
        (ref-study-ids (get-study-ids analysis-tbl))
        (ref-analysis-ids (get-analysis-ids tree-tbl)))
    (and (subset ref-study-ids study-ids)
         (subset ref-analysis-ids analysis-ids))))

(defun consistent-ids-analysis (study-tbl analysis-tbl)
  (declare (xargs :guard (and (good-study-table-struct study-tbl)
                              (good-analysis-table-struct analysis-tbl))))
   (let ((study-ids (get-ids study-tbl))
         (ref-study-ids (get-study-ids analysis-tbl)))
     (subset ref-study-ids study-ids)))

(defun consistent-ids-tree (analysis-tbl tree-tbl)
  (declare (xargs :guard (and (good-analysis-table-struct analysis-tbl)
                              (good-tree-table-struct tree-tbl))))
  (let ((analysis-ids (get-ids analysis-tbl))
        (ref-analysis-ids (get-analysis-ids tree-tbl)))
    (subset ref-analysis-ids analysis-ids)))

;; get an entry matching primary key
(defun get-entry-by-id (id tbl)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns entry in table indicated by given id.~/
;  ~/
;  Arguments:
;    (1) id - a primary id
;    (2) tbl - a good study, analysis or tree table
;
; "
  (declare (xargs :guard (or (good-study-table-struct tbl)
                             (good-analysis-table-struct tbl)
                             (good-tree-table-struct tbl))))
  (assoc-hqual id tbl))


;; functions to ensure that ml scores have a model associated
(defun get-analysis-ids-for-non-nil-ml (tree-tbl)
  (declare (xargs :guard (good-tree-table-struct tree-tbl)))
  (if (consp tree-tbl)
      (if (get-ml (car tree-tbl))
          (cons (get-analysis-id (car tree-tbl))
                (get-analysis-ids-for-non-nil-ml
                 (cdr tree-tbl)))
        (get-analysis-ids-for-non-nil-ml (cdr tree-tbl)))
    nil))

(defthm member-gen-get-ids-good-entry
  (implies (and (good-analysis-table-struct analysis-tbl)
                (member-gen x (get-ids analysis-tbl)))
           (good-analysis-entry (assoc-hqual x analysis-tbl)))
  :rule-classes :forward-chaining)

(defun check-for-model (ids analysis-tbl)
  (declare (xargs :guard (and (good-analysis-table-struct analysis-tbl)
                              (subset ids (get-ids analysis-tbl)))))
  (if (consp ids)
      (let ((entry (get-entry-by-id (car ids) analysis-tbl)))
        (if (get-model entry)
            (check-for-model (cdr ids) analysis-tbl)
          nil))
    t))

(defthm subset-get-analysis-ids-for-non-nil-ml-of-get-analysis
  (subset (get-analysis-ids-for-non-nil-ml tree-tbl)
          (get-analysis-ids tree-tbl)))

(defun ml-has-model (analysis-tbl tree-tbl)
  (declare (xargs :guard (and (good-analysis-table-struct analysis-tbl)
                              (good-tree-table-struct tree-tbl)
                              (consistent-ids-tree analysis-tbl
                                                   tree-tbl))
                  :guard-hints (("Goal''" :in-theory
                                 (disable subset-get-analysis-ids-for-non-nil-ml-of-get-analysis)
                                 :use
                                 (:instance
                                  subset-get-analysis-ids-for-non-nil-ml-of-get-analysis)))))
  (let ((analysis-ids (get-analysis-ids-for-non-nil-ml tree-tbl)))
    (check-for-model analysis-ids analysis-tbl)))

;; stuff here about good trees in relationship to taxa-list
(defun check-for-good-tree-tl (analysis-tbl tree-tbl)
  (declare (xargs :guard (and (good-analysis-table-struct analysis-tbl)
                              (good-tree-table-struct tree-tbl)
                              (consistent-ids-tree analysis-tbl tree-tbl))))
  (if (consp tree-tbl)
      (let* ((analysis-id (get-analysis-id (car tree-tbl)))
             (tree (get-tree (car tree-tbl)))
             (analysis-entry (get-entry-by-id analysis-id
                                              analysis-tbl))
             (tl (get-taxa-list analysis-entry)))
        (and (good-tree-tl tree tl)
             (check-for-good-tree-tl analysis-tbl (cdr tree-tbl))))
    t))

;; And then, a good database has all of the above properties
(defun good-treedb-struct (study-tbl analysis-tbl tree-tbl)
  (declare (xargs :guard t))
  (and (good-study-table-struct study-tbl)
       (good-analysis-table-struct analysis-tbl)
       (good-tree-table-struct tree-tbl)
       (consistent-ids-all study-tbl analysis-tbl tree-tbl)
       (ml-has-model analysis-tbl tree-tbl)
       (check-for-good-tree-tl analysis-tbl tree-tbl)))

(defun good-tree-db (study-tbl analysis-tbl tree-tbl)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Recognizes a well formed and consistent set of tables.~/
;  ~/
;  Arguments:
;    (1) study-tbl - a potential study table
;    (2) analysis-tbl - a potential analysis table
;    (3) tree-tbl - a potential tree table

;  Details: Checks that primary ids are unique, ids indexing into other tables
;           reference existing entries, maximum likelihood scores have an
;           associated model, and that any tree in the tree table has taxa
;           names present in the taxa list in the associated analysis table. "
  (declare (xargs :guard t))
  (and (good-study-table study-tbl)
       (good-analysis-table analysis-tbl)
       (good-tree-table tree-tbl)
       (consistent-ids-all study-tbl analysis-tbl tree-tbl)
       (ml-has-model analysis-tbl tree-tbl)
       (check-for-good-tree-tl analysis-tbl tree-tbl)))

#|| All of this to be updated to 3 table set up.

(defun get-trees-from-db (db)
  (declare (xargs :guard (good-treedb db)))
  (if (consp db)
      (cons (get-tree (cdar db))
            (get-trees-from-db (cdr db)))
    nil))

(defthm get-trees-from-db-when-not-consp
  (implies (not (consp db))
           (equal (get-trees-from-db db)
                  nil)))

(defthm get-trees-from-db-of-cons
  (equal (get-trees-from-db (cons first db))
         (cons (get-tree (cdr first))
               (get-trees-from-db db))))

(dis+ind get-trees-from-db)

(defthm good-treedb-cdr
  (implies (good-treedb x)
           (good-treedb (cdr x))))

(defthm tree-listp-get-trees
  (implies (good-treedb db)
           (tree-listp (get-trees-from-db db)))
  :hints (("Goal" :induct (len db))))

;(defthm good-treedb-gives-integerp-caar
;  (implies (good-treedb db)
;           (equal (integerp (caar db))
;                  (consp db))))

;(defthm good-treedb-good-entry-cdar
;  (implies (and (good-treedb x)
;                (consp x))
;           (good-entry (cdar x)))

;(defthm build-halistp
;  (implies (and (integerp x)
;                (halistp z))
;           (halistp (cons (cons x y) z))))

(defthm good-treedb-gives-halistp
  (implies (good-treedb db)
           (halistp db)))

(defun get-entry-from-db (id db)
  (declare (xargs :guard (good-treedb db)))
  (cdr (assoc-hqual id db)))

(defthm good-treedb-gives-good-entry-get-entry
  (implies (and (good-treedb x)
                (assoc-hqual i x))
           (good-entry (get-entry-from-db i x))))

(defthm good-treedb-not-assoc-gives-nil-get-entry
  (implies (and (good-treedb x)
                (not (assoc-hqual i x)))
           (equal (get-entry-from-db i x)
                  nil)))

(in-theory (disable get-entry-from-db))

;;; functions to get db's satifying a particular criteria
;;; about the entries
;;; one function for each piece of an entry, with theorem
;;; saying the result is correct.

(defthm good-entry-halistp
  (implies (good-entry x)
           (halistp x))
  :hints (("Goal" :expand (good-entry x))))

(defun good-pairing-to-add (pos val entry)
  (declare (xargs :guard t))
  (and (good-entry entry)
       (or ;;You can't change the taxa-list this way since
           ;; it requires the tree to be reordered
           ;;(and (equal pos 'taxa-list)
           ;;     (good-taxa-list val))
           ;; same with rooting... requires mv-root
           ;;(and (equal pos 'rooted?)
           ;;     (good-rooted-flg val))
           (and (equal pos 'brlens)
                (good-brlens-flg val))
           (and (equal pos 'tree)
                (good-tree val
                           (get-taxa-list entry)))
           (and (equal pos 'analysis-id)
                (good-analysis-id val))
           (and (equal pos 'date)
                (good-date val))
           (and (equal pos 'author)
                (good-author val))
           (and (equal pos 'tool)
                (good-tool val))
           (and (equal pos 'method)
                (good-method val))
           (and (equal pos 'data-type)
                (good-data-type val))
           (and (equal pos 'model)
                (if (rationalp (get-ml entry))
                    (stringp val)
                  (good-model val)))
           (and (equal pos 'ingroup)
                (good-ingroup val
                              (get-taxa-list entry)))
           (and (equal pos 'outgroup)
                (good-outgroup val
                               (get-taxa-list entry)))
           (and (equal pos 'mp)
                (good-mp val))
           (and (equal pos 'ml)
                (good-ml val
                         (get-model entry))))))

;Question : Should I be hopying the val??
(defun update-entry (pos val entry)
  (declare (xargs :guard
                  (and (good-entry entry)
                       (good-pairing-to-add pos val entry))))
  ;; remember, you can't change taxa-list cause then you
  ;; need to change the tree
  (hut pos val entry))


(defcong perm equal (good-taxa-list x) 1
  :hints (("Goal" :in-theory (enable good-taxa-list))))

(defun update-taxa-list-of-entry (entry tl)
  (declare (xargs :guard (and ;(good-taxa-list tl)
                              (good-entry entry)
                              (perm tl
                                    (get-taxa-list entry)))
                  :guard-hints
                  (("Subgoal 3" :in-theory
                    (disable
                     perm-implies-equal-good-taxa-list-1)
                    :use (:instance
                          perm-implies-equal-good-taxa-list-1
                          (x tl)
                          (x-equiv
                           (get-taxa-list entry)))))
                  ))
  (if (equal (get-taxa-list entry) tl)
      entry
    ;; update the taxa-list and reorder tree
    (if (perm tl (get-taxa-list entry))
        (cons (hons 'taxa-list tl)
              (cons (hons 'tree
                          (let ((new-tree (order-by-merge
                                           t
                                           (get-tree entry)
                                           (taxa-list-to-taxon-index tl))))
                            (if (get-rooted-flg entry)
                                new-tree
                              (mv-root new-tree))))
                    entry))
      entry)))

(defthm stringp-gives-stringp-or-nil
  (implies (stringp x)
           (stringp-or-nil x))
  :hints (("Goal" :in-theory (enable stringp-or-nil))))

(defthm good-entry-through-cons
  (implies (and (good-entry entry)
                (good-pairing-to-add pos val entry))
           (good-entry (cons (cons pos val)
                             entry)))
  :hints (("Goal"
           :in-theory (enable good-entry
                              get-model
                              get-taxa-list
                              get-ml))))

(defthm update-no-changes
  (and  (equal (get-brlens-flg (update-taxa-list-of-entry
                                entry tl))
               (get-brlens-flg entry))
        (equal (get-rooted-flg (update-taxa-list-of-entry
                                entry tl))
               (get-rooted-flg entry))
        (equal (get-analysis-id (update-taxa-list-of-entry
                                entry tl))
               (get-analysis-id entry))
        (equal (get-date (update-taxa-list-of-entry
                                entry tl))
               (get-date entry))
        (equal (get-author (update-taxa-list-of-entry
                                entry tl))
               (get-author entry))
        (equal (get-tool (update-taxa-list-of-entry
                                entry tl))
               (get-tool entry))
        (equal (get-method (update-taxa-list-of-entry
                                entry tl))
               (get-method entry))
        (equal (get-data-type (update-taxa-list-of-entry
                                entry tl))
               (get-data-type entry))
        (equal (get-model (update-taxa-list-of-entry
                                entry tl))
               (get-model entry))
        (equal (get-ingroup (update-taxa-list-of-entry
                                entry tl))
               (get-ingroup entry))
        (equal (get-outgroup (update-taxa-list-of-entry
                                entry tl))
               (get-outgroup entry))
        (equal (get-mp (update-taxa-list-of-entry
                                entry tl))
               (get-mp entry))
        (equal (get-ml (update-taxa-list-of-entry
                                entry tl))
               (get-ml entry)))
        :hints (("Goal" :in-theory
                 (enable
                  get-rooted-flg
                  get-brlens-flg
                  get-analysis-id
                  get-date
                  get-author
                  get-tool
                  get-method
                  get-data-type
                  get-model
                  get-ingroup
                  get-outgroup
                  get-mp
                  get-ml))))

(defthm update-changes
  (implies (and (perm (double-rewrite tl)
                      (get-taxa-list entry))
                (not (equal tl (get-taxa-list entry))))
           (and (equal (get-taxa-list (update-taxa-list-of-entry
                                       entry tl))
                       tl)
                (equal (get-tree (update-taxa-list-of-entry
                                  entry tl))
                       (let ((new-tree (order-by-merge
                                        t
                                        (get-tree entry)
                                        (taxa-list-to-taxon-index tl))))
                         (if (get-rooted-flg entry)
                             new-tree
                           (mv-root new-tree))))))
  :hints (("Goal" :in-theory (enable get-taxa-list
                                     get-tree))))

(defthm when-update-changes-nothing
  (implies (or (not (perm (double-rewrite tl)
                          (get-taxa-list entry)))
               (equal (double-rewrite tl)
                      (get-taxa-list entry)))
           (and (equal (get-tree (update-taxa-list-of-entry
                                  entry tl))
                       (get-tree entry))
                (equal (get-taxa-list (update-taxa-list-of-entry
                                       entry tl))
                       (get-taxa-list entry)))))

(in-theory (disable update-taxa-list-of-entry))

(defthm halistp-through-update
  (implies (halistp entry)
           (halistp (update-taxa-list-of-entry entry tl)))
  :hints (("Goal" :in-theory (enable update-taxa-list-of-entry))))


;; need a few more lemma about mv-root and order-by
;; currently skip-proofed in appropriate files

(defthm good-tree-through-order-by-merge
  (implies (and (good-tree tree tl)
                (good-taxa-list (double-rewrite tl))
                (perm (double-rewrite new-tl)
                      (double-rewrite tl)))
           (good-tree (order-by-merge
                       t tree
                       (taxa-list-to-taxon-index new-tl))
                      new-tl))
  :hints (("Goal" :in-theory (enable good-tree))))

(defthm good-tree-through-mv-root
  (implies (good-tree tree tl)
           (good-tree (mv-root tree)
                      tl))
  :hints (("Goal" :in-theory (enable good-tree))))

(defthm update-taxa-list-of-entry-gives-good-entry
  (implies (and (good-entry entry)
                (perm (double-rewrite tl)
                      (get-taxa-list entry)))
           (good-entry
            (update-taxa-list-of-entry entry tl)))
  :hints (("Goal" :in-theory (enable good-entry-redefinition))
          ("Goal'" :expand (good-entry (update-taxa-list-of-entry
                                        entry tl))
           :cases ((equal tl (get-taxa-list entry))))))

;;Question: Should these be honses? huts?
(defun unroot-tree-entry (entry)
  (declare (xargs :guard (good-entry entry)))
  (if (get-rooted-flg entry)
      (cons (cons 'rooted? nil)
            (cons (cons 'tree (mv-root (get-tree entry)))
                  entry))
    entry))

(defthm unroot-no-changes
  (and  (equal (get-brlens-flg (update-taxa-list-of-entry
                                entry tl))
               (get-brlens-flg entry))
        (equal (get-analysis-id (update-taxa-list-of-entry
                                entry tl))
               (get-analysis-id entry))
        (equal (get-date (update-taxa-list-of-entry
                                entry tl))
               (get-date entry))
        (equal (get-author (update-taxa-list-of-entry
                                entry tl))
               (get-author entry))
        (equal (get-tool (update-taxa-list-of-entry
                                entry tl))
               (get-tool entry))
        (equal (get-method (update-taxa-list-of-entry
                                entry tl))
               (get-method entry))
        (equal (get-data-type (update-taxa-list-of-entry
                                entry tl))
               (get-data-type entry))
        (equal (get-model (update-taxa-list-of-entry
                                entry tl))
               (get-model entry))
        (equal (get-ingroup (update-taxa-list-of-entry
                                entry tl))
               (get-ingroup entry))
        (equal (get-outgroup (update-taxa-list-of-entry
                                entry tl))
               (get-outgroup entry))
        (equal (get-mp (update-taxa-list-of-entry
                                entry tl))
               (get-mp entry))
        (equal (get-ml (update-taxa-list-of-entry
                                entry tl))
               (get-ml entry))
        (equal (get-taxa-list (unroot-tree-entry entry))
               (get-taxa-list entry)))
        :hints (("Goal" :in-theory
                 (enable
                  get-taxa-list
                  get-brlens-flg
                  get-analysis-id
                  get-date
                  get-author
                  get-tool
                  get-method
                  get-data-type
                  get-model
                  get-ingroup
                  get-outgroup
                  get-mp
                  get-ml))))

(defthm good-entry-unroot-tree-entry
  (implies (good-entry entry)
           (good-entry (unroot-tree-entry entry)))
  :hints (("Goal" :in-theory (enable good-entry
                                     get-tree))))

(in-theory (disable unroot-tree-entry))

(defun db-with-taxa-list (tl db)
  (declare (xargs :guard (good-treedb db)))
  (if (consp db)
      (if (perm tl (get-taxa-list (cdar db)))
          (cons (cons (caar db)
                      (update-taxa-list-of-entry
                       (cdar db) tl))
                (db-with-taxa-list tl (cdr db)))
        (db-with-taxa-list tl (cdr db)))
    nil))

(defthm db-with-taxa-list-when-not-consp
  (implies (not (consp db))
           (equal (db-with-taxa-list tl db)
                  nil)))

(defthm db-with-taxa-list-of-cons
  (equal (db-with-taxa-list tl (cons first rest))
         (if (perm (double-rewrite tl)
                   (get-taxa-list (cdr first)))
             (cons (cons (car first)
                      (update-taxa-list-of-entry
                       (cdr first) tl))
                   (db-with-taxa-list tl rest))
           (db-with-taxa-list tl rest))))

(in-theory (disable db-with-taxa-list))

(defun db-with-method (method db)
  (declare (xargs :guard (good-treedb db)))
  (if (consp db)
      (if (equal method (get-method (cdar db)))
          (cons (car db) (db-with-method method (cdr db)))
        (db-with-method method (cdr db)))
    nil))

(defthm db-with-method-when-not-consp
  (implies (not (consp db))
           (equal (db-with-method method db)
                  nil)))

(defthm db-with-method-of-cons
  (equal (db-with-method method (cons first rest))
         (if (equal method (get-method (cdr first)))
             (cons first (db-with-method method rest))
           (db-with-method method rest))))

(in-theory (disable db-with-method))

(defthm good-tree-db-with-method
  (implies (force (good-treedb db))
           (good-treedb (db-with-method method db)))
  :hints (("Goal" :induct (len db))))

(defthm assoc-db-with-method-gives-correct-get-method
  (implies (assoc-hqual i (db-with-method method db))
           (equal
            (get-method
             (cdr (assoc-hqual i
                               (db-with-method method db))))
            method))
  :hints (("Goal" :induct (len db))))

(defun db-with-date (date db)
  (declare (xargs :guard (good-treedb db)))
  (if (consp db)
      (if (equal date (get-date (cdar db)))
          (cons (car db) (db-with-date date (cdr db)))
        (db-with-date date (cdr db)))
    nil))

(defthm db-with-date-when-not-consp
  (implies (not (consp db))
           (equal (db-with-date date db)
                  nil)))

(defthm db-with-date-of-cons
  (equal (db-with-date date (cons first rest))
         (if (equal date (get-date (cdr first)))
             (cons first (db-with-date date rest))
           (db-with-date date rest))))

(in-theory (disable db-with-date))

(defthm good-tree-db-with-date
  (implies (force (good-treedb db))
           (good-treedb (db-with-date date db)))
  :hints (("Goal" :induct (len db))))

(defthm assoc-db-with-date-gives-correct-get-date
  (implies (assoc-hqual i (db-with-date date db))
           (equal
            (get-date
             (cdr (assoc-hqual i
                               (db-with-date date db))))
            date))
  :hints (("Goal" :induct (len db))))

(defun db-with-author (author db)
  (declare (xargs :guard (good-treedb db)))
  (if (consp db)
      (if (equal author (get-author (cdar db)))
          (cons (car db) (db-with-author author (cdr db)))
        (db-with-author author (cdr db)))
    nil))

(defthm db-with-author-when-not-consp
  (implies (not (consp db))
           (equal (db-with-author author db)
                  nil)))

(defthm db-with-author-of-cons
  (equal (db-with-author author (cons first rest))
         (if (equal author (get-author (cdr first)))
             (cons first (db-with-author author rest))
           (db-with-author author rest))))

(in-theory (disable db-with-author))

(defthm good-tree-db-with-author
  (implies (force (good-treedb db))
           (good-treedb (db-with-author author db)))
  :hints (("Goal" :induct (len db))))

(defthm assoc-db-with-author-gives-correct-get-author
  (implies (assoc-hqual i (db-with-author author db))
           (equal
            (get-author
             (cdr (assoc-hqual i
                               (db-with-author author db))))
            author))
  :hints (("Goal" :induct (len db))))


(defun db-with-tool (tool db)
  (declare (xargs :guard (good-treedb db)))
  (if (consp db)
      (if (equal tool (get-tool (cdar db)))
          (cons (car db) (db-with-tool tool (cdr db)))
        (db-with-tool tool (cdr db)))
    nil))

(defthm db-with-tool-when-not-consp
  (implies (not (consp db))
           (equal (db-with-tool tool db)
                  nil)))

(defthm db-with-tool-of-cons
  (equal (db-with-tool tool (cons first rest))
         (if (equal tool (get-tool (cdr first)))
             (cons first (db-with-tool tool rest))
           (db-with-tool tool rest))))

(in-theory (disable db-with-tool))

(defthm good-tree-db-with-tool
  (implies (force (good-treedb db))
           (good-treedb (db-with-tool tool db)))
  :hints (("Goal" :induct (len db))))

(defthm assoc-db-with-tool-gives-correct-get-tool
  (implies (assoc-hqual i (db-with-tool tool db))
           (equal
            (get-tool
             (cdr (assoc-hqual i
                               (db-with-tool tool db))))
            tool))
  :hints (("Goal" :induct (len db))))

(defun db-with-data-type (data-type db)
  (declare (xargs :guard (good-treedb db)))
  (if (consp db)
      (if (equal data-type (get-data-type (cdar db)))
          (cons (car db) (db-with-data-type data-type (cdr db)))
        (db-with-data-type data-type (cdr db)))
    nil))

(defthm db-with-data-type-when-not-consp
  (implies (not (consp db))
           (equal (db-with-data-type data-type db)
                  nil)))

(defthm db-with-data-type-of-cons
  (equal (db-with-data-type data-type (cons first rest))
         (if (equal data-type (get-data-type (cdr first)))
             (cons first (db-with-data-type data-type rest))
           (db-with-data-type data-type rest))))

(in-theory (disable db-with-data-type))

(defthm good-tree-db-with-data-type
  (implies (force (good-treedb db))
           (good-treedb (db-with-data-type data-type db)))
  :hints (("Goal" :induct (len db))))

(defthm assoc-db-with-data-type-gives-correct-get-data-type
  (implies (assoc-hqual i (db-with-data-type data-type db))
           (equal
            (get-data-type
             (cdr (assoc-hqual i
                               (db-with-data-type data-type db))))
            data-type))
  :hints (("Goal" :induct (len db))))

(defun db-with-analysis-id (analysis-id db)
  (declare (xargs :guard (good-treedb db)))
  (if (consp db)
      (if (equal analysis-id (get-analysis-id (cdar db)))
          (cons (car db) (db-with-analysis-id analysis-id (cdr db)))
        (db-with-analysis-id analysis-id (cdr db)))
    nil))

(defthm db-with-analysis-id-when-not-consp
  (implies (not (consp db))
           (equal (db-with-analysis-id analysis-id db)
                  nil)))

(defthm db-with-analysis-id-of-cons
  (equal (db-with-analysis-id analysis-id (cons first rest))
         (if (equal analysis-id (get-analysis-id (cdr first)))
             (cons first (db-with-analysis-id analysis-id rest))
           (db-with-analysis-id analysis-id rest))))

(in-theory (disable db-with-analysis-id))

(defthm good-tree-db-with-analysis-id
  (implies (force (good-treedb db))
           (good-treedb (db-with-analysis-id analysis-id db)))
  :hints (("Goal" :induct (len db))))

(defthm assoc-db-with-analysis-id-gives-correct-get-analysis-id
  (implies (assoc-hqual i (db-with-analysis-id analysis-id db))
           (equal
            (get-analysis-id
             (cdr (assoc-hqual i
                               (db-with-analysis-id analysis-id db))))
            analysis-id))
  :hints (("Goal" :induct (len db))))


(defun db-with-model (model db)
  (declare (xargs :guard (good-treedb db)))
  (if (consp db)
      (if (equal model (get-model (cdar db)))
          (cons (car db) (db-with-model model (cdr db)))
        (db-with-model model (cdr db)))
    nil))

(defthm db-with-model-when-not-consp
  (implies (not (consp db))
           (equal (db-with-model model db)
                  nil)))

(defthm db-with-model-of-cons
  (equal (db-with-model model (cons first rest))
         (if (equal model (get-model (cdr first)))
             (cons first (db-with-model model rest))
           (db-with-model model rest))))

(in-theory (disable db-with-model))

(defthm good-tree-db-with-model
  (implies (force (good-treedb db))
           (good-treedb (db-with-model model db)))
  :hints (("Goal" :induct (len db))))

(defthm assoc-db-with-model-gives-correct-get-model
  (implies (assoc-hqual i (db-with-model model db))
           (equal
            (get-model
             (cdr (assoc-hqual i
                               (db-with-model model db))))
            model))
  :hints (("Goal" :induct (len db))))

||#
