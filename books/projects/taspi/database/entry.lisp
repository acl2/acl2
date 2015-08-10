(in-package "ACL2")
(include-book "props")

;; Currently, table are not honsed up, though we will take care
;; to hons
;; use assoc-hqual since we don't care if the last atom is nil
(defmacro my-get (x y)
  `(cdr (assoc-hqual ,x ,y)))

;; Stubs are used a placeholders for recognizing appropriately formed
;; sequences and mappings of taxon names to identifiers
(defstub good-sequences (x)
  t)

(defstub good-mapping (x)
  t)

;; key for each entry is the id, then rest of attributes are
;; an alist of values
(defun good-study-entry (entry)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Recognizes a well-formed study table entry.~/
;  ~/
;  "
  (declare (xargs :guard t))
  (if (consp entry)
      (let ((study-id (car entry))
            (rest (cdr entry)))
        (let ((seqs (my-get 'sequences rest))
              (map (my-get 'mapping rest))
              (name (my-get 'name rest)))
          (and (good-id study-id)
               (good-sequences seqs)
               (good-mapping map)
               (good-name name))))
        nil))

(defun good-analysis-entry (entry)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Recognizes a well-formed analysis table entry.~/
;  ~/
;  "
  (declare (xargs :guard t))
  (if (consp entry)
      (let ((analysis-id (car entry))
            (rest (cdr entry)))
        (let ((study-id (my-get 'study-id rest))
              (name (my-get 'name rest))
              (method (my-get 'method rest))
              (dtype (my-get 'data-type rest))
              (model (my-get 'model rest))
              (date (my-get 'date rest))
              (tool (my-get 'tool rest))
              (author (my-get 'author rest))
              (tl (my-get 'taxa-list rest))
              (ingroup (my-get 'ingroup rest))
              (outgroup (my-get 'outgroup rest)))
          (and (good-id analysis-id)
               (good-id study-id)
               (good-name name)
               (good-method method)
               (good-data-type dtype)
               (good-model model)
               (good-date date)
               (good-tool tool)
               (good-author author)
               (good-taxa-list tl)
               (good-ingroup ingroup tl)
               (good-outgroup outgroup tl))))
    nil))

(defun good-tree-entry (entry)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Recognizes a well-formed tree table entry.~/
;  ~/
;  "
  (declare (xargs :guard t))
  (if (consp entry)
      (let ((tree-id (car entry))
            (rest (cdr entry)))
        (let ((analysis-id (my-get 'analysis-id rest))
              (rooted? (my-get 'rooted? rest))
              (brlens? (my-get 'brlens? rest))
              (tree (my-get 'tree rest))
              (type (my-get 'type rest))
              (mp (my-get 'mp rest))
              (ml (my-get 'ml rest))
              (name (my-get 'name rest)))
          (and (good-id tree-id)
               (good-id analysis-id)
               (good-rooted-flg rooted?)
               (good-brlens-flg brlens?)
               (good-tree tree)
               (good-tree-type type) ; single, consensus
               (good-mp mp)
               (good-ml ml)
               (good-name name))))
    nil))

;;primary key accessor
(defun get-id (entry)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns the primary key of a table entry.~/
;  ~/
;  "
  (declare (xargs :guard (or (good-study-entry entry)
                             (good-analysis-entry entry)
                             (good-tree-entry entry))))
  (car entry))

(defthm good-id-get-id-study
  (implies (good-study-entry entry)
           (good-id (get-id entry))))

(defthm good-id-get-id-analysis
  (implies (good-analysis-entry entry)
           (good-id (get-id entry))))

(defthm good-id-get-id-tree
  (implies (good-tree-entry entry)
           (good-id (get-id entry))))

; Name accessor
(defun get-name (entry)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns the name of a table entry.~/
;  ~/
;  "
  (declare (xargs :guard (or (good-study-entry entry)
                             (good-analysis-entry entry)
                             (good-tree-entry entry))))
  (my-get 'name (cdr entry)))

(defthm good-get-name-entry
  (implies (good-study-entry entry)
           (good-name (get-name entry))))

(defthm good-get-name-analysis
  (implies (good-analysis-entry entry)
           (good-name (get-name entry))))

(defthm good-get-name-tree
  (implies (good-tree-entry entry)
           (good-name (get-name entry))))


;;study table accessor functions
(defun get-sequences (entry)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns the sequences from a study table entry.~/
;  ~/
;  "
  (declare (xargs :guard (good-study-entry entry)))
  (my-get 'sequences (cdr entry)))

(defthm good-get-sequences
  (implies (good-study-entry entry)
           (good-sequences (get-sequences entry))))

(defun get-mapping (entry)
  (declare (xargs :guard (good-study-entry entry)))
  (my-get 'mapping (cdr entry)))

(defthm good-get-mapping
  (implies (good-study-entry entry)
           (good-mapping (get-mapping entry))))

;; Analysis table accessors
(defun get-study-id (entry)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns the study-id of an analysis table entry.~/
;  ~/
;  "
  (declare (xargs :guard (good-analysis-entry entry)))
  (my-get 'study-id (cdr entry)))

(defthm good-get-study-id
  (implies (good-analysis-entry entry)
           (good-id (get-study-id entry))))

(defun get-method (entry)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns the method of an analysis table entry.~/
;  ~/
;  "
  (declare (xargs :guard (good-analysis-entry entry)))
  (my-get 'method (cdr entry)))

(defthm good-get-method
  (implies (good-analysis-entry entry)
           (good-method (get-method entry))))

(defun get-data-type (entry)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns the data-type of an analysis table entry.~/
;  ~/
;  "
  (declare (xargs :guard (good-analysis-entry entry)))
  (my-get 'data-type (cdr entry)))

(defthm good-get-data-type
  (implies (good-analysis-entry entry)
           (good-data-type (get-data-type entry))))

(defun get-model (entry)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns the model of an analysis table entry.~/
;  ~/
;  "
  (declare (xargs :guard (good-analysis-entry entry)))
  (my-get 'model (cdr entry)))

(defthm good-get-model
  (implies (good-analysis-entry entry)
           (good-model (get-model entry))))

(defun get-date (entry)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns the date of an analysis table entry.~/
;  ~/
;  "
  (declare (xargs :guard (good-analysis-entry entry)))
  (my-get 'date (cdr entry)))

(defthm good-get-date
  (implies (good-analysis-entry entry)
           (good-date (get-date entry))))

(defun get-tool (entry)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns the tool of an analysis table entry.~/
;  ~/
;  "
  (declare (xargs :guard (good-analysis-entry entry)))
  (my-get 'tool (cdr entry)))

(defthm good-get-tool
  (implies (good-analysis-entry entry)
           (good-tool (get-tool entry))))

(defun get-author (entry)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns the author of an analysis table entry.~/
;  ~/
;  "
  (declare (xargs :guard (good-analysis-entry entry)))
  (my-get 'author (cdr entry)))

(defthm good-get-author
  (implies (good-analysis-entry entry)
           (good-author (get-author entry))))

(defun get-taxa-list (entry)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns the taxa list of an analysis table entry.~/
;  ~/
;  "
  (declare (xargs :guard (good-analysis-entry entry)))
  (my-get 'taxa-list (cdr entry)))

(defthm good-get-taxa-list
  (implies (good-analysis-entry entry)
           (good-taxa-list (get-taxa-list entry))))

(defun get-ingroup (entry)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns the ingroup of an analysis table entry.~/
;  ~/
;  "
  (declare (xargs :guard (good-analysis-entry entry)))
  (my-get 'ingroup (cdr entry)))

(defthm good-get-ingroup
  (implies (good-analysis-entry entry)
           (good-ingroup (get-ingroup entry)
                         (get-taxa-list entry))))

(defun get-outgroup (entry)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns the outgroup of an analysis table entry.~/
;  ~/
;  "
  (declare (xargs :guard (good-analysis-entry entry)))
  (my-get 'outgroup (cdr entry)))

(defthm good-get-outgroup
  (implies (good-analysis-entry entry)
           (good-outgroup (get-outgroup entry)
                          (get-taxa-list entry))))

;; tree table accessors
(defun get-analysis-id (entry)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns the analysis-id of a tree table entry.~/
;  ~/
;  "
  (declare (xargs :guard (good-tree-entry entry)))
  (my-get 'analysis-id (cdr entry)))

(defthm good-get-analysis-id
  (implies (good-tree-entry entry)
           (good-id (get-analysis-id entry))))

(defun get-rooted-flg (entry)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns the rootedness flag of a tree table entry.~/
;  ~/
;  "
  (declare (xargs :guard (good-tree-entry entry)))
  (my-get 'rooted? (cdr entry)))

(defthm good-get-rooted
  (implies (good-tree-entry entry)
           (good-rooted-flg (get-rooted-flg entry))))

(defun get-brlens-flg (entry)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns the presence of branch lengths flag of a tree table entry.~/
;  ~/
;  "
  (declare (xargs :guard (good-tree-entry entry)))
  (my-get 'brlens? (cdr entry)))

(defthm good-get-brlens
  (implies (good-tree-entry entry)
           (good-brlens-flg (get-brlens-flg entry))))

(defun get-tree (entry)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns the tree of a tree table entry.~/
;  ~/
;  "
  (declare (xargs :guard (good-tree-entry entry)))
  (my-get 'tree (cdr entry)))

(defthm good-get-tree
  (implies (good-tree-entry entry)
           (good-tree (get-tree entry))))

(defun get-tree-type (entry)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns the tree type of a tree table entry.~/
;  ~/
;  "
  (declare (xargs :guard (good-tree-entry entry)))
  (my-get 'type (cdr entry)))

(defthm good-get-tree-type
  (implies (good-tree-entry entry)
           (good-tree-type (get-tree-type entry))))

(defun get-mp (entry)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns the maximum parsimony score of a tree table entry.~/
;  ~/
;  "
  (declare (xargs :guard (good-tree-entry entry)))
  (my-get 'mp (cdr entry)))

(defthm good-get-mp
  (implies (good-tree-entry entry)
           (good-mp (get-mp entry))))

(defun get-ml (entry)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns the maximum likelihood score of a tree table entry.~/
;  ~/
;  "
  (declare (xargs :guard (good-tree-entry entry)))
  (my-get 'ml (cdr entry)))

(defthm good-get-ml
  (implies (good-tree-entry entry)
           (good-ml (get-ml entry))))

;; redefine good-entrys in terms of the accessors:
(defthm good-study-entry-redefinition
  (equal (good-study-entry entry)
         (if (consp entry)
             (and (good-id (get-id entry))
                  (good-sequences (get-sequences entry))
                  (good-mapping (get-mapping entry))
                  (good-name (get-name entry)))
           nil))
  :rule-classes :definition)

(defthm good-analysis-entry-redefinition
  (equal (good-analysis-entry entry)
         (if (consp entry)
             (and (good-id (get-id entry))
                  (good-id (get-study-id entry))
                  (good-name (get-name entry))
                  (good-method (get-method entry))
                  (good-data-type (get-data-type entry))
                  (good-model (get-model entry))
                  (good-date (get-date entry))
                  (good-tool (get-tool entry))
                  (good-author (get-author entry))
                  (good-taxa-list (get-taxa-list entry))
                  (good-ingroup (get-ingroup entry)
                                (get-taxa-list entry))
                  (good-outgroup (get-outgroup entry)
                                 (get-taxa-list entry)))
           nil))
  :rule-classes :definition)

(defthm good-tree-entry-redefinition
  (equal (good-tree-entry entry)
         (if (consp entry)
             (and (good-id (get-id entry))
                  (good-id (get-analysis-id entry))
                  (good-rooted-flg (get-rooted-flg entry))
                  (good-brlens-flg (get-brlens-flg entry))
                  (good-tree (get-tree entry))
                  (good-tree-type (get-tree-type entry))
                  (good-mp (get-mp entry))
                  (good-ml (get-ml entry))
                  (good-name (get-name entry)))
           nil))
  :rule-classes :definition)

(defthm good-study-entry-gives-consp
  (implies (good-study-entry entry)
           (consp entry))
  :rule-classes :forward-chaining)

(defthm good-analysis-entry-gives-consp
  (implies (good-analysis-entry entry)
           (consp entry))
  :rule-classes :forward-chaining)

(defthm good-tree-entry-gives-consp
  (implies (good-tree-entry entry)
           (consp entry))
  :rule-classes :forward-chaining)

;;general functions
(in-theory (disable get-id))
(in-theory (disable get-name))

;;from study table
(in-theory (disable get-sequences
                    get-mapping))

;;from analysis table
(in-theory (disable get-study-id
                    get-method
                    get-data-type
                    get-model
                    get-date
                    get-tool
                    get-author
                    get-taxa-list
                    get-ingroup
                    get-outgroup))

;;from tree-table
(in-theory (disable get-analysis-id
                    get-rooted-flg
                    get-brlens-flg
                    get-tree
                    get-tree-type
                    get-mp
                    get-ml))


(in-theory (disable good-study-entry
                    good-analysis-entry
                    good-tree-entry))




