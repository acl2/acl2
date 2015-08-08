(in-package "ACL2")
(include-book "misc/hons-help2" :dir :system) ;hons stuff

(include-book "../code/gen-trees/sets-lists-trees")
(include-book "../code/gen-trees/app-rev-lists")
(include-book "../code/tree-manip/sort-help")

(defun good-taxa-list (tl)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Recognizes a well formed list of taxa names.~/
;  ~/
;  Arguments:
;      (1) tl - a potential list of taxa names

;  "
  (declare (xargs :guard t))
  (and (int-symlist tl)
       (<= 2 (len tl))
       (no-dups-gen tl)))

(defthm good-taxa-list-int-symlist
  (implies (good-taxa-list tl)
           (int-symlist tl)))

(defthm good-taxa-list-len
  (implies (good-taxa-list tl)
           (<= 2 (len tl)))
  :rule-classes (:linear :rewrite))

(defthm good-taxa-list-no-dups
  (implies (good-taxa-list tl)
           (no-dups-gen tl)))

(in-theory (disable good-taxa-list))


;Kindof a hack... but needed
(defthm consp-when-len-nonzero
  (implies (not (equal (len (double-rewrite x)) 0))
           (equal (consp x)
                  t)))

(defun good-tree (tree)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Determines if a tree is well-formed.~/
;  ~/
;  Arguments:
;     (1) tree - a potential tree

;  Details: Does not recognize trees with branch lengths.
;           Requires both treep and taspip. "
  (declare (xargs :guard t))
  (and (treep tree)
       (taspip t tree)))

(defthm good-tree-treep-get-tree
  (implies (good-tree tree)
           (treep tree))
  :rule-classes (:forward-chaining :rewrite))

;(defthm good-taxa-list-good-tree-gives-consp-get-tree
;  (implies (and (good-tree tree tl)
;                (force (good-taxa-list tl)))
;           (consp tree))
;    :rule-classes (:forward-chaining :rewrite))

(defthm good-tree-gives-taspip-t-tree
  (implies (good-tree tree)
           (taspip t tree)))

(in-theory (disable good-tree))

(defun good-tree-tl (tree tl)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Determines if a tree matches a taxa list and is ordered accordingly.~/
;  ~/
;  Arguments:
;     (1) tree - a tree
;     (2) tl - a taxa list

; "
  (declare (xargs :guard (and (good-tree tree)
                              (good-taxa-list tl))))
  (and (perm (mytips tree) tl)
       (orderedp t tree
                 (taxa-list-to-taxon-index tl))))

(defthm good-tree-ordered-get-tree
  (implies (good-tree-tl tree tl)
           (orderedp t tree
                          (taxa-list-to-taxon-index tl))))

(defthm good-tree-perm-mytips
  (implies (good-tree-tl tree tl)
           (perm (mytips tree)
                  (double-rewrite tl)))
  :rule-classes (:forward-chaining :rewrite))


(defun stringp-or-nil (x)
  (declare (xargs :guard t))
  (or (stringp x)
      (equal x nil)))

(defthm stringp-or-nil-not-nil-gives-stringp-type
  (implies (and (stringp-or-nil x)
                x)
           (stringp x)))

;no good rule class... options? or rely on case split?
;(defthm stringp-or-nil-not-stringp-gives-type
;  (implies (and (stringp-or-nil id)
;                (not (stringp id)))
;           (equal id nil)))

(in-theory (disable stringp-or-nil))

(defun integerp-or-nil (x)
  (declare (xargs :guard t))
  (or (integerp x)
      (equal x nil)))

(defthm integerp-or-nil-not-nil-gives-integerp-type
  (implies (and (integerp-or-nil x)
                x)
           (integerp x)))

(in-theory (disable integerp-or-nil))

(defmacro good-rooted-flg (flg)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Recognizes a well-formed flag indicating rootedness.~/
;  ~/
;  "
  `(booleanp ,flg))

(defmacro good-brlens-flg (flg)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Recognizes a well-formed flag indicating branch length presence.~/
;  ~/
;  "
  `(booleanp ,flg))

(defmacro good-id (id)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Recognizes a well-formed id.~/
;  ~/
;  "
   `(integerp-or-nil ,id))

(defmacro good-name (name)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Recognizes a well-formed name specfication.~/
;  ~/
;  "
   `(integerp-or-nil ,name))

(defmacro good-date (date)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Recognizes a well-formed date specification.~/
;  ~/
;  "
   `(stringp-or-nil ,date))

(defmacro good-author (author)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Recognizes a well-formed author specification.~/
;  ~/
;  "
   `(stringp-or-nil ,author))

(defmacro good-tool (tool)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Recognizes a well-formed tool specification.~/
;  ~/
;  "
   `(stringp-or-nil ,tool))

(defmacro good-method (method)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Recognizes a well-formed method specification.~/
;  ~/
;  "
   `(stringp-or-nil ,method))

(defmacro good-data-type (data-type)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Recognizes a well-formed data type specification.~/
;  ~/
;  "
   `(stringp-or-nil ,data-type))

(defmacro good-model (model)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Recognizes a well-formed model specification.~/
;  ~/
;  "
   `(stringp-or-nil ,model))

(defun good-mp (mp)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Recognizes a well-formed maximum parsimony score.~/
;  ~/
;  "
  (declare (xargs :guard t))
  (or (rationalp mp)
      (equal mp nil)))

(defmacro good-ingroup (group tl)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Recognizes a well-formed ingroup.~/
;  ~/
;  Arguments:
;     (1) group - potential ingroup
;     (2) tl - a list of taxa

;  Details: A good ingroup is a subset of the given taxa."
   `(subset ,group ,tl))

(defmacro good-outgroup (group tl)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Recognizes a well-formed outgroup.~/
;  ~/
;  Arguments:
;     (1) group - potential outgroup
;     (2) tl - a list of taxa

;  Details: A good outgroup is a subset of the given taxa."
   `(subset ,group ,tl))

(defun good-ml (ml)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Recognizes a well-formed maximum likelihood score.~/
;  ~/
;  "
  (declare (xargs :guard t))
  (or (rationalp ml)
      (equal ml nil)))

(defmacro good-tree-type (type)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Recognizes a well-formed tree type specification.~/
;  ~/
;  "
   `(stringp-or-nil ,type))
