;;; Replete
(in-package "ACL2")
(include-book "replete-helper")


; The Lisp function replete-trees takes as its arguments a list of
; trees called args, a tree called parent, and a replete alist db;
; args must be equal to parent or one of the CDRs of parent; parent
; must not be in db.  If replete-trees is called with args equal to
; parent, then (a) replete-trees returns an alist, call it db2,
; such that (cons (cons parent nil) db2) is a replete alist, (b)
; parent is not in the domain of db2, (c) the only members of
; the domain of db2 not in db are proper subtrees of parent,
; and (d) all the proper nontip subtrees of parent are in the
; domain of db2.

(defun replete-trees (args parent db)
  (declare (xargs :guard (alistp-gen db)
                  :verify-guards nil))

  (cond ((atom args) db)
        (t (replete-trees
            (cdr args)
            parent
            (cond ((atom (car args)) db)
                  (t (let* ((p (het (car args) db))
                            (db (cond (p db)
                                      (t (replete-trees
                                          (car args)
                                          (car args)
                                          db)))))
                       (hut (car args) (cons parent (cdr p)) db))))))))

(defthm replete-trees-when-not-consp
  (implies (not (consp args))
           (equal (replete-trees args parent db)
                  db)))

(defthm replete-trees-of-consp
  (equal (replete-trees (cons first rest) parent db)
         (replete-trees rest parent
                       (cond ((atom first) db)
                             (t (let* ((p (het first db))
                                       (db (cond (p db)
                                                 (t (replete-trees
                                                     first
                                                     first
                                                     db)))))
                                  (hut first (cons parent (cdr p)) db)))))))

(dis+ind replete-trees)

(defun replete-trees-list-top1 (l db)
  (declare (xargs :guard (and (non-subtree-listp l l)
                              (alistp-gen db)
                              (bound-to-nat-list l db))
                  :verify-guards nil))
  (cond ((atom l) db)
        (t (replete-trees-list-top1
            (cdr l)
            (let ((p (het (car l) db)))
              (cond (p (hut (car l) (+ 1 (cdr p)) db))
                    (t (hut (car l) 1
                            (replete-trees (car l) (car l) db)))))))))

(defthm replete-trees-list-top1-when-not-consp
  (implies (not (consp l))
           (equal (replete-trees-list-top1 l db)
                  db)))

(defthm replete-trees-list-top1-of-consp
  (equal (replete-trees-list-top1 (cons first rest) db)
         (replete-trees-list-top1
            rest
            (let ((p (het first db)))
              (cond (p (hut first (+ 1 (cdr p)) db))
                    (t (hut first 1
                            (replete-trees first first db))))))))

(dis+ind replete-trees-list-top1)

; Replete-trees-list-top takes a list l of non-tip trees no member of
; which is a proper subtree of another.  Replete-trees-list-top
; returns a replete alist db such that (1) x is a member of the domain
; of db if and only if x is a member of l or is a non-tip proper
; subtree of a member of l and (2) if x is in the domain of db, then
; db(x) is an integer if and only if x is a member of l and db(x) is
; the number of times x occurs in l.

(defun replete-trees-list-top (l)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns a replete mapping of trees and subtrees in the input list to either
;  the number of times the tree occurs or to a list of each subtrees immediate
;  parents.~/
;  ~/
;  Arguments:
;     (1) l - a list of trees no member of which is a proper subtree of another

;  Details: The trees should all be ordered according to the same taxa list.
;           Branch lengths are not allowed (see replete-trees-list-brlens)."
  (declare (xargs :guard (non-subtree-listp l l)
                  :verify-guards nil))
  (replete-trees-list-top1 l '*replete-trees-list-top*))

(in-theory (disable replete-trees-list-top))

;;; Frequency

; Definition.  Suppose that l is a list of nontip trees, that no
; member of l is a proper subtree of a member of l, and that x is a
; subtree of some member of l.  We define the "frequency" of x in l
; to be the number of occurrences of x in l.

; Theorem.  Under the suppositions in the definition of "frequency"
; for x in l, if x is a member of l, its frequency in l is the number
; of times it is a member of l; furthermore, if x is not a member of
; l, the frequency x in l is the sum, as y ranges over the multi-set
; of subtrees of l of which x is an immediate member, of the
; frequency of y in l.

; Informal note.  Memoizing frequency, of course, means that we never
; have to compute the frequency of a tree twice.  Note that if one
; memoizes frequency, it is probably the case, for efficiency, that
; the db with respect to which one is computing the frequency should
; be a hons, as we arrange.  The previous remark is merely a reminder
; of the terrible performance we got without doing that honsing!

; In computing the frequency of x in l, we compute (frequency x db)
; where db is an alist that is assoc-equal equivalent to (replete-trees
; l), because the value returned by replete-trees has the relevant
; information immediately available.
(defun sum-frequencies-list-measure (l db)
  (declare (xargs :guard (alistp-gen db)))
  (if (atom l)
      0
    (make-ord 1 (+ 1 (nfix (- (biggest-cdr db)
                              (smallest-in-list l))))
              (len l))))

(defun frequency-measure (x db)
  (declare (xargs :guard (alistp-gen db)))
  (make-ord 1 (+ 1 (nfix (- (biggest-cdr db)
                            (acl2-count x))))
            0))

(mutual-recursion
(defun sum-frequencies-list (l db)
  (declare (xargs :measure (sum-frequencies-list-measure l db)
                   :guard (and (alistp-gen db)
                               (nat-or-cons-range-halistp db)
                               (if-cons-range-member-of-all-halistp db)
                               (if-cons-range-subset-of-domain-halistp db db)
                               (subset-of-domain l db))
                   :verify-guards nil))
  (cond ((atom l) 0)
        (t (+ (frequency (car l) db)
              (sum-frequencies-list (cdr l) db)))))

(defun frequency (x db)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns the number of times the list based fringe x occurs as implied by the
;  database given.~/
;  ~/
;  Arguments:
;     (1) x - a list based fringe
;     (2) db - a mapping of subtrees to integers or parent lists (such as that
;              produced by replete)
;
;  Details: The database must have appropriate structure (but is produced as
;           necessary by replete).  The underlying taxa list should be
;           consistent between both the fringe and the database."
  (declare (xargs :measure (frequency-measure x db)
                  :guard (and (alistp-gen db)
                              (nat-or-cons-range-halistp db)
                              (if-cons-range-member-of-all-halistp db)
                              (if-cons-range-subset-of-domain-halistp db db))))
  (if (mbt (if-cons-range-member-of-all-halistp db))
      (let ((p (het x db)))
        (cond ((integerp (cdr p)) (cdr p))
              (t (sum-frequencies-list (cdr p) db))))
    0))
)

(defthm sum-frequencies-list-when-not-consp
  (implies (not (consp l))
           (equal (sum-frequencies-list l db)
                  0)))

(defthm sum-frequencies-list-of-consp
  (equal (sum-frequencies-list (cons first rest) db)
         (+ (frequency first db)
            (sum-frequencies-list rest db))))

(dis+ind sum-frequencies-list)

(in-theory (disable frequency))


