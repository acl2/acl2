(in-package "ACL2")
(include-book "../gen-trees/sets-lists-trees") ;; mostly tree-preds,
                                               ;; but a couple thms with
                                               ;; member-gen and subset

;;For frequency functions

;; x is a member of all lists in l, a list of lists (or non-tip trees.)
(defun member-of-all (x l)
  (declare (xargs :guard t))
  (if (atom l)
      t
    (and (member-hqual x (car l))
         (member-of-all x (cdr l)))))

(defthm member-of-all-when-not-consp
  (implies (not (consp l))
           (equal (member-of-all x l)
                  t)))

(defthm member-of-all-of-consp
  (equal (member-of-all x (cons first rest))
         (and (member-hqual x first)
              (member-of-all x rest))))

(dis+ind member-of-all)

;; List l is a subset of the domain of alist db.
(defun subset-of-domain (l db)
  (declare (xargs :guard t))
  (if (atom l)
      t
    (and (assoc-hqual (car l) db)
         (subset-of-domain (cdr l) db))))

(defthm subset-of-domain-when-not-consp
  (implies (not (consp l))
           (equal (subset-of-domain l db)
                  t)))

(defthm subset-of-domain-of-consp
  (equal (subset-of-domain (cons first rest) db)
         (and (assoc-hqual first db)
              (subset-of-domain rest db))))

(dis+ind subset-of-domain)

;; Recognizes an alist db whose range is made up of nats and conses.
(defun nat-or-cons-range-halistp (db)
  (declare (xargs :guard (alistp-gen db)))
  (if (atom db)
      t
    (and (or (natp (cdar db))
             (consp (cdar db)))
         (nat-or-cons-range-halistp (cdr db)))))

(defthm nat-or-cons-range-halistp-when-not-consp
  (implies (not (consp db))
           (equal (nat-or-cons-range-halistp db)
                  t)))

(defthm nat-or-cons-range-halistp-of-consp
  (equal (nat-or-cons-range-halistp (cons first rest))
         (and (or (and (integerp (cdr first))
                       (<= 0 (cdr first)))
                  (consp (cdr first)))
              (nat-or-cons-range-halistp rest))))

(dis+ind nat-or-cons-range-halistp)

;; Recognizes an alist db where for each key/value pair, if the value is a cons then it
;; is a list of lists (trees) each of which has the key as a member.
(defun if-cons-range-member-of-all-halistp (db)
  (declare (xargs :guard (alistp-gen db)))
  (if (atom db)
      t
    (and (or (not (consp (cdar db)))
             (member-of-all (caar db) (cdar db)))
         (if-cons-range-member-of-all-halistp (cdr db)))))

(defthm if-cons-range-member-of-all-halistp-when-not-consp
  (implies (not (consp db))
           (equal (if-cons-range-member-of-all-halistp db)
                  t)))

(defthm if-cons-range-member-of-all-halistp-of-consp
  (equal (if-cons-range-member-of-all-halistp (cons first rest))
         (and (or (not (consp (cdr first)))
                  (member-of-all (car first) (cdr first)))
              (if-cons-range-member-of-all-halistp rest))))

(dis+ind if-cons-range-member-of-all-halistp)

;; Recognizes an alist db where for each key/value pair, if the value is a cons then it
;; is a list of lists (trees) each of which is in the domain of full.
;; A replete alist db has the property (if-cons-range-subset-of-domain-halistp db db).
(defun if-cons-range-subset-of-domain-halistp (db full)
  (declare (xargs :guard (alistp-gen db)))
  (if (atom db)
      t
    (and (or (not (consp (cdar db)))
             (subset-of-domain (cdar db) full))
         (if-cons-range-subset-of-domain-halistp (cdr db) full))))

(defthm if-cons-range-subset-of-domain-halistp-when-not-consp
  (implies (not (consp db))
           (equal (if-cons-range-subset-of-domain-halistp db full)
                  t)))

(defthm if-cons-range-subset-of-domain-halistp-of-consp
  (equal (if-cons-range-subset-of-domain-halistp (cons first rest) full)
         (and (or (not (consp (cdr first)))
                  (subset-of-domain (cdr first) full))
              (if-cons-range-subset-of-domain-halistp rest full))))

(dis+ind if-cons-range-subset-of-domain-halistp)

;; True if every element of l is either a key in db or a member of list.
;; This is needed for the proof of
;; if-cons-range-subset-of-domain-halistp-replete-trees1 as a generalization of
;; subset-of-domain.
(defun subset-of-domain-or-list (l db list)
  (declare (xargs :guard t))
  (if (atom l)
      t
    (and (or (assoc-hqual (car l) db)
             (member-hqual (car l) list))
         (subset-of-domain-or-list (cdr l) db list))))

(defthm subset-of-domain-or-list-when-not-consp
  (implies (not (consp l))
           (equal (subset-of-domain-or-list l db list)
                  t)))

(defthm subset-of-domain-or-list-of-consp
  (equal (subset-of-domain-or-list (cons first rest) db list)
         (and (or (assoc-hqual first db)
                  (member-hqual first list))
              (subset-of-domain-or-list rest db list))))

(dis+ind subset-of-domain-or-list)

;; If true, for every key/value pair in db where the value is a cons, the value
;; is a list every member of which is either a key in full or a member of list.
;; This is needed for the proof of
;; if-cons-range-subset-of-domain-halistp-replete-trees1 as a generalization of
;; if-cons-range-subset-of-domain-halistp.
(defun if-cons-range-subset-of-domain-or-list (db full list)
  (declare (xargs :guard (alistp-gen db)))
  (if (atom db)
      t
    (and (or (not (consp (cdar db)))
             (subset-of-domain-or-list (cdar db) full list))
         (if-cons-range-subset-of-domain-or-list (cdr db) full list))))

(defthm if-cons-range-subset-of-domain-or-list-when-not-consp
  (implies (not (consp db))
           (equal (if-cons-range-subset-of-domain-or-list db full list)
                  t)))

(defthm if-cons-range-subset-of-domain-or-list-of-consp
  (equal (if-cons-range-subset-of-domain-or-list (cons first rest) full list)
         (and (or (not (consp (cdr first)))
                  (subset-of-domain-or-list (cdr first) full list))
              (if-cons-range-subset-of-domain-or-list rest full list))))

(dis+ind if-cons-range-subset-of-domain-or-list)

;; Measure functions for the frequency/sum-frequencies-list mutual recursion.
;; Idea: In a replete alist db, db(x) is a list of trees which have x as a
;; member; therefore they are bigger than x (according to acl2-count, for
;; example.)  In the mutual recursion of frequency/sum-frequencies-list,
;; therefore, the size of the trees we're looking at increases every time we
;; look one up in the db.  But we can never exceed the size of the biggest tree
;; in the cdrs of the pairs in db or, for that matter, simply the size of any
;; of the cdrs of the pairs.
;; Therefore we use (biggest-cdr db) as the maximum value; we compare this to
;; (smallest-in-list l), which never decreases and which increases whenever the
;; length of l has the possibility of growing.

;; Finds the maximum acl2-count of any bound value in alist db.
(defun biggest-cdr (db)
  (declare (xargs :guard (alistp-gen db)))
  (if (atom db)
      0
    (max (acl2-count (cdar db))
         (biggest-cdr (cdr db)))))

(defthm biggest-cdr-when-not-consp
  (implies (not (consp db))
           (equal (biggest-cdr db)
                  0)))

(defthm biggest-cdr-of-consp
  (equal (biggest-cdr (cons first rest))
         (max (acl2-count (cdr first))
              (biggest-cdr rest))))

(dis+ind biggest-cdr)

;; Finds the smallest acl2-count of a member of list l.
(defun smallest-in-list (l)
  (declare (xargs :guard t))
  (if (atom l)
      -1 ;; should not occur
    (if (atom (cdr l))
        (acl2-count (car l))
      (min (acl2-count (car l))
           (smallest-in-list (cdr l))))))

(defthm smallest-in-list-when-not-consp
  (implies (not (consp l))
           (equal (smallest-in-list l)
                  -1)))

(defthm smallest-in-list-of-consp
  (equal (smallest-in-list (cons first rest))
         (if (atom rest)
             (acl2-count first)
           (min (acl2-count first)
                (smallest-in-list rest)))))

(dis+ind smallest-in-list)

;; True iff every member of l is in the domain of alists db1 or db2.
;; Needed for showing that subset-of-domain is preserved by hhshrink-alist.
(defun subset-of-domains (l db1 db2)
  (declare (xargs :guard t))
  (if (atom l)
      t
    (and (or (assoc-hqual (car l) db1)
             (assoc-hqual (car l) db2))
         (subset-of-domains (cdr l) db1 db2))))

(defthm subset-of-domains-when-not-consp
  (implies (not (consp l))
           (equal (subset-of-domains l db1 db2)
                  t)))

(defthm subset-of-domains-of-consp
  (equal (subset-of-domains (cons first rest) db1 db2)
         (and (or (assoc-hqual first db1)
                  (assoc-hqual first db2))
              (subset-of-domains rest db1 db2))))

(dis+ind subset-of-domains)

;; key is not a proper subtree of any of the keys in db.
(defun not-subtree-of-keys (key db)
  (declare (xargs :guard (alistp-gen db)))
  (if (atom db)
      t
    (and (not (proper-subtreep key (caar db)))
         (not-subtree-of-keys key (cdr db)))))

(defthm not-subtree-of-keys-when-not-consp
  (implies (not (consp db))
           (equal (not-subtree-of-keys key db)
                  t)))

(defthm not-subtree-of-keys-of-consp
  (equal (not-subtree-of-keys key (cons first rest))
         (and (not (proper-subtreep key (car first)))
              (not-subtree-of-keys key rest))))

(dis+ind not-subtree-of-keys)

;; True if no member of l is a subtree of any key in db.
(defun not-subtree-of-keys-list (list db)
  (declare (xargs :guard (alistp-gen db)))
  (if (atom list)
      t
    (and (not-subtree-of-keys (car list) db)
         (not-subtree-of-keys-list (cdr list) db))))

(defthm not-subtree-of-keys-list-when-not-consp
  (implies (not (consp list))
           (equal (not-subtree-of-keys-list list db)
                  t)))

(defthm not-subtree-of-keys-list-of-consp
  (equal (not-subtree-of-keys-list (cons first rest) db)
         (and (not-subtree-of-keys first db)
              (not-subtree-of-keys-list rest db))))

(dis+ind not-subtree-of-keys-list)

;; True if every key in db bound to a natural is not a proper subtree of tree.
(defun if-nat-val-key-not-subtree-of (tree db)
  (declare (xargs :guard (alistp-gen db)))
  (if (atom db)
      t
    (and (or (not (natp (cdar db)))
             (not (proper-subtreep (caar db) tree)))
         (if-nat-val-key-not-subtree-of tree (cdr db)))))

(defthm if-nat-val-key-not-subtree-of-when-not-consp
  (implies (not (consp db))
           (equal (if-nat-val-key-not-subtree-of tree db)
                  t)))

(defthm if-nat-val-key-not-subtree-of-of-consp
  (equal (if-nat-val-key-not-subtree-of tree (cons first rest))
         (and (or (not (and (integerp (cdr first))
                            (<= 0 (cdr first))))
                  (not (proper-subtreep (car first) tree)))
              (if-nat-val-key-not-subtree-of tree rest))))

(dis+ind if-nat-val-key-not-subtree-of)

;; True if no tree in the list l is a proper subtree of any key in db bound to
;; a natural.
(defun if-nat-val-key-not-subtree-of-any (l db)
  (declare (xargs :guard (alistp-gen db)))
  (if (atom l)
      t
    (and (if-nat-val-key-not-subtree-of (car l) db)
         (if-nat-val-key-not-subtree-of-any (cdr l) db))))

(defthm if-nat-val-key-not-subtree-of-any-when-not-consp
  (implies (not (consp l))
           (equal (if-nat-val-key-not-subtree-of-any l db)
                  t)))

(defthm if-nat-val-key-not-subtree-of-any-of-consp
  (equal (if-nat-val-key-not-subtree-of-any (cons first rest) db)
         (and (if-nat-val-key-not-subtree-of first db)
              (if-nat-val-key-not-subtree-of-any rest db))))

(dis+ind if-nat-val-key-not-subtree-of-any)

;;; Theorem's for measure of frequency
(defthm member-hqual-implies-smaller
  (implies (member-hqual x l)
           (< (acl2-count x) (acl2-count l)))
  :rule-classes :linear)

(defthm member-equal-implies-smaller
  (implies (member-equal x l)
	   (< (acl2-count x) (acl2-count l)))
  :rule-classes :linear)

(defthm member-of-all-implies-smaller-than-smallest
  (implies (and (consp l)
                (member-of-all x l))
           (< (acl2-count x)
              (smallest-in-list l)))
  :rule-classes (:rewrite :linear))

(defthm if-cons-range-member-of-all-halistp-member-of-all
  (implies (and (if-cons-range-member-of-all-halistp db)
                (or (not (assoc-hqual x db))
                    (consp (cdr (assoc-hqual x db)))))
           (member-of-all x (cdr (assoc-hqual x db)))))

(defthm replete-alist-measure-okp-assoc-hqual2
  (implies (and (consp (cdr (assoc-hqual x db)))
                (if-cons-range-member-of-all-halistp db))
           (< (acl2-count x) (smallest-in-list (cdr (assoc-hqual x db)))))
  :rule-classes (:rewrite :linear))

(defthm smallest-in-list-acl2-count
  (implies (consp list)
           (< (smallest-in-list list) (acl2-count list)))
  :rule-classes (:rewrite :linear))

(defthm smallest-assoc-hqual-biggest-cdr
  (implies (consp (cdr (assoc-hqual x db)))
           (> (biggest-cdr db) (smallest-in-list (cdr (assoc-hqual x db)))))
  :rule-classes (:rewrite :linear))

(defthm biggest-cdr-assoc-hqual
  (implies (and (if-cons-range-member-of-all-halistp db)
                (consp (cdr (assoc-hqual x db))))
           (< (acl2-count x) (biggest-cdr db)))
  :rule-classes (:rewrite :linear))


(encapsulate ()
;; True if sub is a suffix of some (not necessarily proper) subtree of tree.
;; This is needed for the proof of not-subtree-of-keys-replete-trees as a
;; generalization of subtreep.
(defun suffix-of-subtree (sub tree)
  (declare (xargs :guard t))
  (or (equal sub tree)
      (and (not (atom tree))
           (or (suffix-of-subtree sub (car tree))
               (suffix-of-subtree sub (cdr tree))))))

(local (defthm suffix-of-subtree-measure
         (implies (suffix-of-subtree sub tree)
                  (<= (acl2-count sub) (acl2-count tree)))
         :rule-classes (:rewrite :linear)))

;; Nothing is a proper subtree of itself:
(defthm subtreep-measure
  (if flg
      (implies (subtreep a b)
               (<= (acl2-count a) (acl2-count b)))
    (implies (proper-subtreep a b)
             (< (acl2-count a) (acl2-count b))))
  :hints (("Goal" :induct (tree-p-induction b flg)))
  :rule-classes nil)

(defthm not-proper-subtree-suffix-of-subtree
  (implies (suffix-of-subtree sub tree)
           (not (proper-subtreep tree sub)))
  :hints (("Goal" :use (:instance subtreep-measure
                                  (flg nil)
                                  (a tree)
                                  (b sub)))))
)

(defthm subset-of-domain-implies-subset-of-domain-or-list
  (implies (subset-of-domain l db)
           (subset-of-domain-or-list l db list)))

(defthm implies-if-cons-range-subset-of-domain-or-list
  (implies (if-cons-range-subset-of-domain-halistp db full)
           (if-cons-range-subset-of-domain-or-list db full list)))

(defthm subset-of-domain-or-list-implies-subset-of-domain
  (implies (subset-of-domain-or-list l db nil)
           (subset-of-domain l db)))

(defthm if-cons-range-subset-of-domain-or-list-nil
  (implies (if-cons-range-subset-of-domain-or-list db full nil)
           (if-cons-range-subset-of-domain-halistp db full)))

(defthm nat-or-cons-range-halistp-not-integerp-consp
  (implies (and (nat-or-cons-range-halistp db)
                (assoc-hqual x db)
                (not (and (integerp (cdr (assoc-hqual x db)))
                          (<= 0 (cdr (assoc-hqual x db))))))
           (consp (cdr (assoc-hqual x db)))))

(defthm replete-alist-guard-assoc-hqual-subset-of-domain
  (implies (and (if-cons-range-subset-of-domain-halistp db db1)
                (or (not (assoc-hqual x db))
                    (consp (cdr (assoc-hqual x db)))))
           (subset-of-domain (cdr (assoc-hqual x db)) db1)))


(defthm subset-of-domains-subset-of-domain
  (implies (subset-of-domain l db)
           (subset-of-domains l db db2)))

(defthm subset-of-domains-cdr-cons
  (implies (and (subset-of-domains l db1 db2)
                (equal bind (cons (caar db1) (cdar db1))))
           (subset-of-domains l (cdr db1) (cons bind db2))))

(defthm subset-of-domains-assoc-cdr
  (implies (and (subset-of-domains l db1 db2)
                (assoc-hqual (caar db1) db2))
           (subset-of-domains l (cdr db1) db2)))

(defthm hhshrink-alist-nat-or-cons-range-halistp1
  (implies (and (nat-or-cons-range-halistp alst)
                (nat-or-cons-range-halistp acc))
           (nat-or-cons-range-halistp (hhshrink-alist alst acc))))

(defthm hhshrink-alist-nat-or-cons-range-halistp
  (implies (and (nat-or-cons-range-halistp alst)
                (atom x))
           (nat-or-cons-range-halistp (hhshrink-alist alst x)))
  :hints (("Goal" :in-theory (disable hhshrink-alist))))

(defthm hhshrink-alist-if-cons-range-subset-of-domain-halistp1-1
  (implies (and (if-cons-range-subset-of-domain-halistp a b)
                (if-cons-range-subset-of-domain-halistp c b))
           (if-cons-range-subset-of-domain-halistp (hhshrink-alist a c) b)))

;; added x instead of nil
(defthm hhshrink-alist-if-cons-range-subset-of-domain-halistp1-atom
  (implies (and (if-cons-range-subset-of-domain-halistp a b)
                (not (consp x)))
           (if-cons-range-subset-of-domain-halistp (hhshrink-alist a x) b))
  :hints (("Goal" :in-theory (disable hhshrink-alist))))

(defthm hhshrink-alist-subset-of-domains
  (implies (and (subset-of-domains l db1 db2)
                (alistp-gen db1))
           (subset-of-domain l (hhshrink-alist db1 db2)))
  :hints (("Goal" :induct (hshrink-alist db1 db2))))

(defthm hhshrink-alist-subset-of-domain-atom
  (implies (and (subset-of-domain l db)
                (alistp-gen db)
                (not (consp x)))
           (subset-of-domain l (hhshrink-alist db x)))
  :hints (("Goal" :in-theory (disable hhshrink-alist))))

(defthm hhshrink-alist-if-cons-range-subset-of-domain-halistp2-1
  (implies (and (if-cons-range-subset-of-domain-halistp a b)
                (if-cons-range-subset-of-domain-halistp a c)
                (alistp-gen b))
           (if-cons-range-subset-of-domain-halistp a (hhshrink-alist b c)))
   :hints (("Goal" :in-theory (disable hhshrink-alist))))

(defthm hhshrink-alist-if-cons-range-subset-of-domain-halistp2-atom
  (implies (and (if-cons-range-subset-of-domain-halistp a b)
                (alistp-gen b)
                (not (consp x)))
           (if-cons-range-subset-of-domain-halistp a (hhshrink-alist b x)))
  :hints (("Goal" :induct (if-cons-range-subset-of-domain-halistp a b)
	   :in-theory (disable hhshrink-alist))))

(defthm not-subtree-of-keys-list-cons-db
  (implies (and (not-subtree-of-keys-list l db)
                (not (has-proper-subtree-in-list key l)))
           (not-subtree-of-keys-list l (cons (cons key val) db))))

(defthm not-subtree-of-keys-list-atom
  (implies (atom x)
           (not-subtree-of-keys-list l x)))

(defthm if-nat-val-key-not-subtree-of-any-atom
  (implies (atom x)
           (if-nat-val-key-not-subtree-of-any l x)))

(defthm if-nat-val-key-not-subtree-of-any-cons
  (implies (and (non-subtree-listp l list)
                (if-nat-val-key-not-subtree-of-any l db)
                (member-hqual key list))
           (if-nat-val-key-not-subtree-of-any l (cons (cons key val) db))))

(defthm if-cons-range-subset-of-domain-or-list-cons-full
  (implies (if-cons-range-subset-of-domain-or-list db full list)
           (if-cons-range-subset-of-domain-or-list db (cons (cons key val) full) list)))


(defthm if-cons-range-subset-of-domain-or-list-implies-switch
  (implies (if-cons-range-subset-of-domain-or-list db full (cons key list))
           (if-cons-range-subset-of-domain-or-list
            db (cons (cons key val) full) list)))


(defthm if-cons-range-subset-of-domain-or-list-cons-list
  (implies (if-cons-range-subset-of-domain-or-list db full list)
           (if-cons-range-subset-of-domain-or-list db full (cons x list))))


(defthm if-cons-range-subset-of-domain-or-list-assoc-hqual
  (implies (and (if-cons-range-subset-of-domain-or-list db full list)
                (consp (cdr (assoc-hqual key db))))
           (subset-of-domain-or-list (cdr (assoc-hqual key db)) full list)))

(defthm hhshrink-alist-if-cons-range-member-of-all-halistp1
  (implies (and (if-cons-range-member-of-all-halistp db1)
                (if-cons-range-member-of-all-halistp db2)
                (alistp-gen db1))
           (if-cons-range-member-of-all-halistp (hhshrink-alist db1 db2))))

(defthm hshrink-alist-nat-or-cons-range-halistp1
  (implies (and (nat-or-cons-range-halistp alst)
                (nat-or-cons-range-halistp acc)
                (alistp-gen alst))
           (nat-or-cons-range-halistp (hshrink-alist alst acc))))

(defthm hshrink-alist-nat-or-cons-range-halistp
  (implies (and (nat-or-cons-range-halistp alst)
                (alistp-gen alst)
                (not (consp x)))
           (nat-or-cons-range-halistp (hshrink-alist alst x))))

(defthm hshrink-alist-if-cons-range-subset-of-domain-halistp1-1
  (implies (and (if-cons-range-subset-of-domain-halistp a b)
                (if-cons-range-subset-of-domain-halistp c b)
                (alistp-gen a))
           (if-cons-range-subset-of-domain-halistp (hshrink-alist a c) b)))

(defthm hshrink-alist-if-cons-range-subset-of-domain-halistp1-atom
  (implies (and (if-cons-range-subset-of-domain-halistp a b)
                (alistp-gen a)
                (not (consp x)))
           (if-cons-range-subset-of-domain-halistp (hshrink-alist a x) b)))

(defthm subset-of-domains-gives-subset-of-domain
  (implies (and (not (consp db1))
                (subset-of-domains l db1 db2))
           (subset-of-domain l db2)))

(defthm hshrink-alist-subset-of-domains
  (implies (and (subset-of-domains l db1 db2)
                (alistp-gen db1))
           (subset-of-domain l (hshrink-alist db1 db2)))
  :hints (("Goal" :induct (hshrink-alist db1 db2))))

(defthm hshrink-alist-subset-of-domain-atom
  (implies (and (subset-of-domain l db)
                (alistp-gen db)
                (not (consp x)))
           (subset-of-domain l (hshrink-alist db x))))

(defthm hshrink-alist-if-cons-range-subset-of-domain-halistp2-1
  (implies (and (if-cons-range-subset-of-domain-halistp a b)
                (if-cons-range-subset-of-domain-halistp a c)
                (alistp-gen b))
           (if-cons-range-subset-of-domain-halistp a (hshrink-alist b c))))

(defthm hshrink-alist-if-cons-range-subset-of-domain-halistp2-atom
  (implies (and (if-cons-range-subset-of-domain-halistp a b)
                (alistp-gen b)
                (not (consp x)))
           (if-cons-range-subset-of-domain-halistp a (hshrink-alist b x)))
  :hints (("Goal" :induct (if-cons-range-subset-of-domain-halistp a b))))

(defthm hshrink-alist-if-cons-range-member-of-all-halistp1
  (implies (and (if-cons-range-member-of-all-halistp db1)
                (if-cons-range-member-of-all-halistp db2)
                (alistp-gen db1))
           (if-cons-range-member-of-all-halistp (hshrink-alist db1 db2))))

(defthm if-nat-val-key-not-subtree-of-member-equal
  (implies (and (if-nat-val-key-not-subtree-of parent db)
                (member-gen tree (double-rewrite parent)))
           (if-nat-val-key-not-subtree-of tree db)))

(defthm if-nat-val-key-not-subtree-of-parent-member-parent-not-natp
  (implies (and (if-nat-val-key-not-subtree-of parent db)
                (member-gen x parent)
                (assoc-hqual x db))
           (not (and (integerp (cdr (assoc-hqual x db)))
                     (<= 0 (cdr (assoc-hqual x db))))))
  :rule-classes :forward-chaining)

(defthm if-cons-range-subset-of-domain-or-list-cons-subset-db
  (implies (and (if-cons-range-subset-of-domain-or-list db full list)
                (subset val list))
           (if-cons-range-subset-of-domain-or-list
            (cons (cons key val) db) full list)))
