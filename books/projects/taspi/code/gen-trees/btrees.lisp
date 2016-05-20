(in-package "ACL2")
(include-book "arithmetic-3/bind-free/top" :dir :system)
(include-book "arithmetic-3/floor-mod/floor-mod" :dir :system)
(set-default-hints '((nonlinearp-default-hint
                      stable-under-simplificationp
                      hist
                      pspv)))
(include-book "../gen-helper/fast-lists")

;; Functions to determine necessary height of btrees
(defun ilog2-help (n)
  (declare (xargs :guard (natp n)))
  (cond ((zp n) 0)
        (t (+ 1 (ilog2-help (floor n 2))))))

(defun ilog2 (n)
  (declare (xargs :guard (natp n)))
   (cond ((< n 1) 0)
         (t (ilog2-help (1- n)))))

(defthm ilog2-help>1
  (implies (and (integerp depth)
                (<= 1 depth))
           (<= 1 (ilog2-help depth)))
  :rule-classes (:rewrite :linear))

(defthm natp-ilog-to-help
  (and (integerp (ilog2-help x))
       (<= 0 (ilog2-help x))))

(defthm ilog2-help-implications
  (implies (and (integerp x)
                (<= 1 x))
           (<= 1 (ilog2-help x))))

(defthm ilog2-implications
  (implies (and (integerp x)
                (<= 2 x))
           (<= 1 (ilog2 x))))

(encapsulate ()

(local
(defthm crock
  (implies (and (integerp x)
                (integerp y)
                (< x (+ 1 y)))
           (< (* 2 x) (+ 1 (* 2 y)))))
)

(local
(defthm one
  (implies (and (integerp j)
                (< 0 j))
           (<= 1 (ilog2-help j))))
)

(local
(defthm two
  (implies (and (integerp j)
                (< 0 j))
           (integerp (expt 2 (+ -1 (ilog2-help j))))))
)

(local
(defthm expt-smaller-helper
   (implies (and (integerp x)
                 (<= 0 x))
            (< (expt 2 (+ -1 (ilog2-help x)))
               (+ 1 x)))
   :hints (("subgoal *1/4.1" ; Matt K. mod 5/2016 (type-set bit for {1})
            :use (:instance crock
                            (x (expt 2
                                     (+ -1 (ilog2-help
                                            j))))
                            (y j)))))
)

(defthm expt-smaller-log2-helper
  (implies (and (integerp x)
                (<= 1 x))
           (< (expt 2 (+ -1 (ilog2-help (+ -1 x))))
              x))
  :hints (("goal" :use (:instance expt-smaller-helper (x (+ -1 x))))))

(defthm expt-smaller-ilog2
  (implies (and (integerp x)
                (<= 2 x))
           (< (expt 2 (+ -1 (ilog2 x)))
              x)))
;end encapsulate
)

(dis+ind ilog2-help)
(in-theory (disable ilog2))

(defun bits-to-tree (i log2-len-taxa-list)
  (declare (xargs :guard (integerp i)))
  (if (or (not (integerp log2-len-taxa-list))
          (< log2-len-taxa-list 0))
      nil
    (if (equal log2-len-taxa-list 0)
        (hons (oddp i) (evenp i))
      (let ((value (expt 2 log2-len-taxa-list)))
        (if (< i value)
            (hons nil (bits-to-tree i (1- log2-len-taxa-list)))
          (hons (bits-to-tree (- i value) (1- log2-len-taxa-list))
                nil))))))

(defun taxa-list-to-tree-alist-help (taxa-list pos num-of-bits)
  (declare (xargs :guard (integerp pos)))
  (cond ((atom taxa-list) nil)
        (t (cons (cons (car taxa-list)
                       (bits-to-tree pos num-of-bits))
                 (taxa-list-to-tree-alist-help (cdr taxa-list) (1+ pos)
                                              num-of-bits)))))

(defthm taxa-list-to-tree-alist-help-when-not-consp
  (implies (not (consp tl))
           (equal (taxa-list-to-tree-alist-help tl pos num-of-bits)
                  nil)))

(defthm taxa-list-to-tree-alist-help-of-consp
  (equal (taxa-list-to-tree-alist-help (cons first rest)
                                       pos num-of-bits)
         (cons (cons first
                     (bits-to-tree pos num-of-bits))
               (taxa-list-to-tree-alist-help rest
                                             (1+ pos)
                                             num-of-bits))))

(dis+ind taxa-list-to-tree-alist-help)

(defun taxa-list-to-tree-alist (taxa-list)
  (declare (xargs :guard t))
  (taxa-list-to-tree-alist-help taxa-list 0 (1- (ilog2 (len taxa-list)))))

(in-theory (disable taxa-list-to-tree-alist))

(defun build-taxa-list-tree-help (tree-depth pos index-to-taxon)
  (declare (xargs :guard (and (natp tree-depth)
                              (acl2-numberp pos))))
  (if (zp tree-depth)
      (cdr (het pos index-to-taxon))
    (hons (build-taxa-list-tree-help (1- tree-depth)
                                    (+ pos (expt 2 (1- tree-depth)))
                                    index-to-taxon)
          (build-taxa-list-tree-help (1- tree-depth)
                                    pos
                                    index-to-taxon))))

(defun build-taxa-list-tree (taxa-list)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns a mapping from each taxon in list to each taxon's bdd representation~/
;  ~/
;  Arguments:
;      (1) taxa-list - a list of taxa

;  "
  (declare (xargs :guard t))
  (let ((tree-depth (ilog2 (len taxa-list)))
        (index-to-taxon (taxa-list-to-index-taxon taxa-list)))
    (build-taxa-list-tree-help tree-depth 0 index-to-taxon)))

(in-theory (disable build-taxa-list-tree))

(defthm alistp-taxa-list-to-tree-alist-help
  (alistp-gen (taxa-list-to-tree-alist-help x y z)))

(defthm alistp-taxa-list-to-tree-alist
  (alistp-gen (taxa-list-to-tree-alist x))
  :hints (("Goal" :in-theory (enable taxa-list-to-tree-alist))))

(defthm consp-build-taxa-list-tree-help-from-ilog2-help
  (implies (and (integerp i)
                (<= 1 i))
           (consp (build-taxa-list-tree-help (ilog2-help i)
                                             pos
                                             y)))
  :hints (("Goal" :in-theory (enable ilog2-help))))

(defthm consp-build-taxa-list-tree-help-from-ilog2
  (implies (and (integerp i)
                (<= 2 i))
           (consp (build-taxa-list-tree-help (ilog2 i)
                                             pos
                                             y)))
  :hints (("Goal" :in-theory (enable ilog2))))

(defthm consp-build-taxa-list-tree-from-len-taxa-list
  (implies (<= 2 (len taxa-list))
           (consp (build-taxa-list-tree taxa-list)))
  :hints (("Goal" :in-theory (enable build-taxa-list-tree))))

;; Checks if the btree is a full btree with height level
(defun balanced-tree-helper (x level)
  (declare (xargs :guard (natp level)))
  (if (zp level)
      (atom x)
    (and (consp x)
         (balanced-tree-helper (car x) (1- level))
         (balanced-tree-helper (cdr x) (1- level)))))

(defthm balanced-tree-helper-when-not-consp
  (implies (not (consp x))
           (equal (balanced-tree-helper x level)
                  (if (zp level) t nil))))


(defthm balanced-tree-helper-of-consp
  (equal (balanced-tree-helper (cons first rest) level)
         (if (zp level) nil
           (and (balanced-tree-helper first (1- level))
                (balanced-tree-helper rest (1- level))))))

(dis+ind balanced-tree-helper)

;; gives height of a btree
(defun depth (x)
  (declare (xargs :guard t))
  (if (consp x)
      (1+ (max (depth (car x))
               (depth (cdr x))))
    0))

(defthm depth-when-not-consp
  (implies (not (consp x))
           (equal (depth x)
                  0)))

(defthm depth-of-consp
  (equal (depth (cons first rest))
         (1+ (max (depth first)
                  (depth rest)))))

(dis+ind depth)

;; checks if a btree is balanced at every level
(defun balanced-tree (x)
  (declare (xargs :guard t))
  (balanced-tree-helper x (depth x)))

(defthm balanced-tree-when-not-consp
  (implies (not (consp x))
           (equal (balanced-tree x)
                  t)))

(defthm balanced-tree-helper-level-zero-gives-atom
  (implies (balanced-tree-helper x 0)
           (not (consp x)))
  :hints (("Goal" :in-theory (enable balanced-tree-helper)))
  :rule-classes :forward-chaining)

(defthm balanced-tree-helper-gives-depth
  (implies (and (balanced-tree-helper x level)
                (not (zp level)))
           (equal (depth x)
                  level)))

(defthm balanced-tree-of-consp
  (implies (balanced-tree (cons first rest))
           (equal (depth first)
                  (depth rest))))

(in-theory (disable balanced-tree))

(defthm balanced-tree-of-cons-gives-balanced-tree-each
  (implies (balanced-tree (cons first rest))
           (and (balanced-tree first)
                (balanced-tree rest)))
  :hints (("Goal" :in-theory (enable balanced-tree))))

;; x is a list of btrees, y a single btree
;; checks that each of the btrees in x have a height no greater than
;; the height (depth) of y
(defun good-depths (x y)
  (declare (xargs :guard t))
  (if (consp x)
      (and (<= (depth (car x))
               (depth y))
           (good-depths (cdr x) y))
    t))

(defthm good-depths-when-not-consp
  (implies (not (consp x))
           (equal (good-depths x y)
                  t)))

(defthm good-depths-of-consp
  (equal (good-depths (cons first rest) y)
         (and (<= (depth first)
                  (depth y))
              (good-depths rest y))))

(dis+ind good-depths)

(defthm good-depths-consp-good-depth-car
  (implies (good-depths x y)
           (<= (depth (car x))
               (depth y))))

(defthm good-depths-cdr
  (implies (good-depths x y)
           (good-depths (cdr x) y)))

(defthm consp-gives-depth<0
  (implies (consp x)
           (< 0 (depth x)))
  :rule-classes (:rewrite :linear))


;; need depth of all assocs to be 0, which is what
;; good-index-taxon-halist gives us
(defthm depth-build-taxa-list-depth
  (implies (and (good-index-taxon-halist y)
                (integerp x)
                (<= 0 x))
           (equal (depth (build-taxa-list-tree-help x pos y))
                  x)))

(defthm depth-build-taxa-list-tree
  (implies (int-symlist taxa-list)
           (equal (depth (build-taxa-list-tree taxa-list))
                  (ilog2 (len taxa-list))))
  :hints (("Goal" :in-theory (enable build-taxa-list-tree))))

(defthm balanced-tree-helper-build-taxa-list-tree-help
  (implies (and (good-index-taxon-halist y)
                (integerp x)
                (<= 0 x))
           (balanced-tree-helper
            (build-taxa-list-tree-help x pos y)
            x)))

(defthm balanced-tree-helper-build-taxa-list-tree
  (implies (and (int-symlist taxa-list)
                (<= 2 (len taxa-list)))
           (balanced-tree-helper (build-taxa-list-tree taxa-list)
                                 (depth (build-taxa-list-tree
                                         taxa-list))))
  :hints (("Goal" :in-theory (enable build-taxa-list-tree))))

(defthm balanced-tree-build-taxa-list-tree
  (implies (and (int-symlist taxa-list)
                (<= 2 (len taxa-list)))
           (balanced-tree (build-taxa-list-tree taxa-list)))
  :hints (("Goal" :in-theory (enable balanced-tree
                                     build-taxa-list-tree))))

(defthm consp-build-taxa-list-tree-help
  (implies (and (integerp depth)
                (<= 1 depth))
           (consp (build-taxa-list-tree-help
                    depth p list)))
  :hints (("Subgoal *1/3'"
           :expand (build-taxa-list-tree-help 1 p list))))

(defthm consp-build-taxa-list-tree-when-consp
  (implies (<= 2 (len x))
           (consp (build-taxa-list-tree x)))
  :hints (("Goal" :in-theory (enable build-taxa-list-tree))))

(in-theory (disable build-taxa-list-tree-help))

(defthm good-depths-with-build-taxa-list-tree
  (implies (and (int-symlist taxa-list)
                (consp x)
                (good-depths
                 x
                 (build-taxa-list-tree taxa-list)))
           (<= (depth (car x))
               (ilog2 (len taxa-list)))))

(defthm consp-bits-to-tree
  (implies (and (integerp x)
                (<= 0 x))
           (consp (bits-to-tree i x))))

(defthm good-depths-through-evens
  (implies (good-depths x y)
           (good-depths (evens-gen x) y))
  :hints (("Goal" :induct (evens-gen x))))

