#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
;;
;; Dependency Trees for Data Dependency Analysis
;; Jared Davis 
;;

(in-package "DTREE")
(include-book "raw")
(include-book "set")
(include-book "erase")

;; We introduce four functions: (haschild name dtree) returns true iff a dtree
;; has an immediate child with the given name.  Getchild returns such a child,
;; or dtree::*default* if no such child exists.  Setchild adds or updates a
;; child in the dtree, and erasechild erases a child.  These functions are
;; basically alternatives to in, get, set, and erase, but which are only useful
;; for manipulating single-level dtrees.
;;
;; These functions have really been added only as an afterthought, and we hope
;; they might be useful abstractions.  But, we realize that the reasoning
;; strategy we provide here is probably insufficient.  So, at the end of this
;; file, we provide four theorems, which are "abbreviation" rules (i.e., simple
;; rewrite rules) that should automatically eliminate all occurrences of these
;; functions from your proofs.
;;
;;  - haschild-is-in-of-singleton-list
;;  - setchild-is-set-of-singleton-list
;;  - getchild-is-get-of-singleton-list
;;  - erasechild-is-erase-of-singleton-list
;;
;; These theorems can be disabled if they are problematic, and you can then
;; fall back on the reasoning in this file.  However, generally we think it is
;; best to work with "the real thing" rather than these child functions.

(defund haschild (name dtree)
  (declare (xargs :guard (dtreep dtree)))
  (map::in name (children dtree)))

(defund getchild (name dtree)
  (declare (xargs :guard (dtreep dtree)))
  ;; (haschild name dtree))))
  (if (haschild name dtree)
      (map::get name (children dtree))
    dtree::*default*))

(defund setchild (name value dtree)
  (declare (xargs :guard (and (dtreep dtree)
                              (dtreep value))))
  (rawdtree (localdeps dtree)
            (map::set name (dtreefix value) (children dtree))))

(defund erasechild (name dtree)
  (declare (xargs :guard (dtreep dtree)))
  (rawdtree (localdeps dtree)
            (map::erase name (children dtree))))


(defthm dtreep-of-getchild
  (dtreep (getchild name dtree))
  :hints(("goal" :in-theory (enable getchild haschild))))

(defthm dtreep-of-setchild
  (dtreep (setchild name value dtree))
  :hints(("goal" :in-theory (enable setchild))))

(defthm dtreep-of-erasechild
  (dtreep (setchild name value dtree))
  :hints(("goal" :in-theory (enable setchild))))


(defcong equivdeps equal (haschild name dtree) 2
  :hints(("Goal" :in-theory (enable haschild))))

(defcong equivdeps equivdeps (getchild name dtree) 2
  :hints(("Goal" :in-theory (enable getchild))))

(defcong equivdeps equivdeps (setchild name value dtree) 2
  :hints(("Goal" :in-theory (enable setchild))))

(defcong equiv equiv (getchild name dtree) 2
  :hints(("Goal" :in-theory (enable getchild))))

(defcong equiv equiv (setchild name value dtree) 2
  :hints(("Goal" :in-theory (enable setchild))))

(defcong equiv equiv (setchild name value dtree) 3
  :hints(("Goal" :in-theory (enable setchild))))

(defcong equiv equiv (erasechild name dtree) 2
  :hints(("Goal" :in-theory (enable erasechild))))



(defthm haschild-of-setchild
  (equal (haschild a (setchild b value dtree))
         (if (equal a b)
             t
           (haschild a dtree)))
  :hints(("Goal" :in-theory (enable haschild setchild))))

(defthm haschild-of-erasechild
  (equal (haschild a (erasechild b dtree))
         (if (equal a b)
             nil
           (haschild a dtree)))
  :hints(("Goal" :in-theory (enable haschild erasechild))))



(defthm getchild-when-not-haschild
  (implies (not (haschild a dtree))
           (equal (getchild a dtree)
                  dtree::*default*))
  :hints(("Goal" :in-theory (enable haschild getchild))))

(defthm getchild-of-setchild
  (equal (getchild a (setchild b value dtree))
         (if (equal a b)
             (dtreefix value)
           (getchild a dtree)))
  :hints(("Goal" :in-theory (enable getchild setchild haschild))
         ("Subgoal 1" :cases ((haschild a dtree)))))

(defthm getchild-of-erasechild
  (equal (getchild a (erasechild b dtree))
         (if (equal a b)
             dtree::*default*
           (getchild a dtree)))
  :hints(("Goal" :in-theory (enable getchild erasechild haschild))))



(defthm erasechild-of-erasechild-different
  (implies (case-split (not (equal a b)))
           (equiv (erasechild a (erasechild b dtree))
                  (erasechild b (erasechild a dtree))))
  :hints(("Goal" :in-theory (enable erasechild)))
  :rule-classes ((:rewrite :loop-stopper ((a b setchild)))))

(defthm erasechild-of-erasechild-same
  (equiv (erasechild a (erasechild a dtree))
         (erasechild a dtree))
  :hints(("Goal" :in-theory (enable erasechild))))



(defthm setchild-of-setchild-different
  (implies (case-split (not (equal a b)))
           (equiv (setchild a v1 (setchild b v2 dtree))
                  (setchild b v2 (setchild a v1 dtree))))
  :hints(("Goal" :in-theory (enable setchild)))
  :rule-classes ((:rewrite :loop-stopper ((a b setchild)))))

(defthm setchild-of-setchild-same
  (equiv (setchild a v1 (setchild a v2 dtree))
         (setchild a v1 dtree))
  :hints(("Goal" :in-theory (enable setchild))))



(defthm erasechild-of-setchild-different
  (implies (case-split (not (equal a b)))
           (equiv (erasechild a (setchild b val dtree))
                  (setchild b val (erasechild a dtree))))
  :hints(("Goal" :in-theory (enable erasechild setchild)))
  :rule-classes ((:rewrite :loop-stopper ((a b setchild)))))

(defthm erasechild-of-setchild-same
  (equiv (erasechild a (setchild a val dtree))
         (erasechild a dtree))
  :hints(("Goal" :in-theory (enable erasechild setchild))))



(defthm setchild-of-erasechild-different
  (implies (case-split (not (equal a b)))
           (equiv (setchild a val (erasechild b dtree))
                  (erasechild b (setchild a val dtree))))
  :hints(("Goal" :in-theory (enable erasechild setchild)))
  :rule-classes ((:rewrite :loop-stopper ((a b setchild)))))

(defthm setchild-of-erasechild-same
  (equiv (setchild a val (erasechild a dtree))
         (setchild a val dtree))
  :hints(("Goal" :in-theory (enable erasechild setchild))))





(defthm haschild-is-in-of-singleton-list
  (equal (haschild a dtree)
         (in (list a) dtree))
  :hints(("Goal" :in-theory (enable haschild in))))

(defthm setchild-is-set-of-singleton-list
  (equal (setchild a val dtree)
         (set (list a) val dtree))
  :hints(("Goal" :in-theory (enable setchild set))))

(defthm getchild-is-get-of-singleton-list
  (equal (getchild a dtree)
         (get (list a) dtree))
  :hints(("Goal" :in-theory (enable in getchild get))))


;; Not true anymore.

#+joe
(defthm erasechild-is-erase-of-singleton-list
  (equal (erasechild a dtree)
         (erase (list a) dtree))
  :hints(("Goal" :in-theory (enable erasechild erase))))
