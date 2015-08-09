(in-package "ACL2")
(include-book "misc/hons-help2" :dir :system)


;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.
; (defdoc TASPI
;   ":Doc-Section TASPI
;    Documentation for TASPI.~/
;    Tree Analysis System for Phylogenetic Inquiry~/
;    A suite a functions for working with trees.")

(def-macro-alias hhshrink-alist fast-alist-fork! 2)
(def-macro-alias member-hqual hons-member-equal 2)

(defmacro dis+ind (x)
  `(encapsulate ()
                (in-theory (disable ,x))
                (in-theory (enable (:induction ,x)))))

;; Utility for theorems whose proofs involve mutual induction.
;; (flag flg val) creates a bind-free hyp saying to bind flg to val and a
;; logical hyp (equal flg val).
(defun bind-free-binding-for-flag (var val)
  (declare (xargs :guard t))
  `((,var . ',val)))

(defmacro flag (var val)
  `(and (bind-free (bind-free-binding-for-flag ',var ,val))
        (equal ,var ,val)))

(defun build-fast-alist-from-alist (l acc)
  (declare (xargs :guard t))
  (cond ((atom l) acc)
        ((consp (car l))
         (hons-acons (caar l) (cdar l)
                     (build-fast-alist-from-alist (cdr l) acc)))
        (t (build-fast-alist-from-alist (cdr l) acc))))

; Useful measure for trees
(defun tree-measure (x flg)
  (declare (xargs :guard t))
  (make-ord 1 (1+ (acl2-count x)) (if flg 1 0)))

;; handy induction to have around
(defun tree-p-induction (x flg)
  (declare (xargs :measure (tree-measure x flg)
                  :guard t))
  (if flg
      (if (atom x)
          nil
        (tree-p-induction x nil))
    (if (atom x)
        nil
      (prog2$ (tree-p-induction (car x) t)
              (tree-p-induction (cdr x) nil)))))


(defun evens-gen (x)
  (declare (xargs :guard t))
  (if (consp x)
      (if (consp (cdr x))
          (cons (car x)
                (evens-gen (cddr x)))
        (list (car x)))
    nil))

(defthm evens-gen-when-not-consp
  (implies (not (consp x))
           (equal (evens-gen x)
                  nil)))

(defthm evens-gen-of-consp
  (equal (evens-gen (cons x y))
         (if (consp y)
             (cons x (evens-gen (cdr y)))
           (list x))))

(dis+ind evens-gen)

(defun odds-gen (x)
  (declare (xargs :guard t))
  (if (consp x)
      (evens-gen (cdr x))
    nil))

(defthm odds-gen-when-not-consp
  (implies (not (consp x))
           (equal (odds-gen x)
                  nil)))

(defthm odds-gen-of-consp
  (equal (odds-gen (cons x y))
         (evens-gen y)))

(in-theory (disable odds-gen))

;; thm for sort-bdd-fringes measure
(defthm evens-gen-smaller
  (implies (and (consp x)
                (consp (cdr x)))
           (< (acl2-count (evens-gen x))
              (acl2-count x)))
  :hints (("Goal" :in-theory (enable evens-gen))))

(defthm even-gen-smaller-2
  (implies (consp x)
           (< (acl2-count (evens-gen x))
              (+ 1 (acl2-count x))))
  :hints (("Goal" :in-theory (enable evens-gen))))

(defthm even-gen-smaller-3
  (implies (consp alst2)
           (< (acl2-count (evens-gen alst2))
              (+ 1 (acl2-count alst1)
                 (acl2-count alst2))))
  :hints (("Goal" :in-theory (disable even-gen-smaller-2)
           :use (:instance even-gen-smaller-2
                           (x alst2)))))

(defun app (x y)
  (declare (xargs :guard t))
  (if (consp x)
      (cons (car x) (app (cdr x) y))
    y))

(defthm app-when-not-consp
  (implies (not (consp x))
           (equal (app x y)
                  y)))

(defthm app-of-consp
  (equal (app (cons x y) z)
         (cons x (app y z))))

(dis+ind app)

; Matt K., 11/2014: Changed the names "flatten" to "taspi-flatten" and "rev" to
; "taspi-rev" below, to avoid conflicts with std/lists/list-defuns.lisp,
; std/lists/flatten.lisp, and std/lists/rev.lisp.

(defun taspi-flatten (x)
  (declare (xargs :guard t))
  (if (consp x)
      (app (taspi-flatten (car x))
           (taspi-flatten (cdr x)))
    (list x)))

(defthm taspi-flatten-when-not-consp
  (implies (not (consp x))
           (equal (taspi-flatten x)
                  (list x))))

(defthm flatten-of-consp
  (equal (taspi-flatten (cons x y))
         (app (taspi-flatten x)
              (taspi-flatten y))))

(dis+ind taspi-flatten)

(defun taspi-rev (x)
  (declare (xargs :guard t))
  (if (consp x)
      (app (taspi-rev (cdr x)) (list (car x)))
    nil))

(defthm taspi-rev-when-not-consp
  (implies (not (consp x))
           (equal (taspi-rev x)
                  nil)))

(defthm rev-of-consp
  (equal (taspi-rev (cons x y))
         (app (taspi-rev y) (list x))))

(dis+ind taspi-rev)

(defun my-join (fn args)
  (declare (xargs :guard t))
  (if (consp args)
      (if (consp (cdr args))
          (if (consp (cddr args))
              (cons fn (cons (car args)
                             (cons (my-join fn (cdr args)) nil)))
            (cons fn args))
        "Error in my-join")
    "Error in second branch of my-join"))

(defmacro app-gen (x y &rest rst)
  (my-join 'app (cons x (cons y rst))))

(defun nth-gen (n l)
  (declare (xargs :guard (natp n)))
  (if (atom l)
      nil
    (if (zp n)
        (car l)
      (nth-gen (- n 1) (cdr l)))))

(defthm nth-gen-when-not-consp
  (implies (not (consp l))
           (equal (nth-gen n l)
                  nil)))

(defthm nth-gen-of-consp
  (equal (nth-gen n (cons x y))
         (if (zp n)
             x
           (nth-gen (- n 1) y))))

(dis+ind nth-gen)


(defun alistp-gen (x)
  (declare (xargs :guard t))
  (if (consp x)
      (and (consp (car x))
           (alistp-gen (cdr x)))
    t))

(defthm alistp-gen-of-not-consp
  (implies (not (consp x))
           (equal (alistp-gen x) t)))

(defthm alistp-gen-when-consp
  (equal (alistp-gen (cons first rest))
         (and (consp first)
              (alistp-gen rest))))

(dis+ind alistp-gen)

(defthm alistp-gen-through-evens-cdr
  (implies (alistp-gen x)
           (alistp-gen (evens-gen (cdr x)))))

(defthm alistp-gen-build-fast-alist-from-alist
  (implies (alistp-gen acc)
           (alistp-gen (build-fast-alist-from-alist x acc))))

(defun strip-cars-gen (x)
  (declare (xargs :guard (alistp-gen x)))
  (if (consp x)
      (cons (car (car x))
            (strip-cars-gen (cdr x)))
    nil))

(defthm strip-cars-gen-when-not-consp
  (implies (not (consp x))
           (equal (strip-cars-gen x)
                  nil)))

(defthm strip-cars-gen-of-consp
  (equal (strip-cars-gen (cons first rest))
         (cons (car first)
               (strip-cars-gen rest))))

(dis+ind strip-cars-gen)

(defun strip-cdrs-gen (x)
  (declare (xargs :guard (alistp-gen x)))
  (if (consp x)
      (cons (cdr (car x))
            (strip-cdrs-gen (cdr x)))
    nil))

(defthm strip-cdrs-gen-when-not-consp
  (implies (not (consp x))
           (equal (strip-cdrs-gen x)
                  nil)))

(defthm strip-cdrs-gen-of-consp
  (equal (strip-cdrs-gen (cons first rest))
         (cons (cdr first)
               (strip-cdrs-gen rest))))

(dis+ind strip-cdrs-gen)

(defun del-pair (x l)
  (declare (xargs :guard (alistp-gen l)))
  (if (consp l)
      (if (equal x (caar l))
          (cdr l)
        (cons (car l) (del-pair x (cdr l))))
    nil))

(defthm del-pair-when-not-consp
  (implies (not (consp l))
           (equal (del-pair x l)
                  nil)))

(defthm del-pair-of-consp
  (equal (del-pair x (cons first rest))
         (if (equal x (car first))
             rest
           (cons first (del-pair x rest)))))

(dis+ind del-pair)
