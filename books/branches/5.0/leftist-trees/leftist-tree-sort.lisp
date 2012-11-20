(in-package "ACL2")

(include-book "../sorting/perm")
(include-book "../sorting/ordered-perms")
(include-book "../sorting/convert-perm-to-how-many")

(include-book "leftist-tree-defuns")
(include-book "leftist-tree-defthms")

;;;;;;;;;;;;;;
;; HEAPSORT ;;
;;;;;;;;;;;;;;

;; -- At this point, heapsort is fairly simple. We define
;;    "ltree-to-list" which constructs a list by calling
;;    find-min and delete-min repeatedly on the tree.
;;    Then to sort a list, we just need to convert it to 
;;    a leftist tree via build-lt, and then call 
;;    ltree-to-list on the result.

(defun ltree-to-list (tree)
  (declare 
   (xargs :measure (size-lt tree)))
  (cond ((atom tree) nil)
        (t (cons (find-min-lt tree)
                 (ltree-to-list (delete-min-lt tree))))))

;% (ltree-sort l)
; -- Computes a leftist-heapsort of a list.
(defun ltree-sort (l)
  (ltree-to-list (build-lt l)))

;;;;;;;;;;;;;;;;;;;;;;;;;
;; HEAPSORT IS CORRECT ;;
;;;;;;;;;;;;;;;;;;;;;;;;;

;; Note: This comes down to proving that the car of the 
;;       ltree-to-list of a proper-lt tree is equal to the
;;       root of the original tree. These rewrite rules
;;       are disabled in general, since neither is really
;;       simpler than the other, and both are used
;;       independently in proving the main theorem.

(local
 (defthmd root-equals-car-list-lt
   (implies (and (consp tree)
                 (proper-lt tree))
            (equal (cadr tree)
                   (car (ltree-to-list tree))))))

(local
 (defthmd car-list-equals-root-lt
   (implies (and (consp tree)
                 (proper-lt tree))
            (equal (car (ltree-to-list tree))
                   (cadr tree)))))

(local 
 (defthmd orderedp-proper-ltree-to-list-ltree-L1
   (implies (and (consp left_tree)
                 (consp right_tree)
                 (proper-lt left_tree)
                 (proper-lt right_tree)
                 (lexorder x (root-lt left_tree))
                 (lexorder x (root-lt right_tree)))
            (lexorder x
                      (root-lt (merge-lt left_tree right_tree))))
   :hints (("Goal"
            :induct (merge-lt left_tree right_tree)))))

(defthm orderedp-proper-ltree-to-list
  (implies (proper-lt tree)
           (orderedp (ltree-to-list tree)))
  :hints (("Subgoal *1/3.3'"
           :in-theory (enable car-list-equals-root-lt))
          ("Subgoal *1/3.2'"
           :in-theory (enable root-equals-car-list-lt))
          ("Subgoal *1/3.1"
           :in-theory (enable car-list-equals-root-lt))
          ("Subgoal *1/3.1'"
           :use ((:instance orderedp-proper-ltree-to-list-ltree-L1
                            (x (cadr tree))
                            (left_tree (caddr tree))
                            (right_tree (cadddr tree)))))))

(defthm orderedp-ltree-sort
  (orderedp (ltree-sort l)))

(defthm true-listp-ltree-sort
  (true-listp (ltree-sort l)))

;; how-many-lt ;;
(defun how-many-lt (e tree)
  (cond ((is-empty-lt tree) 0)
        ((equal e (root-lt tree))
         (+ 1 (how-many-lt e (left-lt tree))
            (how-many-lt e (right-lt tree))))
        ((lexorder (root-lt tree) e)
         (+ (how-many-lt e (left-lt tree))
            (how-many-lt e (right-lt tree))))
        (t 0)))

(defthm how-many-lt-zero
  (implies (not (lexorder (root-lt tree) e))
           (equal (how-many-lt e tree) 0)))

; root(tree1) > root(tree2)
; root(tree2) > e
; ==> (how-many-lt e tree1) = 0
(local 
 (defthmd how-many-merge-lt-L1
   (implies (and (consp tree1)
                 (consp tree2)
                 (proper-lt tree1)
                 (proper-lt tree2)
                 (not (lexorder (root-lt tree1)
                                (root-lt tree2)))
                 (not (lexorder (root-lt tree2)
                                e)))
            (equal (how-many-lt e tree1) 0))))

; root(tree1) <= root(tree2)
; e < root(tree1)
; ==> (how-many-lt e tree2) = 0
(local
 (defthmd how-many-merge-lt-L2
   (implies (and (consp tree1)
                 (consp tree2)
                 (proper-lt tree1)
                 (proper-lt tree2)
                 (lexorder (root-lt tree1)
                           (root-lt tree2))
                 (not (lexorder (root-lt tree1) e)))
            (equal (how-many-lt e tree2) 0))))

(defthm how-many-merge-lt
  (implies (and (proper-lt tree1)
                (proper-lt tree2))
           (equal (how-many-lt e (merge-lt tree1 tree2))
                  (+ (how-many-lt e tree1)
                     (how-many-lt e tree2))))
  :hints (("Goal"
           :in-theory (enable how-many-merge-lt-L1
                              how-many-merge-lt-L2)
           :induct (merge-lt tree1 tree2))))

(defthm how-many-insert-lt
  (implies (proper-lt tree)
           (equal (how-many-lt e (insert-lt e tree))
                  (+ 1 (how-many-lt e tree)))))

(defthm how-many-delete-min-lt
  (implies (and (proper-lt tree)
                (consp tree))
           (equal (how-many-lt e (delete-min-lt tree))
                  (+ (how-many-lt e (left-lt tree))
                     (how-many-lt e (right-lt tree))))))

(defthm how-many-build-lt
  (equal (how-many-lt e (build-lt l))
         (how-many e l)))

(local
 (defthm how-many-ltree-to-list-L1
   (implies (and (proper-lt tree)
                 (not (lexorder x e))
                 (lexorder x (root-lt tree)))
            (equal (how-many-lt e tree) 0))))

(defthm how-many-ltree-to-list
  (implies (proper-lt tree)
           (equal (how-many e (ltree-to-list tree))
                  (how-many-lt e tree))))

(defthm how-many-ltree-sort
  (equal (how-many e (ltree-sort x))
         (how-many e x)))
