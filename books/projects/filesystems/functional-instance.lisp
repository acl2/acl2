(in-package "ACL2")

(include-book "file-system-lemmas")
(include-book "std/lists/sets" :dir :system)

(defthm consp-of-strip-cars
  (iff (consp (strip-cars x)) (consp x)))

(defun sum-cdrs (root alist)
  (if (atom alist) root (sum-cdrs (+ (cdar alist) root) (cdr alist))))

(defthmd sum-cdrs-of-true-list-fix
  (equal (sum-cdrs root (true-list-fix alist))
         (sum-cdrs root alist)))

(defcong
  list-equiv equal (sum-cdrs root alist)
  2
  :hints (("goal" :use ((:instance sum-cdrs-of-true-list-fix
                                   (alist alist-equiv))
                        sum-cdrs-of-true-list-fix))))

(defund
  sum-cdrs-by-seq (root alist seq)
  (declare (xargs :measure (len seq)))
  (if (or (atom seq)
          (atom (assoc-equal (car seq) alist)))
      root
      (sum-cdrs-by-seq (+ root
                          (cdr (assoc-equal (car seq) alist)))
                       (remove-assoc-equal (car seq) alist)
                       (cdr seq))))

(defthm sum-cdrs-of-+-1
  (implies (syntaxp (variablep root))
           (equal (sum-cdrs (+ x root) alist)
                  (+ (sum-cdrs root alist) x)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies (syntaxp (variablep root))
             (equal (sum-cdrs (+ root x) alist)
                    (+ (sum-cdrs root alist) x))))))

(defthm sum-cdrs-by-seq-of-+-1
  (implies (syntaxp (variablep root))
           (equal (sum-cdrs-by-seq (+ x root) alist seq)
                  (+ (sum-cdrs-by-seq root alist seq) x)))
  :hints (("Goal" :in-theory (enable sum-cdrs-by-seq)) )
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies (syntaxp (variablep root))
             (equal (sum-cdrs-by-seq (+ root x) alist seq)
                    (+ (sum-cdrs-by-seq root alist seq) x))))))

;; Binding hypotheses aren't seeming to work like they do with rewrite rules...
(defthm
  sum-cdrs-of-remove-assoc
  (implies
   (and
    (no-duplicatesp-equal (strip-cars alist))
    (not (member-equal nil (strip-cars alist)))
    (consp (assoc-equal name alist)))
   (equal (+ (sum-cdrs root (remove-assoc-equal name alist))
             (cdr (assoc-equal name alist)))
          (sum-cdrs root alist)))
  :rule-classes
  ((:forward-chaining
    :trigger-terms ((sum-cdrs root (remove-assoc-equal name alist))))))

(encapsulate
  ()

  (local
   (defthm lemma
     (implies (and (consp (assoc-equal (car seq) alist))
                   (set-equiv seq (strip-cars alist))
                   (no-duplicatesp-equal (strip-cars alist))
                   (car seq)
                   (not (member-equal nil (cdr seq))))
              (equal (+ (cdr (assoc-equal (car seq) alist))
                        (sum-cdrs root
                                  (remove-assoc-equal (car seq) alist)))
                     (sum-cdrs root alist)))
     :hints (("goal" :in-theory (disable sum-cdrs-of-remove-assoc)
              :use (:instance sum-cdrs-of-remove-assoc
                              (name (car seq)))))
     :rule-classes
     ((:forward-chaining
       :trigger-terms ((sum-cdrs root
                                 (remove-assoc-equal (car seq)
                                                     alist)))))))

  (defthm
    sum-cdrs-by-seq-correctness-1
    (implies (and (set-equiv seq (strip-cars alist))
                  (no-duplicatesp-equal (strip-cars alist))
                  (no-duplicatesp-equal seq)
                  (not (member-equal nil seq)))
             (equal (sum-cdrs-by-seq root alist seq)
                    (sum-cdrs root alist)))
    :hints
    (("goal" :induct (sum-cdrs-by-seq root alist seq)
      :in-theory (e/d (sum-cdrs-by-seq) (set-equiv)))
     ("subgoal *1/1.1"
      :in-theory (disable member-of-strip-cars)
      :use ((:instance member-of-strip-cars (alist alist)
                       (x (car seq))))))))
