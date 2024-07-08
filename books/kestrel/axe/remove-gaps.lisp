; Removing gaps in DAG node numbering
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2024 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "translation-array")
(local (include-book "kestrel/alists-light/alistp" :dir :system))
(local (include-book "kestrel/alists-light/strip-cars" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))

(local
  (defthm strip-cars-of-reverse-list
    (equal (strip-cars (reverse-list alist))
           (reverse-list (strip-cars alist)))
    :hints (("Goal" :in-theory (enable strip-cars reverse-list)))))

(local
  (defthm alistp-of-reverse-list
    (equal (alistp (reverse-list alist))
           (alistp (true-list-fix alist)))
    :hints (("Goal" :in-theory (enable alistp reverse-list)))))

(local
  (defthm rational-listp-of-reverse-list
    (equal (rational-listp (reverse-list list))
           (rational-listp (true-list-fix list)))
    :hints (("Goal" :in-theory (enable rational-listp reverse-list true-list-fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund remove-gaps-in-dag-aux (rev-dag ;nodenums in ascending order
                                next-nodenum
                                dag-acc  ;nodenums in descending order
                                translation-array ;maps nodes already seen in rev-dag to nodes in dag-array
                                )
  (declare (xargs :guard (and (weak-dagp-aux rev-dag)
                              (natp next-nodenum)
                              ;; (true-listp dag-acc)
                              (array1p 'translation-array translation-array)
                              (translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array)
                              (all-< (strip-cars rev-dag) (alen1 'translation-array translation-array)))
                  :guard-hints (("Goal" :do-not '(generalize eliminate-destructors)
                                 :expand (weak-dagp-aux rev-dag)
                                 :in-theory (enable strip-cars dag-exprp)))))
  (if (endp rev-dag)
      dag-acc
    (let* ((entry (first rev-dag))
           (nodenum (car entry))
           (expr (cdr entry)))
      (if (variablep expr)
          (remove-gaps-in-dag-aux (rest rev-dag)
                                  (+ 1 next-nodenum)
                                  (cons (cons next-nodenum expr) dag-acc)
                                  (aset1 'translation-array translation-array nodenum next-nodenum))
        (let ((fn (ffn-symb expr)))
          (if (eq 'quote fn) ; note that the constant will be inlined when we handle the parents
              (remove-gaps-in-dag-aux (rest rev-dag)
                                      next-nodenum ; we don't use a node for the constant
                                      dag-acc
                                      (aset1 'translation-array translation-array nodenum expr))
            ;;else, it's a regular function call:
            (let* ((args (dargs expr))
                   (renamed-args (translate-args args translation-array)))
              (remove-gaps-in-dag-aux (rest rev-dag)
                                      (+ 1 next-nodenum)
                                      (cons (cons next-nodenum (cons fn renamed-args)) dag-acc)
                                      (aset1 'translation-array translation-array nodenum next-nodenum)))))))))

;; DAG can have gaps in the numbering (e.g., may only include relevant nodes) but all mentioned nodes should exist
;; and nodes should be in decreasing order as in a normal DAG.
(defund remove-gaps-in-dag (dag)
  (declare (xargs :guard (and (weak-dagp-aux dag)
                              (consp dag)
                              (<= (car (car dag)) *max-1d-array-index*)
                              (all-< (strip-cars (reverse-list dag))
                                     (+ 1 (car (car dag)))))))
  (let* ((top-nodenum (top-nodenum dag))
         (len (+ 1 top-nodenum)))
    (remove-gaps-in-dag-aux (reverse dag)
                            0
                            nil
                            (make-empty-array 'translation-array len))))
