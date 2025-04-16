; A tool to define a merge sort function, given a comparison function.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: IN-PROGRESS

;; This books provides the defmergesort tool, which builds a fast merge-sort
;; (the way it splits the list seems faster than using evens and odds).

(include-book "pack")

(defun defmergesort-fn (merge-sort-name
                        merge-name
                        comparison-fn ;; todo: allow an expression?
                        element-pred
                        verify-guards
                        extra-theorems
                        )
  (declare (xargs :guard (and (symbolp merge-name)
                              (symbolp merge-sort-name)
                              (symbolp comparison-fn) ; todo: allow a lambda?
                              (symbolp element-pred)
                              (booleanp verify-guards)
                              (booleanp extra-theorems)))) ;todo: flesh this out
  (let* ((list-pred (pack$ 'all- element-pred))
         (list-pred-of-mv-nth-0-of-split-list-fast-aux-theorem-name (pack$ list-pred '-of-mv-nth-0-of-split-list-fast-aux))
         (list-pred-of-mv-nth-0-of-split-list-fast-theorem-name (pack$ list-pred '-of-mv-nth-0-of-split-list-fast))
         (list-pred-of-mv-nth-1-of-split-list-fast-aux-theorem-name (pack$ list-pred '-of-mv-nth-1-of-split-list-fast-aux))
         (list-pred-of-mv-nth-1-of-split-list-fast-theorem-name (pack$ list-pred '-of-mv-nth-1-of-split-list-fast))
         ;;(list-pred-of-revappend-theorem-name (pack$ list-pred '-of-revappend))
         (list-pred-of-cons-theorem-name (pack$ list-pred '-of-cons-for-defmergesort))
         (list-pred-of-cdr-theorem-name (pack$ list-pred '-of-cdr-for-defmergesort))
         (element-pred-of-car-theorem-name (pack$ 'use- list-pred '-for-car-for-defmergesort))
         (list-pred-of-merge-theorem-name (pack$ list-pred '-of- merge-name))
         (list-pred-of-merge-sort-theorem-name (pack$ list-pred '-of- merge-sort-name))
         (true-listp-of-merge-theorem-name (pack$ 'true-listp-of- merge-name))
         (true-listp-of-merge-sort-theorem-name (pack$ 'true-listp-of- merge-sort-name)))
    `(progn
       ;; Always needed:
       (include-book "kestrel/utilities/split-list-fast-defs" :dir :system)
       ;; Reasoning support for basic theorems:
       (local (include-book "kestrel/utilities/split-list-fast" :dir :system))
       ;; Needed to express the extra theorems, but sometimes causes name clashes:
       ,@(and extra-theorems `((include-book "kestrel/lists-light/perm-def" :dir :system)))
       (encapsulate
         ()
         (local (include-book "kestrel/lists-light/revappend" :dir :system))
         (local (include-book "kestrel/utilities/merge-sort-generic" :dir :system))

         ;; Checks that all elements of X satisfy the ELEMENT-PRED.
         ;; We try to be compatible here with what defforall does.
         (defund ,list-pred (x)
           (declare (xargs :guard t
                           :verify-guards nil))
           (if (atom x)
               t
             (and (,element-pred (first x))
                  (,list-pred (rest x)))))

         ;; Made local so as not to conflict with what defforall would generate
         (local
          (defthm ,list-pred-of-cons-theorem-name
            (equal (,list-pred (cons x y))
                   (and (,element-pred x)
                        (,list-pred y)))
            :hints (("Goal" :in-theory (enable ,list-pred atom car-cons cdr-cons)))))

         ;; Made local so as not to conflict with what defforall would generate
         (local
          (defthm ,element-pred-of-car-theorem-name
            (implies (and (,list-pred x)
                          (consp x))
                     (,element-pred (car x)))
            :hints (("Goal" :in-theory (enable ,list-pred atom car-cons cdr-cons)))))

         ;; Made local so as not to conflict with what defforall would generate
         (local
          (defthm ,list-pred-of-cdr-theorem-name
            (implies (,list-pred x)
                     (,list-pred (cdr x)))
            :hints (("Goal" :in-theory (enable ,list-pred atom car-cons cdr-cons)))))

         ,@(and verify-guards `((verify-guards ,list-pred)))

         ;; Merge 2 sorted lists
         (defund ,merge-name (l1 l2 acc)
           (declare (xargs :measure (+ (len l1) (len l2))
                           :hints (("Goal" :in-theory nil
                                    :use (:functional-instance (:termination-theorem merge-generic)
                                                               (generic-comparison ,comparison-fn))))
                           :guard (and (,list-pred l1)
                                       (,list-pred l2)
                                       (true-listp acc))
                           ,@(if verify-guards
                                 nil
                               '(:verify-guards nil))))
           (cond ((atom l1) (revappend acc l2)) ;; todo: would null would be faster than atom?
                 ((atom l2) (revappend acc l1))
                 ((,comparison-fn (car l1) (car l2))
                  (,merge-name (cdr l1)
                               l2 (cons (car l1) acc)))
                 (t (,merge-name l1 (cdr l2)
                                 (cons (car l2) acc)))))

         (defthm ,(pack$ 'consp-of- merge-name)
           (equal (consp (,merge-name l1 l2 acc))
                  (or (consp l1)
                      (consp l2)
                      (consp acc)))
           :hints (("Goal" :induct t
                    :in-theory (enable ,merge-name))))

         ;; Merge sort the list L
         (defund ,merge-sort-name (l)
           (declare (xargs :measure (len l)
                           :hints (("Goal" :in-theory nil
                                    :use (:functional-instance (:termination-theorem merge-sort-generic)
                                                               (generic-comparison ,comparison-fn))))
                           :guard (and (true-listp l)
                                       (,list-pred l))
                           :verify-guards nil ;done below
                           ))
           (if (atom (cdr l))
               l
             (mv-let (first-half second-half)
               (split-list-fast l)
               (,merge-name (,merge-sort-name first-half)
                            (,merge-sort-name second-half)
                            nil))))

         (defthm ,(pack$ 'consp-of- merge-sort-name)
           (equal (consp (,merge-sort-name l))
                  (consp l))
           :hints (("Goal" :induct (,merge-sort-name l)
                    :in-theory (enable ,merge-sort-name
                                       consp-of-mv-nth-0-of-split-list-fast
                                       consp-of-mv-nth-1-of-split-list-fast))))

         ;; todo: might these clash with the theorems generated by a defforall?  or with other pre-exisiting theorems?
         ;; (defthm list-pred-of-cons
         ;;   (equal (,list-pred (cons a x))
         ;;          (and

         ;;should we make any of these local?
         ;; todo: limit the theory used in these..
         ;;defforall could do these too?
         (defthm ,list-pred-of-mv-nth-0-of-split-list-fast-aux-theorem-name
           (implies (and (,list-pred lst)
                         (,list-pred acc)
                         (<= (len tail) (len lst)))
                    (,list-pred (mv-nth 0 (split-list-fast-aux lst tail acc))))
           :hints (("Goal" :in-theory '(,list-pred)
                    :use (:functional-instance all-generic-predp-of-mv-nth-0-of-split-list-fast-aux
                                               (generic-predp ,element-pred)
                                               (all-generic-predp ,list-pred)))))

         (defthm ,list-pred-of-mv-nth-0-of-split-list-fast-theorem-name
           (implies (,list-pred lst)
                    (,list-pred (mv-nth 0 (split-list-fast lst))))
           :hints (("Goal" :in-theory nil ;; all constraints should be cached
                    :use (:functional-instance all-generic-predp-of-mv-nth-0-of-split-list-fast
                                               (generic-predp ,element-pred)
                                               (all-generic-predp ,list-pred)))))

         (defthm ,list-pred-of-mv-nth-1-of-split-list-fast-aux-theorem-name
           (implies (,list-pred lst)
                    (,list-pred (mv-nth 1 (split-list-fast-aux lst tail acc))))
           :hints (("Goal" :in-theory nil ;; all constraints should be cached
                    :use (:functional-instance all-generic-predp-of-mv-nth-1-of-split-list-fast-aux
                                               (generic-predp ,element-pred)
                                               (all-generic-predp ,list-pred)))))

         (defthm ,list-pred-of-mv-nth-1-of-split-list-fast-theorem-name
           (implies (,list-pred lst)
                    (,list-pred (mv-nth 1 (split-list-fast lst))))
           :hints (("Goal" :in-theory nil ;; all constraints should be cached
                    :use (:functional-instance all-generic-predp-of-mv-nth-1-of-split-list-fast
                                               (generic-predp ,element-pred)
                                               (all-generic-predp ,list-pred)))))

         (defthm ,list-pred-of-merge-theorem-name
           (implies (and (,list-pred l1)
                         (,list-pred l2)
                         (,list-pred acc))
                    (,list-pred (,merge-name l1 l2 acc)))
           :hints (("Goal" :in-theory '(,merge-name) ;; all constraints should be cached
                    :use (:functional-instance all-generic-predp-of-merge-generic
                                               (generic-predp ,element-pred)
                                               (all-generic-predp ,list-pred)
                                               (generic-comparison ,comparison-fn)
                                               (merge-generic ,merge-name)))))

         (defthm ,true-listp-of-merge-theorem-name
           (implies (and (true-listp l1)
                         (true-listp l2))
                    (true-listp (,merge-name l1 l2 acc)))
           :hints (("Goal" :in-theory nil ;; all constraints should be cached
                    :use (:functional-instance true-listp-of-merge-generic
                                               (generic-comparison ,comparison-fn)
                                               (merge-generic ,merge-name)))))

         (defthm ,true-listp-of-merge-sort-theorem-name
           (implies (true-listp lst)
                    (true-listp (,merge-sort-name lst)))
           :hints (("Goal" :in-theory '(,merge-sort-name) ;; all other constraints should be cached
                    :use (:functional-instance true-listp-of-merge-sort-generic
                                               (generic-comparison ,comparison-fn)
                                               (merge-generic ,merge-name)
                                               (merge-sort-generic ,merge-sort-name)))))

         (defthm ,list-pred-of-merge-sort-theorem-name
           (implies (,list-pred lst)
                    (,list-pred (,merge-sort-name lst)))
           :hints (("Goal" :in-theory nil ;; all constraints should be cached
                    :use (:functional-instance all-generic-predp-of-merge-sort-generic
                                               (generic-predp ,element-pred)
                                               (all-generic-predp ,list-pred)
                                               (generic-comparison ,comparison-fn)
                                               (merge-generic ,merge-name)
                                               (merge-sort-generic ,merge-sort-name)))))

         ,@(and verify-guards `((verify-guards ,merge-sort-name
                                  :hints (("Goal"
                                           :use ((:instance true-listp-of-mv-nth-0-of-split-list-fast (lst l))
                                                 (:instance true-listp-of-mv-nth-1-of-split-list-fast (lst l))
                                                 (:instance ,list-pred-of-mv-nth-0-of-split-list-fast-theorem-name (lst l))
                                                 (:instance ,list-pred-of-mv-nth-1-of-split-list-fast-theorem-name (lst l))
                                                 (:instance ,list-pred-of-merge-sort-theorem-name (lst (mv-nth 0 (split-list-fast l))))
                                                 (:instance ,list-pred-of-merge-sort-theorem-name (lst (mv-nth 1 (split-list-fast l)))))
                                           :in-theory nil)))))

         ,@(and extra-theorems
                `((local (include-book "kestrel/lists-light/perm" :dir :system))

                  ;; proved elsewhere but needed to make PERM the equiv of the rules below:
                  (defequiv perm :package :equiv) ; the :package argument prevents errors if defmergesort is done in a package other than ACL2

                  (defthm ,(pack$ 'perm-of- merge-name)
                    (perm (,merge-name x y acc)
                          (append x y acc))
                    :hints (("Goal" :in-theory nil ;; all constraints should be cached
                             :use (:functional-instance perm-of-merge-generic
                                                        (generic-comparison ,comparison-fn)
                                                        (merge-generic ,merge-name)))))

                  (defthm ,(pack$ 'perm-of- merge-sort-name)
                    (perm (,merge-sort-name x)
                          x)
                    :hints (("Goal" :in-theory nil ;; all constraints should be cached
                             :use (:functional-instance perm-of-merge-sort-generic
                                                        (generic-predp ,element-pred)
                                                        (all-generic-predp ,list-pred)
                                                        (generic-comparison ,comparison-fn)
                                                        (merge-generic ,merge-name)
                                                        (merge-sort-generic ,merge-sort-name)))))))))))

;; todo: allow more options
;; todo: should list-pred imply true-listp (maybe not?)
;; todo: should be comparison be strict like < or weak like <=
(defmacro defmergesort (merge-sort-name ;the name to use for the "merge sort" function
                        merge-name ;the name to use for the "merge" function
                        comparison ;the comparison function (e.g., <) (todo: allow this to take extra args?)
                        element-pred ;the name of a predicate recognizing the items to sort
                        ;; list-pred ;a predicate asserting that all elements of a list satisfy element-pred
                        &key
                        (verify-guards 't)
                        (extra-theorems 't) ;whether to generate theorems that mention non-built-in functions, like perm
                        )
  (defmergesort-fn merge-sort-name merge-name comparison element-pred verify-guards extra-theorems))
