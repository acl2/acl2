; Misc utilities
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "utilities")
(include-book "kestrel/lists-light/perm" :dir :system)

(defthm perm-of-2list-of-insert-when-not-in
  (implies (not (set::in item set))
           (perm (set::2list (set::insert item set))
                 (cons item (set::2list set))))
  :hints (("Goal" :expand ( ;(SET::INSERT ITEM SET)
                           (SET::2LIST (SET::INSERT ITEM SET))
                           )
           :in-theory (e/d ( ;(:induction set::insert)
                            )
                           ( ;PERM-OF-CONS PERM-OF-CONS-MEMBERP-CASE
;SET::USE-WEAK-INSERT-INDUCTION
                            )))))

(defthm perm-of-2list-of-insert
  (perm (set::2list (set::insert item set))
        (if (set::in item set)
            (set::2list set)
          (cons item (set::2list set))))
  :hints (("Goal" :expand ( ;(SET::INSERT ITEM SET)
                           (SET::2LIST (SET::INSERT ITEM SET))
                           )
           :in-theory (e/d ( ;(:induction set::insert)
                            )
                           ( ;PERM-OF-CONS PERM-OF-CONS-MEMBERP-CASE
;SET::USE-WEAK-INSERT-INDUCTION
                            )))))

;; (thm
;;  (perm (set::2list (set::insert item set))
;;             (if (set::in item set)
;;                 (set::2list set)
;;               (cons item (set::2list set)))))

(defthm 2list-of-delete
  (equal (set::2list (set::delete key set))
         (remove1 key (set::2list set))))

;move
(defthm unique-of-2list
  (no-duplicatesp-equal (set::2list x))
  )

;; ;move
;; ;gen the 1
;; (defthm count-of-2-list-bound
;;   (equal (< 1 (BAG::COUNT KEY (SET::2LIST x)))
;;          nil))
