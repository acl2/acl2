; Correctness proof of the optimization
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "unify-term-and-dag")
(include-book "unify-term-and-dag-fast")

(defthm-flag-unify-term-and-dag
  (defthmd unify-term-and-dag-item-fast-correct-helper
    (implies (and (symbol-alistp alist)
                  (pseudo-termp term))
             (equal (unify-term-and-dag term darg dag-array dag-len alist)
                    (if (term-skeleton-matches-dagp term darg dag-array)
                        (unify-term-and-dag-when-skeleton-correct term darg dag-array dag-len alist)
                      :fail)))
    :flag unify-term-and-dag)
  (defthmd unify-terms-and-dag-items-fast-correct-helper
    (implies (and (symbol-alistp alist)
                  (pseudo-term-listp terms))
             (equal (unify-terms-and-dag terms dargs dag-array dag-len alist)
                    (if (term-skeletons-match-dagp terms dargs dag-array)
                        (unify-terms-and-dag-when-skeleton-correct terms dargs dag-array dag-len alist)
                      :fail)))
    :flag unify-terms-and-dag)
  :hints (("Goal" :in-theory (enable unify-term-and-dag
                                     unify-terms-and-dag
                                     term-skeleton-matches-dagp
                                     term-skeletons-match-dagp
                                     unify-term-and-dag-when-skeleton-correct
                                     unify-terms-and-dag-when-skeleton-correct))))

(defthmd unify-term-and-dag-item-fast-correct
  (implies (pseudo-termp term)
           (equal (unify-term-and-dag-item-fast term darg dag-array dag-len)
                  (unify-term-and-dag           term darg dag-array dag-len nil)))
  :hints (("Goal" :in-theory (enable unify-term-and-dag-item-fast
                                     unify-term-and-dag-item-fast-correct-helper))))

(defthm unify-terms-and-dag-items-fast-correct
  (implies (pseudo-term-listp terms)
           (equal (unify-terms-and-dag-items-fast terms dargs dag-array dag-len)
                  (unify-terms-and-dag            terms dargs dag-array dag-len nil)))
  :hints (("Goal" :in-theory (enable unify-terms-and-dag-items-fast
                                     unify-terms-and-dag-items-fast-correct-helper))))
