; Proofs about reconstruct-lets-in-term
;
; Copyright (C) 2021-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "reconstruct-lets-in-term")
(include-book "free-vars-in-term")
(include-book "kestrel/lists-light/perm-def" :dir :system)
(local (include-book "kestrel/lists-light/remove-duplicates-equal" :dir :system))
(local (include-book "kestrel/lists-light/perm" :dir :system))
(include-book "no-duplicate-lambda-formals-in-termp")

;; This proves that the free vars returned by the -aux function are correct:
(defthm-flag-reconstruct-lets-in-term-aux
  (defthm mv-nth-1-of-reconstruct-lets-in-term-aux-under-perm
    (implies (and (pseudo-termp term)
                  (no-duplicate-lambda-formals-in-termp term))
             (perm (mv-nth 1 (reconstruct-lets-in-term-aux term))
                   (free-vars-in-term term)))
    :flag reconstruct-lets-in-term-aux)
  (defthm mv-nth-1-of-reconstruct-lets-in-terms-aux-under-perm
    (implies (and (pseudo-term-listp terms)
                  (no-duplicate-lambda-formals-in-termsp terms))
             (perm (mv-nth 1 (reconstruct-lets-in-terms-aux terms))
                   (free-vars-in-terms terms)))
    :flag reconstruct-lets-in-terms-aux)
  :hints (("subgoal *1/3" :use (:instance free-vars-in-terms-when-symbol-listp (terms (cddr term))))
          ("subgoal *1/2" :use (:instance free-vars-in-terms-when-symbol-listp (terms (cddr term))))
          ("Goal" :expand ((free-vars-in-term term)
                           (free-vars-in-terms (cdr term)))
           :in-theory (enable reconstruct-lets-in-term-aux
                              reconstruct-lets-in-terms-aux
                              no-duplicate-lambda-formals-in-termp))))
