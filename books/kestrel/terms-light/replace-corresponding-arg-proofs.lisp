; Proofs about subst-var-alt
;
; Copyright (C) 2023-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "replace-corresponding-arg")
(include-book "lambdas-closed-in-termp")
(include-book "no-nils-in-termp")
(include-book "non-trivial-formals")
(include-book "kestrel/evaluators/empty-eval" :dir :system)

(defthm lambdas-closed-in-termsp-of-replace-corresponding-arg
  (implies (and (lambdas-closed-in-termsp args)
                (lambdas-closed-in-termp new-arg))
           (lambdas-closed-in-termsp (replace-corresponding-arg new-arg args formal formals)))
  :hints (("Goal" :in-theory (enable replace-corresponding-arg))))

(defthm no-nils-in-termsp-of-replace-corresponding-arg
  (implies (and (no-nils-in-termsp args)
                (no-nils-in-termp new-arg))
           (no-nils-in-termsp (replace-corresponding-arg new-arg args formal formals)))
  :hints (("Goal" :in-theory (enable replace-corresponding-arg))))

(defthm empty-eval-list-of-replace-corresponding-arg
  (equal (empty-eval-list (replace-corresponding-arg new-arg args formal formals) a)
         (replace-corresponding-arg (empty-eval new-arg a) (empty-eval-list args a) formal formals))
  :hints (("Goal" :in-theory (enable replace-corresponding-arg))))

(defthm len-of-non-trivial-formals-of-replace-corresponding-arg-linear
  (<= (len (non-trivial-formals formals (replace-corresponding-arg var args var formals)))
      (len (non-trivial-formals formals args)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable replace-corresponding-arg non-trivial-formals))))
