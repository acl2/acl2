; Tests of my-make-flag
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "my-make-flag")
(include-book "kestrel/utilities/deftest" :dir :system)
(include-book "misc/install-not-normalized" :dir :system)

(deftest
  ;; The rule car-rewrite caused the proof attempted by make-flag to fail:
  (defund car2 (x) (car x))
  (defthm car-rewrite
    (equal (car x) (car2 x))
    :hints (("Goal" :in-theory (enable car2))))
  ;;fails:
  (must-fail (make-flag evens))
  ;;works:
  (my-make-flag evens))

(deftest
  ;; Test where clique members appear in their own termination theorem:
  (my-make-flag pseudo-termp))

;; Fails without the :ruler-extenders argument:
(deftest
  (install-not-normalized occur-cnt-bounded)
  (my-make-flag
       occur-cnt-bounded
       :flag-function-name flag-occur-cnt-bounded-for-copy-function
       :ruler-extenders :lambdas
       :body ((occur-cnt-bounded occur-cnt-bounded$not-normalized)
              (occur-cnt-bounded-lst occur-cnt-bounded-lst$not-normalized))))

(deftest
  ;; without the clause-processor, this took > 40 seconds:
  ;; The clause-processor doesn't prove the whole measure conjecture, because
  ;; ACL2's simplification makes it harder to prove.
  (my-make-flag tamep))

(deftest
  ;; In this call, the clause-processor finishes the whole proof of the measure conjecture:
  (my-make-flag pseudo-termp))
