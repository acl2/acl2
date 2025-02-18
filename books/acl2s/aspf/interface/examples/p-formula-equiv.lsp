(in-package "ACL2")

(include-book "../top")
(include-book "../acl2s-utils/top")

(in-package "ACL2S")

;; Here's a data definition representing a simple propositional formula
(defdata p-formula
  (or bool
      var
      (list 'not p-formula)
      (list (enum '(and or implies)) p-formula p-formula)))

:q

(defpackage :simplifier (:use :cl))
(in-package :simplifier)
(import '(acl2s::p-formulap
          acl2s::nth-p-formula
          acl2s::boolp
          acl2s::varp
          acl2s::implies))
(import '(acl2s-interface::acl2s-query
          acl2s-interface::quiet-mode-on))

;; Here's an example of some arbitrary transformation on p-formulas
;; that we claim produces an equivalent p-formula
(defun simplify-nots (f)
  (assert (p-formulap f))
  (cond ((boolp f) f)
        ((varp f) f)
        ((eql (car f) 'not) ;; is (list 'not ?)
         (let ((simplified-arg (simplify-nots (second f))))
           (if (and (consp simplified-arg) (eql (car simplified-arg) 'not))
               (second simplified-arg)
             (list 'not simplified-arg))))
        (t (list (car f) (simplify-nots (second f)) (simplify-nots (third f))))))

;; Now, let's test it.
;; Turn on quiet mode to prevent a ton of extra output
(quiet-mode-on)
(print "Testing...")
;; Run 1000 tests.
(loop for n from 0 to 1000
      ;; first, use the enumerator from the defdata to generate a
      ;; random p-formula
      do (let* ((seed (random (1- (expt 2 31))))
                (f (nth-p-formula seed)))
           ;; The enumerator has a small chance of generating a
           ;; non-p-formula, so we check for that here.
           (if (not (p-formulap f))
               (format t "-")
             (let* ;; simplify the formula
                 ((simp-f (simplify-nots f))
                  ;; ask ACL2 to prove that they are equivalent
                  (res (acl2s-query `(thm (iff ,f ,simp-f)))))
               ;; If (car res) = t, then the proof failed.
               (if (car res)
                   (format t "simplify-nots returns a nonequivalent expression for f=~S~%" f)
                 ;; Otherwise, it succeeded so let's print a character to denote this.
                 (format t "."))))
           ;; Just so we see output while testing is running
           (when (eql (mod n 50) 49) (force-output))))
