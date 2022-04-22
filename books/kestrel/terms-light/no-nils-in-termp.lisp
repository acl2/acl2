; Proof of correctness of expand-lambdas-in-term
;
; Copyright (C) 2021-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "free-vars-in-term")
(local (include-book "kestrel/lists-light/union-equal" :dir :system))

;; This is needed due to a deficiency in how defevaluator evaluates NIL, which
;; is syntactically a variable although not a legal one:

(mutual-recursion
 ;; Checks that NIL never appears as a variable in TERM, including in lambda
 ;; bodies.
 (defun no-nils-in-termp (term)
   (declare (xargs :guard (pseudo-termp term)))
   (if (variablep term)
       (not (equal term nil))
     (let ((fn (ffn-symb term)))
       (if (eq 'quote fn)
           t
         (and (no-nils-in-termsp (fargs term))
              (if (consp fn)
                  (no-nils-in-termp (lambda-body fn))
                t))))))
 (defun no-nils-in-termsp (terms)
   (declare (xargs :guard (pseudo-term-listp terms)))
   (if (endp terms)
       t
     (and (no-nils-in-termp (first terms))
          (no-nils-in-termsp (rest terms))))))

(defthm-flag-free-vars-in-term
  (defthm not-member-equal-of-nil-and-free-vars-in-term
    (implies (and (pseudo-termp term)
                  (no-nils-in-termp term))
             ;; This is weaker than (no-nils-in-termp term) because it doesn't
             ;; check lambda bodies:
             (not (member-equal nil (free-vars-in-term term))))
    :flag free-vars-in-term)
  (defthm not-member-equal-of-nil-and-free-vars-in-terms
    (implies (and (pseudo-term-listp terms)
                  (no-nils-in-termsp terms))
             (not (member-equal nil (free-vars-in-terms terms))))
    :flag free-vars-in-terms)
  :hints (("Goal" :expand ((FREE-VARS-IN-TERM TERM))
           :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (

                            free-vars-in-terms
                            )
                           ()))))

(defthm no-nils-in-termp-when-symbolp
  (implies (symbolp term)
           (equal (no-nils-in-termp term)
                  (not (equal term nil))))
  :hints (("Goal" :in-theory (enable no-nils-in-termp))))

(defthm no-nils-in-termsp-of-remove-equal
  (implies (no-nils-in-termsp terms)
           (no-nils-in-termsp (remove-equal term terms)))
  :hints (("Goal" :in-theory (enable no-nils-in-termsp
                                     remove-equal))))

(defthm no-nils-in-termsp-of-union-equal
  (equal (no-nils-in-termsp (union-equal terms1 terms2))
         (and (no-nils-in-termsp terms1)
              (no-nils-in-termsp terms2)))
  :hints (("Goal" :in-theory (enable no-nils-in-termsp
                                     union-equal))))

(defthm no-nils-in-termsp-of-intersection-equal
  (implies (or (no-nils-in-termsp terms1)
               (no-nils-in-termsp terms2))
           (no-nils-in-termsp (intersection-equal terms1 terms2)))
  :hints (("Goal" :in-theory (enable no-nils-in-termsp
                                     intersection-equal))))
