; A tool to try to order the vars in an R1CS
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "R1CS")

(include-book "../sparse/r1cs")
(include-book "kestrel/lists-light/reverse-list" :dir :system)
(local (include-book "kestrel/lists-light/union-equal" :dir :system))
(local (include-book "kestrel/lists-light/last" :dir :system))
(local (include-book "kestrel/alists-light/pairlis-dollar" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp2" :dir :system))

(local (in-theory (disable symbol-listp))) ;move

(local (in-theory (disable mv-nth)))

(local (in-theory (enable ACL2::SYMBOLP-OF-CAR-WHEN-SYMBOL-LISTP)))

;; A tool to order the variables in an R1CS

(local
 (defthm all->=-len-of-2-when-sparse-vectorp
   (implies (sparse-vectorp vec)
            (acl2::all->=-len vec 2))
   :hints (("Goal" :in-theory (enable sparse-vectorp
                                      acl2::all->=-len)))))

(defund r1cs-sparse-vector-vars (vec)
  (declare (xargs :guard (sparse-vectorp vec)))
  (remove '1 (acl2::strip-cadrs vec)))

(defthm symbol-listp-of-r1cs-sparse-vector-vars
  (implies (sparse-vectorp vec)
           (symbol-listp (r1cs-sparse-vector-vars vec)))
  :hints (("Goal" :in-theory (enable r1cs-sparse-vector-vars))))

(defund r1cs-constraint-vars (constraint)
  (declare (xargs :guard (r1cs-constraintp constraint)))
  (let ((a (r1cs-constraint->a constraint))
        (b (r1cs-constraint->b constraint))
        (c (r1cs-constraint->c constraint)))
    (union-eq (r1cs-sparse-vector-vars a)
              (r1cs-sparse-vector-vars b)
              (r1cs-sparse-vector-vars c))))

(defthm symbol-listp-of-r1cs-constraint-vars
  (implies (r1cs-constraintp constraint)
           (symbol-listp (r1cs-constraint-vars constraint)))
  :hints (("Goal" :in-theory (enable r1cs-constraint-vars))))


;; a list whose elements are vars or lists of vars (representing sets of vars constrained together, such as bits of a bvcat)
(defund done-varsp (done-vars)
  (declare (xargs :guard t))
  (if (atom done-vars)
      (null done-vars)
    (let ((item (first done-vars)))
      (and (or (symbolp item)
               (symbol-listp item))
           (done-varsp (rest done-vars))))))

(defthm done-varsp-of-singleton
  (equal (done-varsp (list x))
         (or (symbolp x)
             (symbol-listp x)))
  :hints (("Goal" :in-theory (enable done-varsp))))

(local
 (defthm true-listp-when-done-varsp
   (implies (done-varsp x)
            (true-listp x))
   :hints (("Goal" :in-theory (enable done-varsp)))))

(local
 (defthm done-varsp-when-symbol-listp
   (implies (symbol-listp x)
            (done-varsp x))
   :hints (("Goal" :in-theory (enable done-varsp)))))

(defund in-done-varsp (var done-vars)
  (declare (xargs :guard (and (symbolp var)
                              (done-varsp done-vars))
                  :guard-hints (("Goal" :in-theory (enable done-varsp)))))
  (if (endp done-vars)
      nil
    (let ((item (first done-vars)))
      (or (if (symbolp item)
              (eq var item)
            (member-eq var item))
          (in-done-varsp var (rest done-vars))))))

;; Returns (mv new-vars old-vars)
(defund partition-vars (vars done-vars new-vars-acc old-vars-acc)
  (declare (xargs :guard (and (symbol-listp vars)
                              (done-varsp done-vars))))
  (if (endp vars)
      (mv new-vars-acc old-vars-acc)
    (let ((var (first vars)))
      (if (in-done-varsp var done-vars) ;may be slow, could optimize using a property list world
          (partition-vars (rest vars) done-vars new-vars-acc (cons var old-vars-acc))
        (partition-vars (rest vars) done-vars (cons var new-vars-acc) old-vars-acc)))))

(defthm symbol-listp-of-mv-nth-0-of-partition-vars
  (implies (and (symbol-listp vars)
                (symbol-listp new-vars-acc))
           (symbol-listp (mv-nth 0 (partition-vars vars done-vars new-vars-acc old-vars-acc))))
  :hints (("Goal" :in-theory (enable partition-vars))))

(defthm true-listp-of-mv-nth-0-of-partition-vars
  (implies (true-listp new-vars-acc)
           (true-listp (mv-nth 0 (partition-vars vars done-vars new-vars-acc old-vars-acc))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable partition-vars))))

(defthm symbol-listp-of-mv-nth-1-of-partition-vars
  (implies (and (symbol-listp vars)
                (symbol-listp old-vars-acc))
           (symbol-listp (mv-nth 1 (partition-vars vars done-vars new-vars-acc old-vars-acc))))
  :hints (("Goal" :in-theory (enable partition-vars))))

(defun coeffs-doublingp (vars first-coeff flipped-vec p)
  (declare (xargs :guard (and (symbol-listp vars)
                              (alistp flipped-vec)
                              ;; no, because of the 1: (symbol-alistp flipped-vec)
                              (rtl::primep p)
                              (< 2 p)
                              (fep first-coeff p))))
  (if (endp vars)
      t
    (let* ((var (first vars))
           (coeff (lookup-equal var flipped-vec)))
      (and (integerp coeff)
           (equal (mod coeff p) first-coeff)
           (coeffs-doublingp (rest vars)
                             (mul 2 first-coeff p)
                             flipped-vec
                             p)))))

;; todo: allow the order to differ?
(defund vars-are-concatenated-in-sparse-vectorp (vars vec p)
  (declare (xargs :guard (and (symbol-listp vars)
                              (sparse-vectorp vec)
                              (rtl::primep p)
                              (< 2 p))))
  (let* ((coeffs (strip-cars vec))
         (pseudo-vars (acl2::strip-cadrs vec))
         (flipped-vec (pairlis$ pseudo-vars coeffs)) ;reflection of the vec, so we can look up the coeffs of vars
         (first-var-coeff (lookup-eq (first vars) flipped-vec)))
    (and (integerp first-var-coeff)
         (coeffs-doublingp vars (mod first-var-coeff p) flipped-vec p))))

;todo: consider also bitp constraints of the form (x+y+z)*(x+y+z-1)=0
(defund vars-are-concatenated-in-constraintp (new-vars constraint p)
  (declare (xargs :guard (and (symbol-listp new-vars)
                              (r1cs-constraintp constraint)
                              (rtl::primep p)
                              (< 2 p))))
  (let* ((a (r1cs-constraint->a constraint))
         (b (r1cs-constraint->b constraint))
         (c (r1cs-constraint->c constraint))
         (a-vars (r1cs-sparse-vector-vars a))
         (b-vars (r1cs-sparse-vector-vars b))
         (c-vars (r1cs-sparse-vector-vars c))
         )
    (and
     ;; ;; all the vars appear in a single constraint:
     ;; (or (and (not (intersection-eq new-vars a-vars)) (not (intersection-eq new-vars b-vars))) ; new-vars only in c
     ;;     (and (not (intersection-eq new-vars a-vars)) (not (intersection-eq new-vars c-vars))) ; new-vars only in b
     ;;     (and (not (intersection-eq new-vars b-vars)) (not (intersection-eq new-vars c-vars))) ; new-vars inly in a
     ;;     )
     ;; For each sparse vector if it mentions any of the vars, it mentions the concatenation of all of them (we assume vars don't occur more than once in a constraint):
     (if (intersection-eq new-vars a-vars)
         (vars-are-concatenated-in-sparse-vectorp new-vars a p)
       t)
     (if (intersection-eq new-vars b-vars)
         (vars-are-concatenated-in-sparse-vectorp new-vars b p)
       t)
     (if (intersection-eq new-vars c-vars)
         (vars-are-concatenated-in-sparse-vectorp new-vars c p)
       t))))

;; Returns (mv successp new-done-vars tagged-constraint) where if successp is nil, the other vals are meaningless.
(defund order-vars-in-r1cs-constraint (constraint done-vars p)
  (declare (xargs :guard (and (r1cs-constraintp constraint)
                              (done-varsp done-vars)
                              (rtl::primep p)
                              (< 2 p))))
  (b* ((vars (r1cs-constraint-vars constraint))
       (num-vars (len vars))
       ((mv new-vars old-vars) (partition-vars vars done-vars nil nil))
       (num-new-vars (len new-vars))
       ;;(num-old-vars (len old-vars))
       )
    (if (not vars)
        (prog2$ (er hard? 'order-vars-in-r1cs-constraint "Constraint ~x0 has no vars." constraint)
                (mv nil done-vars nil))
      (if (not old-vars)
          ;; only new-vars:
          (if (= 1 num-vars)
              ;; only 1 var in the constraint and it's a new var (example: a bitp constraint)
              (mv t
                  done-vars ; todo: should we consider this var to be done? what if there are no constraints defining it?
                  `(:solo ,(first vars) ,constraint))
            ;; only new vars and there is more than one of them (not yet handled):
            (prog2$ (cw "(Note: Only new vars, and more than one of them (~x0), in constraint ~x1.)~%" new-vars constraint)
                    (mv nil done-vars nil)))
        (if (not new-vars)
            ;; only old vars:
            (if (= 1 num-vars)
                ;; only 1 var in the constraint and its an old var (example: a bitp constraint)
                (mv t
                    done-vars ; var is already done
                    `(:solo ,(first vars) ,constraint))
              ;; only old vars and there is more than one of them (not yet handled):
              (prog2$ (cw "(Note: Only old vars, and more than one of them (~x0), in constraint ~x1.)~%" old-vars constraint)
                      (mv nil done-vars nil)))
          ;; Constraint has both old and new vars:
          (if (= 1 num-new-vars)
              ;; usual case: a single new var, constrained wrt some old vars
              (mv t
                  (cons (first new-vars) done-vars) ; we know it's not already present
                  `(:constrains ,(first new-vars) ,constraint))
            ;; More than one new var:
            ;; This can happen if some of the vars are actually constrained elsewhere but we fail to recognize those
            ;; other constraints (so they are not truly new in this constraint).
            (if (or (vars-are-concatenated-in-constraintp new-vars constraint p)
                    (vars-are-concatenated-in-constraintp (acl2::reverse-list new-vars) constraint p))
                ;; the multiple vars are part of the same bvcat:
                (mv t
                    (cons new-vars ;; add the whole list (we know none are already present in done-vars)
                          done-vars)
                    `(:constrains-all ,new-vars ,constraint))
              (if t ;; todo: restrict this to something like the check above (but we saw a non-contiguous set of bits being concatenated - bit 32 was missing)
                  (prog2$ (cw "(Note: More than one new var (~x0) in constraint ~x1.  Doesn't match a pattern we know about, but we are assuming it's ok.)~%" new-vars constraint)
                          (mv t
                              (cons new-vars ;; add the whole list (we know none are already present)
                                    done-vars)
                              `(:constrains-all ,new-vars ,constraint)))
                (prog2$ (cw "(Note: More than one new var (~x0) in constraint ~x1.  Doesn't match a pattern we know about.)~%" new-vars constraint)
                        (mv nil done-vars nil) ;todo handle (may be all the bits of a cat or sum?)
                        )))))))))

(defthm done-varsp-of-mv-nth-1-of-order-vars-in-r1cs-constraint
  (implies (and (r1cs-constraintp constraint)
                (done-varsp done-vars))
           (done-varsp (mv-nth 1 (order-vars-in-r1cs-constraint constraint done-vars p))))
  :hints (("Goal" :in-theory (enable order-vars-in-r1cs-constraint done-varsp))))

;; Makes 1 pass through the constraints.
;; Returns (mv tagged-constraints unhandled-constraints done-vars).
;; done-vars are in reverse-order (inputs last)
(defund order-r1cs-vars-aux-aux (constraints done-vars tagged-constraints-acc unhandled-constraints-acc p)
  (declare (xargs :guard (and (r1cs-constraint-listp constraints)
                              (done-varsp done-vars)
                              (true-listp tagged-constraints-acc)
                              (r1cs-constraint-listp unhandled-constraints-acc)
                              (rtl::primep p)
                              (< 2 p))))
  (if (endp constraints)
      (mv tagged-constraints-acc unhandled-constraints-acc done-vars)
    (b* ((constraint (first constraints))
         ((mv successp new-done-vars tagged-constraint)
          (order-vars-in-r1cs-constraint constraint done-vars p)))
      (if successp
          (order-r1cs-vars-aux-aux (rest constraints)
                                   new-done-vars
                                   (cons tagged-constraint tagged-constraints-acc)
                                   unhandled-constraints-acc
                                   p)
        ;; Could not handle the constraint yet:
        (order-r1cs-vars-aux-aux (rest constraints)
                                 done-vars
                                 tagged-constraints-acc
                                 (cons constraint unhandled-constraints-acc)
                                 p)))))

(defthm true-listp-of-mv-nth-0-of-order-r1cs-vars-aux-aux
  (implies (and (r1cs-constraint-listp constraints)
                (done-varsp done-vars)
                (true-listp tagged-constraints-acc)
                (r1cs-constraint-listp unhandled-constraints-acc))
           (true-listp (mv-nth 0 (order-r1cs-vars-aux-aux constraints done-vars tagged-constraints-acc unhandled-constraints-acc p))))
  :hints (("Goal" :in-theory (enable order-r1cs-vars-aux-aux))))

(defthm r1cs-constraint-listp-of-mv-nth-1-of-order-r1cs-vars-aux-aux
  (implies (and (r1cs-constraint-listp constraints)
                (done-varsp done-vars)
                (true-listp tagged-constraints-acc)
                (r1cs-constraint-listp unhandled-constraints-acc))
           (r1cs-constraint-listp (mv-nth 1 (order-r1cs-vars-aux-aux constraints done-vars tagged-constraints-acc unhandled-constraints-acc p))))
  :hints (("Goal" :in-theory (enable order-r1cs-vars-aux-aux))))

(defthm done-varsp-of-mv-nth-2-of-order-r1cs-vars-aux-aux
  (implies (and (r1cs-constraint-listp constraints)
                (done-varsp done-vars)
                (true-listp tagged-constraints-acc)
                (r1cs-constraint-listp unhandled-constraints-acc))
           (done-varsp (mv-nth 2 (order-r1cs-vars-aux-aux constraints done-vars tagged-constraints-acc unhandled-constraints-acc p))))
  :hints (("Goal" :in-theory (enable order-r1cs-vars-aux-aux))))

;; Returns (mv tagged-constraints done-vars).
;; TODO: Idea: Consider first handling all "obvious" constraints (e.g., defining single new var, or a concatenation of several new vars, in terms of old vars).  Then, when nothing more can be done, allow less obvious constraints (a bunch of new vars constrained in terms of old vars).  Then go back to obvious ones again.
(defund order-r1cs-vars-aux (constraints done-vars tagged-constraints-acc p)
  (declare (xargs :guard (and (r1cs-constraint-listp constraints)
                              (done-varsp done-vars)
                              (true-listp tagged-constraints-acc)
                              (rtl::primep p)
                              (< 2 p))
                  :measure (nfix (len constraints))))
  (b* (((mv tagged-constraints-acc unhandled-constraints done-vars)
        (order-r1cs-vars-aux-aux constraints done-vars tagged-constraints-acc nil p)))
    (if (not unhandled-constraints)
        ;; Every constraint was handled:
        (mv tagged-constraints-acc
            (reverse done-vars) ; put vars in correct order
            )
      (if (< (len unhandled-constraints) (len constraints))
          ;; Progress was made, so make another pass:
          (prog2$ (cw "~x0 constraints left after this pass.~%" (len unhandled-constraints))
                  (order-r1cs-vars-aux unhandled-constraints done-vars tagged-constraints-acc p))
        ;; This pass made no progress:
        (prog2$ (er hard? 'order-r1cs-vars-aux "Unhandled constraints remain: ~X01." unhandled-constraints nil)
                (mv nil nil))))))

;; Returns (mv tagged-constraints done-vars).
(defund order-r1cs-vars (constraints input-vars p)
  (declare (xargs :guard (and (r1cs-constraint-listp constraints)
                              (symbol-listp input-vars)
                              (rtl::primep p)
                              (< 2 p))))
  (let ((done-vars (list input-vars))) ; start with inputs as a single element of the done-vars, since there's no ordering between them
    (order-r1cs-vars-aux constraints done-vars nil p)))
