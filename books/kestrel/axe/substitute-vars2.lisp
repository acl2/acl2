; New tools for substituting equated vars in DAGS
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

(include-book "substitute-vars")
(local (include-book "kestrel/lists-light/len" :dir :system))

(local (in-theory (disable natp)))

;move
(defthm not-consp-of-mv-nth-3-of-find-var-and-expr-to-subst
  (implies (and (mv-nth 0 (find-var-and-expr-to-subst lhs rhs dag-array dag-len))
                (dargp-less-than lhs dag-len)
                (dargp-less-than rhs dag-len)
                )
           (not (consp (mv-nth 3 (find-var-and-expr-to-subst lhs rhs dag-array dag-len)))))
  :hints (("Goal" :in-theory (enable find-var-and-expr-to-subst NODENUM-OF-VAR-TO-SUBSTP))))

;move
(defthm natp-of-mv-nth-2-of-check-for-var-subst-literal
  (implies (and (natp literal-nodenum)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (< literal-nodenum dag-len)
                (mv-nth 0 (check-for-var-subst-literal literal-nodenum dag-array dag-len)))
           (natp (mv-nth 2 (check-for-var-subst-literal literal-nodenum dag-array dag-len))))
  :hints (("Goal" :in-theory (enable check-for-var-subst-literal))))

(defthm natp-of-mv-nth-3-of-check-for-var-subst-literal
  (implies (and (natp literal-nodenum)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (< literal-nodenum dag-len)
                (mv-nth 0 (check-for-var-subst-literal literal-nodenum dag-array dag-len)))
           (natp (mv-nth 3 (check-for-var-subst-literal literal-nodenum dag-array dag-len))))
  :hints (("Goal" :in-theory (enable check-for-var-subst-literal))))

;; a triple of the form (<nodenum-of-var> <equated-nodenum> <literal-nodenum).
(defun subst-candidatep (cand)
  (declare (xargs :guard t))
  (and (nat-listp cand)
       (equal 3 (len cand))))

(defun subst-candidate-listp (cands)
  (declare (xargs :guard t))
  (if (atom cands)
      (null cands)
    (and (subst-candidatep (first cands))
         (subst-candidate-listp (rest cands)))))

;; TODO: What if we have the equality of two vars?  Should we consider both?

;; Returns a subst-candidate-listp.  Looks through the literals for ones that
;; equate vars with other nodes.
(defund subst-candidates (literal-nodenums dag-array dag-len acc)
  (declare (xargs :guard (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (nat-listp literal-nodenums)
                              (all-< literal-nodenums dag-len))))
  (if (endp literal-nodenums)
      acc
    (b* ((literal-nodenum (first literal-nodenums))
         ((mv foundp
              & ;; var
              nodenum-of-var
              nodenum-or-quotep-to-put-in ;for now, this is always a quotep?
              )
          ;; todo: Use a version that doesn't check supporters!:
          (check-for-var-subst-literal literal-nodenum dag-array dag-len)))
      (subst-candidates (rest literal-nodenums)
                        dag-array
                        dag-len
                        (if foundp
                            (cons (list nodenum-of-var nodenum-or-quotep-to-put-in literal-nodenum)
                                  acc)
                          acc)))))

(defthm subst-candidate-listp-of-subst-candidates
  (implies (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (nat-listp literal-nodenums)
                (all-< literal-nodenums dag-len)
                (subst-candidate-listp acc))
           (subst-candidate-listp (subst-candidates literal-nodenums dag-array dag-len acc)))
  :hints (("Goal" :in-theory (e/d (subst-candidates)
                                  ()))))
