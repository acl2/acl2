; Counting IF-branches
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "dags")
(include-book "kestrel/utilities/forms" :dir :system)
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund lookup-with-default (key alist default)
  (declare (xargs :guard (and (eqlablep key)
                              (alistp alist))))
  (let ((res (assoc key alist)))
    (if (not res)
        default
      (cdr res))))

(local
  (defthm natp-of-lookup-with-default-type
    (implies (and (nat-listp (strip-cdrs alist))
                  (natp default))
             (natp (lookup-with-default key alist default)))
    :rule-classes :type-prescription
    :hints (("Goal" :in-theory (enable lookup-with-default assoc-equal strip-cdrs)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund count-top-level-if-branches-in-rev-dag (rev-dag
                                                alist ; maps nodenums to the number of if-leaves they each represent
                                                )
  (declare (xargs :guard (and (weak-dagp rev-dag)
                              (alistp alist)
                              (nat-listp (strip-cdrs alist)))
                  :guard-hints (("Goal" :in-theory (enable consp-of-cdr-of-dargs-when-dag-exprp-iff
                                                           consp-of-dargs-when-dag-exprp-iff)))))
  (if (not (mbt (consp rev-dag)))
      (er hard? 'count-top-level-if-branches-in-rev-dag "Empty DAG.")
    (let* ((entry (first rev-dag))
           (expr (cdr entry))
           (leaf-count (if (and (call-of 'if expr)
                                (consp (cdr (cdr (dargs expr)))))
                           (let ((then (darg2 expr))
                                 (else (darg3 expr)))
                             ;; only counting leaves in the then and else branches, not the test:
                             (+ (if (consp then) ; check for quotep
                                    1
                                  (lookup-with-default then alist 1))
                                (if (consp else) ; check for quotep
                                    1
                                  (lookup-with-default else alist 1))))
                         1 ; level expr is not an IF
                         )))
      (if (endp (cdr rev-dag)) ; we've reached the top node
          leaf-count
        (count-top-level-if-branches-in-rev-dag (cdr rev-dag)
                                                (if (< 1 leaf-count)
                                                    ;; only store counts greater than 1:
                                                    (acons (car entry) leaf-count alist)
                                                  alist))))))

;; Does not look for MYIF or BVIF or anything like that, only IF.
;; TODO: Optimize by using a result array?
(defund count-top-level-if-branches-in-dag (dag)
  (declare (xargs :guard (pseudo-dagp dag)))
  (count-top-level-if-branches-in-rev-dag (reverse-list dag) nil))
