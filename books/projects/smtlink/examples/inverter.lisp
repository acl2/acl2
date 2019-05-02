;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (May 2019)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2

(in-package "SMT")
(include-book "util")

(defprod inverter
  ((input sig-path-p)
   (output sig-path-p)))

(define inverter-sigs ((i inverter-p))
  :returns (l sig-path-listp)
  (b* ((i (inverter-fix i))
       (input (inverter->input i))
       (output (inverter->output i)))
    (cons input (sig-path-list-fix (cons output (sig-path-list-fix nil))))))

(define inverter-count ((i inverter-p)
                        (curr any-table-p))
  :returns (markers maybe-integer-p)
  :guard-hints (("Goal" :in-theory (e/d (sigs-in-bool-table inverter-sigs))))
  (b* ((i (inverter-fix i))
       (curr (any-table-fix curr))
       ((unless (sigs-in-bool-table (inverter-sigs i) curr))
        (maybe-integer-fix nil))
       (in-sig (inverter->input i))
       (input (cdr (smt::magic-fix 'sig-path_booleanp
                                   (assoc-equal in-sig (any-table-fix curr)))))
       (out-sig (inverter->output i))
       (output (cdr (smt::magic-fix 'sig-path_booleanp
                                    (assoc-equal out-sig (any-table-fix curr))))))
    (maybe-integer-some (boolval (equal input output))))
  )

;; This definition allows stuttering
(define inverter-valid-step ((i inverter-p)
                             (prev any-table-p)
                             (next any-table-p))
  :returns (ok booleanp)
  :guard-hints (("Goal" :in-theory (e/d (sigs-in-bool-table inverter-sigs))))
  (b* ((i (inverter-fix i))
       (prev (any-table-fix prev))
       (next (any-table-fix next))
       ((unless (sigs-in-bool-table (inverter-sigs i) prev)) nil)
       ((unless (sigs-in-bool-table (inverter-sigs i) next)) nil)
       (input (inverter->input i))
       (output (inverter->output i))
       (in-prev (cdr (smt::magic-fix 'sig-path_booleanp
                                     (assoc-equal input (any-table-fix prev)))))
       (out-prev (cdr (smt::magic-fix 'sig-path_booleanp
                                      (assoc-equal output (any-table-fix prev)))))
       (in-next (cdr (smt::magic-fix 'sig-path_booleanp
                                     (assoc-equal input (any-table-fix next)))))
       (out-next (cdr (smt::magic-fix 'sig-path_booleanp
                                      (assoc-equal output (any-table-fix next))))))
    (cond
     ;; if in-prev != out-prev
     ;; and out-next != out-prev
     ((and (not (equal in-prev out-prev))
           (not (equal out-next out-prev)))
      nil)
     ;; if in-prev == out-prev
     ;; and in-prev != in-next
     ((and (equal in-prev out-prev)
           (not (equal in-prev in-next)))
      t)
     ;; all other cases are t
     (t t)))
  )

(define inverter-valid ((i inverter-p)
                        (tr any-trace-p))
  :returns (ok booleanp)
  :measure (len tr)
  (b* ((i (inverter-fix i))
       ((unless (consp (any-trace-fix (cdr (any-trace-fix tr))))) t)
       (first (car (any-trace-fix tr)))
       (rest (cdr (any-trace-fix tr)))
       (second (car (any-trace-fix rest)))
       ((unless (inverter-valid-step i first second)) nil))
    (inverter-valid i rest))
  )
