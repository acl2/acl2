; Check whether a DAG has only supported expressions
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2023 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "dags")
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/cdr" :dir :system))

;inline?
;check this - is it anything missing?
;fixme check in this that the sizes are not 0 -- and print a warning (or even halt?) if they are?
;does this function handle everything in *bv-and-array-fns-we-can-translate* ?
;the quotep checks on arguments could be consp checks?
;fixme compare to can-always-translate-expr-to-stp?
; should this allow ':irrelevant values in bvifs?
(defun pure-fn-call-exprp (expr)
  (declare (xargs :guard (dag-function-call-exprp expr)
                  :guard-hints (("Goal" :in-theory (enable consp-of-cdr)))))
  (let ((fn (ffn-symb expr)))
    ;;(member-eq fn *bv-and-array-fns-we-can-translate*)
    ;;maybe we should check that operands are of the right type?
    (case fn
          ;;((myif) t) ;check more? we no longer translate myif, only bvif?
          ((equal) t) ;fixme check the things being equated? or maybe they get checked elsewhere
          ((boolor booland boolif not bitnot bitxor bitor bitand) t)
          ((bv-array-write bv-array-read bvsx slice)
           (and (consp (rest (dargs expr)))
                (quotep (darg1 expr))
                (quotep (darg2 expr))))
          ((bvnot bvand bvor bvxor bvmult bvminus bvuminus bvplus bvdiv bvmod sbvdiv sbvrem bvchop ;$inline
                  getbit sbvlt bvlt bvle bvif leftrotate32)
           (and (consp (dargs expr))
                (quotep (darg1 expr)))) ;fixme make sure the value is okay?
          (bvcat (and (consp (rest (rest (dargs expr))))
                      (quotep (darg1 expr))
                      (quotep (darg3 expr))))
          (otherwise nil))))

(defund expr-is-purep (expr)
  (declare (xargs :guard (dag-exprp expr)))
  ;; (declare (xargs :guard t))
  (or (variablep expr) ;check more?
      (fquotep expr)   ;check more?
      (pure-fn-call-exprp expr)))

;; Checks whether everything in the DAG is something we can translate to STP
(defund dag-is-purep-aux (dag print pure-so-farp)
  (declare (xargs :guard (and (weak-dagp-aux dag)
                              (member-eq print '(nil :first :all)))))
  (if (endp dag)
      pure-so-farp
    (let* ((entry (first dag))
           (expr (cdr entry)))
      (if (expr-is-purep expr)
          (dag-is-purep-aux (rest dag) print pure-so-farp)
        ;; EXPR is not pure:
        (if (not print)
            nil
          (prog2$ (cw "Non-pure expression in DAG: ~x0.~%" expr)
                  (if (eq print :first)
                      nil
                    (dag-is-purep-aux (rest dag) print nil))))))))

;; Checks whether everything in the DAG is something we can translate to STP
(defund dag-is-purep (dag)
  (declare (xargs :guard (weak-dagp-aux dag)))
  (dag-is-purep-aux dag :first t))

;; ;; Checks whether everything in the DAG is something we can translate to STP
;; (defund dag-or-quotep-is-purep (dag-or-quotep)
;;   (declare (xargs :guard (or (quotep dag)
;;                              (weak-dagp-aux dag))))
;;   (if (quotep dag)
;;       t ;todo: check more?
;;     (dag-is-purep-aux dag :first t)))
