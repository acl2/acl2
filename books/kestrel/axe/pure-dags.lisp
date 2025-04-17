; Check whether a DAG has only supported expressions
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
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/cdr" :dir :system))

(local (in-theory (disable dag-function-call-exprp-redef)))

;; Check that, if ARG is a constant, it is a boolean constant.
(defund boolean-arg-okp (arg)
  (declare (xargs :guard (dargp arg)))
  (if (consp arg) ;check for quotep
      (if (booleanp (unquote arg))
          t
        (prog2$ (cw "Warning: Non-boolean constant ~x0 detected in a boolean context.~%" arg)
                nil))
    ;; it's a nodenum, so no checking is needed here (we will cut at that node if needed):
    t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; todo: consider adding a size param
;; check that, if it is a constant, then it is a bv constant
(defund bv-arg-okp (arg)
  (declare (xargs :guard (dargp arg)))
  (if (consp arg) ; checks for quotep
      (if (natp (unquote arg))
          t
        (prog2$ (cw "Warning: Non-BV constant ~x0 detected in BV context.~%" arg)
                nil))
    ;; it's a nodenum, so no checking is needed here (we will cut at that node if needed):
    t))

(defthm bv-arg-okp-forward
  (implies (and (bv-arg-okp arg)
                (consp arg))
           (natp (unquote arg)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable bv-arg-okp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; todo: consisder checking the size of the elements
(defund bv-array-arg-okp (len arg)
  (declare (xargs :guard (and (integerp len)
                              (<= 2 len) ; an array of length 1 would have no index bits
                              (dargp arg))))
  (if (consp arg) ; checks for quotep
      (let ((data (unquote arg)))
        (if (and (nat-listp data)
                 (= len (len data)))
            t
          (prog2$ (cw "Warning: Non-bv-array constant ~x0 detected in bv-array context.~%" arg)
                  nil)))
    ;; it's a nodenum, so no checking is needed here (we will cut at that node if needed):
    t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This checks the args if they are constants but does not look up nodenums.
;; This no longer allows ':irrelevant values in bvifs.
;; Note that we no longer translate IF or MYIF.
;; todo: consider adding unsigned-byte-p
;; todo: compare to can-always-translate-expr-to-stp and get-induced-type and translate-dag-expr
(defund pure-fn-call-exprp (expr)
  (declare (xargs :guard (dag-function-call-exprp expr)
                  :guard-hints (("Goal" :in-theory (enable consp-of-cdr)))))
  (let ((fn (ffn-symb expr))
        (dargs (dargs expr)))
    ;;(member-eq fn *bv-and-array-fns-we-can-translate*)
    ;;maybe we should check that operands are of the right type, but that would require passing in the dag-array
    (case fn
      (not (and (= 1 (len dargs))
                (boolean-arg-okp (first dargs))))
      ((booland boolor) (and (= 2 (len dargs))
                             (boolean-arg-okp (first dargs))
                             (boolean-arg-okp (second dargs))))
      (boolif (and (= 3 (len dargs))
                   (boolean-arg-okp (first dargs))
                   (boolean-arg-okp (second dargs))
                   (boolean-arg-okp (third dargs))))
      (bitnot (and (= 1 (len dargs))
                   (bv-arg-okp (first dargs))))
      ((bitand bitor bitxor) (and (= 2 (len dargs))
                                  (bv-arg-okp (first dargs))
                                  (bv-arg-okp (second dargs))))
      ((bvchop bvnot bvuminus) (and (= 2 (len dargs))
                                    (darg-quoted-posp (first dargs))
                                    (bv-arg-okp (second dargs))))
      (getbit (and (= 2 (len dargs))
                   (darg-quoted-natp (first dargs))
                   (bv-arg-okp (second dargs))))
      (slice (and (= 3 (len dargs))
                  (darg-quoted-natp (first dargs))
                  (darg-quoted-natp (second dargs))
                  (<= (unquote (second dargs))
                      (unquote (first dargs)))
                  (bv-arg-okp (third dargs))))
      ((bvequal
         bvand bvor bvxor
         bvplus bvminus bvmult
         bvdiv bvmod
         sbvdiv sbvrem
         bvlt bvle
         sbvlt sbvle)
       (and (= 3 (len dargs))
            (darg-quoted-posp (first dargs))
            (bv-arg-okp (second dargs))
            (bv-arg-okp (third dargs))))
      (bvcat (and (= 4 (len dargs))
                  (darg-quoted-posp (first dargs))
                  (bv-arg-okp (second dargs))
                  (darg-quoted-posp (third dargs))
                  (bv-arg-okp (fourth dargs))))
      (bvsx (and (= 3 (len dargs))
                 (darg-quoted-posp (first dargs))
                 (darg-quoted-posp (second dargs))
                 (<= (unquote (second dargs))
                     (unquote (first dargs)))
                 (bv-arg-okp (third dargs))))
      (bvif (and (= 4 (len dargs))
                 (darg-quoted-posp (first dargs))
                 (boolean-arg-okp (second dargs))
                 (bv-arg-okp (third dargs))
                 (bv-arg-okp (fourth dargs))))
      (leftrotate32 (and (= 2 (len dargs))
                         (darg-quoted-natp (first dargs))
                         ;;(< (unquote (first dargs)) 32)
                         (bv-arg-okp (second dargs))))
      (bv-array-read (and (= 4 (len dargs))
                          (darg-quoted-posp (first dargs))
                          (darg-quoted-natp (second dargs))
                          (<= 2 (unquote (second dargs))) ;an array of length 1 would have 0 index bits..
                          (bv-arg-okp (third dargs))
                          (bv-array-arg-okp (unquote (second dargs)) (fourth dargs))))
      (bv-array-write (and (= 5 (len dargs))
                           (darg-quoted-posp (first dargs))
                           (darg-quoted-natp (second dargs))
                           (<= 2 (unquote (second dargs))) ;an array of length 1 would have 0 index bits..
                           (bv-arg-okp (third dargs))
                           (bv-arg-okp (fourth dargs))
                           (bv-array-arg-okp (unquote (second dargs)) (fifth dargs))))
      (bv-array-if (and (= 5 (len dargs)) ; (bv-array-if element-size len test array1 array2)
                        (darg-quoted-posp (first dargs)) ; excludes element size 0
                        (darg-quoted-natp (second dargs)) ; could use darg-quoted-integerp, here and elsewhere, if that existed.
                        (<= 2 (unquote (second dargs))) ;an array of length 1 would have 0 index bits..
                        (boolean-arg-okp (third dargs))
                        (bv-array-arg-okp (unquote (second dargs)) (fourth dargs))
                        (bv-array-arg-okp (unquote (second dargs)) (fifth dargs))))
      ;; todo: consider how to handle equal:
      ((equal) t) ;fixme check the things being equated? or maybe they get checked elsewhere
      (otherwise nil))))

(defund expr-is-purep (expr)
  (declare (xargs :guard (dag-exprp expr)))
  (or (variablep expr) ;check more?
      (fquotep expr)   ;check more?
      (pure-fn-call-exprp expr)))

;; This could stop as soon as it finds a non-pure node, but if printp is
;; non-nil, it continues so that more "Non-pure expression" printing can occur.
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
            nil ; stop immediately
          ;; print a message and check the rest of the dag:
          (prog2$ (cw "Note: Node ~x0 is not pure: ~x1.~%" (car entry) expr) ; todo: don't print this more than once for each kind of thing.
                  (if (eq print :first)
                      nil
                    (dag-is-purep-aux (rest dag) print nil))))))))

;; Checks whether everything in the DAG is something we can translate to STP, except this
;; does not look up dargs that are nodenums to ensure they are the right type.
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; replaces nodenums with underscores
(defund darg-patterns (dargs)
  (declare (xargs :guard (darg-listp dargs)))
  (if (endp dargs)
      nil
    (let ((darg (first dargs)))
      (if (consp darg) ; checks for quotep
          (cons darg (darg-patterns (rest dargs)))
        (cons '_ (darg-patterns (rest dargs)))))))

(defund dag-expr-pattern (expr)
  (declare (xargs :guard (dag-exprp expr)))
  (if (or (variablep expr)
          (fquotep expr))
      expr ; rare
    ;; function call:
    (cons (ffn-symb expr)
          (darg-patterns (dargs expr)))))

;; Abstracts out the patterns, so we don't print lots of similar nodes (with
;; different nodenums).
(defund expression-patterns-in-dag-aux (dag acc)
  (declare (xargs :guard (and (weak-dagp-aux dag)
                              (true-listp acc))))
  (if (endp dag)
      (reverse acc) ; or we could skip this
    (let* ((entry (first dag))
           (expr (cdr entry)))
      (expression-patterns-in-dag-aux (rest dag)
                           (add-to-set-equal (dag-expr-pattern expr) acc)))))

;; todo: abstract out constants that are not sizes/bv indices (even abstract constant array indices)
;; todo: abstract vars and constants
(defund expression-patterns-in-dag (dag)
  (declare (xargs :guard (weak-dagp-aux dag)))
  (expression-patterns-in-dag-aux dag nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Abstracts out the patterns, so we don't print lots of similar non-pure nodes
;; (with different nodenums).
(defund non-pure-expression-patterns-in-dag-aux (dag acc)
  (declare (xargs :guard (and (weak-dagp-aux dag)
                              (true-listp acc))))
  (if (endp dag)
      (reverse acc) ; or we could skip this
    (let* ((entry (first dag))
           (expr (cdr entry)))
      (if (expr-is-purep expr)
          (non-pure-expression-patterns-in-dag-aux (rest dag) acc)
        (non-pure-expression-patterns-in-dag-aux (rest dag)
                                      (add-to-set-equal (dag-expr-pattern expr) acc))))))

(defund non-pure-expression-patterns-in-dag (dag)
  (declare (xargs :guard (weak-dagp-aux dag)))
  (non-pure-expression-patterns-in-dag-aux dag nil))
