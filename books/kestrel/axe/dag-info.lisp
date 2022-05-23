; Computing information and statistics about DAGs
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/alists-light/acons-unique" :dir :system)
(include-book "dag-size")
(include-book "kestrel/utilities/defmergesort" :dir :system)
(local (include-book "kestrel/alists-light/alistp" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/arithmetic-light/natp" :dir :system))
(local (include-book "kestrel/utilities/merge-sort-symbol-less-than" :dir :system))

(defun pair-with-rational-cdrp (x)
  (declare (xargs :guard t))
  (and (consp x) (rationalp (cdr x))))

(defun cdr-< (x y)
  (declare (xargs :guard (and (pair-with-rational-cdrp x)
                              (pair-with-rational-cdrp y))))
  (< (cdr x) (cdr y)))

;; For sorting an alist based on < comparison of the values (the cdrs of the pairs in the alist).
(defmergesort merge-cdr-< merge-sort-cdr-< cdr-< pair-with-rational-cdrp :verify-guards t)

(defthm alistp-of-merge-cdr-<
  (implies (and (alistp l1)
                (alistp l2)
                (alistp acc))
           (alistp (merge-cdr-< l1 l2 acc)))
  :hints (("Goal" :in-theory (enable merge-cdr-<))))

(defthm alistp-of-mv-nth-0-of-split-list-fast-aux
  (implies (and (alistp lst)
                (alistp tail)
                (alistp acc)
                (<= (len tail) (len lst)))
           (alistp (mv-nth 0 (split-list-fast-aux lst tail acc))))
  :hints (("Goal" :in-theory (enable split-list-fast-aux))))

(defthm alistp-of-mv-nth-1-of-split-list-fast-aux
  (implies (and (alistp lst)
                (alistp tail)
                (alistp acc)
                (<= (len tail) (len lst)))
           (alistp (mv-nth 1 (split-list-fast-aux lst tail acc))))
  :hints (("Goal" :in-theory (enable split-list-fast-aux))))

(defthm alistp-of-mv-nth-0-of-split-list-fast
  (implies (alistp alist)
           (alistp (mv-nth 0 (split-list-fast alist))))
  :hints (("Goal" :in-theory (enable split-list-fast))))

(defthm alistp-of-mv-nth-1-of-split-list-fast
  (implies (alistp alist)
           (alistp (mv-nth 1 (split-list-fast alist))))
  :hints (("Goal" :in-theory (enable split-list-fast))))

(defthm alistp-of-merge-sort-cdr-<
  (implies (alistp alist)
           (alistp (merge-sort-cdr-< alist)))
  :hints (("Goal" :in-theory (enable merge-sort-cdr-<))))

(defforall-simple pair-with-rational-cdrp)

(defthm rationalp-of-lookup-equal-when
  (implies (and (lookup-equal key alist)
                (all-pair-with-rational-cdrp alist))
           (rationalp (lookup-equal key alist)))
  :hints (("Goal" :in-theory (enable all-pair-with-rational-cdrp))))

;gen
(defthm nat-listp-of-strip-cdrs-of-acons-unique
  (implies (and (nat-listp (strip-cdrs alist))
                (natp val))
           (nat-listp (strip-cdrs (acons-unique key val alist))))
  :hints (("Goal" :in-theory (enable acons-unique strip-cdrs))))

(defthm all-pair-with-rational-cdrp-of-acons-unique
  (implies (and (all-pair-with-rational-cdrp alist)
                (rationalp val))
           (all-pair-with-rational-cdrp (acons-unique key val alist)))
  :hints (("Goal" :in-theory (enable acons-unique))))

;space-separated, on one line
(defun print-symbols (syms)
  (declare (xargs :guard (symbol-listp syms)))
  (if (endp syms)
      nil
    (b* ((sym (first syms))
         (- (cw "~x0 " sym)))
      (print-symbols (rest syms)))))

(defun print-symbols-4-per-line (syms)
  (declare (xargs :guard (symbol-listp syms)))
  (if (endp syms)
      nil
    (b* ((- (cw "  "))
         (- (print-symbols (firstn 4 syms)))
         (- (cw "~%"))) ;newline
      (print-symbols-4-per-line (nthcdr 4 syms)))))

(defun print-function-counts (alist)
  (declare (xargs :guard (alistp alist)))
  (if (endp alist)
      nil
    (b* ((entry (first alist))
         (fn (car entry))
         (count (cdr entry))
         (- (cw "  ~x0: ~t1~c2~%" fn 50 (cons count 10))))
      (print-function-counts (rest alist)))))

;res is an alist mapping functions in the dag to their occurrence counts
(defun tabulate-dag-fns-aux (dag alist)
  (declare (xargs :guard (and (weak-dagp-aux dag)
                              (alistp alist)
                              (nat-listp (strip-cdrs alist)))
                  :guard-hints (("Goal" :expand (WEAK-DAGP-AUX DAG)
                                 :in-theory (enable natp-of-+-of-1
                                                    )))))
  (if (endp dag)
      alist
    (let* ((entry (first dag))
           (expr (cdr entry)))
      (if (or (variablep expr)
              (fquotep expr))
          (tabulate-dag-fns-aux (cdr dag) alist)
        (let* ((fn (ffn-symb expr))
               (count (or (lookup-eq fn alist) 0))
               (new-count (+ 1 count))
               (alist (acons-unique fn new-count alist)))
          (tabulate-dag-fns-aux (cdr dag) alist))))))

(defthm true-listp-of-tabulate-dag-fns-aux
  (implies (true-listp alist)
           (true-listp (tabulate-dag-fns-aux dag alist))))

(defthm alistp-of-tabulate-dag-fns-aux
  (implies (alistp alist)
           (alistp (tabulate-dag-fns-aux dag alist))))

(defthm all-pair-with-rational-cdrp-of-tabulate-dag-fns-aux
  (implies (all-pair-with-rational-cdrp alist)
           (all-pair-with-rational-cdrp (tabulate-dag-fns-aux dag alist)))
  :hints (("Goal" :in-theory (enable tabulate-dag-fns-aux))))

(defun tabulate-dag-fns (dag)
  (declare (xargs :guard (weak-dagp dag)))
  (tabulate-dag-fns-aux dag nil))

(defun print-dag-info (dag name print-size)
  (declare (xargs :guard (and (pseudo-dagp dag)
                              (< (len dag) 2147483647)
                              (or (symbolp name)
                                  (null name))
                              (booleanp print-size))))
  (if (quotep dag) ; not possible, given the guard
      (b* ((- (if name
                  (cw "The entire DAG ~x0 is: ~x1.~%" name dag)
                (cw "The entire DAG is: ~x0.~%" dag))))
        nil)
    (b* ((- (if name
                (cw "(DAG info for ~x0:~%" name)
              (cw "(DAG info:~%")))
         (- (cw " Unique nodes: ~x0~%" (len dag)))
         ;; Can be slow:
         (- (and print-size
                 (cw " Total nodes: ~x0~%" (dag-size dag))))
         ;; These usually get inlined (we could count those):
         ;; (constants (dag-constants dag))
         ;; (- (cw "~x0 constants~%" (len constants)))
         (vars (merge-sort-symbol< (dag-vars dag)))
         (- (cw " ~x0 Variables:~%" (len vars)))
         (- (print-symbols-4-per-line vars))
         (fns (dag-fns dag))
         (- (cw " ~x0 Functions:~%" (len fns)))
         (- (print-symbols-4-per-line fns))
         (- (cw " Function counts:~%"))
         (fn-counts (merge-sort-cdr-< (tabulate-dag-fns dag)))
         (- (print-function-counts fn-counts))
         (- (cw ")~%")))
      nil)))

;; Print some statistics about a DAG:
;; TODO: print something about constant nodes, or constants that appear in nodes?
;; This calls dag-size, which uses arrays.
;; Returns the error triple (mv nil :invisible state).
(defun dag-info-fn (dag dag-form print-size state)
  (declare (xargs :guard (and (pseudo-dagp dag)
                              (< (len dag) 2147483647)
                              (booleanp print-size))
                  :stobjs state))
  (prog2$ (print-dag-info dag
                          (if (symbolp dag-form)
                              dag-form
                            nil ; don't try to print the name of the dag
                            )
                          print-size)
          (value :invisible)))

;; Prine info about the given DAG.  The DAG argument is evaluated.
(defmacro dag-info (dag &key (print-size 'nil))
  `(dag-info-fn ,dag ',dag ,print-size state))
