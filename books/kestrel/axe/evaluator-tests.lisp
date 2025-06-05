; Tests of the evaluator
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

(include-book "evaluator")
(include-book "std/testing/must-be-redundant" :dir :system)

(must-be-redundant
 (MUTUAL-RECURSION
  (defund apply-axe-evaluator (fn args interpreted-function-alist array-depth)
    (declare
     (xargs
      :measure 1
      :guard
      (and
       (or (symbolp fn) (pseudo-lambdap fn))
       (true-listp args)
       (interpreted-function-alistp interpreted-function-alist)
       (natp array-depth))))
    (if
     (consp fn)
     (let* ((formals (second fn))
            (body (third fn))
            (alist (pairlis$-fast formals args)))
           (eval-axe-evaluator
            alist body
            interpreted-function-alist array-depth))
     (let
      ((args-to-walk-down args))
      (mv-let
        (hit val)
        (if
         (endp args-to-walk-down)
         (mv nil nil)
         (let ((args-to-walk-down (cdr args-to-walk-down)))
                      (if
                       (endp args-to-walk-down)
                       (let ((arg1 (nth 0 args)))
                        (case fn
                          (quotep (mv t (quotep arg1)))
                          (natp (mv t (natp arg1)))
                          (posp (mv t (posp arg1)))
                          (integerp (mv t (integerp arg1)))
                          (rationalp (mv t (rationalp arg1)))
                          (print-constant (mv t (print-constant arg1)))
                          (not (mv t (not arg1)))
                          (power-of-2p (mv t (power-of-2p arg1)))
                          (lg (mv t (lg-unguarded arg1)))
                          (bool-to-bit (mv t (eval-in-logic (bool-to-bit arg1))))
                          (char-code (mv t (char-code-unguarded arg1)))
                          (code-char (mv t (code-char-unguarded arg1)))
                          (symbol-package-name
                               (mv t (symbol-package-name-unguarded arg1)))
                          (symbol-name (mv t (symbol-name-unguarded arg1)))
                          (all-same (mv t (all-same-unguarded arg1)))
                          (bool-fix$inline (mv t (bool-fix$inline arg1)))
                          (booleanp (mv t (booleanp arg1)))
                          (list::2set (mv t (list::2set arg1)))
                          (rkeys (mv t (rkeys arg1)))
                          (key-list (mv t (key-list arg1)))
                          (true-list-fix (mv t (true-list-fix arg1)))
                          (all-integerp (mv t (all-integerp arg1)))
                          (no-duplicatesp-equal
                               (mv t (no-duplicatesp-equal-unguarded arg1)))
                          (strip-cdrs (mv t (strip-cdrs-unguarded arg1)))
                          (strip-cars (mv t (strip-cars-unguarded arg1)))
                          (stringp (mv t (stringp arg1)))
                          (true-listp (mv t (true-listp arg1)))
                          (consp (mv t (consp arg1)))
                          (bytes-to-bits (mv t (eval-in-logic (bytes-to-bits arg1))))
                          (width-of-widest-int
                               (mv t (width-of-widest-int-unguarded arg1)))
                          (all-natp (mv t (all-natp arg1)))
                          (endp (mv t (endp-unguarded arg1)))
                          (bitnot (mv t (bitnot-unguarded arg1)))
                          (logmaskp (mv t (logmaskp arg1)))
                          (integer-length
                               (mv t (integer-length-unguarded arg1)))
                          (ceiling-of-lg
                               (mv t (ceiling-of-lg-unguarded arg1)))
                          (unary-/ (mv t (unary-/-unguarded arg1)))
                          (nfix (mv t (nfix arg1)))
                          (ifix (mv t (ifix arg1)))
                          (len (mv t (len arg1)))
                          (reverse-list (mv t (reverse-list-unguarded arg1)))
                          (acl2-numberp (mv t (acl2-numberp arg1)))
                          (zp (mv t (zp-unguarded arg1)))
                          (unary-- (mv t (unary---unguarded arg1)))
                          (atom (mv t (atom arg1)))
                          (car (mv t (car-unguarded arg1)))
                          (cdr (mv t (cdr-unguarded arg1)))
                          (map-reverse-list (mv t (map-reverse-list-unguarded arg1)))
                          (realpart (mv t (realpart-unguarded arg1)))
                          (imagpart (mv t (imagpart-unguarded arg1)))
                          (symbolp (mv t (symbolp arg1)))
                          (characterp (mv t (characterp arg1)))
                          (complex-rationalp (mv t (complex-rationalp arg1)))
                          (denominator (mv t (denominator-unguarded arg1)))
                          (numerator (mv t (numerator-unguarded arg1)))
                          (t (mv nil nil))))
                       (let ((args-to-walk-down (cdr args-to-walk-down)))
                        (if
                         (endp args-to-walk-down)
                         (let ((arg2 (nth 1 args))
                               (arg1 (nth 0 args)))
                          (case fn
                           (mv-nth (mv t (mv-nth-unguarded arg1 arg2)))
                           (items-have-len
                                (mv t (items-have-len-unguarded arg1 arg2)))
                           (all-all-unsigned-byte-p
                                (mv t (all-all-unsigned-byte-p arg1 arg2)))
                           (add-to-end (mv t (eval-in-logic (add-to-end arg1 arg2))))
                           (coerce (mv t (coerce-unguarded arg1 arg2)))
                           (< (mv t (<-unguarded arg1 arg2)))
                           (equal (mv t (equal arg1 arg2)))
                           (eql (mv t (equal arg1 arg2)))
                           (= (mv t (equal arg1 arg2)))
                           (list-equiv (mv t (list-equiv arg1 arg2)))
                           (prefixp (mv t (prefixp arg1 arg2)))
                           (lookup-equal (mv t (lookup-equal-unguarded arg1 arg2)))
                           (lookup (mv t (lookup-equal-unguarded arg1 arg2)))
                           (lookup-eq (mv t (lookup-equal-unguarded arg1 arg2)))
                           (bvnot (mv t (bvnot-unguarded arg1 arg2)))
                           (bvuminus (mv t (bvuminus-unguarded arg1 arg2)))
                           (assoc-equal
                                (mv t (assoc-equal-unguarded arg1 arg2)))
                           (unsigned-byte-p-forced
                                (mv t (unsigned-byte-p-forced arg1 arg2)))
                           (trim (mv t (trim-unguarded arg1 arg2)))
                           (binary-+ (mv t (binary-+-unguarded arg1 arg2)))
                           ;; (all-items-less-than (mv t (all-items-less-than arg1 arg2)))
                           (every-nth (mv t (every-nth-unguarded arg1 arg2)))
                           (intersection-equal
                                (mv t (intersection-equal-unguarded arg1 arg2)))
                           (all-equal$ (mv t (all-equal$-unguarded arg1 arg2)))
                           (repeatbit (mv t (repeatbit-unguarded arg1 arg2)))
                           (implies (mv t (implies arg1 arg2)))
                           (first-non-member
                                (mv t (first-non-member-unguarded arg1 arg2)))
                           (booland (mv t (booland arg1 arg2)))
                           (boolor (mv t (boolor arg1 arg2)))
                           (getbit-list (mv t (getbit-list-unguarded arg1 arg2)))
                           (set::union (mv t (eval-in-logic (set::union arg1 arg2))))
                           (leftrotate32
                                (mv t (leftrotate32-unguarded arg1 arg2)))
                           (set::insert (mv t (eval-in-logic (set::insert arg1 arg2))))
                           (floor (mv t (floor-unguarded arg1 arg2)))
                           (member-equal
                                (mv t (member-equal-unguarded arg1 arg2)))
                           (g (mv t (g arg1 arg2)))
                           (nthcdr (mv t (nthcdr-unguarded arg1 arg2)))
                           (take (mv t (take-unguarded arg1 arg2)))
                           (firstn (mv t (firstn-unguarded arg1 arg2)))
                           (binary-append
                                (mv t (binary-append-unguarded arg1 arg2)))
                           (signed-byte-p (mv t (signed-byte-p arg1 arg2)))
                           (unsigned-byte-p
                                (mv t (unsigned-byte-p arg1 arg2)))
                           (bvchop-list
                                (mv t (bvchop-list-unguarded arg1 arg2)))
                           (all-unsigned-byte-p
                                (mv t (all-unsigned-byte-p arg1 arg2)))
                           (all-signed-byte-p
                                (mv t (all-signed-byte-p arg1 arg2)))
                           (bitor (mv t (bitor-unguarded arg1 arg2)))
                           (bitand (mv t (bitand-unguarded arg1 arg2)))
                           (bitxor (mv t (bitxor-unguarded arg1 arg2)))
                           (expt (mv t (expt-unguarded arg1 arg2)))
                           (min (mv t (min-unguarded arg1 arg2)))
                           (max (mv t (max-unguarded arg1 arg2)))
                           (mod (mv t (mod-unguarded arg1 arg2)))
                           (getbit (mv t (getbit-unguarded arg1 arg2)))
                           (cons (mv t (cons arg1 arg2)))
                           (bvchop (mv t (bvchop-unguarded arg1 arg2)))
                           (logtail$inline
                                (mv t (logtail$inline-unguarded arg1 arg2)))
                           (logext (mv t (logext-unguarded arg1 arg2)))
                           (nth (mv t (nth-unguarded arg1 arg2)))
                           (binary-* (mv t (binary-*-unguarded arg1 arg2)))
                           (bvnot-list
                                (mv t (bvnot-list-unguarded arg1 arg2)))
                           (eq (mv t (equal arg1 arg2)))
                           (ceiling (mv t (ceiling-unguarded arg1 arg2)))
                           (group (mv t (eval-in-logic (group arg1 arg2))))
                           (group2 (mv t (eval-in-logic (group2 arg1 arg2))))
                           (set::in (mv t (eval-in-logic (set::in-unguarded arg1 arg2))))
                           (symbol< (mv t (symbol<-unguarded arg1 arg2)))
                           (t (mv nil nil))))
                         (let ((args-to-walk-down (cdr args-to-walk-down)))
                          (if
                           (endp args-to-walk-down)
                           (let ((arg3 (nth 2 args))
                                 (arg2 (nth 1 args))
                                 (arg1 (nth 0 args)))
                            (case fn
                             (repeat-tail
                                  (mv t (repeat-tail arg1 arg2 arg3)))
                             (negated-elems-listp (mv t
                                                      (negated-elems-listp-unguarded
                                                           arg1 arg2 arg3)))
                             (leftrotate (mv t (leftrotate-unguarded arg1 arg2 arg3)))
                             (acons (mv t (acons-unguarded arg1 arg2 arg3)))
                             (bvshr (mv t (bvshr-unguarded arg1 arg2 arg3)))
                             (bvashr (mv t (bvashr-unguarded arg1 arg2 arg3)))
                             (packbv (mv t (packbv-unguarded arg1 arg2 arg3)))
                             (unpackbv
                                 (mv t
                                     (eval-in-logic (unpackbv-less-guarded arg1 arg2 arg3))))
;;                             (bvplus-lst (mv t (bvplus-lst arg1 arg2 arg3)))
                             (bvequal
                                  (mv t (bvequal-unguarded arg1 arg2 arg3)))
                             (bvlt (mv t (bvlt-unguarded arg1 arg2 arg3)))
                             (bvle (mv t (bvle-unguarded arg1 arg2 arg3)))
                             (bvxor (mv t (bvxor-unguarded arg1 arg2 arg3)))
                             (bvor (mv t (bvor-unguarded arg1 arg2 arg3)))
                             (bvand (mv t (bvand-unguarded arg1 arg2 arg3)))
                             (bvmult
                                  (mv t (bvmult-unguarded arg1 arg2 arg3)))
                             (bvplus
                                  (mv t (bvplus-unguarded arg1 arg2 arg3)))
                             (bvminus
                                  (mv t (bvminus-unguarded arg1 arg2 arg3)))
                             (bvmod (mv t (bvmod-unguarded arg1 arg2 arg3)))
                             (bvdiv (mv t (bvdiv-unguarded arg1 arg2 arg3)))
                             (bvsx (mv t (bvsx-unguarded arg1 arg2 arg3)))
                             (sbvdiv (mv t (sbvdiv-unguarded arg1 arg2 arg3)))
                             (sbvdivdown (mv t (eval-in-logic (sbvdivdown arg1 arg2 arg3))))
                             (sbvrem (mv t (eval-in-logic (sbvrem arg1 arg2 arg3))))
                             (sbvmoddown (mv t (eval-in-logic (sbvmoddown arg1 arg2 arg3))))
                             (sbvlt
                                 (mv t (sbvlt-unguarded arg1 (ifix arg2) (ifix arg3))))
                             (sbvle (mv t (sbvle-unguarded arg1 arg2 arg3)))
                             (s (mv t (s arg1 arg2 arg3)))
                             (myif (mv t (myif arg1 arg2 arg3)))
                             (boolif (mv t (boolif arg1 arg2 arg3)))
                             (array-elem-2d
                               (mv t (eval-in-logic (array-elem-2d arg1 arg2 arg3))))
                             (bv-arrayp
                                  (mv t (bv-arrayp arg1 arg2 arg3)))
                             (update-nth (mv t (update-nth-unguarded arg1 arg2 arg3)))
                             (if (mv t (if arg1 arg2 arg3)))
                             (slice
                                  (mv t (slice-unguarded arg1 arg2 arg3)))
                             (bvshl (mv t (bvshl-unguarded arg1 arg2 arg3)))
                             ;; (keep-items-less-than (mv t (keep-items-less-than-unguarded arg1 arg2 arg3)))
                             (subrange (mv t
                                           (subrange-unguarded arg1
                                                               arg2
                                                               arg3)))
                             (bvxor-list
                                  (mv t
                                      (bvxor-list-unguarded arg1 arg2 arg3)))
                             (t (mv nil nil))))
                           (let ((args-to-walk-down (cdr args-to-walk-down)))
                            (if
                             (endp args-to-walk-down)
                             (let ((arg4 (nth 3 args))
                                   (arg3 (nth 2 args))
                                   (arg2 (nth 1 args))
                                   (arg1 (nth 0 args)))
                              (case fn
                               (dag-val-with-axe-evaluator
                                 (mv t
                                     (eval-in-logic (dag-val-with-axe-evaluator
                                          arg1 arg2 arg3 (+ 1 array-depth)))))
                               (apply-axe-evaluator
                                    (mv t
                                        (eval-in-logic (apply-axe-evaluator
                                             arg1 arg2 arg3 array-depth))))
                               (update-subrange
                                  (mv t
                                      (eval-in-logic (update-subrange arg1 arg2 arg3 arg4))))
                               (update-nth2
                                    (mv t (eval-in-logic (update-nth2 arg1 arg2 arg3 arg4))))
                               (bv-array-clear
                                 (mv t (eval-in-logic (bv-array-clear arg1 arg2 arg3 arg4))))
                               (bvcat
                                  (mv t
                                      (bvcat-unguarded arg1 arg2 arg3 arg4)))
                               (bv-array-read (mv t
                                                  (bv-array-read-unguarded
                                                       arg1 arg2 arg3 arg4)))
                               (bvif
                                 (mv t (bvif-unguarded arg1 arg2 arg3 arg4)))
                               (t (mv nil nil))))
                             (let
                               ((args-to-walk-down (cdr args-to-walk-down)))
                              (if
                               (endp args-to-walk-down)
                               (let ((arg5 (nth 4 args))
                                     (arg4 (nth 3 args))
                                     (arg3 (nth 2 args))
                                     (arg2 (nth 1 args))
                                     (arg1 (nth 0 args)))
                                (case fn
                                 (update-subrange2
                                      (mv t
                                          (eval-in-logic (update-subrange2
                                               arg1 arg2 arg3 arg4 arg5))))
                                 (bv-array-write
                                   (mv t
                                       (bv-array-write-unguarded (nfix arg1)
                                                                 (nfix arg2)
                                                                 (nfix arg3)
                                                                 arg4 arg5)))
                                 (bv-array-clear-range
                                      (mv t
                                          (eval-in-logic (bv-array-clear-range
                                               arg1 arg2 arg3 arg4 arg5))))
                                 (t (mv nil nil))))
                               (let
                                ((args-to-walk-down (cdr args-to-walk-down)))
                                (if (endp args-to-walk-down)
                                    (mv nil nil)
                                 (let ((args-to-walk-down
                                            (cdr args-to-walk-down)))
                                  (if (endp args-to-walk-down)
                                      (mv nil nil)
                                   (let ((args-to-walk-down
                                              (cdr args-to-walk-down)))
                                    (if
                                     (endp args-to-walk-down)
                                     (let ((arg8 (nth 7 args))
                                           (arg7 (nth 6 args))
                                           (arg6 (nth 5 args))
                                           (arg5 (nth 4 args))
                                           (arg4 (nth 3 args))
                                           (arg3 (nth 2 args))
                                           (arg2 (nth 1 args))
                                           (arg1 (nth 0 args)))
                                      (declare (ignore arg8))
                                      (case fn
                                       (eval-dag-with-axe-evaluator
                                        (mv
                                         t
                                         (eval-in-logic (eval-dag-with-axe-evaluator
                                           arg1 arg2 arg3
                                           arg4 arg5 arg6 arg7 array-depth))))
                                       (t (mv nil nil))))
                                     (mv nil nil))))))))))))))))))
        (if
         hit val
         (let
          ((match (assoc-eq fn interpreted-function-alist)))
          (if
           (not match)
           (er hard? 'apply-axe-evaluator "Unknown function: ~x0 applied to args ~x1.  Consider passing it as an interpreted function, or adding it to the list of built-ins for the evaluator ~x2.  (This error also occurs when a function appears with an incorrect number of arguments.)"
               fn args 'axe-evaluator)
           (let* ((fn-info (cdr match))
                  (formals (first fn-info))
                  (body (second fn-info))
                  (alist (pairlis$-fast formals args)))
                 (eval-axe-evaluator
                  alist body interpreted-function-alist
                  array-depth)))))))))
  (defund eval-axe-evaluator (alist form interpreted-function-alist array-depth)
    (declare (xargs :verify-guards nil
                    :guard (and (symbol-alistp alist)
                                (pseudo-termp form)
                                (interpreted-function-alistp interpreted-function-alist)
                                (natp array-depth))))
    (cond
     ((variablep form)
      (lookup-eq form alist))
     ((fquotep form) (unquote form))
     (t
      (let
       ((fn (ffn-symb form)))
       (if
        (and (or (eq fn 'if) (eq fn 'myif))
             (= 3 (len (fargs form))))
        (let*
         ((test-form (farg1 form))
          (test-result (eval-axe-evaluator
                        alist
                        test-form interpreted-function-alist
                        array-depth)))
         (eval-axe-evaluator
          alist
          (if test-result
              (farg2 form)
              (farg3 form))
          interpreted-function-alist array-depth))
        (let
         ((args
           (eval-list-axe-evaluator alist (fargs form)
                                    interpreted-function-alist
                                    array-depth)))
         (apply-axe-evaluator fn args interpreted-function-alist
                              array-depth)))))))
  (defund
    eval-list-axe-evaluator
    (alist form-lst
           interpreted-function-alist array-depth)
    (declare
     (xargs
      :verify-guards nil
      :measure (len form-lst)
      :guard
      (and
       (symbol-alistp alist)
       (pseudo-term-listp form-lst)
       (interpreted-function-alistp interpreted-function-alist)
       (natp array-depth))))
    (if
     (endp form-lst)
     nil
     (cons (eval-axe-evaluator
            alist (car form-lst)
            interpreted-function-alist array-depth)
           (eval-list-axe-evaluator alist (cdr form-lst)
                                    interpreted-function-alist
                                    array-depth))))
  (defund
    dag-val-with-axe-evaluator
    (dag alist
         interpreted-function-alist array-depth)
    (declare
     (xargs
      :measure 0
      :guard
      (and
       (or (myquotep dag)
           (and (pseudo-dagp dag)
                (< (len dag) *max-1d-array-length*)))
       (symbol-alistp alist)
       (interpreted-function-alistp interpreted-function-alist)
       (natp array-depth))))
    (if
     (quotep dag)
     (unquote dag)
     (let*
      ((top-nodenum (top-nodenum-of-dag dag))
       (dag-array-name (pack$ 'dag-array-
                              array-depth '-for-dag-val))
       (dag-array (make-into-array dag-array-name dag))
       (eval-array-name (pack$ 'eval-array-
                               array-depth '-for-dag-val))
       (eval-array
        (make-empty-array eval-array-name (+ 1 top-nodenum))))
      (car (aref1 eval-array-name
                  (eval-dag-with-axe-evaluator
                   (list top-nodenum)
                   dag-array-name dag-array
                   alist eval-array-name eval-array
                   interpreted-function-alist array-depth)
                  top-nodenum)))))
  (defund
    eval-dag-with-axe-evaluator
    (nodenum-worklist dag-array-name dag-array var-value-alist
                      eval-array-name eval-array
                      interpreted-function-alist array-depth)
    (declare
     (xargs
      :guard
      (and
       (nat-listp nodenum-worklist)
       (if (consp nodenum-worklist)
           (pseudo-dag-arrayp dag-array-name dag-array
                              (+ 1 (maxelem nodenum-worklist)))
           t)
       (symbol-alistp var-value-alist)
       (symbolp eval-array-name)
       (if (consp nodenum-worklist)
           (eval-arrayp eval-array-name eval-array
                        (+ 1 (maxelem nodenum-worklist)))
           t)
       (interpreted-function-alistp interpreted-function-alist)
       (natp array-depth))
      :verify-guards nil))
    (if
     (endp nodenum-worklist)
     eval-array
     (let*
      ((nodenum (first nodenum-worklist))
       (expr (aref1 dag-array-name dag-array nodenum)))
      (if
       (variablep expr)
       (let ((value (lookup-eq-safe expr var-value-alist)))
            (eval-dag-with-axe-evaluator
             (rest nodenum-worklist)
             dag-array-name dag-array
             var-value-alist eval-array-name
             (aset1 eval-array-name
                    eval-array nodenum (cons value nil))
             interpreted-function-alist array-depth))
       (let
        ((fn (car expr)))
        (if
         (equal fn 'quote)
         (let ((value (unquote expr)))
              (eval-dag-with-axe-evaluator
               (rest nodenum-worklist)
               dag-array-name dag-array
               var-value-alist eval-array-name
               (aset1 eval-array-name
                      eval-array nodenum (cons value nil))
               interpreted-function-alist array-depth))
         (let
          ((dargs (dargs expr)))
          (if (or (and (or (eq 'if fn)
                           (eq 'myif fn))
                       (= 3 (len dargs)))
                  (and (eq 'bvif fn)
                       (= 4 (len dargs))))
           (let*
            ((test (if (eq 'bvif fn)
                       (second dargs)
                       (first dargs)))
             (test-quotep (quotep test))
             (test-result
              (if test-quotep nil
                  (aref1 eval-array-name eval-array test)))
             (test-done (or test-quotep test-result)))
            (if
             (not test-done)
             (eval-dag-with-axe-evaluator
              (cons test nodenum-worklist)
              dag-array-name dag-array var-value-alist
              eval-array-name eval-array
              interpreted-function-alist array-depth)
             (let*
              ((test-val (if test-quotep (unquote test)
                             (car test-result)))
               (relevant-branch
                (if (eq 'bvif fn)
                    (if test-val (third dargs) (fourth dargs))
                    (if test-val (second dargs)
                        (third dargs))))
               (quotep-relevant-branch (quotep relevant-branch))
               (relevant-branch-result
                (if quotep-relevant-branch nil
                    (aref1 eval-array-name
                           eval-array relevant-branch)))
               (relevant-branch-done
                (or quotep-relevant-branch
                    relevant-branch-result)))
              (if
               (not relevant-branch-done)
               (eval-dag-with-axe-evaluator
                (cons relevant-branch nodenum-worklist)
                dag-array-name dag-array var-value-alist
                eval-array-name eval-array
                interpreted-function-alist array-depth)
               (let*
                ((bvifp (eq fn 'bvif))
                 (size (and bvifp (first dargs)))
                 (size-quotep (and bvifp (quotep size)))
                 (size-result
                  (and bvifp (not size-quotep)
                       (aref1 eval-array-name eval-array size)))
                 (bvif-and-size-not-done
                  (and bvifp
                       (not (or size-quotep size-result)))))
                (if
                 bvif-and-size-not-done
                 (eval-dag-with-axe-evaluator
                  (cons size nodenum-worklist)
                  dag-array-name dag-array var-value-alist
                  eval-array-name eval-array
                  interpreted-function-alist array-depth)
                 (let*
                  ((relevant-branch-value
                    (if quotep-relevant-branch
                        (unquote relevant-branch)
                        (car relevant-branch-result)))
                   (value
                    (if (eq fn 'bvif)
                        (bvchop (if size-quotep (unquote size)
                                    (car size-result))
                                relevant-branch-value)
                        relevant-branch-value)))
                  (eval-dag-with-axe-evaluator
                   (cdr nodenum-worklist)
                   dag-array-name dag-array
                   var-value-alist eval-array-name
                   (aset1 eval-array-name
                          eval-array nodenum (cons value nil))
                   interpreted-function-alist
                   array-depth))))))))
           (mv-let
             (nodenum-worklist worklist-extendedp)
             (get-args-not-done-array
              dargs eval-array-name
              eval-array nodenum-worklist nil)
             (if
              worklist-extendedp
              (eval-dag-with-axe-evaluator
               nodenum-worklist
               dag-array-name dag-array var-value-alist
               eval-array-name eval-array
               interpreted-function-alist array-depth)
              (let*
               ((arg-values
                 (get-vals-of-args-array
                  dargs eval-array-name eval-array))
                (value
                 (apply-axe-evaluator
                  fn arg-values interpreted-function-alist
                  array-depth)))
               (eval-dag-with-axe-evaluator
                (cdr nodenum-worklist)
                dag-array-name dag-array
                var-value-alist eval-array-name
                (aset1 eval-array-name
                       eval-array nodenum (cons value nil))
                interpreted-function-alist
                array-depth)))))))))))))

 ;;outside the mutual-recursion:
 (defun apply-axe-evaluator-to-quoted-args (fn args interpreted-function-alist array-depth)
   (declare (xargs
             :guard
             (and
              (or (symbolp fn) (pseudo-lambdap fn))
              (true-listp args)
              (all-myquotep args)
              (interpreted-function-alistp interpreted-function-alist)
              (natp array-depth))
             :verify-guards nil))
   (if
    (consp fn)
    (let*
     ((formals (second fn))
      (body (third fn))
      (alist (pairlis$-fast formals (unquote-list args))))
     (eval-axe-evaluator
      alist body
      interpreted-function-alist array-depth))
    (let
     ((args-to-walk-down args))
     (mv-let
       (hit val)
       (if
        (endp args-to-walk-down)
        (mv nil nil)
        (let
         ((args-to-walk-down (cdr args-to-walk-down)))
         (if
                      (endp args-to-walk-down)
                      (let ((arg1 (unquote (nth 0 args))))
                       (case fn
                        (quotep (mv t (quotep arg1)))
                        (natp (mv t (natp arg1)))
                        (posp (mv t (posp arg1)))
                        (integerp (mv t (integerp arg1)))
                        (rationalp (mv t (rationalp arg1)))
                        (print-constant (mv t (print-constant arg1)))
                        (not (mv t (not arg1)))
                        (power-of-2p (mv t (power-of-2p arg1)))
                        (lg (mv t (lg-unguarded arg1)))
                        (bool-to-bit (mv t (eval-in-logic (bool-to-bit arg1))))
                        (char-code (mv t (char-code-unguarded arg1)))
                        (code-char (mv t (code-char-unguarded arg1)))
                        (symbol-package-name
                             (mv t (symbol-package-name-unguarded arg1)))
                        (symbol-name (mv t (symbol-name-unguarded arg1)))
                        (all-same (mv t (all-same-unguarded arg1)))
                        (bool-fix$inline (mv t (bool-fix$inline arg1)))
                        (booleanp (mv t (booleanp arg1)))
                        (list::2set (mv t (list::2set arg1)))
                        (rkeys (mv t (rkeys arg1)))
                        (key-list (mv t (key-list arg1)))
                        (true-list-fix (mv t (true-list-fix arg1)))
                        (all-integerp (mv t (all-integerp arg1)))
                        (no-duplicatesp-equal
                             (mv t (no-duplicatesp-equal-unguarded arg1)))
                        (strip-cdrs (mv t (strip-cdrs-unguarded arg1)))
                        (strip-cars (mv t (strip-cars-unguarded arg1)))
                        (stringp (mv t (stringp arg1)))
                        (true-listp (mv t (true-listp arg1)))
                        (consp (mv t (consp arg1)))
                        (bytes-to-bits (mv t (eval-in-logic (bytes-to-bits arg1))))
                        (width-of-widest-int
                             (mv t (width-of-widest-int-unguarded arg1)))
                        (all-natp (mv t (all-natp arg1)))
                        (endp (mv t (endp-unguarded arg1)))
                        (bitnot (mv t (bitnot-unguarded arg1)))
                        (logmaskp (mv t (logmaskp arg1)))
                        (integer-length
                             (mv t (integer-length-unguarded arg1)))
                        (ceiling-of-lg (mv t (ceiling-of-lg-unguarded arg1)))
                        (unary-/ (mv t (unary-/-unguarded arg1)))
                        (nfix (mv t (nfix arg1)))
                        (ifix (mv t (ifix arg1)))
                        (len (mv t (len arg1)))
                        (reverse-list (mv t (reverse-list-unguarded arg1)))
                        (acl2-numberp (mv t (acl2-numberp arg1)))
                        (zp (mv t (zp-unguarded arg1)))
                        (unary-- (mv t (unary---unguarded arg1)))
                        (atom (mv t (atom arg1)))
                        (car (mv t (car-unguarded arg1)))
                        (cdr (mv t (cdr-unguarded arg1)))
                        (map-reverse-list (mv t (map-reverse-list-unguarded arg1)))
                        (realpart (mv t (realpart-unguarded arg1)))
                        (imagpart (mv t (imagpart-unguarded arg1)))
                        (symbolp (mv t (symbolp arg1)))
                        (characterp (mv t (characterp arg1)))
                        (complex-rationalp (mv t (complex-rationalp arg1)))
                        (denominator (mv t (denominator-unguarded arg1)))
                        (numerator (mv t (numerator-unguarded arg1)))
                        (t (mv nil nil))))
                      (let ((args-to-walk-down (cdr args-to-walk-down)))
                       (if
                        (endp args-to-walk-down)
                        (let ((arg2 (unquote (nth 1 args)))
                              (arg1 (unquote (nth 0 args))))
                         (case fn
                           (mv-nth (mv t (mv-nth-unguarded arg1 arg2)))
                           (items-have-len
                                (mv t (items-have-len-unguarded arg1 arg2)))
                           (all-all-unsigned-byte-p
                                (mv t (all-all-unsigned-byte-p arg1 arg2)))
                           (add-to-end (mv t (eval-in-logic (add-to-end arg1 arg2))))
                           (coerce (mv t (coerce-unguarded arg1 arg2)))
                           (< (mv t (<-unguarded arg1 arg2)))
                           (equal (mv t (equal arg1 arg2)))
                           (eql (mv t (equal arg1 arg2)))
                           (= (mv t (equal arg1 arg2)))
                           (list-equiv (mv t (list-equiv arg1 arg2)))
                           (prefixp (mv t (prefixp arg1 arg2)))
                           (lookup-equal (mv t (lookup-equal-unguarded arg1 arg2)))
                           (lookup (mv t (lookup-equal-unguarded arg1 arg2)))
                           (lookup-eq (mv t (lookup-equal-unguarded arg1 arg2)))
                           (bvnot (mv t (bvnot-unguarded arg1 arg2)))
                           (bvuminus (mv t (bvuminus-unguarded arg1 arg2)))
                           (assoc-equal
                                (mv t (assoc-equal-unguarded arg1 arg2)))
                           (unsigned-byte-p-forced
                                (mv t (unsigned-byte-p-forced arg1 arg2)))
                           (trim (mv t (trim-unguarded arg1 arg2)))
                           (binary-+ (mv t (binary-+-unguarded arg1 arg2)))
                           ;; (all-items-less-than (mv t (all-items-less-than arg1 arg2)))
                           (every-nth (mv t (every-nth-unguarded arg1 arg2)))
                           (intersection-equal
                                (mv t (intersection-equal-unguarded arg1 arg2)))
                           (all-equal$ (mv t (all-equal$-unguarded arg1 arg2)))
                           (repeatbit (mv t (repeatbit-unguarded arg1 arg2)))
                           (implies (mv t (implies arg1 arg2)))
                           (first-non-member
                                (mv t (first-non-member-unguarded arg1 arg2)))
                           (booland (mv t (booland arg1 arg2)))
                           (boolor (mv t (boolor arg1 arg2)))
                           (getbit-list (mv t (getbit-list-unguarded arg1 arg2)))
                           (set::union (mv t (eval-in-logic (set::union arg1 arg2))))
                           (leftrotate32
                                (mv t (leftrotate32-unguarded arg1 arg2)))
                           (set::insert (mv t (eval-in-logic (set::insert arg1 arg2))))
                           (floor (mv t (floor-unguarded arg1 arg2)))
                           (member-equal
                                (mv t (member-equal-unguarded arg1 arg2)))
                           (g (mv t (g arg1 arg2)))
                           (nthcdr (mv t (nthcdr-unguarded arg1 arg2)))
                           (take (mv t (take-unguarded arg1 arg2)))
                           (firstn (mv t (firstn-unguarded arg1 arg2)))
                           (binary-append
                                (mv t (binary-append-unguarded arg1 arg2)))
                           (signed-byte-p (mv t (signed-byte-p arg1 arg2)))
                           (unsigned-byte-p
                                (mv t (unsigned-byte-p arg1 arg2)))
                           (bvchop-list
                                (mv t (bvchop-list-unguarded arg1 arg2)))
                           (all-unsigned-byte-p
                                (mv t (all-unsigned-byte-p arg1 arg2)))
                           (all-signed-byte-p
                                (mv t (all-signed-byte-p arg1 arg2)))
                           (bitor (mv t (bitor-unguarded arg1 arg2)))
                           (bitand (mv t (bitand-unguarded arg1 arg2)))
                           (bitxor (mv t (bitxor-unguarded arg1 arg2)))
                           (expt (mv t (expt-unguarded arg1 arg2)))
                           (min (mv t (min-unguarded arg1 arg2)))
                           (max (mv t (max-unguarded arg1 arg2)))
                           (mod (mv t (mod-unguarded arg1 arg2)))
                           (getbit (mv t (getbit-unguarded arg1 arg2)))
                           (cons (mv t (cons arg1 arg2)))
                           (bvchop (mv t (bvchop-unguarded arg1 arg2)))
                           (logtail$inline
                                (mv t (logtail$inline-unguarded arg1 arg2)))
                           (logext (mv t (logext-unguarded arg1 arg2)))
                           (nth (mv t (nth-unguarded arg1 arg2)))
                           (binary-* (mv t (binary-*-unguarded arg1 arg2)))
                           (bvnot-list
                                (mv t (bvnot-list-unguarded arg1 arg2)))
                           (eq (mv t (equal arg1 arg2)))
                           (ceiling (mv t (ceiling-unguarded arg1 arg2)))
                           (group (mv t (eval-in-logic (group arg1 arg2))))
                           (group2 (mv t (eval-in-logic (group2 arg1 arg2))))
                           (set::in (mv t (eval-in-logic (set::in-unguarded arg1 arg2))))
                           (symbol< (mv t (symbol<-unguarded arg1 arg2)))
                           (t (mv nil nil))))
                        (let ((args-to-walk-down (cdr args-to-walk-down)))
                         (if
                          (endp args-to-walk-down)
                          (let ((arg3 (unquote (nth 2 args)))
                                (arg2 (unquote (nth 1 args)))
                                (arg1 (unquote (nth 0 args))))
                           (case fn
                            (repeat-tail (mv t (repeat-tail arg1 arg2 arg3)))
                            (negated-elems-listp (mv t
                                                     (negated-elems-listp-unguarded
                                                          arg1 arg2 arg3)))
                            (leftrotate (mv t (leftrotate-unguarded arg1 arg2 arg3)))
                            (acons (mv t (acons-unguarded arg1 arg2 arg3)))
                            (bvshr (mv t (bvshr-unguarded arg1 arg2 arg3)))
                            (bvashr (mv t (bvashr-unguarded arg1 arg2 arg3)))
                            (packbv (mv t (packbv-unguarded arg1 arg2 arg3)))
                            (unpackbv
                                 (mv t
                                     (eval-in-logic (unpackbv-less-guarded arg1 arg2 arg3))))
;;                            (bvplus-lst (mv t (bvplus-lst arg1 arg2 arg3)))
                            (bvequal
                                 (mv t (bvequal-unguarded arg1 arg2 arg3)))
                            (bvlt (mv t (bvlt-unguarded arg1 arg2 arg3)))
                            (bvle (mv t (bvle-unguarded arg1 arg2 arg3)))
                            (bvxor (mv t (bvxor-unguarded arg1 arg2 arg3)))
                            (bvor (mv t (bvor-unguarded arg1 arg2 arg3)))
                            (bvand (mv t (bvand-unguarded arg1 arg2 arg3)))
                            (bvmult (mv t (bvmult-unguarded arg1 arg2 arg3)))
                            (bvplus (mv t (bvplus-unguarded arg1 arg2 arg3)))
                            (bvminus
                                 (mv t (bvminus-unguarded arg1 arg2 arg3)))
                            (bvmod (mv t (bvmod-unguarded arg1 arg2 arg3)))
                            (bvdiv (mv t (bvdiv-unguarded arg1 arg2 arg3)))
                            (bvsx (mv t (bvsx-unguarded arg1 arg2 arg3)))
                            (sbvdiv (mv t (sbvdiv-unguarded arg1 arg2 arg3)))
                            (sbvdivdown (mv t (eval-in-logic (sbvdivdown arg1 arg2 arg3))))
                            (sbvrem (mv t (eval-in-logic (sbvrem arg1 arg2 arg3))))
                            (sbvmoddown (mv t (eval-in-logic (sbvmoddown arg1 arg2 arg3))))
                            (sbvlt
                                 (mv t (sbvlt-unguarded arg1 (ifix arg2) (ifix arg3))))
                            (sbvle (mv t (sbvle-unguarded arg1 arg2 arg3)))
                            (s (mv t (s arg1 arg2 arg3)))
                            (myif (mv t (myif arg1 arg2 arg3)))
                            (boolif (mv t (boolif arg1 arg2 arg3)))
                            (array-elem-2d
                              (mv t (eval-in-logic (array-elem-2d arg1 arg2 arg3))))
                            (bv-arrayp
                                 (mv t (bv-arrayp arg1 arg2 arg3)))
                            (update-nth (mv t (update-nth-unguarded arg1 arg2 arg3)))
                            (if (mv t (if arg1 arg2 arg3)))
                            (slice
                                 (mv t (slice-unguarded arg1 arg2 arg3)))
                            (bvshl (mv t (bvshl-unguarded arg1 arg2 arg3)))
                            ;; (keep-items-less-than (mv t (keep-items-less-than-unguarded arg1 arg2 arg3)))
                            (subrange (mv t
                                          (subrange-unguarded arg1
                                                              arg2
                                                              arg3)))
                            (bvxor-list
                                 (mv t
                                     (bvxor-list-unguarded arg1 arg2 arg3)))
                            (t (mv nil nil))))
                          (let ((args-to-walk-down (cdr args-to-walk-down)))
                           (if
                            (endp args-to-walk-down)
                            (let ((arg4 (unquote (nth 3 args)))
                                  (arg3 (unquote (nth 2 args)))
                                  (arg2 (unquote (nth 1 args)))
                                  (arg1 (unquote (nth 0 args))))
                             (case fn
                              (dag-val-with-axe-evaluator
                                 (mv t
                                     (eval-in-logic (dag-val-with-axe-evaluator
                                          arg1 arg2 arg3 (+ 1 array-depth)))))
                              (apply-axe-evaluator
                                   (mv t
                                       (eval-in-logic (apply-axe-evaluator
                                            arg1 arg2 arg3 array-depth))))
                              (update-subrange
                                  (mv t
                                      (eval-in-logic (update-subrange arg1 arg2 arg3 arg4))))
                              (update-nth2
                                   (mv t (eval-in-logic (update-nth2 arg1 arg2 arg3 arg4))))
                              (bv-array-clear
                                 (mv t (eval-in-logic (bv-array-clear arg1 arg2 arg3 arg4))))
                              (bvcat
                                  (mv t
                                      (bvcat-unguarded arg1 arg2 arg3 arg4)))
                              (bv-array-read (mv t
                                                 (bv-array-read-unguarded
                                                      arg1 arg2 arg3 arg4)))
                              (bvif
                                 (mv t (bvif-unguarded arg1 arg2 arg3 arg4)))
                              (t (mv nil nil))))
                            (let
                               ((args-to-walk-down (cdr args-to-walk-down)))
                             (if
                              (endp args-to-walk-down)
                              (let ((arg5 (unquote (nth 4 args)))
                                    (arg4 (unquote (nth 3 args)))
                                    (arg3 (unquote (nth 2 args)))
                                    (arg2 (unquote (nth 1 args)))
                                    (arg1 (unquote (nth 0 args))))
                               (case fn
                                (update-subrange2
                                     (mv t
                                         (eval-in-logic (update-subrange2
                                              arg1 arg2 arg3 arg4 arg5))))
                                (bv-array-write
                                   (mv t
                                       (bv-array-write-unguarded (nfix arg1)
                                                                 (nfix arg2)
                                                                 (nfix arg3)
                                                                 arg4 arg5)))
                                (bv-array-clear-range
                                     (mv t
                                         (eval-in-logic (bv-array-clear-range
                                              arg1 arg2 arg3 arg4 arg5))))
                                (t (mv nil nil))))
                              (let
                               ((args-to-walk-down (cdr args-to-walk-down)))
                               (if (endp args-to-walk-down)
                                   (mv nil nil)
                                (let ((args-to-walk-down
                                           (cdr args-to-walk-down)))
                                 (if (endp args-to-walk-down)
                                     (mv nil nil)
                                  (let ((args-to-walk-down
                                             (cdr args-to-walk-down)))
                                   (if
                                    (endp args-to-walk-down)
                                    (let ((arg8 (unquote (nth 7 args)))
                                          (arg7 (unquote (nth 6 args)))
                                          (arg6 (unquote (nth 5 args)))
                                          (arg5 (unquote (nth 4 args)))
                                          (arg4 (unquote (nth 3 args)))
                                          (arg3 (unquote (nth 2 args)))
                                          (arg2 (unquote (nth 1 args)))
                                          (arg1 (unquote (nth 0 args))))
                                     (declare (ignore arg8))
                                     (case fn
                                      (eval-dag-with-axe-evaluator
                                       (mv
                                        t
                                        (eval-in-logic (eval-dag-with-axe-evaluator arg1 arg2 arg3 arg4 arg5 arg6 arg7 array-depth))))
                                      (t (mv nil nil))))
                                    (mv nil nil))))))))))))))))))
                   (if
                    hit val
                    (let
                     ((match (assoc-eq fn interpreted-function-alist)))
                     (if
                      (not match)
                      (er
                       hard?
                       'apply-axe-evaluator-to-quoted-args
                       "Unknown function: ~x0 applied to args ~x1 (pass it as an interpreted function, or add to the list of built-ins, or check the arity of the call)."
                       fn args)
                      (let*
                        ((fn-info (cdr match))
                         (formals (first fn-info))
                         (body (second fn-info))
                         (alist
                              (pairlis$-fast formals (unquote-list args))))
                        (eval-axe-evaluator
                             alist body interpreted-function-alist
                             array-depth))))))))))
