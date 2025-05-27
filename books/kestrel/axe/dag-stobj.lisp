; Representing DAGs as stobjs
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

;; STATUS: In-progress.  Not used as of October, 2023.

;; TODO: Rename sdag to dag-stobj?

(include-book "dag-constant-alist")
(include-book "dag-variable-alist")
(include-book "bounded-darg-listp")

;; Throughout this file, we use "sdag" to mean "stobj DAG" (that is, a stobj
;; that represents an Axe DAG).

;; TODO: Consider disallowing constant nodes.
;; TODO: Consider allowing the stobj to be a single quotep.
;; TODO: Inline the function.

;; TODO: Strengthen types
;; TODO: Consider fixnums...
(defstobj sdag
  ;; The "length" of the DAG (number of valid nodes):
  (sdag-len :type (integer 0 *)
            :initially 0)
  ;; For each node, stores what we call it's "FN", which is either :var, quote,
  ;; or a regular function symbol:
  (sdag-fns :type (array symbol (1000))
            :initially nil)
  ;; For each node, stores what we call it's "ARGS".  For :var, this is the
  ;; variable (a symbol).  For quote, this is the quoted value.  For a regular
  ;; function, this is the list of args:
  (sdag-args :type (array t (1000))
             :initially nil)
  ;; Maps each node to the list of nodenums of all of its parents.
  (sdag-parents :type (array t (1000))
                :initially nil)
  ;; TODO: Use a hash table?
  (sdag-constants :type t
                  :initially nil)
  ;; TODO: Use a hash table?
  (sdag-variables :type t
                  :initially nil)
  :renaming ((sdag-fnsi sdag-fn)
             (sdag-argsi sdag-args)))

(in-theory (disable sdag-args-length sdag-argsp sdag-fns-length sdag-fnsp sdag-len sdag-lenp sdag-parents-length sdag-parentsp sdagp
                    sdag-fn
                    sdag-args))

(defthm sdagp-forward-1
  (implies (sdagp sdag)
           (natp (sdag-len sdag)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable sdagp sdag-len sdag-lenp))))

;; Check that, for nodes N and up, the fn and the args of each node are consistent.
;; Counts up to match functions like make-sdag-constant-alist-aux.
(defun sdag-fns-and-args-okp (n sdag)
  (declare (xargs :stobjs sdag
                  :guard (and (natp n)
                              (<= (sdag-len sdag) (sdag-fns-length sdag))
                              (equal (sdag-fns-length sdag)
                                     (sdag-args-length sdag)))
                  :measure (nfix (+ 1 (- (sdag-len sdag) n)))))
  (if (or (>= n (sdag-len sdag))
          (not (mbt (natp n)))
          (not (mbt (natp (sdag-len sdag)))))
      t
    (and (let ((fn (sdag-fn n sdag))
               (args (sdag-args n sdag)))
           (case fn
             ;; if the fn is :var, the args is a single symbol (the variable),
             ;; not even a list:
             (:var (symbolp args))
             ;; if the fn is 'quote, there is a single arg (the quoted thing):
             ;; TODO: Why even make it a list?
             (quote (and (= 1 (len args))
                         (true-listp args)))
             ;; for a regular function call, the args are nodenums less than n
             ;; and/or quoteps:
             (otherwise (bounded-darg-listp args n))))
         (sdag-fns-and-args-okp (+ 1 n) sdag))))

(defthm true-listp-of-sdag-args-when-sdag-fns-and-args-okp
  (implies (and (not (equal (sdag-fn n sdag) :var))
                (sdag-fns-and-args-okp min sdag)
                (sdagp sdag)
                (integerp n)
                (< n (sdag-len sdag))
                (natp min)
                (<= min n))
           (true-listp (sdag-args n sdag)))
  :hints (("Goal" :in-theory (enable SDAG-FN))))

(defthm symbolp-of-sdag-args-when-sdag-fns-and-args-okp
  (implies (and (equal (sdag-fn n sdag) :var)
                (sdag-fns-and-args-okp min sdag)
                (sdagp sdag)
                (integerp n)
                (< n (sdag-len sdag))
                (natp min)
                (<= min n))
           (symbolp (sdag-args n sdag)))
  :hints (("Goal" :in-theory (enable sdag-fn))))

;;;
;;; make-sdag-constant-alist-aux
;;;

;; Returns the dag-constant-alist.
;; Pairs are in decreasing order of nodenum.
(defund make-sdag-constant-alist-aux (n ;counts up
                                      sdag
                                      ;;gets populated:
                                      dag-constant-alist)
  (declare (xargs :stobjs sdag
                  :guard (and (equal (sdag-fns-length sdag)
                                     (sdag-args-length sdag))
                              (<= (sdag-len sdag) (sdag-fns-length sdag))
                              (sdag-fns-and-args-okp 0 sdag)
                              (natp n)
                              (<= n (sdag-len sdag))
                              (dag-constant-alistp dag-constant-alist))
                  :measure (nfix (+ 1 (- (sdag-len sdag) n)))))
  (if (or (>= n (sdag-len sdag))
          (not (mbt (natp n)))
          (not (mbt (natp (sdag-len sdag)))))
      dag-constant-alist
    (let* ((fn (sdag-fn n sdag))
           (dag-constant-alist
            (case fn
              ;; a var is not a constant
              (:var dag-constant-alist)
              ;; a quote is always a constant
              (quote (acons (cons 'quote (sdag-args n sdag))
                            n
                            dag-constant-alist))
              ;; a function call is a "constant" iff its args contain no
              ;; nodenums:
              (otherwise (let ((args (sdag-args n sdag)))
                           (if (all-consp args)
                               (acons (cons fn args)
                                      n
                                      dag-constant-alist)
                             dag-constant-alist))))))
      (make-sdag-constant-alist-aux (+ 1 n)
                                    sdag
                                    dag-constant-alist))))

(defthm dag-constant-alistp-of-make-sdag-constant-alist-aux
  (implies (dag-constant-alistp dag-constant-alist)
           (dag-constant-alistp (make-sdag-constant-alist-aux n sdag dag-constant-alist)))
  :hints (("Goal" :in-theory (enable make-sdag-constant-alist-aux))))

;; Computes the dag-constant-alist of an sdag from its nodes.  For a
;; well-formed sdag, this is what should be stored in the sdag-constants
;; component.  Pairs are in decreasing order of nodenum.
(defund make-sdag-constant-alist (sdag)
  (declare (xargs :stobjs sdag
                  :guard (and (equal (sdag-fns-length sdag)
                                     (sdag-args-length sdag))
                              (<= (sdag-len sdag) (sdag-fns-length sdag))
                              (sdag-fns-and-args-okp 0 sdag))))
  (make-sdag-constant-alist-aux 0 sdag nil))

(defthm dag-constant-alistp-of-make-sdag-constant-alist
  (dag-constant-alistp (make-sdag-constant-alist sdag))
  :hints (("Goal" :in-theory (enable make-sdag-constant-alist))))

;;;
;;; make-sdag-variable-alist-aux
;;;

;; Returns the dag-variable-alist.
;; Pairs are in decreasing order of nodenum.
(defund make-sdag-variable-alist-aux (n ;counts up
                                      sdag
                                      ;;gets populated:
                                      dag-variable-alist)
  (declare (xargs :stobjs sdag
                  :guard (and (equal (sdag-fns-length sdag)
                                     (sdag-args-length sdag))
                              (<= (sdag-len sdag) (sdag-fns-length sdag))
                              (sdag-fns-and-args-okp 0 sdag)
                              (natp n)
                              (<= n (sdag-len sdag))
                              (dag-variable-alistp dag-variable-alist))
                  :measure (nfix (+ 1 (- (sdag-len sdag) n)))))
  (if (or (>= n (sdag-len sdag))
          (not (mbt (natp n)))
          (not (mbt (natp (sdag-len sdag)))))
      dag-variable-alist
    (let* ((fn (sdag-fn n sdag))
           (dag-variable-alist
            (if (eq fn :var)
                (add-to-dag-variable-alist (sdag-args n sdag) ;will be the single symbol
                                           n
                                           dag-variable-alist)
              dag-variable-alist)))
      (make-sdag-variable-alist-aux (+ 1 n)
                                    sdag
                                    dag-variable-alist))))

(defthm dag-variable-alistp-of-make-sdag-variable-alist-aux
  (implies (and (sdag-fns-and-args-okp n sdag)
                (dag-variable-alistp dag-variable-alist))
           (dag-variable-alistp (make-sdag-variable-alist-aux n sdag dag-variable-alist)))
  :hints (("Goal" :in-theory (enable make-sdag-variable-alist-aux))))

;; Computes the dag-variable-alist of an sdag from its nodes.  For a
;; well-formed sdag, this is what should be stored in the sdag-variables
;; component.  Pairs are in decreasing order of nodenum.
(defund make-sdag-variable-alist (sdag)
  (declare (xargs :stobjs sdag
                  :guard (and (equal (sdag-fns-length sdag)
                                     (sdag-args-length sdag))
                              (<= (sdag-len sdag) (sdag-fns-length sdag))
                              (sdag-fns-and-args-okp 0 sdag))))
  (make-sdag-variable-alist-aux 0 sdag (empty-dag-variable-alist)))

(defthm dag-variable-alistp-of-make-sdag-variable-alist
  (implies (sdag-fns-and-args-okp 0 sdag)
           (dag-variable-alistp (make-sdag-variable-alist sdag)))
  :hints (("Goal" :in-theory (enable make-sdag-variable-alist))))

;;;
;;; wf-sdagp (well-formed stobj DAG)
;;;

;; Recognize a well-formed sdag:
(defun wf-sdagp (sdag)
  (declare (xargs :stobjs sdag))
  (let ((dag-len (sdag-len sdag))
        (fns-length (sdag-fns-length sdag))
        (dag-constant-alist (sdag-constants sdag))
        (dag-variable-alist (sdag-variables sdag)))
    (and (< dag-len (expt 2 56)) ;tighten?
         ;; The array has at least enough space to hold all the valid nodes:
         (<= dag-len fns-length)
         ;; All three arrays have the same length:
         (= fns-length (sdag-args-length sdag))
         (= fns-length (sdag-parents-length sdag))
         ;; The fns and args of all the nodes are consistent:
         (sdag-fns-and-args-okp 0 sdag)
         ;; The indices are correct:
         ;; TODO: The parent array
         (equal dag-constant-alist (make-sdag-constant-alist sdag))
         (equal dag-variable-alist (make-sdag-variable-alist sdag)))))

;; todo: prove that the dag-constant-alist is bounded - or just check the first entry since we know the nodenums decrease

;; ;; get the fn of node N in SDAG.
;; (defund sdag-fn (n sdag)
;;   (declare (xargs :stobjs sdag
;;                   :guard (and (natp n)
;;                               (< n (sdag-len sdag))
;;                               (wf-sdagp sdag))))
;;   (sdag-fn n sdag))

;; ;; get the args of node N in SDAG.
;; (defund sdag-args (n sdag)
;;   (declare (xargs :stobjs sdag
;;                   :guard (and (natp n)
;;                               (< n (sdag-len sdag))
;;                               (wf-sdagp sdag))))
;;   (sdag-argsi n sdag))

;; The sdag is initially well-formed:
(defthm wf-sdagp-of-create-sdag
  (wf-sdagp (create-sdag)))
