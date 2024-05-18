; Pruning irrelevant IF-branches in a DAG
;
; Copyright (C) 2022-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This utility tries to resolve IF/MYIF/BOOLIF/BVIF tests in the dag, using STP and the contexts of the nodes.

;; TODO: Add the ability to rewrite tests when pruning.

(include-book "prove-with-stp")
(include-book "rewriter-basic")
(include-book "dag-size-fast")
(include-book "basic-rules")
(include-book "rule-lists") ; for unsigned-byte-p-forced-rules
(include-book "bv-rules-axe") ; for bvchop-identity-axe
(include-book "kestrel/booleans/booleans" :dir :system) ; for MYIF-OF-BOOL-FIX-ARG1
(include-book "kestrel/bv/rules" :dir :system) ; todo: reduce, for the unsigned-byte-p-forced rules
(include-book "kestrel/bv/sbvrem" :dir :system)
(include-book "kestrel/bv/sbvdiv" :dir :system)
(include-book "kestrel/bv/unsigned-byte-p-forced-rules" :dir :system)
(include-book "kestrel/bv-lists/bv-array-read-rules" :dir :system)
(include-book "kestrel/utilities/if" :dir :system) ; for rules mentioned below
(include-book "kestrel/utilities/myif-def" :dir :system) ; do not remove (since this book knows about myif)
(include-book "kestrel/utilities/real-time-since" :dir :system)
(include-book "kestrel/utilities/rational-printing" :dir :system) ; for print-to-hundredths
(include-book "kestrel/booleans/boolif" :dir :system) ; do not remove (since this book knows about boolif)
(include-book "kestrel/booleans/bool-fix" :dir :system) ; do not remove (since this book knows about bool-fix$inline)
(include-book "kestrel/utilities/ensure-rules-known" :dir :system)
(local (include-book "cars-decreasing-by-1"))
(local (include-book "kestrel/utilities/get-real-time" :dir :system))
(local (include-book "kestrel/lists-light/cdr" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "kestrel/typed-lists-light/integer-listp" :dir :system))

(local (in-theory (disable state-p natp w
                           ;; for speed:
                           use-all-rationalp-for-car
                           consp-from-len-cheap
                           default-+-2
                           default-cdr
                           member-equal)))

;move
(local
  (defthm symbolp-when-member-equal
    (implies (and (member-equal x lst)
                  (symbol-listp lst))
             (symbolp x))
    :hints (("Goal" :in-theory (enable member-equal)))))

(local
  (defthm member-equal-of-singleton
    (implies (and (syntaxp (quotep lst))
                  (= 1 (len lst)))
             (iff (member-equal x lst)
                  (equal x (first lst))))
    :hints (("Goal" :in-theory (enable member-equal)))))

(defthmd integer-listp-of-strip-cars-when-weak-dagp-aux
  (implies (weak-dagp-aux dag)
           (integer-listp (strip-cars dag)))
  :hints (("Goal" :in-theory (enable weak-dagp-aux))))

(defthm bounded-possibly-negated-nodenumsp-when-bounded-contextp
  (implies (bounded-contextp context bound)
           (equal (bounded-possibly-negated-nodenumsp context bound)
                  (not (equal (false-context) context))))
  :hints (("Goal" :in-theory (enable bounded-contextp))))

;move:

;; ;; Checks that DAG is a true-list of pairs of the form (<nodenum> . <bounded-dag-expr>).
;; (defund bounded-weak-dagp-aux (dag bound)
;;   (declare (xargs :guard (natp bound)))
;;   (if (atom dag)
;;       (null dag)
;;     (let ((entry (car dag)))
;;       (and (consp entry)
;;            (let* ((nodenum (car entry))
;;                   (expr (cdr entry)))
;;              (and (natp nodenum)
;;                   (< nodenum bound)
;;                   (bounded-dag-exprp nodenum expr)
;;                   (bounded-weak-dagp-aux (cdr dag) bound)))))))

;; (defthm weak-dagp-aux-when-bounded-weak-dagp-aux
;;   (implies (bounded-weak-dagp-aux dag bound) ; free var
;;            (weak-dagp-aux dag))
;;   :hints (("Goal" :in-theory (enable bounded-weak-dagp-aux
;;                                      weak-dagp-aux))))

;; (defthm bounded-weak-dagp-aux-of-cdr
;;   (implies (bounded-weak-dagp-aux dag bound)
;;            (bounded-weak-dagp-aux (cdr dag) bound))
;;   :hints (("Goal" :in-theory (enable bounded-weak-dagp-aux))))

;; (defthm bounded-weak-dagp-aux-forward-to-alistp
;;   (implies (bounded-weak-dagp-aux dag bound)
;;            (alistp dag))
;;   :rule-classes :forward-chaining
;;   :hints (("Goal" :in-theory (enable bounded-weak-dagp-aux alistp))))

;; (defthm bounded-weak-dagp-aux-when-pseudo-dagp-aux
;;   (implies (and (pseudo-dagp-aux dag n)
;;                 (< n bound)
;;                 (natp n)
;;                 (natp bound))
;;            (bounded-weak-dagp-aux dag bound))
;;   :hints (("Goal" :in-theory (enable pseudo-dagp-aux bounded-weak-dagp-aux))))

;; (defthm bounded-weak-dagp-aux-of-len-when-pseudo-dagp
;;   (implies (pseudo-dagp dag)
;;            (bounded-weak-dagp-aux dag (len dag)))
;;   :hints (("Goal" :in-theory (enable pseudo-dagp pseudo-dagp-aux bounded-weak-dagp-aux))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; When the test of an IF or MYIF can be resolved, the IF/MYIF can be replaced
;; by a call of ID around either its then-branch or its else-branch.  This
;; ensures the resulting DAG is still legal and has no changes in node
;; numbering.  The calls to ID can be removed by a subsequent call of the
;; rewriter.  TODO: Do better?
(defun id (x) x)

(defund prune-dag-post-rewrite-rules ()
  (declare (xargs :guard t))
  (append
  '(id
    bool-fix-when-booleanp ; todo: add more booleanp rules, or even pass them in?
    bool-fix-of-bool-fix
    boolif-of-bool-fix-arg1
    boolif-of-bool-fix-arg2
    boolif-of-bool-fix-arg3
    if-of-bool-fix-arg1
    myif-of-bool-fix-arg1
    bvif-of-bool-fix
    not-of-bool-fix
    boolor-of-bool-fix-arg1
    boolor-of-bool-fix-arg2
    booland-of-bool-fix-arg1
    booland-of-bool-fix-arg2
    booleanp-of-bool-fix-rewrite
    if-same-branches
    if-when-non-nil-constant
    if-of-nil
    ;; if-of-not ; maybe
    if-of-t-and-nil-when-booleanp ; or bool-fix it
    myif-same-branches
    myif-of-nil
    myif-of-constant-when-not-nil
    myif-nil-t
    myif-of-t-and-nil-when-booleanp
    ;; todo: more rules?
    bvchop-identity-axe
    )
  (unsigned-byte-p-forced-rules)
  ;; todo: add rules like bvif-of-bvchop-arg3 (make a rule-list for them)
  ;; (bv-function-of-bvchop-rules) ;; hmmm, maybe we should pass in these rules?
  ))

(ensure-rules-known (prune-dag-post-rewrite-rules))

;; Returns (mv erp result state), where result is :true (meaning non-nil), :false, or :unknown.
;; TODO: Also use rewriting?  See also try-to-resolve-test.
(defund try-to-resolve-node-with-stp (nodenum-or-quotep
                                      assumptions
                                      ;; rule-alist interpreted-function-alist monitored-rules call-stp
                                      dag-array ;must be named 'dag-array (todo: generalize?)
                                      dag-len
                                      dag-parent-array ;must be named 'dag-parent-array (todo: generalize?)
                                      base-filename    ;a string
                                      print
                                      max-conflicts ;a number of conflicts, or nil for no max
                                      ;; counterexamplep
                                      state)
  (declare (xargs :guard (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (bounded-dag-parent-arrayp 'dag-parent-array dag-parent-array dag-len)
                              (equal (alen1 'dag-parent-array dag-parent-array)
                                     (alen1 'dag-array dag-array))
                              (or (myquotep nodenum-or-quotep)
                                  (and (natp nodenum-or-quotep)
                                       (< nodenum-or-quotep dag-len)))
                              (bounded-possibly-negated-nodenumsp assumptions dag-len)
                              (stringp base-filename)
                              (print-levelp print)
                              (or (null max-conflicts)
                                  (natp max-conflicts)))
                  :stobjs state))
  (b* (((when (consp nodenum-or-quotep)) ; test for quotep
        (if (unquote nodenum-or-quotep)
            (mv (erp-nil) :true state)
          (mv (erp-nil) :false state)))
       (nodenum nodenum-or-quotep)
       (- (and (print-level-at-least-tp print) (cw "(Attempting to resolve test with STP using ~x0 assumptions.~%" (len assumptions))))
       ;; TODO: Consider trying to be smart about whether to try the true proof or the false proof first (e.g., by running a test).
       (- (and (print-level-at-least-tp print) (cw "(Attempting to prove test true with STP:~%")))
       ((mv true-result state)
        (prove-node-implication-with-stp assumptions
                                         nodenum
                                         dag-array dag-len dag-parent-array
                                         base-filename print max-conflicts
                                         nil ; counterexamplep
                                         nil ; print-cex-as-signedp
                                         state))
       ((when (eq *error* true-result))
        (prog2$ (er hard? 'try-to-resolve-node-with-stp "Error calling STP")
                (mv :error-calling-stp :unknown state)))
       ((when (eq *valid* true-result)) ;; STP proved the test
        (prog2$ (and (print-level-at-least-tp print) (cw "STP proved the test true.))~%"))
                (mv (erp-nil) :true state)))
       (- (and (print-level-at-least-tp print) (cw "STP failed to prove the test true.)~%")))
       (- (and (print-level-at-least-tp print) (cw "(Attempting to prove test false with STP:~%")))
       ((mv false-result state)
        (prove-node-implication-with-stp assumptions
                                         `(not ,nodenum)
                                         dag-array dag-len dag-parent-array
                                         base-filename print max-conflicts
                                         nil ;counterexamplep
                                         nil ; print-cex-as-signedp
                                         state))
       ((when (eq *error* false-result))
        (prog2$ (er hard? 'try-to-resolve-node-with-stp "Error calling STP")
                (mv :error-calling-stp :unknown state)))
       ((when (eq *valid* false-result)) ;; STP proved the negation of the test
        (prog2$ (and (print-level-at-least-tp print) (cw "STP proved the test false.))~%"))
                (mv (erp-nil) :false state))))
    (prog2$ (and (print-level-at-least-tp print) (cw "STP did not resolve the test.))~%"))
            (mv (erp-nil) :unknown state))))

(defthm w-of-mv-nth-2-of-try-to-resolve-node-with-stp
  (equal (w (mv-nth 2 (try-to-resolve-node-with-stp dag dag-array dag-len dag-parent-array context-array print max-conflicts dag-acc state)))
         (w state))
  :hints (("Goal" :in-theory (enable try-to-resolve-node-with-stp))))

(defthm true-listp-of-dargs-of-cdr-of-car-when-pseudo-dagp-type
  (implies (and (pseudo-dagp dag)
                (consp dag))
           (true-listp (dargs (cdr (car dag)))))
  :rule-classes :type-prescription)

;; These justify the pruning done by prune-dag-approximately-aux:
(thm (implies test (equal (myif test x y) (if test x y)))) ; myif can be treated just like if
(thm (implies test (equal (if test x y) (id x))))
(thm (implies test (equal (myif test x y) (id x))))
(thm (implies (not test) (equal (if test x y) (id y))))
(thm (implies (not test) (equal (myif test x y) (id y))))
(thm (implies test (equal (boolif test x y) (bool-fix$inline x))))
(thm (implies (not test) (equal (boolif test x y) (bool-fix$inline y))))
(thm (implies test (equal (bvif size test x y) (bvchop size x))))
(thm (implies (not test) (equal (bvif size test x y) (bvchop size y))))

;; Returns (mv erp dag state).
(defund prune-dag-approximately-aux (dag dag-array dag-len dag-parent-array context-array print max-conflicts dag-acc state)
  (declare (xargs :guard (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (bounded-dag-parent-arrayp 'dag-parent-array dag-parent-array dag-len)
                              (equal (alen1 'dag-parent-array dag-parent-array)
                                     (alen1 'dag-array dag-array))
                              (or (null dag)
                                  (pseudo-dagp dag))
                              (<= (len dag) dag-len)
                              ;; (bounded-weak-dagp-aux dag dag-len)
                              (bounded-context-arrayp 'context-array context-array dag-len dag-len)
                              (print-levelp print)
                              (or (null max-conflicts)
                                  (natp max-conflicts))
                              (weak-dagp-aux dag-acc) ; ignores the order
                              (cars-increasing-by-1 dag-acc)
                              (if (and (consp dag)
                                       (consp dag-acc))
                                  (equal (car (first dag-acc)) (+ 1 (car (first dag))))
                                t))
                  :guard-hints (("Goal" ;:expand (bounded-weak-dagp-aux dag dag-len)
                                 :do-not '(generalize eliminate-destructors)
                                 :in-theory (e/d (;pseudo-dagp-aux
                                             true-listp-of-dargs-of-cdr-of-car-when-pseudo-dagp-type
                                             car-of-car-when-pseudo-dagp)
                                                 (weak-dagp-aux myquotep))))
                  :stobjs state))
  (if (endp dag)
      (mv (erp-nil) (reverse-list dag-acc) state)
    (let* ((entry (first dag))
           (nodenum (car entry))
           (expr (cdr entry)))
      (if (atom expr) ; variable (nothing to do):
          (prune-dag-approximately-aux (rest dag) dag-array dag-len dag-parent-array context-array print max-conflicts (acons nodenum expr dag-acc) state)
        (let ((fn (ffn-symb expr)))
          (case fn
            ;; quoted constant (nothing to do):
            (quote (prune-dag-approximately-aux (rest dag) dag-array dag-len dag-parent-array context-array print max-conflicts (acons nodenum expr dag-acc) state))
            ((if myif) ; (if/myif test then-branch else-branch)
             (b* (((when (not (consp (cdr (cdr (dargs expr))))))
                   (mv :bad-if-arity nil state))
                  ;; Get the context for this IF/MYIF node (note that its test node may appear in other contexts too):
                  (context (aref1 'context-array context-array nodenum))
                  ((when (eq (false-context) context))
                   (cw "NOTE: False context encountered for node ~x0 (selecting then-branch).~%" nodenum)
                   (prune-dag-approximately-aux (rest dag) dag-array dag-len dag-parent-array context-array print max-conflicts (acons nodenum `(id ,(darg2 expr)) dag-acc) state))
                  ;; Try to resolve the IF test:
                  ((mv erp result state)
                   ;; TODO: What if the test is among the context assumptions?
                   ;; TODO: Should we use any rewriting here?
                   (try-to-resolve-node-with-stp (darg1 expr) ; the test of the IF/MYIF
                                                 context      ; the assumptions
                                                 dag-array dag-len dag-parent-array
                                                 "PRUNE" ; todo: improve?
                                                 print
                                                 max-conflicts
                                                 state))
                  ((when erp) (mv erp nil state))
                  ;; We use a wrapper of ID here to ensure the node is
                  ;; still legal (not a naked nodenum) and to preserve the node
                  ;; numbering (calls to ID will later be removed by rewriting):
                  (expr (if (eq result :true)
                            `(id ,(darg2 expr)) ; the IF/MYIF is equal to its then-branch
                          (if (eq result :false)
                              `(id ,(darg3 expr)) ; the IF/MYIF is equal to its else-branch
                            ;; Could not resolve the test:
                            expr))))
               (prune-dag-approximately-aux (rest dag) dag-array dag-len dag-parent-array context-array print max-conflicts (acons nodenum expr dag-acc) state)))
            ((boolif) ; (boolif test then-branch else-branch)
             (b* (((when (not (consp (cdr (cdr (dargs expr))))))
                   (mv :bad-boolif-arity nil state))
                  ;; Get the context for this BOOLIF node (note that its test node may appear in other contexts too):
                  (context (aref1 'context-array context-array nodenum))
                  ((when (eq (false-context) context))
                   (cw "NOTE: False context encountered for node ~x0 (selecting then-branch).~%" nodenum)
                   (prune-dag-approximately-aux (rest dag) dag-array dag-len dag-parent-array context-array print max-conflicts (acons nodenum `(bool-fix$inline ,(darg2 expr)) dag-acc) state))
                  ;; Try to resolve the BOOLIF test:
                  ((mv erp result state)
                   ;; TODO: What if the test is among the context assumptions?
                   ;; TODO: Should we use any rewriting here?
                   (try-to-resolve-node-with-stp (darg1 expr) ; the test of the BOOLIF
                                                 context      ; the assumptions
                                                 dag-array dag-len dag-parent-array
                                                 "PRUNE" ; todo: improve?
                                                 print
                                                 max-conflicts
                                                 state))
                  ((when erp) (mv erp nil state))
                  ;; Even if we can resolve the test, we have to keep the
                  ;; bool-fixing.  This also ensures the node is still legal
                  ;; (not a naked nodenum) and preserves the node numbering
                  ;; (calls to bool-fix$inline will later be removed by rewriting):
                  (expr (if (eq result :true)
                            `(bool-fix$inline ,(darg2 expr)) ; the BOOLIF is equal to the bool-fix of its then-branch
                          (if (eq result :false)
                              `(bool-fix$inline ,(darg3 expr)) ; the BOOLIF is equal to the bool-fix of its else-branch
                            ;; Could not resolve the test:
                            expr))))
               (prune-dag-approximately-aux (rest dag) dag-array dag-len dag-parent-array context-array print max-conflicts (acons nodenum expr dag-acc) state)))
            ((bvif) ; (bvif size test then-branch else-branch)
             (b* (((when (not (consp (cdddr (dargs expr)))))
                   (mv :bad-bvif-arity nil state))
                  ;; Get the context for this BVIF node (note that its test node may appear in other contexts too):
                  (context (aref1 'context-array context-array nodenum))
                  ((when (eq (false-context) context))
                   (cw "NOTE: False context encountered for node ~x0 (selecting then-branch).~%" nodenum)
                   (prune-dag-approximately-aux (rest dag) dag-array dag-len dag-parent-array context-array print max-conflicts (acons nodenum `(bvchop ,(darg1 expr) ,(darg3 expr)) dag-acc) state))
                  ;; Try to resolve the BVIF test:
                  ((mv erp result state)
                   ;; TODO: What if the test is among the context assumptions?
                   ;; TODO: Should we use any rewriting here?
                   (try-to-resolve-node-with-stp (darg2 expr) ; the test of the BVIF
                                                 context      ; the assumptions
                                                 dag-array dag-len dag-parent-array
                                                 "PRUNE" ; todo: improve?
                                                 print
                                                 max-conflicts
                                                 state))
                  ((when erp) (mv erp nil state))
                  ;; Even if we can resolve the test, we have to keep the
                  ;; chopping.  This also ensures the node is still legal
                  ;; (not a naked nodenum) and preserves the node numbering
                  ;; (calls to bvchop will later be removed by rewriting):
                  (expr (if (eq result :true)
                            `(bvchop ,(darg1 expr) ,(darg3 expr)) ; the BVIF is equal to the bvchop of its then-branch
                          (if (eq result :false)
                              `(bvchop ,(darg1 expr) ,(darg4 expr)) ; the BVIF is equal to the bvchop of its else-branch
                            ;; Could not resolve the test:
                            expr))))
               (prune-dag-approximately-aux (rest dag) dag-array dag-len dag-parent-array context-array print max-conflicts (acons nodenum expr dag-acc) state)))
            (t
             (prune-dag-approximately-aux (rest dag) dag-array dag-len dag-parent-array context-array print max-conflicts (acons nodenum expr dag-acc) state))))))))

(local
 (defthmd pseudo-dagp-aux-of-top-nodenum-of-dag-when-weak-dagp-aux-and-cars-decreasing-by-1
   (implies (and (consp dag)
                 (cars-decreasing-by-1 dag)
                 (equal 0 (car (car (last dag))))
                 (weak-dagp-aux dag))
            (pseudo-dagp-aux dag (top-nodenum-of-dag dag)))
   :hints (("Goal" :induct (weak-dagp-aux dag)
            :in-theory (enable cars-decreasing-by-1
                               weak-dagp-aux
                               pseudo-dagp-aux
                               top-nodenum-of-dag)))))

(local
 (defthm prune-dag-approximately-aux-return-type
   (implies (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                 (bounded-dag-parent-arrayp 'dag-parent-array dag-parent-array dag-len)
                 (equal (alen1 'dag-parent-array dag-parent-array)
                        (alen1 'dag-array dag-array))
                 (or (null dag)
                     (pseudo-dagp dag))
                 (<= (len dag) dag-len)
                 (bounded-context-arrayp 'context-array context-array dag-len dag-len)
                 (or (null max-conflicts)
                     (natp max-conflicts))
                 (weak-dagp-aux dag-acc) ; ignores the order
                 (cars-increasing-by-1 dag-acc)
                 (if (and (consp dag)
                          (consp dag-acc))
                     (equal (car (first dag-acc)) (+ 1 (car (first dag))))
                   t)
                 (or (consp dag) (consp dag-acc)) ; at least one of them is a cons
                 (if (not (consp dag))
                     (equal (car (first dag-acc)) 0)
                   t))
            (mv-let (erp new-dag state)
              (prune-dag-approximately-aux dag dag-array dag-len dag-parent-array context-array print max-conflicts dag-acc state)
              (declare (ignore state))
              (implies (not erp)
                       (and (cars-decreasing-by-1 new-dag)
                            (weak-dagp-aux new-dag)
                            (consp new-dag)
                            (equal (car (car (last new-dag))) 0)))))
   :rule-classes nil
   :hints (("Goal" :induct t
            :expand ((prune-dag-approximately-aux dag dag-array dag-len dag-parent-array context-array print nil dag-acc state)
                     (prune-dag-approximately-aux dag dag-array dag-len dag-parent-array context-array print nil nil state))
            :in-theory (e/d (prune-dag-approximately-aux
                             true-listp-of-dargs-of-cdr-of-car-when-pseudo-dagp-type
                             car-of-car-when-pseudo-dagp
                             integer-listp-of-strip-cars-when-weak-dagp-aux)
                            (nth
                             len-of-cdr
                             member-equal
                             weak-dagp-aux
                             myquotep))))))

;for dag-acc=nil
(local
 (defthm prune-dag-approximately-aux-return-type-special
   (implies (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                 (bounded-dag-parent-arrayp 'dag-parent-array dag-parent-array dag-len)
                 (equal (alen1 'dag-parent-array dag-parent-array)
                        (alen1 'dag-array dag-array))
                 (or (null dag)
                     (pseudo-dagp dag))
                 (<= (len dag) dag-len)
                 (bounded-context-arrayp 'context-array context-array dag-len dag-len)
                 (or (null max-conflicts)
                     (natp max-conflicts))
                 (consp dag))
            (mv-let (erp new-dag state)
              (prune-dag-approximately-aux dag dag-array dag-len dag-parent-array context-array print max-conflicts nil state)
              (declare (ignore state))
              (implies (not erp)
                       (and (cars-decreasing-by-1 new-dag)
                            (weak-dagp-aux new-dag)
                            (consp new-dag)
                            (equal (car (car (last new-dag))) 0)))))
   :hints (("Goal" :use (:instance prune-dag-approximately-aux-return-type (dag-acc nil))))))

;gen?
(local
 (defthm prune-dag-approximately-aux-return-type-special-corollary
   (implies (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                 (bounded-dag-parent-arrayp 'dag-parent-array dag-parent-array dag-len)
                 (equal (alen1 'dag-parent-array dag-parent-array)
                        (alen1 'dag-array dag-array))
                 (or (null dag)
                     (pseudo-dagp dag))
                 (<= (len dag) dag-len)
                 (bounded-context-arrayp 'context-array context-array dag-len dag-len)
                 (or (null max-conflicts)
                     (natp max-conflicts))
                 (consp dag))
            (mv-let (erp new-dag state)
              (prune-dag-approximately-aux dag dag-array dag-len dag-parent-array context-array print max-conflicts nil state)
              (declare (ignore state))
              (implies (not erp)
                       (pseudo-dagp new-dag))))
   :hints (("Goal" :use (prune-dag-approximately-aux-return-type-special
                         (:instance pseudo-dagp-aux-of-top-nodenum-of-dag-when-weak-dagp-aux-and-cars-decreasing-by-1
                                    (dag (mv-nth 1 (prune-dag-approximately-aux dag dag-array dag-len dag-parent-array context-array print max-conflicts nil state)))))
            :in-theory (e/d (pseudo-dagp top-nodenum-of-dag) (prune-dag-approximately-aux-return-type-special))))))

(local
 (defthm w-of-mv-nth-2-of-prune-dag-approximately-aux
   (equal (w (mv-nth 2 (prune-dag-approximately-aux dag dag-array dag-len dag-parent-array context-array print max-conflicts dag-acc state)))
          (w state))
   :hints (("Goal" :in-theory (enable prune-dag-approximately-aux)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp dag-or-quotep state).
;; Smashes the arrays named 'dag-array, 'temp-dag-array, and 'context-array.
;; todo: may need multiple passes, but watch for loops!
(defund prune-dag-approximately (dag
                                 ;; assumptions
                                 ;; rules ; todo: add support for this
                                 ;; interpreted-fns
                                 ;; monitored-rules
                                 ;;call-stp
                                 check-fnsp ; whether to check for prunable functions
                                 print
                                 state)
  (declare (xargs :guard (and (pseudo-dagp dag)
                              (<= (len dag) *max-1d-array-length*)
                              ;; (pseudo-term-listp assumptions)
                              ;; (symbol-listp rules)
                              ;; (symbol-listp interpreted-fns)
                              ;; (symbol-listp monitored-rules)
                              ;; (or (booleanp call-stp)
                              ;;     (natp call-stp))
                              (booleanp check-fnsp)
                              (print-levelp print)
                              (ilks-plist-worldp (w state)))
                  :guard-hints (("Goal" :in-theory (enable car-of-car-when-pseudo-dagp)))
                  :stobjs state))
  (b* ((prunep (if check-fnsp (dag-fns-include-any dag '(if myif boolif bvif)) t))
       ((when (not prunep))
        (cw "(Note: No pruning to do.)~%")
        (mv nil dag state))
       (- (cw "(Pruning DAG with approximate contexts:~%"))
       ((mv start-real-time state) (get-real-time state)) ; we use wall-clock time so that time in STP is counted
       (context-array (make-full-context-array-for-dag dag))
       (dag-array (make-into-array 'dag-array dag))
       (dag-len (+ 1 (top-nodenum-of-dag dag)))
       (dag-parent-array (make-dag-parent-array-with-name2 dag-len 'dag-array dag-array 'dag-parent-array))
       ((mv erp dag state)
        (prune-dag-approximately-aux dag dag-array dag-len dag-parent-array context-array
                                     print
                                     60000     ;todo max-conflicts
                                     nil       ; dag-acc
                                     state))
       ((when erp) (mv erp nil state))
       ;; Ensure we can continue with the processing below:
       ((when (> (top-nodenum-of-dag dag) *max-1d-array-index*)) (mv :dag-too-big nil state))
       ;; There may be orphan nodes if some pruning was done:
       (dag-or-quotep (drop-non-supporters dag))
       ((when (quotep dag-or-quotep)) (mv (erp-nil) dag-or-quotep state))
       (dag dag-or-quotep) ; it's not a quotep
       ;; Get rid of any calls to ID that got introduced during pruning (TODO: skip if there were none):
       ;; Similarly, try to get rid of calls of BOOL-FIX$INLINE that got introduced.
       ;; And try to propagate successful resolution of tests upward in the DAG.
       ((mv erp rule-alist) (make-rule-alist (prune-dag-post-rewrite-rules)
                                             (w state)))
       ((when erp) (mv erp nil state))
       ((mv erp dag-or-quotep) (simplify-dag-basic dag
                                                   nil ; assumptions
                                                   nil ; interpreted-function-alist
                                                   nil ; limits
                                                   rule-alist
                                                   nil ; count-hits
                                                   nil ; print
                                                   (acl2::known-booleans (w state))
                                                   nil ; monitored-symbols
                                                   nil ; fns-to-elide
                                                   nil ; normalize-xors
                                                   nil ; memoize
                                                   ))
       ((when erp) (mv erp nil state))
       ((mv elapsed state) (real-time-since start-real-time state))
       (- (cw "Done pruning DAG (")
          (print-to-hundredths elapsed) ; todo: could have real-time-since detect negative time
          (cw "s.))~%")))
    (mv (erp-nil) dag-or-quotep state)))

;; Returns (mv erp dag-or-quotep state).
(defund maybe-prune-dag-approximately (prune-branches dag print state)
  (declare (xargs :guard (and (or (booleanp prune-branches)
                                  (natp prune-branches))
                              (pseudo-dagp dag)
                              (<= (len dag) *max-1d-array-length*)
                              (print-levelp print)
                              (ilks-plist-worldp (w state)))
                  :stobjs state))
  (b* (((when (not prune-branches))
        ;; don't even print anything in this case, as we've been told not to prune
        (mv nil dag state))
       ((when (not (dag-fns-include-any dag '(if myif boolif bvif))))
        (cw "(Note: No pruning to do.)~%")
        (mv nil dag state))
       ((when (and (natp prune-branches) ; it's a limit on the size
                   ;; todo: allow this to fail fast:
                   (not (dag-or-quotep-size-less-thanp dag prune-branches))))
        ;; todo: don't recompute the size here:
        (cw "(Note: Not pruning with approximate contexts since DAG size (~x0) exceeds ~x1.)~%" (dag-or-quotep-size-fast dag) prune-branches)
        (mv nil dag state)))
    ;; prune-branches is either t or is a size limit and the dag is small enough, so we prune:
    (prune-dag-approximately dag
                             nil ; we already know there are prunable ops
                             print
                             state)))
