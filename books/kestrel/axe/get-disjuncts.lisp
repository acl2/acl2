; Supporting utilities for the Axe Prover(s)
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

(include-book "kestrel/booleans/booland" :dir :system) ;; since this tool knows about booland
(include-book "kestrel/booleans/boolor" :dir :system) ;; since this tool knows about boolor
(include-book "dag-array-builders")
(include-book "def-dag-builder-theorems")
(include-book "kestrel/utilities/forms" :dir :system) ; for call-of
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/no-duplicatesp-equal" :dir :system))

;; Returns (mv erp provedp extended-acc dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist).
;; When NEGATED-FLG is nil, EXTENDED-ACC is ACC extended with the disjuncts of ITEM, except that if a true disjunct is found, we signal it by returning T for PROVEDP.
;; When NEGATED-FLG is t, EXTENDED-ACC is ACC extended with the negations of the conjuncts of ITEM, except that if any of the negated conjuncts is true, we signal it by returning T for PROVEDP.
;; Throughout, we maintain IFF-equivalence but not necessarily equality.
;; This may extend the dag, since some of the disjuncts may not already exist in the dag (ex: for (not (booland x y)), the disjuncts are (not x) and (not y), and these may not exist in the dag).
;; TODO: In theory this could blow up due to shared structure, but I haven't seen that happen.
;ffixme handle non-predicates (in which case we'll have an if nest, not a boolor nest)?
(defund get-darg-disjuncts (item dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist acc negated-flg print)
  (declare (xargs :guard (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                              (dargp-less-than item dag-len)
                              (nat-listp acc)
                              (booleanp negated-flg))
                  :measure (if (consp item)
                               0
                             (+ 1 (nfix item)))
                  :hints (("Goal" :in-theory (enable car-becomes-nth-of-0)))
                  :verify-guards nil ; done below
                  ))
  ;; drop this check?
  (if (not (mbt (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                     (dargp-less-than item dag-len))))
      (mv (erp-t)
          nil
          (er hard 'get-darg-disjuncts "Bad inputs (this should not happen).")
          dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
    (if (not negated-flg)
        ;; The negated-flag is nil, so we are returning disjuncts of ITEM:
        (if (consp item) ;test for quotep
            (if (unquote item)
                ;; A non-nil constant proves the clause:
                (mv (erp-nil)
                    t   ; provedp
                    nil ; meaningless
                    dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
              ;; A nil constant gets dropped:
              (prog2$ (and print (cw "NOTE: Dropping nil disjunct.~%"))
                      (mv (erp-nil)
                          nil ;provedp
                          acc ; not extended
                          dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))
          (let ((expr (aref1 'dag-array dag-array item)))
            (if (variablep expr)
                ;; Can't get disjuncts from a variable:
                (mv (erp-nil)
                    nil ; provedp
                    (add-to-set-eql item acc)
                    dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
              (let ((fn (ffn-symb expr)))
                ;;todo: handle fn=quote ?
                (case fn
                  (boolor (if (not (= 2 (len (dargs expr))))
                              (prog2$ (er hard? 'get-darg-disjuncts "Bad arity for BOOLOR.")
                                      (mv :bad-arity nil nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
                            ;; it is a boolor, so get disjuncts from the arguments:
                            (b* (((mv erp provedp acc dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                                  ;;todo: why do we handle arg2 first?
                                  ;; TODO: Should this call be the tail call?
                                  (get-darg-disjuncts (darg2 expr) dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                 acc
                                                 nil ;negated-flg
                                                 print
                                                 ))
                                 ((when erp) (mv erp nil nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
                                 ((when provedp) (mv (erp-nil) t nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))
                              (get-darg-disjuncts (darg1 expr) dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                             acc ; has been extended for darg2
                                             nil ; negated-flg
                                             print
                                             ))))
                  (if (if (not (= 3 (len (dargs expr))))
                          (prog2$ (er hard? 'get-darg-disjuncts "Bad arity for IF.")
                                  (mv :bad-arity nil nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
                        (if (equal (darg1 expr) (darg2 expr))
                            ;; (if x x y) is just (or x and y), so get disjuncts from the arguments:
                            (b* (((mv erp provedp acc dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                                  (get-darg-disjuncts (darg1 expr) dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                 acc
                                                 nil ;negated-flg
                                                 print
                                                 ))
                                 ((when erp) (mv erp nil nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
                                 ((when provedp) (mv (erp-nil) t nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))
                              (get-darg-disjuncts (darg3 expr) dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                             acc ; has been extended for darg1
                                             nil ; negated-flg
                                             print
                                             ))
                          ;; TODO: Handle more cases of if, such as (if x t y)
                          (mv (erp-nil)
                              nil ; provedp
                              (add-to-set-eql item acc)
                              dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
                  (not (if (not (= 1 (len (dargs expr))))
                           (prog2$ (er hard? 'get-darg-disjuncts "Bad arity for NOT.")
                                   (mv :bad-arity nil nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
                         ;; EXPR is a call of not, so we can view it as (not (and x1 x2 ... xn)), which is the same as (or (not
                         ;; x1) (not x2) ... (not xn)).  So, to get EXPR's disjuncts, we extract x1 through xn and then negate
                         ;; them all.  That is, we get the negated conjuncts of the argument of the NOT.
                         (get-darg-disjuncts (darg1 expr) dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist acc
                                        t ; negated-flg
                                        print
                                        )))
                  (implies (if (not (= 2 (len (dargs expr))))
                               (prog2$ (er hard? 'get-darg-disjuncts "Bad arity for IMPLIES.")
                                       (mv :bad-arity nil nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
                             ;; EXPR is (implies <x> <y>), which is the same as (or (not <x>) <y>), so its disjuncts
                             ;; are the disjuncts of (not <x>) [see above case for NOT], together with the disjuncts of
                             ;; y:
                             (b* (((mv erp provedp acc dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                                   ;;todo: why do we handle arg2 first?
                                   (get-darg-disjuncts (darg1 expr) dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                  acc
                                                  t ; negated-flg
                                                  print
                                                  ))
                                  ((when erp) (mv erp nil nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
                                  ((when provedp) (mv (erp-nil) t nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))
                               (get-darg-disjuncts (darg2 expr) dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                              acc ; has been extended for darg1
                                              nil ;negated-flg
                                              print
                                              ))))
                  (t ;;it's not something we know how to get disjuncts from:
                   (mv (erp-nil)
                       nil ; provedp
                       (add-to-set-eql item acc)
                       dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))))))
      ;; The negated-flag is t, so we are returning the negations of the conjuncts of ITEM:
      (if (consp item) ;test for quotep
          (if (unquote item)
              ;; A non-nil constant gets dropped, since we are to negate all conjuncts
              (mv (erp-nil)
                  nil ;provedp
                  acc
                  dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
            ;; A nil constant proves the clause, since we are to negate all conjuncts
            (mv (erp-nil)
                t   ; provedp
                nil ; meaningless
                dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
        (let ((expr (aref1 'dag-array dag-array item)))
          (if (variablep expr)
              ;; Can't get negated conjuncts from a variable, so add its negation and return the item:
              (mv-let (erp negated-nodenum dag-array dag-len dag-parent-array dag-constant-alist)
                (add-function-call-expr-to-dag-array2 'not (list item) dag-array dag-len dag-parent-array dag-constant-alist)
                (mv erp
                    nil                                  ; provedp
                    (add-to-set-eql negated-nodenum acc) ;meaningless if erp is t.
                    dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
            (let ((fn (ffn-symb expr)))
              (case fn
                ;;todo: handle fn=quote ?
                (booland (if (not (= 2 (len (dargs expr))))
                             (prog2$ (er hard? 'get-darg-disjuncts "Bad arity for BOOLAND.")
                                     (mv :bad-arity nil nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
                           ;; To get the negated conjuncts of a booland, we get the negated conjuncts from the arguments and union the results:
                           (b* (((mv erp provedp acc dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                                 ;; TODO: Why do we process arg2 first?
                                 (get-darg-disjuncts (darg2 expr) dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist acc
                                                t ;negated-flg
                                                print))
                                ((when erp) (mv erp nil nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
                                ((when provedp) (mv (erp-nil) t nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))
                             (get-darg-disjuncts (darg1 expr) dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                            acc ; has been extended for darg2
                                            t   ;negated-flg
                                            print))))
                (if (if (not (= 3 (len (dargs expr))))
                        (prog2$ (er hard? 'get-darg-disjuncts "Bad arity for IF.")
                                (mv :bad-arity nil nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
                      ;; Treat (if x y nil) as (and x y)
                      (if (equal (darg3 expr) *nil*)
                          ;; To get the negated conjuncts of an AND, we get the negated conjuncts from the arguments and union the results:
                          (b* (((mv erp provedp acc dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                                (get-darg-disjuncts (darg1 expr) dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist acc
                                               t ;negated-flg
                                               print))
                               ((when erp) (mv erp nil nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
                               ((when provedp) (mv (erp-nil) t nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))
                            (get-darg-disjuncts (darg2 expr) dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                           acc ; has been extended for darg1
                                           t   ;negated-flg
                                           print))
                        ;; TODO: Handle any other kinds of IF?
                        ;;it's not something we know how to get negated conjuncts from, so add its negation and return the item:
                        (mv-let (erp negated-nodenum dag-array dag-len dag-parent-array dag-constant-alist)
                          (add-function-call-expr-to-dag-array2 'not (list item) dag-array dag-len dag-parent-array dag-constant-alist)
                          (mv erp
                              nil                                  ; provedp
                              (add-to-set-eql negated-nodenum acc) ;meaningless if erp is t.
                              dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))))
                (not (if (not (= 1 (len (dargs expr))))
                         (prog2$ (er hard? 'get-darg-disjuncts "Bad arity for NOT.")
                                 (mv :bad-arity nil nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
                       ;; EXPR is a call of NOT, so we can view it as (not (or x1 x2 ... xn)), which is the same as (and (not
                       ;; x1) (not x2) ... (not xn)).  So, to get EXPR's *negated* conjuncts, we just get x1 through xn
                       ;; (removing double negations), which are the disjuncts the argument to the NOT.
                       (get-darg-disjuncts (darg1 expr) dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist acc
                                      nil ;;negated-flg
                                      print)))
                (t ;;it's not something we know how to get negated conjuncts from, so add its negation and return the item:
                 (mv-let (erp negated-nodenum dag-array dag-len dag-parent-array dag-constant-alist)
                   (add-function-call-expr-to-dag-array2 'not (list item) dag-array dag-len dag-parent-array dag-constant-alist)
                   (mv erp
                       nil                                      ; provedp
                       (add-to-set-eql negated-nodenum acc) ;meaningless if erp is t.
                       dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))))))))))

;; (mv-let (erp nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
;;   (make-term-into-dag-array-basic '(booland x y) 'dag-array-name 'dag-parent-array-name nil)
;;   (declare (ignore erp))
;;   (get-darg-disjuncts nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist nil t print))

(def-dag-builder-theorems
  (get-darg-disjuncts item dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist acc negated-flg print)
  (mv erp
      provedp ;todo: when this was missing, def-dag-builder-theorems did now throw a nice error
      disjuncts dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))

;; The disjuncts are always nodenums.
(defthm nat-listp-of-mv-nth-2-of-get-darg-disjuncts
  (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (dargp-less-than item dag-len)
                (nat-listp acc))
           (nat-listp (mv-nth 2 (get-darg-disjuncts item dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist acc negated-flg print))))
  :hints (("Goal" :in-theory (e/d (get-darg-disjuncts) (natp)))))

(verify-guards get-darg-disjuncts :hints (("Goal" :in-theory (e/d (car-becomes-nth-of-0) (natp)))))

(defthm true-listp-of-mv-nth-2-of-get-darg-disjuncts
  (implies (true-listp acc)
           (true-listp (mv-nth 2 (get-darg-disjuncts item dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist acc negated-flg print))))
  :hints (("Goal" :in-theory (e/d (get-darg-disjuncts) (natp)))))

(defthm all-<-of-mv-nth-2-of-get-darg-disjuncts
  (implies  (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                 (dargp-less-than item dag-len)
                 (nat-listp acc)
                 (all-< acc dag-len)
                 (not (mv-nth 0 (get-darg-disjuncts item dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist acc negated-flg print))))
            (all-< (mv-nth 2 (get-darg-disjuncts item dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist acc negated-flg print))
                   (mv-nth 4 (get-darg-disjuncts item dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist acc negated-flg print))))
  :hints (("Goal" :in-theory (e/d (get-darg-disjuncts CAR-BECOMES-NTH-OF-0) (natp)))))

(defthm no-duplicatesp-equal-of-mv-nth-2-of-get-darg-disjuncts
  (implies (no-duplicatesp-equal acc)
           (no-duplicatesp-equal (mv-nth 2 (get-darg-disjuncts item dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist acc negated-flg print))))
  :hints (("Goal" :in-theory (e/d (get-darg-disjuncts) (natp)))))

;; Extends ACC with nodenums whose disjunction is equivalent to the disjunction of the NODENUMS.
;; Returns (mv erp provedp extended-acc dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist).
(defund get-disjuncts-from-nodes (nodenums ;todo: we could now allow constants
                                  dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                  acc
                                  print)
  (declare (xargs :guard (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                              (nat-listp nodenums)
                              (all-< nodenums dag-len)
                              (nat-listp acc)
                              (all-< acc dag-len))
;                  :hints (("Goal" :in-theory (enable car-becomes-nth-of-0)))
                  ))
  (if (endp nodenums)
      ;; I suppose we could skip the reverse here:
      (mv (erp-nil)
          nil ;provedp
          (reverse acc)
          dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
    (b* ( ;; todo add handling of constant disjuncts, currently not returned by get-darg-disjuncts
         ((mv erp provedp acc dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
          (get-darg-disjuncts (first nodenums)
                         dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                         acc ; will be extended
                         nil ; negated-flg
                         print
                         ))
         ((when erp) (mv erp nil nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
         ((when provedp) (mv (erp-nil) t nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))
      (get-disjuncts-from-nodes (rest nodenums) dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist acc print))))

(def-dag-builder-theorems
  (get-disjuncts-from-nodes nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist acc print)
  (mv erp provedp extended-acc dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))

(defthm get-disjuncts-from-nodes-of-nil
  (equal (get-disjuncts-from-nodes nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist acc print)
         (mv (erp-nil)
             nil ;provedp
             (reverse acc)
             dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
  :hints (("Goal" :in-theory (enable get-disjuncts-from-nodes))))

(defthm no-duplicatesp-equal-of-mv-nth-2-of-get-disjuncts-from-nodes
  (implies (no-duplicatesp-equal acc)
           (no-duplicatesp-equal (mv-nth 2 (get-disjuncts-from-nodes nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist acc print))))
  :hints (("Goal" :in-theory (e/d (get-disjuncts-from-nodes) (natp)))))

;move
(local
 (defthm nat-listp-of-append
   (equal (nat-listp (append x y))
          (and (nat-listp (true-list-fix x))
               (nat-listp y)))
   :hints (("Goal" :in-theory (enable nat-listp reverse-list)))))

;move
(local
 (defthm nat-listp-of-reverse-list
   (equal (nat-listp (reverse-list x))
          (nat-listp (true-list-fix x)))
   :hints (("Goal" :in-theory (enable nat-listp reverse-list)))))

;; The disjuncts are always nodenums.
(defthm nat-listp-of-mv-nth-2-of-get-disjuncts-from-nodes
  (implies  (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                 (nat-listp nodenums)
                 (all-< nodenums dag-len)
                 (nat-listp acc)
                 (all-< acc dag-len))
            (nat-listp (mv-nth 2 (get-disjuncts-from-nodes nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist acc print))))
  :hints (("Goal" :in-theory (e/d (get-disjuncts-from-nodes) (natp)))))

(defthm all-<-of-mv-nth-2-of-get-disjuncts-from-nodes
  (implies  (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                 (nat-listp nodenums)
                 (all-< nodenums dag-len)
                 (nat-listp acc)
                 (all-< acc dag-len))
            (all-< (mv-nth 2 (get-disjuncts-from-nodes nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist acc print))
                   (mv-nth 4 (get-disjuncts-from-nodes nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist acc print))))
  :hints (("Goal" :in-theory (e/d (get-disjuncts-from-nodes) (natp)))))

(defthm true-listp-of-mv-nth-2-of-get-disjuncts-from-nodes
  (implies (true-listp acc)
           (true-listp (mv-nth 2 (get-disjuncts-from-nodes nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist acc print))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (e/d (get-disjuncts-from-nodes) (natp)))))

(defthm <=-of-mv-nth-4-of-get-disjuncts-from-nodes
  (implies  (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                 (nat-listp nodenums)
                 (all-< nodenums dag-len)
                 (nat-listp acc)
                 (all-< acc dag-len))
            (<= dag-len
                (mv-nth 4 (get-disjuncts-from-nodes nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist acc print))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (e/d (get-disjuncts-from-nodes) (natp)))))

(defthm <-of-0-and-mv-nth-4-of-get-disjuncts-from-nodes
  (implies  (and (consp nodenums) ; implies (< 0 dag-len)
                 (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                 (nat-listp nodenums)
                 (all-< nodenums dag-len)
                 (nat-listp acc)
                 (all-< acc dag-len))
            (< 0
                (mv-nth 4 (get-disjuncts-from-nodes nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist acc print))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (e/d (get-disjuncts-from-nodes) (natp)))))




;can be used to test get-disjuncts:
;; (defun get-disjuncts-of-term (term)
;;   (let* ((dag-lst (dagify-term term))
;;          (dag-len (len dag-lst))
;;          (dag-array (MAKE-INTO-ARRAY 'dag-array dag-lst)))
;;     (mv-let (dag-parent-array dag-constant-alist dag-variable-alist)
;;             (make-dag-indices 'dag-array dag-array 'dag-parent-array dag-len)
;;             (mv-let (disjuncts dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
;;                     (get-disjuncts (+ -1 dag-len) dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist nil nil)
;;                     (declare (ignore dag-len dag-parent-array dag-constant-alist dag-variable-alist))
;;                     (list disjuncts dag-array)))))
;; ex: (GET-DISJUNCTS-OF-TERM '(boolor w (not (booland x (not (boolor y z))))))
