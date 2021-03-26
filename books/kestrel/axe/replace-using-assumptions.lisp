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

(include-book "kestrel/utilities/forms" :dir :system) ; for call-of
(include-book "dag-arrays")
(include-book "axe-trees")
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "numeric-lists"))

;x must be a nodenum or quotep:
;(defmacro isconstant (x) `(consp ,x))

 ;can we deprecate this?  or split for var terms and all others - could just add term to the dag and use the main routine
;do we need both this and the version for a nodenum?
;"term" is either a variable or a function applied to a list of constants and nodenums
;looks for a nodenum-to-assume-false that points to:
; term -- rewrite term to false
; (not term) -- rewrite term to t, if term is a call of a known-predicate (fixme we could try to prove that it's a boolean - what if we have that as a hyp?)
; (not (equal new-nodenum-or-quotep term)) - rewrite term to the new term
;fixme more generally, if we have a hyp of (booleanp term) we can safely rewrite term in an iff context everywhere?
;equiv is 'equal or 'iff (or nil, which means equal) for now
;; Returns a nodenum or quotep, or nil to indicate failure.
;ffixme this should not fail if it's trying to use an equality we've already decided to substitute and drop..
;perhaps term is always either a var of a fn-call applied to nodenums and quoteps
;todo: rename term to tree in the param and this function's name:
(defund replace-term-using-assumptions-for-axe-prover (term equiv nodenums-to-assume-false dag-array print)
  (declare (xargs :guard (and (axe-treep term)
                              (symbolp equiv)
                              (all-natp nodenums-to-assume-false)
                              (true-listp nodenums-to-assume-false)
                              (if (consp nodenums-to-assume-false)
                                  (pseudo-dag-arrayp 'dag-array dag-array (+ 1 (maxelem nodenums-to-assume-false)))
                                t))
                  :guard-hints (("Goal" :in-theory (e/d (CAR-BECOMES-NTH-OF-0) (natp))))))
  (if (endp nodenums-to-assume-false)
      nil ;; failed to rewrite TERM
    (let* ((nodenum-to-assume-false (first nodenums-to-assume-false))
           (expr-to-assume-false (aref1 'dag-array dag-array nodenum-to-assume-false)))
      (if (equal term expr-to-assume-false)
          *nil* ; TERM can be safely assumed false
        (if (not (and (call-of 'not expr-to-assume-false)
                      (= 1 (len (dargs expr-to-assume-false)))
                      (atom (darg1 expr-to-assume-false))))
            (replace-term-using-assumptions-for-axe-prover term equiv (rest nodenums-to-assume-false) dag-array print)
          ;; EXPR-TO-ASSUME-FALSE is of the form (not <nodenum>):
          (let ((non-nil-expr (aref1 'dag-array dag-array (darg1 expr-to-assume-false))))
            (if (and (eq equiv 'iff)
                     (equal term non-nil-expr) ;fffixme allow the equal to be weaker?  huh?
;                     (consp term) ;fixme move up so we don't retest this?
;                    (member-eq (ffn-symb term) *known-predicates-jvm*) ;move up?
;fixme what if we have a hyp that says that term is a boolean?
                     )
                *t* ;since it's assumed non-nil and we only have to preserve iff, it's t
              (if (not (and (call-of 'equal non-nil-expr)
                            (= 2 (len (dargs non-nil-expr)))
                            (atom (darg2 non-nil-expr))))
                  (replace-term-using-assumptions-for-axe-prover term equiv (rest nodenums-to-assume-false) dag-array print)
                ;; this is consistent with what we've been doing all along (turning equalities around to bring the smaller term to the left)
                (if (and (equal term (aref1 'dag-array dag-array (darg2 non-nil-expr))) ;fixme allow the equal to be weaker?
                         ;; NON-NIL-EXPR is of the form (equal <thing> <nodenum-of-term>)
                         ;;recall that equalities now rewrite the term on the right to the term on the left (the smaller term)

                         ;;(quotep (darg1 non-nil-expr))  ;;new! ;Sun Feb 14 12:33:01 2010 ;fffixme allow vars?  keep this in sync with the code that decides whether to substitute?
                         ;;fixme maybe the protection against looping should go right here?
                         ;; how should we prevent loops?  what if we have (equal <x> <y>) <x> would rewriter back to <y> in the context in which <y> appears?
;new Mon Mar 29 09:48:23 2010:
                         (if (quotep (darg1 non-nil-expr))
                             t ;always put a quotep in
                           nil ;Sun May 15 21:49:00 2011
                           ;;                            (if (variablep (aref1 'dag-array dag-array (darg1 non-nil-expr)))
                           ;;                                nil ;don't put a variable back in
                           ;;                              (variablep term) ;nil ;Wed Mar 31 08:32:09 2010  ;fixme wait until substitute-a-var?  can this loop if term (a variable) is equated to something invcluding itself?
                           ;; ;;                              (or (simpler-dag-termp2 (darg1 non-nil-expr) term dag-array) ;fffixme gotta fix this up to take a term
                           ;; ;;                                  (and (variablep term)
                           ;; ;;                                       (not (member nodenum ;fffixme gotta fix this up to take a term
                           ;; ;;                                                    (supporters-of-node (darg1 non-nil-expr) 'dag-array dag-array 'tag-array-for-supporters)))))
                           ;;                              )
                           ))
                    (prog2$ (and (eq :verbose print)
                                 (cw "Putting in ~x0 for term ~x1.~%" (darg1 non-nil-expr) term))
                            (darg1 non-nil-expr))
                  (replace-term-using-assumptions-for-axe-prover term equiv (rest nodenums-to-assume-false) dag-array print))))))))))

(defthm replace-term-using-assumptions-for-axe-prover-forward-to-consp
  (implies (replace-term-using-assumptions-for-axe-prover term equiv nodenums-to-assume-false dag-array print)
           (consp nodenums-to-assume-false))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable replace-term-using-assumptions-for-axe-prover))))

(defthm dargp-less-than-of-replace-term-using-assumptions-for-axe-prover
  (implies (and (replace-term-using-assumptions-for-axe-prover var equiv nodenums-to-assume-false dag-array print) ;no failure
                (all-natp nodenums-to-assume-false)
                (if (consp nodenums-to-assume-false)
                    (pseudo-dag-arrayp 'dag-array dag-array (+ 1 (maxelem nodenums-to-assume-false)))
                  t)
                (all-< nodenums-to-assume-false dag-len))
           (dargp-less-than (replace-term-using-assumptions-for-axe-prover var equiv nodenums-to-assume-false dag-array print) dag-len))
  :hints (("Goal" :in-theory (e/d (replace-term-using-assumptions-for-axe-prover car-becomes-nth-of-0)
                                  (myquotep)))))

;todo: in fact, it's always a quotep !
;; (defthm dargp-of-replace-term-using-assumptions-for-axe-prover
;;   (implies (and (replace-term-using-assumptions-for-axe-prover term equiv nodenums-to-assume-false dag-array print)
;;                 (axe-treep term)
;;                 (symbolp equiv)
;;                 (all-natp nodenums-to-assume-false)
;;                 (true-listp nodenums-to-assume-false)
;;                 ;; (if (consp nodenums-to-assume-false)
;;                 ;;     (pseudo-dag-arrayp 'dag-array dag-array (+ 1 (maxelem nodenums-to-assume-false)))
;;                 ;;   t)
;;                 )
;;            (dargp (replace-term-using-assumptions-for-axe-prover term equiv nodenums-to-assume-false dag-array print)))
;;   :hints (("Goal" :in-theory (e/d (replace-term-using-assumptions-for-axe-prover) (dargp)))))


;; Tries to replace NODENUM (current only with a constant) using facts known
;; from the NODENUMS-TO-ASSUME-FALSE.  The result is related to NODENUM by the
;; EQUIV passed in ('equal or 'iff).
;; Returns a quotep, or nil to indicate failure.  May some day be allowed to return a nodenum.
;; TODO: To speed this up, we could separately track nodenums to assume false and nodenums to assume true (non-nil).
;; TODO: To speed this up, we could perhaps index the known true/false facts by top function-symbol.
;; TODO: To speed this up, we could perhaps maintain this information as node-replacement pairs, perhaps even in an array.
;; If there are multiple matches, the first one will fire, even if later ones might be better.
(defund replace-nodenum-using-assumptions-for-axe-prover (nodenum
                                                          equiv ;todo: perhaps pass in an iff-flag
                                                          nodenums-to-assume-false
                                                          dag-array)
  (declare (xargs :guard (and (natp nodenum)
                              (symbolp equiv)
                              (all-natp nodenums-to-assume-false)
                              (true-listp nodenums-to-assume-false)
                              (pseudo-dag-arrayp 'dag-array dag-array (+ 1 (maxelem (cons nodenum nodenums-to-assume-false)))))
                  :guard-hints (("Goal"
                                 :use ((:instance true-listp-of-dargs-of-aref1-when-pseudo-dag-arrayp-simple
                                                  (dag-array-name 'dag-array)
                                                  (n (nth 0 nodenums-to-assume-false)))
                                       (:instance true-listp-of-dargs-of-aref1-when-pseudo-dag-arrayp-simple
                                                  (dag-array-name 'dag-array)
                                                  (n (nth 0 (dargs (aref1 'dag-array dag-array (nth 0 nodenums-to-assume-false)))))))
                                 :in-theory (e/d (car-becomes-nth-of-0
                                                  NATP-OF-+-OF-1)
                                                 (natp
                                                  true-listp-of-dargs-of-aref1-when-pseudo-dag-arrayp
                                                  true-listp-of-dargs-of-aref1-when-pseudo-dag-arrayp-simple))))))
  (if (endp nodenums-to-assume-false)
      nil ;; failure to rewrite NODENUM
    (let* ((nodenum-to-assume-false (first nodenums-to-assume-false)))
      (if (eql nodenum nodenum-to-assume-false) ; could do (member nodenum nodenums-to-assume-false) in a wrapper function
          ;; NODENUM is among the NODENUMS-TO-ASSUME-FALSE, so we replace it with 'nil:
          *nil*
        (let* ((expr-to-assume-false (aref1 'dag-array dag-array nodenum-to-assume-false)))
          (if (not (and (call-of 'not expr-to-assume-false)
                        (consp (dargs expr-to-assume-false))
                        ;; (not (consp (rest (dargs expr-to-assume-false)))) ;todo: think about bad arities
                        (atom (darg1 expr-to-assume-false)) ;makes sure it's a nodenum
                        ))
              ;; expr-to-assume-false does not have a form we can use, so keep looking:
              (replace-nodenum-using-assumptions-for-axe-prover nodenum equiv (rest nodenums-to-assume-false) dag-array)
            ;; EXPR-TO-ASSUME-FALSE is of the form (not <nodenum-to-assume-non-nil>):
            (let ((nodenum-to-assume-non-nil (darg1 expr-to-assume-false)))
              (if (and (eql nodenum nodenum-to-assume-non-nil)
                       (eq 'iff equiv))
                  ;; NODENUM is equal to NODENUM-TO-ASSUME-NON-NIL, and since we only must preserve IFF, we can replace
                  ;; it with 't: TODO: If nodenum is the nodenum of a boolean (either because of the ffn-symb or because
                  ;; we have a hyp to that effect?), we could replace it with *t* even if the equiv is 'equal:
                  *t*
                (let ((expr-to-assume-non-nil (aref1 'dag-array dag-array nodenum-to-assume-non-nil)))
                  (if (not (and (call-of 'equal expr-to-assume-non-nil)
                                ;;(= 2 (len (dargs expr-to-assume-non-nil)))
                                (consp (rest (dargs expr-to-assume-non-nil))) ;todo: think about bad arities
                                ))
                      ;; expr-to-assume-non-nil does not have a form we can use, so keep looking:
                      (replace-nodenum-using-assumptions-for-axe-prover nodenum equiv (rest nodenums-to-assume-false) dag-array)
                    (let ((darg1 (darg1 expr-to-assume-non-nil))
                          (darg2 (darg2 expr-to-assume-non-nil)))
                      (if (and (eql nodenum darg2)
                               ;; expr-to-assume-non-nil is of the form (equal <thing> NODENUM):
                               ;; note the order: equalities fire right-to-left, since the small thing is put first
                               (consp darg1) ;; check for quotep
                               ;; (if (quotep darg1)
                               ;;     t ;always put a constant in
                               ;;   ;;thing is a nodenum:
                               ;;   nil ;Sun May 15 18:35:43 2011
                               ;;   ;; (if (variablep (aref1 'dag-array dag-array thing))
                               ;;   ;;     nil ;don't put a variable back in... (or can we order the variables???)
                               ;;   ;;   (or nil ;(simpler-dag-termp thing nodenum dag-array) ;fixme do we always want to do this?  fixme is this known from how the equality is ordered? ;can this loop?
                               ;;   ;;       (and (variablep (aref1 'dag-array dag-array nodenum)) ;don't test this over and over?  or we could wait until substitute-a-var?
                               ;;   ;;            (not (member nodenum (supporters-of-node thing 'dag-array dag-array 'tag-array-for-supporters))))
                               ;;   ;;       ))
                               ;;   )
                               ) ;expensive?!
                          ;; ffixme, don't do this when the assumptions haven't yet been simplified? can lead to loops!
                          (progn$ ;; (and (eq :verbose print) (cw "Putting in ~x0 for node ~x1.~%" (darg1 expr-to-assume-non-nil) nodenum))
                           darg1)
                        ;;this whole case is new (FFIXME this violates the rule about equalities firing from right to left):
                        ;;fixme keep this in sync with the stuff above...
                        (if (and (eql nodenum darg1)
                                 (consp darg2) ;; check for quotep
                                 ;; ;; expr-to-assume-non-nil is of the form (equal NODENUM <thing>):
                                 ;; (let ((thing (darg2 expr-to-assume-non-nil)))
                                 ;;   (if (quotep thing)
                                 ;;       t ;always put a quotep in
                                 ;;     nil ;Sun May 15 18:35:52 2011
                                 ;;     ;; (if (variablep (aref1 'dag-array dag-array thing))
                                 ;;     ;;     nil ;don't put a variable back in...
                                 ;;     ;;   (or nil ;(simpler-dag-termp thing nodenum dag-array)
                                 ;;     ;;       (and (variablep (aref1 'dag-array dag-array nodenum))
                                 ;;     ;;            (not (member nodenum (supporters-of-node thing 'dag-array dag-array 'tag-array-for-supporters))))))
                                 ;;     ))
                                 )
                            ;; ffixme, don't do this when the assumptions haven't yet been simplified? can lead to loops!
                            (progn$ ;; (and (eq :verbose print) (cw "Putting in ~x0 for node ~x1.~%" (darg2 expr-to-assume-non-nil) nodenum))
                             darg2)
                          ;; keep looking:
                          (replace-nodenum-using-assumptions-for-axe-prover nodenum equiv (rest nodenums-to-assume-false) dag-array
                                                                            ;;print
                                                                            ))))))))))))))

;; Currently it can only put in a quotep!
(defthm myquotep-of-replace-nodenum-using-assumptions-for-axe-prover
  (implies (and (replace-nodenum-using-assumptions-for-axe-prover nodenum equiv nodenums-to-assume-false dag-array) ;no failure
                (natp nodenum)
                ;;(symbolp equiv)
                (all-natp nodenums-to-assume-false)
                ;;(true-listp nodenums-to-assume-false)
                ;; todo: why is force needed here?:
                (force (pseudo-dag-arrayp 'dag-array dag-array (+ 1 (maxelem (cons nodenum nodenums-to-assume-false))))))
           (myquotep (replace-nodenum-using-assumptions-for-axe-prover nodenum equiv nodenums-to-assume-false dag-array)))
  :hints (("Goal"
           :in-theory (e/d (replace-nodenum-using-assumptions-for-axe-prover
                            car-becomes-nth-of-0
                            NATP-OF-+-OF-1)
                           (natp
                            ;;quotep
                            myquotep
                            ;;MAXELEM-OF-CONS
                            )))))

;; simple consequence needed for proofs about the prover
(defthm axe-treep-of-replace-nodenum-using-assumptions-for-axe-prover
  (implies (and (replace-nodenum-using-assumptions-for-axe-prover nodenum equiv nodenums-to-assume-false dag-array)
                (natp nodenum)
                ;;(symbolp equiv)
                (nat-listp ;all-natp
                 nodenums-to-assume-false)
                ;;(true-listp nodenums-to-assume-false)
                (pseudo-dag-arrayp 'dag-array dag-array (+ 1 nodenum))
                ;; todo: why is force needed here?
                (force (implies (consp nodenums-to-assume-false)
                                (pseudo-dag-arrayp 'dag-array dag-array (+ 1 (maxelem nodenums-to-assume-false))))))
           (axe-treep (replace-nodenum-using-assumptions-for-axe-prover nodenum equiv nodenums-to-assume-false dag-array)))
  :hints (("Goal" :in-theory (disable myquotep axe-treep)
           :use (:instance myquotep-of-replace-nodenum-using-assumptions-for-axe-prover))))

(defthm bounded-axe-treep-of-replace-nodenum-using-assumptions-for-axe-prover
  (implies (and (replace-nodenum-using-assumptions-for-axe-prover nodenum equiv nodenums-to-assume-false dag-array)
                (natp nodenum)
                ;;(symbolp equiv)
                (nat-listp ;all-natp
                 nodenums-to-assume-false)
                ;;(true-listp nodenums-to-assume-false)
                (pseudo-dag-arrayp 'dag-array dag-array (+ 1 nodenum))
                ;; todo: why is force needed here?
                (force (implies (consp nodenums-to-assume-false)
                                (pseudo-dag-arrayp 'dag-array dag-array (+ 1 (maxelem nodenums-to-assume-false))))))
           (bounded-axe-treep (replace-nodenum-using-assumptions-for-axe-prover nodenum equiv nodenums-to-assume-false dag-array) dag-len))
  :hints (("Goal" :use (:instance myquotep-of-replace-nodenum-using-assumptions-for-axe-prover))))

;;Returns a nodenum or quotep.
(defund maybe-replace-nodenum-using-assumptions-for-axe-prover (nodenum equiv
                                                                        nodenums-to-assume-false
                                                                        dag-array)
  (declare (xargs :guard (and (natp nodenum)
                              (symbolp equiv)
                              (all-natp nodenums-to-assume-false)
                              (true-listp nodenums-to-assume-false)
                              (pseudo-dag-arrayp 'dag-array dag-array (+ 1 (maxelem (cons nodenum nodenums-to-assume-false)))))))
  (let ((assumption-match (replace-nodenum-using-assumptions-for-axe-prover nodenum equiv nodenums-to-assume-false dag-array))) ;currently, this can only be a constant?
    (if assumption-match
        ;; we replace the term with something it's equated to in nodenums-to-assume-false (currently can only be a constant). eventually, we might need to think about handling chains of equalities:
        assumption-match
      ;; no change:
      nodenum)))

(defthm dargp-less-than-of-maybe-replace-nodenum-using-assumptions-for-axe-prover
  (implies (and (natp nodenum)
                ;;(symbolp equiv)
                (nat-listp nodenums-to-assume-false)
                (pseudo-dag-arrayp 'dag-array dag-array (+ 1 nodenum))
                ;; todo: is the force needed here?
                (force (implies (consp nodenums-to-assume-false)
                                (pseudo-dag-arrayp 'dag-array dag-array (+ 1 (maxelem nodenums-to-assume-false))))))
           (dargp-less-than (maybe-replace-nodenum-using-assumptions-for-axe-prover nodenum equiv nodenums-to-assume-false dag-array)
                            (+ 1 nodenum)))
  :hints (("Goal" :in-theory (e/d (dargp-less-than maybe-replace-nodenum-using-assumptions-for-axe-prover)
                                  (myquotep-of-replace-nodenum-using-assumptions-for-axe-prover))
           :use (:instance myquotep-of-replace-nodenum-using-assumptions-for-axe-prover))))

(defthm dargp-less-than-of-maybe-replace-nodenum-using-assumptions-for-axe-prover-gen
  (implies (and (< nodenum n)
                (natp n)
                (natp nodenum)
                ;;(symbolp equiv)
                (nat-listp nodenums-to-assume-false)
                (pseudo-dag-arrayp 'dag-array dag-array (+ 1 nodenum))
                ;; todo: is the force needed here?
                (force (implies (consp nodenums-to-assume-false)
                                (pseudo-dag-arrayp 'dag-array dag-array (+ 1 (maxelem nodenums-to-assume-false))))))
           (dargp-less-than (maybe-replace-nodenum-using-assumptions-for-axe-prover nodenum equiv nodenums-to-assume-false dag-array)
                            n))
  :hints (("Goal" :use (:instance dargp-less-than-of-maybe-replace-nodenum-using-assumptions-for-axe-prover)
           :in-theory (disable dargp-less-than-of-maybe-replace-nodenum-using-assumptions-for-axe-prover))))
