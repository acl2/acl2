; Computing a node-replacement-alist from a context
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2016-2021 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "conjunctions-and-disjunctions") ; for possibly-negated-nodenumsp, etc
(include-book "contexts") ; for max-nodenum-in-possibly-negated-nodenums-aux, etc.
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))

;dup in kestrel-acl2/utilities/string-utilities.lisp
(local
 (defthm consp-when-true-listp
  (implies (true-listp x)
           (equal (consp x) (not (equal x nil))))))

;move, dup?
(defthm max-nodenum-in-possibly-negated-nodenums-aux-lower-bound
  (implies (and (possibly-negated-nodenumsp predicates-or-negations)
                (<= -1 acc))
           (<= -1 (max-nodenum-in-possibly-negated-nodenums-aux predicates-or-negations acc)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable max-nodenum-in-possibly-negated-nodenums-aux possibly-negated-nodenumsp))))

(defthm <=-of-max-nodenum-in-possibly-negated-nodenums-aux
  (<= acc (max-nodenum-in-possibly-negated-nodenums-aux items acc))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable max-nodenum-in-possibly-negated-nodenums-aux
                                     possibly-negated-nodenumsp
                                     possibly-negated-nodenump))))

(defthm <=-of-car-and-max-nodenum-in-possibly-negated-nodenums-aux
  (implies (and (possibly-negated-nodenumsp items)
                (consp items)
                ;; (not (consp (car items)))
                )
           (<= (car items) (max-nodenum-in-possibly-negated-nodenums-aux items acc)))
  :rule-classes (:rewrite (:linear :trigger-terms ((max-nodenum-in-possibly-negated-nodenums-aux items acc))))
  :hints (("Goal" :in-theory (enable max-nodenum-in-possibly-negated-nodenums-aux
                                     POSSIBLY-NEGATED-NODENUMSP
                                     possibly-negated-nodenump))))

(defthm <=-of-max-nodenum-in-possibly-negated-nodenums-aux-and-max-nodenum-in-possibly-negated-nodenums-aux
  (implies (<= acc1 acc2)
           (<= (max-nodenum-in-possibly-negated-nodenums-aux items acc1)
               (max-nodenum-in-possibly-negated-nodenums-aux items acc2)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable max-nodenum-in-possibly-negated-nodenums-aux))))

(defthm <=-of-max-nodenum-in-possibly-negated-nodenums-aux-of-cdr
  (implies (<= acc1 acc2)
           (<= (max-nodenum-in-possibly-negated-nodenums-aux (cdr items) acc1)
               (max-nodenum-in-possibly-negated-nodenums-aux items acc2)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :induct (max-nodenum-in-possibly-negated-nodenums-aux items acc)
           :in-theory (enable max-nodenum-in-possibly-negated-nodenums-aux
                              (:I max-nodenum-in-possibly-negated-nodenums-aux)))))

(defthm max-nodenum-in-possibly-negated-nodenums-lower-bound
  (implies (possibly-negated-nodenumsp predicates-or-negations)
           (<= -1 (max-nodenum-in-possibly-negated-nodenums predicates-or-negations)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable max-nodenum-in-possibly-negated-nodenums))))

(defthm <=-of-car-and-max-nodenum-in-possibly-negated-nodenums
  (implies (and (possibly-negated-nodenumsp items)
                (consp items)
                ;; (not (consp (car items)))
                )
           (<= (car items) (max-nodenum-in-possibly-negated-nodenums items)))
  :rule-classes (:rewrite (:linear :trigger-terms ((max-nodenum-in-possibly-negated-nodenums items))))
  :hints (("Goal" :in-theory (enable max-nodenum-in-possibly-negated-nodenums))))

(defthm <=-of-nth-0-and-max-nodenum-in-possibly-negated-nodenums
  (implies (and (possibly-negated-nodenumsp items)
                (consp items)
                ;; (not (consp (nth 0 items)))
                )
           (<= (nth 0 items) (max-nodenum-in-possibly-negated-nodenums items)))
  :rule-classes ((:linear :trigger-terms ((max-nodenum-in-possibly-negated-nodenums items))))
  :hints (("Goal" :use (:instance <=-of-car-and-max-nodenum-in-possibly-negated-nodenums)
           :in-theory (disable <=-of-car-and-max-nodenum-in-possibly-negated-nodenums))))

(defthm <=-of-nth-0-and-max-nodenum-in-possibly-negated-nodenums-2
  (implies (and (possibly-negated-nodenumsp items)
                ;; (not (consp (nth 0 items)))
                )
           (equal (< (max-nodenum-in-possibly-negated-nodenums items) (nth 0 items))
                  (not (consp items))))
  :hints (("Goal" :use (:instance <=-of-car-and-max-nodenum-in-possibly-negated-nodenums)
           :in-theory (disable <=-of-car-and-max-nodenum-in-possibly-negated-nodenums))))

(defthm <=-of-max-nodenum-in-possibly-negated-nodenums-of-cdr
  (implies (possibly-negated-nodenumsp items)
           (<= (max-nodenum-in-possibly-negated-nodenums (cdr items))
               (max-nodenum-in-possibly-negated-nodenums items)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable max-nodenum-in-possibly-negated-nodenums))))

(defthm max-nodenum-in-possibly-negated-nodenums-of-singleton
  (implies (possibly-negated-nodenump item)
           (equal (max-nodenum-in-possibly-negated-nodenums (list item))
                  (if (consp item)
                      (cadr item)
                    item)))
  :hints (("Goal" :in-theory (enable max-nodenum-in-possibly-negated-nodenums
                                     max-nodenum-in-possibly-negated-nodenums-aux
                                     possibly-negated-nodenump))))

(defthm max-nodenum-in-possibly-negated-nodenums-of-singleton-2
  (implies (not (consp item))
           (equal (max-nodenum-in-possibly-negated-nodenums (list item))
                  (max -1 item)))
  :hints (("Goal" :in-theory (enable max-nodenum-in-possibly-negated-nodenums
                                     max-nodenum-in-possibly-negated-nodenums-aux))))

(defthm integerp-of-nth-when-possibly-negated-nodenumsp-cheap
  (implies (and (possibly-negated-nodenumsp predicates-or-negations)
                (natp n))
           (equal (integerp (nth n predicates-or-negations))
                  (and (< n (len predicates-or-negations))
                       (not (consp (nth n predicates-or-negations))))))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil)))
  :hints (("Goal" :in-theory (e/d (possibly-negated-nodenumsp nth) (nth-of-cdr)))))

(defthm not-<-of-0-of-nth-when-possibly-negated-nodenumsp-cheap
  (implies (and (possibly-negated-nodenumsp predicates-or-negations)
                (<= k 0))
           (not (< (nth n predicates-or-negations) k)))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil)))
  :hints (("Goal" :in-theory (e/d (possibly-negated-nodenumsp
                                   nth
                                   possibly-negated-nodenump)
                                  (nth-of-cdr)))))

(defthm not-equal-of-1-and-len-of-nth-when-possibly-negated-nodenumsp-cheap
  (implies (possibly-negated-nodenumsp predicates-or-negations)
           (not (equal 1 (len (nth n predicates-or-negations)))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (e/d (possibly-negated-nodenumsp
                                   nth
                                   possibly-negated-nodenump)
                                  (nth-of-cdr)))))

(defthm node-replacement-alist-for-context-aux-helper
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array (+ 1 (nth '0 predicates-or-negations)))
                (natp (nth '0 predicates-or-negations))
                (natp n)
                (< n (len (dargs$inline (aref1 dag-array-name dag-array (nth '0 predicates-or-negations)))))
                (not (consp (nth n (dargs (aref1 dag-array-name dag-array (nth '0 predicates-or-negations))))))
                (not (equal 'quote (car (aref1 dag-array-name dag-array (nth '0 predicates-or-negations)))))
                (possibly-negated-nodenumsp predicates-or-negations)
                (consp predicates-or-negations)
                )
           (<= (nth n (dargs$inline (aref1 dag-array-name dag-array (nth '0 predicates-or-negations))))
               (max-nodenum-in-possibly-negated-nodenums predicates-or-negations)))
  :hints (("Goal" :use (:instance <-of-nth-of-dargs-of-aref1-when-pseudo-dag-arrayp (nodenum (nth '0 predicates-or-negations)))
           :in-theory (e/d (car-becomes-nth-of-0)
                           (<-of-nth-of-dargs-of-aref1-when-pseudo-dag-arrayp
                            <-of-nth-of-dargs)))))

(defthmd natp-of-+-of-1-alt
  (implies (integerp x)
           (equal (natp (+ 1 x))
                  (<= -1 x))))

(local (in-theory (enable natp-of-+-of-1-alt)))

(defthmd consp-when-<-of-0-and-nth
  (implies (< 0 (NTH n x))
           (consp x))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

(defthmd natp-of-nth-0-when-possibly-negated-nodenumsp
  (implies (and (possibly-negated-nodenumsp predicates-or-negations)
                predicates-or-negations
                (not (consp (nth 0 predicates-or-negations))))
           (natp (nth 0 predicates-or-negations)))
  :rule-classes (:rewrite :forward-chaining))
(local (in-theory (enable  natp-of-nth-0-when-possibly-negated-nodenumsp)))

;PREDICATES-OR-NEGATIONS is a possibly-negated-nodenumsp (list of items of the form: <nodenum> or (not <nodenum>))
;extends ACC with a list of pairs of the form (<nodenum> . <nodenum-or-quotep>) where PREDICATES-OR-NEGATIONS imply that the car of each pair is equal to the cdr
;this function is similar to add-equality-pairs
;fixme until Tue Sep  7 15:07:51 2010 this could return a pair whose car was a quoted constant (!) or whose car was an entire expression (!)
;fixme really this is building an alist - use acons below?
;the booland case makes termination tricky
(defun node-replacement-alist-for-context-aux (predicates-or-negations dag-array print known-booleans acc)
  (declare (xargs :measure (make-ord 1
                                     (+ 1 (nfix (max-nodenum-in-possibly-negated-nodenums predicates-or-negations)))
                                     (len predicates-or-negations))
                  :hints (("Goal" :in-theory (enable car-becomes-nth-of-0)
                           :cases ((<= (nth 0 predicates-or-negations) (max-nodenum-in-possibly-negated-nodenums predicates-or-negations)))))
                  :guard (and (possibly-negated-nodenumsp predicates-or-negations)
                              (pseudo-dag-arrayp 'dag-array dag-array (+ 1 (max-nodenum-in-possibly-negated-nodenums predicates-or-negations)))
                              (symbol-listp known-booleans))
                  :guard-hints (("Goal" :in-theory (e/d (car-becomes-nth-of-0
                                                         consp-when-<-of-0-and-nth
                                                         CONSP-WHEN-TRUE-LISTP
                                                         )
                                                        (;<=-OF-NTH-0-AND-MAX-NODENUM-IN-POSSIBLY-NEGATED-NODENUMS
                                                         ;(:linear <=-OF-NTH-0-AND-MAX-NODENUM-IN-POSSIBLY-NEGATED-NODENUMS)
                                                         ;;PSEUDO-DAG-ARRAYP-MONOTONE
                                                         node-replacement-alist-for-context-aux-helper
                                                         <-OF-NTH-OF-DARGS-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP
                                                         ))
                                 :do-not '(generalize eliminate-destructors)
                                 :use (
                                       (:instance <-OF-NTH-OF-DARGS-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP
                                                  (NODENUM (NTH 0 PREDICATES-OR-NEGATIONS))
                                                  (DAG-ARRAY DAG-ARRAY)
                                                  (DAG-ARRAY-NAME 'DAG-ARRAY)
                                                  (N 0))
                                       (:instance <-OF-NTH-OF-DARGS-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP
                                                  (NODENUM (NTH 0 PREDICATES-OR-NEGATIONS))
                                                  (DAG-ARRAY DAG-ARRAY)
                                                  (DAG-ARRAY-NAME 'DAG-ARRAY)
                                                  (N 1))
                                       (:instance node-replacement-alist-for-context-aux-helper
                                                  (n 1)
                                                  (DAG-ARRAY-name 'DAG-ARRAY)))))))
  (if (or (endp predicates-or-negations)
          (not (mbt (possibly-negated-nodenumsp predicates-or-negations))))
      acc
    (let* ((pred (first predicates-or-negations)))
      (if (consp pred) ;any consp is a call of not, and (not x) becomes the pair (x . 'nil):
          ;;todo: can we do better if the thing being negated is an OR?
          (node-replacement-alist-for-context-aux (cdr predicates-or-negations) dag-array print
                                                  known-booleans
                                                  (cons (cons (farg1 pred) *nil*)
                                                        acc))
        ;;pred is a nodenum:
        (let ((expr (aref1 'dag-array dag-array pred)))
          (if (atom expr) ; a variable (could add that the var is not nil?)
              (prog2$ (and (eq :verbose print) (cw "node-replacement-alist-for-context-aux is skipping variable pred ~x0~%" expr))
                      (node-replacement-alist-for-context-aux (cdr predicates-or-negations) dag-array print known-booleans acc))
            (let ((fn (ffn-symb expr)))
              (if (eq 'quote fn) ;if the constant is nil, what should happen?
                  (prog2$ (and (eq :verbose print) (cw "node-replacement-alist-for-context-aux is skipping constant pred ~x0~%" expr))
                          (node-replacement-alist-for-context-aux (cdr predicates-or-negations) dag-array print known-booleans acc))
                ;;it's a real function call:
                (if (and (eq 'equal fn) ;; (equal x y) may need to be turned around
                         (= 2 (len (dargs expr))) ;for guards
                         )
                    (let ((arg1 (darg1 expr))
                          (arg2 (darg2 expr)))
                      (if (consp arg1)     ;tests for quotep
                          (if (consp arg2) ;tests for quotep
                              (prog2$ (and (eq :verbose print) (cw "node-replacement-alist-for-context-aux is skipping equality of quoteps ~x0~%" expr))
                                      (node-replacement-alist-for-context-aux (cdr predicates-or-negations) dag-array print known-booleans acc))
                            (node-replacement-alist-for-context-aux (cdr predicates-or-negations)
                                                                    dag-array
                                                                    print
                                                                    known-booleans
                                                                    (cons (cons arg2 arg1) ;reverse the order
                                                                          acc)))
                        ;;arg1 is not a quotep (consider more sophisticated tests when deciding whether to reverse the order:
                        (node-replacement-alist-for-context-aux (cdr predicates-or-negations)
                                                                dag-array
                                                                print
                                                                known-booleans
                                                                (cons (cons pred *t*) ;new: we also replace the equality itself with true
                                                                      (cons (cons arg1 arg2)
                                                                            acc)))))
                  (if (and (eq 'not fn) ;ffixme this should never happen?!
                           (= 1 (len (dargs expr))) ;for guards
                           )
                      (let ((arg (darg1 expr)))
                        (if (atom arg)
                            ;; (not <nodenum>) becomes the pair (<nodenum> . 'nil) ;;the case above for 'equal handles the (equal x nil) phrasing for nots..
                            (node-replacement-alist-for-context-aux (cdr predicates-or-negations)
                                                                    dag-array
                                                                    print
                                                                    known-booleans
                                                                    (cons (cons arg *nil*)
                                                                          acc))
                          (prog2$ (and (eq :verbose print) (cw "node-replacement-alist-for-context-aux is skipping the negation of a constant: ~x0~%" expr))
                                  (node-replacement-alist-for-context-aux (cdr predicates-or-negations) dag-array print known-booleans acc))))
                    (if (and (eq 'booland fn) ;should not happen (the booland should have been opened when finding the context?)
                             (= 2 (len (dargs expr)))    ;for termination
                             (not (consp (darg1 expr))) ;nodenum (todo: handle a constant)
                             (not (consp (darg2 expr))) ;nodenum (todo: handle a constant)
                             (mbt (< (darg1 expr) pred)) ;for termination
                             (mbt (< (darg2 expr) pred)) ;for termination
                             (mbt (pseudo-dag-arrayp 'dag-array dag-array (+ 1 pred))) ;for termination
                             )
                        ;; (booland x y) causes x and y to be processed recursively
                        (node-replacement-alist-for-context-aux (cdr predicates-or-negations)
                                                                dag-array
                                                                print
                                                                known-booleans
                                                                (node-replacement-alist-for-context-aux (list (darg2 expr))
                                                                                                        dag-array
                                                                                                        print
                                                                                                        known-booleans
                                                                                                        (node-replacement-alist-for-context-aux (list (darg1 expr))
                                                                                                                                                dag-array
                                                                                                                                                print
                                                                                                                                                known-booleans
                                                                                                                                                acc)))
                      ;; for expr=(<known-predicate> ...) we get the pair (<nodenum-of-expr> . 't)
                      (if (member-eq fn known-booleans) ;we test for not above so dont need to exclude it here?
                          (node-replacement-alist-for-context-aux (cdr predicates-or-negations)
                                                                  dag-array
                                                                  print
                                                                  known-booleans
                                                                  (cons (cons pred *t*) ;yikes, had expr here instead of pred!
                                                                        acc))
                        (prog2$ (and print ;(eq :verbose print) ;could add the fact that it is not nil?
                                     (cw "NOTE: node-replacement-alist-for-context-aux is skipping expr ~x0 (not a call of a known predicate).~%" expr))
                                (node-replacement-alist-for-context-aux (cdr predicates-or-negations)
                                                                        dag-array
                                                                        print
                                                                        known-booleans
                                                                        acc))))))))))))))

(defthm <-of-nth-of-+-1-of-max-nodenum-in-possibly-negated-nodenums-aux
  (implies (and (possibly-negated-nodenumsp predicates-or-negations)
                (natp n)
                (not (consp (nth n predicates-or-negations)))
                (< n (len predicates-or-negations)))
           (< (nth n predicates-or-negations)
              (binary-+ '1 (max-nodenum-in-possibly-negated-nodenums-aux predicates-or-negations acc))))
  :hints (("Goal" :in-theory (e/d (max-nodenum-in-possibly-negated-nodenums-aux possibly-negated-nodenumsp nth)
                                  (nth-of-cdr)))))

(defthm <-of-nth-of-+-1-of-max-nodenum-in-possibly-negated-nodenums
  (implies (and (possibly-negated-nodenumsp predicates-or-negations)
                (natp n)
                (not (consp (nth n predicates-or-negations)))
                (< n (len predicates-or-negations)))
           (< (nth n predicates-or-negations) (binary-+ '1 (max-nodenum-in-possibly-negated-nodenums predicates-or-negations))))
  :hints (("Goal" :in-theory (e/d (max-nodenum-in-possibly-negated-nodenums max-nodenum-in-possibly-negated-nodenums-aux possibly-negated-nodenumsp nth)
                                  (nth-of-cdr)))))

(defthm not-<-of-max-nodenum-in-possibly-negated-nodenums-aux-and-car
  (implies (and (consp predicates-or-negations)
                (not (consp (car predicates-or-negations))))
           (<= (car predicates-or-negations)
               (max-nodenum-in-possibly-negated-nodenums-aux predicates-or-negations acc)))
  :hints (("Goal" :induct t
           :in-theory (enable max-nodenum-in-possibly-negated-nodenums-aux))))

(defthm not-<-of-max-nodenum-in-possibly-negated-nodenums-and-car
  (implies (and (consp predicates-or-negations)
                (not (consp (car predicates-or-negations))))
           (not (< (max-nodenum-in-possibly-negated-nodenums predicates-or-negations)
                   (car predicates-or-negations))))
  :hints (("Goal" :in-theory (enable max-nodenum-in-possibly-negated-nodenums))))

;some of the above lemmas may not be needed

(verify-guards node-replacement-alist-for-context-aux :hints (("Goal" ;:in-theory (enable POSSIBLY-NEGATED-NODENUMSP)
                                                   :in-theory (enable car-becomes-nth-of-0)
                                                   :cases ((CONSP PREDICATES-OR-NEGATIONS))
                                                   :expand ((possibly-negated-nodenumsp predicates-or-negations)
                                                            ;(max-nodenum-in-possibly-negated-nodenums predicates-or-negations)
                                                            ;;(max-nodenum-in-possibly-negated-nodenums-aux predicates-or-negations -1)
                                                            )))
  :otf-flg t)

;context is a possibly-negated-nodenumsp (list of items of the form: <nodenum> or (not <nodenum>))
;fixme do we end up doing this over and over for the same context predicates?
;returns a list of "replacement pairs" of the form (<nodenum> . <nodenum-or-quotep>) where the context implies that the car of each pair is equal to the cdr
(defun node-replacement-alist-for-context (context dag-array known-booleans print)
  (declare (xargs :guard (and (possibly-negated-nodenumsp context)
                              (pseudo-dag-arrayp 'dag-array dag-array (+ 1 (max-nodenum-in-possibly-negated-nodenums context)))
                              (symbol-listp known-booleans))))
  (node-replacement-alist-for-context-aux context dag-array print known-booleans nil))
