; More material on DAGs
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

;; Used only by the x86 lifter.

(include-book "dags")
(include-book "kestrel/utilities/polarity" :dir :system)
(include-book "kestrel/alists-light/lookup-safe" :dir :system)
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/reverse-list" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "kestrel/alists-light/acons" :dir :system))
(local (include-book "kestrel/alists-light/alistp" :dir :system))

(in-theory (disable BOUNDED-DAG-EXPRP))

(local (in-theory (enable consp-of-car-when-alistp-alt)))

;; A renumbering maps nodenums to nodenums/quoteps
(defun renumberingp (renumbering)
  (declare (xargs :guard t))
  (if (atom renumbering)
      (null renumbering)
    (let ((entry (first renumbering)))
      (and (consp entry)
           (let ((key (car entry))
                 (val (cdr entry)))
             (and (natp key)
                  (or (natp val)
                      (myquotep val))
                  (renumberingp (rest renumbering))))))))

(defthm alistp-when-renumberingp-cheap
  (implies (renumberingp renumbering)
           (alistp renumbering))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

(defthm integerp-of-cdr-of-assoc-equal-when-renumberingp
  (implies (and (renumberingp renumbering)
                (assoc-equal x renumbering)
                (not (consp (cdr (assoc-equal x  renumbering)))))
           (integerp (cdr (assoc-equal x renumbering))))
  :hints (("Goal" :in-theory (enable renumberingp))))

(defthm non-neg-of-cdr-of-assoc-equal-when-renumberingp
  (implies (and (renumberingp renumbering)
                (assoc-equal x renumbering)
                (not (consp (cdr (assoc-equal x  renumbering)))))
           (<= 0 (cdr (assoc-equal x renumbering))))
  :hints (("Goal" :in-theory (enable renumberingp))))

;; Renumber an argument of a dag-expr according to the renumbering, which must
;; have an entry for it.
(defund renumber-dag-expr-arg (arg renumbering)
  (declare (xargs :guard (and (or (natp arg)
                                  (myquotep arg))
                              (renumberingp renumbering))))
  (if (consp arg) ;test for a constant
      arg
    (let ((match (assoc arg renumbering)))
      (if (not match)
          (prog2$ (er hard? 'renumber-dag-expr-arg "No renumbering for ~x0." arg)
                  0) ;so we know it's always a nat
        (cdr match)))))

(defthm dargp-of-renumber-dag-expr-arg
  (implies (and (dargp arg)
                (renumberingp renumbering))
           (dargp (renumber-dag-expr-arg arg renumbering)))
  :hints (("Goal" :in-theory (e/d (renumber-dag-expr-arg) (;myquotep
                                                            )))))

(defun renumber-dag-expr-args (args renumbering)
  (declare (xargs :guard (and (true-listp args)
                              (all-dargp args)
                              (renumberingp renumbering))))
  (if (endp args)
      nil
    (cons (renumber-dag-expr-arg (first args) renumbering)
          (renumber-dag-expr-args (rest args) renumbering))))

;; Returns the renumbered expr
(defund renumber-dag-expr (expr renumbering)
  (declare (xargs :guard (and (dag-exprp0 expr)
                              (renumberingp renumbering))
                  :guard-hints (("Goal" :in-theory (enable DAG-EXPRP0)))
                  ))
  (if (variablep expr)
      expr
    (if (eq 'quote (ffn-symb expr))
        expr
      (let* ((fn (ffn-symb expr))
             (args (dargs expr))
             (args (renumber-dag-expr-args args renumbering)))
        (cons fn args)))))

(defthm dag-exprp0-of-renumber-dag-expr
  (implies (and (dag-exprp0 expr)
                (renumberingp renumbering))
           (dag-exprp0 (renumber-dag-expr expr renumbering)))
  :hints (("Goal" :in-theory (enable renumber-dag-expr dag-exprp0))))

(in-theory (disable WEAK-DAGP-AUX RENUMBERINGP))

(defthm WEAK-DAGP-AUX-forward-to-true-listp
  (implies (WEAK-DAGP-AUX dag)
           (true-listp dag))
  :rule-classes (:forward-chaining)
  :hints (("Goal" :in-theory (enable WEAK-DAGP-AUX))))

(defthm renumberingp-of-acons
  (implies (renumberingp renumbering)
           (equal (renumberingp (acons key val renumbering))
                  (and (natp key)
                       (dargp val)
                       )))
  :hints (("Goal" :in-theory (enable renumberingp acons))))

(in-theory (disable mv-nth))

(defthm weak-dagp-aux-of-acons
  (implies (and (weak-dagp-aux dag)
                (bounded-dag-exprp nodenum expr)
                (<= (+ 1 (car (car dag))) nodenum)
                (consp dag))
           (equal (weak-dagp-aux (acons nodenum expr dag))
                  (natp nodenum)))
  :hints (("Goal" :expand ((weak-dagp-aux dag)
                           (weak-dagp-aux (cons (cons nodenum expr)
                                                dag)))
           :in-theory (enable acons bounded-dag-exprp dag-exprp0))))

(defthm integerp-of-+-of-1-and-car-of-car-when-weak-dagp-aux
  (implies (weak-dagp-aux dag)
           (integerp (+ 1 (car (car dag)))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :expand (weak-dagp-aux dag)
           :in-theory (enable weak-dagp-aux))))

(defthm <=-of-0-and-+-of-1-and-car-of-car-when-weak-dagp-aux
  (implies (weak-dagp-aux dag)
           (<= 0 (+ 1 (car (car dag)))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :expand (weak-dagp-aux dag)
           :in-theory (enable weak-dagp-aux))))

(defthm bounded-dag-exprp-when-symbolp
  (implies (symbolp expr)
           (bounded-dag-exprp n expr))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable bounded-dag-exprp))))

(defthm weak-dagp-aux-of-acons-of-0-and-nil-when-symbolp
  (implies (symbolp expr)
           (weak-dagp-aux (acons 0 expr nil)))
  :hints (("Goal" :expand ((weak-dagp-aux (acons 0 expr nil))))))

(defthm consp-when-bounded-dag-exprp-weaken
  (implies (and (syntaxp (want-to-weaken (consp expr)))
                (bounded-dag-exprp n expr))
           (equal (consp expr)
                  (not (symbolp expr))))
  :hints (("Goal" :in-theory (enable bounded-dag-exprp DAG-EXPRP0))))

(defun binds-all-nats-up-to (n alist)
  (declare (xargs :guard (and (or (natp n)
                                  (eql -1 n))
                              (alistp alist))
                  :measure (nfix (+ 1 n))))
  (if (not (natp n))
      t
    (and (assoc n alist)
         (binds-all-nats-up-to (+ -1 n) alist))))

(local (in-theory (disable alistp)))

(defthm alistp-of-cdr
  (implies (alistp x)
           (alistp (cdr x)))
  :hints (("Goal" :in-theory (enable alistp))))

(defun maps-everything-to-quote-or-nodenum-less-than (alist n)
  (declare (xargs :guard (and (or (natp n)
                                  (equal -1 n))
                              (alistp alist))))
  (if (endp alist)
      t
    (and (let ((val (cdr (first alist))))
           (or (myquotep val)
               (and (natp val)
                    (< val n))))
         (maps-everything-to-quote-or-nodenum-less-than (rest alist) n))))

;; (BOUNDED-DAG-EXPRP (BINARY-+ '1 (IF (CONSP MAIN-DAG) (CAR (CAR MAIN-DAG)) '-1)) (RENUMBER-DAG-EXPR (CDR (CAR REV-DAG-TO-MERGE)) RENUMBERING))

(defthm assoc-equal-when-binds-all-nats-up-to
  (implies (and (binds-all-nats-up-to m renumbering)
                (natp x)
                (natp m)
                (<= x m))
           (assoc-equal x renumbering)))

(defthm <-of-cdr-of-assoc-equal-when-maps-everything-to-quote-or-nodenum-less-than
  (implies (and (maps-everything-to-quote-or-nodenum-less-than renumbering n)
                (assoc-equal arg renumbering)
                (not (consp (cdr (assoc-equal arg renumbering)))))
           (< (cdr (assoc-equal arg renumbering)) n))
  :hints (("Goal" :in-theory (enable assoc-equal))))

(defthm not-of-cdddr-of-assoc-equal-when-maps-everything-to-quote-or-nodenum-less-than
  (implies (maps-everything-to-quote-or-nodenum-less-than renumbering n)
           (not (cdddr (assoc-equal (car args) renumbering))))
  :hints (("Goal" :in-theory (enable assoc-equal))))

(defthm natp-of-cdr-of-assoc-equal-when-maps-everything-to-quote-or-nodenum-less-than
  (implies (and (maps-everything-to-quote-or-nodenum-less-than renumbering n)
                (assoc-equal arg renumbering)
                (not (consp (cdr (assoc-equal arg renumbering)))))
           (natp (cdr (assoc-equal arg renumbering))))
  :hints (("Goal" :in-theory (enable assoc-equal))))

;limit?
(defthm car-of-car-linear-when-weak-dagp-aux
  (implies (and (weak-dagp-aux dag)
                dag)
           (<= 0 (car (car dag))))
  :rule-classes (:linear)
  :hints (("Goal" :in-theory (enable weak-dagp-aux))))

(defthm weak-dagp-aux-of-cdr
  (implies (weak-dagp-aux dag)
           (weak-dagp-aux (cdr dag)))
  :hints (("Goal" :in-theory (enable weak-dagp-aux))))

(defthm car-of-car-linear-when-weak-dagp-aux
  (implies (and (weak-dagp-aux dag)
                dag)
           (<= 0 (car (car dag))))
  :rule-classes (:linear)
  :hints (("Goal" :in-theory (enable weak-dagp-aux))))

(defthm car-of-car-type-when-weak-dagp-aux-type
  (implies (and (weak-dagp-aux dag)
                dag)
           (natp (car (car dag))))
  :rule-classes (:type-prescription)
  :hints (("Goal" :in-theory (enable weak-dagp-aux))))

;; TODO: Same as consecutivep of strip-cars?
(defun cars-increasing-by-1 (rev-dag)
  (declare (xargs :guard (weak-dagp-aux rev-dag)))
  (if (endp rev-dag)
      t
    (if (endp (cdr rev-dag))
        t
      (and (equal (car (second rev-dag))
                  (+ 1 (car (first rev-dag))))
           (cars-increasing-by-1 (rest rev-dag))))))


;; (thm
;;  (BINDS-ALL-NATS-UP-TO 0 RENUMBERING)
;;  :hints (("Goal" :expand ((BINDS-ALL-NATS-UP-TO 0 RENUMBERING)))))

(defthm binds-all-nats-up-to-of-acons-greater
  (implies (and (< n n2)
        ;        (natp n)
       ;         (natp n2)
                )
           (equal (binds-all-nats-up-to n (acons n2 val renumbering))
                  (binds-all-nats-up-to n renumbering)))
  :hints (("Goal" :in-theory (enable acons)
           :expand ((BINDS-ALL-NATS-UP-TO 0 RENUMBERING)
                    (BINDS-ALL-NATS-UP-TO 0 (CONS (CONS N2 VAL) RENUMBERING))))))

(defthm binds-all-nats-up-to-of-acons-of-one-more
  (implies (and (binds-all-nats-up-to n renumbering)
                (natp n))
           (binds-all-nats-up-to (+ 1 n) (acons (+ 1 n) val renumbering)))
  :hints (("Goal" :in-theory (enable binds-all-nats-up-to))))

;; (thm
;;  (implies (or (myquotep arg)
;;               (natp arg))
;;           (equal (renumber-dag-expr-arg arg nil)
;;                  arg))
;;  :hints (("Goal" :in-theory (enable RENUMBER-DAG-EXPR-ARG))))

(defthm consp-of-renumber-dag-expr
  (equal (consp (renumber-dag-expr expr renumbering))
         (consp expr))
  :hints (("Goal" :in-theory (enable renumber-dag-expr))))

;rename
(defthm quotep-of-renumber-dag-expr
  (equal (equal 'quote (car (renumber-dag-expr expr renumbering)))
         (equal 'quote (car expr)))
  :hints (("Goal" :in-theory (enable renumber-dag-expr))))

(defthm renumber-dag-expr-when-not-consp
  (implies (not (consp expr))
           (equal (renumber-dag-expr expr renumbering)
                  expr))
  :hints (("Goal" :in-theory (enable renumber-dag-expr))))

;rename
(defthm renumber-dag-expr-when-quotep
  (implies (equal 'quote (car expr))
           (equal (renumber-dag-expr expr renumbering)
                  expr))
  :hints (("Goal" :in-theory (enable renumber-dag-expr))))

(defthm PSEUDO-DAGP-AUX-of-minus1
  (equal (PSEUDO-DAGP-AUX DAG -1)
         (equal nil dag))
  :hints (("Goal" :in-theory (enable PSEUDO-DAGP-AUX))))

(defthm maps-everything-to-quote-or-nodenum-less-than-monotonic
  (implies (and (maps-everything-to-quote-or-nodenum-less-than renumbering m)
                (<= m n)
                (natp m)
                (natp n))
           (maps-everything-to-quote-or-nodenum-less-than renumbering n)))

(defthm pseudo-dagp-aux-of-acons
  (implies (natp n)
           (equal (pseudo-dagp-aux (acons n expr dag) n)
                  (and (bounded-dag-exprp n expr)
                       (pseudo-dagp-aux dag (+ -1 n)))))
  :hints (("Goal" :in-theory (enable pseudo-dagp-aux))))

(defthm consp-of-cddr-of-assoc-equal-when-maps-everything-to-quote-or-nodenum-less-than
  (implies (and (syntaxp (want-to-weaken (consp (cddr (assoc-equal arg renumbering)))))
                (maps-everything-to-quote-or-nodenum-less-than renumbering n)
                (assoc-equal arg renumbering))
           (equal (consp (cddr (assoc-equal arg renumbering)))
                  (not (integerp (cdr (assoc-equal arg renumbering))))))
  :hints (("Goal" :in-theory (enable assoc-equal))))

;rename
(defthm quotep-of-cdr-of-assoc-equal-when-maps-everything-to-quote-or-nodenum-less-than
  (implies (and (syntaxp (want-to-weaken (equal (cadr (assoc-equal arg renumbering))
                                                'quote)))
                (maps-everything-to-quote-or-nodenum-less-than renumbering n)
                (assoc-equal arg renumbering))
           (equal (equal (cadr (assoc-equal arg renumbering))
                         'quote)
                  (not (integerp (cdr (assoc-equal arg renumbering))))))
  :hints (("Goal" :in-theory (enable assoc-equal))))

(defthm all-dargp-less-than-of-renumber-dag-expr-args
  (implies (and (all-dargp-less-than args nodenum2)
                (natp nodenum2)
                (natp nodenum)
                (maps-everything-to-quote-or-nodenum-less-than renumbering nodenum)
                (binds-all-nats-up-to (+ -1 nodenum2) renumbering)
                (renumberingp renumbering))
           (all-dargp-less-than (renumber-dag-expr-args args renumbering) nodenum))
  :hints (("Goal" :induct (renumber-dag-expr-args args renumbering)
           :in-theory (enable renumber-dag-expr renumber-dag-expr-arg bounded-dag-exprp dargp-less-than))))

(defthm all-dargp-of-renumber-dag-expr-args
  (implies (and (all-dargp-less-than args nodenum2)
                (natp nodenum2)
                (natp nodenum)
                (maps-everything-to-quote-or-nodenum-less-than renumbering nodenum)
                (binds-all-nats-up-to (+ -1 nodenum2) renumbering)
                (renumberingp renumbering))
           (all-dargp (renumber-dag-expr-args args renumbering)))
  :hints (("Goal" :induct (renumber-dag-expr-args args renumbering)
           :in-theory (enable renumber-dag-expr renumber-dag-expr-arg bounded-dag-exprp))))

(defthm bounded-dag-exprp-of-renumber-dag-expr
  (implies (and (binds-all-nats-up-to nodenum3 renumbering)
                (bounded-dag-exprp (+ 1 nodenum3) expr)
                (maps-everything-to-quote-or-nodenum-less-than renumbering nodenum)
                (renumberingp renumbering)
                (integerp nodenum3)
                (<= -1 nodenum3)
                (natp nodenum))
           (bounded-dag-exprp nodenum (renumber-dag-expr expr renumbering)))
  :hints (("Goal" :in-theory (enable renumber-dag-expr dag-exprp0 bounded-dag-exprp))))

(defthm bounded-dag-exprp-when-not-consp
  (implies (not (consp x))
           (equal (bounded-dag-exprp nodenum x)
                  (symbolp x)))
  :hints (("Goal" :in-theory (enable bounded-dag-exprp DAG-EXPRP0))))

(defthm bounded-dag-exprp-when-quotep
  (implies (eq 'quote (car x))
           (equal (bounded-dag-exprp nodenum x)
                  (and (consp (cdr x))
                       (null (cddr x)))))
  :hints (("Goal" :in-theory (enable bounded-dag-exprp DAG-EXPRP0))))

(defthm dag-expr-of-caar-and-cdar-when-weak-dagp-aux
  (implies (and (weak-dagp-aux dag)
                (consp dag))
           (BOUNDED-DAG-EXPRP (CAR (CAR dag)) (CDR (CAR dag))))
  :hints (("Goal" :in-theory (enable weak-dagp-aux))))

(defthm RENUMBER-DAG-EXPR-ARGS-when-ALL-DARGP-LESS-THAN-of-0
  (implies (and (ALL-DARGP-LESS-THAN args 0)
                (true-listp args))
           (equal (RENUMBER-DAG-EXPR-ARGS args RENUMBERING)
                  args))
  :hints (("Goal" :in-theory (enable ALL-DARGP-LESS-THAN RENUMBER-DAG-EXPR-ARG))))

(defthm renumber-dag-expr-when-bounded-dag-exprp-of-0
  (implies (bounded-dag-exprp 0 expr)
           (equal (renumber-dag-expr expr renumbering)
                  expr))
  :hints (("Goal" :in-theory (enable renumber-dag-expr bounded-dag-exprp dag-exprp0))))

;; Returns (mv dag renumbering)
;; The renumbering maps nodenums in REV-DAG-TO-MERGE to nodenums in the MAIN-DAG.
;; TODO: need to require renumbering to map every node in rev-dag-to-merge seen so far to a node in main-dag (or a constant)
;; TODO: Make a version that uses arrays?
;; See also merge-embedded-dag-into-dag
(defun merge-dag-into-dag-aux (rev-dag-to-merge main-dag renumbering)
  (declare (xargs :guard (and (weak-dagp-aux rev-dag-to-merge) ;okay even though this is reversed
                              (weak-dagp-aux main-dag) ;because we call top-nodenum
                              (pseudo-dagp-aux main-dag (top-nodenum main-dag))
                              (renumberingp renumbering)
                              (cars-increasing-by-1 rev-dag-to-merge)
                              (if rev-dag-to-merge
                                  (binds-all-nats-up-to (+ -1 (car (car rev-dag-to-merge)))
                                                        renumbering)
                                t)
                              (if main-dag
                                  (maps-everything-to-quote-or-nodenum-less-than renumbering (+ 1 (top-nodenum main-dag)))
                                (equal renumbering nil)))
                  :guard-hints (("Goal" :do-not-induct t
                                 :do-not '(generalize eliminate-destructors)
                                 :expand (WEAK-DAGP-AUX REV-DAG-TO-MERGE)
                                 :in-theory (e/d (WEAK-DAGP-AUX add-to-dag)
                                                 (weak-dagp-aux-when-pseudo-dagp-aux ;why?
                                                  ))))))
  (if (endp rev-dag-to-merge)
      (mv main-dag renumbering)
    (let* ((pair (first rev-dag-to-merge))
           (nodenum (car pair))
           (expr (cdr pair))
           ;; expr mentions smaller nodenums, so the renumbering should map them to new nodenums
           (expr (renumber-dag-expr expr renumbering)))
      (mv-let (new-nodenum main-dag)
        (add-to-dag expr main-dag)
        (merge-dag-into-dag-aux (rest rev-dag-to-merge)
                                main-dag
                                (acons nodenum new-nodenum renumbering))))))

(defthm CARS-INCREASING-BY-1-of-append
  (equal (CARS-INCREASING-BY-1 (APPEND x y))
         (if (not (consp x))
             (CARS-INCREASING-BY-1 y)
           (if (not (consp y))
               (CARS-INCREASING-BY-1 x)
             (and (CARS-INCREASING-BY-1 x)
                  (CARS-INCREASING-BY-1 y)
                  (equal (car (car y))
                         (+ 1 (car (car (last x))))))))))

;; (defthm car-of-last-of-rev
;;   (equal (CAR (LAST (REV x)))
;;          (car x))
;;   :hints (("Goal" :in-theory (enable rev))))

;; (defthm car-of-rev
;;   (implies (consp x)
;;            (equal (car (rev x))
;;                   (car (last x))))
;;   :hints (("Goal" :in-theory (enable rev))))

(defthm cars-increasing-by-1-of-reverse-list
  (implies (and (pseudo-dagp-aux dag-to-merge nodenum)
                (integerp nodenum))
           (cars-increasing-by-1 (reverse-list dag-to-merge)))
  :hints (("Goal" :in-theory (enable pseudo-dagp-aux reverse-list))))

(defthm car-of-nth-of-car-of-car-when-pseudo-dagp-aux
  (implies (and (pseudo-dagp-aux dag nodenum)
                (natp nodenum)
                (consp dag))
           (equal (CAR (NTH (CAR (CAR dag)) dag))
                  0))
  :hints (("Goal" :in-theory (enable pseudo-dagp-aux last))))

(defthm car-of-car-of-last-when-pseudo-dagp-aux
  (implies (and (pseudo-dagp-aux dag nodenum)
                (natp nodenum)
                (consp dag))
           (equal (car (car (last dag)))
                  0))
  :hints (("Goal" :in-theory (enable pseudo-dagp-aux last))))

(defthm alistp-of-mv-nth-1-of-merge-dag-into-dag-aux
  (implies (alistp renumbering)
           (alistp (mv-nth 1 (merge-dag-into-dag-aux rev-dag main-dag renumbering)))))

;; Returns (mv new-nodenum-or-quotep dag)
(defun merge-dag-into-dag (dag-to-merge main-dag)
  (declare (xargs :guard (and (or (myquotep dag-to-merge)
                                  (pseudo-dagp main-dag))
                              (pseudo-dagp dag-to-merge))
                  :guard-hints (("Goal" :in-theory (enable pseudo-dagp)))))
  (if (quotep dag-to-merge)
      (mv dag-to-merge main-dag)
    (mv-let (dag renumbering)
      (merge-dag-into-dag-aux (reverse dag-to-merge) main-dag nil)
      (mv (lookup-safe ;todo: drop the -safe
           (top-nodenum dag-to-merge) renumbering)
          dag))))

(mutual-recursion
 ;;returns (mv nodenum-or-quotep new-dag)
 ;; similar to compose-term-and-dag-aux except here the alist maps vars to entire dags
 (defun compose-term-and-dags-aux (term alist dag)
;   (declare (xargs :guard (pseudo-termp term)))
   (if (variablep term)
       (let ((match (assoc-eq term alist)))
         (if (not match)
             ;; it's a var we are not replacing:
             (add-to-dag term dag)
           ;; this var is being replaced with a dag (or perhaps a quotep???)
           (let ((new-dag (cdr match)))
             (merge-dag-into-dag new-dag dag))))
     (if (quotep term)
         (mv term dag)
       ;; function call:
       (let ((fn (ffn-symb term))
             (args (fargs term)))
         (mv-let (new-args dag)
           (compose-term-and-dags-aux-lst args alist dag)
           (add-to-dag (cons fn new-args) dag))))))

 ;;returns (mv nodenums-and-constants dag)
 (defun compose-term-and-dags-aux-lst (terms alist dag)
   (if (endp terms)
       (mv nil dag)
     (mv-let (car-nodenum dag)
       (compose-term-and-dags-aux (car terms) alist dag)
       (mv-let (cdr-nodenums dag)
         (compose-term-and-dags-aux-lst (cdr terms) alist dag)
         (mv (cons car-nodenum cdr-nodenums)
             dag))))))

;; Return a DAG equal to TERM after applying ALIST to replace some vars with sub-dags
(defun compose-term-and-dags-fn (term
                                 alist ;maps vars to dags
                                 extra-vars ;vars that appear in term but are not bound in the alist
                                 )
  (let* ((term-vars (all-vars term))
         (alist-vars (strip-cars alist))
         (allowed-term-vars (append alist-vars extra-vars))
         )
    (if (not (subsetp-eq term-vars allowed-term-vars))
        (er hard? 'compose-term-and-dags
            "Unexpected vars, ~x0, found in term ~x1 (not bound in the alist and not mentioned in :extra-vars (~x2))."
            (set-difference-eq term-vars allowed-term-vars)
            term
            extra-vars)
      (mv-let (nodenum dag)
        (compose-term-and-dags-aux term
                                   alist
                                   nil ;empty DAG
                                   )
        (declare (ignore nodenum)) ;i think this is guaranteed to be the top-nodenum of the resulting dag
        dag))))

(defmacro compose-term-and-dags (term
                                 alist ;maps vars to dags
                                 &key
                                 (extra-vars 'nil) ;vars that appear in term but are not bound in the alist
                                 )
  `(compose-term-and-dags-fn ,term ,alist ,extra-vars))

;; (equal (dag-to-term (COMPOSE-TERM-AND-DAGS '(foo x (bar y) (bar y)) (acons 'x '((1 + '1 0) (0 . W)) (acons 'y ''3 nil))))
;;        '(FOO (+ '1 W) (BAR '3) (BAR '3)))

;; Returns (mv low-nodes rev-high-nodes) where low-nodes are the nodes below
;; NODENUM and rev-high-nodes are the reverse (so, low nodes first) of the
;; nodes at NODENUM and higher.
(defun split-dag-at-node (dag nodenum high-nodes-acc)
  (declare (xargs :guard (and (weak-dagp-aux dag)
                              (natp nodenum))))
  (if (endp dag)
      (mv nil high-nodes-acc)
    (let ((current-nodenum (caar dag)))
      (if (< current-nodenum nodenum)
          (mv dag high-nodes-acc)
        (split-dag-at-node (rest dag) nodenum (cons (first dag) high-nodes-acc))))))

;move:
;(defconst *test-dag* '((4 foo 3 '200) (3 bar 2 1) (2 . v) (1 . '100) (0 . v2) ))
;(pseudo-dagp *test-dag*)
;(split-dag-at-node (reverse *test-dag*) 2 nil)

;todo: allow the renumbering to be missing nodes (meaning make no change)?

;; TODO: Will this be too slow to be useful?

;; (defun compose-dags-simple (main-dag var-to-replace subdag-for-var check-varsp)
;;   (declare (xargs :guard (and (or (quotep main-dag)
;;                                   (pseudo-dagp main-dag))
;;                               (or (quotep subdag-for-var)
;;                                   (pseudo-dagp subdag-for-var))
;;                               (booleanp check-varsp))))
;;   (if (quotep main-dag)
;;       (if check-varsp
;;           (er hard? 'compose-dags-simple "Variable ~x0 does not appear in dag ~x1 because it is a constant." var-to-replace main-dag)
;;         main-dag)
;;     (let ((nodenum-of-var (find-node-for-expr var-to-replace main-dag)))
;;       (if (not nodenum-of-var)
;;           (if check-varsp
;;               (er hard? 'compose-dags-simple "Variable ~x0 does not appear in dag ~x1." var-to-replace main-dag)
;;             main-dag)
;;         (if (quotep subdag-for-var)
;;             (b* (;; maybe overkill, but this prevents a naked constant:
;;                  (main-dag-top-nodenum (top-nodenum main-dag))
;;                  ((mv low-nodes rev-high-nodes)
;;                   (split-dag-at-node main-dag nodenum-of-var nil))





;;                  (renumbering (acons nodenum-of-var subdag-for-var nil))
;;                  ((mv new-dag renumbering)
;;                   (merge-dag-into-dag-aux rev-high-nodes low-nodes renumbering))
;;                  (new-top-nodenum (lookup main-dag-top-nodenum renumbering))
;;                  )
;;               (drop-nodes-past new-top-nodenum new-dag))
;;           nil)))))


;;           (b* ((subdag-for-var-top-nodenum (top-nodenum subdag-for-var))
;;                (main-dag-top-nodenum (top-nodenum main-dag))
;;                (rev-main-dag (reverse main-dag))
;;                ((mv rev-low-nodes rev-high-nodes)
;;                 (split-dag-at-node rev-main-dag nodenum-of-var nil))
;;                ((mv new-dag renumbering)
;;                 (merge-dag-into-dag-aux rev-low-nodes subdag-for-var nil))
;;                (renumbering (acons nodenum-of-var subdag-for-var-top-nodenum renumbering))
;;                ((mv new-dag renumbering)
;;                 (merge-dag-into-dag-aux rev-high-nodes new-dag renumbering))
;;                (new-top-nodenum (lookup main-dag-top-nodenum renumbering))
;;                )
;;             (drop-nodes-past new-top-nodenum new-dag)))))))
