
(in-package "SAT")
(program)
(set-state-ok t)

(include-book "sat-setup")
(include-book "local-clause-simp")

;; In this file we handle instances of the following axiom:
;; (neq x y)) -> (neq (car x) (car y)) \/ (neq (cdr x) (cdr y)) \/
;;               (consp x) \/ (consp y)

;; This axiom can be rewritten as (to avoid the negations):
;; (equal (car x) (car y)) /\ (equal (cdr x) (cdr y)) /\
;; (consp x) /\ (consp y)
;; ->
;; (equal x y)

;; Our methodology is to handle this axiom during the traversal
;; of "x", where "x" is the intermedate variable traversed first.
;; At this point all uses of "x" have already been traversed,
;; so we have the complete set of relevant components of "x".

;; If (car x) or (cdr x) are irrelevant, then we add no new
;; clauses.

;; Otherwise we determine a DNF formula Ca involving the components of
;; x that imply (equal (car x) (car y)) and Cb involving the components
;; of x that imply (equal (cdr x) (cdr y)).  We then
;; have a method "and-merge-implications" that merges two DNF formulas X
;; and Y into a DNF formula Z such that Z implies X and Y, as well
;; as a method "or-merge-implications" that merges two DNF formulas X
;; and Y into a DNF formula Z such that Z implies X or Y.  New variables
;; are sometimes created to avoid explosion.  The DNF formula for
;; (equal x y) is therefore:

;; (merge-and Ca (merge-and Cb (merge-and (list (list consp-x)) (list (list consp-y)))))

;; We represent the conjunct f1 /\ f2 /\ ... fN as
;; the list ((not f1) (not f2) ... fN).  Here we add
;; a new element f0 to the conjunct:

(defun add-conjunct (f0 conj)
  (cons (negate-f-expr f0) conj))

;; The cnf-literals is a disjunction y0 \/ y1 \/ ... yN
;; that is intended to represent the implication
;; (not y0) /\ (not y1) /\ ... (not yN) -> ???
;; and now we want the conjunction y0 /\ y1 /\ ... yN.
;; In our minds we negate the literals, but in reality
;; the conjunction is already negated, so this is the
;; identity function.
(defun conj-from-cnf-lits (cnf-lits)
  cnf-lits)

(defun singleton-conjunct (f0)
  (list (negate-f-expr f0)))

(defun append-conjuncts (x0 x1)
  (rev-append x0 x1))

;; Add a clause representing that conj (f1 /\ ... fN)
;; implies f0.
(defun add-cnf-conjunct-implication (f0 conj $sat state)
  (declare (xargs :stobjs $sat))
  (add-cnf-clause (cons f0 conj) $sat state))

;; Add x0 to the disj, (x1 \/ x2 \/ ... xN), where
;; the dijunction is represented as a list of its
;; elements preceded by its length.
(defun add-disjunct (x0 disj)
  (cons (1+ (car disj)) (cons x0 (cdr disj))))

(defun empty-disjunct ()
  (cons 0 nil))

(defun singleton-disjunct (x0)
  (cons 1 (list x0)))

(defconst *max-disjunct-size* 50)

(defun add-cnf-disjunct-implication1 (f0 disj $sat state)
  (declare (xargs :stobjs $sat))
  (if (endp disj)
      (mv $sat state)
    (mv-let
     ($sat state)
     (add-cnf-conjunct-implication f0 (car disj) $sat state)
     (add-cnf-disjunct-implication1 f0 (cdr disj) $sat state))))
;; Add that disj implies f0:
;; (x0 \/ x1 \/ ... xN) -> f0
(defun add-cnf-disjunct-implication (f0 disj $sat state)
  (declare (xargs :stobjs $sat))
  (add-cnf-disjunct-implication1 f0 (cdr disj) $sat state))

;; Normalizes x0 /\ disj
;; x0 /\ (y0 \/ y1 \/ ... yN)
(defun merge-and2 (x0 disj ans)
  (cond
   ((endp disj)
    ans)
   (t
    (let ((ans (cons (append-conjuncts x0 (car disj)) ans)))
      (merge-and2 x0 (cdr disj) ans)))))

;; Normalizes disj0 /\ disj1,
;; (x0 \/ x1 \/ ... xN) /\ (y0 \/ y1 \/ ... yN)
;; (x0 /\ y0) \/
;; (x0 /\ y1) \/
;; ...
;; (x0 /\ yN) \/
;; (x1 /\ y0) \/
;; ...
;; (xN /\ yN) \/
(defun merge-and1 (disj0 disj1 ans)
  (cond
   ((endp disj0)
    ans)
   (t
    (let ((ans (merge-and2 (car disj0) disj1 ans)))
      (merge-and1 (cdr disj0) disj1 ans)))))

;; Given two disjuncts disj0 and disj1 return a
;; disjunct disj2 such that disj2 -> (disj0 /\ disj1).
(defun merge-and (disj0 disj1 $sat state)
  (declare (xargs :stobjs $sat))
  (let* ((len-disj0 (car disj0))
         (len-disj1 (car disj1))
         (len-ans (* len-disj0 len-disj1)))
    (cond
     ((= len-ans 0)
      (mv (empty-disjunct) $sat state))
     ((or (= len-disj0 1) (= len-disj1 1)
          (< len-ans *max-disjunct-size*))
      (mv (cons len-ans (merge-and1 (cdr disj0) (cdr disj1) nil))
          $sat
          state))
     ((> len-disj0 len-disj1)
      (mv-let
       (f-var $sat)
       (++f-var $sat)
       (mv-let
        ($sat state)
        (add-cnf-disjunct-implication f-var disj0 $sat state)
        (mv (cons len-disj1
                  (merge-and1 (list (singleton-conjunct f-var))
                              (cdr disj1)
                              nil))
            $sat
            state))))
     (t
      (mv-let
       (f-var $sat)
       (++f-var $sat)
       (mv-let
        ($sat state)
        (add-cnf-disjunct-implication f-var disj1 $sat state)
        (mv (cons len-disj0
                  (merge-and1 (list (singleton-conjunct f-var))
                              (cdr disj0)
                              nil))
            $sat
            state)))))))

(defun merge-or (x0 x1)
  (cons (+ (car x0) (car x1))
        (rev-append (cdr x0) (cdr x1))))

(defun compute-eq-atoms (atoms-alist i1 eq-i0-i1-disj $sat)
  (declare (xargs :stobjs $sat))
  (if (endp atoms-alist)
      (mv eq-i0-i1-disj $sat)
    (let ((a (caar atoms-alist))
          (eq-i0-a (cdar atoms-alist)))
      (mv-let
       (eq-i1-a $sat)
       (create-atom-var i1 a $sat)
       ;; (not (eq i0 a)) \/ (not (eq i1 a))
       (let ((x0 (add-conjunct eq-i0-a (singleton-conjunct eq-i1-a))))
         (compute-eq-atoms (cdr atoms-alist)
                           i1
                           (add-disjunct x0 eq-i0-i1-disj)
                           $sat))))))

(defun compute-eq-alist (eq-alist i1 eq-i0-i1-disj $sat)
  (declare (xargs :stobjs $sat))
  (if (endp eq-alist)
      (mv eq-i0-i1-disj $sat)
    (let ((a (caar eq-alist))
          (eq-i0-a (cdar eq-alist)))
      (mv-let
       (eq-i1-a $sat)
       (create-eq-var i1 a $sat)
       ;; (not (eq i0 a)) \/ (not (eq i1 a))
       (let ((x0 (add-conjunct eq-i0-a (singleton-conjunct eq-i1-a))))
         (compute-eq-alist (cdr eq-alist)
                           i1
                           (add-disjunct x0 eq-i0-i1-disj)
                           $sat))))))


;; Return a DNF formula that implies (equal i0 i1).
(defun compute-eq-disjunction (i0 i1 $sat state)
  (declare (xargs :stobjs $sat))
  (cond
   ((not (valid-varp i0))
    (mv (empty-disjunct) $sat state))
   (t
    (mv-let
     (eq-i0-i1-disj $sat)
     (compute-eq-atoms (atoms-alist-vari i0 $sat) i1 (empty-disjunct) $sat)
     (mv-let
      (eq-i0-i1-disj $sat)
      (compute-eq-alist (eq-alist-vari i0 $sat)
                        i1
                        eq-i0-i1-disj
                        $sat)
      (let ((car-i0 (car-vari i0 $sat))
            (cdr-i0 (cdr-vari i0 $sat))
            (consp-i0 (consp-vari i0 $sat)))
        (cond
         ((or (not (valid-varp car-i0))
              (not (valid-varp cdr-i0)))
          ;; Note: I don't think we really have to do this if
          ;; (car i1) or (cdr i1) don't exist.  I need to
          ;; think more about that though!!! ???
          (mv eq-i0-i1-disj $sat state))
         ((not (valid-varp consp-i0))
          ;; This consp should have been added by add-extra-consp-vars
          (mv (er hard 'compute-eq-disjunction
                  "The consp of a variable must exist if we are going ~
                   to instanciate the neq axiom on it~%")
              $sat
              state))
         (t
          (mv-let
           (car-i1 $sat)
           (get-car-var i1 $sat)
           (mv-let
            (cdr-i1 $sat)
            (get-cdr-var i1 $sat)
            (mv-let
             (consp-i1 $sat)
             (create-consp-var i1 $sat)
             (mv-let
              (car-disj $sat state)
              (compute-eq-disjunction car-i0 car-i1 $sat state)
              (mv-let
               (cdr-disj $sat state)
               (compute-eq-disjunction cdr-i0 cdr-i1 $sat state)
               (mv-let
                (eq-i0-i1-disj-cons $sat state)
                (merge-and (singleton-disjunct (singleton-conjunct consp-i0))
                           (singleton-disjunct (singleton-conjunct consp-i1))
                           $sat
                           state)
                (mv-let
                 (eq-i0-i1-disj-cons $sat state)
                 (merge-and cdr-disj eq-i0-i1-disj-cons $sat state)
                 (mv-let
                  (eq-i0-i1-disj-cons $sat state)
                  (merge-and car-disj eq-i0-i1-disj-cons $sat state)
                  (mv (merge-or eq-i0-i1-disj-cons eq-i0-i1-disj)
                      $sat
                      state)))))))))))))))))

(defun make-neq-cnf (i0 i1 eq-i0-i1 $sat state)
  (declare (xargs :stobjs $sat))
  (mv-let
   (eq-i0-i1-disj $sat state)
   (compute-eq-disjunction i0 i1 $sat state)
   (add-cnf-disjunct-implication eq-i0-i1 eq-i0-i1-disj $sat state)))

