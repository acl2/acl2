#|$ACL2s-Preamble$;
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "../portcullis")
(acl2::begin-book t);$ACL2s-Preamble$|#

#|
User interface to cgen's fixer rules and preservation rules
author: harshrc
file name: cgen-rules.lisp
date created: [2016-03-22 Tue]

|#

(in-package "CGEN")

(include-book "acl2s/defdata/defdata-util" :dir :system)
(include-book "utilities")


; TYPE METADATA TABLE
(table fixer-rules-table nil nil :clear)        ; (lit . fixer-term) -> rule metadata
(table preservation-rules-table nil nil :clear) ; (lit . fixer-terms) -> rule metadata

; Note: Lets not worry about storing fixers separately with its IC and OC. What
; we probably do need to maintain as an invariant is that the hypotheses of the
; rules should satisfy all the body-contracts of the fixer-term *and* should be
; preserved after the fixing. [2016-03-22 Tue]

;; [2017-10-11 Wed] :test-hyp restricts the checking of the rule with extra "test" hypotheses.
(def-const *cgen-rule-keywords*
  '(:test-hyp :hyp :meta-precondition :rule :rule-classes :override-check :verbose))

(def-const *cgen-rule-classes*
  '(:fixer :preservation))

(defmacro define-rule  (name &rest keys)
  (b* ((verbosep (let ((lst (member :verbose keys)))
                   (and lst (cadr lst))))
       (keys (defdata::remove-keywords-from-args '(:verbose) keys)))
    `(with-output 
      ,@(and (not verbosep) '(:off :all :summary-off :all :on (error comment))) :stack :push
      (make-event
       (cgen-rule-events ',name ',keys ',verbosep (w state) state)))))


;copied from defuns.lisp and modified
(defun guard-obligation/without-check (term guard-debug state)
  (declare (xargs :mode :program :stobjs (state)))
  (mv-let (cl-set cl-set-ttree)
          (acl2::guard-obligation-clauses (cons :term term) guard-debug (acl2::ens state) (acl2::w state) state)
          (value (list* term cl-set cl-set-ttree))))

(defmacro body-contracts-obligation (term &key guard-debug)
  `(er-let* ((tuple (guard-obligation/without-check ,term ',guard-debug state)))
     (cond ((eq tuple :redundant) (value :redundant))
           (t (let ((displayed-goal (acl2::prettyify-clause-set (cadr tuple)
                                                          (acl2::let*-abstractionp state)
                                                          (acl2::w state))))
                (value displayed-goal))))))


(defun destruct-mv1 (n mv-exp arity ans)
  (if (zp n)
      ans
    (b* ((i (1- n)))
      (destruct-mv1 (1- n) mv-exp arity
                    (cons (list 'MV-NTH (kwote i) (list 'MV-LIST (kwote arity) mv-exp)) ans)))))



(defun destruct-mv (mv-exp arity wrld)
  (declare (xargs :mode :program))
  (if (zp arity)
      (er hard? 'destruct-mv "~| ~x0 arity not legal.~%" arity)
    (if (<= arity 1)
        (list mv-exp)
      (b* ((possible-list-exp (acl2::untranslate mv-exp nil wrld))
           ;;hack -- because mv gets expanded to a list 
           ((when (and (consp possible-list-exp) (eq (car possible-list-exp) 'LIST)))
            (cdr possible-list-exp)))
        (destruct-mv1 arity mv-exp arity '())))))

(program)
(set-state-ok t)
(defun translate-cmp-lst (xs STOBJS-OUT LOGIC-MODEP KNOWN-STOBJS CTX W STATE-VARS)
  (if (endp xs)
      (acl2::value-cmp nil)
    (b* (((acl2::cmp term) (acl2::translate-cmp (car xs) stobjs-out logic-modep known-stobjs ctx w state-vars))
         ((acl2::cmp rest-terms) (translate-cmp-lst (cdr xs) stobjs-out logic-modep known-stobjs ctx w state-vars)))
      (acl2::value-cmp (cons term rest-terms)))))



#|
(defrule path-table-fixer-rule
  (implies (and (alispt pt)
                (graphp g)
                (member a (strip-cars g)))
           (path-table-p a (path-table-fix a pt g) g))
  :rule-classes :fixer)

(defrule path-table-fixer-rule
  :hyp (and (alispt pt)
            (graphp g)
            (member a (strip-cars g)))
  :rule (let ((pt (path-table-fix a pt g)))
          (path-table-p a pt g)))

(cgen-rule path-table-fixer-rule2
  :hyp (and (alispt pt)
            (graphp g)
            (member a (strip-cars g)))
  :rule (mv-let (pt g) (path-table-fix2 a pt g)
                (path-table-p a pt g))
  :rule-classes :fixer)

(cgen-rule append-inverse1
  :hyp (and (true-listp X1)
            (true-listp X2)
            (true-listp X3))
  :rule (mv-let (X1 X2) (append-inverse1 X1 X3)
                (equal x3 (append x1 x2)))
  :rule-classes :fixer)

(cgen-rule append-inverse2
  :hyp (and (true-listp X1)
            (true-listp X2)
            (true-listp X3)
            (natp n)
            (< n (len X3)))
  :rule (mv-let (X1 X2) (append-inverse2 n X3) ; should n be allowed??
                (equal x3 (append x1 x2)))
  :rule-classes :fixer)

(cgen-rule append-inverse2-no-free-var
  :hyp (and (true-listp X1)
            (true-listp X2)
            (true-listp X3)
            (< (len X1) (len X3)))
  :rule (mv-let (X1 X2) (append-inverse2 (len X1) X3)
                (equal x3 (append x1 x2)))
  :rule-classes :fixer)

(cgen-rule rule-name
  :hyp hyp-term(In \cup Out)
  :rule (mv-let Out fixer-term(In)  ;mv-let binding
                constraint-term(Vars)) 
  :rule-classes :fixer)
OR 
(cgen-rule rule-name
  :hyp hyp-term(In \cup Out)
  :rule (let ((Y fixer-term(In)))  ;let binding Out={Y}
          constraint-term(Vars))
  :rule-classes :fixer)
Invariants:
1. Body contracts of fixer-term have to be satisfied under hyp-term
2. Vars \subset In \cup Out,  Out \subset Vars
3. hyp-term should be preserved through the fixer changes.
4. rule should be valid under hyp-term -- use thm or at the least test?


|#



(defun destructure-fixer-rule (rule)
  (cond ((and (= 4 (len rule)) (eq (car rule) 'MV-LET))
         (b* ((`(MV-LET ,Out ,fixer-exp ,constraint) rule))
           (list Out fixer-exp constraint)))
        ((and (= 3 (len rule)) (eq (car rule) 'LET) (= 1 (len (second rule)))) ;exactly one let binding
         (b* ((`(LET ((,Y ,fixer-exp)) ,constraint) rule))
           (list (list Y) fixer-exp constraint)))
        (t (er hard? 'destructure-fixer-rule "~| ~x0 is not a fixer rule.~%" rule))))



(defun make-cgen-rule-events/fixer (rule kwd-alist override-checkp verbosep ctx wrld state)
  (b* (((list Out fixer-exp constraint) (destructure-fixer-rule rule))
       ((unless (and (defdata::proper-symbol-listp Out)
                     (> (len Out) 0)))
        (er soft ctx "~| ~x0 is not a non-empty list of variable names.~%" Out))
       ((er constraint-term ) (acl2::translate constraint t nil t ctx wrld state))
       ((er fixer-term) (acl2::translate fixer-exp t nil t ctx wrld state))
       (In (reverse (acl2::all-vars fixer-term)))
       (mv-expanded-fixer-terms (destruct-mv fixer-term (len Out) wrld))
       (fixer-binding (acl2::listlis Out mv-expanded-fixer-terms))
;       (fixed-constraint-term (acl2::subcor-var Out mv-expanded-fixer-terms constraint-term))
       (Vars (reverse (acl2::all-vars constraint-term)))
       ((unless (and (subsetp-eq Vars (union-eq In Out)) (subsetp-eq Out Vars)))
        (er soft ctx "~| Invariant doesnt hold: ~x0 subsetof ~x1 and ~x2 subsetof ~x0~%"
            Vars (union-eq In Out) Out))
       (rule-metadata (list (cons :In In)
                            (cons :Out Out)
                            (cons :fixer-vars (union-eq In Out))
                            (cons :fixer-term fixer-term)
                            (cons :constraint-vars Vars)
                            (cons :constraint-term constraint-term)
                            (cons :fixer-let-binding fixer-binding)))
       (rule-metadata (append kwd-alist rule-metadata))
       (key (cons constraint-term fixer-term))
       (fixer-table-alist (table-alist 'FIXER-RULES-TABLE wrld))
       ((when (assoc-equal key fixer-table-alist))
        (er soft ctx "~| Duplicate entry found in fixer-rules-table: ~x0~%" key))
       (table-ev `((TABLE FIXER-RULES-TABLE ',key ',rule-metadata :put)))
       (hyps (union-equal (defdata::get1 :hyps rule-metadata)
                          (defdata::get1 :test-hyps rule-metadata)))
       ;;(vl (if verbosep 4 (acl2::acl2s-defaults :get :verbosity-level)))
       (vl (if verbosep 4 1))
       (proof-obligation4 (if (> (len Out) 1)
                              `(IMPLIES (AND . ,hyps)
                                        (MV-LET ,Out ,fixer-term
                                                ,constraint-term))
                            `(IMPLIES (AND . ,hyps)
                                      (let ((,(car Out) ,fixer-term))
                                        ,constraint-term))))
       (invariant4-ev `((ACL2S::TEST? ,proof-obligation4
                                     ;:use-fixers nil
                                     :verbosity-level ,vl)))
       ((mv erp guard-ob state) (body-contracts-obligation fixer-term :guard-debug verbosep)) ;needs state
       ((when erp) (er soft ctx "~| guard-obligation error~%"))
       (proof-obligation1 `(IMPLIES (AND . ,hyps) ,guard-ob))
       (invariant1-ev
        `((ACL2S::TEST? ,proof-obligation1
                        ;:use-fixers nil
                        :verbosity-level ,vl)))
       (proof-obligation3 `(IMPLIES (AND . ,hyps)
                                    (LET ,fixer-binding
                                         (declare (ignorable ,@(strip-cars fixer-binding)))
                                         (AND . ,hyps))))
       (invariant3-ev
        (and hyps
             `((ACL2S::TEST? ,proof-obligation3
                             ;:use-fixers nil
                             :verbosity-level ,vl))))
       )
;; Invariants:
;; 1. Body contracts of fixer-term have to be satisfied under hyp-term
;; 2. Vars \subset In \cup Out,  Out \subset Vars
;; 3. hyp-term should be preserved through the fixer changes.
;; 4. rule should be valid under hyp-term -- use thm or at the least test?
    (value (append (and (not override-checkp)
                        `((value-triple (cw? t "~|Test? obligation: Body contracts of fixer term should be satisfied. ~% ~x0~%" ',proof-obligation1))))
                   (and (not override-checkp) invariant1-ev)
                   (and hyps (not override-checkp)
                        `((value-triple (cw? t "~|Test? Obligation: Hypotheses should be preserved through fixer changes. ~x0~%" ',proof-obligation3))))
                   (and (not override-checkp) invariant3-ev)
                   (and (not override-checkp)
                        `((value-triple (cw? t "~|Test? Obligation: Fixer rule should be valid under hypotheses. ~x0~%" ',proof-obligation4))))
                   (and (not override-checkp) invariant4-ev)
                   table-ev))))

#|
For preservation rules:
(defrule perm-preserved
  (implies (and (true-listp X1)
                (true-listp X2)
                (perm X1 X2))
           (perm (rem-dups X1) (rem-dups X2))) ; two fixer terms!!
  :rule-class :preservation)

(defrule perm-preserved
  :hyp (and (true-listp X1)
            (true-listp X2))
  :rule (implies (perm X1 X2)
                 (let ((X1 (rem-dups X1)) ;treated as two separate fixers
                       (X2 (rem-dups X2)))
                   (perm X1 X2)))
  :rule-class :preservation)

(defrule perm-preserved
  :hyp (and (true-listp X1)
            (true-listp X2))
  :rule (implies (perm X1 X2)
                 (mv-let (X1 X2) (MV (rem-dups X1) (rem-dups X2)) ;treated as a single fixer
                         (perm X1 X2)))
  :rule-class :preservation)

(cgen-rule rule-name
  :hyp hyp-term(FVars)
  :rule (implies constraint-term(CVars)
                 (mv-let (Y1 ...) fixer-term_1(In1)
                         constraint-term(CVars)))
  :rule-classes :preservation)

(cgen-rule rule-name
  :hyp hyp-term(FVars \cup Cvars) ??
  :rule (implies constraint-term(CVars)
                 (let ((Y1 fixer-term_1(In1) ...))
                     constraint-term(CVars)))
  :rule-classes :preservation)
Invariants:
1. Body contracts of fixer-term_i have to be satisfied under hyp-term
2. {Y_i} \cap CVars is not empty
3. hyp-term should be preserved through the fixer changes. ??
4. rule should be valid under hyp-term -- use thm or at the least test?

|#



(defun destructure-preservation-rule (rule wrld)
  (declare (ignorable wrld))
  (b* ((`(IMPLIES ,constraint1 ,concl) rule)
       (ctx 'destructure-preservation-rule))
    (cond ((eq (car concl) 'MV-LET)
           (b* ((`(MV-LET ,Out ,single-mv-fixer-exp ,constraint) concl)
                ;(fixer-exps (destruct-mv possible-mv-fixer-exp (len Out) wrld))
                )
             (list :mv Out (list single-mv-fixer-exp) constraint1 constraint)))
          ((eq (car concl) 'LET)
           (b* ((`(LET ,fixer-binding ,constraint) concl)
                (Out (strip-cars fixer-binding))
                (fixer-exps (defdata::strip-cadrs fixer-binding)))
             (list :let Out fixer-exps constraint1 constraint)))
          (t (er hard? ctx "~| ~x0 is not a preservation rule.~%" rule)))))

(defun assoc-equal-lst (keys alist)
  "give back the subset of the alist that correspond to these keys. the order
of the entries is same as of the alist"
  (declare (xargs :guard (and (true-listp keys)
                              (alistp alist))))
  (if (endp alist)
      nil
    (b* (((cons k &) (car alist)))
      (if (member-equal k keys)
          (cons (car alist)
                (assoc-equal-lst keys (cdr alist)))
        (assoc-equal-lst keys (cdr alist))))))

(defun make-cgen-rule-events/preservation (rule kwd-alist override-checkp verbosep ctx wrld state)
  (b* (((list kind Out fixer-exps c1 constraint) (destructure-preservation-rule rule wrld))
       ((unless (equal c1 constraint))
        (er soft ctx "~| ~x0 should be same as ~x1 in a preservation rule.~%"
            c1 constraint))
       ((unless (and (defdata::proper-symbol-listp Out)
                     (> (len Out) 0)))
        (er soft ctx "~| ~x0 is not a non-empty list of variable names.~%" Out))
       ((er constraint-term) (acl2::translate constraint t nil t ctx wrld state))
       ((er fixer-terms)
; Matt K. mod: formerly was ACL2::CMP-TO-ERROR-TRIPLE@PAR, which failed in ACL2(p).
        (ACL2::CMP-TO-ERROR-TRIPLE
         (translate-cmp-lst fixer-exps t nil t ctx wrld (acl2::default-state-vars nil))))

       (mv-expanded-fixer-terms (if (and (eq kind :mv)
                                         (= 1 (len fixer-terms)))
                                    (destruct-mv (car fixer-terms) (len Out) wrld)
                                  fixer-terms))
       (fixer-binding (acl2::listlis Out mv-expanded-fixer-terms))
       (Vars (reverse (acl2::all-vars constraint-term)))
       ((unless (and (intersectp-equal Out Vars)))
        (er soft ctx "~| Invariant does not hold: ~x1 should have a common member with ~x0~%" Vars  Out))
       (rule-metadata (list (cons :Out Out)
                            (cons :constraint-vars Vars)
                            (cons :constraint-term constraint-term)
                            (cons :fixer-terms fixer-terms)
                            (cons :fixer-let-binding fixer-binding)))
       (rule-metadata (append kwd-alist rule-metadata))
       (key (cons constraint-term fixer-terms)) ; use all the fixer-terms
       (p-table-alist (table-alist 'PRESERVATION-RULES-TABLE wrld))
       ((when (assoc-equal key p-table-alist))
        (er soft ctx "~| Duplicate entry found in preservation-rules-table: ~x0~%" key))
       (table-ev `((TABLE PRESERVATION-RULES-TABLE ',key ',rule-metadata :put)))
       (hyps (union-equal (defdata::get1 :hyps rule-metadata)
                          (defdata::get1 :test-hyps rule-metadata)))
       ;;(vl (if verbosep 4 (acl2::acl2s-defaults :get :verbosity-level)))
       (vl (if verbosep 4 1))
       (relevant-fixer-binding (assoc-equal-lst (intersection-eq Out Vars) fixer-binding))
       (proof-obligation4 `(IMPLIES (AND ,@(append hyps (list constraint-term)))
                                    (LET ,relevant-fixer-binding
                                         ,constraint-term)))
       (invariant4-ev `((ACL2S::TEST? ,proof-obligation4
                                     ;:use-fixers nil
                                     :verbosity-level ,vl)))
       ((er guard-ob) (body-contracts-obligation (cons ''t fixer-terms) :guard-debug verbosep)) ;needs state
       (proof-obligation1 `(IMPLIES (AND . ,hyps) ,guard-ob))
       (invariant1-ev `((ACL2S::TEST? ,proof-obligation1
                                      ;:use-fixers nil
                                      :verbosity-level ,vl)))
       ;(invariant3-ev `(ACL2S::TEST? (IMPLIES (AND . ,hyps) (LET ,fixer-binding (AND . ,hyps))) :verbosity-level ,vl))
       )
;; Invariants:
;; 1. Body contracts of fixer-term_i have to be satisfied under hyp-term
;; 2. FVars=\bigcup_i Vars(fixer-term_i), {Y_i} \subset CVars
;; 3. hyp-term should be preserved through the fixer changes. ??
;; 4. rule should be valid under hyp-term -- use thm or at the least test?

    (value (append (and (not override-checkp)
                        `((value-triple (cw? t "~|Test? obligation: Body contracts of fixer term should be satisfied. ~% ~x0~%" ',proof-obligation1))))
                   (and (not override-checkp) invariant1-ev)
                   ;;invariant3-ev
                   (and (not override-checkp)
                        `((value-triple (cw? t "~|Test? Obligation: Preservation rule should be valid under hypotheses. ~x0~%" ',proof-obligation4))))
                   (and (not override-checkp) invariant4-ev)
                   table-ev))))


(defun make-cgen-rule-events (rule rule-class kwd-alist
                                   override-checkp verbosep ctx wrld state)
  (cond ((eq rule-class :fixer)
         (make-cgen-rule-events/fixer rule kwd-alist
                                      override-checkp verbosep ctx wrld state))
        ((eq rule-class :preservation)
         (make-cgen-rule-events/preservation rule kwd-alist
                                             override-checkp verbosep ctx wrld state))
        (t (er soft ctx "~| Unindentified rule-class: ~x0~%" rule-class))))

(defun cgen-rule-events (name keys verbosep wrld state)
  (declare (xargs :mode :program))
  (b* ((ctx 'cgen-rule)
       ((mv kwd-alist rest)
        (defdata::extract-keywords ctx *cgen-rule-keywords* keys nil nil))
       ((when rest) (er soft ctx "~| Unsupported/Extra args: ~x0~%" rest))
       (- (cw? verbosep "~|Got kwd-alist: ~x0~%" kwd-alist))
       ;; ((unless (well-formed-type-metadata-p kwd-alist wrld))
       ;;  (er soft ctx "~| ~s0~%" (ill-formed-type-metadata-msg kwd-alist wrld)))
       (rule (defdata::get1 :rule kwd-alist))

       (pre (or (defdata::get1 :meta-precondition kwd-alist) 't))
       ((unless (pseudo-termp pre))
        (er soft ctx "~| meta-precondition ~x0 should be a pseudo-termp~%" pre))

       (hyp (or (defdata::get1 :hyp kwd-alist) 't))
       ((unless (pseudo-termp hyp))
        (er soft ctx "~| hyp ~x0 should be a pseudo-termp~%" hyp))
       (hyps (if (and (consp hyp) (eq (car hyp) 'ACL2::AND))
                 (cdr hyp)
               (if (equal hyp 't)
                   nil
                 (list hyp)))) ;TODO naive

       (test-hyp (or (defdata::get1 :test-hyp kwd-alist) 't))
       ((unless (pseudo-termp test-hyp))
        (er soft ctx "~| test-hyp ~x0 should be a pseudo-termp~%" test-hyp))
       (test-hyps (if (and (consp test-hyp) (eq (car test-hyp) 'ACL2::AND))
                      (cdr test-hyp)
                    (if (equal test-hyp 't)
                        nil
                      (list test-hyp)))) ;TODO naive

       

       (rule-class (defdata::get1 :rule-classes kwd-alist))
       ((unless (member-eq rule-class *cgen-rule-classes*))
        (er soft ctx "~| rule-class ~x0 should be one of ~x1~%" rule-class *cgen-rule-classes*))
       ((er events) (make-cgen-rule-events rule
                                      rule-class
                                      (list (cons :meta-precondition pre)
                                            (cons :rule-name name)
                                            (cons :hyps hyps)
                                            (cons :test-hyps test-hyps))
                                      (defdata::get1 :override-check kwd-alist)
                                      verbosep ctx wrld state))
       (program-mode-p (eq :program (default-defun-mode wrld))))
    (value (cons 'PROGN
                 (append (and program-mode-p '((LOGIC)))
                         events
                         (and program-mode-p '((PROGRAM)))
                         `((VALUE-TRIPLE (list :registered ',name))))))))



(defun fixer-rules-table (wrld)
  (table-alist 'FIXER-RULES-TABLE wrld))

(defun preservation-rules-table (wrld)
  (table-alist 'PRESERVATION-RULES-TABLE wrld))
