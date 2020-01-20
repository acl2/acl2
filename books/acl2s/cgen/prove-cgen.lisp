#|$ACL2s-Preamble$;
;;Author - Harsh Raju Chamarthi (harshrc)
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "../portcullis")
(begin-book t :ttags :all);$ACL2s-Preamble$|#

(in-package "CGEN")

(include-book "cgen-search")
(include-book "callback")
(include-book "acl2s-parameter")
               
(set-state-ok t)  


;;list comprehension syntax
;; (and (true-listp vs)
;;      (null |[x : x in vs :  (not (possible-defdata-type-p x))]|))
 
;NOTE 
#||
(acl2::state-global-let*
                    ((acl2::inhibit-output-lst
                      ,(if (system-debug-flag vl)
                          ''(summary)
                        ;;shut everything except error
                        ''(warning warning! observation prove
                                  proof-builder event history
                                  proof-tree summary)))) 
                    
;doesnt work on an make-event
||#


;-------------------------PRINT----------------------------------
;-------------------------start----------------------------------


;; translating bindings in terms of original top goal free variables
;; added  a flag indicating wether we are printing counterexamples or witnesses
;; changed |dont care| to ? --Nov26th
;; counteregp is a flag which tells us that bindings 
;; that we found is for a counterexample
;; and is for a witness otherwise. This helps us in checking if the
;; top-goal bindings and the top-goal orig-clause are consistent 
;; with the subgoal bindings result.
;; Pre-condition var-term-alst is in proper let* order, o.w let*
;; complains
;; April 30 '12: Return to simple trans-eval with state
;; we dont care about efficiency wrt ev-w because we only ever print
;; a small number of cts/wts.
;; May 13th '12 : better naming

(program) ;; all print functions are program mode funs

(set-verify-guards-eagerness 1)

(defun get-top-level-assignment (A top-vars top-term 
                                   elided-var-map counteregp state)
  (declare (xargs :stobjs (state)
                  :guard (and (symbol-alistp elided-var-map)
                              (symbol-listp top-vars)
                              (booleanp counteregp)
                              (symbol-doublet-listp A))))
  
  (b* ((new+elim (all-vars `(list ,@(strip-cadrs elided-var-map))))
       (bound (strip-cars (append A elided-var-map)))
       (not-bound (set-difference-eq (union-eq new+elim top-vars) bound))
       (nil-A (make-constant-value-let-bindings not-bound 'acl2::? nil))
       (A (append nil-A A))
       (A (quote-conses-and-symbols-in-bindings A))
       (bound (strip-cars A))
;filter out entries due to generalization and cross-fertilization
       (elided-var-map (remove-entry-lst bound
;if its already bound why bind it again
                                         (filter-symbol-keys-in-alist 
                                          elided-var-map)))
       (A (append A elided-var-map))
      
;; ;TODO: ASK Matt, why is generalization not being captured.
;; ;Maybe bug in my code!!? CHECK
;; (thm (implies (true-listp x)
;;               (equal (rev (rev x)) x))) 

       ((mv top-hyps top-concl state) (partition-into-hyps-concl-and-preprocess top-term "print-assignment" state))

       (mv-sig-alist (mv-sig-alist (cons top-concl top-hyps) (w state)))
       (hyp/m   (mv-list-ify (single-hypothesis top-hyps) mv-sig-alist))
       (concl/m (mv-list-ify top-concl mv-sig-alist))
       
       ((mv ?er res state) 
        (acl2::state-global-let*
;         ((acl2::guard-checking-on :none))
;; PETE: now controlled by the global cgen::cgen-guard-checking
         ((acl2::guard-checking-on (@ cgen-guard-checking)))
         (trans-eval
          `(let* ,A
             (declare (ignorable ,@(strip-cars A)))
             (list ,hyp/m ,concl/m
; make list/let A (list `(var ,var) ...) 
                   ,(make-var-value-list-bindings top-vars nil)))
          'get-top-level-assignment state T))) ;defattach ok

       ((list hyps-res concl-res top-A) (cdr res))
       (consistent? (if counteregp
                        (and hyps-res (not concl-res))
                      (and hyps-res concl-res))))

;  in
    (value (list consistent? top-A))))


(include-book "misc/evalable-printing" :dir :system)


;; Print the random instantiations for a particular test run.
;; Return value is a dummy error-triple. 
;; This function is called for side-effect only(printing IO)
;; Binding == (var val) 
;; added a flag wether bindings are for a counter-example or not
;; Sep 5th 2011 - removed state, and use cw?
;; April 30 2012 - put back state!
(defun print-assignment (A top-vars top-term elided-var-map
                           vl counteregp state)
  (declare (xargs :stobjs (state)
                  :guard (and (symbol-doublet-listp A)
                              (implies (consp A) (consp (car A)))
                              (symbol-alistp elided-var-map)
                              (symbol-listp top-vars)
                              (booleanp counteregp))))
                              
;the usual, but filter the variables that are in the original output clause
  (b* ((top-A (filter-alist-keys A top-vars))
       (vals  (acl2::make-evalable-lst-how (strip-cadrs top-A) (acl2::get-evalable-printing-abstractions state)))
       (?top-A (list-up-lists (strip-cars top-A) vals))
;; [2015-07-29 Wed] Always check for inconsistency
       ;; ((unless elided-var-map) ;the simple case
       ;;  (value (cw? (normal-output-flag vl)
       ;;              "~| -- ~x0~%" top-A)))
                    ;;;"~| -- ~&0~%" top-A)))
  
;show top goal, show counterexamples and witness in 
;terms of the original free variables(of the top clause)
       ((er (list consistent? top-A)) (get-top-level-assignment A top-vars top-term elided-var-map counteregp state))
       (vals  (acl2::make-evalable-lst-how (strip-cadrs top-A) (acl2::get-evalable-printing-abstractions state)))
       (top-A (list-up-lists (strip-cars top-A) vals))
       ((when consistent?)
        (value (cw? (normal-output-flag vl)
                    "~| -- ~x0~%" top-A)))
                    ;;;"~| -- ~&0~%"  top-A)))
       )
    (if counteregp
        (progn$
         (cw? (normal-output-flag vl)
              "~| -- ~x0~%"  top-A)
         (cw? (normal-output-flag vl)
"~|Note: The above counterexample is not consistent with the top-level form. ~
 Counterexamples are only guaranteed to be consistent with subgoals.~%")
         (value nil))
      (progn$
       (cw? (normal-output-flag vl)
            "~| -- ~x0~%"  top-A)
       (cw? (normal-output-flag vl)
"~|Note: The above witness is not consistent with the top-level form. ~
 Witnesses are only guaranteed to be consistent with subgoals.~%")
       (value nil))
       )))



;added a flag indicating wether we are printing counterexamples or witnesses
(defun print-assignments (A-lst top-vars top-term 
                               elided-var-map vl counteregp state)
;perfix-A is assignments made incrementally in dpll search
  (declare (xargs :stobjs (state)
                  :guard (and (symbol-alist-listp A-lst)
                              (symbol-listp top-vars)
                              (natp vl)
                              (symbol-alistp elided-var-map)
                              (booleanp counteregp))))
   (if (endp A-lst)
     (value nil)
     (er-progn
      (print-assignment (car A-lst) top-vars top-term
                        elided-var-map vl counteregp state)
      (print-assignments (cdr A-lst) top-vars top-term
                          elided-var-map vl counteregp state))))
(logic)


; 30th Aug '12 keep global track of num of wts/cts to print
(def print-cts/wts-subgoals (s-hist cts-p nc nw top-vars top-term vl state)
  (decl :mode :program
        :sig ((s-hist-p booleanp symbol-listp all natp state) 
              -> (mv erp all state))
        :doc "print all cts/wts A (sigma) in s-hist subgoal testing
        history alist")
  (if (endp s-hist)
      (value nil)
    (b* (((cons name s-hist-entry%) (car s-hist))
         (test-outcomes% (access s-hist-entry% test-outcomes))
         (hyps      (access s-hist-entry% hyps))
         (concl     (access s-hist-entry% concl))
         ((when (and cts-p (zp nc)))
; number of cts yet to be printed is zero, skip 
          (value nil))
         ((when (and (not cts-p) (zp nw))) 
; number of wts yet to be printed is zero, skip 
          (value nil))
         
         (A-lst (if cts-p 
                    (access test-outcomes% cts)
                  (access test-outcomes% wts)))
         (elide-map (access s-hist-entry% elide-map))
         (- (cw? (system-debug-flag vl) 
"~|Cgen/SYSDEBUG/print-cts/wts-subgoals: A-lst:~x0 top-vars:~x1 elide-map:~x2~|" 
A-lst top-vars elide-map))
         ((when (endp A-lst)) 
; none found, so move on to the next subgoal
          (print-cts/wts-subgoals (cdr s-hist) cts-p 
                                  nc nw top-vars top-term vl state))
         (nc (- nc (if cts-p (len A-lst) 0)))
         (nw (- nw (if cts-p 0 (len A-lst))))
         (- (cw? (normal-output-flag vl) "~| [found in : ~x0]~%" name))
         (cl (clausify-hyps-concl hyps concl))
         (pform (acl2::prettyify-clause cl nil (w state)))
         (- (cw? (and (not (equal "top" name))
                      cts-p
                      (normal-output-flag vl)) "~x0~%" pform))
         )
     (er-progn
      (print-assignments A-lst top-vars top-term elide-map vl cts-p state)
      (print-cts/wts-subgoals (cdr s-hist) cts-p nc nw top-vars top-term vl state)))))

(program)
; adapted from acl2/axioms.lisp
(defun rational-to-decimal-string (x)
  (let ((x00 (round (* 100 (abs x)) 1)))
    (b* ((prefix (if (< x 0) "-" ""))
         (integer-part (cond ((> x00 99) (to-string (floor (/ x00 100) 1)))
                             (t "0")))
         (r (rem x00 100))
         (fractional-part (cond ((< r 10) (concatenate 'acl2::string "0" (to-string r)))
                               (t (to-string r)))))
      (concatenate 'acl2::string prefix integer-part "." fractional-part))))


;; [2015-04-07 Tue]
;; [2016-08-30 Tue] Removed restriction to vacuous test cases.
(defun print-sat-stats-hyps (hyps kinds total hyp->sat)
;  Hypothesis | Type of Constraint | Negated | Sat/Total
  (if (endp hyps)
      nil
    (b* ((hyp (car hyps))
         (kind (car kinds))
         (num-sat (cdr (assoc-equal hyp hyp->sat)))
         (p (if (= total 0) "100" (rational-to-decimal-string (* 100 (/ num-sat total)))))
         )
      (prog2$ ;in Awk use ; as the field separator
       (cw! "~|Constraint;~f0 ~|Kind;~f1;Percentage;~s4;Sat/Total;~x2/~x3~%" hyp kind num-sat total p)
       (print-sat-stats-hyps (cdr hyps) (cdr kinds) total hyp->sat)))))

(defun update-hyps->num-sat (hyp-vals hyps hyp->num-sat)
  "for each T value of hyp, increment its num-sat"
  (declare (xargs :guard (and (true-listp hyp-vals)
                              (pseudo-term-listp hyps)
                              (alistp hyp->num-sat)
                              (= (len hyp-vals) (len hyps)))))
  (if (endp hyp-vals)
      hyp->num-sat
    (if (car hyp-vals) ;true
        (b* ((n (nfix (cdr (assoc-equal (car hyps) hyp->num-sat)))))
          (update-hyps->num-sat (cdr hyp-vals) (cdr hyps)
                              (put-assoc-equal (car hyps) (1+ n) hyp->num-sat)))
      (update-hyps->num-sat (cdr hyp-vals) (cdr hyps) hyp->num-sat))))
      

  
(defun print-sat-stats/subgoal (hyp-vals-list hyps kinds total hyp->num-sat)
  (if (endp hyp-vals-list)
      (print-sat-stats-hyps hyps kinds total hyp->num-sat)
    (b* ((hyp-vals (car hyp-vals-list))
         (hyp->num-sat (update-hyps->num-sat hyp-vals hyps hyp->num-sat)))
      (print-sat-stats/subgoal (cdr hyp-vals-list) hyps kinds total hyp->num-sat))))



; The following two functions are by Matt K. [2015-04-07 Tue]
#!ACL2
(defun boolean-fn-symb-1 (tp-lst) ; helper function
  (cond ((endp tp-lst) nil)
        ((let ((tp (car tp-lst)))
           (and (ts-subsetp (access type-prescription tp :basic-ts)
                            *ts-boolean*)
                (null (access type-prescription tp :hyps))
                (null (access type-prescription tp :vars)))))
        (t (boolean-fn-symb-1 (cdr tp-lst)))))
#!ACL2
(defun boolean-fn-symb (fn wrld)
  (cond
   ((assoc-eq fn *primitive-formals-and-guards*)
    (or (eq fn 'bad-atom<=)
        (eq fn '<)
        (eq fn 'equal)

; The following is right, by inspection.  Perhaps it would be better though to
; enumerate the appropriate symbols.

        (let ((name (symbol-name fn)))
          (eql (char name (1- (length name)))
               #\P))))
   (t
    (let ((tp-lst (getprop fn 'type-prescriptions nil 'current-acl2-world wrld)))
      (boolean-fn-symb-1 tp-lst)))))

(defun assoc-fn-p (f)
  (member-eq f '(ACL2::ASSOC-EQUAL ACL2::ASSOC-EQ)))

(defun subsetp-fn-p (f)
  (member-eq f '(ACL2::SUBSETP-EQUAL ACL2::SUBSETP-EQ)))

(defun intersectp-fn-p (f)
  (member-eq f '(ACL2::INTERSECTP-EQUAL ACL2::INTERSECTP-EQ)))

(defun equal-fn-p (f)
  (member-eq f '(ACL2::EQUAL ACL2::= ACL2::EQ ACL2::EQL)))

(defun mem-fn-p (R)
  (member-eq R '(acl2::member-eq acl2::member acl2::member-eql acl2::member-equal acl2s::in |ACL2S B|::in)))

(defun subclassify-binary-relation (f args)
  (b* (((when (equal-fn-p f))
        (if (or (proper-symbolp (first args)) (proper-symbolp (second args)))
            (list :EQUAL/VAR)
          (list  :EQUAL)))
       ((when (assoc-fn-p f))
        (if (proper-symbolp (first args))
            (list :ASSOC/VAR)
          (list  :ASSOC)))
       ((when (mem-fn-p f))
        (if (proper-symbolp (first args))
            (list :MEMBER/VAR)
          (list :MEMBER)))
       ((when (member-eq f '(ACL2::<)))
        (if (or (proper-symbolp (first args)) (proper-symbolp (second args)))
            (list :LESS/VAR)
          (list :LESS)))
       ((when (intersectp-fn-p f))
        (list  :INTERSECTP))
       ((when (subsetp-fn-p f))
        (list  :SUBSETP))
       )
    '()))

(defun classify-hyp/kinds (f args wrld)
  "report all kinds that satisfy (f @args)"
  (b* ((arity (len args))
       ((unless (symbolp f))
        (list :LAMBDA-APPLICATION)) ;can it be something else

       ((when (defdata::is-type-predicate f wrld))
        (list :MONADIC/DEFDATA-TYPE))
       ((when (and (equal arity 1)))
        (if (acl2::boolean-fn-symb f wrld)
            (list :MONADIC/PREDICATE)
          (list :MONADIC)))
       ((when (and (equal arity 2)))
        (if (acl2::boolean-fn-symb f wrld)
            (list*  :BINARY/PREDICATE (subclassify-binary-relation f args))
          (list* :BINARY (subclassify-binary-relation f args))))
       ((when (and (equal arity 3)))
        (if (eq f 'ACL2::IF)
            (list :TERNARY/IF)
          (if (acl2::boolean-fn-symb f wrld)
              (list :TERNARY/PREDICATE)
            (list :TERNARY))))
       ((when (and (> arity 3) (acl2::boolean-fn-symb f wrld)))
        (list :>3-ARY-RELATION)))
    (list :UNKNOWN)))


(defun classify-hyp (hyp negp wrld)
  "classify hyp as one of Equality, Arithmetic Inequality, defdata type, monadic predicate, n-ary Relation, unknown"
  (declare (xargs :guard (and (pseudo-termp hyp)
                              (booleanp negp)
                              (plist-worldp wrld))))
  (cond ((atom hyp) (append (if negp '(:NEG) '(:POS)) '(:SHALLOW :ATOMIC-VARIABLE)))
        ((equal (acl2::ffn-symb hyp) 'ACL2::NOT) (classify-hyp (cadr hyp) (not negp) wrld))
        (t (b* ((f (ffn-symb hyp))
                (args (fargs hyp))
                (shallow-p (proper-symbol-listp args))
                (neg+shallow (append (if negp '(:NEG) '(:POS)) (if shallow-p '(:SHALLOW) '(:NON-SHALLOW)))))
             (append neg+shallow (classify-hyp/kinds f args wrld))))))

(defun classify-hyps (hyps wrld)
  (if (endp hyps)
      '()
    (cons (classify-hyp (car hyps) nil wrld)
          (classify-hyps (cdr hyps) wrld))))
  
(defun print-sat-stats/subgoals (s-hist vl wrld)
  (if (endp s-hist)
      nil
    (b* (((cons name s-hist-entry%) (car s-hist))
         (test-outcomes% (access s-hist-entry% test-outcomes))
         (hyps      (access s-hist-entry% hyps))
         (concl      (access s-hist-entry% concl))
         (vacs-hyp-vals-list (access test-outcomes% vacs-hyp-vals-list))
         (cts-hyp-vals-list (access test-outcomes% cts-hyp-vals-list))
         (wts-hyp-vals-list (access test-outcomes% wts-hyp-vals-list))
         (all-hyp-vals-list (append cts-hyp-vals-list
                                    wts-hyp-vals-list
                                    vacs-hyp-vals-list))
         (|#vacs| (access test-outcomes% |#vacs|))
         (total-runs/subgoal (+ |#vacs|
                                (access test-outcomes% |#dups|)
                                (access test-outcomes% |#cts|)
                                (access test-outcomes% |#wts|)))
         (sat% (if (<= total-runs/subgoal 0)
                   "100"
                 (rational-to-decimal-string
                  (* 100 (/ (- total-runs/subgoal |#vacs|) total-runs/subgoal)))))
         (cl (clausify-hyps-concl hyps concl))
         (pform (acl2::prettyify-clause cl nil wrld))

         (disp-enum-alist (access test-outcomes% disp-enum-alist))
         (elim-bindings   (access test-outcomes% elim-bindings))
         
         (hyp->num-sat (pairlis$ hyps (make-list (len hyps) :initial-element 0)))
         (kinds (classify-hyps hyps wrld))
         )
      (progn$
       (cw? (verbose-stats-flag vl) "~|__SUBGOAL_BEGIN__~%")
       (cw? (verbose-stats-flag vl) "SUBGOAL_NAME;~f0;SAT%;~s1~%" name sat%)
       (cw? (verbose-stats-flag vl) "~x0~%" pform)
       (cw? (verbose-stats-flag vl) "Enum: ~%~x0~%"  disp-enum-alist)
       (cw? (and (verbose-stats-flag vl) elim-bindings)
            "Elim/Fixer: ~%~x0~%~%"  elim-bindings)
       (print-sat-stats/subgoal all-hyp-vals-list hyps kinds total-runs/subgoal hyp->num-sat)
       (cw? (verbose-stats-flag vl) "~|__SUBGOAL_END__~%" )
       (print-sat-stats/subgoals (cdr s-hist) vl wrld)))))

(logic)


(def print-s-hist (s-hist printc? printw? nc nw 
                          top-term top-vars top-ctx vl state)
;nc and nw are the number of cts/wts requested by user (acl2s defaults)
  (decl :mode :program
        :sig ((s-hist-p bool bool natp natp 
                        pseudo-termp symbol-list fixnum state) 
              -> (mv erp all state))
        :doc "print counterexample and witnesses recorded in testing subgoal
history s-hist.")
  (b* (((er &) (if printc?
                   (prog2$
                    (cw? (normal-output-flag vl)
"~|~%We falsified the conjecture. Here are counterexamples:~|")
                    (print-cts/wts-subgoals s-hist T nc nw top-vars top-term vl state))
                 (value nil)))

       ((er &) (if printw?
                   (prog2$
                    (cw? (normal-output-flag vl)
"~|~%Cases in which the conjecture is true include:~|")
                    (print-cts/wts-subgoals s-hist NIL nc nw top-vars top-term vl state))
                 (value nil)))
;       (event-name (get-event-name-from-ctx top-ctx))
       (- (and (verbose-stats-flag vl)
               (progn$
                (cw "~%__Vacuous_test_statistics_BEGIN__~%")
                (cw "~|CTX;~f0~%" (if (and (consp top-ctx)) (cdr top-ctx) top-ctx)) 
                (print-sat-stats/subgoals s-hist vl (w state))
                (cw "~|__Vacuous_test_statistics_END__~%")))))
    (value nil)))

(logic)

  
;for trace$ debugging - remove when satisfied 
(defun my+ (a b) (+ a b))
(defun my- (a b) (- a b))

(def total-time-spent-in-testing (s-hist)
  (decl :sig ((s-hist-p) -> rationalp)
        :doc "calculate testing time across subgoals")
  (if (endp s-hist)
      0
    (b* (((cons & s-hist-entry%) (car s-hist)))
     (my+ (my- (access s-hist-entry% end-time)
               (access s-hist-entry% start-time))
          (total-time-spent-in-testing (cdr s-hist))))))
      
  

(defun print-testing-summary-fn (cgen-state ctx state)
  (declare (xargs :mode :program
                  :stobjs (state)))
  (b* ((s-hist (cget s-hist))
;when testing errored out or timed out, theres no point of printing.
       (gcs%   (cget gcs))
       (vl     (cget verbosity-level))
       (- (cw? (debug-flag vl) "~|testing summary - gcs% = ~x0~%" gcs%))
       (- (cw? (debug-flag vl) "~|testing summary - s-hist = ~x0~%" s-hist))
       ((unless (and (consp s-hist) (consp (car s-hist))
                     (> (access gcs% runs) 0)))
        (value (cw? (debug-flag vl) 
"~|CEgen/Debug (~x0): No testing summary to print~|" ctx)))
                  
       (num-subgoals (len s-hist))
       (start (cget start-time))
       (end (cget end-time))
       
       )
   (case-match gcs%
     (('gcs% (total dups . vacs) 
             (num-cts . num-wts))
;ACHTUNG: gcs% defrec exposed
      (b* ((uniq-runs  (my+ num-wts num-cts))
           (sat-runs (my- total (my+ vacs dups)))
           (delta-t-total (my- end start))
           (delta-testing-t-total (total-time-spent-in-testing s-hist))
           (top-term (cget user-supplied-term))
           (top-vars (all-vars top-term))
           (pform (acl2::prettyify-clause ;or should we rather use displayed-goal?
                   (list top-term) nil (w state)))
           ((unless (consp top-vars))
            (b* ((res (if (> num-cts 0) nil t)))
              (value (cw? (normal-output-flag vl) 
"~% ~x0 evaluates to ~x1. Nothing to test!~%" pform res))))

           
           (-  (cw? (normal-output-flag vl) 
                    "~%**Summary of Cgen/testing**~%"))
           (- (cw? (verbose-flag vl)
                   "~x0~%" pform))
           (- (cw? (normal-output-flag vl)
               "~|We tested ~x0 examples across ~x1 subgoals, of which ~x2 (~x3 unique) satisfied the hypotheses, and found ~x4 counterexamples and ~x5 witnesses.~%"
               total num-subgoals sat-runs uniq-runs num-cts num-wts))

           (- (cw? (verbose-flag vl)
               "~|The total time taken (incl. prover time) is "))
; from Matt's save-time book
           ((er &) (if (verbose-flag vl)
                       (pprogn (print-rational-as-decimal delta-t-total
                                                      (standard-co state)
                                                      state)
                           (princ$ " seconds" (standard-co state) state)
                           (newline (standard-co state) state)
                           (value :invisible))
                     (value nil)))

           (- (cw? (verbose-flag vl)
               "~|The time taken by testing is "))
           ((er &) (if (verbose-flag vl)
                       (pprogn (print-rational-as-decimal delta-testing-t-total
                                                      (standard-co state)
                                                      state)
                           (princ$ " seconds" (standard-co state) state)
                           (newline (standard-co state) state)
                           (value :invisible))
                     (value nil)))
           ((mv cts-to-print wts-to-print) (mv (cget num-print-counterexamples) (cget num-print-witnesses)))
           (top-ctx (cget top-ctx))
           ((er &)  (print-s-hist s-hist 
                                  (and (> cts-to-print 0) (> num-cts 0));print cts if true
                                  (and (> wts-to-print 0) (> num-wts 0));print wts if true
                                  cts-to-print wts-to-print 
                                  top-term top-vars top-ctx
                                  vl state)))
       (value nil)))
     (& (value (cw? (normal-output-flag vl) "~|CEgen/Error: BAD gcs% in cgen-state.~|"))))))


;----------------------------------------------------------------
;                         PRINT end                             |
;----------------------------------------------------------------



(logic)

;; (defun keywordify (sym)
;;   (declare (xargs :guard (symbolp sym)))
;;   (acl2s::fix-intern-in-pkg-of-sym (symbol-name sym) :key))

;; (defun keywordify-lst (syms)
;;   (declare (xargs :guard (symbol-listp syms)))
;;   (if (endp syms)
;;       '()
;;     (cons (keywordify (car syms))
;;           (keywordify-lst (cdr syms)))))

(defun make-cgen-params-from-args (kwd-val-lst ans.)
  "Returns alist satisfying cgen-params-p, given args obtained from macro keyword args"
; code modified from extract-keywords from std/util/support.lisp
  (declare (xargs :guard (and (alistp ans.)
                              (keyword-value-listp kwd-val-lst))))
  (b* (((when (atom kwd-val-lst)) ans.)
       (arg1 (first kwd-val-lst))
       (ctx 'make-cgen-params-from-args)
       ((unless (member arg1 acl2s::*acl2s-parameters*)) ;ignore/move-on
        (make-cgen-params-from-args (cddr kwd-val-lst) ans.))
       ((when (atom (rest kwd-val-lst)))
        (er hard? ctx "~x0: keyword ~x1 has no argument." ctx arg1))
 
       (value (second kwd-val-lst))
       (ans. (acons arg1 value ans.)))
    (make-cgen-params-from-args (cddr kwd-val-lst) ans.)))

(defun make-cgen-state-fn (form ctx-name kwd-val-lst wrld)
  (b* ((override-params (make-cgen-params-from-args kwd-val-lst '()))
       (params (acl2s::acl2s-defaults-value-alist. (table-alist 'ACL2S::ACL2S-DEFAULTS-TABLE wrld) override-params '())))
    (list (cons 'PARAMS params)
          (cons 'USER-SUPPLIED-TERM :undefined)
          (cons 'DISPLAYED-GOAL form)
          (cons 'START-TIME :undefined)
          (cons 'GCS *initial-gcs%*)
          (cons 'TOP-CTX (cons :USER-DEFINED ctx-name)))))

(defmacro make-cgen-state (form ctx-name &rest kwd-val-lst)
  `(make-cgen-state-fn ',form ',ctx-name ',kwd-val-lst (w state)))

(defun update-cgen-state-givens/user-fn (term start top-vt-alist cgen-state)
;  called from below macro
  (b* ((cgen-state (cput user-supplied-term term))
       (cgen-state (cput top-vt-alist top-vt-alist))
       (cgen-state (cput start-time start)))
;   in 
    cgen-state))

(defmacro update-cgen-state-givens/user (&key user-supplied-term start-time top-vt-alist)
    "update cgen-state fields user-supplied-term,top-vt-alist etc"
  (declare (xargs :guard (and user-supplied-term
                              start-time
                              top-vt-alist)))
  `(update-cgen-state-givens/user-fn ,user-supplied-term ,start-time ,top-vt-alist cgen-state))

(defun check-syntax (form logicp state)
  (declare (xargs :mode :program :stobjs (state)))
  (acl2::state-global-let*
   ((acl2::inhibit-output-lst acl2::*valid-output-names*))
   (acl2::translate-ignore-ok form T logicp T "test? check" (w state) state)))

;; TODO: remove code duplication between this function and prove/cgen
(defun test/cgen (form hints cgen-state state)
  (declare (ignore hints))
  (declare (xargs :mode :program :stobjs (state)))
  ;; (decl :mode :program
  ;;       :sig ((any hints cgen-state state) 
  ;;             -> (mv (oneof nil :falsifiable :? t) cgen-state state)))
  (b* ((ctx (cget top-ctx))
       (vl  (cget verbosity-level))
       
       ((unless (equal (cget displayed-goal) form))
        (prog2$ (cw? (normal-output-flag vl) 
                     "~|Cgen/Error: cgen-state.displayed-goal should match the first argument to prove/cgen.~|")
                (mv :? cgen-state state)))
         
       (testing-enabled (cget testing-enabled ))
       ((when (eq testing-enabled NIL)) ;dont do any testing
        (prog2$ (cw? (verbose-flag vl) 
                     "~|Cgen/Note: TESTING-ENABLED is set to NIL; skipping this form altogether.~|")
                (mv :? cgen-state state)))
       ((mv erp term state) (check-syntax form NIL state))
       ((when erp)          
        (prog2$
         (cw? (normal-output-flag vl) 
              "~|Cgen/Error: The input form is ill-formed, see below:")
; show error to user which was invisble earlier
         (acl2::state-global-let*
          ((acl2::inhibit-output-lst '(summary)))
          (acl2::translate form  T NIL T "test? check" (w state) state))))


       ((mv all-execp unsupportedp) 
          (cgen-exceptional-functions (list term) vl (w state)))
; 21st March 2013 - catch stobj taking and constrained functions, skip testing.
       ((unless all-execp)  (mv :? cgen-state state)) ;possible with test? ?
       ((when unsupportedp) (mv :? cgen-state state))
       ((when (acl2::global-val 'acl2::include-book-path (w state)))
        (prog2$ (cw? (verbose-flag vl) 
                      "~|Cgen/Note: Inside include-book; skip testing altogether.~|")
                 (mv :? cgen-state state)))
         
; No syntax error in input form, check for program-mode fns
; Note: translate gives nil as the term if form has
; a program-mode function, so we ignore it
         ((mv pm? & state)    (check-syntax form T state))
         (programp            (or pm?
                                  (eq (default-defun-mode (w state)) 
                                      :program)))

         ((mv hyps concl state) (partition-into-hyps-concl-and-preprocess term "test?" state))
         ((mv start-top state) (acl2::read-run-time state))
         
         ((unless (cgen-state-p cgen-state))
          (er soft ctx "~|Cgen/Error: CGEN::CGEN-STATE is ill-formed~|"))
         
         (vars (all-vars term))
         (d-typ-al (dumb-type-alist-infer (cons (cgen-dumb-negate-lit concl) hyps)
                                          vars vl (w state)))
         (- (cw? (verbose-stats-flag vl) 
                 "~|Cgen/Verbose: (at top-level) dumb type-alist is ~x0~|" d-typ-al))

         (cgen-state (update-cgen-state-givens/user :user-supplied-term term
                                                    :start-time start-top  
                                                    :top-vt-alist d-typ-al))
         (clause (clausify-hyps-concl hyps concl))
         (type-alist (if programp 
                         nil
                       (get-acl2-type-alist clause)))
         (tau-interval-alist (tau-interval-alist-clause-fn clause vars (acl2::ens state) state))

         ((mv error-or-timeoutp cgen-state state) (cgen-search-fn "top" hyps concl 
                                                                  type-alist tau-interval-alist
                                                                  '() 
                                                                   programp 
                                                                   cgen-state 
                                                                   ctx state))
         ((mv end state) (acl2::read-run-time state))
         (cgen-state (cput end-time end))
         (gcs% (cget gcs))
         )
    
    ;;in
    (cond ((posp (access gcs% cts)) (mv :falsifiable cgen-state state))
          (error-or-timeoutp (mv t cgen-state state))
          (t (mv :? cgen-state state)))))




(def prove/cgen (form hints cgen-state state)
  (decl :mode :program
        :sig ((any hints cgen-state state) 
              -> (mv (oneof nil :falsifiable :? t) cgen-state state)))
  (b* ((ctx (cget top-ctx))
       (vl  (cget verbosity-level))

       ((unless (equal (cget displayed-goal) form))
        (prog2$ (cw? (normal-output-flag vl) 
                     "~|Cgen/Error: cgen-state.displayed-goal should match the first argument to prove/cgen.~|")
                (mv :? cgen-state state)))
         
       (testing-enabled (cget testing-enabled ))
       ((when (eq testing-enabled NIL)) ;dont do any testing
        (prog2$ (cw? (verbose-flag vl) 
                     "~|Cgen/Note: TESTING-ENABLED is set to NIL; skipping this form altogether.~|")
                (mv :? cgen-state state)))
       ((mv erp term state) (check-syntax form NIL state))
       ((when erp)          
        (prog2$
         (cw? (normal-output-flag vl) 
              "~|Cgen/Error: The input form is ill-formed, see below:")
; show error to user which was invisble earlier
         (acl2::state-global-let*
          ((acl2::inhibit-output-lst '(summary)))
          (acl2::translate form  T NIL T "test? check" (w state) state))))


       ((mv all-execp unsupportedp) 
          (cgen-exceptional-functions (list term) vl (w state)))
; 21st March 2013 - catch stobj taking and constrained functions, skip testing.
       ((unless all-execp)  (mv :? cgen-state state)) ;possible with test? ?
       ((when unsupportedp) (mv :? cgen-state state))
       ((when (acl2::global-val 'acl2::include-book-path (w state)))
        (prog2$ (cw? (verbose-flag vl) 
                      "~|Cgen/Note: Inside include-book; skip testing altogether.~|")
                 (mv :? cgen-state state)))
         
; No syntax error in input form, check for program-mode fns
; Note: translate gives nil as the term if form has
; a program-mode function, so we ignore it
         ((mv pm? & state)    (check-syntax form T state))
         (programp            (or pm?
                                  (eq (default-defun-mode (w state)) 
                                      :program)))

         (- (cw? (debug-flag vl)
                 "~%~%Cgen/Debug: (pm? ~x0) ~x1~|" programp (cons 'test? form))) 

         ((mv hyps concl state) (partition-into-hyps-concl-and-preprocess term "test?" state))
         ((mv start-top state) (acl2::read-run-time state))
         
         ((unless (cgen-state-p cgen-state))
          (er soft ctx "~|Cgen/Error: CGEN::CGEN-STATE is ill-formed~|"))
         
         (vars (all-vars term))
         (d-typ-al (dumb-type-alist-infer (cons (cgen-dumb-negate-lit concl) hyps)
                                          vars vl (w state)))
         (- (cw? (verbose-stats-flag vl) 
                 "~|Cgen/Verbose: (at top-level) dumb type-alist is ~x0~|" d-typ-al))

         (cgen-state (update-cgen-state-givens/user :user-supplied-term term
                                                    :start-time start-top  
                                                    :top-vt-alist d-typ-al))
         (clause (clausify-hyps-concl hyps concl))
         (type-alist (if programp 
                         nil
                       (get-acl2-type-alist clause)))
         (tau-interval-alist (tau-interval-alist-clause clause vars))
                  
; put cgen-state in state, so that nested testing via events is caught and disallowed.
         (state (f-put-global 'cgen-state cgen-state state))
         ((mv ?error-or-timeoutp cgen-state state) (cgen-search-fn "top" hyps concl 
                                                                   type-alist tau-interval-alist
                                                                   '() 
                                                                   programp 
                                                                   cgen-state 
                                                                   ctx state))
         
; No call to prove if
; 1. stopping condition has already been reached
; 2. form contains a program-mode function or we are in program mode
; 3. testing is set to :naive
         (no-prove-call-p  (or (cget stopping-condition-p)
                               programp
                               (eq testing-enabled :naive)))

         (- (cw? (debug-flag vl) "~|Cgen/Debug: no-prove-call-p: ~x0 override-hints: ~x1~%" no-prove-call-p (acl2::override-hints (w state))))
; TODO: print something if erp is true i.e error in testing
         
; put modified cgen-state back in globals, so that the computed hint
; callback can access it
         (state (f-put-global 'cgen-state cgen-state state)) 


; 2 July '13 (bug: hard error reported as proof without induction)
         ((mv trans-erp prove-erp state) 
          (if no-prove-call-p
              (mv nil t state)
            (mv-let 
             (erp trval state)
             (acl2::state-global-let*
              ((acl2::inhibit-output-lst 
                (cond ((debug-flag vl) '(summary))
                      (t #!acl2(set-difference-eq *valid-output-names* '(error))))))
; Pete: replaced the line below to get rid of annoying "Q.E.D."
; messages when testing.              
;                     (t #!acl2(set-difference-eq *valid-output-names* '(error prove))))))
; Q: Why is here a wrapper call to trans-eval?
; A: To catch some hard errors! (see the email to Matt dated 3/20/2013)
              (trans-eval
               `(let ((wrld (w state))
                      (ens (acl2::ens state)))
;It is quite strange that I need to use "( THM ...)" to simulate THM behavior!!
                  (er-let* ((hints (acl2::translate-hints+ 'ACL2::THM;name-tree
                                                     ',hints
                                                     (acl2::default-hints wrld)
                                                     "( THM ...)" wrld state))
                            
                            (ttree (acl2::prove ',term
;; TODO: Matt's code doesnt work through induction and forcing rds
;; Also the OTF flag is set to true, to test all initial subgoals. 
                                          (acl2::make-pspv ens wrld state
                                                     :displayed-goal ',form
                                                     :otf-flg t)
                                          hints ens wrld "( THM ...)" state)))
                    (value nil)))
               ctx state t))
             ;; mv-let body
             (prog2$
              (cw? (and erp (normal-output-flag vl))
                   "~|Cgen/Error: bad trans-eval wrapper call to prove.~|")
              (mv erp (if erp t (cadr trval)) state)))))

         (cgen-state (@ cgen-state)) ;reify cgen-state from callback

         ((mv end state) (acl2::read-run-time state))
         (cgen-state (cput end-time end))
         (gcs% (cget gcs))

         (state (f-put-global 'cgen-state nil state)) ;We set cgen-state global, its our job to reset it.

         )
    
    ;;in
    (cond ((posp (access gcs% cts)) (mv :falsifiable cgen-state state))
          (trans-erp (mv t cgen-state state))
          ((not prove-erp) (mv nil cgen-state state))
          (t (mv :? cgen-state state)))))



        


;; ;TODO:limit test runs when all cases are exhausted for finite data values
;; (test?
;;  (implies (and (booleanp a) 
;;                (booleanp b))
;;           (equal (implies a b) (or (not a) b)))


;; TODO: 
;; 1. union-find algo in per variable counterexample store,
;;    increasing probability of finding countereg.
;; 5. Registered constructors - check if destructor arguments are
;;     subtypes of dex-prex.
