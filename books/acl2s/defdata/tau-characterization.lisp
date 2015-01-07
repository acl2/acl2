#|$ACL2s-Preamble$;
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "../portcullis")
(acl2::begin-book t);$ACL2s-Preamble$|#

#|
Tau characterization event generation
author: harshrc
file name: tau-characterization.lisp
date created: [2014-08-06 Sun]
data last modified: [2014-08-06]
|#

(in-package "DEFDATA")

(include-book "defdata-core")

;; TAU CHARACTERIZATION EVENT GENERATION

(defun max-list (x)
  (if (atom x)
      -1
    (max (car x)
         (max-list (cdr x)))))

; term should be a pseudo-termp, at the least it should not contain LET or other special forms.
; assume x is in term.
; find max depth of an occurrence of x in term
(mutual-recursion
(defun depth-var (x term)
  (cond ((acl2::variablep term) (if (eq x term) 0 nil))
        ((fquotep term) nil)
        (t (let ((d (max-list (depth-var-lst x (fargs term)))))
             (and (natp d) (1+ d))))))

(defun depth-var-lst (x terms)
  (if (endp terms)
      '()
    (let ((d1 (depth-var x (car terms))))
      (if (natp d1)
          (cons d1 (depth-var-lst x (cdr terms)))
        (depth-var-lst x (cdr terms))))))
)

(defun find-x-terms-=-depth (terms x depth)
  "find terms having x at given depth"
  (if (endp terms)
      '()
     (let ((d (depth-var x (car terms)))) ;if null then x does not appear
       (if (and (natp d) (= depth d))
        (cons (car terms) (find-x-terms-=-depth (cdr terms) x depth))
      (find-x-terms-=-depth (cdr terms) x depth)))))

 
(defun find-x-terms->=-depth (terms x depth)
  "find terms having x at greater than or equal to given depth"
  (if (endp terms)
      '()
    (let ((d (depth-var x (car terms)))) ;if null then x does not appear
    (if (and (natp d) (<= depth d))
        (cons (car terms) (find-x-terms->=-depth (cdr terms) x depth))
      (find-x-terms->=-depth (cdr terms) x depth)))))

(defloop nested-functional-terms-with-vars-p (es vs)
  (for ((v in vs)) (thereis (find-x-terms->=-depth es v 2))))

(defun union-lst (lsts)
  (declare (xargs :mode :logic
                  :guard (true-list-listp lsts)))
  (if (endp lsts)
    nil
    (union-equal (car lsts)
                 (union-lst (cdr lsts)))))

(defloop get-conx-name (pred C) ;fails to take into account aliases!
  (for ((entry in C)) (thereis (and (eq pred (get1 :recog (cdr entry))) (car entry)))))


(defun recognizer-call-with-var (call var C)
;  (let ((acl2::var var))
    (case-match call
      ((P x) (and (equal x var) (get-conx-name P C) call))
      (& nil)))

(defloop governing-recognizer-call-with-var (terms x C) ;cheat: just give the first
  (for ((term in terms)) (thereis (recognizer-call-with-var term x C))))



       
  
;Tell J this problem TODO
(DEFUN DUMBer-NEGATE-LIT (TERM)
  (COND ((acl2::VARIABLEP TERM)
         (acl2::FCONS-TERM* 'NOT TERM))
        ((FQUOTEP TERM)
         (COND ((EQUAL TERM NIL) t)
               (T NIL)))
        ((EQ (FFN-SYMB TERM) 'NOT)
         (acl2::FARGN TERM 1))
        ;; ((AND (EQ (FFN-SYMB TERM) 'EQUAL)
        ;;       (OR (EQUAL (FARGN TERM 2) NIL)
        ;;           (EQUAL (FARGN TERM 1) NIL)))
        ;;  (IF (EQUAL (FARGN TERM 2) NIL)
        ;;      (FARGN TERM 1)
        ;;      (FARGN TERM 2)))
        (T (acl2::FCONS-TERM* 'NOT TERM))))

(defloop dumber-negate-lit-lst (terms)
  (for ((term in terms)) (collect (dumber-negate-lit term))))

(program)
(defun break-one-destructor-nest (es x C)
  (b* ((recog-call (governing-recognizer-call-with-var es x C))
       ((unless recog-call) (mv nil nil es nil))
       (es (remove-equal recog-call es))
       (recog (ffn-symb recog-call))
       (conx (get-conx-name recog C))
       (dest-pred-alist (get2 conx :dest-pred-alist C))
       (k (len dest-pred-alist))
       (dex-calls (list-up-lists (strip-cars dest-pred-alist) (make-list k :initial-element x)))
       (x1--xk (numbered-vars x k))
       (cons-x (cons conx x1--xk))
       (sub-alist (pairlis$ dex-calls x1--xk))
       (es (acl2::sublis-expr-lst sub-alist es))
       (x-terms (find-x-terms->=-depth es x 0))) ;find remaining x terms
    (mv cons-x x1--xk es x-terms)))


(defun tau-rule-AND-terms=>Px (es P x C)
  (b* ((fes (find-x-terms->=-depth es x 2)))
     (if (> (len fes) 1) ;def not a tau rule -- see if we can dest-elim
         (b* (((mv cons-x x1--xk dest-es remaining-x-es) (break-one-destructor-nest es x C)))
           (if cons-x ;dest-elim 1 round successful
               (cond (remaining-x-es
                      (prog2$ ;check this
                       (cw "~| Presence of ~x0 precludes a tau characterization of ~x1~%" remaining-x-es P)
                       "Multiple sig terms i.e. (P1 (f x1 ...)) \/ (P2 (f x1 ...)) not allowed in conclusion of signature rule"))
                     ((nested-functional-terms-with-vars-p dest-es x1--xk)
                      (prog2$
                       (cw "~| Nested destructors precludes a tau characterization of ~x0~%" P)
                       "Nesting i.e. (P (f ... (g x1 ...) ...) not allowed in conclusion of signature rule"))
                     (t `(IMPLIES (AND . ,dest-es) (,P ,cons-x))))
             (prog2$
              (cw "~| Non-dest-eliminable AND nest ~x0 precludes a tau characterization of ~x1~%" fes P)
              "Illegal tau rule")))
       (if fes ;there is one nested term
           (if (= (depth-var x (car fes)) 2)
               `(IMPLIES (AND . ,(cons (dumber-negate-lit (list P x)) (remove (car fes) es))) ,(dumber-negate-lit (car fes))) ;sig rule
             "Nesting i.e. (P (f ... (g x1 ...) ...) not allowed in conclusion of signature rule")
;poss simple or conj rule
         `(IMPLIES (AND . ,es) (,P ,x))))))
  


(defloop tau-rules-DNF=>Px (conj-clauses Px C)
  (for ((cl in conj-clauses)) (collect (tau-rule-AND-terms=>Px cl (car Px) (cadr Px) C))))

(include-book "coi/util/pseudo-translate" :dir :system)


(defun tau-rules-form=>Px (e Px new-fns-and-args ctx C wrld)
  (b* (((mv erp te) (acl2::pseudo-translate e new-fns-and-args wrld))
       ((when erp)
        (prog2$
         (cw "~| ~x0: Error in translate: ~x1" ctx te)
         (list "Error in translate in tau-rules => direction")))
       (te (expand-lambda te)) ;eliminate let/lambda
;       (vars (all-vars te))
;       (- (assert$ (= 1 (len vars)) (cw "len vars:~x0" (len vars)))) ;monadic
;       (- (cw "~| ~x0: te = ~x1" ctx te))
       (conjunctive-clauses (acl2::cnf-dnf t te nil)) ;get dnf form
       (rules (tau-rules-DNF=>Px conjunctive-clauses Px C)))
    rules))
    


(defun tau-rules-Px=>OR-terms (terms P x)
  (if (consp terms)
      (b* ((fes2 (find-x-terms->=-depth terms x 2)))
        (cond ((null fes2) ;no nesting, return simple or conj rule
          (if (consp (cdr terms)) ;len > 1 
              `(IMPLIES (AND . ,(cons (list P x) (dumber-negate-lit-lst (cdr terms)))) ,(car terms))
            `(IMPLIES (,P ,x) ,(car terms))))
         ((not (consp (cdr fes2))) ;exactly one sig-like term
          (if (= (depth-var x (car fes2)) 2)
              `(IMPLIES (AND . ,(cons (list P x) (dumber-negate-lit-lst (set-difference-equal terms fes2)))) ,(car fes2)) ;sig rule
            "Nesting i.e. (P (f ... (g x1 ...) ...) not allowed in conclusion of signature rule"))
         (t "Multiple sig terms i.e. (P1 (f x1 ...)) \/ (P2 (f x1 ...)) not allowed in conclusion of signature rule")))
    "Impossible: Empty clause"))

(defloop tau-rules-Px=>CNF (clauses Px)
  (for ((cl in clauses)) (collect (tau-rules-Px=>OR-terms cl (car Px) (cadr Px)))))

(defun get-eq-constant (term wrld)
  "if term is a equality-with-constant, then return (equal e evg)"
  (b* (((mv & recog e &) (acl2::tau-like-term term :same-var wrld)))
    (if (and (consp recog) (null (cdr recog))) ; internal representation of evg equality
        `(equal ,e ,(car recog))
      nil)))
;todo complex-rationalp is not a tau-pred. invariant breaks!

(defloop get-first-eq-constant (terms wrld)
  (for ((term in terms)) (thereis (get-eq-constant term wrld))))

(defun get-eq-constant-dont-change (term wrld)
  "if term is a equality-with-constant, then return (equal e evg)"
  (b* (((mv & recog & &) (acl2::tau-like-term term :same-var wrld)))
    (if (and (consp recog) (null (cdr recog))) ; internal representation of evg equality
        term
      nil)))
;todo complex-rationalp is not a tau-pred. invariant breaks!

(defloop get-first-eq-constant-dont-change (terms wrld)
  (for ((term in terms)) (thereis (get-eq-constant-dont-change term wrld))))
  

(defun tau-rule-Px-recog=>prod (and-terms P x C wrld)
  (declare (ignorable wrld))
  (b* ((recog-exp (governing-recognizer-call-with-var and-terms x C))
;hack REVISIT later
       (recog-exp (and recog-exp (proper-symbolp (car recog-exp))
                       (or (and (subtype-p (car recog-exp) 'acl2::atom wrld) (list 'acl2::atom (cadr recog-exp)))
                           recog-exp)))

       ((unless recog-exp) nil)
;        (list "Either AND type combinator not supported or some other missing case...")
;TODO -- revisit this!! The and-terms eaten up tau-rule-Px-=>EQ-NIL-Hack should not
; in the first place come here.

       
       (dterms (remove-equal recog-exp and-terms)))

     (if (find-x-terms->=-depth dterms x 3)
        (list "Nesting i.e. (P (f ... (g x1 ...) ...) not allowed in conclusion of signature rule.")
;TODO should I break it into multiple rules?
      `((IMPLIES (AND (,P ,x) ,recog-exp) (AND . ,dterms))))))

(defloop tau-rules-Px=>SoP (sop P x C wrld)
  "Given sum-of-products pred expr sop, return a list of characterizing tau rules"
  (for ((prod in sop)) (append (tau-rule-Px-recog=>prod prod P x C wrld))))
       
(defun tau-rule-Px-=>EQ-NIL-Hack (and-terms P x wrld)
  (b* ((eq-exp (get-first-eq-constant-dont-change and-terms wrld))
       ((unless eq-exp) ;hack
        nil)
;       (- (cw "eq-exp = ~x0 " eq-exp))
       (recog-exp (if (or (and (equal (second eq-exp) ''nil) (equal (third eq-exp) x))
                          (and (equal (second eq-exp) 'nil) (equal (third eq-exp) x))
                          (and (equal (second eq-exp) x) (equal (third eq-exp) ''nil))
                          (and (equal (second eq-exp) x) (equal (third eq-exp) 'nil)))
                      (list 'ACL2::ENDP x)
                    nil))
;       (- (cw "recog = ~x0 " recog-exp))
       ((unless recog-exp) nil))
                               
    `((IMPLIES (AND (,P ,x) ,recog-exp) ,eq-exp))))

(defloop tau-rules-Px=>EQ-constants (sop P x wrld)
  "Given sum-of-products pred expr sop, return a list of characterizing tau rules"
  (for ((prod in sop)) (append (tau-rule-Px-=>EQ-NIL-Hack prod P x wrld))))




(defun recognizer-call (call C)
  (case-match call
    ((P x) (and (proper-symbolp x) (get-conx-name P C) call))
    (& nil)))

(defloop governing-recognizer-call (terms C) ;cheat: just give the first
  (for ((term in terms)) (thereis (recognizer-call term C))))


(defun disjoint-clause2-p (cl1 cl2 C wrld)
  (b* ((P1x (governing-recognizer-call cl1 C))
       (P2x (governing-recognizer-call cl2 C))
       (evg1-term (get-first-eq-constant cl1 wrld))
       (evg2-term (get-first-eq-constant cl2 wrld))
       (evg1 (and evg1-term (third evg1-term)))
       (evg2 (and evg2-term (third evg2-term)))
;       (- (cw "~| evg1-term = ~x0 evg2-term = ~x1 P1x = ~x2 P2x = ~x3" evg1-term evg2-term P1x P2x))
       )
    (cond ((and evg1-term evg2-term) (not (equal evg1 evg2)))
          ((and evg2-term P1x (equal (second P1x) (second evg2-term))) 
           (b* (((mv erp res) (acl2::ev-fncall-w (car P1x) (list evg2) wrld nil nil t t nil)))
             (and (not erp) (not res))))
          ((and evg1-term P2x (equal (second P2x) (second evg1-term))) 
           (b* (((mv erp res) (acl2::ev-fncall-w (car P2x) (list evg1) wrld nil nil t t nil)))
             (and (not erp) (not res)))) 
          ((and P1x P2x) (disjoint-p (car P1x) (car P2x) wrld))
          (t nil))))


(defloop clause-disjoint-with-clauses-p (cl clauses C wrld)
  (for ((o in clauses)) (always (disjoint-clause2-p cl o C wrld))))

(defun mutually-disjoint-clauses-p (clauses C wrld)
  (if (or (endp clauses)
          (endp (cdr clauses)))
      t
    (and (clause-disjoint-with-clauses-p (car clauses) (cdr clauses) C wrld)
         (mutually-disjoint-clauses-p (cdr clauses) C wrld))))

(defun shallow-prod-p (texp C)
  (and (consp texp)
       (assoc-equal (car texp) C)))

(defloop atleast-one-shallow-prod-p (xs C)
  (for ((x in xs)) (thereis (shallow-prod-p x C))))

(defun shallow-union-of-prods-p (texp wrld)
  (and (consp texp)
       (eq (car texp) 'OR) ;union
       (b* ((targs (cdr texp))
            (C (table-alist 'data-constructor-table wrld)))
         (atleast-one-shallow-prod-p targs C))))


(defun tau-rules-Px=>form (form Px s  new-fns-and-args ctx C wrld)
  (b* (((mv erp te) (acl2::pseudo-translate form new-fns-and-args wrld))
       ((when erp) 
        (prog2$
         (cw "~| ~x0: Error in translate: ~x1" ctx te)
         (list "Error in translate in tau-rules => direction")))
       (te (expand-lambda te)) ;eliminate let/lambda
;       (vars (all-vars1-lst te '())) 
;       (- (assert$ (= 1 (len vars)) nil))) ;monadic
       )
    (if (shallow-union-of-prods-p s wrld)
        (b* ((conj-clauses (acl2::cnf-dnf t te nil))) ;get dnf form
          (if (mutually-disjoint-clauses-p conj-clauses C wrld)
              (append (tau-rules-Px=>EQ-constants conj-clauses (car Px) (cadr Px) wrld)
                      ;;TODO The conj clauses eaten/consumed by above should be
                      ;;excluded from below call!!
                      (tau-rules-Px=>SoP conj-clauses (car Px) (cadr Px) C wrld))
            (list "Dont know how to characterize (using tau rules) a non-disjoint union type")))

      (b* ((clauses (acl2::cnf-dnf t te t))) ;get cnf
        (tau-rules-Px=>CNF clauses Px)))))
     

(defloop filter-strings (xs)
  (for ((x in xs)) (append (and (stringp x) (list x)))))

(defun mv-messages-rule (rules)
  (b* ((msgs (filter-strings rules))
       (rules (set-difference-equal rules msgs)))
    (cond ((and (consp rules)
                (consp (cdr rules)))
           (mv msgs (cons 'AND rules)))
          ((consp rules) (mv msgs (car rules))) ;single rule
          (t (mv msgs nil)))))
  


(defun all-1-arity-fns1 (conx-al)
    (b* ((dest-pred-alist (get1 :dest-pred-alist conx-al))
         (recog (get1 :recog conx-al)))
      (cons recog (strip-cars dest-pred-alist))))
         
(defloop all-1-arity-fns (new-constructors)
  (for ((cx in new-constructors)) (append (all-1-arity-fns1 (cdr cx)))))

(defun all-conx-fns-args1 (cx x)
    (b* (((cons conx conx-al) cx)
         (arity (get1 :arity conx-al))
         (v1--vk (numbered-vars x arity)))
      (cons conx v1--vk)))
         
(defloop all-conx-fns-args (new-constructors x)
  (for ((cx in new-constructors)) (collect (all-conx-fns-args1 cx x))))


(defloop delete2-key (key C)
  (for ((cx in C)) (collect (cons (car cx) (delete-assoc-eq key (cdr cx))))))

;adapted from coi/util/pseudo-translate.lisp for adding tau-pair prop
(defun extend-wrld-with-fn-args-list-with-tau-pair (fn-args-lst wrld)
  (cond ((endp fn-args-lst) wrld)
        (t (let ((fn (caar fn-args-lst)))
                 ;(formals (cdar fn-args-lst)))
             (putprop
              fn 'acl2::tau-pair (if (is-allp-alias fn wrld) 
                                     (cons nil fn) 
                                   (cons 0 fn))
              (extend-wrld-with-fn-args-list-with-tau-pair (cdr fn-args-lst) wrld))))))

(defun chk-acceptable-tau-rule (term fn-args-lst wrld)
  (let ((pairs (acl2::split-on-conjoined-disjunctions-in-hyps-of-pairs
                (acl2::strip-force-and-case-split-in-hyps-of-pairs (acl2::unprettyify term))))
        (wrld1 (extend-wrld-with-fn-args-list-with-tau-pair fn-args-lst wrld)))
    (acl2::acceptable-tau-rulesp :all pairs wrld1)))
       

(defun tau-characterization-events1 (pair top-kwd-alist ctx wrld)
  (b* (((cons name A) pair)
       ((acl2::assocs ndef N new-constructors new-types kwd-alist) A)
       (new-constructors (delete2-key :field-pred-alist new-constructors))
       (C (append new-constructors (table-alist 'data-constructor-table wrld)))
       (M (append new-types (table-alist 'type-metadata-table wrld)))
       (B (table-alist 'builtin-combinator-table wrld))
       (kwd-alist (append kwd-alist top-kwd-alist))
       (avoid-lst (append (forbidden-names) (strip-cars N)))
       (xvar (if (member-eq 'v avoid-lst) 'v (acl2::generate-variable 'v avoid-lst nil nil wrld)))
       (pred-body (make-pred-I ndef xvar kwd-alist M C B wrld))
       (Px `(,(predicate-name name M) ,xvar))

       (mon-fns (all-1-arity-fns new-constructors))
       (all-conx-fns-args (all-conx-fns-args new-constructors 'x))
       (current-preds (predicate-names (strip-cars new-types) new-types))
       (new-fns-and-args (append (list-up-lists current-preds (make-list (len current-preds) :initial-element 'x))
                                 (and new-constructors all-conx-fns-args)
                                 (and new-constructors (list-up-lists mon-fns (make-list (len mon-fns) :initial-element 'x)))))

       ((mv msgs<= rule-=>-Px)  (mv-messages-rule (tau-rules-form=>Px pred-body Px new-fns-and-args ctx C wrld)))
       ((mv msgs=> rule-Px-=>)  (mv-messages-rule (tau-rules-Px=>form pred-body Px ndef new-fns-and-args ctx C wrld)))

; the following breaks because ndef has name declarations
       (without-names-ndef (remove-names ndef))
       (constituent-tnames (set-difference-eq (all-vars without-names-ndef) (strip-cars new-types)))
       (constituent-preds (predicate-names constituent-tnames))
       (disabled (runes-to-be-disabled constituent-preds wrld))
       ((mv erp term-=>-Px) (acl2::pseudo-translate rule-=>-Px new-fns-and-args wrld))
       ((when erp) (er hard? ctx "~| Bad translate ~x0.~%" rule-=>-Px))
       ((mv erp term-Px-=>) (acl2::pseudo-translate rule-Px-=> new-fns-and-args wrld))
       ((when erp) (er hard? ctx "~| Bad translate ~x0.~%" rule-Px-=>))
       (rule-=>-Px-tau-acceptable-p (chk-acceptable-tau-rule term-=>-Px new-fns-and-args wrld))
       (rule-Px-=>-tau-acceptable-p (chk-acceptable-tau-rule term-Px-=> new-fns-and-args wrld))
       (unacceptable-tau-rule-msg "The formula fails to fit any of the forms for acceptable :TAU-SYSTEM rules.")
       (msgs=> (remove-duplicates-equal (append (and (not rule-=>-Px-tau-acceptable-p) (list unacceptable-tau-rule-msg)) msgs=>)))
       (msgs<= (remove-duplicates-equal (append (and (not rule-Px-=>-tau-acceptable-p) (list unacceptable-tau-rule-msg)) msgs<=)))
       (?recp (get1 :recp kwd-alist))
       )
    

    
    (append (and msgs<= `((value-triple (cw "~| Incomplete tau characterization of ~x0 <= body. ~% Failure messages: ~x1 ~%" ',Px ',msgs<=))))
            (and msgs=> `((value-triple (cw "~| Incomplete tau characterization of ~x0 => body. ~% Failure messages: ~x1 ~%" ',Px ',msgs=>))))
            (and (not msgs=>) (not msgs<=) rule-Px-=>-tau-acceptable-p rule-Px-=>-tau-acceptable-p
                 `((value-triple (cw "~|Defdata/Note: Complete tau characterization of ~x0 successful.~%" ',Px))))
            (and rule-=>-Px 
                 `((DEFTHM ,(symbol-fns::prefix 'def '=> name)
                     ,rule-=>-Px
                     :HINTS (("Goal" :IN-THEORY (e/d (,(car Px)) (,@disabled ,@(strip-cars new-constructors)))))
                     :RULE-CLASSES (,@(and rule-=>-Px-tau-acceptable-p (list :TAU-SYSTEM)) :REWRITE))))
            (and rule-Px-=>
                 `((DEFTHM ,(symbol-fns::suffix name '=> 'def) 
                     ,rule-Px-=>
                     :HINTS (("Goal" :IN-THEORY (e/d (,(car Px)) (,@disabled))))
                     :RULE-CLASSES (,@(and rule-Px-=>-tau-acceptable-p '(:TAU-SYSTEM)) 
                                    ;,@(:REWRITE
                                    ;:backchain-limit-lst 10) 
;HARSH: Check if it is a record (product?) type and also add a rewrite rule here
; Disable the constructor
                                    (:forward-chaining :trigger-terms (,Px))
                                    ; Do we want forward chaining here?
                                    )))))))
     

   

(defloop tau-characterization-events0 (ps kwd-alist wrld)
  (for ((p in ps)) (append (tau-characterization-events1 p kwd-alist 'tau-characterization wrld))))

(defun tau-characterization-events (ps kwd-alist wrld)
  (cons
   `(commentary ,(get1 :print-commentary kwd-alist) "~| Tau characterization events...~%")
   (tau-characterization-events0 ps kwd-alist wrld)))


(add-pre-post-hook defdata-defaults-table :post-hook-fns '(tau-characterization-events))

