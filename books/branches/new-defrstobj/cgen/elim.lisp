#|$ACL2s-Preamble$;
;;Author - Harsh Raju Chamarthi (harshrc)
(ld ;; Newline to fool ACL2/cert.pl dependency scanner
 "portcullis.lsp")
(begin-book t);$ACL2s-Preamble$|#


(in-package "DEFDATA")
(include-book "tools/bstar" :dir :system)

; On-demand dest-elim of record/map/list types

; To each record/map/list type we will add its elim rule to a elim-table. This
; is done in register-record-constructor. Instead of adding an elim rule for
; each destructor fn we will add just one and change the :destructor-term field
; in the call to get-record/list-elim-rule fn.

; In test-checkpoint when we are at push-clause ledge, we will do one csearch
; and if no cts were found, we will check if there is a variable which is of
; type record, list, map etc. If yes, we will call
; eliminate-destructors-clause1-noiter-cgen fn with this type and do on-demand
; destructor elimination, getting back a new clause which we will csearch. We
; will iterate till we find no more record types. List and map types need more
; subtlety, since they can loop if we iterate in the above manner.

;  Because the new dest-elimed clause has unsimplified hyps from
;  generalize rules, we do simplify-hyps before calling
;  cts-wts-search. This is important, because otherwise the type
;  information for fields is not correctly restricted in hyps and we
;  dont benefits of test data generation from defdata types.

  
(mutual-recursion
(defun find-destructor-term (e eliminable destructor-fns)
  (declare (xargs :guard (and (pseudo-termp e)
                              (symbolp eliminable)
                              (symbol-listp destructor-fns))))
  (cond ((variablep e) nil)
        ((fquotep e) nil)
        (t (if (and (member-eq (ffn-symb e) destructor-fns)
                    (eq eliminable (third e)))
               e
             (find-destructor-term-lst (fargs e) eliminable destructor-fns)))))

(defun find-destructor-term-lst (es eliminable destructor-fns)
  "find a subterm in clause thats a record destructor term (destr-fn field eliminable)"
  (declare (xargs :guard (and (pseudo-term-listp es)
                              (symbolp eliminable)
                              (symbol-listp destructor-fns))))
  (if (endp es)
      nil
    (b* ((s (find-destructor-term (car es) eliminable destructor-fns)))
      (if s
          s
        (find-destructor-term-lst (cdr es) eliminable destructor-fns)))))
)        

;comparison shud be total. lesson!
(defun order-two-eliminables (x1 x2 es)
  "x1 <= x2 if dest-term of x1 occurs inside an dest-term of x2, or if neither occur in each other"
  (declare (xargs :verify-guards nil
                  :guard (and (symbolp x1)
                              (symbolp x2)
                              (pseudo-term-listp es))))
  (b* ((destructor-fns '(mget))
       (dt2 (find-destructor-term-lst es x2 destructor-fns)))
    (if dt2
        (find-destructor-term (cadr dt2) x1 destructor-fns)
      (b* ((dt1 (find-destructor-term-lst es x1 destructor-fns)))
        (if dt1
            (not (find-destructor-term (cadr dt1) x2 destructor-fns))
            t)))))
          

(defun merge-car-order-elim (l1 l2 cl)
  (declare (xargs :measure (+ (acl2-count l1) (acl2-count l2))))
  ;; (declare (xargs :guard (and (symbol-alistp l1)
  ;;                             (symbol-alistp l2)
  ;;                             (pseudo-term-listp cl))))
  (cond ((endp l1) l2)
        ((endp l2) l1)
        ((order-two-eliminables (car (car l1)) (car (car l2)) cl)
         (cons (car l1)
               (merge-car-order-elim (cdr l1) l2 cl)))
        (t (cons (car l2)
                 (merge-car-order-elim l1 (cdr l2) cl)))))

(defthm acl2-count-evens-strong
  (implies (and (consp x)
                (consp (cdr x)))
           (< (acl2-count (evens x)) (acl2-count x)))
  :rule-classes :linear)

(defthm acl2-count-evens-weak
  (<= (acl2-count (evens x)) (acl2-count x))
  :hints (("Goal" :induct (evens x)))
  :rule-classes :linear)


(defun merge-sort-eliminables-alst (E cl)
  ;; (declare (xargs :guard (and (symbol-alistp E)
  ;;                             (pseudo-term-listp cl))))
  (if (or (endp E) (endp (cdr E)))
      E
    (merge-car-order-elim (merge-sort-eliminables-alst (evens E) cl)
                          (merge-sort-eliminables-alst (odds E) cl)
                          cl)))
      
        
    

(defun get-record/map-elim-rule (type eliminable clause wrld)
  (declare (xargs :verify-guards nil
                  :guard (and (pseudo-term-listp clause)
                              (symbolp type)
                              (symbolp eliminable)
                              (plist-worldp wrld))))
  (b* ((tbl (table-alist 'record-elim-table wrld))
       (entry (assoc-equal type tbl)))
    (if (consp entry)
        (b* ((rule (cdr entry))
             (dterm (find-destructor-term-lst clause eliminable '(acl2::mget)))
             ((when (null dterm)) (mv nil nil))
             (destructor-term (subst 'x eliminable dterm)))
          (mv (acl2::change acl2::elim-rule rule :destructor-term destructor-term) dterm))
      (b* ((tbl (table-alist 'map-elim-table wrld))
           (entry (assoc-equal type tbl)))
        (if (consp entry)
            (b* ((rule (cdr entry))
                 (dterm (find-destructor-term-lst clause eliminable '(acl2::mget)))
                 ((when (null dterm)) (mv nil nil)))
              (mv rule dterm))
          (mv nil nil))))))


       
(defun delete-quoted-keys (alist)
  (if (endp alist)
      '()
    (if (quotep (caar alist))
        (delete-quoted-keys (cdr alist))
      (cons (car alist) (delete-quoted-keys (cdr alist))))))

(defun select-instantiated-elim-rule-cgen (type eliminable clause wrld)

; type is the type of the variable eliminable that we wish to eliminate.
; Clause is a clause to which we wish to apply destructor elimination.
; Type-alist is the type-alist obtained by assuming all literals of cl nil.

; Return an instantiated version of the elim-rule corresponding to dterm

  (b* (((mv rule dterm) (get-record/map-elim-rule type eliminable clause wrld))
       ((when (null rule)) nil)
       (alist (pairlis$ (fargs (acl2::access acl2::elim-rule rule :destructor-term))
                        (fargs dterm)))
       (alist (delete-quoted-keys alist))
       )
    (acl2::change acl2::elim-rule rule
                  :hyps (acl2::sublis-var-lst alist (acl2::access acl2::elim-rule rule :hyps))
                  :lhs  (acl2::sublis-var alist (acl2::access acl2::elim-rule rule :lhs))
                  :rhs  (acl2::sublis-var alist (acl2::access acl2::elim-rule rule :rhs))
                  :destructor-term
                  (acl2::sublis-var alist (acl2::access acl2::elim-rule rule :destructor-term))
                  :destructor-terms
                  (acl2::sublis-var-lst
                   alist
                   (acl2::access acl2::elim-rule rule :destructor-terms)))))

(defun eliminate-destructors-clause1-cgen (eliminable type cl avoid-vars ens wrld)
  (declare (xargs :mode :program))
; Cl is a clause we are trying to prove. type is the type of the variable eliminable
; on which we will permit a destructor elimination.  Avoid-vars is a list of
; variable names we are to avoid when generating new names.  In addition, we
; avoid the variables in cl. Given the eliminable destructor we get its
; instantiated rule, apply the rule to cl to produce the "normal" elim case.


; We return 4 things.  The first is the clauses to test instead of cl.
; The second is the set of variable names introduced by this
; destructor elimination step.  The third is an "elim-sequence" that
; documents this step.  If the list is nil, it means we did
; nothing. fourth is the elim-rule selected, which is null if none is
; applicable

; 20 July 2013 - returning the new clause instead of return-clauses!

  (mv-let
   (contradictionp type-alist ttree)
   (acl2::type-alist-clause cl nil
                       nil ; force-flg; see comment above
                       nil ens wrld
                       nil nil)
   (declare (ignore ttree))
   (if contradictionp 
       (mv (list cl) nil nil nil)
     (b* ((rule (select-instantiated-elim-rule-cgen type eliminable cl wrld))
          )
       (if (null rule) 
           (mv (list cl) nil nil nil)
         (b* (((mv new-clause new-vars ele)
               (acl2::apply-instantiated-elim-rule rule cl type-alist avoid-vars ens wrld))
              (?clauses1 (acl2::split-on-assumptions (acl2::access acl2::elim-rule rule :hyps)
                                              new-clause nil))
              (?return-clauses (acl2::conjoin-clause-sets clauses1 (list new-clause))))
           (mv new-clause new-vars ele rule)))))))
              
