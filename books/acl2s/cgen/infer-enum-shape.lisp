#|$ACL2s-Preamble$;
;; Author - Harsh Raju Chamarthi (harshrc)
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "../portcullis")
(begin-book t :ttags :all);$ACL2s-Preamble$|#


(in-package "CGEN")

(include-book "basis")

(include-book "type")

;(include-book "acl2s-parameter")
;; (include-book "simple-graph-array")
(include-book "cgen-state")


;;;; * Collecting type and additional constraints

;;; Given a list of hypotheses and a conclusion, we want to find the
;;; type constraints on each free variable. We collect 4 categories of
;;; constraints: 1. defdata type and spilled defdata types 2. equality
;;; constraints 3. range constraints 4. additional constraints.

;;; A defdata type has a type-predicate and a type-enumerator
;;; associated with it.  Ideally we would like to compute the minimal
;;; (best possible) defdata type information, but this can fail, due
;;; to incomplete subtype type information.  So we end up also storing
;;; spillover types, whose union/join is the conservative (superset)
;;; type of the corresponding variable. We also store the equality
;;; constraint, since its a very strong constraint and often comes up
;;; in naive dependencies. Finally we also store additional
;;; constraints, just so as to not throw away information that can
;;; fruitfully be utilized to come up with the smallest set of
;;; possible values the constrained variable can take.
;;; range is just a tau-intervalp

(defrec cs% (defdata-type spilled-types 
              eq-constraint 
              range
              member-constraint ; [2015-04-16 Thu] Added support for member-equal
              additional-constraints) NIL)


(defun cs%-p (v)
  (declare (xargs :guard T))
  (case-match v ;layout not hidden -- see build-enumcalls.lisp
    (('cs% dt st eqc int mem ac)

     (and (possible-defdata-type-p dt) 
          (possible-defdata-type-list-p st)
          (or (pseudo-termp eqc)
              (eq 'defdata::empty-eq-constraint eqc))
          (acl2::tau-intervalp int)
          (pseudo-termp mem)
          (pseudo-term-listp ac)))))
    

(defun |is (symbol . cs%)| (v)
  (declare (xargs :guard T))
  (case-match v
    ((x . y)      (and (symbolp x)
                       (cs%-p y)))))

(defun symbol-cs%-alistp (vs)
  (declare (xargs :guard T))
  (if (consp vs)
      (and (|is (symbol . cs%)| (car vs))
           (symbol-cs%-alistp (cdr vs)))
    NIL))
           

  ;; (foldl (lambda (v acc) (and acc (|is a (symbol . type-constraints%)| v) ))
  ;;        T vs)) 
; Note: The above expression if implemented is not as efficient as 
;; (defun _-list-p (xs) 
;;   (if (endp x) T 
;;     (and (_-p (car x))
;;          (_-list-p (cdr x)))))
  ;; (and (true-listp vs)
  ;;      (null ([ x : x in vs : (not (|is a (symbol . type-constraints%)|)) ])))
 

;; TODO: conclusion is not taken care of now. Only negated conclusion
;; is treated, but we would like to be symmetric with respect to
;; searching cts and wts. --harshrc 4th March 2012.

(def put-additional-constraints. (vs term v-cs%-alst.)
  (decl :sig ((symbol-list pseudo-term symbol-cs%-alist) 
              -> symbol-cs%-alist)
        :doc "put term in alist for all keys in vs")
  (if (endp vs)
      v-cs%-alst.
    (b* (((cons v cs%) (assoc-eq (car vs) v-cs%-alst.))
         (cs% (change cs% additional-constraints 
                      (cons term (access cs% additional-constraints)))))
    (put-additional-constraints. (cdr vs) term 
                                 (put-assoc-eq v cs% v-cs%-alst.)))))

(def insert-before-key  (key entry alist)
  (decl :sig ((symbol entry symbol-alist) -> symbol-alist)
        :doc "insert entry before key in alist")
  (if (endp alist)
      nil
    (if (eq key (caar alist))
        (cons entry alist)
      (cons (car alist)
            (insert-before-key key entry (cdr alist))))))
              
;2 july '13 (type-info-lost-via-dest-elim issue)
; TODO: check if check for cycles is correct!
; 15 Oct '13: ugly hack to reorder around dependency change.
(def put-var-eq-constraint. (v1 v2 vl wrld v-cs%-alst.)
  (decl :sig ((symbol symbol vl plist-world symbol-cs%-alist) 
              -> symbol-cs%-alist)
        :doc "put variable equality constraint in alist for key v")
  (declare (xargs :verify-guards nil))
  (b* (((cons & cs1%) (assoc-eq v1 v-cs%-alst.))
       ((cons & cs2%) (assoc-eq v2 v-cs%-alst.))
       (dt1 (acl2::access cs% cs1% :defdata-type))
       (dt2 (acl2::access cs% cs2% :defdata-type))
       (M  (table-alist 'defdata::type-metadata-table wrld))
       (P1 (defdata::predicate-name dt1 M))
       (P2 (defdata::predicate-name dt2 M))
       ((mv v other-v cs% other-cs%) (if (defdata::subtype-p P2 P1 wrld) 
                                         (mv v1 v2 cs1% cs2%) ;dt2 is better
                                       (mv v2 v1 cs2% cs1%) 
                                       ))
       (eqc (acl2::access cs% cs% :eq-constraint))
       (other-eqc (acl2::access cs% other-cs% :eq-constraint))
       ((when (eq other-v eqc)) v-cs%-alst.) ;redundant
       ((when (eq v other-eqc)) v-cs%-alst.) ;avoid cycle!!
       (- (cw? (and (verbose-stats-flag vl)
                    (not (eq 'defdata::empty-eq-constraint eqc))) 
               "CEgen/Note: Overwriting (variable) eq-constraint for ~x0 with ~x1~|" v other-v))
       (cs% (change cs% eq-constraint other-v))
       (v-cs%-alst. (put-assoc-eq v cs% v-cs%-alst.)))
; 15 Oct '13 -- other-v should come before v in the order of keys in
; v-cs%-alst. or at least in the let* binding. Since there two
; variables are related by an equivalence relation, all entries
; between them will also be in the same equivalence class, so it
; suffices to remove the other-v entry and insert it just in front of
; the entry of v.
    (insert-before-key v (cons other-v other-cs%)
                       (delete-assoc-eq other-v v-cs%-alst.))))


(def put-eq-constraint. (v term vl v-cs%-alst.)
  (decl :sig ((symbol pseudo-term vl symbol-cs%-alist) 
              -> symbol-cs%-alist)
        :doc "put eq-constraint term in alist for key v")
  (b* (((cons & cs%) (assoc-eq v v-cs%-alst.))
       (eqc (access cs% eq-constraint))
       (- (cw? (and (verbose-stats-flag vl)
                    (not (eq 'defdata::empty-eq-constraint eqc)))
               "CEgen/Note: Overwriting eq-constraint for ~x0 with ~x1~|" v term))
       (cs% (change cs% eq-constraint term)))
   (put-assoc-eq v cs% v-cs%-alst.)))


(def put-member-constraint. (v term vl v-cs%-alst.)
  (decl :sig ((symbol pseudo-term vl symbol-cs%-alist) 
              -> symbol-cs%-alist)
        :doc "put member-constraint term in alist for key v")
  (b* (((cons & cs%) (assoc-eq v v-cs%-alst.))
       (memc (access cs% member-constraint))
       (- (cw? (and (verbose-stats-flag vl)
                    (not (equal 'defdata::empty-mem-constraint memc)))
               "CEgen/Note: Overwriting member-constraint for ~x0 with ~x1~|" v term))
       (cs% (change cs% member-constraint term)))
   (put-assoc-eq v cs% v-cs%-alst.)))

(def put-defdata-type. (v typ vl v-cs%-alst.)
  (decl :sig ((symbol possible-defdata-type-p fixnum symbol-cs%-alist) 
              -> symbol-cs%-alist)
        :doc "put defdata type typ in alist for key v")
  (b* (((cons & cs%) (assoc-eq v v-cs%-alst.))
       (dt (access cs% defdata-type))
       (- (cw? (and (verbose-stats-flag vl) (not (eq 'ACL2S::ALL dt)))  ;TODO perhaps use is-top? but that might be expensive?
"CEgen/Note: Overwriting defdata type for ~x0. ~x1 -> ~x2~|" v dt typ))
       (cs% (change cs% defdata-type typ)))
   (put-assoc-eq v cs% v-cs%-alst.)))



(defs  ;;might be mut-rec, but right now I assume tht I wont encounter
       ;;AND and OR like if expressions, and hence dont need the
       ;;mutually-recursive counterpart of v-cs%-alist-from-term. TODO
  (v-cs%-alist-from-term. (term vl wrld ans.)
  (decl :sig ((pseudo-term fixnum plist-world  symbol-cs%-alist)
              ->
              symbol-cs%-alist)
        :doc "helper to collect-constraints")
  (declare (xargs :verify-guards nil))
;Invariant: ans. is an alist thats in the order given by dependency analysis
  (f* ((add-constraints... () (put-additional-constraints. fvars term ans.))
; [2015-04-16 Thu] add support for membership
       (add-eq/mem-constraint... (t1) (if (membership-relationp R wrld)
                                          (put-member-constraint. x t1 vl ans.)
                                        (add-eq-constraint... t1)))
       (add-eq-constraint... (t1) (if (acl2::equivalence-relationp R wrld)
                                      (if (symbolp t1)
                                          (put-var-eq-constraint. x t1 vl wrld ans.)
                                        (put-eq-constraint. x t1 vl ans.))
                                    (add-constraints...))))
     
   (b* ((fvars (all-vars term)))
           
    (case-match term
      
;the following is a rare case (I found it when the conclusion is nil
;and its negation is 'T
      (('quote c) (declare (ignore c))  ans.) ;ignore quoted constant terms 

;TODO possible field variable (i.e f is a getter/selector)
; Note that term cannot have a lambda applicaton/let, so the car of the term is
; always a function symbol if term is a consp.
      ((P (f . &)) (declare (ignore P f))  (add-constraints...)) 

;x has to be an atom below, otherwise, we would have caught that case above.
      (('not x)      (put-eq-constraint. x ''nil vl ans.))
      
      ((P x)   (b* ((tname (defdata::is-type-predicate P wrld))
                    ((cons & cs%) (assoc-eq x ans.))
                    (curr-typ (access cs% defdata-type))
                    (smaller-typ (meet tname curr-typ vl wrld )))
                (if tname
                    (if (not (eq smaller-typ curr-typ))
                        (put-defdata-type. x smaller-typ vl ans.)
                      ans.)
                  (add-constraints...))))

      ((R (f . &) (g . &)) (declare (ignore R f g)) (add-constraints...))

;x has to be an atom below, otherwise, we would have caught that case
;above.
      ((R x ('quote c))    (add-eq/mem-constraint... (kwote c)))
      ((R ('quote c) x)    (add-eq-constraint... (kwote c)))
      ((R x (f . args))    (add-eq/mem-constraint... (acl2::cons-term f args)))
      ((R (f . args) x)    (add-eq-constraint... (acl2::cons-term f args)))
      ((R x y)             (add-eq/mem-constraint... y))
      
      ;; has to be a (R t1 t2 ...) or atomic term
      (&                   (add-constraints...)))))))
                         
  
(def v-cs%-alist-from-terms. (terms vl wrld ans.)
  (decl :sig ((pseudo-term-listp fixnum plist-worldp symbol-cs%-alist) 
              -> symbol-cs%-alist)
        :doc "helper to collect-constraints%")
  (declare (xargs :verify-guards nil))
  (if (endp terms)
      ans.
    (v-cs%-alist-from-terms. (cdr terms) vl wrld  
                             (v-cs%-alist-from-term. (car terms)
                                                     vl wrld ans.))))

(def put-range-constraint. (v int v-cs%-alst.)
  (decl :sig ((symbolp acl2::tau-intervalp symbol-cs%-alistp) 
              -> symbol-cs%-alistp)
        :doc "put interval int in alist for key v")
  (b* (((cons & cs%) (assoc-eq v v-cs%-alst.))
       (cs% (change cs% range int)))
   (put-assoc-eq v cs% v-cs%-alst.)))

(def range-is-alias-p (interval type wrld)
  (decl :sig ((non-empty-non-universal-interval-p symbolp plist-worldp) -> boolean)
        :doc "is interval an alias of type?")
  (declare (xargs :verify-guards nil))
  (b* ((lo (acl2::access acl2::tau-interval interval :lo))
       (hi (acl2::access acl2::tau-interval interval :hi))
       (lo-rel (acl2::access acl2::tau-interval interval :lo-rel))
       (hi-rel (acl2::access acl2::tau-interval interval :hi-rel))
       (P (defdata::predicate-name type (table-alist 'DEFDATA::TYPE-METADATA-TABLE wrld))))
    (case (acl2::access acl2::tau-interval interval :domain)
      (acl2::integerp (or (and (defdata::subtype-p P 'ACL2::NATP wrld)
;use the fact that integers are squeezed (weak inequalities)
                               (equal lo 0)
                               (null hi))
                          (and (defdata::subtype-p P 'ACL2::POSP wrld) 
                               (equal lo 1)
                               (null hi))
                          (and (defdata::subtype-p P 'ACL2::NEGP wrld) 
                               (null lo)
                               (equal hi -1))))
      (otherwise (or (and (defdata::subtype-p P 'ACL2::POSITIVE-RATIONALP wrld)
                          lo-rel ;strict
                          (null hi)
                          (equal lo 0))
                     (and (defdata::subtype-p P 'ACL2::NEGATIVE-RATIONALP wrld) 
                          hi-rel
                          (null lo)
                          (equal hi 0)))))))


(verify-termination acl2::empty-tau-intervalp )
(verify-termination acl2::singleton-tau-intervalp)

(defun singleton-tau-intervalp (interval)
  (b* ((lo (acl2::access acl2::tau-interval interval :lo))
       (hi (acl2::access acl2::tau-interval interval :hi))
       (lo-rel (acl2::access acl2::tau-interval interval :lo-rel))
       (hi-rel (acl2::access acl2::tau-interval interval :hi-rel)))
    (and (acl2::access acl2::tau-interval interval :domain) ;int,rat,num
         (acl2::singleton-tau-intervalp lo-rel lo hi-rel hi))))

(defun non-empty-non-universal-interval-p (interval)
  (and interval
       (acl2::tau-intervalp interval)
       (acl2::access acl2::tau-interval interval :domain) ;either int,rat,num
       (or (rationalp (acl2::access acl2::tau-interval interval :lo)) ;one of bounds should be a number
           (rationalp (acl2::access acl2::tau-interval interval :hi)))
       (b* ((lo (acl2::access acl2::tau-interval interval :lo))
            (hi (acl2::access acl2::tau-interval interval :hi))
            (lo-rel (acl2::access acl2::tau-interval interval :lo-rel))
            (hi-rel (acl2::access acl2::tau-interval interval :hi-rel)))
         (and (not (acl2::empty-tau-intervalp lo-rel lo hi-rel hi))
              (not (acl2::singleton-tau-intervalp lo-rel lo hi-rel hi))))))


(def assimilate-apriori-type-information (vs vt-dlist tau-interval-alist vl wrld ans.)
  (decl :sig ((symbol-list symbol-doublet-list alist symbol-alist fixnum plist-world symbol-cs%-alist) 
              -> symbol-cs%-alist)
        :doc 
"overwrite into v-cs%-alst. the type information in type-alist/tau-interval-alist.
Put defdata symbol types into defdata-type field, but put constants
into eq-constraint field and put interval into range constraint field")
  (declare (xargs :verify-guards nil))
; Aug 30 '12 -- This function fixes a bug in Pete's GE demo, where the
; type=alist had 'NIL as the type, which is a singleton defdata type
; and I was not taking it into consideration when trying to run MEET
; on it, which cannot handle types which are not in the defdata graph,
; and certainly constants are not part of the defdata graph.
  (if (endp vs)
      ans.
    (b* ((x (car vs))
         (prior-types-entry (assoc-eq x vt-dlist)) 
         ;; (ts-info (assoc-eq x type-alist))
         ;; (ts (and ts-info (cadr ts-info))) ;;TODO: approximation. there might be multiple entries!
         ;; (prior-types (and ts (get-type-list-from-type-set ts)))
         ;; prior-types is a list of defdata typenames
         (- (cw? (and (verbose-stats-flag vl)
                      (consp prior-types-entry)
                      (consp (cdr prior-types-entry)) 
                      (not (null (cddr prior-types-entry))))
                 "~|CEgen/Warning: Ignoring rest of union types ~x0 ~|" (cddr prior-types-entry)))
         (typ-given (if (and (consp prior-types-entry) (consp (cdr prior-types-entry)))
                        (cadr prior-types-entry)
                      'ACL2S::ALL))
         ((when (defdata::possible-constant-value-p typ-given))
; is a singleton, then treat it as a eq-constraint
; BOZO: meet-type-alist does it differently. (03/04/13)
          (assimilate-apriori-type-information 
           (cdr vs) vt-dlist tau-interval-alist vl wrld  
           (put-eq-constraint. x typ-given vl ans.)))

         (int-entry (assoc-eq x tau-interval-alist))
         (int (cdr int-entry)) ;possible type bug
         ((when (singleton-tau-intervalp int))
; is a singleton, then treat it as a eq-constraint
          (assimilate-apriori-type-information 
           (cdr vs) vt-dlist tau-interval-alist vl wrld  
           (put-eq-constraint. x (kwote (acl2::access acl2::tau-interval int :lo)) vl ans.)))

         ((cons & cs%) (assoc-eq x ans.))
         (curr-typ (access cs% defdata-type))
         (final-typ (meet curr-typ typ-given vl wrld))
         (ans. (if (and (non-empty-non-universal-interval-p int)
                        (not (range-is-alias-p int final-typ wrld)))
                   (put-range-constraint. x int ans.)
                 ans.)))
                   
; update the current defdata type with the new type information (type-alist)
     (assimilate-apriori-type-information 
      (cdr vs) vt-dlist tau-interval-alist vl wrld
      (put-defdata-type. x final-typ vl ans.)))))

(defconst *empty-cs%*
  (acl2::make cs%
        :defdata-type 'ACL2S::ALL 
        :spilled-types '()
        :eq-constraint 'defdata::empty-eq-constraint
        :range (acl2::make-tau-interval nil nil nil nil nil)
        :member-constraint 'defdata::empty-mem-constraint
        :additional-constraints '()))

(def collect-constraints% (hyps ordered-vars top-vt-dlist type-alist tau-interval-alist vl wrld)
  (decl :sig ((pseudo-term-listp symbol-listp symbol-doublet-listp alistp symbol-alistp
                                 fixnum plist-worldp) -> symbol-cs%-alist)
        :doc 
" 
* Synopsis 
  For each free variable compute/infer both the simple defdata types
  and additional constraints on it.

* Input 
  hyps is a usually a list of hypotheses of the conjecture under query
  and is a term-listp. ordered-vars is the free variables of hyps, but in the
  variable dependency order as computed from the dependency graphs of hyps.
  type-alist is the ACL2 context. 
  top-vt-dlist is meet of top-level dumb type inference and ACL2 type-alist info. 
  tau-interval-alist is the range type information inferred by Tau.
  

* Output
  An alist mapping free variables to cs% record
")
  (declare (xargs :verify-guards nil))
  (f* ((unconstrained-v-cs%-alst (xs) (pairlis$ xs (make-list (len xs)
                                                              :initial-element 
                                                              *empty-cs%*))))
      ;; initialize the alist
    (b* ((v-cs%-alst  (unconstrained-v-cs%-alst ordered-vars))
         (v-cs%-alst  (assimilate-apriori-type-information ordered-vars
                                                           top-vt-dlist tau-interval-alist
                                                           vl wrld v-cs%-alst))
         ;; reify all hyps that are true in the ACL2 context.
         (context-hyps (reify-type-alist-hyps type-alist))
         (hyps+ (defdata::filter-terms-with-vars (union-equal context-hyps hyps) ordered-vars)))
       
     (v-cs%-alist-from-terms. hyps+ vl wrld v-cs%-alst))))

; TODO: Right now we dont use ACL2's type-alist to full effect. For
; example, we might get that (len x) > 3 is non-nil in the type-alist
; but missing in the actual hypotheses, this causes loss in crucial
; shape information.

; [2015-09-01 Tue] Refine enum shape code follows

(program)
(set-state-ok t)
(set-ignore-ok t)


(defun one-way-unify (pat pattern-x given given-x)
  "do match but make sure pattern-x is matched with given-x"
  (b* (((mv ans alist) (acl2::one-way-unify pat given))
       ((unless (eq (get1 pattern-x alist) given-x)) (list nil nil)))
    (list ans alist)))

(mutual-recursion
(defun innermost-subterm-one-way-unify (pat pat-x term x acc)

; This function searches term for the innermost non-variable non-quote
; subterm s such that (one-way-unify pat s) returns t and a
; unify-subst.  If it finds one, it returns t and the unify-subst.
; Otherwise, it returns two nils. Default ans = (list nil nil)

  (cond ((variablep term) acc)
        ((fquotep term) acc)
        (t (b* (((list ans alist) (one-way-unify pat pat-x term x)))
             (cond (ans (innermost-subterm-one-way-unify-lst pat pat-x (fargs term) x (list ans alist))) ;replace
                   (t (innermost-subterm-one-way-unify-lst pat pat-x (fargs term) x acc)))))))

(defun innermost-subterm-one-way-unify-lst (pat pat-x terms x acc)
  (cond
   ((null terms) acc)
   (t (b* (((list ans alist) (innermost-subterm-one-way-unify pat pat-x (car terms) x acc)))
        (cond (ans (innermost-subterm-one-way-unify-lst pat pat-x (cdr terms) x (list ans alist)))
              (t (innermost-subterm-one-way-unify-lst pat pat-x (cdr terms) x acc)))))))

)



(include-book "tools/templates" :dir :system)

(defun sublis-var (sigma term)
  (acl2::sublis-var sigma term))

(defun filter-splice-entries (replace-alist)
  (if (endp replace-alist)
      '()
    (b* (((cons key val) (car replace-alist)))
      (if (equal "@" (subseq (symbol-name key) 0 1))
          (cons (car replace-alist) (filter-splice-entries (cdr replace-alist)))
        (filter-splice-entries (cdr replace-alist))))))

(defun delete-assoc-eq-lst (xs alist)
  (if (endp xs)
      alist
    (delete-assoc-eq-lst (cdr xs) (delete-assoc-eq (car xs) alist))))

(defun eval-meta-replace (mc usigma vl wrld)
  (b* (((unless (consp mc)) (mv nil nil))
       (mc (acl2::listlis (strip-cars mc)
                          (acl2::sublis-var-lst usigma (strip-cadrs mc))))
        (vars (strip-cars mc))
        ((mv erp replace-alist) (trans-my-ev-w `(LET ,mc
                                           (declare (ignorable ,@vars))
                                           ,(make-var-value-cons-bindings vars '()))
                                               'eval-meta-replace wrld nil))
        (splice-alist (filter-splice-entries replace-alist))
        (atom-alist   (delete-assoc-eq-lst (strip-cars splice-alist) replace-alist))
        ((when erp)
         (prog2$
          (cw? (debug-flag vl)
               "~| Error in evaluating meta-replace ~x0 given sigma ~x1~%" mc usigma)
          (mv nil nil))))
     (mv atom-alist splice-alist)))
        


(defun match-constraint1 (constraint-rule given-C x vl wrld)
  "does given-C match with this constraint-rule with a variable renaming for x"
  (declare (ignorable vl))
  (b* ((pattern-C (get1 :constraint constraint-rule))
       (pattern-x (get1 :constraint-variable constraint-rule))
       
       ((list yesp usigma) (if (eq :subterm-match (get1 :match-type constraint-rule))
                             (innermost-subterm-one-way-unify pattern-C pattern-x given-C x (list nil nil))
                           (one-way-unify pattern-C pattern-x given-C x)))
       ((unless yesp) nil) ;did not match

       (- (cw? (debug-flag vl)
               "~| Match successful: ~x0 ~%" usigma))
       (meta-precondition (get1 :meta-precondition constraint-rule))
       (vars (strip-cars usigma))
       (letb (acl2::listlis vars (acl2::kwote-lst (strip-cdrs usigma)))) 
       ((mv erp okp) (trans-my-ev-w `(LET ,letb (declare (ignorable ,@vars)) ,meta-precondition)
                                    'match-constraint1 wrld nil))
       ((unless (and (not erp) okp)) nil)
       (rule-form (get1 :rule constraint-rule)) ;stands for either elim rule or expand (or refine) rule
       (rule-form-instance (sublis-var usigma rule-form))
       (mc (get1 :meta-replace constraint-rule))
       ((mv atom-alist splice-alist)  (eval-meta-replace mc usigma vl wrld))
       (rule-form-instance-renamed (let ((str-alist `((,(symbol-name pattern-x) . ,(symbol-name x)))))
                                     (acl2::template-subst rule-form-instance
                                                           :str-alist str-alist
                                                           :atom-alist atom-alist
                                                           :splice-alist splice-alist
                                                           :pkg-sym x))))
    rule-form-instance-renamed))
    
      

(defun record-p (type wrld)
  (b* ((type-entry (get1 type (defdata::type-metadata-table wrld)))
       (pdef (cgen::get1 :PRETTYIFIED-DEF type-entry)))
    (and (consp pdef)
         (equal (car pdef) 'ACL2S::RECORD))))

(defun expand-record (x type wrld)
  (b* ((type-entry (get1 type (defdata::type-metadata-table wrld)))
      (ndef (cgen::get1 :normalized-def type-entry))
      (conx (car ndef))
      (fields  (strip-cars (cdr ndef)))
      (ftypes  (strip-cdrs (cdr ndef)))
      (new-names (defdata::modify-symbol-lst (string-append (symbol-name x) ".")
                   fields
                   ""
                   (symbol-package-name x)))
      (fpreds (defdata::predicate-names ftypes (defdata::type-metadata-table wrld)))
      (pred-calls (acl2::listlis fpreds new-names)))
  (mv (cons conx new-names) pred-calls)))
                                

(defloop match-constraint/loop (constraint-rules C x vl wrld)
  "return first matched"
  (for ((crule in constraint-rules))
       (thereis (match-constraint1 crule C x vl wrld))))

(defun match-constraint (x type C vl wrld)
  (b* ((M (defdata::type-metadata-table wrld))
       ((unless (defdata::predicate-name type M)) nil)
       (constraint-rules (get2 type :constraint-rules M)))
    (match-constraint/loop constraint-rules C x vl wrld)))
       



(include-book "propagate")
(include-book "misc/bash" :dir :system)

;NOTE: Be extra careful when introducing names -- they should not clash with existing variables.
;TODO.check: RIght now I am not checking the above; so there could be variable name clash bugs.

(mutual-recursion
; Sig: symbol * symbol * pseudo-term-listp * fixnum * world * bindings * pseudo-term-listp
;      -> (mv bindings pseudo-term-listp)
; Pre: constraints mention x
(defun refine-enum-shape1 (x type constraints vl state   rtermB new-hyps)
  "Infer a more specialized ACL2 expression for x:type given additional
   constraints on x.

If no more constraints
   return rtermB, new-hyps
else pick c from constraints
  iterate over trigger-constraints t stored for type till one finds a 'match' 
  (i.e. c (subterm) matches t and satisfies the trigger's condition)
     from rule-action, get specialized exp for x and new-hyps on introduced variables
     store exp for x in rtermB, new-hyps++ 
     get type-bindings for all introduced variables
     constraints' := simplify x=exp + new-hyps ++ constraints
     for each (x' type') in type-bindings
         refine-enum-shape(x', type', constraints' on x', rtermB, new-hyps)
"
  (if (endp constraints)
      (value (list rtermB new-hyps))
    
    (b* ((C (car constraints))
         (rule  (match-constraint x type C vl (w state)))

         ((unless rule) (refine-enum-shape1 x type (cdr constraints) vl state rtermB new-hyps))
         
         (`(IMPLIES ,hyp (EQUAL ,var ,refined-exp)) rule)
         (rule-hyps (if (eq (car hyp) 'ACL2::AND) (cdr hyp) (list hyp))) ;TODO.naive

         ((unless (and (variablep var) (equal var x)))
          (prog2$ (cw? (verbose-stats-flag vl)
"Cgen/refine-enum-shape1:: Expected ~x0 to be an elim rule for var ~x1" rule x)
                  (mv t (list rtermB new-hyps) state)))
         ((when (intersection-eq (list x) (all-vars refined-exp)))
          (prog2$ (cw? (verbose-stats-flag vl)
"Cgen/refine-enum-shape1:: An Invariant broke!! ~x0 should not occur in ~x1." x refined-exp)
                  (mv t (list rtermB new-hyps) state)))

         (new-hyps (union-equal rule-hyps new-hyps))
         (rtermB   (acons x refined-exp rtermB))
         (var-type-dlist (dumb-type-alist-infer rule-hyps (all-vars-lst rule-hyps) vl (w state)))
         ;; ((er constraints~)  (acl2::bash-fn `(IMPLIES (EQUAL ,x ,refined-exp) (AND ,@(cdr constraints)))
         ;;                                    nil (debug-flag vl) 'refine-enum-shape1 state))
         ((er constraints~) (simplify-term-lst (acl2::subst-var-lst refined-exp x (cdr constraints))
                                            rule-hyps
                                            '() state))
         )
      (refine-enum-shapes1 var-type-dlist constraints~ vl state rtermB new-hyps))))

(defun refine-enum-shapes1 (var-type-dlist constraints vl state   rtermB new-hyps)
  (if (endp var-type-dlist)
      (value (list rtermB new-hyps))
    (b* (((list x type) (car var-type-dlist)) ;check shape
         ((er (list rtermB1 new-hyps1))
          (if (record-p type (w state)) ;eagerly expand records
              (b* (((mv rec-expansion rec-field-hyps) (expand-record x type (w state))))
                (value (list (acons x rec-expansion '()) rec-field-hyps)))
          (refine-enum-shape1 x type constraints vl state '() '())))
         (rtermB (union-equal rtermB1 rtermB))
         (new-hyps (union-equal new-hyps1 new-hyps)))
      (refine-enum-shapes1 (cdr var-type-dlist) constraints vl state rtermB new-hyps))))
)


;REVIST -- what if there is a loop because the bindings are recursive? and similar concerns
; termination issue lurking
(mutual-recursion
(defun expand-term-under-bindings (term B)
  (cond ((variablep term)
         (if (assoc-eq term B)
             (expand-term-under-bindings (cdr (assoc-eq term B)) (delete-assoc-eq term B))
           term))
        ((fquotep term) term)
        (t (cons (ffn-symb term)
                 (expand-terms-under-bindings (fargs term) B)))))
(defun expand-terms-under-bindings (terms B)
  (if (endp terms)
      '()
    (cons (expand-term-under-bindings (car terms) B)
          (expand-terms-under-bindings (cdr terms) B)))))

(defloop contains-var (x terms)
  "filter terms that contain variable x"
  (for ((term in terms)) (append (and (member-eq x (all-vars term))
                                      (list term)))))
(defloop remove-terms-with-vars (terms xs)
  "remove terms with variables in xs"
  (for ((term in terms)) (append (and (not (intersection-eq xs (all-vars term)))
                                      (list term)))))


(defun refine-enum-shape (var type constraints vl state)
  "Infer a more specialized (refined) ACL2 expression for x:type given
   additional constraints on x."
  (b* (((er ans) (refine-enum-shape1 var type constraints vl state '() '()))
       ((list rtermB additional-hyps) ans)
       ((when (null rtermB)) (value (list '() '())))
       (refined-term (expand-term-under-bindings var rtermB))
       (elimed-vars (strip-cars rtermB))
       (additional-hyps (remove-terms-with-vars additional-hyps elimed-vars))
       
       (new-vars (all-vars-lst additional-hyps))
       (vars-in-refined-term (all-vars refined-term))
       (- (cw? (debug-flag vl)
"vars-in-additional-hyps: ~x0 and vars-in-refined-term: ~x1" new-vars vars-in-refined-term))
       (- (assert$ (subsetp-eq vars-in-refined-term new-vars) nil)))
    (value (list refined-term additional-hyps))))
       
       
