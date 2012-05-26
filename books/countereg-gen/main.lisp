#|$ACL2s-Preamble$;
;;Author - Harsh Raju Chamarthi (harshrc)
(ld ;; Newline to fool ACL2/cert.pl dependency scanner
 "cert.acl2")
(begin-book t :ttags :all);$ACL2s-Preamble$|#


(in-package "DEFDATA")

;Useful Macros for concise/convenient code.
(include-book "tools/bstar" :dir :system)

(include-book "xdoc/top" :dir :system)
(include-book "with-timeout" :ttags :all)
(include-book "type")
;(include-book "basis")
;(include-book "testing-stobj")
;; (include-book "base")
(include-book "acl2s-parameter")
(include-book "simple-graph-array")
(include-book "random-state")
(include-book "tools/easy-simplify" :dir :system)

;For now TODO

;;;======================================================================
;;;============ Build enumerator expression code =================e=======
;;;======================================================================

;from the members of an union expression, get the constituents
;that are non-recursive.
(defthm flatten-is-true-list1 
  (implies (true-listp lst)
           (true-listp (defdata::flatten b lst)))
  :hints (("Goal" :in-theory (enable defdata::flatten))))
     


(defrec enum-info% (size category expr) NIL)

;; chose 29 bits, because ACL2 uses signed 29 bits in its code!
(defun unsigned-29bits-p (x)
  (declare (xargs :guard T))
  (acl2::unsigned-byte-p 29 x))

(defun fixnump (x)
  (declare (xargs :guard T))
  (unsigned-29bits-p x))

(defun enum-info%-p (v)
  (declare (xargs :guard T))
  (case-match v
    (('enum-info% size category expr) 

     (and (fixnump size)
          (member-eq category
                     '(:singleton :function :defconst))
          (pseudo-termp expr)))))

;usage:

;OLD COMMENT as of 10 March 2012;
;MODIFIED: I had to change the order because it was picking
;up *empty-values* as a constant value and hence
;a singleton which is not working right. 
;Come back to this point later.
;;; harshrc 03/10/12 - updated it to defrec and def

(def get-enum-info% (type ctx wrld)
  (decl :sig ((possible-defdata-type-p symbolp plist-worldp) 
              -> enum-info%-p)
        :doc "to fill")
; returns a well-formed enum-info defrec object
; r is the free variable in the enum-expression which
; is the place-holder for the random-seed or BE arg 
  (if (possible-constant-valuep type)
      (acl2::make enum-info% :size 1 :category :singleton :expr type) 
;ALSO HANDLE SINGLETON TYPES DIRECTLY
    (let ((type-info 
           (get-val type (table-alist 'defdata::types-info-table wrld))))
    (if type-info ;if we find enum-info from type-info-table then use it
        (b* ((size (g :size type-info))
             ((unless (or (eq 't size)
                          (posp size)))
              (er hard ctx "size in type-info ~x0 should be posp.~%" type-info))
             (enum (g :enumerator type-info))
             (test-enum (g :test-enumerator type-info)))
             ;first check for test-enum
          (if test-enum
              (cond 
               ((allows-arity test-enum 1 wrld)
;TODO. I am not checking if test enumerator is to be used or not
                (acl2::make enum-info% :size 't
                          :category :function
                          :expr (list test-enum 'r)))
;this is possible because a test-enum can be a singleton
               ((possible-constant-valuep test-enum) 
                (acl2::make enum-info% :size 1 
                          :category :singleton :expr test-enum)) ;singleton
               (t (let ((stored-defconst 
                         (acl2-getprop test-enum 'const wrld)))
                    
                    (if stored-defconst ;some finite set of values
                        (let* ((values (second stored-defconst))
                               (len-v (len values)))
                          (acl2::make enum-info%  
                             :size len-v 
                             :category (if (= len-v 1) 
                                           :singleton
                                         :defconst)
                             :expr (if (= len-v 1)  
                                       `',(car values)
                                     `(nth r ,test-enum))))
                       (er hard ctx 
"~x0 is neither one of constant, an enumerator function or a values defconst.~%" test-enum)))))

;common scenario: inf enumerator
            (if (eq 't size);inf or custom registered (assume)
                (acl2::make enum-info% :size 't :category :function
                          :expr (list enum 'r));inf or some enum fn
              (let ((stored-defconst 
                     (acl2-getprop enum 'const wrld)))
         
                (if stored-defconst ;some finite set of values
                     (b* ((values (second stored-defconst))
                            (len-v (len values))
                            ((unless (posp len-v))
      (er hard ctx "stored-defconst ~x0 has 0 values~%" stored-defconst)))
                       (acl2::make enum-info%
                          :size len-v 
                          :category (if (= len-v 1) 
                                        :singleton
                                      :defconst)
                          :expr (if (= len-v 1)  
                                    `',(car values)
                                  `(nth r ,enum))))
;uncommon scenario, finite enumerator function        
                    (if (allows-arity enum 1 wrld) 
                        (acl2::make enum-info% :size size 
                                  :category :function
                                  :expr (list enum 'r));some enum fn
                
                      (er hard ctx 
"~x0 is neither one of constant, an enumerator function or a values defconst.~%" enum)))))))
      ;;;o.w we just call peter's fn
      (let* ((vsym (modify-symbol "*" type "-VALUES*"))
             (values (second (acl2-getprop vsym 'const wrld))))
                    
        (if values
            (let ((len-v (len values)))
               (acl2::make enum-info%
                        :size len-v 
                        :category (if (= len-v 1) 
                                      :singleton
                                    :defconst)
                        :expr (if (= len-v 1)  
                                  `',(car values) 
                                `(nth r ,vsym))))
          (let ((esym (modify-symbol "NTH-" type "")))
            ;;check if enum is defined in wrld
            (cond ((allows-arity esym 1 wrld) 
                   (acl2::make enum-info% 
                             :size t 
                             :category :function
                             :expr `(,esym r)))
                  (t 
                   (er hard ctx 
                       "~x0 doesnt appear to be a type.~%" type))
                       ))))))))
              
;May 8 2011
;testing history data structure
;; Maps variables to vtest-history 
;; vtest-history: 
;; (record (n . current test-run-number)
;;         (rec-size . last recursion size chosen for this variable)
;;         (strategy . :random :bounded)
;;         (enum-expr . enumerator expression with holes)
;;         (enum-arg-alist . special alist to fill in the above holes)
;;         (i . determines X_i to be incremented in BE testing))
;; enum-arg-alist:
;; ((defdata::X  . (record (size . t | fin-size) (val . last val of X) ) ...)


;identify (equal x y)
(defun equiv-hyp? (hyp)
  (and (= 3 (len hyp))
       (member-eq (car hyp) '(equal = eq eql));TODO
       (is-a-variablep (second hyp))
       (is-a-variablep (third hyp))))

;identify (equal 3 x) or (equal x 42)
(defun constant-hyp? (hyp)
  (and (= 3 (len hyp))
       (member-eq (car hyp) '(equal = eq eql))
       (or (and (is-a-variablep (second hyp))
                (possible-constant-value-expressionp (third hyp)))
           (and (is-a-variablep (third hyp))
                (possible-constant-value-expressionp (second hyp))))))

;chyp=(equal x <const>)
;gives (mv x <const>)
(defun destruct-simple-hyp (chyp)
  (if (is-a-variablep (second chyp))
      (mv (second chyp) (third chyp))
    (mv (third chyp) (second chyp))))

;identify (equal x expr) or (equal expr y) where expr is not a const expr
;disjoint with constant-hyp? and equiv-hyp?
;added an extra argument storing scc information about variable dependency.
;avoid hyps which may lead to circular dependency

; MODIFIED May 7 2011, if expr is (g a v) then return false, because we want it
; to furthur get dest-elimed, since if we there is still a mget call around it
; has to be a list/map mget call and we want the other variable to get mset
; into the list/map variable rather than the x getting value from mget of
; list/map variable .
(defun simple-var-hyp? (hyp var-quotient-alst list-dest-fns)
  (and (not (constant-hyp? hyp));not (= x c)
       (not (equiv-hyp? hyp));not (= x y)
       (= 3 (len hyp))
       (mem-eq (car hyp) '(equal = eq eql))
       (or (is-a-variablep (second hyp))
           (is-a-variablep (third hyp)))
       (mv-let (var expr)
               (destruct-simple-hyp hyp)
               (and 
                ;;No cycles
                (let* ((vquotient (get-val var var-quotient-alst))
;get-free-vars1 only non-buggy for terms
                       (dvars (get-free-vars1 expr nil))
                       (dquotients (get-val-lst dvars var-quotient-alst)))
                  (not (mem1 vquotient dquotients)))
                ;;No top-level mget in expr
                (not (member-eq (car expr) list-dest-fns))))))
                    



(defun directed-2-rel? (hyp)
  ;(declare (xargs :guard (pseudo-termp hyp)))
;is hyp a directed (computationally) binary relation term
;hyp = (R x (f y)), where f should represent
;some computation other than accessors
;Assumption, hyp cannot be a constant hyp, since
;this function is always called after constant-hyp?
;in function build-vdependency-graph
;TODO maintain a global list of common accessor functions
  (and (= (len hyp) 3)
       (let* ((t2 (second hyp))
              (t3 (third hyp)))
         (or (and (is-a-variablep t2) 
                  (consp t3)
                  (not (member-eq (car t3) 
                           '(acl2::mget acl2::g g
                                        acl2::nth acl2::car SETS::head
                                        acl2::cdr SETS::head))))
             (and (is-a-variablep t3) 
                  (consp t3);copy paste bug
                  (not (member-eq (car t3) 
                           '(acl2::mget acl2::g g
                                        acl2::nth acl2::car SETS::head
                                        acl2::cdr SETS::head))))))))
              
(defun undirected-2-rel? (hyp)
 ; (declare (xargs :guard t))
;is hyp a undirected (computationally) binary relation term
;hyp = (~ x y), where ~ should be one of 
;(= eq equal eql subset-equal < <= > >=)
;TODO maintain a global list of such functions

  (and (= (len hyp) 3)
       (let* ((t2 (second hyp))
              (t3 (third hyp)))
         (and (is-a-variablep t2) 
              (is-a-variablep t3)
              (member-eq (first hyp) ;Relation
                  '(acl2::= acl2::equal acl2::eq acl2::eql
                            acl2::< acl2::<= 
                            acl2::> acl2::>=))))))

;hyp is of form (R term1 term2 ... termn)
;alst is basically the adjacency list rep of a graph
;Assumption term-lst is a term-listp otherwise get-free-vars1
;will not operate correctly
(defun put-interdependency-edges-in-alst (term-lst all-terms alst)
  #|(declare (xargs :guard (and (true-listp term-lst)
                              (true-listp all-terms)
                              (alistp alst))))|#
  (if (endp term-lst)
    alst
    (let* ((term (car term-lst))
           (vars (get-free-vars1 term nil))
           (rest-terms (remove-equal term all-terms))
           (rest-vars (get-free-vars1-lst rest-terms nil))
           )
      (put-interdependency-edges-in-alst 
       (cdr term-lst) all-terms
       (union-entries-in-adj-list vars ;sloppy, dont want self-edges
                                  (set-difference-eq rest-vars vars)
                                  alst)))))
         
;make a dependency graph of variables in a formula.
;TODO: equal can be any equivalence relation
;An edge from A to B means, A depends on B
;Note: (equal x <constant-expr>) forces x to be a leaf!!

;alst = ((var . (listof var)) ...) 
;alst-C= ((var . nil)) ;constants are forced to be leaves
;incoming = (map var (map symbol nat)) 
;e.g  (x . ((= . 1) (R . 2) (< . 1)) YET to be IMPLEMENTED

;PreCondition: hyp-lst is a term-list (IMPORTANT)
(defun build-vdependency-graph (hyp-lst alst alst-C incoming)
  (declare (ignorable incoming))
  (declare (xargs :verify-guards nil
                  :guard (and (pseudo-term-listp hyp-lst)
                              (symbol-alistp alst);       TODO
                              (symbol-alistp alst-C);     lost
                              (symbol-alistp incoming))));type information
 "return the dependency graph in alst, when all hypotheses have been 
processed, the annotation of edges is also returned"
  (if (endp hyp-lst)
    (append alst alst-C) ;ques: shouldnt the order be the other way round?
    (let ((hyp (car hyp-lst)))
      (cond 
       ((constant-hyp? hyp) ;(equal x (cons 1 2))
        (b* (((mv var &) (destruct-simple-hyp hyp)))
          (build-vdependency-graph (cdr hyp-lst)
                                   (remove-entry var alst)
;annotate the fact that var is assigned to a constant
                                   (put-assoc-equal var nil alst-C)
                                   incoming)))
       
       ((undirected-2-rel? hyp);(~ x  y)
;dont draw an edge
        (build-vdependency-graph (cdr hyp-lst) alst alst-C incoming))
       ((directed-2-rel? hyp);(= x (f y))
        (b* (((mv var term) (destruct-simple-hyp hyp))
             (fvars (remove-equal ;sloppy code
                     var (get-free-vars1 term nil))));buggy for non-terms
          (build-vdependency-graph 
           (cdr hyp-lst)
;Q:shudnt we overwrite instead?
;A:No, consider both (= x (f y)) (= x (g w)) in hyps
;But does it matter either way? TODO
           (union-entry-in-adj-list var fvars alst) 
           alst-C
           incoming)))
       (t
;(R term1 term2 ...termN) ==> add edges between x and y where x \in termI
;and y \in termJ and I=!J and R is a N-ary relation
        (let* 
            ((vars (get-free-vars1 hyp nil));only non-buggy for terms
             (num-vars (len vars)))
          (if (<= num-vars 1);unchanged
              (build-vdependency-graph (cdr hyp-lst) alst alst-C incoming)
            (b* ((alst1 (put-interdependency-edges-in-alst 
                         (cdr hyp) ;recurse (term1 ... termn)
                         (cdr hyp) ;all-terms
                         alst))) 
              (build-vdependency-graph (cdr hyp-lst) 
                                       alst1 alst-C incoming)))))))))


(defun build-variable-dependency-graph (hyps vars)
  (build-vdependency-graph hyps (make-empty-adj-list vars) nil nil))

#|
    (c nil ;dep-info record
       :hyps hyps-new 
       :concl concl-new 
       :hyp-vars hyp-vars
       :concl-vars concl-vars
       :vars vars
       :var-type-expr-alist new-var-te-alist
       :var-dependency-adj-list dgraph
       :var->ccnum var-quotient-alst
       :connected-vertices-ordered-list connected-vs-lst)
       ))
|#
            





(defxdoc ACL2::TESTING
  :short "A Testing framework for ACL2"
  :long                               
  "<p>Test formulas before and during a proof attempt, to find
  counterexamples and witnesses potentially saving time and
  effort and providing more intuition into the conjecture under
  scrutiny.  The testing framework is tightly coupled with the
  data definition (<sf>defdata</sf>) framework.</p>
  <p>                  
  test? guarantees printing counterexamples in
  terms of the top goals variables. Unlike thm?
  it takes only one argument(the form to be tested).
  </p>
  <code>
   (test? (implies (and (posp (car x))
                        (posp (cdr x)))
                   (&gt;= (cdr x) (len x))))
  </code>               
  <p>Only do top-level testing </p>
  <code>
   (top-level-test? (equal (reverse (reverse x)) x))
  </code>
  <p>
  To understand more about how testing works,
  please refer to the following 
<a href='http://www.ccs.neu.edu/home/harshrc/ITaITP.pdf'>paper</a></p>
  ")


;;;; Main Idea
;;;; Given any formula, we want to test it using test? or
;;;; amidst a prove call.  By test it, I mean we search for an
;;;; instantiation (or assignment) of the free variables in the
;;;; formula *and* evaluate the ground formula resulting from
;;;; substituting the assignment.  The way 'S2' (name of our
;;;; implementation) works is as follows. We set up the type
;;;; infrastructure, i.e we store type meta data in ACL2 tables for
;;;; all primitive/basic types in ground ACL2 and provide the user
;;;; with macros (defdata) to introduce new types. These macros
;;;; automate maintenance of type meta data. The metadata henceforth
;;;; called defdata tables, store the enumerators for each type
;;;; predicate, and also capture the relationship (subtype and
;;;; disjoint) among the different types. The latter are useful in
;;;; finding the minimal (possible) type information for a variable
;;;; constrained by multiple predicates/relations. When we say 'type',
;;;; we refer to a name that characterizes a set in the ACL2
;;;; Universe. This 'type' is characterized redundantly both with a
;;;; monadic predicate and an monadic enumerator. When the user asks
;;;; to test?/thm a conjecture, S2 queries the defdata tables to
;;;; obtain the name of the corresponding enumerator for each variable
;;;; constrained by a monadic predicate in the conjecture.  In
;;;; practice what S2 derives is not an enumerator function but an
;;;; enumerat(or/ing) expression with holes. When these holes are filled
;;;; with random natural numbers, it will evaluate to a random value
;;;; satisfying the type-like constraints of the concerned
;;;; variable in the conjecture under test. Also in practice there is
;;;; dependency among variables and naively instantiating all of them
;;;; independently will lead to poor test data, since the full
;;;; assignment might turn out to be vacuous (inconsistent hypotheses)
;;;; many a time. (And this indeed is the main hurdle to be crossed).
;;;; 
;;;; Clearly to obtain the best results, we want to be able to do the
;;;; following things.
;;;; 1. Derive an enumerator expression for each variable that
;;;; evaluates to a minimal set of values, the variable is allowed to
;;;; take.
;;;; 2. Derive an enumerator expression for each
;;;; variable that takes into account its dependency on other
;;;; variables. i.e If (= x (f y)) and (posp y), then enumerator
;;;; expression call (enumcall) for y is (nth-pos n) and for x it is
;;;; simply (f y). Thus x never evaluates to a value that would make
;;;; its constraint inconsistent. Things are more complicated for
;;;; mutually-dependent variables and for complex dependency
;;;; relations. 
;;;; 
;;;; Feb 3 2012
;;;; This is basically a constraint satisfaction problem and there exist
;;;; naive backtracking algorithms for finite-domain variables. There also
;;;; exists the notion of arc-consistency, which basically tells you if it
;;;; is possible to extend an partial assignment without backtracking. So
;;;; the "ideal scenario" is to construct the assignment without backtracking.

;;;; Right now, in one search strategy, which is named "simple", we
;;;; simply compute enumerator/type expressions for all free
;;;; variables, taking into account "equality" dependencies and use
;;;; this as a template code to plug in random natural numbers or
;;;; bounded consecutive natural number tuples to obtain either random
;;;; value assignment or a consecutive value assignment in the bounded
;;;; value space of free variables. 

;;;; Alternatively, in the DPLL-style search strategy, which we named
;;;; as "incremental", we incrementally build the assignment, taking
;;;; into account dependency, by selecting the least "dependent"
;;;; variable in the dependency graph built from the conjecture. After
;;;; every variable is assigned a new value (satisfying its local type
;;;; constraints), this information is propagated using the theorem
;;;; prover itself. If the resulting hypotheses of the partially
;;;; instantiated conjecture are contradictory/inconsistent, then we
;;;; backtrack to the last "decision" Assign. We stop when we either
;;;; backtrack too many times, or we have obtained the full value
;;;; assignment (called sigma hereafter).

;;;; The following illustrates the top-level driver pseudocode

;;;; Top-level test driver loop for Conjecture/Subgoal G
;;;; ALl alists u see below have as keys the free variables of G.

;;;; Initialization code:
;;;; defattach conclusion-val/hypotheses-val for G
;;;; T_naive := get naive type alist from defdata tables for G
;;;; T_ACL2  := get ACL2 type alist for freevars(G)
;;;; T_final := get type expression alist for freevars(G) using
;;;;            T_naive, T_ACL2 and the dependency graph of G.
;;;; E := get enumerator expression alist for G using T_final
;;;; make defun next-sigma using E and random seed, be arg tuple
;;;; defattach next-sigma to a fun computing assignments
;;;;   
;;;;
;;;; Driver loop code:
;;;; repeat *num-trial* times or till we meet stopping condition
;;;; \sigma := (next-sigma ...)
;;;;   if (hypotheses-val \sigma)
;;;;      if (conclusion-val \sigma)
;;;;         record witness 
;;;;       record counterexample
;;;;    record vacuous
;;;; end
;;;;
;;;; conclusion-val and hypotheses-val are stub functions which
;;;; are attached during the main search function.
;;;; They take a substitution and apply it to G, returning a boolean.

;;;;harshrc
;;;;10th Jan 2012 (Tuesday)

;;; Purpose: Given a value substitution, the following functions will
;;; apply it to the hypotheses and conclusion of the conjecture under
;;; test and compute the value of the resulting ground formula.
;;; Sig: sigma -> boolean
;;; where sigma is the let bindings or simply the binding of free variables to
;;; values satisfying the "types" of the respective variables.
;(defstub hypotheses-val (*) => *)
(encapsulate
  ((hypotheses-val
    (A) t
    :guard (symbol-doublet-listp A)))
 
  (local (defun hypotheses-val (A) (list A))))
;(defstub conclusion-val (*) => *)
(encapsulate
  ((conclusion-val
    (A) t
    :guard (symbol-doublet-listp A)))
 
  (local (defun conclusion-val (A) (list A))))

;;; Purpose: For the current ... , generate the next value-alist
;;; (sigma) for the formula under test.  next-sigma : (sampling-method
;;; seed tuple) ->  seed' * tuple' * A' Given the sampling method,
;;; current random seed, the current nth-tuple (of nats), it computes
;;; the full assignment (sigma) to be used in the upcoming test run
;;; and also returns the updated seed and updated nth-tuple
(defstub next-sigma (* * *) => (mv * * *))


(def single-hypothesis (hyp-list)
  (decl :sig ((pseudo-term-list) -> (oneof 'T pseudo-term))
        :doc
"?: Transform a list of hypotheses into an equivalent hypothesis
 eg: (single-hypothesis '((posp x) (stringp s)) ==> (and (posp x) (stringp s))
     (single-hypothesis '()) ==> T")
  (if (endp hyp-list)
    't
    `(and ,@hyp-list)))





(set-verify-guards-eagerness 2)

(defun local-sampling-method-builtin (sampling-method i N)
  (declare (xargs :guard (and (natp N)
                              (natp i)
                              (member-eq sampling-method '(:mixed :random :be))
                              (<= i N))))
  (b* (((unless (eq :mixed sampling-method))
        sampling-method))

    (cond ((zp N) :random)
          ((< (/ i N) (/ 50 100))
; first half do bounded-exhaustive testing, then switch to random testing
           :be)
          (t :random))))

(encapsulate
  ((local-sampling-method 
    (s i N) t
    :guard (and (member-eq s '(:mixed :random :be));(keywordp s)
                (natp i) (natp N) (<= i N))))
  
  (local (defun local-sampling-method (s i N) (list s i N))))

(defattach (local-sampling-method local-sampling-method-builtin))


(defrec gcs% ;global-coverage-stats 
  ((total-runs dups . vacs)
   (cts . wts) 
   (cts-to-reach . wts-to-reach)
   (start-time . end-time) id) NIL) ;(hyps . concl) serves as an id


(def initial-gcs% (nc nw start id)
  (decl :sig ((fixnump fixnump rationalp allp) -> gcs%-p)
        :doc "reset/initialized global coverage stats record")
  (acl2::make gcs% :cts 0 :wts 0 :cts-to-reach nc :wts-to-reach nw
        :total-runs 0 :vacs 0 :dups 0 :start-time start :end-time start
        :id id))

(defun gcs%-p (v)
  (declare (xargs :guard T))
  (case-match v
    (
     ('gcs% (total-runs dups . vacs)
            (cts . wts) 
            (cts-to-reach . wts-to-reach)
            (start-time . end-time) &)
     (and (unsigned-29bits-p cts)
          (unsigned-29bits-p wts)
          (unsigned-29bits-p cts-to-reach)
          (unsigned-29bits-p wts-to-reach)
          (rationalp start-time)
          (rationalp end-time)
          (unsigned-29bits-p total-runs)
          (unsigned-29bits-p dups)
          (unsigned-29bits-p vacs)))))

(defmacro gcs-1+ (fld-nm)
  `(change gcs% ,fld-nm
             (acl2::|1+F| (access gcs% ,fld-nm))))


(encapsulate
  ((stopping-condition? 
    (gcs%) t
    :guard (gcs%-p gcs%)))
  (local (defun stopping-condition? (gcs%) (list gcs%))))

;;; Style of accessing/changing defrec objects. The name of the object is
;;; always same as the name of the defrec, just like in stobjs. THis was we
;;; can drop in stobjs in their place!
(defmacro access (r a)
  `(acl2::access ,r ,r ,(intern-in-package-of-symbol (symbol-name a) :key)))
(defmacro change (r a val )
  `(acl2::change ,r ,r ,(intern-in-package-of-symbol (symbol-name a) :key) ,val))
           
(defun stopping-condition?-builtin (gcs%)
  (declare (xargs :guard (gcs%-p gcs%)))
  (and (>= (access gcs% cts) (access gcs% cts-to-reach))
       (>= (access gcs% wts) (access gcs% wts-to-reach))))

(defattach stopping-condition? stopping-condition?-builtin)


(set-verify-guards-eagerness 1)

(def run-single-test. (sampling-method N i r. BE.)
  (decl 
        :sig ((keyword fixnum fixnum fixnum symbol-fixnum-alist) 
              -> 
              (mv keyword symbol-doublet-listp fixnum symbol-fixnum-alist))
        :doc 
"?:
* Synopsis 
Run single trial of search for cts/wts for the formula under test.

* Input parameters 
'N' stands for num-trials.  sampling-method is
itself.  i is the current local-trial number.  'r.' is the current
pseudo-random seed.  'BE.' is alist that holds previous
bounded-exhaustive nat arg seeds used to compute sigma.

* Return sig: (mv res A r. BE.)
A is computed sigma (value binding) used to test this run
res is :vacuous if the hypotheses were inconsistent under A
res is :witness if both conclusion and hyps eval to T under A
else is :counterexample
r. is updated pseudo-random seed
BE. is the updated bounded-exhaustive arg/seed alist.

eg:n/a")
  
  (b* ((sm (local-sampling-method sampling-method i N))
       ((mv A r. BE.) (next-sigma sm r. BE.))
       (|not vacuous ?|  (hypotheses-val A)))
;  in
   (if |not vacuous ?|
       ;; bugfix: why even try to evaluate conclusion when
       ;; the hypotheses arnt satisfied, the whole form's value
       ;; is simply true - May 2nd '12
       (let ((res (if (conclusion-val A) :witness :counterexample)))
        (mv res A r. BE.))
     (mv :vacuous A r. BE.))))

(defrec run-hist% 
  ((|#cts| . cts) (|#wts| . wts) (|#vacs| . vacs) . |#dups|)
; each test run statistics/results are accumulated in run-hist%
  NIL)

(defun run-hist%-p (v)
  (declare (xargs :guard T))
  (case-match v ;its a good thing I dont use case-match run-hist%
    ;anywhere else. The internal layout of run-hist% is thus hidden.
    (('run-hist% (|#cts| . cts) (|#wts| . wts) (|#vacs| . vacs) . |#dups|)
              
     (and (symbol-doublet-list-listp cts)
          (symbol-doublet-list-listp wts)
          (symbol-doublet-list-listp vacs)
          (unsigned-29bits-p |#wts|)
          (unsigned-29bits-p |#cts|)
          (unsigned-29bits-p |#vacs|)
          (unsigned-29bits-p |#dups|)))))
          

(defmacro run-hist-1+ (fld)
"increments the number-valued fields of run-hist%"
  (let* ((fld-dc (string-downcase (symbol-name fld)))
         (fld-nm (intern-in-package-of-symbol 
                  (concatenate-names (list "#" fld-dc)) 'run-hist%)))
    `(change run-hist% ,fld-nm
             (acl2::|1+F| (access run-hist% ,fld-nm)))))


(def record-testrun. (test-assignment-was A run-hist% gcs%)
  (decl :sig ((keyword symbol-doublet-listp run-hist%-p gcs%-p)
              ->
              (mv run-hist%-p gcs%-p))
        :doc 
"?: records the diagnostics/results of a single test trial run ")

  (b* ((num-wts (access gcs% wts-to-reach))
       (num-cts (access gcs% cts-to-reach))
       (gcs% (gcs-1+ total-runs)))
;   in
    (case test-assignment-was
      (:counterexample   (b* ((A-cts (access run-hist% cts))
                             
                             ((when (member-equal A A-cts))
                              (mv (run-hist-1+ dups) (gcs-1+ dups)));ignore A
                             
                             (gcs% (gcs-1+ cts))
                             (m    (access run-hist% |#cts|))
                             (run-hist% ;TODO:per subgoal num-cts stored??
                              (if (< m num-cts)
                                  (change run-hist% cts (cons A A-cts) )
                                run-hist%));dont store extra 
                             (run-hist%   (run-hist-1+ cts)))
;                              in
                         (mv run-hist% gcs%)))


      (:witness          (b* ((A-wts (access run-hist% wts))
                             ((when (member-equal A A-wts))
                              (mv (run-hist-1+ dups) (gcs-1+ dups)))
                             (gcs% (gcs-1+ wts))
                             (m    (access run-hist% |#wts|))
                             (run-hist%   
                              (if (< m num-wts)
                                  (change run-hist% wts (cons A A-wts))
                                run-hist%));dont store extra
                             (run-hist%   (run-hist-1+ wts)))
;                         in       
                          (mv run-hist% gcs%)))

                                             
      (:vacuous          (b* ((A-vacs (access run-hist% vacs))
                             ((when (member-equal A A-vacs))
                              (mv ( run-hist-1+ dups) (gcs-1+ dups)))
                             (gcs% (gcs-1+ vacs))
                             (m    (access run-hist% |#vacs|))
                             (run-hist%   
                              (if (< m (acl2::+f num-wts num-cts))
                                  (change run-hist% vacs (cons A A-vacs))
                                run-hist%));dont store a lot of vacuouses
                             (run-hist%   (run-hist-1+ vacs)))
;                         in
                          (mv run-hist% gcs%)))
      (otherwise         (prog2$ (er hard 'test? "not possible") 
                                 (mv run-hist% gcs%))))))


(def run-n-tests. (n num-trials sm vl r. BE. run-hist% gcs%)
  (decl 
        :sig ((fixnum fixnum keyword fixnum fixnum symbol-fixnum-alist 
                      run-hist% gcs%)
              -> (mv boolean fixnum symbol-fixnum-alist 
                     run-hist% gcs%))
        :doc
"?: 
* Synopsis
  Run 'n' number of trials on the formula under test

* Input parameters 
   n is num-trials minus current local-trial number.
  'r.'  is the current pseudo-random seed.
   BE. is the alist mapping variables to bounded-exhaustive seeds used in the last instantiation
   num-trials is the current testing default
   sm is sampling-method (the current testing default)
   vl is verbosity-level.
   run-hist% stores test run stats.
   gcs% is the global (testing) coverage statistics which is used in determining stopping condition.

* Returns: (mv stop? r. BE. run-hist% gcs%)
stop? is T when stopping-condition? call is satisfied
r. is updated pseudo-random seed
BE. is the updated alist of bounded-exhaustive seeds
run-hist% is the updated testrun history
gcs% is the updated global coverage stats.

")
  (b* (((when (zpf n)) ;Oops, ran out of random trials
        (prog2$ 
         (cw? (debug-flag vl)
                       "~|Finished running ~x0 tests!~%" num-trials)
         (mv NIL r. run-hist% gcs%)))
   
       ((when (stopping-condition? gcs%))
;return, cos we have reached our goal  
        (prog2$
         (cw? (debug-flag vl) 
"~|Stopping condition satisfied for gcs: ~x0~%" gcs%)
         (mv T r. run-hist% gcs%)))
       (local-trial-num  (acl2::|1+F| (acl2::-f num-trials n)))
       ((mv res A r. BE.)
;perform a random test run, the result quadruple
;erp is a flag denoting error, res = value of test  A= value-bindings
        (run-single-test. sm num-trials local-trial-num  r. BE.))
       ((mv run-hist% gcs%) (record-testrun. res A run-hist% gcs%)))
;  in   
   (run-n-tests. (acl2::|1-F| n) num-trials sm vl r. BE. run-hist% gcs%)))

          

(defmacro get-acl2s-default (param alist &optional default-value)
  "get the default value of param as found in alist. if not found return default-value"
  `(b* ((e (assoc-eq ,param ,alist)))
     (if e
         (cdr e)
       ,default-value)))         



;; Pre Condition: hypothesis-val, conclusion-val and next-sigma have been
;; attached when this function is called!
(def run-tests. (N sm vl fvars rseed. run-hist% gcs%)
  (decl :sig ((fixnump keywordp fixnump symbol-listp 
                       fixnump run-hist%-p gcs%-p) 
              -> (mv fixnump run-hist%-p gcs%-p))
        ;:trace T
        :doc 
"?: Run a bunch of simple random/bounded-exhaustive tests/trials to
  find cts/wts for form under test")
;do timeout wrapper here!        
  (b* (((mv stop? rseed. run-hist% gcs%)
        (run-n-tests. N N
                      sm
                      vl
                      rseed. 
                      (pairlis$ fvars 
                                (make-list (len fvars) :initial-element 0))
                      run-hist%
                      gcs%
                      ))
       
       (- (cw? (debug-flag vl) "~|run-hist: ~x0 ~|gcs%: ~x1~%"
               run-hist% gcs%)))
   ;;in
    (mv stop? rseed. run-hist% gcs%)))
         
          
(defun acl2s-defaults-fn. (defaults override-alist ans.)
  (declare (xargs :verify-guards nil
                  :guard (and (symbol-alistp defaults)
                              (symbol-alistp override-alist)
                              (symbol-alistp ans.))))
  (if (endp defaults)
      ans.
    (b* (((cons param rec-val) (car defaults))
         (val (g :value rec-val))
         (override (assoc-eq param override-alist))
         (val (if override (cdr override) val)))
      (acl2s-defaults-fn. (cdr defaults) 
                          override-alist 
                          (cons (cons param val) ans.)))))

(defmacro acl2s-defaults-alist (&optional override-alist)
  "return alist mapping acl2s-parameters to their default values
overridden by entries in override-alist"
  `(acl2s-defaults-fn. (table-alist 'acl2::acl2s-defaults-table (w state))
                      ,override-alist '()))
         
(def separate-const/simple-hyps. (ts wrld Hc. Hs. Ho.)
  (decl :sig ((pseudo-term-list plist-world 
               pseudo-term-list pseudo-term-list pseudo-term-list) 
              -> (mv pseudo-term-list pseudo-term-list pseudo-term-list))
        :doc "given a list of hyps, separate constant hyps, simple defdata-type hyps and others")
  (f* ((add-others-and-recurse... () (separate-const/simple-hyps. 
                                      rst wrld Hc. Hs. (cons hyp Ho.)))
       (add-constant-and-recurse (h) (separate-const/simple-hyps.
                                      rst wrld (cons h Hc.) Hs. Ho.)))
  (if (endp ts)
      (mv Hc. Hs. Ho.)
    
    (b* (((cons hyp rst) ts)) ;pattern matching in b*
    (case-match hyp
      ((P t1)     (if (and (symbolp t1)
                           (is-type-predicate P wrld))
                      (separate-const/simple-hyps. rst wrld 
                                                   Hc. (cons hyp Hs.) Ho.)
                    (add-others-and-recurse...)))
                          
      ((R t1 t2)  (if (acl2::equivalence-relationp R wrld)
                      (cond ((and (symbolp t1) (quotep t2))
                             (add-constant-and-recurse (list R t1 t2)))
                            
                            ((and (quotep t1) (symbolp t2))
                             (add-constant-and-recurse (list R t2 t1)))
                            
                            (t (add-others-and-recurse...)))
                    (add-others-and-recurse...)))
      (&          (add-others-and-recurse...)))))))



(def all-vars-lst (terms)
  (decl :sig ((pseudo-term-listp) -> symbol-list)
        :doc "all free variables in list of terms")
  (all-vars1-lst terms '()))
(verify-termination dumb-negate-lit)

(def vars-in-dependency-order (hyps concl vl wrld)
  (decl :sig ((pseudo-term-list pseudo-term fixnum plist-world) -> symbol-list)
        :doc "return the free variables ordered according to the notion of
  dependency that treats equality relation specially. See FMCAD paper for
  details, but I have not completely implemented the improvements in the
  paper. This is where I can use better heuristics. But with no hard examples
  to work on, I am doing a naive job for now.")
  (b* ((cterms (cons (dumb-negate-lit concl) hyps))
; cterms names constraint terms
       (vars (all-vars-lst cterms))
       ((mv Hc Hs Ho) (separate-const/simple-hyps. cterms wrld '() '() '()))
       
       (dgraph (build-variable-dependency-graph Ho vars)) ;TODO rewrite
       (ord-vs (rev (approximate-topological-sort dgraph (debug-flag vl))))
       
       (cvars (all-vars-lst Hc))
       (svars (all-vars-lst Hs))
; add only those svars that are not in ord-vs to front of ord-vs
; cvars should always be in front, i.e they should be chosen first
       (ord-vs (union-eq svars ord-vs)) ;NOT a set operation
       (ord-vs (union-eq cvars 
                         (set-difference-eq ord-vs cvars))))
   ord-vs))
       
;;;; Collecting type and additional constraints

;;; Given a list of hypotheses and a conclusion, we want to find the
;;; type constraints on each free variable. We collect 3 categories of
;;; constraints: 1. defdata type and spilled defdata types 2. equality
;;; constraint 3. additional constraints.  A defdata type has a
;;; type-predicate and a type-enumerator associated with it.  Ideally
;;; we would like to compute the minimal (best possible) defdata type
;;; information, but this can fail, due to incomplete subtype type
;;; information.  So we end up also storing spillover types, whose
;;; union/join is the conservative (superset) type of the
;;; corresponding variable. We also store the equality constraint,
;;; since its a very strong constraint and often comes up in naive
;;; dependencies. Finally we also store additional constraints, just
;;; so as to not throw away information that can fruitfully be utilized
;;; to come up with the smallest set of possible values the
;;; constrained variable can take.

(defrec cs% (defdata-type spilled-types 
              eq-constraint additional-constraints) NIL)

(defun possible-defdata-type-p (v)
  (declare (xargs :guard T))
  (or (is-singleton-type-p v)
      (is-a-variablep v))) ;defdata type

(defun possible-defdata-type-list-p (vs)
  (declare (xargs :guard T))
  (if (consp vs)
      (and (possible-defdata-type-p (car vs))
           (possible-defdata-type-list-p (cdr vs)))
    T))

(defun cs%-p (v)
  (declare (xargs :guard T))
  (case-match v
    (('cs% dt st eqc ac)   (and (possible-defdata-type-p dt) 
                           (possible-defdata-type-list-p st)
                           (or (pseudo-termp eqc)
                               (null eqc))
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

;;;; collect-type-constraints : Hyps * Concl -> alistof var cs%

;;; Preconditions: Hyps and Concl are if-normalized terms with
;;; at the least no top-level lambda-applications.
;;; Walk over each hypothesis (termp), take care of the cases where
;;; hypothesis is 1. (defdata-type-predicate x) 2. (equal x quoted-constant)
;;; 3. (implies t1 t2) 4. (if t1 t2 t3) 5. (not x) 6. (equal x (g y))
;;; 7. (R . ts)  TODO: some cases have not been fully implemented

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

(def put-eq-constraint. (v term v-cs%-alst.)
  (decl :sig ((symbol pseudo-term symbol-cs%-alist) 
              -> symbol-cs%-alist)
        :doc "put eq-constraint term in alist for key v")
  (b* (((cons & cs%) (assoc-eq v v-cs%-alst.))
       (eqc (access cs% eq-constraint))
       (- (cw? (not (null eqc)) "Warning: Overwriting eq-constraint
  for ~x0.~|" v))
       (cs% (change cs% eq-constraint term)))
   (put-assoc-eq v cs% v-cs%-alst.)))

(def put-defdata-type. (v typ vl v-cs%-alst.)
  (decl :sig ((symbol possible-defdata-type-p fixnum symbol-cs%-alist) 
              -> symbol-cs%-alist)
        :doc "put defdata type typ in alist for key v")
  (b* (((cons & cs%) (assoc-eq v v-cs%-alst.))
       (dt (access cs% defdata-type))
       (- (cw? (and (debug-flag vl) (not (eq 'all dt))) 
"Observation: Overwriting defdata type for ~x0. ~x1 -> ~x2~|" v dt typ))
       (cs% (change cs% defdata-type typ)))
   (put-assoc-eq v cs% v-cs%-alst.)))



(defs  ;;might be mut-rec, but right now I assume tht I wont encounter
       ;;AND and OR like if expressions, and hence dont need the
       ;;mutually-recursive counterpart of v-cs%-alist-from-term. TODO
  (v-cs%-alist-from-term. (term type-alist vl wrld ans.)
  (decl :sig ((pseudo-term symbol-alist fixnum plist-world symbol-cs%-alist)
              ->
              symbol-cs%-alist)
        :doc "helper to collect-constraints")
;Invariant: ans. is an alist thats in the order given by dependency analysis
  (f* ((add-constraints... () (put-additional-constraints. fvars term ans.))
         
       (add-eq-constraint... (t1) (if (acl2::equivalence-relationp R wrld)
                                      (put-eq-constraint. x t1 ans.)
                                    (add-constraints...)))

       (current-defdata-type (x) (b* (((cons & cs%) (assoc-eq x ans.))
                                      (typ (access cs% defdata-type))
                                      (prior-t (assoc-eq x type-alist))
                                      (typ-given 
                                       (if (and prior-t
                                                (consp (cdr prior-t))
                                                (null (cddr prior-t)))
; TODO: Union types are ignored. Implement them.
                                           (cadr prior-t)
                                         'ACL2::ALL)))
                                  (acl2::meet typ typ-given wrld))))
                                  
                                        
     
   (b* ((fvars (all-vars term)))
           
    (case-match term
      
;TODO possible field variable (i.e f is a getter/selector)
; Note that term cannot have a lambda applicaton/let, so the car of the term is
; always a function symbol if term is a consp.
      ((P (f . &)) (declare (ignore P f))  (add-constraints...)) 

;x has to be an atom below, otherwise, we would have caught that case above.
      (('not x)      (put-eq-constraint. x ''nil ans.))
      
      ((P x)   (let ((tname (is-type-predicate P wrld)))
                (if tname
                    (put-defdata-type. 
                     x (acl2::meet tname (current-defdata-type x) wrld) vl ans.)
                  (add-constraints...))))

      ((R (f . &) (g . &)) (declare (ignore R f g)) (add-constraints...))

;x has to be an atom below, otherwise, we would have caught that case
;above.
      ((R x ('quote c))    (add-eq-constraint... (kwote c)))
      ((R ('quote c) x)    (add-eq-constraint... (kwote c)))
      ((R x (f . args))    (add-eq-constraint... (acl2::cons-term f args)))
      ((R (f . args) x)    (add-eq-constraint... (acl2::cons-term f args)))
      
      ;; has to be a (R t1 t2 ...) or atomic term
      (&                   (add-constraints...)))))))
                         
   
(def v-cs%-alist-from-terms. (terms type-alist vl wrld ans.)
  (decl :sig ((pseudo-term-listp symbol-alist 
                                 fixnum plist-worldp symbol-cs%-alist) 
              -> symbol-cs%-alist)
        :doc "helper to collect-constraints%")
  (if (endp terms)
      ans.
    (v-cs%-alist-from-terms. (cdr terms) type-alist vl wrld 
                             (v-cs%-alist-from-term. (car terms) type-alist
                                                     vl wrld ans.))))

(defconst *empty-cs%*
  (acl2::make cs%
        :defdata-type 'acl2::all 
        :spilled-types '()
        :eq-constraint NIL
        :additional-constraints '()))

(def collect-constraints% (hyps ordered-vars type-alist vl wrld)
  (decl :sig ((pseudo-term-listp symbol-listp symbol-alistp 
                                 fixnum plist-worldp) -> symbol-cs%-alist)
        :doc 
" 
* Synopsis 
  For each free variable compute/infer both the simple defdata types
  and additional constraints on it.

* Input
  hyps is a usually a list of hypotheses of the conjecture under query
  and is a term-listp
  ordered-vars is the free variables of hyps, but in the variable
  dependency order as computed from the dependency graphs of hyps.
  type-alist is the type information inferred from ACL2 usually, or
  it might be prior type knowledge we dont want to lose i.e if the
  type inferred from hyps are weaker than in type-alist we will
  keep the stronger type information.
  

* Output
  An alist mapping free variables to cs% record
")
  (f* ((unconstrained-v-cs%-alst 
          (xs) 
          (pairlis$ xs (make-list (len xs)
                                  :initial-element 
                                  *empty-cs%*))))
      ;; initialize the alist
    (b* ((v-cs%-alst  (unconstrained-v-cs%-alst ordered-vars)))
       
     (v-cs%-alist-from-terms. hyps type-alist vl wrld v-cs%-alst))))

(defun symbol-unsigned-29bits-alistp (v)
  (declare (xargs :guard T))
  (if (atom v)
      (null v)
    (and (consp (car v))
         (symbolp (caar v))
         (unsigned-29bits-p (cdar v))
         (symbol-unsigned-29bits-alistp (cdr v)))))

(defthm symbol-unsigned-29bits-alistp-forwards-to-symbol-alistp
  (implies (symbol-unsigned-29bits-alistp x)
           (symbol-alistp x))
  :rule-classes :forward-chaining)

; (random-natural-seed seed.) => (mv random-nat new-seed)
#||
function to compute next BE seed tuple
Precondition: BE. is a consp, i.e at least one free variable
Here is the simple scheme:
((x 0) (y 0) (z 0)) -> 
((y 0) (z 0) (x 1)) -> 
((z 0) (x 1) (z 1)) -> 
((x 0) (y 0) (z 0)) -> 
((x 0) (y 0) (z 0)) ->
((x 0) (y 0) (z 0)) ->
((x 0) (y 0) (z 0)) 

The above algo is O(n) in num of free vars. but simple to implement.
Arrays or a stobj can make this constant time operation.  

Alternative algo: Traverse the enumeration tree in BFS order.  Hvent
thought about how to implement it.
||#

;;; (symbol-unsigned-29bits-alistp) -> symbol-unsigned-29bits-alistp)
;; update 29th April '12
;; let cut the optimization to get guards to verify
(defun |next BE args| (BE.)
  "naive bounded exhaustive enumeration."
  (declare (xargs :guard (and (true-listp BE.)
                              (consp BE.)
                              (symbol-alistp BE.))))
                          
  (b* (((cons v ;; (the (unsigned-byte 29)
                  m) (car BE.))
       (;; (the (unsigned-byte 29) 
        m~ (;; acl2::|1+F|
            1+  (nfix m))))
   (append (cdr BE.) (list (cons v m~)))))
            
     



(def make-next-sigma_mv-let (var-enumcall-alist body)
  (decl :sig ((symbol-alistp all) -> all)
        :doc "helper function to make-next-sigma")
  (f* ((mv-value (v exp) 
          `(case sampling-method 
             (:random (b* (((mv ?m r.) (random-natural-seed r.)))
                       (mv r. BE. ,(subst 'm 'r exp))))
             ;; bugfix - It is possible that m is not in exp
             ;; this is the case when exp is a eq-constraint
             (:be (b* ((?m (cdr (assoc-eq ',v BE.))))
                   (mv r. (|next BE args| BE.) ,(subst 'm 'r exp))))
             (otherwise (mv r. BE. '0)))))
                           
  (if (endp var-enumcall-alist)
      body
    (b* (((cons var ecall) (first var-enumcall-alist)))
;    in 
     `(mv-let (r. BE. ,var)
              ,(mv-value var ecall)
            ,(make-next-sigma_mv-let (rest var-enumcall-alist) body))))))

(def make-guard-var-member-eq (vars alst)
  (decl :sig ((symbol-alistp symbol) -> all)
        :doc "helper function to make-next-sigma")
  (if (endp vars)
      nil
    (cons `(member-eq ',(car vars) ,alst)
          (make-guard-var-member-eq (cdr vars) alst))))
  
(def cs%-enumcall (cs% ctx wrld computed-vars)
  (decl :sig ((cs%-p symbolp plist-worldp symbol-listp) 
              -> (mv fixnum pseudo-termp))
        :doc "for each cs% record we translate it into the
  a (mv size enumcall), where the enumcall is an expression that when evaluated
  gives the value of correct type/constraint and size is the size of the type
  i.e the set of value satisfied by the constraint")
;;; TODO: optimize/complete here using extra information in
;;; spilled-types and additional-constraints
  (case-match cs%
;('cs% defdata-type spilled-types eq-constraint additional-constraints)
    (('cs% defdata-type & 'NIL &) ;we expose cs% record in this function
     (b* ((enum-info% (get-enum-info% defdata-type ctx wrld)))
      (mv (access enum-info% size) (access enum-info% expr))))
; if we see a equality constraint, we give preference to it over a
; defdata type, but only if the variables in the eq-constraint are
; already computed i.e already have an enumcall in the final answer
    (('cs% defdata-type & eq-constraint &)    
     (b* ((eq-vs (all-vars eq-constraint))
          (remaining (set-difference-eq eq-vs computed-vars)))
      (if remaining
          (b* ((enum-info% (get-enum-info% defdata-type ctx wrld)))
           (mv (access enum-info% size) (access enum-info% expr)))
        (mv 1 eq-constraint))))
    (& (prog2$ 
        (er hard ctx "~|BAD record cs% passed to cs%-enumcall")
        (mv 1 NIL)))))
               
     

(def make-enumerator-call-alist (v-cs%-alst ctx wrld ans.)
  (decl :sig ((symbol-cs%-alist symbol plist-world symbol-alist) 
              -> symbol-alist)
        :doc 
        "given an alist mapping variables to cs% records (in dependency order),
  we walk down the alist, translating each type constraint to the corresponding
enumerator call expression")
  (if (endp v-cs%-alst)
      (rev ans.) ;dont change the original dependency order
    (b* (((cons x cs%) (car v-cs%-alst))
         ((mv & call) (cs%-enumcall cs% ctx wrld (strip-cars ans.))))
     
     (make-enumerator-call-alist (cdr v-cs%-alst) ctx wrld
                                 ;; add in reverse order
                                 (cons (cons x call) ans.)))))
    

;bugfix May 24 '12
;partial-A needs to be quoted to avoid being confused with function app
(def kwote-symbol-doublet-list (A)
  (decl :sig ((symbol-doublet-listp) -> quoted-constantp))
  (if (endp A)
      nil
    (cons (list 'list (kwote (caar A)) (cadar A))
          (kwote-symbol-doublet-list (cdr A)))))

(def make-next-sigma-defun (name hyps concl ord-vs partial-A type-alist vl wrld ctx)
  (decl :sig ((string pseudo-term-list pseudo-term symbol-list 
                      symbol-doublet-listp symbol-alist
                      fixnum plist-worldp symbol) 
              -> all)
        :doc "return the defun form defining next-sigma function, given a
        list of hypotheses and conclusion (terms)")
  (f* ((defun-form ()
         `(defun next-sigma-current (sampling-method r. BE.)
            "returns (mv A r. BE.)"
            (declare (ignorable sampling-method)) ;in case ord-vs is nil
              (declare (xargs :guard 
                              (and (member-eq sampling-method
                                              '(:random :be))
                                   (unsigned-byte-p 31 r.)
                                   (symbol-unsigned-29bits-alistp BE.)
                                   (consp BE.) ;precondition TODOcheck
                                   (and ,@(make-guard-var-member-eq
                                           (strip-cars var-enumcall-alist)
                                           'BE.)))
                              :guard-hints 
                              (("Goal" :in-theory (disable unsigned-byte-p)))))
              
              ,(make-next-sigma_mv-let
                var-enumcall-alist
; sigma will be output as a let-bindings i.e symbol-doublet-listp
                `(mv ,(make-var-value-list-bindings 
                       (strip-cars var-enumcall-alist) 
                       (kwote-symbol-doublet-list partial-A))
                     r. BE.)))))
       
   (b* ((v-cs%-alst (collect-constraints% 
                     (cons (dumb-negate-lit concl) hyps)
                     ord-vs type-alist vl wrld))
        (var-enumcall-alist 
         (make-enumerator-call-alist v-cs%-alst ctx wrld '()))
        (- (cw? (verbose-flag vl) 
"~|Subgoal ~x0 variable - enumerator expr : ~x1~%" name var-enumcall-alist)))
    (defun-form))))



(def make-let-binding-for-sigma (vs sigma-symbol)
  (decl :sig ((symbol-list symbol) -> symbol-doublet-listp)
        :doc 
"(make-let-binding-for-sigma '(x y) 'A) => ((x (get-val x A))
                                            (y (get-val y A)))
")
  (if (endp vs)
      '()
    (cons `(,(first vs) (cadr (assoc-eq ',(first vs) ,sigma-symbol)))
          (make-let-binding-for-sigma (cdr vs) sigma-symbol))))

(def make-hypotheses-val-defun (terms ord-vars)
  (decl :sig ((pseudo-term-list symbol-list) -> all)
        :doc "make the defun form for hypotheses-val defstub")
  `(defun hypotheses-val-current (A)
     (declare (ignorable A))
     (declare (xargs :guard (symbol-doublet-listp A)))
     (let ,(make-let-binding-for-sigma ord-vars 'A)
       (declare (ignorable ,@ord-vars))
      ,(single-hypothesis terms))))

(def make-conclusion-val-defun (term ord-vars)
  (decl :sig ((pseudo-term symbol-list) -> all)
        :doc "make the defun form for conclusion-val defstub")
  `(defun conclusion-val-current (A)
     (declare (ignorable A))
     (declare (xargs :guard (symbol-doublet-listp A)))
     (let ,(make-let-binding-for-sigma ord-vars 'A)
       (declare (ignorable ,@ord-vars))
      ,term)))        

;NOTE: interesting to note that I cant use defmacro instead of defabbrev
(defabbrev get-gcs%-global () 
  (if (f-boundp-global 'gcs% state)
    (b* ((gcs% (@ gcs%)))
        (if (gcs%-p gcs%)
          gcs%
          (er hard? ctx "~|gcs% found in globals is of bad type~|")))
    (er hard? ctx "~|gcs% not found in globals ~|")))

(defabbrev put-gcs%-global (gcs%) 
  (if (gcs%-p gcs%)
      (f-put-global 'gcs% gcs% state)
    (prog2$ 
     (er hard? ctx "~|gcs% being put in globals is of bad type~|")
     state)))
 
(defrec s-hist-entry% (run-hist 
                       (hyps vars . concl)
                       (type-alist . elide-map)
                       (start-time . end-time) . name) NIL)

(defun s-hist-entry%-p (v)
  (declare (xargs :guard T))
  (case-match v ;internal layout hidden
    (('s-hist-entry% run-hist
                     (hyps vars . concl)
                     (type-alist . elide-map)
                     (start-time . end-time) . name)
     (and (run-hist%-p run-hist)
          (pseudo-term-listp hyps)
          (pseudo-termp concl)
          (symbol-listp vars)
          (symbol-alistp elide-map) ;actually symbol term alist
          (symbol-alistp type-alist) ; ACL2 type alist
          (stringp name)
          (rationalp start-time)
          (rationalp end-time)))))
          
  
(defun s-hist-p (v)
"is a alist mapping strings to run-hist% records"
  (declare (xargs :guard T))
  (if (atom v)
      (null v)
    (and (consp (car v))
         (stringp (caar v))
         (s-hist-entry%-p (cdar v))
         (s-hist-p (cdr v)))))

(defabbrev get-s-hist-global () 
  (if (f-boundp-global 's-hist state)
    (b* ((s-hist (@ s-hist)))
        (if (s-hist-p s-hist)
          s-hist
          (er hard? ctx "~|hist found in globals is of bad type~|")))
    (er hard? ctx "~|hist not found in globals ~|")))

(defabbrev put-s-hist-global (s-hist) 
  (if (s-hist-p s-hist)
      (f-put-global 's-hist s-hist state)
    (progn$
     (cw? (verbose-flag vl) "~|BAD s-hist : ~x0~|" s-hist)
     (er hard? ctx "~|hist being put in globals is of bad type~|")
     state)))


(defconst *initial-run-hist%* 
  (acl2::make run-hist% 
              :cts '() :wts '() :vacs '() 
              :|#wts| 0 :|#cts| 0 
              :|#vacs| 0 :|#dups| 0))

(def initial-s-hist-entry% (name hyps concl vars 
                                       type-alist elide-map start)
  (decl :sig ((string pseudo-term-list pseudo-term symbol-list 
                      symbol-alist symbol-alist rational) 
              -> s-hist-entry%)
        :doc "make initial s-hist-entry% given args")
  (acl2::make s-hist-entry% 
              :name name :hyps hyps :concl concl :vars vars 
              :type-alist type-alist :elide-map elide-map
              :start-time start :end-time start
              :run-hist *initial-run-hist%*))
          
(def simple-search (name 
                    hyps concl vars partial-A 
                    type-alist
                    run-hist% gcs%
                    N vl sm programp
                    ctx wrld state)
  (decl :sig ((pseudo-term-list pseudo-term symbol-list 
               symbol-doublet-listp symbol-alist
               run-hist% gcs% fixnum fixnum keyword boolean
               symbol plist-world state) 
              -> (mv erp (list boolean run-hist% gcs%) state))
        :mode :program
        :doc 
"
Use :simple search strategy to find counterexamples and witnesses.

* PRE : conjecture has at least one free variable

* What it does
  1. if form has no free variables exit with appropriate return val
  2. topologically sort free vars in order induced by dependency graph
     of hyps and concl
  3. make hypotheses-val conclusion-val,  attach them
  4. make next-sigma defun and attach it
  5. call run-tests!.
  6. store/record information (run-hist%,gcs%) and 
     returns (list stop? run-hist% gcs%) where stop? is T when
     stopping condition is satisfied.
")
  (b* ((hyp-val-defun   (make-hypotheses-val-defun hyps vars))
       (concl-val-defun (make-conclusion-val-defun concl vars))
       (- (cw? (debug-flag vl) 
               "~%~%~x0  hyp/concl defuns: ~| ~x1 ~x2~|" 
               name hyp-val-defun concl-val-defun))
       (next-sigma-defun (make-next-sigma-defun name hyps concl 
                                                vars partial-A type-alist
                                                vl wrld ctx))
       (- (cw? (debug-flag vl) "next-sigma : ~| ~x0~|" next-sigma-defun))
       (rseed. (getseed state))
       
       (call-form   
        `(acl2::state-global-let*
          ((acl2::guard-checking-on ,(if programp :none nil)))
          (b* (((mv stop? rseed. run-hist% gcs%)
                (run-tests. ,N ,sm ,vl ',vars
                            ,rseed. ',run-hist% ',gcs%))
               (state (putseed rseed. state)))
           (prog2$ 
            (cw? (and (verbose-flag ,vl)
                      stop?)
                 "Search aborted, because we reached stopping condition.~|")
            (mv NIL `(value-triple ',(list stop? run-hist% gcs%)) state)))))
       );end b* bindings
;  IN
   (mv-let 
    (erp trval state)
    (trans-eval `(acl2::state-global-let*
                  ((acl2::inhibit-output-lst
                    ,(if (system-debug-flag vl)
                         ''(summary)
                       ;;shut everything except error
                       ''(warning warning! observation prove
                                  proof-checker event expansion
                                  proof-tree summary)))) 
                  (make-event
                   (er-progn
                    ;; added on 29th April '12
                    ;; there is no guarantee that user will verify
                    ;; the guards of every function used in thm form
                    ;; and every enumerator of types in form
                    ;; CHECK: If we verify-guards, is it a
                    ;; substantial runtime performance plus?
                    (set-verify-guards-eagerness 0)
                    ;; added 2nd May '12. Why leave out program context
                    ,@(and programp '((program)))
                    
                    ,hyp-val-defun
                    ,concl-val-defun
                    ,next-sigma-defun
                    (defttag :testing)
; Note: all of these defuns are non-recursive and guards not verified, so
; none of these events will cause a call to prove (we hope)
; This is an important observation, since we rely on test-checkpoint
; computed hint to do testing which will get called on every call to prover.
; Thus we might pollute our globals (recorded testing information to print)
; if we make unexpected (prove ...) calls.
                    (defattach (hypotheses-val hypotheses-val-current) 
                      :skip-checks T)
                    (defattach (conclusion-val conclusion-val-current) 
                      :skip-checks T)
                    (defattach (next-sigma next-sigma-current) 
                      :skip-checks T)
                    (defttag nil)
                    
                    ,call-form))
                  )
                ctx state T)
;extract value of result i.e (list stop? run-hist% gcs%)
    (mv erp (caddr trval) state))))


(def select (terms debug)
  (decl :sig ((pseudo-term-list boolean) 
              -> symbol)
        :doc "choose the variable with least dependency. Build a dependency
  graph, topologically sort it and return the first sink we find.")
;We have to build a dependency graph at each iteration, since the graph changes
;as we incrementally concretize/instantiate variables.  
;SELECT Ideal Situation:: No variable should be picked before the variable it
;depends on has been selected and assigned

  (b* ((vars (all-vars-lst terms))
       (G (build-variable-dependency-graph terms vars))
;TODO: among the variables of a component, we should vary
;the order of selection of variables!!
       (var (car (last (approximate-topological-sort G debug))))
       (- (cw? debug "~|DPLL: Select var: ~x0~%" var)))
   var))

; May 14 '12: changed to v-cs%-alst parameter for optimization
(def assign-value (x |#assigns| cs% partial-A vl ctx wrld state)
  (decl :sig ((symbol fixnum cs% symbol-doublet-listp
                      fixnum symbol plist-world state)
              -> (mv erp (list pseudo-term keyword fixnum) state))
        :mode :program
        :doc "assign a value to x. Infer type constraints from hyps, get the
enumcall for x. trans-eval enumcall to get value to be assigned to x. quote it
to obtain a term. return (mv val :decision i+1), if size of type attributed to
x is greater than 1, otherwise return (mv val :implied i) where i= #assigns
made to x already.")

  (b* ((- (assert$ (cs%-p cs%) 1))
       (bound-vars (strip-cars partial-A))
       ((mv size call) (cs%-enumcall cs% ctx wrld bound-vars))
       
       (r. (getseed state))
       ((mv m r.) (random-natural-seed r.))
       (call (subst m 'r call))
       (state (putseed r. state))
       (vexp (if partial-A 
                 `(let ,partial-A 
                   (declare (ignorable ,@bound-vars))
                      ,call) 
               call))
       (- (cw? (debug-flag vl) 
             "~|ASSIGN: x=~x0  eval[~x1]~|" x  vexp))
       ((er ans)       (trans-eval-single-value vexp ctx state))
       (val-term       (kwote ans)))
   (if (equal size 1) ;size=0 is not possible, also size can be T (inf)
       (value (list val-term :implied |#assigns|))
     (value (list val-term :decision (1+ |#assigns|))))))

(def simplify-term (term hyps state)
  (decl :sig ((pseudo-term pseudo-term-list state) 
              -> (mv erp pseudo-term state))
        :mode :program
        :doc "simplify term under hyps. erp is T if hyps have a contradiction
  in them. return the simplifed term in value-triple")
  (acl2::easy-simplify-term1-fn term hyps '() 'equal 't 't 1000 1000 state))

; TODO: WHat will happen if some variable gets elided during this
; simplifcation?  Then our code breaks, especially rem-vars logic and capturing
; full assignment.

(def simplify-hyps1 (rem-hyps init-hyps ans. state)
  (decl :sig ((pseudo-term-list pseudo-term-list pseudo-term-list state)
              -> (mv erp pseudo-term state))
        :mode :program
        :doc "simplify each hyp in rem-hyps assuming init-hyps, accumulate in
  ans. and return a value triple containing shyps.")
  (if (endp rem-hyps)
      (value ans.)
    (b* ((hyp         (car rem-hyps))
         (other-hyps  (remove1-equal hyp init-hyps))
         ((er shyp)   (simplify-term hyp other-hyps state))
         (simplified? (term-order shyp hyp))
         ((when (eq shyp ''nil)) ;contradiction
          (mv T ans. state))
         (shyp (if simplified? shyp hyp))) ;TODO: revisit
     (simplify-hyps1 (cdr rem-hyps) init-hyps 
                     (if (eq shyp ''t) ans.
                       (append ans. (list shyp))) ;dont mess with order
                     state))))

(def simplify-hyps (hyps eq-hyp state)
  (decl :sig ((pseudo-term-list pseudo-term state) 
              -> (mv erp pseudo-term-list state))
        :mode :program
        :doc "simplify hyps assuming equality eq-hyp. return shyps in an error
        triple.")
  (b* (((er shyps1) (simplify-hyps1 hyps (list eq-hyp) '() state)))
;I do the above and then again simplify to get order-insensitive list of
;simplified hypotheses i.e the order of the hyps in the argument should not
;change the result of this function.
   (simplify-hyps1 shyps1 (cons eq-hyp shyps1) '() state)))
                      
(def propagate (x a hyps concl vl state)
  (decl :sig ((symbol pseudo-term ;actually a quoted constant
                      pseudo-term-list pseudo-term fixnum state)
              -> (mv erp (list pseudo-term-list pseudo-term) state))
        :mode :program
        :doc "propagate the assignment of a to variable x by using a utility
  function from tools/easy-simplify.lisp (earlier I was using
  expander.lisp). return (mv erp (shyps sconcl) state) where erp might be T
  indicating discovery of inconsistency/contradiction in the hypotheses")
 (b* ((eq-hyp (list 'equal x a))
      ((er shyps)  (simplify-hyps hyps eq-hyp state))
;IMP: sconcl shud be a pseudo-term; not a term-list, or an IF
      (- (cw? (debug-flag vl)
"~|PROPAGATE: ~x0 ---~x1=~x2--> ~x3~|" hyps x a shyps))
      ((er sconcl) (simplify-term concl (cons eq-hyp shyps) state))
      (- (cw? (debug-flag vl)
"~|PROPAGATE: ~x0 ---~x1=~x2--> ~x3~|" concl x a sconcl))
;TODO: this following check is causing problem in regression
; May 13 '12
      ;; ((when (or (pseudo-term-listp sconcl)))
;;                  ;(eq (ffn-symb sconcl) 'IF)))
;; ;IF is okay for an and in the conclusion. But will we ever get an IF from
;; ;inside test-checkpoint??
;;        (mv (prog2$ 
;;             (cw? (normal-output-flag vl)
;; "~|BAD: conclusion got reduced to something we dont want!!~|")
;;             T)
;;            (list shyps sconcl) state))
      (vars (all-vars-lst (cons sconcl shyps))))
  (assert$ (not (member-eq x vars)) (mv NIL (list shyps sconcl) state))))
                  

(defun put-val-A (name val dlist)
  (declare (xargs :guard (symbol-doublet-listp dlist)))
  (cond ((endp dlist) (list (list name val)))
        ((equal name (caar dlist))
         (cons (list name val) (cdr dlist)))
        (t (cons (car dlist)
                 (put-val-A name val (cdr dlist))))))





; a% represents the snapshot of the beginning of the dpll do-while loop
(defrec a% (;partial-A is the list of assigns made till now
            (hyps concl partial-A) ;args to simple-search
            (run-hist . gcs) ;accumulate in simple-search
            ((var . cs) val kind i . inconsistent?) 
;result of assign and propagate
            ) 
  NIL)
;Take special note of field names: run-hist and gcs, % is intentionally not
;used in these field names
(defun a%-p (v)
  (declare (xargs :guard T))
  (case-match v
    (('a% run-hist 
          (hyps concl partial-A) 
          (run-hist . gcs) 
          ((var . cs) val kind i . inconsistent?))

     ;==>
     (and (pseudo-term-listp hyps)
          (pseudo-termp concl)
          (symbol-doublet-listp partial-A)
          (symbolp var)
          (pseudo-termp val)
          (member-eq kind (list :na :implied :decision))
          (natp i)
          (booleanp inconsistent?)
          (cs%-p cs)
          (run-hist%-p run-hist)
          (gcs%-p gcs)))))
                                   
(defun a%-listp (v) ;STACK
  (declare (xargs :guard T))
  (if (atom v)
      (null v)
    (and (a%-p (car v))
         (a%-listp (cdr v)))))


; defabbrev was a BAD idea. I should make this a defun, to avoid variable
; capture bugs. For example I was assigning .. :var x ... instead of :var x1
; below, where x would have been the previously selected variable and unless I
; tested carefully I would not have gotten hold of this simple programming err.
; May 24th '12: making this into a defun
(def assign-propagate (x1 i a%
                          H C partial-A 
                          run-hist% gcs%
                          type-alist vl ctx wrld state)
  (decl :sig ((symbol fixnum (oneof a% NIL)
                      pseudo-term-list pseudo-term symbol-doublet-list
                      run-hist% gcs% 
                      symbol-alist fixnum symbol plist-world state)
              -> (mv erp a% state))
        :mode :program
        :doc "assign a value to x1 and propagate this new info to obtain new a%
if a% arg is NIL o.w obtain the updated a%")
;NOTE: When assigning, I ignore nconcl constraint. This might change.
  (b* ((vars (all-vars-lst (cons C H)))
       (cs% (if a% (access a% cs)
              (assert$ (member-eq x1 vars)
                       (cdr (assoc-eq x1 (collect-constraints% 
                                          H vars type-alist
                                          vl wrld))))))
;NOTE: I am not taking into account type constraint from nconcl at the moment.
       
       ((mv erp (list a kind i) state) (assign-value x1 i cs%
                                                   partial-A vl 
                                                   ctx wrld state))
       (a% (or a% ;if null, we should make a new record
               (acl2::make a% 
                           :hyps H :concl C 
                           :partial-A partial-A
                           :run-hist run-hist% :gcs gcs%
                           :inconsistent? erp :cs cs%
                           :var x1 :val a :kind kind :i i)))
       (- (and erp (cw? (normal-output-flag vl)
"~|Error: assign-value failed!")))
       ((mv erp (list H~ C~) state) (propagate x1 a H C vl state))
       (partial-A~  (put-val-A x1 a partial-A));bugfix
; partial-A is a symbol-doublet-listp
       (str (if erp 'ACL2::BAD 'ACL2::GOOD))
       (- (cw? (verbose-flag vl)
"~|Observation: Propagate assignment was ~x0.~|" str)))
; But do update i in a% always, and partial-A when consistent
   (if erp 
       (mv erp H~ C~ 
           (acl2::change a% a% :inconsistent? T :i i) 
           state)
     (mv erp H~ C~ 
         (acl2::change a% a%
                       :inconsistent? NIL
                       :partial-A partial-A~
                       :val a :i i)
         state))))

; concise function call in at least 3 diff functions
; But this still might be a bad idea, see the comment of (def assign-propagate )
(defabbrev assign-propagate... (x i a%) 
  (assign-propagate x i a%
                    H C partial-A
                    run-hist% gcs%
                    type-alist 
                    vl ctx wrld state))

;mutually tail-recursive incremental (dpll) search prodecure
(defs 
  (incremental-search (rem-vars. H C a% A. 
                                 name type-alist ;subgoal params
                                 N vl sm blimit programp
                                 ctx wrld state)

; INVARIANTS: 
; - rem-vars has at least one variable
; - i in record a% is <= blimit
; - a%.x is in rem-vars, only when we push a% into A., do we remove its x field
; from rem-vars
; - H and C are the result of x=a(a%) propagation
; - A. stores a list of consistent a% whose run-hist,gcs fields
;   contain the sigma whose values agree with partial-A for
;   the common variables
;   

; - a% stores the most recent select-assign-propagate result
;   It stores apart from x,a,kind,i and inconsistent?, the
;   snapshot of run-hist% and gcs% just before x was assigned 'a'
;   The run-hist and gcs fields are update to reflect the simple-search result
;   just before pushing a% in A.
;   a% holds H and C snapshots *before* x was assigned! partial-A though is
;   updated if we notice a consistent assignment x=a, i.e x=a is at the top of
;   the stack partial-A. if x=a was inconsistent, we dont put it in
;   partial-A. partial-A is this just an optimization, instead of recreating it
;   from A. I simply store the whole partial assignment in the top entry of A. itself.

; - rem-vars. is disjoint with vars of partial-A stored in top of A.
    (decl :sig (((and consp true-listp) 
                 pseudo-term-list pseudo-term a%-p a%-listp 
                 string symbol-alist
                 fixnump fixnump (in :random :be :hybrid) fixnump booleanp
                 symbolp plist-worldp state) -> 
                (mv erp (list boolean run-hist% gcs%) state))
        :mode :program
        :doc "DPLL like algorithm that searches for a non-vacuous assignment to
the form P (hyps /\ nconcl => nil).  This form returns (mv erp (list stop?
run-hist% gcs%) state).  The search consists of a Select, Assign, Propagate
loop.  Any inconsistency in P results in non-chronological backtracking to the
last decision made in Assign. For more details refer to the FMCAD paper.")

; here are abbreviations for functions with looooong arg lists
; dont read them, go directly to the body of the function, refer to these
; abbreviations while reading the main code.
; NOTE: f* names have defun local scope and not across defuns/clique :(

    (f* ((simple-search... () (simple-search name H C 
                                             (all-vars-lst (cons C H))
                                             (access a% partial-A)
                                             type-alist
                                             (access a% run-hist) 
                                             (access a% gcs)
                                             N vl sm programp 
                                             ctx wrld state))
         (backtrack... () (backtrack rem-vars. a% A.
                                     name type-alist
                                     N vl sm blimit programp
                                     ctx wrld state))
         
         (recurse... (H C) (incremental-search rem-vars. H C a% A.
                                               name type-alist
                                               N vl sm blimit programp
                                               ctx wrld state)))

    (if (endp (cdr rem-vars.))
; We have just one variable left in P, dont try anything fancy.
; bugfix May 25 '12: AND backtrack if you are inconsistent!!
        (if (access a% inconsistent?)
            (backtrack...)
        (simple-search...))

;      in
       (if (not (access a% inconsistent?))
           (b* (((mv erp (list stop? run-hist% gcs%) state)
                 (simple-search...))
                ((when (or erp stop?))
; if theres an error or if we reach stopping condition, simply give up search
                 (mv erp (list stop? run-hist% gcs%) state))
                ((mv x i) (mv (access a% var) (access a% i)))
                (partial-A (access a% partial-A))
                (- (cw? (verbose-flag vl)
"~|DPLL: Consistent assign to ~x0 whose i = ~x1~|" x i)) 

; keep in mind that we thread run-hist% and gcs% thru the assignments to a
; single variable. update them now. (Invariant 3)
                (a% (change a% run-hist run-hist%))
                (a% (change a% gcs gcs%))
                (rem-vars. (remove-eq x rem-vars.))
                (A.        (cons a% A.))
; ok lets set up variables for the next iteration
                (P         (cons (dumb-negate-lit C) H))
                (x1        (select P (debug-flag vl)))
; TODO: ignoring errors in assign/propagate fun
;BUGFIX May 24, stupid type bug. The order of a% was wrong below
                ((mv & H~ C~ a% state) (assign-propagate... x1 0 NIL)))
;           in
            (recurse... H~ C~))


;      ELSE inconsistent (i.e oops a contradiction found in hyps)
         
         (backtrack...)))))
           
 
; sibling procedure in clique
  (backtrack (rem-vars. a% A. name type-alist
                        N vl sm blimit programp
                        ctx wrld state)
;PREcondition: (or (eq kind :implied) (> i blimit))
    (decl :sig (((and consp true-listp) a%-p a%-listp 
                 string symbol-alist
                 fixnum fixnum (in :random :be :hybrid) fixnum boolean
                 symbol plist-world state) 
                -> (mv erp (list boolean run-hist% gcs%) state))
         :mode :program
         :doc "backtrack in dpll like search")
   
    (if (or (eq (access a% kind) :implied) 
            (> (access a% i) blimit)) ;then throw away this a%
        (if (null A.)
;       THEN - error out if x0 exceeds blimit
            (prog2$
             (cw? (verbose-flag vl)
"~|Incremental search failed to even satisfy the hypotheses.~|")
            (mv T (list NIL (access a% run-hist) (access a% gcs)) state))
;       ELSE
          (b* ((a% (car A.))
               (x (access a% var))
               (- (cw? (verbose-flag vl)
"~|DPLL: BACKTRACK to x = ~x0 whose i = ~x1~|" x (access a% i)))) 
           (backtrack (union-eq (list x) rem-vars.)
                      a% (cdr A.) 
                      name type-alist
                      N vl sm blimit programp
                      ctx wrld state)))

;     ELSE a% has a decision which has not reached its backtrack limit
; i.e  we have on our hands a variable assigned an inconsistent decision
; that fortunately has not exceeded its backtrack limit yet
      (b* ((`(a% ,LV & ((,x . &) & & ,i . &)) a%)
;ACHTUNG: a% defrec exposed
; H and C are the snapshot just before x was selected
; partial-A though is the last consistent partial sigma
           ((list H C partial-A) LV)
           ((mv run-hist% gcs%) (mv (access a% run-hist) (access a% gcs)))
           (- (cw? (verbose-flag vl)
"~|DPLL: Repeat assign propagate: x = ~x0 whose current i = ~x1~|" x i))
           ((mv & H~ C~ a% state) (assign-propagate... x i a%)))
       (incremental-search rem-vars. H~ C~ a% A. 
                           name type-alist
                           N vl sm blimit programp
                           ctx wrld state)))))

;;; The Main counterexample/witness generation function           
(def cts-wts-search (name H C type-alist elide-map
                          defaults programp 
                          ctx wrld state)
  (decl :sig ((string pseudo-term-list pseudo-term symbol-alist symbol-alist 
                      symbol-alist boolean
                      symbol plist-world state)
              -> (mv erp boolean state))
        :mode :program
        :doc 
"
* Synopsis       
  Interface to subgoal-level counterexample and witness
  search using either naive testing or incremental dpll
  style search for counterexamples.

* Input parameters
  - name :: name of subgoal or 'top if run from test?
  - H :: hyps - the list of terms constraining the cts and wts search
  - C :: conclusion
  - type-alist :: types inferred by ACL2 forward-chain
  - elide-map :: elide-map[v] = term for each elided variable v
  - defaults :: alist overiding the current acl2s-defaults
  - programp :: T when form has a program mode fun or we are in :program
                Its only use is for efficiency. We use guard-checking :none
                for programp = T and nil otherwise, which is more efficient.
  - ctx :: usually the top-level form which employed this procedure
  - wrld :: current acl2 world
  - state :: state

* Output signature 
  - (mv erp stop? state) where erp is the error tag which is non-nil
    when an error took place during evaluation of (search ...). 
    stop? is T if we should abort our search, i.e our stopping
    condition is satisfied (this value is given by run-tests), 
    otherwise stop? is NIL (by default). 

* What it does
  1. if form has no free variables exit with appropriate return val
  2. construct a new s-hist-entry% and call simple or incremental search
     depending on the search-strategy set in defaults.
  3. the resulting run-hist% (a field in s-hist-entry%), gcs% 
     are recorded in globals @gcs and @s-hist.
  4. return error triple containing stop? (described in simple-search)
")

  (f* ((update-cts-search-globals ()
         (b* ((s-hist-entry% (change s-hist-entry% run-hist run-hist%))
              ((mv end state) (acl2::read-run-time state))
              (s-hist-entry% (change s-hist-entry% end-time end))
              (s-hist (get-s-hist-global))
;note that name is a string so we use equal instead of eq in put-assoc
;put the pair (name . s-hist-entry%) in a list (looks like a stack)
              (s-hist (put-assoc-equal name s-hist-entry% s-hist))
              (state (put-s-hist-global s-hist))
              (state  (put-gcs%-global gcs%)))
          state)))
                  
  (b* ((N (get-acl2s-default 'num-trials defaults 0)) ;shudnt it be 100?
;Note: I dont need to provide the default arg 0 above, since we are
;sure the defaults alist we get is complete i.e it would definitely
;contain the key 'num-trials'. But I am envisioning a scenario, where
;I might call this function on its own and not via test?, then this
;functionality is useful for debugging.
       (vl (get-acl2s-default 'verbosity-level defaults 1))
       (sm (get-acl2s-default 'sampling-method defaults :random))
       (ss (get-acl2s-default 'search-strategy defaults :simple))
       (blimit (get-acl2s-default 'backtrack-limit defaults 2))
       ((mv start state) (acl2::read-run-time state))
       (form  `(implies (and ,@H) ,C)))
;  in
   (if (endp (all-vars-lst (cons C H)));(constant-value-expressionp form wrld)
       ;;dont even try trivial forms like constant expressions
       (b* (((mv erp c state)
             (trans-eval-single-value form ctx state))
            (s-hist-entry% (initial-s-hist-entry% name H C '()
                                                  type-alist elide-map start))
            (gcs% (get-gcs%-global))
            ((mv run-hist% gcs%)
             (record-testrun. (if c :witness :counterexample)
                              '() 
                              (access s-hist-entry% run-hist)
                              gcs%)))
;       in
        (prog2$
         (cw? (verbose-flag vl)
              "~%Stop searching ~x0; formula evaluates to a constant ~x1.~%"  
              name c)
         (let ((state (update-cts-search-globals)))
          (mv erp NIL state))))

;ELSE ATLEAST ONE VARIABLE
     (b* ((vars (vars-in-dependency-order H C vl wrld))
          (s-hist-entry% (initial-s-hist-entry% name H C vars 
                                                type-alist elide-map start))
          (run-hist% (access s-hist-entry% run-hist))
          (gcs% (get-gcs%-global))
          (partial-A '()))
;     in
      (case ss ;search strategy
        (:simple     (b* (((mv erp (list stop? run-hist% gcs%) state)
                           (simple-search name 
                                          H C vars partial-A
                                          type-alist
                                          run-hist% gcs% 
                                          N vl sm programp
                                          ctx wrld state))
                          (state (update-cts-search-globals)))
                      ;;in
                      (prog2$ 
                       (and erp
                            (cw? (normal-output-flag vl)
"~|Error occurred in simple-search.~|"))
                       (mv erp stop? state))))

        (:incremental (b* (((mv erp (list stop? run-hist% gcs%) state)
                            (if (endp (cdr vars))
;bugfix 21 May '12 - if only one var, call simple search
                                (simple-search name
                                               H C vars partial-A
                                               type-alist
                                               run-hist% gcs% 
                                               N vl sm programp
                                               ctx wrld state)
                          
                              (b* ((P  (cons (dumb-negate-lit C) H))
                                   (x0 (select P (debug-flag vl)))
                                   ((mv & H~ C~ a% state) 
                                    (assign-propagate... x0 0 NIL)))
;                              in
                               (incremental-search vars H~ C~ a% '()
                                                   name type-alist
                                                   N vl sm blimit programp
                                                   ctx wrld state))))
                           (state (update-cts-search-globals)))
                       (prog2$ 
                        (and erp
                             (cw? (normal-output-flag vl)
"~|Error occurred in incremental-search.~|"))
                        (mv erp stop? state))))
        (otherwise (prog2$ 
                    (cw? (normal-output-flag vl)
"~|Error in search: Only simple & incremental search strategy are available~|")
                    (mv T NIL state)))))))))

   
;;list comprehension syntax
;; (and (true-listp vs)
;;      (null |[x : x in vs :  (not (possible-defdata-type-p x))]|))
 
;NOTE 
#|(acl2::state-global-let*
                    ((acl2::inhibit-output-lst
                      ,(if (system-debug-flag vl)
                          ''(summary)
                        ;;shut everything except error
                        ''(warning warning! observation prove
                                  proof-checker event expansion
                                  proof-tree summary)))) 
                    
doesnt work on an make-event
|#


(defun test-gen-checkpoint ()
  (declare (xargs :mode :program))
  `(:computed-hint-replacement
     t
     :backtrack
     (cond
      ((eq acl2::processor 'acl2::generalize-clause)
       (er-let*
         ((res (test-gen-clause (car clause-list)
                            state)))
         (value (cond (res
                       '(:do-not '(acl2::generalize)
                         :no-thanks t))
                      (t nil)))))
      (t (value nil)))))

(defun initial-subseq-p (x y)
  (declare (xargs :guard (true-listp x)))
  (if (endp x)
      t
    (and (consp y)
         (equal (car x) (car y))
         (initial-subseq-p (cdr x) (cdr y)))))

(defun cl-id-ancestor (parent child)
  (declare (xargs :mode :program))
  (and (equal (acl2::access acl2::clause-id parent :forcing-round)
              (acl2::access acl2::clause-id child :forcing-round))
       (equal (acl2::access acl2::clause-id parent :pool-lst)
              (acl2::access acl2::clause-id child :pool-lst))
       (if (equal (acl2::access acl2::clause-id child :case-lst)
                  (acl2::access acl2::clause-id parent :case-lst))
           (or (null (acl2::access acl2::clause-id parent :primes))
               (and (acl2::access acl2::clause-id child :primes)
                    (< (acl2::access acl2::clause-id parent :primes)
                       (acl2::access acl2::clause-id child :primes))))
         (initial-subseq-p (acl2::access acl2::clause-id parent :case-lst)
                           (acl2::access acl2::clause-id child :case-lst)))))

        
#||    
; walk the table up to the parent and do intersection of the types
; to find the smallest type
; TODO - might be unsound - ASK Pete!
(defun walk-to-parent-and-collect-type-info
  (id goal-var-info-alst current-vars wrld ans)
  (declare (xargs :mode :program))
  (if (endp goal-var-info-alst)
;ENd of walk(Base case 1), dead code!
    ans
    (let* ((curr-entry (car goal-var-info-alst))
           (curr-id (car curr-entry)))
;(Base case 2)
;current subgoal is 'Top of "Goal", do intersection and return result
      (if (or
           ;;quickfix a possible bug in cl-id-ancestor 
           (equal curr-id (acl2::parse-clause-id "Goal"))
           ;;perhaps called from test? and thm? stop here              
           (equal curr-id 'Top))
        (let* ((var-info (cdr curr-entry)) 
               (vt-alst var-info))
          (union-vt-and ans vt-alst current-vars wrld))
;current subgoal is the closest ancestor, do intersection and return result
        (if (and (not (equal curr-id id))
                 (cl-id-ancestor curr-id id))
           ;is closest ancestor 
          (let* ((var-info (cdr curr-entry)) 
                 (vt-alst var-info))
            (union-vt-and ans vt-alst current-vars wrld))
;else Recursively walk up to the next ancestor
          (walk-to-parent-and-collect-type-info id 
                                                (cdr goal-var-info-alst)
                                                current-vars wrld ans))))))
||#

;-- 2 functions by Matt, to get elided variable replaced term information --
(defun get-dest-elim-replaced-terms (elim-sequence)
  (if (endp elim-sequence)
    nil
    (let* ((elt (car elim-sequence))
           (rhs (nth 1 elt))
           (lhs (nth 2 elt)))
      (cons (list rhs lhs)
            (get-dest-elim-replaced-terms (cdr elim-sequence))))))


(defun walk-to-ancestors-and-collect-replaced-terms (hist ans)
  (declare (xargs :mode :program))
  (if (endp hist)
    ans
    (b* ((H (car hist))
         (ttree (acl2::access acl2::history-entry H :ttree))
         (proc (acl2::access acl2::history-entry H :processor))
         ;(- (cw "DEBUG: proc is ~x0~%" proc))
         )
      (cond ((eq proc 'acl2::generalize-clause)
;Generalize
             (let ((ans1 
                    (list-up-lists 
                     (acl2::tagged-object 'acl2::terms ttree)
                     (acl2::tagged-object 'acl2::variables ttree))))
               (walk-to-ancestors-and-collect-replaced-terms 
                (cdr hist) (append ans1 ans))))
            ((eq proc 'acl2::eliminate-destructors-clause)
;Destructor elimination
             (let* ((elim-sequence 
                     (acl2::tagged-object 'acl2::elim-sequence ttree))
                    (ans1 (get-dest-elim-replaced-terms elim-sequence)))
               (walk-to-ancestors-and-collect-replaced-terms
                (cdr hist) (append ans1 ans))))
;Else (simplification and etc etc)
            (t (let* ((binding-lst 
                       (acl2::tagged-object 'acl2::binding-lst ttree))
                      (ans1 (convert-conspairs-to-listpairs binding-lst)))
                 (walk-to-ancestors-and-collect-replaced-terms
                  (cdr hist) (append ans1 ans))))))))
                 

;; The following 2 functions need to be revisited and rewritten if necessary
(defun let-binding->dep-graph-alst (vt-lst ans)
  "Walk down the var-term list vt-lst and add edges. 
   Build graph alist in ans"
  (if (endp vt-lst)
      ans
    (b* (((list var term) (car vt-lst))
         (fvars (get-free-vars1 term nil)));only non-buggy for terms
   
      (let-binding->dep-graph-alst 
       (cdr vt-lst)
       (union-entry-in-adj-list var fvars ans)))))


(defun do-let*-ordering (vt-lst debug-flag)
  (declare (xargs :guard (symbol-alistp vt-lst)
                  :mode :program))
  (b* ((vars (all-vars-in-var-term-alst vt-lst))
       (dep-g (let-binding->dep-graph-alst vt-lst 
                                           (make-empty-adj-list vars)))
       (sorted-vars (approximate-topological-sort dep-g debug-flag)))
    (get-ordered-alst (rev sorted-vars) vt-lst nil)))
#||
(do-let*-ordering '((X3 '+)
                    (W1 (CONS W W2))
                    (X (CONS X1 X2))
                    (X2 (CONS X3 X4))
                    (W2 (CONS W4 X3))
                    (Z (CONS Y X3))
                    (Y (CONS X X3))
                    (W (CONS Z Y))) 
                  nil)
||#



;; COPIED FROM acl2-sources/basis.lisp line 12607
;; because it is program mode there, and verify-termination needed more effort
;; than I could spare.
(defun dumb-negate-lit-lst (lst)
  (cond ((endp lst) nil)
        (t (cons (dumb-negate-lit (car lst))
                 (dumb-negate-lit-lst (cdr lst))))))

(def clause-mv-hyps-concl (cl)
  (decl :sig ((clause) 
              -> (mv pseudo-term-list pseudo-term))
        :doc "return (mv hyps concl) which are proper terms given a
  clause cl. Adapted from prettyify-clause2 in other-processes.lisp")
  (cond ((null cl) (mv '() ''NIL))
        ((null (cdr cl)) (mv '() (car cl)))
        ((null (cddr cl)) (mv (list (dumb-negate-lit (car cl)))
                              (cadr cl)))
        (t (mv (dumb-negate-lit-lst (butlast cl 1))
               (car (last cl))))))

(set-verify-guards-eagerness 0)
(verify-termination acl2::subcor-var1)      
(verify-termination subcor-var)

;expand-lambda : pseudo-termp -> pseudo-termp (without lambdas)
(mutual-recursion
 (defun expand-lambda (term)
   (declare (xargs :guard (pseudo-termp term)))
   (cond ((variablep term) term)
         ((fquotep term) term)
         ((eq (ffn-symb term) 'hide) term)
         (t
          (let* ((expanded-args (expand-lambda-lst (fargs term)))
                 (fn (ffn-symb term)))
               
            (cond ((flambdap fn) ;get rid of the lambda application
                   (subcor-var (lambda-formals fn)
                               expanded-args 
                               (expand-lambda (lambda-body fn))))
                    
                  (t (acl2::cons-term fn expanded-args)))))))

(defun expand-lambda-lst (term-lst)
  (declare (xargs :guard (pseudo-term-listp term-lst)))
  (cond ((endp term-lst) '())
        (t (cons (expand-lambda (car term-lst))
                 (expand-lambda-lst (cdr term-lst))))))

 )

(set-verify-guards-eagerness 2)
(defun print-summary-user-testing (state)
  (declare (xargs :stobjs state))

  (and 
       (b* ((ctx 'print-summary-user)
            ((unless (and (f-boundp-global 'print-summary-user-flag state)
                          (@ print-summary-user-flag)))
             nil)
            (?er-str "~|BAD global-coverage-stats. ~
Please report to ACL2s maintainer the context in which this happened!~|")
            ((unless (f-boundp-global 'gcs% state))
             nil)
            (gcs% (get-gcs%-global))
            ((unless (gcs%-p gcs%))
             nil)
            (num-wts (access gcs% wts))
            (num-cts (access gcs% cts))
            (- (cw? T;(normal-output-flag)
                    "~|ACL2s found ~x0 counterexamples and ~x1 witnesses. For more details, call (print-testing-summary).~|"
                    num-cts num-wts)))
        nil)))

(set-verify-guards-eagerness 1)                      
                      


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
(defun get-top-level-assignment (A top-vars top-cl 
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

       ((mv ?er res state) 
        (acl2::state-global-let*
         ((acl2::guard-checking-on :none))
         (trans-eval
          `(let* ,A
             (declare (ignorable ,@(strip-cars A)))
             (list ,top-cl
; make list/let A (list `(var ,var) ...) 
                   ,(make-var-value-list-bindings top-vars nil)))
          'get-top-level-assignment state nil)))
       ((list form-eval-res top-A) (cdr res)))

;  in
   (if (or (and counteregp (not form-eval-res)) 
;check if its really a counter-example or really a witness
           (and (not counteregp) form-eval-res)) 
       (value (list t top-A))
;only return A if its a true counterexample/witness
     (value (list nil top-A)))));nil means inconsistent top-level A

;; Print the random instantiations for a particular test run.
;; Return value is a dummy error-triple. 
;; This function is called for side-effect only(printing IO)
;; Binding == (var val) 
;; added a flag wether bindings are for a counter-example or not
;; Sep 5th 2011 - removed state, and use cw?
;; April 30 2012 - put back state!
(defun print-assignment (A top-vars top-cl elided-var-map
                           vl counteregp state)
  (declare (xargs :stobjs (state)
                  :guard (and (symbol-doublet-listp A)
                              (consp (car A))
                              (symbol-alistp elided-var-map)
                              (symbol-listp top-vars)
                              (booleanp counteregp))))
                              
;the usual, but filter the variables that are in the original output clause
  (b* ((top-A (filter-alist-keys A top-vars))
       ((unless elided-var-map) ;the simple case
        (value (cw? (normal-output-flag vl)
                    "~| -- ~&0~%" top-A)))
  
;show top goal, show counterexamples and witness in 
;terms of the original free variables(of the top clause)
       ((er (list consistent? top-A))
        (get-top-level-assignment A top-vars top-cl 
                                  elided-var-map counteregp state))

       ((when consistent?)
        (value (cw? (normal-output-flag vl)
                    "~| -- ~&0~%"  top-A))))
    (if counteregp
        (progn$
         (cw? (normal-output-flag vl)
              "~| -- ~&0~%"  top-A)
         (cw? (normal-output-flag vl)
"~|WARNING: The above counterexample is not consistent with top-level form. ~
 This is most likely due to the application of an elim rule that generalized ~
 its parent goal. If that is not what happened, then please report this ~
 example to ACL2s authors.~%")
         (value nil))
      (progn$
       (cw? (normal-output-flag vl)
            "~| -- ~&0~%"  top-A)
       (cw? (normal-output-flag vl)
"~|NOTE: The above witness is not consistent with the top-level form. ~
 Witnesses are only guaranteed to be consistent with subgoals.~%")
       (value nil))
       )))

(defun naive-print-bindings (bindings orig-vars verbosity-level)
  (declare (xargs :guard (and (symbol-doublet-listp bindings)
                              (symbol-listp orig-vars)
                              (natp verbosity-level)
                              (implies (consp bindings)
                                       (and (consp (car bindings))
                                            (symbolp (caar bindings)))))))
;the usual, but filter the variables that are in the original output clause
  (b* ((out-bindings (acl2::restrict-alist orig-vars bindings ))
       (vl verbosity-level))
      (cw? (normal-output-flag vl)
             "~| -- ~&0~%" out-bindings)))
  


;added a flag indicating wether we are printing counterexamples or witnesses
(defun print-assignments (A-lst top-vars top-cl 
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
      (print-assignment (car A-lst) top-vars top-cl
                        elided-var-map vl counteregp state)
; (naive-print-bindings (convert-conspairs-to-listpairs (car bindings-lst))
;                       orig-vars vl)
      (print-assignments (cdr A-lst) top-vars top-cl
                          elided-var-map vl counteregp state))))
(logic)



(def print-cts/wts (s-hist cts-p top-vars top-form vl state)
  (decl :mode :program
        :sig ((s-hist-p booleanp symbol-listp all natp state) 
              -> (mv erp all state))
        :doc "print all cts/wts A (sigma) in s-hist subgoal testing
        history alist")
  (if (endp s-hist)
      (value nil)
    (b* (((cons name s-hist-entry%) (car s-hist))
         (run-hist% (access s-hist-entry% run-hist))
         (A-lst (if cts-p 
                    (access run-hist% cts)
                  (access run-hist% wts)))
         (elide-map (access s-hist-entry% elide-map)))
     (if (endp A-lst) ;none found
         (print-cts/wts (cdr s-hist) cts-p top-vars top-form vl state)
       (er-progn
        (value (cw? (normal-output-flag vl) "~| [found in : ~x0]~%" name))
        (value (cw? (debug-flag vl) 
"~| A-lst:~x0 top-vars:~x1 elide-map:~x2~|" A-lst top-vars elide-map))
        (print-assignments A-lst top-vars top-form 
                           elide-map vl cts-p state)
        (print-cts/wts (cdr s-hist) cts-p top-vars top-form vl state))))))


;; precondition: s-hist shud at least contain an entry of "top"
(def print-s-hist (s-hist num-cts num-wts vl state)
  (decl :mode :program
        :sig ((s-hist-p natp natp natp state) -> (mv erp all state))
        :doc "print counterexample and witnesses recorded in testing subgoal
history s-hist.")
  (b* (((cons & s-hist-entry%) (assoc-equal "top" s-hist))
;replaceing & with "top" gives error. '"top" is fine
       (top-vars (access s-hist-entry% vars))
       (top-form `(implies (and ,@(access s-hist-entry% hyps)) 
                          ,(access s-hist-entry% concl)))
       
       ((er &) (if (> num-cts 0)
                   (prog2$
                    (cw? (normal-output-flag vl)
"~|~%We falsified the conjecture. Here are counterexamples:~|")
                    (print-cts/wts s-hist T top-vars top-form vl state))
                 (value nil)))

       ((er &) (if (> num-wts 0)
                   (prog2$
                    (cw? (normal-output-flag vl)
"~|~%Cases in which the conjecture is true include:~|")
                    (print-cts/wts s-hist NIL top-vars top-form vl state))
                 (value nil))))
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
      
  
(defmacro acl2::print-testing-summary ()
  "prints the last test?/thm's testing summary"
  `(er-progn
    (assign print-summary-user-flag NIL) ;reset, especially important for
      ;thm/defthm forms where I have no POST control
    (print-testing-summary-fn (acl2s-defaults :get verbosity-level) 
                              state)))

(defun print-testing-summary-fn (vl state)
  (declare (xargs :mode :program
                  :stobjs (state)))
  (b* ((ctx 'print-testing-summary)
       (s-hist (get-s-hist-global))
       ((unless (and (consp s-hist) (consp (car s-hist))
                     (equal "top" (caar s-hist))))
        (value (cw? (normal-output-flag vl) "~|BAD s-hist found in globals")))
                  
       (num-subgoals (len s-hist))
       (gcs%   (get-gcs%-global))
       (- (cw? (debug-flag vl) "~|testing summary - gcs% = ~x0~%" gcs%))
       (- (cw? (debug-flag vl) "~|testing summary - s-hist = ~x0~%" s-hist))
       )
   (case-match gcs%
     (('gcs% (total dups . vacs) (num-cts . num-wts) (& . &) (start . end) &)
;ACHTUNG: gcs% defrec exposed
      (b* ((uniq-runs  (my+ num-wts num-cts))
           (sat-runs (my- total (my+ vacs dups)))
           (delta-t-total (my- end start))
           (delta-testing-t-total (total-time-spent-in-testing s-hist))
           (-  (cw? (normal-output-flag vl) 
                "~%~%**Summary of testing**~%"))
           (- (cw? (normal-output-flag vl)
               "~|We tried ~x0 test runs across ~x1 subgoals, of which ~x2 (~x3 unique) satisfied the hypotheses, and found ~x4 counterexamples and ~x5 witnesses.~%"
               total num-subgoals sat-runs uniq-runs num-cts num-wts))
           (- (cw? (normal-output-flag vl)
               "~|Total time taken (incl. prover time) = ~x0 ~
                ~|Time taken by testing = ~x1 ~|"
               delta-t-total
               delta-testing-t-total))
           ((er &)  (print-s-hist s-hist num-cts num-wts vl state)))
       (value nil)))
     (& (value (cw? (normal-output-flag vl) "~|BAD gcs% found in globals"))))))

;----------------------------------------------------------------
;                         PRINT end                             |
;----------------------------------------------------------------



;; The following function implements a callback function (computed hint)
;; which calls the counterexample generation testing code. Thus the
;; the so called "automated" combination of testing and theorem proving
;; is enabled naturally by the computed hints feature in the
;; engineering design of ACL2 theorem prover.
;; If somebody reads this comment, I would be very interested in any other
;; theorem-provers having a call-back mechanism in their implementation.
(defun acl2::test-checkpoint (id cl processor pspv hist state)
  (declare (xargs :stobjs (state)
                  :mode :program
                  :guard (consp pspv)))
;; ASK MATT, why is pspv an irrelevant formal!

;;   (decl :sig ((symbol clause symbol any any state) -> (mv erp boolean state))
;;         :mode :program
;;         :doc
;; "?:
;; This function uses override hint + backtrack hint combination.
;; On the top-level GOAL it initializes gcs% and s-hist. On SUBGOALS 
;; that are not checkpoints does no-op. On checkpoints it calls the 
;; cts/wts/search procedure.
;; ")
; RETURN either (mv t nil state) or (mv nil nil state) 
; PRECONDITION -
; INVARIANT - no new prove call is made during the computation of this
; function (this is very important)

  (b* ((ctx 'acl2::test-checkpoint)
;TODObug: test? defaults should be the one to be used
       (vl (acl2s-defaults :get verbosity-level)) 
       ((mv hyps concl) (clause-mv-hyps-concl cl))
       (- (cw? (debug-flag vl)
"test-checkpoint: id=~x0 and processor=~x1~ hyps=~x2 concl=~x3 ~|" 
id processor hyps concl))
 
       ((when (null hist)) ;thanks to Matt! (earlier code was buggy)
;Top Goal (The beginning of waterfall)
        (b* (((when (acl2::function-symbolp 'inside-test? (w state)))
              (value nil));dont overwrite initial work by test? top
             
             (- (cw? (debug-flag vl) 
"~|Initialising gcs% and s-hist in test-checkpoint for Goal.~|"))
             ((mv start state) (acl2::read-run-time state))
             (gcs% (initial-gcs% (acl2s-defaults :get num-counterexamples)
                                 (acl2s-defaults :get num-witnesses)
                                 start (cons hyps concl)))
             (state (put-gcs%-global gcs%))
             )
         (er-progn
;"top" and "Goal" are names of the same top-level goal
;TODO: Not recording top-level type information. But I probably dont
;have to do it here, since later on, we can walk the HIST and obtain
;it
          (assign print-summary-user-flag NIL) ;reset
          (assign s-hist 
                  (acons "top" 
                        (b* ((vars (all-vars-lst cl))) ;CHECK
                         (initial-s-hist-entry% "top" hyps concl vars 
                                                '() '() start))
                        '()))
          (value nil))))

       ((unless (member-eq processor
                           '(;acl2::preprocess-clause
                             ;;acl2::simplify-clause
                             acl2::settled-down-clause 
                             acl2::eliminate-destructors-clause
                             acl2::fertilize-clause
                             acl2::generalize-clause
                             acl2::eliminate-irrelevance-clause
                             acl2::push-clause)))  
        (value nil));ignore backtrack hint
       
       
       (ens (acl2::access acl2::rewrite-constant
                          (acl2::access 
                           acl2::prove-spec-var pspv :rewrite-constant)
                          :current-enabled-structure))
       
;Use forward-chain ACL2 system function to build the context
;This context, gives us the type-alist ACL2 inferred from the
;the current subgoal i.e. cl
       (wrld (w state))
       
       ((mv & type-alist &)
        (acl2::forward-chain cl
                             (acl2::enumerate-elements cl 0)
                             nil ; do not force
                             nil ; do-not-reconsiderp
                             (w state)
                             ens
                             (acl2::match-free-override wrld)
                             state))
       ((mv hyps concl) (clause-mv-hyps-concl cl))
       
       (name (acl2::string-for-tilde-@-clause-id-phrase id))
       (elided-var-map (walk-to-ancestors-and-collect-replaced-terms hist nil))
       ;; Ordering is necessary to avoid errors in printing top-level cts
     
       (ord-elide-map (do-let*-ordering elided-var-map (debug-flag vl)))
       (vt-acl2-alst  (acl2::get-var-types-from-type-alist 
                       type-alist (all-vars-lst cl)))
       (- (cw? (debug-flag vl) "~|ACL2 type-alist: ~x0~|" vt-acl2-alst))
       
       ((mv ?erp stop? state) (cts-wts-search name hyps concl 
                                              vt-acl2-alst ord-elide-map
                                              (acl2s-defaults-alist) 
                                              NIL ctx wrld state)))
   
;  in  
   (if stop?
       (er-progn
        (if (acl2::function-symbolp 'inside-test? (w state))
            (value nil)
          (print-testing-summary-fn vl state))
        (assign print-summary-user-flag T) ;only for use in print-summary-user
        (mv t nil state))
;ignore errors in cts search function
     (mv nil nil state))))


;Dont print the "Thanks" message:
(defmacro dont-print-thanks-message-override-hint ()
`(make-event  
  '(acl2::add-override-hints 
    '((cond ((or (null acl2::keyword-alist)
                 (assoc-keyword :no-thanks acl2::keyword-alist))
             acl2::keyword-alist)
            (t
             (append '(:no-thanks t) acl2::keyword-alist)))))))
       

;The following 2 function only look at the outermost implies form
;get hypothesis from acl2 term being proved.
(defun get-hyp (form)
  (declare (xargs :guard t))
  (if (atom form)
    t;no hyps is equivalent to true
    (if (and (consp (cdr form))
             (eq 'implies (first form)))
      (second form)
      t)));;no hyps is equivalent to true

(defun get-hyps (pform)
  (declare (xargs :guard t))
  (b* ((hyp (get-hyp pform))
       ((when (eq hyp 't)) nil)
       ((unless (and (consp hyp)
                     (consp (cdr hyp))
                     (eq (car hyp) 'and)))
        (list hyp))
       (rst (cdr hyp)))
    rst))


;get conclusion from acl2 term being proved
(defun get-concl (form)
  (declare (xargs :guard t))
  (if (atom form)
    form
    (if (and (consp (cdr form))
             (consp (cddr form))
             (eq 'implies (first form)))
      (third form)
      form)))

     
;Note on xdoc: <= or < cannot be used inside defxdoc!!

(def test?-fn (form hints override-defaults ctx wrld state)
  (decl :mode :program
        :sig ((any true-list symbol-alist symbol plist-world state) 
              -> (mv erp any state))
        :doc "gives an error triple wrapping a form that will be ... ")
  (f* ((check-syntax   (form logicp) (acl2::translate form  T logicp T 
                                                        "test? check" 
                                                        wrld state)))
  (b* ((defaults (acl2s-defaults-alist override-defaults))
       (testing-enabled   (get-acl2s-default 'testing-enabled defaults))
       (vl                (get-acl2s-default 'verbosity-level defaults))
       ((when (eq testing-enabled NIL)) ;dont do any testing
        (value '(value-triple :invisible))))
       
  (acl2::state-global-let*
   ((acl2::inhibit-output-lst 
     (if (system-debug-flag vl)
         '(summary)
       acl2::*valid-output-names*)))
   
  (b* (((mv erp term state) (check-syntax form NIL))
       ((when erp)          (prog2$
                             (cw? (normal-output-flag vl) 
"~|TEST?: The input form is ill-formed, see below:~%")
;show error to user which was invisble earlier
                             (acl2::state-global-let*
                              ((acl2::inhibit-output-lst '(summary)))
                              (acl2::translate form  T NIL T 
                                               "test? check" 
                                               (w state) state))))
                             
               
; No syntax error in input form, check for program-mode fns
; Note: translate gives nil as the term if form has
; a program-mode function, so we ignore it
       ((mv pm? & state)    (check-syntax form T))
       
       (programp            (or pm?
                                (eq (default-defun-mode (w state)) 
                                    :program)))

       ;; get rid of lambdas i.e let/let*
       (term  (expand-lambda term))
       (pform (acl2::prettyify-clause (list term) nil wrld))
    
       ((mv phyps pconcl)  (mv (get-hyps pform) (get-concl pform)))
    
       ((er hyps) (acl2::translate-term-lst phyps 
                                            t nil t "test?" wrld state)) 
       ((er concl) (acl2::translate pconcl t nil t "test?" wrld state))
; initialize these per test?/thm/defthm globals that store information
; across subgoals in a single thm event
       ((mv start-top state) (acl2::read-run-time state))
       (gcs%  (initial-gcs% 
               (get-acl2s-default 'num-counterexamples defaults)
               (get-acl2s-default 'num-witnesses defaults)
               start-top (cons hyps concl)))
       (state (put-gcs%-global gcs%))
       (state (put-s-hist-global '()))
       ((er &) (assign print-summary-user-flag NIL)) ;reset
       ((mv & type-alist &)
        (if programp (mv nil '() nil)
          (acl2::forward-chain (list term);cl CHECK with Matt!
                               (acl2::enumerate-elements (list term) 0)
                               nil ; do not force
                               nil ; do-not-reconsiderp
                               wrld (acl2::ens state)
                               (acl2::match-free-override wrld)
                               state)))
       (vt-acl2-alst (and type-alist
                          (acl2::get-var-types-from-type-alist 
                           type-alist (all-vars term))))
                                                      
       (- (cw? (and (not programp)
                    (debug-flag vl))
 "~|ACL2 type-alist for TOP : ~x0~|" vt-acl2-alst))
       ((mv erp ?stop? state) (cts-wts-search "top" hyps concl 
                                              vt-acl2-alst '() 
                                              defaults programp
                                              ctx wrld state))
              
; abort b* if top-level-test? failed
; or  if form contains a program-mode function
; or if test? is called in program-mode
       (abortp  (or erp stop? programp (eq testing-enabled :naive)))
      
; TODO: print something if erp is true i.e error in testing
            
; Else call ACL2 prover with a hint
; that does random testing on every checkpoint.
       (- (cw? (system-debug-flag vl) "~|abortp = ~x0~%" abortp))
       ((mv erp & state)
          (if abortp ;if above flag is true dont take theorem prover's help
              (mv T '? state) ;TODO: I am throwing information here!
            (er-progn
             ;; dummy world event to recognize we are inside test?
             (acl2::defun-fn '(inside-test? nil t)
               state '(defun inside-test? nil t))
             (acl2::thm-fn form state
                           (or hints 
;user-specified hints override default hints
                              '(("Goal"
                                 :do-not-induct t 
                                 :do-not '(acl2::generalize 
                                           acl2::fertilize))))
;TODO: Matt's code doesnt work through induction and forcing rds
;Also the OTF flag is set to true, to test all initial subgoals. 
                          t nil))))

; TODO: errors in print functions will abort the whole form
       ((mv end state) (acl2::read-run-time state))
       (gcs%  (get-gcs%-global))
       (gcs% (change gcs% end-time end))
       (state (put-gcs%-global gcs%))
       ((er &) (print-testing-summary-fn vl state))
       ((mv erp state )      
; If testing found a counterexample, print so and abort.
        (b* ((gcs% (get-gcs%-global))
             (num-cts (access gcs% cts)))
            (cond ((posp num-cts) 
                   (prog2$
                    (cw? (normal-output-flag vl)
"Test? found a counterexample.~%")
                    (mv T state)))
;If we had didnt do thm+testing, then we had to abort after top-level
;testing, but we dont have a counterexample, so we simply exit with no error
                  (erp 
                   (prog2$
                    (cw? (normal-output-flag vl)
"Test? succeeded. No counterexamples were found.~%")
                    (mv NIL state)))
;Success means the prover actually proved form is a theorem.
                  (t 
                   (prog2$
                    (cw? (normal-output-flag vl)
"Test? proved the conjecture under consideration (without induction). ~
 Therefore, no counterexamples exist. ~%" nil )
                    (mv NIL state)))))))
   
   (mv erp '(value-triple :invisible) state ))))))

(defxdoc test?
  :parents (ACL2::TESTING)
  :short "Random testing using the ACL2 prover,
  generating counterexamples to original conjecture."
  :long "<tt>test?</tt> is a powerful random testing facility intended
  to be used to increase confidence in the truth of a conjecture by
  providing extensive testing in cases where there is not enough time
  or resources for formal proofs.
  
  <tt>test?</tt> combines random testing with the power of ACL2 and
  our data definition framework. It guarantees than any
  counterexamples generated are truly counterexamples to the original
  conjecture. A counterexample is just a binding that maps the
  variables in the original conjecture to values in the ACL2
  universe. In cases where the value of variables are irrelevant, we
  bind the variables to the symbol <tt>?</tt> : these bindings still
  provide counterexamples, but should raise alarms, since chances are
  that there is a specification error.
  
  If no counterexample is found, there are three possibilities. First,
  it possible that the conjecture is false, in which case increasing
  the amount of testing we do may lead to the discovery of a
  counterexample.  Second, it is also possible that ACL2 proves that
  the conjecture is true, in which case we print a message reporting
  success.  Finally, the conjecture may be true, but ACL2 cannot prove
  it.  For all of these three cases, we consider testing to have
  succeeded, so test? will report success.
  
  We note that in order to be able to generate counterexamples, we do
  not allow ACL2 to use any of the following processes: induction,
  generalization, and cross-fertilization. We do allow destructor-
  elimination, though in rare cases, user defined elim rules may
  generalize the conjecture. Such situations are recognized.  If you
  want to enable the above processes, use thm or thm? instead, but
  note that counterexamples are now only for the subgoal in question,
  not for the original conjecture.

    
  <code>
  Examples:
  (test? (implies (and (posp (car x))
                     (posp (cdr x)))
                (= (cdr x) (len x))))

  </code>
 
  Note is both these examples, counterexamples are generated for the
  original goal, in case some variables are elided away(like y and by
  equality z), we show <tt>?</tt> as their instantiated values.

  <code>
  (test? (implies (and (posp (car x))
                     (equal y y)
                     (equal z y)
                     (posp (cdr x)))
                (= (cdr x) (len x))))
  
  Usage:
  (test? form)
  </code>"
 )

(defattach (acl2::print-summary-user 
            print-summary-user-testing))

(defmacro test? (form &key hints override-defaults)
  `(with-output
     :stack :push
     :off :all
     :gag-mode T
     (make-event
      (test?-fn ',form ',hints 
                ',override-defaults
                'test? (w state) state))))#|ACL2s-ToDo-Line|#

   
;Lets start with the canonical rev-rev example!
;Does Reverse of Reverse give back the original.Is it a Theorem?
;; (trace$ cts-wts-search)

;; (include-book "acl2s-parameter")
;; (acl2s-defaults :set verbosity-level 5)
;; (acl2s-defaults :set acl2::testing-enabled t)
;; (defttag t)
;; (defthm ok (equal (rev (rev x)) x))

;; (test? (equal (rev (rev x)) x) :override-defaults ((testing-enabled . T)))

;;  USAGE and EXAMPLES
;; (set-acl2s-random-testing-enabled t)

;; ;no slow array warning if inline-book base, but gives warning otherwise(FIXED)
;; (union-vt-and '((x pos nat) (y all))
;;               '((x rational) (y symbol boolean))
;;               (w state))


;; ;TODO:limit test runs when all cases are exhausted for finite data values
;; (test?
;;  (implies (and (booleanp a) 
;;                (booleanp b))
;;           (equal (implies a b) (or (not a) b)))


;; TODO: 
;; 1. union-find algo in per variable counterexample store,
;;    increasing probability of finding countereg.
;; 2. a proof obligation testing type consistency is missing in register-type
;; 3. what about intersection (and) of types/acl2-subsets?
;; 5. Registered constructors - check if destructor arguments are
;;     subtypes of dex-prex.
;; 6. IMP: Analyse efficiency of union-vt-and, see if it can be faster,
;;     although it shudnt matter as num of free-vars is normally small!
