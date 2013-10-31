#|$ACL2s-Preamble$;
;;Author - Harsh Raju Chamarthi (harshrc)
(ld ;; Newline to fool ACL2/cert.pl dependency scanner
 "portcullis.lsp")
(begin-book t :ttags :all);$ACL2s-Preamble$|#


(in-package "DEFDATA")

;Useful Macros for concise/convenient code.
(include-book "tools/bstar" :dir :system)
(include-book "basis")
(include-book "with-timeout" :ttags ((:acl2s-timeout)))
(include-book "type")
;(include-book "basis")
;(include-book "testing-stobj")
;; (include-book "base")
(include-book "acl2s-parameter")
(include-book "simple-graph-array")
(include-book "graph-tc" :ttags ((:hash-stobjs) (:redef+)));transtive closure and subtype relation
(include-book "random-state")
;(include-book "tools/easy-simplify" :dir :system)
(include-book "misc/expander" :dir :system)
(include-book "elim")

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
     


;; chose 29 bits, because ACL2 uses signed 29 bits in its code!
(defun unsigned-29bits-p (x)
  (declare (xargs :guard T))
  (acl2::unsigned-byte-p 29 x))

(defun fixnump (x)
  (declare (xargs :guard T))
  (unsigned-29bits-p x))

;;; Style of accessing/changing defrec objects. The name of the object is
;;; always same as the name of the defrec, just like in stobjs. THis way we
;;; can drop in stobjs in their place!
(defmacro access (r a)
  `(acl2::access ,r ,r ,(intern-in-package-of-symbol (symbol-name a) :key)))
(defmacro change (r a val )
  `(acl2::change ,r ,r ,(intern-in-package-of-symbol (symbol-name a) :key) ,val))


(defrec enum-info% (size category expr expr2) NIL)
(defun enum-info%-p (v)
  (declare (xargs :guard T))
  (case-match v
    (('enum-info% size category expr expr2) 

     (and (fixnump size)
          (member-eq category
                     '(:singleton :function :defconst :numeric-range :empty))
          (pseudo-termp expr)
          (pseudo-termp expr2)))))


;redundant from data.lisp
(defrec types-info%
  (size enumerator predicate test-enumerator enum-uniform
        recursivep derivedp
        type-class defs) NIL)

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
          


  

(def make-range-enum-info% (domain interval)
  (decl :sig ((symbolp non-empty-non-universal-interval-p) -> enum-info%-p)
        :doc "given tau-interval interval construct an enum-info% rec with appropriate enum calls")
  (b* ((lo (acl2::access acl2::tau-interval interval :lo))
       (hi (acl2::access acl2::tau-interval interval :hi))
       (lo-rel (acl2::access acl2::tau-interval interval :lo-rel))
       (hi-rel (acl2::access acl2::tau-interval interval :hi-rel)))
       
  (case domain
    (acl2::integer (let ((lo (and lo (if lo-rel (1+ lo) lo))) ;make both inclusive bounds
                         (hi (and hi (if hi-rel (1- hi) hi))))
                     (cond ((and lo hi)
                            (acl2::make enum-info% 
                                        :size 't ;(- hi lo)
                                        :category :numeric-range 
                                        :expr `(acl2::nth-integer-between r ,lo ,hi)
                                        :expr2 `(random-int-between-seed ,lo ,hi seed.)))
                           (lo ;hi is positive infinity
                            (acl2::make enum-info% 
                                        :size 't
                                        :category :numeric-range 
                                        :expr `(+ ,lo r)
                                        :expr2 `(mv-let (r seed.)
                                                        (random-natural-seed seed.)
                                                        (mv (+ ,lo r) seed.))))
                           
                           ((posp hi) ;lo is neg infinity and hi is >=1
                            (acl2::make enum-info% 
                                        :size 't
                                        :category :numeric-range 
                                        :expr `(let ((i-ans (acl2::nth-integer r)))
                                                 (if (> i-ans ,hi)
                                                     (mod i-ans (1+ ,hi))
                                                   i-ans));ans shud be less than or equal to hi
                                                        
                                        :expr2 `(mv-let (i-ans seed.)
                                                        (random-integer-seed seed.)
                                                        (mv (if (> i-ans ,hi) 
                                                                (mod i-ans (1+ ,hi)) 
                                                              i-ans) 
                                                            seed.))))
                           (t ;lo is neg inf, and hi is <= 0
                            (acl2::make enum-info% 
                                        :size 't
                                        :category :numeric-range 
                                        :expr `(- ,hi r) ;ans shud be less than or equal to hi
                                        :expr2 `(mv-let (r seed.)
                                                        (random-natural-seed seed.)
                                                        (mv (- ,hi r) seed.)))))))
    (otherwise  (cond ((and lo hi) ;ASSUME inclusive even when you have exclusive bounds
                            (acl2::make enum-info% 
                                        :size 't ;(- hi lo)
                                        :category :numeric-range 
                                        :expr `(acl2::nth-rational-between r ,lo ,hi)
                                        :expr2 `(random-rational-between-seed ,lo ,hi seed.)))
                         (lo ;hi is positive infinity
                          (acl2::make enum-info% 
                                      :size 't
                                      :category :numeric-range 
                                      :expr `(+ ,lo (acl2::nth-positive-rational r))
                                      :expr2 `(mv-let (p seed.)
                                                      (random-probability-seed seed.)
                                                      (mv-let (r seed.)
                                                              (random-natural-seed seed.)
                                                              (mv (+ ,lo (* p r)) seed.)))))
                         
                         ((> hi 0) ;lo is neg infinity and hi is is >= 1
                          (acl2::make enum-info% 
                                        :size 't
                                        :category :numeric-range 
                                        :expr `(let ((rat-ans (acl2::nth-rational r)))
                                                 (if (> rat-ans ,hi)
                                                     (mod rat-ans (1+ ,hi))
                                                   rat-ans));ans shud be less than or equal to hi
                                                        
                                        :expr2 `(mv-let (p seed.)
                                                        (random-probability-seed seed.)
                                                        (mv-let (r seed.)
                                                                (random-integer-seed seed.)
                                                                (let ((rat-ans (* p r)))
                                                                  (mv (if (> rat-ans ,hi) 
                                                                          (mod rat-ans (1+ ,hi)) 
                                                                        rat-ans) 
                                                                      seed.))))))

                         (t;lo is neg infinity and hi is is <= 0
                          (acl2::make enum-info% 
                                      :size 't
                                      :category :numeric-range 
                                      :expr `(- ,hi (acl2::nth-positive-rational r))
                                      :expr2 `(mv-let (p seed.)
                                                      (random-probability-seed seed.)
                                                      (mv-let (r seed.)
                                                              (random-natural-seed seed.)
                                                      (mv (- ,hi (* p r)) seed.))))))))))
                   
                          
                         
  
;usage:

;OLD COMMENT as of 10 March 2012;
;MODIFIED: I had to change the order because it was picking
;up *empty-values* as a constant value and hence
;a singleton which is not working right. 
;Come back to this point later.
;;; harshrc 03/10/12 - updated it to defrec and def

; 5 July '13 - Fixed bug. 2nd argument to 'nth' should be in bounds for finite types (-values* defconst).
; 15 July '13 - added range support
(def get-enum-info% (type range vl wrld R$ types-ht$)
  (decl :sig ((possible-defdata-type-p tau-interval fixnum plist-world R$ types-ht$)
              -> enum-info%-p)

;TODO: union types
        :doc "to fill")
  (declare (xargs :verify-guards nil))
; returns a well-formed enum-info defrec object
; r is the free variable in the enum-expression which
; is the place-holder for the random-seed or BE arg 
  (if (possible-constant-valuep type)
      (acl2::make enum-info% :size 1 :category :singleton :expr type :expr2 `(mv ',type seed.)) 
;ALSO HANDLE SINGLETON TYPES DIRECTLY
    
    (let ((entry (assoc-eq type 
                           (table-alist 'defdata::types-info-table wrld))))
     
    (if entry ;if we find enum-info from type-info-table then use it
        (b* ((types-info% (cdr entry))
              (TI.test-enumerator (access types-info% test-enumerator))
              (TI.enumerator      (access types-info% enumerator))
              (TI.enum-uniform    (access types-info% enum-uniform))
              (TI.size            (access types-info% size))
             ((unless (or (eq 't TI.size)
                         (posp TI.size)))
              (prog2$
               (cw? (normal-output-flag vl)
                    "~|CEgen/Error: size in type-info ~x0 should be posp.~%" (cdr entry))
               (acl2::make enum-info% :size 0 :category :empty :expr nil :expr2 nil)))
             
; 15 July '13 added support for integer and rational ranges
; (acl2-numberp ranges reduce to rational ranges) custom types dont
; take ranges in hyps into account, since they are explicitly given by
; user, the user is burdened with the resposibility of taking them
; into account manually. In any case even defined defdata types play
; well only for integers and rationals, but then you cannot define an
; interesting numeric type, like 4divp, primep, arithmetic
; progression, etc. But you can use / constructor to define some
; interesting types, so I need to think about how to make this more general!! TODO
             ((when (and (is-subtype$$ type 'acl2::integer R$ types-ht$)
                         (non-empty-non-universal-interval-p range)))
              (make-range-enum-info% 'acl2::integer range))
                                     
             ((when (and (is-subtype$$ type 'acl2::acl2-number R$ types-ht$)
                         (non-empty-non-universal-interval-p range)))
              (make-range-enum-info% 'acl2::rational range)))
                                             
              
             ;first check for test-enum
         (if TI.test-enumerator
             (cond 
              ((allows-arity TI.test-enumerator 1 wrld)
;TODO. I am not checking if test enumerator is to be used or not
               (acl2::make enum-info% :size 't
                           :category :function
                           :expr (list TI.test-enumerator 'r)
                           :expr2 (list (modify-symbol "" TI.test-enumerator "-UNIFORM") 'm 'seed.)))
              (t (prog2$
                  (cw? (normal-output-flag vl)
                       "~|CEgen/Error: ~x0 should be an enum function of arity 1.~%" TI.test-enumerator)
                  (acl2::make enum-info% :size 0 :category :empty :expr nil :expr2 nil))))

;common scenario: inf enumerator
           (if (eq 't TI.size);inf or custom registered (assume)
               (acl2::make enum-info% :size 't :category :function
                           :expr (list TI.enumerator 'r)
                           :expr2 (list TI.enum-uniform 'm 'seed.));inf or some enum fn
             (let ((stored-defconst 
                    (acl2-getprop TI.enumerator 'const wrld)))
              
              (if stored-defconst ;some finite set of values
                  (b* ((values (second stored-defconst))
                       (len-v (len values))
                       ((unless (posp len-v))
                        (prog2$
                         (cw? (normal-output-flag vl)
                              "~|CEgen/Error: stored-defconst ~x0 has 0 values~%" stored-defconst)
                         (acl2::make enum-info% :size 0 :category :empty :expr nil :expr2 nil))))
                   (acl2::make enum-info%
                               :size len-v 
                               :category (if (= len-v 1) 
                                             :singleton
                                           :defconst)
                               :expr (if (= len-v 1)  
                                         `',(car values)
                                       `(nth (mod r ,len-v) ,TI.enumerator))
                               :expr2 (if (= len-v 1)  
                                         `(mv ',(car values) seed.) ;todo check random-natural
                                       `(mv (nth (mod seed. ,len-v) ,TI.enumerator) seed.))))
;uncommon scenario, finite enumerator function        
                (if (allows-arity TI.enumerator 1 wrld) 
                    (acl2::make enum-info% :size TI.size 
                                :category :function
                                :expr (list TI.enumerator 'r)
                                :expr2 (list TI.enum-uniform 'm 'seed.));some enum fn
                  
                  (prog2$
                     (cw? (normal-output-flag vl)
                          "~|CEgen/Error: ~x0 is neither one of constant, an enum function or a values defconst.~%" TI.enumerator)
                     (acl2::make enum-info% :size 0 :category :empty :expr nil :expr2 nil))))))))

      ;;;o.w (possibly) custom 
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
                                `(nth (mod r ,len-v) ,vsym))
                        :expr2 (if (= len-v 1)  
                                  `(mv ',(car values) seed.);see todo above 
                                `(mv (nth (mod seed ,len-v) ,vsym) seed.))))
          (let ((esym (modify-symbol "NTH-" type "")))
                
            ;;check if enum is defined in wrld
            (cond ((allows-arity esym 1 wrld) 
                   (acl2::make enum-info% 
                             :size t 
                             :category :function
                             :expr `(,esym r)
                             :expr2 `(mv-let (r seed.)
                                             (random-natural-seed seed.)
                                             (mv (,esym r) seed.))))
                  (t 
                   (prog2$
                     (cw? (normal-output-flag vl)
                          "~|CEgen/Error: ~x0 doesnt appear to be a type.~%" type)
                     (acl2::make enum-info% :size 0 :category :empty :expr nil :expr2 nil)))))))))))
              
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
       
; 15 Oct '13 --harshrc: Commented out the following, so that (= x y)
; case is subsumed by the default case of cond i.e (R term1 ... termN)
; Thus, instead of not drawing an edge, a undirected edge is added
; between x and y.

;;        ((undirected-2-rel? hyp);(~ x  y)
;; ;dont draw an edge
;;         (build-vdependency-graph (cdr hyp-lst) alst alst-C incoming))

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
                              (member-eq sampling-method '(:mixed :random :uniform-random :be))
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
    :guard (and (member-eq s '(:mixed :random :uniform-random :be));(keywordp s)
                (natp i) (natp N) (<= i N))))
  
  (local (defun local-sampling-method (s i N) (list s i N))))

(defattach (local-sampling-method local-sampling-method-builtin))


(defrec gcs% 
; global-coverage-stats 
; Only accumulates sound and top-reproducible cts/wts
; i.e is not modified after a cross-fertilize ledge of the waterfall
  ((total-runs dups . vacs)
   (cts . wts) 
   (cts-to-reach . wts-to-reach)
   (start-time . end-time) 
   all-bets-off? 
   . (top-term top-vt-alist))
  NIL) 


(def initial-gcs% (nc nw start top-term top-vt-alist)
  (decl :sig ((fixnump fixnump rationalp allp) -> gcs%-p)
        :doc "reset/initialized global coverage stats record")
  (acl2::make gcs% :cts 0 :wts 0 :cts-to-reach nc :wts-to-reach nw
        :total-runs 0 :vacs 0 :dups 0 
        :start-time start :end-time start
        :all-bets-off? nil
        :top-term top-term
        :top-vt-alist top-vt-alist))

(defun gcs%-p (v)
  (declare (xargs :guard T))
  (case-match v
    (
     ('gcs% (total-runs dups . vacs)
            (cts . wts) 
            (cts-to-reach . wts-to-reach)
            (start-time . end-time) all-bets-off? . (& vt-al))
     (and (unsigned-29bits-p cts)
          (unsigned-29bits-p wts)
          (unsigned-29bits-p cts-to-reach)
          (unsigned-29bits-p wts-to-reach)
          (rationalp start-time)
          (rationalp end-time)
          (unsigned-29bits-p total-runs)
          (unsigned-29bits-p dups)
          (unsigned-29bits-p vacs)
          (booleanp all-bets-off?)
          (symbol-alistp vt-al)
          ))))

(defmacro gcs-1+ (fld-nm)
  `(change gcs% ,fld-nm
             (acl2::|1+F| (access gcs% ,fld-nm))))


(encapsulate
  ((stopping-condition? 
    (gcs%) t
    :guard (gcs%-p gcs%)))
  (local (defun stopping-condition? (gcs%) (list gcs%))))


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

(defun merge-car-symbol-< (l1 l2)
  (declare (xargs :measure (+ (acl2-count l1) (acl2-count l2))))
                    (cond ((endp l1) l2)
                          ((endp l2) l1)
                          ((symbol-< (car (car l1)) (car (car l2)))
                           (cons (car l1)
                                 (merge-car-symbol-< (cdr l1) l2)))
                          (t (cons (car l2)
                                   (merge-car-symbol-< l1 (cdr l2))))))

(defthm acl2-count-evens-strong
  (implies (and (consp x)
                (consp (cdr x)))
           (< (acl2-count (evens x)) (acl2-count x)))
  :rule-classes :linear)

(defthm acl2-count-evens-weak
  (<= (acl2-count (evens x)) (acl2-count x))
  :hints (("Goal" :induct (evens x)))
  :rule-classes :linear)


(defun merge-sort-car-symbol-< (l)
  (cond ((endp (cdr l)) l)
        (t (merge-car-symbol-< (merge-sort-car-symbol-< (evens l))
                               (merge-sort-car-symbol-< (odds l))))))

;; (defun merge-sort-entry-car-symbol-< (l ans)
;;   (if (endp l)
;;       ans
;;     (merge-sort-entry-car-symbol-< (cdr l)
;;                                    (cons (merge-sort-car-symbol-< (car l)) ans))))

(def record-testrun. (test-assignment-was A run-hist% gcs%)
  (decl :sig ((keyword symbol-doublet-listp run-hist%-p gcs%-p)
              ->
              (mv run-hist%-p gcs%-p))
        :doc 
"?: records the diagnostics/results of a single test trial run ")
  (b* ((num-wts (access gcs% wts-to-reach))
       (num-cts (access gcs% cts-to-reach))
       (A (merge-sort-car-symbol-< A))
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
  (decl :sig ((fixnum fixnum keyword fixnum fixnum symbol-fixnum-alist 
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
  (declare (ignorable vl))
  (b* (((when (zpf n)) ;Oops, ran out of random trials
        (mv NIL r. run-hist% gcs%))
       ((when (stopping-condition? gcs%))
;return, cos we have reached our goal  
         (mv T r. run-hist% gcs%))

       (local-trial-num  (acl2::|1+F| (acl2::-f num-trials n)))
       ((mv res A r. BE.)
;perform a random test run, the result quadruple
;erp is a flag denoting error, res = value of test  A= value-bindings
        (run-single-test. sm num-trials local-trial-num  r. BE.))
       ((mv run-hist% gcs%) (record-testrun. res A run-hist% gcs%))
       (- (cw? nil "~%test num ~x0 got A=~x1~|" n A)))
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
       
       (- (cw? (system-debug-flag vl) "~|run-hist: ~x0 ~|gcs%: ~x1~%"
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
         (val (acl2::access acl2::acl2s-param-info% rec-val :value))
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
                         (set-difference-eq ord-vs cvars)))

; 8th Jan 2013 Possible CCG bug
; Overcaution: remove t and nil which escape pseudo-termp
       (ord-vs (set-difference-eq  ord-vs '(t nil)))
       )

   ord-vs))
       

;;; Foll fun lifted from  type.lisp
;; NOTE: In the following the type 'empty' has
;; special status and treated seperately
(def meet (typ1 typ2 vl wrld R$ types-ht$)
  
  (decl :sig ((symbol symbol vl plist-worldp R$ types-ht$) -> symbol)
        :doc "find smaller type in subtype hierarchy/lattice")
  (declare (xargs :verify-guards nil))
  ;; (decl :sig ((possible-defdata-type-p possible-defdata-type-p
;;                plist-world) -> possible-defdata-type-p)
  (b* (((when (or (eq 'acl2::empty typ1)
                  (eq 'acl2::empty typ2))) 'acl2::empty)
       ((when (eq typ2 typ1)) typ2)
       ((unless (and (defdata::is-a-typeName typ1 wrld)
                     (defdata::is-a-typeName typ2 wrld)))
        (prog2$
         (cw? (verbose-stats-flag vl)
              "~|CEgen/Note: ~x0 or ~x1 not a defdata type. ~ Meet returning universal type ALL.~|" typ1 typ2)
         'acl2::all))
       ((when (eq 'acl2::all typ1)) typ2)
       ((when (eq 'acl2::all typ2)) typ1)
       ((when (is-subtype$$ typ1 typ2 R$ types-ht$))   typ1)
       ((when (is-subtype$$ typ2 typ1 R$ types-ht$))   typ2)
       ((when (is-disjoint$$ typ2 typ1 R$ types-ht$))  'acl2::empty) ;Should we instead define the NULL type??? Modified: so Ans is YES instead of Ans: NO, the way its used now, this is right!
;give preference to custom type
       ((when (defdata::is-a-custom-type typ1 wrld)) typ1)
       ((when (defdata::is-a-custom-type typ2 wrld)) typ2)

; choose the one that was defined later (earlier in 
; reverse chronological order)
       (u1 (type-vertex-ht-get typ1 types-ht$))
       (u2 (type-vertex-ht-get typ2 types-ht$)))
   (if (< u1 u2) 
       typ2 
     typ1)))






;;;; Collecting type and additional constraints

;;; Given a list of hypotheses and a conclusion, we want to find the
;;; type constraints on each free variable. We collect 3 categories of
;;; constraints: 1. defdata type and spilled defdata types 2. equality
;;; constraint 3. range constraints 4. additional constraints.

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
              eq-constraint range additional-constraints) NIL)

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
    (('cs% dt st eqc int ac)   (and (possible-defdata-type-p dt) 
                                (possible-defdata-type-list-p st)
                                (or (pseudo-termp eqc)
                                    (eq 'defdata::empty-eq-constraint eqc))
                                (acl2::tau-intervalp int)
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
(def put-var-eq-constraint. (v1 v2 vl wrld R$ types-ht$ v-cs%-alst.)
  (decl :sig ((symbol symbol vl plist-world R$ types-ht$ symbol-cs%-alist) 
              -> symbol-cs%-alist)
        :doc "put variable equality constraint in alist for key v")
  (declare (xargs :verify-guards nil) (ignore wrld))
  (b* (((cons & cs1%) (assoc-eq v1 v-cs%-alst.))
       ((cons & cs2%) (assoc-eq v2 v-cs%-alst.))
       (dt1 (acl2::access cs% cs1% :defdata-type))
       (dt2 (acl2::access cs% cs2% :defdata-type))
       ((mv v other-v cs% other-cs%) (if (is-subtype$$ dt2 dt1 R$ types-ht$) 
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

(def put-defdata-type. (v typ vl v-cs%-alst.)
  (decl :sig ((symbol possible-defdata-type-p fixnum symbol-cs%-alist) 
              -> symbol-cs%-alist)
        :doc "put defdata type typ in alist for key v")
  (b* (((cons & cs%) (assoc-eq v v-cs%-alst.))
       (dt (access cs% defdata-type))
       (- (cw? (and (verbose-stats-flag vl) (not (eq 'acl2::all dt))) 
"CEgen/Note: Overwriting defdata type for ~x0. ~x1 -> ~x2~|" v dt typ))
       (cs% (change cs% defdata-type typ)))
   (put-assoc-eq v cs% v-cs%-alst.)))



(defs  ;;might be mut-rec, but right now I assume tht I wont encounter
       ;;AND and OR like if expressions, and hence dont need the
       ;;mutually-recursive counterpart of v-cs%-alist-from-term. TODO
  (v-cs%-alist-from-term. (term vl wrld R$ types-ht$ ans.)
  (decl :sig ((pseudo-term fixnum plist-world R$ types-ht$ symbol-cs%-alist)
              ->
              symbol-cs%-alist)
        :doc "helper to collect-constraints")
  (declare (xargs :verify-guards nil))
;Invariant: ans. is an alist thats in the order given by dependency analysis
  (f* ((add-constraints... () (put-additional-constraints. fvars term ans.))
         
       (add-eq-constraint... (t1) (if (acl2::equivalence-relationp R wrld)
                                      (if (symbolp t1)
                                          (put-var-eq-constraint. x t1 vl wrld R$ types-ht$ ans.)
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
      
      ((P x)   (b* ((tname (is-type-predicate P wrld))
                    ((cons & cs%) (assoc-eq x ans.))
                    (curr-typ (access cs% defdata-type))
                    (smaller-typ (meet tname curr-typ vl wrld R$ types-ht$)))
                (if tname
                    (if (not (eq smaller-typ curr-typ))
                        (put-defdata-type. x smaller-typ vl ans.)
                      ans.)
                  (add-constraints...))))

      ((R (f . &) (g . &)) (declare (ignore R f g)) (add-constraints...))

;x has to be an atom below, otherwise, we would have caught that case
;above.
      ((R x ('quote c))    (add-eq-constraint... (kwote c)))
      ((R ('quote c) x)    (add-eq-constraint... (kwote c)))
      ((R x (f . args))    (add-eq-constraint... (acl2::cons-term f args)))
      ((R (f . args) x)    (add-eq-constraint... (acl2::cons-term f args)))
      ((R x y)             (add-eq-constraint... y))
      
      ;; has to be a (R t1 t2 ...) or atomic term
      (&                   (add-constraints...)))))))
                         
  
(def v-cs%-alist-from-terms. (terms vl wrld R$ types-ht$ ans.)
  (decl :sig ((pseudo-term-listp fixnum plist-worldp R$ types-ht$ symbol-cs%-alist) 
              -> symbol-cs%-alist)
        :doc "helper to collect-constraints%")
  (declare (xargs :verify-guards nil))
  (if (endp terms)
      ans.
    (v-cs%-alist-from-terms. (cdr terms) vl wrld R$ types-ht$ 
                             (v-cs%-alist-from-term. (car terms)
                                                     vl wrld R$ types-ht$ ans.))))

(def put-range-constraint. (v int v-cs%-alst.)
  (decl :sig ((symbolp acl2::tau-intervalp symbol-cs%-alistp) 
              -> symbol-cs%-alistp)
        :doc "put interval int in alist for key v")
  (b* (((cons & cs%) (assoc-eq v v-cs%-alst.))
       (cs% (change cs% range int)))
   (put-assoc-eq v cs% v-cs%-alst.)))

(def range-is-alias-p (interval type wrld R$ types-ht$)
  (decl :sig ((non-empty-non-universal-interval-p symbolp plist-worldp R$ types-ht$) -> boolean)
        :doc "is interval an alias of type?")
  (declare (xargs :verify-guards nil) (ignore wrld))
  (b* ((lo (acl2::access acl2::tau-interval interval :lo))
       (hi (acl2::access acl2::tau-interval interval :hi))
       (lo-rel (acl2::access acl2::tau-interval interval :lo-rel))
       (hi-rel (acl2::access acl2::tau-interval interval :hi-rel)))
    (case (acl2::access acl2::tau-interval interval :domain)
      (acl2::integerp (or (and (is-subtype$$ type 'acl2::nat R$ types-ht$) ;use the fact that integers are squeezed (weak inequalities)
                               (equal lo 0)
                               (null hi))
                          (and (is-subtype$$ type 'acl2::pos R$ types-ht$) 
                               (equal lo 1)
                               (null hi))
                          (and (is-subtype$$ type 'acl2::neg R$ types-ht$) 
                               (null lo)
                               (equal hi -1))))
      (otherwise (or (and (is-subtype$$ type 'acl2::positive-rational R$ types-ht$)
                          lo-rel ;strict
                          (null hi)
                          (equal lo 0))
                     (and (is-subtype$$ type 'acl2::negative-rational R$ types-ht$) 
                          hi-rel
                          (null lo)
                          (equal hi 0)))))))

(def assimilate-apriori-type-information (vs type-alist tau-interval-alist vl wrld R$ types-ht$ ans.)
  (decl :sig ((symbol-list symbol-alist symbol-alist fixnum plist-world R$ types-ht$ symbol-cs%-alist) 
              -> symbol-cs%-alist)
        :doc 
"overwrite into v-cs%-alst. the type information in type-alist/tau-interval-alist.
Put defdata symbol types into defdata-type field, but put constants
into eq-constraint field, put interval into range constraint field")
  (declare (xargs :verify-guards nil))
; Aug 30 '12 -- This function fixes a bug in Pete's GE demo, where the
; type=alist had 'NIL as the type, which is a singleton defdata type
; and I was not taking it into consideration when trying to run MEET
; on it, which cannot handle types which are not in the defdata graph,
; and certainly constants are not part of the defdata graph.
  (if (endp vs)
      ans.
    (b* ((x (car vs))
         (prior-t (assoc-eq x type-alist)) ;prior-t is consp assert!
;type-alist of of form (listof (cons var (listof defdata-type)))
;where defdata-type is possible-defdata-type-p. listof represents unions.
         (- 
; TODO: Union types are ignored. Implement them.
; But note that since we always get this through a meet-type-alist, we
; throw away the union type information there itself.
           (cw? (and (verbose-stats-flag vl)
                     (consp prior-t)
                     (consp (cdr prior-t)) 
                     (not (null (cddr prior-t))))
"~|CEgen/Warning: Ignoring rest of union types ~x0 ~|" (cddr prior-t)))
         (typ-given (if (and (consp prior-t) (consp (cdr prior-t)))
                        (cadr prior-t)
                      'ACL2::ALL))
         ((when (possible-constant-valuep typ-given))
; is a singleton, then treat it as a eq-constraint
; BOZO: meet-type-alist does it differently. (03/04/13)
          (assimilate-apriori-type-information 
           (cdr vs) type-alist tau-interval-alist vl wrld R$ types-ht$ 
           (put-eq-constraint. x typ-given vl ans.)))
         (int-entry (assoc-eq x tau-interval-alist))
         (int (cdr int-entry)) ;possible type bug
         ((when (singleton-tau-intervalp int))
; is a singleton, then treat it as a eq-constraint
          (assimilate-apriori-type-information 
           (cdr vs) type-alist tau-interval-alist vl wrld R$ types-ht$ 
           (put-eq-constraint. x (kwote (acl2::access acl2::tau-interval int :lo)) vl ans.)))
         ((cons & cs%) (assoc-eq x ans.))
         (curr-typ (access cs% defdata-type))
         (final-typ (meet curr-typ typ-given vl wrld R$ types-ht$))
         (ans. (if (and (non-empty-non-universal-interval-p int)
                        (not (range-is-alias-p int final-typ wrld R$ types-ht$)))
                   (put-range-constraint. x int ans.)
                 ans.)))
                   
; update the current defdata type with the new type information (type-alist)
     (assimilate-apriori-type-information 
      (cdr vs) type-alist tau-interval-alist vl wrld R$ types-ht$
      (put-defdata-type. x final-typ vl ans.)))))

(defconst *empty-cs%*
  (acl2::make cs%
        :defdata-type 'acl2::all 
        :spilled-types '()
        :eq-constraint 'defdata::empty-eq-constraint
        :range (acl2::make-tau-interval nil nil nil nil nil)
        :additional-constraints '()))

(def collect-constraints% (hyps ordered-vars type-alist tau-interval-alist vl wrld R$ types-ht$)
  (decl :sig ((pseudo-term-listp symbol-listp symbol-alistp symbol-alistp
                                 fixnum plist-worldp R$ types-ht$) -> symbol-cs%-alist)
        :doc 
" 
* Synopsis 
  For each free variable compute/infer both the simple defdata types
  and additional constraints on it.

* Input hyps is a usually a list of hypotheses of the conjecture under
  query and is a term-listp ordered-vars is the free variables of
  hyps, but in the variable dependency order as computed from the
  dependency graphs of hyps.  type-alist is the type information
  inferred from ACL2 usually (intersected with the top-level dumb type
  inference), or it might be prior type knowledge we dont want to lose
  i.e if the type inferred from hyps are weaker than in type-alist we
  will keep the stronger type information.
  

* Output
  An alist mapping free variables to cs% record
")
  (declare (xargs :verify-guards nil))
  (f* ((unconstrained-v-cs%-alst 
          (xs) 
          (pairlis$ xs (make-list (len xs)
                                  :initial-element 
                                  *empty-cs%*))))
      ;; initialize the alist
    (b* ((v-cs%-alst  (unconstrained-v-cs%-alst ordered-vars))
         (v-cs%-alst  (assimilate-apriori-type-information
                       ordered-vars type-alist tau-interval-alist
                       vl wrld R$ types-ht$ v-cs%-alst)))
       
     (v-cs%-alist-from-terms. hyps vl wrld R$ types-ht$ v-cs%-alst))))

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
            
     
(defconst *recursive-uniform-enum-measure* 8)


(def make-next-sigma_mv-let (var-enumcalls-alist body)
  (decl :sig ((symbol-alistp all) -> all)
        :doc "helper function to make-next-sigma")
  (f* ((_mv-value (v exp exp2) 
          `(case sampling-method 
             (:uniform-random (b* (((mv ?m seed.) 
                                    (random-index-seed *recursive-uniform-enum-measure* seed.))
                                   ((mv val seed.) ,exp2))
                        (mv seed. BE. val)))
             (:random 
              (b* (((mv ?r seed.) (random-natural-seed seed.)))
                (mv seed. BE. ,exp)))
             ;; bugfix - It is possible that r is not in exp
             ;; this is the case when exp is a eq-constraint
             (:be (b* ((?r (cdr (assoc-eq ',v BE.))))
                   (mv seed. (|next BE args| BE.) ,exp)))
             (otherwise (mv seed. BE. '0)))))
                           
  (if (endp var-enumcalls-alist)
      body
    (b* (((cons var ecalls) (first var-enumcalls-alist)))
;    in 
     `(mv-let (seed. BE. ,var)
              ,(_mv-value var (first ecalls) (second ecalls))
            ,(make-next-sigma_mv-let (rest var-enumcalls-alist) body))))))

(def make-guard-var-member-eq (vars alst)
  (decl :sig ((symbol-alistp symbol) -> all)
        :doc "helper function to make-next-sigma")
  (if (endp vars)
      nil
    (cons `(member-eq ',(car vars) ,alst)
          (make-guard-var-member-eq (cdr vars) alst))))
  
(def cs%-enumcalls (cs% vl wrld R$ types-ht$ computed-vars)
  (decl :sig ((cs%-p fixnump plist-worldp R$ types-ht$ symbol-listp) 
              -> (mv fixnum (cons pseudo-termp pseudo-termp)))
        :doc "for each cs% record we translate it into the a (mv
  size (list enumcall enumcall2)), where the enumcall is an expression
  that when evaluated gives a value (with random distribution) of
  correct type/constraint and size is the size of the type i.e the set
  of value satisfied by the constraint. enumcall2 is a similar
  expression but with the random seed accumulated/threaded
  uniformly. Return value of (mv 0 nil) stands for an error and is
  recognized by the caller function as such.")
  (declare (xargs :verify-guards nil))
;;; TODO: optimize/complete here using extra information in
;;; spilled-types and additional-constraints
  (case-match cs%
;('cs% defdata-type spilled-types eq-constraint interval additional-constraints)
    (('cs% defdata-type & 'defdata::empty-eq-constraint range &) 
; ACHTUNG: cs% defrec exposed
     (b* ((enum-info% (get-enum-info% defdata-type range vl wrld R$ types-ht$)))
      (mv (access enum-info% size) (list (access enum-info% expr)
                                         (access enum-info% expr2)))))

; if we see a equality constraint, we give preference to it over a
; defdata type, but only if the variables in the eq-constraint are
; already computed i.e already have an enumcall in the final answer
    (('cs% defdata-type & eq-constraint range &)    
     (b* ((eq-vs (all-vars eq-constraint))
          (remaining (set-difference-eq eq-vs computed-vars)))
      (if remaining
          (b* ((enum-info% (get-enum-info% defdata-type range vl wrld R$ types-ht$)))
           (mv (access enum-info% size) (list (access enum-info% expr)
                                              (access enum-info% expr2))))
        (mv 1 (list eq-constraint (list 'mv eq-constraint 'seed.))))))
    (& (prog2$ 
        (cw? (normal-output-flag vl) "~|CEgen/Error: BAD record cs% passed to cs%-enumcalls")
        (mv 0 NIL)))))
               
     
(def make-enumerator-calls-alist (v-cs%-alst vl wrld R$ types-ht$ ans.)
  (decl :sig ((symbol-cs%-alist fixnum plist-world R$ types-ht$ symbol-alist) 
              -> (mv erp symbol-alist))
        :doc 
        "given an alist mapping variables to cs% records (in dependency order),
  we walk down the alist, translating each type constraint to the corresponding
enumerator call expression")
  (declare (xargs :verify-guards nil))
  (if (endp v-cs%-alst)
      (mv nil (rev ans.)) ;dont change the original dependency order
    (b* (((cons x cs%) (car v-cs%-alst))
         ((mv size calls) (cs%-enumcalls cs% vl wrld R$ types-ht$ (strip-cars ans.)))

; simple bug July 9 2013: below comparison, replaced int= with equal,
; this could have been caught by type-checking/guard-verif
         ((when (equal size 0)) (mv t '()))) 
;    in
     (make-enumerator-calls-alist (cdr v-cs%-alst) vl wrld R$ types-ht$
                                 ;; add in reverse order
                                 (cons (cons x calls) ans.)))))
    
(defun displayed-range (interval)
  (b* ((lo (acl2::access acl2::tau-interval interval :lo))
       (hi (acl2::access acl2::tau-interval interval :hi))
       (lo-rel (acl2::access acl2::tau-interval interval :lo-rel))
       (hi-rel (acl2::access acl2::tau-interval interval :hi-rel)))
    (cond ((and lo hi)
           `(,lo ,(if lo-rel '< '<=) 'acl2::_  ,(if hi-rel '< '<=) ,hi))
          (lo
           `(,(if lo-rel '> '>=) ,lo))
          (t `(,(if hi-rel '< '<=) ,hi)))))


; DUPLICATION
(def displayed-defdata-type/eq-constraint (cs% computed-vars)
  (decl :sig ((cs%-p symbol-listp) 
              -> (mv fixnum pseudo-termp))
        :doc "for each cs% record we translate it to defdata-type or 
equality constraint that will be used for enumeration. it shadows cs%-enumcall")
  (case-match cs%
;('cs% defdata-type spilled-types eq-constraint range additional-constraints)
    (('cs% defdata-type & 'defdata::empty-eq-constraint range &) 
; ACHTUNG: cs% defrec exposed
     (if (non-empty-non-universal-interval-p range)
         (list :type defdata-type :range (displayed-range range))
       defdata-type))
    (('cs% defdata-type & eq-constraint range &)    
     (b* ((eq-vs (all-vars eq-constraint))
          (remaining (set-difference-eq eq-vs computed-vars)))
      (if remaining
          (if (non-empty-non-universal-interval-p range)
              (list :type defdata-type :range (displayed-range range))
            defdata-type)
        eq-constraint)))
    (& 'bad-type)))

(def displayed-enum-alist (v-cs%-alst ans.)
  (decl :sig ((symbol-cs%-alist symbol-alist) 
              -> symbol-alist)
        :doc 
        "given an alist mapping variables to cs% records (in dependency order),
  we walk down the alist, translating each type constraint to the corresponding
enumerator type/expr to be displayed in verbose mode")
  (if (endp v-cs%-alst)
      (rev ans.) ;dont change the original dependency order
    (b* (((cons x cs%) (car v-cs%-alst))
         (type (displayed-defdata-type/eq-constraint cs% (strip-cars ans.))))
     
     (displayed-enum-alist (cdr v-cs%-alst)
                           ;; add in reverse order
                           (cons (cons x type) ans.)))))

;bugfix May 24 '12
;partial-A needs to be quoted to avoid being confused with function app
(def kwote-symbol-doublet-list (A)
  (decl :sig ((symbol-doublet-listp) -> quoted-constantp))
  (if (endp A)
      nil
    (cons (list 'list (kwote (caar A)) (cadar A))
          (kwote-symbol-doublet-list (cdr A)))))

(def make-next-sigma-defuns (hyps concl ord-vs 
                                  partial-A type-alist tau-interval-alist
                                  vl wrld R$ types-ht$)
  (decl :sig ((pseudo-term-list pseudo-term symbol-list 
                      symbol-doublet-listp symbol-alist symbol-alist
                      fixnum plist-worldp R$ types-ht$) 
              -> (mv erp all symbol-alist))
        :doc "return the defun forms defining next-sigma function, given a
        list of hypotheses and conclusion (terms). Also return the enum-alist to be displayed")
  (declare (xargs :verify-guards nil))
  (f* ((defun-forms ()
         `((defun next-sigma-current (sampling-method seed. BE.)
            "returns (mv A seed. BE.)"
            (declare (ignorable sampling-method)) ;in case ord-vs is nil
            (declare (type (unsigned-byte 31) seed.))
            (declare (xargs :verify-guards nil
                            :guard 
                            (and (member-eq sampling-method
                                            '(:random :uniform-random :be))
                                 (unsigned-byte-p 31 seed.)
                                 (symbol-unsigned-29bits-alistp BE.)
                                 (consp BE.) ;precondition TODOcheck
                                 (and ,@(make-guard-var-member-eq
                                         (strip-cars var-enumcalls-alist)
                                         'BE.)))
                            :guard-hints 
                            (("Goal" :in-theory (disable unsigned-byte-p)))))
            ,(make-next-sigma_mv-let
                var-enumcalls-alist
; sigma will be output as a let-bindings i.e symbol-doublet-listp
                `(mv ,(make-var-value-list-bindings 
                       (strip-cars var-enumcalls-alist) 
                       (kwote-symbol-doublet-list partial-A))
                     seed. BE.)))
           (defun next-sigma-current-gv (sampling-method seed. BE.)
             (declare (xargs :guard T :verify-guards t))
             ;(declare (type (unsigned-byte 31) seed.))
             (ec-call (next-sigma-current sampling-method seed. BE.))))))
         
; Invariant: v-cs%-alst. should obey a dependency order such that the
; final enum-call alist when converted to a let* will obey the
; dependency order of evaluation. This is mostly satisfied, as
; ord-vars does take care of this. But put-var-eq-constraint. might
; change this, where an extra dependency is created because of type
; information that was ignored during creation of ord-vs, so there is
; an ugly hack in place to reorder in the middle of put-var-eq-constraint.
       
   (b* ((v-cs%-alst (collect-constraints% 
                     (cons (dumb-negate-lit concl) hyps)
                     ord-vs type-alist tau-interval-alist vl wrld R$ types-ht$))
        ((mv erp var-enumcalls-alist)
         (make-enumerator-calls-alist v-cs%-alst vl wrld R$ types-ht$ '()))
        ((when erp) (mv erp '() '()))
        )
;   in
    (mv nil (defun-forms) (displayed-enum-alist v-cs%-alst '())))))



(defs 
  (mv-list-ify (term mv-sig-alist)
    (decl :sig ((pseudo-term symbol-list) -> pseudo-term)
          :doc "wrap all mv fn calls with mv-list")
    (if (variablep term)
      term
      (if (fquotep term)
        term
      (b* ((fn (ffn-symb term))
           (args (fargs term))
           (A mv-sig-alist)
           (entry (assoc-eq fn A))
           ((unless entry)
            (acl2::cons-term fn
                       (mv-list-ify-lst args A)))
           ((cons fn m) entry)) 
;m is output arity and should be greater than 1.
        (acl2::cons-term 'acl2::mv-list
                   (list (kwote m)
                         (acl2::cons-term fn (mv-list-ify-lst args A))))))))

  (mv-list-ify-lst (terms mv-sig-alist)
   (decl :sig ((pseudo-term-list symbol-list) -> pseudo-term-list))
   (if (endp terms)
       '()
     (cons (mv-list-ify (car terms) mv-sig-alist)
           (mv-list-ify-lst (cdr terms) mv-sig-alist)))))
         
        

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

(def make-hypotheses-val-defuns (terms ord-vars mv-sig-alist)
  (decl :sig ((pseudo-term-list symbol-list symbol-alist) -> all)
        :doc "make the defun forms for hypotheses-val defstub")
  `((defun hypotheses-val-current (A)
      (declare (ignorable A))
      (declare (xargs :verify-guards nil :normalize nil
                      :guard (symbol-doublet-listp A)))
      (let ,(make-let-binding-for-sigma ord-vars 'A)
        (declare (ignorable ,@ord-vars))
          ,(mv-list-ify (single-hypothesis terms)
                        mv-sig-alist)))
    (defun hypotheses-val-current-gv (A)
      (declare (xargs :guard T :verify-guards t))
      (ec-call (hypotheses-val-current A)))))

(def make-conclusion-val-defuns (term ord-vars mv-sig-alist)
  (decl :sig ((pseudo-term symbol-list symbol-alist) -> all)
        :doc "make the defun forms for conclusion-val defstub")
  `((defun conclusion-val-current (A)
      (declare (ignorable A))
      (declare (xargs :verify-guards nil :normalize nil
                      :guard (symbol-doublet-listp A)))
      (let ,(make-let-binding-for-sigma ord-vars 'A)
        (declare (ignorable ,@ord-vars))
          ,(mv-list-ify term mv-sig-alist)))
    (defun conclusion-val-current-gv (A)
      (declare (xargs :guard T :verify-guards t))
      (ec-call (conclusion-val-current A)))))

;add the following for guard verif
(defthm symbol-doublet-listp-=>-symbol-alistp
  (implies (symbol-doublet-listp x)
           (symbol-alistp x))
  :rule-classes ((:forward-chaining)
                 (:rewrite :backchain-limit-lst 1)
                 ))


;; records data that is later needed for printing stats/summary 
(defrec s-hist-entry% (run-hist 
                       (hyps vars . concl)
                       (elide-map) ;printing top-level cts/wts
                       (start-time . end-time) . name) NIL)

(defun s-hist-entry%-p (v)
  (declare (xargs :guard T))
  (case-match v ;internal layout hidden
    (('s-hist-entry% run-hist
                     (hyps vars . concl)
                     (elide-map)
                     (start-time . end-time) . name)
     (and (run-hist%-p run-hist)
          (pseudo-term-listp hyps)
          (pseudo-termp concl)
          (symbol-listp vars)
          (symbol-alistp elide-map) ;actually symbol term alist
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

(defun cgen-stats-p (v)
;todo - probably inefficient
  (declare (xargs :guard T))
  (and (keyword-value-listp v)
       ;(= (len v) 4) extensible
       (assoc-keyword :gcs% v)
       (assoc-keyword :s-hist v)))

(defun cgen-stats-event-stackp (s)
  (declare (xargs :guard T))
  (if (atom s)
      (null s)
    (and (cgen-stats-p (car s))
         (cgen-stats-event-stackp (cdr s)))))

(defun valid-cgen-stats-event-stackp (s)
  (declare (xargs :guard T))
  "Should be a non-empty list whose member satisfies cgen-stats-event-stackp"
  (and (cgen-stats-event-stackp s)
       (consp s)))

;; Feb 22 2013 Add a new global state variable which points to
;; a stack of accumulated cgen recorded statistics. Its a stack
;; because we can have nested events, but only the innermost
;; member of the stack should ever be non-empty i.e only the top-level
;; events like defthm/thm/test? should ever hold valid recorded data.
;NOTE: interesting - I cant use defmacro instead of defabbrev
(defabbrev get-gcs%-global () 
  (if (f-boundp-global 'cgen-stats-event-stack state)
    (b* ((cse-stack (@ cgen-stats-event-stack))
         ((unless (valid-cgen-stats-event-stackp cse-stack))
            (er hard? ctx "~|CEgen/Error: (get-gcs%) cgen-stats-event-stack is ill-formed~|"))
         (gcs% (cadr (assoc-keyword :gcs% (car cse-stack)))))
      (if (gcs%-p gcs%)
          gcs%
        (er hard? ctx "~|CEgen/Error: gcs% found in globals is of bad type~|")))
    (er hard? ctx "~|CEgen/Error: cgen-stats-event-stack not found in globals ~|")))

(defabbrev get-s-hist-global () 
  (if (f-boundp-global 'cgen-stats-event-stack state)
    (b* ((cse-stack (@ cgen-stats-event-stack))
         ((unless (valid-cgen-stats-event-stackp cse-stack))
          (er hard? ctx "~|CEgen/Error: (get-s-hist) cgen-stats-event-stack is ill-formed~|"))
         (s-hist (cadr (assoc-keyword :s-hist (car cse-stack)))))
      (if (s-hist-p s-hist)
          s-hist
        (er hard? ctx "~|CEgen/Error: hist found in globals is of bad type~|")))
    (er hard? ctx "~|CEgen/Error: cgen-stats-event-stack not found in globals ~|")))

(defabbrev put-gcs%-global (gcs%) 
  (if (f-boundp-global 'cgen-stats-event-stack state)
      (if (gcs%-p gcs%)
          (b* ((cse-stack (@ cgen-stats-event-stack))
               ((unless (valid-cgen-stats-event-stackp cse-stack))
                  (prog2$ 
                 (er hard? ctx "~|CEgen/Error: (put-gcs%) cgen-stats-event-stack is ill-formed~|")
                 state))
               (cse-stack (cons (list* :gcs% gcs% (acl2::remove-keyword :gcs% (car cse-stack))) 
                                (cdr cse-stack)));update 
               (- (assert$ (valid-cgen-stats-event-stackp cse-stack) 'put-gcs%-global)))
          (f-put-global 'cgen-stats-event-stack cse-stack state))
        (prog2$ 
         (er hard? ctx "~|CEgen/Error: gcs% being put in globals is of bad type~|")
         state))
    (prog2$ (er hard? ctx "~|CEgen/Error: cgen-stats-event-stack not found in globals ~|")
            state)))

(defabbrev put-s-hist-global (s-hist) 
  (if (f-boundp-global 'cgen-stats-event-stack state)
      (if (s-hist-p s-hist)
          (b* ((cse-stack (@ cgen-stats-event-stack))
               ((unless (valid-cgen-stats-event-stackp cse-stack))
                (prog2$ 
                 (er hard? ctx "~|CEgen/Error: (put-s-hist) cgen-stats-event-stack is ill-formed~|")
                 state))
               (cse-stack (cons (list* :s-hist s-hist (acl2::remove-keyword :s-hist (car cse-stack))) 
                                (cdr cse-stack)));update
               (- (assert$ (valid-cgen-stats-event-stackp cse-stack) 'put-s-hist-global)))
          (f-put-global 'cgen-stats-event-stack cse-stack state))
        (progn$
         (cw? (debug-flag vl) "~|BAD s-hist : ~x0~|" s-hist)
         (er hard? ctx "~|CEgen/Error: hist being put in globals is of bad type~|")
         state))
    (prog2$ (er hard? ctx "~|CEgen/Error: cgen-stats-event-stack not found in globals ~|")
            state)))


(defconst *initial-run-hist%* 
  (acl2::make run-hist% 
              :cts '() :wts '() :vacs '() 
              :|#wts| 0 :|#cts| 0 
              :|#vacs| 0 :|#dups| 0))

(def initial-s-hist-entry% (name hyps concl vars 
                                 elide-map start)
  (decl :sig ((string pseudo-term-list pseudo-term symbol-list 
                      symbol-alist rational) 
              -> s-hist-entry%)
        :doc "make initial s-hist-entry% given args")
  (acl2::make s-hist-entry% 
              :name name :hyps hyps :concl concl :vars vars 
              :elide-map elide-map
              :start-time start :end-time start
              :run-hist *initial-run-hist%*))
          


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

; use expand-assumptions-1 instead when you have a term
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


(defun collect-tau-alist (triples tau-alist type-alist pot-lst ens wrld)
(declare (xargs :mode :program))

  (if (endp triples)
      tau-alist
    (b* (((mv ?contradictionp ?mbt ?mbf tau-alist ?calist)
          (acl2::tau-assume nil (caddr (car triples))
                            tau-alist type-alist pot-lst
                            ens wrld nil))
         (- (cw? nil "~% *** tau-assume returned ~x0~%~%" tau-alist)))
      (collect-tau-alist (cdr triples)
                         tau-alist type-alist pot-lst ens wrld))))

(defun tau-alist-clause (clause sign ens wrld state)
  (declare (xargs :mode :program :stobjs (state)))
;duplicated from tau-clausep in prove.lisp.
(b* (((mv ?contradictionp type-alist pot-lst)
      (acl2::cheap-type-alist-and-pot-lst clause ens wrld state))
     (triples (acl2::merge-sort-car-<
                (acl2::annotate-clause-with-key-numbers clause
                                                        (len clause)
                                                        0 wrld)))
     (tau-alist (collect-tau-alist triples sign type-alist pot-lst
                                   ens wrld)))
  tau-alist))


;; (defun tau-alist-clauses (clauses sign ens wrld state ans)
;;   (declare (xargs :mode :program :stobjs (state)))
;;   (if (endp clauses)
;;       ans
;;     (tau-alist-clauses (cdr clauses) sign ens wrld state
;;                        (append (tau-alist-clause (car clauses) sign ens wrld state) ans))))
      



       
(defun all-vals (key alist)
  (declare (xargs :guard (and (symbolp key)
                              (alistp alist))))
  (if (endp alist)
      '()
    (if (eq key (caar alist))
        (cons (cdar alist) (all-vals key (cdr alist)))
      (all-vals key (cdr alist)))))

(defun make-var-taus-alist (vars tau-alist)
  (declare (xargs :guard (and (symbol-listp vars)
                              (alistp tau-alist))))
  (if (endp vars)
      '()
    (b* ((vals (all-vals (car vars) tau-alist)))
      (cons (cons (car vars) vals)
            (make-var-taus-alist (cdr vars) tau-alist)))))

(defun conjoin-tau-interval-lst (taus ans)
; [tau] * interval -> interval
  (declare (xargs :mode :program))
  (if (endp taus)
      ans
    (b* ((tau (car taus))
           (interval (acl2::access acl2::tau tau :interval)))
    (conjoin-tau-interval-lst (cdr taus) 
                              (acl2::conjoin-intervals interval ans)))))
  

(defun tau-interval-alist (var-taus-alist)
;[var . taus] -> [var . interval]
  (declare (xargs :mode :program))
  (if (endp var-taus-alist)
      '()
    (b* (((cons var taus) (car var-taus-alist))
         (interval (conjoin-tau-interval-lst taus nil)) ;nil represents the universal interval 
         )
      (if (null interval) ;universal
          (tau-interval-alist (cdr var-taus-alist))
        (cons (cons var interval)
              (tau-interval-alist (cdr var-taus-alist)))))))



(defun tau-interval-alist-clause (cl name ens vl wrld state)
    (declare (xargs :mode :program :stobjs (state)))
    (b* ((tau-alist (tau-alist-clause cl nil ens wrld state))
         (var-taus-alist (make-var-taus-alist (all-vars-lst cl) tau-alist))
         (- (cw? (system-debug-flag vl)
                 "~|CEgen/Debug: taus alist (~s0): ~x1~|" name var-taus-alist))
         (tau-interval-alist (tau-interval-alist var-taus-alist))
         (- (cw? (debug-flag vl)
                 "~|CEgen/Debug: tau interval alist (~s0): ~x1~|" name tau-interval-alist)))
      tau-interval-alist))
     
    
(defun get-acl2-type-alist (cl name ens vl state)
  (declare (xargs :mode :program
                  :stobjs (state)))
  (b* (((mv erp type-alist &)
       (acl2::forward-chain cl
                            (acl2::enumerate-elements cl 0)
                            nil ; do not force
                            nil ; do-not-reconsiderp
                            (w state)
                            ens
                            (acl2::match-free-override (w state))
                            state))
;Use forward-chain ACL2 system function to build the context
;This context, gives us the type-alist ACL2 inferred from the
;the current subgoal i.e. cl
       (vars (all-vars-lst cl))
       (vt-acl2-alst (if erp ;contradiction
                         (pairlis$ vars (make-list (len vars)
                                                   :initial-element 
                                                   (list 'ACL2::ALL)))
                       (acl2::decode-acl2-type-alist type-alist vars)))
       (- (cw? (debug-flag vl)
"~|CEgen/Debug: ACL2 type-alist (~s0): ~x1~|" name vt-acl2-alst)))
   vt-acl2-alst))


(def dumb-type-alist-infer-from-term (term vl wrld R$ types-ht$ ans.)
  (decl :sig ((pseudo-term-listp fixnum plist-worldp R$ types-ht$ symbol-alistp) 
              -> symbol-alistp)
        :doc "main aux function to infer type-alist from term")
  (declare (xargs :verify-guards nil))
; ans. is a type alist and has type
; (symbol . (listof possible-defdata-type-p))
  (f* ((add-eq-typ... (t1) (if (acl2::equivalence-relationp R wrld)
                               (put-assoc x (list t1) ans.)
                             ans.)))
    
; Copied from v-cs%-alist-from-term. Keep in sync!
  (case-match term
    
;the following is a rare case (I found it when the conclusion is nil
;and its negation is 'T
    (('quote c) (declare (ignore c))  ans.) ;ignore quoted constant terms 

;TODO possible field variable (i.e f is a getter/selector) Note that
; term cannot have a lambda applicaton/let, so the car of the term is
; always a function symbol if term is a consp.
    ((P (f . &)) (declare (ignore P f))  ans.)

;x has to be an atom below, otherwise, we would have caught that case above.
    (('not x)      (put-assoc x (list ''nil) ans.))
    
    ((P x)   (b* ((tname (is-type-predicate P wrld))
                  ((unless tname) ans.)
                  (curr-typs-entry (assoc-eq x ans.))
                  ((unless (and curr-typs-entry 
                                (consp (cdr curr-typs-entry))))
; no or invalid entry, though this is not possible, because we call it with
; default type-alist of ((x . ('ALL)) ...)
                   ans.)
                  (curr-typs (cdr curr-typs-entry))
                  (- (cw? (and (verbose-stats-flag vl) 
                               (consp (cdr curr-typs)))
                          "~|CEgen/Warning: Ignoring rest of union types ~x0 ~|" (cdr curr-typs)))
                     
                  (curr-typ (car curr-typs))
                  ((when (possible-constant-valuep curr-typ)) ans.)
                   
                  (final-typ (meet tname curr-typ vl wrld R$ types-ht$)))
               (put-assoc x (list final-typ) ans.)))

    ((R (f . &) (g . &)) (declare (ignore R f g)) ans.) ;ignore

;x has to be an atom below, otherwise, we would have caught that case
;above.
    ((R x ('quote c))    (add-eq-typ... (kwote c)))
    ((R ('quote c) x)    (add-eq-typ... (kwote c)))
    ;((R x (f . args))    (add-eq-constraint... (acl2::cons-term f args)))
    ;((R (f . args) x)    (add-eq-constraint... (acl2::cons-term f args)))
    
    ;; has to be a (R t1 t2 ...) or atomic term
    (&                   ans.))))

(def dumb-type-alist-infer-from-terms (H vl wrld R$ types-ht$ ans.)
  (decl :sig ((pseudo-term-listp fixnum plist-worldp R$ types-ht$ 
                                 symbol-alistp) -> symbol-alistp)
        :doc "aux function for dumb extraction of defdata types from terms in H")
  (declare (xargs :verify-guards nil))
  (if (endp H)
      ans.
    (b* ((term (car H))
         (ans. (dumb-type-alist-infer-from-term term vl wrld R$ types-ht$ ans.)))
      (dumb-type-alist-infer-from-terms (cdr H) vl wrld R$ types-ht$ ans.))))

(def dumb-type-alist-infer (H vars vl wrld R$ types-ht$)
  (decl :sig ((pseudo-term-listp symbol-listp fixnum plist-worldp R$ types-ht$) 
              -> symbol-alistp)
        :doc "dumb infer defdata types from terms in H")
  (declare (xargs :verify-guards nil))
  (dumb-type-alist-infer-from-terms 
   H vl wrld R$ types-ht$
   (pairlis$ vars (make-list (len vars)
                             :initial-element 
                             (list 'ACL2::ALL)))))


(def meet-type-alist (A1 A2 vl wrld R$ types-ht$)
  (decl :sig ((symbol-alistp symbol-alistp fixnum plist-world R$ types-ht$)
              -> (mv erp symbol-alistp))
        :mode :program ;ev-fncall-w
        :doc "take intersection of types in the type alist")
; no duplicate keys. A1's ordering is used, it has to contain all the
; variables that the user wants in his final type-alist
; A1 and A2 and the return value have type
; (listof (cons symbolp (listof possible-defdata-type-p)))
; TODO: if val has more than 1 type, then we treat it as (list 'ALL)

; Usually its called with A1 as the acl2 type alist and A2 as the
; top-level type alist. so it might contain
; variables thats have been dest-elimed away
  (f* ((get-type... (types) (if (and (consp types)
                                     (null (cdr types)))
                                (car types)
                              (prog2$
                               (cw? (verbose-stats-flag vl)
                                    "~|CEGen/Warning: Ignoring rest of union types ~x0 ~|" (cdr types))
                               (car types))))
         (eval-and-get-meet (typ1 typ2) ;(quoted-constant sym)|(sym quoted-constant)
                            (b* (((mv dt st) (if (is-a-variablep typ1)
                                                 (mv typ1 typ2)
                                               (mv typ2 typ1)))
                                 (P (get-predicate-symbol dt))
                                 ;; args to ev-fncall-w is a list of evaluated values.
                                 ((mv erp res) (acl2::ev-fncall-w P (list (if (quotep st) ;possible bug caught, what if st is not quoted!
                                                                              (acl2::unquote st)
                                                                            st)) 
                                                                  wrld nil nil t nil nil))
                                 (- (cw? (and erp (debug-flag vl))
                                         "~|CEgen/Error in ~x0: while calling ev-fncall-w on ~x1~|" ctx (cons P (list st))))
                                 (- (cw? (and (not erp) (not res) (debug-flag vl))
                                         "~|CEgen/Debug:: ~x0 evaluated to nil~|" (cons P (list st))))
                                 ((when erp)
                                  (mv t 'acl2::empty)))
                              (if res (mv nil st) (mv nil 'acl2::empty)))))
  (if (endp A1)
      (mv nil '())
    (b* (((cons var types1) (car A1))
         (typ1 (get-type... types1))
         (ctx 'meet-type-alist)
         (types2-entry (assoc-eq var A2))
         (types2 (if types2-entry (cdr types2-entry) '(ACL2::ALL)))
         (typ2 (get-type... types2))
         ((unless (and (possible-defdata-type-p typ1) 
                       (possible-defdata-type-p typ2)))
          (mv t '()))
         ((mv erp rest) (meet-type-alist (cdr A1) A2 vl wrld R$ types-ht$))
         ((when erp) (mv t '())))

      (cond ((and (is-a-variablep typ1) (is-a-variablep typ2))
             (mv nil (acons var (list (meet typ1 typ2 vl wrld R$ types-ht$)) rest)))

            ((and (is-singleton-type-p typ1)
                  (is-singleton-type-p typ2)
                  (equal typ1 typ2))
             (mv nil (acons var (list typ1) rest)))

            ((and (is-singleton-type-p typ1)
                  (is-singleton-type-p typ2))
             (mv nil (acons var (list 'acl2::empty) rest)))

            (t
             (b* (((mv erp ans) (eval-and-get-meet typ1 typ2)))
               (mv erp (acons var (list ans) rest)))))))))


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

(def clausify-hyps-concl (hyps concl)
  (decl :sig ((pseudo-term-list pseudo-term)
              -> clause)
        :doc "given hyps concl which are proper terms return equivalent
  clause cl. inverse of clause-mv-hyps-concl")
  (cond ((and (endp hyps) (equal concl ''NIL)) 'NIL)
        ((endp hyps) (list concl))
        ((endp (cdr hyps)) (list (dumb-negate-lit (car hyps)) concl))
        (t (append (dumb-negate-lit-lst hyps)
                   (list concl)))))


(def ss-stats (ss-temp-result old-run-hist%)
  (decl :sig (((list booleanp run-hist% gcs%) run-hist%) -> all)
        :doc "print some stats about this run of simple-search")
  (b* (((list stop? run-hist% &) ss-temp-result)
       (new-num-cts (access run-hist% |#cts|))
       (old-num-cts (acl2::access run-hist% old-run-hist% :|#cts|))
       (new-num-wts (access run-hist% |#wts|))
       (old-num-wts (acl2::access run-hist% old-run-hist% :|#wts|))
       (new-total (+ new-num-cts (access run-hist% |#vacs|) new-num-wts (access run-hist% |#dups|)))
       (old-total (+ old-num-cts (acl2::access run-hist% old-run-hist% :|#vacs|) old-num-wts (acl2::access run-hist% old-run-hist% :|#dups|)))
       (found-wts (- new-num-wts old-num-wts))
       (found-cts (- new-num-cts old-num-cts))
       (n (- new-total old-total))
       (- (cw? t
               "~|CEgen/Stats/simple-search: ~x0/~x1 cts/wts found in this run (~x2 tests)!~|" found-cts found-wts n))
       (- (cw? t
               "~|CEgen/Stats/simple-search: *END* Stopping condition: ~x0~%~%" stop?)))
    nil))
       

;; 1st April 2013 Fix
;; You cannot trust make-event to give the right result
;; through trans-eval. Just use a state temp global.
;; This bug manifests, when you use (skip-proofs ....)

(def simple-search (name 
                    hyps concl vars partial-A 
                    type-alist tau-interval-alist mv-sig-alist
                    run-hist% gcs%
                    N vl sm programp incremental-flag?
                    ctx wrld state)
  (decl :sig ((string pseudo-term-list pseudo-term symbol-list symbol-doublet-listp
                symbol-alist symbol-alist symbol-alist
               run-hist% gcs% fixnum fixnum keyword boolean boolean
               symbol plist-world state) 
              -> (mv erp (list boolean run-hist% gcs%) state))
        :mode :program
        :doc 
        "
Use :simple search strategy to find counterexamples and witnesses.

* What it does
  1. if form has no free variables exit with appropriate return val o.w
  2. make hypotheses-val conclusion-val,  attach them
  3. take intersection of acl2 type-alist with top-level one from gcs%.
  4. make next-sigma defun and attach it
  5. call run-tests!.
  6. store/record information (run-hist%,gcs%) and 
     returns (list stop? run-hist% gcs%) where stop? is T when
     stopping condition is satisfied.
")
  
  (if (endp vars)
      ;;dont even try trivial forms like constant expressions
      (b* ((form  `(implies (and ,@hyps) ,concl))
            ((mv erp c state)
             (trans-eval-single-value form ctx state))
            ((mv run-hist% gcs%)
             (record-testrun. (if c :witness :counterexample)
                              partial-A
                              run-hist% gcs%)))

;       in
        (prog2$
         (if partial-A
             (cw? (verbose-flag vl)
              "~%CEgen/Note: No point in searching ~x0; it evals to const ~x1 under ~x2~|" name c partial-A)
             (cw? (verbose-flag vl)
              "~%CEgen/Note: No point in searching ~x0; it evals to const ~x1~|" name c))
         (mv erp (list NIL run-hist% gcs%) state)))

;ELSE ATLEAST ONE VARIABLE
  (b* ((- (assert$ (consp vars) 'simple-search))
       (- (cw? (verbose-flag vl) "~%~%"))
       (- (cw? (verbose-stats-flag vl) 
               "~|CEgen/Stats/simple-search:: *START*~|"))
       (hyp-val-defuns   (make-hypotheses-val-defuns hyps vars mv-sig-alist))
       (concl-val-defuns (make-conclusion-val-defuns concl vars mv-sig-alist))
       (- (cw? (system-debug-flag vl) 
               "~%~%~x0 **SYSTEM-DEBUG** hyp/concl defuns: ~| ~x1 ~x2~|" 
               name hyp-val-defuns concl-val-defuns))
       (top-vt-alist (access gcs% top-vt-alist))

       ((mv erp0 tr-res state)
        (trans-eval `(mv-list 2 (meet-type-alist ',type-alist ',top-vt-alist ',vl ',wrld R$ types-ht$))
                    ctx state t))
       ((when erp0)
        (mv t (list nil run-hist% gcs%) state))
       ((list erp type-alist) (cdr tr-res))
       ((when erp)
        (prog2$
         (cw? (normal-output-flag vl)
              "~|CEgen/Error: Type intersection failed. Skip searching ~x0.~%" name)
         (mv t (list NIL run-hist% gcs%) state)))

       ((mv erp0 tr-res state) ;matt's tip
        (trans-eval `(mv-list 3 
                              (make-next-sigma-defuns ',hyps ',concl 
                                                      ',vars ',partial-A 
                                                      ',type-alist ',tau-interval-alist
                                                      ',vl ',wrld R$ types-ht$))
                    ctx state t))
       ((when erp0)
        (mv t (list nil run-hist% gcs%) state))
       ((list erp next-sigma-defuns disp-enum-alist) (cdr tr-res))
       ((when erp)
        (prog2$ 
           (cw? (normal-output-flag vl)
                "~|CEgen/Error: Couldn't determine enumerators. Skip searching ~x0.~|" name)
           (mv t (list nil run-hist% gcs%) state)))

       (- (cw? (system-debug-flag vl) "~%*** next-sigma : ~| ~x0~|" next-sigma-defuns))
       (rseed. (getseed state))
       ;;initialize temp result
       ((er &) (assign ss-temp-result (list nil run-hist% gcs%)))
       
       (- (cw? (verbose-flag vl) 
"~|CEgen/Note: Enumerating ~x0 with ~x1~|" name disp-enum-alist))
; print form if origin was :incremental
       (cl (clausify-hyps-concl hyps concl))
       (pform (acl2::prettyify-clause cl nil (w state)))
       (- (cw? (and incremental-flag?
                    (verbose-flag vl)) "~| incrementally on ~x0 under assignment ~x1~%" pform partial-A))

       (call-form   
        `(acl2::state-global-let*
          ((acl2::guard-checking-on ,(if programp :none nil)))
          (b* (((mv stop? rseed. run-hist% gcs%)
                (run-tests. ,N ,sm ,vl ',vars
                            ,rseed. ',run-hist% ',gcs%))
               (state (putseed rseed. state)))
           (er-progn 
             (assign ss-temp-result (list stop? run-hist% gcs%))
             (value '(value-triple :invisible))))))

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
; dont even think of nested testing (nested waterfall call to test checkpoint)
                    (acl2s-defaults :set testing-enabled nil)
                    
                    ;; added 2nd May '12. Why leave out program context
                    
                    ,@(and programp '((program)))
                    
                    ,@hyp-val-defuns
                    ,@concl-val-defuns
                    ,@next-sigma-defuns
; Jan 8th 2013 - program mode doesnt work anymore since
; we dont have trust tags and skip-checks in place, lets
; fix it here.
                    ,@(and programp '((defttag :testing)))
; Note: all of these defuns are non-recursive and guards not verified, so
; none of these events will cause a call to prove (we hope)
; This is an important observation, since we rely on test-checkpoint
; computed hint to do testing which will get called on every call to prover.
; Thus we might pollute our globals (recorded testing information to print)
; if we make unexpected (prove ...) calls. Update 09/28/12 the above call to
; disable testing should guarantee that test-checkpoint will not be called
; again.

; Update Sep 27th 2012
; Folllowing a helpful email by Matt, found a way to fool the function
; to be guard verified, by wrapping its call in an ec-call
; This way I also get rid of the trust tag .... Hurrah!!
; Update Jan 8th 2013, but have to bring back the ttag and skip-checks for
; program mode testing :((
                    ,@(if programp
                          '((defattach (hypotheses-val hypotheses-val-current-gv) :skip-checks t)
                            (defattach (conclusion-val conclusion-val-current-gv) :skip-checks t)
                            (defattach (next-sigma next-sigma-current-gv) :skip-checks t))
                        '((defattach (hypotheses-val hypotheses-val-current-gv))
                          (defattach (conclusion-val conclusion-val-current-gv))
                          (defattach (next-sigma next-sigma-current-gv))))
 
                   ,@(and programp '((defttag nil)))
                    
                    ,call-form))
                  )
                ctx state T)
    (declare (ignore trval))
    (prog2$
     (and (verbose-stats-flag vl)
          (ss-stats (@ ss-temp-result) run-hist%))
     (mv erp (@ ss-temp-result) state))))))


(def select (terms debug)
  (decl :sig ((pseudo-term-list boolean) 
              -> symbol)
        :doc "choose the variable with least dependency. Build a dependency
  graph, topologically sort it and return the first sink we find.")
;PRECONDITION: (len vars) > 1
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
(def assign-value (x |#assigns| cs% partial-A sm vl ctx wrld state R$ types-ht$)
  (decl :sig ((symbol fixnum cs% symbol-doublet-listp
                      sampling-method fixnum symbol plist-world state R$ types-ht$)
              -> (mv erp (list pseudo-term keyword fixnum) state))
        :mode :program
        :doc "assign a value to x. Infer type constraints from hyps, get the
enumcall for x. trans-eval enumcall to get value to be assigned to x. quote it
to obtain a term. return (mv val :decision i+1), if size of type attributed to
x is greater than 1, otherwise return (mv val :implied i) where i= #assigns
made to x already.")
  (f* ((_eval-single-value (call)
              (b* ((vexp (if partial-A 
                             `(let ,partial-A 
                                (declare (ignorable ,@bound-vars))
                                  ,call) 
                           call))
                   (- (cw? (debug-flag vl) 
                           "~|CEgen/Debug/incremental:  ASSIGN ~x0 := eval[~x1]~|" x  vexp)))
                (trans-eval-single-value vexp ctx state))))

  (b* ((- (assert$ (cs%-p cs%) 'assign-value))
       (bound-vars (strip-cars partial-A))
       ((mv size calls) (cs%-enumcalls cs% ctx wrld R$ types-ht$ bound-vars))
       
       (seed. (getseed state))
       ((mv erp seed. ans state)
        (case sm
             (:uniform-random 
              (b* (((mv m seed.) (random-index-seed *recursive-uniform-enum-measure* seed.))
                   (call `(acl2::mv-list 2 ;arity -- pete caught this missing arity on 17 July '13
                               (let ((seed. ,seed.))
                                 ,(subst m 'm (second calls)))))
                   ((mv erp ans2 state) (_eval-single-value call)))
                (mv erp (cadr ans2) (car ans2) state)))
                   
             (otherwise
              (b* (((mv r seed.) (random-natural-seed seed.))
                   (call (subst r 'r (first calls)))
                   ((mv erp ans state) (_eval-single-value call)))
                (mv erp seed. ans state)))))
       ((when (or erp (equal size 0))) (mv t nil state)) ;signal error
        
       (state (putseed seed. state))
       (val-term       (kwote ans)))
   (if (equal size 1) ;size=0 is not possible, also size can be T (inf)
       (value (list val-term :implied |#assigns|))
     (value (list val-term :decision (1+ |#assigns|)))))))

;copied from tools/easy-simplify.lisp (by sol swords)
(defun easy-simplify-term1-fn (term hyps hints equiv
                              normalize rewrite
                              repeat
                              backchain-limit
                              state)
  (declare (XargS :mode :program :stobjs state))
  (b* ((world (w state))
       
       ((er hint-settings)
        (acl2::translate-hint-settings
         'simp-term "Goal" hints 'easy-simplify-term world state))
       (ens (acl2::ens state))
       (base-rcnst
        (acl2::change acl2::rewrite-constant
                acl2::*empty-rewrite-constant*
                :current-enabled-structure ens
                :force-info t))
       ((er rcnst)
        (acl2::load-hint-settings-into-rcnst
         hint-settings base-rcnst nil world 'easy-simplify-term state))
       (ens (acl2::access acl2::rewrite-constant rcnst :current-enabled-structure))
       ((mv flg hyps-type-alist ?ttree)
        (acl2::hyps-type-alist hyps ens world state))
       ((when flg)
        (mv "Contradiction in the hypotheses"
            nil state))
       ((mv ?step-limit new-term ?new-ttree state)
        (acl2::pc-rewrite*
         term hyps-type-alist
         (if (eq equiv 'acl2::equal)
             nil
           (list (acl2::make acl2::congruence-rule
                       :rune acl2::*fake-rune-for-anonymous-enabled-rule*
                       :nume nil
                       :equiv equiv)))
         (eq equiv 'acl2::iff)
         world rcnst nil nil normalize rewrite ens state
         repeat backchain-limit
         (acl2::initial-step-limit world state))))
    (value new-term)))

(def simplify-term (term hyps hints state)
  (decl :sig ((pseudo-term pseudo-term-list true-list state) 
              -> (mv erp pseudo-term state))
        :mode :program
        :doc "simplify term under hyps. erp is T if hyps have a contradiction
  in them. return the simplifed term in error triple")
  (easy-simplify-term1-fn term hyps hints 'acl2::equal 't 't 1000 1000 state))



; TODO: WHat will happen if some variable gets elided during this
; simplifcation?  Then our code breaks, especially rem-vars logic and capturing
; full assignment.

(def simplify-hyps1-under-assignment (rem-hyps init-hyps x a hints ans. vl state)
  (decl :sig ((pseudo-term-list pseudo-term-list symbol quoted-constant true-list pseudo-term-list bool state)
              -> (mv erp pseudo-term state))
        :mode :program
        :doc "simplify each hyp in rem-hyps assuming init-hyps (minus
  hyp), accumulate in ans. and return a value triple containing shyps
  and an error triple if a contradiction is found in an syhp")
  (if (endp rem-hyps)
      (value ans.)
    (b* ((hyp         (car rem-hyps))
         (other-hyps  (remove1-equal hyp init-hyps))
         ((er shyp)   (simplify-term hyp other-hyps hints state))
         (simplified? (term-order shyp hyp))
         ((when (equal shyp ''nil)) ;contradiction
          (mv T ans. state))
; 27th Aug '12. FIXED a bug in testing-regression.lsp. In incremental mode
; the assert$ that x should not be in the free vars of the conjecture
; was being violated because I was naively checking against term-order.
; But in the case of small-posp, the type assumptions that could have been
; brought to ACL2's attention using compound-recognizer rules were hidden
; leading to a big IF term being generated in shyp.
; SO now if the above happens(I should give a warning here), at the very
;  least I subst the assignment in hyp.
         (- (cw? (and (system-debug-flag vl) 
                      (not simplified?))
             "~|ACHTUNG: simplify-hyps result not less than hyp in term-order~|"))
         (shyp (if simplified? shyp (subst a x hyp))))
     
      (simplify-hyps1-under-assignment 
       (cdr rem-hyps) init-hyps x a hints
       (if (equal shyp ''t) ans.
         (append ans. (list shyp))) ;dont mess with order
       vl state))))

(def simplify-hyps-under-assignment (hyps x a vl state)
  (decl :sig ((pseudo-term-list symbol quoted-constant boolean state) 
              -> (mv erp pseudo-term-list state))
        :mode :program
        :doc "simplify hyps assuming x=a. return shyps in an error
        triple. erp=T if contradiction found in shyps")
  (b* ((eq-hyp (list 'acl2::equal x a)) ;variable comes first
      ((er shyps1) (simplify-hyps1-under-assignment hyps (list eq-hyp) x a '() '() vl state)))
;I do the above and then again simplify to get order-insensitive list of
;simplified hypotheses i.e the order of the hyps in the argument should not
;change the result of this function.
   (simplify-hyps1-under-assignment shyps1 (cons eq-hyp shyps1) x a '() '() vl state)))
                      
(def propagate (x a hyps concl vl state)
  (decl :sig ((symbol pseudo-term ;actually a quoted constant
                      pseudo-term-list pseudo-term fixnum state)
              -> (mv erp (list pseudo-term-list pseudo-term) state))
        :mode :program
        :doc "propagate the assignment of a to variable x by using a utility
  function from tools/easy-simplify.lisp (earlier I was using
  expander.lisp). return (mv erp (shyps sconcl) state) where erp might be T
  indicating discovery of inconsistency/contradiction in the hypotheses")
 (b* (((er shyps)  (simplify-hyps-under-assignment hyps x a vl state))
;IMP: sconcl shud be a pseudo-term; not a term-list, or an IF
      (- (cw? (debug-flag vl)
"~|CEGen/Debug/Propagate: ~x0 ---~x1=~x2--> ~x3~|" hyps x a shyps))
      (eq-hyp (list 'equal x a)) ;variable comes first
      ((er sconcl) (simplify-term concl (cons eq-hyp shyps) nil state))
      (- (cw? (debug-flag vl)
"~|CEGen/Debug/Propagate: ~x0 ---~x1=~x2--> ~x3~|" concl x a sconcl))
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
  (assert$ (not (member-eq x vars)) (mv NIL (list vars shyps sconcl) state))))
                  

(defun put-val-A (name val dlist) ;use mset instead?
  (declare (xargs :guard (symbol-doublet-listp dlist)))
  (cond ((endp dlist) (list (list name val)))
        ((equal name (caar dlist))
         (cons (list name val) (cdr dlist)))
        (t (cons (car dlist)
                 (put-val-A name val (cdr dlist))))))

;; (def update-A-after-propagate (x a new-vars old-vars A.)
;;   (decl :sig ((symbol quoted-constant symbol-list symbol-list symbol-doublet-list) -> symbol-doublet-list)
;;         :doc "A[x]:=a, for elimed-vars do y:='?." ;TODO: use bindings-lst from ttree like we do elsewhere.
;;         )
;;   (b* ((elimed-vars (remove-duplicates-eq (set-difference-eq old-vars (cons x new-vars))))
;;        (A. (put-val-A x a A.)) ;use (mset x (list a) A) instead?
;;        (rst (pairlis$ elimed-vars (make-list (len elimed-vars)
;;                                              :initial-element 
;;                                              (list (kwote 'ACL2::?))))))
;;     (append rst A.)))
    



; a% represents the snapshot of the beginning of the dpll do-while loop
(defrec a% ((hyps concl vars partial-A type-alist tau-interval-alist) ;args to simple search
            ((var . cs) val kind i . inconsistent?) ;result of assign and propagate
            ) 
  NIL)
;Take special note of field names: run-hist and gcs, % is intentionally not
;used in these field names
(defun a%-p (v)
  (declare (xargs :guard T))
  (case-match v
    (('a% (hyps concl vars partial-A type-alist tau-interval-alist) 
          ((var . cs) val kind i . inconsistent?))

     ;==>
     (and (symbol-listp vars)
          (pseudo-term-listp hyps)
          (pseudo-termp concl)
          (symbol-doublet-listp partial-A)
          (symbol-alistp type-alist)
          (symbol-alistp tau-interval-alist)
          (symbolp var)
          (pseudo-termp val)
          (member-eq kind (list :na :implied :decision))
          (natp i)
          (booleanp inconsistent?)
          (or (null cs) (cs%-p cs))
          ))))
                                   
(defun a%-listp (v) ;STACK
  (declare (xargs :guard T))
  (if (atom v)
      (null v)
    (and (a%-p (car v))
         (a%-listp (cdr v)))))



;TODO- prove a theorem that the above two fns are inverses


; defabbrev was a BAD idea. I should make this a defun, to avoid variable
; capture bugs. For example I was assigning .. :var x ... instead of :var x1
; below, where x would have been the previously selected variable and unless I
; tested carefully I would not have gotten hold of this simple programming err.
; May 24th '12: making this into a defun
; 18 July '13 -- modified to a simplified signature
(def assign-propagate (a% name sm vl ctx wrld state R$ types-ht$)
  (decl :sig ((a% string sampling-method 
                  fixnum symbol plist-world state R$ types-ht$)
              -> (mv erp (list pseudo-term-list pseudo-term symbol-list 
                               symbol-doublet-list symbol-alist symbol-alist a%) state))
        :mode :program
        :doc "assign a value to a%.x and propagate this new info to obtain the updated a%")
  (b* ((`(a% ,LV . &) a%)
;ACHTUNG: a% defrec exposed
        ((list H C vars partial-A type-alist tau-interval-alist) LV)
        ((mv x i) (mv (access a% var) (access a% i)))
        (cs% (or (access a% cs)
                 (assert$ (member-eq x vars)
                          (cdr (assoc-eq x (collect-constraints% 
                                             H vars type-alist tau-interval-alist
                                             vl wrld R$ types-ht$))))))
;DESIGN decision: not taking into account type constraint from nconcl at the moment.
       
       ((mv erp ans state) (assign-value x i cs% partial-A sm vl ctx wrld state R$ types-ht$))
       ((when erp)
        (progn$
         (cw? (normal-output-flag vl)
              "~|CEGen/Error/incremental: assign-value failed (in ~s0).~|" name)
         (cw? (verbose-stats-flag vl)
              "~|CEGen/Stats: Call was (assign-value ~x0 ~x1 ~x2 ...)~|" x i cs%)
         (mv erp nil state)))
        
       ((list a kind i) ans)

       (a% (acl2::change a% a% :cs cs% :val a :kind kind :i i))
       
       ((mv erp res state) (propagate x a H C vl state))
       (str (if erp "inconsistent" "consistent"))
       (- (cw? (verbose-stats-flag vl)
               "~%CEgen/Stats/incremental: Propagate ~x0 := ~x1 (i:~x3) was ~s2.~|" x a str i)))

; But do update i in a% always, and partial-A when consistent
   (if erp 
       (value (list  '() ''t '() '() '() '() ;is it ok to give back empty alists?
                 (acl2::change a% a% :inconsistent? T)))
     ;else 
     (b* (((list vars~ H~ C~) res)
          (cl~ (clausify-hyps-concl H~ C~))
          (ens (acl2::ens state))
          (name~ (acl2::concatenate 'acl2::string name " incremental " (to-string x) " i=" (to-string i)))
          (type-alist~ (get-acl2-type-alist cl~ name~ ens vl state))
          (tau-interval-alist~ (tau-interval-alist-clause cl~ name~ ens vl wrld state))
          (- (cw? nil "~% new ta = ~x0 and old ta = ~x1~%" type-alist~ type-alist))
          (- (cw? nil "~% new tau-int-alist = ~x0 and old tau-int-alist = ~x1~%" tau-interval-alist~ tau-interval-alist))
          (partial-A~  (put-val-A x a partial-A)) ; partial-A is a symbol-doublet-listp
          )
       

       (value (list H~ C~ vars~ partial-A~ type-alist~ tau-interval-alist~
                     (acl2::change a% a%
                                   :inconsistent? NIL)))))))


;mutually tail-recursive incremental (dpll) search prodecure
(defs 
  (incremental-search (a% A. 
                          name  mv-sig-alist ;subgoal params
                          run-hist% gcs%
                          N vl sm blimit programp
                          ctx wrld state)

; INVARIANTS: 
; - vars has at least 1 variable
; - A. is a stack of consistent a% whose run-hist,gcs fields
;   contain the sigma whose values agree with partial-A for
;   the common variables
;   

; - a% is a snapshot. its occurs in 2 stages/forms. in the first stage
;   it stores H,C,vars,partial-A, type-alist,tau-interval-alist
;   and x just after a SELECT.
;   It then gets updated by a consistent assign_propagate call.
;   updated fields: a,kind,i,cs% and inconsistent? flag
;   Finally the run-hist and gcs fields simply threaded through and through

; - vars is disjoint with vars of partial-A stored in top of stack A.
    (decl :sig ((a% a%-listp 
                 string  symbol-alist
                 run-hist%-p gcs%-p
                 fixnump fixnump (in :random :uniform-random :be :mixed) fixnump booleanp
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

    (f* ((simple-search... () (simple-search name 
                                             H C vars partial-A type-alist tau-interval-alist
                                             mv-sig-alist
                                             run-hist% gcs%
                                             N vl sm programp t
                                             ctx wrld state))
         (backtrack... () (backtrack a% A.
                                     name mv-sig-alist
                                     run-hist% gcs%
                                     N vl sm blimit programp
                                     ctx wrld state))
         
         (recurse... () (incremental-search a% A.
                                            name mv-sig-alist
                                            run-hist% gcs%
                                            (floor N (1+ (len A.))) ;geometrically decrease num of trials TODO revisit
                                            vl sm blimit programp
                                            ctx wrld state)))

      (b* (((mv erp ap-res state) ;snapshot a% moves to second stage/form
            (trans-eval `(assign-propagate ',a% ',name ',sm ',vl ',ctx ',wrld state R$ types-ht$)
                        ctx state t))
           ((when erp) ;error in assign value
            (prog2$
             (cw? (normal-output-flag vl)
                  "~|CEGen/Error: Aborting incremental search!~|")
             (mv T (list NIL run-hist% gcs%) state)))
           ((list H C vars partial-A type-alist tau-interval-alist a%) (cadr (cdr ap-res))))
      

;       in
        (if (not (access a% inconsistent?))
           (b* (((mv erp (list stop? run-hist% gcs%) state)
                 (simple-search...))
                ((when (or erp stop?))
; if theres an error or if we reach stopping condition, simply give up search
                 (mv erp (list stop? run-hist% gcs%) state))

                ((when (or (endp vars)
                           (endp (cdr vars)))) 
                 (backtrack...));no luck with :simple, lets backtrack and try again
                 
                (A. (cons a% A.))
; ok lets set up a% for the next iteration
                (x1 (select (cons (dumb-negate-lit C) H) (debug-flag vl)))
                (a% (acl2::make a% 
                                :vars vars :hyps H :concl C 
                                :partial-A partial-A
                                :type-alist type-alist
                                :tau-interval-alist tau-interval-alist
                                :inconsistent? nil :cs nil
                                :var x1 :val ''? :kind :na :i 0)))
;           in
            (recurse...))


;      ELSE inconsistent (i.e oops a contradiction found in hyps)
         
         (backtrack...)))))
           
 
; sibling procedure in clique
  (backtrack (a% A. 
                 name mv-sig-alist
                 run-hist% gcs%
                 N vl sm blimit programp
                 ctx wrld state)
; when called from incremental, either contradiction in hyps[x=a] or simple-search failed on P of zero/one variable
    (decl :sig (( a%-p a%-listp 
                 string symbol-alist
                 run-hist%-p gcs%-p
                 fixnum fixnum (in :random :uniform-random :be :mixed) fixnum boolean
                 symbol plist-world state) 
                -> (mv erp (list boolean run-hist% gcs%) state))
         :mode :program
         :doc "backtrack in dpll like search")
   
    (if (or (eq (access a% kind) :implied) 
            (> (access a% i) blimit)) 
        (if (null A.)
;       THEN - error out if x0 exceeds blimit
            (prog2$
             (cw? (verbose-stats-flag vl)
"~|CEGen/Note: Incremental search failed to even satisfy the hypotheses.~|")
            (value (list NIL run-hist% gcs%)))
;       ELSE throw away this a%
          (b* ((a% (car A.))
               (x (access a% var))
               (- (cw? (verbose-stats-flag vl)
"~|CEGen/Stats/incremental:  Backtrack to var : ~x0 -- i = ~x1~|" x (access a% i)))) 
           (backtrack a% (cdr A.) ;pop stack
                      name mv-sig-alist
                      run-hist% gcs%
                      N vl sm blimit programp
                      ctx wrld state)))

;     ELSE a% has a decision which has not reached its backtrack limit
      (incremental-search a% A. 
                          name mv-sig-alist
                          run-hist% gcs%
                          (floor N (1+ (len A.)))
                          vl sm blimit programp
                          ctx wrld state))))




;;; The Main counterexample/witness generation function           
(def cts-wts-search (name H C vars 
                          type-alist tau-interval-alist mv-sig-alist
                          programp defaults 
                          run-hist% gcs%
                          ctx wrld state)
  (decl :sig ((string pseudo-term-list pseudo-term symbol-list
                      symbol-alist symbol-alist symbol-alist
                      boolean symbol-alist 
                      run-hist%-p gcs%-p
                      symbol plist-world state)
              -> (mv erp (list boolean s-hist gcs%) state))
        :mode :program
        :doc 
;Note: It does not update the global values @gcs% and @s-hist.
"
* Synopsis       
  Local interface to subgoal-level counterexample and witness
  search using either naive testing or incremental dpll
  style search for counterexamples.

* Input parameters
  - first 8 params other than vars, see def csearch
  - vars :: free variables of (H=>C) in dependency order
  - run-hist% :: newly created run-hist% for this subgoal
  - gcs% :: global gcs%
  - rest see def csearch

* Output signature 
  - (mv erp (list stop? run-hist% gcs%) state) where erp is the error tag which is non-nil
    when an error took place during evaluation of (search ...). 
    stop? is T if we should abort our search, i.e our stopping
    condition is satisfied (this value is given by run-tests), 
    otherwise stop? is NIL (by default). run-hist% and gcs% are 
    accumulated in the search for cts and wts in the current conjecture

* What it does
  1. retrieve the various search/testing parameters

  2. call simple or incremental search
     depending on the search-strategy set in defaults.
  
  3. return error triple with value (list stop? run-hist% gcs%)
")

  
  (b* ((N (get-acl2s-default 'num-trials defaults 0)) ;shudnt it be 100?
;Note: I dont need to provide the default arg 0 above, since we are
;sure the defaults alist we get is complete i.e it would definitely
;contain the key 'num-trials'. But I am envisioning a scenario, where
;I might call this function on its own and not via test?, then this
;functionality is useful for debugging.
       (vl (get-acl2s-default 'verbosity-level defaults 1))
       (sm (get-acl2s-default 'sampling-method defaults :random))
       (ss (get-acl2s-default 'search-strategy defaults :simple))
       (blimit (get-acl2s-default 'backtrack-limit defaults 2)))
  
;   in
    (case ss ;search strategy
      (:simple      (simple-search name 
                                   H C vars '()
                                   type-alist tau-interval-alist mv-sig-alist
                                   run-hist% gcs% 
                                   N vl sm programp nil
                                   ctx wrld state))
      

      (:incremental (if (or (endp vars)
                            (endp (cdr vars)))
;bugfix 21 May '12 - if only one or zero var, call simple search
                        (simple-search name
                                       H C vars '()
                                       type-alist tau-interval-alist mv-sig-alist
                                       run-hist% gcs% 
                                       N vl sm programp nil
                                       ctx wrld state)
                      
                      (b* ((- (cw? (verbose-stats-flag vl) 
                                   "~%~%CEgen/Note: Starting incremental (dpll) search~%"))
                           (x0 (select (cons (dumb-negate-lit C) H) (debug-flag vl)))
                           (a% (acl2::make a% ;initial snapshot
                                           :vars vars :hyps H :concl C 
                                           :partial-A '()
                                           :type-alist type-alist
                                           :tau-interval-alist tau-interval-alist
                                           :inconsistent? nil :cs nil
                                           :var x0 :val ''? :kind :na :i 0)))
;                         in
                        (incremental-search a% '() ;vars has at least 2
                                            name mv-sig-alist
                                            run-hist% gcs%
                                            N vl sm blimit programp
                                            ctx wrld state))))
      
      
      (otherwise (prog2$ 
                  (cw? (normal-output-flag vl)
                       "~|CEgen/Error: Only simple & incremental search strategy are available~|")
                  (mv T NIL state))))))

   

           
  


(def csearch (name H C 
                   type-alist tau-interval-alist 
                   mv-sig-alist elide-map 
                   programp defaults 
                   ctx wrld state)
  (decl :sig ((string pseudo-term-list pseudo-term 
                      symbol-alist symbol-alist 
                      symbol-alist symbol-alist
                      boolean symbol-alist
                      symbol plist-world state)
              -> (mv erp boolean state))
        :mode :program
        :doc 
"
* Synopsis       
  Main Interface to searching for counterexamples (and witnesses)
  in the conjecture (H => C)

* Input parameters
  - name :: name of subgoal or 'top if run from test?
  - H :: hyps - the list of terms constraining the cts and wts search
  - C :: conclusion
  - type-alist :: types inferred by ACL2 forward-chain
  - mv-sig-alist :: for each mv fn, stores its output arity
  - elide-map :: elide-map[v] = term for each elided variable v
  - programp :: T when form has a program mode fun or we are in :program
                Its only use is for efficiency. We use guard-checking :none
                for programp = T and nil otherwise, which is more efficient.
  - defaults :: alist overiding the current acl2s-defaults
  - ctx :: usually the top-level form which employed this procedure
  - wrld :: current acl2 world
  - state :: state

* Output signature 
  - (mv erp stop? state) where erp is the error tag which is non-nil
    when an error took place during evaluation of (search ...). 
    stop? is T if we should abort our search.

* What it does
  1. construct a new s-hist-entry% and call cts.wts.search fun
     with globals @gcs, run-hist% and defaults
  2. the return values of run-hist% (a field in s-hist-entry%), gcs% 
     are recorded in globals @gcs and @s-hist.
  3. return error triple containing stop? (described in simple-search)
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
              (state (put-gcs%-global gcs%)))
          state)))

    (b* (((mv start state) (acl2::read-run-time state))
         (vl (get-acl2s-default 'verbosity-level defaults 1))
         (vars (vars-in-dependency-order H C vl wrld))
         (s-hist-entry% (initial-s-hist-entry% name H C vars 
                                               elide-map start))
         (run-hist% (access s-hist-entry% run-hist))
         (gcs% (get-gcs%-global))
         ((mv erp res state)
          (cts-wts-search name H C vars 
                          type-alist tau-interval-alist mv-sig-alist
                          programp defaults 
                          run-hist% gcs%
                          ctx wrld state))
         ((unless (and (= 3 (len res))
                       (booleanp (first res))
                       (run-hist%-p (second res))
                       (gcs%-p (third res))))
          (prog2$ 
           (cw? (verbose-flag vl)
                "~|CEgen/Error : Bad result from main Cgen procedure!~|")
           (mv T nil state)))
         ((list stop? run-hist% gcs%) res)
         (state (update-cts-search-globals)))
      (mv erp stop? state))))
       
   
(def csearch-with-timeout (name H C 
                                type-alist tau-interval-alist 
                                mv-sig-alist elide-map 
                                programp defaults 
                                ctx wrld state)
  (decl :sig ((string pseudo-term-list pseudo-term 
                      symbol-alist symbol-alist 
                      symbol-alist symbol-alist
                      boolean symbol-alist
                      symbol plist-world state)
              -> (mv erp boolean state))
        :mode :program
        :doc "wrap csearch with a timeout mechanism")
  (acl2::with-timeout1
   (acl2s-defaults :get subgoal-timeout)
   (csearch name H C 
            type-alist tau-interval-alist 
            mv-sig-alist elide-map
            programp defaults ctx wrld state)
   (prog2$
    (cw? (normal-output-flag 
             (get-acl2s-default 'verbosity-level defaults 1))
            "~|Search for counterexamples TIMED OUT! ~
Use (acl2s-defaults :set subgoal-timeout 0) to disable timeout. ~
For more information see :doc subgoal-timeout.~%")
; error flag raised. stop? is set to NIL but it doesnt matter I guess.
    (mv T NIL state)))) ;TODO im losing testing summary here!
               
  
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
  "Sig: clause-id * clause-id -> boolean
   function: Is parent an ancestor of child in the ACL2 proof tree?"
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


(defun collect-replaced-terms (hist ans)
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
               (collect-replaced-terms 
                (cdr hist) (append ans1 ans))))
            ((eq proc 'acl2::eliminate-destructors-clause)
;Destructor elimination
             (let* ((elim-sequence 
                     (acl2::tagged-object 'acl2::elim-sequence ttree))
                    (ans1 (get-dest-elim-replaced-terms elim-sequence)))
               (collect-replaced-terms
                (cdr hist) (append ans1 ans))))
;Else (simplification and etc etc)
            (t (let* ((binding-lst 
                       (acl2::tagged-object 'acl2::binding-lst ttree))
                      (ans1 (convert-conspairs-to-listpairs binding-lst)))
                 (collect-replaced-terms
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




(set-verify-guards-eagerness 0)
(verify-termination acl2::subcor-var1)      
(verify-termination subcor-var)

;expand-lambda : pseudo-termp -> pseudo-termp (without lambdas)
(mutual-recursion
 (defun expand-lambda (term)
   (declare (xargs :guard (pseudo-termp term)))
   (cond ((variablep term) term)
         ((fquotep term) term)
         ((eq (ffn-symb term) 'acl2::hide) term)
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

(def partition-hyps-concl (term str state)
  (decl :mode :program
        :sig ((pseudo-termp stringp state) -> (mv pseudo-term-listp pseudo-termp state))
        :doc "expand lambdas, extracts hyps and concl from term") ;expensive operation
  ;; get rid of lambdas i.e let/let*
  (b* ((term  (expand-lambda term))
       (wrld (w state))
       (pform (acl2::prettyify-clause (list term) nil wrld))
       ((mv phyps pconcl)  (mv (get-hyps pform) (get-concl pform)))
       
       ((er hyps) (acl2::translate-term-lst phyps 
                                            t nil t str wrld state)) 
       ((er concl) (acl2::translate pconcl t nil t str wrld state)))
    (mv hyps concl state)))
                      
(defun get-var-tau-alist (term state)
  (declare (xargs :mode :program :stobjs (state)))
  (b* ((ens (acl2::ens state))
       (wrld (w state))
       ((er term) (acl2::translate term t nil t "get-tau-alist" wrld state))
       ((mv hyps concl state) (partition-hyps-concl term "get-tau-alist" state))
       (cl (clausify-hyps-concl hyps concl))
       (tau-alist (tau-alist-clause cl nil ens wrld state))
       (var-taus-alist (make-var-taus-alist (all-vars term) tau-alist)))
    (mv nil  var-taus-alist state)))

(defun get-tau-interval-alist (term name vl state)
    (declare (xargs :mode :program :stobjs (state)))
    (b* (((er var-taus-alist) (get-var-tau-alist term state))
         (var-tau-interval-alist (tau-interval-alist var-taus-alist))
         (- (cw? (debug-flag vl)
                 "~|CEgen/Debug: tau interval alist (~s0): ~x1~|" name var-tau-interval-alist)))
      (value var-tau-interval-alist)))


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

       ((mv ?er res state) 
        (acl2::state-global-let*
         ((acl2::guard-checking-on :none))
         (trans-eval
          `(let* ,A
             (declare (ignorable ,@(strip-cars A)))
             (list ,top-term
; make list/let A (list `(var ,var) ...) 
                   ,(make-var-value-list-bindings top-vars nil)))
          'get-top-level-assignment state T))) ;defttach ok
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
       ((unless elided-var-map) ;the simple case
        (value (cw? (normal-output-flag vl)
                    "~| -- ~&0~%" top-A)))
  
;show top goal, show counterexamples and witness in 
;terms of the original free variables(of the top clause)
       ((er (list consistent? top-A))
        (get-top-level-assignment A top-vars top-term 
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
; (naive-print-bindings (convert-conspairs-to-listpairs (car bindings-lst))
;                       orig-vars vl)
      (print-assignments (cdr A-lst) top-vars top-term
                          elided-var-map vl counteregp state))))
(logic)


; 30th Aug '12 keep global track of num of wts/cts to print
(def print-cts/wts (s-hist cts-p nc nw top-vars top-term vl state)
  (decl :mode :program
        :sig ((s-hist-p booleanp symbol-listp all natp state) 
              -> (mv erp all state))
        :doc "print all cts/wts A (sigma) in s-hist subgoal testing
        history alist")
  (if (endp s-hist)
      (value nil)
    (b* (((cons name s-hist-entry%) (car s-hist))
         (run-hist% (access s-hist-entry% run-hist))
         (hyps      (access s-hist-entry% hyps))
         (concl     (access s-hist-entry% concl))
         ((when (and cts-p (zp nc)))
; number of cts yet to be printed is zero, skip 
          (value nil))
         ((when (and (not cts-p) (zp nw))) 
; number of wts yet to be printed is zero, skip 
          (value nil))
         
         (A-lst (if cts-p 
                    (access run-hist% cts)
                  (access run-hist% wts)))
         (elide-map (access s-hist-entry% elide-map))
         (- (cw? (debug-flag vl) 
"~|DEBUG/print-cts/wts: A-lst:~x0 top-vars:~x1 elide-map:~x2~|" 
A-lst top-vars elide-map))
         ((when (endp A-lst)) 
; none found, so move on to the next subgoal
          (print-cts/wts (cdr s-hist) cts-p 
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
      (print-cts/wts (cdr s-hist) cts-p nc nw top-vars top-term vl state)))))


(def print-s-hist (s-hist printc? printw? nc nw 
                          top-term top-vars vl state)
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
                    (print-cts/wts s-hist T nc nw top-vars top-term vl state))
                 (value nil)))

       ((er &) (if printw?
                   (prog2$
                    (cw? (normal-output-flag vl)
"~|~%Cases in which the conjecture is true include:~|")
                    (print-cts/wts s-hist NIL nc nw top-vars top-term vl state))
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
      
  

(defun print-testing-summary-fn (vl state)
  (declare (xargs :mode :program
                  :stobjs (state)))
  (b* ((ctx 'print-testing-summary)
;when testing errored out or timed out, theres no point of printing.
       (s-hist (get-s-hist-global))
       (gcs%   (get-gcs%-global))
       (- (cw? (debug-flag vl) "~|testing summary - gcs% = ~x0~%" gcs%))
       (- (cw? (debug-flag vl) "~|testing summary - s-hist = ~x0~%" s-hist))
       ((unless (and (consp s-hist) (consp (car s-hist))
                     (> (access gcs% total-runs) 0)))
        (value (cw? (normal-output-flag vl) 
"~|CEgen/Note: No testing summary to print~|")))
                  
       (num-subgoals (len s-hist))
       
       )
   (case-match gcs%
     (('gcs% (total dups . vacs) 
             (num-cts . num-wts) 
             (cts-to-reach . wts-to-reach) 
             (start . end) & . &)
;ACHTUNG: gcs% defrec exposed
      (b* ((uniq-runs  (my+ num-wts num-cts))
           (sat-runs (my- total (my+ vacs dups)))
           (delta-t-total (my- end start))
           (delta-testing-t-total (total-time-spent-in-testing s-hist))
           (top-term (access gcs% top-term))
           (top-vars (all-vars top-term))
           (pform (acl2::prettyify-clause 
                   (list top-term) nil (w state)))
           ((unless (consp top-vars))
            (b* ((res (if (> num-cts 0) nil t)))
              (value (cw? (normal-output-flag vl) 
"~% ~x0 evaluates to ~x1. Nothing to test!~%" pform res))))

           
           (-  (cw? (normal-output-flag vl) 
                    "~%**Summary of testing**~%"))
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
           
           ((er &)  (print-s-hist s-hist 
                                  (> num-cts 0);print cts if true
                                  (> num-wts 0);print wts if true
                                  cts-to-reach wts-to-reach 
                                  top-term top-vars
                                  vl state)))
       (value nil)))
     (& (value (cw? (normal-output-flag vl) "~|CEgen/Error: BAD gcs% found in globals~|"))))))




;----------------------------------------------------------------
;                         PRINT end                             |
;----------------------------------------------------------------

   
  
(defun cts-wts-search-clause (cl name mv-sig-alist 
                                 ens hist elim-elided-var-map
                                 vl ctx wrld state)
   "helper function for test-checkpoint. It basically sets up 
   everything for the call to csearch."
  (declare (xargs :stobjs (state) :mode :program))
  (b* ((vt-acl2-alst (get-acl2-type-alist cl name ens vl state))
       ((mv hyps concl) (clause-mv-hyps-concl cl))
       (- (cw?  (verbose-stats-flag vl)
              "~|CEgen/Verbose: Search clause with elide-map ~x0 ~ ~x1 ~|" 
              elim-elided-var-map (acl2::prettyify-clause cl nil wrld)))
       (elided-var-map (append (collect-replaced-terms hist nil)
                               elim-elided-var-map))
       ;; Ordering is necessary to avoid errors in printing top-level cts

       (ord-elide-map (do-let*-ordering elided-var-map (debug-flag vl)))
       (defaults (acl2s-defaults-alist))
       (tau-interval-alist (tau-interval-alist-clause cl name ens vl wrld state))
       ((mv erp stop? state)  (csearch name hyps concl 
                                     vt-acl2-alst tau-interval-alist 
                                     mv-sig-alist ord-elide-map 
                                     NIL defaults ctx wrld state)))
    (mv erp stop? state)))


(defun cts-wts-search-clauses (clauses name mv-sig-alist 
                                 ens hist elim-elided-var-map
                                 vl ctx wrld state)
"not used"
  (declare (xargs :stobjs (state) :mode :program))
  (if (endp clauses)
      (mv nil nil state)
    (b* (((mv erp stop? state)
          (cts-wts-search-clause (car clauses) name mv-sig-alist
                                 ens hist elim-elided-var-map 
                                 vl ctx wrld state))
         ((when (or erp stop?))
          (mv erp stop? state)))
      (cts-wts-search-clauses (cdr clauses) name mv-sig-alist
                              ens hist elim-elided-var-map 
                              vl ctx wrld state))))
  



      
(def simplify/throw-hyps-elim1 (rem-hyps elim-hyps hints ans. vl state)
  (decl :sig ((pseudo-term-list pseudo-term-list true-list pseudo-term-list fixnum state)
              -> (mv erp pseudo-term-list state))
        :mode :program
        :doc "easy simplify each implicative hyp in rem-hyps assuming
  elim-hyps, accumulate in ans., we just simplify the antecedent and
  keep it if its simplified to true. if not we throw it, and return a
  value triple containing shyps. return erp=T is found contradiction
  in an shyp. order is preserved.")
  (declare (ignorable vl))
  (if (endp rem-hyps)
      (value ans.)
    (b* ((hyp         (car rem-hyps))
         (implicative? (and (consp hyp)
                            (eq 'acl2::implies (ffn-symb hyp)))))
      (if implicative?
         (b* (((er antecedent)   (simplify-term (second hyp) elim-hyps hints state))
              (ans. (if (or (equal antecedent ''t)
                            ;hack
                            (member-equal antecedent elim-hyps))
                        (append ans. (list (third hyp)))
                      ans.)))
           (simplify/throw-hyps-elim1 (cdr rem-hyps) elim-hyps hints
                                      ans. vl state))
        (b* (((er shyp)   (simplify-term hyp elim-hyps hints state))
              (ans. (if (equal shyp ''t)
                        ans.
                      (if (term-order shyp hyp)
                          (append ans. (list shyp))
                        (append ans. (list hyp))))))
          (simplify/throw-hyps-elim1 (cdr rem-hyps) elim-hyps hints
                                     ans. vl state))))))

(def simplify/throw-hyps-elim (hyps elim-hyps hints vl state)
  (decl :sig ((pseudo-term-list pseudo-term-list true-list fixnum state)
              -> (mv erp pseudo-term-list state))
        :mode :program
        :doc "see simplify/throw-hyps-elim1 doc")
  (b* ((- (time-tracker :simplify-hyps-elim :start))
       ((mv erp shyps state) (simplify/throw-hyps-elim1 hyps elim-hyps hints '() vl state))
       (- (time-tracker :simplify-hyps-elim :stop))
       (- (and (verbose-stats-flag vl)
               (time-tracker :simplify-hyps-elim :print?))))
    (mv erp shyps state)))
  

;eliminable-type-alist is (listof (cons var (list type type-class)))
       
;todo - order
(defun record-eliminable-type-alist (def vars elt wrld ans)
  (if (endp vars)
      ans
    (b* ((?rhs (nth 1 elt))
         (lhs (nth 2 elt)) ;(list rhs lhs) (X (REC1 MT MT0))
         (defbody (cadr def))
         (i (position (car vars) lhs))
         (field-type (nth i defbody))
         (fentry (assoc-eq field-type (table-alist 'defdata::types-info-table wrld)))
         (tc (and (consp fentry)
                  (acl2::access types-info% (cdr fentry) :type-class))))
      (if (equal tc 'record)
          (record-eliminable-type-alist def (cdr vars) elt wrld (acons (car vars) (list field-type tc) ans))
        (if (equal tc 'map) ;maps at the end, records in front
            (record-eliminable-type-alist def (cdr vars) elt wrld (append ans (acons (car vars) (list field-type tc) '())))
          (record-eliminable-type-alist def (cdr vars) elt wrld ans)))))) ;drop non-records
         
 
(defun map-eliminable-type-alist (type vars elt wrld)
  (b* (((list a v x) vars)
       (lhs (nth 2 elt)) ;(list rhs lhs) (X (MSET a v m))
       (entry (assoc-eq type (table-alist 'defdata::types-info-table wrld)))
       (def (car (acl2::access types-info% (cdr entry) :defs))) ;(map1 (oneof nil (mset pc data map1)))
       (defbody (cadr def))
       (`(oneof nil ,mset-def) defbody)
       (ai (position a lhs))
       (a-type (nth ai mset-def))
       (a-entry (assoc-eq a-type (table-alist 'defdata::types-info-table wrld)))
       (vi (position v lhs))
       (v-type (nth vi mset-def))
       (v-entry (assoc-eq v-type (table-alist 'defdata::types-info-table wrld)))
       (a-tc (and (consp a-entry)
                  (acl2::access types-info% (cdr a-entry) :type-class)))
       (ans (acons x (list type 'map) '())) ;give back its rest for furthur map dest-elim
       (ans (if (member-equal a-tc '(record map))
                (acons a (list a-type a-tc) ans)
              ans))
       (v-tc (and (consp v-entry)
                  (acl2::access types-info% (cdr v-entry) :type-class)))
       (ans (if (member-equal v-tc '(record map))
                (acons v (list v-type v-tc) ans)
              ans)))
    ans))
       
        

       
(defun new-eliminable-type-alist (type tc vars elt wrld)
  (case tc
    (record (b* ((entry (assoc-eq type (table-alist 'defdata::types-info-table wrld)))
                 (def (car (acl2::access types-info% (cdr entry) :defs)))) ;(REC1 (REC1 REC0 RATIONAL))
              (record-eliminable-type-alist def vars elt wrld '())))
    (map (map-eliminable-type-alist type vars elt wrld))
    (otherwise '())))



(defun get-disabled-funs-elim-simp (type tc wrld)
  (b* ((?record-conx (strip-cars (table-alist 'defdata::record-constructors wrld)))
       (entry (assoc-eq type (table-alist 'defdata::types-info-table wrld))) ;definitely in the table
       (def (car (acl2::access types-info% (cdr entry) :defs))) ;(REC1 (REC1 REC0 RATIONAL)) or ;(reg (oneof nil (mset nat data reg)))
       (defbody (cadr def))
       (field-types (cond ((equal tc 'record)
                           (cdr defbody)) ;(REC1 REC0 RATIONAL)
                          ((equal tc 'map)
                           (cdr (third defbody)));(oneof nil (mset nat data reg))
                          (t '())))
                           
       (field-preds (get-predicate-symbol-lst field-types)))
    (append nil ;record-conx 
            field-preds)))

       
(defun subst-equal-alist (alist tree)
  (declare (xargs :guard (alistp alist)))
  (if (endp alist)
    tree
    (subst-equal-alist
      (cdr alist)
      (subst-equal (cdar alist) (caar alist) tree))))

#|
(DEFDATA::GET-DEST-ELIM-REPLACED-TERMS
        ((-1 MT1 (MSET MT9 MT10 MIY)
             ((MT8 . MT9)
              ((MGET MT8 MT1) . MT10)
              ((MAP-IDENTITY MT1) . MIY)) . &)
|#
; NOTE: MT8 above needs to be captured in the elided-var-map (binding)
; TODO: get-dest-elim-replaced-terms needs to be fixed for elim rules
; that have extra variables than the eliminable variable
(defun partition-symbol-keys (alist B rest)
  (declare (xargs :guard (alistp alist)))
  (if (endp alist)
      (mv rest B)
    (if (symbolp (caar alist))
        (partition-symbol-keys (cdr alist) (cons (list (caar alist) (cdar alist)) B)  rest)
      (partition-symbol-keys (cdr alist) B (cons (cons (caar alist) (cdar alist)) rest)))))

(defun get-elim-hyps-and-symbol-elided-var-bindings (rule elt)
  (b* ((`(& ,elim-var ,lhs ,dest-sub-alst . &) elt)
       (hyps (acl2::access acl2::elim-rule rule :hyps))
       (hyps (if (and (consp hyps)
                      (eq 'acl2::and (ffn-symb hyps)))
                 (cdr hyps)
               hyps))
       ((mv dest-sub-alst symbol-elided-var-map) (partition-symbol-keys dest-sub-alst '() '()))
       (hyps (subst-equal-alist dest-sub-alst hyps)))
    (mv (subst lhs elim-var hyps) symbol-elided-var-map)))
       

(defun cts-wts-search-clause-elim (cl name mv-sig-alist 
                                           ens hist avoid-vars 
                                           eliminable type tc 
                                           elim-elided-var-map
                                           vl ctx wrld state)
  (declare (xargs :stobjs (state) :mode :program))
  (b* (((mv new-clause new-vars elim-seq-element rule)
        (eliminate-destructors-clause1-cgen eliminable type cl avoid-vars ens wrld))
       ((when (null new-vars)) 
        (prog2$ 
         (cw? (verbose-stats-flag vl)
              "~|CEgen/Stats: Dest elim on (~x0 ~x1) failed~|" eliminable type)
         (mv nil nil cl '() elim-elided-var-map state)))
       (- (cw? (verbose-stats-flag vl)
              "~|CEgen/Stats: Dest elim on (~x0 ~x1) successful~|" eliminable type))
       ;(new-clause (car (last clauses)))
       ((mv hyps concl) (clause-mv-hyps-concl new-clause))
       (disabled (get-disabled-funs-elim-simp type tc wrld))
       (?hints `(:in-theory (disable ,@disabled))) ;dont lose precious type information
       ((mv elim-hyps symbol-elided-bindings) (get-elim-hyps-and-symbol-elided-var-bindings rule elim-seq-element))
       
   
       
       ((mv ?erpp shyps state) (simplify/throw-hyps-elim hyps elim-hyps hints vl state))
       ;(hints `(("Goal" :in-theory (disable ,@record-conx ,@field-preds))))
       ;((mv ?erpp shyps state) (acl2::simp-hyps hyps state hints t nil :term-order))
       (s-new-clause (clausify-hyps-concl shyps concl))
       (name (concatenate 'string name " dest elim on " (symbol-name  eliminable)))
       (elim-elided-var-map (append elim-elided-var-map ;accumulate prev dest elim rounds
                                    (get-dest-elim-replaced-terms (list elim-seq-element))
                                    symbol-elided-bindings))
       (- (cw? (debug-flag vl)
               "~|CEgen/Debug: Proceeding to search for cts in dest-elimed form ~x0 ~ 
with elide-map ~x1~|" 
              (acl2::prettyify-clause new-clause nil wrld) 
              elim-elided-var-map))
       
       ((mv erp stop? state)
        (cts-wts-search-clause s-new-clause name mv-sig-alist
                               ens hist elim-elided-var-map 
                               vl ctx wrld state))
       (new-eliminables-alst (new-eliminable-type-alist type tc new-vars elim-seq-element wrld)))
    (mv erp stop? s-new-clause new-eliminables-alst elim-elided-var-map state)))
  

    
; 29th june '13 - added on-demand elim support.
(defun cts-wts-search-clause-elim-iter (cl name mv-sig-alist 
                                           ens hist avoid-vars 
                                           eliminables-alst elim-elided-var-map
                                           vl ctx wrld state)
  "iter on eliminables-alst, return (mv erp stop? state)"
  (declare (xargs :stobjs (state) :mode :program))
  (if (endp eliminables-alst)
      (mv nil nil state) ;stop? = nil
  
    (b* (((mv erp stop? cl new-eliminables-alst elim-elided-var-map state) ;cl is the new (dest-elimed) clause to be tested
          (cts-wts-search-clause-elim cl name mv-sig-alist 
                                      ens hist avoid-vars 
                                      (caar eliminables-alst) ;eliminable
                                      (first (cdar eliminables-alst)) ;type
                                      (second (cdar eliminables-alst)) ;tc
                                      elim-elided-var-map
                                      vl ctx wrld state))
          ((when stop?) (mv erp stop? state));abort
          (new-eliminables-alst (merge-sort-eliminables-alst new-eliminables-alst cl))
          (eliminables-alst (if (null new-eliminables-alst)  ;dfs elim
                                (cdr eliminables-alst) 
; appending is fine, since these two lists will be disjoint! more importantly we maintain order!
                              (append new-eliminables-alst (cdr eliminables-alst)))))
      (cts-wts-search-clause-elim-iter cl name mv-sig-alist 
                                       ens hist (union-eq (all-vars-lst cl) avoid-vars)
                                       eliminables-alst elim-elided-var-map
                                       vl ctx wrld state))))
          

;todo - order shud be important
(defun initial-eliminable-type-alist (type-alist wrld ans)
  (if (endp type-alist)
      ans
  (b* ((types-info-table (table-alist 'types-info-table wrld))
       ((cons var types) (car type-alist))
       ((unless (and (consp types) (null (cdr types)))) ; not supported
        (initial-eliminable-type-alist (cdr type-alist) wrld ans))
       (type (car types))
       (entry (assoc-eq type types-info-table))
       (tc (and (consp entry)
                (acl2::access types-info% (cdr entry) :type-class))))
    (if (member-equal tc '(record map))
        (initial-eliminable-type-alist (cdr type-alist) wrld (acons var (list type tc) ans))
      (initial-eliminable-type-alist (cdr type-alist) wrld ans)))))

(defun cts-wts-search-clause-main (cl name mv-sig-alist 
                                      ens hist abo? processor
                                      vl ctx wrld state)
   "main helper function for cgen in test-checkpoint. 
it checks if on-demain dest elim needs to be done"
  (declare (xargs :stobjs (state) :mode :program))
  
  (b* (((when abo?) (mv nil nil state))
        ;; if subgoal is not equivalid, dont even test it.
        
       ((mv erp stop? state)  (cts-wts-search-clause cl name mv-sig-alist
                               ens hist '() vl ctx wrld state))
       ((when stop?) (mv erp stop? state))
       ((unless (eq processor 'acl2::push-clause)) ;only in this last ditch attempt
        (mv erp stop? state))
       ((mv hyps ?concl) (clause-mv-hyps-concl cl))
       (vars (all-vars-lst hyps))
       ((mv erp0 trval state) 
        (trans-eval `(dumb-type-alist-infer ',hyps ',vars ',vl ',wrld R$ types-ht$)
                    ctx state t))
       (dumb-type-alist (if erp0 '() (cdr trval)));ASSUMPTION: trans-eval will not error out
       (initial-elim-alst (initial-eliminable-type-alist dumb-type-alist wrld '()))
       (initial-elim-alst (merge-sort-eliminables-alst initial-elim-alst cl))
       (- (cw? (and (verbose-flag vl)
                    (consp initial-elim-alst))
               "~|CEgen/Note: No luck, lets try record/map dest elim on ~x0 and search again ...~|"
               initial-elim-alst))
       (- (time-tracker :simplify-hyps-elim :end))
       (- (time-tracker :simplify-hyps-elim :init
                        :times '(2 7)
                        :interval 5
                        :msg "~|CEgen/Stats: Elapsed runtime in simplify/throw-hyps-elim is ~st secs;~|~%"))
                      
       )
       
       
       
    (if (null initial-elim-alst)
        (mv erp stop? state) ;nothin to elim
      
      (b* (((mv erp stop? state) 
            (cts-wts-search-clause-elim-iter cl name mv-sig-alist 
                                             ens hist vars 
                                             initial-elim-alst '()
                                             vl ctx wrld state))
           (- (and (verbose-stats-flag vl)
                   (time-tracker :simplify-hyps-elim :print?))))
        (mv erp stop? state)))))
       
    



#|     
(defthm obvious1 
  (implies (and (pseudo-termp s)
                (not (variablep s))
                (not (fquotep s))
                (not (consp (ffn-symb s))))
           (symbolp (ffn-symb s))))
      
(defthm obvious2
  (implies (and (symbolp a)
                (symbol-listp l))
           (symbol-listp (add-to-set-eq a l))))
|#

(mutual-recursion
(defun all-functions. (term ans.)
  "gather all functions in term"
  (declare (xargs :verify-guards nil
                  :guard (and (pseudo-termp term)
                              (symbol-listp ans.))))
  (if (variablep term)
      ans.
    (if (fquotep term)
        ans.
      (let ((fn (ffn-symb term))
            (args (fargs term)))
        (if (consp fn) ;lambda
            (all-functions-lst. args ans.)
          (all-functions-lst. args (add-to-set-eq fn ans.)))))))

(defun all-functions-lst. (terms ans.)
  (declare (xargs :verify-guards nil
                  :guard (and (pseudo-term-listp terms)
                              (symbol-listp ans.))))
  (if (endp terms)
      ans.
    (all-functions-lst.
     (cdr terms) 
     (union-eq (all-functions. (car terms) ans.) 
               ans.)))))
#|      
(defthm all-functions.-type
  (implies (and (symbol-listp a)
                (pseudo-termp term))
           (symbol-listp (all-functions. term a)))
  :hints (("Goal" :induct (all-functions. term a))))
Why is ACL2 not good at this?
|#

;(verify-guards all-functions.)

(defun all-functions (term)
  (all-functions. term '()))

(defun all-functions-lst (terms)
  (all-functions-lst. terms'()))

(verify-termination acl2::logical-namep)

(defun all-functions-definedp-lst (fns wrld)
  "are all the functions used in fns executable?"
  (declare (xargs :verify-guards nil
                  :guard (and (symbol-listp fns)
                              (plist-worldp wrld))))
  (if (endp fns)
      T
    (and (acl2::logical-namep (car fns) wrld)
         (all-functions-definedp-lst (cdr fns) wrld))))


;; 21th March 2013
;; CHeck for multiple valued functions and functions having
;; stobjs in their arguments and return values.

(defun unsupported-fns (fns wrld)
  "gather functions that 
1. take stobjs as args
2. constrained (encapsulate) and no attachment"
  (if (endp fns)
      nil
    (let* ((fn (car fns))
           (constrainedp (acl2-getprop fn 'acl2::constrainedp wrld :default nil))
           (att (acl2-getprop fn 'acl2::attachment wrld :default nil)))
          
      (if (or (or-list (acl2::stobjs-in fn wrld))
              (and constrainedp
                   (null att)))
          (cons fn (unsupported-fns (cdr fns) wrld))
        (unsupported-fns (cdr fns) wrld)))))
  

;; collect output signature arity of all multi-valued fns
(defun mv-sig-alist (fns wrld)
  "for each fn with output arity n>1, the result alist
   will have an entry (fn . n)"
  (declare (xargs :guard (and (symbol-listp fns)
                              (plist-worldp wrld))))
                                    
  (if (endp fns)
      nil
    (let* ((fn (car fns))
           (stobjs-out ;(acl2::stobjs-out fn wrld))) program mode
            (acl2-getprop fn 'acl2::stobjs-out wrld :default '(nil))))
      (if (and (consp stobjs-out)
               (consp (cdr stobjs-out))) ;(mv * ...)
          (acons fn (len stobjs-out)
                 (mv-sig-alist (cdr fns) wrld))
        (mv-sig-alist (cdr fns) wrld)))))



; Catch restrictions, warn and skip testing/csearch
(defun cgen-exceptional-functions (terms vl wrld) ;clause is a list of terms
  "return (mv all-execp unsupportedp mv-sig-alist)"
  (declare (xargs :verify-guards nil
                  :guard (pseudo-term-listp terms)))
  (b* ((fns (all-functions-lst terms))
       (all-execp (all-functions-definedp-lst fns wrld))
       (- (cw? (and (not all-execp) (verbose-flag vl))
"~|CEgen Note: Skipping testing completely, since not all
functions in this conjecture are defined.~%"))
       (unsupportedp (consp (unsupported-fns fns wrld)))
       (- (cw? (and unsupportedp (verbose-flag vl))
"~|CEgen Note: Skipping testing completely, since some
functions in this conjecture either take stobj arguments 
or are constrained without an attachment.~%")))
    (mv all-execp unsupportedp (mv-sig-alist fns wrld))))
       
         

(defun update-gcs%-top-level-fields (term vl ctx state R$ types-ht$)
  (declare (xargs :mode :program 
                   :stobjs (state R$ types-ht$)))

  (b* ((cse-stack (@ cgen-stats-event-stack))
       ((when ;(acl2::function-symbolp 'inside-test? (w state))
            (and (consp cse-stack)
                 (consp (cdr cse-stack))
; if the second item is an inside-test? entry, then the first one would
; be a copy of it, and we better not initialize our own globals
                 (assoc-keyword :inside-test? (cadr cse-stack))))
        state);dont overwrite initial work by test? i.e "top" entry

       ;; update 
       (gcs% (get-gcs%-global))
       (gcs% (change gcs% top-term term))
; ACHTUNG - get-hyps only looks at outermost implies.
       ((mv hyp concl) (mv (get-hyp term) (get-concl term)))
       (hyps (if (eq hyp 't) '() (acl2::expand-assumptions-1 hyp)))
       (vars (vars-in-dependency-order hyps concl vl (w state)))
       (d-type-al (dumb-type-alist-infer
                   (cons (dumb-negate-lit concl) hyps) vars 
                   vl (w state) R$ types-ht$))
       (gcs% (change gcs% top-vt-alist d-type-al))
       (- (cw? (system-debug-flag vl)
               "~|DEBUG: update-top : ~x0 dumb top vt-alist: ~x1 ~|"
               term d-type-al))
       (state (put-gcs%-global gcs%)) ;in top of cse-stack
       )
;   in 
    state))

        
;; The following function implements a callback function (computed hint)
;; which calls the counterexample generation testing code. Thus the
;; the so called "automated" combination of testing and theorem proving
;; is enabled naturally by the computed hints feature in the
;; engineering design of ACL2 theorem prover.
;; If somebody reads this comment, I would be very interested in any other
;; theorem-provers having a call-back mechanism in their implementation.
(defun acl2::test-checkpoint (id cl cl-list processor pspv hist ctx state)
  (declare (xargs :stobjs (state)
                  :mode :program))

;;   (decl :sig ((symbol clause symbol any any state) -> (mv erp boolean state))
;;         :mode :program
;;         :doc
;; "?:
;; This function uses override hint + backtrack no-op hint combination.
;;  On SUBGOALS 
;; that are not checkpoints does no-op. On checkpoints it calls the 
;; cts search procedure. Note that this (observer) hint combination
;; means that when this callback function is called, that particular
;; processor had a HIT and resulted in one or more subgoals, each of
;;  which will fall on top of the waterfall like in a Escher drawing.
;; ")
; RETURN either (mv t nil state) or (mv nil nil state) 
; PRECONDITION -
; INVARIANT - no new prove call is made during the computation of this
; function (this is very important, but now I can relax this invariant,
; with the introduction of post and pre functions at event level)
  (acl2::with-timeout1 
   (acl2s-defaults :get subgoal-timeout)
   (b* (
;TODObug: test? defaults should be the one to be used
       (vl (acl2s-defaults :get verbosity-level))
       ((mv all-execp unsupportedp mv-sig-alist) 
        (cgen-exceptional-functions cl vl (w state)))
;27 June 2012 - Fixed bug, in CCG, some lemmas are non-executable, since they
;involve calling the very function being defined. We should avoid testing
;anything that is not executable.
       ((unless all-execp)
        (value nil))
; 21st March 2013 - catch stobj taking and constrained functions, skip testing.
       ((when unsupportedp)
        (value nil))
;5 Sep 2013 ;satisfies precondition of (get-gcs%-global) below this
; occurs since, prove/test-checkpoint can be called from a non-event
; such as bash. We wont test such prove calls. TODO: allow
; test-checkpoint only for thm/defthm/test?.
       ((unless (and (f-boundp-global 'cgen-stats-event-stack state)
                     (valid-cgen-stats-event-stackp (@ cgen-stats-event-stack))))
        (value nil))
       
     
       (- (cw? (debug-flag vl)
"test-checkpoint : id=~x0 processor=~x1 ctx= ~x2 ~ formula=~x3 hist-len=~x4~|" 
id processor ctx (acl2::prettyify-clause cl nil (w state)) (len hist)))
 
       ((unless (member-eq processor
                           '(;acl2::preprocess-clause
                             ;;acl2::simplify-clause
                             acl2::settled-down-clause 
                             acl2::eliminate-destructors-clause
                             acl2::fertilize-clause
                             acl2::generalize-clause
                             acl2::eliminate-irrelevance-clause
                             acl2::push-clause)))  
; NOTE: I can also use (f-get-global 'checkpoint-processors state)
        (value nil));ignore backtrack hint
       
       (name (acl2::string-for-tilde-@-clause-id-phrase id))
       (wrld (w state))
       (gcs% (get-gcs%-global))
       (top-level-term (acl2::access acl2::prove-spec-var 
                                     pspv :user-supplied-term))
       ((mv & & state) ;ASSUMPTION: trans-eval wont error out
        (if (equal (ffn-symb (access gcs% top-term))
                   'dummy-topform)
            (trans-eval `(update-gcs%-top-level-fields ',top-level-term ',vl ',ctx state R$ types-ht$)
                        ctx state t)
          (value nil)))
       
       (- (cw? (verbose-stats-flag vl)
"~%~%~|CEgen/Note: At checkpoint ~x0 ~x1~|" name processor))
       (ens (acl2::access acl2::rewrite-constant
                          (acl2::access 
                           acl2::prove-spec-var pspv :rewrite-constant)
                          :current-enabled-structure))
       (abo? (access gcs% all-bets-off?))
       ((mv & stop? state) 
        (cts-wts-search-clause-main cl name mv-sig-alist
                                    ens hist abo? processor
                                    vl ctx wrld state))
       (gcs% (get-gcs%-global)) ;gcs% updated by the above csearch
       
;;; Jan 10th 2013 - Not printing at subgoal TODO
       ;; ((er &) (if (and (> (access gcs% cts) 0)
;; ;1. only print summary if there is a counterexample
;; ;2. dont bother with test?, since test? does give a summary at the end
;;                         (not (acl2::function-symbolp 'inside-test? (w state)))
;;                         (acl2s-defaults :get acl2::acl2s-pts-subgoalp))
;;                    (print-testing-summary-fn vl state)
;;                  ;; else (assign print-summary-user-flag T)
;;                  (value nil)))
       
; Assumption Jan 6th 2013 (check with Matt)
; We only arrive here with processor P, if it was a hit i.e if P
; is fertilize-clause then cross-fertilization was successful and
; potentially the generalization was unsound.
       (all-bets-off? (member-eq processor
                                 '(acl2::fertilize-clause
                                   acl2::generalize-clause
                                   acl2::eliminate-irrelevance-clause)))
 ; Monotonic change from nil to t, so its okay if we repeat it.                        
       (gcs% (if all-bets-off?
                 (prog2$ 
                  (cw? (verbose-stats-flag vl) 
                       "~| All bets off ... ~x0 in ~x1~%" name ctx)
                  (change gcs% all-bets-off? t))
               gcs%))
; update gcs% in globals. so gcs% and global gcs% are in sync
       (state (put-gcs%-global gcs%))
       )
   
   
;  in  
   (if (or stop?
           (and (> (access gcs% cts) 0)
                (or (access gcs% all-bets-off?)
                    (eq processor 'acl2::push-clause))))
; jan 6th 2013
; why bother continuing with a generalized (possibly unsound) subgoal
; or an induction when we already have found a counterexample.
; simply abort!

;Note: On abort, we *always* print the summary unless its a test? form!
       (er-progn
        (if (let ((cse-stack (@ cgen-stats-event-stack)))
              (and (consp cse-stack)
                   (consp (cdr cse-stack))
                   (assoc-keyword :inside-test? (cadr cse-stack))))
            ;(acl2::function-symbolp 'inside-test? (w state))
            (value nil)
; Lets update the global end time before printing. 18th March 2013
; Note: end-time is not updated in case of no abort. But
; thats fine, since the user has no way of asking cgen
; to print testing summary after returning from a thm/test?. 
          (b* (((mv end state) (acl2::read-run-time state))
               (gcs%  (get-gcs%-global))
               (gcs%  (change gcs% end-time end))
               (state (put-gcs%-global gcs%)))
            (print-testing-summary-fn vl state)))
        (mv t nil state))

; Check for false generalizations. TODO also do the same for
; cross-fertilization and eliminate-irrelevance if its worth the trouble
     (if (equal processor 'acl2::generalize-clause)
         ;NOTE: this pspv is for the cl not for cl-list, so there
         ;might be some inconsistency or wierdness here
         (b* ((gen-cl (car cl-list))
              (ens (acl2::ens state)) ;get current ens, not parent's.
; 2nd April 2013 - the pspv and hist passed are the parent's (CHECK)
              (type-alist (get-acl2-type-alist gen-cl name ens vl state))
              ((mv H C) (clause-mv-hyps-concl gen-cl))
              (vars (vars-in-dependency-order H C vl wrld))

;TODO.now- check the type of vt-alist.
              (vt-alist (pairlis$ vars (make-list (len vars)
                                                  :initial-element 
                                                  (list 'ACL2::ALL))))
              (term (if (null H)
                        C
                        `(implies (and ,@H) ,C)))
; the above is not really a term, but almost, we can assume AND is a function.
; hopefully it will not affect any computation based on it, certainly will
; not affect all-vars. CHECK! 20th March 2013

              ((mv & & mv-sig-alist)
; 21st March 2013 - Safe to assume that restricted funs will be caught
; higher up in the waterfall.
               (cgen-exceptional-functions gen-cl vl (w state)))
              (tau-interval-alist (tau-interval-alist-clause gen-cl name ens vl wrld state))
              ((mv erp (list & run-hist% &) state)
               (cts-wts-search name H C vars
                           type-alist tau-interval-alist mv-sig-alist NIL
                           (acl2s-defaults-alist) 
                           *initial-run-hist%* 
; we dont care about witnesses and the start time and do no accumulation.
                           (initial-gcs% 1 0 0 term vt-alist)
                           ctx wrld state))
              (num-cts-found (access run-hist% |#cts|)))
          (value (if (and (not erp)
                          (> num-cts-found 0))
                     (progn$ 
                      (cw? (normal-output-flag vl) "~| Generalized subgoal: ~x0~|" 
                           (acl2::prettyify-clause gen-cl nil (w state)))
                      (cw? (normal-output-flag vl)
                           "~| Counterexample found: ~x0 ~|"
                           (car (access run-hist% cts)))
                      (cw? (normal-output-flag vl) "~| Backtracking...~|")
                      '(:do-not '(acl2::generalize)
                                :no-thanks t))
                   nil)))
;ignore errors in cts search function
       (value nil))))
   (prog2$
    (cw? (normal-output-flag (acl2s-defaults :get verbosity-level))
         "~| Subgoal counterexample search TIMED OUT!~%")
    (value nil))
   ))





;Dont print the "Thanks" message:
(defmacro dont-print-thanks-message-override-hint ()
`(make-event  
  '(acl2::add-override-hints 
    '((cond ((or (null acl2::keyword-alist)
                 (assoc-keyword :no-thanks acl2::keyword-alist))
             acl2::keyword-alist)
            (t
             (append '(:no-thanks t) acl2::keyword-alist)))))))
       




     
;Note on xdoc: <= or < cannot be used inside defxdoc!!

(def test?-fn (form hints override-defaults dont-pts? ctx wrld state R$ types-ht$)
; Jan 9th 2013, dont print summary unless there was a counterexample.
  (decl :mode :program
        :sig ((any true-list symbol-alist symbol plist-world state R$ types-ht$) 
              -> (mv erp any state))
        :doc "gives an error triple wrapping a form that will be ... ")
  (f* ((check-syntax   (form logicp) 
                       (acl2::state-global-let*
                        ((acl2::inhibit-output-lst acl2::*valid-output-names*))
                        (acl2::translate form  T logicp T 
                                         "test? check" 
                                         wrld state))))
   (b* ((defaults (acl2s-defaults-alist override-defaults))
        (testing-enabled (get-acl2s-default 'testing-enabled defaults))
        (vl              (get-acl2s-default 'verbosity-level defaults))
        ((when (eq testing-enabled NIL)) ;dont do any testing
         (value '(value-triple :invisible))))
    
     (b* (((mv erp term state) (check-syntax form NIL))
          ((when erp)          
           (prog2$
            (cw? (normal-output-flag vl) 
                 "~|TEST?: The input form is ill-formed, see below:~%")
;show error to user which was invisble earlier
            (acl2::state-global-let*
             ((acl2::inhibit-output-lst '(summary)))
             (acl2::translate form  T NIL T 
                              "test? check" 
                              (w state) state))))

          ((mv all-execp unsupportedp mv-sig-alist) 
           (cgen-exceptional-functions (list term) vl (w state)))
; 21st March 2013 - catch stobj taking and constrained functions, skip testing.
          ((unless all-execp)  (value '(value-triple :invisible))) ;possible with test? ?
          ((when unsupportedp) (value '(value-triple :invisible)))

          
          
; No syntax error in input form, check for program-mode fns
; Note: translate gives nil as the term if form has
; a program-mode function, so we ignore it
          ((mv pm? & state)    (check-syntax form T))
          (programp            (or pm?
                                   (eq (default-defun-mode (w state)) 
                                       :program)))

          (- (cw? (debug-flag vl)
                  "~%~%CEgen/Debug: (pm? ~x0) ~x1~|" programp (cons 'test? form))) 

          ((mv hyps concl state) (partition-hyps-concl term "test?" state))
; initialize these per test?/thm/defthm globals that store information
; across subgoals in a single thm event
          ((mv start-top state) (acl2::read-run-time state))
          
          (cse-stack (@ cgen-stats-event-stack))
          ((unless (cgen-stats-event-stackp cse-stack)) ;can be empty
           (er soft ctx "~|CEgen/Error: cgen-stats-event-stack is ill-formed~|"))
          (vars (all-vars term))
          (d-type-al (dumb-type-alist-infer 
                      (cons (dumb-negate-lit concl) hyps)
                      vars vl (w state) R$ types-ht$))
          (- (cw? (verbose-stats-flag vl) 
                 "~|CEgen/Verbose/test?: dumb type-alist is ~x0~|" d-type-al))
          (gcs%  (initial-gcs% 
                  (get-acl2s-default 'num-counterexamples defaults)
                  (get-acl2s-default 'num-witnesses defaults)
                  start-top term d-type-al))
; PUSH an entry March 7th 2013
; I need to make sure, that I pop this at all exit points from now on.
          (state (f-put-global 'cgen-stats-event-stack 
                               (cons (list :gcs% gcs%
                                           :s-hist '()
                                           :inside-test? t) ;distinguishes a test? entry 
                                     cse-stack)
                               state))
          
          (vt-acl2-alst (if programp 
                            (pairlis$ vars (make-list (len vars)
                                                      :initial-element 
                                                      (list 'ACL2::ALL)))
                          (get-acl2-type-alist (list term) "top" 
                                               (acl2::ens state) vl state)))
             
          ((mv & tau-interval-alist state) (get-tau-interval-alist term "top" vl state))
          ((mv ?error-or-timeoutp ?stop? state) 
           (csearch-with-timeout "top" hyps concl 
                                 vt-acl2-alst tau-interval-alist 
                                 mv-sig-alist '() 
                                 programp defaults ctx wrld state))
          
; dont take theorem prover's help if 
; 1. csearch errored out or timed out (TODO why not? 19 July '13)
; 2. stopping condition has already been reached
; 3. form contains a program-mode function or we are in program mode
; 4. testing is set to :naive
          (no-thm-help?  (or ;error-or-timeoutp ;19 July '13
                             stop?
                             programp
                             (eq testing-enabled :naive)))

; TODO: print something if erp is true i.e error in testing
          
; Else call ACL2 prover with a hint
; that does random testing on every checkpoint.
          (- (cw? (debug-flag vl) "~|CEgen/Debug: thm+testing OFF: ~x0~%" no-thm-help?))
          
          ((mv trans-erp thm-erp state) ;2 July '13 (bug: hard error reported as proof without induction)
           (if no-thm-help? 
               (mv nil t state) ;TODO: I am throwing information here!
             (mv-let 
              (erp trval state)
              (acl2::state-global-let*
               ((acl2::inhibit-output-lst 
                 (if (system-debug-flag vl)
                     '(summary)
                   '(warning warning! observation prove
                             proof-checker event expansion
                             proof-tree summary))))
               (trans-eval `(acl2::thm-fn ',form state
                                         (or ',hints 
;user-specified hints override default hints
                                             '(("Goal"
                                                :do-not-induct t 
                                                :do-not '(acl2::generalize 
                                                          acl2::fertilize))))
;TODO: Matt's code doesnt work through induction and forcing rds
;Also the OTF flag is set to true, to test all initial subgoals. 
                                         t nil) 
                          'test?-fn state T))
              (prog2$
               (cw? (and erp (normal-output-flag vl))
                    "~|CEgen/Error: bad trans-eval call in test?-fn~|")
               (mv erp (if erp t (cadr trval)) state)))))

          
; TODO: errors in print functions will abort the whole form
          ((mv end state) (acl2::read-run-time state))
          (gcs%  (get-gcs%-global))
          (gcs%  (change gcs% end-time end))
          (state (put-gcs%-global gcs%))
          ((er &) (if (or error-or-timeoutp 
                          trans-erp
                          (and (<= (access gcs% cts) 0)
                               dont-pts?))
;no point in printing if error or timeout OR we specifically ask not
;to print the testing summary here if no cts was found.  Sep 3rd 2012 -- modified Jan 9th 2013
                      (value nil)
                    (print-testing-summary-fn vl state)))

          
          ((mv cts-found? state)      
; If testing found a counterexample, print so and abort.
           (b* ((gcs% (get-gcs%-global))
                (num-cts (access gcs% cts)))
             (cond ((posp num-cts) (prog2$
                                    (cw? (normal-output-flag vl)
                                         "~%Test? found a counterexample.~%")
                                    (mv T state)))
                   (trans-erp (prog2$
                               (cw? (normal-output-flag vl)
                                    "~|CEgen/Note: test? did not work (probably due to a hard error)!~%")
                               (mv nil state)))
;Success means the prover actually proved the conjecture under consideration
                   ((not thm-erp) (prog2$
                                   (cw? (normal-output-flag vl)
                                        "~%Test? proved the conjecture under consideration (without induction). ~
 Therefore, no counterexamples exist. ~%")
                                   (mv NIL state)))
; either thm failed, or we didnt call thm. Either way if we didnt find a cts
; then we say the test? succeeded!
                   (thm-erp (prog2$
                             (cw? (normal-output-flag vl)
                                  "~%Test? succeeded. No counterexamples were found.~%")
                             (mv NIL state)))

                   (t (prog2$
                       (cw? (normal-output-flag vl)
                            "~|CEgen/Error: test?-fn: unreachable print option! Please report this to ACL2s maintainer.~%")
                       (mv NIL state))))))

; pop the cse-stack
          (cse-stack (@ cgen-stats-event-stack))
          (- (assert$ (valid-cgen-stats-event-stackp cse-stack) 'test?-fn))
          (state (f-put-global 'cgen-stats-event-stack (cdr cse-stack) state)))

      
      (mv cts-found? '(value-triple :invisible) state )))))

(defdoc test?
  ":Doc-Section ACL2::TESTING

  Random testing using the ACL2 prover,
  generating counterexamples to top-level conjecture.~/

  ~bv[]
  Examples:
  (test? (implies (and (posp (car x))
                     (posp (cdr x)))
                (= (cdr x) (len x))))
  
  (test? (equal (reverse (reverse x)) x))
  
  Usage:
  (test? form :hints hints :override-defaults my-params)

  ~ev[]
  ~/
  
  ~t[test?] is a powerful random testing facility intended
  to be used to increase confidence in the truth of a conjecture by
  providing extensive testing in cases where there is not enough time
  or resources for formal proofs.
  
  ~t[test?] combines random testing with the power of ACL2 and
  our data definition framework. It guarantees than any
  counterexamples generated are truly counterexamples to the original
  conjecture. A counterexample is just a binding that maps the
  variables in the original conjecture to values in the ACL2
  universe. In cases where the value of variables are irrelevant, we
  bind the variables to the symbol ~t[?] : these bindings still
  provide counterexamples, but should raise alarms, since chances are
  that there is a specification error.
  
  If no counterexample is found, there are three possibilities. First,
  it is possible that the conjecture is false, in which case increasing
  the amount of testing we do may lead to the discovery of a
  counterexample.  Second, it is also possible that ACL2 proves that
  the conjecture is true, in which case we print a message reporting
  success.  Finally, the conjecture may be true, but ACL2 cannot prove
  it.  For all of these three cases, we consider testing to have
  succeeded, so ~t[test?] will report success.
  
  We note that in order to be able to generate counterexamples, we do
  not allow ACL2 to use any of the following processes: induction,
  generalization, and cross-fertilization. We do allow destructor-
  elimination, though in rare cases, user defined elim rules may
  generalize the conjecture. Such situations are recognized.  If you
  want to enable the above processes, use ~t[thm] instead, but
  note that counterexamples shown might not be of the top-level conjecture.

    
  ~bv[]
  Examples:
  (test? (implies (and (posp (car x))
                     (posp (cdr x)))
                (= (cdr x) (len x))))
  
  (test? (equal (reverse (reverse x)) x))

  ~ev[]
 
  Note is both these examples, counterexamples are generated for the
  original goal, in case some variables are elided away(like y and by
  equality z), we show ~t[?] as their instantiated values.

  ~bv[]
  (test? (implies (and (posp (car x))
                     (equal y y)
                     (equal z y)
                     (posp (cdr x)))
                (= (cdr x) (len x))))
  
  ~ev[]
  "
 )


;; (defun print-summary-user-testing (state)
;;   (declare (xargs :stobjs state))

;;   (and 
;;        (b* ((ctx 'print-summary-user)
;;             ((unless (and (f-boundp-global 'print-summary-user-flag state)
;;                           (@ print-summary-user-flag)))
;;              nil)
;;             (?er-str "~|BAD global-coverage-stats. ~
;; Please report to ACL2s maintainer the context in which this happened!~|")
;;             ((unless (f-boundp-global 'gcs% state))
;;              nil)
;;             (gcs% (get-gcs%-global))
;;             ((unless (gcs%-p gcs%))
;;              nil)
;;             (num-wts (access gcs% wts))
;;             (num-cts (access gcs% cts))
;;             (vl 1) ;TODO
;;             (- (cw? (normal-output-flag vl)
;;                     "~|ACL2s found ~x0 counterexamples and ~x1 witnesses. ~
;; To print the testing summary, do :pts~|"
;;                     num-cts num-wts))
;;             )
;;         nil)))

(defun initialize-event-user-cgen (ctx body state)
  (declare (xargs :mode :logic 
                  :stobjs state
                  :verify-guards nil))
  (declare (ignorable ctx body))
  (b* (((unless (f-boundp-global 'cgen-stats-event-stack state))
        state) ;ignore
       (cse-stack (@ cgen-stats-event-stack))
       (- (assert$ (cgen-stats-event-stackp cse-stack) 'initialize-event-user-cgen))
       ((mv start state) (acl2::read-run-time state))
       (init-gcs% (initial-gcs% (acl2s-defaults :get num-counterexamples)
                                (acl2s-defaults :get num-witnesses)
;dummy topform will replaced by the actual top-level form in
;test-checkpoint where this information is obtained from pspv
                                start '(dummy-topform dummy) '()))
       
       (vl (acl2s-defaults :get verbosity-level))

; if the top entry is by a test?, then copy its
; contents into the new entry to be pushed into stack
       ((mv gcs% s-hist)
        (if (and (consp cse-stack)
                 (assoc-keyword :inside-test? (car cse-stack)))
            (b* ((v (car cse-stack))
                 (- (cw? (system-debug-flag vl)
               "~|CEgen/Sysdebug: Pushing entry into cgen-stats-event-stack, ~
but also copying the test? event stats into the new entry ~%")))
              (mv (cadr (assoc-keyword :gcs% v)) (cadr (assoc-keyword :s-hist v))))
          (prog2$
           (cw? (system-debug-flag vl)
                "~|CEgen/Sysdebug: Pushing entry into cgen-stats-event-stack ~%")
           (mv init-gcs% '())))))
       

       (f-put-global 'cgen-stats-event-stack 
                     (cons (list :gcs% gcs% :s-hist s-hist) cse-stack)
                     state)))
  
(defun initialize-event-user-cgen-gv (ctx body state)
  (declare (xargs :mode :logic 
                  :stobjs state
                  :guard T))
  (ec-call (initialize-event-user-cgen ctx body state)))
  
                                          

(defun finalize-event-user-cgen (ctx body state)
  (declare (xargs :mode :logic :verify-guards nil :stobjs state))
  (declare (ignore ctx body))
  (b* (((unless (f-boundp-global 'cgen-stats-event-stack state))
        state) ;ignore
       (cse-stack (@ cgen-stats-event-stack))
       ((unless (valid-cgen-stats-event-stackp cse-stack))
; Design decision - Lets fix a bad stack here, without complaining.
        (f-put-global 'cgen-stats-event-stack nil state))
       (vl (acl2s-defaults :get verbosity-level))
       
       
       (rest-stack (cdr cse-stack))

; Fixed bug: There is a symmetry in initialize-event and finalize-event, that
; was ignored by me, and hence the bug. Specifically, the cts and wts collected
; inside thm-fn event are being thrown away, but test? needs to print these. So
; just like in initialize-event we copy contents of test? entry into the new
; entry, we need to copy the top entry into the test? entry, preserving the
; symmetry that these functions ought to keep.
; March 14th 2013.
       (state (if (and (consp rest-stack)
; NOTE: guards are really nice, it below caught the error, where i was
; directly searching in rest-stack instead of car of it.
                       (assoc-keyword :inside-test? (car rest-stack)))
                  ;; copy
                  (b* ((v (car cse-stack))
                       ((mv gcs% s-hist)
                        (mv (cadr (assoc-keyword :gcs% v)) (cadr (assoc-keyword :s-hist v))))
                       (rest-stack~ (cons (list :gcs% gcs% 
                                                :s-hist s-hist
                                                :inside-test? t)
                                          (cdr rest-stack)))
                       (- (cw? (system-debug-flag vl)
            "~|CEgen/Sysdebug: Popping entry in cgen-stats-event-stack, ~
but copying its contents into the test? stats entry ~%")))
                    (f-put-global 'cgen-stats-event-stack
                                  rest-stack~ state))
                (prog2$
                 (cw? (system-debug-flag vl)
            "~|CEgen/Sysdebug: Popping entry in cgen-stats-event-stack ~%")
                (f-put-global 'cgen-stats-event-stack rest-stack state)))))
           
    (prog2$ 
; (print-summary-user-testing state)
     nil ; TODO add regression statistics code here
     state)))

(defun finalize-event-user-cgen-gv (ctx body state)
  (declare (xargs :mode :logic 
                  :guard T
                  :stobjs state))
  (ec-call (finalize-event-user-cgen ctx body state)))

(defattach (acl2::initialize-event-user
            initialize-event-user-cgen-gv))

(defattach (acl2::finalize-event-user
            finalize-event-user-cgen-gv))



(defmacro test? (form &key hints override-defaults dont-print-summary)
  (let* ((vl (get-acl2s-default 'verbosity-level 
                                override-defaults))
         (debug (and (natp vl)
                     (system-debug-flag vl))))
    `(with-output
      :stack :push
      ,(if debug :on :off) :all
      :gag-mode ,(not debug)
     (make-event
      (test?-fn ',form ',hints 
                ',override-defaults ',dont-print-summary
                'test? (w state) state R$ types-ht$)))))

   
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
