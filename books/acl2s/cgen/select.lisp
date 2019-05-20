#|$ACL2s-Preamble$;
;; Author - Harsh Raju Chamarthi (harshrc)
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "../portcullis")
(begin-book t :ttags :all);$ACL2s-Preamble$|#


(in-package "CGEN")

(include-book "basis")
(include-book "simple-graph-array")
(include-book "cgen-state")
(include-book "type")

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
    
    (b* (((cons hyp rst) ts))
    (case-match hyp
      ((P t1)  (declare (ignore P t1))
       (b* (((list P t1) (defdata::expand-lambda hyp)))
         (if (and (symbolp t1)
                  (defdata::is-type-predicate P wrld))
             (separate-const/simple-hyps. rst wrld 
                                          Hc. (cons hyp Hs.) Ho.)
           (add-others-and-recurse...))))
                          
      ((R t1 t2)  (if (acl2::equivalence-relationp R wrld)
                      (cond ((and (symbolp t1) (quotep t2))
                             (add-constant-and-recurse (list R t1 t2)))
                            
                            ((and (quotep t1) (symbolp t2))
                             (add-constant-and-recurse (list R t2 t1)))
                            
                            (t (add-others-and-recurse...)))
                    (add-others-and-recurse...)))
      (&          (add-others-and-recurse...)))))))




;identify (equal x y)
(defun equiv-hyp? (hyp)
  (and (= 3 (len hyp))
       (member-eq (car hyp) '(equal = eq eql));TODO
       (proper-symbolp (second hyp))
       (proper-symbolp (third hyp))))


(mutual-recursion
(defun possible-constant-value-expressionp-lst (expr-lst)
  (if (atom expr-lst)
    t
    (and (possible-constant-value-expressionp (car expr-lst))
         (possible-constant-value-expressionp-lst (cdr expr-lst)))))

(defun possible-constant-value-expressionp (expr)
   (cond ((null expr) t);if nil
         ((defdata::possible-constant-value-p expr) t); if a constant
         ((atom expr) (defdata::possible-constant-value-p expr));if an atom, it has to go through this
         ((not (symbolp (car expr))) nil)
         (t (possible-constant-value-expressionp-lst (cdr expr))))
   )
)

;identify (equal 3 x) or (equal x 42)
(defun constant-hyp? (hyp)
  (and (= 3 (len hyp))
       (member-eq (car hyp) '(equal = eq eql))
       (or (and (proper-symbolp (second hyp))
                (possible-constant-value-expressionp (third hyp)))
           (and (proper-symbolp (third hyp))
                (possible-constant-value-expressionp (second hyp))))))

;identify (mget keyword x) and return x
(defun mget-term-var (term recordp)
  (and (= (len term) 3)
       (member-eq (car term) '(acl2::mget acl2::g g))
       (quotep (cadr term))
       (implies recordp (keywordp (acl2::unquote (cadr term))))
       (proper-symbolp (third term))
       (third term)))


(defun mget-hyp-var (hyp recordp)
  (or (mget-term-var hyp recordp)
      (and (= 3 (len hyp))
           (member-eq (car hyp) '(equal = eq eql))
           (or (mget-term-var (second hyp) recordp)
               (mget-term-var (third hyp) recordp)))))
           
;chyp=(equal x <const>) or (equal <const> x)
;gives (mv x <const>)
(defun destruct-simple-hyp (chyp)
  (if (proper-symbolp (second chyp))
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
       (member-eq (car hyp) '(equal = eq eql))
       (or (proper-symbolp (second hyp))
           (proper-symbolp (third hyp)))
       (mv-let (var expr)
               (destruct-simple-hyp hyp)
               (and 
                ;;No cycles
                (let* ((vquotient (get-val var var-quotient-alst))
;get-free-vars1 only non-buggy for terms
                       (dvars (get-free-vars1 expr nil))
                       (dquotients (get-val-lst dvars var-quotient-alst)))
                  (not (member-equal vquotient dquotients)))
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
       (b* (((mv t2 t3)
             (if (proper-symbolp (second hyp))
                 (mv (second hyp) (third hyp))
               (mv (third hyp) (second hyp)))))
         (and (proper-symbolp t2) 
              (consp t3)
              (not (member-eq (car t3) 
                              '(acl2::mget acl2::g g
                                           acl2::nth acl2::car ;SET::head
                                           acl2::cdr)))))))
              
(defun undirected-2-rel? (hyp)
 ; (declare (xargs :guard t))
;is hyp a undirected (computationally) binary relation term
;hyp = (~ x y), where ~ should be one of 
;(= eq equal eql subset-equal < <= > >=)
;TODO maintain a global list of such functions

  (and (= (len hyp) 3)
       (let* ((t2 (second hyp))
              (t3 (third hyp)))
         (and (proper-symbolp t2) 
              (proper-symbolp t3)
; 15 Oct '13 --harshrc: Modified the following, so that (= x y)
; case is subsumed by the default case of cond i.e (R term1 ... termN)
; Thus, instead of not drawing an edge, a undirected edge is added
; between x and y.

              (member-eq (first hyp) ;Relation
                         '(;acl2::= acl2::equal acl2::eq acl2::eql
                           subset-equal subset-eq subset-eql
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
; [2016-09-15 Thu] updated to newer rules (but without fixer support)
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

       ;; ((mget-hyp-var hyp t) ;(mget :const x) hack: give record types preference
       ;;  (b* ((var (mget-hyp-var hyp t)))
       ;;    (build-vdependency-graph (cdr hyp-lst)
       ;;                             (remove-entry var alst)
       ;;                             (put-assoc-equal var (cdr (assoc-equal var alst)) alst-C)
       ;;                             incoming)))

       
       ((or (atom hyp) ;variable symbols or atomic constants
            (quotep hyp)
            (and (equal (len hyp) 2)
                 (equal (len (get-free-vars1 (cadr hyp) nil)) 1))) ;monadic term
        (build-vdependency-graph (cdr hyp-lst) alst alst-C incoming)) ;dont do anything
       
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
;       [2015-04-16 Thu] Add special support for member
       ((and (equal (len hyp) 3)
             (member-eq (car hyp) '(acl2::member-eq acl2::member acl2::member-eql acl2::member-equal acl2s::in |ACL2S B|::in))
             ;; (membership-relationp (car hyp)) TODO
             (proper-symbolp (second hyp)))
        (b* ((var (second hyp))
             (term (third hyp))
             (fvars (remove-equal ;sloppy code
                     var (get-free-vars1 term nil))));buggy for non-terms
          (build-vdependency-graph 
           (cdr hyp-lst)
           (union-entry-in-adj-list var fvars alst) 
           alst-C
           incoming)))
       ;() recursion
       ;() nesting
       (t (build-vdependency-graph (cdr hyp-lst) alst alst-C incoming))))))
         

(defun build-variable-dependency-graph (hyps vars)
  (build-vdependency-graph hyps (make-empty-adj-list vars) nil nil))



;(verify-termination dumb-negate-lit)


(def vars-in-dependency-order (hyps concl vl wrld)
  (decl :sig ((pseudo-term-list pseudo-term fixnum plist-world) -> symbol-list)
        :doc "return the free variables ordered according to the notion of
  dependency that treats equality relation specially. See FMCAD paper for
  details, but I have not completely implemented the improvements in the
  paper. This is where I can use better heuristics. But with no hard examples
  to work on, I am doing a naive job for now.")
  (b* ((cterms (cons (cgen-dumb-negate-lit concl) hyps))
; cterms names constraint terms
       (vars (all-vars-lst cterms))
       ((mv Hc Hs Ho) (separate-const/simple-hyps. cterms wrld '() '() '()))
       
       (dgraph (build-variable-dependency-graph Ho vars)) ;TODO rewrite
       (ord-vs (reverse (approximate-topological-sort dgraph (system-debug-flag vl))))
       
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

(program)
(mutual-recursion
(defun can-reach1 (v G seen ans)
   (if (member-equal v seen)
       ans
     (b* ((xs (cdr (assoc-equal v G)))
          (seen (cons v seen)))
       (can-reach1-lst xs G seen (union-equal xs ans)))))
(defun can-reach1-lst (vs G seen ans)
  (if (endp vs)
      ans
    (b* ((ans1 (can-reach1 (car vs) G seen ans)))
      (can-reach1-lst (cdr vs) G seen (union-equal ans1 ans))))))
                     
(defun can-reach (v G)
  ; find all vertices that can reach v in G, given an incoming edge adj list G
  (can-reach1 v G '() '()))

(defun pick-sink-with-max-fanin (sinks G ans)
  ;;choose one to which maximum edges can reach
  (if (endp sinks)
      ans
    (if (> (len (can-reach (car sinks) G))
           (len (can-reach ans G)))
        (pick-sink-with-max-fanin (cdr sinks) G (car sinks))
      (pick-sink-with-max-fanin (cdr sinks) G ans))))

(defun add-edge (u v G)
  (put-assoc-equal u (add-to-set-equal v (cdr (assoc-equal u G))) G))

(defun add-edges1 (us v G)
  (if (endp us)
      G
    (add-edges1 (cdr us) v (add-edge (car us) v G))))

(defun transform-to-incoming-edge-alst1 (G G-in)
  (if (endp G)
      G-in
    (b* (((cons u v-lst) (car G)) ;edge from u to each of v-lst
         (G-in (add-edges1 v-lst u G-in)))
      (transform-to-incoming-edge-alst1 (cdr G) G-in))))
  
(defun transform-to-incoming-edge-alst (G)
  (transform-to-incoming-edge-alst1 G (pairlis$ (strip-cars G) nil)))

(defun dumb-get-all-sinks (G)
;given outgoing adj list get all vertices with no outgoing edges
  (if (endp G)
      '()
    (if (null (cdr (car G))) ;no neighbours
        (cons (caar G) (dumb-get-all-sinks (cdr G)))
      (dumb-get-all-sinks (cdr G)))))

(mutual-recursion
(defun var-depth-in-term (x t2)
;find max depth of x in term t2
  (if (equal x t2)
      0
    (if (or (atom t2) ;symbol
            (quotep t2)) ;quoted constant
        -1 ;not found
      (let ((d (max-var-depth-in-terms x (cdr t2) -1)))
        (if (natp d)
            (1+ d)
          d)))))

(defun max-var-depth-in-terms (x terms ans)
  (if (endp terms)
      ans
    (b* ((d1 (var-depth-in-term x (car terms))))
      (max-var-depth-in-terms x (cdr terms) (max d1 ans)))))
)
      
(defun pick-sink-with-max-depth (sinks terms ans)
  ;;choose one to which maximum term depth
  (if (endp sinks)
      ans
    (if (> (max-var-depth-in-terms (car sinks) terms -1)
           (max-var-depth-in-terms ans terms -1))
        (pick-sink-with-max-depth (cdr sinks) terms (car sinks))
      (pick-sink-with-max-depth (cdr sinks) terms ans))))

(defun filter-combinator-type-sinks (sinks vt-alist wrld)
;collect all sinks that are of type record, map, list, alist
  (if (endp sinks)
      '()
    (b* ((sink (car sinks))
         ((cons & types) (assoc-equal sink vt-alist))
         (type (car types))
         (type-metadata (defdata::get1 type (defdata::type-metadata-table wrld)))
         )
      
      (if (or (consp (defdata::get1 :PRETTYIFIED-DEF type-metadata))
              (member-eq (car (defdata::get1 :PRETTYIFIED-DEF type-metadata))
                              '(DEFDATA::RECORD
                                 ;DEFDATA::MAP
                                 ;DEFDATA::ALISTOF
                                 ;DEFDATA::LISTOF
                                 )))
          (cons sink (filter-combinator-type-sinks (cdr sinks)
                                                          vt-alist wrld))
        (filter-combinator-type-sinks (cdr sinks) vt-alist wrld)))))

(defun pick-sink-heuristic (sinks terms vt-alist wrld ans)
  (b* ((c-sinks (filter-combinator-type-sinks sinks vt-alist wrld)))
    (if (consp c-sinks)
        (pick-sink-with-max-depth (cdr c-sinks) terms (car c-sinks))
      (pick-sink-with-max-depth sinks terms ans))))
  
    
(defun pick-constant-hyp-var (terms)
  (if (endp terms)
      nil
    (if (constant-hyp? (car terms)) ;(equal x (cons 1 2))
        (b* (((mv var &) (destruct-simple-hyp (car terms))))
          var)
      (pick-constant-hyp-var (cdr terms)))))

(u::defloop filter-terms-with-arity-> (terms n)
  (for ((term in terms)) (append (and (> (len term) (1+ n)) ;arity = 1+ n
                                      (list term)))))

; incremental algorithm from FMCAD 2011 paper.
; the implementation below deviates by reusing
; simple-search at each partial assign
(def select (terms vl wrld)
  (decl :sig ((pseudo-term-list fixnum plist-world) 
              -> symbol)
        :mode :program
        :doc "choose the variable with least dependency. Build a dependency
  graph, topologically sort it and return the first sink we find.")
;PRECONDITION: (len vars) > 1
;We have to build a dependency graph at each iteration, since the graph changes
;as we incrementally concretize/instantiate variables.  
;SELECT Ideal Situation:: No variable should be picked before the variable it
;depends on has been selected and assigned

  (b* ((vars (all-vars-lst terms))
       (cvar (pick-constant-hyp-var terms))
       ((when (proper-symbolp cvar)) cvar) ;return var (= const) immediately
       (G (build-variable-dependency-graph terms vars))
;TODO: among the variables of a component, we should vary
;the order of selection of variables!!
       (var1 (car (last (approximate-topological-sort G (debug-flag vl)))))
       (sinks (dumb-get-all-sinks G))
       (terms/binary-or-more (filter-terms-with-arity-> terms 1)) ;ignore monadic terms
       (dumb-type-alist (dumb-type-alist-infer terms vars vl wrld))
       (var (pick-sink-heuristic sinks terms/binary-or-more dumb-type-alist wrld var1))
       (- (cw? (verbose-stats-flag vl) "~| Cgen/Incremental-search: Select var: ~x0~%" var)))
   var))
