#|$ACL2s-Preamble$;
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "../portcullis")
(begin-book t :ttags :all);$ACL2s-Preamble$|#


#|
Instructions to use this book
1. Install Glucose
The following are copied from instructions in :doc satlink::sat-solver-options)
a) Download Glucose @ http://www.labri.fr/perso/lsimon/downloads/softwares/glucose-syrup.tgz
b) Extract and run the following command:
   : cd glucose-syrup/simp; make
c) Verify that glucose-syrup/simp/glucose --help prints a help message
(NOTE for Mac users: If you are building Glucose 3.0 or 4.0 on a Mac, the build might fail. In that case, a solution may be to make the two replacements shown below, where the the first in each pair (<) is the Mac version, while the second in each pair (>) is the original source.

<     // friend Lit mkLit(Var var, bool sign = false);
---
>     friend Lit mkLit(Var var, bool sign = false);

< inline  Lit  mkLit  (Var var, bool sign = false) { Lit p; p.x = var + var + (int)sign; return p; }
---
> inline  Lit  mkLit  (Var var, bool sign) { Lit p; p.x = var + var + (int)sign; return p; }

End of NOTE for Mac users.)

2. Create executable script named glucose in your $PATH with contents:
#!/bin/sh
/path-to-glucose/glucose-syrup/simp/glucose -model "$@"

Imp Note: Lets just use the latest ACL2 sources. I have committed the
changes to acl2s-modes (ccg and prover-restrictions books) that will
not be compatible with older version of ACL2. This means to make and
test homeworks you need to use a separate ACL2s copy, perhaps
downloaded from the webpage.

3. Test that things are working:
: cd [acl2-books]/centaur/satlink/solvers
: [acl2-books]/build/cert.pl test-glucose

4. Certify ACL2s books using our script. That will certify this book too.

|#

(in-package "CGEN")

(include-book "acl2s/utilities" :dir :system)
(include-book "centaur/gl/gl" :dir :system)
(include-book "centaur/satlink/top" :dir :system)
(include-book "centaur/gl/bfr-satlink" :dir :system :ttags :all) ;missing in the Manual

; Make a Glucose satlink config
(def-const *my-config* (satlink::make-config :cmdline "glucose -model"))
;; (def-const *my-config* (satlink::make-config :cmdline "cryptominisat5.exe"))

(defun gl-my-satlink-config ()
  (declare (xargs :guard t))
  *my-config*)

; You need to do this otherwise the default glucose-cert is used (which gives error: drat-trim)
(defattach gl::gl-satlink-config gl-my-satlink-config)

; (weird) need to check this config, otherwise the def-gl-thm below errors out
(include-book "centaur/satlink/check-config" :dir :system)
;(value-triple (satlink::check-config *my-config*))

; Turn on the AIG mode
;(local (gl::gl-satlink-mode))

(include-book "acl2s/defdata/defdata-util" :dir :system)

(defun collect-vars (term)
  (reverse (acl2::all-vars term)))

(defmacro s+ (&rest args)
  "string/symbol(s) concat to return a symbol.
  :pkg and :separator keyword args recognized."
  `(defdata::s+ ,@args :pkg "CGEN"))

(defmacro g1 (a x)
  `(defdata::get1 ,a ,x))

;propositional constants
(defun has-output (f x)
  (member x (g1 :out f)))
(defun has-input (f x)
  (member x (g1 :in f)))
(defun I/O-compat (f1 f2)
  "f1 and f2 are I/O compatible"
  (or (intersection-eq (g1 :out f1) (g1 :in f2))
      (intersection-eq (g1 :out f2) (g1 :in f1))))

(defun can-flow (x f1 f2)
  "value of x can possibly flow from f1 to f2"
  (member-eq x (intersection-eq (g1 :out f1) (g1 :in f2))))

(defun sfixes-lit (fixer l)
  (and (member-equal l (g1 :fixes fixer)) t))

(defmacro deffilter (nm arglst filter-fn)
;the first arg is the one to recur on
  `(defloop ,nm (,@arglst)
     (for ((x in ,(car arglst))) (append (and (,filter-fn x) (list x))))))

(deffilter filter-has-output (fixers x-var)
  (lambda (x) (has-output x x-var)))

(deffilter filter-has-input (fixers x-var)
  (lambda (x) (has-input x x-var)))

(deffilter filter-sfixes-lit (fixers l)
  (lambda (f) (sfixes-lit f l)))

(defun subst-args (new-arg old-arg args)
  (if (endp args)
      '()
    (if (equal old-arg (car args))
        (if (and (true-listp new-arg) (consp new-arg)) ;usually (list x1 x2 ..)
            (append (cdr new-arg) (cdr args))
          (cons new-arg (cdr args)))
      (cons (car args) (subst-args new-arg old-arg (cdr args))))))

(defmacro defloop+ (name arglist &rest forms)
  "allows nested for loops"
  (b* ((loop+-form (car (last forms)))
       (`(FOR ((,elem IN ,loop-arg)) ,body) loop+-form)
       ((unless (eq 'FOR (car body)))
          `(defloop ,name ,arglist . ,forms))
        (nm1 (s+ name "1"))
        (arglist-aux (subst-args elem loop-arg arglist)))
    `(PROGN
      (DEFLOOP+ ,nm1 ,arglist-aux ,body)
      (DEFLOOP ,name ,arglist
        (FOR ((_X IN ,loop-arg))
             (APPEND (B* ((,elem _X))
                         (,nm1 ,@arglist-aux))))))))
(defun to-string (x)
  (declare (xargs :mode :program))
  (coerce (cdr (coerce (fms-to-string "~x0" (list (cons #\0 x))) 'list)) 'string))

(defun all-vars/fixer (f)
  (union-eq (g1 :in f) (g1 :out f)))
(defun all-vars/lit (l)
  "assume literal l is a term; return all variables in l"
  (collect-vars l))

(program)
(defun lit-name (lit)
  (acl2s::fix-intern-in-pkg-of-sym (to-string lit) 'acl2::x))

; [TheFixer chosen for c]
(defun chosen-fixer-var (F lit)
  (s+ (g1 :name F) "**" (lit-name lit)))

(defloop+ pvars/chosen-fixer (lits fixers)
  (for ((l in lits))
       (for ((f in fixers))
            (when (sfixes-lit f l)
              (collect (chosen-fixer-var f l))))))

; [Final-value]
(defun final-value-var (f1x)
  (b* (((list f1 x) f1x))
    (s+ (g1 :name f1) "!" x)))

(defloop final-value-vars (fixers x)
  (for ((f in fixers))
       (when (has-output f x)
         (collect (final-value-var (list f x))))))

(defloop pvars/final (vars fixers)
  (for ((x in vars))
       (append (final-value-vars fixers x))))


(defloop+ final-fixer-variable-pairs (vars fixers)
  (for ((x in vars))
       (for ((f in fixers))
            (when (has-output f x)
                  (collect (list (g1 :name f) x))))))

(defun final-value-var-table (vars fixers)
  "map final-value-var to its (list fixer variable) pair"
  (pairlis$ (pvars/final vars fixers)
            (final-fixer-variable-pairs vars fixers)))




; [Connected]
(defloop+ all-pairs-fn (f1s f2s distinct-p)
  (for ((f1 in f1s))
       (for ((f2 in f2s))
            (when (implies distinct-p (not (equal f1 f2)))
              (collect (list f1 f2))))))

(defmacro all-pairs (fs &key distinct-p)
  `(all-pairs-fn ,fs ,fs ',distinct-p))


(defloop+ all-connections1 (f1f2s vars)
  (for (((list f1 f2) in f1f2s))
       (for ((x in vars))
            (when (can-flow x f1 f2)
                  (collect (list f1 x f2))))))

;TODO revisit efficiency
(defun all-connections (fixers vars)
  (all-connections1 (all-pairs fixers :distinct-p t) vars))

;the following two functions assume that you collected connections are between distinct fixers
(defloop connections-from-via (f1 x fixers)
  (for ((f2 in fixers))
       (when (and (has-input f2 x)
                  (not (equal f1 f2)))
         (collect (list f1 x f2)))))

(defloop connections-to-via (f2 x fixers)
  (for ((f1 in fixers))
       (when (and (has-output f1 x)
                  (not (equal f1 f2)))
         (collect (list f1 x f2)))))


(defun connection-var (f1xf2)
  (b* (((list f1 x f2) f1xf2))
    (s+ (g1 :name f1) "-" x "->" (g1 :name f2))))

(defloop connection-vars (f1xf2-list)
  (for ((f1xf2 in f1xf2-list)) (collect (connection-var f1xf2))))

(defun pvars/conn (fixers vars)
  (connection-vars (all-connections fixers vars)))


(defloop connection-var-table1 (f1xf2-list)
  (for ((f1xf2 in f1xf2-list))
       (collect (cons (connection-var f1xf2)
                      (b* (((list f1 x f2) f1xf2))
                          (list (g1 :name f1) x (g1 :name f2)))))))

(defun connection-var-table (vars fixers)
  "map connection-var to the connection"
  (b* ((conns (all-connections fixers vars)))
      (connection-var-table1 conns)))


; [Appears in solution/Valid]
(defun valid-var (f1)
  (s+ (g1 :name f1) ".VALID"))

(defloop pvars/valid (fixers)
  (for ((f1 in fixers)) (collect (valid-var f1))))

(defloop g1-lst (kwd alists)
  (for ((alist in alists)) (collect (g1 kwd alist))))

(defun valid-var-table (fixers)
  "map valid-var to its fixer name"
  (pairlis$ (pvars/valid fixers) (g1-lst :name fixers)))


; [Transitively Connected with flow annotation]

(defun trans-conn-with-flow-var (f1xf2)
  (b* (((list f1 x f2) f1xf2))
      (s+ (g1 :name f1) "---" x "--->" (g1 :name f2))))


(defloop trans-conn-with-flow-vars (f1xf2-list)
  (for ((f1xf2 in f1xf2-list))
       (collect (trans-conn-with-flow-var f1xf2))))

(defun pvars/trans-flow (fixers vars)
  (trans-conn-with-flow-vars (all-connections1 (all-pairs fixers :distinct-p nil) vars)))

; [Transitively Connected]

(defun trans-conn-var (f1f2)
  (b* (((list f1 f2) f1f2))
      (s+ (g1 :name f1) "--->" (g1 :name f2))))


(defloop all-possible-trans-pairs1 (f1f2-list)
  (for ((f1f2 in f1f2-list)) (when (g1 :in (second f1f2))
                               ;;it should have input port
                               (collect f1f2))))

(defun all-possible-trans-pairs (fixers)
  (all-possible-trans-pairs1 (all-pairs fixers)))

(defloop trans-conn-vars (f1f2-list)
  (for ((f1f2 in f1f2-list)) (collect (trans-conn-var f1f2))))

(defun pvars/trans (fixers)
  (trans-conn-vars (all-possible-trans-pairs fixers)))



(defun pvar/sat-term (term)
  (s+ (lit-name term) ".is_SAT"))

(defloop pvars/sat-term (terms)
  (for ((term in terms)) (collect (pvar/sat-term term))))


(defun pvar/sat-lit (lit)
  (s+ (lit-name lit) ".is_SAT"))
(defloop pvars/sat-lit (lits)
  (for ((lit in lits)) (collect (pvar/sat-lit lit))))


(defun pvars-fn (vars fixers lits terms)
  (append (pvars/chosen-fixer lits fixers)
          (pvars/final vars fixers)
          (pvars/conn fixers vars)

          (pvars/valid fixers)
          (pvars/trans-flow fixers vars)
          (pvars/trans fixers)
          (union-equal (pvars/sat-term terms)
                       (pvars/sat-lit lits))
          ))

(defun pvars-type-constraints (vars fixers lits terms)
  (b* ((pvars (pvars-fn vars fixers lits terms))
       (n (len pvars))
       (booleanps (make-list n :initial-element 'booleanp)))
      (defdata::list-up-lists booleanps pvars)))


; Represent a clause as a list

; Now we will generate the SAT constraints/clauses of the encoding




;[Circuit/Each var has atleast one final-value ]
; \E F_k : x \in Out(F_k): F_k!x

(defloop C/atleast-one-final-value (vars fixers)
  (for ((x in vars))
       (collect `(OR ,@(final-value-vars fixers x)))))

;[Circuit/Each var has atmost one final-value ]
; F_j!x => ~F_k!x for all k!=j
(defloop+ C/atmost-one-final-value1 (f1f2-list x)
  (for ((f1f2 in f1f2-list))
       (collect (b* (((list f1 f2) f1f2))
                    `(IMPLIES ,(final-value-var (list f1 x))
                              (NOT ,(final-value-var (list f2 x))))))))

(defloop C/atmost-one-final-value (vars fixers)
  (for ((x in vars)) (append (C/atmost-one-final-value1 (all-pairs (filter-has-output fixers x) :distinct-p t) x))))

; [TheFixer def]
; \A F,c :: F**c => F.valid /\ sfixes(F,c)
(defun C/F-is-TheFixer-for-lit (F lit)
  `(IMPLIES ,(chosen-fixer-var F lit) ,(valid-var F)))

(defloop+ C/TheChosenFixer-def (literals fixers)
  (for ((lit in literals))
       (for ((F in fixers))
            (when (sfixes-lit F lit)
              (collect (C/F-is-TheFixer-for-lit F lit))))))

; [2016-02-17 Wed] example *ms-eg2-fixer-table* gives a wasteful solution!!
; The following constraint precludes it by forcing F**C to be valid for atmost one fixer.
; \A F1,c :: F1**c => \A F2 :F2 sfixes c, F2!=F1: ~F2.valid
;; WRONG pointed by PETE [2016-08-27 Sat] USE the foll instead:
;; \A F1,c :: F1**c => \A F2: F2 sfixes c, F2!=F1 : ~F2**c

;; [2016-09-07 Wed] But this is not enough, so use the following optimization
;; for avoiding redundant fixer terms
; \A F1 :: F1.valid => \E c: sfixes(F1,c): F1**c

(defloop C/valid-fixes-at-least-one-lit (fixers lits)
  (for ((F1 in fixers))
       (collect `(IMPLIES ,(valid-var F1)
                          (OR ,@(pvars/chosen-fixer lits (list F1)))))))

(defloop C/TheCF-uniquely-valid2 (F1 other-lit-fixers lit)
  (for ((F2 in other-lit-fixers)) (collect `(IMPLIES ,(chosen-fixer-var F1 lit)
                                                     (NOT ,(chosen-fixer-var F2 lit))))))

(defloop+ C/TheCF-uniquely-valid1 (literals fixers all-fixers)
  (for ((lit in literals))
       (for ((F1 in fixers))
            (when (sfixes-lit F1 lit)
              (append (C/TheCF-uniquely-valid2 F1
                                               (remove1-equal F1 (filter-sfixes-lit all-fixers lit))
                                               lit))))))

(defun C/TheChosenFixer (lits fixers)
  (append (C/TheChosenFixer-def lits fixers)
          (C/TheCF-uniquely-valid1 lits fixers fixers)))


; [Final-Value fixer is Valid]
; F_1!x => F_1.valid
(defloop+ C/final-value-implies-valid (vars fixers)
  (for ((x in vars))
       (for ((f1 in fixers))
            (when (has-output f1 x)
              (collect `(IMPLIES ,(final-value-var (list f1 x))
                                 ,(valid-var f1)))))))


; [Connections are between Valid fixers]
; F_1-x->F_2 => F_1.valid /\ F_2.valid
(defloop C/connection-implies-valid1 (f1xf2-list)
  (for ((f1xf2 in f1xf2-list))
       (collect (b* (((list f1 ?x f2) f1xf2))
                  `(IMPLIES ,(connection-var f1xf2)
                            (AND ,(valid-var f1)
                                 ,(valid-var f2)))))))

(defun C/connection-implies-valid (fixers vars)
  (C/connection-implies-valid1 (all-connections fixers vars)))


; [Circuit/Atmost one input connection]
; F_j-x->F_1 => ~F_i-x->F_1 for all i!=j

;TODO -- might be inefficient!
(defloop+ C/atmost-one-input-conn1 (fs fifj-list vars)
  (for ((f1 in fs))
       (for (((list fi fj) in fifj-list)) ;distinct pair
            (for ((x in vars))
                 (when (and (can-flow x fi f1)
                            (can-flow x fj f1)
                            (not (equal fi f1)) (not (equal fj f1)))
                   (collect `(IMPLIES ,(connection-var (list fj x f1))
                                      (NOT ,(connection-var (list fi x f1))))))))))

(defun C/atmost-one-input-conn (fixers vars)
  (C/atmost-one-input-conn1 fixers (all-pairs fixers :distinct-p t) vars))

; [Circuit/Atleast one input connection]
; F_1.valid => \Ax:\in In(F_1):\E F_k:x \in Out(F_k):F_k-x->F_1

(defloop+ C/atleast-one-input-conn1 (fs all-fixers vars)
  (for ((f1 in fs))
       (for ((x in vars)) ;A=>B&C == A=>B & A=>C
            (when (has-input f1 x)
              (collect `(IMPLIES ,(valid-var f1)
                                 (OR . ,(connection-vars
                                         (connections-to-via f1 x all-fixers)))))))))

(defun C/atleast-one-input-conn (fixers vars)
  (C/atleast-one-input-conn1 fixers fixers vars))

; [Def of transitivity (with flow variable annotated and otherwise)]
(defun drop-flow-var (f1xf2)
  (b* (((list f1 & f2) f1xf2))
    (list f1 f2)))

;[Partial Def of transitivity]
(defloop C/trans1/basis1 (f1xf2-list)
  (for ((f1xf2 in f1xf2-list))
       (collect `(IMPLIES ,(connection-var f1xf2)
                          (AND ,(trans-conn-with-flow-var f1xf2)
                               ,(trans-conn-var (drop-flow-var f1xf2)))))))


(defun C/trans1/basis (fixers vars)
  (C/trans1/basis1 (all-connections fixers vars)))


(defloop+ triples-with-flow (fixers f2xf3-list)
  "return triples ABC, with flow, to be used in the def of transitivity i.e. A->B & B->C => A->C"
  (for (((list f2 x f3) in f2xf3-list))
       (for ((f1 in fixers))
            (when (and (member x (g1 :out f1)) ;x should flow out of f1
                      (member x (g1 :in f2))  ; and into f2
                      (not (equal f1 f2))     ;ignore loops (in hyps)
                      ;(not (equal f1 f3)) ; BUG: dont ignore these, these are to be caught!
                      )
              (collect (list x f1 f2 f3))))))


(defloop+ C/trans-with-flow1/rec1 (xf1f2f3-list)
  (for ((xf1f2f3 in xf1f2f3-list))
       (collect (b* (((list x f1 f2 f3) xf1f2f3))
                    `(IMPLIES (AND ,(trans-conn-with-flow-var (list f1 x f2))
                                   ,(trans-conn-with-flow-var (list f2 x f3)))
                              ,(trans-conn-with-flow-var (list f1 x f3)))))))

(defun C/trans-with-flow1/rec (fixers vars)
  (b* ((xf1f2f3-list (triples-with-flow fixers (all-connections fixers vars))))
    (C/trans-with-flow1/rec1 xf1f2f3-list)))


(defloop+ triples-without-flow (fixers f2f3-list)
  "return triples ABC, to be used in the def of transitivity i.e. A->B & B->C => A->C"
  (for (((list f2 f3) in f2f3-list))
       (for ((f1 in fixers))
            (when (and (not (equal f1 f2)) ;ignore loops (in hyps)
                       (not (equal f2 f3))
                       (g1 :in f2)) ;f2 should have an input port
                 (collect (list f1 f2 f3))))))


(defloop C/trans1/rec1 (f1f2f3-list)
  (for ((f1f2f3 in f1f2f3-list))
       (collect (b* (((list f1 f2 f3) f1f2f3))
                    `(IMPLIES (AND ,(trans-conn-var (list f1 f2))
                                   ,(trans-conn-var (list f2 f3)))
                              ,(trans-conn-var (list f1 f3)))))))

(defun C/trans1/rec (fixers)
  (b* ((f1f2f3-list (triples-without-flow fixers (all-possible-trans-pairs fixers))))
    (C/trans1/rec1 f1f2f3-list)))


(defun C/trans1 (fixers vars)
  (append (C/trans1/basis fixers vars)
          (C/trans-with-flow1/rec fixers vars)
          (C/trans1/rec fixers)))

; One direction of def of transitivity is not enough.
; We need the other direction to avoid bogus trans
; connections which do not have any base connections.
;  F_1--x-->F_3 => F_1-x->F_3 \/ \E F_2:: F_1--x-->F_2 /\ F_2--x-->F_3


(defloop C/trans-with-flow-only-if2 (f2s f1 f3 x)
  (for ((f2 in f2s))
       (collect (list 'AND
                      (trans-conn-with-flow-var (list f1 x f2))
                      (trans-conn-with-flow-var (list f2 x f3))))))


(defun fixers-between-with-flow (fixers f1 f3 x)
  (if (endp fixers)
    '()
    (b* ((f2 (car fixers))
         ((when (or (equal f2 f1) (equal f2 f3)))
          (fixers-between-with-flow (cdr fixers) f1 f3 x))
         ((unless (and (can-flow x f1 f2)
                       (can-flow x f2 f3)))
          (fixers-between-with-flow (cdr fixers) f1 f3 x)))
     (cons f2 (fixers-between-with-flow (cdr fixers) f1 f3 x)))))


(defloop C/trans-with-flow-only-if1 (f1xf3-list all-fixers)
  (for ((f1xf3 in f1xf3-list))
       (collect
        (b* (((list f1 x f3) f1xf3)
             (f2s (fixers-between-with-flow all-fixers f1 f3 x)))
          `(IMPLIES ,(trans-conn-with-flow-var f1xf3)
                    (OR ,(connection-var f1xf3)
                        . ,(C/trans-with-flow-only-if2 f2s f1 f3 x)))))))

(defun C/trans-with-flow-only-if-direction (fixers vars)
  (C/trans-with-flow-only-if1 (all-connections fixers vars) fixers))

(defun C/trans (fixers vars)
  (append (C/trans1 fixers vars)
          (C/trans-with-flow-only-if-direction fixers vars)
          ))


; [Circuit/No cycles]
; \A F_k :: ~F_k--->F_k

(defloop C/no-cycles (fixers)
  (for ((f1 in fixers))
       (unless (null (g1 :in f1))
         (collect `(NOT ,(trans-conn-var (list f1 f1)))))))


; [Def/semantics of final-value (one dir)]
; \A F_j:F_j != F_i: F_i!x & Fj.valid =>  {FjxFi} /\ F_j--x-->F_i
(defloop C/final-value-def2 (other-x-fixers final-f x)
  (for ((f_j in other-x-fixers))
       (when (not (equal f_j final-f))
         (collect `(IMPLIES
                    (AND ,(final-value-var (list final-f x))
                         ,(valid-var f_j))
                    ,(and (can-flow x f_j final-f)
                          (trans-conn-with-flow-var (list f_j x final-f))))))))

(defloop C/final-value-def11 (x-fixers all-x-fixers x)
  (for ((final-f in x-fixers))
       (append (C/final-value-def2 all-x-fixers final-f x))))

(defabbrev C/final-value-def1 (x-fixers x)
  (C/final-value-def11 x-fixers x-fixers x))

(defloop C/final-value-def (vars fixers)
  (for ((x in vars))
       (append (C/final-value-def1 (filter-has-output fixers x) x))))

; [TheFixer is preserved by downstream]
; \AF,c:sfixes(F,c): \A G : {FxG} /\ x \in Out(G): F**c /\ F--x-->G => spreserves(G,c)
; updated : do also the same for inputs [2016-03-30 Wed] But note that this is just an approx of the ground instantiation method
; C-inv-x(c,x,F1): \A G : {F1xG} & {x \in Out(G)}:  F1--x-->G => spreserves(G,c)
; \AF,c:sfixes(F,c): \Ax:x\in c: {x \in Out(F)}F**c => C-inv-x(c,x,F) /\ {x \in In(F)}F**c => \E F1:{F1xF}: F1-x->F /\ C-inv-x(c,x,F1)

(defun spreserves-lit (fixer l)
  (or (and (member-equal l (g1 :preserves fixer)) t)
      (and (member-equal l (g1 :fixes fixer)) t)
      ;;output vars of fixer function disjoint from vars of lit --> it trivially preserves lit
      (null (intersection-eq (g1 :out fixer) (all-vars/lit l)))
      ;;hack -- assume that all monadic/type literals are preserved
      ;;to avoid specifying too many preservation rules [2016-04-17 Sun]
      ;;TODO -- restrict this to defdata-type only
      (and (consp l) (= (len l) 2))

      ))

(deffilter filter-spreserves-lit (fixers l)
  (lambda (f) (spreserves-lit f l)))

(defloop C-inv-via-x-after-F (lit x F all-fixers)
  (for ((G in all-fixers))
            (when (and (has-output G x)
                       (can-flow x F G)
                       (not (equal F G)))
              (collect `(IMPLIES ,(trans-conn-with-flow-var (list F x G))
                                 ,(spreserves-lit G lit))))))

(defloop C/TheFixer-is-preserved3/inputs (F1-lst lit x lit-fixer all-fixers)
  (for ((F1 in F1-lst))
       (collect `(AND ,(connection-var (list F1 x lit-fixer))
                      ,@(C-inv-via-x-after-F lit x F1 all-fixers)))))

(defloop C/TheFixer-is-preserved2 (xs F lit all-fixers)
  (for ((x in xs))
       (collect (if (has-output F x)
                    `(IMPLIES ,(chosen-fixer-var F lit)
                              (AND . ,(C-inv-via-x-after-F lit x F all-fixers)))
                 `(IMPLIES ,(chosen-fixer-var F lit)
                           (OR . ,(C/TheFixer-is-preserved3/inputs
                                   (strip-cars (connections-to-via F x all-fixers))
                                   lit x F all-fixers)))))))



(defloop C/TheFixer-is-preserved1 (lit-fixers lit all-fixers)
  (for ((F in lit-fixers))
       (append (C/TheFixer-is-preserved2 (all-vars/lit lit) F lit all-fixers))))

(defloop C/TheFixer-is-preserved (lits fixers)
  (for ((lit in lits))
       (append (C/TheFixer-is-preserved1 (filter-sfixes-lit fixers lit) lit fixers))))

#|
; [2016-03-11 Fri] Simulate ground instantiation of preservation rules

; F.x stands for the edge coming out of F, i.e. an output of F that carries a
; value of variable x F.x is not a pvar by itself, but is used inside C(F.x,
; ...) pvar that denotes truth value of that particular constraint instance.
(defun fixer-output-x-var (f1x)
  (b* (((list f1 x) f1x))
    (s+ (g1 :name f1) "." x)))

(defloop fixer-output-x-vars (f1x-list)
  (for ((f1x in f1x-list)) (collect (fixer-output-x-var f1x))))

(defloop fixer-output-x1 (fixers x)
  (for ((f in fixers))
       (when (has-output f x)
         (collect (list f x)))))

(defloop fixer-output-x-alst (vars fixers)
  (for ((x in vars))
       (collect (cons x (fixer-output-x1 fixers x)))))

; Pvar C(F1.x, F2.y, F3.z)
(defun C-truth-val-var (lit vars fx-list)
  ;ASSUMPTION: lit is a pseudo-term
  (b* ((fx-pvars (fixer-output-x-vars fx-list))
       (lit-instance (acl2::subcor-var vars fx-pvars lit)))
    (lit-name lit-instance)))

(defun assoc-lst (keys alist)
  "give back the subset of the alist that correspond to these keys. the order
of the entries is same as the keys"
  (declare (xargs :guard (and (true-listp keys)
                              (alistp alist))))
  (if (endp keys)
      nil
    (b* ((entry (assoc-equal (car keys) alist)))
      (if entry
          (cons entry
                (assoc-lst (cdr keys) alist))
        (assoc-lst (cdr keys) alist)))))

(defloop connections-to (f2 xs fixers)
  (for ((f1 in fixers) (x in xs))
       (when (and (has-output f1 x)
                  (not (equal f1 f2)))
         (collect (list f1 x f2)))))


(defun generate-frule-instance-clause1 (lit vars fx-list lit-fixer)
  (b* ((pvar (C-truth-val-var lit vars fx-list))
       (var-fx-list{} (pairlis$ vars fx-list))
       (fxr-out (g1 :out lit-fixer))
       (out-fx-list{} (fixer-output-x-alst fxr-out (list lit-fixer)))
       ((unless (subsetp out-fx-list{} var-fx-list{})) nil)
;ACHTUNG: Make sure that there is a unique fixer rule for a lit, fixer pair
;; now its possible that this lit-instance is actually "fixed", but for that we need to generate the following clause:
;; C(.. in-fx-list .. out-fx-list..) => F**C /\ Fin1-x1->F /\ ...
       ;; C(F1x1,F2x2,Fy1,Fy2, F3z) => F**C /\ F1-x1->F /\ F2-x2->F /\ F3.valid
       ;; No need for F3.valid. INVARIANT: at the least vars(F) \superset of vars(Lit)
       (fxr-in (g1 :in lit-fixer))
       (in-fx-list{} (assoc-lst fxr-in var-fx-list{})))
    `(IMPLIES ,pvar
              (AND ,(chosen-fixer-var lit-fixer lit)
                   ,@(connection-vars (connections-to lit-fixer
                                                      (strip-cars in-fx-list{});x1   x2   ..
                                                      (strip-cdrs in-fx-list{});Fin1 Fin2 ..
                                                      ))))))


(defloop generate-frule-instance-clause (lit vars fx-list lit-fixers)
  (for ((lit-fixer in lit-fixers))
       (thereis (generate-frule-instance-clause1 lit vars fx-list lit-fixer))))

(defun get-input-args (F prule)
  (declare (ignorable prule))
  (g1 :in F))

#|
(defun match-p (term pat)
  (declare (xargs :guard (and (pseudo-termp term)
                              (pseudo-term pat))))
  (b* (((mv yesp ?sigma) (acl2::one-way-unify pat term))
       (- (cw "~| x0 matches ~x1 with Sigma ~x2~%" term pat sigma))
       )
    yesp))

(defloop matches-some-rule (term rules)
  (for ((rule in rules))
       (if (match-p term (get-concl rule))
           (return rule))))
|#

(defun matches-prule (prule x) (declare (ignorable prule x)) nil)

;; Example arguments
;; (C x y1 y2 z) (x y1 y2 z) ((F0 x) (G1 y1) (G2 y2) (F3 z)) (implies (C x y1 y2 z) (C x (G1 x y1 y2) (G2 x y2) z))
(defun generate-prule-instance-clause1 (lit vars fx-list prule)
  (b* ((pvar (C-truth-val-var lit vars fx-list))
       (var-fx-list{} (pairlis$ vars fx-list))
       ((unless (matches-prule prule var-fx-list{})) nil)
       ;ACHTUNG: Make sure that there is a unique prule for a lit, fixer pair
       ;; now its possible that this lit-instance is actually "preserved", but for that we need to generate the following clause:
; Cxy1y2z => CxG(xy1y2)z
; : {spreserves(G,C)} C(F0.x,G.y1,G.y2,F3.z) =>  F3.valid /\ F0-x->G /\ \E F1,F2:{F1y1G},{F2y2G}: F1-y1->G /\ F2-y2->G /\ C(F1.x,F1.y1,F2.y2,F3.z)

; Cxy1y2z => CxG1(xy1y2)(G2xy2)z
; : {prule for C} C(F0.x,G1.y1,G2.y2,F3.z) =>
;   F3.valid /\ F0-x->G1 /\ F0-x->G2 /\ \E F1,F2:{F1y1G1},{F2y2G2}: F1-y1->G1 /\ F2-y2->G2 /\ C(F0x,F1.y1,F2.y2,F3.z)

; Cxyz => CxG(wy)z or Cxyz => CxG(x'y)z (free variable) TODO -- NOT SUPPORTED for now!!
; : {spreserves(G,C)} C(F1.x,G.y,F3.z) =>  F3.valid /\ \E F2:{F2yG}:F2-y->G /\ C(F1.x,F2.y,F3.z)

       (input-var-pfxr-alist (get-prule-input-alist prule)) ;can have duplicate keys
       (inputs-only (remove-duplicates-eq (strip-cars input-var-pfxr-alist)))
       (in-fx-list{} (assoc-lst inputs-only var-fx-list{}))

       (output-var-pfxr-alist (get-prule-output-alist prule))
       (outputs-only (strip-cars output-var-pfxr-alist))

       (disjoint-vars (set-difference-eq vars (union$ inputs-only outputs-only)))
       (disjoint-var-fx-list{} (assoc-lst disjoint-vars var-fx-list{}))
       (fixers-assigning-vars-disjoint (strip-cars (strip-cdrs disjoint-var-fx-list{})))


       (- (cw "~| input-var-pfxr-alist:~0 output-var-pfxr-alist:~x1 fixers-assigning-vars-disjoint:~x2, ~%" input-var-pfxr-alist output-var-pfxr-alist fixers-assigning-vars-disjoint))

       )
    `(IMPLIES ,pvar
              (AND ,@(pvars/valid fixers-assigning-vars-disjoint)
                   ,@(connections-vars (compose-conns in-fx-list{} input-var-pfxr-alist))
                   ,(exist-inputs-to-pfxrs lit vars fx-list output-var-pfxr-alist)))))

(defloop generate-prule-instance-clause (lit vars fx-list lit-prules)
  (for ((prule in lit-prules))
       (append (generate-prule-instance-clause1 lit vars fx-list prule))))

(defun filter-rules/lit (lit prules)
  (declare (ignorable lit F))
  (car prules))

(defun C-truth-val-f/p/other-inst3 (lit vars f1xf2yf3z fixers prules)
  (b* ((lit-instance (acl2::subcor-var vars (fixer-output-x-vars f1xf2yf3z) lit))
       ;; TODO ACHTUNG -- what if a lit-instance matches multiple rules??
       (C1 (generate-frule-instance-clause lit vars f1xf2yf3z (filter-sfixes-lit fixers lit)))
       ((when C1) C1)
       (C2s (generate-prule-instance-clause lit vars f1xf2yf3z (filter-rules/lit lit prules))) ;TODO also filter not-variable-disjoint
       ((when C2) C2))
    `((NOT ,(C-truth-val-var lit vars f1xf2yf3z)))))

(defloop C-truth-val-f/p/other-inst2 (f1xf2yf3z-list lit vars fixers prules)
  (for ((f1xf2yf3z in f1xf2yf3z-list))
       (collect (C-truth-val-f/p/other-inst3 lit vars f1xf2yf3z fixers prules))))

(defloop singletonize (xs)
  ;"convert (x1 x2 ... xn) to ((x1) (x2) (x3) ... (xn))"
  (for ((x in xs)) (collect (list x))))

(defloop+ cross-product/binary (A1 A2)
  (for ((a in A1))
       (for ((b in A2))
            (collect (list a b)))))

; (cross-product/binary A1 '()) == (cross-product/binary '() A1) == NULL != (singletonize A1)

(defun generate-all-tuples (A-list)
  "Given Lists A1,A2,...,An generate all n-tuples (a1,...,an) where ai \in Ai"
  (if (endp A-list)
      '()
    (if (endp (cdr A-list))
        (singletonize (car A-list))
        (if (endp (cddr A-list))
          (cross-product/binary (car A-list) (cadr A-list))
          (cross-product/binary (car A-list)
                                (generate-all-tuples (cdr A-list)))))))

;(memoize 'cross-product/binary)
;(memoize 'generate-all-tuples)

(defun C-truth-val-f/p/other-inst1 (lit vars fixers prules)
  (b* ((vars-fx-list-alist (fixer-output-x-alst vars fixers))
       (all-possible-f1xf2yf3z (generate-all-tuples (strip-cdrs vars-fx-list-alist))))
    (C-truth-val-f/p/other-inst2 all-possible-f1xf2yf3z lit vars fixers prules)))

(defloop C-truth-val-f/p/other-inst (lits fixers prules{})
  (for ((lit in lits))
       (C-truth-val-f/p/other-inst1 lit (collect-vars lit) fixers (g1 lit prules{}))))
|#


; TODO -- Make sure there arent two copies of a fixer instance. Is that
; possible? That would create confusion among connections.  No that is not
; possible, there is no concept of "occurrences" or instances of
; fixer-instances.



;; [2016-04-02 Sat]
;; [2017-08-18 Fri] Modified data structure from lits-lst to flits{}
;; term->flits{} added.
; term->flits{} is an alist from each cterm to an alist {(fixername1 . flits_1) ..}
; It corresponds to DNF form, i.e., a sum of products i.e. at least one
; flits_i should be sat, and in flits_i, every lit should be sat.

; [2016-04-02 Sat] Create a pvar holding truth-value of each term
; term->flits{} := ((Rfxgxy . ((Rw1gxy w1=fx) (Rw1w2 w1=fx w2=gxy))) ...)
; Rfxgxy.TRUE => (Rw1gxy.isSAT /\ w1=fx.isSAT) \/ (Rw1w2.isSAT /\ w1=fx.isSAT /\ w2=gxy.isSAT)

(defloop C/sat-lits (lits fixers)
  (for ((l in lits))
       (collect (b* ((cs (pvars/chosen-fixer (list l) (filter-sfixes-lit fixers l)))
                     ((when (= 1 (len cs)))
                      `(IMPLIES ,(pvar/sat-lit l)
                                ,(car cs))))
                  `(IMPLIES ,(pvar/sat-lit l)
                            (OR . ,cs))))))



(defloop sat-literals-lst (flits{})
  (for ((fname-lits in flits{}))
       (collect (b* ((cs (pvars/sat-lit (cdr fname-lits)))
                     ((when (= 1 (len cs))) (car cs)))
                  `(AND . ,cs)))))

(defloop C/sat-terms (term->flits{})
  (for ((term--lits{} in term->flits{}))
       (collect (b* ((cs (sat-literals-lst (cdr term--lits{}))))
                  (if (= 1 (len cs))
                      `(IMPLIES ,(pvar/sat-term (car term--lits{}))
                                ,(car cs))
                    `(IMPLIES ,(pvar/sat-term (car term--lits{}))
                              (OR . ,cs)))))))



; [# Satisfied constraints]
; \Sigma_i \E F_j : sfixes(F_j,c_i) : F_j**c_i
(defun bool->0/1 (b) (declare (xargs :mode :logic))  (if b 1 0))


(defloop num-sat-literals1 (terms)
  (for ((term in terms))
       (collect `(BOOL->0/1 ,(pvar/sat-term term)))))

(defun num-sat-literals (terms)
  `(+ . ,(num-sat-literals1 terms))) ;SIGMA




;; And now for the macro that connects all of the above together
(defun indices-of-len1 (n acc)
  (if (zp n)
      acc
    (b* ((n (1- n)))
      (indices-of-len1 n (cons n acc)))))

(defun indices-of-len (n)
  (indices-of-len1 n '()))

(defun pvars-g-bindings (vars fixers lits terms)
  (b* ((pvars (pvars-fn vars fixers lits terms))
       (n (len pvars))
       (g-booleans (make-list n :initial-element :g-boolean))
       (indices (indices-of-len n))
       (g-boolean-forms (pairlis$ g-booleans indices)))
    (defdata::list-up-lists pvars g-boolean-forms)))





; To compute a substitution from a SAT assignment
; 1. From connection var assignment, get an adjacency list with backward edges
; 2. For each variable, get its final fixer and start from there and go backwards building its assignment entry
(defun make-bedges-adjlist1 (connvar-edges conn-var-table ans)
  "given edges in form of symbols F1xF2, return an adjacency list with
   backward edges of the form (fixer-name . flow-var).
   Initially ans has all fixers mapped to their in-list"
  (if (endp connvar-edges)
    ans
    (b* ((connvar (car connvar-edges))
         ((list from var to) (g1 connvar conn-var-table))
         (in-list (g1 to ans))
         (in-list1 (substitute (cons from var) var in-list))
         (ans1 (put-assoc-equal to in-list1 ans)))
        (make-bedges-adjlist1 (cdr connvar-edges) conn-var-table ans1))))

(defloop fixer-in-list-map (fixer-inst-table)
  (for ((entry in fixer-inst-table))
       (collect (b* (((cons f1-name f1-alist) entry)
                     (f1-in-list (g1 :in f1-alist)))
                  (cons f1-name f1-in-list)))))

(defun make-bedges-adjlist (connvar-edges conn-var-table fixer-inst-table)
  (make-bedges-adjlist1 connvar-edges conn-var-table (fixer-in-list-map fixer-inst-table)))

(defloop filter-true-vars (sat-A vars)
  "given sat-assignment sat-A, filter from vars, those that are assigned T"
  (for ((x-v in sat-A))
       (when (and (cadr x-v)
                  (member-eq (car x-v) vars))
             (collect (car x-v)))))

(defloop final-fixer (x fvars final-value-var-table)
  (for ((fvar in fvars))
       (when (equal x (cadr (g1 fvar final-value-var-table)))
             (return (car (g1 fvar final-value-var-table))))))

(defthm alists-measure-decreases-on-remove1-assoc
  (implies (assoc-equal key alist)
           (< (len (remove1-assoc-equal key alist))
              (len alist))))

(include-book "ordinals/lexicographic-ordering-without-arithmetic" :dir :system)


(defun dag-term-at (fx b-adjlist fxri{} flag)
  "given a acyclic adjlist (with backward edges), and (f . x),
   find the term/expression at that node.
   Note:Each node is a function symbol and the backward-edges are in order of
   the inputs to that node."
  (declare ( xargs :mode :logic
                   :measure (acl2::llist (len b-adjlist) (acl2-count fx)) :well-founded-relation acl2::l<))

  ;(declare (xargs :measure (acl2-count b-adjlist) :hints (("Goal" :in-theory (disable acl2-count))))
(if (eq flag :node)
    (b* (((cons f x) fx)
         ((unless (assoc-equal f b-adjlist))
          (er hard? 'dag-term-at "~| ~x0 not found in adjlist!~%" f))
         (adj-in-nodes (g1 f b-adjlist))
         (b-adjlist1 (remove1-assoc-equal f b-adjlist))
         (in-terms (dag-term-at adj-in-nodes b-adjlist1 fxri{} :nodes))
         (fxri-data (g1 f fxri{}))
         (out-list (g1 :out fxri-data))
         (x-pos (position x out-list))
         (In (g1 :In fxri-data))
         ;(in-terms (cdr (strip-mv-nth term1)))
         (fxr-b (g1 :fixer-let-binding fxri-data))
         (fxr-term (cadr (assoc-eq x fxr-b)))
         (actual-term (if fxr-b ;to let fixer-regression still run
                          (acl2::sublis-var (pairlis$ In in-terms) fxr-term)
                        (cons f in-terms)))
         (dag-term (if (null in-terms)
                       ;;enum exp -- record these so that we can easily find them for Cgen
                       (list :enum f :out x)
                     actual-term))
         )
      (if (and (null fxr-b) ;fixer-regression! HACK
               (consp out-list)
               (consp (cdr out-list)))
          ;;take care of mv expressions here only for fixer-regression!
          (list 'MV-NTH (kwote x-pos)
                (list 'MV-LIST (kwote (len out-list)) dag-term))
        dag-term))
  (let ((fxs fx))
    (if (endp fxs)
      '()
      (cons (dag-term-at (car fxs) b-adjlist fxri{} :node)
            (dag-term-at (cdr fxs) b-adjlist fxri{} :nodes))))))

(defun strip-mv-nth (term)
  (case-match term
    (('MV-NTH & ('MV-LIST & exp)) exp)
    (('MV-NTH & exp) exp)
    (& term)))


(defloop soln-sigma (vars fvars final-value-var-table fxri{} b-adjlist)
  (for ((x in vars))
       (collect (b* ((ffixer-nm (final-fixer x fvars final-value-var-table))
                     (soln-term (dag-term-at (cons ffixer-nm x) b-adjlist fxri{} :node)))
                  (cons x soln-term)))))

(defloop invert-alist (alist)
  (declare (xargs :guard (alistp alist)))
  (for ((x.y in alist)) (collect (cons (cdr x.y) (car x.y)))))


(include-book "simple-graph-array")
(defun let-binding->dep-graph-alst (vt-lst ans)
  "Walk down the var-term list vt-lst and add edges.
   Build graph alist in ans"
  (if (endp vt-lst)
      ans
    (b* (((list var term) (car vt-lst))
         (fvars (all-vars term)));only non-buggy for terms
      (let-binding->dep-graph-alst
       (cdr vt-lst)
       (cgen::union-entry-in-adj-list var fvars ans)))))

(defun get-ordered-alst (keys alst ans)
  (declare (xargs :guard (and (true-listp keys) (alistp ans) (alistp alst))))
  "accumulate entries of alist in ans in the order of keys"
  (if (endp keys)
    ans
    (let ((at (assoc-equal (car keys) alst)))
      (if at
        (get-ordered-alst (cdr keys) alst (append ans (list at)))
        (get-ordered-alst (cdr keys) alst ans)))))

(defun do-let*-ordering1 (vars vt-lst debug-flag)
  (declare (xargs :guard (symbol-alistp vt-lst)
                  :mode :program))
  (b* ((dep-g (let-binding->dep-graph-alst vt-lst
                                           (cgen::make-empty-adj-list vars)))
       (sorted-vars (cgen::approximate-topological-sort dep-g debug-flag)))
    (get-ordered-alst (reverse sorted-vars) vt-lst nil)))

(defloop subst-common-subterms-with-corr-vars (alist es)
  "specialized function for convert-to-let*-binding"
  (for ((e in es)) (collect (acl2::sublis-expr (remove1-assoc-equal e alist) e))))

(defun dlist-to-alist (dlist)
  (pairlis$ (strip-cars dlist) (strip-cadrs dlist)))


;; (defun flatten-mv-nth-term (exp ans)
;;   (cond ((or (variablep exp) (quotep exp)) (mv exp ans))
;;         ((eq (ffn-symb exp) 'MV-NTH)
;;          (b* ((f-exp (third exp))
;;               ((unless (consp f-exp)) (mv exp ans))
;;               (f-nm (car f-exp))
;;               (new-var-nm (s+ f-nm "-OUT"))
;;               ((mv f-exp1 ans) (flatten-mv-nth-term f-exp ans)))
;;            (mv (list 'MV-NTH (second exp) new-var-nm) (put-assoc-equal new-var-nm f-exp1 ans))))
;;         (t (b* (((cons f args) exp)
;;                 (mv args1 ans) (flatten-mv-nth-terms args ans))
;;              (mv (cons f args1) ans)))))


;; (defun flatten-mv-nth-terms/alist1 (x-exps ans)
;;   (if (endp x-exps)
;;       ans
;;     (b* (((cons x exp) (car x-exps))
;;          ((mv exp1 ans) (flatten-mv-nth-term exp ans)))
;;       (flatten-mv-nth-terms/alist1 (cdr x-exps) (append ans (list (cons x exp1)))))))



;; (defun flatten-mv-nth-terms/alist (A)
;;   (flatten-mv-nth-terms/alist1 A '()))

(mutual-recursion
(defun replace-enum-exp-with-out-var/term (e)
  (cond ((proper-symbolp e) e)
        ((quotep e) e)
        (t (if (and (consp e) (eq (car e) :enum))
               (nth 3 e) ;get the out var
             (cons (car e)
                   (replace-enum-exp-with-out-var/terms (cdr e)))))))
(defun replace-enum-exp-with-out-var/terms (es)
  (if (endp es)
      '()
    (cons (replace-enum-exp-with-out-var/term (car es))
          (replace-enum-exp-with-out-var/terms (cdr es))))))

(defloop remove-x=x-bindings (dlist)
  (for ((x--xval in dlist))
       (append (and (not (equal (car x--xval) (cadr x--xval)))
                    (list x--xval)))))

(defun convert-to-let*-binding (A)
  (declare (xargs :guard (symbol-alistp A) :mode :program))
  (b* (;(A (flatten-mv-nth-terms A))
       (exp->var-map (invert-alist A))
       (svals (subst-common-subterms-with-corr-vars exp->var-map (strip-cdrs A)))
       (svals (replace-enum-exp-with-out-var/terms svals))
       (vars (strip-cars A))
       (let*-b (acl2::listlis vars svals))
       (let*-b (remove-x=x-bindings let*-b))
       (let*-b (do-let*-ordering1 vars let*-b nil))
       )
    let*-b))


(defun soln-sigma-top (sat-assignment vars fxri{})
  (b* ((fixers (strip-cdrs fxri{}))
       (pvars/valid (filter-true-vars sat-assignment (pvars/valid fixers)))
       ;;ignore fixers that are not valid
       (valid-var-table (valid-var-table fixers))
       (valid-var-table/true (cgen::assoc-lst pvars/valid valid-var-table))
       (fixer-names/valid (strip-cdrs valid-var-table/true))
       (fxri{}/valid (cgen::assoc-lst fixer-names/valid fxri{}))

       (conn-var-table (connection-var-table vars fixers))
       (final-value-var-table (final-value-var-table vars fixers))

       (fixers/valid (strip-cdrs fxri{}/valid))
       (connvar-edges (filter-true-vars sat-assignment
                                        (pvars/conn fixers/valid vars)))
       (bedges-adjlist (make-bedges-adjlist connvar-edges conn-var-table
                                            fxri{}/valid))

       (final-value-vars (filter-true-vars sat-assignment
                                           (pvars/final vars fixers/valid)))
       ;;INvariant -- each variable should have atleast one
       ;;"fixer"/enum, o.w. we cant make a soln-sigma for vars
       (- (assert$ (= (len vars) (len final-value-vars)) "Invariant broken: Some var does not have a final-value expression!"))
       (A (soln-sigma vars final-value-vars final-value-var-table
                      fxri{}/valid
                      bedges-adjlist)))
    A))


(defun make-GL-SAT-encoding (vars lits term->flits{} fxri{})
; return (mv bindings hyp concl-hyp)
;  (declare (xargs :mode :program :stobjs (state)))
  (b* ((fixers (strip-cdrs fxri{}))
       (terms (strip-cars term->flits{}))
       (bindings (pvars-g-bindings vars fixers lits terms))
       (hyp `(AND . ,(pvars-type-constraints vars fixers lits terms)))
       (concl-hypothesis `(AND . ,(append
                                   (C/atleast-one-final-value vars fixers)
                                   ;;(C/atmost-one-final-value vars fixers)
                                   (C/final-value-implies-valid vars fixers)
                                   (C/connection-implies-valid fixers vars)
                                   (C/atmost-one-input-conn fixers vars)
                                   (C/atleast-one-input-conn fixers vars)
                                   (C/trans fixers vars)
                                   (C/no-cycles fixers)
                                   (C/final-value-def vars fixers)
                                   (C/TheFixer-is-preserved lits fixers)
                                   (C/TheChosenFixer lits fixers)
                                   ;; [2016-09-07 Wed] added for optimization purposes
                                   (C/valid-fixes-at-least-one-lit fixers lits)
                                   (C/sat-lits lits fixers)
                                   (C/sat-terms term->flits{})))
                                   ))

    (mv bindings hyp concl-hypothesis)))




(defun fixers-sat-glcp-query (num-sat-lits top-hyps bindings trhyp concl-hyp vl state)
  (declare (xargs :mode :program :stobjs (state)))
  (b* (((mv start-sat-query state) (acl2::read-run-time state))
       (concl `(IMPLIES ,concl-hyp
                        (NOT (EQUAL ,(num-sat-literals top-hyps)
                                    ,num-sat-lits))))
       (ctx 'fixers-sat-glcp-query)
       ((er trconcl) (acl2::translate concl t t nil ctx (w state) state))
       (concl-vars (collect-vars trconcl))
       (missing-vars (set-difference-eq concl-vars (strip-cars bindings)))
       (- (and missing-vars
                (let ((msg (acl2::msg "~
The following variables are present in the theorem but have no symbolic object ~
bindings:
~x0~%" missing-vars)))
                  (cw? (normal-output-flag vl) "****  ERROR ****~%~@0~%" msg))))
       ((when missing-vars) (mv :missing-vars nil state))

       (param-bindings nil)
       (trparam nil)
       (config (gl::make-glcp-config
                :abort-ctrex t
                :abort-vacuous t
                :n-counterexamples 1))
       ((acl2::local-stobjs gl::interp-st)
        (mv err ans gl::interp-st state))
       ((mv erp ?val gl::interp-st state)
        (gl::glcp nil (list bindings param-bindings
                            trhyp trparam trconcl
                            concl config)
                  gl::interp-st state))
;if no error, return as it is, o.w. below report sat assignment
       ((mv end-sat-query state) (acl2::read-run-time state))
       (- (cw? (verbose-stats-flag vl)
               "~|Cgen/Note: GL/SAT Engine: Time taken = "))
       ((mv err & state) (if (verbose-stats-flag vl)
                             (pprogn (print-rational-as-decimal (- end-sat-query start-sat-query)
                                                                (standard-co state)
                                                                state)
                                     (princ$ " seconds" (standard-co state) state)
                                     (newline (standard-co state) state)
                                     (newline (standard-co state) state)
                                     (value :invisible))
                           (value nil)))
       ((when err) (mv err nil gl::interp-st state))
       ((unless erp) (mv :unsat nil gl::interp-st state))
       (x  (car (@ gl::glcp-counterex-assignments))) ;only pick the first
       (sat-A (gl::glcp-obj-ctrex->obj-alist x)))
    (mv nil sat-A gl::interp-st state)))

(defun fixers-maxsat-glcp-query-loop (n top-hyps bindings trhyp concl-hyp mode vl state)
  (declare (xargs :mode :program :stobjs (state)))
  (if (zp n)
    (mv :unsat nil 0 state) ;nothing satisfied
    (b* (((mv erp A state) (fixers-sat-glcp-query n top-hyps bindings trhyp concl-hyp vl state))
         ((unless erp) ;got sat assignment
          (prog2$
           (cw? (verbose-stats-flag vl) "~|Got a sat assignment for #literals = ~x0~%" n)
           (mv nil A n state)))
         ((when (eq mode :sat)) ;dont continue maxsat loop if in this mode
          (mv erp A n state))

         )
      (fixers-maxsat-glcp-query-loop (1- n) top-hyps bindings trhyp concl-hyp mode vl state))))



; fxri{} is the fixer instance metadata table
(defun fixers-maxsat-glcp-query (vars lits term->flits{} relevant-hyps fxri{} mode vl state)
  (declare (xargs :mode :program :stobjs (state)))
  (b* (((when (or (null vars)
                  (null lits)
                  (null term->flits{})
                  (null relevant-hyps)
                  )) ;pathological cases
        (mv :null nil state)); abort, treat as error
       (ctx 'fixers-maxsat-glcp-query)
       ((mv start-code-gen state) (acl2::read-run-time state))

       ((mv bindings hyp concl-hyp)
        (make-GL-SAT-encoding vars lits term->flits{} fxri{}))
       ((mv end-code-gen state) (acl2::read-run-time state))
       (- (cw? (debug-flag vl) "~|concl-hyp is ~x0~%" concl-hyp))
       (- (cw? (verbose-stats-flag vl)
               "~|Cgen/Note: fixer-sat-encoding: Time taken = "))
       ((er &) (if (verbose-stats-flag vl)
                       (pprogn (print-rational-as-decimal (- end-code-gen start-code-gen)
                                                      (standard-co state)
                                                      state)
                           (princ$ " seconds" (standard-co state) state)
                           (newline (standard-co state) state)
                           (newline (standard-co state) state)
                           (value :invisible))
                 (value nil)))

       ((er trhyp) (acl2::translate hyp t t nil ctx (w state) state))



       ((mv erp sat-A ?n state)
        (fixers-maxsat-glcp-query-loop (len relevant-hyps)
                                       relevant-hyps ;[2016-05-04 Wed] only count these
                                       bindings trhyp concl-hyp
                                       mode
                                       vl state))
        ((when erp) ;unsat or error, abort
         (mv erp nil state))
        (terms (strip-cars term->flits{}))
        (fixers (strip-cdrs fxri{}))
        (all-basis-pvars (append (pvars/chosen-fixer lits fixers)
                                 (pvars/final vars fixers)
                                 (pvars/conn fixers vars)
                                 (pvars/valid fixers)
                                 (union-equal (pvars/sat-term terms)
                                              (pvars/sat-lit lits))))
        (pvars/true (filter-true-vars sat-A all-basis-pvars))
        (sat-A/true (acl2::listlis pvars/true (make-list (len pvars/true) :initial-element 't)))
        (- (cw? (debug-flag vl) "True pvars: ~x0~%" (filter-true-vars sat-A (pvars-fn vars fixers lits terms))))
        (- (cw? (verbose-stats-flag vl) "SAT Assignment: ~x0~%" sat-A/true))
        )
    (mv nil sat-A/true state)))

(defun fxri-let*-soln/gl (flits term->flits{} relevant-terms fxri{} vl state)
  ;; return (mv erp (list let*-binding satisfied-terms) state)
  (declare (xargs :stobjs (state)))
  (b* ((flits-vars (acl2::all-vars1-lst flits '()))
       (- (acl2::tshell-ensure))
       ((mv erp sat-A state)
        (fixers-maxsat-glcp-query flits-vars
                                  flits
                                  term->flits{}
                                  relevant-terms
                                  fxri{}
                                  :maxsat ;maxsat loop
                                  vl state))

       ((when (equal :null erp))
        (value (list nil nil)))

       ((when (equal :unsat erp))
        (progn$
         (cw? (verbose-flag vl)
              "~| Cgen/Note: GL query is UNSAT. No fixer arrangement found for~%")
         (cw? (verbose-flag vl) "~| ~x0~%" relevant-terms)
         (value (list nil nil))))

       (rterms-pvars/sat (pvars/sat-term relevant-terms))
       (rterms-pvars/true (filter-true-vars sat-A rterms-pvars/sat))
       (rterms/true (strip-cdrs (cgen::assoc-lst rterms-pvars/true
                                                (pairlis$ rterms-pvars/sat relevant-terms))))


       (ssigma (soln-sigma-top sat-A flits-vars fxri{}))
       (let*-soln0 (convert-to-let*-binding ssigma)))
    (mv erp (list let*-soln0 rterms/true) state)))

(include-book "cgen-state")
(defttag t)
(defattach (fxri-let*-soln fxri-let*-soln/gl) :skip-checks t)
(defttag nil)


(in-theory (disable Implies))

  ;; + Backend/GL engine interface -- We have as inputs, the literals (of
  ;;   desired shape), the dynamic fixer-instance table with the relevant
  ;;   metadata instantiated and also weights for each literals to be
  ;;   used in the MAX-SAT encoding. We return either :UNSOLVABLE or the
  ;;   assignment/arrangement A that maximises the objective function.
  ;;   #+BEGIN_SRC lisp
  ;;     (defun fixer-arrangement (lits fixer-instance-table frule-instances prule-instances litWeight{} state)
  ;;       "Given lits (of a certain shape), the fixer-instance-table
  ;;     comprising of fixers relevant to lits, and literal weights, find an
  ;;     arrangement A (i.e. a substitution of fixer terms to variables of
  ;;     lits) that maximizes Sum(lit|A == t * litWeight{lit})."
  ;;       (mv boolean (or :unsolvable A) state))
  ;;   #+END_SRC
