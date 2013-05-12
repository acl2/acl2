

(in-package "GL")

(include-book "bfr")
(include-book "gl-doc-string")

(defdoc experimental-aig-reasoning
  ":Doc-section ACL2::GL
  Note about GL's experimental AIG reasoning mode.~/

  By default, GL operates on BDD-based data structures and resolves Boolean
reasoning questions using BDD operations.  However, it also has some support
for a different mode that uses And-Inverter graphs instead.
Using AIG mode requires a way to solve Boolean satisfiability problems on AIGs.
We provide one method, of dubious utility, which is to transform the AIG into a
BDD.  This mode may be used by including the book \"bfr-aig-bddify\" and then
running (GL-AIG-BDDIFY-MODE), which is an ACL2 event.  (To return to the
default BDD-only mode, simply run (GL-BDD-MODE).)  We describe below the
mechanisms provided for putting GL into different reasoning modes.  These
mechanisms may be used, by an adventurous user, to attach an external SAT
solver and use that to solve AIG satisfiability queries, avoiding the necessity
of the AIG to BDD transformation.  ~/

GL can be put into different modes using ~il[defattach].  There are several
functions that need to have proper attachments in order for GL to function;
when the GL library is loaded, they are set up to a default configuration in
which GL will use BDD-based reasoning.

The functions that need attachments follow.  Here, BFR stands for Boolean
function representation.

 * BFR-MODE: 0-ary with no constraints.  This detemines whether the Boolean
function components in the symbolic object representation are BDDs or AIGs, and
thus the functions used to combine them.  E.g., the definition of BFR-NOT
is (basically):

~bv[]
 (if (bfr-mode) (aig-not x) (q-not x)).
~ev[]

Similarly, BFR-EVAL either applies EVAL-BDD or AIG-EVAL, depending on BFR-MODE.

By default the function BFR-BDD (which returns NIL) is attached to BFR-MODE,
and thus BFR-NOT uses the BDD operation Q-NOT.  To use AIGs instead, attach
BFR-AIG, which returns T.  

 * BFR-SAT: Unary, returning three values: SAT, SUCCEEDED, CTREX.  The main
constraint of BFR-SAT is that if it returns SAT=NIL and SUCCEEDED=T, then
BFR-EVAL of the input on any environment must be NIL, i.e., the input must be
an unsatisfiable BDD or AIG (depending on the BFR-MODE.)  The CTREX value
should be a counterexample in the case of a SAT result, represented either as a
BDD or an alist mapping variables to Boolean values; see below under
BFR-COUNTEREX-MODE.

To satisfy the constraint in the BDD case, it suffices to simply check whether
the input BDD is NIL; if so, it is satisfiable, and otherwise, it isn't.  This
method is implemented as BFR-SAT-BDD, which is the default attachment of
BFR-SAT.  For AIG mode, we provide an attachment BFR-SAT-BDDIFY which solves an
AIG satisfiability query by transforming the input AIG into a BDD.  However,
one might instead hook up a SAT solver into ACL2 so that it can take an AIG as
input.  Given a way of calling such an external tool, it would not be difficult
to produce a function that conforms to the constraint described above. :-)

 * BFR-COUNTEREX-MODE: 0-ary, no constraints.  This says whether the
counterexample value sometimes returned by BFR-SAT is in the form of a BDD or
an association list.  If it is set up wrong, then output in case of a
counterexample will be garbled.  In both the default BDD mode and in the AIG
BDDIFY mode provided, the counterexample is in the form of a BDD, and so we
attach BFR-COUNTEREX-BDD by default.  However, if an external SAT solver is
used, then there will likely be a single assignment returned, which might more
conveniently be provided as an alist.  Then one would instead attach
BFR-COUNTEREX-ALIST.
~/
")

(encapsulate
  (((bfr-sat *) => (mv * * *)))

  (local (defun bfr-sat (prop)
           (declare (xargs :guard t))
           (mv nil nil prop)))

  (defthm bfr-sat-nvals
    (equal (len (bfr-sat prop)) 3))

  (defthm bfr-sat-true-listp
    (true-listp (bfr-sat prop)))

  (defthm bfr-sat-unsat
    (mv-let (sat succeeded ctrex)
      (bfr-sat prop)
      (declare (ignore ctrex))
      (implies (and succeeded (not sat))
               (not (bfr-eval prop env))))))

(defun bfr-sat-bdd (prop)
  (declare (xargs :guard t))
  (if (bfr-mode)
      (mv nil nil nil) ;; AIG-mode, fail.
    (let ((sat? (acl2::eval-bdd prop (acl2::bdd-sat-dfs prop))))
      (mv sat? t prop))))

(defthm bfr-sat-bdd-unsat
  (mv-let (sat succeeded ctrex)
    (bfr-sat-bdd prop)
    (declare (ignore ctrex))
    (implies (and succeeded (not sat))
             (not (bfr-eval prop env))))
  :hints(("Goal" :in-theory (e/d (bfr-eval)
                                 (acl2::eval-bdd-ubdd-fix))
          :use ((:instance acl2::eval-bdd-ubdd-fix
                           (x prop))))))

(acl2::defattach
 (bfr-sat bfr-sat-bdd
          :hints (("goal" :in-theory '(bfr-sat-bdd-unsat)))))



;; In the AIG case, the counterexample returned is either an alist giving a
;; single satisfying assignment or a BDD giving the full set of satisfying
;; assignments.
(defstub bfr-counterex-mode () t)
(defun bfr-counterex-alist ()
  (declare (Xargs :guard t))
  t)
(defun bfr-counterex-bdd ()
  (declare (xargs :guard t))
  nil)

(acl2::defattach bfr-counterex-mode bfr-counterex-bdd)


;; Given a non-NIL BDD, generates a satisfying assignment (a list of Booleans
;; corresponding to the decision levels.)  The particular satisfying assignment
;; chosen is determined by the sequence of bits in the LST argument.
(defun to-satisfying-assign (lst bdd)
  (declare (xargs :hints (("goal" :in-theory (enable acl2-count)))))
  (cond ((atom bdd) lst)
        ((eq (cdr bdd) nil) (cons t (to-satisfying-assign  lst (car bdd))))
        ((eq (car bdd) nil) (cons nil (to-satisfying-assign  lst (cdr bdd))))
        (t (cons (car lst) (to-satisfying-assign
                            (cdr lst)
                            (if (car lst) (car bdd) (cdr bdd)))))))

(defthm to-satisfying-assign-correct
  (implies (and bdd (acl2::ubddp bdd))
           (acl2::eval-bdd bdd (to-satisfying-assign lst bdd)))
  :hints(("Goal" :in-theory (enable acl2::eval-bdd acl2::ubddp))))

(defun bfr-ctrex-to-satisfying-assign (assign ctrex)
  (if (eq (bfr-counterex-mode) t) ;; alist
      ctrex
    (to-satisfying-assign assign ctrex)))
