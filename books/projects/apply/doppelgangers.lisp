; Copyright (C) 2016, ForrestHunt, Inc.
; Written by Matt Kaufmann and J Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Portcullis:
; (include-book "apply-prim")

; The Doppelgangers for user-book.lisp

; This file defines the doppelgangers for a particular book, namely
; user-book.lisp.  This is part of our demonstration that the apply$ theory is
; meaningful:

;  For any given world, we could define attachments for the two critical apply$
;  stubs -- badge-userfn and apply$-userfn -- such that all apply$ warrants
;  issued in that world are valid in the resulting evaluation theory.

(in-package "ACL2")

; doppelganger (Wikipedia):  a look-alike or double of a living person

; In our usage, we speak of the doppelgangers of functions in the current
; world.  It will turn out that the doppelgangers of the two critical apply$
; stubs are suitable attachments for those constrained functions and they make
; all the warrants valid in the evaluation theory.  The only reason we
; introduce the notion of doppelganger is to establish that the apply$ theory
; is meaningful (i.e., that theorems burdened by warrants are not vacuously
; valid because the warrants are invalid)..  There is no need to implement the
; construction of doppelgangers although one can imagine doing so in order to
; eliminate all ``magic'' associated with apply$ at the expense of tying apply$
; to a fixed collection of warranted functions.

; TODO: An enterprising masters student might want to mechanize the
; doppelganger construction.  He or she will probably find -- at the very least
; -- some nuances of the construction that are unmentioned here.  And he or she
; might find additional necessary restrictions on def-warrant!

; Convention: In this exercise, the doppelganger of a function is named by
; appending an exclamation mark at the end of the function's name; the
; doppelganger of AP will be named AP! and that of APPLY$ will be named
; APPLY$!.  Of course, this convention only guarantees uniqueness if no
; function in the user's book ends with an exclamation mark.  That is true for
; our sample user-book.lisp.

; Doppelgangers may change as the world evolves, in particular, as functions
; acquire badges and warrants.  It is easiest to think of the entire set of
; doppelgangers being recomputed each time the world changes and then the new
; doppelgangers for badge-userfn and apply$-userfn are attached to those
; functions.  (Since the doppelgangers of all mapping functions are defined
; together in a mutually recursive clique with the doppelganger of apply$, the
; doppelganger of collect, say, changes just by the addition of a new mapping
; function, e.g., sumlist.)

; Since we're imagining changing the attachments to badge-userfn and
; apply$-userfn every time the world changes, and each time we change the
; attachments we (re-) compute and defun all the doppelgangers, we actually
; have to imagine generating a whole sequence of new names for each
; doppelganger, e.g., COLLECT!, COLLECT!1, COLLECT!2, ...  if they're all
; theoretically co-existing in the evaluation theory.  So really our simple
; convention of affixing an exclamation mark is just shorthand for ``generate a
; new function name.''  End of Convention.

; In this file we define the doppelgangers of all the functions introduced in
; the book user-book.lisp, as an illustration of how to construct
; doppelgangers.

; Why do we need doppelgangers?

; Consider the goal of defining a function that we can attach to
; apply$-userfn.  That function will turn out to be what we're calling
; apply$-userfn!.  But for the moment let's just call that attachment foo.  We
; want (defun foo (fn args) ...) so that (defattach apply$-userfn foo) is
; acceptable.

; How do we define foo?  In this exercise we'll use AP, REV, and COLLECT as
; generic examples of functions with warrants.  The first two are tame,
; user-defined functions.  The third is a user-defined mapping function.  Their
; definitions are:

; (defun$ ap (x y)
;   (if (consp x)
;       (cons (car x) (ap (cdr x) y))
;       y))

; (defun$ rev (x)
;   (if (consp x)
;       (ap (rev (cdr x)) (cons (car x) nil))
;       nil))

; (defun$ collect (lst fn)
;   (cond
;    ((endp lst) nil)
;    (t (cons (apply$ fn (list (car lst)))
;             (collect (cdr lst) fn)))))

; The most ``natural'' definition (ignoring the issue of guards) of our
; intended attachment for apply$-userfn is something like:

; (defun foo (fn args)
;   (case fn
;     (AP (ap (car args) (cadr args)))
;     (REV (rev (car args)))
;     ...
;     (COLLECT 
;      (if (tamep-functionp (cadr args))
;          (collect (car args) (cadr args))
;          (untame-apply$ fn args)))
;     ...
;     ))

; But then

; (defattach apply$-userfn foo)

; is illegal because it violates the acyclicity restriction of the extended
; ancestor relation discussed in the Essay on Defattach: foo calls all of the
; user's warranted functions, including the mapping functions like collect, but
; collect calls apply$, and apply$ calls apply$-userfn.

; Our intended attachment to apply$-userfn is not allowed to call the user's
; mapping functions!

; Doppelgangers resolve this problem.  Instead of calling ap, rev, and collect,
; our foo will call their doppelganers, ap!, rev!, and collect!, where the
; definitions of the doppelgangers are identical to their counterparts except
; for names (and the important fact that collect! will be in a mutually
; recursive clique discussed below):

; (defun ap! (x y)
;   (if (consp x)
;       (cons (car x) (ap! (cdr x) y))
;       y))

; (defun rev! (x)
;   (if (consp x)
;       (ap! (rev! (cdr x)) (cons (car x) nil))
;       nil))

; (defun collect! (lst fn)
;   (cond
;    ((endp lst) nil)
;    (t (cons (apply$! fn (list (car lst)))
;             (collect! (cdr lst) fn)))))

; Note that in recursion the doppelgangers call themselves, i.e., ap! calls ap!
; recursively.  Note that rev! calls itself, rev!, but also calls ap!, not ap.
; And note that collect! calls itself and also apply$! -- the doppelganger of
; apply$.  In particular, collect! does not call apply$.

; Of course, this begs the question because now we have to define collect! and
; apply$! and apply$-userfn! in a mutually recursive clique.  But it turns out
; that because of the restrictions imposed during the issuance of warrants we
; can actually generate a measure to justify that clique.

; The definition of foo we want is just the doppelganger of the foo we showed
; above, only now we will give it its real name: apply$-userfn!, the
; doppleganger of apply$-userfn.

; (defun apply$-userfn! (fn args)
;   (case fn
;     (AP (ap! (car args) (cadr args)))
;     (REV (rev! (car args)))
;     ...
;     (COLLECT 
;      (if (tamep-functionp! (cadr args))
;          (collect! (car args) (cadr args))
;          (untame-applY$ fn args)))
;     ...
;     ))

; Ignoring the issue of guards, the above definition of apply$-userfn! is the
; one we use.

; Observe that its case split is on the user's (warranted) function names, AP,
; REV, COLLECT, etc., but that it actually calls their doppelgangers.  Also
; observe that on mapping functions (i.e., those whose :ilks are not t, like
; COLLECT) it checks the tamep requirements (as per each warrant) before
; calling the doppelganger.

; (defattach apply$-userfn apply$-userfn!) is legal: there are no cycles in
; the ancestor relation because apply$-userfn! uses a completely disjoint set
; of admissible definitions.

; But legal defattaches are a dime-a-dozen!  All you have to do is satisfy the
; constraints on the two critical apply$ stubs and those constraints are pretty
; minimal.  (For example, we could define the attachment for badge-userfn to
; return some constant badge and the attachment for apply$-userfn (which is
; completely unconstrained) to be any function at all.  So, completely crazily,
; (apply$ 'COLLECT args) could be (REV (car args)).)

; The more interesting challenge is to show that our choice of attachments
; makes all the warrants valid in the evaluation theory.  We do not do this in
; this book.  It is done instead in the book evaluation-theory, which we will
; build on top of this book of doppelgangers.  But by way of foreshadowing: the
; doppelgangers make the warrants valid because in the evaluation theory, where
; (defun apply$-userfn (fn args) (apply$-userfn! fn args)), we can prove that
; every doppelganger is equal to its counterpart:

; (ap! x y)         = (ap x y)
; (rev! x)          = (rev x)
; (collect! lst fn) = (collect lst fn)

; We'll revisit this in evaluation-theory.lisp later.  For the moment we focus
; on the definitions of the doppelgangers of the warranted functions in
; user-book.lisp.

; The fact that the validity of warrants in the evaluation theory is ``more
; interesting'' than the fact that doppelgangers allow some attachments to
; badge-userfn and apply$-userfn ignores a crucial question: can we really
; admit the doppelgangers as a chronology?  The questions to think about as we
; proceed include: what, exactly, is the algorithm for producing the
; doppelgangers, in what order do we introduce them, and how do we justify each
; one?

; [Matt: Another crucial question is: what impact do doppelgangers have on
; defattach?  In particular, note that if the attachment to apply$-userfn is
; its doppelganger, and if the doppelganger calls the doppelgangers of user
; functions, then what happens if the user does a defattach to one of the user
; functions?  To be concrete, apply$-userfn has apply$-userfn! as its
; attachment and apply$-userfn! calls collect!.  So if the user attaches foo to
; collect, it theoretically shouldn't affect apply$-userfn! at all: collect and
; collect! are different functions.  Furthermore, if foo is attachable to
; collect, then I believe that (foo lst fn) and (collect lst fn) are provably
; equal in the evaluation theory, and I demonstrate in evaluation-lemmas.lisp
; that (collect! lst fn) and (collect lst fn) are provably equal in the
; evaluation theory.  Finally, since collect is defun'd, the only way the user
; can get away with attaching foo to collect is with :attach nil, which means
; we don't actually change the runtime behavior of collect: it still executes
; the old defun of collect, not foo.  This may matter if we shift to ACL2(a)
; because in that implementation the actual attachment for apply$-userfn calls
; collect, not collect!.  Collect! doesn't really exist.  So, if attachments to
; defuns DID change runtime behavior (contrary to what I think happens) it
; would that attachment to collect would change apply$-userfn's runtime
; behavior, which is contrary to the construction of apply$-userfn! here.

; Still another question is how does this whole doppelganger story get along
; with the rest of the defattach story?  What happens if the user has a bunch
; of other attachments in place?  Do we understand the ``J button'' to mean:

;  compute and define all the doppelgangers and then do:
;  (defattach badge-userfn badge-userfn!)
;  and
;  (defattach apply$-userfn apply$-userfn!)

; If so, WHEN in the whole defattach story do we push the J button?]

; Recall that three categories of functions have badges.  The names we'll
; use for these categories are shown below: 

; - primitives: the 800+ apply$ primitives (all listed in *badge-prim-falist*
;   defined in apply-prim.lisp)

; - boot functions: the 6 apply$ boot functions (all listed in
;   *apply$-boot-fns-badge-alist* defined in constraints.lisp), and

; - user functions: all the user-defined functions (listed in the badge-table's
;   :badge-userfn-structure, initialized in constraints.lisp and maintained by
;   def-warrant in apply.lisp)

; Aside: The two lists attributed to constraints.lisp above are also actually
; introduced identically in this file.  Doppelgangers.lisp is designed to
; replace constraints.lisp as the portcullis for apply.lisp so we can build an
; ``evaluation theory'' version of apply.lisp.  End of Aside.

; Despite the name ``user functions'' it is possible that the badge-table's
; :badge-userfn-structure lists functions other than ones defined by the user!
; The user might verify-termination for an ACL2 system function and then
; def-warrant it.  ``User function'' really means: functions given badges by
; non-erroneous def-warrant events.

; A (badged) function symbol is ``tame'' iff the :ilks in its badge is T (i.e.,
; all formals have ilk NIL).  A (badged) function that is not tame is called a
; ``mapping function.''  A mapping function has at least one formal with ilk
; :FN or :EXPR (or else its :ilks would be T).  So tame and mapping functions
; form a partitioning of the badged functions.

; Recall also that the (badged) functions can be partitioned into warranted and
; unwarranted functions.  Functions that return multiple values but otherwise
; respect the rules regarding warrants have badges but not warrants.  This
; partitioning cuts across the tame versus mapping function partitioning: both
; tame and mapping functions can be warranted or unwarranted.

; The distinction is important because the doppelgangers of all mapping
; functions -- whether warranted or not -- must be in the mutually recursive
; clique with apply$!, but only the warranted user functions are called by
; apply$-userfn!.  So below we will carefully say ``warranted'' when we mean to
; deal with that subset of the badged functions.

; The fundamental activity in creating doppelgangers is copying the definitions
; of the functions and changing some names.

; The primitives do not have doppelgangers.  When defining the
; doppelganger of some function whose definition calls a primitive, we just
; call the primitive by its standard name.

; The boot functions have doppelgangers.  The doppelgangers of the tame
; functions among the boot functions (BADGE, TAMEP, TAMEP-FUNCTIONP, and
; SUITABLY-TAMEP-LISTP) are treated just like other tame functions (of ``Group
; 1'' below).  You can see their doppelgangers below, e.g., look for
; ``TAMEP!''.  The other two boot functions are mapping functions: APPLY$ and
; EV$.  Their doppelgangers are handled specially and you can see their
; definitions below as part of the big mutually recursive clique with the
; user's mapping functions.  Also part of that clique is the doppelganger for
; EV$-LIST which mutually recursive with APPLY$ and EV$ but not badged simply
; because we didn't think it was a function anybody would want to apply.

; The user functions all have doppelgangers as described here:

; Doppelganger construction starts by partitioning the user functions into
; three groups:

; Group 1: tame functions not ancestrally dependent on apply$,
; Group 2: tame functions ancestrally dependent on apply$.
; Group 3: mapping functions

; Below we give examples of these three groups of functions.  These examples
; are all drawn from user-book.lisp.  Indeed, that file intentionally
; illustrates many different definitional schemas to stress the process of
; doppelganger construction.  We urge the reader to refer to user-book.lisp
; when we discuss a function here without giving its definition explicitly.

; Examples of Group 1 (tame functions not ancestrally dependent on apply$) are
; the familiar AP and REV.  Defining doppelgangers for these functions is
; straightforward: copy the definition and change the names of all boot
; functions and user functions to their doppelgangers.

; E.g., the defun of REV is

; (defun rev (x)
;   (if (consp x)
;       (ap (rev (cdr x)) (cons (car x) nil))
;       nil))

; and its doppelganger is

; (defun rev! (x)
;   (if (consp x)
;       (ap! (rev! (cdr x)) (cons (car x) nil))
;       nil))

; Note that where REV calls the tame user functions AP and REV, its
; doppelganger calls their doppelgangers, AP! and REV!.  Primitives like consp
; and car are left as is.

; Examples of Group 2 functions (tame functions that ancestrally depend on
; apply$) include these two:

; (defun$ collect-rev (lst)
;    (collect lst 'REV))

; and

; (defun$ sum-of-products (lst)
;   (sumlist lst
;            '(LAMBDA (X)
;                     (FOLDR X
;                            '(LAMBDA (I A)
;                                     (BINARY-* I A))
;                            '1))))

; (Aside: (sum-of-products '((1 2 3) (4 5 6) (7 8 9)))
;         = (+ (* 1 2 3) (* 4 5 6) (* 7 8 9))
;         = 630,

; as is established by

; (thm (implies (apply$-warrant-FOLDR)
;               (equal (sum-of-products '((1 2 3) (4 5 6) (7 8 9)))
;                      630))
;      :hints (("Goal" :expand ((:free (x) (HIDE x))))))
; End of Aside)

; We cannot define the doppelgangers of these functions as we did the Group 1
; tame functions because they are defined before we've introduced the mapping
; functions like collect and foldr.  We could include the Group 2 functions
; into the mutually recursive clique with Group 3, but that complicates the
; measure for that clique.  Instead we appeal to a little trick: we define the
; Group 2 functions without actually calling any mapping functions.

; Every tame call of a mapping function can be replaced by a call of an
; ordinary tame helper function specially defined for that call.

; Consider the call: (collect lst 'REV).  Let's derive a function g so that (g
; lst) = (collect lst 'REV).

; Step 1: Copy the definition of collect changing `collect' to `g':
; (defun g (lst fn)
;   (cond ((endp lst) nil)
;         (t (cons (apply$ fn (list (car lst)))
;                  (g (cdr lst) fn)))))

; Step 2: Recall that all mapping functions hold their :FN and :EXPR arguments
; constant in recursion, so as (collect lst 'REV) is unwound, the second
; formal, fn, stays fixed at the constant 'REV.  So drop the formal fn after
; replacing all occurrence of it in the body by 'REV:

; (defun g (lst)
;   (cond ((endp lst) nil)
;         (t (cons (apply$ 'REV (list (car lst)))
;                  (g (cdr lst))))))

; Step 3: Beta reduce the apply$, which is unconditionally possible since REV
; is tame:

; (defun g (lst)
;   (cond ((endp lst) nil)
;         (t (cons (REV (car lst))
;                  (g (cdr lst))))))

; It is easy to prove (g lst) = (collect lst 'REV).

; Each call of a mapping function in a Group 2 function gives rise to a helper
; function, like g, and we can work our way from the innermost calls to the outer ones
; deriving a new body.

; Since (collect lst 'REV) is the body of collect-rev, we could define (defun
; collect-rev (lst) (g lst)).  Once we've eliminated the mapping functions from
; collect-rev, we remove it from Group 2 and put it into Group 1.

; To see the result for a more complicated function like sum-of-products above,
; see the definition of sum-of-products! below, along with its helper
; subfunction sum-of-products-foldr! (which handles the FOLDR inside the
; LAMBDA).

; Examples of Group 3 (mapping functions) are

; (defun$ collect (lst fn)
;   (cond ((endp lst) nil)
;         (t (cons (apply$ fn (list (car lst)))
;                  (collect (cdr lst) fn)))))

; and

; (defun$ foldr (lst fn init)
;   (if (endp lst)
;       init
;       (apply$ fn
;               (list (car lst)
;                     (foldr (cdr lst) fn init)))))

; Defining doppelgangers for these functions is tricky because, they are
; mutually recursive with doppelgangers of apply$ (and thus apply$-userfn), ev$
; and ev$-list, and are thus mutually recursive with each other -- even though
; from the user's perspective they merely use apply$ as a previously introduced
; function symbol and were defined independently of each other.  The challenge
; is to find a measure that handles all the mapping functions simultaneously.

; Furthermore, since the doppelganger of apply$-userfn must call all the
; warranted user mapping functions as well as the warranted tame functions, we
; must admit this mutually recursive clique after defining the doppelgangers of
; the tame functions (Groups 1 and 2).

; Thus, the basic doppelganger construction is: (a) define all the tame
; functions (Groups 1 and 2), and then (b) define all the mapping functions in
; a mutually recursive clique with apply$!, ev$!, and ev$-list!.

; We carry out this program now, for user-book.lisp.  But first, we have a bit
; of routine housekeeping to do.

; This book is designed to be (part of) an alternative portculis for
; apply.lisp.  See the file script.lsp for a script that certifies the
; ``general'' version of apply.lisp, and also certifies an ``evaluation
; theory'' version tailored for user-book.  When building the general version
; of apply.lisp, the book constraints.lisp (which includes apply-prim.lisp) is
; included as part of the portcullis.  Constraints.lisp introduces and
; constrains badge-userfn and apply$-userfn.  But when building the evaluation
; theory version of apply.lisp (which is just a copy of apply.lisp called
; evaluation-apply.lisp) we include this file, doppelgangers.lisp, in the
; portcullis and then defun badge-userfn and apply$-userfn to be their
; respective doppelgangers.

; So this file, in addition to introducing the doppelgangers of all the
; relevant functions in user-book.lisp must do everything else that
; constraints.lisp does to set us up for apply.lisp.

; =================================================================
; Portcullis:
; (include-book "apply-prim")

; Recall that apply-prim.lisp provides us with:

; apply$-primp  -- recognizer for the 800+ primitives known to apply$
; apply$-badgep -- recognizer for well-formed badges
; badge-prim    -- returns the badge of an apply$ primitive
; apply$-prim   -- applies an apply$ primitive

; =================================================================
; 1. Define the apply$-badge record.  These events are taken from
;    constraints.lisp.

; We need to manipulate badges in this book, e.g., to define the doppelgangers
; of tamep and apply$.  And remember, we're doing this work in a world in which
; neither apply.lisp nor user-book.lisp have been included, but we are
; ``prescient:'' we have total knowledge of how apply$ will be used by the
; user's book.

(defrec apply$-badge (authorization-flg arity . ilks) nil)

(defconst *generic-tame-badge-1*
  (MAKE APPLY$-BADGE :AUTHORIZATION-FLG T :ARITY 1 :ILKS t))
(defconst *generic-tame-badge-2*
  (MAKE APPLY$-BADGE :AUTHORIZATION-FLG T :ARITY 2 :ILKS t))
(defconst *generic-tame-badge-3*
  (MAKE APPLY$-BADGE :AUTHORIZATION-FLG T :ARITY 3 :ILKS t))
(defconst *apply$-badge*
  (MAKE APPLY$-BADGE :AUTHORIZATION-FLG T :ARITY 2 :ILKS '(:FN NIL)))
(defconst *ev$-badge*
  (MAKE APPLY$-BADGE :AUTHORIZATION-FLG T :ARITY 2 :ILKS '(:EXPR NIL)))

(defconst *apply$-boot-fns-badge-alist*
  `((BADGE . ,*generic-tame-badge-1*)
    (TAMEP . ,*generic-tame-badge-1*)
    (TAMEP-FUNCTIONP . ,*generic-tame-badge-1*)
    (SUITABLY-TAMEP-LISTP . ,*generic-tame-badge-2*)
    (APPLY$ . ,*apply$-badge*)
    (EV$ . ,*ev$-badge*)))

(table badge-table
       :badge-userfn-structure
       nil)

(table badge-table
       :apply$-userfn!-supporters
       '(TAMEP-FUNCTIONP TAMEP SUITABLY-TAMEP-LISTP
         UNTAME-APPLY$ UNTAME-EV$)
       :put)

; =================================================================
;  2. Constrain untame-apply$ and untame-ev$, just as they are in
;  constraints.lisp, since they are provided by constraints.lisp and we're not
;  including that file.

(defstub untame-apply$ (fn args) t)
(defstub untame-ev$ (x a) t)

; =================================================================
;  3. Define the doppelganger for badge-userfn to return the actual badge of
;     all warranted user functions.  Note that expt-2-and-expt-3, a tame user
;     function, is not warranted (it returns 2 results) so it is not listed.
;     Neither is fn-2-and-fn-3, a mapping function, for the same reason.

(defun badge-userfn! (fn)
  (declare (xargs :guard t))
  (case fn
    (AP
     (make apply$-badge
           :authorization-flg t
           :arity 2
           :ilks t))
    (REV
     (make apply$-badge
           :authorization-flg t
           :arity 1
           :ilks t))
    (PALINDROMIFY-LIST
     (make apply$-badge
           :authorization-flg t
           :arity 1
           :ilks t))
    (LIST-OF-TRUE-LISTSP
     (make apply$-badge
           :authorization-flg t
           :arity 1
           :ilks t))
    (LIST-OF-LIST-OF-TRUE-LISTSP
     (make apply$-badge
           :authorization-flg t
           :arity 1
           :ilks t))
    (EXPT-5
     (make apply$-badge
           :authorization-flg t
           :arity 1
           :ilks t))
    (OK-FNP
     (make apply$-badge
           :authorization-flg t
           :arity 1
           :ilks t))

    (COLLECT-REV
     (make apply$-badge
           :authorization-flg t
           :arity 1
           :ilks t))
    (SUM-OF-PRODUCTS
     (make apply$-badge
           :authorization-flg t
           :arity 1
           :ilks T))

    (COLLECT
     (make apply$-badge
           :authorization-flg t
           :arity 2
           :ilks '(nil :fn)))
    (SUMLIST
     (make apply$-badge
           :authorization-flg t
           :arity 2
           :ilks '(nil :fn)))
    (SUMLIST-WITH-PARAMS
     (make apply$-badge
           :authorization-flg t
           :arity 3
           :ilks '(nil :fn nil)))
    (FILTER
     (make apply$-badge
           :authorization-flg t
           :arity 2
           :ilks '(nil :fn)))
    (ALL
     (make apply$-badge
           :authorization-flg t
           :arity 2
           :ilks '(nil :fn)))
    (COLLECT-ON
     (make apply$-badge
           :authorization-flg t
           :arity 2
           :ilks '(nil :fn)))
    (COLLECT-TIPS
     (make apply$-badge
           :authorization-flg t
           :arity 2
           :ilks '(nil :fn)))
    (COLLECT-FROM-TO
     (make apply$-badge
           :authorization-flg t
           :arity 3
           :ilks '(nil nil :fn)))
    (APPLY$2
     (make apply$-badge
           :authorization-flg t
           :arity 3
           :ilks '(:fn nil nil)))
    (APPLY$2x
     (make apply$-badge
           :authorization-flg t
           :arity 3
           :ilks '(:fn nil nil)))
    (APPLY$2xx
     (make apply$-badge
           :authorization-flg t
           :arity 3
           :ilks '(:fn nil nil)))
    (RUSSELL
     (make apply$-badge
           :authorization-flg t
           :arity 2
           :ilks '(:fn nil)))
    (FOLDR
     (make apply$-badge
           :authorization-flg t
           :arity 3
           :ilks '(nil :fn nil)))
    (FOLDL
     (make apply$-badge
           :authorization-flg t
           :arity 3
           :ilks '(nil :fn nil)))
    (COLLECT*
     (make apply$-badge
           :authorization-flg t
           :arity 2
           :ilks '(nil :fn)))
    (COLLECT2
     (make apply$-badge
           :authorization-flg t
           :arity 3
           :ilks '(nil :fn :fn)))
    (RECUR-BY-COLLECT
     (make apply$-badge
           :authorization-flg t
           :arity 2
           :ilks '(nil :fn)))
    (PROW
     (make apply$-badge
           :authorization-flg t
           :arity 2
           :ilks '(nil :fn)))
    (PROW*
     (make apply$-badge
           :authorization-flg t
           :arity 2
           :ilks '(nil :fn)))
    (FN-5
     (make apply$-badge
           :authorization-flg t
           :arity 2
           :ilks '(:fn nil)))
    (MAP-FN-5
     (make apply$-badge
           :authorization-flg t
           :arity 2
           :ilks '(nil :fn)))
    (SUMLIST-EXPR
     (make apply$-badge
           :authorization-flg t
           :arity 3
           :ilks '(nil :expr nil)))

; See Note on Strengthening the Constraint in badge-userfn-type, in
; constraints.lisp.

    (otherwise nil)))

; =================================================================
;  4. Define the doppelganger of badge following the definition of badge in apply.lisp.

(defun badge! (fn)
  (declare (xargs :guard t))
  (cond
   ((apply$-primp fn) (badge-prim fn))
   ((eq fn 'BADGE) *generic-tame-badge-1*)
   ((eq fn 'TAMEP) *generic-tame-badge-1*)
   ((eq fn 'TAMEP-FUNCTIONP) *generic-tame-badge-1*)
   ((eq fn 'SUITABLY-TAMEP-LISTP) *generic-tame-badge-3*)
   ((eq fn 'APPLY$) *apply$-badge*)
   ((eq fn 'EV$) *ev$-badge*)
   (t (badge-userfn! fn))))

(defthm badge!-type
  (or (null (badge! fn))
      (apply$-badgep (badge! fn)))
  :hints (("Goal" :in-theory (disable badge-prim)))
  :rule-classes
  ((:forward-chaining
    :corollary (implies (badge! fn)
                        (apply$-badgep (badge! fn))))))

(in-theory (disable badge!))

; =================================================================
;  5. Define the doppelgangers of the functions in the tamep clique just as
;     they are defined in apply.lisp except with their doppelganger names.

(defabbrev tamep-lambdap! (fn)
  (and (eq (car fn) 'LAMBDA)
       (consp (cdr fn))
       (symbol-listp (lambda-formals fn))
       (consp (cddr fn))
       (tamep! (lambda-body fn))
       (null (cdddr fn))))

(mutual-recursion
 (defun tamep! (x)
   (declare (xargs :measure (acl2-count x)
                   :guard t
                   :verify-guards nil
                   ))
   (cond ((atom x) (symbolp x))
         ((eq (car x) 'quote)
          (and (consp (cdr x))
               (null (cddr x))))
         ((symbolp (car x))
          (let ((bdg (badge! (car x))))
            (cond
             ((null bdg) nil)
             ((eq (access apply$-badge bdg :ilks) t)
              (suitably-tamep-listp! (access apply$-badge bdg :arity)
                                    nil
                                    (cdr x)))
             (t (suitably-tamep-listp! (access apply$-badge bdg :arity)
                                      (access apply$-badge bdg :ilks)
                                      (cdr x))))))
         ((consp (car x))
          (let ((fn (car x)))
            (and (tamep-lambdap! fn)
                 (suitably-tamep-listp! (length (cadr fn))
                                       nil
                                       (cdr x)))))
         (t nil)))

 (defun tamep-functionp! (fn)
   (declare (xargs :measure (acl2-count fn)
                   :guard t))
   (if (symbolp fn)
       (let ((bdg (badge! fn)))
         (and bdg (eq (access apply$-badge bdg :ilks) t)))
       (and (consp fn)
            (tamep-lambdap! fn))))

 (defun suitably-tamep-listp! (n flags args)

; We take advantage of the fact that (car nil) = (cdr nil) = nil.

   (declare (xargs :measure (acl2-count args)
                   :guard (and (natp n)
                               (true-listp flags))))
   (cond
    ((zp n) (null args))
    ((atom args) nil)
    (t (and 
        (let ((arg (car args)))
          (case (car flags)
            (:FN
             (and (consp arg)
                  (eq (car arg) 'QUOTE)
                  (consp (cdr arg))
                  (null (cddr arg))
                  (tamep-functionp! (cadr arg))))
            (:EXPR
             (and (consp arg)
                  (eq (car arg) 'QUOTE)
                  (consp (cdr arg))
                  (null (cddr arg))
                  (tamep! (cadr arg))))
            (otherwise
             (tamep! arg))))
        (suitably-tamep-listp! (- n 1) (cdr flags) (cdr args))))))
 )

(verify-guards tamep!
  :hints
  (("Goal" :use ((:instance badge!-type (fn fn))
                 (:instance badge!-type (fn (car x)))))))

; In order to verify the guards of the apply$ clique we need various properties
; implied by tamep.  We prove them here.

(defun suitably-tamep-listp!-induction (n flags args)
  (cond
   ((zp n) (list flags args))
   (t (suitably-tamep-listp!-induction (- n 1) (cdr flags) (cdr args)))))

(defthm suitably-tamep-listp!-implicant-1
  (implies (and (suitably-tamep-listp! n flags args)
                (natp n))
           (and (true-listp args)
                (equal (len args) n)))
  :hints (("Goal" :induct (suitably-tamep-listp!-induction n flags args)))
  :rule-classes :forward-chaining)

(defthm tamep!-implicant-1
  (implies (and (tamep! x)
                (consp x))
           (true-listp x))
  :hints (("Goal" :expand (tamep! x)
           :use ((:instance badge!-type (fn (car x)))))))

(in-theory (disable (:executable-counterpart tamep!)
                    (:executable-counterpart tamep-functionp!)
                    (:executable-counterpart suitably-tamep-listp!)))

; =================================================================
;  6. Partition the user's functions into three groups:

;     * Group 1:  tame functions independent of apply$
;       ap
;       rev
;       palindromify-list
;       list-of-true-listsp
;       list-of-list-of-true-listsp
;       ok-fnp

;     * Group 2:  tame functions dependent on apply$
;       collect-rev
;       sum-of-products

;     * Group 3: mapping functions
;       collect
;       sumlist
;       sumlist-with-params
;       filter
;       all
;       collect-on
;       collect-tips
;       apply$2
;       apply$2x
;       apply$2xx
;       russell
;       foldr
;       foldl
;       collect-from-to
;       collect*
;       collect2
;       recur-by-collect
;       prow
;       prow*
;       fn-2-and-fn-3
;       fn-5
;       map-fn-5
;       sumlist-expr

; =================================================================
;  7. Define doppelgangers for all Group 1 and Group 2 functions

; All doppelgangers should have a guard of t so that we can more easily define
; apply$-userfn!.  This is achieved by just using ec-call as necessary.

(defun ap! (x y)
  (declare (xargs :guard t))
  (if (consp x)
      (cons (car x) (ap! (cdr x) y))
      y))

(defun rev! (x)
  (declare (xargs :guard t))
  (if (consp x)
      (ap! (rev! (cdr x)) (cons (car x) nil))
      nil))

(defun palindromify-list! (lst)
  (declare (xargs :guard t))
  (cond ((ec-call (endp lst)) nil)
        (t (cons (ap! (car lst)
                      (rev! (car lst)))
                 (palindromify-list! (cdr lst))))))

(defun list-of-true-listsp! (lst)
  (declare (xargs :guard t))
  (cond ((atom lst) (equal lst nil))
        (t (and (true-listp (car lst))
                (list-of-true-listsp! (cdr lst))))))

(defun list-of-list-of-true-listsp! (lst)
  (declare (xargs :guard t))
  (cond ((atom lst) (equal lst nil))
        (t (and (list-of-true-listsp! (car lst))
                (list-of-list-of-true-listsp! (cdr lst))))))

(defun expt-2-and-expt-3! (x)
  (declare (xargs :guard t))

; We have to verify guard t, which means we have to protect all guarded
; subroutines in the body by ec-call, which means we have to avoid macros.

  (let ((x2 (ec-call (binary-* x x))))
    (mv x2 (ec-call (binary-* x x2)))))

(defun expt-5! (x)
  (declare (xargs :guard t))
  (mv-let (x2 x3)
    (expt-2-and-expt-3! x)
    (ec-call (binary-* x2 x3))))

(defun ok-fnp! (fn)
  (declare (xargs :guard t))
  (and (not (equal fn 'QUOTE))
       (not (equal fn 'IF))
       (tamep! `(,fn X))))

; Here the two Group 2 functions:

(defun collect-rev! (lst)
  (declare (xargs :guard t))
  (cond
   ((ec-call (endp lst)) nil)
   (t (cons (rev! (car lst))
            (collect-rev! (cdr lst))))))

(defun sum-of-products-foldr! (x init)
; Doppelganger for
; (FOLDR X
;        '(LAMBDA (I A)
;                 (BINARY-* I A))
;        '1)
; subterm of sum-of-products

  (declare (xargs :guard t))
  (if (ec-call (endp x))
      init
      ((lambda (i a)
         (ec-call (binary-* i a)))
       (car x)
       (sum-of-products-foldr! (cdr x) init))))

; Note: The quoted LAMBDA expression we see in the FOLDR call happens to be
; well-formed, fully translated, closed, etc.  And so we can use beta reduce
; (apply$ '(LAMBDA (I A) (BINARY-* I A)) ...) to a lambda well-guarded application
; as done above.  However, in general, quoted LAMBDAs need not be well-formed.
; The ``beta reduction'' then must actually go from
; (apply$ '(LAMBDA vars body) ...) to (ev$ 'body (pairlis$ vars ...))
; to the partial evaluation of ev$ on that constant body, eventually getting
; rid of all the ev$ and apply$ terms;

(defun sum-of-products! (lst)
  (declare (xargs :guard t))
  (if (ec-call (endp lst))
      0
      (ec-call
       (binary-+ (sum-of-products-foldr! (car lst) 1) ; FOLDR expression
                 (sum-of-products! (cdr lst))))))

; =================================================================

;  8. Define the doppelgangers of apply$, ev$, ev$-list, and all mapping
;     functions in a mutually recursive clique.  Note that we include
;     unwarranted mapping functions (e.g., fn-2-and-fn-3) among the defuns in
;     the clique because we need them defined so we can defined warranted ones
;     (e.g., fn-5).  But the definition of apply$! below doesn't know how how
;     to apply the unwarranted ones, just the warranted ones.  The challenge in
;     defining this clique is inventing a suitable measure.  We discuss the
;     measure construction after the clique.

(include-book "ordinals/lexicographic-ordering-without-arithmetic" :dir :system)

(defthm consp-implies-acl2-count-non-0
  (implies (consp x)
           (< 0 (acl2-count x)))
  :rule-classes :linear)

; We next define the measure functions for each of the doppelgangers of the
; mapping functions.  We then define, mutually recursively, these
; doppelgangers, including those for apply$ and ev$.  We then discuss the
; measures in the Essay on the Measures for the Apply$ Doppelgangers Clique,
; below.

; The measure is (llist a b c d) where:

; a. The first component is always either 0 or 1.  It is 0 if all the :FN and
; :EXPR formals are tame and 1 otherwise.

; b. The second component is the sum of the acl2-counts of all :FN and :EXPR
; formals.

; c. The third component is the maximal distance to apply$.  For example, in
; the measure for apply$ itself this component is 0.  In a standard mapping
; function (that calls apply$ directly), the component is 1.  In a mapping
; function that calls other mapping functions, the distance is one greater than
; the maximal third component of the measures for the called functions.  See
; the handling of apply$!2, apply$!2x, and apply$!2xx to see the measures
; adding up, and see prow*! for an illustration of the ``maximal'' criteria.

; d. The fourth component is the mapping function's ``native'' measure -- the
; measure used to admit the mapping function in isolation rather than as a
; member of the apply$ clique.  Remember that this measure is a natural number
; and so ``fits'' as a component in LLIST.

; TODO: We could loosen the restriction in badger that the measure of a mapping
; function be natural-number valued and replace it by the restriction that it
; be a bounded ordinal that we could appropriately fit into this measure.  It
; would be easiest to just allow lexicographic measures and extend this measure
; from 4 components to 3+k, where k is the largest lexicographic dimension used
; by any mapping function.  But we haven't needed any mapping functions beyond
; those currently allowed.

(defun functional/expressional-args (fn args)

; Collect the arguments in the :FN and :EXPR slots of fn, for every warranted
; mapping fn.

  (case fn
    (COLLECT
     (list (cadr args)))
    (SUMLIST
     (list (cadr args)))
    (SUMLIST-WITH-PARAMS
     (list (cadr args)))
    (FILTER
     (list (cadr args)))
    (ALL
     (list (cadr args)))
    (COLLECT-ON
     (list (cadr args)))
    (COLLECT-TIPS
     (list (cadr args)))
    (APPLY$2
     (list (car args)))
    (APPLY$2x
     (list (car args)))
    (APPLY$2xx
     (list (car args)))
    (RUSSELL
     (list (car args)))
    (FOLDR
     (list (cadr args)))
    (FOLDL
     (list (cadr args)))
    (COLLECT-FROM-TO
     (list (caddr args)))
    (COLLECT*
     (list (cadr args)))
    (COLLECT2
     (list (cadr args) (caddr args)))
    (RECUR-BY-COLLECT
     (list (cadr args)))
    (PROW
     (list (cadr args)))
    (PROW*
     (list (cadr args)))
    (FN-5
     (list (car args)))
    (MAP-FN-5
     (list (cadr args)))
    (SUMLIST-EXPR
     (list (cadr args)))
    (APPLY$
     (list (car args)))
    (EV$
     (list (car args)))
    (otherwise nil)))

(defun apply$!-measure (fn args)
  (llist 0
         (+ (acl2-count fn)
            (acl2-count (functional/expressional-args fn args)))
         0
         0))

(defun ev$!-measure (x a)
  (declare (ignore a))
  (llist 0 (acl2-count x) 1 0))

(defun ev$!-list-measure (x a)
  (declare (ignore a))
  (llist 0 (acl2-count x) 1 0))

; Just to be methodical, we'll introduce a measure function for each mapping
; function in the clique.  The measure function will take the same formals as
; the mapping function.  But since many mapping functions (i) drive acl2-count
; down on one of their arguments, (ii) carry just one argument of ilk :FN to be
; measured, and (iii) call apply$ explicitly but otherwise don't reach apply$
; (and so all have the max distance of 1 from apply$), we define a ``standard
; mapping measure'' to use for all of those functions.

(defun standard-mapping-measure (lst fn)
  (llist (if (tamep-functionp! fn)
             0
             1)
         (acl2-count fn)
         1
         (acl2-count lst)))

; Whenever you see us use the standard-mapping-measure for a mapping function's
; doppelganger it just means the mapping function was ``standard'' as noted in
; (i), (ii), and (iii) above.  If the first argument supplied to
; standard-mapping-measure is nil it means the mapping function does not call
; itself, i.e., is not explicitly recursive and so ``drives down the
; (acl2-count nil) in every call''.

(defun collect!-measure (lst fn)
  (standard-mapping-measure lst fn))

(defun sumlist!-measure (lst fn)
  (standard-mapping-measure lst fn))

(defun sumlist-with-params!-measure (lst fn params)
  (declare (ignore params))
  (standard-mapping-measure lst fn))

(defun filter!-measure (lst fn)
  (standard-mapping-measure lst fn))

(defun all!-measure (lst fn)
  (standard-mapping-measure lst fn))

(defun collect-on!-measure (lst fn)
  (standard-mapping-measure lst fn))

(defun collect-tips!-measure (x fn)
  (standard-mapping-measure x fn))

(defun apply$2!-measure (fn x y)
  (declare (ignore x y))

; Recall (apply$2 fn x y) = (apply$ fn (list x y)).  So it's a standard (but
; non-recursive) mapping function.

  (standard-mapping-measure nil fn))

(defun apply$2x!-measure (fn x y)
  (declare (ignore x y))

; Apply$2x calls apply$2, so its maximal distance to apply$ is 2 instead of 1.
; Otherwise this is the standard measure:

  (llist (if (tamep-functionp! fn) 0 1)
         (acl2-count fn)
         2
         0))

(defun apply$2xx!-measure (fn x y)
  (declare (ignore x y))

; Apply$2xx calls apply$2x, so its maximal distance to apply$ is 3 instead of
; 1.  Otherwise this is the standard measure:

  (llist (if (tamep-functionp! fn) 0 1)
         (acl2-count fn)
         3
         0))

(defun russell!-measure (fn x)
  (declare (ignore x))
  (standard-mapping-measure nil fn))

(defun foldr!-measure (lst fn init)
  (declare (ignore init))
  (standard-mapping-measure lst fn))

(defun foldl!-measure (lst fn ans)
  (declare (ignore ans))
  (standard-mapping-measure lst fn))

(defun collect-from-to!-measure (i max fn)

; Collect-from-to was admitted with a native measure of
; (nfix (- (+ 1 (ifix max)) (ifix i))), so we use that as the last component
; below.  Otherwise, this is a standard measure:

  (llist (if (tamep-functionp! fn) 0 1)
         (acl2-count fn)
         1
         (nfix (- (+ 1 (ifix max)) (ifix i)))))

(defun collect*!-measure (lst fn)
  (standard-mapping-measure lst fn))

(defun collect2!-measure (lst fn1 fn2)

; Collect2 has two :FN formals and so this shows how the first components of
; the measure are generalized: If all :FN/:EXPR formals are tame the first
; component is 0, else it's 1.  And the second component is the sum of the
; acl2-counts of the :FN/:EXPR formals.

  (llist (if (and (tamep-functionp! fn1)
                  (tamep-functionp! fn2))
             0
             1)
         (+ (acl2-count fn1) (acl2-count fn2))
         1
         (acl2-count lst)))

(defun recur-by-collect!-measure (lst fn)

; Same as standard-mapping-measure except we've used recur-by-collect's native
; measure for the last component.  However, recur-by-collect illustrates a
; curiosity of doppelganger construction not heretofore discussed:
; Recur-by-collect recurses on a call a peer mapping function, namely collect.
; To be able to prove that the measure decreases we would have to reason about
; a peer before it's introduced.  We therefore augment the doppelganger below
; with an MBT.  We discuss this later.

  (llist (if (tamep-functionp! fn) 0 1)
         (acl2-count fn)
         2
         (len lst)))

(defun prow!-measure (lst fn)
  (standard-mapping-measure lst fn))

(defun prow*!-measure (lst fn)

; Note that prow* calls apply$ directly (and so it's MINIMAL distance to apply$
; is 1) but it also calls prow, which has a distance of 1.  So prow*'s MAXIMAL
; distance to apply$ is 2.  Also note that prow* is admitted with measure (len
; lst) so that is the last component below.

  (llist (if (tamep-functionp! fn) 0 1)
         (acl2-count fn)
         2
         (len lst)))

(defun fn-2-and-fn-3!-measure (fn x)
  (declare (ignore x))
  (llist (if (tamep-functionp! fn) 0 1)
         (acl2-count fn)
         1
         0))

(defun fn-5!-measure (fn x)
  (declare (ignore x))
  (llist (if (tamep-functionp! fn) 0 1)
         (acl2-count fn)
         2
         0))

(defun map-fn-5!-measure (lst fn)
  (llist (if (tamep-functionp! fn) 0 1)
         (acl2-count fn)
         3
         (acl2-count lst)))

(defun sumlist-expr!-measure (lst expr alist)
  (declare (ignore alist))
  (llist (if (tamep! expr) 0 1)
         (acl2-count expr)
         1
         (acl2-count lst)))

; In order to admit the following function we must:

(local (in-theory (disable hons-assoc-equal)))

(mutual-recursion

; The structure of this clique is almost just a ``doppelganger'd'' copy of the
; defuns of apply$, ev$, and ev$-list, followed by the doppelgangers of each of
; the user's mapping functions.  But in the clause of apply$ that calls
; apply$-userfn we expand it out to a case-statement that handles all the
; warranted user emapping functions (protected by the tameness requirements in
; their badges).

; In addition, we perform a transformation on the defun of ev$ below when we
; define ev$!.  We explain it when we do it.

 (defun APPLY$! (fn args)
   (declare (xargs :guard (true-listp args)
                   :guard-hints (("Goal" :do-not-induct t))
                   :verify-guards nil
                   :measure (apply$!-measure fn args)
                   :well-founded-relation l<
                   ))
   (cond
    ((consp fn)

; In apply$ we will use (apply$-lambda fn args) here and include that function
; in the mutual recursion.  But that is only done so that apply$-lambda is a
; defined function in raw Lisp that we can redefine for execution efficiency.
; Logically, we could just expand the apply$-lambda call here and elsewhere in
; this clique, which is what we do to avoid complicating the measures.

     (EV$! (ec-call (car (ec-call (cdr (cdr fn))))) ; = (lambda-body fn)
           (ec-call
            (pairlis$ (ec-call (car (cdr fn))) ; = (lambda-formals fn)
                      args))))
    ((apply$-primp fn)
     (ec-call (apply$-prim fn args)))
    ((eq fn 'BADGE)
     (badge! (car args)))
    ((eq fn 'TAMEP)
     (tamep! (car args)))
    ((eq fn 'TAMEP-FUNCTIONP)
     (tamep-functionp! (car args)))
    ((eq fn 'SUITABLY-TAMEP-LISTP)
     (ec-call (suitably-tamep-listp! (car args) (cadr args) (caddr args))))
    ((eq fn 'APPLY$)
     (if (tamep-functionp! (car args))
         (ec-call (APPLY$! (car args) (cadr args)))
         (untame-apply$ fn args)))
    ((eq fn 'EV$)
     (if (tamep! (car args))
         (ev$! (car args) (cadr args))
         (untame-apply$ fn args)))
    (t

; We could call apply$-userfn! here as suggested by the defun of apply$ itself.
; But then we'd have to include its defun in this clique (it's defun would be
; what's written below).  That would just complicate the measure.  So instead
; we just inline it and define apply$-userfn! later to be this same term after
; introducing the clique.  What you see below is exactly the defun of
; (apply$-userfn! fn args).

       (case fn
         (AP (ap! (car args) (cadr args)))
         (REV (rev! (car args)))
         (PALINDROMIFY-LIST (palindromify-list! (car args))) 
         (LIST-OF-TRUE-LISTSP (list-of-true-listsp! (car args)))
         (LIST-OF-LIST-OF-TRUE-LISTSP (list-of-list-of-true-listsp! (car args)))
; Note that expt-2-and-expt-3 has output arity 2 and so is excluded!
;        (expt-2-and-expt-3 (expt-2-and-expt-3! (car args)))
; even though it is used in the body of expt-5!.
         (EXPT-5 (expt-5! (car args)))
         (OK-FNP (ok-fnp! (car args))) 
         (COLLECT-REV (collect-rev! (car args)))
         (SUM-OF-PRODUCTS (sum-of-products! (car args)))
         (COLLECT
          (if (tamep-functionp! (cadr args))
              (COLLECT! (car args) (cadr args))
              (untame-apply$ fn args)))
         (SUMLIST
          (if (tamep-functionp! (cadr args))
              (SUMLIST! (car args) (cadr args))
              (untame-apply$ fn args)))
         (SUMLIST-WITH-PARAMS
          (if (tamep-functionp! (cadr args))
              (SUMLIST-WITH-PARAMS! (car args) (cadr args) (caddr args))
              (untame-apply$ fn args)))
         (FILTER
          (if (tamep-functionp! (cadr args))
              (FILTER! (car args) (cadr args))
              (untame-apply$ fn args)))
         (ALL
          (if (tamep-functionp! (cadr args))
              (ALL! (car args) (cadr args))
              (untame-apply$ fn args)))
         (COLLECT-ON
          (if (tamep-functionp! (cadr args))
              (COLLECT-ON! (car args) (cadr args))
              (untame-apply$ fn args)))
         (COLLECT-TIPS
          (if (tamep-functionp! (cadr args))
              (COLLECT-TIPS! (car args) (cadr args))
              (untame-apply$ fn args)))
         (APPLY$2
          (if (tamep-functionp! (car args))
              (APPLY$2! (car args) (cadr args) (caddr args))
              (untame-apply$ fn args)))
         (APPLY$2x
          (if (tamep-functionp! (car args))
              (APPLY$2x! (car args) (cadr args) (caddr args))
              (untame-apply$ fn args)))
         (APPLY$2xx
          (if (tamep-functionp! (car args))
              (APPLY$2xx! (car args) (cadr args) (caddr args))
              (untame-apply$ fn args)))
         (RUSSELL
          (if (tamep-functionp! (car args))
              (RUSSELL! (car args) (cadr args))
              (untame-apply$ fn args)))
         (FOLDR
          (if (tamep-functionp! (cadr args))
              (FOLDR! (car args) (cadr args) (caddr args))
              (untame-apply$ fn args)))
         (FOLDL
          (if (tamep-functionp! (cadr args))
              (FOLDL! (car args) (cadr args) (caddr args))
              (untame-apply$ fn args)))
         (COLLECT-FROM-TO
          (if (tamep-functionp! (caddr args))
              (COLLECT-FROM-TO! (car args) (cadr args) (caddr args))
              (untame-apply$ fn args)))
         (COLLECT*
          (if (tamep-functionp! (cadr args))
              (COLLECT*! (car args) (cadr args))
              (untame-apply$ fn args)))
         (COLLECT2
          (if (and (tamep-functionp! (cadr args))
                   (tamep-functionp! (caddr args)))
              (COLLECT2! (car args) (cadr args) (caddr args))
              (untame-apply$ fn args)))
         (RECUR-BY-COLLECT
          (if (tamep-functionp! (cadr args))
              (RECUR-BY-COLLECT! (car args) (cadr args))
              (untame-apply$ fn args)))
         (PROW
          (if (tamep-functionp! (cadr args))
              (PROW! (car args) (cadr args))
              (untame-apply$ fn args)))
         (PROW*
          (if (tamep-functionp! (cadr args))
              (PROW*! (car args) (cadr args))
              (untame-apply$ fn args)))
         (FN-5
          (if (tamep-functionp! (car args))
              (FN-5! (car args) (cadr args))
              (untame-apply$ fn args)))
         (MAP-FN-5
          (if (tamep-functionp! (cadr args))
              (MAP-FN-5! (car args) (cadr args))
              (untame-apply$ fn args)))
         (SUMLIST-EXPR
          (if (tamep! (cadr args))
              (SUMLIST-EXPR! (car args) (cadr args) (caddr args))
              (untame-apply$ fn args)))

         (otherwise (untame-apply$ fn args))))))

 (defun EV$! (x a)
   (declare (xargs :guard t
                   :measure (ev$!-measure x a)
                   :well-founded-relation l<))
   (cond
    ((not (tamep! x))
     (untame-ev$ x a))
    ((variablep x)
     (ec-call (cdr (ec-call (assoc-equal x a)))))
    ((fquotep x)
     (cadr x))
    ((eq (car x) 'if)
     (if (ev$! (cadr x) a)
         (ev$! (caddr x) a)
         (ev$! (cadddr x) a)))
    ((eq (car x) 'APPLY$)
     (ec-call (APPLY$! (cadr (cadr x)) (EV$! (caddr x) a))))
    ((eq (car x) 'EV$)
     (ev$! (cadr (cadr x)) (ev$! (caddr x) a)))

; Here in the defun of ev$ we have (t (apply$ (car x) (ev$-list (cdr x) a))).
; But that truly complicates the measure because the only reason the measure
; goes down is that the functional/expressional arguments are quoted (or else x
; wouldn't be tame).  and the ev$-list evaluates those quoted arguments to be
; their evgs, which are smaller.  But that argument relies on properties of
; ev$-list and ev$, which we're in the process of defining.  That is, to be
; able to write an ev$-list call here we would have to treat this as a
; reflexive function with a test of the measure and then later prove the test
; away.  It is simpler to define each mapping function call individually, write
; (cadr (cad...dr x)) instead of (ev$ (cad...dr x) a) for those quoted
; arguments, and prove later, when we prove that ev$! is ev$, that the ev$'s
; evaluate to the evgs.

    ((eq (car x) 'COLLECT)
     (apply$! 'COLLECT
              (list (ev$! (cadr x) a)
                    (cadr (caddr x)))))
    ((eq (car x) 'SUMLIST)
     (apply$! 'SUMLIST
              (list (ev$! (cadr x) a)
                    (cadr (caddr x)))))
    ((eq (car x) 'SUMLIST-WITH-PARAMS)
     (apply$! 'SUMLIST-WITH-PARAMS
              (list (ev$! (cadr x) a)
                    (cadr (caddr x))
                    (ev$! (cadddr x) a))))
    ((eq (car x) 'FILTER)
     (apply$! 'FILTER
              (list (ev$! (cadr x) a)
                    (cadr (caddr x)))))
    ((eq (car x) 'ALL)
     (apply$! 'ALL
              (list (ev$! (cadr x) a)
                    (cadr (caddr x)))))
    ((eq (car x) 'COLLECT-ON)
     (apply$! 'COLLECT-ON
              (list (ev$! (cadr x) a)
                    (cadr (caddr x)))))
    ((eq (car x) 'COLLECT-TIPS)
     (apply$! 'COLLECT-TIPS
              (list (ev$! (cadr x) a)
                    (cadr (caddr x)))))
    ((eq (car x) 'APPLY$2)
     (apply$! 'APPLY$2
              (list (cadr (cadr x)) (ev$! (caddr x) a) (ev$! (cadddr x) a))))
    ((eq (car x) 'APPLY$2x)
     (apply$! 'APPLY$2x
              (list (cadr (cadr x)) (ev$! (caddr x) a) (ev$! (cadddr x) a))))
    ((eq (car x) 'APPLY$2xx)
     (apply$! 'APPLY$2xx
              (list (cadr (cadr x)) (ev$! (caddr x) a) (ev$! (cadddr x) a))))
    ((eq (car x) 'RUSSELL)
     (apply$! 'RUSSELL
              (list (cadr (cadr x)) (ev$! (caddr x) a))))
    ((eq (car x) 'FOLDR)
     (apply$! 'FOLDR
              (list (ev$! (cadr x) a)
                    (cadr (caddr x))
                    (ev$! (cadddr x) a))))
    ((eq (car x) 'FOLDL)
     (apply$! 'FOLDL
              (list (ev$! (cadr x) a)
                    (cadr (caddr x))
                    (ev$! (cadddr x) a))))
    ((eq (car x) 'COLLECT-FROM-TO)
     (apply$! 'COLLECT-FROM-TO
              (list (ev$! (cadr x) a)
                    (ev$! (caddr x) a)
                    (cadr (cadddr x)))))
    ((eq (car x) 'COLLECT*)
     (apply$! 'COLLECT*
              (list (ev$! (cadr x) a)
                    (cadr (caddr x)))))
    ((eq (car x) 'COLLECT2)
     (apply$! 'COLLECT2
              (list (ev$! (cadr x) a)
                    (cadr (caddr x))
                    (cadr (cadddr x)))))
    ((eq (car x) 'RECUR-BY-COLLECT)
     (apply$! 'RECUR-BY-COLLECT
              (list (ev$! (cadr x) a)
                    (cadr (caddr x)))))
    ((eq (car x) 'PROW)
     (apply$! 'PROW
              (list (ev$! (cadr x) a)
                    (cadr (caddr x)))))
    ((eq (car x) 'PROW*)
     (apply$! 'PROW*
              (list (ev$! (cadr x) a)
                    (cadr (caddr x)))))
    ((eq (car x) 'FN-5)
     (apply$! 'FN-5
              (list (cadr (cadr x))
                    (ev$! (caddr x) a))))
    ((eq (car x) 'MAP-FN-5)
     (apply$! 'MAP-FN-5
              (list (ev$! (cadr x) a)
                    (cadr (caddr x)))))
    ((eq (car x) 'SUMLIST-EXPR)
     (apply$! 'SUMLIST-EXPR
              (list (ev$! (cadr x) a)
                    (cadr (caddr x))
                    (ev$! (cadddr x) a))))
    (t
     (APPLY$! (car x)
              (EV$!-LIST (cdr x) a)))))

 (defun EV$!-LIST (x a)
   (declare (xargs :guard t
                   :measure (ev$!-list-measure x a)
                   :well-founded-relation l<))
   (cond
    ((atom x) nil)
    (t (cons (EV$! (car x) a)
             (EV$!-LIST (cdr x) a)))))

; Now the user's mapping functions:

 (defun COLLECT! (lst fn)
   (declare (xargs :measure (collect!-measure lst fn)
                   :well-founded-relation l<))
   (cond
    ((ec-call (endp lst)) nil)
    (t (cons (APPLY$! fn (list (car lst)))
             (COLLECT! (cdr lst) fn)))))

  (defun SUMLIST! (lst fn)
    (declare (xargs :measure (sumlist!-measure lst fn)
                    :well-founded-relation l<))
    (cond
     ((ec-call (endp lst)) 0)
     (t (ec-call (binary-+ (APPLY$! fn (list (car lst)))
                           (SUMLIST! (cdr lst) fn))))))

  (defun SUMLIST-WITH-PARAMS! (lst fn params)
    (declare (xargs :measure (sumlist-with-params!-measure lst fn params)
                    :well-founded-relation l<))
    (cond
     ((ec-call (endp lst)) 0)
     (t (ec-call (binary-+ (ec-call (APPLY$! fn (cons (car lst) params)))
                           (SUMLIST-WITH-PARAMS! (cdr lst) fn params))))))

  (defun FILTER! (lst fn)
    (declare (xargs :measure (filter!-measure lst fn)
                    :well-founded-relation l<))
    (cond
     ((ec-call (endp lst)) nil)
     ((APPLY$! fn (list (car lst)))
      (cons (car lst) (FILTER! (cdr lst) fn)))
     (t (FILTER! (cdr lst) fn))))

  (defun ALL! (lst fn)
    (declare (xargs :measure (all!-measure lst fn)
                    :well-founded-relation l<))
    (cond
     ((ec-call (endp lst)) t)
     (t (and (APPLY$! fn (list (car lst)))
             (ALL! (cdr lst) fn)))))

 (defun COLLECT-ON! (lst fn)
   (declare (xargs :measure (collect-on!-measure lst fn)
                   :well-founded-relation l<))
   (cond
    ((ec-call (endp lst)) nil)
    (t (cons (apply$! fn (list lst))
             (COLLECT-ON! (cdr lst) fn)))))

  (defun COLLECT-TIPS! (x fn)
    (declare (xargs :measure (collect-tips!-measure x fn)
                    :well-founded-relation l<))
    (cond
     ((atom x) (apply$! fn (list x)))
     (t (cons (COLLECT-TIPS! (car x) fn)
              (COLLECT-TIPS! (cdr x) fn)))))

  (defun APPLY$2! (fn x y)
    (declare (xargs :measure (apply$2!-measure fn x y)
                    :well-founded-relation l<))
    (APPLY$! fn (list x y)))

  (defun APPLY$2x! (fn x y)
    (declare (xargs :measure (apply$2x!-measure fn x y)
                    :well-founded-relation l<))
    (APPLY$2! fn x y))

  (defun APPLY$2xx! (fn x y)
    (declare (xargs :measure (apply$2xx!-measure fn x y)
                    :well-founded-relation l<))
    (APPLY$2x! fn x y))

  (defun RUSSELL! (fn x)
    (declare (xargs :measure (russell!-measure fn x)
                    :well-founded-relation l<))
    (NOT (APPLY$! fn (list x x))))

  (defun FOLDR! (lst fn init)
    (declare (xargs :measure (foldr!-measure lst fn init)
                    :well-founded-relation l<))
    (cond
     ((ec-call (endp lst)) init)
     (t (apply$! fn
                (list (car lst)
                      (foldr! (cdr lst) fn init))))))

  (defun FOLDL! (lst fn ans)
    (declare (xargs :measure (foldl!-measure lst fn ans)
                    :well-founded-relation l<))
    (if (ec-call (endp lst))
        ans
        (foldl! (cdr lst)
                fn
                (apply$! fn (list (car lst) ans)))))

 (defun COLLECT-FROM-TO! (i max fn)
    (declare (xargs :measure (collect-from-to!-measure i max fn)))
    (let ((i (ifix i))
          (max (ifix max)))
      (cond
       ((> i max)
        nil)
       (t (cons (apply$! fn (list i))
                (collect-from-to! (ec-call (binary-+ i 1)) max fn))))))

  (defun COLLECT*! (lst fn)
    (declare (xargs :measure (collect*!-measure lst fn)
                    :well-founded-relation l<))
    (if (ec-call (endp lst))
        nil
        (cons (ec-call (apply$! fn (car lst)))
              (collect*! (cdr lst) fn))))

  (defun COLLECT2! (lst fn1 fn2)
    (declare (xargs :measure (collect2!-measure lst fn1 fn2)
                    :well-founded-relation l<))
    (if (ec-call (endp lst))
        nil
        (cons (cons (apply$! fn1 (list (car lst)))
                    (apply$! fn2 (list (car lst))))
              (collect2! (cdr lst) fn1 fn2))))

  (defun RECUR-BY-COLLECT! (lst fn)
    (declare (xargs :measure (recur-by-collect!-measure lst fn)
                    :well-founded-relation l<))
    (if (ec-call (endp lst))
        nil
        (if (MBT (< (len (collect! (cdr lst) fn)) ; Curious!  See below.
                    (len lst)))
            (cons (car lst)
                  (recur-by-collect! (collect! (cdr lst) fn) fn))
            nil)))

  (defun PROW! (lst fn)
    (declare (xargs :measure (prow!-measure lst fn)
                    :well-founded-relation l<))
    (cond ((or (ec-call (endp lst)) (ec-call (endp (cdr lst))))
           nil)
          (t (cons (apply$! fn (list (car lst) (cadr lst)))
                   (prow! (cdr lst) fn)))))
  (defun PROW*! (lst fn)
    (declare (xargs :measure (prow*!-measure lst fn)
                    :well-founded-relation l<))
    (cond ((or (ec-call (endp lst))
               (ec-call (endp (cdr lst))))
           (apply$! fn (list lst lst)))
          ((MBT (< (len (prow! lst fn)) (len lst))) ; Curious! See below.
           (prow*! (prow! lst fn) fn))
          (t nil)))

  (defun FN-2-AND-FN-3! (fn x)
    (declare (xargs :measure (fn-2-and-fn-3!-measure fn x)
                    :well-founded-relation l<))
    (let ((x2 (apply$! fn (list x x))))
      (mv x2 (apply$! fn (list x x2)))))

  (defun FN-5! (fn x)
    (declare (xargs :measure (fn-5!-measure fn x)
                    :well-founded-relation l<))
    (mv-let (x2 x3)
      (fn-2-and-fn-3! fn x)
      (apply$! fn (list x2 x3))))

  (defun MAP-FN-5! (lst fn)
    (declare (xargs :measure (map-fn-5!-measure lst fn)
                    :well-founded-relation l<))
    (if (ec-call (endp lst))
        nil
        (cons (fn-5! fn (car lst))
              (map-fn-5! (cdr lst) fn))))
  (defun SUMLIST-EXPR! (lst expr alist)
    (declare (xargs :measure (sumlist-expr!-measure lst expr alist)
                    :well-founded-relation l<))
    (cond ((ec-call (endp lst)) 0)
          (t (ec-call
              (binary-+ (ev$! expr (cons (cons 'x (car lst)) alist))
                        (sumlist-expr! (cdr lst) expr alist))))))

)

(defthm len-collect!
  (equal (len (collect! x fn)) (len x))
  :hints (("Subgoal *1/1" :expand (collect! x fn))))

(defthm len-prow!
  (implies (not (endp x))
           (< (len (prow! x fn)) (len x)))
  :hints (("Subgoal *1/2" :expand (prow! x fn)))
  :rule-classes :linear)

(verify-guards apply$!
  :hints (("Goal" :do-not-induct t
           :expand ((:free (n ilk ilks x)(suitably-tamep-listp! n (cons ilk ilks) x))))))

(defun apply$-lambda! (fn args)
  (declare (xargs :guard (and (consp fn) (true-listp args))
                  :guard-hints (("Goal" :do-not-induct t))
                  ))
  (EV$! (ec-call (car (ec-call (cdr (cdr fn))))) ; = (lambda-body fn)
        (ec-call
         (pairlis$ (ec-call (car (cdr fn))) ; = (lambda-formals fn)
                   args))))

; -----------------------------------------------------------------
; Essay on the Measures for the Apply$ Doppelgangers Clique,

; Recall that we know from the badger in apply.lisp that all justifications are
; tame and that all mapping functions have decreasing natural valued measures.
; The first condition means that the doppelgangers for the nonprimitive
; functions used in the justification of the doppelgangers of our mapping
; functions have all been introduced before we admit the apply$ clique.  Recall
; also that we know that all mapping functions hold their :FN and :EXPR
; arguments constant in recursion, so that any measure of those arguments stays
; fixed.

; Intuitively, the second and fourth components of the measure explain
; termination: either the size of the functional arguments goes down (as in
; lambda applications or applications of functions on evaluations of quoted
; functions) or the size of the functional arguments stays constant (because
; mapping functions hold them constant) and the mapping function's native
; measure decreases.  But we have to fiddle to allow calls of apply$.

; A user-defined mapping function can apply$ anything to anything.  For
; example, it can apply$ a big lambda expression constant or it can apply$ the
; :FN fn to a gigantic computed argument (think foldr).  Any measure of the
; clique that puts the mapping function and/or size of the arguments (as
; measured by the native measure) as the two most significant components will
; disallow such calls.  So we need a leading measure to allow user-defined
; mapping functions to call apply$.

; We need the third component, the ``maximal distance to apply$,'' to allow
; non-recursive functions that call apply$ (e.g., russell) or calls of apply$
; in the base cases of user-defined mapping functions where the native measure
; has bottomed out (e.g., collect-tips).  Russell is so pathological that it
; may not be convincing to use it as a motivating example.  So consider the
; convenient abbreviation:

; (defun$ apply2 (fn x y) (apply$ fn (list x y))).

; Consider (apply2 'ap x y) calling (apply$ 'ap (list x y)).  Using our
; conventions above, the measure of the former would be the same as
; russell!-measure: (llist 0 (acl2-count fn) 1 0).  The measure of the latter
; is (llist 0 (acl2-count fn) 0 0).  Note that the former is bigger than the
; latter, as required, thanks entirely to the third component.

; About functional/expressional-args: Given a mapping fn to apply and some
; args, it returns the list of elements in args that are treated as functions
; or expressions.  So for example, (functional/expressional-args 'collect args)
; is (list (cadr args)).  We will be interested in the acl2-count of this
; value, which in the case of fn='collect is (+ 1 (acl2-count (cadr args))).
; One might think that the conses used to stitch together the various
; functional arguments are coincidental and that all we'll really care about is
; the sum of the counts of those args.  But that is wrong.  We need the
; acl2-count of this value to be bigger than the sum of the counts of the
; functional arguments!  See ``case 3'' of the following discussion of the
; standard mapping measure below.

; TODO: This is not really a todo unless we get uncomfortable with the basic
; approach of admitting all the mapping functions in a mutually recursive
; clique with apply$.  But if we do become uncomfortable with that: we could
; simplify this whole measure construction by imposing some restriction in
; def-warrant like: every user-defined mapping function is equivalent to some
; application of FOLDR.  This condition or one like it can probably be
; recognized syntactically for all the mapping functions the user is liable to
; use.  So imagine we did that.  Then the story would just admit apply$, ev$,
; ev$-list, and foldr (or the all-powerful generic mapping function we settled
; upon) and then admit the user's particular mapping functions after admitting
; the clique by defining them to be their particular instances of the
; all-powerful function.  Just a thought...  See the file foldr-exercises.lisp
; for some related thoughts.

; A Few Even More Random Thoughts

; It is impossible to recur on an apply$, even a tame one.

; (defun$ my-cdr (x) (cdr x))

; (defun$ recur-by-my-cdr (lst fn)
;   (if (endp lst) 
;       nil
;       (cons (apply$ fn (list (car lst)))
;    	      (recur-by-my-cdr (apply$ 'my-cdr (list lst)) fn))))

; The doppelganger for recur-by-my-cdr can in fact be admitted into the apply$!
; clique.  But you can't defun recur-by-my-cdr because you can't prove
; termination without an (APPLY$-WARRANT-MY-CDR) governing hypothesis in the
; defun.

; If you add that hypothesis as an explicit IF test, you can defun
; recur-by-my-cdr but you cannot (def-warrant recur-by-my-cdr) because
; APPLY$-WARRANT-MY-CDR is defined via defun-sk in terms of a constrained
; witness, APPLY$-WARRANT-MY-CDR-WITNESS, which cannot be warranted.

; TODO: It might be possible to do something like this: defun recur-by-my-cdr
; with the explicit test and admit it as usual.  Then change def-warrant so
; that it lifts any warrants out and formulates and proves a conditional defun.
; Then process the body of that conditional defun for a badge.  Of course, one
; has to think about the badge and warrant having to carry the additional
; warrants, and one has to think about doppelganger construction.  But since we
; see no pressing need for this sort of definition, we haven't thought about it
; further.

; The following function can be added to the clique:

; (defun$ nthcdr-fn (fn lst)
;   (nthcdr (+ 1 (nfix (apply$ fn (list lst)))) lst))

; We can prove that it returns something with smaller len (though we need the
; lemma:

; (defthm len-nthcdr-weak
;   (<= (len (nthcdr n lst))
;       (len lst))
;   :rule-classes :linear)

; to carry out that proof).  We don't need a warrant for fn to prove that
; nthcdr-fn returns something of smaller len.

; We can then define

; (defun$ recur-by-nthcdr-fn (fn lst)
;   (declare (xargs :measure (len lst)))
;   (cond
;    ((endp lst) nil)
;    (t (cons (car lst)
;             (recur-by-nthcdr-fn fn (nthcdr-fn fn lst))))))

; An example illustrating a similar construction is provided here by the function

; (defun$ recur-by-collect (lst fn)
;   (declare (xargs :measure (len lst)))
;   (if (endp lst)
;       nil
;       (cons (car lst)
;  	      (recur-by-collect (collect (cdr lst) fn) fn))))

; The (collect (cdr lst) fn) has smaller len no matter what fn is and the
; measure shown above handles it.

; However, note the rather curious step in the defun of the doppelganger for
; recur-by-collect:

;  (defun RECUR-BY-COLLECT! (lst fn)
;     (declare (xargs :measure (recur-by-collect!-measure lst fn)
;                     :well-founded-relation l<))
;     (if (ec-call (endp lst))
;         nil
;         (if (MBT (< (LEN (COLLECT! (CDR LST) FN))
;                     (LEN LST)))
;             (cons (car lst)
;                   (recur-by-collect! (collect! (cdr lst) fn) fn))
;             nil)))

; Why do we include the MBT in the definition of the recur-by-collect!?  It's
; not in the defun$ of recur-by-collect.

; The issue is that when recur-by-collect is introduced, we've already defined
; collect and so can prove (either as a lemma or inline during defun) that it
; returns something no longer than its first argument.  But when we're defining
; its doppelganger we're also simultaneously defining the doppelganger of
; collect.  Neither has been introduced and so we can't reason about them.
; Essentially, recur-by-collect is a reflexive function because it recurs in a
; crucial way on something returned by recursion (through its peer in the
; clique).  So instead, we include the key fact as an MBT in the definition of
; recur-by-collect!.  We'll prove it away when we prove that the doppelganger
; is recur-by-collect in e.lisp.

; So the basic conclusion of the recur-by-collect exercise here is that we can
; allow recursion by peers in the clique as long as we do not need warrants to
; prove the necessary measure properties.  Since we don't have a way to allow
; warrants in defuns at the moment we're happy to allow recursion by peers.

; But then we still can't do this:

; (defun$ recur-by-nthcdr-fn (fn lst)
;   (declare (xargs :measure (len lst)))
;   (cond
;    ((not (tamep-functionp fn))
;     nil)
;    ((endp lst) nil)
;    (t (cons (car lst)
;             (recur-by-nthcdr-fn fn (apply$ 'nthcdr-fn (list fn lst)))))))

; for the same reasons noted for recur-by-my-cdr: we need the warrant for
; nthcdr-fn and can't put it into the defun$ and have the subsequent
; def-warrant succeed.

; But suppose that problem is fixed.

; Then we still have a problem: we don't know an apply$! clique measure that
; works if this function is in the clique.  We haven't worked it enough to
; summarize the problem.  So the bottom line is just: if you really want to
; start thinking about allowing warrants into warranted definitions by some
; method (like conditional defuns) you're going to have to work on the
; doppelganger story!

; About standard-mapping-measure: The standard measure works for all
; user-defined mapping functions that map a single function fn over an object,
; lst, driving down the acl2-count of lst the recursion and only calling apply$
; explicitly (not via some other mapping function).  Examples of such mapping
; functions are collect, sumlist, sumlist-with-params, filter, all, collect-on,
; and foldr.  The application of fn may be to any arguments, not just arguments
; smaller than lst.  Examples here of mapping functions that apply their fn to
; ``big'' arguments include collect-on (where the fn is applied to all of lst),
; sumlist-with-params (where the fn is supplied with an element of lst but also
; some arbitrary other parameters), and foldr (where the fn is supplied with an
; element of lst and something returned by a recursive call of the mapping
; function, which might be arbitrarily big).

; Returning to the standard-mapping-measure as it is currently defined, let's
; explore it a bit.

; Take collect as the typical example of a mapping function.  Since the standard
; measure splits on whether the fn being applied is a mapping function, let's
; consider both possibilities, i.e., fn is or is not a mapping function.  In
; particular, let's consider the possibilit that fn is 'COLLECT and the
; possibility that it is 'REV, as prototypical examples of mapping with a
; mapping function and mapping with an ordinary function.

; (Footnote: Objection!  Collect takes two args and yet applies fn to only one
; arg, so it seems troubling to think about (collect! lst 'COLLECT).  But
; nowhere do we insist that the arity of the funtion supplied to apply$! be
; equal to the length of the argument list supplied; apply$! just applies the
; function to as many ``elements'' of that list as the arity, using car and cdr
; to fetch the ``elements'' from the true-list of arguments.  So (collect! lst
; 'COLLECT) really does expand to
; (if (consp lst)
;     (cons (apply$ 'COLLECT (list (car lst) nil))
;           (collect! (cdr lst) 'COLLECT))
;     nil)
; So we need a measure that makes the arguments of that inner apply$! smaller
; (since it is in the clique with collect!)  and that makes the recursive call
; of collect! smaller.)

; So we will consider (collect! lst 'COLLECT) and (collect! lst 'REV).  Let's
; consider when collect! calls apply$! and when collect! calls collect!.  We
; will also consider what happens when (apply$! 'COLLECT args) calls collect!
; and when (apply$! 'REV args) calls rev!.

; So here are the cases.  We write term1 ==> term2 to denote ``term1 calls
; term2'' and write m1 >> m2 to denote the ``measure of term1 must be greater
; than the measure of term2.''  We write ``...'' when enough has been written
; to settle the question of whether one lexicographic measure is bigger than
; another.  Note that when we consider a case like term1 ==> term2, we get to
; assume the tests governing the call of term2.  So, for example, collect! calls
; itself recursively only if (consp lst), which we leave largely implicit
; below.

; 1. (collect! lst 'COLLECT) ==> (apply$ 'COLLECT (list (car lst)))
;    (llist 1 0 1 (acl2-count lst))
;    >>
;    (llist 0 ...)

; 2. (collect! lst 'COLLECT) ==> (collect! (cdr lst) 'COLLECT)
;    (llist 1 0 1 (acl2-count lst))
;    >>
;    (llist 1 0 1 (acl2-count (cdr lst)))

; 3. (apply$! 'COLLECT args) ==> (collect! (car args) (cadr args)) [See below.]
;    (llist 0 (acl2-count (functional/expressional-args 'collect args)) 0 0)
;    =
;    (llist 0 (+ 1 (acl2-count (cadr args))) 0 0)
;    >>
;    (llist 0 (acl2-count (cadr args)) 0 (acl2-count (car args)))

;    NOTE: (apply$! 'COLLECT args) will call collect! only if (cadr args) is a
;    tamep-functionp.  This governs the call of collect! in apply$!.  But no
;    mapping function is a tamep-functionp because tame functions have badge T
;    and mapping functions have a :FN or :EXPR in their badge.  So to consider
;    this case 3, we get to know that (cadr args) is not a mapping function and
;    so the generic measure returns its second llist, not its first.

;    Note also the criticality of the +1 generated by counting the cons
;    stitching together the functional/expressional-args in the apply$ measure.

; 4. (collect! lst 'REV) ==> (apply$! 'REV (list (car lst)))
;    (llist 0 (acl2-count 'REV) 0 (acl2-count lst))
;    =
;    (llist 0 0 0 (acl2-count lst))
;    >>
;    (llist 0 0 0 0)

;    Note: This call only happens if (consp lst).  Had we chosen a
;    LAMBDAexpression as the prototypical ordinary fn instead of 'REV, the second
;    component would have decided it.

; 5. (collect! lst 'REV) ==> (collect! (cdr lst) 'REV)
;    (llist 0 (acl2-count 'REV) 0 (acl2-count lst))
;    >>
;    (llist 0 (acl2-count 'REV) 0 (acl2-count (cdr lst)))

; 6. (apply$! 'REV args) ==> (rev! (car args))

;    Since REV is not a mapping function, it is not in the clique
;    and this call is not a ``recursive'' one and thus isn't measured.

; In summary, the leading 1 when a mapping function is applied to a mapping
; function (case 1 above) allows the mapping function to call apply$!, as the
; definition of the mapping function says it must.  The +1 generated by the
; cons stitching together the functional/expressional arguments allows apply$!
; to call a mapping function when the functional argument is tame.  The
; ``distance from apply$'' in the third component is not illustrated in this
; example.  The final (acl2-count lst) provided in the fourth component of the
; standard measure handles the case of a standard mapping function calling
; itself.

; End of Discussion of the Measures for the Apply$! Clique
; -----------------------------------------------------------------

; =================================================================
;  9. Define apply$-userfn! to be the ``new'' part of apply$!.

(defun apply$-userfn! (fn args)
  (declare (xargs :guard (true-listp args))) 
  (case fn
    (AP (ap! (car args) (cadr args)))
    (REV (rev! (car args)))
    (PALINDROMIFY-LIST (palindromify-list! (car args))) 
    (LIST-OF-TRUE-LISTSP (list-of-true-listsp! (car args)))
    (LIST-OF-LIST-OF-TRUE-LISTSP (list-of-list-of-true-listsp! (car args)))
; Note that expt-2-and-expt-3 has output arity 2 and so is excluded!
;   (expt-2-and-expt-3 (expt-2-and-expt-3! (car args)))
; even though it is used in the body of expt-5!.
    (EXPT-5 (expt-5! (car args)))
    (OK-FNP (ok-fnp! (car args))) 
    (COLLECT-REV (collect-rev! (car args)))
    (SUM-OF-PRODUCTS (sum-of-products! (car args)))
    (COLLECT
     (if (tamep-functionp! (cadr args))
         (COLLECT! (car args) (cadr args))
         (untame-apply$ fn args)))
    (SUMLIST
     (if (tamep-functionp! (cadr args))
         (SUMLIST! (car args) (cadr args))
         (untame-apply$ fn args)))
    (SUMLIST-WITH-PARAMS
     (if (tamep-functionp! (cadr args))
         (SUMLIST-WITH-PARAMS! (car args) (cadr args) (caddr args))
         (untame-apply$ fn args)))
    (FILTER
     (if (tamep-functionp! (cadr args))
         (FILTER! (car args) (cadr args))
         (untame-apply$ fn args)))
    (ALL
     (if (tamep-functionp! (cadr args))
         (ALL! (car args) (cadr args))
         (untame-apply$ fn args)))
    (COLLECT-ON
     (if (tamep-functionp! (cadr args))
         (COLLECT-ON! (car args) (cadr args))
         (untame-apply$ fn args)))
    (COLLECT-TIPS
     (if (tamep-functionp! (cadr args))
         (COLLECT-TIPS! (car args) (cadr args))
         (untame-apply$ fn args)))
    (APPLY$2
     (if (tamep-functionp! (car args))
         (APPLY$2! (car args) (cadr args) (caddr args))
         (untame-apply$ fn args)))
    (APPLY$2x
     (if (tamep-functionp! (car args))
         (APPLY$2x! (car args) (cadr args) (caddr args))
         (untame-apply$ fn args)))
    (APPLY$2xx
     (if (tamep-functionp! (car args))
         (APPLY$2xx! (car args) (cadr args) (caddr args))
         (untame-apply$ fn args)))
    (RUSSELL
     (if (tamep-functionp! (car args))
         (RUSSELL! (car args) (cadr args))
         (untame-apply$ fn args)))
    (FOLDR
     (if (tamep-functionp! (cadr args))
         (FOLDR! (car args) (cadr args) (caddr args))
         (untame-apply$ fn args)))
    (FOLDL
     (if (tamep-functionp! (cadr args))
         (FOLDL! (car args) (cadr args) (caddr args))
         (untame-apply$ fn args)))
    (COLLECT-FROM-TO
     (if (tamep-functionp! (caddr args))
         (COLLECT-FROM-TO! (car args) (cadr args) (caddr args))
         (untame-apply$ fn args)))
    (COLLECT*
     (if (tamep-functionp! (cadr args))
         (COLLECT*! (car args) (cadr args))
         (untame-apply$ fn args)))
    (COLLECT2
     (if (and (tamep-functionp! (cadr args))
              (tamep-functionp! (caddr args)))
         (COLLECT2! (car args) (cadr args) (caddr args))
         (untame-apply$ fn args)))
    (RECUR-BY-COLLECT
     (if (tamep-functionp! (cadr args))
         (RECUR-BY-COLLECT! (car args) (cadr args))
         (untame-apply$ fn args)))
    (PROW
     (if (tamep-functionp! (cadr args))
         (PROW! (car args) (cadr args))
         (untame-apply$ fn args)))
    (PROW*
     (if (tamep-functionp! (cadr args))
         (PROW*! (car args) (cadr args))
         (untame-apply$ fn args)))
    (FN-5
     (if (tamep-functionp! (car args))
         (FN-5! (car args) (cadr args))
         (untame-apply$ fn args)))
    (MAP-FN-5
     (if (tamep-functionp! (cadr args))
         (MAP-FN-5! (car args) (cadr args))
         (untame-apply$ fn args)))
    (SUMLIST-EXPR
     (if (tamep! (cadr args))
         (SUMLIST-EXPR! (car args) (cadr args) (caddr args))
         (untame-apply$ fn args)))

    (otherwise (untame-apply$ fn args))))


