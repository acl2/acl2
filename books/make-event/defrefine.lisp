(in-package "ACL2")

#||

  defrefine.lisp
  ~~~~~~~~~~~~~~

Author: Sandip Ray
Date: Wed Aug 1 11:02:39 2007

Synopsis
--------

This book presents a collection of macros to aid in reasoning about
ACL2 functions via refinement.  The idea of refinement (illustrated in
a recent work in progress by Bill Legato) is the following.  We start
with an abstract specification and program, showing that the abstract
specification is satisfied by the abstract program.  We then continue
to refine the specification and the program until we finally reach a
concrete implementation.  At each intermediate step we have an
intermediate specification and an intermediate program.  What this
approach guarantees is that the program satisfies the corresponding
specification at each stage of the refinement process.  Thus there is
a smaller gap to bridge at any level.

It is worth noting that a typical theorem proving effort often
proceeds by "re-creating" the intermediate functions and proving
appropriate properties.  What the proposal saves (I believe) is the
creative reverse-engineering involved in defining the intermediate
steps, and also makes the programmer's intention much clearer.

Contents
--------

So what does this book do?  We provide tools to help an ACL2 user
develop refinement-style programs.  Right now there is no support to
automate the creative reasoning involved --- although that is
certainly something we can and should do.  (That support will require
the refinement tool to have access to libraries, and generate an
intermediate refinement by looking at the component definitions in the
libraries.  The process can be seen as analogous to compilation.)
Rather, the support presented here is in the form of constructs that
help the user manage the theory while developing intermediate
refinements.  That is, it takes care of questions such as "Did I
*really* perform an appropriate refinement?"  "Are there missing
constraints?", etc.   At the logical level the tools here can be
viewed as no more than structuring the process of refinement.  But I
found structuring and discipline to be useful in formal verification
in general, and I'm hoping that they will be useful here.

The tools in this book consist of the following macros:

1. defabstraction: Produce the first specification for a program

2. defrefine: Produce a list of functions that refine a previously
              produced abstraction.  The executable definition of
              these functions is not exported, but these functions are
              constrained to (i)~refine the previous abstraction, and any
              other additional property of the functions that one
              wishes to introduce.

3. defexecutable: Final concrete definition.  It is shown to produce
                  a refinement of a previous abstraction.  The
                  difference between a defexecutable and defrefine is
                  that a defexecutable cannot be further refined
                  as it is assumed to be in the concrete definition.
                  The reason is that we wanted executable definitions
                  and for simulation and stuff of the final product.


Observation
-----------

One of the concerns about ACL2 is that the logic is not higher-order.
This often stifles some of the reasoning that we will like to do with
ACL2.  What this work shows (which is interesting to me) is that we
can emulate pretty much quite a bit of higher order reasoning in ACL2
by making use of features like table events and make-event.


Future Work
-----------

1.  Remove defexecutable and allow some form of simulation in the
    intermediate versions.

      I don't know what to do about this, but I have a feeling that
      defexecutable is not very useful because we want to refine
      anything anytime.  I have it right now, but will consider a
      better  design if I get the idea what will be better.


||#


;; So how does this work?  First I create an "abstraction table".  The
;; entries in the abstraction table can be viewed as higher order
;; predicates that are then refined by other higher-order predicates.
;; The problem with this view is that the predicate is partial.

;; Observation: Note the table guard.  It says that we do not have a
;; deflabel event with the appropriate label.  This prevents the
;; possibility of "redefining" any entry in the table.

(table abstraction-table nil nil
       :guard
       (and (symbolp key)
            (not (getprop key 'label nil 'current-acl2-world world))))


;; I don't remember always how to look up the constraints on the
;; functions at any stage of the refinement process.  So I have this
;; macro here.

(defmacro defprop (hfn)
  `(table abstraction-table ,hfn))


;; I should put the definitions of constrain-info and conjoin here so
;; that it's redundant with the one in the ACL2 sources.  That way, if
;; the definition in the sources changes, we will know that we need to
;; change the definition in this book as well.  But I'll do it only
;; when the design is somewhat more solidified, rather than right
;; away.


(defun constraint (fn wrld)
  (declare (xargs :mode :program))
  (mv-let (sym x)
          (constraint-info fn wrld)
          (cond
           ((unknown-constraints-p x)
            (er hard 'constraint
                "Unable to determine constraints on ~x0!  Presumably this ~
                 function was introduced with a partial-encapsulate; see :DOC ~
                 partial-encapsulate."))
           (sym (conjoin x))
           (t x))))


(defmacro defabstraction (name &rest args)
  `(progn

     (encapsulate ,@args)
     (make-event
      (let* ((signatures (quote ,(first args)))
             (sig (first signatures))
             ;; The reason for the if statement here is that there are
             ;; two flavors of signature, for instance (f (x) t) and
             ;; ((f *) => *).  I do not do further error-checking here
             ;; since the encapsulate presumably had passed the ACL2
             ;; check.  The farg is the first function symbol that has
             ;; been introduced during the encapsulation.  I just care
             ;; about that since the constraints are all associated
             ;; with this function.
             (farg (if (consp (first sig))
                       (first (first sig))
                     (first sig)))

             ;; I am collecting the constraint generated from the
             ;; encapsulation, which can be thought of as the formula
             ;; representing the higher-order notion of formula
             ;; parameterized by the functions in the signature.
             (val-term (constraint farg (w state)))

             (name (quote ,name)))

     ;; Now generate the final event.

        `(progn
           (table abstraction-table (quote ,name) (quote ,val-term))

           ;; I generated the table event but I want to insure that this
           ;; entry will remain in this table.  I do so by now geneating
           ;; a deflabel with the key.  Notice that the table-guard for
           ;; the table says that the key is not one of the labels, which
           ;; guarantees that other people in some include-book for
           ;; instance cannot overwrite this entry.

           (deflabel ,name))))))



;; Now the far more difficult one, refining an abstraction.

(defun snoc (x e)
  (if (endp x) (list e)
    (cons (car x) (snoc (cdr x) e))))

(defun create-alist-from-func-list (lst)
  (if (endp lst) nil
    (acons (first (first lst))
           (second (first lst))
           (create-alist-from-func-list (rest lst)))))

(defmacro defrefine
  (name abstraction term-list
        &key
        (thm-name 'nil)
        (functional-substitution 'nil)
        instructions hints otf-flg rule-classes doc)
  (declare (ignore doc))
  `(make-event
    (mv-let (erp val state)

            ;; First I look up the abstraction in the table.  This
            ;; gets the constraint.

            (table abstraction-table (quote ,abstraction))
            (declare (ignore erp))
            (let* (

                   ;; Now I create the name of the theorem to attach
                   ;; the constraint with.  So I will just create a
                   ;; weird enough name if the user has not provided
                   ;; one.

                   (thm-name
                    (if ,(null thm-name)
                        (quote
                         ,(packn
                           (list name '-
                                 abstraction '-abstraction-refinement)))
                      (quote ,thm-name)))
                   (hints (quote ,hints))
                   (instructions (quote ,instructions))
                   ;; (doc ,doc) ; Matt K. mod for v7-2
                   (rule-classes ,rule-classes)
                   (otf-flg ,otf-flg)
                   (name (quote ,name))

                   ;; Now create the functional substitution.  This
                   ;; makes use of ACL2's own functional substitution
                   ;; function, as used in functional instantiation.
                   ;; I could have tried to use functional
                   ;; instantiation itself, but this is a little more
                   ;; robust and requires me to do much less search.

                   (substitution
                    (create-alist-from-func-list
                     (quote ,functional-substitution)))

                   ;; Here is the generation of the theorem with
                   ;; appropriate functional substitution.  Note that
                   ;; if a subset of the functions are substituted
                   ;; then the rest will be assumed to satisfy their
                   ;; own constraints.  Of course I am using ACL2 to
                   ;; prove the constraints, so this optimization has
                   ;; no soundness impact.

                   (thm-form
                    (mv-let (erp val)
                            (sublis-fn substitution val nil)
                            (declare (ignore erp))
                            val))

                   ;; So now I have the theorem
                   (cumulative-thm
                    `(defthm ,thm-name
                       ,thm-form
                       :hints ,hints
                       :instructions ,instructions
                       ;; :doc ,doc ; Matt K. mod for v7-2
                       :rule-classes ,rule-classes
                       :otf-flg ,otf-flg))

                   ;; I add the theorem at the end of the other
                   ;; constraints supplied by the user.  Note the use
                   ;; of snoc.
                   (all-events (snoc (quote ,term-list)
                                     cumulative-thm)))

              ;; And now I create a new defabstraction event, so I
              ;; recursively install this as the new refinement.
              (value `(defabstraction ,name ,@all-events))))))


;; The defconcretize event is very similar to a defrefine event.  It
;; marks essentially the end of the process, so no further
;; defabstraction event is generated.

(defmacro defconcretize
  (abstraction term-list
        &key
        (thm-name 'nil)
        (functional-substitution 'nil)
        instructions hints otf-flg rule-classes doc)
  (declare (ignore doc))
  `(make-event
    (mv-let (erp val state)
            (table abstraction-table (quote ,abstraction))
            (declare (ignore erp))
            (let* ((thm-name
                    (if ,(null thm-name)
                        (quote
                         ,(packn
                           (list abstraction '-abstraction-concretized)))
                      (quote ,thm-name)))
                   (hints (quote ,hints))
                   (instructions (quote ,instructions))
                   ;; :doc ,doc ; Matt K. mod for v7-2
                   (rule-classes ,rule-classes)
                   (otf-flg ,otf-flg)
                   (substitution
                    (create-alist-from-func-list
                     (quote ,functional-substitution)))
                   (thm-form
                    (mv-let (erp val)
                            (sublis-fn substitution val nil)
                            (declare (ignore erp))
                            val))
                   (cumulative-thm
                    `(defthm ,thm-name
                       ,thm-form
                       :hints ,hints
                       :instructions ,instructions
                       ;; :doc ,doc ; Matt K. mod for v7-2
                       :rule-classes ,rule-classes
                       :otf-flg ,otf-flg))
                   (all-events (snoc (quote ,term-list) cumulative-thm)))
              (value `(progn ,@all-events))))))


;; Now test this.

;; The first test is rather trivial.  I start with an abstract
;; specification f which is known to preserve natp and consp.

(defabstraction generic-fn
  (((f *) => *))
  (local (defun f (x) x))
  (defthm f-is-nat (implies (natp x) (natp (f x))))
  (defthm f-is-cons (implies (consp x) (consp (f x)))))

;; Then I refine this to a new specification g which is also known to
;; preserve stringp.

(defrefine more-concrete-fn generic-fn
  ((((g *) => *))
   (local (defun g (x) x))
   (defthm foo (implies (natp x) (natp (g x)))))
  :functional-substitution ((f g)))


;; But look that the following fails.

(include-book "std/testing/eval" :dir :system)

(must-fail
 (defrefine flawed-more-concrete-fn generic-fn
   ((((g *) => *))
    (local (defun g (x)  (cons 1 x)))
    (defthm foo (implies (natp x) (consp (g x)))))
   :functional-substitution ((f g))))

;; A more conrete function now, which preserves everything other than
;; bad-atoms

(defrefine even-more-concrete-fn more-concrete-fn
  ((((c *) => *))
   (local (defun c (x) x))
   (defthm c-thm (implies (not (bad-atom x)) (not (bad-atom (c x))))))
  :functional-substitution ((g c)))

;; And finally we produce a concrete implementation, which is the
;; identity function.

(defconcretize even-more-concrete-fn
  ((defun d (x) x)
   (defthm d-thm (equal (d x) x)))
  :functional-substitution ((c d)))


;; Now we consider a case where we have two functions bar and baz and
;; we refine them separately.

(defabstraction fubar
  (((baz *) => *)
   ((bar *) => *))

  (local (defun baz (x) x))
  (local (defun bar (x) x))

  (defthm baz-thm
    (implies (natp x) (natp (baz x))))

  (defthm bar-thm
    (implies (natp x) (natp (bar x)))))

;; Here I only refine baz, keeping bar as is.

(defrefine concrete-baz-abstract-bar fubar
  ((((c-baz *) => *))

   (local (defun c-baz (x) x))

   (defthm c-baz-thm
     (implies (integerp x) (integerp (c-baz x)))))

  :thm-name bar-only
  :functional-substitution ((baz c-baz)))


;; I then refine bar as well.

(defrefine concrete-baz-concrete-bar concrete-baz-abstract-bar
  ((((c-bar *) => *))
     (local (defun c-bar (x) x))

   (defthm c-bar-thm
     (implies (integerp x) (integerp (c-bar x)))))
  :functional-substitution ((bar c-bar))
  :hints (("Goal"
           :use ((:instance bar-only)))))


;; Now I concretize them.

(defconcretize concrete-baz-concrete-bar
  ((defun concrete-c-baz (x) (nfix x))
   (defun concrete-c-bar (x) (ifix x)))
  :functional-substitution ((c-baz concrete-c-baz)
                            (c-bar concrete-c-bar)))

