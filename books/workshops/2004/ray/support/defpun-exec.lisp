(in-package "ACL2")

#|

 defpun-exec.lisp
 ~~~~~~~~~~~~~~~~

Author: Sandip Ray
Email: sandip@cs.utexas.edu
Date of last revision: June 20, 2003.

Objective:
---------

The goal of this book is to create a macro that will produce partial functions
with efficient executable counterparts. This is achieved in ACL2 v2-8 through
the use of the :defexec and :mbe utility.

History:
--------

Let us look at the problem in a slightly greater detail. Assume you are given a
function name foo, and a logical body (hereafter called lbody). When a function
(defun foo (x) body) is defined in ACL2, it corresponds to extending the logic
with the axiom (foo x) = body. Assume now that body calls foo, recursively. In
that case, to ensure the soundness of the added axiom, it is imperative to show
that the function terminates. Otherwise it is easy to get unsoundness in the
logic by defining (foo x) as follows:

(defun foo (x) (if (zp x) 0 (1+ (foo x))))

Note that the equation, if used to extend the logic with an axiom, will quickly
produce nil. Informally, the problem is that no function satisfies this
definintional equation.

Now, the termination requirement specifies that you need to show that there is
a measure (m x) which is an ordinal, and decreases along every recursive call,
over a well-founded set. Then it is simple to show that the cotrresponding
axiom is sound in the following sense: There is at least one function that
satisfies this definitional equation.

Now, suppose you want to define a "partial function". Such a function will not
be specified for every input, and for example, will possibly not terminate for
every input. Manolios and Moore show in [1] that you can introduce a partial
function in ACL2 by showing that there exists at least one (total) function
that satisfies its defining equation. In particular, you can show that you can
introduce every partial function that is tail-recursive.

That has significance for example in modeling computing systems such as the
JVM. Consider the following equation that "runs" a machine until it halts.

(run s) = (if (halting s) s (run (step s)))

Of course the program might not halt at all but still it is sound to add the
equation. The approach is shown using a special macro defpun, and you would
write:

(defpun run (s) (if (halting s) s (run (step s))))

This is a macro that expands into an encapsulate, that automatically produces a
witnessing function, and then adds the following definition rule:

(defthm run-def
  (equal (run s) (if (halting s) s (run (step s))))
  :rule-classes :definition)

All this is nice, but it does not allow you to actually "run" from a state,
even if the machine halts from that state.

The goal of this book is to add such executability.

For example, consider another example of a factorial program:

(defpun fact (n a) (if (equal n 0) a (fact (1- n) (* n a))))

Of course this halts only for positive integers n, but you will not be able to
"compute" (fact 5 1) and say it is 120. (Of course you can prove a theorem
saying (fact 5 1) is 120, but you cannot execute the function fact to do it.)

The macro defpun-exec we develop strives to rectify that. In particular, you
introduce an executable function that you can run in Lisp, but only after you
have shown that the executable body corresponds to the logic body under the
values. This is done by the use of guards in ACL2, and the :mbe which is
introduced in v2-8.

Form:
-----

The general form of defpun-exec is as follows:

(defpun-exec foo params lbody :ebody lbody :guard guard)

This provides a function named foo with parameters params, and (logically
speaking) a defining equation saying that foo is exactly equal to the
lbody. The guards are verified then, to show that under the guards, you
can show that lbody is equal to ebody. Hence you simply can use the
exec-body to execute foo on arguments that satisfy the guard.

By default, i.e., if the executable body ebody is not provided, it is simply
the same as lbody. Thanks to Matt Kaufmann for suggesting this.

Spec:
-----

Define a macro defpun-exec with the following properties:

(1) It takes as argument fname, params, lbody, ebody, and guards, say

(defpun-exec foo (x) (lbody x) :ebody (ebody x) :guard (guard x))

The guard argument is optional.

(2) If guards are not provided, a :guard of nil is assumed.  Thus calls of
    foo will never be evaluated.

(3) If the guards are verified, (foo x) can be evaluated for constant x, anf
the value is (ebody x)

(4) If possible do it without changing the defpun macro provided by Manolios
and Moore.

(5) If guards are provided but the verification fails, I dont want anything to
be in the ACL2 universe.

(6) If :ebody is not provided, then a :ebody of (lbody x) is assumed. Hence
executing the function is the same as executing the logical body.

Now I show how to do it.

Assumptions and acknowledgments:
-------------------------------

(1) The book defpun.lisp needs top be on the directory for this book to be
certified. Note: If you dont want that, simply put the two forms (other than
the ; (include-book "defpun") form at the bottom of the defpun.lisp file and
recertify that book.

(2) We would assume that the user works with this book using the relevant
theories as provided, and will not attempt to enable other (auxilliary)
functions we created in the process, for example the -logic functions and their
theorems. If they do, they run the risk of infinite loops in simplification
(which they of course run anyway...). We have provided a couple of theory
invariants to help the user not do something inadvertently, but we do not think
that is sufficient. However, the natural way of using it is to have the -logic
events disabled.

(4) We thank Matt Kaufmann for providing the idea of the -logic-to- theorem
described below to make :expand hints natural.

|#


#| Some helper functions. |#

;; I require the function replace-fsymb, which replaces every occurrence of the
;; function symbol orig with the function symbol new. This is somewhat brittle,
;; since we are operating on untranslated terms; for example, if we want to
;; replace bar1 with bar2 then (foo (bar1 x)) would be replaced by (foo (bar2
;; x)), which would be wrong if foo is defined by (defmacro foo (v) (list
;; 'quote (car v))).  But our goal is simply to provide a convenient macro that
;; tends to do what the user expects; we offer no soundness guarantee.

(mutual-recursion

 (defun replace-fsymb (orig new term)
   (declare (xargs :mode :program))
   (cond ((atom term) term)
         ((eq (car term) orig)
          (cons new (replace-fsymb-list orig new (rest term))))
         (t (cons (first term) (replace-fsymb-list orig new (rest term))))))

 (defun replace-fsymb-list (orig new terms)
   (declare (xargs :mode :program))
   (cond ((endp terms) nil)
         (t (cons (replace-fsymb orig new (first terms))
                  (replace-fsymb-list orig new (rest terms))))))

 )

;; Single-threaded objects (stobjs) complicate the production of executable
;; counterparts. We now implement several functions so that we can work with
;; stobjs.

;; The first thing is to create the fields. I disallow any * in anything other
;; than stobjs. So I remove *. There is also a little trouble here: when a
;; field of a stobj (call it fld) is an array, then the fld name is typically
;; *fldi*. So what I do is remove the last \#i of the the fld name. This has
;; the unfortunate consequence (since I am being a little sloppy) to remove the
;; last i if the fld name is in fact not an array but an actual fld ending with
;; i. I can deal with that, but since the use of all this in case of stobjs is
;; not clear anyhow, I am currently only providing a basic macro that works
;; with stobjs, but I am a little sloppy about all the details. In short, to
;; use this macro in its current form, you should not have a fld in a stobj
;; whose name ends with i. If you do, then nothing is guaranteed, and the macro
;; will probably not go through.

(defun remove-last-i (lst)
  (if (endp lst) nil
    (if (endp (rest lst))
        (if (eq (first lst) #\I)
            nil
          (list (first lst)))
      (cons (first lst) (remove-last-i (rest lst))))))

(defun remove-*-from-list (lst)
  (cond ((endp lst) nil)
        ((eq (first lst) #\*)
         (remove-*-from-list (rest lst)))
        (t (cons (first lst) (remove-*-from-list (rest lst))))))

(defun symbol-without-*-and-last-i (symb)
  (declare (xargs :mode :program))
  (let* ((str (symbol-name symb))
         (lst (coerce str 'list))
         (lst (remove-*-from-list lst))
         (lst (remove-last-i lst))
         (symb (packn lst)))
    symb))

(defun remove-*-and-last-i (alist)
  (declare (xargs :mode :program))
  (if (endp alist) nil
    (acons (caar alist)
           (symbol-without-*-and-last-i (cdar alist))
           (remove-*-and-last-i (rest alist)))))

;; What the code so far did was to replace the vals of an alist (kept the keys
;; same) by stripping * (and the last i) from any of the characters. Now I swap
;; keys and vals so that these fields now become the keys.

(defun swap-key-val (alist)
  (if (endp alist) nil
    (acons (cdar alist) (caar alist)
           (swap-key-val (rest alist)))))

;; Now I am going to create a number of alists, basically everything that is
;; supported by stobjs. I will create access-alist (but that is not really
;; required), update-alist, update-i-alist, and resize-alist.

(defun create-update-alist (alist)
  (declare (xargs :mode :program))
  (if (endp alist) nil
    (acons (packn (list 'update- (caar alist)))
           (cdar alist)
           (create-update-alist (rest alist)))))

(defun create-access-i-alist (alist)
  (declare (xargs :mode :program))
  (if (endp alist) nil
    (acons (packn (list (caar alist) 'i))
           (cdar alist)
           (create-update-alist (rest alist)))))


(defun create-update-i-alist (alist)
  (declare (xargs :mode :program))
  (if (endp alist) nil
    (acons (packn (list 'update- (caar alist) 'i))
           (cdar alist)
           (create-update-alist (rest alist)))))

(defun create-resize-alist (alist)
  (declare (xargs :mode :program))
  (if (endp alist) nil
    (acons (packn (list 'resize- (caar alist)))
           (cdar alist)
           (create-update-alist (rest alist)))))



;; Finally we write a collection of functions that simply replace all the stobj
;; calls with the calls to corresponding nth and update-nth.

(mutual-recursion

 (defun replace-fsymb-alist-update (term alist)
   (declare (xargs :mode :program))
   (if (atom term) term
     (if (member-eq (first term) '(let let*))
         (list (first term)
               (replace-fsymb-list-alist-update (second term) alist)
               (replace-fsymb-alist-update (third term) alist))
       (let ((alist-fld (assoc-eq (car term) alist)))
         (if alist-fld
             (cons 'update-nth
                   (cons (cdr alist-fld)
                         (replace-fsymb-list-alist-update (rest term) alist)))
           (cons (first term) (replace-fsymb-list-alist-update (rest term) alist)))))))

 (defun replace-fsymb-list-alist-update (terms alist)
   (declare (xargs :mode :program))
   (cond ((endp terms) nil)
         (t (cons (replace-fsymb-alist-update (first terms) alist)
                  (replace-fsymb-list-alist-update (rest terms) alist)))))

)

(mutual-recursion

 (defun replace-fsymb-alist-resize (term alist)
   (declare (xargs :mode :program))
   (if (atom term) term
     (if (member-eq (first term) '(let let*))
         (list (first term)
               (replace-fsymb-list-alist-resize (second term) alist)
               (replace-fsymb-alist-resize (third term) alist))
       (let ((alist-fld (assoc-eq (car term) alist)))
         (if alist-fld
             (list 'update-nth
                   (cdr alist-fld)
                   (list 'resize-list (list 'nth
                                            (cdr alist-fld)
                                            (third term))
                         (second term)
                         nil)
                   (third term))
           (cons (first term) (replace-fsymb-list-alist-resize (rest term) alist)))))))

 (defun replace-fsymb-list-alist-resize (terms alist)
   (declare (xargs :mode :program))
   (cond ((endp terms) nil)
         (t (cons (replace-fsymb-alist-resize (first terms) alist)
                  (replace-fsymb-list-alist-resize (rest terms) alist)))))

)


(mutual-recursion

 (defun replace-fsymb-alist-access (term alist)
   (declare (xargs :mode :program))
   (if (atom term) term
     (if (member-eq (first term) '(let let*))
         (list (first term)
               (replace-fsymb-list-alist-access (second term) alist)
               (replace-fsymb-alist-access (third term) alist))
     (let ((alist-fld (assoc-equal (car term) alist)))
       (if alist-fld
           (cons 'nth
                 (cons (cdr alist-fld)
                       (replace-fsymb-list-alist-access (rest term) alist)))
         (cons (first term) (replace-fsymb-list-alist-access (rest term) alist)))))))

 (defun replace-fsymb-list-alist-access (terms alist)
   (declare (xargs :mode :program))
   (cond ((endp terms) nil)
         (t (cons (replace-fsymb-alist-access (first terms) alist)
                  (replace-fsymb-list-alist-access (rest terms) alist)))))

)



(mutual-recursion

 (defun replace-fsymb-alist-access-i (term alist)
   (declare (xargs :mode :program))
   (if (atom term) term
     (if (member-eq (first term) '(let let*))
         (list (first term)
               (replace-fsymb-list-alist-access-i (second term) alist)
               (replace-fsymb-alist-access-i (third term) alist))
     (let ((alist-fld (assoc-equal (car term) alist)))
       (if alist-fld
           (list 'nth
                 (replace-fsymb-alist-access-i (second term) alist)
                 (list 'nth (cdr alist-fld) (replace-fsymb-alist-access-i
                                             (third term) alist)))
         (cons (first term) (replace-fsymb-list-alist-access-i (rest term) alist)))))))

 (defun replace-fsymb-list-alist-access-i (terms alist)
   (declare (xargs :mode :program))
   (cond ((endp terms) nil)
         (t (cons (replace-fsymb-alist-access-i (first terms) alist)
                  (replace-fsymb-list-alist-access-i (rest terms) alist)))))

)

(mutual-recursion

 (defun replace-fsymb-alist-update-i (term alist)
   (declare (xargs :mode :program))
   (if (atom term) term
     (if (member-eq (first term) '(let let*))
         (list (first term)
               (replace-fsymb-list-alist-update-i (second term) alist)
               (replace-fsymb-alist-update-i (third term) alist))
     (let ((alist-fld (assoc-equal (car term) alist)))
       (if alist-fld
           (list 'update-nth
                 (cdr alist-fld)
                 (list 'update-nth
                       (replace-fsymb-alist-update-i (second term) alist)
                       (replace-fsymb-alist-update-i (third term) alist)
                       (list 'nth
                             (cdr alist-fld)
                             (replace-fsymb-alist-update-i (fourth term)
                                                           alist)))
                 (replace-fsymb-alist-update-i (fourth term) alist))
         (cons (first term) (replace-fsymb-list-alist-update-i (rest term) alist)))))))

 (defun replace-fsymb-list-alist-update-i (terms alist)
   (declare (xargs :mode :program))
   (cond ((endp terms) nil)
         (t (cons (replace-fsymb-alist-update-i (first terms) alist)
                  (replace-fsymb-list-alist-update-i (rest terms) alist)))))

)

(defun replace-with-stobj-call (term wrld stobj)
  (declare (xargs :mode :program))
  (let* ((accessor-name (cdr (getprop stobj 'accessor-names nil
                                      'current-acl2-world wrld)))
         (alist (remove-*-and-last-i accessor-name))
         (access-alist (swap-key-val alist))
         (resize-alist (create-resize-alist access-alist))
         (update-alist (create-update-alist access-alist))
         (access-i-alist (create-access-i-alist access-alist))
         (update-i-alist (create-update-i-alist access-alist))
         (term (replace-fsymb-alist-resize term resize-alist))
         (term (replace-fsymb-alist-update term update-alist))
         (term (replace-fsymb-alist-access term access-alist))
         (term (replace-fsymb-alist-access-i term access-i-alist))
         (term (replace-fsymb-alist-update-i term update-i-alist)))
    term))

(defun replace-with-stobj-call-list (term wrld stobjs)
  (declare (xargs :mode :program))
  (if (endp stobjs)
      term
    (let* ((term (replace-with-stobj-call term wrld (first stobjs))))
      (replace-with-stobj-call-list term wrld (rest stobjs)))))


(defun replace-with-stobj-calls (term wrld stobjs)
  (declare (xargs :mode :program))
  (if (endp stobjs) term
    (let* ((term (replace-with-stobj-call term wrld (first stobjs))))
      (replace-with-stobj-calls term wrld (rest stobjs)))))

#| Now we get into the actual macro defpun-exec |#

;; We comment on the macro below assuming that you have given us an defpun-exec
;; of the form:

;; (defpun-exec foo (x) (lbody x) :ebody (ebody x) :guard (guard x))

(include-book "misc/defpun" :dir :system)

(defun defpun-exec-fn (fname params lbody ebody stobjs guard measure
                             termination-hints guard-hints defrule-hints state)
  (declare (xargs :mode :program
                  :stobjs state))
  (let* ((ebody (if (null ebody) lbody ebody))
         (stobjs (if (symbolp stobjs) (list stobjs) stobjs))
         (ebody (if (null stobjs)
                    ebody
                  (replace-with-stobj-call-list ebody (w state) stobjs)))
         (lfname (packn (list fname '-logic)))
         (defn-thm (packn (list fname '-def)))
         (declare-form (list 'declare (append (list 'xargs :guard guard)
                                              (if measure
                                                  (list :measure measure)
                                                nil)
                                              (if termination-hints
                                                  (list :hints
                                                        termination-hints)
                                                nil)
                                              (if guard-hints
                                                  (list :guard-hints
                                                        guard-hints)
                                                nil)))))

    (let ((form
    `(encapsulate nil

      ;; First we define a standard defpun function, call it defpun foo-logic,
      ;; and the body of foo-logic (which we will call (defpun-body x) is
      ;; simply lbody with all calls to foo replaced by (recursive) calls to
      ;; foo-logic.

      (defpun ,lfname ,params
        ,(replace-fsymb fname lfname lbody))

      ;; Now we define the function foo as:
      ;;  (defexec foo (x)
      ;;    (declare (xargs :guard (guard x)))
      ;;    (mbe :logic (foo-logic x) :exec (ebody x)))

      ;; Note: It is possible to use defun to define foo. That is logically
      ;; sound, and the macro would go thru. However, the use of defexec
      ;; insures that when we do execute the function using ebody, the
      ;; execution eventually terminates.


      (defexec ,fname ,params
        ,declare-form
        (mbe :logic ,(cons lfname params)
             :exec ,ebody))


      ;; We have therefore achieved the goal of the executable part. Now we
      ;; provide a definition rule in accordance with the spec.

      ;; (defthm foo-def (equal (foo x) (lbody x)) :rule-classes :definition)

      (defthm ,defn-thm
        (equal ,(cons fname params)
               ,lbody)
        :rule-classes :definition :hints ,defrule-hints)

      ;; So we have achieved the goal. We have provided a definition rule and
      ;; we have provided an executable counterpart. So I would think that we
      ;; satisfied ourselves. I would disable some stuff now, but before that,
      ;; I would like to comment on some suggestions by Matt Kaufmann and
      ;; during the ACL2 meeting on 06/18/2003.

      ;; When I first did this, I was dissatisfied by the following:
      ;;
      ;; Once the definition rule is present you would think that you dont want
      ;; anything to do with foo-logic. So I would not like to have the logical
      ;; body of foo enabled, but rather I would simply have the definition
      ;; rule foo-def above to do what we want with foo. Unfortunately, if the
      ;; user gives a :expand hint, the definition ACL2 opens up is the logical
      ;; which is (foo-logic x) rather than the last definition rule. So I
      ;; still have something to do with it. When I raised the question in the
      ;; ACL2 meeting, Matt came up with the following suggestion:

      ;; Add a rule foo-logic-def of the form (equal (foo-logic x) (lbody
      ;; x)). The idea, then, should be to disable the theorem foo-logic-def
      ;; (introduced by defpun) so that when a :expand hint occurs to foo it
      ;; will use the definition of foo to get logic-body and that will
      ;; immediately be rewritten to (lbody x). That was a nice
      ;; suggestion. Thanks, Matt.

      ;; (defthm foo-logic-to-foo
      ;;   (equal (foo-logic x) (lbody s))
      ;;  :rule-classes :definition)

      (defthm ,(packn (list lfname '-to- fname))
        (equal ,(cons lfname params) ,lbody)
        :rule-classes :definition)

      ;; Now we do simply want the definition rule foo-def to apply, and (only
      ;; in case of an expand hint would we want to have the special rule
      ;; foo-logic-to-foo. So I would rather disable the body of foo in
      ;; general, and also the theorem foo-logic-def which was provided by the
      ;; defpun.

      ;; (in-theory (disable foo (:definition foo-logic-def)))

      (in-theory (disable ,fname (:definition ,(packn (list lfname '-def)))))

      ;; I think some form of theory invariants should be present here, since I
      ;; dont quite like the body of foo and definition foo-def to be both
      ;; enabled, because then foo-def ought never to be used. (foo is
      ;; non-recursive.) Of course it is not a big point to have a theory
      ;; invariant, but here is what I am thinking. A user can either use
      ;; foo-def to deduce properties of foo, or should use the body of foo along
      ;; with facts about foo-logic. To me these are two different (incompatible)
      ;; strategies. So either he should leave foo enabled, not use foo-def or
      ;; foo-logic-to-foo, and provide rules to reason about foo-logic. Or he
      ;; should heve foo disabled, not use foo-logic-def, and use foo-def, and (in
      ;; case of expand hints) foo-logic-to-foo. I think we should have an
      ;; invariant saying that  one of the two theories is used.

      ;; So, here are the theory invariants I provide with this macro. If these
      ;; are not useful then simply comment them out and recertify the book.

      ;; (theory-invariant (incompatible (:definition foo)
      ;;                                 (:definition foo-def)))

      (theory-invariant (incompatible (:defintitiion ,fname)
                                      (:definition
                                       ,(packn (list fname '-def)))))

      ;; (theory-invariant (incompatible (:definition foo-logic-to-foo)
      ;;                                 (:definition foo-logic-def)))

      (theory-invariant (incompatible (:definition
                                       ,(packn (list lfname '-to- fname)))
                                      (:definition
                                       ,(packn (list lfname '-def))))))))

      ;; And that is it. We might have to add more theory invariants, but I
      ;; think that is only important if the user wants to tweak with the
      ;; current structure. The structure is foo is disabled, and only opens
      ;; via an expand hint which would immediately rewrite to (lbody x) using
      ;; the  definition foo-logic-to-foo, and the rest are taken care of by
      ;; the rule foo-def which was the only rule in the defpun
      ;; anyway. However, if the user wants to open up other definitions, he
      ;; better be structured.
      (ld (list form)

          :ld-user-stobjs-modified-warning

; Matt K. mod: ACL2 now requires keyword :ld-user-stobjs-modified-warning in
; code.  If this macro is only to be evaluated at the top level, that keyword
; isn't needed.  But I'm including it, with value :same to preserve existing
; behavior, just in case someone uses it in code.  Perhaps more thought should
; be given to whether or not we want a warning here when a user stobj is
; modified.

          :same))

))

(defmacro defpun-exec (fn params lbody
                          &key
                          (ebody '())
                          (guard '())
                          (measure '())
                          (termination-hints '())
                          (guard-hints '())
                          (defrule-hints '())
                          (stobjs '()))
  (declare (xargs :guard (and (symbolp fn)
                              (or (symbolp stobjs)
                                  (symbol-listp stobjs))
                              (symbol-listp params))))
    `(defpun-exec-fn
       (quote ,fn)
       (quote ,params)
       (quote ,lbody)
       (quote ,ebody)
       (quote ,stobjs)
       (quote ,guard)
       (quote ,measure)
       (quote ,termination-hints)
       (quote ,guard-hints)
       (quote ,defrule-hints)
       state))








#|

Testing
=======

(1) I dont verify the guard below. So it will produce the logic definition and
the definition rule, but will produce a guard of nil, and hence in effect
disable the executable counterpart. This has the precise effect of simply
providing a defpun.

ACL2 !>(defpun-exec fact (n a)
             (if (equal n 0) a (fact (1- n) (* n a)))
             :ebody (if (zp n) a (* n (fact (1- n) a))))

So this will produce everything but you cannot evaluate it.

ACL2 !>(trace$ fact)
NIL
ACL2 !>(thm (equal (fact 5 1) 120))
1> (ACL2_*1*_ACL2::FACT 5 1)

By case analysis we reduce the conjecture to

Goal'
(EQUAL (HIDE (FACT 5 1)) 120).
  2> (ACL2_*1*_ACL2::FACT 5 1)

Name the formula above *1.

No induction schemes are suggested by *1.  Consequently, the proof
attempt has failed.

Summary
Form:  ( THM ...)
Rules: ((:DEFINITION HIDE))
Warnings:  None
Time:  0.00 seconds (prove: 0.00, print: 0.00, other: 0.00)

******** FAILED ********  See :DOC failure  ******** FAILED ********
ACL2 !>

(2) However, now observe that the verified guards work.

ACL2 !>(defpun-exec trfact (n a)
             (if (equal n 0) a (trfact (1- n) (* n a)))
             :ebody (if (zp n) a  (trfact (1- n) (* n a)))
             :guard (and (integerp n) (integerp a) (>= n 0) (>= a 0)))

ACL2 !>(trace$ trfact)
NIL
ACL2 !>(thm (equal (trfact 5 1) 120))
1> (ACL2_*1*_ACL2::TRFACT 5 1)
  2> (TRFACT 5 1)
    3> (TRFACT 4 5)
      4> (TRFACT 3 20)
        5> (TRFACT 2 60)
          6> (TRFACT 1 120)
            7> (TRFACT 0 120)
            <7 (TRFACT 120)
          <6 (TRFACT 120)
        <5 (TRFACT 120)
      <4 (TRFACT 120)
    <3 (TRFACT 120)
  <2 (TRFACT 120)
<1 (ACL2_*1*_ACL2::TRFACT 120)

But we reduce the conjecture to T, by the :executable-counterparts
of EQUAL and TRFACT.

Q.E.D.

Summary
Form:  ( THM ...)
Rules: ((:EXECUTABLE-COUNTERPART EQUAL)
        (:EXECUTABLE-COUNTERPART TRFACT))
Warnings:  None
Time:  0.00 seconds (prove: 0.00, print: 0.00, other: 0.00)

Proof succeeded.
ACL2 !>

(3) Now let use just check that even if you do not provide an ebody then it can
    evaluate the lbody (as long as the lbody can be defined with defpun and
    defexec shows that the guard proof guarantees termination).

ACL2 !>(defpun-exec trfact-without-ebody (n a)
           (if (equal n 0) a (trfact-without-ebody (1- n) (* n a)))
           :guard (and (integerp n) (integerp a) (>= n 0) (>= a 0)))

ACL2 !>(trace$ trfact)
NIL
ACL2 !>(trace$ trfact-without-ebody)
NIL
ACL2 !>(thm (equal (trfact-without-ebody 5 1) 120))
1> (ACL2_*1*_ACL2::TRFACT-WITHOUT-EBODY 5 1)
  2> (TRFACT-WITHOUT-EBODY 5 1)
    3> (TRFACT-WITHOUT-EBODY 4 5)
      4> (TRFACT-WITHOUT-EBODY 3 20)
        5> (TRFACT-WITHOUT-EBODY 2 60)
          6> (TRFACT-WITHOUT-EBODY 1 120)
            7> (TRFACT-WITHOUT-EBODY 0 120)
            <7 (TRFACT-WITHOUT-EBODY 120)
          <6 (TRFACT-WITHOUT-EBODY 120)
        <5 (TRFACT-WITHOUT-EBODY 120)
      <4 (TRFACT-WITHOUT-EBODY 120)
    <3 (TRFACT-WITHOUT-EBODY 120)
  <2 (TRFACT-WITHOUT-EBODY 120)
<1 (ACL2_*1*_ACL2::TRFACT-WITHOUT-EBODY 120)

But we reduce the conjecture to T, by the :executable-counterparts
of EQUAL and TRFACT-WITHOUT-EBODY.

Q.E.D.

Summary
Form:  ( THM ...)
Rules: ((:EXECUTABLE-COUNTERPART EQUAL)
        (:EXECUTABLE-COUNTERPART TRFACT-WITHOUT-EBODY))
Warnings:  None
Time:  0.01 seconds (prove: 0.01, print: 0.00, other: 0.00)

Proof succeeded.
ACL2 !>

We provide another little test to see that the macro works with stobjs. This
also shows how the hints work. Note that we need to provide the explicit guard
for the stobj. I can produce the guard stobjp automatically if necessary, but
in this case it is fine.

ACL2 !>(defstobj foo (fld :type (array T (100)) :resizable t))

;; The extension with stobjs requires that you provide the guard. I can
;; automate the guard production if this is found interesting.

ACL2 !>(defun foop-exec (foo)
         (declare (xargs :guard T))
         (and (true-listp foo)
              (equal (len foo) 1)
              (true-listp (car foo))))


;; Here is an example thatworks with stobjs. Notice that in the :logic argument
;; we had to actually expand out all the stobj calls. This is because defpun
;; cannot handle let and let*. I presume it will, at some future time. But
;; either way, defpun-exec has no real problem with let and let* (although I
;; dont support mv-let yet). Anyway, this example shows that you can now do a
;; slow execution.

ACL2 !>(defpun-exec bar (x foo)
         (if (equal x 0)
             foo
           (bar (- x 1) (update-fldi 0 2 (resize-fld 100 foo))))
         :ebody (if (equal x 0)
                    foo
                  (let* ((foo (resize-fld 100 foo))
                         (foo (update-fldi 0 2 foo))
                         (foo (bar (- x 1) foo)))
                       foo))
         :guard (and (foop-exec foo) (natp x))
         ;; You can give several hints if you wish, but for this example that
         ;; is not necessary.
         :stobjs foo)

ACL2 !>(trace$ bar)
NIL

ACL2 !>(bar 2 '((12 0 0 0)))
1> (ACL2_*1*_ACL2::BAR 2 ((12 0 0 0)))
  2> (BAR 2 ((12 0 0 0)))
    3> (BAR 1
            ((2 0 0 0 NIL NIL NIL NIL NIL NIL NIL
                NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
                NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
                NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
                NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
                NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
                NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
                NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
                NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
                NIL NIL NIL NIL NIL NIL NIL NIL NIL)))
      4> (BAR 0
              ((2 0 0 0 NIL NIL NIL NIL NIL NIL NIL
                  NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
                  NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
                  NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
                  NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
                  NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
                  NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
                  NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
                  NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
                  NIL NIL NIL NIL NIL NIL NIL NIL NIL)))
      <4 (BAR ((2 0 0 0 NIL NIL NIL NIL NIL NIL NIL
                  NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
                  NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
                  NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
                  NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
                  NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
                  NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
                  NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
                  NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
                  NIL NIL NIL NIL NIL NIL NIL NIL NIL)))
    <3 (BAR ((2 0 0 0 NIL NIL NIL NIL NIL NIL NIL
                NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
                NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
                NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
                NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
                NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
                NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
                NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
                NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
                NIL NIL NIL NIL NIL NIL NIL NIL NIL)))
  <2 (BAR ((2 0 0 0 NIL NIL NIL NIL NIL NIL NIL
              NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
              NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
              NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
              NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
              NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
              NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
              NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
              NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
              NIL NIL NIL NIL NIL NIL NIL NIL NIL)))
<1 (ACL2_*1*_ACL2::BAR ((2 0 0 0 NIL NIL NIL NIL NIL NIL NIL
                           NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
                           NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
                           NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
                           NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
                           NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
                           NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
                           NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
                           NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
                           NIL NIL NIL NIL NIL NIL NIL NIL NIL)))
((2 0 0 0 NIL NIL NIL NIL NIL NIL NIL
    NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
    NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
    NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
    NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
    NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
    NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
    NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
    NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
    NIL NIL NIL NIL NIL NIL NIL NIL NIL))
ACL2 !>


|#






