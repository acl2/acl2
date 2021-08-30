; Copyright (C) 2016, ForrestHunt, Inc.
; Written by Matt Kaufmann and J Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; The Maximal Defun of Apply$-Prim

; We define *apply$-primitives*, apply$-primp, and apply$-prim to include
; almost all functions in the bootstrap world that could have badges.  We
; intentionally skip a few problematic or silly primitives, like wormhole1
; which has some syntactic restrictions on how it can be called -- restrictions
; that would complicate or confuse any attempt to apply$ 'wormhole1.  We also
; introduce and verify a metafunction for simplifying (apply$-prim 'fn args).

; This model of APPLY$-PRIM, i.e., MODAPP::APPLY$-PRIM, handles more primitives
; than the built-in ACL2::APPLY$-PRIM because the model is defined in a fully
; booted ACL2 image while the built-in APPLY$-PRIM is defined before the
; boot-strap process is completed.  For example, MODAPP::APPLY$-PRIM can apply
; 'ACL2::APPLY$-PRIM, whereas ACL2::APPLY$-PRIM cannot!

(in-package "MODAPP")

; Handling the Primitives

(defun first-order-like-terms-and-out-arities1 (runes avoid-fns wrld ans)
  (declare (xargs :mode :program))

; We return a list of the form (... ((fn . formals) . output-arity) ...).  See
; first-order-like-terms-and-out-arities for details.

  (cond
   ((endp runes) ans)
   (t (let ((fn (base-symbol (car runes))))
        (cond
         ((and (acl2-system-namep fn wrld)

; In ACL2(r), we avoid non-classical functions, to avoid failure of the
; defevaluator event in the book version of apply-prim.lisp.

               #+:non-standard-analysis
               (acl2::classicalp fn wrld)

               (not (member-eq fn avoid-fns))
               (all-nils (getpropc fn 'stobjs-in nil wrld))

; Note that even functions taking state like state-p and global-table-cars,
; i.e., that take a STATE-STATE input, will have STATE in their stobjs-in and
; hence will fail the test just above.  So we don't need to give special
; treatment to such functions.

               (all-nils (getpropc fn 'stobjs-out nil wrld)))

; Note that stobj creators take no stobjs in but return stobjs.  We don't want
; any such functions in our answer!  Also, we don't want to think about
; functions like BOUNDP-GLOBAL1 and 32-BIT-INTEGER-STACK-LENGTH1 that use
; STATE-STATE as a formal preventing their execution.

          (first-order-like-terms-and-out-arities1
           (cdr runes)
           avoid-fns wrld
           (cons (cons (cons fn (formals fn wrld))
                       (length (getpropc fn 'stobjs-out nil wrld)))
                 ans)))
         (t (first-order-like-terms-and-out-arities1
             (cdr runes)
             avoid-fns wrld
             ans)))))))

(defun first-order-like-terms-and-out-arities (world)

; Search the world for every ACL2 primitive function that does not traffic (in
; or out) in stobjs or state and that are not among a select few (named below)
; that require trust tags or have syntactic restrictions on their calls.  Note
; that our final list includes functions that return multiple values, which are
; not warranted but will have badges: they are first-order-like and could be
; used in the subsequent definitions of warranted functions provided their
; multiple values are ultimately turned into a single returned value.

; Return (... ((fn . formals) . output-arity) ...), that for each identified
; fn, pairs a term, (fn . formals), with its output arity.  We will ultimately
; need those terms to generate the defevaluator event that will define
; apply$-prim and to generate the :meta theorem we need.  We need the output
; arity in computing the badges of the functions; see
; compute-badge-of-primitives.

; We accumulate the pairs in reverse order, which (it turns out) puts the most
; basic, familiar ACL2 primitives first.

; The ``select few'' we do not collect are prohibited as per the comments
; below.  Note: Many functions that we do include actually have no utility in
; this setting.  The symbols commented out below were once so identified (by
; manual inspection).  E.g., does any user really want to call
; make-wormhole-status via apply$?  But if all calls are legal without a trust
; tag, we now include it, just to live up to the name "Maximal".

  (declare (xargs :mode :program))
  (first-order-like-terms-and-out-arities1
   (member-equal '(:DEFINITION ACL2::EV$-LIST)

; This member-equal call produces a tail of the function-theory that eliminates
; runes near the end of ACL2 source file boot-strap-pass-2-b.lisp, added around
; the end of January, 2019 to support loop$, thus eliminating definition runes
; like ACL2::APPLY$-WARRANT-MEMPOS-DEFINITION that do not have corresponding
; function symbols.

                 (function-theory :here))
   '(SYNP                                   ; bad
     HIDE                                   ; stupid
     MV-LIST                                ; restricts arguments
     WORMHOLE1                              ; restricts arguments
     WORMHOLE-EVAL                          ; restricts arguments
;    MAKE-WORMHOLE-STATUS
;    SET-WORMHOLE-DATA
;    SET-WORMHOLE-ENTRY-CODE
;    WORMHOLE-DATA
;    WORMHOLE-ENTRY-CODE
;    WORMHOLE-STATUSP
     SYS-CALL                               ; bad -- requires trust tag
     HONS-CLEAR!                            ; bad -- requires trust tag
     HONS-WASH!                             ; bad -- requires trust tag
     UNTOUCHABLE-MARKER                     ; bad -- untouchable
     ASET1-TRUSTED                          ; bad -- untouchable (added 7/2021)
;    BREAK$
;    PRINT-CALL-HISTORY
;    NEVER-MEMOIZE-FN
;    MEMOIZE-FORM
;    CLEAR-MEMOIZE-STATISTICS
;    MEMOIZE-SUMMARY
;    CLEAR-MEMOIZE-TABLES
;    CLEAR-MEMOIZE-TABLE
     )
   world
   nil))

; We need to know the names, formals, and output arities of the primitives in
; order to generate the defevaluator form, meta theorem, and badges below.  So
; we save them in *first-order-like-terms-and-out-arities*, which looks like:

; (defconst *first-order-like-terms-and-out-arities*
;   '(((ACL2-NUMBERP X) . 1)
;     ((BAD-ATOM<= X Y) . 1)
;     ((BINARY-* X Y) . 1)
;     ...))

; But in apply.lisp and in the support for the execution of the stubs
; badge-userfn and apply$-userfn we do not need the formals and we sometimes
; need the arities.  So we define another constant which is used in those
; places.  That constant, *badge-prim-falist*, is a fast alist.

(make-event
 `(defconst *first-order-like-terms-and-out-arities*
    ',(first-order-like-terms-and-out-arities (w state))))

(defrec apply$-badge (authorization-flg arity . ilks) nil)

; These constants are not actually used in this book but are used in several
; books that include apply-prim.lisp so we define them once, here.

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

(defun compute-badge-of-primitives (terms-and-out-arities)
  (cond ((endp terms-and-out-arities) nil)
        (t (let* ((term (car (car terms-and-out-arities)))
                  (fn (ffn-symb term))
                  (formals (fargs term))
                  (output-arity (cdr (car terms-and-out-arities))))
             (hons-acons fn
                         (make apply$-badge
                               :authorization-flg (eql output-arity 1)
                               :arity (length formals)
                               :ilks t)
                         (compute-badge-of-primitives
                          (cdr terms-and-out-arities)))))))

(defconst *badge-prim-falist*  ; this is a Fast-alist!
  (compute-badge-of-primitives *first-order-like-terms-and-out-arities*))

(defun apply$-primp (fn)
  (declare (xargs :guard t))
  (and (hons-get fn *badge-prim-falist*) t))

(defun badge-prim (fn)
  (declare (xargs :guard t))
  (cdr (hons-get fn *badge-prim-falist*)))

; We need to know that badge-prim returns either nil or a badge of the form
; (APPLY$-BADGE flg arity . T).  This would be trivial except for the fact that
; there are so many cases (because the alist is so long).  So we resort to a
; standard trick for proving something about a big constant: define a function,
; named check-it! below, to check the property computationally, prove that the
; property holds of x if (check-it x) is t, then derive the main theorem by
; instantiating that lemma with {x <-- '<big-constant>}.

(defun apply$-badgep (x)
  (and (consp x)
       (eq (car x) 'apply$-badge)
       (consp (cdr x))
       (booleanp (access apply$-badge x :authorization-flg))
       (consp (cddr x))
       (natp (access apply$-badge x :arity))
       (or (eq (access apply$-badge x :ilks) t)
           (and (true-listp (access apply$-badge x :ilks))
                (equal (len (access apply$-badge x :ilks))
                       (access apply$-badge x :arity))
                (not (all-nils (access apply$-badge x :ilks)))
                (subsetp (access apply$-badge x :ilks) '(nil :fn :expr))))))

(defthm apply$-badgep-properties ; only selected properties!
  (implies (apply$-badgep x)
           (and (consp x)
                (natp (access apply$-badge x :arity))
                (or (eq (access apply$-badge x :ilks) t)
                    (and (true-listp (access apply$-badge x :ilks))
                         (equal (len (access apply$-badge x :ilks))
                                (access apply$-badge x :arity))))))

; Note: Unfortunately, record accessors translate into lambda applications.
; :Rewrite rules handle this appropriately by beta reducing the lambda
; applications in the conclusion.  But :linear rules do not.  So we've written
; all the rules in terms of car/cdr nests rather than access terms.

  :rule-classes
  ((:compound-recognizer
    :corollary (implies (apply$-badgep x)
                        (consp x)))
   (:linear
    :corollary (implies (apply$-badgep x)
                        (<= 0 (CAR (CDR (CDR x))))))
   (:rewrite
    :corollary (implies (apply$-badgep x)
                        (integerp (CAR (CDR (CDR x))))))
   (:rewrite
    :corollary (implies (and (apply$-badgep x)
                             (not (eq (CDR (CDR (CDR x))) t)))
                        (and (true-listp (CDR (CDR (CDR x))))
                             (equal (len (CDR (CDR (CDR x))))
                                    (CAR (CDR (CDR x)))))))))

(encapsulate
  nil
  (local
   (defun check-it! (alist)
     (cond ((atom alist) t)
           (t (and (consp (car alist))
                   (apply$-badgep (cdr (car alist)))
                   (eq (access apply$-badge (cdr (car alist)) :ilks) t)
                   (check-it! (cdr alist)))))))
  (local
   (defthm check-it!-works
     (implies (check-it! alist)
              (implies (hons-get fn alist)
                       (and (consp (hons-get fn alist))
                            (apply$-badgep (cdr (hons-get fn alist)))
                            (eq (access apply$-badge (cdr (hons-get fn alist)) :ilks) t))))
     :rule-classes nil))

  (defthm badge-prim-type
    (implies (apply$-primp fn)
             (and (apply$-badgep (badge-prim fn))
                  (eq (cdr (cdr (cdr (badge-prim fn)))) t)))
    :hints (("Goal" :use (:instance check-it!-works (alist *badge-prim-falist*))
             :in-theory (disable check-it! hons-get)))
    :rule-classes
    ((:rewrite
      :corollary (implies (apply$-primp fn)
                          (and (apply$-badgep (badge-prim fn))
                               (eq (cdr (cdr (cdr (badge-prim fn)))) t))))
     (:forward-chaining
      :corollary (implies (apply$-primp fn)
                          (apply$-badgep (badge-prim fn)))))))

(defun n-car-cadr-caddr-etc (n x)
  (if (zp n)
      nil
      (cons `(CAR ,x)
            (n-car-cadr-caddr-etc (- n 1) `(CDR ,x)))))

(defun make-apply$-prim-body-fn (falist)

; Falist = ((fn . badge) ...) and is a fast alist although we do not actually
; use it as an alist here; we just cdr down it.

  (declare (xargs :mode :program))
  (cond
   ((endp falist) nil)
   (t (let ((fn (car (car falist)))
            (badge (cdr (car falist))))
        (cond
         ((equal (access apply$-badge badge :authorization-flg) t)
          (cons `(,fn (,fn ,@(n-car-cadr-caddr-etc (access apply$-badge badge :arity) 'ARGS)))
                (make-apply$-prim-body-fn (cdr falist))))
         (t (make-apply$-prim-body-fn (cdr falist))))))))

(defmacro make-apply$-prim-body ()
; We ignore primitives whose authorization-flg is nil.
  `(case fn
     ,@(make-apply$-prim-body-fn *badge-prim-falist*)
     (otherwise nil)))

(defun apply$-prim (fn args)
  (make-apply$-prim-body))

; The above defun of apply$-prim contains a case statement with about 800
; cases.  Rewriting it causes stack overflow with the nominal rewrite stack
; size of 1000.  For example, we cannot prove: (thm (equal (apply$-prim 'tamep
; (list x)) (tamep x))).  We will therefore temporarily enlarge the stack and
; verify a metafunction which will enable MUCH faster reduction of (apply$-prim
; 'fn args).

(set-rewrite-stack-limit 4000) ; local to this book

(defun meta-apply$-prim (term)
  (cond ((and (consp term)
              (eq (ffn-symb term) 'apply$-prim)
              (quotep (fargn term 1))
              (symbolp (cadr (fargn term 1))))
         (let* ((fn (cadr (fargn term 1)))
                (args (fargn term 2))
                (temp (hons-get fn *badge-prim-falist*)))
           (cond
            ((or (null temp)
                 (null (access apply$-badge (cdr temp) :authorization-flg)))
             term)
            (t `(,fn ,@(n-car-cadr-caddr-etc
                        (access apply$-badge (cdr temp) :arity)
                        args))))))
        (t term)))

(comp t) ; e.g., for Allegro CL

(make-event
 `(encapsulate
    nil

; We introduce the relevant evaluator; defevaluator works in a
; very restricted theory (*DEFEVALUATOR-FORM-BASE-THEORY*) and so
; we do not have to worry about disabling all the functions
; involved in the defun of apply$-prim.

    (with-output
      :off (prove event)
      (defevaluator apply$-prim-meta-fn-ev
        apply$-prim-meta-fn-ev-list
        ((apply$-prim fn args)
         ,@(strip-cars *first-order-like-terms-and-out-arities*))))

; To prove correctness we need to force car-cadr-caddr-etc
; to open.

    (local
     (defthm n-car-cadr-caddr-etc-opener
       (implies (natp n)
                (equal (n-car-cadr-caddr-etc (+ 1 n) args)
                       (cons (list 'car args)
                             (n-car-cadr-caddr-etc n (list 'CDR args)))))))

; Next is correctness of the apply$-prim simplifier.

; Some day we may fix the well-formedness-guarantee code so that at the time a
; meta function is applied, we only check the non-primitive functions in the
; supplied arities-alist.  That could be done by checking the list at the time
; we store the meta lemma and removing any function that is a primitive.  We
; know -- or can at least sanely assume -- that the arities of all the system
; primitives won't change.  Then the built-in constant to be checked at
; apply-time would be much reduced -- in fact, to NIL in the case of
; meta-apply$-prim.

; If the above fix is ever made, it would be good to add a well-formedness
; guarantee lemma.

; The original proof of the next lemma didn't involve the proof-builder, but
; has been observed to take about 9 times as long that way.

;   (with-output
;     :off (prove event)
;     (defthm apply$-prim-meta-fn-correct
;       (equal (apply$-prim-meta-fn-ev term alist)
;              (apply$-prim-meta-fn-ev (meta-apply$-prim term) alist))
;       :hints (("Goal" :in-theory (disable acl2::apply$-primp
;                                           acl2::apply$-prim
;                                           (:executable-counterpart break$))))
;       :rule-classes ((:meta :trigger-fns (apply$-prim)))))

    (defthm apply$-prim-meta-fn-correct
      (equal (apply$-prim-meta-fn-ev term alist)
             (apply$-prim-meta-fn-ev (meta-apply$-prim term)
                                     alist))
      :instructions
      ((quiet!
        (:bash ("Goal" :in-theory '((:definition hons-assoc-equal)
                                    (:definition hons-equal)
                                    (:definition hons-get)
                                    (:definition meta-apply$-prim)
                                    (:definition quotep)
                                    (:executable-counterpart car)
                                    (:executable-counterpart cdr)
                                    (:executable-counterpart consp))))
        (:in-theory (union-theories
                     '((:definition apply$-prim)
                       (:definition n-car-cadr-caddr-etc))
                     (union-theories acl2::*expandable-boot-strap-non-rec-fns*
                                     (set-difference-theories
                                      (current-theory :here)
                                      (cons '(:rewrite default-car)
                                            (function-theory :here))))))
        (:repeat :prove)))
      :rule-classes ((:meta :trigger-fns (apply$-prim))))

    (defthm apply$-primp-implies-symbolp
      (implies (apply$-primp fn)
               (symbolp fn))
      :rule-classes :forward-chaining)))

(in-theory (disable apply$-prim apply$-primp))

