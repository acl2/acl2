; Copyright (C) 2025, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ZF")

;;; TABLE OF CONTENTS:
;;; Preliminaries
;;; Primitives
;;; Scheme implementations:
;;;   zsub (implementing Comprehension), and
;;;   zfn (implementing Replacement)
;;; Zfc-table
;;; Cartesian product,
;;;   including relevant lemmas about membership in pairs
;;; Apply
;;; Domain, codomain, inverse and some basic lemmas
;;; Omega is an ordinal.
;;; Relational composition
;;; Function composition
;;; fn-equal
;;; The ramified hierarchy V
;;; V-omega contains all ACL2 objects.
;;; More lemmas about V
;;; Map
;;; Miscellaneous lemmas arising in developing other books

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Preliminaries
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun char-listp0 (x)
  (declare (xargs :guard t))
  (if (consp x)
      (and (characterp (car x))
           (char-listp0 (cdr x)))
    (equal x 0)))

(defun make-listp0 (x)
  (declare (xargs :guard t))
  (if (consp x)
      (cons (car x)
            (make-listp0 (cdr x)))
    0))

(defun prefix-symbol (prefix sym)
  (declare (type string prefix)
           (type symbol sym))
  (fix-intern-in-pkg-of-sym
   (concatenate 'string prefix (symbol-name sym))
   sym))

(defun suffix-symbol (suffix sym)
  (declare (type string suffix)
           (type symbol sym))
  (fix-intern-in-pkg-of-sym
   (concatenate 'string (symbol-name sym) suffix)
   sym))

(defun props-to-hyps (lst)
  (declare (xargs :guard (true-listp lst)))
  (pairlis-x2 lst nil))

(defmacro force? (form)

; This macro makes it easy for users to specify which of their :props they want
; forced and which they don't: calls of zfc and anything ending in "$PROP" are
; forced, and others aren't.  So when making an abbreviation, such as
; foldr-prop in foldr.lisp, one generally avoids ending the name with "$PROP"
; since one wants the macro to expand without wrapping force around its call.

  (cond ((and (consp form)
              (symbolp (car form)) ; always true?
              (string-suffixp "$PROP" (symbol-name (car form))))
         `(force ,form))
        ((equal form '(zfc))
         `(force ,form))
        (t form)))

(defun force?-props (lst)
  (declare (xargs :guard (true-listp lst)))
  (pairlis-x1 'force?
              (pairlis-x2 (props-to-hyps lst) nil)))

(defun extend-with-props (form props)
  (declare (xargs :guard (symbol-listp props)))
  (mv-let (hyps concl)
    (case-match form
      (('implies ('and . x) y)
       (mv (and (true-listp x) ; always true; needed for guard proof
                x)
           y))
      (('implies x y)
       (mv (list x) y))
      (& (mv nil form)))
    (list 'implies
          (conjoin-untranslated-terms (append hyps (force?-props props)))
          concl)))

(defun unbound-keys (syms alist)
  (declare (xargs :guard (true-listp syms)))
  (cond ((endp syms) nil)
        ((hons-assoc-equal (car syms) alist) ; avoid assoc guard issue
         (unbound-keys (cdr syms) alist))
        (t (cons (car syms)
                 (unbound-keys (cdr syms) alist)))))

(defun check-props-fn (lst ctx state)

; This function references zfc-table, whose introduction is delayed until later
; below when the necessary infrastructure is available for that.

  (declare (xargs :stobjs state :guard (error1-state-p state)))
  (cond ((not (symbol-listp lst))
         (er soft ctx
             "The :props argument must be a list of symbols, but ~x0 is not."
             lst))
        ((unbound-keys lst (table-alist 'zfc-table (w state)))
         (er soft ctx
             "Every symbol in the :props argument must be a key of the table, ~
              ~x0, to indicate that it is justified by the assumption that we ~
              are working in ACL2/ZFC.  However, ~&1 ~#1~[is~/are~] not such ~
              ~#1~[a key~/keys~]."
             'zfc-table
             (unbound-keys lst (table-alist 'zfc-table (w state)))))
        (t (value nil))))

(defmacro check-props (ctx lst)
  `(make-event
    (er-progn (check-props-fn ',lst ',ctx state)
              (value '(value-triple nil)))
    :on-behalf-of :quiet
    :check-expansion t
    :expansion? (value-triple nil)))

(defun thmz-fn (event)

; Despite the name, this function may be applied to any defthmz, defthmdz, or
; thmz event, to extend its formula's hypotheses with calls of the zero-ary
; functions in its :props argument, default (zfc).

  (declare (xargs :guard (and (true-listp event)
                              (member-eq (car event)
                                         '(thmz defthmz defthmdz)))))
  (mv-let (macro-name name form1 args)
    (cond ((eq (car event) 'thmz)
           (mv 'thm nil (cadr event) (cddr event)))
          (t
           (mv (if (eq (car event) 'defthmz)
                   'defthm
                 'defthmd)
               (cadr event) (caddr event) (cdddr event))))
    (let ((p (position :props args :test 'eq)))
      (mv-let (props props-p args)
        (cond ((null p) (mv '(zfc) nil args))
              (t (mv (nth (1+ p) args)
                     t
                     (append (take p args)
                             (nthcdr (+ 2 p) args)))))
        (let ((ev `(,macro-name ,@(and name (list name))
                                ,(extend-with-props form1

; The check-props call below will guarantee that (symbol-listp props) holds
; before submitting ev.

                                                    (and (symbol-listp props)
                                                         props))
                                ,@args)))
          (cond (props-p `(progn (check-props ,(car event) ,props)
                                 ,ev))
                (t ev)))))))

(defmacro thmz (&whole ev &rest args)
  (declare (ignore args))
  (thmz-fn ev))

(defmacro defthmz (&whole ev &rest args)
  (declare (ignore args))
  (thmz-fn ev))

(defmacro defthmdz (&whole ev &rest args)
  (declare (ignore args))
  (thmz-fn ev))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Primitives
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Here we introduce our formalization of ZFG (ZF plus Global Choice), except
; for the axiom schemes of Comprehension and (our version of) Replacement,
; which come later (see zsub and zfn).

(encapsulate
  (((zfc) => *)        ; See below.
   ((in * *) => *)     ; (in a x) <=> a \in x
   ((pair * *) => *)   ; (pair x y) = {x,y}
   ((min-in *) => *)   ; (min-in x) \in x and (min-in x) does not intersect x
   ((union *) => *)    ; (union x) = union of {a: a \in x}
   ((omega) => *)      ; the set of natural numbers
   ((powerset *) => *) ; (powerset x) is the set of all subsets of x
   )

(local (defun zfc ()

; This predicate will serve as a hypothesis of many axioms and theorems.  Its
; local witness is nil so that the axioms exported here are provable
; (trivially).  A metatheoretic argument, essentially interpreting the ACL2
; primitives and "good" objects into set theory, shows how we can view zfc as
; being true.

         nil))

; The local values are what we imagine our functions returning when (zfc) is
; false.

(local (defun in (x y)
         (declare (ignore x y)
                  (xargs :guard t))
         nil))
(local (defun pair (x y)
         (declare (ignore x y)
                  (xargs :guard t))
         nil))
(local (defun min-in (x)
         (declare (ignore x)
                  (xargs :guard t))
         0))
(local (defun union (x)
         (declare (ignore x)
                  (xargs :guard t))
         nil))
(local (defun omega ()
         (declare (xargs :guard t))
         nil))
(local (defun powerset (x)
         (declare (ignore x)
                  (xargs :guard t))
         nil))

(defthm booleanp-in
  (booleanp (in x y))
  :rule-classes :type-prescription)

(defun-sk subset (x y)
  (forall a (implies (in a x)
                     (in a y))))

; Axiom of Extensionality: Two sets are equal iff they have the same elements.
(defthmdz extensionality
  (implies (and (subset x y)
                (subset y x))
           (equal (equal x y)
                  t)))

; We avoid errors due to guard verification depending on local events.
; This event is local to the surrounding encapsulate.
(set-verify-guards-eagerness 0)

(defun singleton (x) ; {x} = {x,x}
  (pair x x))

(defun union2 (x y) ; x U y = U{x,y}
  (union (pair x y)))

(defthmz min-in-1
; Regularity and global choice, part 1: (min z) is in z if z is non-empty.
  (equal (in (min-in z) z)
         (not (equal z 0))))

(defthmz min-in-2
; Regularity and global choice, part 2: intersection of z and (min z) is
; empty.
  (implies (in a z)
           (not (in a (min-in z)))))

(defthm min-in-0 ; default
  (equal (min-in 0)
         0))

(defthmz in-pair
  (equal (in a (pair x y))
         (or (equal a x)
             (equal a y))))

(defun-sk in-in (a x)
  (exists y (and (in a y)
                 (in y x))))

(defthmz in-union
  (equal (in a (union x))
         (in-in a x)))

(defthmz infinity
  (equal (in n (omega))
         (natp n)))

(defthmz in-powerset
  (equal (in a (powerset x))
         (subset a x)))

; Embedding of ACL2 data types into the set-theoretic universe:

(defthm 0-is-emptyset ; 0 = {}
  (not (in a 0)))

(defthmdz n+1-as-union2 ; n+1 = n U {n}
  (implies (natp n)
           (equal (+ 1 n)
                  (union2 n (singleton n)))))

(defthmdz cons-as-ordered-pair

; This is based on the classic ZF definition of an ordered pair, i.e.,
; <x,y> = {{x},{x,y}}.  Cons is the ordered-pair operation.

  (equal (cons x y)
         (pair (singleton x)
               (pair x y))))

(defun insert (x s) ; {x} U s
  (union2 (singleton x) s))

(defun ztriple (y z) ; {0,y,z}
  (declare (xargs :guard (and (posp y)
                              (not (natp z)))))
  (insert 0 (pair y z)))

(defun negative-int-as-ztriple (x)
  (declare (xargs :guard (and (integerp x)
                              (< x 0))))
  (ztriple 1 (cons (- x) 0)))

(defun integer-as-ztriple (x)
  (declare (xargs :guard (integerp x)))
  (if (< x 0)
      (negative-int-as-ztriple x)
    x))

(defun numerator-as-ztriple (x)
  (declare (xargs :guard (rationalp x)))
  (integer-as-ztriple (numerator x)))

(defun ratio-as-ztriple (x)
  (declare (xargs :guard (and (rationalp x)
                              (not (integerp x)))))
  (ztriple 2 (cons (numerator-as-ztriple x) (denominator x))))

(defun complex-as-ztriple (x)
  (declare (xargs :guard (and (complex-rationalp x)
                              (not (rationalp x)))))
  (ztriple 3 (cons (realpart x) (imagpart x))))

(defun character-as-ztriple (x)
  (declare (xargs :guard (characterp x)))
  (ztriple 4 (cons (char-code x) 0)))

(defun string-as-ztriple (x)
  (declare (xargs :guard (stringp x)))
  (ztriple 5 (cons (make-listp0 (coerce x 'list)) 0)))

(defun symbol-as-ztriple (x)
  (declare (xargs :guard (symbolp x)))
  (ztriple 6 (cons (string-as-ztriple (symbol-package-name x))
                   (string-as-ztriple (symbol-name x)))))

(defthmz negative-int-as-ztriple-identity
  (implies (and (integerp x)
                (< x 0))
           (equal (negative-int-as-ztriple x)
                  x)))

(defthmz integer-as-ztriple-identity
  (implies (integerp x)
           (equal (integer-as-ztriple x)
                  x)))

(defthmz ratio-as-ztriple-identity
  (implies (and (rationalp x)
                (not (integerp x)))
           (equal (ratio-as-ztriple x)
                  x)))

(defthmz complex-as-ztriple-identity
  (implies (and (complex-rationalp x)
                (not (rationalp x)))
           (equal (complex-as-ztriple x)
                  x)))

(defthmz character-as-ztriple-identity
  (implies (characterp x)
           (equal (character-as-ztriple x)
                  x)))

(defthmz string-as-ztriple-identity
  (implies (stringp x)
           (equal (string-as-ztriple x)
                  x)))

(defthmz symbol-as-ztriple-identity
  (implies (symbolp x)
           (equal (symbol-as-ztriple x)
                  x)))
)

(verify-guards union2)
(verify-guards singleton)
(verify-guards subset)
(verify-guards insert)
(verify-guards ztriple)
(verify-guards negative-int-as-ztriple)
(verify-guards integer-as-ztriple)
(verify-guards numerator-as-ztriple)
(verify-guards ratio-as-ztriple)
(verify-guards complex-as-ztriple)
(verify-guards character-as-ztriple)
(verify-guards string-as-ztriple)
(verify-guards symbol-as-ztriple)

(in-theory (disable subset-necc subset in-in))

(defun-sk relation-p (r)
  (declare (xargs :guard t))
  (forall p
    (implies (in p r)
             (consp p)))
  :rewrite :direct)

(defun-sk funp (f)
  (declare (xargs :guard t))
  (forall (p1 p2)
    (non-exec ; for guard verification
     (and (relation-p f)
          (implies (and (in p1 f)
                        (in p2 f)
                        (not (equal p1 p2)))
                   (not (equal (car p1) (car p2)))))))
  :rewrite :direct)

(defthm subset-necc-better-1
  (implies (and (in a x)
                (not (in a y)))
           (not (subset x y)))
  :hints (("Goal" :use subset-necc)))

(defthm subset-necc-better-2
  (implies (and (not (in a y))
                (in a x))
           (not (subset x y)))
  :hints (("Goal" :use subset-necc)))

(defthmz in-union2
  (equal (in a (union2 x y))
         (or (in a x) (in a y)))
  :hints (("Goal" :cases ((in a (union2 x y))))
          (and stable-under-simplificationp
               '(:expand ((in-in a (pair x y)))))))

(in-theory (disable union2))

(defthmz union2-commutative
  (equal (union2 x y)
         (union2 y x))
  :hints (("Goal" :in-theory (enable extensionality subset))))

(defthmz union2-associative
  (equal (union2 (union2 x y) z)
         (union2 x (union2 y z)))
  :hints (("Goal" :in-theory (enable extensionality subset))))

(defthm subset-0
  (subset 0 x)
  :hints (("Goal" :in-theory (enable subset))))

(defthm relation-p-0
  (relation-p 0))

(defthm funp-0
  (funp 0))

(defthm funp-implies-relation-p
  (implies (funp f)
           (relation-p f))
  :rule-classes (:rewrite :forward-chaining))

(in-theory (disable funp relation-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Scheme implementations:
;;;   zsub (implementing Comprehension), and
;;;   zfn (implementing Replacement)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun check-zsub-fn (name args x s u ctx state)
  (declare (xargs :stobjs state :guard (error1-state-p state))
           (ignore s u))
  (cond
   ((not (symbolp name))
    (er soft ctx
        "The first argument of ~x0 must be a symbol, but ~x1 is not."
        'check-zsub name))
   ((not (and (symbol-listp args)
              (no-duplicatesp-eq args)))
    (er soft ctx
        "The second argument of ~x0 must be a duplicates-free list of symbols ~
         but ~x1 is not."
        'check-zsub args))
   ((not (symbolp x))
    (er soft ctx
        "The third argument of ~x0 must be a symbol, but ~x1 is not."
        'check-zsub x))
   ((member-eq x args)
    (er soft ctx
        "The third argument of ~x0 must not be a member of the second ~
         argument, but ~x1 is a member of ~x2."
        'check-zsub x args))
   (t (value nil))))

(defmacro check-zsub (name args x s u)
  `(make-event
    (er-progn (check-zsub-fn ',name ',args ',x ',s ',u 'check-zsub state)
              (value '(value-triple nil)))
    :on-behalf-of :quiet
    :check-expansion t
    :expansion? (value-triple nil)))

(defun zsub-form-and-prop (name args x s u)
  (declare (xargs :guard t))
  (let* ((name$prop (and (symbolp name)
                         (suffix-symbol "$PROP" name)))
         (name$comprehension (and (symbolp name)
                                  (packn (list name '$comprehension)))))
    (mv `(encapsulate
           (((,name$prop) => *)
            ((,name ,@(make-list (len args) :initial-element '*)) => *))
           (check-zsub ,name ,args ,x ,s ,u)
           (local (defun ,name$prop ()
                    nil))
           (local (defun-nx ,name ,args

; We check that all free variables of a are among args, as are all free
; variables of u other than x.  We also check that x does not occur free in a.
; Note that we use defun-nx in case u is not well-formed with respect to
; multiple-value checking.  We take advantage of this use of defun-nx in
; examples involving mv near the end of zify.lisp.

                    (declare (ignorable . ,args))
                    (list (check-vars-not-free (,x) ,s)
                          (let ((,x 0))
                            (declare (ignorable ,x))
                            ,u))))
           (defthm ,name$comprehension
             (implies (force (,name$prop))
                      (equal (in ,x (,name . ,args))
                             (and (in ,x ,s)
                                  ,u)))))
        name$prop)))

(defmacro zsub (name args x s u &key verbose)

; We introduce a set for {x \in s: u}.

; Name is the name of a new function symbol.  X is a variable; s and u are
; untranslated terms; and args is a true list of distinct variables containing
; all the free variables of s and u except not including x.  We want to
; introduce a function f such that:

; x \in (name . args) <=> u & x \in s.

; We require that x not be free in a; otherwise the equivalence above is not as
; intended.  Of course we could in principle replace that prohibition by
; renaming x in s, but that would be awkward since s is an untranslated term.

  (declare (xargs :guard t))
  (mv-let (form prop)
    (zsub-form-and-prop name args x s u)
    (let ((ev `(progn ,form
                      (table zfc-table ',prop '(zsub ,name ,args ,x ,s ,u))
                      (value-triple ',name))))
      (cond (verbose ev)
            (t `(with-output :off (:other-than error) :gag-mode nil
                  ,ev))))))

(defun zfn-form-and-prop (name args x y bound u)
  (declare (xargs :guard ; same guard as for zfn macro; see comment there
                  (and (symbolp name)
                       (symbol-listp args)
                       (symbolp x)
                       (symbolp y)
                       (not (equal x y))
                       (not (member-eq x args))
                       (not (member-eq y args)))))
  (let* ((name$prop (suffix-symbol "$PROP" name))
         (name$funp (packn (list name '$funp)))
         (name$chooses (packn (list name '$chooses)))
         (name$domain-1 (packn (list name '$domain-1)))
         (name$domain-2 (packn (list name '$domain-2))))
    (mv `(encapsulate
           (((,name$prop) => *)
            ((,name ,@(make-list (length args) :initial-element '*)) => *))
           (local (defun ,name$prop ()
                    nil))
           (local (defun ,name ,args

; We check that all free variables of bound are among args, as are all free
; variables of u other than x and y.  We also check that x and y do not occur
; free in bound.

                    (declare (ignorable ,@args))
                    (prog2$ (list (check-vars-not-free (,x ,y) ,bound)
                                  (let ((,x 0) (,y 0))
                                    (declare (ignorable ,x ,y))
                                    ,u))
                            0)))
           (defthm ,name$funp
             (funp (,name ,@args)))
           (defthmz ,name$domain-1
             (implies (force (domain$prop))
                      (subset (domain (,name ,@args))
                              ,bound)))
           (defthm ,name$domain-2
             (implies (and (in ,x ,bound)
                           ,u
                           (force (,name$prop)))
                      (in ,x (domain (,name ,@args)))))
           (defthm ,name$chooses
             (implies (and (equal (apply (,name ,@args) ,x)
                                  ,y)
                           (force (,name$prop)))
                      ,u)))
        name$prop)))

(defmacro zfn (name args x y bound u &key verbose)

; Informal summary:

; Suppose u(x,y) is a term specifying a relation between variables x and y.
; Let D be the set of all x \in bound for which there is some such y.  Then we
; introduce (name . args) to be a function f with domain D such that u(x,y)
; holds for all <x,y> \in f.

; More details:

; This macro is what gives us the Axioms of Collection and Replacement, as it
; introduces a set-theoretic function restricted to a set, which is named bound
; here, without specifying a codomain or range.  (The codomain can then be
; obtained from that function by using the Subset scheme.)

; The idea is that u is a term in x and y, possibly with parameters among args,
; that defines a mapping, potentially multi-valued, from x to y.  We then
; define a set-theoretic function (set of ordered pairs), call it zfn, such
; that for every x in bound, if u(x,y,args) holds for some y then
; u(x,zfn(x),args) holds.  Args should include not only the free variables of u
; besides x and y, but also all free variables of the term, bound.  Neither x
; nor y is allowed to occur free in bound.  (A fancier macro could rename them
; in bound, though it would need make-event since we deal here in untranslated
; terms.)

; Name is to be the name of a new ACL2 function symbol and args is to be its
; list of formals; then what we called zfn above is the application of name to
; args.  X and y are variables; bound and u are untranslated terms; and args is
; a true list of distinct variables containing all the free variables of a and
; of u except not including x or y.  We want to introduce an ACL2 function f,
; such that the following properties hold.  Think of u as being Boolean and as
; having free occurrences of variables x and y, though that isn't necessary
; (one can always conjoin x=x and y=y to u); let zfn = (f . args); and think of
; bound as including the domain of zfn.

; (funp zfn)
; (domain zfn) \subset bound
; ((x \in bound) & u) => x \in (domain zfn)
; (y = zfn(x) => u)

; The final rule just above may be called the $CHOOSES rule, and it's stored as
; an enabled rewrite rule.  So u should have a suitable form for that.

  (declare (xargs :guard

; The guard is not really complete, since name needs to be a new name and x and
; y need to be legal variable names.  But those properties are checked below:
; name is provided to defun, and x and y are let-bound.

                  (and (symbolp name)
                       (symbol-listp args)
                       (symbolp x)
                       (symbolp y)
                       (not (equal x y))
                       (not (member-eq x args))
                       (not (member-eq y args)))))
  (mv-let (form prop)
    (zfn-form-and-prop name args x y bound u)
    (let ((ev `(progn ,form
                      (table zfc-table
                             ',prop
                             '(zfn ,name ,args ,x ,y ,bound ,u))
                      (value-triple ',name))))
      (cond (verbose ev)
            (t `(with-output :off (:other-than error) :gag-mode nil
                  ,ev))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Zfc-table
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun all-keys-present-p1 (keys alist)
  (declare (xargs :guard (symbol-listp keys)))
  (cond ((endp keys) t)
        (t (and (hons-assoc-equal (car keys) alist)
                (all-keys-present-p1 (cdr keys) alist)))))

(defun all-keys-present-p (keys alist)
  (declare (xargs :guard t))
  (and (symbol-listp keys)
       (all-keys-present-p1 keys alist)))

(defun zfc-table-guard (val key world)
  (declare (xargs :mode :program ; because of get-event
                  :guard t))
  (cond
   ((eq val t) (eq key 'zfc))
   ((not (assoc-eq 'zfc (table-alist 'zfc-table world)))
; The key, zfc, must be present before adding other props.  It's not completely
; clear that this is necessary, but since we add that key immediately after
; creating the table, this seems like a harmless check that perhaps supports
; the foundations of zfc integration with ACL2.
    nil)
   (t (case-match val
        (('zsub name args x a u)
         (mv-let (form prop)
           (zsub-form-and-prop name args x a u)
           (and (eq key prop)
                (equal form (get-event name world)))))
        (('zfn name args x y bound u)
         (mv-let (form prop)
           (zfn-form-and-prop name args x y bound u)
           (and (eq key prop)
                (equal form (get-event name world)))))
        (('and . props)
         (let ((ev (get-event key world)))
           (case-match ev
             (('defmacro !key () ('quote ('and . forced-props)))
              (and (equal forced-props (force?-props props))
                   (all-keys-present-p props
                                       (table-alist 'zfc-table world))))
             (& nil))))
        (& nil)))))

(table zfc-table nil nil

; This table stores pairs (prop . just) where prop is a zero-ary predicate that
; holds in the ZFC/ACL2 universe and just is the justification for that claim.
; When prop is zfc, just is t; zfc is essentially built-in to hold.  Otherwise
; just is an expression that is evaluated in the table guard so as to justify
; that claim; see zfc-table-guard.

       :guard (zfc-table-guard val key world))

(table zfc-table 'zfc t)

(defmacro extend-zfc-table (prop &rest props)

; Extend the zfc table by introducing prop as an abbreviation for the forced
; props.

  `(progn (defmacro ,prop ()
            '(and ,@(force?-props props)))
          (table zfc-table
                 ',prop
                 '(and ,@props))))

; Test of zsub
(local
 (encapsulate
   ()
   (local (defstub p (x z) t))
   (local (zsub f1 (a1 z) x1 a1 (p x1 z)))
   (local
    (assert-event
     (er-let* ((val (trans1 '(zsub f1 (a1 z) x1 a1 (p x1 z)))))
       (value (equal
               val
               '(WITH-OUTPUT :OFF (:OTHER-THAN ERROR) :GAG-MODE NIL
                  (PROGN
                   (ENCAPSULATE (((F1$PROP) => *) ((F1 * *) => *))
                     (CHECK-ZSUB F1 (A1 Z) X1 A1 (P X1 Z))
                     (LOCAL (DEFUN F1$PROP NIL NIL))
                     (LOCAL (DEFUN-NX F1 (A1 Z)
                              (DECLARE (IGNORABLE A1 Z))
                              (LIST (CHECK-VARS-NOT-FREE (X1) A1)
                                    (LET ((X1 0))
                                         (DECLARE (IGNORABLE X1))
                                         (P X1 Z)))))
                     (DEFTHM F1$COMPREHENSION
                       (IMPLIES (FORCE (F1$PROP))
                                (EQUAL (IN X1 (F1 A1 Z))
                                       (AND (IN X1 A1) (P X1 Z))))))
                   (TABLE ZFC-TABLE
                          'F1$PROP
                          '(ZSUB F1 (A1 Z) X1 A1 (P X1 Z)))
                   (VALUE-TRIPLE 'F1))))))
     :stobjs-out :auto))))

; A test of zfn comes after introducing domain.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Cartesian product,
;;;   including relevant lemmas about membership in pairs
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun prod-member (p a b)

; (Prod-member p a b) holds when p is a member of the cartesian product a X b.

  (declare (xargs :guard t))
  (and (consp p)
       (in (car p) a)
       (in (cdr p) b)))

; Regarding the choice of s below:
; A X B contains ordered pairs (cons x y) = {{x},{x,y}} where x and y are both
; from A U B, hence {x} and {x,y} are both in (powerset (A U B)).  So (cons x
; y) is a subset of (powerset (A U B)), hence a member of (powerset
; (powerset (A U B))).  So A X B is a subset of (powerset (powerset (A U
; B))).

; The following defines the Cartesian product
; (prod2 a b)
; as:
; {p \in (powerset (powerset (union2 a b))) : (prod-member p a b)}
(zsub prod2 (a b)                        ; name, args
      p                                  ; x
      (powerset (powerset (union2 a b))) ; s (see comment above)
      (prod-member p a b)                ; u
      )

(defthm subset-criterion
  (implies (implies (in (subset-witness x y) x)
                    (in (subset-witness x y) y))
           (subset x y))
  :hints (("Goal" :in-theory (enable subset))))

(defthmz in-cons
  (equal (in x (cons a b))
         (or (equal x (singleton a))
             (equal x (pair a b))))
  :hints (("Goal" :in-theory (enable cons-as-ordered-pair))))

(defthmz in-consp
  (implies (consp p)
           (equal (in x p)
                  (or (equal x (singleton (car p)))
                      (equal x (pair (car p) (cdr p)))))))

; Disabling because we will rarely break the cons abstraction:
(in-theory (disable in-cons in-consp))

(defthmz subset-pair-1
  (implies (subset (pair x y) z)
           (and (in x z) (in y z)))
  :rule-classes nil)

(defthmz subset-pair-2
  (implies (and (in x z) (in y z))
           (subset (pair x y) z))
  :hints (("Goal" :in-theory (enable subset)))
  :rule-classes nil)

(defthmz subset-pair
  (equal (subset (pair x y) z)
         (and (in x z) (in y z)))
  :hints (("Goal" :use (subset-pair-1 subset-pair-2))))

(defthmz in-prod2-lemma
  (implies (prod-member p a b)
           (in p (powerset (powerset (union2 a b)))))
  :hints (("Goal" :in-theory (enable cons-as-ordered-pair subset)))
  :rule-classes nil)

(defthmz in-prod2 ; corollary of prod2$comprehension and in-prod2-lemma
  (equal (in p (prod2 a b))
         (prod-member p a b))
  :props (zfc prod2$prop)
  :hints (("Goal" :use in-prod2-lemma)))

(in-theory (disable prod2$comprehension))

(defthmz relation-p-prod2
  (relation-p (prod2 a b))
  :props (zfc prod2$prop)
  :hints (("Goal" :in-theory (enable relation-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Apply
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; For (apply r x) we choose y such that (cons x y) \in r, if such y exists;
; else, return 0 just to have a well-specified default.

(defchoose apply-base (y) (r x)
  (in (cons x y) r))

(defun apply (r x)
  (declare (xargs :guard t))
  (let ((y (apply-base r x)))
    (if (in (cons x y) r)
        y
      0)))

(defthm apply-rewrite
  (implies (in (cons x y) r)
           (in (cons x (apply r x)) r))
  :hints (("Goal" :use apply-base)))

(defthm apply-default
  (implies (not (in (cons x (apply r x)) r))
           (equal (apply r x) 0)))

(in-theory (disable apply))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Domain, codomain, inverse and some basic lemmas
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Introduce (domain r) = {x \in (union (union r)) : <x,r(x)> \in r.  The
; bounding set is (union (union r)) because the domain of r is a subset of
; (union (union r)).  That's because: If the ordered pair {{x},{x,y}} is in r,
; then {x} \in (union r) so x \in (union (union r)).
(zsub domain (r)        ; name, args
      x                 ; x
      (union (union r)) ; s
      (in (cons x (apply r x))
          r) ; u
      )

; Test of zfn, now that domain has been introduced:
(local
 (encapsulate
   ()
   (local (defstub p (x y z) t))
   (local (zfn f1 (a1 z) x1 y1 a1 (p x1 y1 z)))
   (local
    (assert-event
     (er-let* ((val (trans1 '(zfn f1 (a1 z) x1 y1 a1 (p x1 y1 z)))))
       (value (equal
               val
               '(WITH-OUTPUT :OFF (:OTHER-THAN ERROR) :GAG-MODE NIL
                  (PROGN
                   (ENCAPSULATE (((F1$PROP) => *) ((F1 * *) => *))
                     (LOCAL (DEFUN F1$PROP NIL NIL))
                     (LOCAL (DEFUN F1 (A1 Z)
                              (DECLARE (IGNORABLE A1 Z))
                              (PROG2$
                               (LIST (CHECK-VARS-NOT-FREE (X1 Y1) A1)
                                     (LET ((X1 0) (Y1 0))
                                          (DECLARE (IGNORABLE X1 Y1))
                                          (P X1 Y1 Z)))
                               0)))
                     (DEFTHM F1$FUNP
                       (FUNP (F1 A1 Z)))
                     (DEFTHMZ F1$DOMAIN-1
                       (IMPLIES (FORCE (DOMAIN$PROP))
                                (SUBSET (DOMAIN (F1 A1 Z)) A1)))
                     (DEFTHM F1$DOMAIN-2
                       (IMPLIES (AND (IN X1 A1)
                                     (P X1 Y1 Z)
                                     (FORCE (F1$PROP)))
                                (IN X1 (DOMAIN (F1 A1 Z)))))
                     (DEFTHM F1$CHOOSES
                       (IMPLIES (AND (EQUAL (APPLY (F1 A1 Z) X1) Y1)
                                     (FORCE (F1$PROP)))
                                (P X1 Y1 Z))))
                   (TABLE ZFC-TABLE
                          'F1$PROP
                          '(ZFN F1 (A1 Z) X1 Y1 A1 (P X1 Y1 Z)))
                   (VALUE-TRIPLE 'F1))))))
     :stobjs-out :auto))))

(defthmz pair-forward
  (and (in x (pair x y))
       (in y (pair x y)))
  :rule-classes ((:forward-chaining :trigger-terms ((pair x y)))))

; We leave the following disabled by default, since will probably be common to
; leave domain around rather than to "expand" it in terms of apply.
(defthmdz in-domain-rewrite
  (equal (in x (domain r))
         (in (cons x (apply r x))
              r))
  :props (zfc domain$prop)
  :hints (("Goal" :in-theory (enable cons-as-ordered-pair))))

(in-theory (disable domain$comprehension)) ; subsumed by in-domain-rewrite

(defthmz domain-0
  (equal (domain 0)
         0)
  :props (zfc domain$prop)
  :hints (("Goal" :in-theory (enable extensionality in-domain-rewrite))))

; To define the inverse of a relation r, first note that the field of r (i.e.,
; the union of the domain and range of r) is (union (union r)).  That's because
; if the ordered pair {{x},{x,y}} is in r, then {x} and {x,y} are in (union r)
; so x and y are in (union (union r)).  Thus, if s is the product of the field
; of r with itself, i.e., s = (prod2 (union (union r)) (union (union r))),
; then:
; (inverse r) = {p \in s : for some x,y, p = (cons x y) and (cons y x) \in r}.
(zsub inverse (r) ; name, args
      p           ; x
      (prod2 (union (union r))
             (union (union r))) ; s
      (and (consp p)
           (in (cons (cdr p) (car p))
               r)) ; u
      )

(defun codomain (r)
  (declare (xargs :guard t))
  (domain (inverse r)))

(defthmz in-inverse
  (equal (in x (inverse r))
         (and (consp x)
              (in (cons (cdr x) (car x))
                  r)))
  :props (zfc prod2$prop inverse$prop)
  :hints (("Goal" :in-theory (enable cons-as-ordered-pair))))

(defthmdz in-inverse-alt ; fewer :props but just one direction
  (implies (in x (inverse r))
           (and (consp x)
                (in (cons (cdr x) (car x))
                    r)))
  :props (inverse$prop))

(defthmz relation-p-inverse
  (relation-p (inverse r))
  :props (inverse$prop)
  :hints (("Goal"
           :in-theory (enable relation-p)
           :use (in-inverse-alt))))

(defthmz in-car-domain
  (implies (and (consp p)
                (in p r))
           (in (car p) (domain r)))
  :props (zfc domain$prop)
  :hints (("Goal" :in-theory (enable in-domain-rewrite))))

(defthmz in-relation-p-implies-consp
  (implies (and (in x r)
                (relation-p r))
           (consp x))
  :rule-classes :forward-chaining)

(defthmz in-car-domain-alt
  (implies (and (in p r)
                (consp p)
                (equal x (car p)))
           (in x (domain r)))
  :props (zfc domain$prop))

(defthmd funp-uniqueness ; follows immediately from funp
  (implies (and (funp f)
                (in p1 f)
                (in p2 f)
                (equal (car p1) (car p2)))
           (equal (equal p1 p2)
                  t)))

(defthmz apply-intro-lemma
  (implies (funp f)
           (implies (in p f)
                    (equal (cdr p) (apply f (car p)))))
  :hints (("Goal"
           :use ((:instance funp-uniqueness
                            (p1 p)
                            (p2 (cons (car p) (apply f (car p))))))))
  :rule-classes nil)

(defthmdz apply-intro

; It's not completely clear whether or not it's best to keep this lemma
; disabled.  Maybe it should be enabled, in spite of potential slowdown due to
; excessive matching, so that we don't mess around with membership in a
; function.

  (implies (funp f)
           (equal (in p f)
                  (and (consp p)
                       (in (car p) (domain f))
                       (equal (cdr p) (apply f (car p))))))
  :props (zfc domain$prop)
  :hints (("Goal" :use (apply-intro-lemma)
           :in-theory (enable in-domain-rewrite))))

(theory-invariant (not (and (active-runep '(:rewrite in-domain-rewrite))
                            (active-runep '(:rewrite in-cons-apply))))
                  :key apply-intro-vs-relation-p-necd
                  :error t)

(defthmz inverse-inverse
  (implies (relation-p r)
           (equal (inverse (inverse r))
                  r))
  :props (zfc prod2$prop inverse$prop)
  :hints (("Goal" :in-theory (enable extensionality subset))))

(defthmz in-codomain-suff
  (implies (and (in p r)
                (consp p)
                (equal y (cdr p)))
           (in y (codomain r)))
  :props (zfc domain$prop prod2$prop inverse$prop)
  :hints (("Goal" :restrict ((in-car-domain-alt
                              ((p (cons (cdr p) (car p)))))))))

; We need the following disable for the proof of lemma in-apply-codomain just
; below.  It seems reasonable to disable it globally, since codomain is
; arguably a more basic notion than inverse.
(in-theory (disable codomain))

(defthmz in-apply-codomain
  (implies (in x (domain r))
           (in (apply r x)
                (codomain r)))
  :props (zfc domain$prop prod2$prop inverse$prop)
  :hints (("Goal" :in-theory (enable in-domain-rewrite))))

(defthmdz apply-default-is-0

; For convenience we pin down apply for x not in the domain, in this variant
; of apply-default.  This may match a lot but it really shouldn't often be
; useful, so we keep the rule disabled.

  (implies (not (in x (domain r)))
           (equal (apply r x)
                  0))
  :props (zfc domain$prop)
  :hints (("Goal" :in-theory (enable in-domain-rewrite))))

; With inverse defined, we can make the following succinct definition of
; injective.

(defun injective-funp (f)
  (declare (xargs :guard t))
  (and (funp f)
       (funp (inverse f))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Omega is an ordinal.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Next we check well-foundedness of omega, which by regularity reduces to the
; property that omega is linearly ordered by membership (in).  We prove this by
; (more or less) reducing it to the property that omega is linearly ordered by
; <, since membership (in) is just < on omega.

(in-theory (disable natp))

(defun natp-induction (n)
  (if (zp n)
      n
    (natp-induction (1- n))))

; Next we prove that membership is less-than on omega.

(encapsulate ()

  (local
   (defthmz in-natp-1-1
     (implies (natp i)
              (in i (1+ i)))
     :hints (("Goal" :in-theory (enable n+1-as-union2)))))

  (local
   (defthmz in-natp-1-2-lemma
     (implies (and (natp i)
                   (natp j)
                   (in i j))
              (in i (1+ j)))
     :hints (("Goal" :in-theory (enable n+1-as-union2)))
     :rule-classes nil))

  (local
   (defthmz in-natp-1-2
     (implies (and (natp i)
                   (natp j)
                   (< i j)
                   (in i (1- j)))
              (in i j))
     :hints (("Goal" :use ((:instance in-natp-1-2-lemma
                                      (j (1- j))))))))

  (local
   (defthmz in-natp-1
     (implies (and (natp i)
                   (natp j))
              (implies (< i j)
                       (in i j)))
     :hints (("Goal" :induct (natp-induction j)))
     :rule-classes nil))


  (defthmz in-natp-2
    (implies (natp j)
             (implies (in i j)
                      (and (natp i)
                           (< i j))))
    :instructions ((:induct (natp-induction j))
                   (:use (:instance n+1-as-union2 (n (1- j))))
                   :prove :prove)
    :rule-classes nil)

  (defthmz in-natp
    (implies (natp j)
             (equal (in i j)
                    (and (natp i)
                         (< i j))))
    :hints (("Goal" :use (in-natp-1 in-natp-2))))

  )

(defun-sk in-is-linear (s)
  (declare (xargs :guard t))
  (forall (x y) (implies (and (in x s)
                              (in y s)
                              (not (equal x y)))
                         (or (in x y)
                             (in y x)))))

(verify-guards in-is-linear)

(defthmz in-is-linear-omega
  (in-is-linear (omega)))

(defun-sk transitive (x)
  (declare (xargs :guard t))
  (forall a (implies (in a x)
                     (subset a x)))
  :rewrite :direct)

(verify-guards transitive)

(defthm in-natp-implies-natp-lemma
  (implies (and (natp x)
                (not (in y x))
                (in y (1+ x))
                (zfc))
           (natp y))
  :hints (("Goal" :in-theory (enable n+1-as-union2)))
  :rule-classes nil)

(defthmz in-natp-implies-natp
  (implies (and (in y x)
                (natp x))
           (natp y))
  :hints (("Goal" :induct (natp-induction x))
          ("Subgoal *1/2" :use ((:instance in-natp-implies-natp-lemma
                                           (x (1- x)))))))

(defthmz transitive-omega
  (transitive (omega))
  :hints (("Goal" :expand ((subset (transitive-witness (omega))
                                   (omega))))))

(defun ordinal-p (x)
  (declare (xargs :guard t))
  (and (in-is-linear x)
       (transitive x)))

(defthmz ordinal-p-omega
  (ordinal-p (omega)))

(in-theory (disable in-natp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Relational composition
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun-sk in-rcompose (p r s)
; p = <r1,s2> where for some z <r1,z) \ in r and <z,s2> \in s.
  (declare (xargs :guard t))
  (exists (p1 p2)
    (and (in p1 r)
         (consp p1)
         (in p2 s)
         (consp p2)
         (equal (cdr p1) (car p2))
         (equal p (cons (car p1) (cdr p2))))))

(zsub rcompose (r s)                  ; name, args
      p                               ; x
      (prod2 (domain r) (codomain s)) ; s
      (in-rcompose p r s)             ; u
      )

(defthmz in-rcompose-rewrite-lemma
  (implies (in-rcompose p r s)
           (in p (prod2 (domain r) (codomain s))))
  :props (zfc prod2$prop inverse$prop domain$prop))

(defthmz in-rcompose-rewrite ; corollary of rcompose$comprehension.
  (equal (in p (rcompose r s))
         (in-rcompose p r s))
  :props (zfc prod2$prop rcompose$prop inverse$prop domain$prop))

(defthmz relation-p-rcompose
  (relation-p (rcompose r s))
  :props (zfc prod2$prop rcompose$prop domain$prop inverse$prop)
  :hints (("Goal" :expand ((relation-p (rcompose r s))))))

; Potentially useful lemmas:

(defthmz apply-car-is-cdr
  (implies (and (funp f)
                (in p f))
           (equal (apply f (car p))
                  (cdr p)))
  :props (zfc domain$prop)
  :hints (("Goal" :use apply-intro)))

(defthmz in-rcompose-for-funp
  (implies (and (funp f)
                (funp g)
                (in p (rcompose g f)))
           (equal p
                  (cons (car p)
                        (apply f (apply g (car p))))))
  :props (zfc prod2$prop rcompose$prop domain$prop inverse$prop)
  :instructions (:bash
                 (:generalize ((car (in-rcompose-witness p g f)) pg)
                              ((mv-nth 1 (in-rcompose-witness p g f))
                               pf))
                 :prove)
  :rule-classes nil)

(defthmz funp-rcompose-lemma
  (implies (and (funp f)
                (funp g))
           (let ((f (rcompose g f)))
             (implies (and (in p1 f)
                           (in p2 f)
                           (not (equal p1 p2)))
                      (not (equal (car p1) (car p2))))))
  :props (zfc prod2$prop rcompose$prop domain$prop inverse$prop)
  :hints (("Goal" :use ((:instance in-rcompose-for-funp
                                   (p p1))
                        (:instance in-rcompose-for-funp
                                   (p p2))))))

(defthmz funp-rcompose
  (implies (and (funp f)
                (funp g))
           (funp (rcompose g f)))
  :props (zfc prod2$prop rcompose$prop domain$prop inverse$prop)
  :hints (("Goal" :expand ((funp (rcompose g f))))))

(in-theory (disable rcompose$comprehension ; subsumed by in-rcompose-rewrite
                    in-rcompose))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Function composition
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The initial definition was (defun compose (f g) (rcompose g f)).  The lemma
; rcompose-is-compose below proves its equivalence to the definition below,
; assuming (subset (codomain g) (domain f)).  But the following definition may
; be better suited to avoiding that assumption in theorems about composition.

(zsub compose (f g) ; name, args
      p             ; x
      (prod2 (domain g) (codomain f))
      (equal (cdr p)
             (apply f (apply g (car p))))
      )

(defthmz relation-p-compose
  (relation-p (compose f g))
  :props (zfc prod2$prop compose$prop)
  :hints (("Goal" :in-theory (enable relation-p))))

(defthmz funp-compose
  (implies (and (force (funp f))
                (force (funp g)))
           (funp (compose f g)))
  :props (zfc prod2$prop compose$prop)
  :hints (("Goal" :expand ((funp (compose f g))))))

(defthmz apply-compose-1
  (implies (in (cons x y) (compose f g))
           (equal (equal y
                         (apply f (apply g x)))
                  t))
  :props (zfc compose$prop)
  :hints (("Goal"
; The following disable is necessary because in-prod2 forces (prod2$prop).
           :in-theory (disable in-prod2)))
  :rule-classes nil)

(defthmz in-codomain
  (implies (not (equal (apply f x) 0))
           (in (apply f x)
               (codomain f)))
  :props (zfc prod2$prop domain$prop inverse$prop)
  :hints (("Goal" :in-theory (enable apply))))

(defthmz apply-compose-2
  (implies (and (in x (domain g))
                (not (in (cons x (apply f (apply g x)))
                         (compose f g))))
           (equal (apply f (apply g x))
                  0))
  :props (zfc prod2$prop compose$prop domain$prop inverse$prop)
  :rule-classes nil)

(defthmz apply-compose

; The hypothesis (in x (domain g)) is necessary.  For consider x not in
; (domain g) when 0 is in (domain f).  Then (apply f (apply g x)) is (apply
; f 0), which might not be 0, but (apply (compose f g) x) is 0.  At one time
; we had a different formalization that did not require that hypothesis, but it
; probably had other issues and anyhow, that hypothesis seems very reasonable.
; We force it so that it doesn't get in the way of applying this rule.

  (implies (and (force (funp f))
                (force (funp g))
                (force (in x (domain g))))
           (equal (apply (compose f g) x)
                  (apply f (apply g x))))
  :props (zfc prod2$prop compose$prop domain$prop inverse$prop)
  :hints (("Goal"
           :use ((:instance apply-compose-1
                            (y (apply (compose f g) x)))
                 apply-compose-2)
           :in-theory (disable compose$comprehension))))

(in-theory (disable (:e codomain)))

(defthmz inverse-0
  (equal (inverse 0) 0)
  :props (zfc prod2$prop inverse$prop)
  :hints (("Goal" :in-theory (enable extensionality))))

(defthmz codomain-0-lemma
  (subset (codomain 0) 0)
  :props (zfc prod2$prop domain$prop inverse$prop)
  :hints (("Goal" :in-theory (enable codomain subset))))

(defthmz codomain-0
  (equal (codomain 0) 0)
  :props (zfc prod2$prop domain$prop inverse$prop)
  :hints (("Goal" :in-theory (enable extensionality))))

(defthmz compose-0-g
  (equal (compose 0 g) 0)
  :props (zfc prod2$prop compose$prop domain$prop inverse$prop)
  :hints (("Goal" :in-theory (enable extensionality))))

(defthmz in-apply-codomain-force
  (implies (force (in x (domain r)))
           (in (apply r x) (codomain r)))
  :props (zfc prod2$prop domain$prop inverse$prop))

(defthmz domain-compose-lemma
  (implies (subset (codomain g) (domain f))
           (subset (domain g)
                   (domain (compose f g))))
  :props (zfc prod2$prop compose$prop domain$prop inverse$prop)
  :hints (("Goal"
           :expand ((subset (domain g)
                            (domain (compose f g))))
           :restrict
           ((in-car-domain-alt
             ((p (cons (subset-witness (domain g)
                                       (domain (compose f g)))
                       (apply f (apply g
                                       (subset-witness
                                        (domain g)
                                        (domain (compose f g)))))))))))))

(defthmz domain-compose
  (implies (and (force (funp f))
                (force (funp g))
                (force (subset (codomain g) (domain f))))
           (equal (domain (compose f g))
                  (domain g)))
  :props (zfc prod2$prop compose$prop domain$prop inverse$prop)
  :hints (("Goal" :in-theory (e/d (extensionality
                                   in-domain-rewrite)
                                  (apply-compose)))))

(defthmz apply-0
  (equal (apply 0 x) 0)
  :props (zfc domain$prop)
  :hints (("Goal" :in-theory (enable apply-default-is-0))))

(defthmz compose-f-0-lemma
  (subset (compose f 0) 0)
  :props (zfc prod2$prop compose$prop domain$prop))

(defthmz compose-f-0
  (equal (compose f 0)
         0)
  :props (zfc prod2$prop compose$prop domain$prop)
  :hints (("Goal" :in-theory (enable extensionality))))

(defthmdz extensionality-rewrite
  (equal (equal x y)
         (and (subset x y)
              (subset y x))))

(encapsulate ()

(local (defthmz rcompose-is-compose-1
         (implies (and (funp f)
                       (funp g))
                  (subset (rcompose f g)
                          (compose g f)))
         :hints (("Goal"
                  :in-theory (enable in-rcompose)
                  :expand ((subset (rcompose f g)
                                   (compose g f)))))
         :props (zfc prod2$prop compose$prop domain$prop inverse$prop rcompose$prop)))

(local (defthmz rcompose-is-compose-2
         (implies (and (funp f)
                       (funp g)
                       (subset (codomain f) (domain g)))
                  (subset (compose g f)
                          (rcompose f g)))
         :hints (("Goal"
                  :in-theory (e/d (apply-intro)
                                  (relation-p-necc))
                  :expand ((subset (compose g f)
                                   (rcompose f g)))
; A restrict hint didn't work because the rewriter alone wasn't sufficient to
; relieve the hyps of in-rcompose-suff -- two of the four subgoals in the
; proof-builder, when applying in-rcompose-suff, got to Goal' during their
; proofs.
                  :use
                  ((:instance
                    in-rcompose-suff
                    (r f)
                    (s g)
                    (p (subset-witness (compose g f) (rcompose f g)))
                    (p1 (cons (car (subset-witness (compose g f)
                                                   (rcompose f g)))
                              (apply f (car (subset-witness (compose g f)
                                                            (rcompose f g))))))
                    (p2 (cons (apply f (car (subset-witness (compose g f)
                                                            (rcompose f g))))
                              (apply g (apply f (car (subset-witness
                                                      (compose g f)
                                                      (rcompose f g)))))))))))
         :props (zfc prod2$prop compose$prop domain$prop inverse$prop
                     rcompose$prop)))

(defthmz rcompose-is-compose
  (implies (and (funp f)
                (funp g)
                (subset (codomain f) (domain g)))
           (equal (rcompose f g)
                  (compose g f)))
  :hints (("Goal" :in-theory (enable extensionality-rewrite)))
  :props (zfc prod2$prop compose$prop domain$prop inverse$prop rcompose$prop))
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; fn-equal
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun-sk fn-equal (f g)
  (declare (xargs :guard t))
  (forall x (and (equal (domain f) (domain g))
                 (implies (in x (domain f))
                          (equal (apply f x) (apply g x))))))

(defthm fn-equal-forward-to-equal-domains
  (implies (fn-equal f g)
           (equal (domain f) (domain g)))
  :rule-classes (:rewrite :forward-chaining))

(in-theory (disable fn-equal))

(defthm fn-equal-commutative-1
  (implies (fn-equal f g)
           (fn-equal g f))
  :hints (("Goal"
           :expand ((fn-equal g f))
           :restrict ((fn-equal-necc ((x (fn-equal-witness g f)))))))
  :rule-classes nil)

(defthm fn-equal-commutative
  (equal (fn-equal f g)
         (fn-equal g f))
  :hints (("Goal" :use (fn-equal-commutative-1
                        (:instance fn-equal-commutative-1 (f g) (g f))))))

(defthmdz fn-equal-implies-in
  (implies (and (in p f)
                (funp f)
                (funp g)
                (fn-equal f g))
           (in p g))
  :props (zfc domain$prop)
  :hints (("Goal" :in-theory (e/d (apply-intro)
                                  (relation-p-necc))
           :restrict ((fn-equal-necc ((x (car p))))))))

(defthmdz fn-equal-implies-subset
  (implies (and (funp f)
                (funp g)
                (fn-equal f g))
           (subset f g))
  :props (zfc domain$prop)
  :hints (("Goal" :in-theory (enable subset fn-equal-implies-in))))

(defthmdz fn-equal-implies-equal
  (implies (and (funp f)
                (funp g)
                (fn-equal f g))
           (equal (equal f g)
                  t))
  :props (zfc domain$prop)
  :hints (("Goal" :in-theory (enable extensionality
                                     fn-equal-implies-subset))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; The ramified hierarchy V
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmz equal-apply
  (implies (and (funp f)
                (force (in x (domain f))))
           (equal (equal (apply f x) y)
                  (in (cons x y) f)))
  :props (zfc domain$prop)
  :hints (("Goal" :in-theory (enable apply-intro))))

(defthmz in-insert
  (equal (in a (insert x s))
         (or (equal a x)
             (in a s))))

(defthmz in-ztriple
  (equal (in a (ztriple y z))
         (or (equal a 0)
             (equal a y)
             (equal a z))))

(defthmz subset-x-union2-x-y
  (subset x (union2 x y))
  :rule-classes ((:forward-chaining :trigger-terms ((union2 x y)))))

(defthmz subset-y-union2-x-y
  (subset y (union2 x y))
  :rule-classes ((:forward-chaining :trigger-terms ((union2 x y)))))

(defthmz subset-preserves-in-1
  (implies (and (in a x)
                (subset x y))
           (in a y)))

(defthmz subset-preserves-in-2
  (implies (and (subset x y)
                (in a x))
           (in a y)))

(defthmz subset-transitivity
  (implies (and (subset x y)
                (subset y z))
           (subset x z))
  :hints (("Goal" :expand ((subset x z)))))

(defthmz subset-union2-1
  (implies (subset (union2 x y) z)
           (subset x z))
  :rule-classes nil)

(defthmz subset-union2-2
  (implies (and (subset x z) (subset y z))
           (subset (union2 x y) z))
  :hints (("Goal" :expand ((subset (union2 x y) z))))
  :rule-classes nil)

(defthmz subset-union2
  (equal (subset (union2 x y) z)
         (and (subset x z) (subset y z)))
  :hints (("Goal" :use (subset-union2-1
                        (:instance subset-union2-1 (x y) (y x))
                        subset-union2-2))))

(defthmz ztriple-disjointness
  (implies (and (posp y1)
                (posp y2)
                (not (equal y1 y2))
                (not (natp z1))
                (not (natp z2)))
           (not (equal (ztriple y1 z1)
                       (ztriple y2 z2))))
  :hints (("Goal" :in-theory (enable extensionality-rewrite))))

(in-theory (disable ztriple))

(defun v-n (n)
  (declare (type (integer 0 *) n))
  (if (zp n)
      0
    (powerset (v-n (1- n)))))

(defthmz transitive-0
  (transitive 0))

(in-theory (disable transitive))

(defthmz powerset-preserves-transitive-lemma
  (implies (and (transitive y)
                (subset x y))
           (subset x (powerset y)))
  :hints (("Goal" :expand ((subset x (powerset y))))))

(defthmz powerset-preserves-transitive
  (implies (transitive x)
           (transitive (powerset x)))
  :hints (("Goal" :expand ((transitive (powerset x))))))

(defthmz transitive-v-n
  (implies (natp n)
           (transitive (v-n n))))

; Our version of the Replacement Scheme gives us:
; (forall x \in (omega)) (exists y) (equal y (v-n x))
; =>
; (exists v) (forall x \in (omega))
;   (let ((y (apply v x)))
;     (equal y (v-n x)))
; The call of zfn just below implements that observation.
; The extra EQUAL call below is to make the $CHOOSES theorem a useful rewrite
; rule.
(zfn v ()                        ; name, args
     x y                         ; x, y
     (omega)                     ; bound for x
     (equal (equal y (v-n x)) t) ; u
     )

(defthmz v-n$domain-lemma
  (subset (omega) (domain (v)))
  :props (zfc v$prop domain$prop)
  :hints (("Goal"
           :expand ((subset (omega) (domain (v))))
           :restrict ((v$domain-2
                       ((y (v-n (subset-witness (omega)
                                                 (domain (v)))))))))))

(defthmz v-n$domain
  (equal (domain (v)) (omega))
  :props (zfc v$prop domain$prop)
  :hints (("Goal" :in-theory (enable extensionality))))

(defun v-omega ()
  (declare (xargs :guard t))
  (union (codomain (v))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; V-omega contains all ACL2 objects.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Next we prove that v-omega contains all ACL2 objects.  This will allow us
; to use zify to realize every unary ACL2 function on ACL2 objects into a set
; of ordered pairs.

; We start by proving v-omega-contains-naturals.

(defthmz v-maps-n-to-v-n
  (implies (natp n)
           (in (cons n (v-n n))
               (v)))
  :props (zfc v$prop domain$prop)
  :hints (("Goal"
           :in-theory (disable v$chooses)
           :use ((:instance v$chooses (x n)
                            (y (apply (v) n)))))))

(defthmz in-posp-implies-subset-n-1
  (implies (and (not (zp n))
                (in x n))
           (subset x (- n 1)))
  :hints (("Goal"
           :in-theory (enable in-natp)
           :expand ((subset x (- n 1))))))

(defthmz subset-n-v-n ; towards proving in-n-vn-n+1
  (implies (natp n)
           (subset n (v-n n)))
  :props (zfc v$prop domain$prop)
  :hints (("Goal"
           :induct t
           :restrict ((subset-transitivity ((y (+ -1 n)))))
           :expand ((subset n (powerset (v-n (+ -1 n))))))))

(defthmz in-n-vn-n+1
  (implies (natp n)
           (in n (v-n (+ 1 n))))
  :props (zfc v$prop domain$prop))

(defthmz v-omega-contains-naturals
  (implies (natp n)
           (in n (v-omega)))
  :props (zfc v$prop domain$prop prod2$prop inverse$prop)
  :hints (("Goal"
           :restrict ((in-codomain-suff
                       ((p (cons (1+ n) (v-n (1+ n))))))
                      (in-in-suff
                       ((y (v-n (1+ n)))))))))

; We now work towards showing that v-omega contains the remaining ACL2
; objects.

(defthmz subset-x-0
  (equal (subset x 0)
         (equal x 0))
  :hints (("Goal" :in-theory (enable extensionality))))

(in-theory (disable (:e v-n))) ; avoid some attempts to call powerset

; The following may avoid an induction below, but isn't necessary (or at least,
; it wasn't when it was developed).
(defthmz in-0-v-n
  (implies (not (zp j))
           (in 0 (v-n j))))

(defthmz subset-v-n-implies-in-larger-vn
  (implies (and (subset x (v-n i))
                (natp i)
                (natp j)
                (< i j))
           (in x (v-n j)))
  :instructions (:induct :prove :prove)) ; :hints (("Goal" :induct t)) failed

(defthmz subset-monotone-wrt-v-n
  (implies (and (natp i)
                (natp j)
                (<= i j))
           (subset (v-n i) (v-n j)))
  :hints (("Goal" :expand ((subset (powerset (v-n (+ -1 i)))
                                   (v-n j))))))

(defthmz v-n-closed-under-pair-1
  (implies (and (natp nx)
                (natp ny)
                (in x (v-n nx))
                (in y (v-n ny))
                (natp k)
                (<= nx k)
                (<= ny k))
           (subset (pair x y) (v-n k)))
  :hints (("Goal" :expand ((subset (pair x y) (v-n k))))))

(defthmz v-n-closed-under-pair
  (implies (and (natp nx)
                (natp ny)
                (in x (v-n nx))
                (in y (v-n ny))
                (natp k)
                (< nx k)
                (< ny k))
           (in (pair x y) (v-n k)))
  :hints (("Goal" :expand ((v-n k)))))

; Here come two potentially useful and harmelss (and related) lemmas about
; membership in (v).

(defthmz in-v-implies-natp-car-1
  (implies (in (cons n obj) (v))
           (natp n))
  :props (zfc v$prop domain$prop)
  :hints (("Goal" :in-theory (e/d (apply-intro)
                                  (equal-apply))
           :use v$domain-1))
  :rule-classes :forward-chaining)

(defthmz in-v-implies-natp-car-2
  (implies (in p (v))
           (and (consp p)
                (natp (car p))))
  :props (zfc v$prop domain$prop)
  :hints (("Goal" :in-theory (e/d (apply-intro)
                                  (equal-apply relation-p-necc))
           :use v$domain-1))
  :rule-classes :forward-chaining)

(defthmz in-implies-subset-union
  (implies (in x s)
           (subset x (union s)))
  :hints (("Goal" :in-theory (enable subset))))

; Our next goal is v-omega-closed-under-pair, which "should" be an easy
; consequence of v-n-closed-under-pair.  But I spent awhile on this with ACL2
; (when I was proving the analogue for cons in place of pair) and may have had
; quite a distance to go.  So here is a hand proof that I can follow.

; Suppose x, y \in (v-omega) = (union (codomain (v))).
; So we may choose sx and sy such that
;   x \in sx \in (codomain (v)) and
;   y \in sy \in (codomain (v)).
; then <nx,sx> \in (v) and <ny,sy>  \in (v) for some natp nx, ny.
; (In fact, expanding codomain, we have:
;   nx = (apply (inverse (v)) sx) and
;   ny = (apply (inverse (v)) sy).
;  That makes a nice lemma, in-codomain-necc.)
; But then sx = v-n(nx) and sy = vn(ny).
; So x \in v-n(nx) and y \in vn(ny).
; Let k = (1+ (max nx ny)).
; By v-n-closed-under-pair, (in (pair x y) (v-n k)).
; Claim: (subset (v-n m) (v-omega)) for all natp m.
; Then by the claim, where m = k, (in (pair x y) (v-omega)).  Q.E.D.

; To prove the claim that (subset (v-n m) (v-omega)) then since (v-omega)
; = (union (codomain (v))), it suffices by in-implies-subset-union to
; prove that (in (v-n m) (codomain (v))), for which it suffices that (in
; (cons m (v-n m)) (v).  But this follows from v-maps-n-to-v-n.

; Let's start with the claim.

(defthmz subset-v-n-v-omega
  (implies (force (natp m))
           (subset (v-n m) (v-omega)))
  :props (zfc v$prop domain$prop prod2$prop inverse$prop)
  :hints (("Goal"
           :restrict ((in-codomain-suff ((p (cons m (v-n m)))))))))

; Now we turn to the proof of v-omega-closed-under-pair.

(defthmz in-codomain-necc
  (implies (in x (codomain f))
           (in (cons (apply (inverse f) x)
                      x)
                f))
  :props (zfc domain$prop prod2$prop inverse$prop)
  :hints (("Goal" :in-theory (e/d (codomain in-domain-rewrite)
                                  (apply-default)))))

(defthmz in-v-omega-implies-in-v-n-lemma
  (implies (in x (v-omega))
           (let* ((sx (in-in-witness x (codomain (v))))
                  (nx (apply (inverse (v)) sx)))
             (in (cons nx sx) (v))))
  :props (zfc v$prop domain$prop prod2$prop inverse$prop)
  :hints (("Goal" :in-theory (enable in-in)))
  :rule-classes nil)

(defthmz in-v-omega-implies-in-v-n-lemma-corollary
  (implies (in x (v-omega))
           (let* ((sx (in-in-witness x (codomain (v))))
                  (nx (apply (inverse (v)) sx)))
             (equal sx (v-n nx))))
  :props (zfc v$prop domain$prop prod2$prop inverse$prop)
  :hints (("Goal" :use in-v-omega-implies-in-v-n-lemma))
  :rule-classes nil)

; A handy abbreviation, defined so that it's clearly a natural number:
(defun v-n-inv (x)
  (let* ((sx (in-in-witness x (codomain (v))))
         (nx (apply (inverse (v)) sx)))
    (nfix nx)))

(defthmz in-v-omega-implies-in-v-n
  (implies (in x (v-omega))
           (in x (v-n (v-n-inv x))))
  :props (zfc v$prop domain$prop prod2$prop inverse$prop)
  :hints (("Goal" :use in-v-omega-implies-in-v-n-lemma-corollary
           :do-not '(preprocess)
           :in-theory (enable in-in)))
  :rule-classes (:rewrite :forward-chaining))

(in-theory (disable v-n-inv v-omega (v-omega)))

(defthmz in-v-n-preserved-by-1+
  (implies (and (natp k)
                (in x (v-n k)))
           (in x (v-n (+ 1 k)))))

(defthmz v-omega-closed-under-pair-lemma
  (implies (and (in x (v-omega))
                (in y (v-omega)))
           (in (pair x y)
               (v-n (1+ (max (v-n-inv x)
                             (v-n-inv y))))))
  :props (zfc v$prop domain$prop prod2$prop inverse$prop)
  :rule-classes nil)

(in-theory (disable v-n))

(defthmz v-omega-closed-under-pair
  (implies (and (in x (v-omega))
                (in y (v-omega)))
           (in (pair x y) (v-omega)))
  :props (zfc v$prop domain$prop prod2$prop inverse$prop)
  :hints (("Goal" :use v-omega-closed-under-pair-lemma)))

(defthmz union-0
  (equal (union 0) 0)
  :hints (("Goal" :in-theory (e/d (in-in extensionality)
                                  (subset-x-0)))))

(defthmz v-n-closed-under-union
  (implies (in x (v-n n))
           (in (union x) (v-n n)))
  :hints (("Goal" :in-theory (enable v-n subset in-in))))

(defthmz v-omega-closed-under-union2-lemma
  (implies (and (in x (v-omega))
                (in y (v-omega)))
           (in (union2 x y)
               (v-n (1+ (max (v-n-inv x)
                             (v-n-inv y))))))
  :props (zfc v$prop domain$prop prod2$prop inverse$prop)
  :hints (("Goal"
           :restrict ((v-n-closed-under-pair
                       ((ny (v-n-inv y)) (nx (v-n-inv x)))))
           :in-theory (enable union2)))
  :rule-classes nil)

(defthmz v-omega-closed-under-union2
  (implies (and (in x (v-omega))
                (in y (v-omega)))
           (in (union2 x y) (v-omega)))
  :props (zfc v$prop domain$prop prod2$prop inverse$prop)
  :hints (("Goal" :use v-omega-closed-under-union2-lemma)))

(defthmz v-omega-closed-under-ztriple
  (implies (and (in x (v-omega))
                (in y (v-omega)))
           (in (ztriple x y) (v-omega)))
  :props (zfc v$prop domain$prop prod2$prop inverse$prop)
  :hints (("Goal" :in-theory (enable ztriple singleton))))

(defthmz v-omega-closed-under-cons
  (implies (and (in x (v-omega))
                (in y (v-omega)))
           (in (cons x y) (v-omega)))
  :props (zfc v$prop domain$prop prod2$prop inverse$prop)
  :hints (("Goal" :in-theory (enable cons-as-ordered-pair))))

(defthmz v-omega-contains-integers-lemma
  (implies (and (integerp x)
                (< x 0))
           (in (negative-int-as-ztriple x) (v-omega)))
  :props (zfc v$prop domain$prop prod2$prop inverse$prop)
  :rule-classes nil)

(defthmz v-omega-contains-integers
  (implies (integerp x)
           (in x (v-omega)))
  :props (zfc v$prop domain$prop prod2$prop inverse$prop)
  :hints (("Goal"
           :use v-omega-contains-integers-lemma
           :cases ((< x 0))
           :in-theory (disable negative-int-as-ztriple))))

(defthmz v-omega-contains-rationals-lemma
  (implies (rationalp x)
           (in (ratio-as-ztriple x) (v-omega)))
  :props (zfc v$prop domain$prop prod2$prop inverse$prop)
  :rule-classes nil)

(defthmz v-omega-contains-rationals
  (implies (rationalp x)
           (in x (v-omega)))
  :props (zfc v$prop domain$prop prod2$prop inverse$prop)
  :hints (("Goal"
           :use v-omega-contains-rationals-lemma
           :cases ((integerp x))
           :in-theory (disable ratio-as-ztriple))))

(defthmz v-omega-contains-complex-rationals-lemma
  (implies (complex-rationalp x)
           (in (complex-as-ztriple x) (v-omega)))
  :props (zfc v$prop domain$prop prod2$prop inverse$prop)
  :hints (("Goal" :in-theory (disable complex-as-ztriple-identity)))
  :rule-classes nil)

(defthmz v-omega-contains-complex-rationals
  (implies (complex-rationalp x)
           (in x (v-omega)))
  :props (zfc v$prop domain$prop prod2$prop inverse$prop)
  :hints (("Goal"
           :use v-omega-contains-complex-rationals-lemma
           :cases ((integerp x))
           :in-theory (disable complex-as-ztriple))))

(defthmz v-omega-contains-characters-lemma
  (implies (characterp x)
           (in (character-as-ztriple x) (v-omega)))
  :props (zfc v$prop domain$prop prod2$prop inverse$prop)
  :rule-classes nil)

(defthmz v-omega-contains-characters
  (implies (characterp x)
           (in x (v-omega)))
  :props (zfc v$prop domain$prop prod2$prop inverse$prop)
  :hints (("Goal"
           :use v-omega-contains-characters-lemma
           :in-theory (disable character-as-ztriple))))

(defthmz v-omega-contains-char-listp0
  (implies (char-listp0 x)
           (in x (v-omega)))
  :props (zfc v$prop domain$prop prod2$prop inverse$prop))

(defthm char-listp0-make-listp0
  (implies (character-listp x)
           (char-listp0 (make-listp0 x))))

(defthmz v-omega-contains-strings-lemma
  (implies (stringp x)
           (in (string-as-ztriple x) (v-omega)))
  :props (zfc v$prop domain$prop prod2$prop inverse$prop)
  :rule-classes nil)

(defthmz v-omega-contains-strings
  (implies (stringp x)
           (in x (v-omega)))
  :props (zfc v$prop domain$prop prod2$prop inverse$prop)
  :hints (("Goal"
           :use v-omega-contains-strings-lemma
           :in-theory (disable string-as-ztriple))))

(in-theory (disable negative-int-as-ztriple-identity
                    ratio-as-ztriple-identity
                    character-as-ztriple-identity
                    string-as-ztriple-identity
                    symbol-as-ztriple-identity))

(defthmz v-omega-contains-symbols-lemma
  (implies (symbolp x)
           (in (symbol-as-ztriple x) (v-omega)))
  :props (zfc v$prop domain$prop prod2$prop inverse$prop)
  :hints (("Goal" :in-theory (enable string-as-ztriple-identity)))
  :rule-classes nil)

(defthmz v-omega-contains-symbols
  (implies (symbolp x)
           (in x (v-omega)))
  :props (zfc v$prop domain$prop prod2$prop inverse$prop)
  :hints (("Goal"
           :use v-omega-contains-symbols-lemma
           :in-theory (e/d (symbol-as-ztriple-identity)
                           (symbol-as-ztriple)))))

(defun acl2p (x)
  (declare (xargs :guard t))
  (cond ((consp x) (and (acl2p (car x))
                        (acl2p (cdr x))))
        (t (not (bad-atom x)))))

(defthmz v-omega-contains-numbers
  (implies (acl2-numberp x)
           (in x (v-omega)))
  :props (zfc v$prop domain$prop prod2$prop inverse$prop)
  :hints (("Goal" :cases ((complex-rationalp x)))))

(defthmz v-omega-contains-acl2p
  (implies (acl2p x)
           (in x (v-omega)))
  :props (zfc v$prop domain$prop prod2$prop inverse$prop)
  :hints (("Goal" :in-theory (enable bad-atom))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Map
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun map (f lst)
  (declare (xargs :guard (true-listp lst)))
  (cond ((endp lst) nil)
        (t (cons (apply f (car lst))
                 (map f (cdr lst))))))

(defthm map-append
  (equal (map f (append x y))
         (append (map f x) (map f y))))

(defun list-to-set (lst)
  (cond ((endp lst) 0)
        (t (insert (car lst)
                   (list-to-set (cdr lst))))))

(defthmz map-compose
  (implies (and (force (funp f))
                (force (funp g))
                (force (subset (list-to-set lst) (domain g))))
           (equal (map (compose f g) lst)
                  (map f (map g lst))))
  :props (zfc domain$prop prod2$prop compose$prop inverse$prop))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Miscellaneous lemmas arising in developing other books
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;
; Lemmas that were initially pulled from some work done in proving that HOL
; objects are all in V_{omega*2}.
;;;;;

; The following uses rule subset-v-n-v-omega in its proof.
(defthmz in-in-v-omega-implies-in-v-omega
  (implies (in-in x (v-omega))
           (in x (v-omega)))
  :props (zfc v$prop domain$prop prod2$prop inverse$prop)
  :hints (("Goal"
           :expand ((in-in x (v-omega)))
           :cases ((in x (v-n (v-n-inv (in-in-witness x (v-omega)))))))))

(defthmz transitive-v-omega-lemma
  (implies (and (in x y)
                (in y (v-omega)))
           (in x (v-omega)))
  :props (zfc v$prop domain$prop prod2$prop inverse$prop))

(defthmz transitive-v-omega
  (transitive (v-omega))
  :props (zfc v$prop domain$prop prod2$prop inverse$prop)
  :hints (("Goal" :in-theory (enable transitive subset))))

(defthmz in-codomain-implies-in-apply-inverse-domain
  (implies (and (in y (codomain r))
                (equal d (domain r)))
           (in (apply (inverse r) y)
                d))
  :props (zfc domain$prop prod2$prop inverse$prop)
  :hints (("Goal"
           :restrict ((in-car-domain-alt
                       ((p (cons (apply (inverse r) y) y))))))))

(defthmz in-powerset-powerset
  (implies (and (in (car x) dom)
                (in (cdr x) ran)
                (subset dom s)
                (subset ran s)
                (force (consp x)))
; X is a typical member of dom x ran, so we may write x = <a,b> = {{a},{a,b}}
; for a \in dom and b \in ran.
           (in x (powerset (powerset s))))
  :hints (("Goal"
           :use ((:instance in-cons
                            (x (subset-witness x (powerset s)))
                            (a (car x))
                            (b (cdr x)))))))

(defthmz subset-prod2-powerset-powerset
  (implies (and (subset dom s)
                (subset ran s))
; Let x = (prod2 dom ran).  Then x a set of ordered pairs <a,b> = {{a},{a,b}}
; where a and b are in dom and ran, respectively.  Both {a} and {a,b} are in
; (powerset s) so <a,b> \in (powerset (powerset s)), so x is a subset of
; (powerset (powerset s)).
           (subset (prod2 dom ran)
                   (powerset (powerset s))))
  :props (zfc prod2$prop)
  :hints (("Goal" :expand ((subset (prod2 dom ran)
                                   (powerset (powerset s)))))))

(defthmz cdr-preserves-in-for-transitive-lemma
  (implies (and (transitive s)
                (in (cons a b) s))
           (in b s))
  :hints (("Goal" :in-theory (enable cons-as-ordered-pair)
           :cases ((in (pair a b) s))))
  :rule-classes nil)

(defthmz cdr-preserves-in-for-transitive
  (implies (and (transitive s)
                (or (in nil s)
                    (consp x))
                (in x s))
           (in (cdr x) s))
  :hints (("Goal" :use ((:instance cdr-preserves-in-for-transitive-lemma
                                   (a (car x))
                                   (b (cdr x)))))))

(defthmz car-preserves-in-for-transitive-lemma
  (implies (and (transitive s)
                (in (cons a b) s))
           (in a s))
  :hints (("Goal" :in-theory (enable cons-as-ordered-pair)
           :cases ((in (pair a b) s))))
  :rule-classes nil)

(defthmz car-preserves-in-for-transitive
  (implies (and (transitive s)
                (or (in nil s)
                    (consp x))
                (in x s))
           (in (car x) s))
  :hints (("Goal" :use ((:instance car-preserves-in-for-transitive-lemma
                                   (a (car x))
                                   (b (cdr x)))))))

(defthmz hons-assoc-equal-preserves-in-for-transitive
  (implies (and (transitive s)
                (in hta s)
                (consp (hons-assoc-equal key hta))
                (in x (cdr (hons-assoc-equal key hta))))
           (in x s)))

(defthmz prod-0
  (and (equal (prod2 0 x) 0)
       (equal (prod2 x 0) 0))
  :props (zfc prod2$prop)
  :hints (("Goal" :in-theory (e/d (subset extensionality-rewrite)
                                  (subset-x-0)))))

(encapsulate ()

(local (defthmz subset-domain-prod2
         (subset (domain (prod2 x y)) x)
         :props (zfc domain$prop prod2$prop)
         :hints (("Goal" :in-theory (enable subset in-domain-rewrite))))
       )

(local (defthmz domain-prod2-lemma
         (implies (not (equal y 0))
                  (subset x (domain (prod2 x y))))
         :hints (("Goal"
                  :in-theory (enable subset)
                  :restrict
                  ((in-car-domain-alt
                    ((p (cons (subset-witness x (domain (prod2 x y)))
                              (min-in y))))))))
         :props (zfc domain$prop prod2$prop)))

(defthmz domain-prod2
  (equal (domain (prod2 x y))
         (if (equal y 0)
             0
           x))
  :props (zfc domain$prop prod2$prop)
  :hints (("Goal" :use ((:instance extensionality
                                   (x (domain (prod2 x y)))
                                   (y x))))))
) ; end encapsulate

; The following, in-codomain-rewrite, was originally developed in support of
; proving iterate-plus in the book iterate.lisp.  But it's needed for the
; encapsulate just below that proves codomain-prod2.
(defthmdz in-codomain-rewrite
  (equal (in x (codomain r))
         (in (cons (apply (inverse r) x) x) r))
  :props (zfc prod2$prop domain$prop inverse$prop)
  :hints (("Goal" :in-theory (enable codomain in-domain-rewrite))))

(encapsulate ()

(local (defthmz subset-codomain-prod2
         (subset (codomain (prod2 x y)) y)
         :props (zfc domain$prop prod2$prop inverse$prop)
         :hints (("Goal" :in-theory (enable subset in-codomain-rewrite))))
       )

(local (defthmz codomain-prod2-lemma
         (implies (not (equal x 0))
                  (subset y (codomain (prod2 x y))))
         :hints
         (("Goal"
           :in-theory (enable subset)
           :restrict
           ((in-codomain-suff
             ((p (cons (min-in x)
                       (subset-witness y (codomain (prod2 x y))))))))))
         :props (zfc domain$prop prod2$prop inverse$prop)))

(defthmz codomain-prod2
  (equal (codomain (prod2 x y))
         (if (equal x 0)
             0
           y))
  :props (zfc domain$prop prod2$prop inverse$prop)
  :hints (("Goal" :use ((:instance extensionality
                                   (x y)
                                   (y (codomain (prod2 x y))))))))
) ; end encapsulate

(defthmz subset-omega-v-omega
; This could probably be local, but it's a nice lemma to keep around.
  (subset (omega) (v-omega))
  :hints (("Goal" :in-theory (enable subset)))
  :props (zfc v$prop inverse$prop prod2$prop domain$prop))

;;;;;
; Lemmas developed in support of proving iterate-plus
; in the book iterate.lisp
;;;;;

; The following lemmas support the proof of compose-associative, but may be
; useful in their own right.

(defthmz subset-codomain-compose

; Here is a hand proof.
; By definition of subset, let x \in (codomain (compose g h)).
; So for some y, <y,x> \in (compose g h).
;   What is y?  Well, let r = (inverse (compose g h)); so
;   x \in (domain r).  So by in-domain-rewrite,
;   (in (cons x (apply r x)) r); let y = (apply r x).
; By compose$comprehension,
;   <y,x> \in (prod2 (domain h) (codomain g))
; So x \in (codomain g).

  (subset (codomain (compose g h))
          (codomain g))
  :props (zfc prod2$prop domain$prop compose$prop inverse$prop)
  :hints (("Goal"
           :in-theory (enable subset compose$comprehension)
           :use (:instance in-codomain-rewrite
                           (x (subset-witness (codomain (compose g h))
                                              (codomain g)))
                           (r (compose g h))))))

(defthmz compose-associative-with-fn-equal
  (implies (and (funp f)
                (funp g)
                (funp h)
                (subset (codomain g) (domain f))
                (subset (codomain h) (domain g)))
           (fn-equal (compose (compose f g) h)
                     (compose f (compose g h))))
  :props (zfc prod2$prop domain$prop compose$prop inverse$prop)
  :hints (("Goal"
           :in-theory (e/d (fn-equal)
                           (fn-equal-implies-in))
           :restrict ((subset-transitivity
                       ((y (codomain g))))))))

(defthmz compose-associative
  (implies (and (force (funp f))
                (force (funp g))
                (force (funp h))
                (force (subset (codomain g) (domain f)))
                (force (subset (codomain h) (domain g))))
           (equal (compose (compose f g) h)
                  (compose f (compose g h))))
  :props (zfc prod2$prop domain$prop compose$prop inverse$prop)
  :hints (("Goal" :use compose-associative-with-fn-equal
           :in-theory (e/d (fn-equal-implies-equal)
                           (compose-associative-with-fn-equal)))))

;;;;;
;;; Other miscellaneous lemmas
;;;;;

(defthmz equal-domain-0
  (implies (force (relation-p r))
           (equal (equal (domain r) 0)
                  (equal r 0)))
  :props (zfc domain$prop)
  :hints (("Goal" :use ((:instance in-car-domain (p (min-in r)))))))

(encapsulate ()

(local (defthmz equal-inverse-0-lemma
         (implies (and (relation-p r)
                       (not (equal r 0)))
                  (let ((p (min-in r)))
                    (in (cons (cdr p) (car p))
                        (inverse r))))
         :props (zfc domain$prop inverse$prop prod2$prop)
         :rule-classes nil))

(defthmz equal-inverse-0
  (implies (force (relation-p r))
           (equal (equal (inverse r) 0)
                  (equal r 0)))
  :props (zfc domain$prop inverse$prop prod2$prop)
  :hints (("Goal"
           :use equal-inverse-0-lemma
           :in-theory (disable in-inverse inverse$comprehension))))
) ; end encapsulate

(defthmz subset-codomain-0
  (implies (force (relation-p r))
           (equal (equal (codomain r) 0)
                  (equal r 0)))
  :props (zfc domain$prop inverse$prop prod2$prop)
  :hints (("Goal" :in-theory (enable codomain))))
