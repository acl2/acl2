; Copyright (C) 2018, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Thanks to Eric Smith for the idea leading to this tool.

; TO DO

; - Consider optimization where we maintain a list of clause-lists for theorems
;   in the world, to avoid recomputing those clause-lists repeatedly.

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

(defxdoc defthm<w
  :parents (kestrel-utilities defthm)
  :short "Attempt to prove a theorem directly from previously-proved theorems."
  :long "<p>The macro @('defthm<w') takes the same arguments as @(tsee defthm):
 a name, a form, and (optional) keyword arguments.  It also takes one additional
 keyword argument, @(':prove'), discussed below.</p>

 @({
 General Form:

 (defthm<w name form
   :prove        p ; default :when-hints
   :rule-classes rule-classes
   :instructions instructions
   :hints        hints
   :otf-flg      otf-flg)
 })

 <p>More examples may be found in the @(see community-book),
 @('kestrel/utilities/auto-instance-tests.lisp').</p>

 <p>The name ``@('defthm<w')'' is intended to suggest using the world (w) to do
 the proof: ``Prove this using input from the logical @(see world).''</p>

 @({
 Example Form:

 ; Prove car-cons by appealing to an already-proved theorem, car-cons:
 (defthm<w my-car-cons
   (equal (first (cons a b)) a))
 })

 <p>The world is searched for previous theorems that, together, trivially imply
 the given form.  If such theorems are found, then a @('defthm') event is
 generated for the given form, with the given keyword arguments except for
 @(':prove') and also excepting @(':hints'): rather, a value for @(':')@(tsee
 hints) is generated that reference those previous theorems and that only allow
 simplification in proofs of the subsequent goals, if any (so for example, not
 destructor elimination or induction).  In this case, the supplied value of
 @(':hints') (if any) is ignored.  Also see @(see previous-subsumer-hints)
 for documentation of the utility that generates the hints.</p>

 <p>The behavior described above takes place with the default value of the
 keyword argument, @(':prove'), which is @(':when-hints').  With this default,
 a call of @('defthm<w') fails when suitable hints fail to be generated.  The
 other two legal values for @(':prove') are @('nil') and @('t').  With
 @(':prove nil'), no proof is attempted: instead, the event @('(value-triple
 h)') is generated, where @('h') is the generated hints; note that @('h') is
 nil when hints fail to be generated.  With @(':prove t'), the proof is
 attempted even when no hints are generated; in that case, if @(':hints') are
 supplied then they are used.</p>

 <p>Note: This utility searches for previous @(tsee defthm) and @(tsee
 defaxiom) @(see events) (including, of course, @('defthm') events generated
 from macros such as @(tsee defrule)).  In particular, it does not search for
 corollaries, termination or @(see guard) theorems, or @(tsee defchoose)
 axioms.</p>")

(defxdoc defthmd<w
  :parents (kestrel-utilities defthm defthm<w)
  :short "Attempt to prove a theorem directly from previously-proved theorems."
  :long "<p>This variant of @(tsee defthm<w) generates a @(tsee defthmd) event
 instead of a @(tsee defthm) event, but otherwise is the same as
 @('defthm<w').  See @(see defthm<w).</p>")

(defxdoc thm<w
  :parents (kestrel-utilities defthm defthm<w)
  :short "Attempt to prove a theorem directly from previously-proved theorems."
  :long "<p>This variant of @(tsee defthm<w) generates a call of @(tsee thm)
 instead of a @(tsee defthm) event, but otherwise is the same as @('defthm<w').
 See @(see defthm<w).</p>")

(defxdoc previous-subsumer-hints
  :parents (kestrel-utilities defthm defthm<w)
  :short "Hints to prove a theorem directly from previously-proved theorems."
  :long "@({
 General Form:
 (previous-subsumer-hints term wrld)
 })

 <p>where @('term') is a translated term (see @(see term)) and @('wrld') is a
 logical @(see world), such as @('(w state)').  See @(see defthm<w) for an
 explanation of what this function returns: in short, it either returns
 @('nil') or suitable @(see hints) for proving @(tsee term).  Here is a log
 that illustrates this function.</p>

 @({
 ACL2 !>(previous-subsumer-hints '(equal (car (cons u v)) u) (w state))
 (:BY CAR-CONS
      :DO-NOT *ALL-BUT-SIMPLIFY*)
 ACL2 !>:trans (and (equal (car (cons u v)) u)
                    (equal (cdr (cons a b)) b))

 (IF (EQUAL (CAR (CONS U V)) U)
     (EQUAL (CDR (CONS A B)) B)
     'NIL)

 => *

 ACL2 !>(previous-subsumer-hints '(IF (EQUAL (CAR (CONS U V)) U)
                                      (EQUAL (CDR (CONS A B)) B)
                                      'NIL)
                                  (w state))
 (:USE ((:INSTANCE CAR-CONS (Y V) (X U))
        (:INSTANCE CDR-CONS (Y B) (X A)))
       :IN-THEORY (THEORY 'MINIMAL-THEORY)
       :DO-NOT *ALL-BUT-SIMPLIFY*)
 ACL2 !>
 })")

(program)

; Profiling shows a bottleneck in which almost all the time is inside
; expand-some-non-rec-fns, whose time is essentially fully consumed by looking
; up formals and definition bodies.  I see now that this is probably because
; the world was not an installed world, but rather, a tail of the installed
; world (as we recurred down that installed world).  But I didn't realize that
; at first, so I wrote a faster version of expand-some-non-rec-fns.  I no
; longer have reason to believe that the speedup is significant, but I might as
; well leave that efficiency improvement here (even if it's minor).  Perhaps
; some day I'll put this efficiency improvement into ACL2.

(defun fns-formals-body-alist (fns wrld)
  (cond ((endp fns) nil)
        (t (let ((def-body (original-def-body (car fns) wrld)))
             (assert$ (and def-body
                           (null (access def-body def-body :hyp))
                           (null (access def-body def-body :recursivep)))
                      (acons (car fns)
                             (cons (access def-body def-body :formals)
                                   (access def-body def-body :concl))
                             (fns-formals-body-alist (cdr fns) wrld)))))))

(make-event
 `(defconst *expandables-alist*
    ',(fns-formals-body-alist *expandable-boot-strap-non-rec-fns* (w state))))

(mutual-recursion

(defun fast-expand-some-non-rec-fns-rec (alist term)

; This definition is based on the ACL2 sources definition of
; expand-some-non-rec-fns, but unlike that function, we return (mv changedp
; answer).

  (cond
   ((variablep term) (mv nil term))
   ((fquotep term) (mv nil term))
   (t
    (mv-let (changedp args)
      (fast-expand-some-non-rec-fns-lst alist (fargs term))
      (let ((triple (assoc-eq (ffn-symb term) alist)))
        (cond (triple
               (mv t (subcor-var (cadr triple) ; formals
                                 args
                                 (cddr triple)))) ; body
              (changedp (mv t (cons-term (ffn-symb term) args)))
              (t (mv nil term))))))))

(defun fast-expand-some-non-rec-fns-lst (alist lst)
  (cond ((null lst) (mv nil nil))
        (t (mv-let (changedp1 x)
             (fast-expand-some-non-rec-fns-rec alist (car lst))
             (mv-let
               (changedp2 rest)
               (fast-expand-some-non-rec-fns-lst alist (cdr lst))
               (cond ((or changedp1 changedp2)
                      (mv t (cons x rest)))
                     (t (mv nil lst))))))))

)

(defun fast-expand-some-non-rec-fns (alist term)
  (mv-let (changedp ans)
    (fast-expand-some-non-rec-fns-rec alist term)
    (declare (ignore changedp))
    ans))

(defun expand-term-to-clause-lst (term)
  (declare (xargs :guard (pseudo-termp term)))
  (clausify
   (fast-expand-some-non-rec-fns *expandables-alist* term)
   nil t nil))

(defun unify-subst-equal-1 (a1 a2)
  (declare (xargs :guard (and (symbol-alistp a1)
                              (symbol-alistp a2))))
  (cond ((endp a1) t)
        (t (let ((pair (assoc-eq (caar a1) a2)))
             (and pair
                  (equal (cdar a1) (cdr pair))
                  (unify-subst-equal-1 (cdr a1) a2))))))

(defun unify-subst-equal (a1 a2)
  (declare (xargs :guard (and (symbol-alistp a1)
                              (symbol-alistp a2))))
  (and (unify-subst-equal-1 a1 a2)
       (unify-subst-equal-1 a2 a1)))

(defun symbol-alist-listp (lst)
  (declare (xargs :guard t))
  (cond ((atom lst) (null lst))
        (t (and (symbol-alistp (car lst))
                (symbol-alist-listp (cdr lst))))))

(defun unify-subst-member (a lst)
    (declare (xargs :guard (and (symbol-alistp a)
                                (symbol-alist-listp lst))))
    (cond ((endp lst) nil)
          ((unify-subst-equal a (car lst)) t)
          (t (unify-subst-member a (cdr lst)))))

(mutual-recursion

; This is a variant of the subsumes!-rec mutual-recursion nest that returns a
; unifying substitution or :fail.

(defun subsumes!-rec-alist (cl1 cl2 alist)
  (cond ((endp cl1) alist)
        ((extra-info-lit-p (car cl1))
         (subsumes!-rec-alist (cdr cl1) cl2 alist))
        ((ffn-symb-p (car cl1) 'EQUAL)
         (cond ((quotep (fargn (car cl1) 1))
                (subsumes!1-equality-with-const-alist (car cl1)
                                                      (fargn (car cl1) 2)
                                                      (fargn (car cl1) 1)
                                                      (cdr cl1) cl2 cl2 alist))
               ((quotep (fargn (car cl1) 2))
                (subsumes!1-equality-with-const-alist (car cl1)
                                                      (fargn (car cl1) 1)
                                                      (fargn (car cl1) 2)
                                                      (cdr cl1) cl2 cl2 alist))
               (t (subsumes!1-alist (car cl1) (cdr cl1) cl2 cl2 alist))))
        (t (subsumes!1-alist (car cl1) (cdr cl1) cl2 cl2 alist))))

(defun subsumes!1-equality-with-const-alist (lit x const1 tl1 tl2 cl2 alist)
  (cond ((endp tl2) :fail)
        ((extra-info-lit-p (car tl2))
         (subsumes!1-equality-with-const-alist lit x const1 tl1 (cdr tl2) cl2
                                               alist))
        ((and (ffn-symb-p (car tl2) 'NOT)
              (ffn-symb-p (fargn (car tl2) 1) 'EQUAL))
         (let ((arg1 (fargn (fargn (car tl2) 1) 1))
               (arg2 (fargn (fargn (car tl2) 1) 2)))
           (cond ((and (quotep arg1)
                       (not (equal arg1 const1)))
                  (mv-let
                    (wonp alist1)
                    (one-way-unify1 x arg2 alist)
                    (let ((alist2 (and wonp ; optimization
                                       (subsumes!-rec-alist tl1 cl2 alist1))))
                      (cond ((or (not wonp)
                                 (eq alist2 :fail))
                             (subsumes!1-equality-with-const-alist
                              lit x const1 tl1 (cdr tl2) cl2 alist))
                            (t alist2)))))
                 ((and (quotep arg2)
                       (not (equal arg2 const1)))
                  (mv-let
                    (wonp alist1)
                    (one-way-unify1 x arg1 alist)
                    (let ((alist2 (and wonp ; optimization
                                       (subsumes!-rec-alist tl1 cl2 alist1))))
                      (cond ((or (not wonp)
                                 (eq alist2 :fail))
                             (subsumes!1-equality-with-const-alist
                              lit x const1 tl1 (cdr tl2) cl2 alist))
                            (t alist2)))))
                 (t (subsumes!1-equality-with-const-alist
                     lit x const1 tl1 (cdr tl2) cl2 alist)))))
        (t (mv-let
             (wonp alist1)
             (one-way-unify1 lit (car tl2) alist)
             (let ((alist2 (and wonp ; optimization
                                (subsumes!-rec-alist tl1 cl2 alist1))))
               (cond ((or (not wonp)
                          (eq alist2 :fail))
                      (subsumes!1-equality-with-const-alist
                       lit x const1 tl1 (cdr tl2) cl2 alist))
                     (t alist2)))))))

(defun subsumes!1-alist (lit tl1 tl2 cl2 alist)
  (cond ((endp tl2) :fail)
        ((extra-info-lit-p (car tl2))
         (subsumes!1-alist lit tl1 (cdr tl2) cl2 alist))
        (t (mv-let
             (wonp alist1)
             (one-way-unify1 lit (car tl2) alist)
             (let ((alist2 (and wonp ; optimization
                                (subsumes!-rec-alist tl1 cl2 alist1))))
               (cond ((or (not wonp)
                          (eq alist2 :fail))
                      (subsumes!1-alist lit tl1 (cdr tl2) cl2 alist))
                     (t alist2)))))))

)

(defun some-member-subsumes-alist (cl-set cl)

; This is a variant of some-member-subsumes that returns a unifying
; substitution or :fail.

  (cond ((endp cl-set) :fail)
        (t (let ((temp (subsumes!-rec-alist (car cl-set) cl nil)))
             (cond
              ((eq temp :fail)
               (some-member-subsumes-alist (cdr cl-set) cl))
              (t temp))))))

(defun clause-set-subsumes-1-alists (cl-set1 cl-set2)

; This is a variant of clause-set-subsumes-1.  We return (mv L cl-set), as
; follows.  L is a list of alists.  Cl-set is a subset of cl-set2 such that for
; every clause C2 in cl-set2 not in cl-set, there is a clause C1 in cl-set1 and
; a substitution s in L such that C1/s trivially implies C2.  Note that if L is
; nil the cl-set is equal to cl-set2.

  (cond
   ((endp cl-set2) (mv nil nil))
   (t
    (let ((alist (some-member-subsumes-alist cl-set1 (car cl-set2))))
      (mv-let (alist-lst cl-set)
        (clause-set-subsumes-1-alists cl-set1 (cdr cl-set2))
        (cond ((eq alist :fail)
               (cond (alist-lst (mv alist-lst (cons (car cl-set2) cl-set)))
                     (t (assert$
                         (equal cl-set (cdr cl-set2)) ; should be eq
                         (mv nil cl-set2)))))
              ((unify-subst-member alist alist-lst)
               (mv alist-lst cl-set))
              (t
               (mv (cons alist alist-lst) cl-set))))))))

(defun clause-set-subsumes-alists (cl-set1 cl-set2)

; This is a variant of clause-set-subsumes that returns a list L of unifying
; substitutions, together with the subset cl-set2 obtained by removing each
; clause cl from it such that an instance of cl by a member of L trivially
; implies cl.

  (cond ((or (equal cl-set1 cl-set2)
             (and cl-set1
                  cl-set2
                  (null (cdr cl-set2))
                  (subsetp-equal (car cl-set1) (car cl-set2))))
         (mv (list nil) nil))
        (t (clause-set-subsumes-1-alists cl-set1 cl-set2))))

(defun alists-to-instances (name alists)
  (declare (xargs :guard (symbol-alist-listp alists)))
  (cond ((endp alists) nil)
        (t (cons `(:instance ,name ,@(alist-to-doublets (car alists)))
                 (alists-to-instances name (cdr alists))))))

(mutual-recursion

(defun all-ffn-symbs-subsetp (term fns)

; This function return nil if term contains any lambdas.

  (cond ((or (variablep term)
             (fquotep term))
         t)
        ((lambda-applicationp term)
         (and (all-ffn-symbs-subsetp (lambda-body (ffn-symb term)) fns)
              (all-ffn-symbs-lst-subsetp (fargs term) fns)))
        ((member-eq (ffn-symb term) fns)
         (all-ffn-symbs-lst-subsetp (fargs term) fns))
        (t nil)))

(defun all-ffn-symbs-lst-subsetp (lst fns)
  (cond ((endp lst) t)
        (t (and (all-ffn-symbs-subsetp (car lst) fns)
                (all-ffn-symbs-lst-subsetp (cdr lst) fns)))))
)

(defun previous-subsumer-hints-1 (term cl-lst fns wrld acc)
  (declare (xargs :guard (and (plist-worldp wrld)
                              (termp term wrld)
                              (term-list-listp cl-lst wrld)
                              (symbol-listp fns)
                              (symbol-alist-listp acc))))
  (cond
   ((endp wrld)

; Acc might be non-nil, but it is incomplete.  !! Should we communicate some
; sort of partial result?

    nil)
   ((eq (cadar wrld) 'theorem)
    (let ((thm (cddar wrld)))
      (cond
       ((not (all-ffn-symbs-subsetp thm fns))
        (previous-subsumer-hints-1 term cl-lst fns (cdr wrld) acc))
       ((one-way-unify-p thm term)
        `(:by ,(caar wrld)))
       (t
        (let* ((cl-lst-old (expand-term-to-clause-lst thm)))
          (mv-let (alists cl-lst)
            (clause-set-subsumes-alists cl-lst-old cl-lst)
            (cond
             ((null cl-lst) ; done!
              (assert$
               (consp alists) ; sanity check
               `(:use
                 (,@(alists-to-instances (caar wrld) alists)
                  ,@acc)
                 :in-theory
                 (theory 'minimal-theory))))
             (t
              (let ((acc (if alists
                             (append (alists-to-instances (caar wrld) alists)
                                     acc)
                           acc)))
                (previous-subsumer-hints-1 term cl-lst fns (cdr wrld)
                                           acc))))))))))
   (t (previous-subsumer-hints-1 term cl-lst fns (cdr wrld) acc))))

(defconst *all-but-simplify*
  (remove1-eq 'simplify *do-not-processes*))

(defun previous-subsumer-hints (term wrld)

; We search wrld looking for a theorem that can be instantiated to produce the
; given term, returning a suitable hint or else nil if the search fails.

; As a first cut, at least, we will just look at 'theorem properties.  This
; will avoid looking at formulas of many rules, avoiding rules generated from
; defuns (both :definition and :type-prescription rules) and avoiding
; corollaries.  But that seems reasonable, at least for now.  Probably
; corollaries are often simple restatements of theorems that wouldn't affect a
; subsumption check.

  (declare (xargs :guard (and (plist-worldp wrld)
                              (termp term wrld))))
  (let ((cl-lst (expand-term-to-clause-lst term)))
    (cond ((null cl-lst) ; term is trivially true
           '(:in-theory
             (theory 'minimal-theory)
             :do-not
             *all-but-simplify*))
          (t (let ((x (previous-subsumer-hints-1 term
                                                 cl-lst
                                                 (all-ffn-symbs term nil)
                                                 wrld
                                                 nil)))
               (and x
                    (append x '(:do-not *all-but-simplify*))))))))

(defun thm<w-fn (name form args rule-classes otf-flg prove event-type ctx
                      state)
  (declare (xargs :stobjs state))
  (er-let* ((term (translate form t t nil ctx (w state) state)))
    (let ((h (previous-subsumer-hints term (w state))))
      (cond
       ((null prove) (value `(value-triple ',h)))
       (h ; prove with hints
        (pprogn
         (io? prove nil state
              (h name ctx)
              (fms "NOTE: Proving ~x0 ~@1.~|"
                   (list (cons #\0 name)
                         (cons #\1
                               (cond
                                ((eq (car h) :by)
                                 (msg ":by ~x0" (cadr h)))
                                ((eq (car h) :use)
                                 (msg "using ~x0" (cadr h)))
                                ((eq (car h) :in-theory)
                                 (msg "by trivial means"))
                                (t (er hard ctx
                                       "Unexpected previous-subsumer, ~x0"
                                       h)))))
                   (proofs-co state) state nil))
         (value `(,event-type
                  ,@(and name (list name))
                  ,form
                  :hints (("Goal" ,@h))
                  ,@(and (not (eq rule-classes :none))
                         (list :rule-classes rule-classes))
                  ,@(and otf-flg
                         (list :otf-flg otf-flg))))))
       ((eq prove t)
        (let ((args (remove-keyword :prove args)))
          (value (cond (name (list* event-type name form args))
                       (t (list* event-type form args))))))
       (t ; prove = :when-hints
        (er soft ctx
            "Failed to find previous theorems to prove ~x0!"
            form))))))

(defmacro defthm<w (name form
                         &rest args
                         &key
                         (rule-classes ':none)
                         instructions hints otf-flg
                         (prove ':when-hints))
  (declare (xargs :guard (member-eq prove '(t nil :when-hints))) ; partial
           (ignore instructions hints))
  `(make-event
    (thm<w-fn ',name ',form ',args ',rule-classes ',otf-flg
              ,prove 'defthm (cons 'defthm<w ',name) state)))

(defmacro defthmd<w (name form
                         &rest args
                         &key
                         (rule-classes ':none)
                         instructions hints otf-flg
                         (prove ':when-hints))
  (declare (xargs :guard (member-eq prove '(t nil :when-hints))) ; partial
           (ignore instructions hints))
  `(make-event
    (thm<w-fn ',name ',form ',args ',rule-classes ',otf-flg
              ,prove 'defthmd (cons 'defthmd<w ',name) state)))

(defmacro thm<w (form
                 &rest args
                 &key
                 instructions hints otf-flg
                 (prove ':when-hints))
  (declare (xargs :guard (member-eq prove '(t nil :when-hints))) ; partial
           (ignore instructions hints))
  `(er-let* ((ctx (value 'thm<w))
             (x (thm<w-fn nil ',form ',args :none ',otf-flg
                          ',prove 'thm ctx state))
             (stobjs-out/replaced-val (trans-eval x ctx state t))
             (replaced-val ; (mv erp val replaced-state)
              (value (cdr stobjs-out/replaced-val))))
     (if (car replaced-val)
         (er soft ctx
             "Failed to prove ~x0 using thm<w."
             ',form)
       (value :success))))
