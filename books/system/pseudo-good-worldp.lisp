; Copyright (C) 2013, Regents of the University of Texas
; Written by Matt Kaufmann and J Strother Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Members of the ACL2 community are invited to strengthen the
; predicate pseudo-good-worldp that is defined in this book.  If you
; do so, then please include your name in a standard-form comment in
; the relevant code, like this, and also add your name to the list of
; additional contributors just above this comment.

; Contributed by: Frank N. Stein

; Also, please understand that you are responsible for fixing any
; resulting errors in running "make chk-include-book-worlds" (in
; either the top-level ACL2 directory or, equivalently, in the books/
; subdirectory).  That target checks worlds after including most
; community books (some with ttags are exempted, for example, since
; they put unusual triples in the world).  Note that every ordinary
; regression does one such check by certifying
; books/system/worldp-check.lisp.

(in-package "ACL2")

; -----------------------------------------------------------------

; The files included here were originally part of this file, but they have been
; factored out so that they can be used by other files in the community books
; in a more modular way.

(include-book "std/typed-alists/keyword-to-keyword-value-list-alistp" :dir :system)
(include-book "std/typed-lists/string-or-symbol-listp" :dir :system)
(include-book "pseudo-event-form-listp")
(include-book "pseudo-command-formp")
(include-book "pseudo-event-landmarkp")
(include-book "pseudo-command-landmarkp")
(include-book "pseudo-tests-and-calls-listp")

; -----------------------------------------------------------------

; This book is used by the book worldp-check.lisp to check the concept of a
; ``good world'', as discussed below.  If that check fails, proceed as follows.

;   (include-book "pseudo-good-worldp")
;   (chk-pseudo-good-worldp "pseudo-good-worldp")

; You will typically see an error message of the following form, for some value
; of N:

;   Bad World detected by PSEUDO-GOOD-WORLDP2:  (nth N ...) is an illegal
;   triple.

; In the loop, execute (nth N (w state)), which should evaluate to the
; offending form.  Then you need to figure out why that form causes a failure.
; (There are other error messages, probably much less common.  The context, in
; this case PSEUDO-GOOD-WORLDP2, gives you a function to look at as a starting
; point.)

; -----------------------------------------------------------------

; This file defines the concept of a ``good world''.  But we wrestled with the
; question of how strong it should be.  Ultimately what we define is the
; concept pseudo-good-worldp.  This is a relatively weak approximation of the
; invariants we assume in the ACL2 system code.  (For example, this file checks
; pseudo-termp for some parts of the world where termp is actually assumed, and
; there are unchecked invariants assumed between components stored under
; separate properties, e.g., pseudo-good-worldp does not check that the
; ``equivalence relations'' stored in congruence rules are in fact known
; equivalence relations.)  Failure of the actual world to satisfy these
; unchecked assumptions could easily cause unsoundness or lead to hard errors.
; Pseudo-good-worldp is both a combination of obvious shallow invariants we
; assume plus properties required to do the proofs so far undertaken about
; system code.  It will evolve under the demands of further proofs about system
; functions and is liable to become more restrictive as more system properties.
; Every world "should" satisfy this predicate, though we are aware of worlds
; created using trust tags that fail to do so, in particular using community
; books in directories hacking/ and workshops/2007/dillinger-et-al/code/.  In
; practice those worlds might well be usable, but we should not be surprised
; when pseudo-good-worldp fails for such worlds.

; But in the following discussion we talk about the undefined more generic
; notion ``good-worldp'' and its various possible meanings.

; Good-worldp will be used in theorems about system functions that take the
; world, w, as an argument.  In most of the discussion that follows we pretend
; that all we care about is whether the elements of the world are ``terms''.  In
; truth, we are interested in all sorts of other data structures in the world
; like runes, numes, enabled structures, event indices, arities, formals, etc.
; But the ``term'' question is sufficient to motivate the basic questions.

; Recall that we currently have two senses of being a ``term'', pseudo-termp and
; termp.  The former just checks crude shape and type of each component.  The
; latter takes a world and does a thorough check on arities and the legality of
; various symbols.  Of interest here is that if a ``function symbol'' is obtained
; from a termp of w, then (a) the arity of that function symbol is a natural
; number and (b) every call of that function symbol in any termp of w has that
; number of arguments.

; Let's consider the proof of three different kinds of system properties that
; would involve good-worldp in their formalization: guard verification,
; correctness of theorem proving code, and world-modifying system functions.

; For guard verification, the most shallow notion of ``term'', pseudo-termp, is
; usually sufficient.  There will be a few examples where this is insufficient
; even for guard verification: if all you know about term is that it is a
; pseudo-termp and that it has a top function symbol, then (ffn-symb term)
; might have a non-numeric arity, which would cause a guard violation.  We
; suspect that any system function calling arity will need to know the stronger
; invariant about w.

; For proof of correctness-level properties of system functions, we almost
; certainly need the termp sense of well-formedness.  For example, if two calls
; of the function symbol fn have different numbers of arguments, then
; one-way-unify would not return a substitution that made them the same, even
; though it might report that it did.

; Finally, for some proofs of system-level properties, we need a STILL stronger
; sense of well-formed worlds.  Consider a function that takes a world w and
; rolls us back to an earlier world, w', at some COMMAND-LANDMARK.  We need to
; prove (good-worldp w) --> (good-worldp w').  But now good-world must insure
; that every term in w is a termp with respect to the then-current world.  This
; ``super-strong'' sense of good-worldp uses termp but repeatly resets the
; relevant world to that current at the moment the relevant triple was stored.

; Here we define just one version of good-worldp, pseudo-good-worldp, which is
; designed to be suitable for most guard verification of functions taking world
; as an arg.  Of course, the proof is in the proofs, which will undoubtedly
; turn up ommissions from what is done initially.  Furthermore, our
; anticipation of necessary guard properties is guided by trying to imagine
; that functions alleged to return terms in fact return pseudo-terms.  So our
; initial characterization of properties not directly related to term formation
; is sketchy at best.

; This whole discussion obscures a fact that becomes overwhelmingly obvious
; once you get into the definition of pseudo-good-worldp: there is no end to
; checks one could insist on in the strong sense.  For example, EVENT-LANDMARKs
; include a field that lists the ``names introduced.''  In the weak sense, that
; requirement is formalized by insisting the field is a list of symbols and/or
; strings.  In the strong sense, every element in the list ought to actually be
; a name in w.  Or maybe, in addition, each ought to be a name actually introduced
; within the current event block.  Or maybe, in addition, strings appear only
; if they are package names.  Or maybe, ...

; A much better example is the QUICK-BLOCK-INFO property.  It had better be in
; 1:1 correspondence with the FORMALS; indeed, it need only be found on the
; property list of recursive functions and better be on each recursive
; function.  And it had better accurately reflect some measure controlling the
; recursion.  It's not enough just to be a list of the appropriate symbols --
; as we check here!  The invariants between our various triples are too
; numerous to check until it's time to do proofs requiring them.

; Rather than try to anticipate all such strong interpretations we are going to
; wait until proofs of interest necessitate their identification.

; A minor consideration:  The requirement on some properties is that they are
; Boolean valued.  However, we tend not to store NIL properties and so it is
; highly likely that any property with a BOOLEANP requirement would pass
; if the requirement were replaced by (eq val T).

; -----------------------------------------------------------------
; Converting System Functions to Logic Mode

; Since the functions here will be used in guards, they need to be
; guard-verified.

(logic)
(set-verify-guards-eagerness 2)

; -----------------------------------------------------------------

; We now consider each property in a good world and define a function to
; recognize (in the ``pseudo'' sense) good values.  We start with the property
; GLOBAL-VALUE and enumerate each of the symbols that can have this property
; and what the value must be.

; -----------------------------------------------------------------
; EVENT-INDEX [GLOBAL-VALUE]:

; (event-indexp x w) checks whether x is the legal GLOBAL-VALUE for EVENT-INDEX
; for the world w.

; The appropriate GLOBAL-VALUE for EVENT-INDEX is a cons whose car is some
; natural number n and whose cdr, wlst, is a list of length n+1.  Furthermore,
; the ith element of wlst, is a tail of w and the GLOBAL-VALUE of
; EVENT-LANDMARK in that tail has an access-event-tuple-number that is (* (- n
; i) *event-index-interval*).

; Note that one implication of this is that the global-value of event-landmark
; in w must be a multiple of *event-index-interval*; this follows from the case
; for i=0.


(defun safe-access-event-tuple-number (x)

; This function is like access-event-tuple-number but has a guard of t and
; always returns an integer.  The smallest actual value for
; access-event-tuple-number in a well-formed world is -1.

  (if (consp x)
      (if (integerp (car x))
          (car x)
          (if (consp (car x))
              (if (integerp (caar x))
                  (caar x)
                  -2)
              -2))
      -2))

(defun pseudo-event-indexp (x w)
  (declare (xargs :guard (plist-worldp w)))
  (cond ((consp x)
         (and (equal (car x) (- (len (cdr x)) 1))
              (equal (safe-access-event-tuple-number
                      (fgetprop 'event-landmark 'global-value nil w))
                     (* (car x) *event-index-interval*))

; Having both the (equal (car x) ...) and the (equal ... (* (car x) ...))
; above bothered me for a long time, because I thought of them as redundant
; ways to say what (car x) is.  But they're not redundant.  One relates (car x)
; to the length of (cdr x) and the other is a statement about where in the
; world w event indices appear.

              (consp (cdr x))
              (equal (cadr x) w)
              (or (consp (fgetprop 'event-index 'global-value nil w))
                  (null (fgetprop 'event-index 'global-value nil w)))
              (equal (cddr x)
                     (cdr (fgetprop 'event-index 'global-value nil w)))))
        (t (and (null x)
                (null (fgetprop 'event-index 'global-value nil w))))))

; -----------------------------------------------------------------
; COMMAND-INDEX [GLOBAL-VALUE]:

; See the handling of event-index above.

(defun safe-access-command-tuple-number (x)

; Warning: Keep this in sync with (defrec command-tuple ...) in the ACL2
; sources.

; The smallest actual value for access-command-tuple-number in a well-formed
; world is -2.

  (if (consp x)
      (if (integerp (car x))
          (car x)
        -2)
    -2))

(defun pseudo-command-indexp (x w)
  (declare (xargs :guard (plist-worldp w)))
  (cond ((consp x)
         (and (equal (car x) (- (len (cdr x)) 1))
              (equal (safe-access-command-tuple-number
                      (fgetprop 'command-landmark 'global-value nil w))
                     (* (car x) *event-index-interval*))
              (consp (cdr x))
              (equal (cadr x) w)
              (or (consp (fgetprop 'command-index 'global-value nil w))
                  (null (fgetprop 'command-index 'global-value nil w)))
              (equal (cddr x)
                     (cdr (fgetprop 'command-index 'global-value nil w)))))
        (t (and (null x)
                (null (fgetprop 'command-index 'global-value nil w))))))

; -----------------------------------------------------------------

; EVENT-LANDMARK [GLOBAL-VALUE]

(defun pseudo-function-symbolp (fn n)

; The n above is just a placeholder to allow me to record the requirements on
; the arity of fn.  These requirements cannot be checked in pseudo situation
; because there is no world.  But my convention is that n = nil means no
; requirement stated and otherwise n is a natural that must be the arity of fn.

  (declare (ignore n))
  (symbolp fn))

(defun pseudo-function-symbol-listp (lst n)
  (if (atom lst)
      (null lst)
      (and (pseudo-function-symbolp (car lst) n)
           (pseudo-function-symbol-listp (cdr lst) n))))

; See pseudo-event-landmarkp in pseudo-event-landmarkp.lisp.
; That function was originally here in this file.

; -----------------------------------------------------------------

; COMMAND-LANDMARK [GLOBAL-VALUE]

; See pseudo-command-landmarkp in pseudo-command-landmarkp.lisp.
; That function was originally here in this file.

; -----------------------------------------------------------------
; KNOWN-PACKAGE-ALIST [GLOBAL-VALUE]

; known-package-alistp is already defined.

; -----------------------------------------------------------------
; WELL-FOUNDED-RELATION-ALIST [GLOBAL-VALUE]

(defun pseudo-runep (rune)
  (and (consp rune)
       (keywordp (car rune))
       (consp (cdr rune))
       (symbolp (cadr rune))
       (or (null (cddr rune))
           (natp (cddr rune)))))

(defun pseudo-well-founded-relation-alistp (val)
  (cond ((atom val) (null val))
        ((and (consp (car val))
              (consp (cdr (car val))))
         (let ((rel (car (car val)))
               (m   (cadr (car val)))
               (rune (cddr (car val))))
           (and (pseudo-function-symbolp rel 2)
                (pseudo-function-symbolp m 1)
                (pseudo-runep rune)
                (pseudo-well-founded-relation-alistp (cdr val)))))
        (t nil)))

; -----------------------------------------------------------------
; BUILT-IN-CLAUSES [GLOBAL-VALUE]

; Built-in-clauses is an alist associating function symbols with lists of
; built-in-clause records.

; (defrec built-in-clause ((nume . all-fnnames) clause . rune) t)

(defun pseudo-numep (n)

; A nume is a natural number corresponding to a rune.  In fact, in
; enabled-numep, we additionally assume that numes are fixnums.  In fact, there
; are probably very many fewer numes than fixnums, since there can only be as
; many as there are runes (a function of the world).

  (natp n))

(defun pseudo-built-in-clause-recordp (x)
  (case-match x
    (((nume . all-fnnames) clause . rune)
     (and (or (null nume) (pseudo-numep nume))
          (pseudo-function-symbol-listp all-fnnames nil)
          (pseudo-term-listp clause)
          (pseudo-runep rune)))
    (& nil)))

(defun pseudo-built-in-clause-record-listp (x)
  (if (atom x)
      (null x)
      (and (pseudo-built-in-clause-recordp (car x))
           (pseudo-built-in-clause-record-listp (cdr x)))))

(defun pseudo-built-in-clausesp (x)
  (if (atom x)
      (null x)
      (and (consp (car x))
           (pseudo-function-symbolp (car (car x)) nil)
           (pseudo-built-in-clause-record-listp (cdr (car x)))
           (pseudo-built-in-clausesp (cdr x)))))

; -----------------------------------------------------------------
; ATTACH-NIL-LST [GLOBAL-VALUE]

; Attach-nil-lst is a list of function symbols.

(defun pseudo-attach-nil-lst (lst)
  (pseudo-function-symbol-listp lst nil))

; -----------------------------------------------------------------
; ATTACHMENT-RECORDS [GLOBAL-VALUE]

; Attachment-records is a list of attachment records:

; (defrec attachment ((fns . g) . (components . f)) nil)

(defun attachment-components-pathp (path)

; See the Essay on Merging Defattach Records or comments in
; defattach-merge-into-component.

  (cond ((atom path) (null path))
        (t (and (pseudo-function-symbolp (car path) nil)
                (attachment-components-pathp (cdr path))))))

(defun attachment-component-p (c)
  (case-match c
    (('ATTACHMENT-COMPONENT
      (ext-anc . ord-anc) . path)
     (and (pseudo-function-symbol-listp ext-anc nil)
          (pseudo-function-symbol-listp ord-anc nil)
          (attachment-components-pathp path)))))

(defun attachment-components-p (components)
  (cond ((atom components) (null components))
        (t (and (attachment-component-p (car components))
                (attachment-components-p (cdr components))))))

(defun pseudo-attachment-recordp (x)
  (case-match x
    (('ATTACHMENT
      (g . ext-succ) . (components . pairs))
     (and (pseudo-function-symbol-listp ext-succ nil)
          (pseudo-function-symbolp g nil)
          (attachment-components-p components)
          (symbol-alistp pairs)
          (r-symbol-alistp pairs)))
    (& nil)))

(defun pseudo-attachment-recordsp (x)
  (cond ((atom x) (null x))
        (t (and (pseudo-attachment-recordp (car x))
                (pseudo-attachment-recordsp (cdr x))))))

; -----------------------------------------------------------------
; ATTACHMENTS-AT-GROUND-ZERO [GLOBAL-VALUE]

(defun pseudo-attachments-at-ground-zerop (x)
  (cond ((atom x) (null x))
        (t (and (consp (car x))
                (pseudo-function-symbolp (caar x) nil)
                (pseudo-function-symbolp (cdar x) nil)
                (pseudo-attachments-at-ground-zerop (cdr x))))))

; -----------------------------------------------------------------
; HALF-LENGTH-BUILT-IN-CLAUSES [GLOBAL-VALUE]

; This is always a number set to (floor n 2), where n is the length of built-in-clauses.

(defun pseudo-half-length-built-in-clausesp (n)
  (natp n))

; -----------------------------------------------------------------
; TYPE-SET-INVERTER-RULES [GLOBAL-VALUE]

; This is a list of records:
; (defrec type-set-inverter-rule ((nume . ts) terms . rune) nil)

(defun type-setp (n)
  (and (integerp n)
       (<= *min-type-set* n)
       (<= n *max-type-set*)))

(defun pseudo-type-set-inverter-rule-recordp (x)
  (case-match x
    (('type-set-inverter-rule (nume . ts) terms . rune)
     (and (or (null nume) (pseudo-numep nume))
          (type-setp ts)
          (pseudo-term-listp terms)
          (pseudo-runep rune)))
    (& nil)))

(defun pseudo-type-set-inverter-rulesp (val)
  (if (atom val)
      (null val)
      (and (pseudo-type-set-inverter-rule-recordp (car val))
           (pseudo-type-set-inverter-rulesp (cdr val)))))

; -----------------------------------------------------------------
; GLOBAL-ARITHMETIC-ENABLED-STRUCTURE [GLOBAL-VALUE]

; The global arithmetic enabled structure is just an enabled structure whose
; name happens to be ARITHMETIC-ENABLED-ARRAY-n, where n is the suffix below.
; However, we don't check that the global arithmetic enabled structure is that
; particular instance of an enabled structure; instead we just confirm that it
; has the shape of an enabled structure.

(defun pseudo-rune-array1p (a)

  (declare (xargs :guard (alistp a)))

; We know that a is an array1p (for some name).  We check that every value in
; the array a is a pseudo-runep.

  (cond ((atom a) (null a))
        ((eq (car (car a)) :HEADER)
         (pseudo-rune-array1p (cdr a)))
        (t (and (pseudo-runep (cdr (car a)))
                (pseudo-rune-array1p (cdr a))))))

(defun pseudo-enabled-structure-recordp (val)

; This function is almost the same as enabled-structurep, which is not defined
; in :logic-mode.  (In fact, it is defined only in raw lisp, in
; interface-raw.lisp, and so cannot be moved into the logic.)  The conditions
; below have been strengthened only slightly.  See the defrec for
; enabled-structure.

  (case-match val
    (((index-of-last-enabling . theory-array)
      (array-name . array-length)
      array-name-root . array-name-suffix)
     (and (integerp index-of-last-enabling)
          (<= -1 index-of-last-enabling)
          (symbolp array-name)
          (array1p array-name theory-array)
          (pseudo-rune-array1p theory-array)
          (natp array-length)
          (character-listp array-name-root)
          (natp array-name-suffix)))
    (& nil)))

(defun pseudo-global-arithmetic-enabled-structurep (val)
  (pseudo-enabled-structure-recordp val))

; -----------------------------------------------------------------
; OPERATING-SYSTEM [GLOBAL-VALUE]

(defun operating-systemp (val)
  (member-eq val '(:unix :apple :mswindows)))

; -----------------------------------------------------------------
; EVENT-NUMBER-BASELINE [GLOBAL-VALUE]

(defun event-number-baselinep (val)
  (natp val))

; -----------------------------------------------------------------
; COMMAND-NUMBER-BASELINE-INFO [GLOBAL-VALUE]

(defun command-number-baseline-infop (val)
  (case-match val
    (('command-number-baseline-info current permament-p . original)
     (and (natp current)
          (booleanp permament-p)
          (natp original)))
    (& nil)))

; -----------------------------------------------------------------
; EMBEDDED-EVENT-LST [GLOBAL-VALUE]

(defun pseudo-arglistp (x)
  (symbol-listp x))

(defun pseudo-internal-signaturep (insig)
  (case-match insig
    ((fn formals stobjs-in stobjs-out)
     (and (pseudo-function-symbolp fn nil)   ; should be a fn name
          (pseudo-arglistp formals)          ; should be distinct vars
          (symbol-listp stobjs-in)           ; both stobjs-in and -out should be
          (symbol-listp stobjs-out)          ;       lists of stobj names or nil,
          (equal (len formals) (len stobjs-in)))) ;  consistent with formals
    (& nil)))

(defun pseudo-internal-signature-listp (x)
  (if (atom x)
      (null x)
      (and (pseudo-internal-signaturep (car x))
           (pseudo-internal-signature-listp (cdr x)))))

(defun pseudo-embedded-event-lst-entryp (ee-entry)

; From process-embedded-events we see:

; The shape of an ee-entry is entirely up to the callers and the customers of
; the embedded-event-lst, with three exceptions:
; (a) the ee-entry must always be a consp;
; (b) if the car of the ee-entry is 'encapsulate then the cadr is the internal
;     form signatures of the functions being constrained; and
; (c) if the car of the ee-entry is 'include-book then the cadr is the
;     full-book-name.

  (and (consp ee-entry)
       (if (eq (car ee-entry) 'encapsulate)
           (and (consp (cdr ee-entry))
                (pseudo-internal-signature-listp (cadr ee-entry)))
           t)
       (if (eq (car ee-entry) 'include-book)
           (and (consp (cdr ee-entry))
                (stringp (cadr ee-entry)))
           t)))


(defun pseudo-embedded-event-lstp (val)
  (if (atom val)
      (null val)
      (and (pseudo-embedded-event-lst-entryp (car val))
           (pseudo-embedded-event-lstp (cdr val)))))

; -----------------------------------------------------------------
; CLTL-COMMAND [GLOBAL-VALUE]
; TOP-LEVEL-CLTL-COMMAND-STACK [GLOBAL-VALUE]

; The value of CLTL-COMMAND is a raw lisp form to execute, e.g., (defconst name
; val).  But when the car of the form is DEFUNS the general form is (DEFUNS
; defun-mode-flg ignorep def1 def2 ...) and the raw lisp form to execute is
; actually (DEFUNS def1' def2' ...), where the defi' are computed from the defi
; depending on defun-mode-flg and ignorep.  Defun-Mode-flg is either nil
; (meaning the function is :non-executable or the parent event is an
; encapsulate which is trying to define the executable counterparts of the
; constrained functions; either way, the effective defun-mode is :logic) or a
; defun-mode (meaning the parent event is a DEFUNS and the defun-mode is the
; defun-mode of the defined functions).  Ignorep is 'reclassifying, '(defstobj
; . stobj-name), or nil.

(defun pseudo-cltl-commandp (val)
  (case-match val
    (('DEFUNS defun-mode ignorep . defs)
     (and (or (null defun-mode)
              (eq defun-mode :program)
              (eq defun-mode :logic))
          (or (eq ignorep 'reclassifying)
              (and (consp ignorep)
                   (eq (car ignorep) 'defstobj)
                   (pseudo-function-symbolp (cdr ignorep) nil)) ; really must be stobj-name
              (null ignorep))

; We could do better than (true-listp defs) below.  For example
; (pseudo-event-form-listp defs) should be true, as it is defined in late
; December 2019 (but perhaps it won't be true in the future -- after all, defs
; is a list of CDRs of events).  Much more should also be true, but in the
; "pseudo" spirit we keep this simple.

          (true-listp defs)))
    (&

; We could probably insist that val be a true-listp in this case, but that is
; such a weak check that given our lack of certainty, we don't bother.

     t)))

; The value of TOP-LEVEL-CLTL-COMMAND-STACK is a list of CLTL-COMMAND objects.

(defun pseudo-cltl-command-listp (val)
  (cond ((atom val)
         (null val))
        (t (and (pseudo-cltl-commandp (car val))
                (pseudo-cltl-command-listp (cdr val))))))

; -----------------------------------------------------------------
; INCLUDE-BOOK-ALIST [GLOBAL-VALUE]

; The include-book-alist contains elements of the
; general form         example value

; (full-book-name     ; "/usr/home/moore/project/arith.lisp"
;  user-book-name     ; "project/arith.lisp"
;  familiar-name      ; "arith"
;  cert-annotations   ; ((:SKIPPED-PROOFSP . sp)
;                        (:AXIOMSP . axp)
;                        (:TTAGS . ttag-alistp))
;  . ev-lst-chk-sum)  ; 12345678

; Note:  cert-annotations might be NIL after certify-book.  See below.

; Cert-annotationsp is defined in the source code and uses ttag-alistp.
; We need to admit guard-verified versions of each.

(verify-termination sysfile-p) ; and guards

(verify-termination sysfile-or-string-listp) ; and guards

(verify-termination ttag-alistp) ; and guards

(verify-termination cert-annotationsp) ; and guards

(defun pseudo-include-book-alist-entryp (entry)
  (case-match entry
    ((full-name user-name familiar-name cert-annotations . chk-sum)
     (and (stringp full-name)
          (stringp user-name)
          (stringp familiar-name)

; We permit the cert-annotations component of an include-book-alist entry to be
; nil even though that never arises in a world created by embedded event forms.
; It does arise in the world created by certify-book: just after a book has
; been certified, its include-book-alist entry has a cert-annotations component
; of nil.  If one undoes the certify-book and includes the newly certify book,
; the cert-annotations component of its include-book-alist entry is set
; properly.  We don't think of certify-book as producing world from which one
; can continue, EXCEPT by undoing.  But to know undoing is ok, we need some
; invariants on the world produced by certify-book and pseudo-good-worldp
; is the natural predicate.

          (or (null cert-annotations)
              (cert-annotationsp cert-annotations t))
          (case-match chk-sum
            (((':BOOK-LENGTH . book-length)
              (':BOOK-WRITE-DATE . book-write-date))
             (and (natp book-length)
                  (natp book-write-date)))
            (& (or (integerp chk-sum)
                   (eq chk-sum nil))))))
    (& nil)))

(defun pseudo-include-book-alist-entry-listp (x local-markers-allowedp)
  (cond
   ((atom x) (equal x nil))
   ((and local-markers-allowedp
         (consp (car x))
         (eq (car (car x)) 'local)
         (consp (cdr (car x)))
         (equal (cddr (car x)) nil))
    (and (pseudo-include-book-alist-entryp (cadr (car x)))
         (pseudo-include-book-alist-entry-listp
          (cdr x)
          local-markers-allowedp)))
   (t (and (pseudo-include-book-alist-entryp (car x))
           (pseudo-include-book-alist-entry-listp
            (cdr x)
            local-markers-allowedp)))))

(defun pseudo-include-book-alistp (val)
  (pseudo-include-book-alist-entry-listp val t))    ; note LOCALs are allowed.  Right?

; -----------------------------------------------------------------
; INCLUDE-BOOK-ALIST-ALL [GLOBAL-VALUE]

; This entry has the same shape as include-book-alist.

(defun pseudo-include-book-alist-allp (val)
  (pseudo-include-book-alistp val))

; -----------------------------------------------------------------
; PCERT-BOOKS [GLOBAL-VALUE]

; The pcert-books is a list of full book names.

(defun pseudo-pcert-booksp (val)
  (string-listp val))

; -----------------------------------------------------------------
; INCLUDE-BOOK-PATH [GLOBAL-VALUE]

; The include-book-path is a list of full book names.

(defun pseudo-include-book-pathp (val)
  (string-listp val))

; -----------------------------------------------------------------
; CERTIFICATION-TUPLE [GLOBAL-VALUE]

; A certification-tuple is either nil (the initial value) or one of the
; elements found in an include-book-alist.

(defun certification-tuplep (val)
  (or (null val)
      (pseudo-include-book-alist-entryp val)))

; -----------------------------------------------------------------
; DOCUMENTATION-ALIST [GLOBAL-VALUE]

(defun documentation-tuplep (x)
  (case-match x
    ((topic section citations doc-string)
     (and (or (symbolp topic)
              (stringp topic))
          (or (symbolp section)
              (stringp section))
          (string-or-symbol-listp citations)
          (stringp doc-string)))
    (& nil)))


(defun documentation-alistp (val)
  (if (atom val)
      (eq val nil)
      (and (documentation-tuplep (car val))
           (documentation-alistp (cdr val)))))

; -----------------------------------------------------------------
; PROVED-FUNCTIONAL-INSTANCES-ALIST [GLOBAL-VALUE]

; The following code will convert termp as a :logic mode function:

(defun pseudo-functional-substitution-pairp (x)
; All of the nils in the pseudo-function-symbolp calls below should be
; appropriate arity, e.g., fn should be same arity as fn1, but of course
; you'd have to check that both are legal symbols before you can compare the
; arities.
  (case-match x
    ((fn . ('lambda vars body))
     (and (pseudo-function-symbolp fn nil)
          (pseudo-arglistp vars)
          (pseudo-termp body)))
    ((fn . fn1)
     (and (pseudo-function-symbolp fn nil)
          (pseudo-function-symbolp fn1 nil)))
    (& nil)))

(defun pseudo-functional-substitutionp (x)
  (cond ((atom x) (null x))
        (t (and (pseudo-functional-substitution-pairp (car x))
                (pseudo-functional-substitutionp (cdr x))))))


(defun proved-functional-instances-alist-entryp (x)
  (case-match x
    ((name fn-subst . on-behalf)
     (and (symbolp name)
          (pseudo-functional-substitutionp fn-subst)
          (or (equal on-behalf 0)
              (symbolp on-behalf))))
    (& nil)))

(defun proved-functional-instances-alistp (val)
  (cond ((atom val) (null val))
        (t (and (proved-functional-instances-alist-entryp (car val))
                (proved-functional-instances-alistp (cdr val))))))

; -----------------------------------------------------------------
; NONCONSTRUCTIVE-AXIOM-NAMES [GLOBAL-VALUE]

(defun nonconstructive-axiom-namesp (val)
  (symbol-listp val))

; -----------------------------------------------------------------
; STANDARD-THEORIES [GLOBAL-VALUE]

(defun pseudo-theoryp1 (lst)

; A difference between this function and the more rigorous theoryp is that
; we do not check that the (pseudo-) runes in lst are ordered by nume.
; This function is called ``pseudo-theoryp1'' rather than ``pseudo-theoryp''
; because the latter name is defined later to check the THEORYP property
; and by convention must take sym as an argument.

  (cond ((atom lst) (null lst))
        (t (and (pseudo-runep (car lst))
                (pseudo-theoryp1 (cdr lst))))))

(defun pseudo-standard-theoriesp (val)
  (case-match val
    ((r-unv r-fn1 r-fn2 r-fn3)
     (and (pseudo-theoryp1 r-unv)
          (pseudo-theoryp1 r-fn1)
          (pseudo-theoryp1 r-fn2)
          (pseudo-theoryp1 r-fn3)))
    (& nil)))

; -----------------------------------------------------------------
; CURRENT-THEORY [GLOBAL-VALUE]

(defun pseudo-current-theoryp (val)
  (pseudo-theoryp1 val))

; -----------------------------------------------------------------
; CURRENT-THEORY-AUGMENTED [GLOBAL-VALUE]

(defun pseudo-augmented-theoryp (lst)
  (cond ((atom lst) (null lst))
        (t (and (consp (car lst))
                (pseudo-numep (car (car lst)))
                (pseudo-runep (cdr (car lst)))
                (pseudo-augmented-theoryp (cdr lst))))))

(defun pseudo-current-theory-augmentedp (val)
  (pseudo-augmented-theoryp val))

; -----------------------------------------------------------------
; CURRENT-THEORY-INDEX [GLOBAL-VALUE]

; The current-theory-index is the highest nume in use as of the setting of
; current-theory.

(defun pseudo-current-theory-indexp (val)
  (or (pseudo-numep val)
      (equal val -1)))

; -----------------------------------------------------------------
; GENERALIZE-RULES [GLOBAL-VALUE]

(defrec generalize-rule (nume formula . rune) nil)

(defun pseudo-generalize-rulep (x)
  (case-match x
    (('generalize-rule nume formula . rune)
     (and (pseudo-numep nume)
          (pseudo-termp formula)
          (pseudo-runep rune)))
    (& nil)))

(defun pseudo-generalize-rulesp (val)
  (cond ((atom val) (null val))
        (t (and (pseudo-generalize-rulep (car val))
                (pseudo-generalize-rulesp (cdr val))))))

; -----------------------------------------------------------------
; CLAUSE-PROCESSOR-RULES [GLOBAL-VALUE]

; Each element is a (name . formula) pair, where name is the event in which
; formula was proved as a :clause-processor-rule.

(defun pseudo-clause-processor-rulesp (val)
  (cond ((atom val) (null val))
        (t (and (consp (car val))
                (symbolp (car (car val)))
                (pseudo-termp (cdr (car val)))
                (pseudo-clause-processor-rulesp (cdr val))))))

; -----------------------------------------------------------------
; BOOT-STRAP-FLG [GLOBAL-VALUE]

(defun boot-strap-flgp (val)
  (booleanp val))

; -----------------------------------------------------------------
; BOOT-STRAP-PASS-2 [GLOBAL-VALUE]

(defun boot-strap-pass-2p (val)
  (booleanp val))

; -----------------------------------------------------------------
; SKIP-PROOFS-SEEN [GLOBAL-VALUE]

(defun skip-proofs-seenp (val)

; Legal values are nil, (:include-book full-book-name), or any event form.

  (or (null val)
      (and (true-listp val)
           (equal (len val) 2)
           (eq (car val) :include-book)
           (stringp (cadr val)))
      (pseudo-event-formp val)))

; -----------------------------------------------------------------
; REDEF-SEEN [GLOBAL-VALUE]

(defun redef-seenp (val)

; Legal values are nil, (:include-book full-book-name), or any event form.

  (or (null val)
      (and (true-listp val)
           (equal (len val) 2)
           (eq (car val) :include-book)
           (stringp (cadr val)))
      (pseudo-event-formp val)))

; -----------------------------------------------------------------
; CERT-REPLAY [GLOBAL-VALUE]

(defun cert-replayp (val)
  (or (null val)
      (eq val t)
      (and (consp val)
           (true-listp (cdr val)) ; actually, a world
           (posp (car val)))))

; -----------------------------------------------------------------
; PROOF-SUPPORTERS-ALIST [GLOBAL-VALUE]

(defun proof-supporters-alistp (val)
  (cond ((atom val) (null val))
        (t (and (consp (car val))
                (or (symbolp (caar val))
                    (symbol-listp (caar val)))
                (cdar val)
                (symbol-listp (cdar val))
                (proof-supporters-alistp (cdr val))))))

; -----------------------------------------------------------------
; FREE-VAR-RUNES-ALL [GLOBAL-VALUE]

; List of all runes for which :match-free :all was declared.

(defun pseudo-free-var-runes-allp (val)
  (pseudo-theoryp1 val))

; -----------------------------------------------------------------
; FREE-VAR-RUNES-ONCE [GLOBAL-VALUE]

; List of all runes for which :match-free :once was declared.

(defun pseudo-free-var-runes-oncep (val)
  (pseudo-theoryp1 val))

; -----------------------------------------------------------------
; TRANSLATE-CERT-DATA [GLOBAL-VALUE]

(defun weak-translate-cert-data-record-listp (lst)
  (cond ((atom lst) (null lst))
        (t (and (weak-translate-cert-data-record-p (car lst))
                (weak-translate-cert-data-record-listp (cdr lst))))))

(defun pseudo-translate-cert-datap (val)
  (cond ((atom val) (null val))
        (t (and (consp (car val))
                (symbolp (caar val))
                (weak-translate-cert-data-record-listp (cdar val))
                (pseudo-translate-cert-datap (cdr val))))))

; -----------------------------------------------------------------
; CHK-NEW-NAME-LST [GLOBAL-VALUE]

; This global is actually a constant.  It is a list of the names that are
; redefined during initialization.  We could check that this variable is set
; exactly once in the world, but we don't.

(defun chk-new-name-lstp (val)
  (symbol-listp val))

; -----------------------------------------------------------------
; TAU-CONJUNCTIVE-RULES [GLOBAL-VALUE]

(defun pseudo-tau-pairp (sym val)

; This is a non-traditional pseudo- recognizer.  Sym is supposed to be the
; symbol on which this val is stored on the 'tau-pair property.  Thus, sym
; should be eq to the cdr of the val.  However, we also need the concept of a
; tau pair found elsewhere, e.g., as the pos-implicants property.  We make this
; predicate do double duty.  If sym is nil, then we do not check for any
; relationship between sym and val.

  (declare (xargs :guard (symbolp sym)))
  (cond (sym
         (and (consp val)
              (natp (car val))
              (eq (cdr val) sym)))
        (t (and (consp val)
                (rationalp (car val))
                (symbolp (cdr val))))))

(defun pseudo-tau-pairp-listp (lst)
  (cond ((atom lst) (equal lst nil))
        (t (and (consp (car lst))
                (pseudo-tau-pairp nil (car lst))
                (pseudo-tau-pairp-listp (cdr lst))))))

(defun indexed-pairs-ordered-strictly-descendingp (lst)
  (declare (xargs :guard (pseudo-tau-pairp-listp lst)))
  (cond ((endp lst) t)
        ((endp (cdr lst)) t)
        ((> (car (car lst)) (car (cadr lst)))
         (indexed-pairs-ordered-strictly-descendingp (cdr lst)))
        (t nil)))

(defun pseudo-tau-pairsp (x)
  (and (pseudo-tau-pairp-listp x)
       (indexed-pairs-ordered-strictly-descendingp x)))

(defun pseudo-evg-singletonp (x)
  (and (consp x)
       (null (cdr x))))

(defun pseudo-evg-singletonsp1 (lst)
  (cond ((atom lst) (equal lst nil))
        (t (and (pseudo-evg-singletonp (car lst))
                (pseudo-evg-singletonsp1 (cdr lst))))))

(defun lexorder-strict-ascendingp-without-list-nil (lst)
  (cond ((atom lst) t)
        ((atom (cdr lst)) t)
        ((lexorder (cadr lst) (car lst))
         nil)
        (t
         (lexorder-strict-ascendingp-without-list-nil (cdr lst)))))

(defun pseudo-evg-singletonsp (lst)
  (and (pseudo-evg-singletonsp1 lst)
       (lexorder-strict-ascendingp-without-list-nil
        (if (equal (car lst) '(nil))
            (cdr lst)
          lst))))

; (defrec tau-interval (domain (lo-rel . lo) . (hi-rel . hi)) t)

(defun pseudo-tau-intervalp (x)
  (cond
   ((eq x nil) t)
   ((and (consp x)
         (consp (cdr x))
         (consp (car (cdr x)))
         (consp (cdr (cdr x))))
    (let ((dom (car x))
          (lo-rel (car (cadr x)))
          (lo (cdr (cadr x)))
          (hi-rel (car (cddr x)))
          (hi (cdr (cddr x))))
      (and (or (eq dom 'integerp)
               (eq dom 'rationalp)
               (eq dom 'acl2-numberp)
               (null dom))
           (if (eq dom 'integerp)
               (and (null lo-rel)
                    (or (null lo) (integerp lo))
                    (null hi-rel)
                    (or (null hi) (integerp hi)))
               (and (booleanp lo-rel)
                    (or (null lo)
                        (rationalp lo))
                    (booleanp hi-rel)
                    (or (null hi)
                        (rationalp hi)))))))
   (t nil)))

(defun pseudo-taup (x)

; While the defrec for tau is
; (defrec tau
;   ((pos-evg . neg-evgs) interval . (pos-pairs . neg-pairs))
;   t)
; where
; pos-evg:   nil or a singleton list containing an evg
; neg-evgs:  list of singleton lists of evgs, duplicate-free, suitably ordered
; interval:  pseudo-tau-intervalp
; pos-pairs: list of tau-pairs, duplicate-free, ordered descending
; neg-pairs: list of tau-pairs, duplicate-free ordered descending

; it is possible for cons above to be represented by NIL if the corresponding
; fields are empty.  This happens because we sometimes pass in nil as an empty
; tau and then change one field, constructing something like (nil nil
; . neg-pairs) where you might expect ((nil . nil) nil . neg-pairs).

  (cond ((atom x)
         (equal x nil))
        ((atom (car x))
         (and (equal (car x) nil)
              (if (consp (cdr x))
                  (and (pseudo-tau-intervalp (cadr x))
                       (cond ((atom (cddr x))
                              (equal (cddr x) nil))
                             (t (and (pseudo-tau-pairsp (car (cddr x)))
                                     (pseudo-tau-pairsp (cdr (cddr x)))))))
                  (equal (cdr x) nil))))
        (t (and (and (or (null (car (car x)))
                         (pseudo-evg-singletonp (car (car x))))
                     (pseudo-evg-singletonsp (cdr (car x))))
                (if (consp (cdr x))
                    (and (pseudo-tau-intervalp (cadr x))
                         (cond
                          ((atom (cddr x))
                           (equal (cddr x) nil))
                          (t (and (pseudo-tau-pairsp (car (cddr x)))
                                  (pseudo-tau-pairsp (cdr (cddr x)))))))
                    (equal (cdr x) nil))))))

(defun pseudo-taup-listp (x)
  (cond ((atom x) (equal x nil))
        (t (and (pseudo-taup (car x))
                (pseudo-taup-listp (cdr x))))))

(defun pseudo-tau-conjunctive-rulesp (val)
  (pseudo-taup-listp val))

; -----------------------------------------------------------------
; TAU-RUNES [GLOBAL-VALUE]
; TAU-LOST-RUNES [GLOBAL-VALUE]

(defun pseudo-runep-listp (val)
  (cond ((atom val) (equal val nil))
        (t (and (pseudo-runep (car val))
                (pseudo-runep-listp (cdr val))))))

; -----------------------------------------------------------------
; TAU-NEXT-INDEX [GLOBAL-VALUE]
; TAU-MV-NTH-SYNONYMS [GLOBAL-VALUE]

; These are all handled by previously defined functions.

; -----------------------------------------------------------------
; TTAGS-SEEN [GLOBAL-VALUE]

; This is an association list pairing ttags with lists of filenames with which they
; are associated.

(defun ttags-seenp (val)
  (cond ((atom val) (null val))
        (t (and (consp (car val))
                (symbolp (car (car val))) ; a ttag
                (true-listp (cdr (car val))) ; guard for next conjunct

; The cdr of (car val) is a list of strings, indicating books in which the ttag
; has been declared, and possibly nil, indicating that the ttag was declared at
; top-level.

                (string-listp (remove1-eq 'nil (cdr (car val))))
                (ttags-seenp (cdr val))))))

; -----------------------------------------------------------------
; NEVER-UNTOUCHABLE-FNS [GLOBAL-VALUE]

; This is a symbol-alist pairing function names with lists of
; well-formedness-guarantees.

(verify-termination arity-alistp) ; and guards

(defun well-formedness-guaranteep (x)

; A well-formedness guarantee is actually: ((name fn thm-name1 hyp-fn
; thm-name2) . arity-alist) where name is the name of a metatheorem or the
; correctness of a clause-processor, fn is the metafunction or
; clause-processor, thm-name1 is the name of the theorem establishing that the
; output of fn is well-formed, and hyp-fn and thm-name2 are the analogous
; things for those metatheorems with hyp-fns.  The last two elements are
; omitted when there is no hyp-fn for name.  The arity-alist maps function
; symbols to their assumed arities.  We just check the syntatic conditions.

  (and (consp x)
       (symbol-listp (car x))
       (or (equal (len (car x)) 3)
           (equal (len (car x)) 5))
       (arity-alistp (cdr x))))

(defun well-formedness-guarantee-listp (lst)
  (if (atom lst)
      (eq lst nil)
      (and (well-formedness-guaranteep (car lst))
           (well-formedness-guarantee-listp (cdr lst)))))

(defun never-untouchable-fnsp (val)
  (if (atom val)
      (eq val nil)
      (and (consp (car val))
           (symbolp (car (car val)))
           (well-formedness-guarantee-listp (cdr (car val)))
           (never-untouchable-fnsp (cdr val)))))

; -----------------------------------------------------------------
; UNTOUCHABLE-FNS [GLOBAL-VALUE]

; Technically, the two untouchable lists, fns and vars, should be function or
; macro symbols and state global variables, respectively.  But I don't think
; that has to be enforced.  Random symbols on the list just further limit what
; the user might write.

(defun untouchable-fnsp (val)
  (symbol-listp val))

; -----------------------------------------------------------------
; UNTOUCHABLE-VARS [GLOBAL-VALUE]

(defun untouchable-varsp (val)
  (symbol-listp val))

; -----------------------------------------------------------------
; NEVER-IRRELEVANT-FNS-ALIST [GLOBAL-VALUE]

(defun never-irrelevant-fns-alistp (val)
  (and (symbol-alistp val)
       (subsetp-eq (strip-cdrs val)
                   '(t nil :both))))

; -----------------------------------------------------------------
; DEFINED-HEREDITARILY-CONSTRAINED-FNS [GLOBAL-VALUE]

(defun pseudo-defined-hereditarily-constrained-fnsp (val)
  (pseudo-function-symbol-listp val nil))

; -----------------------------------------------------------------
; WORLD-GLOBALS [GLOBAL-VALUE]

; This list of symbols is fixed and we could could check that it is set exactly once, but don't.

(defun world-globalsp (val)
  (symbol-listp val))

;-----------------------------------------------------------------
; LAMBDA$-ALIST

; Lambda$-alist maps the lambda expressions produced by the raw Lisp
; macroexpansion of lambda$ expressions to the logic translations of the
; lambda$ expressions.  See chk-acceptable-lambda$-translations.  But we just
; insist it is an alist.

(defun lambda$-alistp (val)
  (alistp val))

;-----------------------------------------------------------------
; LOOP$-ALIST

; Loop$-alist maps loop$ expressions to their logic translations.  We just
; insist it is an alist.

(defun loop$-alistp (val)
  (alistp val))

;-----------------------------------------------------------------
; COMMON-LISP-COMPLIANT-LAMBDAS [GLOBAL-VALUE]
(defun common-lisp-compliant-lambdasp (val)
; This is really a list well-formed quoted lambda expressions (all of which
; have been guard verified).  But we're just insisting it be a true list right
; now!
  (true-listp val))

;-----------------------------------------------------------------
; REWRITE-QUOTED-CONSTANT-RULES

; This is a list of rewrite-rule records, all of which have the subclass
; REWRITE-QUOTED-CONSTANT.

(defun pseudo-loop-stopper-elementp (x)
  (case-match x
    ((var1 var2 . fns)
     (and (symbolp var1)
          (symbolp var2)
          (pseudo-function-symbol-listp fns nil)))
    (& nil)))

(defun pseudo-loop-stopperp (x)
  (cond ((atom x) (null x))
        (t (and (pseudo-loop-stopper-elementp (car x))
                (pseudo-loop-stopperp (cdr x))))))

(defun nil-or-nat-listp (x)
  (cond ((atom x) (null x))
        (t (and (or (null (car x))
                    (natp (car x)))
                (nil-or-nat-listp (cdr x))))))

(defun pseudo-match-freep (x)

; According to a comment in the defrec for rewrite-rule, the match-free should
; be :once or :all if there are free vars in the hypotheses of a rule.  This
; function doesn't check that condition.

  (or (null x)
      (eq x :once)
      (eq x :all)))

(defun pseudo-rewrite-quoted-constant-rulep (x)
  (case-match x
    (('REWRITE-RULE rune nume hyps equiv lhs rhs
                    subclass heuristic-info
                    backchain-limit-lst
                    var-info . match-free)
     (cond
      ((eq subclass 'rewrite-quoted-constant)
       (and (pseudo-runep rune)
            (pseudo-numep nume)
            (pseudo-term-listp hyps)
            (pseudo-function-symbolp equiv 2)
            (pseudo-termp lhs)
            (pseudo-termp rhs)
            (consp heuristic-info)
            (integerp (car heuristic-info))
            (<= 1 (car heuristic-info))
            (<= (car heuristic-info) 3)
            (pseudo-loop-stopperp (cdr heuristic-info))
            (or (null backchain-limit-lst) ; If the user explicitly sets this field to a nat
                (nil-or-nat-listp backchain-limit-lst)) ; it is coerced to a list of nats.
            (booleanp var-info)
            (pseudo-match-freep match-free)))
      (t nil)))
    (& nil)))

(defun pseudo-rewrite-quoted-constant-rulesp (x)
  (cond ((atom x) (null x))
        (t (and (pseudo-rewrite-quoted-constant-rulep (car x))
                (pseudo-rewrite-quoted-constant-rulesp (cdr x))))))

;-----------------------------------------------------------------
; ABSOLUTE-EVENT-NUMBER

(defun absolute-event-numberp (sym val)
  (declare (ignore sym))
  (natp val))

;-----------------------------------------------------------------
; ABSSTOBJ-INFO

(defun absstobj-infop (val)
  (and (weak-absstobj-info-p val)
       (symbolp (access absstobj-info val :st$c))
       (let ((absstobj-tuples (access absstobj-info val :absstobj-tuples)))
         (and (symbol-alistp absstobj-tuples)
              (let ((cdrs (strip-cdrs absstobj-tuples)))
                (and (symbol-alistp cdrs)
                     (let ((cddrs (strip-cdrs cdrs)))
                       (and (symbol-alistp cddrs)
                            (r-symbol-alistp cddrs)))))))))

;-----------------------------------------------------------------
; ACCESSOR-NAMES

; This is an array that maps stobj argument positions to name of the constant with
; that position as its value.  E.g., for a stobj named ST with fields REGI, P-C, HALT, and MEM,
; the ACCESSOR-NAMES property is:
;    ((:HEADER :DIMENSIONS (4)
;               :MAXIMUM-LENGTH 5
;               :DEFAULT NIL
;               :NAME ST
;               :ORDER :NONE)
;      (0 . *REGI*)
;      (1 . *P-C*)
;      (2 . *HALT*)
;      (3 . *MEMI*))

(defun accessor-namesp (sym val)
  (array1p sym val))

;-----------------------------------------------------------------
; ATTACHMENT

; ATTACHMENT can be anything for our present purposes.  We may strengthen this
; specification in the future.

(defun attachment-propertyp (sym val)
  (declare (ignore sym))
  (or (pseudo-function-symbolp val nil)
      (and (consp val)
           (eq (car val) :attachment-disallowed)
           (or (stringp (cdr val))
               (and (true-listp (cdr val)) ; msg
                    (stringp (cadr val)))))

; We really should check in the next case val associates
; pseudo-function-symbolps with pseudo-function-symbolp.

      (symbol-alistp val)))

;-----------------------------------------------------------------
; BIG-SWITCH

(defun pseudo-big-switchp (sym val)

; (defrec big-switch-rule (formals switch-var switch-var-pos body) nil)
; where switch-var is the switch var and switch-var-pos is its position in
; formals.
  (declare (ignore sym))
  (and (true-listp val)
       (equal (len val) 5)
       (eq (car val) 'big-switch-rule)
       (let ((formals (nth 1 val))
             (switch-var (nth 2 val))
             (switch-var-pos (nth 3 val))
             (body (nth 4 val)))
         (and (pseudo-arglistp formals)
              (natp switch-var-pos)
              (< switch-var-pos (length formals))
              (equal (nth switch-var-pos formals) switch-var)
              (pseudo-termp body)))))

;-----------------------------------------------------------------
; TAU-BOUNDERS-FORM-1

(defun tau-interval-domainsp (x)
  (cond ((atom x) (eq x nil))
        (t (and (member-eq (car x) '(integerp rationalp acl2-numberp nil))
                (tau-interval-domainsp (cdr x))))))

(defun tau-interval-domainsp-listp (x)
  (cond ((atom x) (eq x nil))
        (t (and (tau-interval-domainsp (car x))
                (tau-interval-domainsp-listp (cdr x))))))

(defun pseudo-bounder-correctnessp (sym x)
  (and (consp x)
       (consp (car x))
       (consp (cdr x))
       (symbolp (car (car x)))
       (tau-interval-domainsp-listp (cdr (car x)))
       (eq sym (car (car x)))
       (symbolp (car (cdr x)))
       (nat-listp (cdr (cdr x)))))

(defun pseudo-tau-boundersp (sym val)
  (cond ((atom val) (eq val nil))
        (t (and (pseudo-bounder-correctnessp sym (car val))
                (pseudo-tau-boundersp sym (cdr val))))))

;-----------------------------------------------------------------
; TAU-BOUNDERS-FORM-2

(defun pseudo-tau-boundersp-listp (sym val)
  (cond ((atom val) (eq val nil))
        (t (and (pseudo-tau-boundersp sym (car val))
                (pseudo-tau-boundersp-listp sym (cdr val))))))

;-----------------------------------------------------------------
; CLASSES

; This is a list of fully elaborated rule classes as returned by translate-rule-classes.
; For the present purposes we just check that it is an alist mapping keywords to keyword alists.

(defun classesp (sym val)
  (declare (ignore sym))
  (keyword-to-keyword-value-list-alistp val))


;-----------------------------------------------------------------
; CLASSICALP

(defun classicalpp (sym val)
  (declare (ignore sym))
  (booleanp val))

;-----------------------------------------------------------------
; CLAUSE-PROCESSOR

(defun clause-processorp (sym val)
  (declare (ignore sym))
  (or (booleanp val)
      (well-formedness-guaranteep val)))

;-----------------------------------------------------------------
; COARSENINGS

; This is really a true list of equivalence relation names.

(defun coarseningsp (sym val)
  (declare (ignore sym))
  (pseudo-function-symbol-listp val 2))

;-----------------------------------------------------------------
; CONCRETE-STOBJ

(defun concrete-stobjp (sym val)
  (declare (ignore sym))
  (symbolp val))

;-----------------------------------------------------------------
; CONGRUENCES

; If fn has arity n, then the 'congruences property of fn is a list of tuples,
; each of which is of the form (equiv slot1 slot2 ... slotn), where equiv is
; some equivalence relation and each slotk summarizes our knowledge of what is
; allowed in each argument slot of fn while maintaining equiv.  Each slotk is a
; list of ``congruence-rules'', which are instances of the record
; (defrec congruence-rule (nume equiv . rune) t).

(defun pseudo-congruence-rulep (x)
  (case-match x
    ((nume equiv . rune)
     (and (pseudo-numep nume)
          (pseudo-function-symbolp equiv 2)
          (pseudo-runep rune)))
    (& nil)))

(defun pseudo-congruence-rule-listp (x)
  (cond ((atom x) (null x))
        (t (and (pseudo-congruence-rulep (car x))
                (pseudo-congruence-rule-listp (cdr x))))))

(defun pseudo-congruence-rule-list-listp (x)
  (cond ((atom x) (null x))
        (t (and (pseudo-congruence-rule-listp (car x))
                (pseudo-congruence-rule-list-listp (cdr x))))))

(defun pseudo-congruence-tuplep (x)

; If x is a congruence tuple found under a function symbol fn of arity n,
; then...

  (or (null x)
      (and (consp x)
           (pseudo-function-symbolp (car x) 2)         ; an equivalence relation
           (pseudo-congruence-rule-list-listp (cdr x)) ; a list of n congruence rule lists.
           )))

(defun pseudo-congruence-tuple-listp (x)
  (cond ((atom x) (null x))
        (t (and (pseudo-congruence-tuplep (car x))
                (pseudo-congruence-tuple-listp (cdr x))))))

(defun congruencesp (sym val)
  (declare (ignore sym))
  (pseudo-congruence-tuple-listp val))

;-----------------------------------------------------------------
; PEQUIVS

; If fn has arity n, then the 'pequivs property of fn is an alist, each of
; whose elements is of the form (equiv pequiv1 ... pequivk), where equiv is
; some equivalence relation and each pequivi is a pequiv record.

(verify-termination legal-variable-or-constant-namep) ; and guards
(verify-termination legal-variablep) ; and guards

(defun pseudo-pequiv-pattern-p (p)
  (or (legal-variablep p)
      (and (weak-pequiv-pattern-p p)
           (symbolp (access pequiv-pattern p :fn)) ; function symbol
           (pseudo-term-listp (access pequiv-pattern p :pre-rev))
           (pseudo-term-listp (access pequiv-pattern p :post))
           (eql (access pequiv-pattern p :posn)
                (1+ (length (access pequiv-pattern p :pre-rev))))
           (pseudo-pequiv-pattern-p (access pequiv-pattern p :next)))))

(defun pseudo-pequiv-p (x)
  (and (weak-pequiv-p x)
       (pseudo-pequiv-pattern-p (access pequiv x :pattern))
       (alistp (access pequiv x :unify-subst))
       (pseudo-congruence-rulep (access pequiv x :congruence-rule))))

(defun pseudo-pequiv-listp (lst)
  (cond ((atom lst) (null lst))
        (t (and (pseudo-pequiv-p (car lst))
                (pseudo-pequiv-listp (cdr lst))))))

(defun pseudo-pequiv-alistp (alist)
  (cond ((atom alist) (null alist))
        (t (and (consp (car alist))
                (symbolp (caar alist)) ; function-symbolp
                (pseudo-pequiv-listp (cdar alist))
                (pseudo-pequiv-alistp (cdr alist))))))

(defun pequivsp (sym val)
  (declare (ignore sym))
  (or (null val)
      (and (weak-pequivs-property-p val)
           (pseudo-pequiv-alistp (access pequivs-property val :deep))
           (pseudo-pequiv-alistp (access pequivs-property val :shallow)))))

;-----------------------------------------------------------------
; CONGRUENT-STOBJ-REP

(defun congruent-stobj-repp (sym val)
  (declare (ignore sym))
  (symbolp val))

;-----------------------------------------------------------------
; CONST

; CONST is the value of a constant.  It can be anything.

; This function should be named CONSTP but that is so common it collides with some
; distributed books and thus prevented their testing.

(defun const-propertyp (sym val)
  (declare (ignore sym val))
  t)

;-----------------------------------------------------------------
; CONSTRAINEDP

; The value of this property is t, nil, or the name of the clause processor
; whose trustworthiness depends on the constrained function sym.  Clause
; processors may have any non-0 number of arguments.

(defun pseudo-constrainedpp (sym val)
  (declare (ignore sym))
  (or (booleanp val)
      (pseudo-function-symbolp val nil)))

;-----------------------------------------------------------------
; CONSTRAINT-LST

(defun constraint-lstp (sym val)
  (declare (ignore sym))
  (or (unknown-constraints-p val)
      (pseudo-function-symbolp val nil) ; the fn where constraints are stored
      (pseudo-term-listp val)))

;-----------------------------------------------------------------
; DEF-BODIES

; This is a list of def-body records:
; (defrec def-body
;  ((nume hyp . concl) equiv . (recursivep formals rune . controller-alist))
;  t)

; meaning (implies hyp (equiv (sym . formals) concl)), with recursivep listing
; the fns in the clique and controll-alist being the map from fn symbols to
; controller masks.  Rune and nume justify it.

; The full controller-alistp check confirms that every fn in the clique is
; bound to an appropriately long Boolean mask in the controller alist.  It
; requires world to get the arities of the fns in the clique, whereas here we
; have only the formals of the one function whose body we're considering.  So
; we have to define a pseudo test.

(defun pseudo-controller-alistp (alist)
  (cond ((atom alist) (null alist))
        ((and (consp (car alist))
              (pseudo-function-symbolp (caar alist) nil)
              (boolean-listp (cdar alist)))
         (pseudo-controller-alistp (cdr alist)))
        (t nil)))

(defun pseudo-def-bodyp (x)
  (case-match x
    (((nume hyp . concl) equiv . (recursivep formals rune . controller-alist))
     (and (pseudo-numep nume)
          (or (null hyp)                ; means there is no hyp
              (pseudo-termp hyp))
          (pseudo-termp concl)
          (and (symbolp equiv)
               equiv) ; equality is represented by equal, not nil
          (pseudo-function-symbol-listp recursivep nil)
          (pseudo-arglistp formals)
          (pseudo-runep rune)
          (pseudo-controller-alistp controller-alist)))
    (& nil)))

(defun pseudo-def-body-listp (x)
  (cond ((atom x) (null x))
        (t (and (pseudo-def-bodyp (car x))
                (pseudo-def-body-listp (cdr x))))))

(defun pseudo-def-bodiesp (sym val)
  (declare (ignore sym))
  (pseudo-def-body-listp val))

;-----------------------------------------------------------------
; DEFAXIOM-SUPPORTER

; When present, this is the name of an axiom in which sym appears.

(defun defaxiom-supporterp (sym val)
  (declare (ignore sym))
  (symbolp val))

;-----------------------------------------------------------------
; DEFCHOOSE-AXIOM

; The formula of the axiom constraining sym, which was introduced by defchoose.

(defun pseudo-defchoose-axiomp (sym val)
  (declare (ignore sym))
  (pseudo-termp val))

;-----------------------------------------------------------------
; ELIMINATE-DESTRUCTORS-RULE

; This contains a single elim-rule:
; (defrec elim-rule
;   (((nume . crucial-position) . (destructor-term . destructor-terms))
;    (hyps . equiv)
;    (lhs . rhs)
;    . rune) nil)

(defun pseudo-elim-rulep (x)
  (case-match x
    (('ELIM-RULE ((nume . crucial-position) . (destructor-term . destructor-terms))
                 (hyps . equiv)
                 (lhs . rhs)
                 . rune)
     (and (pseudo-numep nume)
          (natp crucial-position)
          (pseudo-termp destructor-term)
          (pseudo-term-listp destructor-terms)
          (pseudo-term-listp hyps)
          (pseudo-function-symbolp equiv 2)
          (pseudo-termp lhs)
          (symbolp rhs)  ; actually, a variable symbol
          (pseudo-runep rune)
          (consp destructor-term)
          (< crucial-position (len (cdr destructor-term)))
          (equal rhs (nth crucial-position (cdr destructor-term)))))
    (& nil)))

(defun pseudo-eliminate-destructors-rulep (sym val)
  (declare (ignore sym))
  (pseudo-elim-rulep val))

;-----------------------------------------------------------------
; FORMALS

(defun pseudo-formalsp (sym val)
  (declare (ignore sym))
  (pseudo-arglistp val))

;-----------------------------------------------------------------
; FORWARD-CHAINING-RULES

; This is a list of
; (defrec forward-chaining-rule
;   ((rune . nume) trigger hyps concls . match-free)
;   nil)

(defun pseudo-forward-chaining-rulep (x)
  (case-match x
    (('FORWARD-CHAINING-RULE (rune . nume) trigger hyps concls . match-free)
     (and (pseudo-runep rune)
          (pseudo-numep nume)
          (pseudo-termp trigger)
          (pseudo-term-listp hyps)
          (pseudo-term-listp concls)
          (pseudo-match-freep match-free)))
    (& nil)))

(defun pseudo-forward-chaining-rule-listp (x)
  (cond ((atom x) (null x))
        (t (and (pseudo-forward-chaining-rulep (car x))
                (pseudo-forward-chaining-rule-listp (cdr x))))))

(defun pseudo-forward-chaining-rulesp (sym val)
  (declare (ignore sym))
  (pseudo-forward-chaining-rule-listp val))

;-----------------------------------------------------------------
; GLOBAL-VALUE

(defun pseudo-global-valuep (sym val w)

  (declare (xargs :guard (plist-worldp w)))

; Unlike other pseudo-checkers, this function takes w as an argument.  Here, w
; is the world to which the triple (sym GLOBAL-VALUE . val) was added.  Two
; syms need w to enable fast pseudo checks, EVENT-INDEX and COMMAND-INDEX,
; which generally contain w in their vals.

  (case sym
    (EVENT-LANDMARK (pseudo-event-landmarkp val))
    (COMMAND-LANDMARK (pseudo-command-landmarkp val))
    (KNOWN-PACKAGE-ALIST (known-package-alistp val))
    (WELL-FOUNDED-RELATION-ALIST (pseudo-well-founded-relation-alistp val))
    (BUILT-IN-CLAUSES (pseudo-built-in-clausesp val))
    (ATTACH-NIL-LST (pseudo-attach-nil-lst val))
    (ATTACHMENT-RECORDS (pseudo-attachment-recordsp val))
    (ATTACHMENTS-AT-GROUND-ZERO (pseudo-attachments-at-ground-zerop val))
    (HALF-LENGTH-BUILT-IN-CLAUSES (pseudo-half-length-built-in-clausesp val))
    (TYPE-SET-INVERTER-RULES (pseudo-type-set-inverter-rulesp val))
    (GLOBAL-ARITHMETIC-ENABLED-STRUCTURE (pseudo-global-arithmetic-enabled-structurep val))
    (OPERATING-SYSTEM (operating-systemp val))
    (EVENT-INDEX  (pseudo-event-indexp val w))
    (COMMAND-INDEX (pseudo-command-indexp val w))
    (EVENT-NUMBER-BASELINE (event-number-baselinep val))
    (COMMAND-NUMBER-BASELINE-INFO (command-number-baseline-infop val))
    (EMBEDDED-EVENT-LST (pseudo-embedded-event-lstp val))
    (CLTL-COMMAND (pseudo-cltl-commandp val))
    (TOP-LEVEL-CLTL-COMMAND-STACK (pseudo-cltl-command-listp val))
    (INCLUDE-BOOK-ALIST (pseudo-include-book-alistp val))
    (INCLUDE-BOOK-ALIST-ALL (pseudo-include-book-alist-allp val))
    (PCERT-BOOKS (pseudo-pcert-booksp val))
    (INCLUDE-BOOK-PATH (pseudo-include-book-pathp val))
    (CERTIFICATION-TUPLE (certification-tuplep val))
    (DOCUMENTATION-ALIST (documentation-alistp val))
    (PROVED-FUNCTIONAL-INSTANCES-ALIST (proved-functional-instances-alistp val))
    (NONCONSTRUCTIVE-AXIOM-NAMES (nonconstructive-axiom-namesp val))
    (STANDARD-THEORIES (pseudo-standard-theoriesp val))
    (CURRENT-THEORY (pseudo-current-theoryp val))
    (CURRENT-THEORY-LENGTH (natp val))
    (CURRENT-THEORY-AUGMENTED (pseudo-current-theory-augmentedp val))
    (CURRENT-THEORY-INDEX (pseudo-current-theory-indexp val))
    (GENERALIZE-RULES (pseudo-generalize-rulesp val))
    (CLAUSE-PROCESSOR-RULES (pseudo-clause-processor-rulesp val))
    (BOOT-STRAP-FLG (boot-strap-flgp val))
    (BOOT-STRAP-PASS-2 (boot-strap-pass-2p val))
    (SKIP-PROOFS-SEEN (skip-proofs-seenp val))
    (REDEF-SEEN (redef-seenp val))
    (CERT-REPLAY (cert-replayp val))
    (PROOF-SUPPORTERS-ALIST (proof-supporters-alistp val))
    (FREE-VAR-RUNES-ALL (pseudo-free-var-runes-allp val))
    (FREE-VAR-RUNES-ONCE (pseudo-free-var-runes-oncep val))
    (TRANSLATE-CERT-DATA (pseudo-translate-cert-datap val))
    (CHK-NEW-NAME-LST (chk-new-name-lstp val))
    (TAU-CONJUNCTIVE-RULES (pseudo-tau-conjunctive-rulesp val))
    (TAU-NEXT-INDEX (natp val))
    (TAU-RUNES (pseudo-runep-listp val))
    (TAU-MV-NTH-SYNONYMS (pseudo-function-symbol-listp val nil))
    (TAU-LOST-RUNES (pseudo-runep-listp val))
    (TTAGS-SEEN (ttags-seenp val))
    (NEVER-UNTOUCHABLE-FNS (never-untouchable-fnsp val))
    (UNTOUCHABLE-FNS (untouchable-fnsp val))
    (UNTOUCHABLE-VARS (untouchable-varsp val))
    (DEFINED-HEREDITARILY-CONSTRAINED-FNS
      (pseudo-defined-hereditarily-constrained-fnsp val))
    (WORLD-GLOBALS (world-globalsp val))
    (LAMBDA$-ALIST (lambda$-alistp val))
    (LOOP$-ALIST (loop$-alistp val))
    (COMMON-LISP-COMPLIANT-LAMBDAS (common-lisp-compliant-lambdasp val))
    (NEVER-IRRELEVANT-FNS-ALIST (never-irrelevant-fns-alistp val))
    (REWRITE-QUOTED-CONSTANT-RULES
     (pseudo-rewrite-quoted-constant-rulesp val))
    (otherwise nil)))

;-----------------------------------------------------------------
; GUARD

(defun pseudo-guardp (sym val)
  (declare (ignore sym))
  (pseudo-termp val))

;-----------------------------------------------------------------
; HEREDITARILY-CONSTRAINED-FNNAMES

(defun pseudo-hereditarily-constrained-fnnamesp (sym val)
  (declare (ignore sym))
  (pseudo-function-symbol-listp val nil))

;-----------------------------------------------------------------
; INDUCTION-MACHINE

; An induction machine is a list of tests-and-calls records:
; (defrec tests-and-calls (tests . calls) nil), where each of the two
; fields is a list of terms.

(defun pseudo-induction-machinep (sym val)
  (declare (ignore sym))
  (pseudo-tests-and-calls-listp val))

;-----------------------------------------------------------------
; INDUCTION-RULES

; This is a list of induction-rule records:
; (defrec induction-rule (nume (pattern . condition) scheme . rune) nil)

(defun pseudo-induction-rulep (x)
  (case-match x
    (('INDUCTION-RULE nume (pattern . condition) scheme . rune)
     (and (pseudo-numep nume)
          (pseudo-termp pattern)
          (pseudo-termp condition)
          (pseudo-termp scheme)
          (pseudo-runep rune)))
    (& nil)))

(defun pseudo-induction-rule-listp (x)
  (cond ((atom x) (null x))
        (t (and (pseudo-induction-rulep (car x))
                (pseudo-induction-rule-listp (cdr x))))))

(defun pseudo-induction-rulesp (sym val)
  (declare (ignore sym))
  (pseudo-induction-rule-listp val)  )

;-----------------------------------------------------------------
; JUSTIFICATION

(defun pseudo-ruler-extendersp (x)
  (or (eq x :all)
      (pseudo-function-symbol-listp x nil)))

(defun pseudo-justificationp (sym val)
  (declare (ignore sym))
  (case-match val
    (('JUSTIFICATION subset (subversive-p . (mp . rel))
                     (measure . ruler-extenders))
     (and (pseudo-arglistp subset)
          (booleanp subversive-p)
          (pseudo-function-symbolp mp 1)      ; mp, rel, and measure are used for heuristic purposes
          (pseudo-function-symbolp rel 2)     ; only and may not actually be fns or terms in the
          (pseudo-termp measure)              ; current world! But they are pseudo fns or terms.
          (pseudo-ruler-extendersp ruler-extenders)))
    (& nil)))

;-----------------------------------------------------------------
; LABEL

(defun labelp (sym val)
  (declare (ignore sym))
  (symbolp val))

;-----------------------------------------------------------------
; LEMMAS

; The lemmas property is a list of rewrite-rule records.

; (defrec rewrite-rule (rune nume hyps equiv lhs rhs
;                            subclass heuristic-info
;                            backchain-limit-lst
;                            var-info . match-free)
;   nil)

; But the restrictions on the fields depend on the subclass of the rule.

(defun pseudo-rewrite-rulep (x)
  (case-match x
    (('REWRITE-RULE rune nume hyps equiv lhs rhs
                    subclass heuristic-info
                    backchain-limit-lst
                    var-info . match-free)
     (case subclass
       (backchain
        (and (pseudo-runep rune)
             (pseudo-numep nume)
             (pseudo-term-listp hyps)
             (pseudo-function-symbolp equiv 2)
             (pseudo-termp lhs)
             (pseudo-termp rhs)
             (pseudo-loop-stopperp heuristic-info)
             (or (null backchain-limit-lst)               ; If the user explicitly sets this field to a nat
                 (nil-or-nat-listp backchain-limit-lst))  ; it is coerced to a list of nats.
             (booleanp var-info)
             (pseudo-match-freep match-free)))
       (abbreviation
        (and (pseudo-runep rune)
             (pseudo-numep nume)
             (null hyps)
             (pseudo-function-symbolp equiv 2)
             (pseudo-termp lhs)
             (pseudo-termp rhs)
             (null heuristic-info)
             (null backchain-limit-lst)
             (booleanp var-info)
             (null match-free)))
       (meta
        (and (pseudo-runep rune)
             (pseudo-numep nume)
             (or (null hyps)
                 (pseudo-function-symbolp hyps 1))     ; name of hyp generator
             (pseudo-function-symbolp equiv 2)
             (pseudo-function-symbolp lhs 1)           ; name of meta function
             (or (null rhs)
                 (eq rhs 'extended))
             (or (null heuristic-info)
                 (well-formedness-guaranteep heuristic-info))
             (or (null backchain-limit-lst)
                 (natp backchain-limit-lst))           ; backchain limit for meta rule really can be a nat
;            (null var-info) ; ignored
             (null match-free)))
       (definition
         (and (pseudo-runep rune)
              (pseudo-numep nume)
              (pseudo-term-listp hyps)
              (pseudo-function-symbolp equiv 2)
              (pseudo-termp lhs)
              (pseudo-termp rhs)
              (and (consp heuristic-info)             ; (recursivep . controller-alist)
                   (pseudo-function-symbol-listp (car heuristic-info) nil) ; recursivep
                   (pseudo-controller-alistp (cdr heuristic-info)))        ; controller-alist

              (null backchain-limit-lst)
              (integer-listp var-info) ; should really be nat-listp call
              (null match-free)))
       (otherwise nil)))
    (& nil)))

(defun pseudo-rewrite-rule-listp (x)
  (cond ((atom x) (null x))
        (t (and (pseudo-rewrite-rulep (car x))
                (pseudo-rewrite-rule-listp (cdr x))))))

(defun pseudo-lemmasp (sym val)
  (declare (ignore sym))
  (pseudo-rewrite-rule-listp val))

;-----------------------------------------------------------------
; LEVEL-NO

(defun level-nop (sym val)
  (declare (ignore sym))
  (natp val))

;-----------------------------------------------------------------
; LINEAR-LEMMAS

(defun pseudo-linear-lemmap (x)
  (case-match x
    (('LINEAR-LEMMA (nume . hyps) max-term concl
                      backchain-limit-lst rune . match-free)
     (and (pseudo-numep nume)
          (pseudo-term-listp hyps)
          (pseudo-termp max-term)
          (pseudo-termp concl)
          (or (null backchain-limit-lst)              ; If the user explicitly sets this to a
              (nil-or-nat-listp backchain-limit-lst)) ; nat it is coerced to a list of nats
          (pseudo-runep rune)
          (pseudo-match-freep match-free)))
    (& nil)))

(defun pseudo-linear-lemma-listp (x)
  (cond ((atom x) (null x))
        (t (and (pseudo-linear-lemmap (car x))
                (pseudo-linear-lemma-listp (cdr x))))))

(defun pseudo-linear-lemmasp (sym val)
  (declare (ignore sym))
  (pseudo-linear-lemma-listp val))

;-----------------------------------------------------------------
; LOOP$-RECURSION

(defun loop$-recursionp (sym val)
  (declare (ignore sym))
  (booleanp val))

;-----------------------------------------------------------------
; MACRO-ARGS

(verify-termination legal-initp) ; and guards

(verify-termination macro-arglist-keysp) ; and guards

(verify-termination macro-arglist-after-restp) ; and guards

(verify-termination lambda-keywordp) ; and guards

(verify-termination macro-arglist-optionalp) ; and guards

(verify-termination macro-arglist1p) ; and guards

(verify-termination subsequencep) ; and guards

(verify-termination collect-lambda-keywordps) ; and guards

; We avoid exporting names that might conflict with names used in distributed
; books, so that we can use this book to check the well-formedness of the
; worlds created by other books.

(local
 (defthm member-subsetp
  (implies (and (subsetp a b)
                (member e a))
           (member e b))))

(local
 (defthm subsetp-cons
   (implies (subsetp a b)
            (subsetp a (cons e b)))))

(defun hint-for-macro-arglist-keysp (args passed1 passed2)
  (declare (xargs :verify-guards nil))
  (cond ((endp args) (list passed1 passed2))
        (t (cons (hint-for-macro-arglist-keysp
                  (cdr args)
                  (cons (intern (symbol-name (car args)) "KEYWORD") passed1)
                  (cons (intern (symbol-name (car args)) "KEYWORD") passed2))
                 (hint-for-macro-arglist-keysp
                  (cdr args)
                  (cons (cond ((symbolp (caar args))
                               (intern (symbol-name (caar args))
                                       "KEYWORD"))
                              (t (car (caar args))))
                        passed1)
                  (cons (cond ((symbolp (caar args))
                               (intern (symbol-name (caar args))
                                       "KEYWORD"))
                              (t (car (caar args))))
                        passed2))))))

(defthm macro-arglist-keysp-subsetp
  (implies (and (macro-arglist-keysp args passed2)
                (subsetp passed1 passed2))
           (macro-arglist-keysp args passed1))
  :hints (("Goal" :induct (hint-for-macro-arglist-keysp args passed1 passed2))))

(local
 (defthm subsetp-x-x
   (subsetp x x)))

(defthm macro-arglist-keysp-cdr
  (implies (macro-arglist-keysp args passed)
           (macro-arglist-keysp (cdr args) passed)))

; Thus ends the work for macro-vars-key.  Here it is:

(verify-termination macro-vars-key) ; and guards

(verify-termination macro-vars-after-rest) ; and guards

(defthm eqlable-listp-collect-lambda-keywordsp
  (eqlable-listp (collect-lambda-keywordps args)))

(verify-termination macro-vars-optional) ; and guards

(verify-termination macro-args-structurep) ; and guards

(local
 (defthm true-listp-member-eq
   (implies (true-listp y)
            (true-listp (member-eq x y)))))

; The admission and guard verification of macro-vars, below, is the most
; complicated guard verification task of the lot.  The proof takes about 30
; seconds; 10 subgoals are pushed and proved by induction (though some are
; subsumed by others).

(verify-termination macro-vars) ; and guards

; The following function is a pseudo version of the negations of both
; chk-macro-arglist-msg and chk-macro-arglist.  The reason it is pseudo and not
; exact is that the pseudo version finishes with a check of pseudo-arglistp
; while the real checker finishes with a full-blown arglist check, the
; difference being that the pseudo versions don't insist on well-formed
; variable symbols or give STATE special significance.  So to be precise, if
; the relevant calls of chk-arglist-msg and pseudo-arglistp returned the same
; result, this function is equivalent to the negation of chk-macro-arglist-msg
; and of chk-macro-arglist.

(defun pseudo-macro-arglist-msgp (args)
  (and
   (macro-args-structurep args)
   (pseudo-arglistp (macro-vars args))))

(defun pseudo-macro-argsp (sym val)
  (declare (ignore sym))
  (pseudo-macro-arglist-msgp val))

;-----------------------------------------------------------------
; MACRO-BODY

(defun pseudo-macro-bodyp (sym val)
  (declare (ignore sym))
  (pseudo-termp val))

;-----------------------------------------------------------------
; NEG-IMPLICANTS

(defun pseudo-neg-implicantsp (sym val)
  (declare (ignore sym))
  (pseudo-taup val))

;-----------------------------------------------------------------
; NON-EXECUTABLEP

(defun non-executablepp (sym val)
  (declare (ignore sym))
  (or (eq val :program) ; proxy case (see :DOC defproxy)
      (booleanp val)))

;-----------------------------------------------------------------
; NON-MEMOIZABLE

(defun non-memoizablep (sym val)
  (declare (ignore sym))
  (booleanp val))

;-----------------------------------------------------------------
; POS-IMPLICANTS

(defun pseudo-pos-implicantsp (sym val)
  (declare (ignore sym))
  (pseudo-taup val))

;-----------------------------------------------------------------
; PREDEFINED

(defun predefinedp (sym val)
  (declare (ignore sym))
  (booleanp val))

;-----------------------------------------------------------------
; PRIMITIVE-RECURSIVE-DEFUNP

(defun primitive-recursive-defunpp (sym val)
  (declare (ignore sym))
  (booleanp val))

;-----------------------------------------------------------------
; QUICK-BLOCK-INFO

(defun pseudo-quick-block-info-listp (lst)
  (cond ((atom lst) (null lst))
        (t (and (member-eq (car lst)
                           '(QUESTIONABLE UNCHANGING SELF-REFLEXIVE))
                (pseudo-quick-block-info-listp (cdr lst))))))

(defun pseudo-quick-block-infop (sym val)
  (declare (ignore sym))

; To be exact, this function would have to additionally insure that sym is a
; function symbol, that val is as long as the FORMALS, and (to be semantically
; correct) accurately reflects the use of the arguments in recursion.

  (pseudo-quick-block-info-listp val))

; -----------------------------------------------------------------
; RECOGNIZER-ALIST

; Each property's recognizer-alist contains records of the following form:

; (defrec recognizer-tuple
;   (fn (nume . true-ts)
;       (false-ts . strongp)
;       . rune)
;   t)

(defun pseudo-recognizer-tuplep (fn x)
  (case-match x
    ((!fn (nume . true-ts) (false-ts . strongp) . rune)
     (and (pseudo-function-symbolp fn 1)
          (or (null nume) (pseudo-numep nume))  ; nil corresponds to the fake rune
          (type-setp true-ts)
          (type-setp false-ts)
          (booleanp strongp)
          (pseudo-runep rune)))
    (& nil)))

(defun pseudo-recognizer-alistp (fn x)
  (if (atom x)
      (null x)
      (and (pseudo-recognizer-tuplep fn (car x))
           (pseudo-recognizer-alistp fn (cdr x)))))

;-----------------------------------------------------------------
; RECURSIVEP

(defun pseudo-recursivepp (sym val)
  (declare (ignore sym))
  (pseudo-function-symbol-listp val nil))

;-----------------------------------------------------------------
; REDEFINED

(defun redefinedp (sym val)
  (declare (ignore sym))
  (case-match val
    ((renewal-mode . insig)
     (and (member-eq renewal-mode '(:erase :overwrite :reclassifying-overwrite))
          (or (null insig)
              (pseudo-internal-signaturep insig))))
    (& nil)))

;-----------------------------------------------------------------
; REDUNDANCY-BUNDLE

; Through Version_8.3 we stored a so-called redundancy-bundle for a defstobj
; event.  We found however that this was not sufficient for determining
; redundancy, as discussed in :doc note-8-4.  Perhaps everything in this
; section could therefore be deleted; however, it seems harmless to leave these
; functions in place for now, which could be helpful if they are useful
; elsewhere.

; At any rate, everything below in this section should be considered irrelevant
; to well-formedness of a world.

; The structure of a redundancy-bundle of a stobj is actually pretty
; unimportant.  They are only used as fingerprints of a defstobj event,
; allowing us to recognize a redundant event.  It is not clear that internal
; structure matters at all!  However, before realizing this we had defined the
; following pseudo recognizer for redundancy-bundles and so have left it in
; place.

; The redundancy-bundle of a stobj is computed by defstobj-redundancy-bundle
; and is of the form (field-descriptors . renaming-alist), where
; field-descriptors is the list of field descriptors from a legal defstobj
; event

;         (fieldi :type typei :initially vali :resizable bi)

; where each fieldi is a symbol, each typei is either a type-spec or (ARRAY
; type-spec (max)), each vali is an object satisfying typei, and each bi is
; Boolean.  Any and all of the keyword pairs may be omitted or presented in any
; order and (fieldi) may be shortened to fieldi.  The renaming-alist is a
; symbol-to-symbol doublet-style alist.  But CLTL type language is sufficiently
; complicated that we do not check here that typei is well-formed nor that vali
; satisfies it.  To do better, we should admit translate-declaration-to-guard1
; into the logic.

(defun pseudo-integer-boundp (x)
  (or (integerp x)
      (eq x '*)
      (and (consp x)
           (integerp (car x))
           (null (cdr x)))))

(defun pseudo-rational-boundp (x)
  (or (integerp x)
      (eq x '*)
      (and (consp x)
           (rationalp (car x))
           (null (cdr x)))))

(defun pseudo-type-specp (x)
  (cond ((or (eq x 'integer)
             (eq x 'signed-byte))
         t)
        ((and (consp x)
              (eq (car x) 'integer)
              (true-listp x)
              (equal (length x) 3))
         (and (pseudo-integer-boundp (cadr x))
              (pseudo-integer-boundp (caddr x))))
        ((eq x 'rational) t)
        ((eq x 'real) t)
        ((eq x 'complex) t)
        ((and (consp x)
              (or (eq (car x) 'rational)
                  (eq (car x) 'real))
              (true-listp x)
              (equal (length x) 3))
         (and (pseudo-rational-boundp (cadr x))
              (pseudo-rational-boundp (caddr x))))
        ((eq x 'bit) t)
        ((and (consp x)
              (eq (car x) 'mod)
              (true-listp x)
              (equal (length x) 2)
              (integerp (cadr x)))
         t)
        ((and (consp x)
              (eq (car x) 'signed-byte)
              (true-listp x)
              (equal (length x) 2)
              (integerp (cadr x))
              (> (cadr x) 0))
         t)
        ((eq x 'unsigned-byte)
         t)
        ((and (consp x)
              (eq (car x) 'unsigned-byte)
              (true-listp x)
              (equal (length x) 2)
              (integerp (cadr x))
              (> (cadr x) 0))
         t)
        ((eq x 'atom) t)
        ((eq x 'character) t)
        ((eq x 'cons) t)
        ((eq x 'list) t)
        ((eq x 'nil) t)
        ((eq x 'null) t)
        ((eq x 'ratio) t)
        ((eq x 'standard-char) t)
        ((eq x 'string) t)
        ((and (consp x)
              (eq (car x) 'string)
              (true-listp x)
              (equal (length x) 2)
              (integerp (cadr x))
              (>= (cadr x) 0))
         t)
        ((eq x 'symbol) t)
        ((eq x 't) t)
        ((weak-satisfies-type-spec-p x)
         t)
        ((and (consp x)
              (eq (car x) 'member)
              (eqlable-listp (cdr x)))
         t)
        (t nil)))

; We disable the above function because otherwise some of the functions below
; take a while to admit.

(in-theory (disable pseudo-type-specp))

(defun pseudo-array1-type-specp (x)
  (case-match x
    (('ARRAY type-spec (max))
     (and (pseudo-type-specp type-spec)
          (natp max)))
    (& nil)))

(defun pseudo-stobj-field-descriptor-keyword-pairp (key val)
  (cond ((eq key :type)
         (or (pseudo-type-specp val)
             (pseudo-array1-type-specp val)))
        ((eq key :initially)
         t)
        ((eq key :resizable)
         (booleanp val))
        (t nil)))

(defun pseudo-stobj-field-descriptor-keyword-alistp (x)
  (cond ((atom x) t)
        ((atom (cdr x)) nil)
        (t (and (pseudo-stobj-field-descriptor-keyword-pairp (car x) (cadr x))
                (pseudo-stobj-field-descriptor-keyword-alistp (cddr x))))))

(defun pseudo-stobj-field-descriptorp (x)
;      (fieldi :type typei :initially vali :resizable bi)
  (or (pseudo-function-symbolp x nil)
      (and (true-listp x)
           (consp x)
           (pseudo-function-symbolp (car x) nil)
           (pseudo-stobj-field-descriptor-keyword-alistp (cdr x)))))

(defun pseudo-stobj-field-descriptor-listp (x)
  (cond ((atom x) (null x))
        (t (and (pseudo-stobj-field-descriptorp (car x))
                (pseudo-stobj-field-descriptor-listp (cdr x))))))

(defun pseudo-doublet-style-renaming-alistp (x)
  (cond ((atom x) (null x))
        (t (and (consp (car x))
                (symbolp (car (car x)))
                (consp (cdr (car x)))
                (symbolp (cadr (car x)))
                (null (cddr (car x)))
                (pseudo-doublet-style-renaming-alistp (cdr x))))))

(defun pseudo-redundancy-bundlep (sym val)
  (declare (ignore sym))
  (case-match val
    ((field-descriptors . renaming-alist)
     (and (pseudo-stobj-field-descriptor-listp field-descriptors)
          (pseudo-doublet-style-renaming-alistp renaming-alist)))
    (& nil)))

;-----------------------------------------------------------------
; RUNIC-MAPPING-PAIRS

(defun pseudo-runic-mapping-pairs-listp (x)
  (cond ((atom x) (null x))
        (t (and (consp (car x))
                (pseudo-numep (car (car x)))
                (pseudo-runep (cdr (car x)))
                (pseudo-runic-mapping-pairs-listp (cdr x))))))

(defun pseudo-runic-mapping-pairsp (sym val)
  (declare (ignore sym))
  (pseudo-runic-mapping-pairs-listp val))

;-----------------------------------------------------------------
; SIBLINGS

(defun siblings-propertyp (sym val)
  (declare (ignore sym))
  (pseudo-function-symbol-listp val nil))

;-----------------------------------------------------------------
; SIGNATURE-RULES-FORM-1

(defun pseudo-signaturep (x)

; (defrec signature-rule (input-tau-list (vars . dependent-hyps) output-sign output-recog) t)
; where:
; :inputs-tau-list  - a list of tau in 1:1 correspondence with formals
; :vars             - a list of distinct symbols
; :dependent-hyps   - a list of terms
; :output-sign      - T (positive) or NIL (negative)
; :output-recog     - (i . pred) | (evg) ; i.e., tau-pair or singleton evg list


  (and (true-listp x)
       (equal (len x) 4)
       (let ((inputs-tau-list (nth 0 x))
             (vars-and-dependent-hyps (nth 1 x))
             (output-sign (nth 2 x))
             (output-recog (nth 3 x)))
         (and (pseudo-taup-listp inputs-tau-list)
              (consp vars-and-dependent-hyps)
              (symbol-listp (car vars-and-dependent-hyps))
              (no-duplicatesp-eq (car vars-and-dependent-hyps))
              (pseudo-term-listp (cdr vars-and-dependent-hyps))
              (booleanp output-sign)
              (or (pseudo-tau-pairp nil output-recog)
                  (pseudo-evg-singletonp output-recog))))))

(defun pseudo-signaturep-listp (x)
  (cond ((atom x) (equal x nil))
        (t (and (pseudo-signaturep (car x))
                (pseudo-signaturep-listp (cdr x))))))

(defun pseudo-signature-rules-form-1p (sym val)
  (declare (ignore sym))
  (pseudo-signaturep-listp val))

;-----------------------------------------------------------------
; SIGNATURE-RULES-FORM-2

(defun pseudo-signaturep-listp-listp (x)
  (cond ((atom x) (equal x nil))
        (t (and (pseudo-signaturep-listp (car x))
                (pseudo-signaturep-listp-listp (cdr x))))))

(defun pseudo-signature-rules-form-2p (sym val)
  (declare (ignore sym))
  (pseudo-signaturep-listp-listp val))

;-----------------------------------------------------------------
; SPLIT-TYPES-TERM

(defun pseudo-split-types-termp (sym val)
  (declare (ignore sym))
  (pseudo-termp val))

;-----------------------------------------------------------------
; INVARIANT-RISK

(defun pseudo-invariant-riskp (sym val)
  (declare (ignore sym val))
  t)

;-----------------------------------------------------------------
; STOBJ

(defun pseudo-stobjp (sym val)
  (declare (ignore sym))

; The other-names below contains the names of the field recognizers, accessors,
; updaters, various names associated with array-type fields (like the resizer),
; and the the names of the defconsts associating field names with position,
; e.g., a stobj whose 3rd component is MEM causes (defconst *MEM* 3) to be
; executed and for *MEM* to be among the other names.  For that reason, we do
; not here insist that other-names be (pseudo) function symbols.

  (case-match val
    (('*the-live-state*) t)
    ((live-var recog-name . other-names)
     (and (symbolp live-var)
          (pseudo-function-symbolp recog-name 1)
          (symbol-listp other-names)))
    (& nil)))
;-----------------------------------------------------------------
; STOBJ-CONSTANT

; To each field accessor, e.g., MEM, of a stobj, e.g., ST, there corresponds a
; constant symbol, e.g., *MEM*, whose value is the position of the field.  To
; recognize such stobj constant symbols, we store the name of the corresponding
; stobj, e.g., ST, under the STOBJ-CONSTANT property.

(defun pseudo-stobj-constantp (sym val)
  (declare (ignore sym))
  (pseudo-function-symbolp val nil))

;-----------------------------------------------------------------
; STOBJ-FUNCTION

; Under each function, e.g., UPDATE-MEM or MEMP or RESIZE-MEM, introduced by a
; stobj, e.g., ST, we store the STOBJ-FUNCTION property whose value is the stobj
; name, e.g., ST.

(defun pseudo-stobj-functionp (sym val)
  (declare (ignore sym))
  (pseudo-function-symbolp val nil))

;-----------------------------------------------------------------
; STOBJ-LIVE-VAR

; Under the name of the stobj live variable, e.g., *the-live-st*, we
; store the name of the stobj, e.g., ST.

(defun pseudo-stobj-live-varp (sym val)
  (declare (ignore sym))
  (pseudo-function-symbolp val nil))

;-----------------------------------------------------------------
; STOBJS-IN

; To be exact, val should be in 1:1 correspondence with the FORMALS of the fn
; sym and have NILs in the slots corresponding to non-stobjs and the
; appropriate stobj name in the stobj slots.

(defun pseudo-stobjs-inp (sym val)
  (declare (ignore sym))
  (symbol-listp val))

;-----------------------------------------------------------------
; STOBJS-OUT

; The len of stobjs-out is the output arity of the function sym and should have
; nils in the non-stobj slots and the appropriate stobj names in the stobj
; slots.  Those stobj names should be listed in the stobjs-in of sym too.

(defun pseudo-stobjs-outp (sym val)
  (declare (ignore sym))
  (symbol-listp val))

;-----------------------------------------------------------------
; SYMBOL-CLASS

(defun symbol-classp (sym val)
  (declare (ignore sym))
  (member-eq val '(:PROGRAM :IDEAL :COMMON-LISP-COMPLIANT)))

;-----------------------------------------------------------------
; TABLE-ALIST

(defun table-alistp (sym val)
  (declare (ignore sym))
  (alistp val))

;-----------------------------------------------------------------
; TABLE-GUARD

(defun pseudo-table-guardp (sym val)
  (declare (ignore sym))
  (pseudo-termp val))

;-----------------------------------------------------------------
; TAU-PAIR
; TAU-PAIR-SAVED

; This was taken care of when we defined the NEG-IMPLICANTS property.

;-----------------------------------------------------------------
; THEOREM

(defun pseudo-theoremp (sym val)
  (declare (ignore sym))
  (pseudo-termp val))

;-----------------------------------------------------------------
; THEORY

(defun pseudo-theoryp (sym lst)
  (declare (ignore sym))
  (pseudo-theoryp1 lst))

;-----------------------------------------------------------------
; TYPE-PRESCRIPTIONS

(verify-termination backchain-limit-listp) ; and guards

(defun pseudo-type-prescriptionp (x)
  (case-match x
    ((basic-ts (nume . term)
               (hyps . backchain-limit-lst)
               (vars . rune)
               . corollary)
     (and (type-setp basic-ts)
          (or (null nume)
              (pseudo-numep nume))
          (pseudo-termp term)
          (pseudo-term-listp hyps)
          (or (null backchain-limit-lst)
              (and (backchain-limit-listp backchain-limit-lst)
                   (equal (length backchain-limit-lst)
                          (length hyps))))
          (symbol-listp vars)
          (pseudo-runep rune)
          (pseudo-termp corollary)))
    (& nil)))

(defun pseudo-type-prescription-listp (x)
  (cond ((atom x) (null x))
        (t (and (pseudo-type-prescriptionp (car x))
                (pseudo-type-prescription-listp (cdr x))))))

(defun pseudo-type-prescriptionsp (sym val)
  (declare (ignore sym))
  (pseudo-type-prescription-listp val))

;-----------------------------------------------------------------
; UNEVALABLE-BUT-KNOWN

(defun pseudo-unevalable-but-knownp (sym val)
  (declare (ignore sym))
  (cond ((atom val) (equal val nil))
        (t (and (consp (car val))
                (booleanp (cdr (car val)))
                (pseudo-unevalable-but-knownp nil (cdr val))))))

;-----------------------------------------------------------------
; UNNORMALIZED-BODY

(defun unnormalized-bodyp (sym val)
  (declare (ignore sym))
  (pseudo-termp val))

;-----------------------------------------------------------------
; UNTRANSLATED-THEOREM

(defun untranslated-theoremp (sym val)

; The form of an untranslated theorem is quite arbitrary, because of macros.

  (declare (ignore sym))
  (or (atom val)
      (true-listp val)))

; -----------------------------------------------------------------

; *ACL2-property-unbound*

; In this section I discuss *acl2-property-unbound*.  This property value
; caused me grief in the initial attempts to formalize the event-index property
; I proved.  So I investigated that property value and here record some
; important findings, only one of which is reflected in the definition of
; good-worldp below.

; At first I thought I might cope with *acl2-property-unbound* by ``cleansing''
; the world of it before checking good-worldp: wiping out any shadowed property
; values.  But if the world has been cleansed, then the worlds I find in the
; event indices are not tails of it!  Furthermore, cleansing them will not
; produce tails!

; Shadowing ``on the fly'' is probably the way to go.  That is what our own
; code does, as with actual-props and new-trips.  If this issue becomes
; critical, I'd recommend taking the view that a world is really a pair
; consisting of a list of triples and some shadowing, the latter being a list
; of symbol-property pairs that are now unbound.  That is essentially our
; definitional style in the code, when we can't just ignore the issue locally.

; Here are some observations about the unbound property, confirmed by
; code-walks.  These might be useful in future additions to good-worldp or in
; proofs.

; *ACL2-property-unbound* is only stored by renew-name.  One argument to that
; function is renewal-mode, which must be :erase, :overwrite or
; :reclassifying-overwrite), The only time :reclassifying-overwrite is the
; renewal-mode is when a :program function is being reclassified to an
; identical-defp :logic function.

; When a name has been redefined for any reason, a REDEFINED property is stored.

; Renew-name is called only by chk-redefineable-namep.  That function takes a
; reclassifyingp flag.  If reclassifyingp is non-nil and not a consp message
; (see redundant-or-reclassifying-defunp) then we know that in fact this new
; definition is just a conversion of the existing definition.

; Chk-redefineable-namep is called only by chk-just-new-name.

; chk-just-new-name is called by every event function.  The reclassifyingp
; argument is always nil except in chk-acceptable-defuns1.
; The value there is set by redundant-or-reclassifying-defunsp

; Conclusion: I believe it is safe to assume that, unless redefinition has been
; permitted, the only time we'll see *acl2-property-unbound* in a legal world
; is when it is part of the reclassifying of a :program mode function to :logic
; mode.

; It then becomes relevant to ask what properties might become unbound in a
; legal world?

; Renew-name will not unbind any GLOBAL-VALUE and cites explitly the bad
; consequences of messing with COMMAND-LANDMARKs.  So we can rule out unbound
; being a value of EVENT-INDEX (and all other world globals) ``locally'' in
; good-worldp.

; One might think (naively after 8 years absence) that there are no unbound
; properties in the bootstrap world.  Wrong.

; I think that the only ACL2 properties that are ever unbound in a good world
; (barring use of :REDEF) are those in the list below.  These come from
; verify-termination or verify-guards or the bootstrap process itself.

; This code, executed in raw Lisp, will print the unbound properties of the world,
; other than those explicitly identified below.  The comments interspersed in
; the list of properties below explain how it is these properties come to be
; unbound in the V3.6.1 bootstrap world.

#|
(loop for x in (w state) as i from 1 always
      (if (eq (cddr x) *acl2-property-unbound*)
          (if (member-eq (cadr x)
                         '(
; The only properties that ever get unbound are ones that got set in the first place.
; It is obvious that the following properties can be set by :program mode defuns:

                           SYMBOL-CLASS
                           STOBJS-OUT
                           STOBJS-IN
                           GUARD
                           FORMALS
                           ABSOLUTE-EVENT-NUMBER
                           UNNORMALIZED-BODY

; The following property is set by primordial-event-macro-and-fn for
; ld-skip-proofsp and default-defun-mode-from-state.  (Def-bodies is also set
; for other primitives, like skip-when-logic and include-book-fn, but they
; remain in :program mode and so the setting isn't shadowed out.)

                           DEF-BODIES

; The following property is set by primordial-world for o-p and o-<, however,
; only o-p is subsequently reclassified from :program to :logic

                           TYPE-PRESCRIPTIONS

; We expect a 'classicalp property to be non-nil only in ACL2(r).  It seems
; appropriate to allow classicalp to be unbound, given its inclusion in the
; code for renew-name/overwrite.

                           #+:non-standard-analysis
                           CLASSICALP))
              t

; This print statement will print any unbound property not listed above.  The i is
; the index you type to (walkabout (w state) state) to see the property in full.

              (print (list i (car x) (cadr x))))
          t))
|#

; -----------------------------------------------------------------
; Putting It All Together

(defun pseudo-good-world-triplep (trip w redefp)

; We check that trip is a legal world trip to cons onto world w.  We don't know
; yet that w really is legal but it presumed so.  Redefp controls how strict we
; are when an unbound property is discovered.  (Allowing redefinition may cause
; unsoundness, but we might still wish to verify the guards of our system.)
; Some properties come unbound even in normal, sound usage of the system, as by
; verify-termination, even when :redef has never been allowed.  So we must
; distinguish between those ``expected'' occurrences of unbound properties and
; those that could happen as a result of possibly unsound :redef.  If redefp is
; non-nil, we allow any property to be unbound.  If redefp is nil, we allow
; only expected unbound properties.

  (declare (xargs :guard (plist-worldp w)))

  (cond
   ((and (consp trip)
         (symbolp (car trip))
         (consp (cdr trip))
         (symbolp (cadr trip)))
    (let ((sym (car trip))
          (prop (cadr trip))
          (val (cddr trip)))
      (cond
       ((and redefp
             (eq val *acl2-property-unbound*))
        t)
       (t
        (case prop
          (ABSOLUTE-EVENT-NUMBER
           (or (eq val *acl2-property-unbound*)
               (absolute-event-numberp sym val)))
          (ABSSTOBJ-INFO (absstobj-infop val))
          (ACCESSOR-NAMES (accessor-namesp sym val))
          (ATTACHMENT (attachment-propertyp sym val))
          (BIG-SWITCH (pseudo-big-switchp sym val))
          (TAU-BOUNDERS-FORM-1 (pseudo-tau-boundersp sym val))
          (TAU-BOUNDERS-FORM-2 (pseudo-tau-boundersp-listp sym val))
          (CLASSES (classesp sym val))
          (CLASSICALP (or (eq val *acl2-property-unbound*)
                          (classicalpp sym val)))
          (CLAUSE-PROCESSOR (clause-processorp sym val))
          (COARSENINGS (coarseningsp sym val))
          (CONCRETE-STOBJ (concrete-stobjp sym val))
          (CONGRUENCES (congruencesp sym val))
          (CONGRUENT-STOBJ-REP (congruent-stobj-repp sym val))
          (CONST (const-propertyp sym val))
          (CONSTRAINEDP (pseudo-constrainedpp sym val))
          (CONSTRAINT-LST (constraint-lstp sym val))
          (DEF-BODIES
            (or (eq val *acl2-property-unbound*)
                (pseudo-def-bodiesp sym val)))
          (DEFAXIOM-SUPPORTER (defaxiom-supporterp sym val))
          (DEFCHOOSE-AXIOM (pseudo-defchoose-axiomp sym val))
          (ELIMINATE-DESTRUCTORS-RULE
           (pseudo-eliminate-destructors-rulep sym val))
          (FORMALS
           (or (eq val *acl2-property-unbound*)
               (pseudo-formalsp sym val)))
          (FORWARD-CHAINING-RULES (pseudo-forward-chaining-rulesp sym val))
          (GLOBAL-VALUE
           (and (not (eq val *acl2-property-unbound*))
                (pseudo-global-valuep sym val w)))
          (GUARD
           (or (eq val *acl2-property-unbound*)
               (pseudo-guardp sym val)))
          (HEREDITARILY-CONSTRAINED-FNNAMES
           (pseudo-hereditarily-constrained-fnnamesp sym val))
          (INDUCTION-MACHINE (pseudo-induction-machinep sym val))
          (INDUCTION-RULES (pseudo-induction-rulesp sym val))
          (INVARIANT-RISK (or (eq val *acl2-property-unbound*)
                              (pseudo-invariant-riskp sym val)))
          (JUSTIFICATION (pseudo-justificationp sym val))
          (LABEL (labelp sym val))
          (LEMMAS (pseudo-lemmasp sym val))
          (LEVEL-NO (level-nop sym val))
          (LINEAR-LEMMAS (pseudo-linear-lemmasp sym val))
          (LOOP$-RECURSION (loop$-recursionp sym val))
          (MACRO-ARGS (pseudo-macro-argsp sym val))
          (MACRO-BODY (pseudo-macro-bodyp sym val))
          (NEG-IMPLICANTS (pseudo-neg-implicantsp sym val))
          (NON-EXECUTABLEP (or (eq val *acl2-property-unbound*) ; upgrade proxy
                               (non-executablepp sym val)))
          (NON-MEMOIZABLE (non-memoizablep sym val))
          (PEQUIVS (pequivsp sym val))
          (POS-IMPLICANTS (pseudo-pos-implicantsp sym val))
          (PREDEFINED (or (eq val *acl2-property-unbound*) ; upgrade defproxy
                          (predefinedp sym val)))
          (PRIMITIVE-RECURSIVE-DEFUNP (primitive-recursive-defunpp sym val))
          (QUICK-BLOCK-INFO (pseudo-quick-block-infop sym val))
          (RECOGNIZER-ALIST (pseudo-recognizer-alistp sym val))
          (RECURSIVEP (pseudo-recursivepp sym val))
          (REDEFINED (redefinedp sym val))
          (RUNIC-MAPPING-PAIRS (pseudo-runic-mapping-pairsp sym val))
          (SIBLINGS (siblings-propertyp sym val))
          (SIGNATURE-RULES-FORM-1
           (pseudo-signature-rules-form-1p sym val))
          (SIGNATURE-RULES-FORM-2
           (pseudo-signature-rules-form-2p sym val))
          (SPLIT-TYPES-TERM
           (or (eq val *acl2-property-unbound*)
               (pseudo-split-types-termp sym val)))
          (STOBJ (pseudo-stobjp sym val))
          (STOBJ-CONSTANT (pseudo-stobj-constantp sym val))
          (STOBJ-FUNCTION (pseudo-stobj-functionp sym val))
          (STOBJ-LIVE-VAR (pseudo-stobj-live-varp sym val))
          (STOBJS-IN
           (or (eq val *acl2-property-unbound*)
               (pseudo-stobjs-inp sym val)))
          (STOBJS-OUT
           (or (eq val *acl2-property-unbound*)
               (pseudo-stobjs-outp sym val)))
          (SYMBOL-CLASS
           (or (eq val *acl2-property-unbound*)
               (symbol-classp sym val)))
          (TABLE-ALIST (table-alistp sym val))
          (TABLE-GUARD (pseudo-table-guardp sym val))
          (TAU-PAIR (pseudo-tau-pairp sym val))
          (TAU-PAIR-SAVED (pseudo-tau-pairp sym val))
          (THEOREM (pseudo-theoremp sym val))
          (THEORY (pseudo-theoryp sym val))
          (TYPE-PRESCRIPTIONS
           (or (eq val *acl2-property-unbound*)
               (pseudo-type-prescriptionsp sym val)))
          (UNEVALABLE-BUT-KNOWN (pseudo-unevalable-but-knownp sym val))
          (UNNORMALIZED-BODY
           (or (eq val *acl2-property-unbound*)
               (unnormalized-bodyp sym val)))
          (UNTRANSLATED-THEOREM (untranslated-theoremp sym val))
          (otherwise nil))))))
   (t nil)))

; -----------------------------------------------------------------

(defmacro bad-world! (ctx str &rest args)
  `(prog2$ (cw "~%~%Bad World detected by ~x0:  ~@1~%~%"
               ,ctx
               (msg ,str ,@args))
           nil))

(defun pseudo-good-worldp2 (pos w redefp)

; This function takes pos just for error reporting reasons.  But it messes up
; inductive proofs and so I define a version that is free of pos.

  (declare (xargs :guard (and (natp pos) (plist-worldp w))))
  (cond
   ((atom w)
    (null w))
   ((pseudo-good-world-triplep (car w) (cdr w) redefp)
    (pseudo-good-worldp2 (+ 1 pos) (cdr w) redefp))
   (t (bad-world! 'pseudo-good-worldp2
                  "(nth ~x0 ...) is an illegal triple."
                  pos))))

(defun pseudo-good-worldp1 (w redefp)
  (declare (xargs :guard (plist-worldp w)))
  (cond
   ((atom w)
    (null w))
   ((pseudo-good-world-triplep (car w) (cdr w) redefp)
    (pseudo-good-worldp1 (cdr w) redefp))
   (t nil)))

(defthm pseudo-good-worldp2-is-pseudo-good-worldp1
  (equal (pseudo-good-worldp2 pos w redefp)
         (pseudo-good-worldp1 w redefp))
  :hints (("Goal" :in-theory (disable pseudo-good-world-triplep))))

; This is also useful.

(local
 (defthm sgetprop-is-fgetprop
   (equal (sgetprop sym prop dv wname w)
          (fgetprop sym prop dv w))))

; -----------------------------------------------------------------

; In this next section I define a bunch of global structuring concepts related
; to the distribution of events and commands and their indices.

(defun good-command-blocksp1 (pos just-entered-command-blockp no-event-landmark-yetp w)
  (declare (xargs :guard (and (natp pos)
                              (plist-worldp w))))
  (cond ((atom w) t)
        (t (let ((sym (car (car w)))
                 (prop (cadr (car w)))
                 (val (cddr (car w))))
             (cond ((and (eq sym 'command-landmark)
                         (eq prop 'global-value))
                    (cond
                     (no-event-landmark-yetp
                      (bad-world! 'good-command-blocksp1
                                  "Violation of the command blocks invariant, ~
                                   specifically that every block contain at ~
                                   least one EVENT-LANDMARK, was detected at ~
                                   triple ~x0."
                                  pos))
                     (t (good-command-blocksp1 (+ 1 pos)
                                               t
                                               t
                                               (cdr w)))))
                   ((and (eq sym 'command-index)
                         (eq prop 'global-value))
                    (cond
                     ((or just-entered-command-blockp
                          (null val))
                      (good-command-blocksp1 (+ 1 pos)
                                             nil
                                             no-event-landmark-yetp
                                             (cdr w)))

                     (t (bad-world! 'good-command-blocksp1
                                    "Violation of the command blocks ~
                                     invariant, specifically that every ~
                                     COMMAND-INDEX (except the initializing ~
                                     one) appear immediately after a ~
                                     COMMAND-LANDMARK, was detected at triple ~
                                     ~x0."
                                    pos))))
                   ((and (eq sym 'event-landmark)
                         (eq prop 'global-value))
                    (good-command-blocksp1 (+ 1 pos)
                                           nil
                                           nil
                                           (cdr w)))
                   (t (good-command-blocksp1 (+ 1 pos)
                                             nil
                                             no-event-landmark-yetp
                                             (cdr w))))))))

(defun good-command-blocksp (w)

; Every COMMAND-INDEX should immediately follow a COMMAND-LANDMARK
; Every COMMAND-LANDMARK must have an EVENT-LANDMARK before the next COMMAND-LANDMARK

  (declare (xargs :guard (plist-worldp w)))
  (good-command-blocksp1 0 nil nil w))

(defun sequential-event-landmarksp1 (pos n w)
  (declare (xargs :guard (and (natp pos)
                              (plist-worldp w))))
  (cond ((atom w)
         (if (equal n -2)
             (eq w nil)
             (bad-world! 'sequential-event-landmarksp1
                         "When we reached the end of the world, n was ~x0 ~
                          instead of -2."
                         n)))
        ((and (eq (car (car w)) 'event-landmark)
              (eq (cadr (car w)) 'global-value))
         (if (equal n (safe-access-event-tuple-number (cddr (car w))))
             (sequential-event-landmarksp1 (+ 1 pos) (- n 1) (cdr w))
             (bad-world! 'sequential-event-landmarksp
                         "Item ~x0 was supposed to be EVENT-LANDMARK ~x1 but ~
                          actually has number ~x2."
                         pos
                         n
                         (safe-access-event-tuple-number (cddr (car w))))))
        (t (sequential-event-landmarksp1 (+ 1 pos) n (cdr w)))))

(defun sequential-event-landmarksp (w)
  (declare (xargs :guard (plist-worldp w)))
  (sequential-event-landmarksp1 0
                                (safe-access-event-tuple-number
                                 (fgetprop 'event-landmark 'global-value nil w))
                                w))

(defun sequential-command-landmarksp1 (pos n w)
  (declare (xargs :guard (and (natp pos)
                              (plist-worldp w))))
  (cond ((atom w)
         (if (equal n -2)
             (eq w nil)
             (bad-world! 'sequential-command-landmarksp1
                         "When we reached the end of the world, n was ~x0 ~
                          instead of -2."
                         n)))
        ((and (eq (car (car w)) 'command-landmark)
              (eq (cadr (car w)) 'global-value))
         (if (equal n (safe-access-command-tuple-number (cddr (car w))))
             (sequential-command-landmarksp1 (+ 1 pos) (- n 1) (cdr w))
             (bad-world! 'sequential-command-landmarksp1
                         "Item ~x0 was supposed to be COMMAND-LANDMARK ~x1 ~
                          but actually has number ~x2."
                         pos
                         n
                 (safe-access-command-tuple-number (cddr (car w))))))
        (t (sequential-command-landmarksp1 (+ 1 pos) n (cdr w)))))

(defun sequential-command-landmarksp (w)
  (declare (xargs :guard (plist-worldp w)))
  (sequential-command-landmarksp1 0
                                (safe-access-command-tuple-number
                                 (fgetprop 'command-landmark 'global-value nil w))
                                w))

; FYI: If you count the event-landmarks between the event-indices (or
; analogously for commands), you get a sequence like this: (8 10 10 10 ... 10
; 10 1 1).  The 10 is the *event-index-interval*.  The 8 in this example is, in
; general, some natural number less than the interval.  The two 1's at the very
; end require some explaining!  The last 1 (the one that was stored
; chronologically first) is the assignment of -1 to event-landmark global-value
; in primordial-world-globals.  Also in primordial-world-globals, and after the
; assignment of event-landmark, we initialize event-index to nil.  So that
; creates a world like this: ((EVENT-INDEX global-value . nil) ...
; (EVENT-LANDMARK global-value . (-1 ...))  ...)  At this point the
; absolute-event-number is -1.  The first official event we carry out is
; ENTER-BOOT-STRAP-MODE, which gets event number 0.  Since that is a multiple
; of the event index interval, we lay down another EVENT-INDEX, containing just
; one event landmark.  So that EVENT-INDEX triple is: (EVENT-INDEX global-value
; . (0 (....))).  That 0 is the marker that says we've reached the primordial
; world.

; We know from event-indexp that the current event-landmark at every non-empty
; event-index is a multiple of *event-index-interval*.  We know from
; sequential-event-landmarksp that the landmarks are sequential, starting from
; -1.  Thus, I believe the periodic pattern of indices can be deduced and do
; not specify it.

(defun pseudo-good-worldp (w redefp)
  (and (plist-worldp w)
       (pseudo-good-worldp2 0 w redefp)
       (sequential-event-landmarksp w)
       (sequential-command-landmarksp w)
       (good-command-blocksp w)))

(defmacro chk-pseudo-good-worldp (book-name)

; This macro is used by the %.bkchk make target in books/Makefile.

  `(let ((passed-p (pseudo-good-worldp (w state) nil)))
     (pprogn (newline *standard-co* state)
             (princ$ "Pseudo-good-worldp check for including \""
                     *standard-co* state)
             (princ$ ,book-name *standard-co* state)
             (princ$ (cond (passed-p "\" passed.")
                           (t        "\" failed."))
                     *standard-co* state)
             (newline *standard-co* state)
             (mv (not passed-p) :invisible state))))
