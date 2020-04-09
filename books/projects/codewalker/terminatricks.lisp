; Copyright (C) 2014, ForrestHunt, Inc.
; Written by J Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; (ld "terminatricks.lisp" :ld-pre-eval-print t)
; (certify-book "terminatricks")
; A New Approach to Terminatricks
; J Strother Moore
; Edinburgh, St Andrews
; January, 2014

; =================================================================

; Abstract

; At the highest level, this book implements three basic ideas and then
; implements DEFUNM.  Each is described in a separate Chapter

; * 1: Guessing Measures
;   We use a ``measure patterns'' table to guess measures for recursive
;   functions, including the ability to invent lexicographic combinations a la
;   Boyer-Moore 1979 and a newer facility to assign weights to flags used to
;   control mutually-recursive functions coded as flagged singly-recursive
;   functions.

; * 2:  Learning from User-Supplied Measures
;   We learn from DEFUNs with explicit :measures supplied by the user,
;   extending our measure patterns table by paring down the user's induction
;   machine so that it only mentions those tests necessary to prove the measure
;   conjecture and implementing a notion of subsumption among patterns so that
;   the database is not cluttered with duplications.

; * 3: Generating Non-Recursive Flag Lemmas
;   We support the option of proving automatically generated ``non-recursive
;   flag lemmas'' so that if the admission of a function involves a flag, and
;   one of the flag values just passes the buck to the others -- e.g., one of
;   the functions in the clique is just an eliminable abbreviation for calls on
;   the others -- we generate and prove lemmas that rewrite such non-recursive
;   calls away.

; * 4: DEFUNM
;   We put the three main ideas together in a utility called DEFUNM, which
;   presents itself to the user like DEFUN except it has room after the formals
;   for an :OPTIONS specification.  DEFUNM uses make-event, since it must
;   access state.  DEFUNM becomes DEFUN if the user specifies a measure in the
;   declarations.  Otherwise, it computes the updates to the measure patterns
;   table via the techniques in Chapter 2, then it guesses a measure via
;   Chapter 1, and then, if the :option so specifies it generates any
;   non-recursive flag lemmas available.  It then assembles the results into a
;   PROGN that stores the new measure-patterns, admits the defun with the
;   guessed measure, and proves the flag lemmas.  DEFUNM comes in two flavors,
;   the ordinary one and DEFUNM-NX which introduces non-executable definitions.

; We further discuss each of these four topics in a section each before
; descending into code.  The code is divided into these same three chapters.
; So you will see, for example: ``Chapter 1 (Discussion)'' and ``Chapter 1
; (Code)'' below.  But we do all three discussions before the codes.

; This book has some TODO suggestions in it.

; =================================================================

; Chapter 1 (Discussion): Guessing Measures

;   Chapter Summary: We use a ``measure patterns'' table to guess measures for
;   recursive functions, including the ability to invent lexicographic
;   combinations a la Boyer-Moore 1979 and a newer facility to assign weights
;   to flags used to control mutually-recursive functions coded as flagged
;   singly-recursive functions.

; -----------------------------------------------------------------
; Section: Virtual Formals and Proto Distilled Machines

; A ``virtual formal,'' or ``vformal,'' is a component of a formal, given by an
; expression in that formal.  For example, (nth 7 st) is a virtual formal that
; is changed in a recursion in which st is replaced by (update-nth 7 new-val
; st).  An important property of virtual formals is that they're orthogonal
; (independent): changing one does not change another.  Thus, if (nth 7 (locals
; st)) and (nth 8 (locals st)) are virtual formals, then (locals st) should not
; be so considered.

; Two tables drive the identification of virtual formals:

; generalized-updater-drivers -- establishes the relation between updaters and
;                                accessors

; constructor-drivers -- establishes the relation between constructors and
;                                accessors

; When attempting to find a measure for a proposed function definition, we work
; in terms of virtual formals.

; Since we cannot easily code vformals positionally, we convert each call to a
; list of ``slot'' expressions, (:SLOT vformal new-val).  We convert a
; termination machine into a ``proto distilled machine,'' or ``pdmach'', in
; order to look for plausible measures.  A proto distilled machine is a list of
; pairs, each pair, (tests . call), corresponding to a line of the termination
; machine except that the call has been replaced by a list of the slots
; changed.  Pdmachs are built by make-proto-distilled-machine .

; By the way, this code exploits the fact that basic ACL2 utilities like
; one-way-unify, subsumption, substitution, etc., ``work'' on such pseudo-terms
; as (:SLOT V (CDR V)) or (NTH I :BASE), e.g., ``terms'' where keywords may
; appear in function or variable symbol positions.

; -----------------------------------------------------------------
; Section: Plausible Measures, Measure Suggestions, and Distilled Machines

; To find plausible measures, we look for patterns in the tests and slots of
; the pdmach.  For example, finding (not (zp (nth 7 st))) among the tests and
; (update-nth 7 (- (nth 7 st) 1) st) among the slots suggests the measure
; (acl2-count (nth 7 st)).  But this heuristic search is based on a database
; of measure-pattern (q.v.) which are record structures that basically list
; tests and/or slots that trigger the suggestion of a given measure.  The list
; of available measure-patterns is stored in a table named measure-patterns,
; initialized in this file.  (It is this table that we extend by noting
; user-supplied :measures, as described once we finish describing how we guess
; measures.)

; The ``match'' process in which we trigger measure patterns based on terms
; that occur in the pdmach, not only generates an allegedly plausible measure,
; it generates a score or ``rank'' for each suggested measure and when multiple
; lines suggest the same measure, their ranks are added.  So the higher the
; rank, the better.

; The function initial-dmach-and-measure-suggestions (q.v.) takes the
; function's termination machine and generates the pdmach.  Then it
; heuristically searches pdmach and generates a list of ranked measure
; suggestions, which it sorts so that the highest ranking measures are listed
; first.  Then it converts the pdmach into a ``distilled machine'' or ``dmach''
; in which we will store a lot of additional information about each line.  It
; then returns the dmach and rank ordered list of suggestions.

; To hold the additional information about each line, we introduce a
; ``distilled line'' or ``dline'' (q.v.).  Each dline is a record that stores
; the tests and slots verbatim from the pdmach, a sublis-expr-style
; substitution pairing vformals with their new values (recapitulating the slots
; but more convenient for some operations), a list (initially empty) of
; validated or ``stamped'' ``measure-suggestion'' (or ``mesug'') as explained
; next, and certain information about the machine's possible use of a ``flag
; vformal'' which we discuss among the subtleties below.

; The measure-suggestions of a dline is list of measure-suggestion (q.v.) or
; ``mesug'' records one for each measure suggested.  Inside the mesug we record
; the ``rank'' of its suggestion (e.g., how often and how well it matched the
; patterns that inspired its suggestion), the measure itself, a ``stamp''
; indicating what we learned (by proof) about the measure on this line, and the
; name of the patterns that suggested this measure.  The stamp is <, <=, or
; POSSIBLY-GROWING.  To stamp a measure suggestion for a given line we generate
; the obvious measure conjecture (the tests of the dline imply the measure
; decreases, either strongly or weakly, under the sublis-expr substitution).
; If we can't prove either strength, we stamp it POSSIBLY-GROWING.

; When we first build the dmach, the list of measure suggestions in each dline
; is empty.  Then, in rank order of the plausible measures, we add stamped
; measures to each dline, by attempting to prove the corresponding measure
; conjecture for each line.

; -----------------------------------------------------------------
; Section: Interleaving Stamping and Finding Lexicographic Measures

; Every time we finish analyzing the behavior of a measure across all of the
; lines, we ask whether we can piece together a lexicographic measure
; explaining the machine.  We try to assemble all possible lexicographic
; measures to eliminate (justify) as many dlines as possible.  The basic idea
; is to find measures that definitely decrease on some line and never increase,
; consider each such measure as the most significant in a lex order, delete all
; the lines from the dmach on which that measure decreases and delete that
; measure from all remaining lines, and recur with the reduced machine.  If we
; can justify all the lines (reach the empty machine), we quit and win with
; that measure.  If not (and ignoring the subtlety below), we repeat -- taking
; the next highest ranking measure, adding its behavior to every line, look for
; lex, etc).

; We fail if we run out of suggestions before we find a lexicographic measure
; explaining all the lines.

; -----------------------------------------------------------------
; Section:  Weighing Flags

; The subtlety mentioned above concerns the possibility that the meachine is
; the flagged encoding of a mutually recursive clique.  This is determined if
; there is a virtual formal that is tested with equality against constants in
; every line and is always either unchanged or changed to a constant.  From
; these constraints we can determine the range (set of constant values) the
; flag may take on, the ``incoming value'' of the flag on each line (possibly a
; subset of the range as happens when the tests identifying the flag are
; negative equalities, i.e., the flag is not 'TERM and thus is either
; 'TERM-LIST or 'COND-EXPR), and the outgoing value of the flag on each line.

; Thus, in addition to each dline containing the tests, the slots, the
; substitution, and a list of stamped measure suggestions, each dline contains
; the flag vformal for the whole machine (or nil if there is none), an alist
; mapping each incoming flag value for the line to the list of all outgoing
; flag values for that line (typically a singleton but could be a set of all
; the flag values not excluded by the foregoing tests), and an alist mapping
; the incoming flag values to the very test used to identify that value on this
; line.

; We don't let the flag vformal, if any, participate in the suggestion of
; measures.  For example, a numerically valued flag, e.g., a program counter,
; might be compared to some fixed upper bound to enforce some good state
; invariant about the pc being in bounds, and could suggest a ``counting up''
; style measure.

; Also, if after we've pieced together a lexicographic measure for as many
; dlines as possible we're still left with some ``unjustified'' lines and those
; lines have a flag vformal, we attempt to assign weights to the incoming flag
; values.  For example, the flag 'TERM transitions to 'TERM-LIST and the flag
; 'TERM-LIST transitions to both 'TERM and 'TERM-LIST, then we assign 'TERM
; value 2 and 'TERM-LIST value 1.

; This completes our sketch Chapter 1.

; =================================================================

; Chapter 2 (Discussion):  Learning from User-Supplied Measures

;   Chapter Summary: We learn from user-supplied DEFUNs with explicit :measures
;   supplied by the user, extending our measure patterns table by paring down
;   the user's induction machine so that it only mentions those tests necessary
;   to prove the measure conjecture and implementing a notion of subsumption
;   among patterns so that the database is not cluttered with duplications.

; We now turn to the problem of updating the measure-patterns database.  The
; idea is that the main way the database will grow is from user-supplied
; DEFUNs with explicit :MEASUREs.  A typical scenario is that the user submits
; a DEFUNM and we fail to generate the right measure.  So the user changes the
; DEFUMN to a DEFUN with an explicit :measure and goes on.  We want the
; measure-patterns table to grow as a result of this user-interaction so that
; DEFUNM will guess the right measure in the future for that ``new'' recursion
; scheme.

; Ideally, DEFUN itself would update the measure pattern table.  But since it is an
; ACL2 system primitive we can't change it.

; Our solution is for DEFUNM to update the table before it starts generating
; suggestions.  It sweeps the world back to the last time the table was updated
; and collects user-supplied measures, analyzes them, and possibly stores
; corresponding measure-patterns in the table.

; This is actually quite complicated because we wish to keep the table small by
; (a) throwing out anything from the induction machine that is not relevant to
; the measure proof, and (b) detecting when an about-to-be-added pattern
; subsumes or is subsumed by an existing pattern.  We deal with updating the
; measure-patterns table only at the end of the development of everything else!

; We pare down the original induction-machine by trying to prove stronger and
; stronger measure lemmas by successively eliminating tests that might be
; irrelevant.  This is not done for the measure conjecture for the entire
; machine but line-by-line, independently.  We actually do this paring down in
; two steps.  First we produce a ``syntactically bare-essentials machine'' --
; with the function syntactically-bare-essentials-machine (q.v.) -- which
; throws out tests based on cliques of variables used.  If a test does not
; involve at least one of the variables used in the measure, it is irrelevant
; (unless the conjunction of the tests is contradictory and the recursion can't
; be taken).  Then, given a syntactically bare machine, we further pare it down
; by successively proving the required measure theorem under fewer and fewer of
; the available hypotheses.  This is done by bare-essential-machine (q.v.).

; Having identified a subset of the available hyps sufficient to prove the
; measure conjecture for the line, we manufacture a measure pattern from it and
; add the pattern to the measure-patterns database.  To add a new pattern to the
; table we check for a style of ``pattern subsumption'' in both directions to
; keep the table subsumption free.  See measure-pattern-subsumes and
; update-measure-patterns.

; By the way, a minor distraction on the way to the latter is the
; implementation of four levels of verbosity in describing the change wrought
; on the table: say nothing or describe deletions, additions, and preservations
; in terms of just the number of such actions, the names of the patterns
; involved, or the patterns themselves.

; =================================================================

; Chapter 3 (Discussion): Adding Non-Recursive Flag Lemmas

;   Chapter Summary: We support the option of proving automatically generated
;   ``non-recursive flag lemmas'' so that if the admission of a function
;   involves a flag, and one of the flag values just passes the buck to the
;   others -- e.g., one of the functions in the clique is just an eliminable
;   abbreviation for calls on the others -- we generate and prove lemmas that
;   rewrite such non-recursive calls away.

; If the distilled machine contains a flag and, whenever that flag is among the
; incoming flag values of a dline it is NOT among the outgoing flag values on
; that same line, then that flag value is ``non-recursive'' (it just passes the
; buck to other flag values).  So we can prove a lemma about a general call on
; that value.  To generate the theorem, we will use simplify-under-hyps (see
; the book of that name).  However, we add such lemmas only if the user
; requests it by including :non-rec-flag-lemma among the DEFUNM :options.

; Complication: Pc=2 may pass the buck to pc=10 which may pass the buck to
; pc=2.  Both appear ``non-recursive.''  But if pc=2 is made into a rule, then
; pc=10 better not be!  Of course, we could make pc=10 a rule instead of pc=2.
; So there is arbitrariness in preferring the first non-recursive flag we find,
; but so be it.

; This completes our general sketch of Terminatricks.  Below you will find code
; sections also demarcated by hyhens and a titles, but at a finer level of
; detail and relying implicitly on the background discussion above.

; =================================================================

(in-package "ACL2")
(program)
(set-state-ok t)

(include-book "simplify-under-hyps")

; =================================================================

; Chapter 1 (Code): Guessing Measures

;   Chapter Summary: We use a ``measure patterns'' table to guess measures for
;   recursive functions, including the ability to invent lexicographic
;   combinations a la Boyer-Moore 1979 and a newer facility to assign weights
;   to flags used to control mutually-recursive functions coded as flagged
;   singly-recursive functions.

; This chapter ultimately concludes with the definition of
; stamp-mesugs-and-search

; -----------------------------------------------------------------
; Section:  Call Graph Ordering

; This is a general utility for ordering a set of items according to
; dependency.  Codewalker will use it to process the clock and semantic DEFUNs
; in call graph order.  But Terminatricks also uses it to assign weights to
; flag vformal values.  Suppose we had a mutually recursive clique of 5
; functions numbered 1 through 5 and their calling relationships were: function
; 1 calls function 2, function 2 calls 3, 3 calls 4 and 5, 4 calls 2, and 5
; calls no other functions.  (Calls of a function to itself are not recorded.)
; We could represent this calling graph as:

; ((1 2) (2 3) (3 4 5) (4 2) (5)).

; Then how do we determine the order in which these five functions should be
; defined, or equivalently, what are the relative weights of flag values
; corresponding to these functions?  The answer: compute the reflexive,
; transitive closure of the calls graph to get a ``score'' for each function,
; the score being the reflexive transitive closure of its calls.  Then sort by
; subsetp on their respective scores.

; Instead of numbers, each ``function'' mentioned above is really a pc
; (whatever that is).  We compare them with lexorder.

; More on reflexive-transitive-closure when we get to that function.

(defun insert-no-dups (i lst)
  (cond ((endp lst) (list i))
        ((lexorder i (car lst))
         (if (equal i (car lst))
             lst
             (cons i lst)))
        (t (cons (car lst) (insert-no-dups i (cdr lst))))))

(defun insert*-no-dups (ilst lst)
  (cond ((endp ilst) lst)
        (t (insert*-no-dups (cdr ilst)
                            (insert-no-dups (car ilst) lst)))))

(defun reflexitate (graph)
  (cond ((endp graph) nil)
        (t (cons (cons (car (car graph))
                       (insert*-no-dups (car graph) nil))
                 (reflexitate (cdr graph))))))

(defun combine-if-intersectp (node1 reachable1 reachable2)
  (if (member-equal node1 reachable2)
      (insert*-no-dups reachable1 reachable2)
      reachable2))

(defun transitive-closure1 (node reachable graph)
  (cond ((endp graph) nil)
        (t (cons (cons (car (car graph))
                       (combine-if-intersectp node reachable (cdr (car graph))))
                 (transitive-closure1 node reachable (cdr graph))))))

(defun transitive-closure2 (lst graph)
  (cond ((endp lst) graph)
        (t (transitive-closure2
            (cdr lst)
            (transitive-closure1 (car (car lst)) (cdr (car lst)) graph)))))

(defun transitive-closure (graph)
  (let ((graph1 (transitive-closure2 graph graph)))
    (cond ((equal graph1 graph) graph)
          (t (transitive-closure graph1)))))

(defun reflexive-transitive-closure (graph)

; Graph is an alist with pairs of the form (a . lst), where a is some object
; denoting a node and lst is an lexordered list of all the nodes reachable from
; a.  We close it under reflexivity (a is reachable from a) and transitivity
; (if a is reachable from b and b is reachable from c, then a is reachable from
; c).

  (transitive-closure (reflexitate graph)))

; Recall the example problem above:

; ((1 2) (2 3) (3 4 5) (4 2) (5)).

; (reflexive-transitive-closure '((5 1) (1 2) (2 3 4) (3 1) (4)))
; = ((5 1 2 3 4 5)
;    (1 1 2 3 4)
;    (2 1 2 3 4)
;    (3 1 2 3 4)
;    (4 4))

; Clearly then, 4 is defined first, then 1, 2, and 3, and last is 5.  But wait!
; There's more.  Since 1, 2, and 3 have the same score, they are mutually
; recursive.

; Suppose we have two independent functions, say 6 and 7, each of which calls
; the same set of other functions, say (1 2 3 4).  Then are 6 and 7 mutually
; recursive?  No, because the score for 6 would be (1 2 3 4 6) and that for 7
; will be (1 2 3 4 7), they are incomparble, but must be defined after (1 2 3
; 4).

(defun insert-rtc-graph-into-buckets (item buckets)
  (cond ((endp buckets) (list (list item)))
        ((equal (cdr item) (cdr (car (car buckets))))
         (cons (cons item (car buckets)) (cdr buckets)))
        ((subsetp-equal (cdr item) (cdr (car (car buckets))))
         (cons (list item) buckets))
        (t (cons (car buckets)
                 (insert-rtc-graph-into-buckets item (cdr buckets))))))

(defun sort-rtc-graph-into-buckets (rtc-graph)
  (cond ((endp rtc-graph) nil)
        (t (insert-rtc-graph-into-buckets
            (car rtc-graph)
            (sort-rtc-graph-into-buckets (cdr rtc-graph))))))

; (sort-rtc-graph-into-buckets '((5 1 2 3 4 5)
;                                (1 1 2 3 4)
;                                (2 1 2 3 4)
;                                (3 1 2 3 4)
;                                (4 4)))
; =
; (((4 4))
;  ((1 1 2 3 4) (2 1 2 3 4) (3 1 2 3 4))
;  ((5 1 2 3 4 5)))

; Only the cars of the items in the bugets matter after sorting.  That is, we
; reduce the above to ((4) (1 2 3) (5)).

(defun strip-ordered-call-groups (lst)
  (cond ((endp lst) nil)
        (t (cons (strip-cars (car lst))
                 (strip-ordered-call-groups (cdr lst))))))

(defun call-graph-ordering (call-graph)
  (strip-ordered-call-groups
   (sort-rtc-graph-into-buckets
    (reflexive-transitive-closure call-graph))))

; -----------------------------------------------------------------
; Section: Virtual Formals -- Updaters and Constructors and their Accessors and Matching

; Updater drivers are each of the form (updater accessor), where each is a
; translated term except the keywords :value and :base play special roles: the
; first marks the slot where the new value assigned is passed and the second
; marks the slot where the original composite object resides.

(table generalized-updater-drivers
       :list
       '(((update-nth i :value :base) ; everybody uses update-nth/nth
          (nth i :base))
         ((s i :value :base)          ; for those who use the records book
          (g i :base))

         ))

; We treat :base recursively, looking for other updaters.  A nested term like
; (update-nth 1 new-pc (update-nth 3 new-regs st)) generates two virtual
; formals, (nth 1 st) and (nth 3 st).

; These terms need not be flat as they are above.  For example, we might have
; (set-loci i :value :base) with (nth i (locals :base)) as the accessor.  The
; user may set this table arbitrarily within the conventions above.  translated
; modulo the special use of keywords :value and :base.  However, components
; should be orthogonal.

; Similarly:

(table constructor-drivers
       :list
       '(((cons a b)
          (car :base) (cdr :base))))

; For example, the constructor-style definition of M1 would require:

;        ((make-state a b c d)
;         (pc :base) (locals :base) (stack :base) (program :base))

(defun find-first-instance (term comp doublets)

; Term is a term and comp is either the symbol CAR or CADR.  Doublets is a list
; of (x y) doublets, where x and y are each pseudo-terms (possibly involving
; keyword ``variables'' like :base and :value).  We find the first element of
; doublets, ele, whose comp component (CAR or CADR) matches term and return (mv
; t alist ele).  If no such element is found, we return (mv nil nil nil).

  (cond
   ((endp doublets) (mv nil nil nil))
   (t (mv-let
       (flg alist)
       (one-way-unify1 (if (eq comp 'car)
                           (car (car doublets))
                           (cadr (car doublets)))
                       term
                       nil)
       (cond
        (flg
         (mv t alist (car doublets)))
        (t (find-first-instance term comp (cdr doublets))))))))

(defun dig-to-btm (term drivers)
  (cond ((or (variablep term)
             (fquotep term))
         term)
        (t (mv-let
            (flg alist ele)
            (find-first-instance term 'car drivers)
            (declare (ignore ele))
            (cond
             (flg (dig-to-btm (cdr (assoc-eq :base alist)) drivers))
             (t term))))))

(defun delete-shadowed-slots (slots ans)

; Every element of slots is a ``term'' of the form (:SLOT base term).  We
; delete from slots every element that is preceded in the list by an element
; with the same base.

  (cond ((endp slots) (revappend ans nil))
        ((assoc-equal-cadr (cadr (car slots)) ans)
         (delete-shadowed-slots (cdr slots) ans))
        (t (delete-shadowed-slots (cdr slots) (cons (car slots) ans)))))

; Given an actual term, the base term, and the generalized updater drivers and
; constructor drivers, we compute the corresponding :slot expressions, e.g.,

; (changed-virtual-formal-slots
;  '(UPDATE-NTH '1 ONE                       ; updaters
;    (UPDATE-NTH '2 TWO                      ;  ...
;     (UPDATE-NTH '5 FIVE
;      (UPDATE-NTH '2 OLD-TWO                ;   ... [this one shadowed out]
;       (LOCALS ST)))))                      ; ``base''
;  '(LOCALS ST)                              ; = base
;
;  '(((update-nth i :value :base)            ; drivers
;     (nth i :base))
;    ((s i :value :base) (g i :base)))
;  '(((cons a b) (car :base) (cdr :base))))
; ==>
; ((:SLOT (NTH '1 (LOCALS ST)) ONE)
;  (:SLOT (NTH '2 (LOCALS ST)) TWO)
;  (:SLOT (NTH '5 (LOCALS ST)) FIVE))

(mutual-recursion
(defun changed-virtual-formal-slots (term base gup-drivers con-drivers)
  (cond
   ((or (variablep term)
        (fquotep term))
    (if (equal term base)
        nil
        (list (list :slot base term))))
   (t (mv-let
       (flg alist ele)
       (find-first-instance term 'car gup-drivers)
       (cond
        (flg
         (let ((vterm (cdr (assoc-eq :value alist)))
               (bterm (cdr (assoc-eq :base alist)))
               (vbase (cadr ele)))
           (cond
            ((not (equal (dig-to-btm bterm gup-drivers) base))
             (list (list :slot base term)))
            (t (delete-shadowed-slots
                (append
                 (changed-virtual-formal-slots
                  vterm
                  (sublis-var (cons (cons :base base) alist)
                              vbase)
                  gup-drivers
                  con-drivers)
                 (changed-virtual-formal-slots
                  bterm base gup-drivers con-drivers))
                nil)))))
        (t (mv-let
            (flg alist ele)
            (find-first-instance term 'car con-drivers)
            (cond
             (flg
              (delete-shadowed-slots
               (changed-virtual-formal-slots-lst (fargs term)
                                                 (sublis-var-lst
                                                  (cons (cons :base base)
                                                        alist)
                                                  (cdr ele))
                                                 gup-drivers
                                                 con-drivers)
               nil))
             ((equal term base) nil)
             (t (list (list :slot base term)))))))))))

(defun changed-virtual-formal-slots-lst (terms bases gup-drivers con-drivers)
  (cond ((endp terms) nil)
        (t (append
            (changed-virtual-formal-slots (car terms)
                                          (car bases)
                                          gup-drivers con-drivers)
            (changed-virtual-formal-slots-lst (cdr terms)
                                              (cdr bases)
                                              gup-drivers con-drivers)))))
 )

; -----------------------------------------------------------------
; Section: Proto Distilled Machines

; Recall that a termination machine is a list of tests-and-call records.  Each
; tests-and-call (sometimes called a ``line'' of the termination machine) has a
; list of :tests and a single :call of the function in question.  We produce a
; proto distilled machine pdmach (a list of proto distilled lines, pdlines)
; from the termination machine.

; ``Proto dline'' (``pdline'') is just a pair (tests . slots) and a list of
; proto dlines is a ``proto distilled machine'' (``pdmach'').

; We use will pdmach to determine whether a machine is flagged and to suggest
; measures that we will later stamp as strictly decreasing, weakly decreasing,
; or possibly growing on each line.

; However, we want the tests somewhat normalized, e.g., by expanding (ENDP x)
; and sorting into term order.  So our distillation of a termination machine
; into a pdmach is actually rather elaborate:

; (a) ``distill'' the tests -- this makes it possible to see terms like (P x)
; and (Q x) in actual tests like (AND (P A) (NOT (Q A))), which are of course
; coded as IFs in the translated bodies.  Distillation expands nonrecursive
; functions like ENDP to normalize elementary tests around standard usage,
; splits out the propositional structure, and sorts the literals into term
; order.  So given a machine with a line containing the tests ((IF a T b) c)
; and the call d, will become two lines, one with tests (a c) and call d and
; one with tests (b c) and call d.

; (b) replace the call by a list of :SLOT pseudo-terms -- this allows a
; subsumption-like computation to find the permutations of the formals in
; patterns that match the actuals instead of having to permute the order of the
; actuals.

; (c) introduce virtual formals when dealing with termination machines -- this
; allows us to suggest measures for decreasing components of larger formals
; using measure patterns derived from simpler earlier definitions.  For
; example, the measure pattern derived from a simple definition like factorial
; -- which suggests measuring the formal N with ACL2-COUNT and triggering on
; (:SLOT N (- N 1)) -- will apply to a state-modifying function with a virtual
; slot like: (:SLOT (NTH 7 (NTH 1 S)) (- (NTH 7 (NTH 1 S)) 1)).  Note that we
; DO NOT INTRODUCE VIRTUAL FORMALS when dealing with induction machines -- yet
; -- because we want the slots in patterns to bind variables.  See the
; discussion of slots in the defrec for measure-patterns.

; (d) Finally, we drop any unchanging actuals -- this means our treatment of
; formals is the same as our treatment of virtual formals in this respect.
; But the absence of any slots doesn't signal a base case!

; We call this ``distilling'' the lines and the machine.  The lines in
; distilled machines are simply pairs, (tests . slots), sometimes called
; ``dlines,'' where tests are literals, implicitly conjoined and representing
; some branch through the original propositional structure of the :tests in a
; line of a t-machine leading to a call and slots are the changing (sometimes
; virtual) formals-to-actuals in their corresponding :SLOT pseudo-terms
; notation.  If a dline contains no slots it means that it calls itself with
; all the arguments unchanged.  (This, of course, would make the function
; inadmissible if the corresponding tests aren't contradictory, but that's
; beside the point!)  The point is: a dline with no slots means a recursive
; call!  It does not mean a base case!

; The hard step here is splitting out the tests.  We build the IF expression
; representing (IMPLIES (AND . tests) concl) where concl is some new variable.
; When then clausify it, collect just the clauses whose last literal is concl,
; delete concl from those clauses, and negate every literal in each clause.
; The result is a disjunction of implicitly conjoined tests.  E.g.,
; here is the IF-form of (implies (and (or A B) C) CONCL), clausified:

; (clausify '(IF (IF (IF A 'T B) C 'NIL) CONCL 'T) nil nil nil)
; (((NOT A) (NOT C) CONCL)
;  ((NOT B) (NOT C) CONCL))
; ==> {collect and strip clauses with CONCL}
; (((NOT A) (NOT C))
;  ((NOT B) (NOT C)))
; ==> {dumb-negate-lit each clause}
; ((A C)
;  (B C))

; Logically:
; (IMPLIES (AND (OR A B) C) CONCL)
; <-->
; (AND (IMPLIES (AND A C) CONCL) (IMPLIES (AND B C) CONCL))

; Clearly, CONCL stands for the measure inequality, but we don't need to be
; concerned with its details here.


(defun collect-hyps-of-concl-clauses (clauses concl)
  (cond
   ((endp clauses) nil)
   ((eq concl (car (last (car clauses))))
    (cons (dumb-negate-lit-lst (all-but-last (car clauses)))
          (collect-hyps-of-concl-clauses (cdr clauses) concl)))
   (t (collect-hyps-of-concl-clauses (cdr clauses) concl))))

(defun conjunction-to-dnf (vars tests)

; Vars is a list of variable symbols, tests is a list of terms (implicitly
; conjoined), and vars contains every free var mentioned in tests.  We put
; tests into dnf: a disjunction of conjunctions, represented by a list of
; lists, e.g., ((OR a b) c) is converted to ((a c) (b c)), provided the OR is
; coded as an IF.

  (let* ((concl (cond ((member-eq 'concl vars)
                       (genvar 'GENVAR "CONCL" 1 vars))
                      (t 'CONCL)))
         (clauses
          (clausify (fcons-term* 'IF
                                 (conjoin tests)
                                 concl
                                 *t*)
                    nil nil nil))) ; assumptions, lambda-exp, sr-limit
    (collect-hyps-of-concl-clauses clauses concl)))

(defconst *distillation-fns*
  (cons 'IFF *expandable-boot-strap-non-rec-fns*))

(defun merge-sort-term-order-lst (lst)
  (cond
   ((endp lst) nil)
   (t (cons (merge-sort-term-order (car lst))
            (merge-sort-term-order-lst (cdr lst))))))

(defun distill-tests (formals term-lst wrld)
; We put the tests in term order because clausification can rearrange
; them and we want to recognize identical sets of tests.
  (merge-sort-term-order-lst
   (conjunction-to-dnf
    formals
    (expand-some-non-rec-fns-lst *distillation-fns* term-lst wrld))))

(defun virtual-slots (formals actuals gup-drivers con-drivers)
  (cond ((endp formals) nil)
        (t (append (changed-virtual-formal-slots (car actuals) (car formals)
                                                 gup-drivers con-drivers)
                   (virtual-slots (cdr formals) (cdr actuals)
                                  gup-drivers con-drivers)))))

(defun make-proto-distilled-machine (formals tmach wrld)

; We convert the termination machine tmach to a list of distilled pairs, (tests
; . vslots), one for each call.

  (cond
   ((endp tmach) nil)
   (t (union-equal
       (pairlis-x2
        (distill-tests formals
                       (access tests-and-call (car tmach) :tests)
                       wrld)
        (virtual-slots
         formals
         (fargs (access tests-and-call (car tmach) :call))
         (cdr (assoc-eq :list (table-alist 'generalized-updater-drivers
                                           wrld)))
         (cdr (assoc-eq :list (table-alist 'constructor-drivers
                                           wrld)))))
       (make-proto-distilled-machine formals (cdr tmach) wrld)))))

; -----------------------------------------------------------------
; Section: Identifying and Manipulating Flags

(defun vformals-of-slots (slots ans)
  (cond
   ((endp slots) ans)
   (t (vformals-of-slots (cdr slots)
                         (add-to-set-equal (cadr (car slots)) ans)))))

(defun vformals-of-pdmach (pdmach ans)
  (cond
   ((endp pdmach) (revappend ans nil))
   (t (vformals-of-pdmach (cdr pdmach)
                          (vformals-of-slots
                           (cdr (car pdmach))
                           ans)))))

; Determine whether the machine has a flag (a virtual formal that is tested
; against one or more constants (positively or negatively) in every line, never
; mixed up with the value of any other formal or expression, and either
; assigned some constant value in every line or is held constant.

(defun pos-neg-equal-constantp (v term)

; Both v and term are terms, and v is not quoted.  We return (mv sign v 'const)
; if term is of the form (equal v 'const) or (not (equal v 'const)), where by
; `equal' we include EQUAL, EQ, EQL, and =, we allow for symmetry of equality,
; and sign is T if the equality is positive and nil if negative.  Else we
; return (mv nil nil nil).  We also assume term is tested, i.e., means (NOT
; (EQUAL term 'NIL)).

  (cond
   ((variablep term)
    (cond ((equal term v)
           (mv nil v *nil*))
          (t
           (mv nil nil nil))))
   ((fquotep term)
    (mv nil nil nil))
   (t (mv-let
       (negativep atm)
       (strip-not term)

; Note: The convention on sign in the result of this function is that sign = t
; means the equality is positive and sign = nil means the equality is negated.
; But negativep is T if the term is negated.  The parities of these two notions
; are opposite.

       (cond
        ((variablep atm)
         (cond
          ((equal v atm)
           (mv negativep v *nil*))
          (t
           (mv nil nil nil))))
        ((fquotep atm)
         (mv nil nil nil))
        ((member-eq (ffn-symb atm) '(EQUAL EQ EQL =))
         (cond
          ((and (equal v (fargn atm 1))
                (quotep (fargn atm 2)))
           (mv (not negativep) v (fargn atm 2)))
          ((and (equal v (fargn atm 2))
                (quotep (fargn atm 1)))
           (mv (not negativep) v (fargn atm 1)))
          (t (mv nil nil nil))))
        (t (mv nil nil nil)))))))

; Here is the spec for pos-neg-constantp.  I had to prove it because
; I kept getting my parities swapped!

#||
(defevaluator evx evxl ((not x) (equal x y)(eq x y) (eql x y) (= x y)))
(thm
 (implies (and (pseudo-termp v)
               (not (equal v nil))
               (not (quotep v))
               (pseudo-termp term))
          (mv-let (sign x const)
                  (pos-neg-equal-constantp v term)
                  (cond
                   (x
                    (and (equal x v)
                         (quotep const)
                         (iff (evx term a)
                              (evx (if sign
                                       `(EQUAL ,x ,const)
                                       `(NOT (EQUAL ,x ,const)))
                                   a))))
                   (t t)))))
||#

(defun exists-equality-against-constantp (vformal tests)
  (cond
   ((endp tests) nil)
   (t (mv-let
       (sign v const)
       (pos-neg-equal-constantp vformal (car tests))
       (declare (ignore sign const))
       (or v ; this test is +/-(equal vformal 'evg)!
           (exists-equality-against-constantp vformal (cdr tests)))))))

(defun vformal-is-a-flag-in-line-of-pdmachp (vformal pdline)
  (let ((temp (assoc-equal-cadr vformal (cdr pdline))))
    (and (or (null temp)            ; vformal is unchanged in pdline
             (quotep (caddr temp))) ; or vformal becomes a constant
         (not (occur-lst vformal    ; vformal not used in any
                         (if temp   ; other slot
                             (remove1-equal temp (cdr pdline))
                             (cdr pdline))))
         (exists-equality-against-constantp vformal (car pdline)))))

(defun vformal-is-a-flagp (vformal pdmach)
  (cond ((endp pdmach) t)
        (t (and (vformal-is-a-flag-in-line-of-pdmachp vformal (car pdmach))
                (vformal-is-a-flagp vformal (cdr pdmach))))))

(defun exactly-one-flagp (vformals pdmach flg)
  (cond ((endp vformals) flg)
        ((vformal-is-a-flagp (car vformals) pdmach)

; The current vformal is a flag.  If we have found any other flags, then we
; fail.  Otherwise, we set the flag to this one and continue looking (but now
; looking to fail!).

         (if flg
             nil
             (exactly-one-flagp (cdr vformals) pdmach (car vformals))))
        (t (exactly-one-flagp (cdr vformals) pdmach flg))))

(defun flagged-proto-distilled-machinep (vformals pdmach)

; A proto distilled machine, pdmach, is a list of pairs (tests . slots), one
; for each call, where every where tests is a list of the terms governing the
; call and slots is a list of (:SLOT vformal vactual) slot settings for virtual
; formals.  A pdmach is flagged iff there is exactly one virtual formal, v,
; such that (a) v is tested against one or more constants in every line, and
; (b) every v :SLOT is occupied either by v itself or a constant.  If pdmach is
; flagged, we return the flag, v, a virtual formal.

; Note: A pdmach could conceivably have multiple flags, in which case this
; definition is too strict.  But I don't implement any kind of search for the
; flag to measure, so I insist on exactly one.

  (exactly-one-flagp vformals pdmach nil))

; Determine the range of the virtual formal: The set of all constant values to
; which it is set or against which it is tested.  Note that even though the
; range is always a set of quoted terms, we don't strip out the evgs but leave
; each constant in quoted form because we will repeatedly look for those terms
; and form new terms from them.  We look for both positive and negative tests,
; e.g., (equal pc '2) and (not (equal pc '2)) to help identify the range.  The
; reason we look into the tests at all in determining the range is that the
; function might so identify a flag but happen never to call itself with that
; flag -- just transitioning to one of the others.

(defun range-of-flag-from-tests (vformal tests)
  (cond ((endp tests) nil)
        ((and (not (variablep (car tests)))
              (not (fquotep (car tests))))
         (cond
          ((member-equal (ffn-symb (car tests)) '(EQUAL EQ EQL =))
           (cond
            ((and (equal vformal (fargn (car tests) 1))
                  (quotep (fargn (car tests) 2)))
             (add-to-set-equal
              (fargn (car tests) 2)
              (range-of-flag-from-tests vformal (cdr tests))))
            ((and (equal vformal (fargn (car tests) 2))
                  (quotep (fargn (car tests) 1)))
             (add-to-set-equal
              (fargn (car tests) 1)
              (range-of-flag-from-tests vformal (cdr tests))))
            (t (range-of-flag-from-tests vformal (cdr tests)))))
          ((and (eq (ffn-symb (car tests)) 'NOT)
                (not (variablep (fargn (car tests) 1)))
                (not (fquotep (fargn (car tests) 1)))
                (member-equal (ffn-symb (fargn (car tests) 1))
                              '(EQUAL EQ EQL =)))
           (cond
            ((and (equal vformal (fargn (fargn (car tests) 1) 1))
                  (quotep (fargn (fargn (car tests) 1) 2)))
             (add-to-set-equal
              (fargn (fargn (car tests) 1) 2)
              (range-of-flag-from-tests vformal (cdr tests))))
            ((and (equal vformal (fargn (fargn (car tests) 1) 2))
                  (quotep (fargn (fargn (car tests) 1) 1)))
             (add-to-set-equal
              (fargn (fargn (car tests) 1) 1)
              (range-of-flag-from-tests vformal (cdr tests))))
            (t (range-of-flag-from-tests vformal (cdr tests)))))
          (t (range-of-flag-from-tests vformal (cdr tests)))))
        (t (range-of-flag-from-tests vformal (cdr tests)))))

(defun range-of-flag (vformal pdmach)

; Pdmach is a proto distilled machine, a list of pairs (tests . slots), where
; every element of slots is (:SLOT v val).  We know pdmach is a flagged machine
; with flag vformal, so the tests compare vformal to various constants and the
; slots specify new values that are constant (or leave vformal unchanged by
; having no vformal :SLOT).  We collect all those quoted constants -- from
; tests and slots.  The result is a list of quoted constants, e.g., ('term
; 'term-list) or ('2 '10 '16).

  (cond ((endp pdmach) nil)
        (t (union-equal
            (range-of-flag-from-tests vformal (car (car pdmach)))
            (let ((slot (assoc-equal-cadr vformal (cdr (car pdmach)))))

; If there is no slot setting the flag, then it would have been of the
; form (:SLOT flag flag) and we ignored it.  So we don't add a new flag
; value to the range.

              (if slot
                  (add-to-set-equal
                   (caddr slot)
                   (range-of-flag vformal (cdr pdmach)))
                  (range-of-flag vformal (cdr pdmach))))))))

; Determine the incoming value(s) of the flag in every line, as specified by
; the tests of the line.  We also return the subset of the tests responsible.
; If we can't identify a suitable subset of the range for each line of the
; machine, we'll eventually abort.  The only (recognized) time that a (tests
; . slots) pair specifies multiple values for the flag is when it contains a
; sequence of negative tests against other values in the range, e.g., if range
; is ('a 'b 'c 'd) and we find a pair containing (NOT (EQUAL flg 'a)) (NOT
; (EQUAL flg 'b)), then the pair specifies the incoming values ('c 'd).

(defun member-equal-term1-term2 (term1 term2-lst tests)

; We determine whether tests contains a test equivalent to (EQUAL term1 term2),
; where term2 is an element of term2-lst.  We recognize EQUAL, EQ, EQL, and =
; as synonyms.  We also recognize that they are a symmetric.  If we find a
; suitable equality we return the term2 found and the relevant equality.  If no
; suitable equality is found, we return (mv nil nil), which will make us look
; for negative equalities next.

  (cond ((endp tests) (mv nil nil))
        ((and (not (variablep (car tests)))
              (not (fquotep (car tests)))
              (member-equal (ffn-symb (car tests)) '(EQUAL EQ EQL =)))
         (cond
          ((and (equal (fargn (car tests) 1) term1)
                (member-equal (fargn (car tests) 2) term2-lst))
           (mv (fargn (car tests) 2) (car tests)))
          ((and (equal (fargn (car tests) 2) term1)
                (member-equal (fargn (car tests) 1) term2-lst))
           (mv (fargn (car tests) 1) (car tests)))
          (t (member-equal-term1-term2 term1 term2-lst (cdr tests)))))
        (t (member-equal-term1-term2 term1 term2-lst (cdr tests)))))

(defun member-not-equal-term1-term2 (term1 term2-lst tests)

; Like member-equal-term1-term2 except instead of looking for (EQUAL term1
; term2) we look for (NOT (EQUAL term1 term2)).  We return the first such term2
; and test found, as (mv term2 test).  If no such test exists, we return (mv
; nil nil).

  (cond ((endp tests) (mv nil nil))
        ((and (not (variablep (car tests)))
              (not (fquotep (car tests)))
              (eq (ffn-symb (car tests)) 'NOT)
              (member-equal (ffn-symb (fargn (car tests) 1)) '(EQUAL EQ EQL =)))
         (cond
          ((and (equal (fargn (fargn (car tests) 1) 1) term1)
                (member-equal (fargn (fargn (car tests) 1) 2) term2-lst))
           (mv (fargn (fargn (car tests) 1) 2)
               (car tests)))
          ((and (equal (fargn (fargn (car tests) 1) 2) term1)
                (member-equal (fargn (fargn (car tests) 1) 1) term2-lst))
           (mv (fargn (fargn (car tests) 1) 1)
               (car tests)))
          (t (member-not-equal-term1-term2 term1 term2-lst (cdr tests)))))
        (t (member-not-equal-term1-term2 term1 term2-lst (cdr tests)))))

(defun members-not-excluded (term1 term2-lst tests-remaining tests-used)

; Assuming that (EQUAL term1 term2) must be true for some term2 in term2-lst,
; what are the possible values of term1?  Given that we failed to find (EQUAL
; term1 term2) among the tests-remaining, then throw out all the term2 that are
; excluded by tests-remaining and return that set along with the negative
; equalities used to throw out elements.  We return (mv term2-lst' tests),
; where term2-lst' is a subset of term2-lst and tests is a list of (NOT (EQUAL
; term1 term2)) terms in tests-remaining.  Tests-used is the accumulator of
; tests we have used so far.

  (mv-let (term2 test)
          (member-not-equal-term1-term2 term1 term2-lst tests-remaining)
          (cond
           ((null term2) (mv term2-lst (revappend tests-used nil)))
           (t (members-not-excluded term1
                                    (remove1-equal term2 term2-lst)
                                    (remove1-equal test tests-remaining)
                                    (cons test tests-used))))))

(defun incoming-flags-and-tests-of-pdline (vformal range pdline)

; Pdline is a (tests . slots) pair from a flagged proto distilled machine.
; Vformal is the flag of the machine and range is a list of the possible values
; the flag takes on in the machine.  The tests of pdline (had better)
; specify -- explicitly or implicitly -- a subset of range as the incoming
; value of the flag -- the flag values that satisfy the tests.  If so, we
; return (mv vals tests), where vals is the list of elements of the range
; implied by the tests in pdline and tests is the subset of those tests
; responsible for this implication.  Otherwise, we cause a hard error (because
; we do not have state here).

; Details: If the tests contain (EQUAL vformal 'val), where 'val is a member of
; range, then the incoming values of the flag in this line is the singleton
; list containing 'val and the tests returned is the singleton list containing
; the EQUALity found.  If the tests of pdline contain a series of negative
; equalities of the form (NOT (EQUAL vformal 'vali)), where each such 'vali is
; a member of range, then the incoming values of the flag in this line is the
; list of all the remaining elements in the range, i.e., those not excluded by
; the tests of pdline.  The tests returned are just the negative EQUALities
; found.

; If we can't make sense of the tests in terms of vformal and range, we signal
; a hard error.  This would happen if, for example, no element of range is
; identified by a test and no elements of range are excluded by the tests.

; Note: While vals = nil might seem a more natural signal when no incoming vals
; are implied, nil has another interpretation: it is returned when all elements
; of the range are explicitly excluded.  This happens when the user explicitly
; handled every element of the range.  The slots of pdline with nil incoming
; values are active only if the range invariant is violated in some external
; call of the function being defined.

  (mv-let
   (val test)
   (member-equal-term1-term2 vformal range (car pdline))

; If val is non-nil, it is the element of the range that vformal is assumed
; equal to in pdline.  That is, the slots in pdline are active only if
; vformal is val.

   (cond
    (val (mv (list val) (list test)))
    (t (mv-let
        (vals tests)
        (members-not-excluded vformal range (car pdline) nil)

; If vals is equal to range, then we didn't find any flag values excluded by
; the tests, in which case the pdmach from which pdline comes is unexpectedly
; contrary to what we expect; so we'll abort the whole idea of measuring the
; flag.  If vals is not equal to range, then it is a proper subset of range and
; the slots in pdline are active only if vformal is one of values in vals.

        (cond
         ((equal vals range)
          (mv (er hard 'incoming-flags-and-tests-of-pdline
                  "Even though this machine was detected to have a virtual ~
                   formal, ~x0, used as a flag, and the range of that formal ~
                   was determined to be ~x1, we have been unable to determine ~
                   the incoming values of the flag in the line of the machine ~
                   ruled by the tests ~X24.  Note that the outgoing slot ~
                   bindings for this line are ~X34."
                  vformal
                  range
                  (car pdline)
                  (cdr pdline)
                  nil)
              nil))
         (t (mv vals tests))))))))

; -----------------------------------------------------------------
; Section:  Measure Patterns and Measure Suggestions

; A measure-pattern indicates that the presence of certain tests and slots
; suggests a certain measure.  Patterns are a little fancier and we'll declare
; and document the record below when we start to use them.  Patterns, when
; applied to pdlines and pdmachs suggest measures.  However, it is not
; necessary for a pattern to match perfectly to suggest a measure.  For
; example, a pattern may indicate that a certain test and a certain slot
; configuration suggest a measure but when applied the test is not found but
; the slot is.  The suggestion is made anyway, but will have a lower rank than
; one that fit the pattern better.

; Suggestions are recorded in measure-suggestion (mesug) records:

; Note:  The following record must be cheap, so

; (access measure-suggestion mesug :rank) = (car mesug)
; (access measure-suggestion mesug :measure) = (cadr mesug)

; Given a list of measure-suggestions we sort it by comparing cars (i.e.,
; :ranks) and sometimes seach with assoc-equal-cadr (i.e., for :measure).

(defrec measure-suggestion    ; ``mesug''
  (rank measure stamp names)
  t)                          ; CHEAP!  See note above.

; Our basic plan is to look at each (tests . slots) pair in a proto distilled
; machine and fire all the measure-patterns to collect all the mesugs
; applicable to any pdline in the machine.  Then we'll ascertain the actual
; behavior of each measure on each line (whether suggested by that line or not)
; by attempting to prove the obvious conjectures.

; Our immediate goal is to apply a measure pattern mp to a pdline pair and
; compute a list of alists with the property that when one of the alists is
; used to instantiate the pattern's :tests and :slots there is a non-empty
; intersection with the pdline's tests and slots.

; Since it is possible for the same (set-equal) alist to be generated by
; several patterns, we have to union these lists of pairs together: if two
; pairs have set-equal alists, we keep the one with the higher s-score.

(defun member-set-equal (set sets)

; Set is a list being treated as a set.  Sets is a list of such sets.  We
; determine whether set occurs in sets and return the tail of sets that starts
; with that occurrence.  I.e., this is just member in which the test is
; set-equal-equal.

  (cond ((endp sets) nil)
        ((set-equalp-equal set (car sets))
         sets)
        (t (member-set-equal set (cdr sets)))))

(defun collect-set (set sets)
  (let ((sets1 (member-set-equal set sets)))
    (cond
     ((null sets1) (cons set sets))
     (t sets))))

(defun union-sets (sets1 sets2)

; Both arguments are lists of sets treated as sets.  We union the two lists
; together.

  (cond ((endp sets1) sets2)
        (t (union-sets
            (cdr sets1)
            (collect-set (car sets1) sets2)))))

(mutual-recursion

(defun all-partial-subsumptions1 (terms1 terms2 alist)

; We assume there is at least one variable symbol in terms1, and thus any
; winning alist will be non-nil.

  (cond
   ((null terms1)
    (if alist (list alist) nil))
   (t (all-partial-subsumptions11 (car terms1)
                                  (cdr terms1)
                                  terms2 terms2 alist))))

(defun all-partial-subsumptions11 (lit tl1 tl2 terms2 alist)
  (cond ((null tl2) nil)
        (t (mv-let
            (wonp alist1)
            (one-way-unify1 lit (car tl2) alist)

; We are searching for all possible extensions of alist to match as many
; literals of (lit . tl1) as we can.  So if lit matches the first one in tl2,
; we have to do two things: (a) try to match of as many of the rest of the
; literals as we can (after incrementing the score of the now extended alist1),
; and (b) find ways to match lit with the other elements of tl2.  If lit
; doesn't match the first one in tl2 then we must (c) forget lit and try to
; match as many of the rest as we can under the original alist, and (b) [again]
; find ways to match lit with the other elements of tl2.  Having done either
; (a) and (b) or (c) and (b) we then union the resulting pairs together,
; keeping the higher score of any two pairs with the same alist.

            (union-sets
             (if wonp
                 (all-partial-subsumptions1 tl1 terms2 alist1)  ; (a)
                 (all-partial-subsumptions1 tl1 terms2 alist))  ; (c)
             (all-partial-subsumptions11 lit tl1
                                         (cdr tl2)
                                         terms2 alist)))))))    ; (b)

(defun all-partial-subsumptions (pats terms)

; Pats and terms are lists of (pseudo-)terms.  Return the set of all alists, a,
; such that pats/a has a non-empty intersection with terms.

; (all-partial-subsumptions '((P x)       (Q y) (R x y))   ; pats
;                           '((P A) (P B) (Q C) (R B C)))  ; terms
; (((x . A))          ;[1]
;  ((y . C) (x . A))  ;[2]
;  ((x . B))          ;[3]
;  ((y . C) (x . B))  ;[4]
;  ((y . C)))         ;[5]

; Each of these substitutions ``picks up'' at least least one pattern from
; pats, i.e., when the pats are instantiated with one of these alists, at least
; one instantiated pattern is among terms.  We do it in all possible ways.  So,
; for example, [1] picks up (P x)/[1] = (P A) and (P A) is among terms.  [2]
; picks up both (P x) and (Q y).  [4] picks up all three pats.

; One might ask: why bother with [1], [3], and [5] when they can be extended to
; pick up other pats?  The answer is that in the recursion we must generate [1]
; so we can extend it to generate [2] and possibly others later.

  (all-partial-subsumptions1 pats terms nil))

; We will actually eliminate any partial subsumptions that do not bind every
; variable in the measure.  Note that a partial subsumption is allowed to bind
; variables not occurring in the measure: such a variable my occur in one of
; the tests, say, we want to detect that the substitution picks up the actual
; test.

(defun all-assoc-eq (vars alist)
; Check that every var in vars is bound in alist.
  (cond ((endp vars) t)
        (t (and (assoc-eq (car vars) alist)
                (all-assoc-eq (cdr vars) alist)))))

(defun collect-complete-alists (vars alists)
  (cond ((endp alists) nil)
        ((all-assoc-eq vars (car alists))
         (cons (car alists)
               (collect-complete-alists vars (cdr alists))))
        (t (collect-complete-alists vars (cdr alists)))))

(defrec measure-pattern
  (name measure vars tests slots invariants pseudo-clause)
  nil)

; Name is any symbol and is just used to identify the name of this heuristic.

; Measure is the measure term being suggested.

; Vars is the list of variable symbols occuring freely in measure.

; Tests is the list of tests suggesting this measure.  Note: It is possible for
; a distilled test to mention a variable not occurring in the measure, as would
; happen if the user's definition had tested (MEMBER E X) and relied on it to
; insure (CONSP X).

; Slots is the list of changing slots suggesting this measure.  Note: Each
; element of slots is (:SLOT formal actual) where formal is a variable symbol,
; not a virtual formal.  A slot is allowed (by our code) to use a formal not
; occurring in measure.  But in fact we suspect that all the patterns we or the
; user will generate will only mention changing formals involved in the measure
; so as not to weaken the applicability of the suggestion.

; Invariants is a list of pseudo-terms expressing a conjunction of restrictions
; on legal instantiations of the variables in tests and slots.  Each element
; must be a cons and the car (``function symbol'') of each must be a KEYWORD
; other than :measure and :slot.  These pseudo-terms are not actually evaluated
; properly, they are interpreted by a special-purpose invariant checker with
; respect to the substitution alist produced by matching the :tests and :slots.
; But they must obey the rules of pseudo-terms because they are subjected to
; subsumption.  The allowed invariant pseudo-terms and their meanings with
; respect to a substitution alist are:

; (:constant ':negint v) - v is bound in alist to a quoted negative integer
; (:constant ':posint v) - v is bound in alist to a quoted positive integer

; The restrictions on invariants insure that we can do a subsumption check on
; them (by just appending them into the pseudo-clause for the measure pattern,
; see pseudo-clause-of-measure-pattern) without them being mixed up with tests
; (which are true terms), measures, or slots.

; See the code immediately below for how we check the syntax and meaning of
; invariants wrt the substitution alist, and how the user might extend the
; allowed invariants.

; Pseudo-clause is just a list containing the measure, all the tests, all the
; slots, and all the invariants.  The measure ``literal'' is tagged with
; :measure.  This ``clause'' has no logical meaning.  Its only role is to allow
; us to check, via a simple conventional clause subsumption check, that the
; measure, tests, slots, and invariants of one mp subsume those of another.
; This test is used when adding a new mp to the database.  Each ``clause'' only
; has one :measure ``literal'' and so measures are only subsumed by measures.
; Similarly for the ``literals'' from the invariants, thanks to the minimal
; syntactic checks in mp-invariantsp.  Slots are interchangeable with other
; slots modulo substitution but cannot be subsumed by any other part of the
; pattern.  And tests are proper terms and are the only proper terms in the
; ``clause'' and so they don't mix with measures, slots, or invariants.

; It may seem counterintuitive that subsumption ever fires if we have
; ``maximally'' cleaned up our machines as we do with bare-essential-machine
; below.  But ``maximal'' is relative to the resource limits and, more
; importantly, to the lemma development that may put certain results within
; reach that were not in reach before.  I give an example of subsumption
; actually firing among my tests below.  See the examples around the defun of
; overly-complicated and less-complicated below.

(defmacro make-measure-pattern

; This is just a convenient way to (make measure-pattern ...)  and have the
; :pseudo-clause filled in implicitly.

  (&key name measure vars tests slots invariants)
  `(let ((name ,name)
         (measure ,measure)
         (vars ,vars)
         (tests ,tests)
         (slots ,slots)
         (invariants ,invariants))
     (make measure-pattern
           :name name
           :measure measure
           :vars vars
           :tests tests
           :slots slots
           :invariants invariants
           :pseudo-clause (cons (list :measure measure)
                                (append invariants
                                        tests
                                        slots)))))

(logic)

; The attachable function chk-mp-invariantsp introduced below allows the user to
; enforce invariants on the alists used to instantiate measure-patterns.  We
; attach an initial invariants checker, chk-mp-invariantsp-builtin, but the user
; wishing to extend the kinds of invariants checked can do so by attaching a
; different function.  Of course, any function attached to chk-mp-invariantsp
; must be guard-verified with the same (or weaker) guard.  The only thing we
; assume about the arguments to chk-mp-invariantsp is that the inv is a
; true-listp and the alist is a symbol-alist that maps vars to pseudo-terms.
; Nothing else is assumed about the structure of the invariants!  Users must
; code new invariants checkers to anticipate ``ill-formed'' invariants modulo
; their notion of invariants.

; Users are also advised that the elements of inv should be treated as
; conjuncts by any new attachment.  That is because we use subsumption to
; determine that one set of invariants implies another.  Failure to respect the
; conjunctive nature of mp invariants will not cause any problem other than
; somewhat unpredictable behavior regarding when one measure-pattern subsumes
; another.

; This is just a poor man's first-order replacement for the more general
; ability to translate and evaluate an arbitrary predicate on alist and to
; solve the problem of when one invariant implies another.  In an earlier
; version we used simple-translate-and-eval for this, but that requires passing
; state in and trafficking in value-triples, and made the implication question
; impractical.

(defun mp-invariantsp (inv)
  (declare (xargs :guard t))
  (cond ((atom inv) (eq inv nil))
        ((and (consp (car inv))
              (pseudo-termp (car inv))
              (keywordp (ffn-symb (car inv)))
              (not (eq (ffn-symb (car inv)) :SLOT))
              (not (eq (ffn-symb (car inv)) :MEASURE)))
         (mp-invariantsp (cdr inv)))
        (t nil)))

(encapsulate (((chk-mp-invariantsp * *) => *
               :formals (inv alist)
               :guard (and (mp-invariantsp inv)
                           (symbol-alistp alist)
                           (pseudo-term-listp (strip-cdrs alist)))))
             (local (defun chk-mp-invariantsp (inv alist)
                      (declare (xargs :mode :logic)
                               (ignore inv alist))
                      t)))

(defun chk-mp-invariantsp-builtin (inv alist)

; This is the initial interpretation (attachment) to chk-mp-invariantsp.  Inv is
; a pseudo-term list of tuples representing a conjunction of restrictions on
; alist.  These pseudo-terms are not evaluated properly -- alist is not an
; argument -- but are interpreted here wrt alist.  They must be pseudo-terms
; because they are subjected to subsumption.  The only tuples recognized right
; now are:

; (:constant ':negint v) - v is bound in alist to a quoted negative integer
; (:constant ':posint v) - v is bound in alist to a quoted positive integer

; More could be added but it must be the case that ill-formed tuples do not
; cause errors!  See the discussion of attachment above.

  (declare (xargs :mode :logic
                  :guard (and (mp-invariantsp inv)
                              (symbol-alistp alist)
                              (pseudo-term-listp (strip-cdrs alist)))))
  (cond ((endp inv) t)
        ((and (consp (car inv))
              (true-listp (car inv)))
         (and
          (case (car (car inv))
            (:constant
             (let* ((arg1 (fargn (car inv) 1))
                    (typ  (if (quotep arg1) (cadr arg1) nil))
                    (var (fargn (car inv) 2))
                    (temp (assoc-eq var alist)))
               (and temp
                    (quotep (cdr temp))
                    (let ((evg (cadr (cdr temp))))
                      (case typ
                        (:negint (and (integerp evg)
                                      (< evg 0)))
                        (:posint (and (integerp evg)
                                      (< 0 evg)))
                        (otherwise nil))))))
            (otherwise nil))
          (chk-mp-invariantsp-builtin (cdr inv) alist)))
        (t nil)))

(defattach chk-mp-invariantsp chk-mp-invariantsp-builtin)

(program)

(defun prettyify-measure-pattern (mp)
  (let ((tests (access measure-pattern mp :tests))
        (slots (access measure-pattern mp :slots))
        (invariants (access measure-pattern mp :invariants)))
    `(make-measure-pattern
      :name ',(access measure-pattern mp :name)
      :tests ,(if tests (kwote tests) nil)
      :slots ,(if slots (kwote slots) nil)
      :invariants ,(if invariants (kwote invariants) nil)
      :measure ',(access measure-pattern mp :measure)
      :vars ',(access measure-pattern mp :vars))))

(defun prettyify-measure-pattern-lst (lst)
  (cond ((endp lst) nil)
        (t (cons (prettyify-measure-pattern (car lst))
                 (prettyify-measure-pattern-lst (cdr lst))))))

; -----------------------------------------------------------------
; Section: Applying Measure Patterns to Suggest Measures

; TODO: We could try to weed out bogus suggestions.  Here's what I mean: We
; currently ignore the actual hyps in the theorem that would justify a measure
; suggestion.  For example, in the first suggestion below, we don't insist that
; (natp i) be present in the (equal i 0) case.  In the 1979 book, we actually
; used the rewriter to prove that the governing tests imply the hyps of the
; relevant lemma.  If that was proved, we KNEW the measure decreased (possibly
; only weakly) in that call.  We then tried to assemble a lexicographic
; combination out of the things we knew, and if we succeeded, we declared
; victory.

; In ACL2, we are going to prove the measure conjecture, come what may.  So
; there is no point in proving that the tests imply the hypotheses... unless it
; turns out that it is faster to do that to rule out bogus suggestions before
; resorting to a full-blown admissions check.

; End of TODO

; TODO:  Populate this table when I know what I'm doing with patterns!

(table measure-patterns
       :list
       (list
; Should we add commuted versions of these, i.e., (binary-+ i negint)?
        (make-measure-pattern
         :name 'tested-non-zp-and-decremented
         :tests '((not (zp i)))
         :slots '((:slot i (binary-+ negint i)))
         :invariants '((:constant ':negint negint))
         :measure '(acl2-count i)
         :vars '(i))
        (make-measure-pattern
         :name 'tested-non-0-and-decremented
         :tests '((not (equal i '0)))
         :slots '((:slot i (binary-+ negint i)))
         :invariants '((:constant ':negint negint))
         :measure '(acl2-count i)
         :vars '(i))
        (make-measure-pattern
         :name 'tested-positive-and-decremented
         :tests '((< '0 i))
         :slots '((:slot i (binary-+ negint i)))
         :invariants '((:constant ':negint negint))
         :measure '(acl2-count i)
         :vars '(i))
        (make-measure-pattern
         :name 'counting-up-with-zp-trick
         :tests '((not (zp (binary-+ max (unary-- i)))))
         :slots '((:slot i (binary-+ posint i)))
         :invariants '((:constant ':posint negint))
         :measure '(nfix (- max i))
         :vars '(i max))
        (make-measure-pattern
         :name 'counting-up-with-<-test
         :tests '((< i max))
         :slots '((:slot i (binary-+ posint i)))
         :invariants '((:constant ':posint negint))
         :measure '(nfix (- (ifix max) (ifix i)))
         :vars '(i max))
        (make-measure-pattern
         :name 'recursion-by-cdr-strong
         :tests '((consp x))
         :slots '((:slot x (cdr x)))
         :invariants nil
         :measure '(acl2-count x)
         :vars '(x))
        (make-measure-pattern
         :name 'recursion-by-car-strong
         :tests '((consp x))
         :slots '((:slot x (car x)))
         :invariants nil
         :measure '(acl2-count x)
         :vars '(x))
        (make-measure-pattern
         :name 'recursion-by-cdr-weak
         :tests nil
         :slots '((:slot x (cdr x)))
         :invariants nil
         :measure '(acl2-count x)
         :vars '(x))
        (make-measure-pattern
         :name 'recursion-by-car-strong
         :tests nil
         :slots '((:slot x (car x)))
         :invariants nil
         :measure '(acl2-count x)
         :vars '(x))))

; The user is free to extend this table at will.

; TODO: At the moment, no facilities are provided to make that convenient other
; than implicitly by using DEFUN with an explicit :MEASURE and letting the
; system ``learn'' from it and automatically generate a measure-pattern.  But
; auto-generated patterns do not use the full power of the patterns.

(defun rank-mesug1 (x y)

; Roughly speaking, we count how many elements of x occur as elements of y.
; However, if an element of x a :SLOT expression, we give it weight 2 if it is
; changing slot and weight 1 otherwise.  In addition, if y is T we treat it as
; though it contains all the elements of x.

; TODO: ARE there any unchanging slots in measure-patterns?  I think not!

  (cond ((endp x) 0)
        ((or (eq y t)
             (member-equal (car x) y))
         (+ (if (consp (car x))
                (if (eq (ffn-symb (car x)) :SLOT)
                    (if (equal (fargn (car x) 1)
                               (fargn (car x) 2))
                        1      ; unchanging slot
                        2)     ; changing slot
                    1)         ; a test
                1)             ; a test
             (rank-mesug1 (cdr x) y)))
        (t (rank-mesug1 (cdr x) y))))

(defun rank-mesug (alist mp unflagged-pdline)

; Unflagged-pdline is a (test . slots) pair distilled from a termination
; machine -- with the :SLOT for the machine's flag variable, if any, deleted.
; Alist is a substitution for instantiating the measure pattern mp.  The alist
; instance of the measure in mp has been suggested by pdline.

; We compute the rank of the suggestion as an integer between 1 and 100.  We sum
; the number of :slots it picks up (weighing changing slots by a factor of 2)
; and the number of :tests it picks up, then we normalize that so the highest
; score is 100.

; Note that the score can be arbitrarily close to 100 (including a ``perfect''
; 100) even when NONE of the slots are matched!  We give an example below.
; It is relevant because we have considered imposing a restriction in which we
; throw out suggestions that do not stem from at least one matched slot and one
; way to do that would be to use a threshold formula that detects that condition.
; But this is not such a formula!

; For example, if there was only 1 :slot in the pattern and it was not matched,
; but there were 199 tests (!)  and they all matched, the relevant computation
; would be (ceiling (* 100 (/ (+ 0 199) (+ 2 199))) 1) = (ceiling 99.004 1) =
; 100 (This is the minimal number of tests that produces a perfect 100.)  On
; the other hand, if we used FLOOR instead of CEILING we'd reserve 100 for the
; case where all of the slots matched too.  But that doesn't really solve the
; thresholding problem because, even with FLOOR and a realistic scenario, like
; 1 :slot which is not matched with 3 tests which are all matched we would get
; quite respectable rank of 60 and ranks can still reach 99 with enough tests.

; Warning: If you change the 100 to something else, be sure to look for other
; occurrences of 100 in this book.  There are no others as of February 13,
; 2014.

  (let ((inst-slots (sublis-var-lst alist (access measure-pattern mp :slots)))
        (inst-tests (sublis-var-lst alist (access measure-pattern mp :tests))))

; We could more simply just count how many elements of the instantiated tests
; and slots occur respectively in the car and cdr of the pdline, and then scale
; the slot count by 2.  But if we wish to distinguish changing slots from
; unchanging ones we have to take look inside the list of slots.  Thus the need
; for rank-mesug1.

    (ceiling
     (* 100
        (/ (+ (rank-mesug1 inst-slots (cdr unflagged-pdline))
              (rank-mesug1 inst-tests (car unflagged-pdline)))
           (+ (rank-mesug1 inst-slots t)
              (rank-mesug1 inst-tests t))))
     1)))

(defun find-mesug-with-measure-in-mesug-lst (measure mesug-lst)
  (cond ((endp mesug-lst) nil)
        ((equal measure
                (access measure-suggestion (car mesug-lst) :measure))
         (car mesug-lst))
        (t (find-mesug-with-measure-in-mesug-lst measure (cdr mesug-lst)))))

(defun collect-measure-suggestion (mesug mesug-lst)

; Add mesug to mesug-lst, combining it with any existing mesug with the same
; :measure.  We sum the two ranks and union the names.

  (let ((mesug1 (find-mesug-with-measure-in-mesug-lst
                 (access measure-suggestion mesug :measure)
                 mesug-lst)))
    (cond
     ((null mesug1)
      (cons mesug mesug-lst))
     (t (cons (change measure-suggestion mesug1
                      :rank (+ (access measure-suggestion mesug :rank)
                               (access measure-suggestion mesug1 :rank))
                      :names
                      (union-equal (access measure-suggestion mesug :names)
                                   (access measure-suggestion mesug1 :names)))
              (remove1-equal mesug1 mesug-lst))))))

(defun measure-unchanged-by-slotsp (measure slots)

; Is measure left unchanged in this call?  Slots is a list of (:SLOT vformal
; new-val) slots, where each listed vformal is changed to some new-val.  We
; return t if no vformal occurs in measure, in which case it (plausibly) means
; that measure is unchanged in this call.  How might we produce a suggestion
; that measure decreases when no component of it is changed by the call?
; Answer: by triggering the suggestion entirely from tests.  There may be other
; ways, but this was found to weed out some silly suggestions.

  (cond ((endp slots) t)
        ((occur (fargn (car slots) 1) measure) nil)
        (t (measure-unchanged-by-slotsp measure (cdr slots)))))

; -----------------------------------------------------------------
; Section: Ad Hoc Simplification of Suggested Measures to Eliminate Silly Ones

; When we instantiate the :measure of a measure-pattern with an alist we first
; rewrite the pattern to simplify it.  This rewriting is only heuristic!  It
; does not have to be sound because we're only producing terms that we suspect
; are decreasing.  If they're proved to work, they work, regardless of how
; randomly we might have arrived at them.  But the reason we rewrite
; instantiated measures is mainly to rule out silly ones, e.g., (+ (nfix a) (-
; (nfix a))), as might happen if a rule for :measure (+ (nfix max) (- (nfix
; i))) gets instantiated with both max and i being a.  This measure will
; rewrite to 0, which is recognized as being unchanging.

(defconst *heuristic-rules*
  '(((binary-+ x (unary-- x)) . '0)
    ((< x x) . 'nil)
    ((natp (len x)) . 't)
    ((nfix (nfix x)) . (nfix x))
    ((nfix (len x)) . (len x))))

(defun apply-heuristic-rule (rule term)
; (mv hitp term'), no change loser on term.
  (let ((lhs (car rule))
        (rhs (cdr rule)))
    (mv-let (ans alist)
            (one-way-unify lhs term)
            (cond
             (ans (mv t (sublis-var alist rhs)))
             (t (mv nil term))))))

(defun apply-heuristic-rules (rules term)
  (cond
   ((endp rules) term)
   (t (mv-let (hitp term)
              (apply-heuristic-rule (car rules) term)
              (cond
               (hitp term)
               (t (apply-heuristic-rules (cdr rules) term)))))))

(defun eval-if-possible (fn args)
  (cond
   ((all-quoteps args)
    (case fn
      (binary-+ (kwote (+ (cadr (car args)) (cadr (cadr args)))))
      (binary-* (kwote (* (cadr (car args)) (cadr (cadr args)))))
      (expt (kwote (expt (cadr (car args)) (cadr (cadr args)))))
      (unary-- (kwote (- (cadr (car args)))))
      (natp (kwote (natp (cadr (car args)))))
      (integerp (kwote (integerp (cadr (car args)))))
      (< (kwote (< (cadr (car args)) (cadr (cadr args)))))
      (nfix (kwote (nfix (cadr (car args)))))
      (ifix (kwote (ifix (cadr (car args)))))
      (otherwise (fcons-term fn args))))
   (t (fcons-term fn args))))

(mutual-recursion
(defun heuristic-rewriter (term)
  (cond
   ((variablep term) term)
   ((fquotep term) term)
   ((eq (ffn-symb term) 'IF)
    (let ((test (heuristic-rewriter (fargn term 1))))
      (cond
       ((quotep test)
        (if (cadr test)
            (heuristic-rewriter (fargn term 2))
            (heuristic-rewriter (fargn term 3))))
       (t (fcons-term* 'IF test
                       (heuristic-rewriter (fargn term 2))
                       (heuristic-rewriter (fargn term 3)))))))
   (t (let* ((fn (ffn-symb term))
             (args (heuristic-rewriter-lst (fargs term)))
             (term1 (eval-if-possible fn args)))
        (cond
         ((quotep term1) term1)
         (t (apply-heuristic-rules *heuristic-rules* term1)))))))

(defun heuristic-rewriter-lst (terms)
  (cond ((endp terms) nil)
        (t (cons (heuristic-rewriter (car terms))
                 (heuristic-rewriter-lst (cdr terms)))))))

; -----------------------------------------------------------------
; Section:  Collecting and Sorting All Measure Suggestions

(defun accumulate-measure-suggestions (alists mp unflagged-pdline mesug-lst)

; Measure pattern mp has generated all the matches described by alists,
; suggesting the :measure of mp as instantiated by each alist.  Each suggestion
; carries the :name of mp as a tag and a :rank computed with rank-mesug.  The
; only reason we have the unflagged-pdline is so we can detect whether some
; suggested measure is silly because no variable in it is changed.  We
; accumulate them all (non-silly) mesugs onto mesug-lst.

  (cond
   ((endp alists) mesug-lst)
   (t (accumulate-measure-suggestions
       (cdr alists)
       mp
       unflagged-pdline
       (let* ((alist (car alists))
              (measure1 (heuristic-rewriter
                         (sublis-var alist
                                     (access measure-pattern mp :measure))))
              (slots (cdr unflagged-pdline)))
         (if (or (null (all-vars measure1))
                 (measure-unchanged-by-slotsp measure1 slots))
             mesug-lst
             (collect-measure-suggestion
              (make measure-suggestion
                    :rank (rank-mesug alist mp unflagged-pdline)
                    :measure measure1
                    :names (list (access measure-pattern mp :name)))
              mesug-lst)))))))

(defun apply-measure-pattern (mp unflagged-pdline mesug-lst)

; Mp is a measure-pattern.  Pdline is a pdline from a distilled tmach, i.e.,
; unflagged-pdline is a cons pair of the form (tests . slots), where tests is a
; list of literals tested down a branch of the original t-machine and slots is
; the list of the changing (:SLOT v a) pseudo-terms corresponding to one call
; governed by those tests -- it is ``unflagged'' in the sense that if the
; machine has a flag, its slot binding has been eliminated by slots.  We use
; unflagged-pdlines to generate the measure suggestions because we don't want
; the flag to participate in measure generation (except for the explicit flag
; weighing measures we generate elsewhere).  We return the accumulated mesug
; list, i.e., the accumulated instantiated measure suggestions.

  (let* ((vars (access measure-pattern mp :vars))
         (tpats (access measure-pattern mp :tests))
         (spats (access measure-pattern mp :slots))
         (tests (car unflagged-pdline))
         (slots (cdr unflagged-pdline))
         (alists (collect-complete-alists
                 vars
                 (all-partial-subsumptions
                  (append spats tpats)
                  (append slots tests)))))
    (accumulate-measure-suggestions alists mp unflagged-pdline mesug-lst)))

(defun apply-all-measure-patterns (measure-patterns unflagged-pdline mesug-lst)

; We apply each measure pattern in measure-patterns to the (unflagged)
; pdline and build up a mesug list of all suggested instances of
; measures.  The unflagged pdline is just a pdline with all mention of the flag
; variable (if any) excised to prevent its participation in the measure
; generation process.

; Each mesug created has the sum of the ranks of any suggestions leading to the
; same measure, and the names of all suggestions leading to that instance.

  (cond
   ((endp measure-patterns)
    mesug-lst)
   (t (apply-all-measure-patterns
       (cdr measure-patterns)
       unflagged-pdline
       (apply-measure-pattern (car measure-patterns)
                              unflagged-pdline
                              mesug-lst)))))

(defun delete-when-occur-lst (term term-lst)
; Delete every element of term-lst in which term occurs.
  (cond
   ((endp term-lst) nil)
   ((occur term (car term-lst))
    (delete-when-occur-lst term (cdr term-lst)))
   (t
    (cons (car term-lst)
          (delete-when-occur-lst term (cdr term-lst))))))

(defun unflag-pdline (flag-vformal pdline)
; If flag-vformal is non-nil, we remove all traces of it from pdline, a line
; from a distilled machine.  This prevents the flag from participating in
; measure suggestions.
  (cond
   ((null flag-vformal) pdline)
   (t (cons (delete-when-occur-lst flag-vformal (car pdline))
            (let ((slot (assoc-equal-cadr flag-vformal (cdr pdline))))
              (if slot
                  (remove1-equal slot (cdr pdline))
                  (cdr pdline)))))))

(defun collect-all-measure-suggestions1
  (measure-patterns flag-vformal pdmach mesug-lst)
  (cond
   ((endp pdmach) mesug-lst)
   (t (collect-all-measure-suggestions1
       measure-patterns
       flag-vformal
       (cdr pdmach)
       (apply-all-measure-patterns measure-patterns
                                   (unflag-pdline flag-vformal (car pdmach))
                                   mesug-lst)))))

(defun collect-all-measure-suggestions (measure-patterns flag-vformal pdmach)
  (merge-sort-car->
   (collect-all-measure-suggestions1 measure-patterns
                                     flag-vformal
                                     pdmach
                                     nil)))

; -----------------------------------------------------------------
; Section:  Distilled Lines and Distilled Machines

; Now we begin generating and manipulating (true) dlines as opposed to
; ``proto-dlines.''

(defrec dline
  (ruling-tests                         ; (term_1 ...)
   call-slots                           ; ((:SLOT vformal_1 term_1) ...)
   sublis-expr-alist                    ; ((vformal_1 . term_1) ...)
   measure-suggestion-lst               ; (measure-suggestion_1 ...)
   flag-vformal                         ; nil or vformal used as flag
   incoming-flag-to-outgoing-flag-alist ; ((val-in_1 . val-out_1) ...)
   incoming-flag-to-recog-term-alist)   ; ((val-in_1 . recog-term_1) ...)
  nil)

; A ``distilled machine'' (``pdmach'') is a list of pdlines.

(defun map-slots-to-expr-alist (slots)
; ((:SLOT v val) ...) ==> ((v . val) ...)
  (cond ((endp slots) nil)
        (t (cons (cons (cadr (car slots))
                       (caddr (car slots)))
                 (map-slots-to-expr-alist (cdr slots))))))

(defun initial-dmach1 (flag-vformal flag-range pdmach)
  (cond
   ((endp pdmach) nil)
   (t (let ((pdline (car pdmach)))
        (mv-let
         (incoming-flag-to-outgoing-flag-alist
          incoming-flag-to-recog-test)
         (cond
          ((null flag-vformal)
           (mv nil nil))
          ((null (assoc-equal-cadr flag-vformal (cdr pdline)))
           (mv nil nil))
          (t (mv-let
              (incoming-flag-vals
               incoming-flag-tests)
              (incoming-flags-and-tests-of-pdline flag-vformal flag-range pdline)
              (let ((j (caddr (assoc-equal-cadr flag-vformal (cdr pdline)))))
                (mv (pairlis-x2 incoming-flag-vals
                                (list j))
                    (pairlis-x2 incoming-flag-vals
                                (conjoin incoming-flag-tests)))))))
         (cons (make dline
                     :ruling-tests (car pdline)
                     :call-slots (cdr pdline)
                     :sublis-expr-alist (map-slots-to-expr-alist (cdr pdline))
                     :measure-suggestion-lst nil ; will be populated later
                     :flag-vformal flag-vformal
                     :incoming-flag-to-outgoing-flag-alist
                       incoming-flag-to-outgoing-flag-alist
                     :incoming-flag-to-recog-term-alist
                       incoming-flag-to-recog-test)
               (initial-dmach1 flag-vformal flag-range (cdr pdmach))))))))

(defun initial-dmach-and-measure-suggestions
  (formals tmach measure-patterns wrld)

; Formals are the formals of the termination machine tmach; measure-patterns
; are the available patterns.  We produce the initial distilled machine and a
; rank-orderered list of measure-suggestions.

  (let* ((pdmach
          (make-proto-distilled-machine formals tmach wrld))
         (vformals
          (vformals-of-pdmach pdmach nil))
         (flag-vformal
          (flagged-proto-distilled-machinep vformals pdmach))
         (flag-range
          (if flag-vformal
              (range-of-flag flag-vformal pdmach)
              nil))
         (mesug-lst
          (collect-all-measure-suggestions measure-patterns
                                           flag-vformal pdmach)))
    (mv (initial-dmach1 flag-vformal flag-range pdmach)
        mesug-lst)))

; -----------------------------------------------------------------
; Section:  A Resource Limited Version of THM

; We implement a limited form of memoization below.  While the function
; resource-limited-thmp takes state, we do not memoize it and do not intend to
; pass the memo alist over changes to state.

; We sometimes expect memoization to pay off and sometimes not to.  So if the
; memo-alist arg is t it means don't use memoization; otherwise the memo-alist
; is exactly what you'd expect: an alist associating tuples of all the
; arguments (except state) with the value last computed.  We use memoization
; when we stamp measure suggestions; see stamp-mesug-for-dline.  We do not use
; memoization when we are computing the ``bare machine;'' see the description
; of the algorithm in the comment above bare-essential-hyps.

; By the way, anything called a ``termemo'' (``Terminatricks memo'') is a pair,
; (ans . memo-alist) where ans is the value the user wanted computed and
; memo-alist is just an updated memo-alist as manufactured and checked by
; resource-limited-thmp.

(defmacro termemo (ans memo-alist) `(cons ,ans ,memo-alist))
(defmacro termemo-ans (termemo) `(car ,termemo))
(defmacro termemo-alist (termemo) `(cdr ,termemo))

(defun resource-limited-thmp (conjecture step-limit hints otf-flg
                                         state memo-alist)

; We translate and attempt to prove conjecture under the given step-limit,
; hints, and otf-flg.  Memo-alist is either T or an alist that associates keys
; like `(,conjecture ,step-limit ,hints ,otf-flg) with the previously computed
; answer.  (We assume STATE hasn't changed, but I don't intend to keep the
; memo-alist from one event to another.)  If memo-alist is t, it means don't
; memoize and we just call the prover and return the Boolean answer indicating
; whether the prover succeeded or failed.  But if memo-alist is not t, we
; return (value (termemo ans memo-alist')) where ans is the Boolean answer and
; memo-alist' is a possibly updated memo-alist.

; All output is shut off!  To do silent, resource limited proof-search we
; actually open a log file and write everything to it, so the user can see the
; search tree if desired.

  (let* ((tuple (if (eq memo-alist t)
                    t
                    (list conjecture step-limit hints otf-flg)))
         (temp (if (eq memo-alist t)
                   nil
                   (assoc-equal tuple memo-alist))))
    (cond
     (temp
      (value (termemo (cdr temp) memo-alist)))
     (t (state-global-let*
         ((inhibit-output-lst *valid-output-names*)
          (gag-mode nil set-gag-mode-fn))
         (mv-let (erp val state)
                 (with-prover-step-limit!
                  step-limit
                  (thm-fn conjecture state hints otf-flg))
                 (declare (ignore val))
                 (value (if (eq memo-alist t)
                            (not erp)
                            (termemo (not erp)
                                     (cons (cons tuple (not erp)) memo-alist))))))))))

; -----------------------------------------------------------------
; Section:  Stamping Measure Suggestions and Adding Them to Distilled Machines

; Eventually below we will consider each of the suggested measures (in rank
; order) and for each measure, m, we will (a) stamp (as <, <= or
; possibly-growing) and add m to each line of the dmach, (b) look for a
; decreasing lexicographic measure, and (c) either quit or repeat depending on
; whether one is found.

; Here is how we do (a) above:  stamp and add a mesug to each dline

(defun remove-isolated-terms (vars term-lst)
; Delete any term in term-lst that has no variables in common with vars.
  (cond ((endp term-lst) nil)
        ((intersectp-eq vars (all-vars (car term-lst)))
         (cons (car term-lst)
               (remove-isolated-terms vars (cdr term-lst))))
        (t (remove-isolated-terms vars (cdr term-lst)))))

(defun make-measure-conjecture-from-mesug (rel mesug dline)

; We generate the formula representing the measure conjecture that must be
; proved for mesug to hold on dline.  Rel is < or <=.

; Warning: We actually throw out of the ruling-hyps any hypothesis that is
; independent of the variables in the conclusion!  Ours is a simpler conjecture
; than what ACL2's Defun Principle will have to prove, but its validity implies
; the conjecture that defun will prove.  We do this because our proof attempts
; are severely resource constrained and we don't want to fail on a valid
; measure just because some irrelevant hyp causes the simplifier to go out to
; lunch.  Such a failure could cause defunm to fail to discover a measure.
; Matt Kaufmann provided a nice proof that this technique does not sacrifice
; completeness at least for definitions that are not reflexive.  See the Essay
; on Eliminating Isolated Tests at the end of this book.

  (let* ((ruling-hyps (access dline dline :ruling-tests))
         (rhs (access measure-suggestion mesug :measure))
         (lhs
          (sublis-expr (access dline dline :sublis-expr-alist) rhs))
         (relevant-hyps
          (conjoin
           (remove-isolated-terms (all-vars1 lhs (all-vars rhs))
                                  ruling-hyps))))
    `(implies ,relevant-hyps
              (,rel ,lhs ,rhs))))

(defun stamp-mesug-for-dline (mesug dline step-limit state memo-alist)

; Given a mesug, we try to prove its corresponding measure conjectures (both
; for relation < and, if necessary, for <=.  We ``stamp'' the resulting mesug
; as follows:

; :stamp <                  proved strong descent on this line (and so can
;                            also infer weak descent)
; :stamp <=                 could not prove strong descent (within step-limit)
;                            but did prove weak descent
; :stamp POSSIBLY-GROWING   tried and failed to prove both strong and weak
;                            descent

; We return (value termemo) where termemo is a pair (mesug' . memo-alist'),
; where mesug' is the stamped mesug and memo-alist' is the updated memo alist.

; Note that a stamped mesug doesn't mean the measure goes down, even weakly! It
; only means that its :stamp reports what a step-limited proof could establish
; -- including that the suggestion can't be proved and may not hold at all!

  (er-let*
    ((strong-termemo
      (resource-limited-thmp
       (make-measure-conjecture-from-mesug '< mesug dline)
       step-limit nil nil state memo-alist))
     (weak-termemo
      (if (termemo-ans strong-termemo)
          (value strong-termemo)
          (resource-limited-thmp
           (make-measure-conjecture-from-mesug '<= mesug dline)
           step-limit nil nil state (termemo-alist strong-termemo)))))
    (let ((stamped-mesug
           (cond
            ((termemo-ans strong-termemo)
             (change measure-suggestion mesug :stamp '<))
            ((termemo-ans weak-termemo)
             (change measure-suggestion mesug :stamp '<=))
            (t (change measure-suggestion mesug :stamp 'POSSIBLY-GROWING)))))
      (value (termemo stamped-mesug
                      (termemo-alist weak-termemo))))))

(defun add-stamped-mesug-to-dmach (mesug dmach step-limit state memo-alist)
; We add a stamped mesug (with stamp <, <=, or POSSIBLY-GROWING) indicating
; whether the :measure in mesug decreases strongly, weakly, or possibly
; neither, to each line of dmach.  We return a termemo containing the extended
; dmach and the new memo alist.
  (cond
   ((endp dmach) (value (termemo nil memo-alist)))
   (t (er-let* ((stamped-mesug-termemo
                 (stamp-mesug-for-dline mesug (car dmach)
                                        step-limit state memo-alist))
                (rest-dlines-termemo
                 (add-stamped-mesug-to-dmach
                  mesug (cdr dmach) step-limit state (termemo-alist stamped-mesug-termemo))))
        (let ((new-dline
               (change dline (car dmach)
                       :measure-suggestion-lst
                       (cons (termemo-ans stamped-mesug-termemo)
                             (access dline (car dmach)
                                     :measure-suggestion-lst)))))
          (value (termemo (cons new-dline (termemo-ans rest-dlines-termemo))
                          (termemo-alist rest-dlines-termemo))))))))

; -----------------------------------------------------------------
; Section:  Weighing Flags

; Before we can carry out step (b) described above -- the search for a winning
; lexicographic measure -- we must describe how we assign weights to flags.
; Here's why and then how.

; When we build up a lexicographic measure we accumulate the winning sequence
; of mesugs in reverse order.  If we win, we'll make a LLIST term out of their
; :measures.  The name of our accumulator is rev-lex-mesug-lst.  Also, when we
; search for the lexicographic measure we gradually eliminate dlines from the
; dmach, relying on suggested measures that decrease, until we have no more
; mesugs that decrease.  Then we try to assign weights to the flag, if any, to
; explain the remaining dlines.

; Suppose that flag value a transitions (in the reduced dmach) to flag value b,
; b goes to c and d, and c goes to e.  Then call-graph-ordering tells us that c
; must be defined first, then b, then a.  Another way to look at it is that a
; must be heavier than b, b heavier than c and d, and c heavier than e.  We
; therefore build a measure like this:

; value  wt
; c      2
; b      3
; a      4
; others 1

(include-book "ordinals/lexicographic-ordering-without-arithmetic" :dir :system)

(defun assign-flag-weights1 (ordering wt)

; Ordering is the result of ordering the flag values as per the
; call-graph-ordering.  We assign each flag value a weight as per the two
; invariants: all flags in the same bucket of the ordering get the same weight
; and weights ascend from wt (initially 2) as we sweep down the ordering.  Note
; that we never assign weight 1.  We leave that to the construction of the
; final IF-expression.

  (cond
   ((endp ordering)
    nil)
   (t (append (pairlis-x2 (car ordering) (kwote wt))
              (assign-flag-weights1 (cdr ordering)
                                    (+ 1 wt))))))


(defun flag-transitions-alist1 (in-out-alist alist)
; For every pair (in . out-lst) in in-out-alist, union out-lst
; into the in entry in alist.
  (cond
   ((endp in-out-alist) alist)
   (t (flag-transitions-alist1
       (cdr in-out-alist)
       (put-assoc-equal
        (car (car in-out-alist))
        (union-equal (cdr (car in-out-alist))
                     (cdr (assoc-equal (car (car in-out-alist)) alist)))
        alist)))))

(defun flag-transitions-alist (dmach alist)
  (cond
   ((endp dmach) alist)
   (t (let ((in-out-alist
             (access dline (car dmach) :incoming-flag-to-outgoing-flag-alist)))
        (flag-transitions-alist
         (cdr dmach)
         (flag-transitions-alist1 in-out-alist alist))))))

(defun flag-recog-test-alist1 (in-to-test-alist alist)
  (cond
   ((endp in-to-test-alist) alist)
   (t (let ((temp (assoc-equal (car (car in-to-test-alist)) alist)))
        (cond
         (temp
          (cond ((equal (cdr (car in-to-test-alist))
                        (cdr temp))
                 (flag-recog-test-alist1 (cdr in-to-test-alist) alist))
                (t (er hard 'flag-recog-test-alist1
                       "How can one incoming flag value, ~x0, be mapped to ~
                        two different recognizing test expressions, namely, ~
                        ~x1 and ~x2?"
                       (car (car in-to-test-alist))
                       (cdr temp)
                       (cdr (car in-to-test-alist))))))
         (t (flag-recog-test-alist1 (cdr in-to-test-alist)
                                    (cons (car in-to-test-alist) alist))))))))

(defun flag-recog-test-alist (dmach alist)
  (cond
   ((endp dmach) alist)
   (t (let ((in-to-test-alist
             (access dline (car dmach) :incoming-flag-to-recog-term-alist)))
        (flag-recog-test-alist
         (cdr dmach)
         (flag-recog-test-alist1 in-to-test-alist alist))))))

; Suppose dmach has (non-nil) flag flag-vformal but doesn't change the flag on
; some call.  Then no measure of the flag will explain dmach.  For example,
; suppose pc is the flag and when it is equal to 10 the outgoing call passes pc
; or 10 into the pc slot.  Then no measure of pc alone will work.  These two
; cases, `pc' or an explicit value that happens to be the same, are identified
; differently because we don't store slot expressions like (:SLOT pc pc) for
; unchanging vformals.

(defun flag-identity-transition1p (flag-vformal dmach)
; Does dmach contain a dline with no SLOT for the flag?
  (cond
   ((endp dmach) nil)
   ((assoc-equal flag-vformal (access dline (car dmach) :sublis-expr-alist))
    (flag-identity-transition1p flag-vformal (cdr dmach)))
   (t t)))

(defun flag-identity-transition2p-in-out-alist (alist)
; Does alist contain a pair such as (key . (... key ...))?
  (cond
   ((endp alist) nil)
   ((member-equal (car (car alist))
                  (cdr (car alist)))
    t)
   (t (flag-identity-transition2p-in-out-alist (cdr alist)))))

(defun flag-identity-transition2p (dmach)
; Does dmach contain a line where the incoming and outgoing values of
; the flag are the same?
  (cond
   ((endp dmach) nil)
   ((flag-identity-transition2p-in-out-alist
     (access dline (car dmach) :incoming-flag-to-outgoing-flag-alist))
    t)
   (t (flag-identity-transition2p (cdr dmach)))))

(defun flag-identity-transitionp (flag-vformal dmach)
  (or (flag-identity-transition1p flag-vformal dmach)
      (flag-identity-transition2p dmach)))

(defun assign-flag-weights (dmach)

; We return two alists, wt-alist and test-alist.  The first, wt-alist, maps
; certain flag values to weights of at least 2.  Flag values with weight 1 are
; not assigned in this alist; it is reserved as the ultimate default value of
; the IF-expression we'll build expressing the measure term.  The second
; result, test-alist, maps certain flag values to the tests that recognized
; them and we'll use those tests in our IF-expression.

  (let* ((transition-alist (flag-transitions-alist dmach nil))
         (test-alist (flag-recog-test-alist dmach nil))
         (ordering (call-graph-ordering transition-alist)))

; If all elements are in the same bucket of the ordering and that bucket
; contains all the outgoing flag values as well, then all the relevant flags
; will be assigned the same weight and we've lost.

    (cond ((and (consp ordering)
                (null (cdr ordering))
                (subsetp-equal (strip-cdrs transition-alist) (car ordering)))
           (mv nil nil))
          (t (mv (assign-flag-weights1 ordering 2)
                 test-alist)))))

(defun convert-flag-weight-alist-to-if-expr (wt-alist test-alist)
; Wt-alist maps each flag value to a weight; test-alist maps each flag value to
; a recognizing term.  We return an IF-expression expressing the measure.
  (cond
   ((endp wt-alist) *1*)
   ((not (assoc-equal (car (car wt-alist)) test-alist))
    (er hard 'convert-flag-weight-alist-to-if-expr
        "It was thought that every key in wt-alist, ~x0, was associated with ~
         a test in test-alist, ~x1.  But that is not the case!"
        wt-alist test-alist))
   (t `(IF ,(cdr (assoc-equal (car (car wt-alist)) test-alist))
           ,(cdr (car wt-alist))
           ,(convert-flag-weight-alist-to-if-expr (cdr wt-alist) test-alist)))))

(defun find-decreasing-flag-weights (dmach rev-lex-mesug-lst)

; Dmach is a non-empty distilled machine.  We get its flag variable, if any,
; and try to invent a mesug that assigns weights to the flag values so as to
; explain all the lines in dmach.  If so, we accumulate it onto
; rev-lex-mesug-lst and win; else we lose.

  (let ((flag-vformal (access dline (car dmach) :flag-vformal)))
    (cond
     ((null flag-vformal) nil)
     ((flag-identity-transitionp flag-vformal dmach) nil)
     (t (mv-let
         (wt-alist test-alist)
         (assign-flag-weights dmach)
         (cond
          ((null wt-alist) nil)
          (t (cons (convert-flag-weight-alist-to-if-expr wt-alist test-alist)
                   rev-lex-mesug-lst))))))))

; -----------------------------------------------------------------
; Section:  Putting Together a Lexicographic Measure

; Now we do step (b) described above: we try to piece together a decreasing
; lexicographic measure for a dmach.  We actually accumulate a list of measure
; terms rev-lex-measure-lst, such that when listed in reverse order and put
; together with LLIST they constitute a decreasing lexicographic measure.
; (`Rev-Lex-Measure-Lst' stands for ``reversed lexicograph measure list.'')

; The basic idea is to find a measure that definitely decreases in at least one
; dline and is definitely non-increasing in all the others.  We do this by
; counting, for each measure mentioned in the dmach, the number of dlines the
; stamp is <, aborting with a ``count'' of nil if we find a stamp of
; possibly-growing.  For each such sometimes decreasing and never increasing
; measure, we recur after (a) adding the measure to our evolving
; rev-lex-measure-lst, (b) deleting from dmach the dlines on which the measure
; definitely decreases, and (c) deleting the corresponding mesugs from all
; surviving dlines.  If we reach the empty machine, rev-lex-measure-lst
; identifies a decreasing lexicographic measure.  If we reach a machine with no
; sometimes decreasing measures, we use the flag analysis above to try to
; explain the remaining lines.  If so, we add it to the list and win.  If not,
; we lose.  The function that implements this algorithm is defined at the end
; of this section and is named find-rev-lex-measure-lst-dmach .

(defun all-measures-in-dmach (dmach)

; We return the set of :measures mentioned in the mesugs of dmach.  We exploit
; the observation that every dline of a dmach mentions the same set of
; :measures in its :measure-suggestion-lst.  (The difference across dlines is
; merely how they're stamped.)  So we need only collect the :measures of the
; first dline.

; Note: (access measure-suggestion mesug :measure) = (cadr mesug)!

  (strip-cadrs (access dline (car dmach) :measure-suggestion-lst)))

(defun measure-decreases-cnt (measure dmach k)

; We return the number of times, k, that measure strictly decreases in dlines
; of dmach.  However, if we find a line in which measure is possibly growing,
; we return NIL.  K should initially be 0.

; Note (access measure-suggestion mesug :measure) = (cadr mesug).

  (cond
   ((endp dmach) k)
   (t (let* ((mesug
              (assoc-equal-cadr
               measure
               (access dline (car dmach) :measure-suggestion-lst)))
             (stamp (access measure-suggestion mesug :stamp)))
        (cond
         ((eq stamp '<)
          (measure-decreases-cnt measure (cdr dmach) (+ 1 k)))
         ((eq stamp '<=)
          (measure-decreases-cnt measure (cdr dmach) k))
         (t nil))))))

(defun measure-decreases-cnt-pairs-lst (measure-lst dmach)
; Return the list of all sometimes decreasing and never increasing measures,
; paired with their counts.  This is the main workhorse function of the
; function below.
  (cond
   ((endp measure-lst) nil)
   (t (let ((cnt (measure-decreases-cnt (car measure-lst) dmach 0)))
        (cond
         ((or (null cnt)
              (equal cnt 0))
          (measure-decreases-cnt-pairs-lst (cdr measure-lst)
                                           dmach))
         (t (cons (cons cnt
                        (car measure-lst))
                  (measure-decreases-cnt-pairs-lst (cdr measure-lst)
                                                   dmach))))))))

(defun sometimes-decreasing-never-increasing-measures (dmach)

; Return an ordered list of pairs (cnt . measure), where cnt is the number of
; dlines in which measure strictly decreases without ever increasing, highest
; cnt first.

  (strip-cdrs
   (merge-sort-car->
    (measure-decreases-cnt-pairs-lst
     (all-measures-in-dmach dmach)
     dmach))))

(defun eliminate-measure-from-dmach (measure dmach)
; See the basic idea sketched at the top of this section.

; Note (access measure-suggestion mesug :measure) = (cadr mesug).
  (cond
   ((endp dmach) nil)
   (t (let ((mesug
             (assoc-equal-cadr measure
                               (access dline (car dmach)
                                       :measure-suggestion-lst))))
; Every dline contains a stamped mesug for every known measure!
        (cond
         ((eq (access measure-suggestion mesug :stamp)
              '<)
          (eliminate-measure-from-dmach measure (cdr dmach)))
         (t (cons (change dline (car dmach)
                          :measure-suggestion-lst
                          (remove1-equal mesug
                                         (access dline (car dmach)
                                                 :measure-suggestion-lst)))
                  (eliminate-measure-from-dmach measure (cdr dmach)))))))))

(mutual-recursion

(defun find-rev-lex-measure-lst-dmach (dmach rev-lex-measure-lst)
; See the description of this algorithm at the top of the section.
  (cond
   ((endp dmach)
    rev-lex-measure-lst)
   (t (let ((measures
             (sometimes-decreasing-never-increasing-measures dmach)))
        (cond
         ((null measures)
          (find-decreasing-flag-weights dmach rev-lex-measure-lst))
         (t (find-rev-lex-measure-lst-dmach*
             measures
             dmach
             rev-lex-measure-lst)))))))

(defun find-rev-lex-measure-lst-dmach* (measures dmach rev-lex-measure-lst)
  (cond
   ((endp measures) nil)
   (t (or (find-rev-lex-measure-lst-dmach
           (eliminate-measure-from-dmach
            (car measures)
            dmach)
           (cons (car measures) rev-lex-measure-lst))
          (find-rev-lex-measure-lst-dmach* (cdr measures)
                                           dmach rev-lex-measure-lst))))))

; -----------------------------------------------------------------
; Section:  Adding Stamped Measures and Searching for Lex Measures

; Now we implement the algorithm that alternately adds a new stamped measure to
; each dline of dmach and searches for a winning lexicographic measure.

(defun stamp-mesugs-and-search-win (rev-lex-measure-lst wrld)

; This is the ``winning exit function'' of stamp-mesugs-and-search, below.  It
; is used when we've won and wish to assemble the winning lexicographic measure
; into an untranslated term and its corresponding well-founded relation.
; We return the pair containing those two things.

  (cond
   ((null (cdr rev-lex-measure-lst))
    (cons (untranslate (car rev-lex-measure-lst) nil wrld)
          'o<))
   (t (cons (untranslate
             (cons 'LLIST (revappend rev-lex-measure-lst nil))
             nil wrld)
            'L<))))

(defun stamp-mesugs-and-search (mesug-lst dmach step-limit state memo-alist)

; To a first approximation we return either nil or a pair consisting of an
; untranslated winning measure term and its corresponding well-founded
; relation.  But actually we return a value triple containing a termemo
; containing those two results along with the accumulated memo-alist.
; Precisely: we return (value (ans . memo-alist')), where ans is either nil or
; (measure . well-founded-relation).

  (cond
   ((null mesug-lst) (value (termemo nil memo-alist)))
   (t (er-let*
        ((dmach1-termemo
          (add-stamped-mesug-to-dmach (car mesug-lst) dmach step-limit state memo-alist)))
        (let ((rev-lex-measure-lst
               (find-rev-lex-measure-lst-dmach (termemo-ans dmach1-termemo) nil)))
          (cond
           ((null rev-lex-measure-lst)
            (stamp-mesugs-and-search (cdr mesug-lst)
                                     (termemo-ans dmach1-termemo)
                                     step-limit state
                                     (termemo-alist dmach1-termemo)))
           (t (value
               (termemo
                (stamp-mesugs-and-search-win rev-lex-measure-lst
                                             (w state))
                memo-alist)))))))))

; =================================================================

; Chapter 2 (Code):  Learning from User-Supplied Measures

;   Chapter Summary: We learn from user-supplied DEFUNs with explicit :measures
;   supplied by the user, extending our measure patterns table by paring down
;   the user's induction machine so that it only mentions those tests necessary
;   to prove the measure conjecture and implementing a notion of subsumption
;   among patterns so that the database is not cluttered with duplications.

; We recommend re-reading the introductory discussion of this topic, which may
; be found above under Chapter 2 (Discussion).

; This chapter ultimately concludes with the definitions of
; add-measure-patterns-to-data-base and slightly later update-measure-patterns.
; The former adds new patterns to a list of known patterns and the latter
; actually does that, describes the changes, and installs the result as the new
; table.

; -----------------------------------------------------------------
; Section:  Identifying User-Provided Measures

; It is necessary to distinguish user-supplied measures from ones guessed by
; DEFUNM.  Thus, there are basically three kinds of DEFUN:  those where no :measure
; was supplied and is thus ACL2-COUNT of the first argument tested and changed on every
; recursion, those in which an explicit :measure is supplied by the user, and those
; in which an explicit measure is supplied by DEFUNM.

; So we use the following identity macro for marking defun events generated by
; successful DEFUNM events.  DEFUNM wraps its guessed measure in this macro.
; The macro call is preserved in the event-landmark laid down, but is
; eliminated in all the logical work, including the JUSTIFICATION records.  If
; we made this symbol an identity function it would start to build up in
; learned measures as in (defunm-marker (defunm-marker (acl2-count x))).

(defmacro DEFUNM-MARKER (x) x)

; The following code is in support of measure-hint-in-defunp, which determines
; whether an event form is a DEFUN with an explicit :MEASURE.  When we find an
; explicit :MEASURE we indicate whether it was generated by DEFUNM or the user,
; keying on the presence of the DEFUNM-MARKER identity function as the
; top-level function symbol of the measure.

(defun measure-hint-in-xargs (x)
  (cond ((atom x) nil)
        ((eq (car x) :measure)
         (if (and (consp (cdr x))
                  (consp (cadr x))
                  (eq (car (cadr x)) 'DEFUNM-MARKER))
             'DEFUNM
             t))
        (t (measure-hint-in-xargs (cddr x)))))

(defun measure-hint-in-dcl-lst1 (x)
  (cond ((endp x) nil)
        ((and (consp (car x))
              (eq (car (car x)) 'xargs))
         (or (measure-hint-in-xargs (cdr (car x)))
             (measure-hint-in-dcl-lst1 (cdr x))))
        (t (measure-hint-in-dcl-lst1 (cdr x)))))

(defun measure-hint-in-dcl-lst (x)
  (cond
   ((endp x) nil)
   ((and (consp (car x))
         (equal (car (car x)) 'declare))
    (or (measure-hint-in-dcl-lst1 (cdr (car x)))
        (measure-hint-in-dcl-lst (cdr x))))
   (t nil)))

(defun measure-hint-in-defunp (event)

; Is event a DEFUN with an explicit :MEASURE?  If so, was it [probably]
; generated by DEFUNM or the user?  We return NIL, DEFUNM, or T with the
; obvious meanings: no measure, a measure generated by DEFUNM, or a measure
; generated by the user.  We say ``probably'' above because nothing prevents
; the user from marking one of his or her measures with DEFUNM-MARKER.

  (and (consp event)
       (eq (car event) 'defun)
       (measure-hint-in-dcl-lst (all-but-last (cdddr event)))))

; -----------------------------------------------------------------
; Section:  Collecting the Defuns from which Patterns are Built

; A successful DEFUNM may execute a TABLE event updating the measure-patterns
; table followed chronologically by a DEFUN.  (It may also prove some
; non-recursive flag lemmas as discussed in Chapter 3.)  Any DEFUN event
; generated by DEFUNM is marked as such by the presence of the DEFUNM-MARKER
; identity macro at the outermost function symbol in the measure.  In the
; update phase, we will scan the world from :here to the last time the
; measure-pattern table was updated or until the last time a DEFUNM was done,
; and collect any intervening DEFUN events with :MEASUREs.

; A subtlety in this design is that a successful DEFUNM generates a DEFUN event
; with a :MEASURE hint.  Do we collect that last DEFUNM?  Can we learn anything
; from a successful DEFUN we generated from the measure-patterns?  Yes!

; To discuss this more precisely, let's give names to the relevant commands and
; events.  Suppose we are trying to execute a DEFUNM command, cmd1, which will
; in fact first execute a TABLE event, tbl1, to update the measure-patterns,
; and then, after speculatively trying the suggested measures, will execute a
; successful (and DEFUNM-MARKER marked) DEFUN event, def1.  In the first phase
; of the DEFUMN processing, it will scan the world from :here to the last
; measure-patterns TABLE event or the last DEFUNM event (even if it did not
; generate a TABLE event because nothing new was learned).  Let the earlier
; DEFUMN command be cmd0 with event def0 (with or without a chronologically
; preceding table event).  The measure used for def0 was generated after
; checking and possibly updating the table.  Let the table that generated
; def0's measure be tbl0.  That table might be further updated in light of the
; success of def0.

; Here is how.  Suppose tbl0 contains an unnecessarily complicated
; measure-pattern, say with many extra :tests, because it was suggested by a
; function with lots of case analysis in it.  Suppose def0 is much simpler, say
; fewer tests, but was explained by the same measure and was generated because
; the complicated pattern suggested the measure.  That suggestion might have
; had a low rank since def0 did not have all the (unnecessary) tests in the
; tbl0 pattern.  If cmd1 incrementally updates the table with tbl1 it will
; compare the measure-pattern implied by def0 with the measure-pattern in tbl0
; and could replace that overly complicated pattern with a simpler one.  That
; means subsequent suggestions of that measure will have higher rank.

; It is thus worthwhile to collect not just intervening user DEFUNs with
; explicit :measures but to also collect the function introduced by the most
; recent DEFUNM.

(defun collect-fns-for-incremental-mp-update (wrld fns)
  (let ((wrld (scan-to-event wrld)))
    (cond
     ((endp wrld)

; We return the fns in chronological order so we process
; generate their implied patterns in that order.

      fns)
     (t (let ((event (access-event-tuple-form (cddr (car wrld)))))
          (cond
           ((and (eq (car event) 'table)
                 (eq (cadr event) 'measure-patterns))
            fns)
           (t (let ((measurep (measure-hint-in-defunp event)))
                (cond
                 ((null measurep)
                  (collect-fns-for-incremental-mp-update (cdr wrld) fns))
                 ((eq measurep 'DEFUNM)
; We stop here, but we do add the function symbol admitted by this DEFUNM.
                  (add-to-set-eq (cadr event) fns))
                 (t (collect-fns-for-incremental-mp-update
                     (cdr wrld)
                     (add-to-set-eq (cadr event) fns))))))))))))

(defun filter-fns-for-appropriate-measures (fns ens wrld)
; We collect the fns in fns that have justifications with natural number measures
; and decrease according to O< over the ordinals.
  (cond
   ((endp fns) nil)
   (t (let* ((fn (car fns))
             (just (getprop fn 'justification nil 'current-acl2-world wrld)))
        (cond
         ((and just
               (eq (access justification just :mp) 'O-P)
               (eq (access justification just :rel) 'O<)
               (mv-let (ts ttree)
                       (type-set (access justification just :measure)
                                 nil nil nil ens wrld nil nil nil)
                       (declare (ignore ttree))
                       (not (ts-subsetp *ts-cons* ts))))
; If the domain of the well-founded relation is O-P then we know that if
; the type-set of the measure does not include CONS the measure is a natural
; number.
          (cons fn (filter-fns-for-appropriate-measures (cdr fns) ens wrld)))
         (t (filter-fns-for-appropriate-measures (cdr fns) ens wrld)))))))

; -----------------------------------------------------------------
; Section: Constructing Measure Patterns from Admitted Defuns

; Having identified the function symbols we wish to consider, we now turn to
; the question of deriving measure-patterns (if any) from the successful
; admission of a fn.  The idea is to derive a pattern from every call in the
; induction-machine, suggesting the measure in the justification of the
; function.  We only do this for NATP valued measures with
; well-founded-relation o<.  Note that this means the relation is always <.
; (Since we never learn from lexicographic measures, we never see a line where
; the operative measure merely stays fixed or weakly decreases.)

; Remember that an induction machine is a list of tests-and-calls -- not
; tests-and-CALL -- and that some of the :calls fields are nil, indicating base
; cases.  Some key problems in generating patterns from induction machines are
; that the tests may involve IF-expressions (e.g., the IF-form of (OR a b))
; causing splits and some tests are not necessary for termination (e.g., the
; (EQUAL E (CAR X)) in the definition of (MEM E X).  If we allow these
; overly-complicated tests to generate measure patterns, we get a lot of bogus
; and impractical patterns.

; TODO: We may eventually need to handle virtual formals here.  But at the
; moment we limit ourselves just to formals.

; Here is a sketch of the main steps.

;  (0) Convert the induction-machine into a syntactically bare essentials
;  machine consisting entirely of pairs (tests . subst), where tests are the
;  syntactically relevant distilled tests governing some call and subst is the
;  relevant components of the formals-to-actuals substitution for that call.

;  (1) For each pair in the syntactically bare essentials machine, discard any
;  pair for which the requisite measure theorem cannot be proved (within our
;  resource bounds) and then eliminate any unnecessary tests.  The result is a
;  bare-essentials-machine.

;  (2) For each pair in the bare essentials machine, create a measure pattern.

; We now implement each of these steps, in separate sections.

; -----------------------------------------------------------------
; Section:  Syntactically Bare Essential Machine

;  (0) Convert the induction-machine into a syntactically bare essentials
;  machine consisting entirely of pairs (tests . subst), where tests are the
;  syntactically relevant distilled tests governing some call and subst is the
;  relevant components of the formals-to-actuals substitution for that call.

; Thus, each pair of the syntactically bare essentials machine concerns one
; call and only the tested literals needed for that one call.

; The tests are implicitly conjoined, free of all propositional connectives
; (other than NOT), and syntactically minimal (i.e., only mention vars somehow
; relevant to the concluding measure inequality) for that call, and listed in
; ascending term order.

; The idea is to pare down the tests and substitution to bare essentials by
; syntactic criteria only.  By getting rid of propositional connectives (like
; OR) and splitting out the cases, we can make patterns that are more likely to
; fire on -- and only on -- essential conditions.

; For example, if the measure is (m x) and the call maps formals (x y z) to (+
; x y), y', and z', and the tests are (p x), (q y), (r x y), (a z), then we
; return the pair containing tests ((p x) (q y) (r x y)) and the substitution
; ((x . (+ x y))).  The y and z pairs are discarded from the substitution
; because they are not important to the measure or the measure theorem.  The
; test (a z) is discarded because it is not relevant.  But the test (q y) is
; kept because it is linked to x by (r x y), which is also kept.

; First we develop a way to partition the tests according to the variables
; they somehow use.

(defun pair-vars-with-tests (tests)
  (cond ((endp tests) nil)
        (t (cons (cons (all-vars (car tests)) (list (car tests)))
                 (pair-vars-with-tests (cdr tests))))))

(defun partition-tests-by-vars (tests)

; Given a set of terms, tests, we build a partitioning of the tests in which
; each partition contains all the tests that share a set of variables.  Thus,
; if (P x), (Q y), and (R x y) are among the tests, they end up in the same
; partition, whereas (A u), (B v), and (C z) each end up in separate
; partitions.  We return a set of pairs, each pair being (vars' . tests') where
; vars' is some subset of the variables occurring in tests and tests' are all
; the variables somehow mentioning vars'.  The tests' form a partitioning of
; the tests (and the vars' form a partitioning of the variables in the tests).

  (m&m (pair-vars-with-lits tests)
       'intersectp-eq/union-equal))

; Next we recover the tests somehow using certain variables.

(defun find-partition-containing (var partitioning)

; Partitioning is a list of pairs, (vars' . tests').  We return the
; first pair such that its vars' includes var as a member.

  (cond ((endp partitioning) nil)
        ((member-eq var (car (car partitioning)))
         (car partitioning))
        (t (find-partition-containing var (cdr partitioning)))))

(defun syntactically-relevant-tests (vars partitioning)

; See relevant-tests for context.  Vars is a list of variables, some subset of
; all the variables in some theorem.  Partitioning is a list of pairs, each of
; the form (vars' . tests'), where vars' is a list of variables and tests'
; are all (and only) the tests mentioning vars'.  The sets of vars' form a
; partitioning of all the variables in the problem.  Loosely put, each pair
; contains an independent clique of variables and all the tests somehow
; involving just those variables.  We collect all the tests somehow involving
; any variable in vars.

  (cond ((endp vars) nil)
        (t (union-equal
            (cdr (find-partition-containing (car vars) partitioning))
            (syntactically-relevant-tests (cdr vars) partitioning)))))

; Here we throw out substitution pairs that are not relevant to the target
; variables.

(defun relevant-subst-pairs (vars alist)
  (cond ((endp vars) nil)
        (t (cons (assoc-eq (car vars) alist)
                 (relevant-subst-pairs (cdr vars) alist)))))

; And here we put it all together to create a syntactically minimal set of
; tests implying measure decreases under subst.

(defun syntactically-relevant-tests-and-subst-pair (tests measure subst)

; Assuming that tests imply that measure/subst < measure, syntactically minimize
; tests and subst by throwing out irrelevant tests and substitution pairs.
; Return (tests' . subst').

  (let* ((measure-vars ; all vars in measure
          (all-vars measure))
         (concl-vars ; all vars in (< measure/subst measure).
          (all-vars1 (sublis-var subst measure)
                     measure-vars)))

; TODO: I sort the hyps, simplest first.  Maybe I should reverse that?  The
; question is, do we want the proof search to eliminate the simplest first or
; the most complicated first?  Does it make a difference?

    (cons (merge-sort-term-order
           (syntactically-relevant-tests concl-vars
                                         (partition-tests-by-vars tests)))
          (relevant-subst-pairs measure-vars subst))))

(defun syntactically-bare-essentials-machine2 (formals tests measure calls)
  (cond
   ((endp calls) nil)
   (t (add-to-set-equal
       (syntactically-relevant-tests-and-subst-pair
        tests
        measure
        (pairlis$ formals (fargs (car calls))))
       (syntactically-bare-essentials-machine2
        formals tests measure
        (cdr calls))))))

(defun syntactically-bare-essentials-machine1 (formals tests-lst measure calls)
  (cond
   ((endp tests-lst) nil)
   (t (union-equal
       (syntactically-bare-essentials-machine2
        formals
        (car tests-lst)
        measure calls)
       (syntactically-bare-essentials-machine1
        formals
        (cdr tests-lst)
        measure calls)))))

(defun syntactically-bare-essentials-machine (formals measure imach)
  (cond
   ((endp imach) nil)
   ((null (access tests-and-calls (car imach) :calls))
    (syntactically-bare-essentials-machine formals measure (cdr imach)))
   (t (append
       (syntactically-bare-essentials-machine1
        formals
        (conjunction-to-dnf
         formals
         (access tests-and-calls (car imach) :tests))
        measure
        (access tests-and-calls (car imach) :calls))
       (syntactically-bare-essentials-machine formals measure (cdr imach))))))

; -----------------------------------------------------------------
; Section:  Semantically Essential Machines

; The crux of the idea is identifying the semantically essential hypotheses as
; efficiently as we can.

; The algorithm below takes a set of hyps and a concl, and -- providing hyps
; and concl satisfy a certain ill-defined ``prime mover'' condition -- returns
; either nil or a smallest subset of the hyps that provably implies concl with
; given resource constraints.  The ``prime mover'' condition means that there
; is a unique subset of hyps that implies concl.  If this is not true, the
; algorithm may not find the smallest such subset.  The algorithm works in
; log-time assuming the proof attempts occur in constant time.  It is based on
; the following theoretically valid assumption that does not actually hold in
; practice: If hyps' is a subset of hyps and (hyps --> concl) cannot be proved,
; then (hyps' --> concl) cannot be proved.  The practical fly in this
; theoretical ointment is that an irrelevant hyp might send the prover into a
; black hole and cause it to exhaust the resource bounds, while the elimination
; of that irrelevant hypothesis eliminates the gateway into the black hole and
; will produce an easily provable theorem.  We just hope that doesn't happen
; often!

; The algorithm accurately identifies a subset of hyps that provably implies
; concl within the resource bounds, but if the prime mover condition is
; violated or some hyp is a black hole for the prover the algorithm may not
; return the smallest such subset.

; The algorithm:

; If hyps --> concl cannot be proved, fail.  Else, try each of the immediate
; subsets (the subsets obtained by deleting exactly one element) of hyps.  If
; they all fail, then hyps is a smallest subset.  If one of them succeeds with
; answer hyps', then hyps' is a smallest subset.

; Note that since we're potentially trying all subsets of the hyps, there's no
; reason to use memoization on the calls to resource-limited-thmp: every call
; is on a different formula.

; In earlier versions of this, we enumerated all subsets of the hyps and tried
; each -- an exponential time algorithm.  Of course, if the winning subset
; happens to occur early in the enumeration, the exponential method will beat
; the log-time one.

; On the prime mover condition: Suppose hyps is (A B C) and concl is D and
; suppose that both (A --> D) and (B & C) --> D, but neither B nor C alone
; implies D.  Depending on the order in which things are tried, the algorithm
; might identify (B C) as the ``smallest'' adequate subset, even though (A) is
; smaller.  The reason is that when it drops A it can prove ((B&C)-->D) and
; nothing smaller for that subset.

; We could remove the condition by continuing to search after finding a
; smallest subset.  For example, if after identifying (B C) as a smallest
; subset it nevertheless tried (A B) and/or (A C), it would then discover that
; (A) was adequate.  Then we could choose between (A) and (B C).

; One way the prime mover condition could be violated is if (A --> (B&C)).  For
; example, let A be (CONSP x), B be (TRUE-LISTP x), and C be (NOT (EQUAL x
; NIL)).  This situation probably doesn't arise much in practice because in
; practice the hyps are all tests explicitly written by the user in a function
; definition and users almost never intentionally write an IF that tests a
; condition already known to be true.  (An exception to this rule: situations
; where MBT is used.)

; But ((A X) & (B Y) & (C Z)) --> ((A X) v ((B Y) & (C Z))) is an example of
; three completely independent hypotheses that lead to two adequate and
; irreducible subsets, one of which is smaller than the other.  I only chose a
; first order example (instead of the propositional root of the example (a & b)
; --> (a v b)) because our applications all involve variables and by choosing
; distinct variables we make it clear that the hypotheses are independent.

; However, I suspect that in our situation, the prime mover condition almost
; always holds: there is one reason the tests imply that the measure decreases.

; TODO: A clearly superior way would be to first see if certain known
; conditions are met, e.g., see if the implication is subsumed by

; (not (zp x)) --> (< (acl2-count (- x 1)) (acl2-count x))

; and if so pick out just the relevant instance of (not (zp x)).  The idea
; would then be to use a few smart heuristics to eliminate the bulk of the
; common cases and then the log-time approach in general.  If it is thought
; that the singleton hyps case is common, we could try all of singleton hyps
; before the log-time approach, and modify the log-time approach so as not to
; do any singletons.

; TODO: Explore the possibility that the prime mover condition is violated,
; by doing the search above.

; TODO: Consider step-count propagation: One could make the full search
; slightly less inefficient by reducing the resources available.  For example,
; returning to the ((A & B & C) --> D) example above, if (B&C) --> D is
; provable in k steps, as reported by (last-prover-steps state), then one could
; limit the attempts at (B --> D) and (C --> D) to k steps.  Furthermore, after
; identifying (B C) as an adequate subset, one could limit (A & B) --> D and (A
; & C) --> D to k steps as well.

; We should pursue these after getting the rest to work!

(mutual-recursion

; We implement the algorithm described above for finding a smallest subset of
; hyps that implies concl.  See the description above.  We assume that the
; empty hyps do not imply concl and thus use nil to signal failure.

(defun bare-essential-hyps (hyps concl step-limit hints otf-flg state)

; Return (value nil) if hyps --> concl cannot be proved with the given
; resources and hints.  Else, return (value hyps') where hyps' is a smallest
; subset of hyps such that hyps' --> concl can be proved with the resources and
; hints.

  (er-let*

; Note: memo-alist = t in the call resource-limited-thmp below means
; memoization is not to be used and the answer is just the Boolean one: did we
; prove it or not?

    ((thmp (resource-limited-thmp `(IMPLIES (AND ,@hyps) ,concl)
                                  step-limit hints otf-flg state t)))
    (cond
     (thmp
      (bare-essential-hyps-lst hyps hyps concl step-limit hints otf-flg state))
     (t (value nil)))))

(defun bare-essential-hyps-lst (hyps hyps0 concl step-limit hints otf-flg state)

; hyps0 --> concl succeeded.  We now try each immediate subset of hyps0.

  (cond
   ((endp hyps) (value hyps0))
   (t (er-let*
        ((ans (bare-essential-hyps (remove1-equal (car hyps) hyps0) concl
                                   step-limit hints otf-flg state)))
        (cond
         (ans (value ans))
         (t (bare-essential-hyps-lst (cdr hyps) hyps0 concl
                                     step-limit hints otf-flg state))))))))

(defun bare-essential-machine1
  (syn-bare-mach measure step-limit hints otf-flg state)
  (cond
   ((endp syn-bare-mach)
    (value nil))
   (t (let* ((hyps (car (car syn-bare-mach)))
             (subst (cdr (car syn-bare-mach)))
             (concl (fcons-term* '<
                                 (sublis-var subst measure)
                                 measure)))
        (er-let*
          ((hyps1
            (bare-essential-hyps hyps concl step-limit hints otf-flg state)))
          (cond
           ((null hyps1)
            (bare-essential-machine1 (cdr syn-bare-mach)
                                     measure step-limit hints otf-flg state))
           (t (er-let* ((rest-mach
                         (bare-essential-machine1 (cdr syn-bare-mach)
                                                  measure step-limit
                                                  hints otf-flg state)))
                (value (add-to-set-equal (cons hyps1 subst) rest-mach))))))))))

(defun bare-essential-machine
  (syn-bare-mach measure step-limit hints otf-flg state)
; At one point I did some io here.
  (bare-essential-machine1 syn-bare-mach measure
                           step-limit hints otf-flg state))

; -----------------------------------------------------------------
; Section:  Create a Measure-Pattern

(defun alist-to-slot-pseudo-terms (alist)
  (cond ((endp alist) nil)
        ((equal (car (car alist))
                (cdr (car alist)))
         (alist-to-slot-pseudo-terms (cdr alist)))
        (t (cons (list :SLOT (car (car alist)) (cdr (car alist)))
                 (alist-to-slot-pseudo-terms (cdr alist))))))

(defun derived-measure-patterns1 (fn measure vars bare-essential-mach)
  (cond
   ((endp bare-essential-mach) nil)
   (t (cons
       (make-measure-pattern
        :name fn
        :measure measure
        :vars vars
        :tests (car (car bare-essential-mach))
        :slots (alist-to-slot-pseudo-terms (cdr (car bare-essential-mach)))
        :invariants nil)
       (derived-measure-patterns1 fn measure vars
                                  (cdr bare-essential-mach))))))

(defun derived-measure-patterns (fn state)

; Fn is a recursively defined function name in the world of state and its
; justification contains a NATP valued measure over the domain O-P with
; relation O<.  We return a set of measure-patterns derived from the induction
; machine stored for fn.

  (let* ((wrld (w state))
         (formals (formals fn wrld))
         (measure (access justification
                          (getprop fn 'justification nil
                                   'current-acl2-world wrld)
                          :measure))
         (vars (all-vars measure))
         (mach0
          (syntactically-bare-essentials-machine
           formals measure
           (getprop fn 'induction-machine nil
                    'current-acl2-world wrld))))
    (er-let*
      ((mach1
        (bare-essential-machine mach0 measure 1000 nil nil state)))
      (value (derived-measure-patterns1 fn measure vars mach1)))))

(defun derived-measure-patterns-lst (fns state)
  (cond
   ((endp fns) (value nil))
   (t (er-let*
        ((mp-lst1 (derived-measure-patterns (car fns) state))
         (mp-lst2 (derived-measure-patterns-lst (cdr fns) state)))
        (value (append mp-lst1 mp-lst2))))))

; -----------------------------------------------------------------
; Section:  Adding Measure Patterns to the Database

; Aside:  Our basic design of DEFUNM calls for computing the new list of measure
; patterns, using it to justify the current DEFUNM event, and then installing
; the new patterns in the measure-patterns table.  Thus, our comments are really
; concerned with adding new measure patterns to a list of other measure patterns
; (that will eventually become the database).

; Next we consider how to determine whether we should replace one measure
; pattern by another.  Under what conditions is one mp better than another?  We
; say that measure pattern mp1 ``subsumes'' measure pattern mp2 iff the
; pseudo-clause of mp1 subsumes that of mp2.

; Note that if the pseudo-clause of mp1 subsumes that of mp2, then there is a
; substitution s such that when applied to the pseudo-clause of mp1 produces a
; pseudo-clause that is a subset of that of mp2.  Ignoring the substitution for
; a moment, this means that the measures of the two patterns are the same, all
; the :slots of mp1 are found among the :slots of mp2 (mp2 may have more
; :slots), all the :tests of mp1 are found among the :tests of mp2 (mp2 may
; have more tests), and all the invariant tuples of mp1 are found among those
; of mp2 (mp2 may have more and invariants are conjoined).  In the most common
; case, the substitution will be variable-to-variable and subsumption just
; checks for variance.  But given that we do full-blown subsumption, we allow
; mp1 to be strictly more general than mp2.

(defun measure-pattern-subsumes (mp1 mp2)

; This determines whether measure-pattern mp1 subsumes measure-pattern mp2.

  (subsumes *init-subsumes-count*
            (access measure-pattern mp1 :pseudo-clause)
            (access measure-pattern mp2 :pseudo-clause)
            nil))

; However, replacement of mp2 in the database by mp1 just because mp1 subsumes
; mp2 is a little misguided.  Note that ((consp x) (consp y)) subsumes ((consp
; z)).  We define a function below that attempts to determine which, if either,
; of two mps is better.

(defun some-part-of-mp-simplerp (mp1 mp2)

; This function is only called if mp1 and mp2 subsume each other.  We try to
; determine if there is some pragmatic reason for preferring one to the other.
; It can happen that some part of mp1 is simpler than mp2 and vice versa, e.g.,
; mp1 may have fewer :tests but mp2 may have fewer :slots.

  (or (< (len (access measure-pattern mp1 :tests))
         (len (access measure-pattern mp2 :tests)))
      (< (len (access measure-pattern mp1 :slots))
         (len (access measure-pattern mp2 :slots)))
      (< (len (access measure-pattern mp1 :invariants))
         (len (access measure-pattern mp2 :invariants)))))

(defun which-mp-is-better (mp1 mp2)

; We return 1, 2, or nil to indicate whether mp1 is better than mp2, mp2 is
; better than mp1, or they are incomparable.  If in fact they are equivalent
; (as far as we can tell), we return 2.  This means that it is most efficient
; if mp1 is some supposedly new measure-pattern being considered for addition
; to the database and mp2 is some pre-existing pattern in the database; this
; convention would leave the database unchanged by the ``addition'' of mp1.

  (if (measure-pattern-subsumes mp1 mp2)
      (if (measure-pattern-subsumes mp2 mp1)
; They subsume each other.  Is one strictly simpler than the other?
          (if (some-part-of-mp-simplerp mp1 mp2)
              (if (some-part-of-mp-simplerp mp2 mp1)
; Each has its own advantages even though they appear to be logically
; equivalent.  We'll keep 2 by arbitrary choice.
                  2
; They appear equivalent and mp1 is simpler, so keep it.
                  1)
; Here we know they subsume each other and no part of mp1 is simpler than mp2.
; If some part of mp2 is simpler than mp1, we'd keep 2.  If no part of mp2 is
; simpler, we'd keep 2 by arbitrary choice.  So we keep 2.
              2)
; Mp1 subsumes mp2 but not vice versa.  We keep mp1.
          1)
      (if (measure-pattern-subsumes mp2 mp1)
; Mp2 subsumes mp1 but not vice versa.  Keep mp2.
          2
; Neither subsumes the other.  They're incomparable.
          nil)))

(defun collect-worse-measure-patterns (mp1 mp-lst ans)

; We are considering adding measure pattern mp1 to the list of measure
; patterns, mp-lst.  We collect those elements of mp-lst that are worse than
; mp1.  We return either T or some subset of mp-lst.  If we return T it means
; we have found an mp2 in mp-lst that is better than mp1 and that we should not
; add mp1.

  (cond
   ((endp mp-lst) ans)
   (t (let ((temp (which-mp-is-better mp1 (car mp-lst))))
        (cond
         ((null temp)
          (collect-worse-measure-patterns mp1 (cdr mp-lst) ans))
         ((eql temp 2)

; One might wonder: If some old mp2 is better than mp1, what should we do with
; all the old patterns already accumulated into ans -- which are worse than the
; mp1?  The answer is: ans must be nil.  Reason: when those earlier elements of
; mp-lst, e.g., mp0, were considered for adding to mp-lst, we would have
; detected that this mp2 is better and thrown them out.

; This is just the transitivity of the better-than relation but it was
; sufficiently confusing that we decided to confirm it in a toy version of this
; problem.  In the toy, mps were just triples of numbers.  A toy was used
; because we didn't want to admit subsumption as a logic mode function and
; prove it transitive.

; (defun measure-pattern-subsumes (mp1 mp2)  ; subsumption is transitive
;   (<= (car mp1) (car mp2)))

; (defun some-part-of-mp-simplerp (mp1 mp2)  ; simplerp is a disjunction
;   (or (<= (cadr mp1) (cadr mp2))           ; of inequalities like this
;       (<= (caddr mp1) (caddr mp2))))

; Then define which-mp-is-better with the defun above, in logic mode.

; (thm
;  (implies (and (equal (which-mp-is-better mp1 mp0) 1)  ; mp1 better than mp0
;                (equal (which-mp-is-better mp1 mp2) 2)) ; mp2 better than mp1
;           (equal (which-mp-is-better mp0 mp2) 2)))     ; mp2 better than mp0

          t)
         (t (collect-worse-measure-patterns mp1
                                            (cdr mp-lst)
                                            (cons (car mp-lst) ans))))))))

(defun add-measure-pattern-to-data-base (mp mp-lst)
  (let ((temp (collect-worse-measure-patterns mp mp-lst nil)))
    (cond
     ((eq temp t) mp-lst)
     ((null temp) (cons mp mp-lst))
     (t (cons mp (set-difference-equal mp-lst temp))))))

(defun add-measure-patterns-to-data-base (mp-lst mp-data-base)
  (cond ((endp mp-lst) mp-data-base)
        (t (add-measure-patterns-to-data-base
            (cdr mp-lst)
            (add-measure-pattern-to-data-base (car mp-lst)
                                              mp-data-base)))))

; -----------------------------------------------------------------
; Section:  Explaining the Imminent Change to the Measure Patterns Database

(defun count-and-collect-measure-patterns (mp-lst1 mp-lst2 n names)

; Count the measure-patterns in mp-lst1 that are not in mp-lst2 and return
; that count and the duplicate-free list of their names.

  (cond ((endp mp-lst1) (mv n names))
        ((member-equal (car mp-lst1) mp-lst2)
         (count-and-collect-measure-patterns (cdr mp-lst1) mp-lst2 n names))
        (t (count-and-collect-measure-patterns
            (cdr mp-lst1)
            mp-lst2
            (+ 1 n)
            (add-to-set-eq (access measure-pattern (car mp-lst1) :name)
                           names)))))

(defun compute-measure-patterns (state)

; This function computes a new measure-patterns list from the current
; measure-patterns table and any new DEFUNs (with explicit natp :MEASURES)
; added since the measure-patterns database was last updated.  We return the
; new list of measure-patterns.  WE DO NOT INSTALL IT!  To install it one must
; execute a TABLE event, which we presume our caller will do.

; TODO: Think about efficiency in the face of failed DEFUNMs or failed updates.
; For example, I believe it is the case that if a DEFUNM fails, then any update
; it might have done to the database is lost.  That is, I think the table
; command is only executed if we find a justification that works for the newly
; proposed defun.  But the updating of the database might itself involve a lot
; of work and that work then has to be repeated until we do a successful defunm
; or update-measure-patterns.  I just don't know how bad this inefficiency is.

  (let* ((ens (ens state))
         (wrld (w state))
         (fns (filter-fns-for-appropriate-measures
               (collect-fns-for-incremental-mp-update wrld nil)
               ens wrld)))
    (er-let*
      ((derived-mp-lst (derived-measure-patterns-lst fns state)))
      (let* ((old-mp-lst
              (cdr (assoc-eq :list (table-alist 'measure-patterns wrld))))
             (ans (add-measure-patterns-to-data-base derived-mp-lst old-mp-lst)))
        (value ans)))))

(defun strip-measure-pattern-names (mp-lst)
  (cond ((endp mp-lst) nil)
        (t (cons (access measure-pattern (car mp-lst) :name)
                 (strip-measure-pattern-names (cdr mp-lst))))))

(defun measure-pattern-lst-diff (verbosity mp-lst0 mp-lst1)

; We compute a self-explanatory data structure that reports how the list of
; measure patterns in mp-lst0 was changed to produce mp-lst1.  Verbosity is a
; number between 0 and 3 that controls how much we report.
; 0 -- report nothing
; 1 -- summarize by numbers deleted, added, and unchanged
; 2 -- summarize by names of deleted, added, and unchanged patterns
; 3 -- summarize by prettified patterns deleted, added, and unchanged

  (cond
   ((equal verbosity 0) nil)
   (t (let* ((unchanged (intersection-equal mp-lst0 mp-lst1))
             (deleted (set-difference-equal mp-lst0 mp-lst1))
             (added (set-difference-equal mp-lst1 mp-lst0)))
        (case verbosity
          (1 `((:deleted ,(len deleted))
               (:added ,(len added))
               (:unchanged ,(len unchanged))))
          (2 `((:deleted ,(strip-measure-pattern-names deleted))
               (:added ,(strip-measure-pattern-names added))
               (:unchanged ,(strip-measure-pattern-names unchanged))))
          (otherwise
           `((:deleted
              ,(cond
                ((null deleted) nil)
                (t `(list ,@(prettyify-measure-pattern-lst deleted)))))
             (:added
              ,(cond
                ((null added) nil)
                (t `(list ,@(prettyify-measure-pattern-lst added)))))
             (:unchanged
              ,(cond
                ((null unchanged) nil)
                (t `(list ,@(prettyify-measure-pattern-lst unchanged))))))))))))

; -----------------------------------------------------------------
; Section:  Updating the Measure-Patterns Table

(defmacro update-measure-patterns (verbosity)
  `(make-event
    (er-let* ((new-measure-patterns
               (compute-measure-patterns state)))
      (pprogn
       (fms "~%Measure Patterns Updated:~%~X01~%"
            (list (cons #\0 (measure-pattern-lst-diff
                             ,verbosity
                             (cdr
                              (assoc-eq :list
                                        (table-alist 'measure-patterns
                                                     (w state))))
                             new-measure-patterns))
                  (cons #\1 nil))
            (proofs-co state)
            state
            nil)
       (cond
        ((equal new-measure-patterns
                (cdr (assoc-eq :list (table-alist 'measure-patterns (w state)))))
         (value '(value-triple nil)))
        (t
         (value (list 'table 'measure-patterns
                      :list (kwote new-measure-patterns)))))))))

; =================================================================

; Chapter 3 (Code): Adding Non-Recursive Flag Lemmas

;   Chapter Summary: We support the option of proving automatically generated
;   ``non-recursive flag lemmas'' so that if the admission of a function
;   involves a flag, and one of the flag values just passes the buck to the
;   others -- e.g., one of the functions in the clique is just an eliminable
;   abbreviation for calls on the others -- we generate and prove lemmas that
;   rewrite such non-recursive calls away.

; We recommend re-reading the introductory discussion of this topic, which may
; be found above under Chapter 3 (Discussion).

; This chapter ultimately concludes with the definition of
; make-non-recursive-flag-rule-lst.

(defun non-recursive-flag-valuep (val nrvals dmach)

; Dmach is a flagged machine and val is one of the possible flag values and
; nrvals is the list of all non-recursive flag values identified so far.  We
; determine whether every line with an incoming flag value of val goes out on a
; flag other than val AND other than any of the nrvals.

  (cond
   ((endp dmach) t)
   ((intersectp-equal
     (cons val nrvals)
     (cdr
      (assoc-equal
       val
       (access dline (car dmach) :incoming-flag-to-outgoing-flag-alist))))
    nil)
   (t (non-recursive-flag-valuep val nrvals (cdr dmach)))))

(defun collect-non-recursive-flag-values1 (vals nrvals dmach)
  (cond
   ((endp vals) nil)
   ((non-recursive-flag-valuep (car vals) nrvals dmach)
    (cons (car vals)
          (collect-non-recursive-flag-values1 (cdr vals)
                                              (cons (car vals) nrvals)
                                              dmach)))
   (t (collect-non-recursive-flag-values1 (cdr vals) nrvals dmach))))

(defun get-all-incoming-and-outgoing-flag-values1 (io-alist ans)
  (cond
   ((endp io-alist) ans)
   (t (get-all-incoming-and-outgoing-flag-values1
       (cdr io-alist)
       (add-to-set-equal (car (car io-alist))
                         (union-equal (cdr (car io-alist)) ans))))))

(defun get-all-incoming-and-outgoing-flag-values (dmach ans)
  (cond
   ((endp dmach)
    ans)
   (t (get-all-incoming-and-outgoing-flag-values
       (cdr dmach)
       (get-all-incoming-and-outgoing-flag-values1
        (access dline (car dmach) :incoming-flag-to-outgoing-flag-alist)
        ans)))))

(defun collect-non-recursive-flag-values (dmach)
  (cond
   ((and dmach
         (access dline (car dmach) :flag-vformal))
    (collect-non-recursive-flag-values1
     (get-all-incoming-and-outgoing-flag-values dmach nil)
     nil
     dmach))
   (t nil)))

; A bit of ugliness: We need to generate a name for the lemma and that name
; will include the non-rec flag pc value in question.  Should we print the name
; in binary, octal, decimal, or hex?  We key off of the name of the root
; function, presuming that if it has a number in it that is delimited by
; hyphens we'll use its base.

(defun parse-base-from-fnname2p (lst digits non-empty-flg)
  (cond
   ((endp lst) non-empty-flg)
   ((eql (car lst) #\-) non-empty-flg)
   ((member (car lst) digits :test 'eql)
    (parse-base-from-fnname2p (cdr lst) digits t))
   (t nil)))

(defun parse-base-from-fnname1 (lst)
  (let ((temp (member #\- lst :test 'eql)))
    (cond
     ((null temp) nil)
     ((and (consp (cdr temp))
           (member (cadr temp) '(#\B #\O #\X) :test 'eql)
           (parse-base-from-fnname2p
            (cddr temp)
            (cond
             ((eql (cadr temp) #\B)
              '(#\0 #\1))
             ((eql (cadr temp) #\O)
              '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7))
             ((eql (cadr temp) #\X)
              '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7
                #\8 #\9 #\A #\B #\C #\D #\E #\F))
             (t
              '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9)))
            nil))
      (cond ((eql (cadr temp) #\B) 2)
            ((eql (cadr temp) #\O) 8)
            ((eql (cadr temp) #\X) 16)))
     ((and (consp (cdr temp))
           (parse-base-from-fnname2p
            (cdr temp)
            '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9)
            nil))
      10)
     (t (parse-base-from-fnname1 (cdr temp))))))

(defun parse-base-from-fnname (fn)

; We look for a number as printed in one of the bases 2, 8, 10, or 16
; (preceeded by B, nothing, O, or X) and delimited on the left by hyphen and on
; the right by either hyphen or the end of the name.  If we find one, we return
; the base (2, 8, 10, or 16) of the leftmost one.  Otherwise, nil.  For
; example, SEM-XAB12F and CLK-B01010-CORRECT produce 16 and 2 respectively,
; and replacing the F by G in the first would yield NIL.

  (parse-base-from-fnname1 (coerce (symbol-name fn) 'list)))

(defun make-non-recursive-flag-rule (fn formals body flag-vformal val state)

; Return either
; (defthm name (equal (fn ... val ...) new-body)), or
; (defthm name (implies (equal flag-vformal val) (equal (fn ...) new-body)))
; depending on whether the flag-vformal is a formal or not.

  (let* ((base (or (parse-base-from-fnname fn)
                   10))
         (name
          (intern-in-package-of-symbol
           (mv-let (col str)
                   (fmt1-to-string "~s0-@-~sb~x1"
                                   (list (cons #\0 (symbol-name fn))
                                         (cons #\b
                                               (case base
                                                 (2 "B")
                                                 (8 "O")
                                                 (16 "X")
                                                 (otherwise "")))
                                         (cons #\1 (cadr val)))
                                   0
                                   :fmt-control-alist
                                   (list (cons 'print-base base)))
                   (declare (ignore col))
                   str)
           fn))
         (rhs (simplify-under-hyps
               (list (list 'EQUAL flag-vformal val))
               body
               state)))
    (cond
     ((member-equal flag-vformal formals)
      `(defthm ,name
         (equal (,fn ,@(subst-var-lst val flag-vformal formals))
                ,rhs)))
     (t `(defthm ,name
           (implies (equal ,flag-vformal ,val)
                    (equal (,fn ,@formals)
                           ,rhs)))))))

(defun make-non-recursive-flag-rule-lst (fn formals body flag-vformal val-lst state)
; Return a list of defthm events, one for each flag value in val-lst.
  (cond
   ((endp val-lst) nil)
   (t (cons
       (make-non-recursive-flag-rule fn formals body
                                     flag-vformal (car val-lst) state)
       (make-non-recursive-flag-rule-lst fn formals body
                                         flag-vformal (cdr val-lst) state)))))

; =================================================================

; Chapter 4:  DEFUNM

;   Chapter Summary: We put the three main ideas together in a utility called
;   DEFUNM, which presents itself to the user like DEFUN except it has room
;   after the formals for an :OPTIONS specification.  DEFUNM uses make-event,
;   since it must access state.  DEFUNM becomes DEFUN if the user specifies a
;   measure in the declarations.  Otherwise, it computes the updates to the
;   measure patterns table via the techniques in Chapter 2, then it guesses a
;   measure via Chapter 1, and then, if the :option so specifies it generates
;   any non-recursive flag lemmas available.  It then assembles the results
;   into a PROGN that stores the new measure-patterns, admits the defun with
;   the guessed measure, and proves the flag lemmas.  DEFUNM comes in two
;   flavors, the ordinary one and DEFUNM-NX which introduces non-executable
;   definitions.

(defmacro do-and-undo (form)

; This executes form and then rolls the world (and most system state globals)
; back to their pre-form values.  Matt Kaufmann wrote this for me!  I was
; trying to do it by executing form and then an undo, but that doesn't work at
; the event- (rather than command-) level.

  `(make-event
    (er-progn ,form
              (value '(value-triple nil)))))

(defconst *defunm-step-limit* 10000)

(defun progn-for-defunm-if-necessary (updatep defunm-expr optional-lemmas)
  (let ((lst `(,@(if updatep '((update-measure-patterns 2)) nil)
               ,defunm-expr
               ,@optional-lemmas)))
    (cond
     ((and (consp lst)
           (null (cdr lst)))
      (car lst))
     (t (cons 'progn lst)))))

(defun defunm-fn (defun-flavor whole-form name arglist rest)
; We dig the :options out of rest before we start.
  (mv-let
   (options rest)
   (if (and (consp rest)
            (consp (cdr rest))
            (eq (car rest) :options))
       (if (and (true-listp (cadr rest))
                (subsetp-eq (cadr rest) '(:non-rec-flag-lemmas)))
; If more options are added, look for options below!
           (mv (cadr rest) (cddr rest))
           (mv :error rest))
       (mv nil rest))
   (cond
    ((eq options :error)
     `(er soft 'Terminatricks
          "The :options keyword argument, when supplied, must immediately ~
           follow the formals and its value must be a true-list that is a ~
           subset of the known Terminatricks options, ~x0."
          '(:non-rec-flag-lemmas)))
    ((measure-hint-in-dcl-lst (all-but-last rest))
     (cond
      ((null options)
       `(,defun-flavor ,name ,arglist ,@rest))
      (t `(er soft 'Terminatricks
              "When you provide a :measure to DEFUNM, the :OPTIONS argument ~
               must be NIL.  We currently don't support options unless we ~
               have to do a measure analysis anyway.  But by the time we get ~
               the :options implemented in the normal use cases, it probably ~
               won't be hard to add this feature."))))
    (t
     `(make-event
       (er-let* ((new-measure-patterns
                  (compute-measure-patterns state)))
; Use new measure patterns in subsequent analysis and save for event
; generation so we don't have to recompute them.
         (er-progn
          (set-bogus-measure-ok t) ; added by Matt K. 2/20/2016
          (assign new-measure-patterns
                  new-measure-patterns)
; ``Admit'' the defun with a bogus measure just to grab the tmach.  Then
; undo this so it doesn't confuse future proofs.
          (do-and-undo
           (er-progn
            (skip-proofs
             (,defun-flavor ,name ,arglist
               (declare (xargs :measure (acl2-count (list ,@arglist)))) ; Bogus!
               ,@rest))
            (let* ((name ',name)
                   (tbody (body name t (w state)))
                   (tmach (termination-machine nil nil
                                               (list name) ; fns
                                               nil
                                               tbody nil nil :all)))
              (er-progn
               (assign defunm-tbody tbody)
               (assign termination-machine tmach)))))

          (let* ((new-measure-patterns (@ new-measure-patterns))
                 (old-measure-patterns
                  (cdr (assoc-eq :list
                                 (table-alist 'measure-patterns (w state)))))
                 (tbody (@ defunm-tbody))
                 (tmach (@ termination-machine))
                 (defun-flavor ',defun-flavor)
                 (name ',name)
                 (arglist ',arglist)
                 (options ',options)
                 (rest ',rest)
                 )
            (cond
             ((null tmach) ; non-recursive
; If options is non-nil it's only element can be :non-rec-flag-lemmas and there
; aren't any.
              (value (progn-for-defunm-if-necessary
                      (not (equal new-measure-patterns
                                  old-measure-patterns))
                      `(,defun-flavor ,name ,arglist ,@rest)
                      nil)))
             (t
              (er-progn
               (defstub ,name ,arglist t)
               (er-let*
                 ((triple
                   (mv-let
                    (dmach mesug-lst)
                    (initial-dmach-and-measure-suggestions arglist tmach
                                                           new-measure-patterns
                                                           (w state))
                    (er-let*
                      ((pair (stamp-mesugs-and-search mesug-lst dmach
                                                      *defunm-step-limit* state
                                                      nil)))
                      (value (cons pair
                                   (cond
                                    ((and (member-eq :non-rec-flag-lemmas options)
                                          dmach
                                          (access dline (car dmach) :flag-vformal))
                                     (make-non-recursive-flag-rule-lst
                                      name arglist
                                      tbody
                                      (access dline (car dmach) :flag-vformal)
                                      (collect-non-recursive-flag-values dmach)
                                      state))
                                    (t nil))))))))
                 (let ((measure-rel-pair (termemo-ans (car triple)))
                       (optional-lemmas (cdr triple)))
                   (cond
                    ((null measure-rel-pair)
                     (er soft 'Terminatricks
                         "Terminatricks was unable to guess a measure for ~x0.  ~
                        You could add an explicit :MEASURE.  This will ~
                        `teach' Terminatricks a new measure pattern.  If ~
                        there is a function definition simpler than ~x0 that ~
                        still illustrates the same recursive scheme and an ~
                        appropriate :MEASURE for it, introducing that simpler ~
                        function may perhaps teach Terminatricks the best ~
                        pattern."
                         name))
                    (t
; We lay down a PROGN (as necessary) followed by an update-measure-patterns, the
; new DEFUN, and the optional-lemmas.
                     (value
                      (progn-for-defunm-if-necessary
                       (not (equal new-measure-patterns   ; update measure patterns?
                                   old-measure-patterns))
                       `(,defun-flavor ,name ,arglist     ; new defunm
                          (declare
                           (xargs :measure (DEFUNM-MARKER ,(car measure-rel-pair))
                                  :well-founded-relation ,(cdr measure-rel-pair)))
                          ,@rest)
                       optional-lemmas))))))))))))        ; optional lemmas
       :on-behalf-of ,whole-form)))))

(defmacro defunm (&whole whole-form name arglist &rest rest)
  (defunm-fn 'DEFUN whole-form name arglist rest))

(defmacro defunm-nx (&whole whole-form name arglist &rest rest)
  (defunm-fn 'DEFUN-NX whole-form name arglist rest))

; -----------------------------------------------------------------
; Section: Just Comments

; Essay on Eliminating Isolated Tests

; On 30 Jan, 2014, I wrote to Matt Kaufmann asking if he could settle the
; conjecture below.  I had spent some frustrating time thinking about it and
; decided I'd rather get on with coding Terminatricks than justifying the
; idea.

;    Let's say a formal parameter, A, of a function defun of
;    FN is ``isolated'' if it is never used in a tested
;    (actually, ruling) expression and the only occurrences
;    of A in recursive calls are in the A-slot.

;    Typical isolated parameter are ``pure accumulators''
;    like the Y in (REV-APPEND X Y) and ACC in
;    (MERGE-LEXORDER X Y ACC).  Of course, not all
;    accumulators are isolated, e.g., IGNORED-SEEN in
;    LEGAL-LET*-P is tested.

;    Conjecture: If a defun of FN is admissible and FN has
;    an isolated parameter A, then there exists a measure
;    for FN that does not include A.  (I.e., A need not be
;    in the measured subset.)

;    Intuitively, this seems true to me because A can't
;    affect the termination if it is never tested.  But the
;    obvious way to prove it would be to say that if you
;    have a proof for some measure that involves A you can
;    prove it for a measure that doesn't involve A.  But I
;    don't see how to define such a measure if I don't know
;    anything about the successful measure other than that it
;    decreases in a well-founded ordering.

; I also said I'd be happy with a proof for the simple case illustrated by

; (defun fn (x a)
;   (declare (xargs :measure (m x a)))
;   (if (test x)
;       (fn (d x) (g x a))
;       a))

; where (m x a) is a natural.

; Matt replied soon after: ``Interesting question!'' and then provided the
; following script proving the Conjecture for the simple case requested.  I
; have edited his script to make the names more intuitive to me.

#||
(encapsulate
 ((test (x) t)
  (d (x) t)
  (g (x a) t)
  (m (x a) t))
 (local (defun test (x) (posp x)))
 (local (defun d (x) (1- x)))
 (local (defun g (x a) (list x a)))
 (local (defun m (x a)
          (declare (ignore a))
          (nfix x)))
 (defthm natp-m
   (natp (m x a))
   :rule-classes :type-prescription)
 (defthm m-goes-down
   (implies (test x)
            (< (m (d x) (g x a))
               (m x a)))))

(defun recursion-depth (x a)
  (declare (xargs :measure (m x a)))
  (if (test x)
      (1+ (recursion-depth (d x) (g x a)))
    0))

(defun minimal-sufficient-depthp (x n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (not (test x))
    (and (test x)
         (minimal-sufficient-depthp (d x) (1- n)))))

(defthm minimal-sufficient-depthp-is-unique
  (implies (and (minimal-sufficient-depthp x n1)
                (minimal-sufficient-depthp x n2))
           (equal (nfix n1)
                  (nfix n2)))
  :rule-classes nil)

(local (include-book "arithmetic/top" :dir :system)) ; for -1 + 1 + x = nfix(x)

(defthm recursion-depth-is-minimally-sufficient
  (minimal-sufficient-depthp x (recursion-depth x a))
  :hints (("Goal" :induct (recursion-depth x a)))
  :rule-classes nil)

(defthm recursion-depth-depends-only-on-x
  (implies (syntaxp (not (equal a ''nil)))
           (equal (recursion-depth x a)
                  (recursion-depth x nil)))
  :hints (("Goal" :use ((:instance minimal-sufficient-depthp-is-unique
                                   (n1 (recursion-depth x a))
                                   (n2 (recursion-depth x nil)))
                        (:instance recursion-depth-is-minimally-sufficient)
                        (:instance recursion-depth-is-minimally-sufficient (a nil))))))

(defun m2 (x)
  (recursion-depth x nil))

(defthm natp-m2
  (natp (m2 x))
  :rule-classes :type-prescription)

(defthm m2-goes-down
  (implies (test x)
           (< (m2 (d x))
              (m2 x)))
  :hints (("Goal" :expand ((recursion-depth x nil)))))

||#

