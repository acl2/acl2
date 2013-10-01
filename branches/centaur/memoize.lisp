; ACL2 Version 6.3 -- A Computational Logic for Applicative Common Lisp
; Copyright (C) 2013, Regents of the University of Texas

; This version of ACL2 is a descendent of ACL2 Version 1.9, Copyright
; (C) 1997 Computational Logic, Inc.  See the documentation topic NOTE-2-0.

; This program is free software; you can redistribute it and/or modify
; it under the terms of the LICENSE file distributed with ACL2.

; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; LICENSE for more details.

; Written by:  Matt Kaufmann               and J Strother Moore
; email:       Kaufmann@cs.utexas.edu      and Moore@cs.utexas.edu
; Department of Computer Science
; University of Texas at Austin
; Austin, TX 78701 U.S.A.

; memoize.lisp -- Logical definitions for memoization functions, only
; to be included in the experimental HONS version of ACL2.

; The original version of this file was contributed by Bob Boyer and
; Warren A. Hunt, Jr.  The design of this system of Hash CONS,
; function memoization, and fast association lists (applicative hash
; tables) was initially implemented by Boyer and Hunt.

(in-package "ACL2")

(defmacro defn (f a &rest r)

  ":Doc-Section Events
   definition with ~il[guard] ~c[t]~/

   ~c[Defn] is ~ilc[defun] with ~il[guard] ~c[t].~/~/"

  `(defun ,f ,a (declare (xargs :guard t)) ,@r))

(defmacro defnd (f a &rest r)

  ":Doc-Section Events
   ~il[disable]d definition with ~il[guard] ~c[t]~/

   ~c[Defnd] is ~ilc[defund] with ~il[guard] ~c[t].~/~/"

  `(defund ,f ,a (declare (xargs :guard t)) ,@r))

(defdoc hons-and-memoization
  ":Doc-Section Hons-and-Memoization

  hash cons, function memoization, and applicative hash tables~/

  Bob Boyer and Warren Hunt, and later Jared Davis and Sol Swords, have
  developed a canonical representation for ACL2 data objects and a function
  memoization mechanism to facilitate reuse of previously computed results.
  This facility includes procedures to read and print ACL2 expressions in such
  a way that repetition of some ACL2 objects is eliminated, thereby permitting
  a kind of on-the-fly file compression.  The implementation does not alter the
  semantics of ACL2 except to add a handful of definitions.

  We give the name ``ACL2(h)'' to the resulting experimental extension of the
  ACL2 system, which includes hash cons, function memoization, and fast
  association lists (applicative hash tables).  It is optimized for Clozure
  Common Lisp (CCL), but other ANSI-compliant host Lisp implementations may
  also work, provided there are sufficient machine resources.

  If you want to use ACL2(h), you might find it helpful to consult the document
  ~c[centaur/README.html] in the ACL2 community books.

  An easy way is to build ACL2(h) is to include the following with a `make'
  command:
  ~bv[]
  ACL2_HONS=h
  ~ev[]
  So for example, to make an executable image and also documentation
  (which will appear in subdirectories ~c[doc/EMACS] and ~c[doc/HTML]):
  ~bv[]
  make large DOC ACL2_HONS=h
  ~ev[]~/

  Much of the documentation for the remainder of this topic is taken from the
  paper ``Function Memoization and Unique Object Representation for ACL2
  Functions'' by Robert S. Boyer and Warren A. Hunt, Jr., which has appeared in
  the Sixth International Workshop on the ACL2 Theorem Prover and Its
  Applications, ACM Digital Library, 2006.

  In the implementation of the ACL2 logic, ACL2 data objects are represented by
  Common Lisp objects of the same type, and the ACL2 pairing operation is
  internally implemented by the Common Lisp ~ilc[cons] function.  In Common
  Lisp, ~c[cons] is guaranteed to provide a new pair, distinct from any
  previously created pair.  We have defined a new ACL2 function ~ilc[HONS] that
  is logically identical to the ACL2 ~c[cons] function, but whose
  implementation usually reuses an existing pair if its components are
  identical to the components of an existing pair.  A record of ACL2 HONS
  objects is kept, and when an ACL2 function calls ~c[hons] ACL2 searches for
  an existing identical pair before allocating a new pair; this operation been
  called ``hash consing''.

  It appears that hash consing was first conceived by A. P. Ershov in 1957, to
  speed up the recognition of common subexpressions.  Ershov showed how to
  collapse trees to minimal DAGs by traversing trees bottom up, and he used
  hashing to eliminate the re-evaluation of common subexpressions.  Later,
  Eiichi Goto implemented a Lisp system with a built-in hash consing operation:
  his h-CONS cells were rewrite protected and free of duplicate copies, and
  Goto used this hash consing operation to facilitate the implementation of a
  symbolic algebra system he developed.

  Memoizing functions also has a long history.  In 1967, Donald Michie proposed
  using memoized functions to improve the performance of machine learning.
  Rote learning was improved by a learning function not forgetting what it had
  previously learned; this information was stored as memoized function values.

  The use of hash consing has appeared many times.  For instance, Henry Baker
  used hash consing to improve the performance of the well-known Boyer
  rewriting benchmark.  Baker used both hash consing and function memoization
  to improve the speed of the Takeuchi function, exactly in the spirit of our
  implementation, but without the automated, system-wide integration we report
  here.

  The ACL2 implementation permits memoization of user-defined functions.
  During execution a user may enable or disable function memoization on an
  individual function basis, may clear memoization tables, and may even keep a
  stack of memoization tables.  This facility takes advantage of our
  implementation where we keep one copy of each distinct ACL2 data object.  Due
  to the functional nature of ACL2, it is sufficient to have at most one copy
  of any data structure; thus, a user may arrange to keep data canonicalized.
  This implementation extends to the entire ACL2 system the benefits enjoyed by
  BDDs: canonicalization, memoization, and fast equality check.

  We have defined various algorithms using these features, and we have
  observed, in some cases, substantial performance increases.  For instance, we
  have implemented unordered set intersection and union operations that operate
  in time roughly linear in the size of the sets.  Without using arrays, we
  defined a canonical representation for Boolean functions using ACL2 objects.
  We have investigated the performance of rewriting and tree consensus
  algorithms to good effect, and we believe function memoization offers
  interesting opportunities to simplify algorithm definition while
  simultaneously providing performance improvements.

  We recommend that users focus at first on the logical definitions of
  ~ilc[hons] and other primitives rather than their underlying Common Lisp
  implementations.  Integrated with this memoization system is a performance
  monitoring system, which can provide real-time feedback on the operation and
  usefulness of ~ilc[hons] and function memoization.  For a more detailed
  description of these tools, please see the ACL2 2006 workshop paper mentioned
  above.

  The Fibonacci function is a small example that demonstrates the utility of
  function memoization.  The following definition exhibits a runtime that is
  exponential in its input argument.
  ~bv[]
  (defun fib (x)
    (declare (xargs :guard (natp x)))
    (mbe
     :logic
     (cond ((zp x) 0)
           ((= x 1) 1)
           (t (+ (fib (- x 1)) (fib (- x 2)))))
     :exec
     (if (< x 2)
         x
       (+ (fib (- x 1)) (fib (- x 2))))))
  ~ev[]

  Below we show how the ACL2 ~ilc[time$] utility can measure the time to
  execute a call to the ~c[fib] function (with some editing to avoid noise from
  the underlying Common Lisp implementation).  ~ilc[Memoize] is actually an
  ACL2 macro that expands to a call of the ACL2 function used to identify a
  function for memoization; ~pl[memoize].  This function also accepts a
  well-formed term that must be true in order for the system to memoize a call
  of the memoized function; to ensure that an instance of the term is safe for
  evaluation in Common Lisp, a check is performed that if the ~il[guard] of the
  memoized function is satisfied, then this instance will execute without
  error.
  ~bv[]
  ACL2 !>(time$ (fib 40))
  ; (EV-REC *RETURN-LAST-ARG3* ...) took
  ; 0.99 seconds realtime, 0.98 seconds runtime
  ; (1,296 bytes allocated).
  102334155
  ACL2 !>(memoize 'fib)

  Summary
  Form:  ( TABLE MEMOIZE-TABLE ...)
  Rules: NIL
  Time:  0.01 seconds (prove: 0.00, print: 0.00, other: 0.01)

  Summary
  Form:  ( PROGN (TABLE MEMOIZE-TABLE ...) ...)
  Rules: NIL
  Time:  0.01 seconds (prove: 0.00, print: 0.00, other: 0.01)
   FIB
  ACL2 !>(time$ (fib 40))
  ; (EV-REC *RETURN-LAST-ARG3* ...) took
  ; 0.00 seconds realtime, 0.00 seconds runtime
  ; (2,864 bytes allocated).
  102334155
  ACL2 !>(time$ (fib 100))
  ; (EV-REC *RETURN-LAST-ARG3* ...) took
  ; 0.00 seconds realtime, 0.00 seconds runtime
  ; (7,024 bytes allocated).
  354224848179261915075
  ACL2 !>(unmemoize 'fib)
  ~ev[]

  We see that once the function ~c[fib] is identified as a function for which
  function calls should be memoized, the execution times are substantially
  reduced.  Finally, we can prevent ~c[fib] from being further memoized; in
  fact, ~ilc[unmemoize] erases the previously memoized values.

  The implementation of hash consing, memoization, and applicative hash tables
  involves several facets: canonical representation of ACL2 data, function
  memoization, and the use of Lisp hash tables to improve the performance of
  association list operations.  We discuss each of these in turn, and we
  mention some subtle interrelationships.  Although it is not necessary to
  understand the discussion in this section, it may permit some users to better
  use this implementation.  This discussion may be confusing for some ACL2
  users as it makes references to Lisp implementation features.

  The ACL2 system is actually implemented as a Lisp program that is layered on
  top of a Common Lisp system implementation.  ACL2 data constants are
  implemented with their corresponding counterparts in Common Lisp; that is,
  ACL2 cons pairs, strings, characters, numbers, and symbols are implemented
  with their specific Common Lisp counterparts.  This choice permits a number
  of ACL2 primitive functions to be implemented with their corresponding Common
  Lisp functions, but there are indeed differences.  ACL2 is a logic, and as
  such, it does not specify anything to do with physical storage or execution
  performance.  When ACL2 is used, the knowledgeable user can write functions
  to facilitate the reuse of some previously computed values.

  Recall the three mechanisms under discussion: hash consing, function
  memoization, and fast association list operations.  The function memoization
  mechanism takes advantage of the canonical representation of data objects
  provided by the ~ilc[hons] operation as does the fast association list
  operation mechanism.  Each time ~c[hons] is invoked, its arguments are
  themselves converted, if necessary, to uniquely represented objects.

  The ACL2 universe is recursively closed under the ~c[cons] pairing operation
  and the atoms.  Hash consing (~ilc[hons]) is logically identical to ~c[cons],
  but a set of tables is used to record each ~c[hons] pair.  When a ~c[hons]
  pair is requested, the implementation checks, in the current set of tables,
  whether the requested pair already exists.  If not, a new pair is created and
  a record of that pair is made; otherwise, a reference to the previously
  created pair is returned.  Thus, any data object created with ~c[hons] has a
  unique representation, as does every subcomponent.  We also arrange for
  strings to have a unique representation ~-[] only one copy of each different
  string is kept ~-[] and when any previously unseen string is an argument to
  ~c[hons], we add the string to a unique table of strings.  A system-wide
  benefit of having a canonical representation for data is that equality
  comparisons between any two data objects can be done in constant time.

  The definition of ~ilc[hons] in no way changes the operation of ~c[cons] ~-[]
  ~c[hons] creates a ~c[cons] pair.  When asked to create a ~c[hons], the
  implementation checks to see if there is a ~c[cons] with the same ~ilc[car]
  and ~ilc[cdr] as the ~c[hons] being requested.  Thus, the only difference
  between the results of a ~c[hons] call and a corresponding ~c[cons] call is a
  notation in some invisible (to the ACL2 logic) tables where we record which
  ~c[cons] elements are also ~c[hons] elements.  Since a ~c[hons] is nothing
  but a ~c[cons], the operation of ~c[car] and ~c[cdr] is unchanged.  In fact,
  the implementation is designed so that at any time it is safe to clear the
  table identifying which ~c[cons] elements are also considered ~c[hons]
  elements.

  User-defined functions with defined and verified guards can be memoized.
  When a function is memoized, a user-supplied condition restricts the domain
  when memoization is attempted.  When the condition is satisfied, memoization
  is attempted (assuming that memoization for the function is presently
  enabled); otherwise, the function is just evaluated.  Each memoized function
  has a hash table that is used to keep track of a unique list of function
  arguments paired with their values.  If appropriate, for each function the
  corresponding table is checked to see if a previous call with exactly the
  same arguments already exists in the table: if so, then the associated value
  is returned; if not, then the function is evaluated and a new key-value pair
  is added to the table of memoized values so that some future call will
  benefit from the memoization.  With ACL2 user functions memoization can be
  dynamically enabled and disabled.  There is an ACL2 function that clears a
  specific memoization table.  And finally, just as with the ~c[hons] table, a
  stack of these function memoization tables is maintained; that is, it is
  possible to memoize a function, use it a bit, set the memoized values aside,
  start a new table, use it, and then return to the original table.

  We next discuss the fast lookup operation for association lists.  When a pair
  is added to an association list using the functions ~ilc[hons-acons] or
  ~ilc[hons-acons!], the system also records the key-value pair in an
  associated hash table.  As long as a user only used these two functions when
  placing key-value pairs on an association list, the key-value pairs in the
  corresponding hash table will be synchronized with the key-value pairs in the
  association list.  Later, if ~ilc[hons-get] is used to look up a key, then
  instead of performing a linear search of the association list we consult the
  associated hash table.  If a user does not strictly follow this discipline,
  then a linear search may be required.  In some sense, these association lists
  are much like ACL2 arrays, but without the burden of explicitly naming the
  arrays.  The ACL2 array ~ilc[compress1] function is analogous to the
  functions ~ilc[hons-shrink-alist] and ~ilc[hons-shrink-alist!].  There are
  user-level ACL2 functions that allow the associated hash tables to be cleared
  and removed.

  Finally, we would advise anyone who is using CCL in a research environment to
  stay plugged into the ``trunk'' or ``bleeding edge'' of CCL development.
  This is very easy to do by typing a few commands to a shell, for example
  standing above the target directory as follows, provided one has ~c[svn]
  working.
  ~bv[]

   For linux:

     rm -rf ccl
     svn co http://svn.clozure.com/publicsvn/openmcl/trunk/linuxx8664/ccl

   For an x86 Macintosh running the Darwin OS:

     svn co http://svn.clozure.com/publicsvn/openmcl/trunk/darwinx8664/ccl

   To keep up to date, you may find it sufficient to do:

     cd ccl
     svn update

   Whether obtaining a fresh CCL or just updating, finally issue these
   commands.

     ./lx86cl64
     (rebuild-ccl :full t)
     (quit)
     ./lx86cl64
     (rebuild-ccl :full t)
     (quit)

  ~ev[]

  ~sc[References]

  Baker, Henry G., The Boyer Benchmark at Warp Speed. ACM Lisp
  Pointers V,3 (Jul-Sep 1992), pages 13-14.

  Baker, Henry G., A Tachy 'TAK'.  ACM Lisp Pointers Volume 3,
  July-September, 1992, pages 22-23.

  Robert S. Boyer and Warren A. Hunt, Jr., Function Memoization
  and Unique Object Representation for ACL2 Functions, in the Sixth
  International Workshop on the ACL2 Theorem Prover and Its
  Applications, ACM Digital Library, 2006.

  A. P. Ershov.  On Programming of Arithmetic  Operations.  In
  the Communications of the ACM, Volume 118, Number 3, August,
  1958, pages 427-430.

  Eiichi Goto, Monocopy and Associative Algorithms in Extended Lisp,
  TR-74-03, University of Toyko, 1974.

  Richard P. Gabriel.  Performance and Evaluation of Lisp Systems.
  MIT Press, 1985.

  Donald Michie.  Memo functions: a Language Feature with Rote
  Learning Properties.  Technical Report MIP-R-29, Department of
  Artificial Intelligence, University of Edinburgh, Scotland, 1967.

  Donald Michie.  Memo Functions and Machine Learning.  In Nature,
  Volumne 218, 1968, pages 19-22.
  ~/")

#+(or acl2-loop-only (not hons))
(defn clear-memoize-table (fn)

  ":Doc-Section Hons-and-Memoization

  forget values remembered for the given function~/

  This ~il[documentation] topic relates to the experimental extension of ACL2
  supporting hash cons, fast alists, and memoization; ~pl[hons-and-memoization].

  This function returns its argument, ~c[fn], unchanged.  The values memoized
  for ~c[fn] are forgotten.~/~/"

  fn)

#+(or acl2-loop-only (not hons))
(defn clear-memoize-tables ()

  ":Doc-Section Hons-and-Memoization

  forget values remembered for all the memoized functions~/

  This ~il[documentation] topic relates to the experimental extension of ACL2
  supporting hash cons, fast alists, and memoization; ~pl[hons-and-memoization].

  ~c[Clear-memoize-tables] is a logical no-op.  All memoized values are
  forgotten.  It returns ~c[nil], invoking ~ilc[clear-memoize-table] for each
  memoized function.~/~/"

  nil)

#+(or acl2-loop-only (not hons))
(defn memoize-summary ()
  ":Doc-Section Hons-and-Memoization

  display all collected profiling and memoization table info~/

  This ~il[documentation] topic relates to the experimental extension of ACL2
  supporting hash cons, fast alists, and memoization; ~pl[hons-and-memoization].

  Logically, this function just returns ~c[nil], but it displays profiling and
  memoization table information.  The profiling statistics may be cleared with
  ~c[(]~ilc[clear-memoize-statistics]~c[)].~/~/"

  nil)

#+(or acl2-loop-only (not hons))
(defn clear-memoize-statistics ()
  ":Doc-Section Hons-and-Memoization

  clears all profiling info displayed by ~c[(]~ilc[memoize-summary]~c[)]~/

  This ~il[documentation] topic relates to the experimental extension of ACL2
  supporting hash cons, fast alists, and memoization; ~pl[hons-and-memoization].

  Logically, this function just returns ~c[nil].  It clears all profiling info
  displayed by ~c[(]~ilc[memoize-summary]~c[)]~/~/"

  nil)

(defmacro memsum ()
  ":Doc-Section Hons-and-Memoization

  display all collected profiling and memoization info~/

  This ~il[documentation] topic relates to the experimental extension of ACL2
  supporting hash cons, fast alists, and memoization; ~pl[hons-and-memoization].

  This macro is an abbreviation for ~ilc[memoize-summary].  Logically, it just
  returns ~c[nil].~/~/"

  '(memoize-summary))

; The macros MEMOIZE-ON and MEMOIZE-OFF typically cause "under the hood"
; effects that, though not changing the semantics of what ACL2 returns, may
; affect the speed and/or space utilization of the computation.

; The functions memoize and unmemoize have rather innocent looking
; semantics.  But under the hood, they enable and disable memoization.
; The function memoize might cause errors due to compilation problems.

(defconst *hons-primitive-fns*
  ;; This affects acl2-exports, maybe other stuff
  '(hons-copy
    hons
    hons-equal
    hons-equal-lite
    hons-clear
    hons-wash
    hons-summary
    hons-resize-fn
    get-slow-alist-action
    hons-get
    hons-acons
    hons-acons!
    hons-shrink-alist
    hons-shrink-alist!
    fast-alist-len
    fast-alist-free
    fast-alist-summary
    cons-subtrees
    number-subtrees
    clear-hash-tables
    flush-hons-get-hash-table-link
    ;; from memoize.lisp
    clear-memoize-table
    clear-memoize-tables
    memoize-summary
    clear-memoize-statistics))

(defconst *hons-primitives*
  ;; hons-related macros and primitive fns
  (append '(hons-resize
            set-slow-alist-action
            memoize
            unmemoize
            memoize-on
            memoize-off
            memsum)
          *hons-primitive-fns*))

(defconst *mht-default-size* 60)

(defun memoize-form (fn
                     condition
                     condition-p
                     condition-fn
                     hints
                     otf-flg
                     inline
                     trace
                     commutative
                     forget
                     memo-table-init-size
                     aokp
                     ideal-okp)

; Jared Davis suggests that we consider bundling up these 13 parameters, for
; example into an alist.  He says: "Various subsets of these arguments occur in
; spaghetti fashion throughout the code for memoize, add-trip, the
; memoize-table stuff, etc."

  (declare (xargs :guard t))
  (let ((condition (cond ((equal condition ''t) t)
                         ((equal condition ''nil) nil)
                         (t condition))))
    (cond
     ((and condition-fn (null condition-p))
      `(progn (table memoize-table
                     (deref-macro-name ,fn (macro-aliases world))
                     (list* (cons :condition-fn ,condition-fn)
                            (cons :inline ,inline)
                            (cons :trace ,trace)
                            (cons :commutative ,commutative)
                            (cons :forget ,forget)
                            (cons :memo-table-init-size
                                  ,(or memo-table-init-size
                                       *mht-default-size*))
                            (cons :aokp ,aokp)
                            (and (not (eq ,ideal-okp :default))
                                 (list (cons :ideal-okp ,ideal-okp)))))
              (value-triple (deref-macro-name
                             ,fn
                             (macro-aliases (w state))))))
     ((and condition-p
           (not (eq condition t))
           (not (eq condition nil)))
      `(make-event
        (let* ((wrld (w state))
               (fn (deref-macro-name ,fn (macro-aliases wrld)))
               (condition ,condition)
               (formals
                (and (symbolp fn) ; guard for getprop
                     (getprop fn 'formals t
                              'current-acl2-world wrld)))
               (stobjs-in (getprop fn 'stobjs-in t
                                   'current-acl2-world wrld))
               (condition-fn (or ,condition-fn
                                 (intern-in-package-of-symbol
                                  (concatenate
                                   'string
                                   (symbol-name fn)
                                   "-MEMOIZE-CONDITION")
                                  fn)))
               (hints ,hints)
               (otf-flg ,otf-flg)
               (inline ,inline)
               (trace ,trace)
               (commutative ,commutative)
               (forget ,forget)
               (memo-table-init-size ,memo-table-init-size)
               (aokp ,aokp)
               (ideal-okp ,ideal-okp))
          (cond ((not (and
                       (symbolp fn)
                       (not (eq t formals))
                       (not (eq t stobjs-in))
                       (not (eq t (getprop fn 'stobjs-out t

; Normally we would avoid getting the stobjs-out of return-last.  But
; return-last will eventually be rejected for mamoization anyhow (by
; memoize-table-chk).

                                           'current-acl2-world wrld)))
                       (cltl-def-from-name fn wrld)))
                 (er hard 'memoize
                     "The symbol ~x0 is not a known function symbol, and thus ~
                      it cannot be memoized."
                     fn))

; Certify-book seems to do things twice, so the following is commented out.

;             ((cdr (assoc-eq fn (table-alist 'memoize-table wrld)))
;              (er hard 'memoize "~x0 is already memoized." fn))

                ((not (member-eq inline '(t nil)))
                 (er hard 'memoize
                     "The value ~x0 for inline is illegal (must be ~x1 or ~x2)."
                     inline t nil))
                ((not (member-eq trace '(t nil)))
                 (er hard 'memoize
                     "The value ~x0 for trace is illegal (must be ~x1 or ~x2)."
                     trace t nil))
                (t
                 `(progn
                    (defun ,condition-fn ,formals
                      (declare
                       (ignorable ,@formals)
                       (xargs :guard
                              ,(getprop fn 'guard *t*
                                        'current-acl2-world wrld)
                              :verify-guards nil
                              ,@(let ((stobjs (remove nil stobjs-in)))
                                  (and stobjs
                                       `(:stobjs ,stobjs)))))
                      ,condition)
                    (verify-guards ,condition-fn
                                   ,@(and hints `(:hints ,hints))
                                   ,@(and otf-flg
                                          `(:otf-flg ,otf-flg)))
                    (table memoize-table
                           ',fn
                           (list* (cons :condition-fn ',condition-fn)
                                  (cons :inline ',inline)
                                  (cons :trace ',trace)
                                  (cons :commutative ',commutative)
                                  (cons :forget ',forget)
                                  (cons :memo-table-init-size
                                        (or ,memo-table-init-size
                                            *mht-default-size*))
                                  (cons :aokp ',aokp)
                                  (and (not (eq ',ideal-okp :default))
                                       (list (cons :ideal-okp ',ideal-okp)))))
                    (value-triple ',fn)))))))
     (t `(progn (table memoize-table
                       (deref-macro-name ,fn (macro-aliases world))
                       (list* (cons :condition-fn ,condition) ; t or nil
                              (cons :inline ,inline)
                              (cons :trace ,trace)
                              (cons :commutative ,commutative)
                              (cons :forget ,forget)
                              (cons :memo-table-init-size
                                    (or ,memo-table-init-size
                                        *mht-default-size*))
                              (cons :aokp ',aokp)
                              (and (not (eq ',ideal-okp :default))
                                   (list (cons :ideal-okp ',ideal-okp)))))
                (value-triple (deref-macro-name
                               ,fn
                               (macro-aliases (w state)))))))))

(defmacro memoize (fn &key
                      (condition 't condition-p)
                      condition-fn hints otf-flg
                      (recursive 't)
                      trace
                      commutative
                      forget
                      memo-table-init-size
                      aokp
                      (ideal-okp ':default)
                      (verbose 't))

; WARNING: If you add a new argument here, consider making corresponding
; modifications to memoize-form, table-cltl-cmd, maybe-push-undo-stack, and
; add-trip.  (These were the functions modified when adding the FORGET
; argument; the process was to see how the COMMUTATIVE argument was handled.)

; If condition and condition-fn are both non-nil, then the intent is
; that we do exactly what we would normally do for condition except
; that we use the name condition-fn.

; Parallelism blemish: when waterfall parallelism is enabled (detected by
; seeing whether ACL2 global 'waterfall-parallelism is non-nil), memoize and
; unmemoize should be changed to modify the 'saved-memoize-table instead of
; 'memoize-table.

  ":Doc-Section Events

  turn on memoization for a specified function~/

  This ~il[documentation] topic relates to an experimental extension of ACL2
  under development by Bob Boyer and Warren Hunt.  ~l[hons-and-memoization] for
  a general discussion of memoization and the related features of hash consing
  and applicative hash tables.

  ~bv[]
  Examples:
  (memoize 'foo)                      ; remember the values of calls
                                      ;   of foo
  (memoize 'foo :condition t)         ; same as above
  (memoize 'foo :condition '(test x)) ; memoize for args satisfying
                                      ;   the given condition
  (memoize 'foo :condition-fn 'test)  ; memoize for args satisfying
                                      ;   a call of the given function
  (memoize 'foo :recursive nil)       ; don't memoize recursive calls
  (memoize 'foo :aokp t)              ; attachments OK for stored results
  (memoize 'foo :ideal-okp t)         ; memoize even if foo is in :logic mode
                                      ;   but has not been guard-verified~/

  General Form:
  (memoize fn                         ; memoizes fn and returns fn
           :condition    condition    ; optional (default t)
           :condition-fn condition-fn ; optional
           :hints        hints        ; optional, for verifying the
                                      ;   guards of condition-fn
           :otf-flg      otf-flg      ; optional, for verifying the
                                      ;   guards of condition-fn
           :recursive    t/nil        ; optional (default t)
           :commutative  t/lemma-name ; optional (default nil)
           :forget       t/nil        ; optional (default nil)
           :memo-table-init-size size ; optional (default *mht-default-size*)
           :aokp         t/nil        ; optional (default nil)
           :ideal-okp    t/:warn/nil  ; optional (default nil)
           :verbose      t/nil        ; optional (default t)
           )
  ~ev[]
  where ~c[fn] evaluates to a user-defined function symbol; ~c[condition] is
  either ~c[t] (the default), ~c['t], ~c[nil], or ~c['nil], or else evaluates
  to an expression whose free variables are among the formal parameters of
  ~c[fn]; and ~c[condition-fn] is either ~c[nil] (the default) or else
  evaluates to a legal function symbol.  Further restrictions and options are
  discussed below.  Note that all arguments are evaluated (but for the special
  handling of value ~c[t] for ~c[:commutative], the argument must literally be
  ~c[t]; see below).

  Generally ~c[fn] must evaluate to a defined function symbol.  However, this
  value can be the name of a macro that is associated with such a function
  symbol; ~pl[macro-aliases-table].  That associated function symbol is the one
  called ``memoized'' in the discussion below, but we make no more mention of
  this subtlety.

  In the most common case, ~c[memoize] takes a single argument, which evaluates
  to a function symbol.  We call this function symbol the ``memoized function''
  because ``memos'' are saved and re-used, in the following sense.  When a call
  of the memoized function is evaluated, the result is ``memoized'' by
  associating the call's arguments with that result, in a suitable table.  But
  first an attempt is made to avoid such evaluation, by doing a lookup in that
  table on the given arguments for the result, as stored for a previous call on
  those arguments.  If such a result is found, then it is returned without
  further computation.  This paragraph also applies if ~c[:condition] is
  supplied but is ~c[t] or ~c['t].

  If keyword argument ~c[:condition-fn] is supplied, but ~c[:condition] is not,
  then the result of evaluating ~c[:condition-fn] must be a defined function
  symbol whose formal parameter list and ~ilc[guard] are the same as for the
  function being memoized.  If ~c[fn] is in ~c[:]~ilc[logic] mode, then
  ~il[guard]s must have been verified for ~c[:condition-fn].  Such a
  ``condition function'' will be run whenever the memoized function is called,
  on the same parameters, and the lookup or table store described above are
  only performed if the result from the condition function call is non-~c[nil].

  Suppose however that ~c[:condition] is supplied.  If the value supplied is
  ~c[t] or ~c['t], then the lookup and table store described above are always
  done.  If the value is ~c[nil] or ~c['nil], then this lookup and table store
  are never done, although statistics may be gathered; ~pl[profile].  Now
  consider other values for ~c[:condition].  An attempt will be made to define
  a condition function whose ~il[guard] and formal parameters list are the same
  as those of the memoized function, and whose body is the result, ~c[r], of
  evaluating the given ~c[condition].  The name of that condition function is
  the result of evaluating ~c[:condition-fn] if supplied, else is the result of
  concatenating the string ~c[\"-MEMOIZE-CONDITION\"] to the end of the name of
  the memoized function.  The condition function will be defined with
  ~il[guard] verification turned off, but that definition will be followed
  immediately by a ~ilc[verify-guards] event; and this is where the optional
  ~c[:hints] and ~c[:otf-flg] are attached.  At evaluation time the condition
  function is used as described in the preceding paragraph; so in effect, the
  condition (~c[r], above) is evaluated, with its variables bound to the
  corresponding actuals of the memoized function call, and the memoized
  function attempts a lookup or table store if and only if the result of that
  evaluation is non-~c[nil].

  Note that ~c[fn] can be either a ~c[:]~ilc[logic] mode function or a
  ~c[:]~ilc[program] mode function.  However, only the corresponding raw Lisp
  function is actually memoized, so ~il[guard] violations can defeat
  memoization, and ~c[:]~ilc[logic] mode functions without their ~il[guard]s
  verified will only be memoized when called by ~c[:]~ilc[program] mode
  functions.  (~l[guards-and-evaluation] for more information about guards and
  evaluation in ACL2.)  If ~c[fn] is a ~c[:]~ilc[logic] mode function and
  ~c[:condition] is supplied and not ~c[t] or ~c[nil], then the condition must
  be a ~il[guard]-verified function.

  Calls of this macro generate events of the form
  ~c[(table memoize-table fn ((:condition-fn fn) ...))].  When successful, the
  returned value is of the form ~c[(mv nil function-symbol state)].

  Suppose that a function is already memoized.  Then it is illegal to memoize
  that function.  Moreover, if the function was memoized with an associated
  condition (i.e., was memoized with keyword ~c[:condition] or
  ~c[:condition-fn] having value other than ~c[t] or ~c[nil]), then it is also
  illegal to convert the function from ~c[:]~ilc[program] to ~c[:]~ilc[logic]
  mode (~pl[verify-termination]).  To turn off memoization, ~pl[unmemoize].

  ~c[Memoize] is illegal for a function if its arguments include ~c[state] or
  if it returns any ~il[stobj]s.  Also, ~c[memoize] never allows attachments
  to be used (~pl[defattach]); if an attachment is used during evaluation, then
  the evaluation result will not be stored.

  We conclude with by documenting keyword parameters not discussed above.

  Keyword parameter ~c[:recursive] is ~c[t] by default, which means that
  recursive calls of ~c[fn] will be memoized just as ``top-level'' calls of
  ~c[fn].  When ~c[:recursive] is instead set to ~c[nil], memoization is only
  done at the top level.  Using ~c[:recursive nil] is similar to writing a
  wrapper function that just calls ~c[fn], and memoizing the wrapper instead of
  ~c[fn].

  If ~c[:trace] has a non-~c[nil] value, then ~c[memoize] also traces in a
  traditional Lisp style.  If ~c[:trace] has value ~c[notinline] or
  ~c[notinline], then a corresponding declaration is added at the beginning of
  the new definition of ~c[fn].

  A non-~c[nil] value for ~c[:commutative] can be supplied if ~c[fn] is a
  binary function in ~c[:logic] mode.  If the ~c[memoize] event is successful,
  then subsequently: whenever each argument to ~c[fn] is either a rational
  number or a ~il[hons], then when the evaluation of ~c[fn] on those arguments
  is memoized, the evaluation of ~c[fn] on the swap of those arguments is, in
  essence, also memoized.  If ~c[:commutative] is supplied and is not ~c[nil]
  or ~c[t], then it should be the name of a previously-proved theorem whose
  formula states the commutativity of ~c[fn], i.e., is the formula
  ~c[(equal (fn x y) (fn y x))] for a pair ~c[{x,y}] of distinct variables.  If
  ~c[:commutative] is ~c[t] ~-[] but not merely an expression that evaluates to
  ~c[t] ~-[] then an attempt to prove such a lemma will be made on-the-fly.
  The name of the lemma is the symbol in the same package as ~c[fn], obtained
  by adding the suffix ~c[\"-COMMUTATIVE\"] to the ~ilc[symbol-name] of ~c[fn].
  If the proof attempt fails, then you may want first to prove the lemma
  yourself with appropriate hints and perhaps supporting lemmas, and then
  supply the name of that lemma as the value of ~c[:commutative].

  If ~c[:commutative] is supplied, and a non-commutative condition is provided
  by ~c[:condition] or ~c[:condition-fn], then although the results will be
  correct, the extra memoization afforded by ~c[:commutative] is unspecified.

  If ~c[:memo-table-init-size] is supplied, then it should be a positive
  integer specifying the initial size of an associated hash table.

  Argument ~c[:aokp] is relevant only when attachments are used; ~pl[defattach]
  for background on attachments.  When ~c[:aokp] is ~c[nil], the default,
  computed values are not stored when an attachment was used, or even when an
  attachment may have been used because a function was called that had been
  memoized using ~c[:aokp t].  Otherwise, computed values are always stored,
  but saved values are not used except when attachments are allowed.  To
  summarize:
  ~bf[]
    aokp=nil (default): ``Pure'', i.e., values do not depend on attachments
    - Fetch: always legal
    - Store: only store resulting value when attachments were not used

    aokp=t: ``Impure'', i.e., values may depend on attachments
    - Fetch: only legal when attachments are allowed (e.g., not during proofs)
    - Store: always legal
  ~ef[]

  If ~c[:ideal-okp] is supplied and not ~c[nil], then it is permitted to
  memoize an ``ideal-mode'' function: one in ~c[:]~ilc[logic] mode whose
  ~il[guard]s have not been verified.  In general, it is ill-advised to memoize
  an ideal-mode function, because its calls are typically evaluated ``in the
  logic'' without calling a memoized ``raw Lisp'' version of the function.
  However, if the function is called by a ~c[:]~ilc[program] mode function,
  evaluation can transfer to raw Lisp before reaching the call of the memoized
  function, in which case memoization will take place.  For such situations you
  can provide value ~c[:warn] or ~c[t] for keyword parameter ~c[:ideal-okp].
  Both of these values allow memoization of ideal-mode functions, but if
  ~c[:warn] is supplied then a warning will take place.  Note that you may set
  the key ~c[:memoize-ideal-okp] of the ~ilc[acl2-defaults-table] to value
  ~c[t] or ~c[:warn] to change the default, but if parameter ~c[:ideal-okp] is
  supplied, the ~ilc[acl2-defaults-table] value is ignored.

  If ~c[:verbose] is supplied, it should either be ~c[nil], which will inhibit
  proof, event, and summary output (~pl[with-output]), or else ~c[t] (the
  default), which does not inhibit output.  If the output baffles you, try
  ~bv[]
  :trans1 (memoize ...)
  ~ev[]
  to see the single-step macroexpansion of your ~c[memoize] call.

  The default for ~c[:forget] is ~c[nil].  If ~c[:forget] is supplied, and not
  ~c[nil], then it must be ~c[t], which causes all memoization done for a
  top-level call of ~c[fn] to be forgotten when that top-level call exits.~/

  :cite hons-and-memoization
  :cited-by hons-and-memoization"

  (declare (xargs :guard (booleanp recursive))
           (ignorable condition-p condition condition-fn hints otf-flg
                      recursive trace commutative forget memo-table-init-size
                      aokp ideal-okp verbose))

  #-acl2-loop-only
  `(progn (when (eql *ld-level* 0)

; We are not inside the ACL2 loop (hence not in certify-book, for
; example).

            (let ((state *the-live-state*))
              (warning$ 'memoize nil
                        "No change for function ~x0: Memoization ~
                         requests are ignored in raw Lisp.  In raw ~
                         Lisp, use memoize-fn."
                        ',fn)))
          (value-triple nil))

  #+acl2-loop-only
  (let* ((inline recursive)
         (form
          (cond
           ((eq commutative t)
            `(make-event
              (let* ((fn ,fn)
                     (commutative
                      (intern-in-package-of-symbol
                       (concatenate 'string (symbol-name fn) "-COMMUTATIVE")
                       fn)))
                (list ; use encapsulate so that each form is printed first
                 'encapsulate
                 ()
                 (list 'defthm commutative
                       (list 'equal
                             (list fn 'x 'y)
                             (list fn 'y 'x))
                       :rule-classes nil)
                 (memoize-form (kwote fn) ',condition ',condition-p
                               ',condition-fn ',hints ',otf-flg ',inline
                               ',trace
                               (kwote commutative)
                               ',forget
                               ',memo-table-init-size
                               ',aokp
                               ',ideal-okp)))))
           (t (memoize-form fn condition condition-p condition-fn
                            hints otf-flg inline trace commutative forget
                            memo-table-init-size aokp ideal-okp)))))
    (cond (verbose form)
          (t `(with-output
               :off (summary prove event)
               :gag-mode nil
               ,form)))))

(defmacro unmemoize (fn)

  ":Doc-Section Events

  turn off memoization for the specified function~/
  ~bv[]
  Example:
  (unmemoize 'foo) ; turn off memoization of foo~/

  General Form:
  (unmemoize fn)
  ~ev[]

  where ~c[fn] evaluates to a function symbol that is currently
  memoized; ~pl[memoize].  An exception is that as with ~ilc[memoize],
  ~c[fn] may evaluate to the name of a macro that is associated with
  such a function symbol; ~pl[macro-aliases-table].

  Calls of this macro generate events of the form
  ~c[(table memoize-table fn nil)].  When successful, the returned
  value is of the form ~c[(mv nil function-symbol state)].

  To remove the effects of all ~ilc[memoize] ~il[events], evaluate:
  ~c[(clear-memo-table)].  To save and restore memoization,
  ~pl[save-and-clear-memoization-settings] and
  ~pl[restore-memoization-settings].~/

  :cite hons-and-memoization
  :cited-by hons-and-memoization"

  (declare (xargs :guard t))
  #-acl2-loop-only
  `(progn (when (eql *ld-level* 0)

; We are not inside the ACL2 loop (hence not in certify-book, for
; example).

            (warning$ 'unmemoize nil
                      "No change for function ~x0: Unmemoization requests are ~
                       ignored in raw Lisp.  In raw Lisp, use unmemoize-fn."
                      ',fn))
          (value-triple nil))
  #+acl2-loop-only
  `(with-output
    :off summary
    (progn (table memoize-table
                  (deref-macro-name ,fn (macro-aliases world))
                  nil)
           (value-triple
            (deref-macro-name ,fn (macro-aliases (w state)))))))

(defmacro profile (fn &rest r)

  ":Doc-Section Events

  turn on profiling for one function~/

  NOTE: An alternative to this utility, which has a lot less functionality but
  doesn't depend on the experimental extension of ACL2 mentioned just below,
  may be found in community book ~c[books/misc/profiling.lisp].

  This documentation topic relates to an experimental extension of ACL2 under
  development by Bob Boyer and Warren Hunt.  ~l[hons-and-memoization] for a
  general discussion of memoization, on which this ~c[profile] utility is
  built, and the related features of hash consing and applicative hash tables.

  ~c[Profile] can be useful in Common Lisp debugging and performance analysis,
  including examining the behavior of ACL2 functions.

  ~bv[]
  Example:
  (profile 'fn)       ; keep count of the calls of fn
  (profile 'fn        ; as above, with with some memoize options
           :trace t
           :forget t)
  (memsum) ; report statistics on calls of memoized functions (e.g., fn)
  (clear-memoize-statistics) ; clear memoization (and profiling) statistics
  ~ev[]

  Evaluation of ~c[(profile 'fn)] redefines ~c[fn] so that a count will be kept
  of the calls of FN.  The information recorded may be displayed, for example,
  by invoking ~c[(]~ilc[memoize-summary]~c[)] or (equivalently) ~c[(memsum)].
  If you wish to gather fresh statistics for the evaluation of a top-level
  form, ~pl[clear-memoize-statistics].

  ~c[Profile] is just a macro that calls ~ilc[memoize] to do its work.
  ~c[Profile] gives the two keyword parameters ~c[:condition] and
  ~c[:recursive] of ~ilc[memoize] the value ~c[nil].  Other keyword parameters
  for ~c[memoize], which must not include ~c[:condition], ~c[:condition-fn], or
  ~c[:recursive], are passed through.  To eliminate profiling, use
  ~ilc[unmemoize]; for example, to eliminate profiling for function ~c[fn],
  evaluate ~c[(unmemoize 'fn)].

  You may find raw Lisp functions ~c[profile-all] and ~c[profile-acl2] to be
  useful.  Please contact the ACL2 developers if you want versions of these
  functions to be executable from inside the ACL2 read-eval-print loop.~/~/"

  (declare (xargs :guard (and (keyword-value-listp r)
                              (not (assoc-keyword :condition r))
                              (not (assoc-keyword :condition-fn r))
                              (not (assoc-keyword :recursive r)))))
  `(memoize ,fn :condition nil :recursive nil ,@r))

#-hons
(defmacro memoize-on-raw (fn form)
  (declare (ignore fn))
  form)

(defmacro memoize-on (fn form)

; MEMOIZE-ON evaluates form.  During the evaluation the symbol fn has as
; its symbol-function what it had immediately AFTER the memoization of
; fn.  Hence, the values of calls of fn may be remembered during the
; evaluation and later.  Warning: to use MEMOIZE-ON, fn must already
; be memoized.

  `(return-last 'memoize-on-raw ,fn ,form))

#-hons
(defmacro memoize-off-raw (fn form)
  (declare (ignore fn))
  form)

(defmacro memoize-off (fn form)

; MEMOIZE-OFF evaluates form.  During the evaluation the symbol fn has as
; its symbol-function what it had immediately BEFORE the memoization
; of fn.  Hence the values of calls of fn may not be remembered during
; the evaluation.  Warning: to use MEMOIZE-OFF, fn must already be
; memoized."

  `(return-last 'memoize-off-raw ,fn ,form))

(defmacro memoizedp-world (fn wrld)
  `(let ((fn ,fn)
         (wrld ,wrld))
     (cond
      ((not (global-val 'hons-enabled wrld))
       (er hard 'memoizedp
           "Memoizedp cannot be called in this ACL2 image, as it requires a ~
            hons-aware ACL2.  See :DOC hons-and-memoization."))
      (t
       (cdr (assoc-eq fn (table-alist 'memoize-table wrld)))))))

(defmacro memoizedp (fn)
  (declare (xargs :guard t))
  `(memoizedp-world ,fn (w state)))

;;; hons-shrink-alist

; HONS-SHRINK-ALIST, when called with an atomic second
; argument, produces an alist that is alist-equivalent
; to the first argument, but with all irrelevant entries in
; the first argument deleted.  Informal remark: the alist
; returned is a hons when the initial ANS is not an atom.

; Comment about the last clause above.  Or really?
; Counterexamples?
;
; mbu> stp
; ? (honsp (hons-shrink-alist '((a . b) (a . b2)) (hons-acons 1 2 3)))
; NIL
;
; mbu> stp
; ? (honsp (hons-shrink-alist '((a . b) (a . b2)) nil))
; NIL
; ?

; Some centaur/ books put entries in *never-profile-ht*.  In order to allow
; those books to certify in vanilla ACL2, we define a default value for that
; variable here.

#+(and (not hons) (not acl2-loop-only))
(defparameter *never-profile-ht*
  (make-hash-table :test 'eq))

#+(or acl2-loop-only (not hons))
(defun never-memoize-fn (fn)
   (declare (xargs :guard (symbolp fn))
            (ignore fn))
   nil)

(defmacro never-memoize (fn)
  ":Doc-Section Hons-and-Memoization
  Mark a function as unsafe to memoize.~/

  This ~il[documentation] topic relates to the experimental extension of ACL2
  supporting hash cons, fast alists, and memoization;
  ~pl[hons-and-memoization].

  Logically, this function just returns ~c[nil].  But execution of
  ~c[(never-memoize fn)] records that ~c[fn] must never be memoized, so that
  any attempt to memoize ~c[fn] will fail.

  Any function can be marked as unsafe to memoize; in fact, ~c[fn] need not
  even be defined at the time it is marked.

  This is useful for prohibiting the memoization of functions that are known to
  involve destructive functions like ~c[nreverse].~/~/"

  (declare (xargs :guard (symbolp fn)))
  `(make-event
    (prog2$ (never-memoize-fn ',fn)
            '(value-triple :invisible))
    :check-expansion t))
