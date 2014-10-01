; ACL2 Version 6.5 -- A Computational Logic for Applicative Common Lisp
; Copyright (C) 2014, Regents of the University of Texas

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
; Austin, TX 78712 U.S.A.

; memoize-raw.lisp -- Raw lisp definitions for memoization functions, only to
; be included in the experimental HONS version of ACL2.

; The original version of this file was contributed by Bob Boyer and Warren
; A. Hunt, Jr.  The design of this system of Hash CONS, function memoization,
; and fast association lists (applicative hash tables) was initially
; implemented by Boyer and Hunt.  Contributions have been made since then by
; Jared David, Matt Kaufmann, J Moore, and Sol Swords.

(in-package "ACL2")

; SECTION: To do, near-term

; - Incorporate some Lisp comments into the :doc.  In particular, probably the
;   *record-xxx* and *report-xxx* should be incorporated into the :doc.  In
;   general, add/improve documentation, including for the following.
;   - *memoize-summary-order-list*
;   - *sort-to-from-by-calls*
;   - memoize (e.g., clarify/emphasize that :recursive actually avoids inlining
;     and :recursive nil avoids counting recursive calls in (memsum)); maybe
;     explain how fns like LEN with special raw-Lisp code can thus be memoized
;     only with :recursive nil; perhaps move some things from the Lisp comment
;     to the :doc
;   - Memoize-summary and memsum.  Incorporate long comment in memoize-summary.
;     Update :doc (maybe other topics too) to clarify that we stop at
;     most-positive-mfixnum [see safe-incf].  Alternatively, memsum could just
;     print a message if we ever hit that limit, and require an optional
;     argument if one wants the results anyhow.
;   - Update :doc for the pons/hons-wash soundness fix checked into git,
;     especially for hons-wash.

; - Consider counting pons calls even when a number is returned; else make sure
;   the :doc is clear about this.  (See the definition of pons.)

; - Perhaps write an essay summarizing how memoization works, including
;   discussion of *memoize-call-array* (or at least pointing to the comment
;   there).

; - Add interface functions, perhaps including the following.  I can imagine a
;   single macro or function that takes, say, a keyword argument in order to
;   print (to the comment window, or to state perhaps using the oracle) what's
;   desired.  OR -- maybe suitable utilities can go into books, if we make
;   enough interface functions available.

;   o *Memoize-summary-order-list* (as a state global perhaps)

;   o Profile, unmemoize-profiled; maybe even profile-all and profile-acl2, but
;     maybe keep those instead in books/centaur/memoize/old/profile*, or maybe
;     both, with a sort of autoloading as is done for WET.

;   o And so on -- see in particular function with this comment: "Note: This
;     function should probably either be made available in the loop or else
;     eliminated."

; - If we want to be able to memoize n functions, then it looks like the number
;   of (virtual) columns of *memoize-call-array* need only be something like
;   n+5.  So perhaps that array need not be a square array -- it can have fewer
;   columns than rows -- in which case we can save close to a factor of two on
;   space.  But that might well require considerable code re-work; for example,
;   memoize-call-array-grow computes (/ *2max-memoize-fns* 2), but surely that
;   would have to change.  It's not clear that it's worth saving a factor of
;   roughly two on something whose default is of size 10^6 and might not need
;   to grow.

; - We have calls like (make-symbol "BODY-NAME") and bindings like
;   (,*mf-old-caller* *caller*) -- the former interns a new symbol each time
;   (though with the same, EQ result each time) while the latter saves a symbol
;   using a defconstant form in file acl2.lisp.  Consider making this all more
;   consistent in style.

; - Try (again?) to do initial memoizations before saving the image, rather
;   than at start-up.  Camm Maguire has reported that for GCL, he saw about a
;   5% penalty for those memoizations at start-up.

; SECTION: To do, longer-term

; - Consider eliminating the function memoized-values (and memstat) or, perhaps
;   better yet, have it return a data structure rather than printing individual
;   values.

; - Perhaps think about this comment in the definition of pons:

; It might be tempting to think about creating a static cons here.

; - Consider using memo-max-sizes-entry records not only to guess good sizes,
;   but also to guess good rehash sizes.

; - Maybe think a bit harder about whether our initial memoizations (calls of
;   memoize-fn in acl2h-init-memoizations) are really handled properly, given
;   that our code is so oriented towards calling memoize in the loop.  The
;   current approach seems to have worked well for a long time, so maybe this
;   isn't much of a priority.  But it seems a bit dodgy somehow.

; - Tests such as (< (* 100 local-tt) tt) and (> (* 10000 local-tt) tt) in
;   function memoize-summary-after-compute-calls-and-times restrict reporting
;   to cases where the time is at least 1% of the time taken by the main
;   function.  We might want to make this customizable.

; - Get memoization to be thread-safe.  Jared Davis removed early code in that
;   direction, explaining that it "was just muddying the waters and making
;   things harder to understand."

; - Consider eliminating defun-one-output in most cases, simply for the sake of
; - elegance.

; - Consider eliminating some uses of our-syntax, instead relying on normal
;   ACL2 printing.

; - Look at the following comment in memoize-fn-outer-body and consider the
;   possibility of using clrhash in some cases (e.g., there and in
;   clear-one-memo-and-pons-hash) to save spec.

; Below, we "clear" the tables by setting them to nil, rather than by calling
; clrhash.  The latter approach would probably avoid reallocation of space, but
; we suspect that such a gain in space efficiency might be offset by a loss in
; time efficiency.  The present approach has been working, so we prefer not to
; change it.  Below is just a little space analysis.

; - Consider printing sufficiently small floats without E notation.

; - Think about when to use defv vs. defg; maybe pick one and stick with it?
;   Or perhaps better yet, this question might be moot after considering the
;   next item.

; - Perhaps bundle up user-settable variables (see "User-settable variables for
;   recording" below) into a single defrec stored in a state global, and
;   provide suitable interface functions.  Careful though -- some books may
;   bind current such variables, so we'd probably want to provide a convenient
;   mechanism for doing such bindings.  As Jared notes, if such records are
;   stored in ordinary special variables -- i.e., not introduced with defg or
;   defv -- then although some performance advantage of defg/defv might be
;   lost, it can be easier to support multi-threading by taking advantage of
;   the fact that bindings of specials are thread-local.  He also reminds us of
;   the ability to use local variables [see for example the use of
;   physical-memory-cached-answer in the defun of physical-memory], and tells
;   us that these can give similar efficiency to defv/defg with the similar
;   drawback of not being thread-local, but with the advantage that the
;   locality can ease not only ACL2 source code maintenance, but also avoid
;   problems for other people's code (because it can't access such globals
;   directly).

; - Document user-settable variables (or if the item just above is implemented
;   with a record stored in a state global, document the fields and/or their
;   readers and setters).

; - Try turning egc on in CCL.  (See function acl2h-init.)  Jared says (9/2014)
;   that "leaving on EGC could really reduce the memory requirements of 95+% of
;   the ACL2 jobs in the community books, and could be really good."

; - Consider moving start-sol-gc and supporting functions out of the ACL2 code
;   base, quite possibly into community books directory
;   books/centaur/misc/memory-mgmt/.  But perhaps create some way (an interface
;   of some sort) to get the effect of start-sol-gc, when desirable, without
;   the need for trust tags.  Perhaps consider the effect on ACL2(hp).  Jared
;   thinks that removing memory management responsibility out of the ACL2
;   sources "might be especially useful if you are going to turn EGC back on by
;   default."

; - In pons-addr-of-argument, (+ hl-dynamic-base-addr (hl-staticp x)) is
;   probably a fixnum.  Especially for GCL, maybe wrap (the fixnum ...) around
;   it.  Also maybe declaim a return type of (values (or null fixnum)), in case
;   that helps GCL in particular; or maybe make this a macro (or at least
;   inline it, but then maybe we still want the declaim form).

; - Revisit the comment in mf-index about how we use hl-staticp without
;   checking that the argument is as normally expected.

; - Consider this suggestion from Jared, quoting a comment in memoize:

; Jared Davis suggests that we consider bundling up these 13 parameters, for
; example into an alist.  He says: "Various subsets of these arguments occur in
; spaghetti fashion throughout the code for memoize, add-trip, the
; memoize-table stuff, etc."

; - Investigate odd behavior of with-lower-overhead for LispWorks, as explained
;   in a comment there.




; Experimental: Multithreaded Memoization
;
; Usage: build ACL2 like this:
;
;    $ make ACL2_HONS=h ACL2_MT_MEMO=1 ...
;
; This basically does a (pushnew :multithreaded-memoize *features*) during the
; build.  The resulting ACL2 is then has the ability to support multi-threaded
; memoization.
;
; Multi-threaded memoization is not enabled by default.  This is appropriate
; for avoiding locking overhead on ordinary, single-threaded ACL2(h) code.  To
; enable multi-threaded memoization (at some cost of locking), you can run:
;
;   (setq *enable-multithreaded-memoization* t)
;
; This activates locking that is intended to allow multiple threads to
; simultaneously execute memoized functions.
;
; The implementation is in many ways suboptimal because, for the most part, I
; just want to get something working.  To keep things simple, I have added a
; single, global memoize lock.  This lock needs to be acquired whenever a
; thread needs to do something that could mutate soundness-related memoize
; state.  This is straightforward, but could (obviously) lead to a lot of lock
; contention if you write multithreaded code that is using memoization heavily.
; It could also slow down single threaded code because of the overhead of
; acquiring and releasing locks all the time.
;
; In the future it would probably be worth reworking things so that, e.g., each
; memo table has its own separate lock.  On the other hand, that makes things
; like deadlock a lot trickier.  That sounds pretty horrifying, so I'm going to
; stick with the simple but possibly slow implementation for now.
;
; BOZO check out *caller*.  I'm not really worried about stats, but it might be
; that if Matt understands this code, we could change it to, e.g., a defvar,
; and let each thread have its own notion of *caller* or whatever other
; variables are necessary...

#+multithreaded-memoize
(defg *enable-multithreaded-memoization*
  ;; By default set up multithreaded memoization only if we are running on
  ;; ACL2(p).  However, nothing here is really ACL2(p) specific, and users of
  ;; plain ACL2(h) can change this in raw Lisp if they know what they're doing.
  #+acl2-par t
  #-acl2-par nil)

#+multithreaded-memoize
(defg *global-memoize-lock*
  ;; BOZO this should probably be using DEFLOCK, but that doesn't seem to work
  ;; on non-ACL2(p) builds.
  (ccl::make-lock '*global-memoize-lock*))

(defmacro with-global-memoize-lock (&rest forms)
  ;; BOZO this should probably be introduced automatically by DEFLOCK, but
  ;; again that doesn't work on non-ACL2(p).
  #-multithreaded-memoize
  `(progn . ,forms)
  #+multithreaded-memoize
  (let ((body (gensym)))
    ;; Avoid duplication of ,forms to avoid code blowup
    `(flet ((,body () . ,forms))
       (if *enable-multithreaded-memoization*
           (ccl::with-lock-grabbed (*global-memoize-lock*) (,body))
         (,body)))))

(defmacro memo-mht (&rest args)

  #-multithreaded-memoize
  ;; For normal, non-multithreaded memoization, this just makes an ordinary
  ;; hash table.  On CCL, attempts to access such a hash table from threads
  ;; other than the thread that created the hash table result in errors.  This
  ;; acts as a kind of simple safety net against multithreaded code mucking
  ;; with a memoize-related hash table.
  `(hl-mht . ,args)

  #+multithreaded-memoize
  ;; Otherwise, for multithreaded memoize, we need to allow all threads to
  ;; access things like the memoize tables, pons tables, etc.  In this case
  ;; we're assuming responsibility for locking.
  ;;
  ;; I believe we could safely use either :shared t or :lock-free t here.  I
  ;; suspect :lock-free may give better performance, but it would be good to
  ;; back this up with experimental evidence.
  `(hl-mht :lock-free t . ,args))



; SECTION: Preliminaries

;; One may comment out the following PUSHNEW and rebuild to get profiling
;; times not based upon the curious and wondrous RDTSC instruction of some x86
;; processors.  On a machine with several cores, the RDTSC values returned by
;; different cores may be slightly different, which could lead one into such
;; nonsense as instructions apparently executing in negative time, when timing
;; starts on one core and finishes on another.  To some extent we ignore such
;; RDTSC nonsense, but we still can report mysterious results since we have no
;; clue about which core we are running on in CCL.

#+ccl
(eval-when
 (:execute :compile-toplevel :load-toplevel)
 (when (fboundp 'ccl::rdtsc)
   (pushnew :RDTSC *features*)))

#+gcl
(when (not (gcl-version->= 2 6 10))

; Note for GCL: As of late May 2013, with-standard-io-syntax seems to work
; properly in ANSI GCL.  If necessary one could use our-with-standard-io-syntax
; here, but better would be to use an up-to-date ANSI GCL.

  (error "Please use GCL Version 2.6.10 or later, as we use the function~%~s, ~
          which might not always be supported in an earlier version."
         'with-standard-io-syntax))

; SECTION: Constants and globals

; This section contains most of the constants and globals in this file,
; including all globals that might be modified (for example, directly by the
; user, or during initialization).

; NOTE: It might be best to skip this section on a first reading, or at most
; browse it lightly, returning to look at specific constants and globals when
; they are encountered later.

; Subsection: type mfixnum

; We use the type mfixnum for counting things that are best counted in the
; trillions or more.  Mfixnums happen to coincide with regular fixnums on
; 64-bit CCL, and may be fixnums in other Lisps (e.g. SBCL 1.1.8 and, as
; confirmed by Camm Maguire Sept. 2014, in 64-bit GCL where fixnums are 64 bits
; long).

(defconstant most-positive-mfixnum

; Warning: In function internal-real-ticks, we rely on this value having a
; binary representation as a sequence of ones.

; This is more than 10^18, that is, more than a billion billions.  It seems
; reasonable to assume (at least in 2014 and for some years beyond) that any
; integer quantities that we accumulate, such as call counts, are less than
; that.  This number is also more than the (2*500,000,000)^2, which is the size
; of *memoize-call-array* when we have approximately 500 million memoized
; functions.

  (1- (expt 2 60)))

(deftype mfixnum ()
  `(integer ,(- -1 most-positive-mfixnum)
            ,most-positive-mfixnum))

; Subsection: User-settable variables for recording

; To minimize metering overhead costs, one may set the "*RECORD-" variables
; below to NIL before memoizing.

; *RECORD-BYTES* and other *RECORD-...* variables are bound in
; REMEMOIZE-ALL, so we use DEFPARAMETER rather than DEFG.

; Warning: Keep the following set of globals in sync with memoize-info, as
; described there.

(defparameter *record-bytes*

; If *record-bytes* is not NIL at the time a function is memoized, we attempt
; to count all heap bytes allocated during calls of that function.

; It is quite possibly fine to replace the following form by T.  However, we
; leave this restriction, which produces nil in 32-bit CCL, because it has
; probably been here for many versions through 6.5 and at this point (August
; 2014) we don't expect much use of 32-bit CCL when doing memoization.

  (and (member :ccl *features*) ; most Lisps don't report bytes
       (> most-positive-fixnum (expt 2 32))))

(defparameter *record-calls*

; If *RECORD-CALLS* is not NIL at the time a function is memoized, we count all
; calls of the function.

  t)

(defparameter *record-hits*

; If *RECORD-HITS* is not NIL at the time a function is memoized, we count the
; number of times that a previously computed answer is used again.

  t)

(defparameter *record-mht-calls*

; If *RECORD-MHT-CALLS* is not NIL at the time a function is memoized, we
; record the number of times that a memoize hash-table is created for the
; function.

  t)

(defparameter *record-pons-calls*

; If *RECORD-PONS-CALLS* is not NIL at the time a function is memoized, pons
; calls are counted.

  t)

(defparameter *record-time*

; If *RECORD-TIME* is not NIL the time a function is memoized, we record the
; elapsed time for each outermost call of the function.

  t)

; Subsection: User-settable variables for reporting

(defg *mf-print-right-margin* ; rather arbitrary default; seems to work well
  79)

(defv *report-bytes*

; When memoize-summary is invoked, print the number of bytes allocated on the
; heap, if this variable is not nil at that time and the host Lisp supports
; providing that information.

  #+ccl t #-ccl nil)

(defv *report-calls*

; When memoize-summary is invoked, print the number of calls, if this variable
; is not nil at that time.

  t)

(defv *report-calls-from*

; When memoize-summary is invoked, print the following if this variable is not
; nil at that time: which functions called the given function, how many times,
; and how long the calls took.

  t)

(defv *report-calls-to*

; When memoize-summary is invoked, print the following if this variable is not
; nil at that time: which functions were called by the given function, how many
; times, and how long the calls took.

  t)

(defv *report-hits*

; When memoize-summary is invoked, print the number of times that a previously
; computed answer was reused, if this variable is not nil at that time.

  t)

(defv *report-mht-calls*

; When memoize-summary is invoked, print the number of times that a memo
; hash-table for the function was created, if this variable is not nil at that
; time.  This may be of interest to those who memoize functions with stobj
; arguments, since when such a stobj changes, the function's memoization hash
; table is deleted, and then later, when necessary, created afresh.

  t)

(defv *report-pons-calls*

; When memoize-summary is invoked, print the number of calls of pons, if this
; variable is not nil at that time.

  t)

(defv *report-time*

; When memoize-summary is invoked, print information about the total time used
; to compute the outermost calls, if this variable is not nil at that time.

  t)

(defv *report-on-memo-tables*

; When memoize-summary is invoked, print information about memo tables, if this
; variable is not nil at that time.

  t)

(defv *report-on-pons-tables*

; When memoize-summary is invoked, print information about pons tables, if this
; variable is not nil at that time.

  t)

(defg *sort-to-from-by-calls* nil)

(defg *memoize-summary-order-reversed*

; When memoize-summary is invoked, report on functions in order from least to
; greatest, if this variable is not nil at that time.

  nil)

(defg *mf-print-alist-width* 45)

(defg *memoize-summary-order-list*

; This is a list of functions that MEMOIZE-SUMMARY uses to sort all functions
; that are currently memoized in preparation for displaying information about
; them.  The order used is lexicographical, with the first order having the
; most weight.  Each order function takes one argument, a symbol, and returns a
; rational.

; The default is '(total-time number-of-calls).

; Options for the functions include the following.

;    bytes-allocated [CCL only]
;    bytes-allocated/call [CCL only]
;    execution-order
;    hits/calls
;    pons-calls
;    number-of-calls
;    number-of-hits
;    number-of-memoized-entries
;    number-of-mht-calls
;    symbol-name-order
;    time-for-non-hits/call
;    time/call
;    total-time

  '(total-time number-of-calls))

(defg *memoize-summary-limit*

; The value is either nil or the maximum number of functions upon which
; memoize-summary reports.  A nil value means report on all."

  20)

(defg *condition-nil-as-hit*

; Set this variable to a non-nil value if you want the failure of a memoization
; condition to be recorded as a "hit".  That seems counterintuitive, which is
; why the default is nil.  (Note profiling doesn't report misses, so this
; decision doesn't impact profiling reports.)  But if you care a lot about the
; "Time per missed call" reported by memsum, maybe you'll want to set this to
; t.  NOTE that this value is consulted at the time a function is memoized, not
; at call time or memsum time.

  nil)

; Subsection: Miscellaneous user-settable variables

(defvar *never-memoize-ht*

; Function exit-boot-strap-mode further populates this hash table by calling
; function initialize-never-memoize-ht.

; Users can set this with never-memoize.

  (let ((ht (memo-mht :test 'eq)))
    (loop for x in *stobjs-out-invalid*
          do (setf (gethash x ht) t))
    #+ccl (setf (gethash 'ccl::rdtsc ht) t) ; used in memoize implementation
    ht))

; Subsection: Variables not user-settable (managed by the implementation)

(defg *float-ticks/second* (float (expt 2 31))) ; 2 GHz
(defg *float-ticks/second-initialized* nil)

(declaim (float *float-ticks/second*))

(defg *pons-call-counter* 0)
(defg *pons-misses-counter* 0)
(declaim (type mfixnum *pons-call-counter*))
(declaim (type mfixnum *pons-misses-counter*))

(defg *mf-shorten-ht* ; see mf-shorten
  ;; [Jared] This would be a perfect candidate for switching to a
  ;;   (let ((mf-shorten-ht ...)) (defun mf-shorten ...))
  ;; style of variable...
  (memo-mht :test 'eql))

(defg *memoize-info-ht*

; This hash table associates memoized function symbols with various
; information.  It has two mappings in one (see setf forms in memoize-fn), that
; is, two kinds of keys: symbols and numbers.
;
;   1. It maps each currently memoized function symbol, fn, to a DEFREC record
;      of type MEMO-INFO-HT-ENTRY.  One field of that record is :NUM.
;
;   2. It maps each such :NUM value back to the corresponding symbol, fn.

  (memo-mht))

(declaim (hash-table *memoize-info-ht*))

(defparameter *memo-max-sizes*

; This hash table binds function names to memo-max-sizes-entry structures.

; Jared originally added this table because he wanted to know how big
; memoization tables were getting (so that he could set up appropriate initial
; sizes), but when tables are cleared they are thrown away, so for tables that
; are frequently cleared it wasn't possible to see how large the table had
; become.

; After seeing the information, it seemed a good idea to use it to infer what a
; good table size might be when the memo table is re-created.

  (memo-mht))

(defun initial-memoize-call-array (n)

; Warning: It is assumed in sync-memoize-call-array that this array has a
; length of 1 when n is 1.

  (make-array n :element-type 'mfixnum :initial-element 0))

(defg *memoize-call-array*

; *Memoize-call-array*, 'ma' for short, is used for storage of the monitoring
; information for memoized functions.  This array is conceptually
; two-dimensional.  To read from or write to this array, see ma-index and the
; ma-index-xxx macros.  Each "dimension" of ma is twice the maximum number of
; memoized functions; so the length is 4 times the square of the maximum number
; of memoized functions.

; The length of this array is both a fixnum and an mfixnum; see
; memoize-call-array-grow.

; Ma is initialized in memoize-init.  Think of ma as a two dimensional array
; with dimensions (twice the max number of memoized functions) x (twice the max
; number of memoized functions).

; COLUMNS.  Each 'column' corresponds to info about a memoized function, but
; the first five columns are 'special'.  We count rows and columns starting at
; 0.  Column 0 is used as scratch space by compute-calls-and-times for sums
; across all functions.  Columns 1, 2, and 3 are not currently used at all.
; Column 4 is for the anonymous 'outside caller'.  Column 5 is for the first
; memoized function, column 6 is for the second, and so on.

; ROWS.  In columns 5 and greater, row 0 is used to count 'bytes', row 1 counts
; 'hits', row 2 counts mht calls, and row 4 counts pons calls that don't simply
; return a number (i.e., an address in the static-hons case).  (3 was formerly
; used to count hons calls, but that is no longer the case.)  The elements of
; an ma column starting at row 10 are for counting and timing info.  Suppose
; column 7 corresponds to the memoized function FOO and column 12 corresponds
; to the memoized function BAR.  Whenever FOO calls BAR, element 2*12 of column
; 7 will be incremented by 1, and the total elapsed ticks for the call will be
; added to element 2*12+1 of column 7.

; Though ma may 'grow', it may not grow while any memoized function is running,
; and here is why: every memoized function has a cached opinion about the size
; of ma.  (Here is a technical explanation, which one may wish to ignore.  For
; example, memoize-fn binds the variable fn-col-base to (ma-index fnn), which
; is computed based on the size of ma at the time the function is memoized.
; Fn-col-base is passed to memoize-fn-outer-body, where it is used to generated
; code for the memoized function.)

  '(initial-memoize-call-array 1))

(declaim (type (simple-array mfixnum (*))
               *memoize-call-array*))

(defg *callers-array*

; At the end of a call of compute-calls-and-times, which is called by
; memoize-summary, (aref *callers-array* n) will contain the numbers of the
; functions that have called the function numbered n.

  (make-array 0))

(declaim (type (simple-array t (*)) *callers-array*))

(defconstant *ma-bytes-index*       0)
(defconstant *ma-hits-index*        1)
(defconstant *ma-mht-index*         2)
; Originally there was an *ma-hons-index* of 3, but we no longer count honses.
(defconstant *ma-pons-index*        4)

; We associate memoized function symbols with fixnums, and vice versa.  See
; symbol-to-fixnum-create.

(declaim (type (and mfixnum

; Normally we are happy to declare variables in this file to be of mfixnum type
; only, but here we also declare these of type fixnum so that indices i below
; such variables may safely appear in forms (loop for i fixnum ...).

                    fixnum)
               *max-symbol-to-fixnum*
               *initial-2max-memoize-fns*
;              *initial-max-symbol-to-fixnum* ; defconstant, below
               *2max-memoize-fns*))

(defconstant *initial-max-symbol-to-fixnum* 4)

(defg *max-symbol-to-fixnum* *initial-max-symbol-to-fixnum*)

(defv *initial-2max-memoize-fns* 1000)

(defg *2max-memoize-fns* ; length of *memoize-call-array*
  *initial-2max-memoize-fns*)

(defg *max-mem-usage*

; This global is set in start-sol-gc.  It is an upper bound, in bytes of memory
; used, that when exceeded results in certain garbage collection actions.

; See also the centaur/misc/memory-mgmt books.

  (expt 2 32))

(defg *gc-min-threshold*

; This is set in start-sol-gc.

; See also the centaur/misc/memory-mgmt books.

  (expt 2 30))

(defg *memoize-init-done* nil)

(defg *hons-gentemp-counter* 0)

(defg *memoize-fn-signature-error*
  ;; [Jared] I think it's ugly for this sort of thing to be a global.
  "Memoize-fn: could not determine a signature for ~a.~%~
  To assert the signature of ~:*~a, use (mf-note-arity '~:*~a nargs nvals),~%~
  for example, (mf-note-arity '~:*~a 3 1).)  If there are stobjs arguments~%~
  then do not use that mechanism; instead, pass suitable arguments to~%~
  memoize-fn.")

(defvar *sol-gc-installed* nil)

(defg *memoize-use-attachment-warning-p* t)

(defv *number-of-arguments-and-values-ht*

; Mf-note-arity is an interface for updating this variable.

; This hash table maps a symbol fn to a cons pair (a . d), where a is the
; number of inputs and d is the number of outputs of fn.  NIL for a or d
; indicates 'don't know'.

  (memo-mht))

(declaim (hash-table *number-of-arguments-and-values-ht*))

; Globals not included in this section:
; - *caller*
; - *10-days*
; - *float-internal-time-units-per-second*

; SECTION: Our-syntax

(defmacro our-syntax (&rest args)

; This macro extends Common Lisp's with-standard-io-syntax by binding *package*
; and *readtable*.  It may not be necessary to bind *readtable* here, but it
; has been done historically and it seems harmless.  We bind *package* because
; the Common Lisp utility with-standard-io-syntax binds *package* to the
; CL-USER package.

; The settings in our-syntax are oriented towards reliable, standard, vanilla,
; mechanical reading and printing, and less towards human readability.

; Please, before changing the following, consider existing uses of this macro
; insofar as the changes might impact reliable, standard, vanilla, mechanical
; printing.

; Consider using our-syntax-nice.

  `(with-standard-io-syntax
    (let ((*package* (find-package-fast
                      (f-get-global 'current-package *the-live-state*)))
          (*readtable* *acl2-readtable*))
      ,@args)))

(defmacro our-syntax-nice (&rest args)

; Our-syntax-nice may offer slightly more pleasant human readabilty than
; our-syntax.  Although we stopped using it ourselves in Sept. 2014, we leave
; it for now since it is used in some books.

  `(our-syntax
    (setq *print-case*                 :downcase)
    (setq *print-pretty*               t)
    (setq *print-readably*             nil)
    (setq *print-right-margin*         ,*mf-print-right-margin*)
    (setq *print-miser-width*          100)
    ,@args))

; SECTION: Number of Arguments

(defun mf-note-arity (fn nargs nvals)

; This raw Lisp function declares that fn has the indicated number of inputs
; and outputs.

  (with-global-memoize-lock
    (setf (gethash fn *number-of-arguments-and-values-ht*)
          (cons nargs nvals))))

(defun memoize-look-up-def-raw (sym quiet-p)

; This function attempts to return the definition of sym as an s-expression
; (not a symbol-function), as (name formals . rest).  When that attempt fails,
; then an error occurs if quiet-p is nil but nil is returned otherwise.

; For CCL, we could evaluate the following two forms so that
; function-lambda-expression will return the form used in the defun of
; a function symbol.

;    (setq ccl::*save-definitions* t)
;    (setq ccl::*fasl-save-definitions* t)

; However, while memoization is implemented with some features specific to CCL
; (e.g., RDTSC), in general we prefer that the functionality be independent of
; the host Lisp, so that books are less likely to fail certification when
; changing host Lisps (or versions of a given host Lisp).  Moreover, an ACL2
; regression based on CCL took close to 2% longer when including those forms in
; acl2.lisp:

; With the above forms:
; 33606.972u 498.459s 1:16:57.09 738.6%   0+0k 0+2676744io 0pf+0w

; Without the above forms:
; 32964.076u 475.053s 1:15:31.71 737.8%   0+0k 135096+2542696io 78pf+0w

; (- 1 (/ (+ 32964.076 475.053) (+ 33606.972 498.459)))
; = 0.019536536570964436

; (- 1 (/ (+ 3600 (* 60 15) 31.71) (+ 3600 (* 60 16) 57.09)))
; = 0.01849216714424018

; The property acl2-saved-def, which appears below, is installed when save-def
; is used; see for example bad-lisp-objectp.

  (let ((temp (get sym 'acl2-saved-def)))
    (cond (temp (cdr temp))
          (t (let* ((fn (symbol-function sym))
                    (lam (and fn (function-lambda-expression fn))))
               (cond (lam (assert (eq (car lam) 'lambda))
                          lam)
                     (quiet-p nil)
                     (t (error "Lisp cannot find a definition for ~
                                ~s.~%Consider using ~s or supplying to ~
                                ~%memoize(-fn) an explicit :CL-DEFUN ~
                                argument.~a"
                               sym
                               'save-def
                               #-ccl
                               ""
                               #+ccl
                               (format
                                nil
                                "~%Alternatively, you might solve this ~%~
                                 problem, for CCL only, by setting Lisp ~%~
                                 globals CCL::*SAVE-DEFINITIONS* and ~%~
                                 CCL::*FASL-SAVE-DEFINITIONS* to T before~%~
                                 defining ~a (though this might slow down~%~
                                 performance)."
                                sym)))))))))

(defun-one-output mf-len-inputs (fn)

; This function returns the length of the inputs of fn, or nil for "don't
; know".

  (assert (symbolp fn))
  (assert (fboundp fn))
  (assert (not (macro-function fn)))
  (assert (not (special-operator-p fn)))

  (with-global-memoize-lock
    (or (let ((pair (gethash fn *number-of-arguments-and-values-ht*)))
          (and (consp pair)
               (integerp (car pair))
               (car pair)))
        (let ((formals
               (getprop fn 'formals t 'current-acl2-world (w *the-live-state*))))
          (and (not (eq t formals))
               (length formals)))
        (let ((def (memoize-look-up-def-raw fn t)))
          (and def (length (cadr def)))))))

(defun-one-output mf-len-outputs (fn)

; This function returns the length of the outputs of fn, or nil for "don't
; know".

  (assert (symbolp fn))
  (assert (fboundp fn))
  (assert (not (macro-function fn)))
  (assert (not (special-operator-p fn)))

  (with-global-memoize-lock
    (or (let ((pair (gethash fn *number-of-arguments-and-values-ht*)))
          (and (consp pair)
               (integerp (cdr pair))
               (cdr pair)))
        (let* ((state *the-live-state*)
               (w (w state)))
          (and (not (eq t (getprop fn 'formals t 'current-acl2-world w)))
               (len (stobjs-out fn w))))
        (and (get fn 'acl2-saved-def)

; Save-def guarantees that there is a single output of the defined function.

             1))))

; SECTION: Timing Utilities

; WARNING: Whenever using *float-ticks/second*, consider whether it should be
; properly initialized if that has not already been done.  Here is the story:

; In order to set *float-ticks/second* to a reasonably accurate value, there is
; a one-time delay due to a call of sleep in float-ticks/second-init, which
; might be noticeable when starting up ACL2.  We avoid this delay until we need
; the accuracy.  For example, fix-ticks is used in the wrappers of memoized
; functions, making it performance-critical, but it only uses
; float-ticks/second to compute a heuristic sanity check; so we avoid that
; delay in fix-ticks.  On the other hand, for many purposes we want
; *float-ticks/second* to be accurate, such as in calls of total-time (for
; printing memoize-summary information).  For those, we tolerate the delay.

; The community book books/centaur/memoize/timer.lsp provides some potentially
; useful ideas, but as of this writing (late August 2014) we stick pretty close
; to what has previously been done here.

(defconstant *10-days-in-seconds* (* 10 24 60 60))

(defun 10-days ()
  (let ((n (* *10-days-in-seconds*
              (ceiling *float-ticks/second*))))
    (when (> n most-positive-mfixnum)

; It's OK to comment out the following error and only do the setq.  But we
; have the error here in order to catch confusion on our part.  In one
; experiment circa Sept 2014 on a 2.66 GHz Mac we got this:

; ? (10-days)
; 1855425871872000
; ? most-positive-mfixnum
; 1152921504606846975
; ? 

      (error "~s is too large: ~s.  This is a surprise!~%Please ~
              contact the ACL2 implementors."
             '(10-days)
             n)
      (setq n most-positive-mfixnum))
    n))

(defg *10-days*

; We get a reasonable approximation based on *float-ticks/second*, which is
; improved after calling float-ticks/second-init.

  (10-days))

(declaim (type mfixnum *10-days*))

(defg *float-internal-time-units-per-second*
  (float internal-time-units-per-second))

(declaim (float *float-internal-time-units-per-second*))

(defmacro the-mfixnum (x)

; This silly macro may help someday in debugging, using code such as is found
; in the comment just below.  Of course, by adding an optional argument that
; specifies some sort of location for this call, we can get more specific
; debugging information.  Debugging could also be aided by replacing this with
; a corresponding defun, which could be traced.

; `(let ((x ,x))
;    (cond ((not (typep x 'fixnum))
;           (error "OUCH")))
;    (the mfixnum x))

  `(the mfixnum ,x))

(defmacro internal-real-ticks ()

; We use logand below instead of mod because it is faster (see below).  This
; use of logand relies on the fact that the binary representation of
; most-positive-mfixnum is a sequence of ones.

; The following tests use values of i that are fixnums, because that is what we
; expect to encounter in most cases and they avoid the overhead of building
; bignums.  But there is no reason to expect the overwhelming advantage of
; avoiding mod to disappear if bignums are involved.  Indeed, if "to
; most-positive-mfixnum" is replaced by "(+ most-positive-mfixnum n)" below,
; convincing results are still obtained.

;   (defun my-test-0 (n)
;     (loop for i from (- most-positive-mfixnum n) to most-positive-mfixnum
;           when (eql (the integer i)
;                     -1)
;           do (error "Found 0!")))
;
;   (defun my-test-1 (n)
;     (loop for i from (- most-positive-mfixnum n) to most-positive-mfixnum
;           when (eql (the integer (logand i most-positive-mfixnum))
;                     -1)
;           do (error "Found 0!")))
;
;   (defun my-test-2 (n)
;     (loop for i from (- most-positive-mfixnum n) to most-positive-mfixnum
;           when (eql (the integer (mod i most-positive-mfixnum))
;                     -1)
;           do (error "Found 0!")))
;
;   (time$ (my-test-0 10000000))
;   (time$ (my-test-1 10000000))
;   (time$ (my-test-2 10000000)) ; much slower than the others

; Note that (ccl::rdtsc) returns a fixnum; see
; http://trac.clozure.com/ccl/wiki/ReleaseNotes.

  #+(and RDTSC (not 32-bit-target)) ; faster for 64
  '(the-mfixnum (ccl::rdtsc))
  #+(and RDTSC 32-bit-target)          ; slower for 32
  '(the-mfixnum (logand (ccl::rdtsc64) ; don't truncate at 32-bit CCL fixnum
                        most-positive-mfixnum))
  #-RDTSC
  '(the-mfixnum (logand (the-mfixnum (get-internal-real-time))
                        most-positive-mfixnum)))

(defun-one-output float-ticks/second-init ()

; [Jared] multithreading note: I think it's fine not to protect this with a
; lock, if two threads happen to recompute it, that's seems harmless enough.

  (unless *float-ticks/second-initialized*
    #+RDTSC (let ((i1 (ccl::rdtsc64))
                  (i2 (progn (sleep .1) (ccl::rdtsc64))))
              (cond
               ((> i2 i1)
                (setq *float-ticks/second*
                      (* 10 (float (- i2 i1)))))
               (t ; retain initial value of *float-ticks/second*
                (format t
                        "~%***WARNING***: Float-ticks/second-init ~
                         failed;~%using arbitrary default value.~%Memoize ~
                         timings may be unreliable.~%")
                (force-output *standard-output*))))
    #-RDTSC (setq *float-ticks/second*
                  *float-internal-time-units-per-second*)
    (setq *10-days* (10-days))
    (setq *float-ticks/second-initialized* t)
    (check-type *float-ticks/second*
                (and float (satisfies plusp)))))

; SECTION: Safe-incf

(defun safe-incf-aux-error (x inc where)
  (declare (type mfixnum x inc))
  (cond
   (where
    (error "~%; SAFE-INCF-AUX: ** Error: ~a."
           (list :x x :inc inc :where where)))
   (t (setf (the mfixnum x)
            most-positive-mfixnum)))
  nil)

(defmacro safe-incf-aux (x inc &optional where)

; This is essentially safe-incf, but where inc is known to have a positive
; integer value.

  (cond
   ((not (or (symbolp inc)
             (and (< inc most-positive-mfixnum)
                  (> inc 0))))
    (safe-incf-aux-error x inc where))
   ((and (true-listp x) ; e.g., x is (aref ar (.. expr ..))
         (equal (len x) 3)
         (member (car x) '(aref svref))
         (symbolp (nth 1 x))
         (consp (nth 2 x)))
    (let ((idx (make-symbol "IDX")))
      `(let ((,idx (the-mfixnum ,(nth 2 x))))
         (declare (type mfixnum ,idx))
         (safe-incf (,(nth 0 x)
                     ,(nth 1 x)
                     ,idx)
                    ,inc
                    ',where))))
   (t (let ((v (make-symbol "V")))
        `(let ((,v (the-mfixnum ,x)))
           (declare (type mfixnum ,v))
           (cond ((<= ,v (the-mfixnum
                              (- most-positive-mfixnum
                                 (the-mfixnum ,inc))))
                  (setf (the mfixnum ,x)
                        (the-mfixnum (+ ,v (the-mfixnum ,inc))))
                  nil)
                 (t (safe-incf-aux-error ',x ',inc ',where))))))))

(defmacro safe-incf (x inc &optional where)

; Summary: we increment nonnegative mfixnum x by nonnegative mfixnum inc,
; returning nil.  But if the result is too large to be of type mfixnum, then we
; cause an error if where is non-nil, else we set x to most-positive-mfixnum.

; SAFE-INCF is a raw Lisp macro that behaves the same as INCF when both X and
; INC are nonnegative MFIXNUMs and their sum is a nonnegative MFIXNUM.  In a
; call of (SAFE-INCF x inc), X must be a place that holds an MFIXNUM.  INC must
; evaluate to an MFIXNUM.  Both X and INC must evaluate without side effects,
; so that it is impossible to tell which was executed first or whether only one
; or both were executed.  If INC is not positive, no update takes place at all.
; Otherwise, if the sum of the values of X and INC is not an MFIXNUM, which is
; tested without causing an error, a run-time error will be caused.  Else, if
; the sum is an MFIXNUM then, as with INCF, the place X will be set to hold the
; sum of the old value of that place and the value of INC.  The value returned
; by SAFE-INCF is NIL.  Caution: INC may be evaluated first, which is why side
; effects are prohibited.

; An optional third parameter is merely to help with error location
; identification.

; In (SAFE-INCF (AREF A (FOO)) INC), (FOO) is only evaluted once.
; Same for SVREF.

; The argument, where, is only used in reporting errors.  When where is
; non-nil, an error occurs if (+ x inc) is too large to be an mfixnum;
; otherwise, x is set to most-positive-mfixnum.  Note that nil is always
; returned; the only purpose is to increment x, not return a value.

  (cond ((integerp inc)
         (if (<= inc 0)
             nil
           `(safe-incf-aux ,x ,inc ,where)))
        ((symbolp inc)
         `(if (>= 0 (the-mfixnum ,inc))
              nil
            (safe-incf-aux ,x ,inc ,where)))
        (t (let ((incv (make-symbol "INCV")))
             `(let ((,incv (the-mfixnum ,inc)))
                (declare (type mfixnum ,incv))
                (if (>= 0 ,incv)
                    nil
                  (safe-incf-aux ,x ,incv ,where)))))))

; SECTION: Ponsing: Creating keys ("ponses") for memoization tables

; Pons differs from hons in that it does not honsify its arguments and in that
; it takes a hash table as a third argument.  We use pons in memoization.

; We use pons instead of hons in memoization because we could not afford to
; honsify (using fast-alist-fork!, say) certain alists in certain biology
; tests.  About the same time, we (gratuitously) decided to stop hons'ifying
; the output of memoized functions.

; Most of the comments and code in this section were initially derived from
; books/centaur/memoize/pons.lsp, authored by Jared Davis and, as stated there,
; "a descendant of the memoization scheme developed by Bob Boyer and Warren
; A. Hunt, Jr. which was incorporated into the HONS version of ACL2, sometimes
; called ACL2(h)."

; Pons is the critical function for generating memoization keys.  To a rough
; approximation, here is how we memoize (F arg1 arg2 ... argN):
;
;     PONS := (PIST* arg1 ... argN)
;     LOOK := MemoTableForF[PONS]
;     if (LOOK exists)
;        return LOOK
;     else
;        RESULT := (F arg1 arg2 ... argN)
;        MemoTableForF[PONS] = RESULT
;        return RESULT
;
; In other words, we use (PIST* arg1 ... argN) to create the hash key for the
; arguments arg1 ... argN.  And PIST* is defined in terms of PONS.
;
;    (PIST*)          = NIL
;    (PIST* X1)       = X1
;    (PIST* X1 X2)    = (PONS X1 X2)
;    (PIST* X1 X2 X3) = (PONS X1 (PONS X2 X3))
;      ...                ...
;
; As its name suggests, PONS is similar to a HONS.  The main difference is that
; whereas (HONS X Y) requires us to recursively generate a "canonical" version
; of X and Y, (PONS X Y) does not descend into its arguments.
;
; It is worth noting that in the 0 and 1-ary cases of PIST*, no PONSing is
; necessary!  Because of this it can be considerably cheaper to memoize unary
; and zero-ary functions than higher-arity functions.  Note also that as the
; arity of the function increases, the amount of ponsing (and hence its cost)
; increases.
;
; The soundness requirement on PIST* is that two argument lists should produce
; EQL keys only if they are pairwise EQUAL.  This follows from a stronger
; property of PONS:
;
;     (EQL (PONS A B) (PONS C D))  --->  (EQL A C) && (EQL B D).
;
; Why is this property sufficient?  The 0-2 argument cases are trivial.  Here
; is an sketch of the 3-ary case, which generalizes easily to the N-ary case:
;
;    Our goal is to ensure:
;
;       If   (EQL (PIST* A1 B1 C1) (PIST* A2 B2 C2))
;       Then (EQUAL A1 A2) && (EQUAL B1 B2) && (EQUAL C2 C2)
;
;    Assume the hypothesis:
;
;       (EQL (PONS A1 (PONS B1 C1)) (PONS A2 (PONS B2 C2)))
;
;    Then from our PONS property it follows immediately that
;
;      1. (EQL A1 A2), and hence (EQUAL A1 A2) since EQL implies EQUAL.
;      2. (EQL (PONS B1 C1) (PONS B2 C2)).
;
;    From 2, again from our PONS property it follows that
;
;      1. (EQL B1 B2), and hence (EQUAL B1 B2) since EQL implies EQUAL.
;      2. (EQL C1 C2), and hence (EQUAL C1 C2) since EQL implies EQUAL.
;
;    Which is what we wanted to show.
;
; For our memoization scheme to be effective, it is desirable for PIST* to
; produce EQL keys when given pairwise-EQL argument lists.  This follows easily
; if our PONS property holds in both directions, that is:
;
;     (EQL (PONS A B) (PONS C D))  <--->  (EQL A C) && (EQL B D).
;
; Okay, so how does PONS actually work?  First we will introduce a "slow"
; ponsing scheme, and then explain an optimization that avoids slow ponsing in
; many cases.
;
;
; Slow Ponsing.
;
; The above discussion hides the fact that PONS and PIST* take an additional
; argument, called the Pons Table.  This table is essentially a scheme for
; remembering which keys we have produced for argument lists that have been
; encountered thus far.  Note that the act of PONSing implicitly modifies the
; Pons Table.
;
; The Pons Table is similar to the CDR-HT-EQL in the Classic Honsing scheme;
; see the Essay on Classic Honsing.  That is, it is an EQL hash table that
; binds each
;
;    Y ->  { key : key is the key for (PONS X Y) }
;
; As in classic honsing, these sets are represented as Flex Alists.  The basic
; implementation of (PONS X Y), then, is as follows:
;
;     Y_KEYS := PonsTable[Y]
;     XY_KEY := FlexAssoc(X, Y_KEYS)
;     If (XY_KEY was found)
;        return XY_KEY
;     Else
;        NewKey = (CONS X Y)
;        Y_KEYS := FlexAcons(NewKey, Y_KEYS)
;        PonsTable[Y] := Y_KEYS
;        return NewKey
;
; In other words, we build a new (X . Y) cons and use it as the key, unless we
; had previously seen these same arguments and such a key is already available.
;
;
; Avoiding Slow Ponsing.
;
; When static honsing is enabled, we activate an improvement to slow ponsing.
;
; In particular, if X and Y can be assigned addresses (see the discussion of
; Static Hons Addressing from hons-raw.lisp) without the use of an OTHER-HT or
; STR-HT, then we can just combine their addresses with hl-addr-combine (which
; is one-to-one) and use the resulting integer as our key.  In many cases this
; allows us to avoid the hash table lookups required in Slow Ponsing.
;
; The basic ideas here are:
;
;   - Some ACL2 objects (any static conses, symbol, or small fixnum) have
;     addresses, but other objects (larger numbers, characters, strings, and
;     ordinary conses) do not.
;
;   - If (PONS X Y) is given X and Y that both have addresses, we basically
;     just hash their addresses with hl-addr-combine.  The resulting integer is
;     used as the key.
;
;   - Otherwise, we fall back to Slow Ponsing.  Since slow ponsing always
;     creates a cons instead of an integer, there's no possibility of confusion
;     between the keys from the two schemes.

; Note that unlike much of the memoization code, pons address calculation can
; traffic in fixnums rather than mfixnums.

#+static-hons
(defun pons-addr-of-argument (x)

; Warning: Keep this in sync with hl-addr-of and hl-addr-of-unusual-atom.

; See hl-addr-of.  This is similar, except without the STR-HT or OTHER-HT we
; can simply fail to assign addresses to strings, large numbers, rationals, and
; so forth.

  (cond ((eq x nil) 256)
        ((eq x t)   257)
        ((symbolp x)
         (hl-symbol-addr x))
        ((and (typep x 'fixnum)
              (<= hl-minimum-static-int (the fixnum x))
              (<= (the fixnum x) hl-maximum-static-int))
         (the fixnum
              (+ hl-static-int-shift (the fixnum x))))
        ((characterp x)
         (char-code x))

        ((and (consp x)
              (hl-hspace-truly-static-honsp x *default-hs*))

; Note that a honsp is not garbage collected unless it is first freed from its
; addr-table.  So the following value will correspond to x until a hons-wash is
; done, which is long enough since a hons-wash clears all pons tables.

; [Jared] Is this OK for multithreaded memoize?  I think so.  The scenario here
; is:
;
;  - The memo tables are shared across all threads
;  - Each thread has its own hons space and their own notion of which
;    conses are hl-hspace-truly-static-honsp
;  - It is NOT OK (as in, it would be a soundness bug) for us to keep memo
;    table entries after hons spaces get washed or cleared, because the index
;    we're computing could then be reassigned to some other cons, as described
;    in the comment below about "mistake" and "contradiction".
;
; The current strategy is to have the hons wash/clear functions clear all the
; memo tables to ensure this doesn't happen.  I think that's sufficient even in
; a multithreaded context: even though some honses in space A may not be honses
; in space B, they still have uniquely assigned indices (their hl-staticp
; indices), and that's all we're relying on here.  In other words, I think we
; may get memoize misses because of differences in whether things are honsed,
; but we aren't going to get any false hits.

         (+ hl-dynamic-base-addr (hl-staticp x)))
        (t

; It is perhaps a bit tempting to add a case for (hl-staticp x), and then
; proceed as in the consp case of hl-addr-of.  But if x is later garbage
; collected, then afterwards, each entry in the pons table created using this
; address is likely to be stale.  In fact, such treatment of static conses
; allowed the following book to be certified in ACL2(h) Versions 6.5 and 5.0
; (and quite possibly all versions inbetween and maybe some earlier).

;  (in-package "ACL2")
;
;  (defn foo (x y) (+ (len x) (nfix y)))
;
;  (memoize 'foo :recursive nil)
;
;  (value-triple (progn$ (foo (hons-copy '(a)) 0)
;                        (foo (hons-copy '(b)) 0)
;                        (foo (hons-copy '(c)) 0)
;                        (foo (hons-copy '(d)) 0)
;                        (hons-wash)
;                        nil))
;
;  (defthm mistake
;    (equal (foo (hons-copy '(a b)) 0)
;           1)
;    :hints (("Goal" :in-theory (e/d (foo (hons-copy))
;                                    (hons-copy))))
;    :rule-classes nil)
;
;  (defthm contradiction
;    nil
;    :hints (("Goal" :use mistake))
;    :rule-classes nil)

         nil)))


; [Jared] multithreading notes.  Pons tables must be shared hash tables.  There
; are no locks in the pons code, because we assume that the lock will be
; grabbed before we start ponsing.

#+static-hons
(defabbrev pons-addr-hash (x y)

; We try to compute the addresses of X and Y and hash them together.  If either
; doesn't have an address, we just return NIL.

  (let ((xaddr (pons-addr-of-argument x)))
    (if (not xaddr)
        nil
      (let ((yaddr (pons-addr-of-argument y)))
        (if (not yaddr)
            nil
          (hl-addr-combine* xaddr yaddr))))))

(defmacro incf-pons-calls ()
  '(safe-incf *pons-call-counter* 1))

(defmacro incf-pons-misses ()
  '(safe-incf *pons-misses-counter* 1))

(defun pons (x y ht)
  (declare (hash-table ht))

  #+static-hons
  (let ((addr (pons-addr-hash x y)))
    (when addr (return-from pons addr)))

  (incf-pons-calls)

  (let* ((flex-alist (gethash y ht))
         (entry      (hl-flex-assoc x flex-alist)))
    (cond
     (entry)
     (t
      (incf-pons-misses)
      (let* ((was-alistp (listp flex-alist))
             (new-cons

; It might be tempting to think about creating a static cons here.
; But in order to benefit from that, we would need to find a good way
; to use its index, perhaps in place of new-cons as a key of the pons
; table.  But in that case we would still need to hang on to that
; (static) cons so that it isn't garbage collected; so there is no
; obvious benefit to creating a static cons here, after all.

              (cons x y))
             (new-flex-alist (hl-flex-acons new-cons flex-alist)))

; Ctrl+C safety is subtle.  If was-alistp, then the above was applicative.  We
; now install the flex alist, which occurs as a single update to the hash
; table.

        (when was-alistp
          (setf (gethash y ht) new-flex-alist))

; Otherwise, the flex-acons was non-applicative and the table was already
; extended, so there's nothing more we need to do.

        new-cons)))))

(defmacro pist* (table &rest x)
  (cond ((atom x) x)
        ((atom (cdr x)) (car x))
        (t (list 'pons
                 (car x)
                 (cons 'pist* (cons table (cdr x)))
                 table))))

; SECTION: Identifying functions that are unsafe to memoize

(defun never-memoize-fn (fn)

; Warning: Keep the return values in sync for the logic and raw Lisp.

  (with-global-memoize-lock
    (setf (gethash fn *never-memoize-ht*) t))
  nil)

(defun never-memoize-p (fn)
  (with-global-memoize-lock
    (gethash fn *never-memoize-ht*)))

(defun initialize-never-memoize-ht ()

; Our goal is to avoid memoizing functions that support the implementation of
; memoization.  So we disallow functions defined in file hons-raw.lisp or in
; file memoize-raw.lisp, as well as built-ins Common Lisp functions.  This
; might not be a complete list, and it might even be too comprehensive; but it
; seems like a reasonable start.

  (let ((ht (memo-mht :test 'eq)))
    (note-fns-in-file "hons-raw.lisp" ht) ; its fns may be used in this file
    (note-fns-in-file "memoize-raw.lisp" ht)
    (flet ((update-nmht (fn)
                        (when (and (fboundp fn)
                                   (not (macro-function fn)))

; We only memoize functions, so we can restrict according to the test above.

                          (never-memoize-fn fn))))
      (maphash (lambda (key val)
                 (declare (ignore val))
                 (update-nmht key))
               ht)
      (loop for fn in *common-lisp-symbols-from-main-lisp-package*
            do
            (update-nmht fn))))
  nil)

; SECTION: Preliminary memoization support

(defrec memoize-info-ht-entry

; The *memoize-info-ht* associates memoized function symbols with these
; records.

; The fields are vaguely ordered by most frequently referenced first, but it's
; not clear that this is important for efficiency, except perhaps for
; ext-anc-attachments (see update-memo-entry-for-attachments).

  (ext-anc-attachments ; see the Essay on Memoization with Attachments

; Start-ticks is a symbol whose value is the start time (in float ticks) of the
; current, outermost call of fn, or -1 if no call of fn is in progress.

   start-ticks   ; see above
   num           ; an integer, unique to fn
   tablename     ; a symbol whose value is the memoize table for fn
   ponstablename ; a symbol whose value is the pons table for fn
   condition     ; :condition passed to memoize-fn (but nil for *nil*)
   inline        ; T or NIL :inline arg, as passed to memoize-fn
   memoized-fn   ; the new value of (symbol-function fn)
   old-fn        ; the old value of (symbol-function fn), or nil
   fn            ; a symbol, the name of the function being memoized
   sts           ; the stobj memo-table lists for fn

; Cl-defun is the function body actually used, in the inline=t case, as
; supplied (or as computed, if not supplied).

   cl-defun             ; see above
   formals              ; as supplied (or as computed, if not supplied)
   commutative          ; asserts this is a binary commutative function
   specials             ; hack for raw Lisp functions that read specials
   stobjs-in            ; as supplied (or as computed, if not supplied)
   stobjs-out           ; as supplied (or as computed, if not supplied)
   record-bytes         ; value as bound at the time MEMOIZE-FN is called
   record-calls         ;        ''
   record-hits          ;        ''
   record-mht-calls     ;        ''
   record-pons-calls    ;        ''
   record-time          ;        ''
   forget               ; Boolean, clears memo when outermost call exits
   memo-table-init-size ; integer, reasonable default of *mht-default-size*
   aokp                 ; use of attachments is allowed

; [Jared] multithreading notes: we could probably add a lock here that was only
; on a per-function basis.  That could help avoid needing the global lock, much
; of the time.

   )
  t)

(defmacro ma-index (col &optional (row 0) (2mmf '*2max-memoize-fns*))

; This function creates an index into the one-dimensional array,
; *memoize-call-array*.  That array is conceptually a two-dimensional array,
; and the arguments are a corresponding column and row of that 2D array.  If
; row is not supplied, then the index returned points to the start of the
; column (i.e., for a row of 0).

  (let ((col-base `(* ,2mmf
                      (the-mfixnum ,col))))
    (if (eql row 0)
        `(the-mfixnum ,col-base)
      `(ma-index-from-col-base ,col-base ,row))))

(defmacro ma-index-from-col-base (col-base row)

; This function creates an index into the one-dimensional array,
; *memoize-call-array*.  That array is conceptually a two-dimensional array,
; and the arguments are a corresponding column and row of that 2D array.
; Col-base is an index into *memoize-call-array* reprsenting the start of a
; column, and row represents a row of the 2D array.

  `(the-mfixnum (+ (the-mfixnum ,col-base)
                   (the-mfixnum ,row))))

(defmacro ma-index-calls (child &optional
                                (parent 0)
                                (2mmf '*2max-memoize-fns*))

; When parent calls child, we will make an entry in *memoize-call-array* for
; the "column" of parent at a "row" corresponding to child, where "column" and
; "row" are in quotes because while we think of *memoize-call-array* as a
; two-dimensional array, it actually has only one dimension.  This macro
; computes the index into *memoize-call-array* for that entry.  A special case
; is "column" 0 of *memoize-call-array*, which is used as scratch space by
; COMPUTE-CALLS-AND-TIMES for sums across all functions.  In that case there is
; no "parent" -- we are just accumulating all calls regardless of any notion of
; "parent".

  (let ((2child `(the-mfixnum (* 2 (the-mfixnum ,child)))))
    (if (eql parent 0)
        2child ; simplification of `(ma-index 0 ,2child ,2mmf)
      `(ma-index ,parent ,2child ,2mmf))))

(defmacro ma-index-ticks (child &optional
                               (parent 0)
                               (2mmf '*2max-memoize-fns*))

; This macro is similar to ma-index-calls, but it counts ticks instead of
; calls.  See comments in ma-index-calls.

  (let ((2child+1 `(the-mfixnum
                        (1+ (the-mfixnum (* 2 (the-mfixnum ,child)))))))
    (if (eql parent 0)
        2child+1 ; simplification of `(ma-index 0 ,2child+1 ,2mmf)
      `(ma-index ,parent ,2child+1 ,2mmf))))

(defun outside-caller-col-base ()

; See *caller*.  Notice that although we pass *initial-max-symbol-to-fixnum*
; explicitly below, the value also depends on the global *2max-memoize-fns*.

  (ma-index *initial-max-symbol-to-fixnum*))

(defg *caller*

; This variable represents the index into *memoize-call-array* that starts the
; layout of the "column" for the innermost memoized function call being
; evaluated (or, in the case of its initial value, the column for
; "outside-caller" = (gethash *initial-max-symbol-to-fixnum*
; *memoize-info-ht*).  The idea is to accumulate calls and ticks into that
; "column".

; When memoized functions are executing in parallel, the value of *caller* and
; of statistics derived therefrom may be meaningless and random.

  (let ((val (outside-caller-col-base)))
    (check-type val mfixnum)
    val))

(declaim (type mfixnum *caller*))

(defrec memo-max-sizes-entry

; This represents a single entry in the *memo-table-max-sizes* table.

  (num-clears   ; how many times has this table been cleared (nat)
   max-pt-size  ; maximum size of the pons table before any clear (nat)
   max-mt-size  ; maximum size of the memo table before any clear (nat)
   avg-pt-size  ; average size of the pons table before any clear (float)
   avg-mt-size  ; average size of the memo table before any clear (float)
   )
  t)

(defun make-initial-memoize-hash-table (fn init-size)

; Fn is the name of a function.  Init-size is the initial size that the user
; says we should use.  We want to create and return a new hash table for this
; function's memoization table.  One possible implementation of this function
; would just be:
;
;    (memo-mht :size init-size)
;
; But we hope to do better.  Our idea is to look at how large the table has
; been in the past, and use that size to make a good prediction of how large
; the table will be this time.
;
; The idea here is to build a table that's just slightly bigger than the
; average size we've seen so far.  We arbitrarily say that "slightly bigger"
; means 1.2x the previous average.
;
; By itself this would be scary.  Big hash tables can use a lot of memory;
; here we see in CCL that 1 MB of space can buy you about 53,000 entries:

;      ? [RAW LISP] (time (make-hash-table :size 53102))
;      (MAKE-HASH-TABLE :SIZE 53102)
;      took 606 microseconds (0.000606 seconds) to run.
;      During that period, and with 4 available CPU cores,
;           453 microseconds (0.000453 seconds) were spent in user mode
;           126 microseconds (0.000126 seconds) were spent in system mode
;       999,984 bytes of memory allocated.
;      #<HASH-TABLE :TEST EQL size 0/53102 #x30200276BDDD>
;      ? [RAW LISP]

; I want to avoid creating a hundred-megabyte memo tables for a function just
; because it was used heavily for a short while and then cleared once before.
; On the other hand, if a memo table truly does get large on a regular basis,
; then we do want to guess a big size for it.
;
; So in this code, I enforce an artificial maximum on our guess, but I allow
; this maximum to grow with the number of times we've cleared the table.
; Basically I allow the maximum guess to grow at a rate of 1 MB per clear.  If
; a table has been cleared 100 times, I think we have a pretty good sense of
; its average usage and we can be comfortable allocating up to 100 MB for it.
; If it's been cleared more than 1000 times, the cap is a gigabyte.  But of
; course, to actually reach such a large guess, you'd have to be repeatedly
; filling up the table to contain millions of entries and then clearing it.

  (with-global-memoize-lock
    (let* ((max-sizes ; previously recorded sizes of this table, if any exist
            (gethash fn *memo-max-sizes*))
           (size-to-use
            (if (not max-sizes)

; We never cleared this memoize table before, so we don't have anything to go
; on besides what the user says.  Do what they say.

                init-size
              (let* ((nclears       (access memo-max-sizes-entry max-sizes
                                            :num-clears))
                     (avg-mt-size   (access memo-max-sizes-entry max-sizes
                                            :avg-mt-size))
                     (our-guess     (ceiling (* 1.20 avg-mt-size)))
                     (capped-guess  (min our-guess (* nclears 44000)))
                     (final-guess   (max 60 init-size capped-guess)))
                final-guess))))
      (memo-mht :size size-to-use))))

(defun make-initial-memoize-pons-table (fn init-size)
  (declare (ignorable init-size))

; This is similar to make-initial-memoize-table, but for the pons table.

  (with-global-memoize-lock
    (let* ((max-sizes (gethash fn *memo-max-sizes*))
           (size-to-use
            (if (not max-sizes)

; We've never cleared this pons table before, so we don't have anything to go
; on besides what the user says.  Now, this is subtle.  Originally I just
; returned init-size here, i.e., "do what the user says."  But while this makes
; sense for the memo table, it doesn't necessarily make much sense for the pons
; table.  In particular, we can sometimes avoid ponsing by using our
; static-cons-index-hashing scheme.

; In some sense it would probably be good to give the user explicit control
; over the pons table size.  But for now, the main use of our memoize table
; size controls is to set things up for big BDD/AIG/SEXPR operations where
; we've got honsed data.  So, we just use *mht-default-size* here, which seems
; as reasonable a choice as any, say that the memo-table-init-size only affects
; the memoize table and not the initial pons table.

                *mht-default-size*
              (let* ((nclears       (access memo-max-sizes-entry max-sizes
                                            :num-clears))
                     (avg-pt-size   (access memo-max-sizes-entry max-sizes
                                            :avg-pt-size))
                     (our-guess     (ceiling (* 1.20 avg-pt-size)))
                     (capped-guess  (min our-guess (* nclears 44000)))
                     (final-guess   (max *mht-default-size*
                                         init-size
                                         capped-guess)))
                final-guess))))
      (memo-mht :size size-to-use))))

(defun update-memo-max-sizes (fn pt-size mt-size)

; Fn is a memoized function with a non-nil pons-table or memo-table, which is
; about to receive a new pons-table and memo-table of size pt-size and mt-size
; respectively (perhaps nil initially, in which case the size is 1).  We update
; the *memo-max-sizes* entry associated with f.

  (with-global-memoize-lock
    (let ((old (gethash fn *memo-max-sizes*)))
      (if (not old)
          (setf (gethash fn *memo-max-sizes*)
                (make memo-max-sizes-entry
                      :num-clears 1
                      :max-pt-size pt-size
                      :max-mt-size mt-size
                      :avg-pt-size (coerce pt-size 'float)
                      :avg-mt-size (coerce mt-size 'float)))
        (let* ((old.num-clears  (access memo-max-sizes-entry old :num-clears))
               (old.max-pt-size (access memo-max-sizes-entry old :max-pt-size))
               (old.max-mt-size (access memo-max-sizes-entry old :max-mt-size))
               (old.avg-pt-size (access memo-max-sizes-entry old :avg-pt-size))
               (old.avg-mt-size (access memo-max-sizes-entry old :avg-mt-size))
               (new.num-clears  (+ 1 old.num-clears)))
          (setf (gethash fn *memo-max-sizes*)
                (make memo-max-sizes-entry
                      :num-clears  new.num-clears
                      :max-pt-size (max pt-size old.max-pt-size)
                      :max-mt-size (max mt-size old.max-mt-size)
                      :avg-pt-size (/ (+ pt-size (* old.avg-pt-size
                                                    old.num-clears)) 
                                      new.num-clears)
                      :avg-mt-size (/ (+ mt-size (* old.avg-mt-size
                                                    old.num-clears))
                                      new.num-clears)))))))
  nil)

(defun print-memo-max-sizes ()

; Note (Matt K., 9/2014): This is just a printing function, probably rarely
; used, so I haven't really reviewed this code, though I did test it
; successfully.

  (with-global-memoize-lock
    (when (equal (hash-table-count *memo-max-sizes*) 0)
      (return-from print-memo-max-sizes nil))
    (format t "Memo table statistics gathered at each from when they were ~
             cleared:~%~%")
    (let ((indent 8) ; initial value of 8 is the length of "Function"
          indent-str)
      (maphash (lambda (fn entry)
                 (declare (ignore entry))
                 (setq indent (max indent (length (symbol-name fn)))))
               *memo-max-sizes*)
      (setq indent-str (format nil "~a" (+ 2 indent)))
      (format t (concatenate 'string "~" indent-str ":@a") "Function")
      (format t " ~10:@a | ~15:@a ~15:@a | ~15:@a ~15:@a~%"
              "Clears" "PT Max" "PT Avg" "MT Max" "MT Avg")
      (maphash
       (lambda (fn entry)
         (let* ((num-clears  (access memo-max-sizes-entry entry :num-clears))
                (max-pt-size (access memo-max-sizes-entry entry :max-pt-size))
                (max-mt-size (access memo-max-sizes-entry entry :max-mt-size))
                (avg-pt-size (access memo-max-sizes-entry entry :avg-pt-size))
                (avg-mt-size (access memo-max-sizes-entry entry :avg-mt-size)))
           (format t
                   (concatenate 'string "~" indent-str
                                ":@a ~10:D | ~15:D ~15:D | ~15:D ~15:D~%")
                   fn num-clears
                   max-pt-size (floor avg-pt-size)
                   max-mt-size (floor avg-mt-size))))
       *memo-max-sizes*)
      (format t "~%")))
  nil)

; Essay on Memoization Involving Stobjs

; We allow memoization of functions that take user-defined stobjs (not state)
; as arguments but do not return stobjs.  The key is the use of memoize-flush
; to "forget" all that was remembered for certain functions that use certain
; stobjs.  We must keep memoize-flush very fast in execution so as not to slow
; down stobj update or resize operations in general.  Indeed, memoize-flush may
; (according to tests run) incur essentially no cost (after Version_4.3) as
; long as no functions with stobj arguments are actually memoized.

; The following example shows why we disallow memoization of functions that
; return stobjs.  First, redefine memoize-table-chk by eliminating the branch
; that causes an error in the presence of stobj names in stobjs-out.  Then
; start up ACL2 and submit the forms below.  The problem is that we do not
; inhibit storing a result in the case that the stobj has changed from the time
; the function was called to the time the result is to be stored.

; (defstobj st fld)
; (defun foo (st)
;   (declare (xargs :stobjs st))
;   (let ((st (update-fld (cons (fld st) (fld st)) st)))
;     (mv (fld st) st)))
; (foo st) ; updates (fld st), returns (mv (nil) st)
; (memoize 'foo)
; (foo st) ; updates (fld st), returns (mv ((nil) nil) st)
; (foo st) ; no longer updates (fld st)
; (foo st) ; no longer updates (fld st)
; (fld st) ; still ((nil . nil). (nil . nil))

(defun-one-output empty-ht-p (x)
  (and (hash-table-p x)
       (eql 0 (hash-table-count (the hash-table x)))))

(defun memoize-flush1 (lst)

; Experiments showed that when lst is nil, it is faster to call this function
; than to inline its code into the body of memoize-flush.

; We "forget" all memoized values by clearing all necessary memoize tables; see
; the comment about memoize-flush in memoize-fn.  We leave the pons table alone
; in order to keep this flushing operation as fast as possible.  Note that the
; pons table merely stores keys to be looked up in the memo table, so there is
; no soundness issue, and in fact those pons table entries might remain useful;
; the cost is the space taken up by the pons tables.

  (with-global-memoize-lock
    (loop for sym in lst do
          (when (boundp (the symbol sym)) ; not sure if this test is needed
            (let ((old (symbol-value (the symbol sym))))
              (unless (or (null old)
                          (eql 0 (hash-table-count (the hash-table old))))
                (setf (symbol-value (the symbol sym)) nil)))))))

(defmacro memoize-flush (st)

; See memoize-flush1 for a relevant discussion.

  (and st
       (let ((s (st-lst st)))
         `(when ,s ; optimization
            (memoize-flush1 ,s)))))

#+ccl
(defmacro heap-bytes-allocated ()
  '(the-mfixnum (ccl::%heap-bytes-allocated)))

(defun sync-memoize-call-array ()

; Warning: Be careful if you call this function is from other than memoize-init
; or memoize-call-array-grow.  Think about whether it would be a mistake to do
; otherwise, especially while memoized functions are running.  In particular,
; this function sets *caller* to denote the "outside" caller.

; We assume that *2max-memoize-fns* is the intended length of
; *memoize-call-array* and *max-symbol-to-fixnum* is the maximum fixnum
; associated with a memoized function symbol.

; It should be rare that this function is called after its call by
; memoize-init, i.e., by a call from memoize-call-array-grow.  That is:
; memoize-call-array-grow should be rare.  This code historically often cleared
; *memoize-call-array* and *callers-array* in most cases when called by
; memoize-call-array-grow.  For simplicity, we make that be the case always,
; and cleary.

  (with-global-memoize-lock
    (let ((n1 (ma-index *2max-memoize-fns*))
          (n2 (1+ *max-symbol-to-fixnum*)))
      (declare (type (and fixnum mfixnum) n1 n2))
      (setq *memoize-call-array* (initial-memoize-call-array 1))
      (setq *callers-array* (make-array 0))
      (gc$)
      (setq *memoize-call-array* (initial-memoize-call-array n1))
      (setq *callers-array* (make-array n2 :initial-element nil))
      (setq *caller* (outside-caller-col-base)))))

(defun memoize-call-array-grow
  (&optional (2nmax (* 2 (ceiling (* 3/2 (/ *2max-memoize-fns* 2))))))

; In our own code we call this function with no arguments.  However, as of this
; writing, community book file centaur/memoize/old/profile-raw.lsp calls it
; with an argument.  The argument will become the new dimension of the
; (virtual) 2D square array, *memoize-call-array*.

  (with-global-memoize-lock
    (unless (integerp 2nmax)
      (error "(memoize-call-array-grow ~s).  Arg must be an integer."
             2nmax))
    (unless (evenp 2nmax)
      (error "(memoize-call-array-grow ~s).  Arg must be even." 2nmax))
    (unless (> 2nmax 100)
      (error "(memoize-call-array-grow ~s).  Arg must be > 100." 2nmax))
    (when (<= 2nmax *2max-memoize-fns*)
      (cw "; memoize-call-array-grow: *memoize-call-array* already big enough.~%")
      (return-from memoize-call-array-grow))
    (unless (<= (* 2nmax 2nmax) most-positive-mfixnum)
      (error "memoize-call-array-grow:  most-positive-mfixnum exceeded.  Too ~
            many memoized functions."))
    (unless (<= (* 2nmax 2nmax) most-positive-fixnum)
      (error "memoize-call-array-grow:  most-positive-fixnum exceeded.  Too ~
            many memoized functions."))
    (unless (< (* 2nmax 2nmax) array-total-size-limit)
      (error "memoize-call-array-grow: ARRAY-TOTAL-SIZE-LIMIT exceeded.  Too ~
            many memoized functions."))
    (unless (< (* 2nmax 2nmax) array-dimension-limit)
      (error "memoize-call-array-grow: ARRAY-DIMENSION-LIMIT exceeded.  Too ~
            many memoized functions."))
    (unless (eql *caller* (outside-caller-col-base))
      (cw "; MEMOIZE-CALL-ARRAY-GROW was called while a memoized function~%~
         ; was executing, so call reports may be quite inaccurate.~%"))
    (setq *2max-memoize-fns* 2nmax)
    (let ((state *the-live-state*))
      (observation 'sync-memoize-call-array
                   "Now reinitializing memoization structures.  This will erase ~
                  saved values and statistics."))
    (sync-memoize-call-array)
    (rememoize-all))
  nil)

(defun-one-output symbol-to-fixnum-create (s)

; We return the number n associated with function symbol s, in the sense that
; (gethash n *memoize-info-ht*) = s.  If no such number n yet exists, it is
; returned -- but this function does not actually add the association; that is
; done by its caller, memoize-fn.

  (check-type s symbol)
  (with-global-memoize-lock
    (let ((g (gethash s *memoize-info-ht*)))
      (if g
          (access memoize-info-ht-entry g :num)
        (let (new)
          (assert (eql *caller* (outside-caller-col-base))) ; sanity check
          (loop for i fixnum
                from (1+ *initial-max-symbol-to-fixnum*)
                below (the fixnum (floor *2max-memoize-fns* 2))
                do (unless (gethash i *memoize-info-ht*)
                     (setq new i)
                     (return)))
          (cond (new (setq *max-symbol-to-fixnum*
                           (max *max-symbol-to-fixnum* new))
                     new)
                (t (memoize-call-array-grow)
                   (safe-incf *max-symbol-to-fixnum* 1 symbol-to-fixnum-create)
                   *max-symbol-to-fixnum*)))))))

(defun-one-output symbol-to-fixnum (s)
  (check-type s symbol)
  (with-global-memoize-lock
    (let ((g (gethash s *memoize-info-ht*)))
      (if g
          (access memoize-info-ht-entry g :num)
        (error "(symbol-to-fixnum ~s).  Illegal symbol." s)))))

(defun-one-output fixnum-to-symbol (n)
  (check-type n fixnum)
  (with-global-memoize-lock
    (or (gethash n *memoize-info-ht*)
        (error "(fixnum-to-symbol ~s). Illegal number." n))))

(defun-one-output coerce-index (x)

; X is either a memoized function symbol or the associated number
; (symbol-to-fixnum, also column number in *memoize-call-array* and index in
; *callers-array*) of such.

  (cond ((typep x 'fixnum) ; equivalently, x is a number
         (assert (and (>= (the fixnum x) 0)
                      (< (the fixnum x)
                         (the fixnum (ash (length *memoize-call-array*)
                                          -1)))))
         x)
        (t ; could (assert (symbolp x)) but probably not worth the cycles
         (symbol-to-fixnum x))))

(defun-one-output hons-gentemp (root)
  (check-type root string)
  (loop
   (safe-incf *hons-gentemp-counter* 1 hons-gentemp)
   (let ((name (our-syntax
                (format nil "HONS-G-~s,~s" root *hons-gentemp-counter*))))
     (multiple-value-bind (sym status)
         (intern name (find-package "ACL2_INVISIBLE"))
       (if (null status) (return sym))))))

(defun-one-output st-lst (st)

; ST-LST returns a symbol whose value is a list in which are saved the
; names of the memoize tables that will be set to nil whenever the
; stobj st is changed.

  (check-type st symbol)
  (intern (our-syntax (format nil "HONS-S-~s,~s"
                              (package-name (symbol-package st))
                              (symbol-name st)))
          (find-package "ACL2_INVISIBLE")))

(defun-one-output mf-dcls (l)
     (loop for dec in l nconc
           (let ((temp
                  (if (consp dec)
                      (loop for d in (cdr dec) nconc
                            (if (and (consp d) (eq (car d) 'ignore))
                                nil ; ignorable is added in memoize-fn-def
                              (cons d nil))))))
             (if temp (cons (cons 'declare temp) nil)))))

(defun memoize-use-attachment-warning (fn at-fn)
  (when *memoize-use-attachment-warning-p*
    (let ((state *the-live-state*))
      (warning$ 'top-level "Attachment"
                "Although the function ~x0 is memoized, a result is not being ~
                 stored because ~@1.  Warnings such as this one, about not ~
                 storing results, will remain off for all functions for the ~
                 remainder of the session unless the variable ~x2 is set to a ~
                 non-nil value in raw Lisp."
                fn
                (mv-let (lookup-p at-fn)
                        (if (consp at-fn)

; Then at-fn is of the form (:lookup . f), where f was memoized with :aokp t
; and a saved value for f was used, as explained in the lookup-p case below.

                            (assert$ (eq (car at-fn) :lookup)
                                     (mv t (cdr at-fn)))
                          (mv nil at-fn))
                        (cond (lookup-p
                               (msg "a stored result was used from a call of ~
                                     memoized function ~x0, which may have ~
                                     been computed using attachments"
                                    at-fn))
                              (t
                               (msg "an attachment to function ~x0 was used ~
                                     during evaluation of one of its calls"
                                    at-fn))))
                '*memoize-use-attachment-warning-p*))
    (setq *memoize-use-attachment-warning-p* nil)))

(defun-one-output memoize-fn-suffix (str sym)
  (check-type str string)
  (check-type sym symbol)
  (let ((spkn (package-name (symbol-package sym)))
        (sn (symbol-name sym)))

; Sometimes we use our-syntax for calls like this, and sometimes we don't.
; It's not clear that it much matters, so we have tended to preserve what was
; true historically.

    (format nil "~s,~s,~s" str spkn sn)))

(defmacro mf-index (x &optional known-not-rational)
  (assert (symbolp x)) ; else we should use defabbrev here
  `(cond ,@(unless known-not-rational
             `(((typep ,x 'fixnum) ,x)))
         #+static-hons
         (t

; Since this function is only heuristic, it is sound to use the weak staticp
; check below, instead of using consp and hl-hspace-truly-static-honsp checks
; as we do in pons-addr-of-argument.  We are hopeful that this decision won't
; result in expensive needless misses when checking memoization tables, but
; perhaps more thought about that would be useful here.

          (hl-staticp ,x))))

(defun-one-output mis-ordered-commutative-args (x y)

; This "function" need not return the same value for every call on the same
; input argument list.  We use this function to create a suitable memoization
; table key, to decide whether to reorder x and y before calling pist* (see
; memoize-fn).  Such reordering is justified for an ACL2 function of two
; arguments that has been proven commutative, because such reordering causes no
; difference in the result that can be detected by the ACL2 logic.

; The basic idea is to create an "index" for each argument.  For static conses
; we use hl-staticp as the index; but some Lisps have no static conses.  Of
; course, it is always legal to return nil.  Perhaps in the future we will use
; machine addresses or some other technique for sorting the arguments.

; We order objects that are rational or have an index before objects that are
; neither.

  (cond
   ((eql x y) nil)
   (t (let ((idx (mf-index x)))
        (declare (type (or null fixnum) idx))
        (cond
         (idx
          (let ((idy (mf-index y)))
            (declare (type (or null fixnum) idy))
            (cond
             (idy (< (the fixnum idy)
                     (the fixnum idx)))
             ((rationalp y)
              (< y (the fixnum idx))))))
         ((rationalp x)
          (let ((idy (mf-index y)))
            (declare (type (or null fixnum) idy))
            (cond
             (idy (< (the fixnum idy)
                     x))
             ((rationalp y)
              (< y x)))))
         ((or (rationalp y)
              (mf-index y t))))))))

(defun memoize-look-up-def (fn cl-defun inline wrld)

; This function returns a definition (fn formals ...), that is, without the
; initial DEFUN.  It returns cl-defun unchanged (other than stripping off the
; car if it is DEFUN), unless cl-defun is :DEFAULT -- which won't happen when
; memoize is called in the ACL2 loop (search in the definition of add-trip for
; the form (assert$ cl-defun (memoize-fn (nth 1 tuple) ...)).  In that :DEFAULT
; case, a reasonable attempt is made to find a definition.

; In memoize-fn, we rely on the fact that when memoize-look-up-def is called
; with a non-nil value of inline and it returns without error, then it returns
; a non-nil definition (which is a true list).

  (cond ((eq cl-defun :default)
         (cond
          ((null inline) nil)
          ((not (fboundp fn))
           (error "MEMOIZE-LOOK-UP-DEF: ** ~a is undefined." fn))
          ((let ((def (cltl-def-from-name fn wrld)))
             (cond (def (assert (eq (car def) 'defun))
                        (cdr def)))))
          (t (memoize-look-up-def-raw fn nil))))
        ((eq (car cl-defun) 'defun)
         (cdr cl-defun))
        (t
         cl-defun)))

(defg *memoize-timing-bugs* 0)

(defmacro fix-ticks (ticks ctx)

; Warning: If you make this a function and add a declaim form first such as
;   (declaim (ftype (function (mfixnum t) (values mfixnum))
;                   fix-ticks))
; then in GCL, make sure that after the build, the symbol-plist shows the
; correct declaim information.  We have seen a version of GCL 2.6.12pre for
; which this was not the case, which apparently was the cause of an unexpected
; error.

  `(let ((ticks ,ticks)
         (ctx ,ctx))
     (declare (type mfixnum ticks))
     (the-mfixnum
      (cond ((and (<= 0 (the-mfixnum ticks))
                  (< (the-mfixnum ticks)
                     (the-mfixnum *10-days*)))
             (the-mfixnum ticks))
            (t
             (incf *memoize-timing-bugs*)
             (when (<= *memoize-timing-bugs* 10)
               (format t "Ignoring time increment of ~a sec for ~a~%"
                       (/ ticks *float-ticks/second*) ctx)
               (when (eql *memoize-timing-bugs* 10)
                 (format t "Timing is very dubious.  Suppressing further messages.~%")))
             0)))))

; SECTION: The main code for creating memoized function definitions:
; memoize-fn, unmemoize-fn, etc.

(defun-one-output memoizedp-raw (fn)
  (and (symbolp fn)
       (with-global-memoize-lock
         (values (gethash fn *memoize-info-ht*)))))

(defmacro mf-make-symbol (&rest r) ; for forming symbols in package ACL2
  `(our-syntax (intern (format nil ,@r) *acl2-package*)))

(defun memoize-fn-init (fn inline wrld &aux (state *the-live-state*))

; Do initial stuff for memoize-fn, including error checking.  Quite possibly
; only a few of the check below (if any) are necessary if memoize-fn is called
; by way of an invocation of memoize in the ACL2 loop.

  (with-global-memoize-lock

    (unless (symbolp fn)
      (error "Memoize-fn: ~s is not a symbol." fn))

    (maybe-untrace! fn) ; See the comment about Memoization in trace$-def.

    (unless *memoize-init-done*
      (error "Memoize-fn:  *MEMOIZE-INIT-DONE* is still nil."))

    (unless (fboundp fn)
      (error "Memoize-fn: ~s is not fboundp." fn))

    (when (or (macro-function fn)
              (special-operator-p fn)
              (and (fboundp 'compiler-macro-function) ; for GCL as of 5/2013
                   (compiler-macro-function fn)))
      (error "Memoize-fn: ~s is a macro or a special operator or has a compiler ~
            macro." fn))

    (when (never-memoize-p fn)
      (error "Memoize-fn: ~s must never be memoized" fn))

    (when (and inline
               (or (member-eq fn
                              (f-get-global 'logic-fns-with-raw-code state))
                   (member-eq fn
                              (f-get-global 'program-fns-with-raw-code state))))
      (error "Memoize-fn: ~s must never be memoized with :inline t,~%~
            because it belongs to the list stored in state global~%~
            variable ~s and thus runs code different~%~
            than that stored in the ACL2 logical world, as is typically~%~
            used when inserting inlined code for memoization."
             fn
             (if (member-eq fn
                            (f-get-global 'logic-fns-with-raw-code state))
                 'logic-fns-with-raw-code
               'program-fns-with-raw-code)))

    (when (memoizedp-raw fn)
      (observation 'memoize
                   "~s0 is currently memoized. We will first unmemoize it, then ~
                  memoize it again."
                   fn)
      (unmemoize-fn fn))

    (when (member fn (eval '(trace)))
      (observation 'memoize
                   "Untracing ~s before memoizing it."
                   fn)
      (eval `(untrace ,fn)))

; TRACE, UNTRACE, OLD-TRACE, and OLD-UNTRACE are macros that get
; redefined sometimes.  So we use EVAL in calling them.

    #+ccl
    (when (ccl::%advised-p fn)
      (error "~%; Memoize-fn: Please unadvise ~s before calling memoize-fn on ~
             it." fn))

    (when (and (fboundp 'old-trace)
               (member fn (eval '(old-trace))))
      (observation 'memoize
                   "Old-untracing ~s before memoizing it."
                   fn)
      (eval `(old-untrace ,fn)))

    (when (getprop fn 'constrainedp nil 'current-acl2-world wrld)
      (error "Memoize-fn: ~s is constrained; you may instead wish to memoize a ~
            caller or to memoize its attachment (see :DOC defattach)."
             fn))

    #+ccl
    (when (multiple-value-bind (req opt restp keys)
              (ccl::function-args (symbol-function fn))
            (or restp
                keys
                (not (integerp req))
                (not (eql opt 0))))

; This sanity check will never cause an error when memoization is invoked using
; memoize inside the ACL2 loop.

; CCL documentation returned by
; (documentation 'ccl::function-args 'function)
; justifies the four bound variables above.  The additional 5 values returned
; by ccl::function-args are discarded, as per the CL HyperSpec documentation of
; multiple-value-bind.

      (error "Memoize-fn: ~a has non-simple arguments." fn))))

(defun memoize-fn-init-2 (fn formals condition stobjs-in stobjs-out)

; Do more initial stuff for memoize-fn after formals is computed.

  (with-global-memoize-lock

    (unless (and (symbol-listp formals)
                 (no-duplicatesp formals)
                 (loop for x in formals never (constantp x)))

; This sanity check is unnecessary when memoization is invoked using memoize
; inside the ACL2 loop.

      (error "Memoize-fn: FORMALS, ~a, must be a true list of distinct, ~
            nonconstant symbols."
             formals))

    (when (intersection lambda-list-keywords formals)

; This sanity check is unnecessary when memoization is invoked using memoize
; inside the ACL2 loop.

      (error "Memoize-fn: FORMALS, ~a, may not intersect LAMBDA-LIST-KEYWORDS."
             formals))

    (when (and condition (or (member 'state stobjs-in)
                             (member 'state stobjs-out)))

; This sanity check is unnecessary when memoization is invoked using memoize
; inside the ACL2 loop, because in memoize-table-chk, we disallow state as a
; formal and we disallow every stobj as an output.

; Although we don't support memoization of functions involving state, we do
; allow user-defined stobjs as inputs, by laying down code in stobj-let-fn-raw
; and defstobj-field-fns-raw-defs to flush memo tables as necessary.  But there
; is no such accommodation for the ACL2 state.

      (error "Memoize-fn:  ~s uses STATE." fn))))

(defun memoize-fn-inner-body (fn condition body-call fn-col-base
                                 tablename localtablename
                                 ponstablename localponstablename
                                 memo-table-init-size
                                 formals specials stobjs-out number-of-args
                                 commutative aokp)

; This is the main part of the body of the function defined by memoize-fn.

; Comments saying "performance counting*" are intended to mark code that might
; best be ignored on a first reading.  A long comment in *memoize-call-array*
; outlines how performance counting is implemented.

;; [Jared] multithreading note: all of this is going to be protected with the
;; global lock, so we shouldn't need any locking inside here.  See
;; memoize-fn-def.

  (let ((mf-record-mht ; performance counting
         (and *record-mht-calls*
              `((safe-incf
                 (aref ,*mf-ma*
                       ,(ma-index-from-col-base fn-col-base *ma-mht-index*))
                 1))))
        (mf-record-hit ; performance counting
         (and *record-hits*
              condition ; never record hits when profiling
              `((safe-incf
                 (aref ,*mf-ma*
                       ,(ma-index-from-col-base fn-col-base *ma-hits-index*))
                 1)))))
    `(cond
      ((not ,condition)
       ,@(and *condition-nil-as-hit* ; see comment in definition of this var
              mf-record-hit)
       ,body-call)
      ,@(and
         condition ; else dead code
         `((t
            (let (,*mf-ans* ,*mf-args* ,*mf-ans-p*)
              (declare (ignorable ,*mf-ans* ,*mf-args* ,*mf-ans-p*))
              (when (null ,tablename) ; e.g., after (clear-memoize-tables)
                ,@mf-record-mht
                (setq ,tablename (make-initial-memoize-hash-table
                                  ',fn ,memo-table-init-size))
                ,@(and (> number-of-args 1)
                       `((setq ,ponstablename
                               (make-initial-memoize-pons-table
                                ',fn ,memo-table-init-size)))))
              (setq ,localtablename ,tablename)
              ,@(and (> number-of-args 1)
                     `((assert ,ponstablename)
                       (setq ,localponstablename ,ponstablename)))

; Generate the pons key.  If there is just one arg, pist* just returns the arg
; and doesn't do any ponsing.

              (setq ,*mf-args*
                    ,(cond
                      (commutative
                       `(cond ((mis-ordered-commutative-args
                                ,(car formals)
                                ,(cadr formals))
                               (pist* ,localponstablename
                                      ,(cadr formals)
                                      ,(car formals)
                                      ,@specials))
                              (t
                               (pist* ,localponstablename
                                      ,(car formals)
                                      ,(cadr formals)
                                      ,@specials))))
                      (t `(pist* ,localponstablename
                                 ,@formals
                                 ,@specials))))

; Attempt to find the saved result.

              (multiple-value-setq
               (,*mf-ans* ,*mf-ans-p*)
               ,(let ((gethash-form
                       `(gethash ,*mf-args*
                                 (the hash-table ,localtablename))))
                  (cond (aokp `(cond
                                (*aokp* ,gethash-form)
                                (t (values nil nil))))
                        (t gethash-form))))
              (cond
               (,*mf-ans-p*

; Memoized lookup succeeded.  Update performance counts and return result.

                ,@(and aokp

; We note that a saved value for fn was used, which may have dependent on an
; attachment since aokp is true.  See memoize-use-attachment-warning for how
; this special lookup-marker (:lookup . fn) is used.

                       `((update-attached-fn-called
                          ',(cons :lookup fn))))
                ,@mf-record-hit
                ,@(cond ((null (cdr stobjs-out))
                         `(,*mf-ans*))
                        (t

; The result stored in the memo table is of the form (list* x1 x2 ... xk),
; where k is the length of stobjs-out.  This result was stored when the
; returned value was (mv x1 x2 ... xk).  We build an expression (mv e1 e2
; ... ek), where each ei except the last is the result of popping the variable
; stored in *mf-ans*, i.e., #:ANS, leaving ek as that variable itself.

                         (let ((len-1 (1- (length stobjs-out))))
                           `(,(cons
                               'mv
                               (nconc (loop for i fixnum below len-1
                                            collect `(pop ,*mf-ans*))
                                      (list *mf-ans*))))))))
               (t

; Memoized lookup failed.  Now call the function and perhaps store what is
; returned by the call.

                ,(let* ((vars

; Vars is the list of variables (O0 O1 ... 0N) for the outputs, where N is the
; length of stobjs-out.  (We play it safe and use (O0) if somehow stobjs-out is
; nil.)

                         (loop for i fixnum below
                               (if (cdr stobjs-out)
                                   (length stobjs-out)
                                 1)
                               collect (mf-make-symbol "O~a" i)))
                        (prog1-fn (if (cdr stobjs-out)
                                      'multiple-value-prog1
                                    'prog1)))
                   `(let (,*attached-fn-temp*)
                      (mv?-let
                       ,vars
                       (let (*attached-fn-called*)
                         (,prog1-fn
                          ,body-call
                          (setq ,*attached-fn-temp* *attached-fn-called*)))
                       (progn
                         (cond
                          ,@(and (not aokp)
                                 `((,*attached-fn-temp*
                                    (memoize-use-attachment-warning
                                     ',fn
                                     ,*attached-fn-temp*))))
                          (t ; Save the results in the memo table.
                           (setf (gethash ,*mf-args*
                                          (the hash-table ,localtablename))
                                 (list* ,@vars))))
                         (when ,*attached-fn-temp* ; optimization
                           (update-attached-fn-called ,*attached-fn-temp*))
                         (mv? ,@vars))))))))))))))

(defun memoize-fn-outer-body (inner-body fn fn-col-base start-ticks forget
                                         number-of-args
                                         tablename ponstablename)

; The code returned below will be put in the context of outer-body in the code
; returned by memoize-fn-def.  It is a wrapper for inner-body, and it is used
; when the special variable symbol stored in start-ticks has a symbol-value of
; -1, indicating that we are looking at an outermost call of fn.  This
; mechanism avoids double-counting for recursive calls of fn.

; Comments about "performance counting" mark code that might best be ignored on
; a first reading.  A long comment in *memoize-call-array* outlines how
; performance counting is implemented.

; This code is what sets the special variable, *caller*, to the appropriate
; index for fn into *memoize-call-array* (namey fn-col-base, which points to
; the column for fn).  So, any immediately subsidiary calls of memoized
; functions will be "charged" to fn, and *caller* will only be re-assigned by
; subsidiary top-level calls of other memoized functions.

;; [Jared] multithreading note: all of this is going to be protected with the
;; global lock, so we shouldn't need any locking inside here.  See
;; memoize-fn-def.

  `(let ((,*mf-old-caller* *caller*)
         #+ccl
         ,@(and *record-bytes* ; performance counting
                `((,*mf-start-bytes* (heap-bytes-allocated))))
         ,@(and *record-pons-calls* ; performance counting
                `((,*mf-start-pons* *pons-call-counter*))))
     (declare
      (ignorable #+ccl
                 ,@(and *record-bytes* `(,*mf-start-bytes*))
                 ,@(and *record-pons-calls* `(,*mf-start-pons*)))
      (type mfixnum
            ,*mf-old-caller*
            ,@(and *record-pons-calls* `(,*mf-start-pons*))
            #+ccl
            ,@(and *record-bytes* `(,*mf-start-bytes*))))
     (unwind-protect-disable-interrupts-during-cleanup
      (progn (setq ,start-ticks  ,(if *record-time*
                                      '(internal-real-ticks)
                                    '0))
             (setq *caller* ,fn-col-base) ; performance counting
             ,inner-body)
      (setq *caller* ,*mf-old-caller*)
      ,@(and *record-pons-calls* ; performance counting
             `((safe-incf
                (aref ,*mf-ma*
                      ,(ma-index-from-col-base fn-col-base *ma-pons-index*))
                (the-mfixnum (- *pons-call-counter* ,*mf-start-pons*)))))
      #+ccl
      ,@(and *record-bytes* ; performance counting
             `((safe-incf
                (aref ,*mf-ma*
                      ,(ma-index-from-col-base fn-col-base *ma-bytes-index*))
                (the-mfixnum (- (heap-bytes-allocated) ,*mf-start-bytes*)))))
      ,@(and *record-time* ; performance counting
             `((safe-incf
                (the mfixnum
                     (aref ,*mf-ma* (the-mfixnum (1+ ,*mf-count-loc*))))
                (the-mfixnum
                 (fix-ticks (the-mfixnum (- (internal-real-ticks)
                                            ,start-ticks))
                            ',fn)))))
      ,@(and forget

; Below, we "clear" the tables by setting them to nil, rather than by calling
; clrhash.  The latter approach would probably avoid reallocation of space, but
; we suspect that such a gain in space efficiency might be offset by a loss in
; time efficiency.  The present approach has been working, so we prefer not to
; change it.  Below is just a little space analysis.

; Perhaps we should use clrhash below.  Here is the story:

; When we evaluated (defconstant *a* (make-list 1000)) in raw Lisp (CCL) and
; then ran (time$ (bad-lisp-objectp *a*)), we saw about 70K bytes allocated
; then and each additional time (time$ (bad-lisp-objectp *a*)) was evaluated,
; because the :forget argument (see *thread-unsafe-builtin-memoizations*, used
; in acl2h-init-memoizations) was blowing away hash tables -- see setq forms
; below.  After evaluating (unmemoize-fn 'bad-lisp-objectp), the bytes went to
; 0 per evaluation.  Then we evaluated (memoize-fn 'bad-lisp-objectp) -- this
; time without a :forget argument -- and found about 70K bytes allocated on the
; first timing of (bad-lisp-objectp *a*), but 0 bytes allocated on subsequent
; evaluations, presumably because we weren't starting from scratch.
; Interestingly, the byte allocation on subsequent runs was also 0 after
; memoizing with :forget t when we experimented by replacing the setq forms
; below by clrhash calls.  So perhaps we should consider oding that, to avoid
; generating garbage hash tables.

             `((setq ,tablename nil)
               ,@(and (> number-of-args 1)
                      `((setq ,ponstablename nil)))))
      (setq ,start-ticks -1))))

(defun memoize-fn-def (inner-body outer-body body body-name
                                  fn formals specials dcls fnn start-ticks
                                  localtablename localponstablename)

; Comments about "performance counting" mark code that might best be ignored on
; a first reading.  A long comment in *memoize-call-array* outlines how
; performance counting is implemented.

  `(defun ,fn ,formals ,@dcls
     (declare (ignorable ,@formals ,@specials))

     (with-global-memoize-lock ;; <--- [Jared]: protect ALL THE THINGS

       (let* ((,*mf-count-loc* ; performance counting
               ,(if (or *record-calls* *record-time*)

; The following expression is similar to `(ma-index-calls ,fnn *caller*),
; except that *caller* is already a column (that is, already multiplied by the
; square dimension of *memoize-call-array*).

                    `(the-mfixnum (+ *caller* ,(* 2 fnn)))
                  0))
              (,*mf-ma* *memoize-call-array*)
              ,localtablename ,localponstablename)
         (declare (type mfixnum ,*mf-count-loc*)
                  (ignorable ,*mf-count-loc* ,*mf-ma*
                             ,localponstablename
                             ,localtablename)
                  (type (simple-array mfixnum (*))
                        ,*mf-ma*))
         ,@(and *record-calls* ; performance counting
                `((safe-incf (aref ,*mf-ma* ,*mf-count-loc*) 1)))
         (flet ((,body-name () ,body))
           (if (eql -1 ,start-ticks)
               ,outer-body
             ,inner-body))))))

(defun-one-output memoize-eval-compile (def old-fn)
  #+(or ccl sbcl) ; all functions are compiled
  (declare (ignore old-fn))
  (unless (and (consp def)
               (eq 'defun (car def))
               (consp (cdr def))
               (symbolp (cadr def)))
    (error "MEMOIZE-EVAL-COMPILE:  Bad input:~%~s." def))
  #+(or ccl sbcl)
  (compile (eval def)) ; probably the compile is unnecessary but harmless
  #-(or ccl sbcl)
  (if (and old-fn (compiled-function-p old-fn))
      (compile (eval def))
    (eval def))
  nil)

(defun memoize-fn (fn &key
                      (condition t)
                      (inline t)
                      (cl-defun :default)
                      (formals :default)
                      (stobjs-in :default)
                      (specials nil)
                      (commutative nil)
                      (stobjs-out :default)
                      (forget nil)
                      (memo-table-init-size *mht-default-size*)
                      (aokp nil)
                      &aux (wrld (w *the-live-state*)))

; Warning: Keep the argument list for this function in sync with memoize-info,
; as explained  there.

; We do not claim that memoize-fn is bulletproof when called directly in raw
; Lisp, rather than via a call to memoize in the ACL2 loop.  However, make some
; effort for it to behave reasonably.

; If the :INLINE parameter T, then the body of FN is placed inline in the
; memoized definition; otherwise, a funcall of the original function is placed
; there.

; Comments about "performance counting" mark code that might best be ignored on
; a first reading.  A long comment in *memoize-call-array* outlines how
; performance counting is implemented.

; Old documentation, which may be updated soon and/or merged into the :doc:

  "The documentation for MEMOIZE-FN is very incomplete.  One may invoke
  (MEMOIZE-FN fn) on the name of a Common Lisp function FN from outside the
  ACL2 loop to get results of possible interest in terms of memoization
  activity and profiling information.  MEMOIZE-FN already has a dozen
  parameters.

  MEMOIZE-FN replaces the SYMBOL-FUNCTION for the symmbol FN with 'enhanced'
  raw Common Lisp code that, supposedly, does not affect the value returned by
  FN but may make some notes and may even obtain some return values by
  remembering them from a previous call.

  If the CONDITION parameter is not NIL or 'NIL, then whenever FN is called,
  and there is not as yet any value remembered for a call of FN on the given
  arguments, then if the evaluation of the CONDITION parameter (where the
  formals of FN are bound to its actuals) is not NIL or 'NIL, the values that
  are computed for FN on the given arguments will be saved under the given
  arguments.

  If the INLINE parameter is T, then when MEMOIZE-FN creates a new body for FN,
  we place the old body of FN within the new body, i.e., 'in line'.  However,
  if the INLINE parameter is NIL, then we place code that calls the existing
  SYMBOL-FUNCTION for FN within the new body.  One might well argue that our
  parity for the INLINE parameter to MEMOIZE-fn is backwards, but we don't
  think so.

  One may lie to MEMOIZE-FN to force the memoization of a function that has
  ACL2's state as an explicit parameter by using fraudulent FORMALS, STOBJS-IN,
  and STOBJS-OUT parameters to MEMOIZE-FN.

  If the COMMUTATIVE parameter is not NIL, then the two arguments may be
  swapped before further processing.  We hope/presume that ACL2 will have been
  used first to prove that commutativity.

  If the CL-DEFUN parameter is not NIL, we pretend that the current body of FN
  is that parameter, and similarly for FORMALS, STOBJS-IN, and STOBJS-OUT.

  If FN is a raw Common Lisp function and not an ACL2-approved function, it may
  make reference to a variable, say S, that has a SPECIAL binding, in which
  case one needs to consider what in the world the meaning is for memoizing
  such a function at all.  If S is a member of the SPECIALS parameter, then it
  is assumed that FN does not alter but only refers to S.  MEMOIZE-FN acts as
  though FN had S as an extra argument for purposes of memoization.

  If the FORGET parameter is not NIL, the pons and memo tables of FN are
  discarded at the end of every outermost call of FN."

  #-hons
  (return-from memoize-fn
               (progn (when (not (zerop *ld-level*))
                        (warning$ 'memoize nil
                                  "No change for function ~x0: Memoization ~
                                   requests are ignored in this ACL2 ~
                                   executable because it is not hons-enabled."
                                  fn))
                      fn))

  (with-global-memoize-lock
    ;; [Jared] this lock protects the operation of the memoize command, itself.
    ;; The memoized function separately has its own locking, see
    ;; memoize-fn-def.
    (when (equal condition *nil*)
      (setq condition nil))
    (with-warnings-suppressed ; e.g., might avoid redefinition warnings
      (memoize-fn-init fn inline wrld)
      (let* ((cl-defun (memoize-look-up-def fn cl-defun inline wrld))
             (formals
              (cond
               ((eq formals :default)
                (let ((formals (getprop fn 'formals t 'current-acl2-world wrld)))
                  (if (eq formals t)
                      (if (consp cl-defun)
                          (cadr cl-defun)
                        (let ((n (mf-len-inputs fn)))
                          (if n
                              (loop for i fixnum below n
                                    collect (mf-make-symbol "X~a" i))
                            (error *memoize-fn-signature-error* fn))))
                    formals)))
               (t formals)))
             (stobjs-in
              (if (eq stobjs-in :default)
                  (let ((s (getprop fn 'stobjs-in t 'current-acl2-world wrld)))
                    (if (eq s t)
                        (make-list (len formals)) ; assume no stobjs
                      s))
                stobjs-in))
             (stobjs-out
              (if (eq stobjs-out :default)
                  (let ((s

; Note that the never-memoize-p check made in memoize-fn-init guarantees that
; here, we are not taking the stobjs-out of functions in *stobjs-out-invalid*.

                         (getprop fn 'stobjs-out t 'current-acl2-world wrld)))
                    (if (eq s t)
                        (let ((n (mf-len-outputs fn)))
                          (cond (n (make-list n))
                                ((null condition)

; This case is impossible when memoization is invoked using memoize inside the
; ACL2 loop, so we do not need to expect perfection here.  Fortunately,
; stobjs-out is probably irrelevant when condition is nil; so we assume that a
; single non-stobj value is returned.

                                 (list nil))
                                (t (error *memoize-fn-signature-error* fn))))
                      s))
                stobjs-out)))
        (memoize-fn-init-2 fn formals condition stobjs-in stobjs-out)
        (setf (gethash fn *number-of-arguments-and-values-ht*)
              (cons (length stobjs-in) (length stobjs-out)))
        (let* ((fnn ; performance counting
                (symbol-to-fixnum-create fn))
               (fn-col-base ; performance counting
                (ma-index fnn))
               (old-fn (symbol-function fn))
               (body
                (progn
                  (assert old-fn)
                  (cond
                   (inline

; When memoize-look-up-def is called with a non-nil value of inline and it
; returns without error, then it returns a non-nil definition (which is a true
; list).

                     (assert (consp cl-defun)) 
                     (car (last cl-defun)))
                   (t `(funcall
                        #-gcl ,old-fn
                        #+gcl ',old-fn ; old-fn could be (lisp:lambda-block ...)
                        ,@formals)))))
               (body-name (make-symbol "BODY-NAME"))
               (body-call

; This call has no arguments, which is OK because a suitable closure is formed.
; For example, before memoizing a function (foo x) we can evaluate

;   (trace! (memoize-fn-def :native t 
;                           :entry t
;                           :exit (progn (pprint (car values)) t)))

; to find that the memoized definition of foo has this form:

;   (DEFUN FOO (X) ... (FLET ((#:BODY-NAME NIL (LIST X X))) ...))

                (list body-name))
               (dcls (mf-dcls (cddr (butlast cl-defun))))
               (start-ticks

; Submit a defg form and return the generated name:

                (let ((v (hons-gentemp
                          (memoize-fn-suffix "START-TICKS-" fn))))
                  (eval `(prog1 (defg ,v -1)
                           (declaim (type mfixnum ,v))))))
               (tablename

; Submit a defg form and return the generated name:

                (eval `(defg
                         ,(hons-gentemp (memoize-fn-suffix "MEMOIZE-HT-FOR-" fn))
                         nil)))
               (ponstablename

; Submit a defg form and returns the generated name:

                (eval `(defg
                         ,(hons-gentemp (memoize-fn-suffix "PONS-HT-FOR-" fn))
                         nil)))
               (localtablename (make-symbol "TABLENAME"))
               (localponstablename (make-symbol "PONSTABLENAME"))
               (sts

; Here we support memoize-flush, which keeps memoize tables coherent in the
; presence of user-defined stobjs.  For each (user-level) stobj input name, st,
; we collect up the variable (st-lst st), whose value is the list of names of
; memoize tables that need to be cleared whenever that stobj changes.  Below,
; we will push the present function's table name onto each of these lists.

; Ultimately, stobj updates are made by stobj primitives.  After the stobj
; primitive for stobj st makes an update, the memo table for a function f
; taking st as its nth argument (say) is no longer valid for saved calls of f
; for which the nth argument is st.  Because of congruent stobjs and abstract
; stobjs, that nth argument need not be st, and we believe that in principle,
; we could restrict flushing of memo table entries of f to those whose nth
; argument is eq to the stobj being updated (whether st, congruent to st, or an
; abstract stobj whose concrete stobj is congruent to st).  But for now we take
; the coarser approach, which has the advantage that we simply throw away the
; memo-table for f when flushing, leaving it to be garbage collected; see
; memoize-flush1.

                (and condition ; else no memo table usage, so skip flushing
                     (remove-duplicates-eq
                      (loop for st in (union stobjs-in stobjs-out)
                            when st
                            collect
                            (assert$
                             (not (eq st 'state)) ; see memoize-table-chk
                             (st-lst (congruent-stobj-rep

; In the case that st is an abstract stobj, we replace it with the
; corresponding concrete stobj before getting a canonical (congruent)
; representative; see the rather long comment just above that mentions
; "abstract" stobjs.

                                      (or (concrete-stobj st wrld)
                                          st)
                                      wrld)))))))
               (number-of-args

; This is the number of arguments.  Specials only matter for raw Lisp
; functions; see the notes above in memoize-fn.  Basically if the function
; reads from specials we want to count them as arguments.

                (+ (len formals) (len specials)))
               (inner-body
                (memoize-fn-inner-body
                 fn condition body-call fn-col-base
                 tablename localtablename ponstablename localponstablename
                 memo-table-init-size
                 formals specials stobjs-out number-of-args
                 commutative aokp))
               (outer-body
                (memoize-fn-outer-body
                 inner-body fn fn-col-base start-ticks forget number-of-args
                 tablename ponstablename))
               (def
                (memoize-fn-def
                 inner-body outer-body body body-name
                 fn formals specials dcls fnn start-ticks
                 localtablename localponstablename))
               (success nil))
          (unwind-protect
              (progn
                (let ((ma *memoize-call-array*))
                  (declare (type (simple-array mfixnum (*)) ma))
                  (loop for i of-type mfixnum ; performance counting
                        from fn-col-base      ; loop through this column
                        below
                        (ma-index-from-col-base fn-col-base *2max-memoize-fns*)
                        unless (eql (aref ma i) 0)
                        do (setf (aref ma i) 0)))
                (memoize-eval-compile def old-fn)
                (setf (gethash fn *memoize-info-ht*)
                      (make memoize-info-ht-entry
                            :ext-anc-attachments
                            (and aokp (ext-ancestors-attachments fn wrld))
                            :start-ticks start-ticks
                            :num fnn
                            :tablename tablename
                            :ponstablename ponstablename
                            :condition condition
                            :inline inline
                            :memoized-fn (symbol-function fn)
                            :old-fn old-fn
                            :fn fn
                            :sts sts
                            :cl-defun cl-defun
                            :formals formals
                            :commutative commutative
                            :specials specials
                            :stobjs-in stobjs-in
                            :stobjs-out stobjs-out
                            :record-bytes      *record-bytes*
                            :record-calls      *record-calls*
                            :record-hits       *record-hits*
                            :record-mht-calls  *record-mht-calls*
                            :record-pons-calls *record-pons-calls*
                            :record-time       *record-time*
                            :forget            forget
                            :memo-table-init-size memo-table-init-size
                            :aokp aokp))
                (setf (gethash fnn *memoize-info-ht*) fn)
                (and condition (loop for s in sts do
                                     (push tablename
                                           (symbol-value (the symbol s)))))
                (setq success t))
            (unless success
              (without-interrupts ; perhaps already the case in some Lisps
                (setf (symbol-function fn) old-fn)
                (remhash fn *memoize-info-ht*)
                (remhash fnn *memoize-info-ht*)
                (and condition
                     (loop for s in sts
                           when (eq tablename
                                    (car (symbol-value (the symbol s))))
                           do (pop (symbol-value (the symbol s)))))
                (setq fn nil) ; in case we decide not to cause an error
                (error "Memoize-fn:  Failed to memoize ~s." fn))))))))
    fn)

(defun-one-output unmemoize-fn (fn)

; Warning: Do not be tempted to remove the definition of the condition
; function.  If fn was memoized using the memoize macro in the ACL2 loop, then
; a non-trivial condition is a first-class ACL2 function.

  #-hons
  (return-from unmemoize-fn
               (progn (when (not (zerop *ld-level*))
                        (warning$ 'unmemoize nil
                                  "No change for function ~x0: Unmemoization ~
                                   requests are ignored in this ACL2 ~
                                   executable because it is not hons-enabled."
                                  fn))
                      fn))

  (with-global-memoize-lock
    (maybe-untrace! fn) ; See the comment about Memoization in trace$-def.
    (let ((rec (memoizedp-raw fn)))
      (unless rec ; expect rec=nil in the loop, else unmemoize is redundant
        (error "Unmemoize-fn: ~s is not memoized." fn))
      (let* ((num (the-mfixnum (access memoize-info-ht-entry rec
                                       :num)))
             (tablename (access memoize-info-ht-entry rec
                                :tablename))
             (ponstablename (access memoize-info-ht-entry rec
                                    :ponstablename))
             (sts (access memoize-info-ht-entry rec
                          :sts))
             (col-base (ma-index num))
             (saved-table (symbol-value (the symbol tablename)))
             (saved-ponstable (symbol-value (the symbol ponstablename)))
             (saved-fn-entry (gethash fn *memoize-info-ht*))
             (saved-num-entry (gethash num *memoize-info-ht*))
             (ma *memoize-call-array*)
             (success nil))
        (declare (type mfixnum num col-base)
                 (type (simple-array mfixnum (*)) ma))
        (unwind-protect
            (progn
              (format nil "unmemoizing ~s" fn)
              (let (#+ccl (ccl:*warn-if-redefine-kernel* nil))
                (let ((old-fn (access memoize-info-ht-entry rec :old-fn)))
                  (assert old-fn)
                  (setf (symbol-function (the symbol fn))
                        old-fn)))
              (loop for i of-type mfixnum
                    from col-base ; loop through col-base column
                    below (ma-index-from-col-base col-base *2max-memoize-fns*)
                    unless (eql (aref ma i) 0)
                    do (setf (aref ma i) 0))
              (remhash fn *memoize-info-ht*)
              (remhash num *memoize-info-ht*)
              (setf (symbol-value (the symbol tablename)) nil)
              (setf (symbol-value (the symbol ponstablename)) nil)
              (loop for s in sts do
                    (when (boundp s)
                      (setf (symbol-value (the symbol s))
                            (remove tablename (symbol-value (the symbol s))))))
              (setq success t))
          (unless success
            (without-interrupts ; perhaps already the case in some Lisps

; We don't restore *memoize-call-array*; those statistics are simply lost.

              (setf (symbol-value (the symbol tablename)) saved-table)
              (setf (symbol-value (the symbol ponstablename)) saved-ponstable)
              (setf (gethash fn *memoize-info-ht*) saved-fn-entry)
              (setf (gethash num *memoize-info-ht*) saved-num-entry)
              (loop for s in sts do
                    (when (boundp s)
                      (push tablename (symbol-value (the symbol s)))))))))))
  fn)

(defun-one-output maybe-unmemoize (fn)

; We rely on the normal undoing mechanism (for :ubt etc.) to take care of
; unmemoization.  However, as a courtesy to users who memoize using raw Lisp,
; we provide this interface for unmemoizing functions that might not be known
; to ACL2 (via the memoize-table) as being memoized.

  (with-global-memoize-lock
    (when (and (memoizedp-raw fn)
               (not (cdr (assoc-eq fn (table-alist 'memoize-table
                                                   (w *the-live-state*))))))
      (unmemoize-fn fn))))

(defun-one-output memoized-functions ()

; We return the names of all memoized functions as a list.

  (with-global-memoize-lock
    (let (ans)
      (maphash (lambda (fn info)
                 (declare (ignore info))
                 (when (symbolp fn)
                   (push fn ans)))
               *memoize-info-ht*)
      ans)))

(defun-one-output length-memoized-functions ()

; We return the number of currently memoized (or profiled) functions.  We
; subtract one for the outside-caller entry and divide by 2 since there are two
; entries for each memoized function: one for the function symbol and one that
; associates :num of that symbol's entry back to the symbol.

  (with-global-memoize-lock
    (values (floor (1- (hash-table-count (the hash-table *memoize-info-ht*)))
                   2))))

(defun-one-output unmemoize-all ()

; Unmemoize all currently memoized functions,including all profiled functions.

; Warning: This function does not deal with memoize-table.  ACL2 users should
; evaluate (clear-memo-table) instead of calling unmemoize-all directly.

; A warning to would-be code improvers.  It would be a bad idea to redefine
; unmemoize-all to maphash over *memoize-info-ht*, because of the ANSI rules
; restricting which hash table entries may be modified during a maphash.

  (loop for x in (memoized-functions) do (unmemoize-fn x)))

(defun-one-output memoize-info (k)

; Warning: Keep this in sync with memoize-fn and rememoize-all.

; We return the settings of the various arguments to memoize-fn and the
; settings of the special variables that influence memoize-fn during the
; memoization of the given function symbol.  The rather arcane structure
; returned is used in rememoize-all.

  (with-global-memoize-lock
    (let ((v (gethash k *memoize-info-ht*)))
      (and v
           (list

; Warning: Keep the following list in sync with the argument list for
; memoize-fn.  Also note that the :fn must be first; see rememoize-all.

            (list (access memoize-info-ht-entry v :fn)
                  :condition
                  (access memoize-info-ht-entry v :condition)
                  :inline
                  (access memoize-info-ht-entry v :inline)
                  :cl-defun
                  (access memoize-info-ht-entry v :cl-defun)
                  :formals
                  (access memoize-info-ht-entry v :formals)
                  :stobjs-in
                  (access memoize-info-ht-entry v :stobjs-in)
                  :specials
                  (access memoize-info-ht-entry v :specials)
                  :commutative
                  (access memoize-info-ht-entry v :commutative)
                  :stobjs-out
                  (access memoize-info-ht-entry v :stobjs-out)
                  :forget
                  (access memoize-info-ht-entry v :forget)
                  :memo-table-init-size
                  (access memoize-info-ht-entry v :memo-table-init-size)
                  :aokp
                  (access memoize-info-ht-entry v :aokp))

; Warning: Keep the following list in sync with the set of *record-xxx*
; globals, and with rememoize-all.

            (list (access memoize-info-ht-entry v :record-bytes)
                  (access memoize-info-ht-entry v :record-calls)
                  (access memoize-info-ht-entry v :record-hits)
                  (access memoize-info-ht-entry v :record-mht-calls)
                  (access memoize-info-ht-entry v :record-pons-calls)
                  (access memoize-info-ht-entry v :record-time)))))))

(defun-one-output rememoize-all ()

; Warning: Keep this function in sync with memoize-info.

  (with-global-memoize-lock
    (let (lst)
      (maphash (lambda (k v)
                 (declare (ignore v))
                 (when (symbolp k)
                   (push (memoize-info k) lst)))
               *memoize-info-ht*)

; Note: memoize-info arranges that (caar x) is the memoized function symbol.

      (loop for x in lst do (unmemoize-fn (caar x)))
      (gc$)
      (setq *max-symbol-to-fixnum* *initial-max-symbol-to-fixnum*)
      (loop for x in lst do

; Warning: Keep the first argument below in sync with memoize-info.

            (progv '(*record-bytes*
                     *record-calls*
                     *record-hits*
                     *record-mht-calls*
                     *record-pons-calls*
                     *record-time*)
                (cadr x)
              (apply 'memoize-fn (car x)))))))

(defun profile-fn (fn &rest r &key (condition nil) (inline nil)
                      &allow-other-keys)

; Note that :condition and :inline are laid down twice in the call of
; memoize-fn below: once explicitly and once in r.  There is no error in such
; repetition, as Section 3.4.1.4 ("Specifiers for keyword parameters") of the
; Common Lisp Hyperspec says: "If more than one such argument pair matches, the
; leftmost argument pair is used."  By including the :condition and :inline
; arguments explicitly below, which are specified in the argument list as nil,
; we guarantee that the resulting function is profiled and executes its
; original body.

  (apply #'memoize-fn fn
         :condition condition
         :inline inline
         r))

(defun-one-output profiled-functions ()

; For purposes of this function, the profiled functions are defined as those
; produced by memoize-fn with null :condition and :inline fields.  We could
; probably allow :inline to be non-nil, but it will always be nil for functions
; profiled using profile-fn in raw Lisp or profile in the loop, so we enforce a
; nil value for :inline, not just :condition.

  (with-global-memoize-lock
    (let (lst)
      (maphash (lambda (k v)
                 (when (and (symbolp k)
                            (null (access memoize-info-ht-entry v :condition))
                            (null (access memoize-info-ht-entry v :inline)))
                   (push k lst)))
               *memoize-info-ht*)
      lst)))

(defun-one-output unmemoize-profiled ()

; This raw Lisp function unmemoizes (and hence unprofiles) all functions
; currently memoized with :condition nil and :inline nil.

  (loop for x in (profiled-functions) do
        (unmemoize-fn (car x))))

; SECTION: Statistics gathering and printing routines

(defun-one-output mf-num-to-string (n) ; for forming numbers

; Consider invoking this function in the context of our-syntax.

  (check-type n number)
  (if (= n 0) (setq n 0))
  (cond ((typep n '(integer -99 999))
         (format nil "~8d" n))
        ((or (< -1000 n -1/100)
             (< 1/100 n 1000))
         (format nil "~8,2f" n))
        (t (format nil "~8,2e" n))))

(defun mf-shorten (x n)

; Consider invoking this function in the context of our-syntax.

; Unless x is a string of length at most n, return a string that represents x,
; truncated to the first n characters, and associate x with that string in
; *mf-shorten-ht* (if there is not already such association).

  (cond ((and (stringp x) (<= (length x) n))
         x)
        (t
         (let ((x (if (stringp x)
                      (hons-copy x)
                    x)))
           ;; [Jared] I think there's no need to protect this hash table
           ;; because of the way it's used.
           (cond ((gethash x *mf-shorten-ht*))
                 (t (let ((*print-pretty* nil)
                          (*print-length* 10)
                          (*print-level* 5)
                          (*print-lines* 2))
                      (let ((str
                             (with-output-to-string
                               (s)
                               (cond ((stringp x) (princ x s))
                                     (t (prin1 x s))))))
                        (setf (gethash x *mf-shorten-ht*)
                              (cond ((<= (length str) n) str)
                                    (t (concatenate
                                        'string
                                        (subseq str 0 (max 0 n))
                                        "..."))))))))))))

(defun-one-output mf-print-alist (alist separation)

; Consider invoking this function in the context of our-syntax.

  (check-type separation (integer 0))
  (setq alist
        (loop for x in alist collect
              (progn

; Avoid a bug in GCL 2.6.10 (and perhaps some earlier versions?).

                (when #+gcl (gcl-version->= 2 6 11)
                      #-gcl t
                      (check-type x
                                  (cons (or string symbol)
                                        (cons (or string (integer 0))
                                              null))))
                (list (mf-shorten (car x) *mf-print-alist-width*)
                      (if (integerp (cadr x))
                          (mf-num-to-string (cadr x))
                        (cadr x))))))
  (let* ((max1 (loop for x in alist maximize (length (car x))))
         (max2 (loop for x in alist maximize (length (cadr x))))
         (width (max (or *print-right-margin*
                         *mf-print-right-margin*)
                     (+ separation max1 max2))))
    (loop for x in alist do
          (fresh-line)
          (princ (car x))
          (loop for i
                below (- width (+ (length (car x))
                                  (length (cadr x))))
                do (write-char #\Space))
          (princ (cadr x))))
  nil)

(defmacro safe-incf-pons (x inc)

; This function was originally called very-unsafe-incf, and as its name
; implied, it was defined to increment x by inc without checking that the
; result is of mfixnum type.  We are guessing that the cost of being safe is
; small, so we are renaming this function as safe-incf-pons, since it has only
; been used for reporting statistics related to pons.  It would certainly be
; fine to eliminate this extra layer altogether once we are confident that it
; causes only negligible slowdown in statistics reporting.

  `(safe-incf ,x ,inc))

(defun-one-output pons-summary ()

; Note: This function should probably either be made available in the loop or
; else eliminated.

; This function is not called anywhere else in the ACL2 sources, nor is it
; available from the loop.  Perhaps though it could be useful in tuning the
; implementation.

  (our-syntax
   (let ((sssub 0)       ; sum of sizes of subtables
         (nponses 0)     ; number of ponses
         (nsubs 0)       ; number of subsidiary hash tables (in flex alists)
         (nponstab 0))   ; number of pons tables
     (declare (type mfixnum sssub nponses nsubs))
     (format t "Pons-summary:~%")
     (with-global-memoize-lock
       (maphash
        (lambda (k v)
          (when (symbolp k)
            (let ((tab (symbol-value (access memoize-info-ht-entry v
                                             :ponstablename))))
              (when tab
                (safe-incf-pons nponstab 1)
                (maphash
                 (lambda (k v)
                   (declare (ignore k))
                   (cond
                    ((not (listp v)) ; the flex-alist v is a hash table
                     (safe-incf-pons sssub (hash-table-size (the hash-table v)))
                     (safe-incf-pons nponses
                                     (hash-table-count (the hash-table v)))
                     (safe-incf-pons nsubs 1))
                    (t (safe-incf-pons nponses (length v)))))
                 tab)))))
        *memoize-info-ht*))
     (mf-print-alist
      `((" Pons hits/calls"
         ,(let* ((c *pons-call-counter*)
                 (m *pons-misses-counter*)
                 (h (- c m)))
            (format nil "~,1e / ~,1e = ~,2f" h c (if (eql c 0) 0 (/ h c)))))
        (" Number of pons tables" ,(mf-num-to-string nponstab))
        (" Number of pons sub tables" ,(mf-num-to-string nsubs))
        (" Sum of pons sub table sizes" ,(mf-num-to-string sssub))
        (" Number of ponses" ,(mf-num-to-string nponses)))
      5)
     (format t ")")
     (force-output *standard-output*)
     nil)))

(defun memoized-values (&optional (fn (memoized-functions)))

; Note: This function should probably either be made available in the loop or
; else eliminated.

; We print all the currently memoized values for the given function symbol or
; list of function symbols, which by default is the list of all memoized
; function symbols.

  (with-global-memoize-lock
    (cond ((listp fn) (mapc #'memoized-values fn))
          ((not (memoizedp-raw fn))
           (format t "~%; Memoized-values:  ~s is not memoized." fn))
          (t (let ((tb (symbol-value
                        (access memoize-info-ht-entry
                                (gethash fn *memoize-info-ht*)
                                :tablename))))
               (cond ((and tb (not (eql 0 (hash-table-count
                                           (the hash-table tb)))))
                      (format t "~%; Memoized values for ~s." fn)
                      (maphash (lambda (key v)
                                 (format t "~%~s~%=>~%~s" key v))
                               (the hash-table tb))))))))
  (force-output *standard-output*)
  nil)

(defun print-call-stack ()

; Note: This function should probably either be made available in the loop or
; else eliminated.

; (Print-call-stack) prints the stack of memoized function calls currently
; running and the time they have been running.

  (float-ticks/second-init)
  (our-syntax
   (let (lst
         (ticks (internal-real-ticks))
         (*print-case* :downcase))
     (with-global-memoize-lock
       (maphash (lambda (k v)
                  (when (symbolp k)
                    (let ((x (symbol-value (the symbol
                                             (access memoize-info-ht-entry
                                                     v :start-ticks)))))
                      (declare (type mfixnum x))
                      (when (> x 0) ; in particular, on the stack (x not -1)
                        (push (cons k x) lst)))))
                *memoize-info-ht*))
     (setq lst (sort lst #'< :key #'cdr))
     (setq lst (loop for pair in lst collect
                     (list (car pair)
                           (mf-num-to-string (/ (the-mfixnum
                                                     (- ticks (cdr pair)))
                                                *float-ticks/second*)))))
     (when lst
       (terpri *standard-output*)
       (mf-print-alist
        (cons '("Stack of monitored function calls."
                "Time since outermost call.")
              lst)
        5))))
  (force-output *standard-output*)
  nil)

(defun-one-output pons-calls (x)

; This function symbol can be included in *memoize-summary-order-list*.

; For a memoized function x, (pons-calls x) is the number of times that x has
; called pons.

  (setq x (coerce-index x))
  (aref *memoize-call-array*
        (ma-index x *ma-pons-index*)))

#+ccl
(defun-one-output bytes-allocated (x)

; This function symbol can be included in *memoize-summary-order-list*.

; For a memoized function x, (bytes-allocated x) is the number of
; heap bytes x has caused to be allocated on the heap.

  (setq x (coerce-index x))
  (aref *memoize-call-array*
        (ma-index x *ma-bytes-index*)))

(defun-one-output number-of-hits (x)

; This function symbol can be included in *memoize-summary-order-list*.

; For a memoized function x, (number-of-hits x) is the number of
; times that a call of x returned a remembered answer.

  (setq x (coerce-index x))
  (aref *memoize-call-array*
        (ma-index x *ma-hits-index*)))

(defun-one-output number-of-memoized-entries (x)

; This function symbol can be included in *memoize-summary-order-list*.

; For a memoized function x, (number-of-memoized-entries x) is the number of
; entries currently stored for x."

  (setq x (coerce-index x))
  (with-global-memoize-lock
    (let ((h (gethash x *memoize-info-ht*)))
      (unless h (error "~a is not memoized." x))
      (let* ((sym (access memoize-info-ht-entry
                          h
                          :tablename))
             (val (symbol-value sym)))
        (if (hash-table-p val) ; note: val is nil after clear-memoize-table
            (hash-table-count (the hash-table val))
          0)))))

(defun-one-output number-of-mht-calls (x)

; This function symbol can be included in *memoize-summary-order-list*.

; For a memoized function x, (number-of-mht-calls x) is the number
; of times that the memoize hash-table for x was created.

  (setq x (coerce-index x))
  (aref *memoize-call-array*
        (ma-index x *ma-mht-index*)))

(defun-one-output total-time (x)

; This function symbol can be included in *memoize-summary-order-list*.

; For a memoized function x, (total-time x) is the total time spent inside
; (all outermost) calls of x.

; One must first call compute-calls-and-times to get sensible results.

  (setq x (coerce-index x))
  (float-ticks/second-init)
  (/ (aref *memoize-call-array* (ma-index-ticks x))
     *float-ticks/second*))

(defun-one-output number-of-calls (x)

; This function symbol can be included in *memoize-summary-order-list*.

; For a memoized function x, (number-of-calls x) is the total number of calls
; of x.

; One must first call compute-calls-and-times to get sensible results.

  (setq x (coerce-index x))
  (aref *memoize-call-array*
        (ma-index-calls x)))

(defun-one-output time-for-non-hits/call (x)

; This function symbol can be included in *memoize-summary-order-list*.

; One must first call compute-calls-and-times to get sensible results.

  (setq x (coerce-index x))
  (let ((n (- (number-of-calls x) (number-of-hits x))))
    (if (zerop n) 0 (/ (total-time x) n))))

(defun-one-output time/call (x)

; This function symbol can be included in *memoize-summary-order-list*.

; One must first call compute-calls-and-times to get sensible results.

  (setq x (coerce-index x))
  (let ((n (number-of-calls x)))
    (if (zerop n) 0 (/ (total-time x) n))))

(defun-one-output hits/calls (x)

; This function symbol can be included in *memoize-summary-order-list*.

; One must first call compute-calls-and-times to get sensible results.

  (setq x (coerce-index x))
  (let ((n (number-of-calls x)))
    (if (zerop n)
        0
      (/ (number-of-hits x)

; Why (float n) instead of n?  We see no clear reason, but we leave this
; historical call of float in place.

         (float n)))))

#+ccl
(defun-one-output bytes-allocated/call (x)

; This function symbol can be included in *memoize-summary-order-list*.

; One must first call compute-calls-and-times to get sensible results.

  (setq x (coerce-index x))
  (let ((n (number-of-calls x)))
    (if (zerop n) 0 (/ (bytes-allocated x) n))))

(defun char-list-fraction (l)
  (if (atom l)
      0
    (+ (char-code (car l))
       (/ (char-list-fraction (cdr l))
          256))))

(defun symbol-name-order (s)

; Symbol-name-order maps symbols to rationals preserving lexicographic order.

; This function symbol can be included in *memoize-summary-order-list*.

  (unless (symbolp s) (setq s (fixnum-to-symbol s)))
  (- (char-list-fraction (coerce (symbol-name s) 'list))))

(defun-one-output execution-order (s)

; This function symbol can be included in *memoize-summary-order-list*.

  (with-global-memoize-lock
    (unless (symbolp s) (setq s (fixnum-to-symbol s)))
    (the-mfixnum (symbol-value
                  (the symbol
                    (access memoize-info-ht-entry
                            (gethash s *memoize-info-ht*)
                            :start-ticks))))))

(defun compute-calls-and-times ()

  (with-global-memoize-lock
    (let ((ma *memoize-call-array*)
          (2m *2max-memoize-fns*)
          (ca *callers-array*)
          (n ; fixnum, because *max-symbol-to-fixnum* <= 1/2 *2max-memoize-fns*
           (the fixnum (1+ *max-symbol-to-fixnum*))))
      (declare (type (simple-array mfixnum (*)) ma)
               (type (simple-array t (*)) ca)
               (type fixnum 2m n))
      (cond ((eql (length ca) n)
             (loop for i fixnum below n
                   do (setf (aref ca i) nil)))
            (t (setq *callers-array* (make-array n :initial-element nil))
               (setq ca *callers-array*)))
      (loop for i fixnum below (ma-index-calls n 0 2m)

; fixnum, because (ma-index-calls n 0 2m) = 2n <= *2max-memoize-fns*

; Initialize column 0 of *memoize-call-array* to set to 0, for each i < n, both
; (ma-index-calls i 0 2m) and (ma-index-ticks i 0 2m).

            do (setf (aref ma i) 0))
      (loop for i fixnum ; column, for caller
            from *initial-max-symbol-to-fixnum*
            to *max-symbol-to-fixnum* ; indeed a fixnum; see comments above
            do
            (let ((col-base (ma-index i 0 2m)))
              (declare (type mfixnum col-base))
              (loop for j fixnum ; row
                    from *initial-max-symbol-to-fixnum*
                    to *max-symbol-to-fixnum* ; indeed a fixnum; see above
                    do
                    (let* ((calls-row (ma-index-calls j))
                           (index (ma-index-from-col-base col-base calls-row))
                           (calls (the-mfixnum (aref ma index))))
                      (declare (type mfixnum calls-row index calls))
                      (when (> calls 0)
                        (let* ((ticks-index

; The index for ticks is (ma-index-from-col-base col-base (ma-index-ticks j)).
; But that is just (1+ index), so we use the latter, more efficient form.

                                (the-mfixnum (1+ index)))
                               (ticks (aref ma ticks-index))
                               (ticks-row ; (ma-index-ticks j)
                                (the-mfixnum (1+ calls-row))))
                          (declare (type mfixnum ticks-index ticks ticks-row))
                          (safe-incf (aref ma calls-row)
                                     calls
                                     compute-calls-and-times)
                          (safe-incf (aref ma ticks-row)
                                     ticks
                                     compute-calls-and-times)
                          (push i ; Add i to the callers of j.
                                (aref ca j)))))))))))

(defun-one-output print-not-called ()

; Note: This function should probably either be made available in the loop or
; else eliminated.

; (Print-not-called) prints, one to a line, in alphabetic order, the currently
; memoized functions that have never been called.  This utility may be useful
; when looking for test coverage.

  (compute-calls-and-times)
  (let ((ans nil))
    (with-global-memoize-lock
      (maphash (lambda (k v)
                 (declare (ignore v))
                 (when (and (symbolp k)
                            (eql 0 (number-of-calls k)))
                   (push k ans)))
               *memoize-info-ht*))
    (loop for x in (sort ans 'alphorder)
          do (print x))))

(defun-one-output memoize-summary-sort ()
  (labels
   ((lex-> (l1 l2)
           (cond ((or (atom l1)
                      (atom l2))
                  nil)
                 ((> (car l1) (car l2)) t)
                 ((< (car l1) (car l2)) nil)
                 (t (lex-> (cdr l1) (cdr l2))))))
   (let (pairs)
     (with-global-memoize-lock
       (maphash
        (lambda (fn v)
          (when (symbolp fn)
            (let ((num (access memoize-info-ht-entry v :num)))
              (declare (type mfixnum num))
              (when (< 0 (number-of-calls num))
                (push (cons fn (loop for order
                                     in *memoize-summary-order-list*
                                     collect (funcall order fn)))
                      pairs)))))
        *memoize-info-ht*))
     (sort pairs
           (if *memoize-summary-order-reversed*
               (lambda (x y) (lex-> y x))
             #'lex->)
           :key #'cdr))))

(defun-one-output outside-caller-p (x)
  (with-global-memoize-lock
    (or (<= x *initial-max-symbol-to-fixnum*)
        (null (gethash x *memoize-info-ht*)))))

(defun-one-output memoize-condition (fn)
  (with-global-memoize-lock
    (let ((x (gethash fn *memoize-info-ht*)))
      (and x
           (access memoize-info-ht-entry x :condition)))))

(defun-one-output memoize-summary-after-compute-calls-and-times ()

; One must first call compute-calls-and-times to get sensible results.

  (with-global-memoize-lock

    (float-ticks/second-init)
    (our-syntax
     (let* ((fn-pairs (memoize-summary-sort))
            (ma *memoize-call-array*)
            (len-orig-fn-pairs (len fn-pairs))
            (len-fn-pairs 0)    ; set below
            (global-total-time 0) ; set below
            #+ccl
            (global-bytes-allocated 0) ; set below
            (global-pons-calls 0)      ; set below
            )
       (declare (type (simple-array mfixnum (*)) ma)
                (type fixnum len-orig-fn-pairs len-fn-pairs))
       (when (and *memoize-summary-limit*
                  (> len-orig-fn-pairs *memoize-summary-limit*))
         (setq fn-pairs (take *memoize-summary-limit* fn-pairs)))
       (setq len-fn-pairs (len fn-pairs))
       (when (> len-fn-pairs 0)
         (format t
                 "~%Sorted by *memoize-summary-order-list* = ~s."
                 *memoize-summary-order-list*)
         (when (< len-fn-pairs len-orig-fn-pairs)
           (format t
                   "~%Reporting on ~:d of ~:d functions because ~
                 *memoize-summary-limit* = ~a."
                   len-fn-pairs
                   len-orig-fn-pairs
                   *memoize-summary-limit*)))
       (setq global-total-time
             (loop for pair in fn-pairs sum (total-time (car pair))))
       #+ccl
       (setq global-bytes-allocated
             (loop for pair in fn-pairs sum
                   (bytes-allocated (car pair))))
       (setq global-pons-calls
             (loop for pair in fn-pairs sum (pons-calls (car pair))))
       (when (null fn-pairs)
         (format t "~%(memoize-summary) has nothing to report.~%"))
       (loop for pair in fn-pairs do
             (let* ((fn (car pair))
                    (entry (gethash fn *memoize-info-ht*))
                    (tablename
                     (symbol-value
                      (access memoize-info-ht-entry entry :tablename)))
                    (ponstablename
                     (symbol-value
                      (access memoize-info-ht-entry entry :ponstablename)))
                    (start-ticks
                     (the-mfixnum
                      (symbol-value
                       (the symbol
                         (access memoize-info-ht-entry entry
                                 :start-ticks)))))
                    (num (the-mfixnum (access memoize-info-ht-entry entry
                                              :num)))
                    (nhits (the-mfixnum (number-of-hits num)))
                    (nmht (the-mfixnum (number-of-mht-calls num)))
                    (ncalls (the-mfixnum (number-of-calls num)))
                    (pons-calls (the-mfixnum (pons-calls num)))
                    (no-hits (or (not *report-hits*)
                                 (null (memoize-condition fn))))
                    #+ccl
                    (bytes-allocated (bytes-allocated num))
                    (tt (max .000001

; Why insist that tt be at least .000001?  That has been the case historically,
; and it might be reasonable since a smaller time might be unlikely and anyhow,
; .000001 is not unreasonable if only as "noise".  So we leave this code alone.

                             (total-time num)))
                    (t/c (time/call num))
                    (in-progress-str
                     (if (eql start-ticks -1) "" " (running)"))
                    (selftime tt))
               (declare (type integer start-ticks)
                        (type mfixnum num nhits nmht ncalls
                              pons-calls
                              #+ccl bytes-allocated))
               (format t "~%(~s~%" fn)
               (mf-print-alist
                `(,@(when (or *report-calls* *report-hits*)
                      `((,(format nil " ~a~a"
                                  (if no-hits "Calls" "Hits/calls")
                                  in-progress-str)
                         ,(cond
                           (no-hits (format nil "~a" (mf-num-to-string ncalls)))
                           ((zerop ncalls)
                            (format nil "~8,2e/~8,2e = ????%"
                                    nhits
                                    0))
                           (t (format nil "~8,2e/~8,2e = ~4,1f%"
                                      nhits
                                      ncalls
                                      (* 100 (/ nhits (float ncalls)))))))))
                  ,@(when (and *report-mht-calls*

; The following inequality was here historically, perhaps because nmht is
; always at least 1 (not sure about that); anyhow, it seems OK to leave it.

                               (>= nmht 2))
                      `((" Number of calls to mht" ,(mf-num-to-string nmht))))
                  ,@(when *report-time*
                      `((" Time of all outermost calls"
                         ,(cond
                           ((zerop global-total-time)
                            (format nil "~a; ????%"
                                    (mf-num-to-string tt)))
                           (t
                            (format nil "~a; ~4,1f%"
                                    (mf-num-to-string tt)
                                    (* 100 (/ tt global-total-time))))))
                        (" Time per call" ,(mf-num-to-string t/c))))

; The commented-out code (when ...), below, has been here historically (through
; August 2014), but it's not clear why.  Note that the "Heisenberg" note is
; only made for profiled functions; what's so special about the profiling case?
; Let's just leave it to the user to decide what to make of a very small time
; per call.  To see such a case, you can try this:

; (defn foo (x) x)
; (profile 'foo)
; (foo 1)
; (foo 2)
; (memsum)

;              ,@(when (and (null (access memoize-info-ht-entry entry
;                                         :condition))
;                           (null (access memoize-info-ht-entry entry
;                                         :inline))
;                           (< t/c 1e-6))
;                  `((,(format nil " Doubtful timing info for ~a." fn)
;                     "Heisenberg effect.")))
                  #+ccl
                  ,@(when (and (> bytes-allocated 0) *report-bytes*)
                      (assert (> global-bytes-allocated 0))
                      `((" Heap bytes allocated"
                         ,(format nil "~a; ~4,1f%"
                                  (mf-num-to-string bytes-allocated)
                                  (* 100 (/ bytes-allocated
                                            global-bytes-allocated))))
                        (" Heap bytes allocated per call"
                         ,(mf-num-to-string (/ bytes-allocated ncalls)))))
                  ,@(when (and (> pons-calls 0)
                               *report-pons-calls*)
                      (assert (> global-pons-calls 0))
                      `((" Pons calls"
                         ,(format nil "~a; ~4,1f%"
                                  (mf-num-to-string pons-calls)
                                  (* 100 (/ pons-calls global-pons-calls))))))
                  ,@(when (and *report-hits* *report-time* (not (eql 0 nhits)))
                      `((" Time per missed call"
                         ,(mf-num-to-string (time-for-non-hits/call num)))))
                  ,@(when *report-calls-to*
                      (let ((lst nil)
                            (outside-fn-time 0)
                            (outside-fn-count 0))
                        (declare (type mfixnum outside-fn-count))
                        (loop
                         for callern in ; collect fns called by fn
                         (loop for i below (length *callers-array*)
                               when (member num (aref *callers-array* i))
                               collect i)
                         do
                         (let* ((call-loc (ma-index-calls callern num))
                                (calls (aref ma call-loc))
                                (ticks-loc ; (ma-index-ticks callern num)
                                 (the-mfixnum (1+ call-loc)))
                                (ticks (aref ma ticks-loc))
                                (local-tt (/ ticks *float-ticks/second*)))
                           (declare
                            (type mfixnum call-loc calls ticks-loc ticks))
                           (decf selftime local-tt)
                           (cond
                            ((or (outside-caller-p callern)
                                 (< (* 100 local-tt) tt))
                             (incf outside-fn-time local-tt)
                             (safe-incf
                              outside-fn-count
                              calls
                              memoize-summary-after-compute-calls-and-times))
                            (t (push
                                `((,(format nil
                                            " To ~s"
                                            (fixnum-to-symbol callern))
                                   ,(format nil
                                            "~8,2e calls took~8,2e; ~a%"
                                            calls
                                            local-tt
                                            (cond
                                             ((> (* 10000 local-tt) tt)
                                              (assert (< 0 tt))
                                              (format
                                               nil
                                               "~4,1f"
                                               (* 100 (/ local-tt tt))))
                                             (t "<0.01"))))
                                  . ,(if *sort-to-from-by-calls*
                                         calls
                                       local-tt))
                                lst)))))
                        (when (> outside-fn-time 0)
                          (assert (< 0 tt))
                          (push
                           `((,(format nil " To other functions")
                              ,(format
                                nil
                                "~8,2e calls took~8,2e; ~a%"
                                outside-fn-count
                                outside-fn-time
                                (if (> (* 10000 outside-fn-time) tt)
                                    (format nil
                                            "~4,1f"
                                            (* 100 (/ outside-fn-time tt)))
                                  "<0.01")))
                             . ,(if *sort-to-from-by-calls*
                                    outside-fn-count
                                  outside-fn-time))
                           lst))
                        (when (and (> selftime 0)
                                   (not (= selftime tt)))
                          (assert (< 0 tt))
                          (push `((" To self/unprofiled functions"
                                   ,(format
                                     nil
                                     "~8,2e; ~a%"
                                     selftime
                                     (if (> (* 10000 selftime) tt)
                                         (format nil
                                                 "~4,1f"
                                                 (* 100 (/ selftime tt)))
                                       "<0.01")))
                                  . ,(if *sort-to-from-by-calls*
                                         0 ; unknown number of calls; just use 0
                                       selftime))
                                lst))
                        (setq lst (sort lst #'> :key #'cdr))
                        (strip-cars lst)))
                  ,@(when *report-calls-from*
                      (let ((lst nil)
                            (outside-caller-time 0)
                            (outside-caller-count 0))
                        (loop
                         for callern in (aref *callers-array* num)
                         do
                         (let* ((call-loc (ma-index-calls num callern))
                                (calls (aref ma call-loc))
                                (ticks-loc ; (ma-index-ticks num callern)
                                 (the-mfixnum (1+ call-loc)))
                                (ticks (aref ma ticks-loc))
                                (local-tt (/ ticks *float-ticks/second*)))
                           (declare
                            (type mfixnum call-loc calls ticks-loc ticks))
                           (cond
                            ((or (outside-caller-p callern)
                                 (< (* 100 local-tt) tt))
                             (incf outside-caller-time local-tt)
                             (incf outside-caller-count calls))
                            (t (push
                                `((,(format
                                     nil
                                     " From ~s"
                                     (fixnum-to-symbol callern))
                                   ,(format
                                     nil
                                     "~8,2e calls took~8,2e; ~a%"
                                     calls
                                     local-tt
                                     (if (and (<= .001 local-tt)
                                              (< local-tt tt))
                                         (format nil
                                                 "~4,1f"
                                                 (* 100 (/ local-tt tt)))
                                       "?")))
                                  . ,(if *sort-to-from-by-calls*
                                         calls
                                       local-tt))
                                lst)))))
                        (when (> outside-caller-time 0)
                          (push
                           `((,(format nil " From other functions")
                              ,(format
                                nil
                                "~8,2e calls took~8,2e; ~a%"
                                outside-caller-count
                                outside-caller-time
                                (if (and (<= .001 outside-caller-time)
                                         (< outside-caller-time tt))
                                    (format
                                     nil
                                     "~4,1f"
                                     (* 100 (/ outside-caller-time tt)))
                                  "?")))
                             . ,(if *sort-to-from-by-calls*
                                    outside-caller-count
                                  outside-caller-time))
                           lst))
                        (setq lst (sort lst #'> :key #'cdr))
                        (strip-cars lst)))
                  ,@(when (or *report-on-memo-tables* *report-on-pons-tables*)
                      (let ((sum-pons-sub-sizes 0)
                            (nponses 0)
                            (nponssubs 0))
                        (declare (type mfixnum
                                       sum-pons-sub-sizes nponses nponssubs))
                        (and
                         ponstablename
                         *report-on-pons-tables*
                         (maphash
                          (lambda (key value)
                            (declare (ignore key))
                            (cond
                             ((not (listp value))
                              (safe-incf-pons sum-pons-sub-sizes
                                              (hash-table-size
                                               (the hash-table value)))
                              (safe-incf-pons nponses
                                              (hash-table-count
                                               (the hash-table value)))
                              (safe-incf-pons nponssubs 1))
                             (t (safe-incf-pons nponses (length value)))))
                          ponstablename))
                        `(,@(and
                             tablename
                             *report-on-memo-tables*
                             (let ((count (hash-table-count
                                           (the hash-table tablename)))
                                   (size (hash-table-size
                                          (the hash-table tablename))))
                               `((,(format nil " Memoize table count/size")
                                  ,(format
                                    nil
                                    "~8,2e/~8,2e = ~4,1f%"
                                    count size (* 100 (/ count size)))))))
                          ,@(and
                             ponstablename
                             *report-on-pons-tables*
                             (let ((count (hash-table-count
                                           (the hash-table ponstablename)))
                                   (size (hash-table-size
                                          (the hash-table ponstablename))))
                               `((" (Pons table count/size"
                                  ,(format
                                    nil
                                    "~:d/~:d = ~4,1f%)"
                                    count
                                    size
                                    (* 100 (/ count size))))
                                 (" (Number of pons sub tables"
                                  ,(format
                                    nil
                                    "~a)"
                                    (mf-num-to-string nponssubs)))
                                 (" (Sum of pons sub table sizes"
                                  ,(format
                                    nil
                                    "~a)"
                                    (mf-num-to-string sum-pons-sub-sizes)))
                                 (" (Number of ponses"
                                  ,(format
                                    nil
                                    "~a)"
                                    (mf-num-to-string nponses))))))))))
                5))
             (format t ")"))))
    (terpri *standard-output*)
    (force-output *standard-output*))
  nil)

(defun-one-output memoize-summary ()

; Warning: Keep the return values in sync for the logic and raw Lisp.

; (Memoize-summary) reports data stored during the execution of the functions
; in (memoized-functions).

; Typically each call of a memoized function, fn, is counted.
; The elapsed time until an outermost function call of fn ends, the
; number of heap bytes allocated in that period (CCL only), and other
; 'charges' are 'billed' to fn.  That is, quantities such as elapsed
; time and heap bytes allocated are not charged to subsidiary
; recursive calls of fn while an outermost call of fn is running.
; Recursive calls of fn, and memoized 'hits', are counted, unless fn
; was memoized with nil as the value of the :inline parameter of
; memoize.

; The settings of the following determine, at the time a function is
; given to memoize, the information that is collected for calls of
; the function:

;        Variable              type

;        *record-bytes*       boolean    (available in CCL only)
;        *record-calls*       boolean
;        *record-hits*        boolean
;        *record-mht-calls*   boolean
;        *record-pons-calls*  boolean
;        *record-time*        boolean

; The settings of the following determine, at the time that
; memoize-summary is called, what information is printed:

;        *report-bytes*       boolean   (available in ccl only)
;        *report-calls*       boolean
;        *report-calls-from*  boolean
;        *report-calls-to*    boolean
;        *report-hits*        boolean
;        *report-mht-calls*   boolean
;        *report-pons-calls*  boolean
;        *report-time*        boolean

;        *report-on-memo-tables*   boolean
;        *report-on-pons-tables*   boolean
;        *memoize-summary-limit*            (or integerp null)
;        *memoize-summary-order-list*       (symbol symbol ... symbol)
;        *memoize-summary-order-reversed*   boolean

; Functions are sorted lexicographically according to the ordering
; induced by the function names in *memoize-summary-order-list*, each
; member of which must be a unary function that returns a rational.

; (Clear-memoize-tables) forgets the remembered values of all memoized function
; calls.  It does not alter a function's status as being a memoized function,
; nor does it alter the monitoring data accumulated.

; (Unmemoize-all) undoes the memoization status of all memoized
; functions.

; (Clear-memoize-call-array) zeroes out the monitoring information for
; all functions.  It does not alter any function's status as a
; memoized function nor does it change the values remembered for any
; memoized function.

; Here is an example of hacking with *memoize-summary-order-list* that
; instructs memoize-summary to print information about, say,
; 1st-mod-err first:

;   (push (lambda (fn)
;           (if (eq fn '1st-mod-err) 1 0))
;         *memoize-summary-order-list*)."

; Note that like the "Time of all outermost calls", the "Pons calls" reported
; are cumulative.  For example, we get 8 pons calls for G (not 4) in the
; following example, using CCL: 4 for G, and 4 for the subsidiary calls of F.

;   (defn f (x y) (cons x y))
;   (defn g (x y) (f x y))
;   (memoize 'f)
;   (memoize 'g)
;   (g '(3 . 4) '(5 . 6))
;   (g '(3 . 5) '(5 . 6))
;   (g '(3 . 6) '(5 . 6))
;   (g '(3 . 7) '(5 . 6))
;   (memsum)

  (compute-calls-and-times)
  (memoize-summary-after-compute-calls-and-times)
  nil)

; SECTION: Clearing and initialization

(defun clear-one-memo-and-pons-hash (l)

;  It is debatable whether one should use the clrhash approach or the
;  set-to-nil approach in clear-one-memo-and-pons-hash.  the clrhash approach,
;  in addition to reducing the number of make-hash-table calls necessary, has
;  the effect of immediately clearing a hash-table even if some other function
;  is holding on to it, so more garbage may get garbage collected sooner than
;  otherwise.  The set-to-nil approach has the advantage of costing very few
;  instructions and very little paging.  See also the comment "Perhaps we
;  should use clrhash below" in memoize-fn-outer-body.

  (with-global-memoize-lock
    (let* ((fn (access memoize-info-ht-entry l :fn))
           (mt (symbol-value (access memoize-info-ht-entry l :tablename)))
           (pt (symbol-value (access memoize-info-ht-entry l :ponstablename)))
           (mt-count (and mt (hash-table-count mt)))
           (pt-count (and pt (hash-table-count pt))))
      (when mt
        (setf (symbol-value (access memoize-info-ht-entry l :tablename)) nil))
      (when pt
        (setf (symbol-value (access memoize-info-ht-entry l :ponstablename)) nil))
      (when (or mt-count pt-count)
        (update-memo-max-sizes fn (or pt-count 1) (or mt-count 1)))))
  nil)

(defun-one-output clear-memoize-table (k)

; Warning: Keep the return values in sync for the logic and raw Lisp.

  (with-global-memoize-lock
    (when (symbolp k)
      (let ((l (gethash k *memoize-info-ht*)))
        (when l (clear-one-memo-and-pons-hash l)))))
  k)

(defun-one-output clear-memoize-tables ()

; Warning: Keep the return values in sync for the logic and raw Lisp.

  (with-global-memoize-lock
    (let (success)
      (unwind-protect
          (progn
            (maphash (lambda (k l)
                       (when (symbolp k)
                         (clear-one-memo-and-pons-hash l)))
                     *memoize-info-ht*)
            (setq success t))
        (or success (error "clear-memoize-tables failed."))))
    (setq *pons-call-counter* 0)
    (setq *pons-misses-counter* 0))
  nil)

(defun clear-memoize-call-array ()

; (Clear-memoize-call-array) zeros out all records of function calls for
; purposes of reporting, for example by memoize-summary.

  (with-global-memoize-lock
    (let ((ma *memoize-call-array*))
      (declare (type (simple-array mfixnum (*)) ma))
      (let ((len (length ma)))
        (cond ((typep len 'fixnum)
               (loop for i fixnum below len
                     do (setf (aref ma i) 0)))
              (t ; maybe impossible?
               (loop for i of-type integer below len
                     do (setf (aref ma i) 0))))))))

(defun clear-memoize-statistics ()

; Warning: Keep the return values in sync for the logic and raw Lisp.

  (with-global-memoize-lock
    (setq *pons-call-counter* 0)
    (setq *pons-misses-counter* 0)
    (clear-memoize-call-array))
  nil)

(defun-one-output memoize-init ()

; This function initializes most globals that are managed automatically by the
; memoization implementation, i.e., that are not user-settable.  Not included
; here is *sol-gc-installed*, which we consider to pertain to ACL2(h) but to be
; outside memoization proper.

  (when *memoize-init-done*
    (return-from memoize-init nil))
  (with-global-memoize-lock
    (unless (eql *caller* (the-mfixnum (outside-caller-col-base)))
      (error "memoize-init:  A memoized function is running."))
    (let (success)
      (unwind-protect
          (progn
            (setq *pons-call-counter* 0)
            (setq *pons-misses-counter* 0)
            (setq *memoize-info-ht* (memo-mht))
            (setf (gethash *initial-max-symbol-to-fixnum* *memoize-info-ht*)
                  "outside-caller")
            (setq *max-symbol-to-fixnum* *initial-max-symbol-to-fixnum*)
            (setq *2max-memoize-fns* *initial-2max-memoize-fns*)
            (sync-memoize-call-array)
            (setq *memo-max-sizes* (memo-mht))
            (setq success t))
        (if success
            (setq *memoize-init-done* t)
          (error "memoize-init failed.")))))
  nil)

(defmacro with-lower-overhead (&rest r)

; Warning: Keep this in sync with lower-overhead.

  `(let ((*record-bytes* nil)
         (*record-calls*

; It has been a mystery why we have needed to set *record-calls* to t in
; LispWorks.  We found that otherwise, for example, evaluation hangs for
; (bad-lisp-objectp (make-list 100000)) when bad-lisp-objectp is in the initial
; memoized state produced by calling acl2h-init (see acl2h-init-memoizations)
; It might well be worth looking into this again.

          #-lispworks nil #+lispworks t)
         (*record-hits* nil)
         (*record-mht-calls* nil)
         (*record-pons-calls* nil)
         (*record-time* nil))
     ,@r))

(defun acl2h-init-memoizations ()

; Warning: Keep in sync with acl2h-init-unmemoizations.  Note however that some
; of the functions memoized here are not memoized by acl2h-init-unmemoizations,
; as explained below and in a comment in that function.

; The memoizations performed here, for certain built-in functions, may be
; important for performance in applications that traffic in large objects or
; terms.  Some of these memoizations are undone by acl2h-init-unmemoizations,
; which is called by ACL2(hp) when waterfall-parallelism is turned on, in order
; to avoid errors during the waterfall due the fact that memoization is not
; thread-safe.

  (loop for entry in

; Warning: If this list is changed, visit the comments in the memoized
; functions.

        (list* '(fchecksum-obj :forget t)
               '(expansion-alist-pkg-names-memoize :forget t)
               *thread-unsafe-builtin-memoizations*)
        when (not (memoizedp-raw (car entry)))
        do (with-lower-overhead
            (apply 'memoize-fn entry))))

(defun acl2h-init-unmemoizations ()

; Warning: Keep in sync with acl2h-init-memoizations.

; We unmemoize only those functions whose memoization may interfere with
; waterfall parallelism.  In particular, we avoid unmemoizing fchecksum-obj and
; expansion-alist-pkg-names-memoize, which had caused ACL2(hp) certification
; failure for community book books/system/doc/render-doc-combined (which went
; out to lunch with many fchecksum-obj on the stack).

; We unmemoize bad-lisp-objectp because the *1* function for
; symbol-package-name calls chk-bad-lisp-object, and of course
; symbol-package-name can be called during the waterfall.  Of course,
; worse-than-builtin is also called during the waterfall, so we unmemoize it
; here as well.

  (loop for entry in

; Warning: If this list is changed, visit the comments in the memoized
; functions.

        *thread-unsafe-builtin-memoizations*
        when (memoizedp-raw (car entry))
        do (unmemoize-fn (car entry))))

;;;;;;;;;;
;;; Start memory management code (start-sol-gc)
;;;;;;;;;;

; This section of code was suggested by Jared Davis as a way to regain
; performance of ACL2(h) on regressions at UT CS.  Initially, these regressions
; showed significant slowdown upon including new memoization code from Centaur
; on 3/28/2013:
; ; old:
; 24338.570u 1357.200s 1:19:02.75 541.7%	0+0k 0+1918864io 0pf+0w
; ; new:
; 33931.460u 1017.070s 1:43:24.28 563.2%	0+0k 392+1931656io 0pf+0w
; After restoring (start-sol-gc) in function acl2h-init, we regained the old
; level of performance for a UT CS ACL2(h) regression, with the new memoizaion
; code.

(defun mf-looking-at (str1 str2 &key (start1 0) (start2 0))

; (Mf-looking-at str1 str2 :start1 s1 :start2 s2) is non-nil if and only if
; string str1, from location s1 to its end, is an initial segment of string
; str2, from location s2 to its end.

   (unless (typep str1 'simple-base-string)
     (error "looking at:  ~a is not a string." str1))
   (unless (typep str2 'simple-base-string)
     (error "looking at:  ~a is not a string." str2))
   (unless (typep start1 'fixnum)
     (error "looking at:  ~a is not a fixnum." start1))
   (unless (typep start2 'fixnum)
     (error "looking at:  ~a is not a fixnum." start2))
   (locally
     (declare (simple-base-string str1 str2)
              (fixnum start1 start2))
     (let ((l1 (length str1)) (l2 (length str2)))
       (declare (fixnum l1 l2))
       (loop
        (when (>= start1 l1) (return t))
        (when (or (>= start2 l2)
                  (not (eql (char str1 start1)
                            (char str2 start2))))
          (return nil))
        (incf start1)
        (incf start2)))))

(defun our-uname ()

; Returns nil or else a keyword, currently :darwin or :linux, to indicate the
; result of shell command "uname".

  (multiple-value-bind
   (exit-code val)
   (system-call+ "uname" nil)
   (and (eql exit-code 0)
        (stringp val)
        (<= 6 (length val))
        (cond ((string-equal (subseq val 0 6) "Darwin") :darwin)
              ((string-equal (subseq val 0 5) "Linux") :linux)))))

(defun meminfo (&optional arg)

; With arg = nil, this function either returns 0 or else the physical memory.
; See the code below to understand what information might be returned for
; non-nil values of arg.

  (assert (or (null arg)
              (stringp arg)))
  (or
   (with-standard-io-syntax
    (case (our-uname)
      (:linux
       (let ((arg (or arg  "MemTotal:")))
         (and
          (our-ignore-errors (probe-file "/proc/meminfo"))
          (with-open-file
           (stream "/proc/meminfo")
           (let (line)
             (loop while (setq line (read-line stream nil nil)) do
                   (when (mf-looking-at arg line)
                     (return
                      (values
                       (read-from-string line nil nil
                                         :start (length arg)))))))))))
      (:darwin
       (let* ((arg (or arg "hw.memsize"))
              (len (length arg)))
         (multiple-value-bind
          (exit-code val)
          (system-call+ "sysctl" (list arg))
          (and (eql exit-code 0)
               (mf-looking-at arg val)
               (mf-looking-at arg ": " :start1 len)
               (let ((ans (read-from-string val nil nil :start (+ 2 len))))
                 (and (integerp ans)
                      (equal (mod ans 1024) 0)
                      (/ ans 1024)))))))
      (t nil)))
   0))

(let ((physical-memory-cached-answer nil))
   (defun physical-memory () ; in KB
     (or physical-memory-cached-answer
         (setq physical-memory-cached-answer
               (meminfo)))))

#+ccl
(defun set-and-reset-gc-thresholds ()

; See start-sol-gc for a full discussion.  The comments here summarize how that
; works out if, for example, there are 8G bytes of physical memory, just to
; make the concepts concrete -- so it might be helpful to read the comments in
; this function before reading the more general discussion in start-sol-gc.

  (let ((n

; E.g., with 8G bytes of physical memory, *max-mem-usage* is 1/8 of that --
; i.e., 1G -- and *gc-min-threshold* is 1/4 of that -- i.e., (1/4)G.  Then here
; we arrange to allocate enough memory after a GC to reach *max-mem-usage* = 1G
; bytes before the next GC, unless the current memory usage is more than
; (3/4)G, in which case we allocate the minimum of (1/4)G.

         (max (- *max-mem-usage* (ccl::%usedbytes))
              *gc-min-threshold*)))

; Now set the "threshold" to the number of bytes computed above (unless that
; would be a no-op).

    (unless (eql n (ccl::lisp-heap-gc-threshold))
      (ccl::set-lisp-heap-gc-threshold n)))

; The above setting won't take effect until the next GC unless we take action.
; Here is that action, which actually allocates the bytes computed above as
; free memory.

  (ccl::use-lisp-heap-gc-threshold)

; Finally, still assuming 8G bytes of phyical memory, set the "threshold" to
; (1/4)G.  This is how much the next GC will set aside as free memory -- at
; least initially, but then the post-gc hook will call this function.  As
; explained above, in the case that the current memory usage is less than
; (3/4)G, enough free memory will be allocated so that the next GC is triggered
; after *max-mem-usage* = 1G bytes are in use.

  (unless (eql *gc-min-threshold* (ccl::lisp-heap-gc-threshold))
    (ccl::set-lisp-heap-gc-threshold *gc-min-threshold*)))

#+ccl
(defun start-sol-gc ()

;          Sol Swords's scheme to control GC in CCL
;
; The goal is to get CCL to perform a GC whenever we're using almost
; all the physical memory, but not otherwise.
;
; The discussion below is self-contained, but for more discussion, relevant CCL
; documentation is at http://ccl.clozure.com/ccl-documentation.html, Chapter
; 16.
;
; The usual way of controlling GC on CCL is via LISP-HEAP-GC-THRESHOLD.  This
; value is approximately the amount of free memory that will be allocated
; immediately after GC.  This means that the next GC will occur after
; LISP-HEAP-GC-THRESHOLD more bytes are used (by consing or array allocation or
; whatever).  But this means the total memory used by the time the next GC
; comes around is the threshold plus the amount that remained in use at the end
; of the previous GC.  This is a problem because of the following scenario:
;
;  - We set the LISP-HEAP-GC-THRESHOLD to 3GB since we'd like to be able
;    to use most of the 4GB physical memory available.
;
;  - A GC runs or we say USE-LISP-HEAP-GC-THRESHOLD to ensure that 3GB
;    is available to us.
;
;  - We run a computation until we've exhausted this 3GB, at which point
;    a GC occurs.
;
;  - The GC reclaims 1.2 GB out of the 3GB used, so there is 1.8 GB
;    still in use.
;
;  - After GC, 3GB more is automatically allocated -- but this means we
;    won't GC again until we have 4.8 GB in use, meaning we've gone to
;    swap.
;
; What we really want is, instead of allocating a constant additional
; amount after each GC, to allocate up to a fixed total amount including
; what's already in use.  To emulate that behavior, we use the hack
; below.  This operates as follows, assuming the same 4GB total physical
; memory as in the above example (or, unknown physical memory that defaults to
; 4GB as shown below, i.e., when function meminfo returns 0).
;
; 1. We set the LISP-HEAP-GC-THRESHOLD to (0.5G minus used bytes) and call
; USE-LISP-HEAP-GC-THRESHOLD so that our next GC will occur when we've used a
; total of 0.5G.
;
; 2. We set the threshold back to *gc-min-threshold*= 0.125GB without calling
; USE-LISP-HEAP-GC-THRESHOLD.
;
; 3. Run a computation until we use up the 0.5G and the GC is called.  Say the
; GC reclaims 0.3GB so there's 0.2GB in use.  0.125GB more (the current
; LISP-HEAP-GC-THRESHOLD) is allocated so the ceiling is 0.325GB.
;
; 4. A post-GC hook runs which again sets the threshold to (0.5G minus used
; bytes), calls USE-LISP-HEAP-GC-THRESHOLD to raise the ceiling to 0.5G, then
; sets the threshold back to 0.125GB, and the process repeats.
;
; A subtlety about this scheme is that post-GC hooks runs in a separate
; thread from the main execution.  A possible bug is that in step 4,
; between checking the amount of memory in use and calling
; USE-LISP-HEAP-GC-THRESHOLD, more memory might be used up by the main
; execution, which would set the ceiling higher than we intended.  To
; prevent this, we interrupt the main thread to run step 4.

; The following settings are highly heuristic.  We arrange that gc
; occurs at 1/8 of the physical memory size in bytes, in order to
; leave room for the gc point to grow (as per
; set-and-reset-gc-thresholds).  If we can determine the physical
; memory; great; otherwise we assume that it it contains at least 4GB,
; a reasonable assumption we think for anyone using the HONS version
; of ACL2.

  (let* ((phys (physical-memory))
         (memsize (cond ((> phys 0) (* phys 1024)) ; to bytes
                        (t (expt 2 32)))))
    (setq *max-mem-usage* (min (floor memsize 8)
                               (expt 2 31)))
    (setq *gc-min-threshold* (floor *max-mem-usage* 4)))
  (unless *sol-gc-installed*
    (ccl::add-gc-hook
     #'(lambda ()
         (ccl::process-interrupt
          (slot-value ccl:*application* 'ccl::initial-listener-process)
          #'set-and-reset-gc-thresholds))
     :post-gc)
    (setq *sol-gc-installed* t))
  (set-and-reset-gc-thresholds))

(defun-one-output acl2h-init ()

; ACL2-DEFAULT-RESTART is called whenever a saved image for any version of ACL2
; is started up.  For ACL2(h), ACL2-DEFAULT-RESTART calls ACL2H-INIT.  Although
; we expect ACL2-DEFAULT-RESTART to be called only once, nevertheless for
; robustness we code ACL2H-INIT so that it may be called multiple times.

  (memoize-init)

  #+static-hons
  (setq *print-array*

; With *print-array* turned on, we end up sometimes seeing the SBITS array in
; backtraces, etc, which can effectively kill your session (can't interrupt,
; etc.).  This is only a problem with static-honsing since classic honsing
; doesn't have sbits anyway.

        nil)

  #+ccl
  (start-sol-gc)

; It is can be helpful for the user to know what the garbage collector is doing
; when using HONS and MEMOIZE.  We leave full-gc messages on but turn EGC
; messages off.  We're disabling EGC anyway, but when we've experimented with
; leaving it on, the EGC messages are way too verbose.

  (gc-verbose t nil)

; We turn off EGC because it doesn't seem to work well with memoizing
; worse-than-builtin and sometimes seems buggy; but we want to investigate this
; more.

  #+ccl
  (ccl::egc nil)

  nil)

; SECTION: Miscellaneous (e.g.  shorter, older names)

; Note: memsum is defined in memoize.lisp.

(defun memstat (&rest r)
  (apply #'memoized-values r))

(defun clear-memo-tables ()
  (clear-memoize-tables))

(defun lower-overhead ()

; Warning: Keep this in sync with with-lower-overhead.

; An old comment here claims that lower-overhead does not help much (in
; speeding things up, presumably).  It might be interesting to test that.

  (setq *record-bytes* nil)
  (setq *record-calls*

; See the comment about LispWorks in with-lower-overhead; we make the analogous
; adjustment for LispWorks here, in case it's necessary.

        #-lispworks nil #+lispworks t)
  (setq *record-hits* nil)
  (setq *record-mht-calls* nil)
  (setq *record-pons-calls* nil)
  (setq *record-time* nil))

(defun update-memo-entry-for-attachments (fns entry wrld)

; See the Essay on Memoization with Attachments.

; This function is called by update-memo-entries-for-attachments.  We return
; (mv changed-p new-entry), where if changed-p is not t or nil then it is a
; function symbol whose attachment has changed, which requires clearing of the
; corresponding memo table.

;; [Jared] it looks like this doesn't need any locking protection

  (let* ((ext-anc-attachments
          (access memoize-info-ht-entry entry :ext-anc-attachments))
         (valid-p
          (if (eq fns :clear)
              :clear
            (or (null ext-anc-attachments)
                (ext-anc-attachments-valid-p fns ext-anc-attachments wrld
                                             t)))))
    (cond ((eq valid-p t) (mv nil entry))
          (t
           (mv (if (eq valid-p nil) t valid-p)
               (change memoize-info-ht-entry entry
                       :ext-anc-attachments
                       (ext-ancestors-attachments
                        (access memoize-info-ht-entry entry :fn)
                        wrld)))))))

(defun update-memo-entries-for-attachments (fns wrld state)

; See the Essay on Memoization with Attachments.  Here is a brief, high-level
; summary of what is going on.

; This function is called by update-wrld-structures, which is called when the
; world is updated.  When a defattach event is added or removed from the world,
; variable *defattach-fns* collects the name of the function with an attachment
; (either being added or removed).  Ultimately, *defattach-fns* is passed as
; the fns parameter to the present function, and functions' entries in
; *memoize-info-ht* are correspondingly updated as necessary, in particular
; clearing tables whose values may have depended on attachments that are no
; longer present.

  (let ((ctx 'top-level)
        (fns (if (eq fns :clear)
                 :clear
               (strict-merge-sort-symbol-<
                (loop for fn in fns
                      collect (canonical-sibling fn wrld))))))
    (when (eq fns :clear)
      (observation ctx
                   "Memoization tables for functions memoized with :AOKP T ~
                    are being cleared."))
    (when fns ; optimization
      (with-global-memoize-lock
        (maphash (lambda (k entry)
                   (when (symbolp k)
                     (mv-let (changedp new-entry)
                       (update-memo-entry-for-attachments fns entry wrld)
                       (when changedp
                         (when (not (or (eq changedp t)
                                        (eq fns :clear)))
                           (observation ctx
                                        "Memoization table for function ~
                                             ~x0 is being cleared because ~
                                             attachment to function ~x1 has ~
                                             changed."
                                        k changedp)
                           (clear-one-memo-and-pons-hash entry))
                         (setf (gethash k *memoize-info-ht*)
                               new-entry)))))
                 *memoize-info-ht*)))))
