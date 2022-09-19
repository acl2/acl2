; Copyright (C) 2014, Regents of the University of Texas
; Written by Matt Kaufmann (original date March, 2014)
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

(defxdoc with-supporters
  :parents (macro-libraries)
  :short "Automatically include specified definitions from a specified book"
  :long
  "<p>When @(see local) @(tsee include-book) forms are used in support of
  definitions and theorems, the enclosing book or @(tsee encapsulate) event may
  be ill-formed because of missing definitions.  Consider the following
  example.</p>

  @({
  (encapsulate
    ()
    (local (include-book \"bk\")) ; defines function f ;
    (defun g (x) (f x)))
  })

  <p>In this example, the definition of @('f') in @('\"bk.lisp\"') is required
  in order to admit the definition of @('g'); thus, we say that (the definition
  of) @('f') is a <i>supporter of</i> (the definition of) @('g').</p>

  <p>@('With-supporters') automatically generates and evaluates definitions, in
  order to support a given set of names and events.  See also @(tsee
  with-supporters-after) for a related utility.</p>

  <p>General forms:</p>

  @({
  (with-supporters (local ev) ; a local event
                   [optional keyword arguments, including perhaps:]
                   :names (name-1 ... name-m) ; optional keyword argument
                   [other optional keyword arguments]
                   event-1 ... event-k)
  })

  <p>where the optional keyword arguments are not evaluated and are described
  below, and each @('event-i') is an @(see event).  The effect is the same
  as</p>

  @({((encapsulate () (local ev) EXTRA event-1 ... event-k)})

  <p>where @('EXTRA') is a sequence of events that includes the supporters of
  the @('name-i') and @('event-i') so that the second pass of that
  @('encapsulate') call will succeed.  (Recall that @(see local) events are
  skipped during that pass; see @(see encapsulate).)  More precisely,
  @('EXTRA') includes the following:</p>

  <ul>

  <li>function, macro, and constant definitions that support the supplied
  @(':names') and @('event-1') through @('event-k');</li>

  <li>definitions of macros that are aliases for the newly-defined
  functions (see @(see macro-aliases-table));</li>

  <li>@(tsee defattach) and @(tsee table) events; and</li>

  <li>@(tsee in-theory) events so that the rules introduced by the @('EXTRA')
  definitions are suitably enabled or disabled.</li>

  </ul>

  <h3>Other keywords</h3>

  <p>Each keyword argument must appear immediately after the initial local
  event, before the supplied @('event-i').  The keyword @(':names') is
  discussed above; here we discuss the others.  The keyword arguments are not
  evaluated.</p>

  <ul>

  <li>@(':show') (default @('nil'))<br/>

  This argument must be @('nil'), @(':only'), or @('t').  If it is @(':only')
  then no event is submitted, but the generated @('encapsulate') is shown by
  returning it as the value component of an @(see error-triple).  If it is
  @('t') then that @('encapsulate') event is printed, before it is evaluated as
  usual.</li>

  <li>@(':tables') (default @('nil'))<br/>

  If this value is not @('nil'), then it may be a list of table names, causing
  the indicated tables to be populated as they were immediately after
  evaluating the @(see local) event, @('ev').  Otherwise the value should be
  @(':all'), indicating that this should be done for all tables (with the
  exception, for technical reasons, of @('pe-table') and the @('xdoc')
  table).</li>

  <li>@(':with-output') (default @('(:off :all :on error)'))<br/>

  This value is an alternating list of keywords and values that can be accepted
  by the @(see with-output) utility.</li>

  </ul>

  <h3>Examples</h3>

  <p>We now illustrate with examples, starting with one that does not use the
  @(':names') keyword.</p>

  <p>Consider the following event.</p>

  @({
  (encapsulate
   ()
   (local (include-book \"std/lists/duplicity\" :dir :system))
   (defthm duplicity-append
     (equal (duplicity a (append x y))
            (+ (duplicity a x) (duplicity a y)))))
  })

  <p>This event fails because the function @('duplicity') is defined in the
  locally included book, and hence that function is undefined when the above
  @(tsee defthm) form is processed during the second pass of the @(tsee
  encapsulate) event.</p>

  <p>One solution is to move the @('include-book') form so that it appears
  non-locally in front of the @('encapsulate') event.  But we may not want to
  include other @(see events) from that book, out of concern that rules defined
  in that book could affect our proof development, or perhaps because including
  the book is slow and we want the superior book to include only what is
  necessary from that book.</p>

  <p>A more suitable solution may thus be to use the macro,
  @('with-supporters'), in place of @('encapsulate'), as follows.</p>

  @({
  (with-supporters
   (local (include-book \"std/lists/duplicity\" :dir :system))
   (defthm duplicity-append
     (equal (duplicity a (append x y))
            (+ (duplicity a x) (duplicity a y)))))
  })

  <p>That macro determines automatically that the function @('duplicity') needs
  to be defined, so it generates an @('encapsulate') event like the original
  one above but with the definition of @('duplicity') added non-locally.  In
  this example, @('duplicity') is actually defined in terms of another
  function, @('duplicity-exec'), so its definition is needed as well.  The
  generated event is initially as follows, as we can see using the @(':show')
  keyword.</p>

  @({
  ACL2 !>(with-supporters
          (local (include-book \"std/lists/duplicity\" :dir :system))
          :show :only
          (defthm duplicity-append
            (equal (duplicity a (append x y))
                   (+ (duplicity a x) (duplicity a y)))))

  Summary
  Form:  ( MAKE-EVENT (WITH-OUTPUT! :OFF ...))
  Rules: NIL
  Time:  0.13 seconds (prove: 0.00, print: 0.00, other: 0.13)
  Prover steps counted:  154
   (WITH-OUTPUT
     :OFF :ALL :ON ERROR
     (ENCAPSULATE
          NIL
          (LOCAL (INCLUDE-BOOK \"std/lists/duplicity\"
                               :DIR :SYSTEM))
          (SET-ENFORCE-REDUNDANCY T)
          (SET-BOGUS-DEFUN-HINTS-OK T)
          (SET-BOGUS-MUTUAL-RECURSION-OK T)
          (SET-IRRELEVANT-FORMALS-OK T)
          (SET-IGNORE-OK T)
          (PROGN (DEFUN DUPLICITY-EXEC (A X N)
                        (DECLARE (XARGS :GUARD (NATP N)))
                        (IF (ATOM X)
                            N
                            (DUPLICITY-EXEC A (CDR X)
                                            (IF (EQUAL (CAR X) A) (+ 1 N) N))))
                 (VERIFY-GUARDS DUPLICITY-EXEC))
          (PROGN (DEFUN DUPLICITY (A X)
                        (DECLARE (XARGS :GUARD T :VERIFY-GUARDS NIL))
                        (MBE :LOGIC (COND ((ATOM X) 0)
                                          ((EQUAL (CAR X) A)
                                           (+ 1 (DUPLICITY A (CDR X))))
                                          (T (DUPLICITY A (CDR X))))
                             :EXEC (DUPLICITY-EXEC A X 0)))
                 (VERIFY-GUARDS DUPLICITY))
          (IN-THEORY (DISABLE (:DEFINITION DUPLICITY-EXEC)
                              (:INDUCTION DUPLICITY-EXEC)
                              (:DEFINITION DUPLICITY)
                              (:INDUCTION DUPLICITY)
                              (:DEFINITION DUPLICITY-EXEC)
                              (:INDUCTION DUPLICITY-EXEC)
                              (:DEFINITION DUPLICITY)
                              (:INDUCTION DUPLICITY)
                              (:DEFINITION DUPLICITY-EXEC)
                              (:INDUCTION DUPLICITY-EXEC)))
          (SET-ENFORCE-REDUNDANCY NIL)
          (DEFTHM DUPLICITY-APPEND
                  (EQUAL (DUPLICITY A (APPEND X Y))
                         (+ (DUPLICITY A X) (DUPLICITY A Y))))))
  ACL2 !>
  })

  <p>Notice that care is taken to preserve the @(':')@(tsee mode), @(see
  guard)-verification, and @(see enable)d status of supporting functions.</p>

  <p>For more examples, see @(see community-books) file
  @('tools/with-supporters-test-top.lisp').</p>")

(defxdoc with-supporters-after
  :parents (macro-libraries)
  :short "Automatically define necessary redundant definitions from after a
  specified event"
  :long
  "<p>When @(see local) @(tsee include-book) forms are used in support of
  definitions and theorems, the resulting book or @(tsee encapsulate) event may
  be ill-formed because of missing definitions.  The macro,
  @('with-supporters-after'), is intended to avoid this problem.</p>

  <p>See @(tsee with-supporters) for a related utility.  (However,
  @('with-supporters-after') does not support keyword arguments; they may be
  straightforward to add.)  The documentation below assumes familiarity with
  @('with-supporters').</p>

  <p>General form:</p>

  @({(with-supporters-after name event-1 ... event-k)})

  <p>where @('name') is the name of an event and @('event-i') are @(see
  events).  The effect is the same as</p>

  @({((encapsulate () EXTRA event-1 ... event-k)})

  <p>where @('EXTRA') includes redundant definitions and other events
  introduced after @('name'), as necessary, in order to avoid undefined
  function errors when processing this @(tsee encapsulate) event, as is the
  case for @('with-supporters'), in particular, including @(see in-theory)
  events so that the rules introduced by the @('EXTRA') definitions are
  suitably enabled or disabled.  Consider the following example.</p>

  @({
  (in-package \"ACL2\")

  (include-book \"tools/with-supporters\" :dir :system)

  (deflabel my-label)

  (local (include-book \"std/lists/duplicity\" :dir :system))

  (with-supporters-after
   my-label
   (defthm duplicity-append
     (equal (duplicity a (append x y))
            (+ (duplicity a x) (duplicity a y)))))
  })

  <p>The form above is equivalent to the following.  Again, see @(tsee
  with-supporters) for relevant background.</p>

  @({
  (PROGN (SET-ENFORCE-REDUNDANCY T)
         (SET-BOGUS-DEFUN-HINTS-OK T)
         (SET-BOGUS-MUTUAL-RECURSION-OK T)
         (SET-IRRELEVANT-FORMALS-OK T)
         (SET-IGNORE-OK T)
         (PROGN (DEFUN DUPLICITY-EXEC (A X N)
                  (DECLARE (XARGS :GUARD (NATP N)))
                  (IF (ATOM X)
                      N
                      (DUPLICITY-EXEC A (CDR X)
                                      (IF (EQUAL (CAR X) A) (+ 1 N) N))))
                (VERIFY-GUARDS DUPLICITY-EXEC))
         (PROGN (DEFUN DUPLICITY (A X)
                  (DECLARE (XARGS :GUARD T :VERIFY-GUARDS NIL))
                  (MBE :LOGIC (COND ((ATOM X) 0)
                                    ((EQUAL (CAR X) A)
                                     (+ 1 (DUPLICITY A (CDR X))))
                                    (T (DUPLICITY A (CDR X))))
                       :EXEC (DUPLICITY-EXEC A X 0)))
                (VERIFY-GUARDS DUPLICITY))
         (IN-THEORY (DISABLE (:DEFINITION DUPLICITY-EXEC)
                             (:INDUCTION DUPLICITY-EXEC)
                             (:DEFINITION DUPLICITY)
                             (:INDUCTION DUPLICITY)
                             (:DEFINITION DUPLICITY-EXEC)
                             (:INDUCTION DUPLICITY-EXEC)
                             (:DEFINITION DUPLICITY)
                             (:INDUCTION DUPLICITY)
                             (:DEFINITION DUPLICITY-EXEC)
                             (:INDUCTION DUPLICITY-EXEC)))
         (SET-ENFORCE-REDUNDANCY NIL)
         (DEFTHM DUPLICITY-APPEND
           (EQUAL (DUPLICITY A (APPEND X Y))
                  (+ (DUPLICITY A X) (DUPLICITY A Y)))))
  })")
