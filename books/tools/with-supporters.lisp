; Copyright (C) 2014, Regents of the University of Texas
; Written by Matt Kaufmann (original date March, 2014)
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This utility provides necessary function definitions, but not macro
; definitions.

(in-package "ACL2")

(program)
(set-state-ok t)

(defun macroexpand-till-event-1 (form names ctx wrld state-vars)

; See macroexpand-till-event.  Here, names is (primitive-event-macros).

  (cond ((or (atom form)
             (not (symbolp (car form)))
             (atom (cdr form)))
         (mv 'bad-shape form))
        ((eq (car form) 'local)
         (mv-let
          (erp result)
          (macroexpand-till-event-1 (cadr form) names ctx wrld state-vars)
          (cond (erp (mv erp result))
                (t (mv nil (list 'local result))))))
        ((member-eq (car form) names)
         (mv nil form))
        (t (let ((body (getprop (car form) 'macro-body nil 'current-acl2-world
                                wrld)))
             (cond (body (mv-let
                          (erp new)
                          (macroexpand1-cmp form ctx wrld state-vars)
                          (cond (erp (mv 'expansion-error (cons erp new)))
                                (t (macroexpand-till-event-1 new names ctx wrld
                                                             state-vars)))))
                   (t (mv 'not-macro form)))))))

(defun macroexpand-till-event (form state)

; Returns (mv erp result), where (mv nil x) for non-nil x indicates that form
; expanded to the event x, and otherwise there is an error.

  (let ((ctx 'macroexpand-till-event))
    (mv-let (erp result)
            (macroexpand-till-event-1 form
                                      (primitive-event-macros)
                                      ctx
                                      (w state)
                                      (default-state-vars t))
            (case erp
              (bad-shape (er soft ctx
                             "Macroexpansion of ~x0 produced oddly-shaped form:~|~x1"
                             form result))
              (expansion-error (cmp-to-error-triple (mv (car result) (cdr result))))
              (not-macro (er soft ctx
                             "Macroexpansion of ~x0 produced non-event form:~|~x1"
                             form result))
              (otherwise (value result))))))

(defun new-fns (names n wrld acc)

; Return a list of all symbols in names whose absolute-event-number property
; has value greater than n.

  (cond ((endp names) acc)
        (t (new-fns (cdr names)
                    n
                    wrld
                    (cond ((> (getprop (car names) 'absolute-event-number 0
                                       'current-acl2-wrld wrld)
                              n)
                           (cons (car names) acc))
                          (t acc))))))

(defun sort-supporting-fns-alist (fns alist wrld)
  (cond ((endp fns) alist)
        (t (sort-supporting-fns-alist
            (cdr fns)
            (cons (cons (getprop (car fns) 'absolute-event-number 0
                                 'current-acl2-wrld wrld)
                        (car fns))
                  alist)
            wrld))))

(defun sort-supporting-fns (fns wrld)

; Sort fns in order of introduction in the given world.

  (let ((alist (sort-supporting-fns-alist fns nil wrld)))
    (strip-cdrs (merge-sort-car-< alist))))

(defun instantiable-ancestors-with-guards (fns wrld ans)

; See ACL2 source function instantiable-ancestors, from which this is derived.
; However, in this case we also include function symbols from guards in the
; result.

  (cond
   ((null fns) ans)
   ((member-eq (car fns) ans)
    (instantiable-ancestors-with-guards (cdr fns) wrld ans))
   (t
    (let* ((ans1 (cons (car fns) ans))
           (imm (immediate-instantiable-ancestors (car fns) wrld ans1))
           (guard (getprop (car fns) 'guard nil 'current-acl2-world wrld))
           (imm+guard-fns (if guard
                              (all-fnnames1 nil guard imm)
                            imm))
           (ans2 (instantiable-ancestors-with-guards imm+guard-fns wrld ans1)))
      (instantiable-ancestors-with-guards (cdr fns) wrld ans2)))))

(defun macro-names-from-aliases (names macro-aliases acc)
  (cond ((endp names) acc)
        (t (macro-names-from-aliases
            (cdr names)
            macro-aliases
            (let ((pair (rassoc (car names) macro-aliases)))
              (cond (pair (cons (car pair) acc))
                    (t acc)))))))

(defun supporting-fns (lst ev-names acc-names n macro-aliases wrld state)

; Lst is initially a list of events, but macro names can be added to it as we
; recur.  Initially ev-names and acc-names is nil.  We return all functions
; with absolute-event-number exceeding n that support events in the given list
; of events, where wrld is (w state).

  (cond ((endp lst) (value (sort-supporting-fns
                            (set-difference-eq acc-names ev-names)
                            wrld)))
        (t (er-let* ((ev (if (consp (car lst))
                             (macroexpand-till-event (car lst) state)
                           (value nil)))
                     (name (value (if (symbolp (car lst))
                                      (car lst)
                                    (and (consp ev)
                                         (consp (cdr ev))
                                         (symbolp (cadr ev))
                                         (cadr ev))))))
             (cond
              ((or (null name)
                   (member-eq name acc-names))
               (supporting-fns (cdr lst) ev-names acc-names n macro-aliases
                               wrld state))
              (t
               (let* ((formula (or (getprop name 'macro-body nil
                                            'current-acl2-world wrld)
                                   (formula name nil wrld)))
                      (guard (getprop name 'guard nil 'current-acl2-world
                                      wrld))
                      (new-names
                       (and formula ; non-nil if guard is non-nil
                            (new-fns (instantiable-ancestors-with-guards
                                      (new-fns
                                       (all-fnnames1 nil
                                                     formula
                                                     (and guard
                                                          (all-fnnames guard)))
                                       n wrld nil)
                                      wrld
                                      nil)
                                     n wrld nil))))
                 (supporting-fns
; Collect names of new macros that might be ancestral in the bodies.
                  (macro-names-from-aliases new-names
                                            macro-aliases
                                            (cdr lst))
                  (if ev
                      (cons name ev-names)
                    ev-names)
                  (append new-names (if ev acc-names (cons name acc-names)))
                  n macro-aliases wrld state))))))))

(defun get-events (names ctx wrld state)
  (cond ((endp names) (value nil))
        ((null (getprop (car names) 'absolute-event-number nil
                        'current-acl2-world wrld))
         (er soft ctx
             "The symbol ~x0 does not name an event."
             (car names)))
        (t (let ((ev (get-event (car names) wrld)))
             (cond ((or (atom ev)
                        (eq (car ev) 'ENTER-BOOT-STRAP-MODE))
                    (er soft ctx
                        "The symbol ~x0 appears to name a built-in event."
                        (car names)))
                   (t (er-let* ((rest (get-events (cdr names) ctx wrld state)))
                        (value (cons ev rest)))))))))

(defmacro with-supporters (local-event &rest events)
  (mv-let
    (names events)
    (cond ((not (and (true-listp local-event)
                     (eq (car local-event) 'local)
                     (consp (cdr local-event))
                     (null (cddr local-event))))
           (mv (er hard 'with-supporters
                   "The first argument of ~x0 should be of the form (LOCAL ~
                    ...), but that argument is ~x1."
                   'with-supporters local-event)
               nil))
          ((eq (car events) :names)
           (cond ((null (cdr events))
                  (mv (er hard 'with-supporters
                          "No argument was supplied for :NAMES!")
                      nil))
                 ((not (symbol-listp (cadr events)))
                  (mv (er hard 'with-supporters
                          "The value of :NAMES must be a list of symbols, ~
                           which ~x0 is not."
                          (cadr events))
                      nil))
                 (t (mv (cadr events) (cddr events)))))
          ((atom (car events))
           (mv (er hard 'with-supporters
                   "An event must be a cons, but your first event was ~x0. ~
                    Perhaps you intended to use :NAMES?" (car events))
               nil))
          ((member-eq :names (cdr events))
           (mv (er hard 'with-supporters
                   "The :NAMES keyword of WITH-SUPPORTERS must appear ~
                    immediately after the (initial) LOCAL event.")
               nil))
          (t (mv nil events)))
    `(make-event
      (let ((num (max-absolute-event-number (w state))))

; Below, we remove LOCAL from local-event for the make-event expansion, and we
; use std::defredundant-fn rather than what might seem more elegant,
; std::defredundant.  These changes are necessary in order for defredundant to
; work when including uncertified books or, more generally, when state global
; 'ld-skip-proofsp has value 'include-book.  Before 2/18/2022 we did not have
; these changes, and Eric Smith pointed out that the form (include-book
; "projects/x86isa/machine/instructions/fp/base" :dir :system) fails when
; "base" is uncertified, because of a failed call of with-supporters in that
; uncertified book.

        (er-progn (progn ,(cadr local-event) ,@events)
                  (er-let* ((fns (supporting-fns ',events nil nil num
                                                 (macro-aliases (w state))
                                                 (w state)
                                                 state))
                            (named-events
                             (get-events (sort-supporting-fns ',names (w state))
                                         'with-supporters
                                         (w state)
                                         state)))
                    (value
                     (list* 'encapsulate
                            ()
                            ',local-event
                            (append
                             named-events
                             (cons (std::defredundant-fn fns nil state)
                                   ',events))))))))))

(defmacro with-supporters-after (name &rest events)
  (declare (xargs :guard (symbolp name)))
  `(make-event
    (let ((num (getprop ',name 'absolute-event-number nil
                        'current-acl2-world (w state))))
      (cond
       ((null num)
        (er soft 'with-supporters
            "The symbol ~x0 does not seem to be the name of an event."
            ',name))
       (t (er-progn (progn ,@events)
                    (er-let* ((fns (supporting-fns ',events nil nil num
                                                   (macro-aliases (w state))
                                                   (w state)
                                                   state)))
                      (value (list* 'progn
                                    `(std::defredundant
                                       :names ,fns)
                                    ',events)))))))))

(defxdoc with-supporters
  :parents (macro-libraries)
  :short "Automatically define necessary redundant definitions from @(see
          local)ly included books"
  :long
  "<p>When @(see local) @(tsee include-book) forms are used in support of
  definitions and theorems, the resulting book or @(tsee encapsulate) event may
  be ill-formed because of missing definitions.  The macro,
  @('with-supporters'), is intended to avoid this problem.  See also @(tsee
  with-supporters-after) for a related utility.</p>

  <p>General forms:</p>

  @({
  (with-supporters local-event event-1 ... event-k)
  })

  @({
  (with-supporters local-event
                   :names (name-1 ... name-m)
                   event-1 ... event-k)
  })

  <p>where @('local-event') and each event @('event-i') and (if supplied)
  @('name-i') are @(see events) and @('local-event') is of the form @('(local
  <event>)').  The effect is the same as</p>

  @({((encapsulate () local-event EXTRA event-1 ... event-k)})

  <p>where @('EXTRA') is a sequence of events that includes the following, in
  an attempt to re-create the environment produced by @('local-event') in order
  to process each @('event-i') during the second pass of the @(tsee
  encapsulate) event.</p>

  <ul>

  <li>function definitions</li>

  <li>definitions of macros that are aliases for additional functions being
  defined; see @(see macro-aliases-table)</li>

  <li>@(tsee in-theory) events so that the rules introduced by the @('EXTRA')
  definitions are suitably enable or disabled</li>

  <li>If @(':names') is supplied, then the first events in @('EXTRA') are the
  events named by the @('name-i'), in order.</li>

  </ul>

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
  encapsulate) event.  (Recall that @(see local) events are skipped during that
  pass; see @(see encapsulate).)</p>

  <p>One solution is to move the @('include-book') form so that it appears
  non-locally in front of the @('encapsulate') event.  But we may not want to
  include other @(see events) from that book, out of concern that rules defined
  in that book could affect our proof development.</p>

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
  generated event is initially as follows.</p>

  @({
  (encapsulate
   ()
   (local (include-book \"std/lists/duplicity\"
                        :dir :system))
   (std::defredundant
     :names (duplicity-exec duplicity))
   (defthm duplicity-append
     (equal (duplicity a (append x y))
            (+ (duplicity a x) (duplicity a y)))))
  })

  <p>Notice that @('with-supporters') is implemented using the macro @(tsee
  std::defredundant).  (Also see @(see redundant-events).)  When the call above
  of @('std::defredundant') is expanded, the result is essentially as follows.
  Note that @(tsee in-theory) events are generated in an attempt to set the
  enable/disable status of each rule introduced by each function to match the
  status after the original @('include-book') event.</p>

  @({
  (encapsulate
   ()
   (set-enforce-redundancy t)
   (defun duplicity-exec (a x n)
     (declare (xargs :mode :logic :verify-guards t))
     (declare (xargs :measure (:? x)))
     (declare (xargs :guard (natp n)))
     (if (atom x)
         n
       (duplicity-exec a (cdr x)
                       (if (equal (car x) a) (+ 1 n) n))))
   (in-theory (e/d ((:type-prescription duplicity-exec)
                    (:executable-counterpart duplicity-exec))
                   ((:induction duplicity-exec)
                    (:definition duplicity-exec))))
   (defun duplicity (a x)
     (declare (xargs :mode :logic :verify-guards t))
     (declare (xargs :measure (:? x)))
     (declare (xargs :guard t))
     (mbe :logic (cond ((atom x) 0)
                       ((equal (car x) a)
                        (+ 1 (duplicity a (cdr x))))
                       (t (duplicity a (cdr x))))
          :exec (duplicity-exec a x 0)))
   (in-theory (e/d ((:type-prescription duplicity)
                    (:executable-counterpart duplicity))
                   ((:induction duplicity)
                    (:definition duplicity)))))

  })

  <p>For a second example, consider the following form from the @(see
  community-books), file @('tools/with-supporters-test-top.lisp').</p>

  @({
  (with-supporters
   (local (include-book \"with-supporters-test-sub\"))
   :names (mac1 mac1-fn)
   (defun h2 (x)
     (g3 x)))
  })

  <p>Here are the events in the locally included book.</p>

  @({
  (defun mac1-fn (x)
    x)

  (defmacro mac1 (x)
    (mac1-fn x))

  (defun g1 (x)
    (declare (xargs :guard t))
    (mac1 x))

  (defun mac2-fn-b (x)
    x)

  (defun mac2-fn (x)
    (mac2-fn-b x))

  (defmacro mac2 (x)
    (mac2-fn x))

  (add-macro-alias mac2 g2)

  (defun g2 (x)
    (declare (xargs :guard (g1 x)))
    (mac2 x))

  (defun g3 (x)
    (g2 x))
  })

  <p>Notice that @('g3') in the top-level book calls @('g2'), whose @(see
  guard) mentions @('g1').  Now although @('g1') calls the macro @('mac1'),
  @('with-supporters') is not clever enough to notice this, because it tracks
  dependencies using translated terms (see @(see term)), for which macros have
  been expanded away.  Thus, macros like @('mac1'), as well as functions used
  in their definitions (like @('mac1-fn')), must be specified explicitly.
  This specification is made with @(':names (mac1 mac1-fn)') in the call of
  @('with-supporters') above.</p>

  <p>There is an exception to this required use of the @(':names') keyword
  argument: macros that are aliases for functions that support the events.
  Returning to our example, notice that @('g3') is defined using the function
  @('g2'), which in turn calls the macro, @('mac2').  So we might expect, as
  described for @('mac1') above, that @('mac2') must be included in
  @(':names').  But fortunately, @('mac2') is a macro alias for a function that
  supports the definition of @('h2') specified in the call of
  @('with-supporters'): @('g2') supports that definition and @('mac2') is a
  macro alias for @('g2').  Thus @('mac2') and its supporting function
  @('mac2-fn') are added to the list of generated events (called @('EXTRA'),
  above).</p>

  <p>In summary, the above call of @('with-supporters') generates the following
  event.</p>

  @({
  (ENCAPSULATE NIL
                (LOCAL (INCLUDE-BOOK \"with-supporters-test-sub\"))
                (DEFUN MAC1-FN (X) X)
                (DEFMACRO MAC1 (X) (MAC1-FN X))
                (STD::DEFREDUNDANT G1 MAC2-FN-B MAC2-FN MAC2 G2 G3)
                (DEFUN H2 (X) (G3 X)))
  })

  <p>As in the first example, @('std::defredundant') generates definitions for
  the indicated names.</p>")

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
  @('with-supporters-after') does not support the @(':names') argument; that
  should be straightforward to add, if needed.)  The documentation below
  assumes familiarity with @('with-supporters').</p>

  <p>General form:</p>

  @({(with-supporters-after name event-1 ... event-k)})

  <p>where @('name') is the name of an event and @('event-i') are @(see
  events).  The effect is the same as</p>

  @({((encapsulate () EXTRA event-1 ... event-k)})

  <p>where @('EXTRA') includes redundant definitions of functions introduced
  after @('name'), as necessary, in order to avoid undefined function errors
  when processing this @(tsee encapsulate) event.  (As with
  @('with-supporters'), @('EXTRA') may also include macro aliases and their
  supporters; see @(see with-supporters) for details.)  @('EXTRA') also
  includes @(see in-theory) events so that the rules introduced by the
  @('EXTRA') definitions are suitably enable or disabled.  Consider the
  following example.</p>

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
  with-supporters) for relevant background.  Note that the present macro, like
  that one, is also implemented using the macro @(tsee std::defredundant).</p>

  @({
  (progn
   (encapsulate
    ()
    (set-enforce-redundancy t)
    (logic)
    (defun duplicity-exec (a x n)
      (declare (xargs :mode :logic :verify-guards t))
      (declare (xargs :measure (:? x)))
      (declare (xargs :guard (natp n)))
      (if (atom x)
          n
          (duplicity-exec a (cdr x)
                          (if (equal (car x) a) (+ 1 n) n))))
    (in-theory (e/d ((:type-prescription duplicity-exec)
                     (:executable-counterpart duplicity-exec))
                    ((:induction duplicity-exec)
                     (:definition duplicity-exec))))
    (defun duplicity (a x)
      (declare (xargs :mode :logic :verify-guards t))
      (declare (xargs :measure (:? x)))
      (declare (xargs :guard t))
      (mbe :logic (cond ((atom x) 0)
                        ((equal (car x) a)
                         (+ 1 (duplicity a (cdr x))))
                        (t (duplicity a (cdr x))))
           :exec (duplicity-exec a x 0)))
    (in-theory (e/d ((:type-prescription duplicity)
                     (:executable-counterpart duplicity))
                    ((:induction duplicity)
                     (:definition duplicity)))))
   (defthm duplicity-append
     (equal (duplicity a (append x y))
            (+ (duplicity a x) (duplicity a y)))))
  })")
