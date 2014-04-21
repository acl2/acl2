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

(defun supporting-fns (events ev-names acc-names n wrld state)

; Initially ev-names and acc-names is nil.  We return all functions with
; absolute-event-number exceeding n that support events in the given list of
; events, where wrld is (w state).

  (cond ((endp events) (value (sort-supporting-fns
                               (set-difference-eq acc-names ev-names)
                               wrld)))
        (t (er-let* ((x (macroexpand-till-event (car events) state)))
             (cond
              ((null x)
               (supporting-fns (cdr events) ev-names acc-names n wrld state))
              (t
               (let* ((name (cadr x))
                      (formula (and (symbolp name)
                                    (formula name nil wrld)))
                      (guard (and (symbolp name)
                                  (getprop name 'guard nil 'current-acl2-world
                                           wrld))))
                 (supporting-fns
                  (cdr events)
                  (cons name ev-names)
                  (cond (formula
                         (new-fns (instantiable-ancestors-with-guards
                                   (new-fns (all-fnnames1 nil
                                                          formula
                                                          (and guard
                                                               (all-fnnames guard)))
                                            n wrld nil)
                                   wrld
                                   nil)
                                  n wrld acc-names))
                        (t acc-names))
                  n
                  wrld
                  state))))))))

(defmacro with-supporters (local-event &rest events)
  `(make-event
    (let ((num (max-absolute-event-number (w state))))
      (er-progn (progn ,local-event ,@events)
                (er-let* ((fns (supporting-fns ',events nil nil num
                                               (w state) state)))
                  (value (list* 'encapsulate
                                ()
                                ',local-event
                                (cons 'std::defredundant fns)
                                ',events)))))))

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
                                                   (w state) state)))
                      (value (list* 'progn
                                    (cons 'std::defredundant fns)
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

  <p>General form:</p>

  @({(with-supporters local-event event-1 ... event-k)})

  <p>where @('local-event') and event @('event-i') are @(see events) and
  @('local-event') is @(see local).  The effect is the same as</p>

  @({((encapsulate () local-event EXTRA event-1 ... event-k)})

  <p>where @('EXTRA') includes redundant definitions of functions as necessary,
  in order to avoid undefined function errors when processing this @(tsee
  encapsulate) event.  @('EXTRA') also includes @(see in-theory) events so that
  the rules introduced by the @('EXTRA') definitions are suitably enable or
  disabled.  We now illustrate with an example.</p>

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
  function, @('duplicity-exec'), so its definition is needed as well.
  Moreover, @(tsee in-theory) events are generated in an attempt to set the
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

  <p>This macro is implemented using the macro @(tsee std::defredundant).  Also see
  @(see redundant-events).</p>")

(defxdoc with-supporters-after
  :parents (macro-libraries)
  :short "Automatically define necessary redundant definitions from after a
  specified event"
  :long
  "<p>When @(see local) @(tsee include-book) forms are used in support of
  definitions and theorems, the resulting book or @(tsee encapsulate) event may
  be ill-formed because of missing definitions.  The macro,
  @('with-supporters-after'), is intended to avoid this problem.</p>

  <p>See @(tsee with-supporters) for a related utility.  The documentation
  below assumes familiarity with that macro.</p>

  <p>General form:</p>

  @({(with-supporters-after name event-1 ... event-k)})

  <p>where @('name') is the name of an event and @('event-i') are @(see
  events).  The effect is the same as</p>

  @({((encapsulate () EXTRA event-1 ... event-k)})

  <p>where @('EXTRA') includes redundant definitions of functions introduced
  after @('name'), as necessary, in order to avoid undefined function errors
  when processing this @(tsee encapsulate) event.  @('EXTRA') also includes
  @(see in-theory) events so that the rules introduced by the @('EXTRA')
  definitions are suitably enable or disabled.  Consider the following
  example.</p>

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
