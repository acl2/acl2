; Copyright (C) 2015, Regents of the University of Texas
; Written by Matt Kaufmann (October, 2015)
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

#||

This comment motivates the macro install-not-normalized, defined below.

;;; Eric Smith created the following example.
(defun return-nil (x) (declare (ignore x)) nil)
(defun foo (x) (return-nil x))
;Now we can't prove that foo equals its body in a theory that just includes foo:
(thm
 (equal (foo x)
        (return-nil x))
 :hints (("Goal" :in-theory '(foo))))
;; Note that the defbodies property of foo no longer mentions return-nil, but
;; the unnormalized body of course does.

;;; This also fails:
(thm
 (equal (foo x)
        (return-nil x))
 :hints (("Goal"
          :expand ((foo x))
          :in-theory (theory 'minimal-theory))))

;;; NEW (to be generated programmatically using make-event via new utility
;;; install-not-normalized, below):
(defthm foo$not-normalized
  (equal (foo x) (return-nil x))
  :rule-classes ((:definition :install-body t)))

; This succeeds.
(thm
 (equal (foo x)
        (return-nil x))
 :hints (("Goal" :in-theory '(foo$not-normalized))))

; This succeeds.
(thm
 (equal (foo x)
        (return-nil x))
 :hints (("Goal"
          :expand ((foo x))
          :in-theory (theory 'minimal-theory))))
||#

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

; For true-listp-all-fnnames:
(local (include-book "system/all-fnnames" :dir :system))

(defun install-not-normalized-name (name)
  (declare (xargs :guard (symbolp name)))
  (intern-in-package-of-symbol (concatenate 'string
                                            (symbol-name name)
                                            "$NOT-NORMALIZED")
                               name))

(defun install-not-normalized-fn-1 (name wrld clique defthm-name)
  (declare (xargs :mode :program ; because of logical-defun call
                  :guard (and (symbolp name)
                              (symbolp defthm-name)
                              (plist-worldp wrld)
                              (symbol-listp clique))))
  (let* ((formals (formals name wrld))
         (name-def (or (logical-defun name wrld)
                       (er hard? 'install-not-normalized-fn-1
                           "There is no defun associated with the name, ~x0."
                           name)))
         (body (car (last name-def)))
         (defthm-name (or defthm-name
                          (install-not-normalized-name name)))
         (controller-alist (let* ((def-bodies
                                    (getprop name 'def-bodies nil
                                             'current-acl2-world wrld))
                                  (def-body ; (def-body name wrld)
                                    (and (true-listp def-bodies)
                                         (car def-bodies))))
                             (and ;; (weak-def-body-p def-body) ; for guard proof
                              (access def-body def-body
                                      :controller-alist))))
         (unnormalized-body
          (getprop name 'unnormalized-body nil 'current-acl2-world wrld))
         (cliquep (and clique
                       ;; (pseudo-termp unnormalized-body) ; for guard proof
                       (intersectp-eq clique (all-fnnames unnormalized-body)))))
    `((defthm ,defthm-name
        (equal (,name ,@formals)
               ,body)
        :hints (("Goal" :by ,name))
        :rule-classes ((:definition :install-body t
                                    ,@(and cliquep
                                           (list :clique
                                                 clique))
                                    ,@(and cliquep
                                           controller-alist
                                           (list :controller-alist
                                                 controller-alist)))))
      (in-theory (disable ,name)))))

(defun install-not-normalized-fn-lst (fns wrld all-fns defthm-name-doublets)
  (declare (xargs :mode :program
                  :guard (and (symbol-listp fns)
                              (symbol-listp all-fns)
                              (symbol-alistp defthm-name-doublets)
                              (doublet-listp defthm-name-doublets)
                              (symbol-listp (strip-cadrs defthm-name-doublets))
                              (plist-worldp wrld))))
  (cond ((endp fns)
         nil)
        (t (append (install-not-normalized-fn-1
                    (car fns) wrld all-fns
                    (cadr (assoc-eq (car fns) defthm-name-doublets)))
                   (install-not-normalized-fn-lst
                    (cdr fns) wrld all-fns
                    defthm-name-doublets)))))

(defun install-not-normalized-fn (name wrld allp defthm-name)
  (declare (xargs :mode :program
                  :guard (and (symbolp name)
                              (plist-worldp wrld))))
  (let* ((ctx 'install-not-normalized)
         (fns (getprop name 'recursivep nil 'current-acl2-world wrld))
         (defthm-name-doublets
           (and defthm-name
                (cond ((symbolp defthm-name)
                       (list (list name defthm-name)))
                      ((not (and (symbol-alistp defthm-name)
                                 (doublet-listp defthm-name)
                                 (symbol-listp
                                  (strip-cadrs defthm-name))))
                       (er hard? ctx
                           "Illegal :defthm-name argument: ~x0"
                           defthm-name))
                      ((and (true-listp fns) ; for guard; always true
                            (not (subsetp-eq (strip-cars defthm-name)
                                             fns)))
                       (let ((bad (set-difference-eq (strip-cars defthm-name)
                                                     fns)))
                         (er hard? ctx
                             "Illegal :defthm-name argument: ~x0.  The ~
                              name~#1~[~x1 is~/s ~&1 are~] bound in your ~
                              :defthm-name argument but not among the list of ~
                              candidate names, ~x2, for being given an ~
                              unnormalized definition."
                             defthm-name bad fns)))
                      (t defthm-name)))))
    (cond
     ((symbol-listp fns) ; for guard verification
      (install-not-normalized-fn-lst (or (and allp fns)
                                         (list name))
                                     wrld fns defthm-name-doublets))
     (t (er hard? ctx
            "Implementation error!  Not a non-empty symbol-listp: ~x0"
            fns)))))

(defmacro install-not-normalized (name &key (allp 't) defthm-name)

; Alessandro Coglio sent the following example, which failed until taking his
; suggestion to use encapsulate (originally we used progn) and call
; set-ignore-ok.

;   (include-book "misc/install-not-normalized" :dir :system)
;   (include-book "std/util/define" :dir :system)
;   (define f (x) x)
;   (install-not-normalized f) ; error

; The problem was that the DEFINE generated the term ((LAMBDA (__FUNCTION__ X)
; X) 'F X).

  (declare (xargs :guard (and name (symbolp name))))
  `(make-event
    (list* 'encapsulate
           ()
           '(set-ignore-ok t) ; see comment above
           '(set-irrelevant-formals-ok t) ; perhaps not necessary, but harmless
           (install-not-normalized-fn ',name (w state) ,allp ,defthm-name))))

(defun fn-is-body-name (name)
  (declare (xargs :guard (symbolp name)))
  (intern-in-package-of-symbol
   (concatenate 'string (symbol-name name) "$IS-BODY")
   name))

(defmacro fn-is-body (name &key hints thm-name rule-classes)
  (declare (xargs :guard (and name (symbolp name))))
  `(make-event
    (let* ((name ',name)
           (wrld (w state))
           (formals (formals name wrld))
           (body (getprop name 'unnormalized-body nil 'current-acl2-world wrld)))
      (list* 'defthm
             (or ',thm-name (fn-is-body-name name))
             (list 'equal
                   (cons name formals)
                   body)
             (append (and ',hints
                          (list :hints ',hints))
                     (list :rule-classes ',rule-classes))))))

(defxdoc install-not-normalized
  :parents (proof-automation)
  :short "Install an unnormalized definition"
  :long "@({
 General Form:

 (install-not-normalized NAME :allp FLG :defthm-name DNAME-SPEC)
 })

 <p>We explain the arguments of @('install-not-normalized') below, but first
 let us illustrate its use with an example.</p>

 <p>By default, ACL2 simplifies definitions by ``normalizing'' their bodies;
 see @(see normalize).  If you prefer that ACL2 avoid such simplification when
 expanding a function call, then you can assign the value of @('nil') to @(tsee
 xargs) keyword @(':normalize') (see @(see defun)) instead of the default value
 of @('t').  But that might not be a reasonable option, for example because the
 definition in question occurs in an included book that you prefer not to edit.
 An alternative is to call a macro, @('install-not-normalized').</p>

 <p>Consider the following example from Eric Smith.</p>

 @({
 (defun return-nil (x) (declare (ignore x)) nil)
 (defun foo (x) (return-nil x))

 ; Fails!
 (thm (equal (foo x) (return-nil x))
      :hints ((\"Goal\" :in-theory '(foo))))

 ; Also fails!
 (thm (equal (foo x) (return-nil x))
      :hints ((\"Goal\" :expand ((foo x))
                      :in-theory (theory 'minimal-theory))))
 })

 <p>The problem is that ACL2 stores @('nil') for the body of @('foo'), using
 ``type reasoning'' to deduce that @('return-nil') always returns the value,
 @('nil').  So if @('foo') is the only enabled rule, then we are left trying to
 prove that @('nil') equals @('(return-nil x)').  Of course, this example is
 trivial to fix by enabling @('return-nil'), or even just its @(':')@(tsee
 type-prescription) rule, but we want to support development of robust tools
 that manipulate functions without needing to know anything about their callees.
 </p>

 <p>To solve this problem, we can invoke @('(install-not-normalized foo)'),
 which generates the following @(':')@(tsee definition) rule.</p>

 @({
 (DEFTHM FOO$NOT-NORMALIZED
   (EQUAL (FOO X) (RETURN-NIL X))
   :HINTS ((\"Goal\" :BY FOO))
   :RULE-CLASSES ((:DEFINITION :INSTALL-BODY T)))
 })

 <p>Each of the following now succeeds.  For the second, note that the rule
 @('FOO$NOT-NORMALIZED') has installed a new body for @('FOO').</p>

 @({
 (thm (equal (foo x) (return-nil x))
      :hints ((\"Goal\" :in-theory '(foo$not-normalized))))

 (thm (equal (foo x) (return-nil x))
      :hints ((\"Goal\"
               :expand ((foo x))
               :in-theory (theory 'minimal-theory))))
 })

 <p>Let us see some more example forms; then, we discuss the general form.</p>

 @({
 Example Forms:

 (install-not-normalized NAME)

 ; Equivalent to the form above:
 (install-not-normalized NAME :allp t)

 ; Generate a definition for NAME but not for others from its mutual-recursion:
 (install-not-normalized NAME :allp nil)

 ; Give the name BAR to the new theorem:
 (install-not-normalized NAME :defthm-name 'BAR)

 ; Give the name F1-DEF to the new theorem for F1 and
 ; give the name F2-DEF to the new theorem for F2:
 (install-not-normalized NAME :defthm-name '((f1 f1-def) (f2 f1-def)))

 General Form:

 (install-not-normalized NAME :allp FLG :defthm-name DNAME-SPEC)
 })

 <p>where the keyword arguments are evaluated, but not @('NAME'), and:</p>

 <ul>

 <li>@('NAME') is the name of a function introduced by @(tsee defun) (or one of
 its variants, including @(tsee defund) and @(tsee defun-nx)), possibly using
 @(tsee mutual-recursion).</li>

 <li>@('FLG') (if supplied) is a Boolean that is relevant only in the case that
 @('NAME') was introduced using @('mutual-recursion').  When @('FLG') is nil, a
 @(tsee defthm) event is to be introduced only for @('NAME'); otherwise, there
 will be a new @('defthm') for every function defined with the same
 @('mutual-recursion') as @('NAME').</li>

 <li>@('DNAME-SPEC') (if supplied) is usually a symbol denoting the name of the
 @('defthm') event to be introduced for @('NAME'), which is
 @('NAME$NOT-NORMALIZED') by default &mdash; that is, the result of modifying
 the @(tsee symbol-name) of @('F') by adding the suffix
 @('\"$NOT-NORMALIZED\"').  Otherwise, of special interest when @('NAME') was
 introduced with @('mutual-recursion'): @('DNAME-SPEC') is a list of doublets
 of the form @('(F G)'), where @('F') is a symbol as described for @('NAME')
 above, and the symbol @('G') is the name of the @('defthm') event generated
 for the symbol @('F').</li>

 </ul>

 <p>Any such @('defthm') event has @(':')@(tsee rule-classes)
 @('((:definition :install-body t))'), with suitable additional fields when
 appropriate for keywords @(':clique') and @(':controller-alist').  To obtain
 its default name programmatically:</p>

 @({
 ACL2 !>(install-not-normalized-name 'foo)
 FOO$NOT-NORMALIZED
 ACL2 !>
 })

 <p>Remark.  Each definition installed by @('install-not-normalized') contains
 the original body, not a translated version.  (See @(see term) for a
 discussion of the the notion of ``translated term''.)</p>

 <p>For a somewhat related utility, see @(see fn-is-body).</p>

 <p>For examples, see the Community Book
 @('misc/install-not-normalized-tests.lisp').</p>")

(defxdoc fn-is-body
  :parents (proof-automation)
  :short "Prove that a function called on its formals equals its body"
  :long "@({
 General Form:

 (fn-is-body fn &key hints thm-name rule-classes)

 })

 <p>Evaluation of the form above generates a @(tsee defthm) event whose name is
 @('thm-name') &mdash; by default, the result of adding the suffix \"$IS-BODY\"
 to @('fn'), which is a function symbol.  To obtain that name
 programmatically:</p>

 @({
 ACL2 !>(fn-is-body-name 'foo)
 FOO$IS-BODY
 ACL2 !>
 })

 <p>That event is of the form @('(equal (fn x1 ... xn) <body>)'), where @('(x1
 ... xn)') is the list of formal parameters of @('fn') and @('<body>') is the
 body of @('fn').  If @(':hints') or @(':rule-classes') are supplied, they will
 be attached to the generated @('defthm') form.</p>

 <p>For a somewhat related utility, see @(see install-not-normalized).</p>

 <p>For examples, see the Community Book
 @('misc/install-not-normalized.lisp').</p>")
