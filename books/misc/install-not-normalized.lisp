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

(defun install-not-normalized-name (name)
  (declare (xargs :guard (symbolp name)))
  (intern-in-package-of-symbol (concatenate 'string
                                            (symbol-name name)
                                            "$NOT-NORMALIZED")
                               name))

(defun install-not-normalized-fn-1 (name wrld clique defthm-name)
  (declare (xargs :guard (and (symbolp name)
                              (symbolp defthm-name)
                              (plist-worldp wrld))))
  (let* ((formals (formals name wrld))
         (body (getprop name 'unnormalized-body nil 'current-acl2-world wrld))
         (defthm-name (or defthm-name
                          (install-not-normalized-name name)))
         (controller-alist (let* ((def-bodies
                                    (getprop name 'def-bodies nil
                                             'current-acl2-world wrld))
                                  (def-body ; (def-body name wrld)
                                    (and (true-listp def-bodies)
                                         (car def-bodies))))
                             (and (weak-def-body-p def-body) ; for guard proof
                                  (access def-body def-body :controller-alist)))))
    `((defthm ,defthm-name
        (equal (,name ,@formals)
               ,body)
        :hints (("Goal" :by ,name))
        :rule-classes ((:definition :install-body t
                                    ,@(and clique
                                           (list :clique
                                                 clique))
                                    ,@(and clique
                                           controller-alist
                                           (list :controller-alist
                                                 controller-alist)))))
      (in-theory (disable ,name)))))

(defun install-not-normalized-fn-lst (fns wrld all-fns defthm-name-alist)
  (declare (xargs :guard (and (symbol-listp fns)
                              (symbol-alistp defthm-name-alist)
                              (symbol-listp (strip-cdrs defthm-name-alist))
                              (plist-worldp wrld))))
  (cond
   ((endp fns)
    nil)
   (t (append (install-not-normalized-fn-1 (car fns) wrld all-fns
                                           (cdr (assoc-eq (car fns)
                                                          defthm-name-alist)))
              (install-not-normalized-fn-lst (cdr fns) wrld all-fns
                                             defthm-name-alist)))))

(defun install-not-normalized-fn (name wrld allp defthm-name)
  (declare (xargs :guard (and (symbolp name)
                              (plist-worldp wrld))))
  (let* ((ctx 'install-not-normalized)
         (fns (getprop name 'recursivep nil 'current-acl2-world wrld))
         (defthm-name-alist
           (and defthm-name
                (cond ((symbolp defthm-name)
                       (list (cons name defthm-name)))
                      ((not (and (symbol-alistp defthm-name)
                                 (symbol-listp
                                  (strip-cdrs defthm-name))))
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
                                     wrld fns defthm-name-alist))
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

(local (include-book "misc/eval" :dir :system))

(defmacro my-test (&rest forms)
  `(local (encapsulate
            ()
            (local (in-theory (current-theory :here))) ; avoid redundancy
            (local (progn ,@forms)))))

; Example (challenge supplied by Eric Smith):

(my-test

(defun return-nil (x) (declare (ignore x)) nil)

(defun foo (x) (return-nil x))

(must-fail
 (fn-is-body foo
             :hints (("Goal" :in-theory '(foo)))))

(must-fail
 (fn-is-body foo
             :hints (("Goal"
                      :expand ((foo x))
                      :in-theory (theory 'minimal-theory)))))

(install-not-normalized foo)

(must-succeed
 (fn-is-body foo
             :hints (("Goal" :in-theory '(foo$not-normalized)))))

(must-succeed
 (fn-is-body foo
             :hints (("Goal"
                      :expand ((foo x))
                      :in-theory (theory 'minimal-theory)))))
)

; As above, but with the default name supplied explicitly.

(my-test

(defun return-nil (x) (declare (ignore x)) nil)

(defun foo (x) (return-nil x))

(install-not-normalized foo :defthm-name 'foo$not-normalized)

(must-succeed
 (fn-is-body foo
             :hints (("Goal" :in-theory '(foo$not-normalized)))))

(must-succeed
 (fn-is-body foo
             :hints (("Goal"
                      :expand ((foo x))
                      :in-theory (theory 'minimal-theory)))))
)

; As above, but with a name supplied explicitly that is not the default.

(my-test

(defun return-nil (x) (declare (ignore x)) nil)

(defun foo (x) (return-nil x))

(install-not-normalized foo :defthm-name 'foo-is-unnormalized-body)

(must-succeed
 (fn-is-body foo
             :hints (("Goal" :in-theory '(foo-is-unnormalized-body)))))

(must-succeed
 (fn-is-body foo
             :hints (("Goal"
                      :expand ((foo x))
                      :in-theory (theory 'minimal-theory)))))
)

; Recursion example:

(my-test

(defun my-t () t)
(defun my-nil () nil)
(defun my-zero () 0)

(defun f-norm (x)
  (if (my-t)
      (if (consp x)
          (cons (car x) (f-norm (cdr x)))
        (my-zero))
    (my-nil)))

(must-fail
 (fn-is-body f-norm
             :hints (("Goal" :in-theory '(f-norm)))))

(must-fail
 (fn-is-body f-norm
             :hints (("Goal"
                      :expand ((f-norm x))
                      :in-theory (theory 'minimal-theory)))))

(install-not-normalized f-norm)

(must-succeed
 (fn-is-body f-norm
             :hints (("Goal" :in-theory '(f-norm$not-normalized)))))

(must-succeed
 (fn-is-body f-norm
             :hints (("Goal"
                      :expand ((f-norm x))
                      :in-theory (theory 'minimal-theory)))))
)

; As above, but with the default name supplied explicitly.

(my-test

(defun my-t () t)
(defun my-nil () nil)
(defun my-zero () 0)

(defun f-norm (x)
  (if (my-t)
      (if (consp x)
          (cons (car x) (f-norm (cdr x)))
        (my-zero))
    (my-nil)))

(install-not-normalized f-norm :defthm-name 'f-norm$not-normalized)

(must-succeed
 (fn-is-body f-norm
             :hints (("Goal" :in-theory '(f-norm$not-normalized)))))

(must-succeed
 (fn-is-body f-norm
             :hints (("Goal"
                      :expand ((f-norm x))
                      :in-theory (theory 'minimal-theory)))))
)

; As above, but with a name supplied explicitly that is not the default.

(my-test

(defun my-t () t)
(defun my-nil () nil)
(defun my-zero () 0)

(defun f-norm (x)
  (if (my-t)
      (if (consp x)
          (cons (car x) (f-norm (cdr x)))
        (my-zero))
    (my-nil)))

(install-not-normalized f-norm :defthm-name 'f-norm-alt-def)

(must-succeed
 (fn-is-body f-norm
             :hints (("Goal" :in-theory '(f-norm-alt-def)))))

(must-succeed
 (fn-is-body f-norm
             :hints (("Goal"
                      :expand ((f-norm x))
                      :in-theory (theory 'minimal-theory)))))
)

; Mutual-recursion example:

(my-test

(defun my-t () t)
(defun my-nil () nil)
(defun my-zero () 0)

(mutual-recursion

 (defun f1-norm (x)
   (if (my-t)
       (if (consp x)
           (cons (car x) (f2-norm (cdr x)))
         (my-zero))
     (my-nil)))

 (defun f2-norm (x)
   (if (my-t)
       (if (consp x)
           (cons (car x) (f1-norm (cdr x)))
         (my-zero))
     (my-nil)))
 )

(must-fail
 (fn-is-body f1-norm
             :hints (("Goal" :in-theory '(f1-norm)))))

(must-fail
 (fn-is-body f1-norm
             :hints (("Goal"
                      :expand ((f1-norm x))
                      :in-theory (theory 'minimal-theory)))))

(install-not-normalized f1-norm)

(must-succeed
 (fn-is-body f1-norm
             :hints (("Goal" :in-theory '(f1-norm$not-normalized)))))

(must-succeed
 (fn-is-body f1-norm
             :hints (("Goal"
                      :expand ((f1-norm x))
                      :in-theory (theory 'minimal-theory)))))

; f2 is handled too:

(must-succeed
 (fn-is-body f2-norm
             :hints (("Goal" :in-theory '(f2-norm$not-normalized)))))

(must-succeed
 (fn-is-body f2-norm
             :hints (("Goal"
                      :expand ((f2-norm x))
                      :in-theory (theory 'minimal-theory)))))
)

; As above, but with one default name supplied explicitly.

(my-test

(defun my-t () t)
(defun my-nil () nil)
(defun my-zero () 0)

(mutual-recursion

 (defun f1-norm (x)
   (if (my-t)
       (if (consp x)
           (cons (car x) (f2-norm (cdr x)))
         (my-zero))
     (my-nil)))

 (defun f2-norm (x)
   (if (my-t)
       (if (consp x)
           (cons (car x) (f1-norm (cdr x)))
         (my-zero))
     (my-nil)))
 )

(install-not-normalized f1-norm :defthm-name 'f1-norm$not-normalized)

(must-succeed
 (fn-is-body f1-norm
             :hints (("Goal" :in-theory '(f1-norm$not-normalized)))))

(must-succeed
 (fn-is-body f1-norm
             :hints (("Goal"
                      :expand ((f1-norm x))
                      :in-theory (theory 'minimal-theory)))))

; f2 is handled too:

(must-succeed
 (fn-is-body f2-norm
             :hints (("Goal" :in-theory '(f2-norm$not-normalized)))))

(must-succeed
 (fn-is-body f2-norm
             :hints (("Goal"
                      :expand ((f2-norm x))
                      :in-theory (theory 'minimal-theory)))))
)

; As above, but with a name supplied explicitly that is not the default.

(my-test

(defun my-t () t)
(defun my-nil () nil)
(defun my-zero () 0)

(mutual-recursion

 (defun f1-norm (x)
   (if (my-t)
       (if (consp x)
           (cons (car x) (f2-norm (cdr x)))
         (my-zero))
     (my-nil)))

 (defun f2-norm (x)
   (if (my-t)
       (if (consp x)
           (cons (car x) (f1-norm (cdr x)))
         (my-zero))
     (my-nil)))
 )

(install-not-normalized f1-norm :defthm-name 'f1-norm-new-def)

(must-succeed
 (fn-is-body f1-norm
             :hints (("Goal" :in-theory '(f1-norm-new-def)))))

(must-succeed
 (fn-is-body f1-norm
             :hints (("Goal"
                      :expand ((f1-norm x))
                      :in-theory (theory 'minimal-theory)))))

; f2 is handled too:

(must-succeed
 (fn-is-body f2-norm
             :hints (("Goal" :in-theory '(f2-norm$not-normalized)))))

(must-succeed
 (fn-is-body f2-norm
             :hints (("Goal"
                      :expand ((f2-norm x))
                      :in-theory (theory 'minimal-theory)))))
)

; As above, but with both names supplied explicitly that are not the default.

(my-test

(defun my-t () t)
(defun my-nil () nil)
(defun my-zero () 0)

(mutual-recursion

 (defun f1-norm (x)
   (if (my-t)
       (if (consp x)
           (cons (car x) (f2-norm (cdr x)))
         (my-zero))
     (my-nil)))

 (defun f2-norm (x)
   (if (my-t)
       (if (consp x)
           (cons (car x) (f1-norm (cdr x)))
         (my-zero))
     (my-nil)))
 )

(install-not-normalized f1-norm :defthm-name '((f1-norm . f1-norm-new-def)
                                               (f2-norm . f2-norm-new-def)))

(must-succeed
 (fn-is-body f1-norm
             :hints (("Goal" :in-theory '(f1-norm-new-def)))))

(must-succeed
 (fn-is-body f1-norm
             :hints (("Goal"
                      :expand ((f1-norm x))
                      :in-theory (theory 'minimal-theory)))))

; f2 is handled too:

(must-succeed
 (fn-is-body f2-norm
             :hints (("Goal" :in-theory '(f2-norm-new-def)))))

(must-succeed
 (fn-is-body f2-norm
             :hints (("Goal"
                      :expand ((f2-norm x))
                      :in-theory (theory 'minimal-theory)))))
)

; Mutual-recursion example, but handling only one function in the nest:

(my-test

(defun my-t () t)
(defun my-nil () nil)
(defun my-zero () 0)

(mutual-recursion

 (defun f3-norm (x)
   (if (my-t)
       (if (consp x)
           (cons (car x) (f4-norm (cdr x)))
         (my-zero))
     (my-nil)))

 (defun f4-norm (x)
   (if (my-t)
       (if (consp x)
           (cons (car x) (f3-norm (cdr x)))
         (my-zero))
     (my-nil)))
 )

(must-fail
 (fn-is-body f3-norm
             :hints (("Goal" :in-theory '(f3-norm)))))

(must-fail
 (fn-is-body f3-norm
             :hints (("Goal"
                      :expand ((f3-norm x))
                      :in-theory (theory 'minimal-theory)))))

(install-not-normalized f3-norm :allp nil) ; "nil" for "not the entire nest

(must-succeed
 (fn-is-body f3-norm
             :hints (("Goal" :in-theory '(f3-norm$not-normalized)))))

(must-succeed
 (fn-is-body f3-norm
             :hints (("Goal"
                      :expand ((f3-norm x))
                      :in-theory (theory 'minimal-theory)))))

; F4 is not handled, since we gave nestp = nil in the call above of
; install-not-normalized.

(must-fail
 (fn-is-body f4-norm
             :hints (("Goal" :in-theory '(f4-norm$not-normalized)))))

(must-fail
 (fn-is-body f4-norm
             :hints (("Goal"
                      :expand ((f4-norm x))
                      :in-theory (theory 'minimal-theory)))))
)

; As above, but with a name supplied explicitly that is not the default.

(my-test

(defun my-t () t)
(defun my-nil () nil)
(defun my-zero () 0)

(mutual-recursion

 (defun f3-norm (x)
   (if (my-t)
       (if (consp x)
           (cons (car x) (f4-norm (cdr x)))
         (my-zero))
     (my-nil)))

 (defun f4-norm (x)
   (if (my-t)
       (if (consp x)
           (cons (car x) (f3-norm (cdr x)))
         (my-zero))
     (my-nil)))
 )

(install-not-normalized f3-norm
                        :allp nil ; "nil" for "not the entire nest
                        :defthm-name 'f3-norm-new)

(must-succeed
 (fn-is-body f3-norm
             :hints (("Goal" :in-theory '(f3-norm-new)))))

(must-succeed
 (fn-is-body f3-norm
             :hints (("Goal"
                      :expand ((f3-norm x))
                      :in-theory (theory 'minimal-theory)))))

; F4 is not handled, since we gave nestp = nil in the call above of
; install-not-normalized.

(must-fail
 (fn-is-body f4-norm
             :hints (("Goal" :in-theory '(f4-norm$not-normalized)))))

(must-fail
 (fn-is-body f4-norm
             :hints (("Goal"
                      :expand ((f4-norm x))
                      :in-theory (theory 'minimal-theory)))))
)

(include-book "xdoc/top" :dir :system)

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
 trivial to fix by enabling @('foo'); but we want to support development of
 tools that leave @('foo') disabled for some reason.</p>

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
 (install-not-normalized NAME :defthm-name '((f1 . f1-def) (f2 . f1-def)))

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
 introduced with @('mutual-recursion'): @('DNAME-SPEC') is an association list
 that maps symbols to symbols.  An entry @('(F . G)') indicates that @('G') is
 the name of the @('defthm') event generated for @('f').</li>

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

 <p>For a somewhat related utility, see @(see fn-is-body).</p>

 <p>For examples, see the Community Book
 @('misc/install-not-normalized.lisp').</p>")

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
