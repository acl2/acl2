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

(defun install-not-normalized-fn-1 (name wrld clique)
  (declare (xargs :guard (and (symbolp name)
                              (plist-worldp wrld))))
  (let* ((formals (formals name wrld))
         (body (getprop name 'unnormalized-body nil 'current-acl2-world wrld))
         (defthm-name (install-not-normalized-name name))
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

(defun install-not-normalized-fn-lst (fns wrld all-fns)
  (declare (xargs :guard (and fns
                              (symbol-listp fns)
                              (plist-worldp wrld))))
  (cond ((endp (cdr fns))
         (install-not-normalized-fn-1 (car fns) wrld all-fns))
        (t (append (install-not-normalized-fn-1 (car fns) wrld all-fns)
                   (install-not-normalized-fn-lst (cdr fns) wrld all-fns)))))

(defun install-not-normalized-fn (name wrld nestp)
  (declare (xargs :guard (and (symbolp name)
                              (plist-worldp wrld))))
  (let ((fns (and nestp
                  (getprop name 'recursivep nil 'current-acl2-world wrld))))
    (cond ((and (true-listp fns)
                (cdr fns))
           (cond ((symbol-listp fns)
                  (install-not-normalized-fn-lst fns wrld fns))
                 (t (er hard? 'install-not-normalized-fn
                        "Surprise!  Not a non-empty symbol-listp: ~x0"
                        fns))))
          (t (install-not-normalized-fn-1 name wrld nil)))))

(defmacro install-not-normalized (name &optional (nestp 't))

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
           (install-not-normalized-fn ',name (w state) ,nestp))))

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
            (in-theory (current-theory :here)) ; avoid redundancy
            ,@forms)))

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

(install-not-normalized f3-norm nil) ; "nil" for "not the entire nest

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

(include-book "xdoc/top" :dir :system)

(defxdoc install-not-normalized
  :parents (proof-automation)
  :short "Install an unnormalized definition"
  :long "<p>By default, ACL2 simplifies the definitions by ``normalizing''
 their bodies; see @(see normalize).  If you prefer that ACL2 avoid such
 simplification when expanding a function call, then you can assigning the
 value of @('nil') to @(tsee xargs) keyword @(':normalize') (see @(see defun))
 instead of the default value of @('t').  But that might not be a reasonable
 option, for example because the definition in question occurs in an included
 book that you prefer not to edit.  An alternative is to call a macro,
 @('install-not-normalized').</p>

 @({
 General Forms:

 (install-not-normalized NAME)
 (install-not-normalized NAME t) ; equivalent to the form above
 (install-not-normalized NAME nil)

 })

 <p>In the forms above, @('NAME') should be the name of a function symbol
 introduced with @(tsee defun) (or one of its variants, including @(tsee
 defund) and @(tsee defun-nx)).  The forms above are equivalent unless
 @('NAME') was defined together with other functions in a @(tsee
 mutual-recursion) (or @(tsee defuns)) event.  In that case, the first two
 forms install a non-normalized definition for every function symbol defined in
 that event, while the third form only handles @('NAME').  By ``handle'', we
 mean that a rule of class @('(:definition :install-body t)') is installed,
 with suitable additional fields for keywords @(':clique') and
 @(':controller-alist') when more than one name is handled.  The name of the
 rule generated for function @('F') is the symbol @('F$NOT-NORMALIZED'), that
 is, the result of modifying the @(tsee symbol-name) of @('F') by adding the
 suffix @('\"$NOT-NORMALIZED\"').  To obtain that name programmatically:</p>

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
