; Copyright (C) 2016, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

(defxdoc defthmr
  :parents (defthm events kestrel-utilities)
  :short "Submit a theorem, as a @(see rewrite) rule only if possible."
  :long "<p>@('Defthmr') stands for ``defthm rule''.  It is a macro that is
 intended to be equivalent to @(tsee defthm) &mdash; in particular, it takes
 the same arguments as @('defthm') &mdash; but when necessary it avoids the
 default of @(':rule-classes :rewrite').  Here we also document @('defthmdr'),
 which is similar to @('defthmr') but when a rewrite rule is created, it is
 immediately disabled; thus @('defthmdr') is to @('defthmd') as @('defthmr') is
 to @('defthm').</p>

 @({
 Examples:

 (defthmr symbol-name-abc
   (equal (symbol-name 'abc) \"ABC\"))

 (defthmdr symbol-name-intern$-acl2
   (equal (symbol-name (intern$ name \"ACL2\")) name))

 General Forms:

 (defthmr  name term ...) ; same keyword arguments accepted as for defthm
 (defthmdr name term ...) ; same keyword arguments accepted as for defthm
 })

 <p>In the first example above, the use of @('defthm') would cause an
 error:</p>

 @({
 ACL2 !>(defthm symbol-name-abc
          (equal (symbol-name 'abc) \"ABC\"))


 ACL2 Error in ( DEFTHM SYMBOL-NAME-ABC ...):  A :REWRITE rule generated
 from SYMBOL-NAME-ABC is illegal because it rewrites the term 'T to
 itself! ....
 })

 <p>The problem is that the internal form for the term @('(equal (symbol-name
 'abc) \"ABC\")') is, perhaps surprisingly, @(''T').  The reason is that ACL2
 evaluates calls of undefined primitives, such as @(tsee symbol-name) and
 @(tsee equal), when translating to internal form.</p>

 <p>@('Defthmr') and @('defthmdr') avoid this problem by adding
 @(':rule-classes nil') in such cases.  The two examples above thus generate
 the following events.  In the first example, the addition of @(':rule-classes nil')
 avoids the error discussed above, by instructing ACL2 to avoid the default
 behavior of attempting to store the theorem as a @(see rewrite) rule.  The
 second example has no such problem (because of the variable, @('name')), so
 ACL2 treats that @('defthmdr') simply as @('defthmd').</p>

 @({
 (defthm symbol-name-abc
   (equal (symbol-name 'abc) \"ABC\")
   :rule-classes nil)

 (defthmd symbol-name-intern$-acl2
   (equal (symbol-name (intern$ name \"ACL2\")) name))
 })

 <p>Note that if a @(':rule-classes') keyword argument is supplied, then the
 given call of @('defthmr') or @('defthmdr') simply expands directly to the
 corresponding call of @('defthm') or @('defthmd'), respectively.</p>")

(defpointer defthmdr defthmr)

(program)
(set-state-ok t)

(defun defthmr-fn (name term args disabledp ctx state)
  (let ((wrld (w state)))
    (mv-let
      (erp tterm state)
      (translate term t t t ctx wrld state) ; same call as in defthm-fn1
      (cond
       (erp (mv (msg "An ill-formed term was submitted to ~x0 (see message ~
                      above)."
                     (if disabledp 'defthmdr 'defthmr))
                nil
                state))
       (t
        (state-global-let*
         ((inhibit-output-lst *valid-output-names*))
         (mv-let
           (erp val state)

; J Moore 8/22/2020: Modified call below when new first argument, qc-flg, was
; added.  By specifying qc-flg = nil we require name to be a :rewrite rule
; rather than a :rewrite-quoted-constant rule.

           (chk-acceptable-rewrite-rule nil ; qc-flg
                                        name
                                        nil ; match-free
                                        nil ; loop-stopper
                                        tterm
                                        ctx
                                        (ens state)
                                        (w state)
                                        state)
           (declare (ignore val))
           (cond
            (erp (value `(defthm ,name ,term ,@args :rule-classes nil)))
            (t (let ((deft (if disabledp 'defthmd 'defthm)))
                 (value `(,deft ,name ,term ,@args))))))))))))

(defmacro defthmr (name term &rest args
                        &key
                        (rule-classes 'nil rule-classes-p)
                        instructions hints otf-flg)

; Warning: Keep in sync with defthmdr below.

  (declare ; using args instead
   (ignore rule-classes instructions hints otf-flg))
  (cond
   (rule-classes-p `(defthm ,name ,term ,@args))
   (t `(make-event
        (defthmr-fn ',name ',term ',args nil
          '(defthmr . ,name)
          state)))))

(defmacro defthmdr (name term &rest args
                         &key rule-classes instructions hints otf-flg)

; Warning: Keep in sync with defthmr above.

  (declare (ignore instructions hints otf-flg)) ; using args instead
  (cond
   (rule-classes `(defthmd ,name ,term ,@args))
   (t `(make-event
        (defthmr-fn ',name ',term ',args t
          '(defthmr . ,name)
          state)))))

; Here is another approach.  But it's heavy-handed somehow, and presents
; difficult challenges in controlling the output.
#||
(defmacro defthmr (name term &key hints otf-flg)
  `(make-event
    '(:or (defthm ,name
            ,term
            ,@(and hints `(:hints ,hints))
            ,@(and otf-flg `(:otf-flg ,otf-flg)))
          (defthm ,name
            ,term
            ,@(and hints `(:hints ,hints))
            ,@(and otf-flg `(:otf-flg ,otf-flg))
            :rule-classes nil))))
||#

; Examples

(logic)

(local (progn

(defthmr symbol-name-abc
   (equal (symbol-name 'abc) "ABC"))

(defthmr app-assoc
  (equal (append (append x y) z)
         (append x y z)))

(defthmr integerp-0 ; motivating example from Eric Smith
  (integerp 0))

(defthmr integerp-0-explicit-rule-classes-nil
  (integerp 0)
  :rule-classes nil)

(defthmdr car-append
  (equal (car (append x y))
         (if (consp x)
             (car x)
           (car y))))

(defthmdr integerp-0-alt
  (integerp 0)
  :otf-flg t)

))

; Just two interactive-only tests of an error here:

#+skip
(defthmr bad-1
; Undefined function.
  (foo x))

#+skip
(defthmr symbol-name-abc-bad
  (equal (symbol-name 'abc) "ABC")
  :rule-classes :rewrite)
