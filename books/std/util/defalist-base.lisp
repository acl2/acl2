; Standard Utilities Library
; Copyright (C) 2008-2014 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "STD")
(include-book "deflist-base")
(include-book "std/alists/abstract" :dir :system)

(defxdoc defalist
  :parents (std/util)
  :short "Introduce a recognizer for a typed association list (alist)."

  :long "<p>Defalist allows you to quickly introduce a recognizer for a typed
association list (e.g., @('string-nat-alistp')) and proves basic theorems about
it.</p>

<p>Unlike many ACL2 alist recognizers, the recognizers introduced by defalist
<b>do not</b>, by default, imply @('(alistp x)'), but they do imply something
like @('(cons-listp x)').  That is,</p>

<ul>
<li>We require that each element is a cons, but</li>
<li>We do not require the alists to be nil-terminated.</li>
</ul>

<p>Not requiring @('nil') termination has some advantages.  It plays well with
@(see acl2::equivalence) relations like @(see list-equiv) and @(see
acl2::alist-equiv).  It also allows you to use features of @(see
acl2::fast-alists) such as \"size hints\" and \"alist names\" (see @(see
hons-acons) for details).</p>

<p>But there is also a disadvantage.  Namely, it may be difficult to operate on
a defalist using traditional alist functions, whose @(see guard)s require @(see
alistp).  Fortunately, there are generally good alternatives to these
traditional functions with no such requirement, e.g.,:</p>

<ul>
<li>@(see acons) &rarr; @(see hons-acons) or ordinary @(see cons)es.</li>
<li>@(see assoc) &rarr; @(see hons-get) for fast alists, or @(see hons-assoc-equal)
    for ordinary alists</li>
<li>@(see strip-cars) &rarr; @(see alist-keys)</li>
<li>@(see strip-cdrs) &rarr; @(see alist-vals)</li>
</ul>

<p>General form:</p>

@({
 (defalist name formals
    &key key               ; required
         val               ; required
         guard             ; t by default
         verify-guards     ; t by default
         keyp-of-nil       ; :unknown by default
         valp-of-nil       ; :unknown by default
         true-listp        ; nil by default
         mode              ; current defun-mode by default
         already-definedp  ; nil by default
         parents           ; nil by default
         short             ; nil by default
         long              ; nil by default
         )
})

<p>For example,</p>

@({
 (defalist string-nat-alistp (x)
    :key (stringp x)
    :val (natp x))
})

<p>introduces a new function, @('string-nat-alistp'), that recognizes alists
whose keys are strings and whose values are natural numbers.  It also proves
many theorems about this new function.</p>

<p>Note that <b>x</b> is treated in a special way: it refers to the whole alist
in the formals and guards, but refers to individual keys or values in the
@(':key') and @(':val') positions.  This is similar to how @(see deflist),
@(see defprojection), and @(see defmapappend) handle @('x').</p>

<h3>Usage and Arguments</h3>

<p>Let @('pkg') be the package of @('name').  All functions, theorems, and
variables are created in this package.  One of the formals must be @('pkg::x'),
and this argument represents the alist to check.  Otherwise, the only
restriction on the formals is that you may not use the names @('pkg::a'),
@('pkg::n'), or @('pkg::y'), because we use these variables in the theorems we
generate.</p>

<p>The @(':key') and @(':val') arguments are required and should be simple
function calls involving some subset of the formals.  The basic idea is that
you write @('x') for the particular key or value that is being inspected.</p>

<p>The optional @(':guard') and @(':verify-guards') are given to the
@('defund') event that we introduce.  In other words, these are the guards that
will be used for the list recognizer, not the element recognizer.</p>

<p>The optional @(':true-listp') argument can be used to make the new
recognizer \"strict\" and only accept alists that are @('nil')-terminated; by
default the recognizer will be \"loose\" and will not pay attention to the
final <tt>cdr</tt>.  See @(see strict-list-recognizers) for further
discussion.</p>

<p>The optional @(':keyp-of-nil') (similarly @(':valp-of-nil')) keywords can be
used when @('(key-recognizer nil ...)') (similarly @('(val-recognzier nil
...)')) is always known to be @('t') or @('nil').  When it is provided,
@('defalist') can generate slightly better theorems.</p>

<p>The optional @(':already-definedp') keyword can be set if you have already
defined the function.  This can be used to generate all of the ordinary
@('defalist') theorems without generating a @('defund') event, and is useful
when you are dealing with mutually recursive recognizers.</p>

<p>The optional @(':mode') keyword can be set to @(':program') to introduce the
recognizer in program mode.  In this case, no theorems are introduced.</p>

<p>The optional @(':parents'), @(':short'), and @(':long') keywords are as in
@(see defxdoc).  Typically you only need to specify @(':parents'), perhaps
implicitly with @(see xdoc::set-default-parents), and suitable documentation
will be automatically generated for @(':short') and @(':long').  If you don't
like this documentation, you can supply your own @(':short') and/or @(':long')
to override it.</p>")

(program)
(set-state-ok t)

;; This piggybacks on deflist stuff to get a big chunk of the theorems we need.
(defun defalist-deflist-instantiate-table-thms (name formals key val kwd-alist x world)
  (b* ((table (table-alist 'acl2::listp-rules world))
       (element `(and (consp ,x)
                      ,@(and (not (eq key t))
                             `((,(car key) . ,(subst `(car ,x) x (cdr key)))))
                      ,@(and (not (eq val t))
                             `((,(car val) . ,(subst `(cdr ,x) x (cdr val)))))))
       (kwd-alist `((:negatedp . nil)
                    (:elementp-of-nil . nil)
                    . ,kwd-alist))
       (fn-subst (deflist-substitution name formals element kwd-alist x))
       (req-alist (deflist-requirement-alist kwd-alist formals element)))
    (deflist-instantiate-table-thms-aux table element name formals kwd-alist x req-alist fn-subst world)))


(defun defalist-substitution (name formals key val kwd-alist x)
  (b* ((key-negatedp (getarg :key-negatedp nil kwd-alist))
       (val-negatedp (getarg :val-negatedp nil kwd-alist))
       (true-listp (getarg :true-listp nil kwd-alist)))
    `((acl2::keytype-p ,(if key-negatedp
                            `(lambda (,x) (not ,key))
                          `(lambda (,x) ,key)))
      (acl2::non-keytype-p ,(if key-negatedp
                                `(lambda (,x) ,key)
                              `(lambda (,x) (not ,key))))
      (acl2::valtype-p ,(if val-negatedp
                            `(lambda (,x) (not ,val))
                          `(lambda (,x) ,val)))
      (acl2::non-valtype-p ,(if val-negatedp
                                `(lambda (,x) ,val)
                              `(lambda (,x) (not ,val))))
      (acl2::keyval-alist-p (lambda (,x) (,name . ,formals)))
      (acl2::keyval-alist-final-cdr-p ,(if true-listp
                                           'not
                                         '(lambda (x) t))))))

(defun defalist-requirement-alist (kwd-alist formals key val)
  (b* ((key-negatedp (getarg :key-negatedp nil kwd-alist))
       (val-negatedp (getarg :val-negatedp nil kwd-alist))
       (key-simple (simple-fncall-p-hack key))
       (val-simple (simple-fncall-p-hack val))
       (true-listp (getarg :true-listp nil kwd-alist))
       (keyp-of-nil (getarg :keyp-of-nil :unknown kwd-alist))
       (valp-of-nil (getarg :valp-of-nil :unknown kwd-alist))
       (single-var (eql (len formals) 1))
       (cheap      (getarg :cheap      nil kwd-alist)))
    `((acl2::keytype-p-of-nil . ,(eq keyp-of-nil (not key-negatedp)))
      (acl2::not-keytype-p-of-nil . ,(eq keyp-of-nil key-negatedp))
      (acl2::valtype-p-of-nil . ,(eq valp-of-nil (not val-negatedp)))
      (acl2::not-valtype-p-of-nil . ,(eq valp-of-nil val-negatedp))
      (acl2::key-negatedp . ,key-negatedp)
      (acl2::val-negatedp . ,val-negatedp)
      (acl2::keytype-simple . ,key-simple)
      (acl2::valtype-simple . ,val-simple)
      (acl2::true-listp . ,true-listp)
      (acl2::single-var . ,single-var)
      (acl2::cheap      . ,cheap))))

(mutual-recursion
 (defun defalist-thmbody-subst (body key val name formals x key-negatedp val-negatedp)
   (if (atom body)
       body
     (case (car body)
       (acl2::keytype-p
        (if (eq key t)
            t
          (let ((call (cons (car key) (subst (cadr body) x (cdr key)))))
            (if key-negatedp
                (list 'not call)
              call))))
       (acl2::non-keytype-p
        (if (eq key t)
            nil
          (let ((call (cons (car key) (subst (cadr body) x (cdr key)))))
            (if key-negatedp
                call
              (list 'not call)))))
       (acl2::valtype-p
        (if (eq val t)
            t
          (let ((call (cons (car val) (subst (cadr body) x (cdr val)))))
            (if val-negatedp
                (list 'not call)
              call))))
       (acl2::non-valtype-p
        (if (eq val t)
            nil
          (let ((call (cons (car val) (subst (cadr body) x (cdr val)))))
            (if val-negatedp
                call
              (list 'not call)))))
       (acl2::keyval-alist-p
        (cons name (subst (cadr body) x formals)))
       (t (if (symbolp (car body))
              (cons (car body)
                    (defalist-thmbody-list-subst (cdr body) key val name formals x key-negatedp val-negatedp))
            (defalist-thmbody-list-subst body key val name formals x key-negatedp val-negatedp))))))
 (defun defalist-thmbody-list-subst (body key val name formals x key-negatedp val-negatedp)
   (if (atom body)
       body
     (cons (defalist-thmbody-subst (car body) key val name formals x key-negatedp val-negatedp)
           (defalist-thmbody-list-subst (cdr body) key val name formals x key-negatedp val-negatedp)))))


(defun defalist-thmname-subst (thmname name key val)
  (b* ((thmname (symbol-name thmname))
       (keyp (and (consp key) (car key)))
       (valp (and (consp val) (car val)))
       (subst-list `(("KEYVAL-ALIST-P" . ,(symbol-name name))
                     ("KEYVAL-ALIST" . ,(symbol-name name))
                     ,@(and (consp key)
                            `(("KEYTYPE-P" . ,(symbol-name keyp))
                              ("KEYTYPE" . ,(symbol-name keyp))))
                     ,@(and (consp val)
                            `(("VALTYPE-P" . ,(symbol-name valp))
                              ("VALTYPE" . ,(symbol-name valp)))))))
    (intern-in-package-of-symbol
     (dumb-str-sublis subst-list thmname)
     name)))


(defun defalist-ruleclasses-subst (rule-classes key val name formals x key-negatedp val-negatedp)
  (b* (((when (atom rule-classes)) rule-classes)
       (class (car rule-classes))
       ((when (atom class))
        (cons class
              (defalist-ruleclasses-subst
                (cdr rule-classes) key val name formals x key-negatedp val-negatedp)))
       (corollary-look (assoc-keyword :corollary (cdr class)))
       ((unless corollary-look)
        (cons class
              (defalist-ruleclasses-subst
                (cdr rule-classes) key val name formals x key-negatedp val-negatedp)))
       (prefix (take (- (len class) (len corollary-look)) class))
       (corollary-term (defalist-thmbody-subst
                         (cadr corollary-look)
                         key val name formals x key-negatedp val-negatedp)))
    (cons (append prefix `(:corollary ,corollary-term . ,(cddr corollary-look)))
          (defalist-ruleclasses-subst
            (cdr rule-classes) key val name formals x key-negatedp val-negatedp))))

(defun defalist-instantiate (table-entry key val name formals kwd-alist x
                                        req-alist fn-subst world)
  (b* (((cons inst-thm alist) table-entry)
       ((when (not alist)) nil)
       (alist (and (not (eq alist t)) alist))
       (req-look (assoc :requirement alist))
       (req-ok (or (not req-look)
                   (generic-eval-requirement (cadr req-look) req-alist)))
       ((unless req-ok) nil)
       (thmname-base (let ((look (assoc :name alist)))
                       (if look (cadr look) inst-thm)))
       (thmname (defalist-thmname-subst thmname-base name key val))
       (body (let ((look (assoc :body alist)))
               (if look (cadr look)
                 (fgetprop inst-thm 'acl2::untranslated-theorem nil world))))
       ((when (not body)) (er hard? 'defalist-instantiate
                              "Bad defalist table entry: ~x0~%" inst-thm))
       (rule-classes
        (b* ((cheap-look (and (getarg :cheap nil kwd-alist)
                              (assoc :cheap-rule-classes alist)))
             ((when cheap-look) (cadr cheap-look))
             (look (assoc :rule-classes alist)))
          (if look (cadr look) (fgetprop inst-thm 'acl2::classes nil world))))
       (key-negatedp (getarg :key-negatedp nil kwd-alist))
       (val-negatedp (getarg :val-negatedp nil kwd-alist))
       (rule-classes (defalist-ruleclasses-subst rule-classes key val name formals x key-negatedp val-negatedp))
       (disable (cdr (assoc :disable alist)))
       (defthm/defthmd (if disable 'defthmd 'defthm)))
    `((,defthm/defthmd ,thmname
        ,(defalist-thmbody-subst body key val name formals x key-negatedp val-negatedp)
        :hints (("goal" :use ((:functional-instance
                               ,inst-thm
                               . ,fn-subst))))
        :rule-classes ,rule-classes))))


(defun defalist-instantiate-table-thms-aux
  (table key val name formals kwd-alist x
         req-alist fn-subst world)
  (if (atom table)
      nil
    (append (defalist-instantiate (car table) key val name formals kwd-alist x
              req-alist fn-subst world)
            (defalist-instantiate-table-thms-aux (cdr table) key val name formals kwd-alist x
              req-alist fn-subst world))))



(defun defalist-instantiate-table-thms (name formals key val kwd-alist x world)
  (b* ((table (table-alist 'acl2::alistp-rules world))
       (fn-subst (defalist-substitution name formals key val kwd-alist x))
       (req-alist (defalist-requirement-alist kwd-alist formals key val)))
    (defalist-instantiate-table-thms-aux table key val name formals kwd-alist x req-alist fn-subst world)))

(defun defalist-fn (name formals kwd-alist other-events state)
  (declare (xargs :mode :program))
  (b* (((unless (symbolp name))
        (er hard 'deflist "Name must be a symbol, but is ~x0." name))

       (mksym-package-symbol name)
       (world (w state))

       ;; Special variables that are reserved by defalist.
       (x (intern-in-package-of-symbol "X" name))
       (a (intern-in-package-of-symbol "A" name))
       (n (intern-in-package-of-symbol "N" name))
       (y (intern-in-package-of-symbol "Y" name))

       ((unless (and (symbol-listp formals)
                     (no-duplicatesp formals)))
        (er hard 'defalist
            "The formals must be a list of unique symbols, but the ~
            formals are ~x0." formals))

       ((unless (member x formals))
        (er hard 'defalist
            "The formals must contain X, but are ~x0.~%" formals))

       ((when (or (member a formals)
                  (member n formals)
                  (member y formals)))
        (er hard 'defalist
            "As a special restriction, formals may not mention a, n, ~
            or y, but the formals are ~x0." formals))

       (key (getarg :key t kwd-alist))
       ((unless (or (eq key t)
                    (and (consp key)
                         (symbolp (car key)))))
        (er hard 'defalist
            "The key recognizer must be a function applied ~
             to the formals, but is ~x0." key))
       (keyp         (if (eq key t) t (car key)))
       (key-formals  (if (eq key t) nil (cdr key)))

       (val (getarg :val t kwd-alist))
       ((unless (or (eq val t)
                    (and (consp val)
                         (symbolp (car val)))))
        (er hard 'defalist
            "The value recognizer must be a function applied ~
             to the formals, but is ~x0." val))
       (valp         (if (eq val t) t (car val)))
       (val-formals  (if (eq val t) nil (cdr val)))

       (keyp-of-nil (if (eq key t) t (getarg :keyp-of-nil :unknown kwd-alist)))
       ((unless (member keyp-of-nil '(t nil :unknown)))
        (er hard? 'defalist
            "keyp-of-nil must be a boolean or :unknown."))

       (valp-of-nil (if (eq val t) t (getarg :valp-of-nil :unknown kwd-alist)))
       ((unless (member valp-of-nil '(t nil :unknown)))
        (er hard? 'defalist
            "valp-of-nil must be a boolean or :unknown."))

       (true-listp (getarg :true-listp nil kwd-alist))
       (guard (getarg :guard t kwd-alist))
       (verify-guards (getarg :verify-guards t kwd-alist))
       ((unless (booleanp verify-guards))
        (er hard 'defalist
            ":verify-guards must be a boolean, but is ~x0."
            verify-guards))

       (mode (getarg :mode (default-defun-mode world) kwd-alist))
       ((unless (or (eq mode :logic)
                    (eq mode :program)))
        (er hard 'defalist
            ":mode must be one of :logic or :program, but is ~x0." mode))

       (already-definedp (getarg :already-definedp nil kwd-alist))
       ((unless (or (eq mode :logic)
                    (not already-definedp)))
        (er hard 'defalist
            ":mode :program and already-definedp cannot be used together."))

       (short (getarg :short nil kwd-alist))
       (long  (getarg :long nil kwd-alist))
       (parents-p (assoc :parents kwd-alist))

       (squelch-docs-p (and already-definedp
                            (not short)
                            (not long)
                            (not (cdr parents-p))))

       (parents (and (not squelch-docs-p)
                     (if parents-p
                         (cdr parents-p)
                       (or (xdoc::get-default-parents world)
                           '(acl2::undocumented)))))

       (short (and (not squelch-docs-p)
                   (or short
                       (and parents
                            (concatenate 'string
                                         "@(call " (xdoc::full-escape-symbol name)
                                         ") recognizes association lists where every key satisfies @(see? "
                                         (xdoc::full-escape-symbol keyp)
                                         ") and each value satisfies @(see? "
                                         (xdoc::full-escape-symbol valp) ").")))))

       (long (and (not squelch-docs-p)
                  (or long
                      (and parents
                           (concatenate 'string "<p>This is an ordinary @(see std::defalist).</p>"
                                        "@(def " (xdoc::full-escape-symbol name) ")")))))

       (rest (append (getarg :rest nil kwd-alist)
                     other-events))

       (def (if already-definedp
                nil
              `((defund ,name (,@formals)
                  (declare (xargs :guard ,guard
                                  :verify-guards ,verify-guards
                                  :mode ,mode
                                  ;; We tell ACL2 not to normalize because
                                  ;; otherwise type reasoning can rewrite the
                                  ;; definition, and ruin some of our theorems
                                  ;; below, e.g., when KEYP is known to always be
                                  ;; true.
                                  :normalize nil
                                  ))
                  (if (consp ,x)
                      (and (consp (car ,x))
                           ,@(and (not (eq key t))
                                  `((,keyp ,@(subst `(caar ,x) x key-formals))))
                           ,@(and (not (eq val t))
                                  `((,valp ,@(subst `(cdar ,x) x val-formals))))
                           (,name ,@(subst `(cdr ,x) x formals)))
                    ,(if true-listp
                         `(null ,x)
                       t))))))

       ((when (eq mode :program))
        `(defsection ,name
           ,@(and (or squelch-docs-p parents-p parents) `(:parents ,parents))
           ,@(and short   `(:short ,short))
           ,@(and long    `(:long ,long))
           ,@(and squelch-docs-p '(:no-xdoc-override t))
           (program)
           ,@def
           ,@rest))

       (theory-hack      (getarg :theory-hack      nil      kwd-alist))
       (events
        `((logic)
          (logic)
          (set-inhibit-warnings "theory" "free" "non-rec") ;; Note: implicitly local

          (local
           (encapsulate
             ()
             ;; FAUGH.  It's horrible to get this to work in all cases.
             ;;
             ;; See defalist-tests: if we have something like ALLP or NONEP, ACL2
             ;; can "helpfully" reduce them for us during preprocessing and then
             ;; rejects our rules because they look like we're trying to prove
             ;; (booleanp t) or (booleanp nil).
             ;;
             ;; To prevent that from happening, we have to turn off at least the
             ;; tau system and the type-prescription rules for keyp/valp.  But we
             ;; can't even do *THAT* reliably, because not all functions have
             ;; type-prescriptions.  (Woah, really?  Yes really: for instance,
             ;; built-ins like stringp.)
             ;;
             ;; So, as a horrible workaround, I'll prove these with rule-classes
             ;; nil and then re-prove them in the nil theory.

             ,@(and (not (eq key t))
                    `((local (defthm ,(mksym 'booleanp-of- keyp '-for- name '-key-lemma)
                               (or (equal (,keyp ,@key-formals) t)
                                   (equal (,keyp ,@key-formals) nil))
                               :rule-classes nil))))

             ,@(and (not (eq val t))
                    `((local (defthm ,(mksym 'booleanp-of- valp '-for- name '-val-lemma)
                               (or (equal (,valp ,@val-formals) t)
                                   (equal (,valp ,@val-formals) nil))
                               :rule-classes nil))))

             ,@(and (not (eq keyp-of-nil :unknown))
                    (not (eq key t))
                    `((local (defthm ,(mksym keyp '-of-nil-for- name '-key-lemma)
                               (equal (,keyp ,@(subst ''nil x key-formals))
                                      ',keyp-of-nil)
                               :rule-classes nil))))

             ,@(and (not (eq valp-of-nil :unknown))
                    (not (eq val t))
                    `((local (defthm ,(mksym valp '-of-nil-for- name '-val-lemma)
                               (equal (,valp ,@(subst ''nil x val-formals))
                                      ',valp-of-nil)
                               :rule-classes nil))))

             (local (in-theory nil))

             ,@(and (not (eq key t))
                    `((defthm ,(mksym 'booleanp-of- keyp '-for- name '-key)
                        (or (equal (,keyp ,@key-formals) t)
                            (equal (,keyp ,@key-formals) nil))
                        :rule-classes :type-prescription
                        :hints(("Goal" :by ,(mksym 'booleanp-of- keyp '-for- name '-key-lemma))))))

             ,@(and (not (eq val t))
                    `((defthm ,(mksym 'booleanp-of- valp '-for- name '-val)
                        (or (equal (,valp ,@val-formals) t)
                            (equal (,valp ,@val-formals) nil))
                        :rule-classes :type-prescription
                        :hints(("Goal" :by ,(mksym 'booleanp-of- valp '-for- name '-val-lemma))))))

             ,@(and (not (eq keyp-of-nil :unknown))
                    (not (eq key t))
                    `((maybe-defthm-as-rewrite
                       ,(mksym keyp '-of-nil-for- name '-key)
                       (equal (,keyp ,@(subst ''nil x key-formals))
                              ',keyp-of-nil)
                       :hints(("Goal" :by ,(mksym keyp '-of-nil-for-
                                                  name '-key-lemma))))))

             ,@(and (not (eq valp-of-nil :unknown))
                    (not (eq val t))
                    `((maybe-defthm-as-rewrite
                       ,(mksym valp '-of-nil-for- name '-val)
                       (equal (,valp ,@(subst ''nil x val-formals))
                              ',valp-of-nil)
                       :hints(("Goal" :by ,(mksym valp '-of-nil-for-
                                                  name '-val-lemma))))))
             ))

          ,@def

          (local (in-theory (theory 'minimal-theory)))
          (local (in-theory (disable (:executable-counterpart tau-system))))
          (local (in-theory (enable ;; deflist-support-lemmas
                             ,name
                             ,@(and (not (eq key t))
                                    `(,(mksym 'booleanp-of- keyp '-for- name '-key)))
                             ,@(and (not (eq val t))
                                    `(,(mksym 'booleanp-of- valp '-for- name '-val)))
                             (:type-prescription ,name))))
          (local (enable-if-theorem ,(mksym keyp '-of-nil-for- name '-key)))
          (local (enable-if-theorem ,(mksym valp '-of-nil-for- name '-val)))
          ,@theory-hack

; basic deflist style theorems ------------------------------------------------

          ,@(defalist-deflist-instantiate-table-thms name formals key val kwd-alist x world)
          ,@(defalist-instantiate-table-thms name formals key val kwd-alist x world))))

    `(defsection ,name
       ,@(and (or squelch-docs-p parents-p parents) `(:parents ,parents))
       ,@(and short   `(:short ,short))
       ,@(and long    `(:long ,long))
       ,@(and squelch-docs-p '(:no-xdoc-override t))
       (encapsulate ()
         . ,events)

       . ,(and rest
               `((value-triple (cw "Defalist: submitting /// events.~%"))
                 (with-output
                   :stack :pop
                   (progn
                     (local (in-theory (enable ,name)))
                     . ,rest)))))))

(defconst *defalist-valid-keywords*
  '(:key
    :val
    :cheap
    :guard
    :verify-guards
    :guard-debug
    :guard-hints
    :already-definedp
    :keyp-of-nil
    :valp-of-nil
    :mode
    :parents
    :short
    :long
    :true-listp
    :rest
    :verbosep
    :theory-hack))

(defmacro defalist (name formals &rest args)
  (b* ((__function__ 'defalist)
       ((unless (symbolp name))
        (raise "Name must be a symbol."))
       (ctx (list 'defalist name))
       ((mv main-stuff other-events) (split-/// ctx args))
       ((mv kwd-alist extra-args)
        (extract-keywords ctx *defalist-valid-keywords* main-stuff nil))
       ((when extra-args)
        (raise "Wrong number of non-keyword arguments to defalist."))
       (verbosep (getarg :verbosep nil kwd-alist)))
    `(with-output
       :stack :push
       ,@(if verbosep
             nil
           '(:gag-mode t :off (acl2::summary
                               acl2::observation
                               acl2::prove
                               acl2::proof-tree
                               acl2::event)))
       (make-event
        `(progn ,(defalist-fn ',name ',formals ',kwd-alist ',other-events state)
                (value-triple '(defalist ,',name)))))))
