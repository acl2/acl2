; Copyright (C) 2012-2015 Centaur Technology
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)
(include-book "just-expand")



(defxdoc preservation-thms
  :parents (stobj)
  :short "Automation for proving that stobj-modifying functions preserve
certain properties"
  :long "
<p>A major pain when programming in logic mode with stobjs is maintaining
all the invariants necessary to prove guards.  We provide utilities to define a
set of theorem templates and to prove those theorems of a function.</p>

<p>Usage:
@({
 (def-stobj-preservation-thms fnname
    :stobjname my-stobj
    :templates my-stobj-pres-templates
    :omit (my-thm-template-x my-thm-template-y)
    :history my-stobj-pres-history) })
tries to prove a set of preservation theorems as stored in the table
<tt>my-st-pres-templates</tt>.</p>

<p>To add a new preservation theorem to the existing set, use, for example,
@({
  (add-stobj-preservation-thm
   nth-of-field-preserved
   :vars (id)
   :body `(implies (< id (my-index ,orig-stobj))
                   (equal (nth id (nth ',*fieldi* ,new-stobj))
                          (nth id (nth ',*fieldi* ,orig-stobj))))
   :hints `(,@expand/induct-hints
            (and stable-under-simplificationp
                 '(:in-theory (enable my-index))))
   :enable '(my-rule my-ruleset)
   :disable '(bad-rule other-rules)
   :rule-classes `(:rewrite (:linear :trigger-terms (,new-stobj)))
   :templates my-stobj-pres-templates
   :history my-stobj-pres-history)})
Certain placeholder variables can be used in the body, hints, enable, disable,
and rule-classes fields:
<ul>
<li><tt>orig-stobj</tt> is the variable denoting the original stobj before modification</li>
<li><tt>new-stobj</tt> is the term giving the modified stobj after the function
call: for example, @('(mv-nth 1 (modify-my-stobj my-stobj))')</li>
<li><tt>call</tt> is the call of the function without the possible
<tt>mv-nth</tt>, for example, @('(modify-my-stobj my-stobj)')</li>
<li><tt>expand/induct-hints</tt> are a generated set of hints specific to each
function for which the preservation theorem is to be proved, which expand and
 (if recursive) induct on that function</li>
<li><tt>fn</tt> is the function being worked on</li>
<li><tt>fn$</tt> is the @('deref-macro-name') of that function,
e.g. <tt>binary-logior</tt> if the <tt>fn</tt> were <tt>logior</tt></li>
<li><tt>formals</tt> is the formals of the function, possibly with some
modification to the names, but the same ones used in <tt>call</tt> and
<tt>new-stobj</tt>.</li></ul>
The <tt>:vars</tt> argument should be a list containing all of the variable
names used in the theorem body; if the formals of the function contain any of
these variables, we will use a modified list of formals that avoids them.</p>

<p>One additional keyword argument, <tt>:deps</tt>, is allowed; if provided,
this should be a list of stobj-preservation-thm template names such as
<tt>nth-node-preserved</tt> above.  This signifies that this theorem should
only be proved of functions for which the dependencies were also proved.</p>

<p>Two additional macros, @('retroactive-add-stobj-preservation-thm') and
@('retroactive-add-stobj-preservation-thm-local') are similar to
@('add-stobj-preservation-thm') but additionally prove the new theorem for all
existing functions for which other stobj-preservation-thms have already been
proved, modulo the dependencies of the new theorem. The <tt>-local</tt> version
makes the addition of the new theorem local to the current book or encapsulate,
so that nonlocal calls of <tt>def-stobj-preservation-thms</tt> won't include
it.</p>

<p>All of these macros take keyword arguments <tt>templates</tt> and
<tt>history</tt>, which should be symbols.  These symbols are the ACL2 table
names in which the templates and usage history are stored.  (The history is
used mainly for checking dependencies).  In order to simplify the usage of this
utility, we supply a macro-generating macro:
@({
 (def-stobj-preservation-macros :name hello
                                :default-stobjname my-stobj
                                :templates my-templates-table
                                :history my-history-table)})
which defines simple wrapper macros
@({
 (def-hello-preservation-thms ...)
 (add-hello-preservation-thm ...)
 (retroactive-add-hello-preservation-thm ...)
 (retroactive-add-hello-preservation-thm-local ...)})
that behave the same as the ones above, execpt that they don't take the
<tt>:templates</tt> or <tt>:history</tt> arguments and they use
<tt>my-stobj</tt> by default for <tt>:stobjname</tt>.</p>
")




(defun fix-formals-for-vars (vars formals)
  (declare (xargs :mode :program))
  (if (atom vars)
      formals
    (let* ((pos (position (car vars) formals))
           (formals (if pos
                        (update-nth
                         pos (acl2::genvar (car vars) (symbol-name (car vars))
                                           0 formals)
                         formals)
                      formals)))
      (fix-formals-for-vars (cdr vars) formals))))

;; tables:
;; stobj-preservation-thm-templates: contains templates for all the theorems
;; stobj-preservation-thm-records: contains records of which theorems were
;;                               proved for which function/stobj-name pairs

(defmacro add-stobj-preservation-record (fn stobjname tmpname histtable)
  (let ((pair (cons fn stobjname)))
    `(table ,histtable
            ',pair
            (cons ',tmpname
                  (cdr (assoc-equal ',pair
                              (table-alist ',histtable world)))))))

(defun check-deps-satisfied (deps fn stobjname histtable state)
  (declare (xargs :mode :program :stobjs state))
  (subsetp-eq deps
              (cdr (assoc-equal (cons fn stobjname)
                                (table-alist histtable (w state))))))

(defun mk-stobj-preservation-thm (fn stobjname template histtable state)
  (declare (xargs :mode :program :stobjs state))
  (b* (((acl2::nths name vars body hints ruleset deps enable disable
                    rule-classes) template)
       (world (w state))
       (fn$ (acl2::deref-macro-name fn (acl2::macro-aliases world)))
       (formals (fix-formals-for-vars vars (acl2::formals fn$ world)))
       (stobjs-out (acl2::stobjs-out fn$ world))
       (thmname (intern-in-package-of-symbol
                 (concatenate 'string (symbol-name name) "-OF-" (symbol-name fn))
                 fn))
       (call (cons fn formals))
       (new-stobj (if (cdr stobjs-out)
                      `(mv-nth ,(position stobjname stobjs-out) ,call)
                    call))
       (recp (acl2::recursivep fn$ t world))
       (expand/induct-hints
        (if (and recp (not (cdr recp)))
            `((just-induct-and-expand ,call))
          `(("Goal" . ,(append '(:do-not-induct t)
                               `(:in-theory (disable (:definition ,fn$)))
                               (if (and recp (not (cdr recp)))
                                   nil
                                 `(:expand (,call)))))))))
    `(make-event
      (b* (((unless (check-deps-satisfied ',deps ',fn ',stobjname ',histtable state))
            '(value-triple :skipped))
           (,(intern-in-package-of-symbol
              (symbol-name '?expand/induct-hints)
              histtable)
            ',expand/induct-hints)
           (,(intern-in-package-of-symbol
              (symbol-name '?new-stobj)
              histtable) ',new-stobj)
           (,(intern-in-package-of-symbol
              (symbol-name '?call)
              histtable)',call)
           (,(intern-in-package-of-symbol
              (symbol-name '?fn)
              histtable) ',fn)
           (,(intern-in-package-of-symbol
              (symbol-name '?fn$)
              histtable) ',fn$)
           (,(intern-in-package-of-symbol
              (symbol-name '?orig-stobj)
              histtable) ',stobjname)
           (,(intern-in-package-of-symbol
              (symbol-name '?formals)
              histtable) ',formals)
           (,(intern-in-package-of-symbol
              (symbol-name '?stobjs-out)
              histtable) ',stobjs-out))
        `(encapsulate nil
           (local (in-theory (e/d* ,,enable ,,disable)))
           (defthm ,',thmname
                  ,,body
                  :hints ,,hints
                  :rule-classes ,,rule-classes)
           ,@',(and ruleset
                    `((add-to-ruleset ,ruleset ,thmname)))
           (add-stobj-preservation-record ,',fn ,',stobjname ,',name ,',histtable))))))

(defun mk-stobj-preservation-thms (fn stobjname omit templates histtable state)
  (declare (xargs :mode :program :stobjs state))
  (if (atom templates)
      nil
    (if (and (cdar templates)
             (not (member (caar templates) omit)))
        (cons (mk-stobj-preservation-thm fn stobjname (car templates)
                                         histtable state)
              (mk-stobj-preservation-thms fn stobjname omit (cdr templates)
                                          histtable state))
      (mk-stobj-preservation-thms fn stobjname omit (cdr templates) histtable
                                  state))))

(defun def-stobj-preservation-thms-fn (fn stobjname omit template-table
                                          histtable state)
  (declare (xargs :mode :program :stobjs state))
  (list* 'progn
         (mk-stobj-preservation-thms
          fn stobjname omit
          (reverse
           (table-alist template-table
                        (w state)))
          histtable
          state)))

(defmacro def-stobj-preservation-thms (fn &key (stobjname 'stobj) (omit 'nil)
                                          templates history)
  `(make-event (def-stobj-preservation-thms-fn ',fn ',stobjname ',omit
                 ',templates ',history state)))

(defxdoc def-stobj-preservation-thms
  :parents (preservation-thms)
  :short "Prove the existing set of aigstobj preservation theorems for a given function"
  :long "See @(see acl2::preservation-thms) for complete documentation.")

(defun mk-stobj-preservation-thms-each-fn (records templates history state)
  (declare (xargs :mode :program :stobjs state))
  (if (atom records)
      nil
    (cons `(def-stobj-preservation-thms
             ,(caaar records) :stobjname ,(cdaar records)
             :templates ,templates :history ,history)
          (mk-stobj-preservation-thms-each-fn
           (cdr records) templates history state))))

(defun do-stobj-preservation-thms-fn (unique-name templates history state)
  (declare (xargs :mode :program :stobjs state)
           (ignore unique-name))
  (cons 'progn
        (mk-stobj-preservation-thms-each-fn
         (reverse (table-alist history (w state)))
         templates history state)))

(defmacro do-stobj-preservation-thms (unique-name &key templates history)
  `(make-event (do-stobj-preservation-thms-fn
                ',unique-name ',templates ',history
                state)))

(defun add-stobj-preservation-thm-fn (name vars body hints ruleset templates
                                           history deps enable disable rule-classes)
  (declare (ignorable history))
  `(progn (table ,templates
                 ',name
                 ',(list vars body hints ruleset deps enable disable rule-classes))
          . ,(and ruleset
                  `((def-ruleset! ,ruleset nil)))))

(defmacro add-stobj-preservation-thm (name &key vars body hints
                                           ruleset templates history
                                           deps enable disable
                                           (rule-classes ':rewrite))
  (add-stobj-preservation-thm-fn name vars body hints ruleset
                                 templates history deps enable disable rule-classes))

(defxdoc add-stobj-preservation-thm
  :parents (preservation-thms)
  :short "Add a theorem template to the def-stobj-preservation-thms database"
  :long "See @(see acl2::preservation-thms) for complete documentation.")

(defmacro retroactive-add-stobj-preservation-thm (name &rest args
                                                       &key templates history
                                                       &allow-other-keys)
  `(encapsulate nil
     (local (table ,templates nil nil :clear))
     (add-stobj-preservation-thm ,name . ,args)
     (do-stobj-preservation-thms ,name :templates ,templates :history ,history)))

(defxdoc retroactive-add-stobj-preservation-thm
  :parents (preservation-thms)
  :short "Add a theorem template to the def-stobj-preservation-thms database
and prove it about existing functions"
  :long "See @(see acl2::preservation-thms) for complete documentation.")

(defmacro retroactive-add-stobj-preservation-thm-local (name &rest args
                                                             &key templates history
                                                             &allow-other-keys)
  `(progn
     (encapsulate nil
       (local (table ,templates nil nil :clear))
       (local (add-stobj-preservation-thm ,name . ,args))
       (do-stobj-preservation-thms ,name :templates ,templates :history ,history))
     (local (add-stobj-preservation-thm ,name . ,args))))

(defxdoc retroactive-add-stobj-preservation-thm-local
  :parents (preservation-thms)
  :short "Localy add a theorem template to the def-stobj-preservation-thms database
and (nonlocally) prove it about existing functions"
  :long "See @(see acl2::preservation-thms) for complete documentation.")

(defun def-stobj-preservation-macros-fn (name default-stobjname templates history)
  (b* ((defthms-name
         (intern-in-package-of-symbol
          (concatenate
           'string "DEF-" (symbol-name name) "-PRESERVATION-THMS")
          name))
       (add-name
        (intern-in-package-of-symbol
         (concatenate
          'string "ADD-" (symbol-name name) "-PRESERVATION-THM")
         name))
       (retro-name
        (intern-in-package-of-symbol
         (concatenate
          'string "RETROACTIVE-ADD-" (symbol-name name) "-PRESERVATION-THM")
         name))
       (retro-local-name
        (intern-in-package-of-symbol
         (concatenate
          'string "RETROACTIVE-ADD-" (symbol-name name) "-PRESERVATION-THM-LOCAL")
         name)))
    `(progn
       (defmacro ,defthms-name (fn &key (stobjname ',default-stobjname) omit)
         `(def-stobj-preservation-thms
            ,fn :stobjname ,stobjname :omit ,omit
            :templates ,',templates :history ,',history))
       (defxdoc ,defthms-name
         :parents (preservation-thms)
         :short "Generated by def-stobj-preservation-macros."
         :long "See @(see acl2::preservation-thms) for complete documentation.")
       (defmacro ,add-name (name &key vars body hints ruleset deps enable
                                 disable (rule-classes ':rewrite))
         `(add-stobj-preservation-thm
           ,name :vars ,vars :body ,body :hints ,hints :deps ,deps
           :ruleset ,ruleset :templates ,',templates :history ,',history
           :enable ,enable :disable ,disable :rule-classes ,rule-classes))
       (defxdoc ,add-name
         :parents (preservation-thms)
         :short "Generated by def-stobj-preservation-macros."
         :long "See @(see acl2::preservation-thms) for complete documentation.")
       (defmacro ,retro-name (name &rest args)
         `(retroactive-add-stobj-preservation-thm
           ,name ,@args :templates ,',templates :history ,',history))
       (defxdoc ,retro-name
         :parents (preservation-thms)
         :short "Generated by def-stobj-preservation-macros."
         :long "See @(see acl2::preservation-thms) for complete documentation.")
       (defmacro ,retro-local-name (name &rest args)
         `(retroactive-add-stobj-preservation-thm-local
           ,name ,@args :templates ,',templates :history ,',history))
       (defxdoc ,retro-local-name
         :parents (preservation-thms)
         :short "Generated by def-stobj-preservation-macros."
         :long "See @(see acl2::preservation-thms) for complete documentation."))))

(defmacro def-stobj-preservation-macros (&key name default-stobjname templates
                                              history)
  (def-stobj-preservation-macros-fn name default-stobjname templates history))


