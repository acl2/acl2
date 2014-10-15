; Rulesets -- Extensible alternative to theories
; Copyright (C) 2008-2012 Centaur Technology
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
; Original authors: Sol Swords and Jared Davis
;                   {sswords,jared}@centtech.com

(in-package "ACL2")
(include-book "xdoc/top" :dir :system)
(program)

(defxdoc rulesets
  :parents (theories deftheory)
  :short "Table-based alternative to ACL2's named theories."

  :long "<p>Rulesets are like @(see theories), but can be extended with
additional rules after first being defined.  That is, you can build up a
ruleset incrementally, across many books, instead of having to define it all at
once and having it be forever fixed.</p>

<p>Basic usage of rulesets is just like theories.  You can:</p>

<ul>
<li>Introduce rulesets with @(see def-ruleset)</li>
<li>Extend existing rulesets with @(see add-to-ruleset).</li>
<li>Enable/disable rulesets with @(see enable*), @(see disable*), and @(see
e/d*)</li>
</ul>

<p>When we define a new package @('FOO'), we often set up @('FOO::enable') as
an alias for @('enable*'), to make using rulesets more convenient.</p>

<p>Advanced users can do some nifty things with rulesets, e.g., you can have a
superior ruleset that contains other rulesets, and it will grow as you add
rules to the contained rulesets.</p>")

; BOZO this documentation is incomplete and doesn't really explain ruleset
; designators and fancy things like rules-of-class.  Oh well, maybe someday.

(defun get-ruleset (name world)
  (let* ((ruleset-alist (table-alist 'ruleset-table world)))
    (cdr (assoc name ruleset-alist))))

(defmacro ruleset (name)
  `(get-ruleset ,name world))

(defun is-ruleset (name world)
  (let* ((ruleset-alist (table-alist 'ruleset-table world)))
    (consp (assoc name ruleset-alist))))

(defun ruleset-designatorp (x world)
  (cond ((rule-name-designatorp x (macro-aliases world) world))
        ((symbolp x)
         (or (is-ruleset x world)
             (cw "~
**NOTE**:~%~x0 is not a rune, theory name, or ruleset name.~%" x)))
        (t (and (consp x)
                (case-match x
                  ((':ruleset ruleset)
                   (or (is-ruleset ruleset world)
                       (cw "**NOTE**:~%~x0 is not a ruleset.~%"
                           ruleset)))
                  ((':executable-counterpart-theory &) t)
                  ((':current-theory &) t)
                  ((':theory &) t)
                  ((':rules-of-class & &) t)
                  (& (cw "~
**NOTE**:~%~x0 is neither a rune nor a valid ruleset designator.~%" x)))))))


;; This does not short-circuit, so that we get error messages for all the
;; invalid entries.
(defun ruleset-designator-listp1 (x world ok)
  (if (atom x)
      (and (eq x nil) ok)
    (ruleset-designator-listp1
     (cdr x) world (and (ruleset-designatorp (car x) world) ok))))

(defun ruleset-designator-listp (x world)
  (ruleset-designator-listp1 x world t))


(defun rules-of-class1 (class theory)
  (declare (xargs :mode :program))
  (if (atom theory)
      nil
    (if (and (consp (car theory))
             (eq (caar theory) class))
        (cons (car theory) (rules-of-class1 class (cdr theory)))
      (rules-of-class1 class (cdr theory)))))

(defmacro rules-of-class (class name)
  `(rules-of-class1 ,class (universal-theory ,name)))

(defun def-ruleset-core (name rules world state)
  (declare (xargs :stobjs state))
  (if (ruleset-designator-listp rules world)
      (value `(table ruleset-table ',name ',rules))
    (er soft 'def-ruleset "Invalid ruleset specified~%")))

(defun add-to-ruleset-core (name rules world state)
  (declare (xargs :stobjs state))
  (if (ruleset-designator-listp rules world)
      (value `(table ruleset-table ',name
                     (union-equal ',rules (ruleset ',name))))
    (er soft 'add-to-ruleset "Invalid ruleset specified~%")))

(defun check-not-ruleset (name world state)
  (declare (xargs :stobjs state))
  (if (is-ruleset name world)
      (er soft 'def-ruleset
          "~x0 is already a ruleset.  Use add-to-ruleset or def-ruleset! ~
               instead.~%" name)
    (value 'ok)))

(defun check-ruleset (name world state)
  (declare (xargs :stobjs state))
  (if (is-ruleset name world)
      (value 'ok)
    (er soft 'add-to-ruleset
        "~x0 is not already a ruleset.  Use def-ruleset, def-ruleset! ~
             or add-to-ruleset! instead.~%" name)))

(defun ruleset-form-preprocess (form)
  (if (and (symbolp form)
           (not (booleanp form)))
      `'(,form)
    form))

(defsection def-ruleset
  :parents (rulesets)
  :short "@(call def-ruleset) creates a new ruleset."

  :long "<p>Examples:</p>
@({
 (def-ruleset my-rules
   '(append reverse))

 (def-ruleset other-rules
   '(member-equal my-rules revappend))
})

<p>The first example creates a new ruleset, @('my-rules'), with only the
definitions of @('append') and @('reverse').</p>

<p>The section example creates a new ruleset, @('other-rules'), with the
definitions of @('member-equal') and @('revappend'), and also a link to
@('my-rules').  When rules are added to @('my-rules'), @('other-rules')
also grows.</p>"

  (defmacro def-ruleset (name form)
    (declare (xargs :guard (symbolp name)))
    `(make-event
      (let ((world (w state))
            (name ',name))
        (er-progn
         (check-not-ruleset name world state)
         (let ((rules ,(ruleset-form-preprocess form)))
           (def-ruleset-core
             name rules world state)))))))

(defsection add-to-ruleset
  :parents (rulesets)
  :short "@(call add-to-ruleset) adds additional rules to an existing
ruleset."

  :long "<p>Examples:</p>
@({
 (add-to-ruleset my-rules
   '(foop))

 (add-to-ruleset other-rules
   '(car-cons cdr-cons (force)))
})"

  (defmacro add-to-ruleset (name form)
    (declare (xargs :guard (symbolp name)))
    `(make-event
      (let ((world (w state))
            (name ',name))
        (er-progn
         (check-ruleset name world state)
         (let ((rules ,(ruleset-form-preprocess form)))
           (add-to-ruleset-core name rules world state)))))))

(defsection def-ruleset!
  :parents (rulesets)
  :short "Same as @(see def-ruleset) except that it does not complain if the
ruleset already exists, instead acting like add-to-ruleset in that case."

  (defmacro def-ruleset! (name form)
    (declare (xargs :guard (symbolp name)))
    `(make-event
      (let* ((world (w state))
             (name ',name)
             (rules ,(ruleset-form-preprocess form)))
        (if (is-ruleset name world)
            (add-to-ruleset-core name rules world state)
          (def-ruleset-core name rules world state))))))

(defmacro set-ruleset! (name form)
  (declare (xargs :guard (symbolp name)))
  `(make-event
    (let* ((world (w state))
           (name ',name)
           (rules ,(ruleset-form-preprocess form)))
      (def-ruleset-core name rules world state))))

(defmacro add-to-ruleset! (name form)
  (declare (xargs :guard (symbolp name)))
  `(make-event
    (let* ((world (w state))
           (name ',name)
           (rules ,(ruleset-form-preprocess form)))
      (add-to-ruleset-core name rules world state))))


;; This is fragile; we don't recursively check rulesets that we're expanding.
(defun expand-ruleset1 (x world)
  (if (atom x)
      nil
    (let ((des (car x)))
      (cond ((rule-name-designatorp des (macro-aliases world) world)
             (cons des (expand-ruleset1 (cdr x) world)))
            ((atom des)
             (append (expand-ruleset1 (ruleset des) world)
                     (expand-ruleset1 (cdr x) world)))
            (t (case (car des)
                 (:ruleset
                  (append (expand-ruleset1 (ruleset (cadr des)) world)
                          (expand-ruleset1 (cdr x) world)))
                 (:executable-counterpart-theory
                  (append (executable-counterpart-theory (cadr des))
                          (expand-ruleset1 (cdr x) world)))
                 (:rules-of-class
                  (append (rules-of-class (cadr des) (caddr des))
                          (expand-ruleset1 (cdr x) world)))
                 (:theory
                  (append (theory (cadr des))
                          (expand-ruleset1 (cdr x) world)))
                 (:current-theory
                  (append (executable-counterpart-theory (cadr des))
                          (expand-ruleset1 (cdr x) world)))))))))

(defun expand-ruleset (x world)
  (if (ruleset-designator-listp x world)
      (expand-ruleset1 x world)
    (er hard 'expand-ruleset "~x0 is not a valid ruleset.~%" x)))

(defsection enable*
  :parents (rulesets)
  :short "Ruleset-aware version of @(see enable)."
  :long "<p>Examples:</p>

@({
 (in-theory (enable* my-rules append car-cons))

 (defthm ...
    :hints ((\"Goal\" :in-theory (enable* foo ...))))
})"

  (defmacro enable* (&rest x)
    `(union-theories-fn
      (current-theory :here)
      (expand-ruleset ',x world)
      t world)))

(defsection disable*
  :parents (rulesets)
  :short "Ruleset-aware version of @(see disable)."
  :long "<p>Examples:</p>

@({
 (in-theory (disable* my-rules append car-cons))

 (defthm ...
    :hints ((\"Goal\" :in-theory (disable* foo ...))))
})"

  (defmacro disable* (&rest x)
    `(set-difference-theories-fn
      (current-theory :here)
      (expand-ruleset ',x world)
      t world)))

(defsection e/d*
  :parents (rulesets)
  :short "Ruleset-aware version of @(see e/d)."
  :long "<p>Examples:</p>

@({
 (in-theory (e/d* (unusual-rules append)
                  (expensive-rules default-car default-cdr)))

 (defthm ...
    :hints ((\"Goal\"
             :in-theory (e/d* (unusual-rules append)
                              (expensive-rules default-car
                               default-cdr)))))
})"

  (defun e/d*-fn (theory e/d-list enable-p)
    (declare (xargs :guard (and (true-list-listp e/d-list)
                                (or (eq enable-p t)
                                    (eq enable-p nil)))))
    (cond ((atom e/d-list) theory)
          (enable-p (e/d*-fn `(UNION-THEORIES ,theory
                                              (expand-ruleset ',(car e/d-list) world))
                             (cdr e/d-list) nil))
          (t (e/d*-fn `(SET-DIFFERENCE-THEORIES ,theory
                                                (expand-ruleset ',(car e/d-list) world))
                      (cdr e/d-list) t))))

  (defmacro e/d** (&rest theories)
    (declare (xargs :guard (true-list-listp theories)))
    (cond ((atom theories) nil)
          (t (e/d*-fn nil theories t))))

  (defmacro e/d* (&rest theories)
    (declare (xargs :guard (true-list-listp theories)))
    (cond ((atom theories) '(current-theory :here))
          (t (e/d*-fn '(current-theory :here)
                      theories t)))))

(defmacro ruleset-theory (ruleset)
  `(expand-ruleset (ruleset ,ruleset) world))


#||

(logic)

(local
 (encapsulate
  nil

(include-book
   ;; This is on a separate line so that this book won't appear to depend on
   ;; the make-event subdir.
   "make-event/assert" :dir :system)

(def-ruleset! foo '(append reverse))
(def-ruleset! bar '(foo nth))

(add-to-ruleset foo '((consp)))

(in-theory nil)
(in-theory (enable* foo))

(assert! (let ((ens (ens state)))
           (and (not (active-runep '(:definition member-equal)))
                (not (active-runep '(:definition nth)))
                (active-runep '(:definition binary-append))
                (active-runep '(:definition reverse))
                (active-runep '(:executable-counterpart consp)))))

(in-theory nil)
(in-theory (enable* bar))
(assert! (let ((ens (ens state)))
           (and (not (active-runep '(:definition member-equal)))
                (active-runep '(:definition nth))
                (active-runep '(:definition binary-append))
                (active-runep '(:definition reverse))
                (active-runep '(:executable-counterpart consp)))))

(in-theory (disable* foo))
(assert! (let ((ens (ens state)))
           (and (active-runep '(:definition nth))
                (not (active-runep '(:definition member-equal)))
                (not (active-runep '(:definition binary-append)))
                (not (active-runep '(:definition reverse)))
                (not (active-runep '(:executable-counterpart consp))))))

(in-theory nil)
(in-theory (e/d* ((:ruleset bar)) ((:ruleset foo))))
(assert! (let ((ens (ens state)))
           (and (active-runep '(:definition nth))
                (not (active-runep '(:definition member-equal)))
                (not (active-runep '(:definition binary-append)))
                (not (active-runep '(:definition reverse)))
                (not (active-runep '(:executable-counterpart consp))))))


||#
