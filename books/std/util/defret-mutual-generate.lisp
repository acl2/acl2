; Standard Utilities Library
; Copyright (C) 2019 Centaur Technology
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
; Original authors: Sol Swords <sswords@centtech.com>


(in-package "STD")
(include-book "defines")

(set-state-ok t)
(program)


(defxdoc defret-mutual-generate
  :parents (defret-mutual)
  :short "Generate a @(see defret-mutual) form using rules that produce hyps and
          conclusion conjuncts based on @(see define) formal and return
          specifiers." 
  :long "
<h3>Motivation</h3>

<p>Suppose you have a mutual recursion with several functions and you want to
prove some theorems about them.  Often you need to prove something about all of
them at once using mutual induction; @(see defret-mutual) and @(see
acl2::make-flag) are good tools for doing this. But sometimes there are so many
functions that it becomes unwieldy to write a full @('defret-mutual') form
containing an explicit theorem for each function.  This often involves a lot of
repetition and isn't very DRY.  Instead, one might be able to generate the
theorems using rules based on the input/output signature of the functions.
That is what defret-mutual-generate is intended to do.</p>

<p>The general idea is that for each function in the clique, we get that
function's input/output signature and apply a sequence of rules, defined by the
arguments to @('defret-mutual-generate'), which result in a theorem to prove.
The rules may check things like the presence or absence of a formal or return
value, the name of the function, etc., and compose the resulting theorem by
adding hypothesis or conclusion conjuncts, @('B*') bindings, etc.  Then we
take the results from all the functions in the clique and prove them all
together using @('defret-mutual').</p>

<h4>Invocation Syntax</h4>

<p>For a single set of rules generating a mutually inductive set of theorems, use
the following form.  The conditions and actions used by the rules entries are
described below.</p>

@({
 (defret-mutual-generate thmname-template
   :rules ((condition1 action1 ...)
           (condition2 action2 ...))
   ...
   ;; optional keywords
   :hints top-level-hints
   :instructions rarely-used
   :no-induction-hint nil
   :otf-flg nil
   ;; defaults to the most recent defines form:
   :mutual-recursion defines-name)
 })

<p>A few other keywords effectively generate additional @(':rules') entries, as
discussed below under Common Abbreviations.  These may be used wherever
@(':rules') may occur.</p>

<p>For example:</p>

@({
 (defret-mutual-generate term-vars-of-<fn>
    :rules ((t
             (:each-formal :type pseudo-termp :var x (:add-hyp (not (member v (term-vars x)))))
             (:each-formal :type pseudo-term-listp :var x (:add-hyp (not (member v (termlist-vars x)))))
             (:each-return :type pseudo-termp :var x (:add-concl (not (member v (term-vars x)))))
             (:each-return :type pseudo-term-listp :var x (:add-concl (not (member v (termlist-vars x))))))
            ((:has-return :type pseudo-term-listp)
             (:set-thmname termlist-vars-of-<fn>))
            ((:has-formal :name x :type pseudo-term-listp)
             (:add-keyword :hints ('(:expand ((termlist-vars x)))))))
   :mutual-recursion my-rewriter)
 })

<p>Sometimes it is necessary to prove more than one kind of theorem at once
within a mutual induction.  In this case @('defret-mutual-generate') allows
more than one set of rules to apply separately to each function in the mutual
recursion, and makes a @('defret-mutual') form containing all of the resulting
@('defret') forms. The syntax for this is as follows:</p>

@({
 (defret-mutual-generate
   (defret-generate thmname-template1
     :rules rules1
     ...)
   (defret-generate thmname-template2
     :rules rules2
     ...)
   ...
   ;; same optional keywords as above
   :hints top-level-hints
   :mutual-recursion my-defines-name)
 })


<h3>Theorem Generation Rules</h3>

<p>For each function in the mutual recursion, @('defret-mutual-generate')
produces a @(see defret) form by applying a series of rules.  Each rule is a
pair @('(condition actions)') where if the condition is satisfied, the actions
modify the @('defret') form.  The rules may be written directly by the user or
generated using some abbreviations, discussed below.</p>


<h4>Condition language</h4>

<p>The condition under which a rule applies may be a Boolean formula using
AND/OR/NOT, T and NIL, and the following checks:</p>

<ul>
<li>@('(:has-formal :name name :type type)') checks that the function has a
formal satisfying the specified criteria.  If @(':name') is given then it
checks for a formal with the given name; if @(':type') is given then it checks
for a formal that has a guard @('(type name)').</li>

<li>@('(:has-return :name name :type type)') checks that the function has a
return value satisfying the given criteria, simple to @('has-formal').</li>

<li>@('(:fnname name)') only applies to the given function.</li>

</ul>
<p>See the function @('dmgen-eval-condition') for implementation.</p>

<h4>Actions</h4>

<p>An action may be any of the following:</p>

<ul>
<li>@('(:add-hyp term)') adds @('term') as a top-level hypothesis.</li>
<li>@('(:add-concl term)') adds @('term') as a conclusion, conjoined with any others.</li>
<li>@('(:add-bindings . bindings)') adds the given @('B*') bindings, after
binding the return values but outside of both the hyps and conclusions.</li>
<li>@('(:each-formal :type type :var var :action action)'), where each action
is an @(':add-hyp'), @(':push-hyp') or @(':add-concl') form, adds the
given hyp or conclusion for each formal with the given type, with @('var') in
these actions replaced by the name of the formal.</li>

<li>@('(:each-return :type type :var var :action action)'), similar to
@('each-formal') but acts on return values instead of formals.</li>

<li>@('(:push-hyp term)') pushes @('term') as a hypothesis for any conclusions
added subsequently until it is popped off the stack with @('(:pop-hyp)').</li>
<li>@('(:pop-hyp)') removes the most recently pushed hypothesis so it won't
affect subsequent conclusions added.</li>

<li>@('(:add-keyword key val ...)') adds the keyword/value pairs as arguments
to the resulting @('defret') form; typical keys to use are @(':hints') and
@(':rule-classes').</li>

<li>@('(:set-thmname template)') sets the theorem name template for the
@('defret') to the given symbol, which may include the substring @('<FN>')
which is replaced by the name of the function.</li>

</ul>


<h4>Common Abbreviations</h4>

<p>The @('defret-mutual-generate') macro supports some other keywords
besides :rules, each of which generates rules according to some common usage
patterns.  Note that the ordering of rules is significant for the behavior of
@(':push-hyp')/@(':pop-hyp') and @(':add-concl').  The rules generated by these
abbreviations are considered before the explicit @(':rules'); this means that
any conclusions generated by @(':return-concls') will not be affected by any
@(':push-hyp') forms from the @(':rules').</p>

<h5>@(':formal-hyps')</h5>

<p>This keyword generates hypotheses based on the names/types of formals.  Its
argument is a list of elements of one of the following forms:</p>

<ul>
<li>@('(formalname hyp-term :type type)') adds the given hyp to the theorem of
any function with a formal of the given name.  If @(':type') is given, it will
only be added if that formal is of the specified type.</li>

<li>@('((type-pred name) hyp-term)') adds the given hyp term for every formal
of the given type, binding that formal to @('name').</li>
</ul>

<h5>@(':return-concls')</h5>
<p>This keyword generates hypotheses based on the names/types of return values.
Its argument is a list of elements similar to those of @(':formal-hyps').</p>

<h5>@(':function-keys')</h5>
<p>This keyword adds hints or other keywords to the theorems corresponding to
function names. For example:</p>

@({
 :function-keys
    ((rewrite-term-list
       :hints ('(:expand ((termlist-vars x)))))
})")


;; Use the prefix DMGEN for our functions...

(defun dmgen-check-formal-type (type formal)
  (or (not type)
      (b* (((formal f1) formal))
        (or (and (eq type t) (eq f1.guard t))
            (equal f1.guard `(,type ,f1.name))))))

(defun dmgen-has-formal (name type formals)
  (if (atom formals)
      nil
    (or (b* (((formal f1) (car formals)))
          (and (or (not name) (eq f1.name name))
               (dmgen-check-formal-type type f1)))
        (dmgen-has-formal name type (cdr formals)))))

(defun dmgen-check-returnspec-type (type returnspec)
  (or (not type)
      (b* (((returnspec r1) returnspec))
        (or (and (eq type t) (eq r1.return-type t))
            (equal r1.return-type `(,type ,r1.name))))))

(defun dmgen-has-returnspec (name type returnspecs)
  (if (atom returnspecs)
      nil
    (or (b* (((returnspec r1) (car returnspecs)))
          (and (or (not name) (eq r1.name name))
               (dmgen-check-returnspec-type type r1)))
        (dmgen-has-returnspec name type (cdr returnspecs)))))


(mutual-recursion
 (defun dmgen-check-condition (condition)
   (if (atom condition)
       (and (not (booleanp condition))
            (msg "Bad atom: ~x0" condition))
     (case (car condition)
       ((and or) (b* (((unless (true-listp (cdr condition)))
                       (msg "Bad AND/OR form: ~x0" condition)))
                   (dmgen-check-conditionlist (cdr condition))))
       (not (b* (((unless (and (consp (cdr condition))
                               (not (cddr condition))))
                  (msg "Bad NOT form: ~x0" condition)))
              (dmgen-check-condition (cadr condition))))
       ((:has-formal :has-return)
        (and (not (keyword-value-listp (cdr condition)))
             (msg "Bad HAS form: ~x0" condition)))
       (:fnname (and (not (and (consp (cdr condition))
                               (not (cddr condition))
                               (symbolp (cadr condition))))
                     (msg "bad FNNAME form: ~x0" condition)))
       (otherwise (msg "Bad condition form: ~x0" condition)))))
 (defun dmgen-check-conditionlist (conditions)
   (if (atom conditions)
       nil
     (or (dmgen-check-condition (car conditions))
         (dmgen-check-conditionlist (cdr conditions))))))

(mutual-recursion
 (defun dmgen-eval-condition (condition guts)
   (if (atom condition)
       condition
     (case (car condition)
       ((and or) (dmgen-eval-conditionlist (car condition) (cdr condition) guts))
       (not (not (dmgen-eval-condition (cadr condition) guts)))
       ((:has-formal :has-return)
        (b* ((type (cadr (assoc-keyword :type (cdr condition))))
             (name (cadr (assoc-keyword :name (cdr condition)))))
          (if (eq (car condition) ':has-formal)
              (dmgen-has-formal name type (defguts->formals guts))
            (dmgen-has-returnspec name type (defguts->returnspecs guts)))))
       (:fnname (eq (cadr condition) (defguts->name guts))))))

 (defun dmgen-eval-conditionlist (and/or conditions guts)
   (if (atom conditions)
       (eq and/or 'and)
     (let ((first (dmgen-eval-condition (car conditions) guts)))
       (if (eq and/or 'and)
           (and first
                (dmgen-eval-conditionlist and/or (cdr conditions) guts))
         (or first
             (dmgen-eval-conditionlist and/or (cdr conditions) guts)))))))

(def-primitive-aggregate dmgen-defret-form
  (thmname
   top-hyps      ;; list of hyps
   hyps-and-concls
   ;; list of: (:hyp . hyp) or (:concl . concl) or (:pop-hyp) where each hyp
   ;; applies to all subsequently pushed concls until it is popped off with
   ;; :pop-hyp
   bindings
   keywords
   fn))

(defun dmgen-check-add-hyp/concl-action (action)
  (and (not (and (consp (cdr action))
                 (not (cddr action))))
       (msg "Bad add-hyp/concl action: ~x0" action)))

(defun dmgen-check-pop-hyp-action (action)
  (and (cdr action)
       (msg "Bad pop-hyp action: ~x0" action)))

(defun dmgen-check-add-bindings-action (action)
  (and (not (true-listp (cadr action)))
       (msg "Bad add-bindings action: ~x0" action)))

(defun dmgen-check-formal/return-action (action)
  (if (atom action)
      (msg "Bad formal action (atom): ~x0" action)
    (if (member-eq (car action) '(:add-hyp :push-hyp :pop-hyp :add-concl))
        (dmgen-check-add-hyp/concl-action action)
      (msg "Bad formal action: ~x0" action))))


(defun dmgen-push-hyp (new-term form)
  (b* (((dmgen-defret-form form)))
    (change-dmgen-defret-form
     form
     :hyps-and-concls (cons (cons :hyp new-term) form.hyps-and-concls))))

(defun dmgen-pop-hyp ( form)
  (b* (((dmgen-defret-form form)))
    (change-dmgen-defret-form
     form
     :hyps-and-concls (cons '(:pop-hyp) form.hyps-and-concls))))


(defun dmgen-add-concl (new-term form)
  (b* (((dmgen-defret-form form)))
    (change-dmgen-defret-form
     form
     :hyps-and-concls (cons (cons :concl new-term) form.hyps-and-concls))))

(defun dmgen-add-hyp (new-term form)
  (b* (((dmgen-defret-form form)))
    (change-dmgen-defret-form
     form
     :top-hyps (cons new-term form.top-hyps))))

;; (defun dmgen-check-formal/return-actions (actions)
;;   (if (atom actions)
;;       nil
;;     (or (dmgen-check-formal/return-action (car actions))
;;         (dmgen-check-formal/return-actions (cdr actions)))))

(defun dmgen-formal/return-action (replace-var formalname action form)
  (b* (((when (eq (car action) :pop-hyp))
        (dmgen-pop-hyp form))
       (new-term (if replace-var
                     (subst formalname replace-var (cadr action))
                   (cadr action))))
    (case (car action)
      (:add-hyp
       (dmgen-add-hyp new-term form))
      (:push-hyp
       (dmgen-push-hyp new-term form))
      (:add-concl
       (dmgen-add-concl new-term form)))))

;; (defun dmgen-formal/return-actions (replace-var formalname actions form)
;;   (if (atom actions)
;;       form
;;     (dmgen-formal/return-actions
;;      replace-var formalname
;;      (cdr actions)
;;      (dmgen-formal/return-action
;;       replace-var formalname (car actions) form))))

(defun dmgen-each-formal-action (type replace-var action form formals)
  (if (atom formals)
      form
    (let ((form
           (if (dmgen-check-formal-type type (car formals))
               (dmgen-formal/return-action replace-var (formal->name (car formals)) action form)
             form)))
      (dmgen-each-formal-action type replace-var action form (cdr formals)))))

(defun dmgen-each-returnspec-action (type replace-var action form returnspecs)
  (if (atom returnspecs)
      form
    (let ((form
           (if (dmgen-check-returnspec-type type (car returnspecs))
               (dmgen-formal/return-action replace-var (returnspec->name (car returnspecs)) action form)
             form)))
      (dmgen-each-returnspec-action type replace-var action form (cdr returnspecs)))))

(defun dmgen-check-each-formal/return-action (action)
  (cond ((not (keyword-value-listp (cdr action)))
         (msg "Bad each-formal/return action: ~x0" action))
        ((dmgen-check-formal/return-action (cadr (assoc-keyword :action (cdr action)))))
        (t nil)))

(defun dmgen-check-add-keyword-action (action)
  (and (not (keyword-value-listp (cdr action)))
       (msg "Bad add-keyword action: ~x0" action)))

(defun dmgen-check-set-thmname-action (action)
  (and (not (and (consp (cdr action))
                 (symbolp (cadr action))
                 (not (cddr action))))
       (msg "Bad set-thmname action: ~x0" action)))


(defun dmgen-check-action (action)
  (if (atom action)
      (msg "Bad action (atom): ~x0" action)
    (case (car action)
      ((:add-hyp :push-hyp :add-concl) (dmgen-check-add-hyp/concl-action action))
      (:pop-hyp (dmgen-check-pop-hyp-action action))
      ((:each-formal :each-return) (dmgen-check-each-formal/return-action action))
      (:add-bindings (dmgen-check-add-bindings-action action))
      (:add-keyword (dmgen-check-add-keyword-action action))
      (:set-thmname (dmgen-check-set-thmname-action action))
      (t (msg "Bad action: ~x0" action)))))

(defun dmgen-check-actions (actions)
  (if (atom actions)
      nil
    (or (dmgen-check-action (car actions))
        (dmgen-check-actions (cdr actions)))))

(defun dmgen-check-rule (rule)
  (or (dmgen-check-condition (car rule))
      (dmgen-check-actions (cdr rule))))

(defun dmgen-check-rules (rules)
  (if (atom rules)
      nil
    (or (dmgen-check-rule (car rules))
        (dmgen-check-rules (cdr rules)))))

(defun dmgen-action (action guts form)
  (b* (((dmgen-defret-form form)))
    (case (car action)
      (:add-hyp             (dmgen-add-hyp (cadr action) form))
      (:push-hyp            (dmgen-push-hyp (cadr action) form))
      (:pop-hyp             (dmgen-pop-hyp form))
      (:add-concl           (dmgen-add-concl (cadr action) form))
      (:add-bindings (change-dmgen-defret-form form :bindings (append form.bindings (cadr action))))
      (:each-formal (dmgen-each-formal-action
                     (cadr (assoc-keyword :type (cdr action)))
                     (cadr (assoc-keyword :var (cdr action)))
                     (cadr (assoc-keyword :action (cdr action)))
                     form (defguts->formals guts)))
      (:each-return (dmgen-each-returnspec-action
                     (cadr (assoc-keyword :type (cdr action)))
                     (cadr (assoc-keyword :var (cdr action)))
                     (cadr (assoc-keyword :action (cdr action)))
                     form (defguts->returnspecs guts)))
      (:add-keyword (change-dmgen-defret-form form :keywords (append (cdr action) form.keywords)))
      (:set-thmname (change-dmgen-defret-form form :thmname (cadr action))))))

(defun dmgen-actions (actions guts form)
  (if (atom actions)
      form
    (dmgen-actions (cdr actions)
                   guts
                   (dmgen-action (car actions) guts form))))

(defun dmgen-apply-rule (rule guts form)
  (if (dmgen-eval-condition (car rule) guts)
      (dmgen-actions (cdr rule) guts form)
    form))

(defun dmgen-apply-rules (rules guts form)
  (if (atom rules)
      form
    (dmgen-apply-rules (cdr rules)
                       guts
                       (dmgen-apply-rule (car rules) guts form))))

(defun dmgen-collect-consecutive-hyps (x)
  (and (consp x)
       (eq (caar x) :hyp)
       (cons (cdar x)
             (dmgen-collect-consecutive-hyps (cdr x)))))

(defun dmgen-skip-past-hyps (x)
  (if (and (consp x)
           (eq (caar x) :hyp))
      (dmgen-skip-past-hyps (cdr x))
    x))

(defun dmgen-hyps-and-concls-to-expression (hyps concls)
  (b* (((when (atom concls)) t)
       (concl (cond ((atom (cdr concls)) (car concls))
                    (t `(and . ,concls))))
       ((when (eq concl t)) t)
       ((when (atom hyps)) concl)
       (hyp (cond ((atom (cdr hyps)) (car hyps))
                  (t `(and . ,hyps)))))
    `(implies ,hyp ,concl)))

(defun add-concl (concl rest)
  (if (eq concl t)
      rest
    (cons concl rest)))

(defun dmgen-process-hyps-and-concls (x)
  (cond ((atom x) (mv nil nil))
        ((eq (caar x) :pop-hyp) (mv nil (cdr x))) 
        ((eq (caar x) :hyp)
         (b* (((mv concls rest) (dmgen-process-hyps-and-concls (cdr x)))
              ((mv rest-concls rest-rest)
               (dmgen-process-hyps-and-concls rest)))
           (mv (add-concl (dmgen-hyps-and-concls-to-expression (list (cdar x)) concls)
                          rest-concls)
               rest-rest)))
        ((eq (caar x) :concl)
         (b* (((mv concls rest) (dmgen-process-hyps-and-concls (cdr x))))
           (mv (add-concl (cdar x) concls) rest)))
        (t (mv (er hard? 'dmgen-process-hyps-and-concls "Illformed hyps-and-concls: ~x0" x) nil))))
    
        


(defun dmgen-defret-form->defrets (form)
  (b* (((dmgen-defret-form form))
       (hyps-and-concls (reverse form.hyps-and-concls))
       ((mv concls remainder) (dmgen-process-hyps-and-concls hyps-and-concls))
       ((when remainder)
        (er hard? 'dmgen-defret-form->defrets "Error processing hyps-and-concls: too many pop-hyp forms?~%"))
       ((unless concls)
        nil)
       (form (dmgen-hyps-and-concls-to-expression form.top-hyps concls))
       (form-with-bindings (if (consp form.bindings)
                               `(b* ,form.bindings ,form)
                             form)))
    `((defret ,form.thmname
        ,form-with-bindings
        ,@form.keywords
        :fn ,form.fn))))

;; (defun dmgen-defret-forms->defrets (forms)
;;   (if (atom forms)
;;       nil
;;     (append (dmgen-defret-form->defrets (car forms))
;;             (dmgen-defret-forms->defrets (cdr forms)))))

(defun dmgen-generate-defrets-for-fn (thmname rules guts)
  (dmgen-defret-form->defrets
   (dmgen-apply-rules rules guts
                      (make-dmgen-defret-form
                       :thmname thmname
                       :fn (defguts->name guts)))))

(defun dmgen-generate-defrets (thmname rules gutslist)
  (if (atom gutslist)
      nil
    (append (dmgen-generate-defrets-for-fn thmname rules (car gutslist))
            (dmgen-generate-defrets thmname rules (cdr gutslist)))))

(defun dmgen-generate-for-rules (thmname rules gutslist)
  (b* ((errmsg (dmgen-check-rules rules))
       ((when errmsg)
        (er hard? 'defret-mutual-generate
            "Bad rule found among the rules for ~x0.  Specifically: ~@1" thmname errmsg)))
    (dmgen-generate-defrets thmname rules gutslist)))

(defun dmgen-check-formal-hyp-form (form)
  (cond ((atom form)
         (msg "Bad formal-hyps form (atom): ~x0" form))
        ((not (and (true-listp form)
                   (<= 2 (len form))
                   (keyword-value-listp (cddr form))))
         (msg "Bad formal-hyps form (length): ~x0" form))
        ((symbolp (car form))
         ;; (formalname hyp-term :type type)  (type optional)
         nil)
        ((and (consp (car form))
              (symbolp (caar form))
              (consp (cdar form))
              (symbolp (cadar form)))
         ;; ((type-pred name) hyp-term)
         nil)
        (t (msg "Bad formal-hyps form (condition): ~x0" form))))

(defun dmgen-check-return-concl-form (form)
  (cond ((atom form)
         (msg "Bad return-concls form (atom): ~x0" form))
        ((not (and (true-listp form)
                   (<= 2 (len form))
                   (keyword-value-listp (cddr form))))
         (msg "Bad return-concls form (length): ~x0" form))
        ((symbolp (car form))
         ;; (formalname hyp-term :type type)  (type optional)
         nil)
        ((and (consp (car form))
              (symbolp (caar form))
              (consp (cdar form))
              (symbolp (cadar form)))
         ;; ((type-pred name) hyp-term)
         nil)
        (t (msg "Bad return-concls form (condition): ~x0" form))))


(defun dmgen-check-formal-hyps (forms)
  (if (atom forms)
      nil
    (or (dmgen-check-formal-hyp-form (car forms))
        (dmgen-check-formal-hyps (cdr forms)))))

(defun dmgen-check-return-concls (forms)
  (if (atom forms)
      nil
    (or (dmgen-check-return-concl-form (car forms))
        (dmgen-check-return-concls (cdr forms)))))


(defun dmgen-process-formal-hyp-form (form)
  (cond ((symbolp (car form))
         (b* (((list* formalname hyp-term keys) form))
           `(((:has-formal :name ,formalname ,@keys)
              (:add-hyp ,hyp-term)))))
        (t (b* (((list (list type var) hyp-term) form))
             `((t (:each-formal :type ,type :var ,var
                   :action (:add-hyp ,hyp-term))))))))

(defun dmgen-process-formal-hyp-forms (forms)
  (if (atom forms)
      nil
    (append (dmgen-process-formal-hyp-form (car forms))
            (dmgen-process-formal-hyp-forms (cdr forms)))))

(defun dmgen-process-return-concl-form (form)
  (cond ((symbolp (car form))
         (b* (((list* returnname concl-term keys) form))
           `(((:has-return :name ,returnname ,@keys)
              (:add-concl ,concl-term)))))
        (t (b* (((list (list type var) concl-term) form))
             `((t (:each-return :type ,type :var ,var
                   :action (:add-concl ,concl-term))))))))

(defun dmgen-process-return-concl-forms (forms)
  (if (atom forms)
      nil
    (append (dmgen-process-return-concl-form (car forms))
            (dmgen-process-return-concl-forms (cdr forms)))))


(defun dmgen-process-formal-hyps (forms)
  (b* ((err (dmgen-check-formal-hyps forms))
       ((when err)
        (er hard? 'defret-mutual-generate
            "Bad :formal-hyps forms, specifically: ~@0~%" err)))
    (dmgen-process-formal-hyp-forms forms)))

(defun dmgen-process-return-concls (forms)
  (b* ((err (dmgen-check-return-concls forms))
       ((when err)
        (er hard? 'defret-mutual-generate
            "Bad :return-concls forms, specifically: ~@0~%" err)))
    (dmgen-process-return-concl-forms forms)))

(defun dmgen-check-function-key-form (form)
  (and (not (and (consp form)
                 (symbolp (car form))
                 (keyword-value-listp (cdr form))))
       (msg "Bad function-key form: ~x0" form)))

(defun dmgen-check-function-keys (forms)
  (if (atom forms)
      nil
    (or (dmgen-check-function-key-form (car forms))
        (dmgen-check-function-keys (cdr forms)))))

(defun dmgen-process-function-key-form (form)
  (b* (((cons fnname keys) form))
    `(((:fnname ,fnname)
       (:add-keyword . ,keys)))))

(defun dmgen-process-function-key-forms (forms)
  (if (atom forms)
      nil
    (append (dmgen-process-function-key-form (car forms))
            (dmgen-process-function-key-forms (cdr forms)))))

(defun dmgen-process-function-keys (forms)
  (b* ((err (dmgen-check-function-keys forms))
       ((when err)
        (er hard? 'defret-mutual-generate
            "Bad :function-keys forms, specifically: ~@0~%" err)))
    (dmgen-process-function-key-forms forms)))

(defconst *defret-generate-keywords*
  '(:rules :formal-hyps :return-concls :function-keys))


(defun dmgen-multi-ruleset (dmgen-form guts)
  (b* (((unless (eq (car dmgen-form) 'defret-generate))
        (er hard? 'defret-generate "Must start with defret-generate"))
       ((unless (and (consp (cdr dmgen-form))
                     (symbolp (cadr dmgen-form))))
        (er hard? 'defret-generate "Must contain a theorem name template as the first argument"))
       (thmname (cadr dmgen-form))
       ((mv kwd-alist bad)
        (extract-keywords `(defret-generate ,thmname)
                          *defret-generate-keywords*
                          (cddr dmgen-form)
                          nil))
       ((when bad)
        (er hard? 'defret-generate "extra arguments in defret-generate"))
       (rules (append (dmgen-process-formal-hyps (cdr (assoc :formal-hyps kwd-alist)))
                      (dmgen-process-return-concls (cdr (assoc :return-concls kwd-alist)))
                      (dmgen-process-function-keys (cdr (assoc :function-keys kwd-alist)))
                      (cdr (assoc :rules kwd-alist)))))
    (dmgen-generate-for-rules thmname rules (defines-guts->gutslist guts))))

(defun dmgen-multi-rulesets (dmgen-forms guts)
  (if (atom dmgen-forms)
      nil
    (append (dmgen-multi-ruleset (car dmgen-forms) guts)
            (dmgen-multi-rulesets (cdr dmgen-forms) guts))))


(defun kwd-alist-to-keyword-value-list (keys kwd-alist)
  (if (atom keys)
      nil
    (let ((look (assoc-eq (car keys) kwd-alist)))
      (if look
          (list* (car keys) (cdr look)
                 (kwd-alist-to-keyword-value-list (cdr keys) kwd-alist))
        (kwd-alist-to-keyword-value-list (cdr keys) kwd-alist)))))
      

(defun dmgen-multi (kwd-alist dmgen-forms world)
  (b* ((defines-alist (get-defines-alist world))
       (mutrec (cdr (assoc :mutual-recursion kwd-alist)))
       (mutual-recursion (or mutrec (caar defines-alist)))
       ((unless mutual-recursion)
        (er hard? 'defret-mutual-generate
            "Defret-mutual-generate needs a mutual recursion created with defines to work on."))
       (guts (cdr (assoc mutual-recursion defines-alist)))
       ((unless guts)
        (er hard? 'defret-mutual-generate
            "~x0 is not the name of a mutual recursion created with defines." mutual-recursion))
       (defrets (dmgen-multi-rulesets dmgen-forms guts))
       (top-thmname (cadar dmgen-forms)))
    `(defret-mutual ,top-thmname
       ,@defrets
       :skip-others t
       ,@(kwd-alist-to-keyword-value-list
          '(:mutual-recursion :hints :no-induction-hint :instructions :otf-flg)
          kwd-alist))))


(defun dmgen-extract-keywords (args keys)
  (if (atom args)
      (mv nil nil)
    (if (and (symbolp (car args))
             (member-eq (car args) keys))
        (b* (((mv others kwd-alist) (dmgen-extract-keywords (cddr args) keys)))
          (mv others (cons (cons (car args) (cadr args)) kwd-alist)))
      (b* (((mv others kwd-alist) (dmgen-extract-keywords (cdr args) keys)))
        (mv (cons (car args) others) kwd-alist)))))


(defun dmgen-single (args world)
  (b* ((thmname (car args))
       (keywords (cdr args))
       ((unless (keyword-value-listp keywords))
        (er hard? 'defret-mutual-generate
            "Bad arguments: not a keyword-value list"))
       ((mv defret-generate-args top-kwd-alist)
        (dmgen-extract-keywords keywords '(:mutual-recursion :hints :no-induction-hint
                                           :instructions :otf-flg)))
       (dmgen-forms `((defret-generate ,thmname . ,defret-generate-args))))
    (dmgen-multi top-kwd-alist dmgen-forms world)))


(defun defret-mutual-generate-fn (args world)
  (b* (((when (symbolp (car args)))
        (dmgen-single args world))
       ((mv defret-generate-forms top-kwd-alist)
        (dmgen-extract-keywords args '(:mutual-recursion :hints :no-induction-hint
                                       :instructions :otf-flg))))
    (dmgen-multi top-kwd-alist defret-generate-forms world)))

(defmacro defret-mutual-generate (&rest args)
  `(make-event
    (defret-mutual-generate-fn ',args (w state))))







