; FGL - A Symbolic Simulation Framework for ACL2
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "FGL")

;; This includes just the thm/defthm-producing macros, so that books can
;; include the rest of FGL locally and just include this book nonlocally in
;; order to have their def-fgl-thms exported.

(include-book "std/alists/alist-defuns" :dir :system)

(defun fgl-thm-fn (args)
  (declare (xargs :mode :program))
  (let* ((concl (if (keywordp (car args))
                    (cadr (assoc-keyword :concl args))
                  (car args)))
         (args (if (keywordp (car args))
                   args
                 (cdr args)))
         (body (let ((look (assoc-keyword :hyp args)))
                 (if look
                     `(implies ,(cadr look) ,concl)
                   concl)))
         (rule-classes (let ((look (assoc-keyword :rule-classes args)))
                         (and look
                              `(:rule-classes ,(cadr look)))))
         (hints (cadr (assoc-keyword :hints args))))
    `(thm
      ,body
      :hints (,@hints
              '(:clause-processor expand-an-implies-cp)
              '(:clause-processor (fgl-interp-cp clause (default-fgl-config . ,args) interp-st state)))
      ,@rule-classes)))

(defmacro fgl-thm (&rest args)
  (fgl-thm-fn args))

(defun maybe-add-xdoc (name thm args)
  (b* ((parents-look (assoc-keyword :parents args))
       (short-look (assoc-keyword :short args))
       (long-look (assoc-keyword :long args))
       (want-xdoc (or parents-look short-look long-look)))
    (if want-xdoc
        `(defsection ,name
           ,@(and parents-look `(:parents ,(cadr parents-look)))
           ,@(and short-look `(:short ,(cadr short-look)))
           ,@(and long-look `(:long ,(cadr long-look)))
           ,thm)
      thm)))

(defun def-fgl-thm-fn (name args)
  (declare (xargs :mode :program))
  (maybe-add-xdoc name
                  `(defthm ,name
                     . ,(cdr (fgl-thm-fn args)))
                  (if (keywordp (car args)) args (cdr args))))

(defmacro def-fgl-thm (name &rest args)
  (def-fgl-thm-fn name args))

(defxdoc def-fgl-thm
  :parents (fgl)
  :short "Prove a theorem using FGL"
  :long "

<p>@('Def-fgl-thm') is the main macro used for proving a theorem using FGL.  It
produces a @(see defthm) form containing hints that cause the FGL clause
processor to be used to attempt the proof of the theorem.  Basic usage is as
follows:</p>

@({
 (def-fgl-thm <thmname>
    <theorem-body>
    <keyword-args>)
 })
<p>However, for backward compatibility with GL, the following usage is also supported:</p>
@({
 (def-fgl-thm <thmname>
   :hyp <hyp-term>
   :concl <concl-term>
   <keyword-args>)
 })

<p>The main keyword arguments supported include the fields of the @(see
fgl-config) object, and a few others listed below.  Each field of the
@('fgl-config') object is assigned as follows:</p>
<ul>
<li>The explicit value given in the @('def-fgl-thm') form, if there is one</li>
<li>Else if the table @('fgl::fgl-config-table') has an entry for the keyword field name, the value to which it is bound</li>
<li>Else if the keyword field name is bound as a state global, its global value</li>
<li>Else the default value defined by @(see make-fgl-config).</li>
</ul>

<p>The non-@('fgl-config') keywords recognized are:</p>
<ul>
<li>@(':hyp') and @(':concl'), used with the backward-compatible usage form above</li>
<li>@(':rule-classes'), giving the rule classes of the theorem proved</li>
<li>@(':hints'), a list of subgoal or computed hints that are listed before the
FGL clause processor hints.</li>
<li>@(':parents'), @(':short'), @(':long'), the usual xdoc documentation
arguments.  If any of these are provided, a @('defsection') containing the
theorem is created, rather than just the theorem.</li>
</ul>

<p>For now, other keyword arguments are accepted and ignored without complaint.
This probably will someday need to change.</p>
")


(defun fgl-param-thm-cases (param-bindings param-hyp)
  (if (atom param-bindings)
      nil
    (cons (list (msg "Case: ~x0" (caar param-bindings))
                `(let ,(pairlis$ (alist-keys (caar param-bindings))
                                 (pairlis$ (kwote-lst (alist-keys (alist-vals (caar param-bindings))))
                                           nil))
                   ,param-hyp))
          (fgl-param-thm-cases (cdr param-bindings) param-hyp))))


(defun fgl-param-thm-fn (args)
  (declare (xargs :mode :program))
  (let* ((concl (if (keywordp (car args))
                    (cadr (assoc-keyword :concl args))
                  (car args)))
         (args (if (keywordp (car args))
                   args
                 (cdr args)))
         (body (let ((look (assoc-keyword :hyp args)))
                 (if look
                     `(implies ,(cadr look) ,concl)
                   concl)))
         (rule-classes (let ((look (assoc-keyword :rule-classes args)))
                         (and look
                              `(:rule-classes ,(cadr look)))))
         (hints (cadr (assoc-keyword :hints args))))
    `(thm
      ,body
      :hints (,@hints
              (fgl-casesplit :cases
                             (fgl-param-thm-cases
                              ,(cadr (assoc-keyword :param-bindings args))
                              ',(cadr (assoc-keyword :param-hyp args)))
                             :split-params ,(cadr (assoc-keyword :split-params args))
                             :solve-params ,(cadr (assoc-keyword :solve-params args))
                             :split-concl-p ,(cadr (assoc-keyword :split-concl-p args))
                             :repeat-concl-p ,(cadr (assoc-keyword :repeat-concl-p args)))
              '(:clause-processor (fgl-interp-cp clause (default-fgl-config . ,args) interp-st state)))
      ,@rule-classes)))

(defmacro fgl-param-thm (&rest args)
  (fgl-param-thm-fn args))

(defun def-fgl-param-thm-fn (name args)
  (declare (xargs :mode :program))
  (maybe-add-xdoc name
                  `(defthm ,name
                     . ,(cdr (fgl-param-thm-fn args)))
                  (if (keywordp (car args)) args (cdr args))))

(defmacro def-fgl-param-thm (name &rest args)
  (def-fgl-param-thm-fn name args))


(defxdoc def-fgl-param-thm
  :parents (fgl)
  :short "Prove a theorem using FGL with case-splitting."
  :long "

<p>@('Def-fgl-param-thm') is similar to @(see def-fgl-thm), but runs a clause
processor prior to FGL that splits the goal into several cases based on the
provided arguments.  It somewhat replicates the behavior of @(see
gl::def-gl-param-thm), but ignores the shape specifiers provided for the
various cases.</p>

<p>The usage of @('def-fgl-param-thm') is similar to that of @(see
def-fgl-thm), but it accepts several more keyword arguments:</p>

<ul>

<li>@(':param-bindings') is the same as in @(see gl::def-gl-param-thm), but
the shape specifier alist in each entry is ignored.</li>

<li>@(':param-hyp') is the same as in @(see gl::def-gl-param-thm).</li>

<li>@(':split-params') provides the @(see fgl-sat-check) parameters object for
proving that case split provided covers all cases.</li>

<li>@(':solve-params') provides the @(see fgl-sat-check) object for proving each case.</li>

<li>@(':repeat-concl-p') controls whether the conclusion is (if nil)
rewritten/symbolically executed once and then solved separately for each case,
or (if nonnil) rewritten/symbolically executed (and also solved) separately for
each case.</li>

</ul>

")
            
