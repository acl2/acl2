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
(include-book "xdoc/top" :dir :system)
(include-book "std/util/bstar" :dir :system)

(defxdoc defmvtypes
  :parents (std/util)
  :short "Introduce type-prescription rules for a function that returns
multiple values."

  :long "<p>Defmvtypes is just a shorthand that allows you to quickly introduce
type-prescription rules for a function that returns multiple values.</p>

<p>General form:</p>

@({
 (defmvtypes fn return-types
    [:hyp   hyp]
    [:hints hints])
})

<p>For example,</p>

@({
 (defmvtypes foo
   (true-listp nil booleanp (and (consp x) (true-listp x))))
})

<p>introduces three type-prescription rules:</p>
<ol>
 <li>@('(true-listp (mv-nth 0 (foo ...))')</li>
 <li>@('(booleanp (mv-nth 2 (foo ...))')</li>
 <li>@('(and (consp (mv-nth 3 (foo ...)))
             (true-listp (mv-nth 3 (foo ...))))')</li>
</ol>


<h3>Usage and Arguments</h3>

<p>Each of the @('return-types') should either be a plain symbol like
@('true-listp'), or a term whose only free variable is @('pkg::x'), where
@('pkg') is the package of @('fn').</p>

<p>The theorems introduced will be unconditional unless a @(':hyp') argument is
provided.  For instance,</p>

@({
 (defmvtypes foo
   (nil nil true-listp)
   :hyp (bar a b c))
})

<p>Would result in:</p>

@({
 (implies (bar a b c)
          (true-listp (mv-nth 2 (foo ...))))
})

<p>The @(':hints') argument can be used to specify custom @(see acl2::hints) to
use.  The same hints are given to each theorem.</p>

<h3>Interaction with @(see force)</h3>

<p>Sometimes @(see force) can get in the way of proving nice, hypothesis-free
type-prescription rules.  To try to avoid this, by default @('defmvtypes')
automatically:</p>

<ul>
<li>Disables forcing before submitting its theorems, then</li>
<li>Uses @(see acl2::computed-hints) to re-enable @('force') when goals are
@('stable-under-simplification').</li>
</ul>

<p>The hope is that this will generally prevent @(see force) from screwing up
type-prescription theorems, but will allow it to be used when it would be
useful to do so.  If you do <b>not</b> want this behavior, you can suppress it
by giving any @(':hints').</p>")

(defun inducting-p (clause-id)
  (declare (xargs :mode :program))
  (consp (acl2::access acl2::clause-id clause-id :pool-lst)))

(defun defmvtypes-nonrecursive-hint (id stable-under-simplificationp)
  ;; Hint to use for defmvtypes of non-recursive functions.  Allow forcing
  ;; after we've stabilized.
  (declare (xargs :mode :program))
  (declare (ignore id))
  (and stable-under-simplificationp
       '(:in-theory (enable (:executable-counterpart force)))))

(defun defmvtypes-recursive-hint (id stable-under-simplificationp)
  ;; Hint to use for defmvtypes of recursive functions.  Allow forcing, but
  ;; only after we've stabilized and already tried induction.
  (declare (xargs :mode :program))
  (and stable-under-simplificationp
       (inducting-p id)
       '(:in-theory (enable (:executable-counterpart force)))))

(defun defmvtypes-element-to-thm
  (spec  ; the type specifier (symbol/term)
   hyp   ; user supplied hyps
   fn    ; function to prove things about
   args  ; formals of the function
   recp  ; is this function recursive?
   place ; the return-value number
   hints ; user-supplied hints
   )
  ;; Returns ((defthm ...)) or NIL
  (declare (xargs :mode :program))
  (b* (((unless spec)
        nil)
       (thmname (intern-in-package-of-symbol
                 (concatenate 'string
                              (symbol-name fn) "-MVTYPES-"
                              (coerce (explode-atom place 10) 'string))
                 fn))
       (x       (intern-in-package-of-symbol "X" fn))
       (rval    `(mv-nth ,place (,fn . ,args)))
       (concl   (cond
                 ((symbolp spec)
                  (list spec rval))
                 ((atom spec)
                  (er hard? 'defmvtypes-element-to-thm
                      "Bad return-value type specifier: ~x0." spec))
                 (t
                  (let ((new (subst rval x spec)))
                    (if (equal new spec)
                        (er hard? 'defmvtypes-element-to-thm
                            "Bad return-value type specifier: does not ~
                             mention ~x0: ~x1." x spec)
                      new))))))
    `((defthm ,thmname
        ,(if hyp
             `(implies ,hyp ,concl)
           concl)
        :rule-classes :type-prescription
        :hints ,(cond (hints hints)
                      (recp  '((defmvtypes-recursive-hint
                                id stable-under-simplificationp)))
                      (t     '((defmvtypes-nonrecursive-hint
                                 id stable-under-simplificationp))))))))

(defun defmvtypes-elements-to-thms (specs hyp fn args recp place hints)
  (declare (xargs :mode :program))
  (if (atom specs)
      nil
    (append (defmvtypes-element-to-thm (car specs)
              hyp fn args recp place hints)
            (defmvtypes-elements-to-thms (cdr specs)
              hyp fn args recp (+ 1 place) hints))))

(defun defmvtypes-fn (specs fn hyp hints world)
  (declare (xargs :mode :program))
  (b* ((args (getprop fn 'acl2::formals :bad
                      'acl2::current-acl2-world world))
       ((when (eq args :bad))
        (er hard? 'defmvtypes-fn "Failed to find formals for ~x0.~%" fn))
       (recp (consp (getprop fn 'acl2::induction-machine nil
                             'current-acl2-world world))))
    `(encapsulate
       ()
       ,(if hints
            `(local (in-theory (enable ,fn)))
          `(local (in-theory (e/d (,fn)
                                  ((:executable-counterpart force))))))
       ,@(defmvtypes-elements-to-thms specs hyp fn args recp 0 hints))))

(defmacro defmvtypes (fn specs &key hyp hints)
  `(make-event (defmvtypes-fn ',specs ',fn ',hyp ',hints (w state))))


;; Basic tests

(local
 (encapsulate
   ()
   (defund foo (x y)
     (mv (cons x y)
         0
         1
         (if x t nil)
         (cons x nil)))

   (defmvtypes foo
     (consp (equal x 0) posp booleanp (and (consp x) (true-listp x))))

   (defun bar (a b)
     (mv a b))

   (defmvtypes bar
     (consp integerp)
     :hyp (and (force (consp a))
               (force (integerp b))))

   (defun baz (a b) (bar a b))

   (defmvtypes baz
     (atom rationalp)
     :hyp (and (atom a)
               (rationalp b))
     :hints(("Goal")))

   (defun f (x)
     (b* (((when (atom x)) (mv 0 t 0))
          ((mv a b c) (f (cdr x))))
       (mv a
           (not b)
           (+ 1 c))))

   (defmvtypes f
     ((equal x 0) booleanp natp))))
