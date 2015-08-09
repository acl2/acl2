; Milawa - A Reflective Theorem Prover
; Copyright (C) 2005-2009 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
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
; Original author: Jared Davis <jared@kookamara.com>

(in-package "ACL2")

;; assume.lisp
;;
;; We introduce a utility for sharing assumptions across theorems.
;;
;; BOZO this file should be submitted to the ACL2 distribution and removed from
;; our sources.  It should become a "misc" book.

;;; The following legacy doc string was replaced Nov. 2014 by the
;;; auto-generated defxdoc form just below.
; (defdoc assume
;   ":Doc-Section Events
;
;    a system for sharing assumptions across many theorems~/
;
;    We provide a simple table-based system for reusable assumptions.  To the
;    user, this system takes on the following interface:
;    ~bv[]
;      (assume <term>)
;         adds term to the local assumptions
;
;      (unassume <term>)
;         removes <term> from the local assumptions
;
;      (conclude <name> <thm> :hints ... :rule-classes ...)
;         like defth, but proves <thm> under the current assumptions
;    ~ev[]
;
;    For example, consider the following ACL2 rules:
;    ~bv[]
;      (defthm natp-of-plus
;        (implies (and (natp x)
;                      (natp y))
;                 (natp (+ x y))))
;
;      (defthm natp-of-minus
;        (implies (and (natp x)
;                      (natp y)
;                      (< y x))
;                 (natp (- x y))))
;    ~ev[]
;
;    We can convert these into the assume/conclude style as follows:
;    ~bv[]
;      (assume (natp x))
;      (assume (natp y))
;      (conclude natp-of-plus (natp (+ x y)))
;      (conclude natp-of-minus (implies (< y x) (natp (- x y))))
;    ~ev[]~/
;
;    The ~c[assume] and ~c[unassume] commands are implicitly ~il[local], so you
;    can use ~il[encapsulate] in addition to ~c[unassume] to limit the scope of
;    your assumptions.
;
;    The ~c[conclude] command recognizes ~c[thm]s of the following forms:
;    ~bv[]
;       (implies (and hyp1 ... hypN) concl)
;       (implies hyp1 concl)
;       concl
;    ~ev[]
;
;    It augments the <thm> by injecting the current assumptions after the last
;    hyp.  That is, we produce:
;    ~bv[]
;      (implies (and hyp1 ... hypN assm1 ... assmK) concl)
;      (implies (and hyp1 assm1 ... assmK) concl)
;      (implies (and assm1 ... assmK) concl)
;    ~ev[]
;
;    We expect this to be appropriate most of the time, since shared hyps tend to
;    be ``common'' sorts of things, e.g., type constraints, etc.  Meanwhile, the
;    unshared hyps should tend to be more complicated and unusual, so we place
;    them at the front of the rule in an effort to make ``fast failing'' rules.")

(include-book "xdoc/top" :dir :system)

(defxdoc assume
  :parents (events)
  :short "A system for sharing assumptions across many theorems"
  :long "<p>We provide a simple table-based system for reusable assumptions.
 To the user, this system takes on the following interface:</p>

 @({
    (assume <term>)
       adds term to the local assumptions

    (unassume <term>)
       removes <term> from the local assumptions

    (conclude <name> <thm> :hints ... :rule-classes ...)
       like defth, but proves <thm> under the current assumptions
 })

 <p>For example, consider the following ACL2 rules:</p>

 @({
    (defthm natp-of-plus
      (implies (and (natp x)
                    (natp y))
               (natp (+ x y))))

    (defthm natp-of-minus
      (implies (and (natp x)
                    (natp y)
                    (< y x))
               (natp (- x y))))
 })

 <p>We can convert these into the assume/conclude style as follows:</p>

 @({
    (assume (natp x))
    (assume (natp y))
    (conclude natp-of-plus (natp (+ x y)))
    (conclude natp-of-minus (implies (< y x) (natp (- x y))))
 })

 <p>The @('assume') and @('unassume') commands are implicitly @(see local), so
 you can use @(see encapsulate) in addition to @('unassume') to limit the scope
 of your assumptions.</p>

 <p>The @('conclude') command recognizes @('thm')s of the following forms:</p>

 @({
     (implies (and hyp1 ... hypN) concl)
     (implies hyp1 concl)
     concl
 })

 <p>It augments the &lt;thm&gt; by injecting the current assumptions after the
 last hyp.  That is, we produce:</p>

 @({
    (implies (and hyp1 ... hypN assm1 ... assmK) concl)
    (implies (and hyp1 assm1 ... assmK) concl)
    (implies (and assm1 ... assmK) concl)
 })

 <p>We expect this to be appropriate most of the time, since shared hyps tend
 to be ``common'' sorts of things, e.g., type constraints, etc.  Meanwhile, the
 unshared hyps should tend to be more complicated and unusual, so we place them
 at the front of the rule in an effort to make ``fast failing'' rules.</p>")

(table assume.table 'assumptions nil)

(defun assume.get-assumptions (world)
  (declare (xargs :mode :program))
  (cdr (assoc-eq 'assumptions (table-alist 'assume.table world))))

(defun assume.assume-fn (assm)
  `(local (table assume.table 'assumptions
                 (cons ',assm (assume.get-assumptions world)))))

(defmacro assume (assm)
  (assume.assume-fn assm))


(defun assume.unassume-fn (assm)
  (declare (xargs :mode :program))
  `(local (table assume.table 'assumptions
                 (remove-equal ',assm (assume.get-assumptions world)))))

(defmacro unassume (assm)
  (assume.unassume-fn assm))


(defun assume.conclude-fn (name thm extra-args world)
  (declare (xargs :mode :program))
  (cond ((and (consp thm)
              (equal (first thm) 'implies)
              (consp (second thm))
              (equal (first (second thm)) 'and))
         ;; Thm has the form (implies (and hyp1 ... hypN) concl)
         (let ((hyps  (cdr (second thm)))
               (concl (third thm)))
           `(defthm ,name
              (implies (and ,@(append hyps (assume.get-assumptions world)))
                       ,concl)
              ,@extra-args)))
        ((and (consp thm)
              (equal (first thm) 'implies))
         ;; Thm has the form (implies hyp1 concl)
         (let ((hyps  (list (second thm)))
               (concl (third thm)))
           `(defthm ,name
              (implies (and ,@(append hyps (assume.get-assumptions world)))
                       ,concl)
              ,@extra-args)))
        (t
         ;; Thm has the form concl
         `(defthm ,name
            (implies (and ,@(assume.get-assumptions world))
                     ,thm)
            ,@extra-args))))

(defmacro conclude (name thm &rest extra-args)
  `(make-event (assume.conclude-fn ',name ',thm ',extra-args (w state))))





(defmacro MILAWA::assume (&rest args)
  `(ACL2::assume ,@args))

(defmacro MILAWA::unassume (&rest args)
  `(ACL2::unassume ,@args))

(defun milawa-conclude-fn (name thm extra-args world)
  (declare (xargs :mode :program))
  (cond ((and (consp thm)
              (equal (first thm) 'implies)
              (consp (second thm))
              (equal (first (second thm)) 'and))
         ;; Thm has the form (implies (and hyp1 ... hypN) concl)
         (let ((hyps  (cdr (second thm)))
               (concl (third thm)))
           `(MILAWA::defthm ,name
              (implies (and ,@(ACL2::append hyps (ACL2::assume.get-assumptions world)))
                       ,concl)
              ,@extra-args)))
        ((and (consp thm)
              (equal (first thm) 'implies))
         ;; Thm has the form (implies hyp1 concl)
         (let ((hyps  (list (second thm)))
               (concl (third thm)))
           `(MILAWA::defthm ,name
              (implies (and ,@(ACL2::append hyps (ACL2::assume.get-assumptions world)))
                       ,concl)
              ,@extra-args)))
        (t
         ;; Thm has the form concl
         `(MILAWA::defthm ,name
            (implies (and ,@(ACL2::assume.get-assumptions world))
                     ,thm)
            ,@extra-args))))

(defmacro MILAWA::conclude (name thm &rest extra-args)
  `(ACL2::make-event (milawa-conclude-fn ',name ',thm ',extra-args (ACL2::w ACL2::state))))

