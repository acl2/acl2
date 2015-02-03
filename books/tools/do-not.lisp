; Do-Not Hint
; Copyright (C) 2010 Centaur Technology
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
;
; Additional Copyright Notice.
;
; This file is an extension of the "no-fertilize" hint from the Milawa theorem
; prover, Copyright (C) 2005-2009 Kookamara LLC.  For details, see the file
; projects/milawa/ACL2/acl2-hacks/no-fertilize.lisp.

(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "xdoc/top" :dir :system)

(defun strip-quotes-for-do-not (x)
  ;; Turn any quoted arguments into unquoted args, so that
  ;;   (do-not 'induct 'generalize)
  ;; and
  ;;   (do-not induct generalize)
  ;; are both permitted.
  (declare (xargs :guard t))
  (cond ((atom x)
         nil)
        ((and (quotep (car x))
              (consp (cdr (car x))))
         (cons (unquote (car x))
               (strip-quotes-for-do-not (cdr x))))
        (t
         (cons (car x)
               (strip-quotes-for-do-not (cdr x))))))


(defconst *allowed-for-do-not*
  '(induct preprocess simplify eliminate-destructors
           fertilize generalize eliminate-irrelevance))

(defun check-allowed-for-do-not (x)
  (declare (xargs :guard t))
  (cond ((atom x)
         t)
        ((member-equal (car x) *allowed-for-do-not*)
         (check-allowed-for-do-not (cdr x)))
        (t
         (er hard? 'do-not
             "~x0 is not allowed.  The allowed symbols are ~x1."
             (car x) *allowed-for-do-not*))))


(table do-not-table 'things-not-to-be-done nil)
(table do-not-table 'do-not-inductp nil)

(defmacro do-not (&rest things)
  (declare (xargs :guard t))
  (b* ((things (strip-quotes-for-do-not things))
       (-      (check-allowed-for-do-not things))
       (induct (if (member-eq 'induct things) t nil))
       (others (remove-eq 'induct things)))
      `(with-output
        :off (event summary)
        (progn
          (table do-not-table 'do-not-inductp ',induct)
          (table do-not-table 'things-not-to-be-done ',others)))))


(defsection do-not-hint
  :parents (hints)
  :short "Give @(':do-not') hints automatically."
  :long "<p>@('Do-not-hint') is a computed hint (~l[computed-hints]) that gives
@(':do-not') and perhaps @(':do-not-induct') hints automatically.  For
instance:</p>

@({
  (local (do-not generalize fertilize))
  (defthm thm1 ...)
  (defthm thm2 ...)
  ...
})

<p>is roughly equivalent to:</p>

@({
  (defthm thm1 ... :hints ((\"Goal\" :do-not '(generalize fertilize))))
  (defthm thm2 ... :hints ((\"Goal\" :do-not '(generalize fertilize))))
})

<p>except that the @(':do-not') hints are actually given at
@('stable-under-simplificationp') checkpoints.  This is kind of useful: the
hints will apply to forced subgoals in addition to regular subgoals, and won't
clutter proofs that never hit a @('stable-under-simplificationp')
checkpoint.</p>

<p>The @('do-not') macro expands to some @(see table) events that update the
@('do-not-table').  It should typically be made local to a book or encapsulate
since globally disabling these proof engines is likely to be particularly
disruptive to other proofs.</p>

<p>The arguments to @('do-not') can be any of the keywords used for
@(':do-not') hints, and may also include @('induct') which results in
@(':do-not-induct t') hints.</p>"

  (defun do-not-hint (world stable-under-simplificationp state)
    (declare (xargs :mode :program :stobjs state))
    (b* (((unless stable-under-simplificationp)
          ;; No reason to give a hint until stable-under-simplificationp.
          nil)

         (tbl     (table-alist 'do-not-table world))
         (things  (cdr (assoc 'things-not-to-be-done tbl)))
         (inductp (cdr (assoc 'do-not-inductp tbl)))

         ((when (and (atom things)
                     (not inductp)))
          ;; Nothing is prohibited, so give no hint.
          nil)

         (- (or (gag-mode)
                (cw "~%;; do-not-hint: prohibiting ~x0.~|"
                    (if inductp
                        (cons 'induct things)
                      things))))

         (hint (if inductp
                   '(:do-not-induct t)
                 nil))
         (hint (if (consp things)
                   (append `(:do-not ',things) hint)
                 hint)))
      hint))

  (add-default-hints!
   '((do-not-hint world stable-under-simplificationp state))))
