; Computational Object Inference
; Copyright (C) 2005-2014 Kookamara LLC
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


(in-package "ACL2")

(include-book "defdoc")

(include-book "xdoc/top" :dir :system)

(defun event-sequence (args)
  (if args `(encapsulate
		()
	      ,@args)
    `(progn)))

;; ===================================================================
;;
;; \#if preprocessor macro
;;
;; ===================================================================

(defmacro \#if (p &rest args)
  `(make-event
    (event-sequence (if ,p ',args nil))))

;;; The following legacy doc string was replaced Nov. 2014 by the
;;; auto-generated defxdoc form just below.
; (def::doc \#if
;
;   :section \#if
;
;   :one-liner "A C-preprocessor-like macro for conditional events"
;
;   :details (docstring
; "
;   \\#if is a C-preprocessor-like macro that allows a sequence of
; embedded event forms to be made conditional on state.
;
;   (\\#if (equal (@ acl2-version) \"ACL2 Version 3.3\")
;
;     (defun test1 (x) x)
;     (defthm test-equal
;       (equal (test x) x))
;
;    )
;
;   The first argument to \\#if is a predicate that is evaluated
; in the current state.  If the predicate evaluates to true, the
; remaining forms are submitted to ACL2.  If not, the remaining
; forms are skipped.  \\if events can be nested.
;
;   "(docref"#if-else")"
;   "(docref"#cond")"
;
; "))

(defxdoc |#IF|
  :parents (|#IF|)
  :short "A C-preprocessor-like macro for conditional events"
  :long "<p>\\#if is a C-preprocessor-like macro that allows a sequence of
 embedded event forms to be made conditional on state.</p>

 <p>(\\#if (equal (@@ acl2-version) \"ACL2 Version 3.3\")</p>

 <p>(defun test1 (x) x) (defthm test-equal (equal (test x) x))</p>

 <p>)</p>

 <p>The first argument to \\#if is a predicate that is evaluated in the current
 state.  If the predicate evaluates to true, the remaining forms are submitted
 to ACL2.  If not, the remaining forms are skipped.  \\if events can be
 nested.</p>

 <p>See <see topic='@(url |#IF-ELSE|)'>#if-else</see> See <see topic='@(url
 |#COND|)'>#cond</see></p>")

;; ===================================================================

(local
 (\#if (@ acl2-version) (defun test1 (x) x)))

(local
 (\#if (not (@ acl2-version)) (defun test2 (x) x)))

;; ===================================================================
;;
;; \#if-else preprocessor macro
;;
;; ===================================================================

(defmacro \#if-else (p e1 e2)
  `(make-event
    (event-sequence (if ,p '(,e1) '(,e2)))))

;;; The following legacy doc string was replaced Nov. 2014 by the
;;; auto-generated defxdoc form just below.
; (def::doc \#if-else
;
;   :section \#if-else
;
;   :one-liner "A C-preprocessor-like macro for alternate conditional events"
;
;   :details (docstring
; "
;   \\#if-else is a C-preprocessor-like macro that alternates
; between two different embedded event forms depending on the
; result of evaluating the condition.
;
;   (\#if-else (equal (@ acl2-version) \"ACL2 Version 3.3\")
;
;     (defun test1 (x) (1- x))
;
;     (defun test1 (x) (1+ x))
;
;    )
;
;   The first argument to \\#if-else is a predicate that is evaluated
; in the current state.  If the predicate evaluates to true, the second
; argument to if-else will be submitted to ACL2.  If the predicate
; evaluates to false, the third argument will be submitted. \\#if-else
; events can be nested.
;
;   "(docref"#if")"
;   "(docref"#cond")"
;
; "))

(defxdoc |#IF-ELSE|
  :parents (|#IF-ELSE|)
  :short "A C-preprocessor-like macro for alternate conditional events"
  :long "<p>\\#if-else is a C-preprocessor-like macro that alternates between
 two different embedded event forms depending on the result of evaluating the
 condition.</p>

 <p>(#if-else (equal (@@ acl2-version) \"ACL2 Version 3.3\")</p>

 <p>(defun test1 (x) (1- x))</p>

 <p>(defun test1 (x) (1+ x))</p>

 <p>)</p>

 <p>The first argument to \\#if-else is a predicate that is evaluated in the
 current state.  If the predicate evaluates to true, the second argument to
 if-else will be submitted to ACL2.  If the predicate evaluates to false, the
 third argument will be submitted. \\#if-else events can be nested.</p>

 <p>See <see topic='@(url |#IF|)'>#if</see> See <see topic='@(url
 |#COND|)'>#cond</see></p>")

;; ===================================================================

(defun cond-to-if (cond)
  (if (consp cond)
      `(if ,(caar cond) '(,(cadar cond))
	 ,(cond-to-if (cdr cond)))
    nil))

(defun make-cond-event (cond-form)
  `(make-event
    (event-sequence ,(cond-to-if cond-form))))

;; ===================================================================
;;
;; \#cond preprocessor macro
;;
;; ===================================================================

(defmacro \#cond (&rest args)
  (make-cond-event args))

;;; The following legacy doc string was replaced Nov. 2014 by the
;;; auto-generated defxdoc form just below.
; (def::doc \#cond
;
;   :section \#cond
;
;   :one-liner "A C-preprocessor-like macro for alternate conditional events"
;
;   :details (docstring
; "
;   \\#cond is a C-preprocessor-like macro that selects zero
; or one event among a possible sequence of events based upon
; the result of evaluating the condition associated with the
; event.
;
;   (\\#cond
;    ((@ test3) (defun test3 (x) x))
;    ((@ test4) (defun test4 (x) x))
;    ((@ test5) (defun test5 (x) x))
;   )
;
;   The \\#cond macro accepts a sequence of terms in cond form.
; Each predicate of the cond form is evaluated in sequence.  If a
; predicate evaluates to true, the term associated with that
; predicate will be submitted to ACL2.  If no predicate evalutes
; to true, the event is a no-op.
;
;   "(docref"#if")"
;   "(docref"#if-else")"
;
; "))

(defxdoc |#COND|
  :parents (|#COND|)
  :short "A C-preprocessor-like macro for alternate conditional events"
  :long "<p>\\#cond is a C-preprocessor-like macro that selects zero or one
 event among a possible sequence of events based upon the result of evaluating
 the condition associated with the event.</p>

 <p>(\\#cond ((@@ test3) (defun test3 (x) x)) ((@@ test4) (defun test4 (x) x))
    ((@@ test5) (defun test5 (x) x)) )</p>

 <p>The \\#cond macro accepts a sequence of terms in cond form.  Each predicate
 of the cond form is evaluated in sequence.  If a predicate evaluates to true,
 the term associated with that predicate will be submitted to ACL2.  If no
 predicate evalutes to true, the event is a no-op.</p>

 <p>See <see topic='@(url |#IF|)'>#if</see> See <see topic='@(url
 |#IF-ELSE|)'>#if-else</see></p>")

;; ===================================================================

(local
 (\#cond
  ((equal (@ acl2-version) "1") (defun test3 (x) x))
  ((equal (@ acl2-version) "2") (defun test4 (x) x))
  (t                            (defun test5 (x) x))
  ))