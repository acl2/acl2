; FGL - A Symbolic Simulation Framework for ACL2
;; SPDX-FileCopyrightText: Copyright 2025 Arm Limited and/or its affiliates <open-source-office@arm.com>
;; SPDX-License-Identifier: BSD-3-Clause
;; 
;; Redistribution and use in source and binary forms, with or without
;; modification, are permitted provided that the following conditions are
;; met:

;; o Redistributions of source code must retain the above copyright
;;   notice, this list of conditions and the following disclaimer.

;; o Redistributions in binary form must reproduce the above copyright
;;   notice, this list of conditions and the following disclaimer in the
;;   documentation and/or other materials provided with the distribution.

;; o Neither the name of the copyright holder nor the names of
;;   its contributors may be used to endorse or promote products derived
;;   from this software without specific prior written permission.

;; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
;; "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
;; LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
;; A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
;; HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
;; SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
;; LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
;; DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
;; THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
;; (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
;; OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

;; Author: Sol Swords <sol.swords@arm.com>

(in-package "FGL")

(include-book "fancy-ev")
(include-book "rules")

;; This book defines a way to scrape info from the FGL stack, resembling a
;; backtrace.  The user provides a backtrace specification consisting of a list
;; containing rule names paired with lists of variables.  For each stack frame
;; that is an application of some listed rule, we collect a backtrace frame
;; containing that rule name and the (top-level -- i.e. major-frame) bindings
;; for the listed variables.

(fty::defoption maybe-fgl-generic-rune fgl-generic-rune-p)

(defprod backtrace-spec
  :parents (backtrace)
  :short "Specification of what to collect in an FGL backtrace"
  ((rune maybe-fgl-generic-rune-p "FGL rule name to match, or NIL to match only the bottom (goal) frame.")
   (vars pseudo-var-list-p "List of variables of that rule to collect."))
  :layout :list)

(fty::deflist backtrace-speclist :elt-type backtrace-spec :true-listp t
  :parents (backtrace))


(defprod backtrace-frame
  :parents (backtrace)
  :short "Datatype for FGL backtrace frames"
  ((index natp :rule-classes :type-prescription "Stack frame number")
   (rune maybe-fgl-generic-rune-p "Name of the rule applied at the frame")
   (objs fgl-object-bindings-p "Selected symbolic object bindings"))
  :layout :list)

(fty::deflist backtrace :elt-type backtrace-frame :true-listp t
  :parents (backtraces))

(define backtrace-speclist-find ((rune maybe-fgl-generic-rune-p)
                                 (x backtrace-speclist-p))
  :returns (spec (iff (backtrace-spec-p spec) spec))
  (if (atom x)
      nil
    (if (equal (maybe-fgl-generic-rune-fix rune)
               (backtrace-spec->rune (car x)))
        (backtrace-spec-fix (car x))
      (backtrace-speclist-find rune (cdr x)))))


(define bindings-extract-vars ((vars pseudo-var-list-p)
                               (bindings fgl-object-bindings-p))
  :returns (new-bindings fgl-object-bindings-p)
  (if (atom vars)
      nil
    (let ((look (hons-assoc-equal (pseudo-var-fix (car vars))
                                  (fgl-object-bindings-fix bindings))))
      (if look
          (cons (cons (pseudo-var-fix (car vars)) (cdr look))
                (bindings-extract-vars (cdr vars) bindings))
        (bindings-extract-vars (cdr vars) bindings)))))

(define stack-backtrace-aux ((n natp)
                             (specs backtrace-speclist-p)
                             (stack))
  :guard (<= n (stack-frames stack))
  :returns (backtrace backtrace-p)
  :measure (nfix (- (stack-frames stack) (nfix n)))
  (b* (((when (mbe :logic (zp (- (stack-frames stack) (nfix n)))
                   :exec (eql n (stack-frames stack))))
        nil)
       (rule (stack-nth-frame-rule n stack))
       (rune (and rule (fgl-generic-rule->rune rule)))
       (spec (backtrace-speclist-find rune specs))
       ((unless spec)
        (stack-backtrace-aux (1+ (lnfix n)) specs stack))
       ((backtrace-spec spec))
       (bindings (stack-nth-frame-bindings n stack)))
    (cons (backtrace-frame n rune (bindings-extract-vars spec.vars bindings))
          (stack-backtrace-aux (1+ (lnfix n)) specs stack))))


(define stack-backtrace ((specs backtrace-speclist-p)
                         stack)
  :returns (backtrace backtrace-p)
  (stack-backtrace-aux 0 specs stack))

(define interp-st-stack-backtrace ((specs backtrace-speclist-p) interp-st)
  :parents (backtraces)
  :short "Collect a backtrace object from the FGL rewriter stack, given a list of rule specifications"
  :returns (backtrace backtrace-p)
  (stobj-let ((stack (interp-st->stack interp-st)))
             (bt)
             (stack-backtrace specs stack)
             bt))

(fancy-ev-add-primitive interp-st-stack-backtrace (backtrace-speclist-p specs))

(define stack-backtrace-top-aux ((n natp)
                                 (specs backtrace-speclist-p)
                                 (stack))
  :guard (<= n (stack-frames stack))
  :returns (frame (iff (backtrace-frame-p frame) frame))
  :measure (nfix (- (stack-frames stack) (nfix n)))
  (b* (((when (mbe :logic (zp (- (stack-frames stack) (nfix n)))
                   :exec (eql n (stack-frames stack))))
        nil)
       (rule (stack-nth-frame-rule n stack))
       (rune (and rule (fgl-generic-rule->rune rule)))
       (spec (backtrace-speclist-find rune specs))
       ((unless spec)
        (stack-backtrace-top-aux (1+ (lnfix n)) specs stack))
       ((backtrace-spec spec))
       (bindings (stack-nth-frame-bindings n stack)))
    (backtrace-frame n rune (bindings-extract-vars spec.vars bindings)))
  ///
  (defretd <fn>-in-terms-of-stack-backtrace-aux
    (equal frame (car (stack-backtrace-aux n specs stack)))
    :hints(("Goal" :in-theory (enable stack-backtrace-aux)))))


(define stack-backtrace-top ((specs backtrace-speclist-p)
                             stack)
  :returns (frame (iff (backtrace-frame-p frame) frame))
  (stack-backtrace-top-aux 0 specs stack)
  ///
  
  (defretd <fn>-in-terms-of-stack-backtrace
    (equal frame (car (stack-backtrace specs stack)))
    :hints(("Goal" :in-theory (enable stack-backtrace
                                      stack-backtrace-top-aux-in-terms-of-stack-backtrace-aux)))))

(define interp-st-stack-backtrace-top ((specs backtrace-speclist-p) interp-st)
  :returns (frame (iff (backtrace-frame-p frame) frame))
  :parents (backtraces)
  :short "Produce a backtrace frame for the top FGL rewriter stack frame that matches any
of a list of rule specifications"
  (stobj-let ((stack (interp-st->stack interp-st)))
             (bt)
             (stack-backtrace-top specs stack)
             bt))

(fancy-ev-add-primitive interp-st-stack-backtrace-top (backtrace-speclist-p specs))


(define stack-full-backtrace-aux ((n natp)
                                  (stack))
  :guard (<= n (stack-frames stack))
  :returns (backtrace backtrace-p)
  :measure (nfix (- (stack-frames stack) (nfix n)))
  (b* (((when (mbe :logic (zp (- (stack-frames stack) (nfix n)))
                   :exec (eql n (stack-frames stack))))
        nil)
       (rule (stack-nth-frame-rule n stack))
       (rune (and rule (fgl-generic-rule->rune rule)))
       (bindings (stack-nth-frame-bindings n stack)))
    (cons (backtrace-frame n rune bindings)
          (stack-full-backtrace-aux (1+ (lnfix n)) stack))))


(define stack-full-backtrace (stack)
  :returns (backtrace backtrace-p)
  (stack-full-backtrace-aux 0 stack))

(define interp-st-stack-full-backtrace (interp-st)
  :returns (backtrace backtrace-p)
  :parents (backtraces)
  :short "Produce a full backtrace for the FGL rewriter stack, containing all top-level bindings of all rules"
  (stobj-let ((stack (interp-st->stack interp-st)))
             (bt)
             (stack-full-backtrace stack)
             bt))

(fancy-ev-add-primitive interp-st-stack-full-backtrace t)


(local (defthm fgl-object-alist-p-when-bindings
         (implies (fgl-object-bindings-p x)
                  (fgl-object-alist-p x))
         :hints(("Goal" :in-theory (enable fgl-object-alist-p
                                           fgl-object-bindings-p)))))

(define backtrace-frame-to-obj ((x backtrace-frame-p))
  :parents (backtrace)
  :short "Turn a FGL backtrace frame into a proper symbolic object"
  :returns (obj fgl-object-p)
  :guard-debug t
  (b* (((backtrace-frame x)))
    (g-cons (g-concrete x.index)
            (g-cons (g-concrete x.rune)
                    (g-cons (g-map '(:g-map) x.objs) nil)))))

(define backtrace-to-obj ((x backtrace-p))
  :parents (backtraces)
  :short "Turn a FGL backtrace into a proper symbolic object"
  :returns (obj fgl-object-p)
  (if (atom x)
      nil
    (g-cons (backtrace-frame-to-obj (car x))
            (backtrace-to-obj (cdr x)))))
   
(fancy-ev-add-primitive backtrace-to-obj (backtrace-p x))

(define stack-find-top-rule-frame-aux ((n natp)
                                       (rune maybe-fgl-generic-rune-p)
                                       (stack))
  :guard (<= n (stack-frames stack))
  :returns (index acl2::maybe-natp :rule-classes :type-prescription)
  :measure (nfix (- (stack-frames stack) (nfix n)))
  (b* (((when (mbe :logic (zp (- (stack-frames stack) (nfix n)))
                   :exec (eql n (stack-frames stack))))
        nil)
       ((when (equal (maybe-fgl-generic-rune-fix rune)
                     (b* ((rule (stack-nth-frame-rule n stack)))
                       (and rule (fgl-generic-rule->rune rule)))))
        (lnfix n)))
    (stack-find-top-rule-frame-aux (1+ (lnfix n)) rune stack))
  ///
  (defret <fn>-upper-bound
    (implies index
             (< index (stack-frames stack)))
    :rule-classes :linear))

(define stack-find-top-rule-frame ((rune maybe-fgl-generic-rune-p)
                                   stack)
  :returns (index acl2::maybe-natp :rule-classes :type-prescription)
  (stack-find-top-rule-frame-aux 0 rune stack)
  ///
  (defret <fn>-upper-bound
    (implies index
             (< index (stack-frames stack)))
    :rule-classes :linear))

(define stack-top-rule-frame-bindings ((rune maybe-fgl-generic-rune-p)
                                       stack)
  :returns (bindings fgl-object-bindings-p)
  (b* ((index (stack-find-top-rule-frame rune stack)))
    (and index
         (stack-nth-frame-bindings index stack))))

(define interp-st-stack-top-frame-bindings ((rune maybe-fgl-generic-rune-p)
                                            interp-st)
  :returns (bindings fgl-object-bindings-p)
  (stobj-let ((stack (interp-st->stack interp-st)))
             (bindings)
             (stack-top-rule-frame-bindings rune stack)
             bindings))

(fancy-ev-add-primitive interp-st-stack-top-frame-bindings (maybe-fgl-generic-rune-p rune))



(define function-rules-to-backtrace-spec-aux ((x fgl-rulelist-p)
                                              (formals pseudo-var-list-p)
                                              (vars pseudo-var-list-p))
  :returns (specs backtrace-speclist-p)
  (b* (((when (atom x))
        nil)
       (x1 (car x))
       ((unless (fgl-rule-case x1 :rewrite))
        (function-rules-to-backtrace-spec-aux (cdr x) formals vars))
       ((fgl-rule-rewrite x1))
       ((unless (pseudo-term-case x1.lhs :fncall))
        (function-rules-to-backtrace-spec-aux (cdr x) formals vars))
       ((pseudo-term-fncall x1.lhs))
       ((unless (eql (len x1.lhs.args) (len formals)))
        (function-rules-to-backtrace-spec-aux (cdr x) formals vars))
       (pairs (pairlis$ formals x1.lhs.args))
       (subst (cmr::termlist-subst vars pairs))
       (subst-vars (cmr::termlist-vars subst)))
    (cons (backtrace-spec x1.rune subst-vars)
          (function-rules-to-backtrace-spec-aux (cdr x) formals vars))))


(define function-rules-to-backtrace-spec ((fn pseudo-fnsym-p)
                                          (vars pseudo-var-list-p)
                                          state)
  :parents (backtraces)
  :short "Get a set of FGL backtrace specifiers for all FGL rules targeting a function symbol"
  (b* ((wrld (w state))
       ((mv ?err rules) (fgl-function-rules fn wrld))
       (formals (getpropc fn 'formals t wrld))
       ((unless (pseudo-var-list-p formals))
        (raise "Bad formals for ~x0: ~x1" fn formals)
        nil))
    (function-rules-to-backtrace-spec-aux rules formals vars)))

(fancy-ev-add-primitive function-rules-to-backtrace-spec (and (pseudo-fnsym-p fn)
                                                              (pseudo-var-list-p vars)))

(defxdoc backtraces
  :parents (fgl-rewrite-rules)
  :short "Accessing a backtrace during FGL rewriting"
  :long "<p>The following utilities allow FGL to retrieve backtrace data while
rewriting. These can be used to help debug code proofs or FGL rewriter
problems.</p>

<h3>Specifying backtrace data to collect</h3>
<ul>

<li>@(see backtrace-spec) is the data structure specifying an FGL rule to
include in the backtrace and which variables of that rule to include.  A list
of these (a @(see backtrace-speclist)) are given to the backtrace collection
functions to get data from multiple rules.</li>

<li>@(see function-rules-to-backtrace-spec) collects backtrace specs for all
FGL rewrite rules targeting a particular function.</li>

</ul>

<h3>Collecting a backtrace of symbolic values</h3>

<ul>

<li>@(see interp-st-stack-backtrace) collects a backtrace for a list of
backtrace-specs. The resulting object is a list of @(see backtrace-frame)
objects, giving the frame number, rule name, and variable bindings.</li>

<li>@(see interp-st-stack-backtrace-top) returns the innermost frame (car) of
the @('interp-st-stack-backtrace'), stopping once it finds it.</li>

<li>@(see interp-st-stack-full-backtrace) collects a full backtrace; that is,
one containing all of the bindings for all of the frames of the FGL stack, as a
list of @(see backtrace-frame) objects.</li>

</ul>

<h3>Evaluating a backtrace under a satisfying assignment</h3>

<p>A backtrace is a data structure with symbolic objects in it. Sometimes it is
useful to evaluate this object to get concrete values for all of the symbolic
objects.</p>

<ul>

<li>@(see backtrace-to-obj) and @(see backtrace-frame-to-obj) construct proper
symbolic objects from (respectively) a backtrace or backtrace-frame. It's
likely that one of these already is a proper symbolic object, but these functions
make sure of it.</li>

<li>@(see fgl-counterexamples) for utilities that can be used to derive a
counterexample and evaluate the backtrace under it.</li>

</ul>

")
