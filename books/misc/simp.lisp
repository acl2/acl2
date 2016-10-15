; Copyright (C) 2014, ForrestHunt, Inc.
; Written by Matt Kaufmann, August, 2014
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "misc/bash" :dir :system)

(program)

(defun simp-pairs (clauses wrld state acc)
  (declare (xargs :stobjs state))
  (cond ((endp clauses)
         (value acc))
        (t (let* ((cl (car clauses))
                  (term (assert$ (consp cl)
                                 (car (last cl))))
                  (hyps (dumb-negate-lit-lst (butlast cl 1))))
             (case-match term
               (('equal lhs '?)
                (simp-pairs (cdr clauses)
                            wrld
                            state
                            (cons (cons (untranslate lhs nil wrld)
                                        (untranslate-lst hyps t wrld))
                                  acc)))
               (& (er soft 'simp
                      "A clause returned was ~x0, which doesn't have a final ~
                       literal of the form ~x1."
                      cl '(equal term ?))))))))

(defmacro simp (lhs hyps &key hints verbose)
  `(er-let* ((clauses (bash-term-to-dnf '(implies (and ,@hyps)
                                                  (equal ,lhs ?))
                                        ',hints
                                        ',verbose
                                        t
                                        state)))
     (simp-pairs clauses (w state) state nil)))

(defxdoc simp
  :parents
  (proof-automation)
  :short "<tt>Simp</tt> returns a list of simplified versions of its input
 term, each paired with a hypothesis list under which the input and output
 terms are provably equal."

  :long "

 <p>This tool is implemented on top of another tool, @(tsee bash-term-to-dnf).
 However, @('bash-term-to-dnf') treats its input term as a propositional
 assertion, so it is unsuitable if you want to simpify a non-Boolean term to
 produce a provably equal output term.  The @('simp') tool is well-suited to
 that task.</p>

 <p>However, a case split may occur under simplification.  Moroever, @('simp')
 takes a second argument, which is a list of hypotheses, which are simplified
 too and hence might also generate case splits.  Thus, @('simp') actually
 returns a list of term/hypothesises pairs each of the form
 @('(<simplified-term> <simplified-hypothesis-1>
 ... <simplified-hypothesis-k>)'), where for each such pair the following may
 be expected to be a theorem:</p>

 @({
 (implies (and <simplified-hypothesis-1>
               ...
               <simplified-hypothesis-k>)
          <simplified-term>)
 })

 <p>Example:</p>

 <p>Suppose we have submitted the following two definitions.</p>

 @({
 (defun p (x) (or (stringp x) (acl2-numberp x)))
 (defun f (x) (if (p x) (cons x x) 17))
 })

 <p>Then:</p>

 @({
 ACL2 !>(simp (f x) nil)
  (((CONS X X) (ACL2-NUMBERP X))
   (17 (NOT (STRINGP X))
       (NOT (ACL2-NUMBERP X)))
   ((CONS X X) (STRINGP X)))
 ACL2 !>(simp (f x) nil :hints ((\"Goal\" :in-theory (disable p))))
  ((17 (NOT (P X))) ((CONS X X) (P X)))
 ACL2 !>
 })

 <p>Notice the space in front of the results.  This indicates that what is
 actually returned is an <see topic=\"@(url ERROR-TRIPLE)\">error
 triple</see>, for example as follows in the final case above.</p>

 @({
 (mv ((17 (NOT (P X))) ((CONS X X) (P X))) <state>)
 })

 <p>General Form:</p>

 @({
 (simp term hypothesis-list :hints hints :verbose verbose)
 })

 <p>where @('term') and each member of the list @('hypothesis-list') are terms
 in user-level syntax, @('hints') (which is optional) is a list of @(see hints)
 such as might be given to @(tsee defthm), and a @('verbose') (which is
 optional, @('nil') by default) allows output from the prover if non-@('nil').
 The result is an <see topic=\"@(url ERROR-TRIPLE)\">error triple</see>,
 <tt>(mv nil val state)</tt>, where <tt>val</tt> is a list, each member of
 which is of the form @('(<simplified-term> <simplified-hypothesis-1>
 ... <simplified-hypothesis-k>)'), where @('<simplified-term>') and each
 @('<simplified-hypothesis-i>') are untranslated (user-level) forms, as
 described earlier in this topic.</p>")
