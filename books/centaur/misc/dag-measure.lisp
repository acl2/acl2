; Copyright (C) 2008-2011 Centaur Technology
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

; cert_param: (non-acl2r)

(include-book "std/util/define" :dir :system)
(include-book "std/basic/defs" :dir :system)
(include-book "tools/flag" :dir :system)
(include-book "std/basic/two-nats-measure" :dir :system)
(include-book "misc/hons-help" :dir :system) ;; for alist-keys/vals
(include-book "tools/templates" :dir :system)
(local (include-book "std/lists/sets" :dir :system))

;; This book provides a generic framework for a semi-common problem: we have a
;; finite DAG that is encoded in such a way that it isn't obvious that it's
;; acyclic; e.g., perhaps it's represented as an alist mapping nodes to
;; successor lists.  We then want to do some traversal of the graph, but what
;; measure can we use?  Often one gets around this by keeping track of seen
;; nodes, but this complicates the algorithm and makes it much more difficult
;; to prove anything about it.  We provide a generic termination argument for
;; such traversals that doesn't require passing along a separate seen list.

;; Generic theory for finite graphs: we just have a successor function and a
;; set of all nodes.  These don't have any constraints.

(defxdoc def-dag-measure
  :parents (proof-automation)
  :short "Generic framework that allows simple traversals of DAGs."
  :long "<p>Suppose we have a representation of some finite DAG, but it is
encoded in such a way that it isn't obvious that it's acyclic.  E.g., perhaps
our representation is an alist mapping each node to its list of successors.  We
then want to do some traversal of the graph.  The challenge is to prove that our traversal function terminates.</p>

<p>One typical way to do this is to record the nodes we've already traversed to
ensure that we don't re-traverse them; then, an appropriate measure for
termination is the count of nodes that we haven't yet traversed.  Writing
functions in this style is doable, but passing around the record of nodes we've
already seen complicates reasoning about the function.</p>

<p>This framework helps to streamline a different approach.  In this approach, we define
<ul>
<li>a relatively fast, executable function that checks whether all paths from the current node through the graph are loop-free</li>
<li>a measure function that takes a node in the graph, where if node A is loop-free and has successor node B, then measure(B) &lt; measure(A).</li>
</ul>
This combination allows traversal functions to be written in this style:</p>
@({
  (mutual-recursion
    (defun traverse-node (node graph)
      (declare (xargs :guard (loopfree-p node graph)
                      :measure (node-measure node graph)))
      (if (mbt (loopfree-p node graph))
         (do-something node (traverse-list (successors node graph) graph))
       (fail)))
    (defun traverse-list (nodelist graph)
      (declare (xargs :guard (loopfreelist-p nodelist graph)
                      :measure (node-list-measure list graph)))
      (if (atom nodelist)
          (end-val)
        (combine (traverse-node (car nodelist) graph)
                 (traverse-list (cdr nodelist) graph)))))
})

<p>The framework is generic as to how the successors of a node are determined;
e.g., they could be stored in an alist and extracted with assoc, or generated
by some arbitrary function.  It expects the successor function to produce a
list of nodes.  If the successors are not conveniently encoded as a list of
nodes, you might still be able to work with this framework with some extra
proof work.  Another way in which the framework is not completely generic is
that it uses an underlying traversal function that stores seen nodes in a fast
alist.  If this isn't the right encoding for your problem, you may again need
to do some extra proofs to use this framework.</p>

<p>The following example shows how to use the macro @('def-dag-measure')
provided by this book:</p>
@({
 (def-dag-measure algraph
   :graph-formals (graph)
   :successors-expr (cdr (assoc-eq x graph))
   :nodes-expr (strip-cars graph)
   :guard (and (alistp graph) (symbol-list-listp (strip-cdrs graph)))
   :node-guard (symbolp x)
   :node-list-guard (symbol-listp x))
})

<p>In the above example:</p>
<ul>
<li>@('algraph') is the base name that will be used for the functions
produced</li>
<li>The @(':graph-formals') are a list of extra arguments required in
each function that operates on a graph.</li>
<li>@(':successors-expr') and @(':nodes-expr') describe the representation of the
graph: @(':successors-expr') is an expression that, given graph node @('x'),
returns the list of successors of @('x'), and @(':nodes-expr') is an expression
that produces the full list of nodes of the graph.</li>
<li>@(':guard'), @(':node-guard'), and @(':node-list-guard') specify guards for
the functions.</li>
</ul>

<p>This produces the following functions:</p>
<ul>
<li>@('(algraph-loopfree-p x graph)') and @('(algraph-loopfreelist-p x graph)') return @('t') if the portion of the graph reachable from (node, resp. node list) @('x') is acyclic.  These are guard-verified fast (?) executable functions that do a linear time and space traversal of the graph.  Theorems are provided showing that if a node is loop free, then its successors are loop free.</li>
<li>@('(algraph-measure x graph)') and @('(algraph-list-measure x graph)') are measure functions that can be used as the @('node-measure') and @('node-list-measure') in mutual recursions such as @('traverse') above.</li>
</ul>

<p>An example of how to use these functions to admit a simple node-count function is also provided by the macro, and reproduced here:</p>
@({
 (mutual-recursion
  (defun algraph-count (x graph)
    (declare (xargs :measure (algraph-measure x graph)
                    :guard (and (alistp graph)
                                (symbol-list-listp (strip-cdrs graph))
                                (symbolp x)
                                (algraph-loopfree-p x graph))))
    (if (mbt (algraph-loopfree-p x graph))
        (+ 1 (algraph-count-list (cdr (assoc-eq x graph)) graph))
      0))
  (defun algraph-count-list (x graph)
    (declare (xargs :measure (algraph-list-measure x graph)
                    :guard (and (alistp graph)
                                (symbol-list-listp (strip-cdrs graph))
                                (symbol-listp x)
                                (algraph-loopfreelist-p x graph))))
    (if (atom x)
        0
      (+ (algraph-count (car x) graph)
         (algraph-count-list (cdr x) graph)))))
})
")

;; <p>The most basic way to use the framework is to define a mutual recursion
;; similar to the definition of @('fg-depth-memo') and @('fg-depth-memo-list'), but with the following substitutions:</p>
;; <ul>
;; <li>replace the occurrence of @('(fg-successors x)') with an expression for the
;; list of successors of x in your graph.</li>
;; <li>replace each occurrence of @('(fg-nodes)') with an expression for a list
;; containing all graph nodes (it must be a theorem that if x is not in this list,
;; then it has no successors).</li>
;; </li>
;; </ul>

;; <p>Then, define analogues of the following functions:</p>
;; <ul>
;; <li>@('fg-loopfree-p')</li>
;; <li>@('fg-loopfreelist-p')</li>
;; <li>@('fg-measure')</li>
;; <li>@('fg-list-measure-aux')</li>
;; <li>@('
;; "



(define fg-memo-p (x)
  (if (atom x)
      t
    (and (or (atom (car x))
             (eq (cdar x) :back)
             (eq (cdar x) :loop)
             (natp (cdar x)))
         (fg-memo-p (cdr x))))
  ///
  (defthm lookup-in-fg-memo
    (implies (and (fg-memo-p x)
                  (hons-assoc-equal k x)
                  (not (equal (cdr (hons-assoc-equal k x)) :back))
                  (not (equal (cdr (hons-assoc-equal k x)) :loop)))
             (and (natp (cdr (hons-assoc-equal k x)))
                  (integerp (cdr (hons-assoc-equal k x)))
                  (<= 0 (cdr (hons-assoc-equal k x))))))

  (defthm fg-memo-p-of-acons
    (equal (fg-memo-p (cons (cons k v) x))
           (and (fg-memo-p x)
                (or (eq v :back)
                    (eq v :loop)
                    (natp v))))))







(defconst *dag-measure-template*
  '(encapsulate
     nil
     (local (defthm fg-nonmember-successor-constraint
              (implies (not (member x __nodes__))
                       (not (consp __successors__)))
              :rule-classes nil))

     (local (defthm fg-node-guard-implies-node-list-guard-of-successors
              (implies (and __nodeguard__ __guard__)
                       (let ((x __successors__))
                         (declare (ignorable x))
                         (and __nodelistguard__ __guard__)))
              :rule-classes nil))

     (local (defthm fg-node-list-guard-implies-node-list-guard-of-cdr
              (implies (and __nodelistguard__ __guard__)
                       (let ((x (cdr x)))
                         (declare (ignorable x))
                         (and __nodelistguard__ __guard__)))
              :rule-classes nil))

     (local (defthm fg-node-list-guard-implies-node-guard-of-car
              (implies (and __nodelistguard__ __guard__)
                       (let ((x (car x)))
                         (declare (ignorable x))
                         (and __nodeguard__ __guard__)))
              :rule-classes nil))

     (local (include-book "centaur/misc/dag-measure-thms" :dir :system))
     (local (in-theory (enable alist-keys)))

     (local (defthm len-equal-0
              (equal (equal (len x) 0)
                     (not (consp x)))))

     ;; Self-memoized depth function
     (mutual-recursion
      (defun __name__-depth-memo (x memo __formals__)
        (declare (xargs :measure (nat-list-measure
                                  (list (len (set-difference-equal
                                              __nodes__
                                              (alist-keys memo)))
                                        0 1))
                        :verify-guards nil
                        :guard (and __guard__
                                    __nodeguard__
                                    (fg-memo-p memo))))
        (b* ((look (hons-get x memo))
             ((when look)
              (let ((val (cdr look)))
                (if (or (eq val :back)
                        (eq val :loop))
                    (mv :loop memo)
                  (mv (lnfix val) memo))))
             (memo (hons-acons x :back memo))
             ((mv max-depth memo)
              (__name__-depth-memo-list __successors__ memo __formals__))
             (res (if (eq max-depth :loop)
                      :loop
                    (+ 1 (lnfix max-depth)))))
          (mv res (hons-acons x res memo))))
      (defun __name__-depth-memo-list (x memo __formals__)
        (declare (xargs :measure (nat-list-measure
                                  (list (len (set-difference-equal
                                              __nodes__
                                              (alist-keys memo)))
                                        (len x) 0))
                        :guard (and __guard__
                                    __nodelistguard__
                                    (fg-memo-p memo))))
        (b* (((when (atom x)) (mv 0 memo))
             ((mv depth1 memo1) (__name__-depth-memo (car x) memo __formals__))
             ((unless (mbt (<= (len (set-difference-equal
                                     __nodes__
                                     (alist-keys memo1)))
                               (len (set-difference-equal
                                     __nodes__
                                     (alist-keys memo))))))
              (mv :loop memo1))
             ((mv depth2 memo) (__name__-depth-memo-list (cdr x) memo1 __formals__))
             ((when (or (eq depth1 :loop) (eq depth2 :loop)))
              (mv :loop memo)))
          (mv (max depth1 depth2) memo))))

     (flag::make-flag __name__-depth-flag __name__-depth-memo)

     ;; A couple of theorems required for guard verification.
     (defthm-__name__-depth-flag
       (defthm __name__-depth-memo-measure-decr
         (b* (((mv ?res memo1) (__name__-depth-memo x memo __formals__)))
           (<= (len (set-difference-equal
                     __nodes__
                     (alist-keys memo1)))
               (len (set-difference-equal
                     __nodes__
                     (alist-keys memo)))))
         :flag __name__-depth-memo)
       (defthm __name__-depth-memo-list-measure-decr
         (b* (((mv ?res memo1) (__name__-depth-memo-list x memo __formals__)))
           (<= (len (set-difference-equal
                     __nodes__
                     (alist-keys memo1)))
               (len (set-difference-equal
                     __nodes__
                     (alist-keys memo)))))
         :flag __name__-depth-memo-list))

     (defthm-__name__-depth-flag
       (defthm __name__-depth-memo-type
         (b* (((mv ?res memo1) (__name__-depth-memo x memo __formals__)))
           (implies (fg-memo-p memo)
                    (and (fg-memo-p memo1)
                         (implies (not (eq res :loop))
                                  (and (natp res)
                                       (integerp res)
                                       (<= 0 res))))))
         :flag __name__-depth-memo)
       (defthm __name__-depth-memo-list-type
         (b* (((mv ?res memo1) (__name__-depth-memo-list x memo __formals__)))
           (implies (fg-memo-p memo)
                    (and (fg-memo-p memo1)
                         (implies (not (eq res :loop))
                                  (and (natp res)
                                       (integerp res)
                                       (<= 0 res))))))
         :flag __name__-depth-memo-list))

     ;; Verify the guards
     (encapsulate nil
       (local (defthm fudges
                (implies (integerp x)
                         (and (acl2-numberp x)
                              (rationalp x)))))
       (verify-guards __name__-depth-memo
         :hints (("goal" :use (fg-node-guard-implies-node-list-guard-of-successors
                               fg-node-list-guard-implies-node-list-guard-of-cdr
                               fg-node-list-guard-implies-node-guard-of-car)))))


     ;; Functions derived from __name__-depth-memo: loopfree predicate, loopfreelist
     ;; predicate
     (define __name__-loopfree-p (x __formals__)
       :guard (and __guard__ __nodeguard__)
       (b* (((mv res memo) (__name__-depth-memo x nil __formals__)))
         (fast-alist-free memo)
         (not (eq res :loop))))

     (define __name__-loopfreelist-p (x __formals__)
       :guard (and __guard__ __nodelistguard__)
       (b* (((mv res memo) (__name__-depth-memo-list x nil __formals__)))
         (fast-alist-free memo)
         (not (eq res :loop))))


     ;; Measure/list measure functions
     (define __name__-measure (x __formals__)
       :verify-guards nil
       :returns (res o-p)
       (nat-list-measure
        (list (b* (((mv res memo) (__name__-depth-memo x nil __formals__)))
                (fast-alist-free memo)
                res)
              0
              0)))

     (define __name__-list-measure-aux (x memo __formals__)
       :verify-guards nil
       (if (atom x)
           (mv 0 memo)
         (b* (((mv res1 memo) (__name__-depth-memo (car x) memo __formals__))
              ((mv res2 memo) (__name__-list-measure-aux (cdr x) memo __formals__)))
           (mv (max (if (eq res1 :loop) 0 res1) res2)
               memo))))

     (define __name__-list-measure (x __formals__)
       :verify-guards nil
       :returns (res o-p)
       (nat-list-measure
        (list (b* (((mv res memo) (__name__-list-measure-aux x nil __formals__)))
                (fast-alist-free memo)
                res)
              1
              (len x))))


     (local
      (defun fg-functional-inst-hint (thmname)
        `(:computed-hint-replacement
          ((let ((lit (car (last clause))))
             (case-match lit
               (('equal fncall &)
                `(:expand (,fncall)))))
           (and stable-under-simplificationp
                '(:use fg-nonmember-successor-constraint)))
          :use
          ((:functional-instance
            ,thmname
            (fg-nodes (lambda () __nodes__))
            (fg-successors (lambda (x) __successors__))
            (fg-depth-memo (lambda (x memo) (__name__-depth-memo x memo __formals__)))
            (fg-depth-memo-list (lambda (x memo) (__name__-depth-memo-list x memo __formals__)))
            (fg-loopfree-p (lambda (x) (__name__-loopfree-p x __formals__)))
            (fg-loopfreelist-p (lambda (x) (__name__-loopfreelist-p x __formals__)))
            (fg-measure (lambda (x) (__name__-measure x __formals__)))
            (fg-list-measure-aux (lambda (x memo) (__name__-list-measure-aux x memo __formals__)))
            (fg-list-measure (lambda (x) (__name__-list-measure x __formals__)))))
          :do-not-induct t)))

     ;; Theorems you can now instantiate:

     (defthm __name__-loopfreelist-p-of-successors
       (implies (__name__-loopfree-p x __formals__)
                (__name__-loopfreelist-p __successors__ __formals__))
       :hints((fg-functional-inst-hint 'fg-loopfreelist-p-of-successors)))

     (defthm __name__-loopfreelist-p-of-cdr
       (implies (and (__name__-loopfreelist-p x __formals__)
                     (consp x))
                (__name__-loopfreelist-p (cdr x) __formals__))
       :hints((fg-functional-inst-hint 'fg-loopfreelist-p-of-cdr)))

     (defthm __name__-loopfree-p-of-car
       (implies (and (__name__-loopfreelist-p x __formals__)
                     (consp x))
                (__name__-loopfree-p (car x) __formals__))
       :hints((fg-functional-inst-hint 'fg-loopfree-p-of-car)))


     (defthm __name__-list-measure-of-cdr
       (implies (consp x)
                (o< (__name__-list-measure (cdr x) __formals__)
                    (__name__-list-measure x __formals__)))
       :hints((fg-functional-inst-hint 'fg-list-measure-of-cdr)))

     (defthm __name__-measure-of-car
       (implies (consp x)
                (o< (__name__-measure (car x) __formals__)
                    (__name__-list-measure x __formals__)))
       :hints((fg-functional-inst-hint 'fg-measure-of-car)))

     (defthm __name__-list-measure-of-successors
       (implies (__name__-loopfree-p x __formals__)
                (o< (__name__-list-measure __successors__ __formals__)
                    (__name__-measure x __formals__)))
       :hints ((fg-functional-inst-hint 'fg-list-measure-of-successors)))

     (mutual-recursion
      (defun __name__-count (x __formals__)
        (declare (xargs :measure (__name__-measure x __formals__)
                        :verify-guards nil
                        :guard (and __guard__ __nodeguard__
                                    (__name__-loopfree-p x __formals__))))
        (b* (((unless (mbt (__name__-loopfree-p x __formals__))) 0))
          (+ 1 (__name__-count-list __successors__ __formals__))))
      (defun __name__-count-list (x __formals__)
        (declare (xargs :measure (__name__-list-measure x __formals__)
                        :guard (and __guard__ __nodelistguard__
                                    (__name__-loopfreelist-p x __formals__))))
        (if (atom x)
            0
          (+ (__name__-count (car x) __formals__)
             (__name__-count-list (cdr x) __formals__)))))

     (verify-guards __name__-count
       :hints (("goal" :use (fg-node-guard-implies-node-list-guard-of-successors
                             fg-node-list-guard-implies-node-list-guard-of-cdr
                             fg-node-list-guard-implies-node-guard-of-car))))))


(deffunmac def-dag-measure (name &key
                                 graph-formals
                                 successors-expr
                                 nodes-expr
                                 (node-guard 't)
                                 (node-list-guard 't)
                                 (guard 't))
  (declare (xargs :mode :program))
  (template-subst *dag-measure-template*
                  :atom-alist `((__nodes__ . ,nodes-expr)
                                (__successors__ . ,successors-expr)
                                (__nodeguard__ . ,node-guard)
                                (__nodelistguard__ . ,node-list-guard)
                                (__guard__ . ,guard))
                  :splice-alist `((__formals__ . ,graph-formals))
                  :str-alist `(("__NAME__" . ,(symbol-name name)))
                  :pkg-sym name))

(local
 (progn

   ;; Examples

   (encapsulate nil
     (local (defthm member-alist-keys
              (iff (member x (alist-keys y))
                   (hons-assoc-equal x y))
              :hints(("Goal" :in-theory (enable alist-keys)))))

     (def-dag-measure falgraph
       :graph-formals (graph)
       :successors-expr (mbe :logic (cdr (hons-assoc-equal x graph))
                             :exec (cdr (hons-get x graph)))
       :nodes-expr (alist-keys graph)))

   (def-dag-measure algraph
     :graph-formals (graph)
     :successors-expr (cdr (assoc-eq x graph))
     :nodes-expr (strip-cars graph)
     :guard (and (alistp graph) (symbol-list-listp (strip-cdrs graph)))
     :node-guard (symbolp x)
     :node-list-guard (symbol-listp x))))




