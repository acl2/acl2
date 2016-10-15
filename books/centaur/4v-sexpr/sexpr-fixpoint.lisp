; S-Expressions for 4-Valued Logic
; Copyright (C) 2010-2012 Centaur Technology
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
;
; sexpr-fixpoint.lisp
;  - core fixpoint algorithm for monotonic, lattice-height-1 sexpr objects

(in-package "ACL2")
(include-book "nsexprs")
(include-book "sexpr-rewrites")
(include-book "centaur/misc/hons-extra" :dir :system)
(include-book "centaur/misc/sneaky-load" :dir :system)
(include-book "centaur/misc/nat-list-duplicates" :dir :system)
(include-book "centaur/misc/tuplep" :dir :system)
(include-book "centaur/misc/dfs-measure" :dir :system)
(include-book "std/basic/two-nats-measure" :dir :system)
(include-book "centaur/vl/util/cwtime" :dir :system)
(local (include-book "arithmetic/top-with-meta" :dir :system))

(local (in-theory (disable set::double-containment)))


;; BOZO library stuff -----------------------------------------------

(defun redundant-append (a b)
  ;; bozo name is weird -- maybe "smart-append" instead?
  ;; bozo actually also redundant with faig-least-fixpoint.lisp ... /smacks head
  (declare (xargs :guard (true-listp a)))
  (mbe :logic (append a b)
       :exec (if b
                 (append a b)
               a)))

(defun reverse-alist (x)
  (declare (xargs :guard t))
  (cond ((atom x)
         nil)
        ((atom (car x))
         (reverse-alist (cdr x)))
        (t
         (cons (cons (cdar x) (caar x))
               (reverse-alist (cdr x))))))

(defun collect-keys-with-value (x val)
  (declare (xargs :guard t))
  (cond ((atom x)
         nil)
        ((atom (car x))
         (collect-keys-with-value (cdr x) val))
        ((equal (cdar x) val)
         (cons (caar x)
               (collect-keys-with-value (cdr x) val)))
        (t
         (collect-keys-with-value (cdr x) val))))


; probably localize these theorems or integrate them into libraries

(defthm true-listp-hons-shrink-alist
  (iff (true-listp (hons-shrink-alist a b))
       (true-listp b)))

; ----------------- end library stuff ----------------------------


; Sneaky Loop Debugging
;
; SEXPR-FIXPOINTS can perform poorly when there are apparent combinational
; loops.  Unfortunately, it can be very difficult to figure out where the loops
; are being encountered.  To assist with debugging these loops, we now
; automatically detect and print information about the looping signals.
;
; To avoid complicating the logical story by passing around inv-varmap and the
; loops we've found, we use the sneaky-load stuff for this.  Our real debugging
; code abuses sneaky-mutate to use it to print our debugging info.  But we
; won't install our debugging by default, so that this file doesn't need to
; depend on elaborate VL stuff that we use to make the debugger better.  See
; sexpr-loop-debug.lisp for the real debugger.

(defstub sneaky-loop-debugger () t)
(defstub sneaky-loop-say-how-bad (sig-number ndeps) t)

(defun default-sneaky-loop-debugger ()
  (declare (xargs :guard t))
  nil)

(defun default-sneaky-loop-say-how-bad (sig-number ndeps)
  (declare (xargs :guard t)
           (ignorable sig-number ndeps))
  (progn$
   (cw "Note: signal ~x0 depends on ~x1 previous signals.~%" sig-number ndeps)
   (cw "Consider installnig the loop-debugger.~%")
   nil))

(defattach sneaky-loop-debugger default-sneaky-loop-debugger)
(defattach sneaky-loop-say-how-bad default-sneaky-loop-say-how-bad)




; The fixpoint algorithm is adapted from faig-least-fixpoint.lisp.  We leave
; the semantics uninterpreted for now.
;
; The top-level function is:
;
;    (SEXPR-FIXPOINT-WITH-VARMAP UPDATE-FNS VARMAP)
;
; Here,
;
;    UPDATE-FNS is an alist binding some signal names (atoms) to s-expressions
;    representing their update functions.
;
;    VARMAP is a 1-1 mapping from singal names to natural numbers.  It must
;    provide a binding for every key in the update-fns alist, and also for any
;    variables mentioned in any s-expression in the update-fns alist.
;
; We produce a new alist where every variable in UPDATE-FNS is bound to an
; S-Expression that represents its value after running all of the update
; functions until a fixed point is reached.
;
; The point of the VARMAP is to provide a translation from S-Expressions that
; involve arbitrary variables to S-Expressions that only involve natural-number
; variables.  We can compute the 4v-sexpr-vars of these "nat var sexprs" much more
; efficiently than for regular sexprs; see nat-var-sexprs.lisp for details.
;
; Indeed, our top-level function is nothing more than a wrapper which:
;
;    (1) rewrites the UPDATE-FNS using the VARMAP, producing some
;        NAT-UPDATE-FNS where all the signal names are natural numbers
;
;    (2) applies an auxilliary function to these NAT-UPDATE-FNS, which computes
;        all of the fixpoints in terms of these numbered variables.
;
;    (3) rewrites the resulting fixpoints using the inverse of VARMAP in order
;        to get fixpoint functions that are in terms of the original variables.
;
; Each rewriting pass is only O(n) in the size of the update-fns, and as such
; is relatively cheap.
;
;
; From now on, suppose we are working with natural variabled UPDATE-FNS.  The
; auxilliary function in step 2 can also be regarded as our top-level function
; for finding fixpoints of these kinds of update-fns, and is:
;
;    (SEXPR-FIXPOINTS UPDATE-FNS)
;
; It returns a new alist that binds the signal names to their final
; S-Expressions.  This function also operates in two phases:
;
;    (1) we try to topologically sort the update functions into a good order
;        that will minimize the number of backward-propagations needed in the
;        core algorithm, then
;
;    (2) we apply our core algorithm to the reordered update functions.
;
; The sorting phase is carried out by SEXPR-DFS, which (BOZO which presumably
; stands for "depth first search" or "depth first sort") and is not
; particularly tricky.
;
;
; The real core of the algorithm is:
;
;   (FIND-SEXPR-LEAST-FIXPOINT UPDATE-FNS)
;      --->
;   (MV FIXPOINTS NEED-FIXING DEPTABLE)


(defconst *sexpr-fixpoint-rewrite* t)

(defun sexpr-update-fixpoints (deps fixpoints new-fixpoint)
  (declare (xargs :guard t))
  (if (atom deps)
      fixpoints
    (let ((look (hons-get (car deps) fixpoints)))
      (if look
          (hons-acons (car deps)
                      (if *sexpr-fixpoint-rewrite*
                          (4v-sexpr-restrict-with-rw (cdr look) new-fixpoint)
                        (4v-sexpr-restrict (cdr look)
                                        new-fixpoint))
                      (sexpr-update-fixpoints (cdr deps) fixpoints
                                              new-fixpoint))
        (sexpr-update-fixpoints (cdr deps) fixpoints
                                new-fixpoint)))))


(defun update-deptable (vars deps deptable)
  ;; forall v in vars, deptable[v] := deps @ deptable[v]
  (declare (xargs :guard (true-listp deps)))
  (if (atom vars)
      deptable
    (hons-acons (car vars)
                (redundant-append deps (cdr (hons-get (car vars) deptable)))
                (update-deptable (cdr vars) deps deptable))))


(defun sexpr-fixpoint-forward-propagate (sexpr fixpoints)
;; Composes the previously-computed fixpoints into an update function
;; (sexpr).
  (declare (xargs :guard t))
  (if *sexpr-fixpoint-rewrite*
      (4v-sexpr-restrict-with-rw sexpr fixpoints)
    (4v-sexpr-restrict sexpr fixpoints)))



(encapsulate nil

  (defthm 4v-sexpr-restrict-with-rw-vars-subset
    (subsetp-equal (4v-sexpr-vars (4v-sexpr-restrict-with-rw x al))
                   (append (4v-sexpr-vars-list (alist-vals al))
                           (set-difference-equal (4v-sexpr-vars x)
                                                 (alist-keys al))))
    :hints ((witness)))

  (local (defthm nat-listp-append-iff
           (implies (true-listp a)
                    (iff (nat-listp (append a b))
                         (and (nat-listp a)
                              (nat-listp b))))
           :hints(("Goal" :in-theory (enable nat-listp)))))

  (defthm nat-listp-4v-sexpr-vars-list-alist-vals-when-4v-nsexpr-alist-p
    (implies (4v-nsexpr-alist-p al)
             (nat-listp (4v-sexpr-vars-list (alist-vals al))))
    :hints(("Goal" :in-theory (enable nat-listp alist-vals 4v-sexpr-vars-list))))

  (local (defthm nat-listp-set-differenc-equal
           (implies (nat-listp x)
                    (nat-listp (set-difference-equal x y)))
           :hints(("Goal" :in-theory (enable nat-listp set-difference-equal)))))

  ;; BOZO wtf where did nat-listp-subset go?
  (local (defthm natp-when-nat-listp-member
           (implies (and (member a x)
                         (nat-listp x))
                    (natp a))
           :hints(("Goal" :in-theory (enable nat-listp)))))

  (local (defthm nat-listp-when-subsetp
           (implies (and (subsetp-equal x y)
                         (nat-listp y))
                    (equal (nat-listp x)
                           (true-listp x)))
           :hints(("Goal" :induct (len x)
                   :in-theory (enable subsetp-equal nat-listp)))))

  (defthm 4v-nsexpr-p-sexpr-rewrite
    (implies (and (4v-nsexpr-p x)
                  (4v-nsexpr-alist-p al))
             (nat-listp (4v-sexpr-vars (4v-sexpr-restrict-with-rw x al))))
    :hints (("goal" :use ((:instance nat-listp-when-subsetp
                                     (x (4v-sexpr-vars (4v-sexpr-restrict-with-rw x al)))
                                     (y (append (4v-sexpr-vars-list (alist-vals al))
                                                (set-difference-equal (4v-sexpr-vars x)
                                                                      (alist-keys al))))))))))




(defun find-sexpr-least-fixpoint (update-fns)
  (declare (xargs :guard (4v-nsexpr-alist-p update-fns)
                  :verify-guards nil))

; The update-fns have already been ordered.
;
; Returns (mv fixpoints need-fixing deptable)
;
; fixpoints: alist mapping signal names to their SEXPR fixpoints.  each SEXPR
;            may contain varnames for signals that occur previously to it in
;            update-fns.
;
; need-fixing: list of signals that still need to be Xed out.
;
; deptable: table mapping signal names to lists of signal names.
;
; Invariant: If some signal S in the fixpoints depends on D, then
;               S \in deptable[D]

  (if (atom update-fns)
      (mv nil nil nil)
    (b* (((mv fixpoints need-fixing deptable)
          (find-sexpr-least-fixpoint (cdr update-fns)))

         ((when (not (mbt (consp (car update-fns)))))
          (mv fixpoints need-fixing deptable))

         (signame (caar update-fns))
         (sexpr   (cdar update-fns))

         ;; Composing the previously-computed fixpoints into the update
         ;; function.
         (fixpoint
          (sexpr-fixpoint-forward-propagate sexpr fixpoints))

         (-
          ;; BOZO is this a good idea?  Probably.
          (clear-memoize-table (if *sexpr-fixpoint-rewrite*
                                   '4v-sexpr-restrict-with-rw
                                 '4v-sexpr-restrict)))

         ;; Signals upon which signame depends.
         (compose-vars
          (4v-nsexpr-vars fixpoint))
         ;; (my-4v-sexpr-vars fixpoint)

         ;; If signame depends on itself (after composing in the previous
         ;; fixpoints), then it will need to be set to X throughout the
         ;; fixpoints, in a final pass later.  We track such signals in
         ;; needs-fixing.
         (needs-fixingp
          (mbe :logic (member-equal signame compose-vars)
               :exec (if (integerp signame)
                         (member signame compose-vars)
                       (member-equal signame compose-vars))))

         ;; Get from deptable the list of signals whose fixpoints we've already
         ;; computed that depend on our vars.

         (deps
          (hons-remove-duplicates (cdr (hons-get signame deptable))))

         (- (and deps
                 (sneaky-loop-say-how-bad signame (len deps))))

; BOZO we could skip this work when deps are empty, which most of the time
; they are.

         ;; Back propagation: For each such dependency, replace the on/off var
         ;; with its fixpoint formula.  Now, no fixpoint contains either of our
         ;; on/offset variables.
         (restr-al3 (make-fast-alist `((,signame . ,fixpoint))))
         (new-fixpoints (sexpr-update-fixpoints deps fixpoints restr-al3))
         (- (fast-alist-free restr-al3))

         (-
          ;; BOZO is this a good idea?
          (clear-memoize-table (if *sexpr-fixpoint-rewrite*
                                   '4v-sexpr-restrict-with-rw
                                 '4v-sexpr-restrict)))



         ;; Update the dependency table: Each variable in this signal's
         ;; fixpoint needs its dependencies updated to include this signal and
         ;; all previous fixpoints that depend on it, since back-propagation
         ;; likely added all this signal's variables to those fixpoints.
         (deptable (update-deptable compose-vars (cons signame deps) deptable)))
      (mv (hons-acons signame fixpoint new-fixpoints)
          (if needs-fixingp
              (cons signame need-fixing)
            need-fixing)
          deptable))))

(defthm 4v-nsexpr-alist-p-sexpr-update-fixpoints
  (implies (and (4v-nsexpr-alist-p fixpoints)
                (4v-nsexpr-alist-p new-fixpoint))
           (4v-nsexpr-alist-p (sexpr-update-fixpoints deps fixpoints new-fixpoint))))

(defthm 4v-nsexpr-alist-p-find-sexpr-least-fixpoint
  (implies (4v-nsexpr-alist-p update-fns)
           (4v-nsexpr-alist-p (mv-nth 0 (find-sexpr-least-fixpoint
                                            update-fns))))
  :hints(("Goal" :in-theory (disable hons-assoc-equal
                                     sexpr-rewrite))))

(verify-guards find-sexpr-least-fixpoint)




;; To find the series of signals in a loop, run back through the seen alist
;; collecting signals that are recorded as started but not finished until we
;; reach the starting point of the signal in question.
(defun trace-loop (signal seen-al whole-seen-al acc)
  (declare (xargs :guard t))
  (b* (((when (atom seen-al))
        (er hard? 'trace-loop "Didn't find signal in seen-al.~%"))
       ((when (or (atom (car seen-al))
                  (not (eq (cdar seen-al) 'started))
                  (eq (cdr (hons-get (caar seen-al) whole-seen-al))
                      'finished)))
        (trace-loop signal (cdr seen-al) whole-seen-al acc))
       (acc (cons (caar seen-al) acc))
       ((when (equal (caar seen-al) signal)) acc))
    (trace-loop signal (cdr seen-al) whole-seen-al acc)))


(defun sexpr-dfs (queue deps seen-al parent back-edges)

; Returns the final (MV SEEN-AL BACK-EDGES)

; QUEUE is the nodes we have left to explore; initially the names of all
; update-fns.
;
; DEPS is the alist mapping wires to the variables of their update functions.
;
; SEEN-AL is an fast alist:
;  - unvisited nodes are not bound yet
;  - nodes are bound to 'started as we begin exploring their dependencies
;  - nodes are bound to 'finished after we're done exploring their dependencies
;
; PARENT is (LIST NODE) if we are currently looking at some node's dependents,
; or is NIL otherwise.
;
; BACK-EDGES is an ordinary alist that will record all loops we encounter.
; That is, if we wind up trying to explore a node that has already been
; 'started but not 'finished, then we record (parent-node . this-node) in the
; back-edges alist.
;
; BOZO back-edges is not actually used for anything, maybe we shouldn't bother
; to construct it.

  (declare (xargs :well-founded-relation nat-list-<
                  :measure (dfs-measure queue deps seen-al)
                  :hints (("goal" :do-not-induct t))
                  :guard t
                  :verify-guards nil))
  (b* (((when (atom queue)) (mv seen-al back-edges))

       (node (car queue))
       ((when (hons-get node seen-al))
        ;; Already saw the node.  Don't add anything to the seen-al.  If the
        ;; node has already been 'finished, we can just skip it.  If it's only
        ;; been 'started, we're in a loop, so record the back edge.
        (b* ((back-edges
              (if (and (consp parent)
                       (eq (cdr (hons-get node seen-al)) 'started))
                  (prog2$ (sneaky-push :sexpr-loop-debug-loops
                                       (trace-loop node seen-al seen-al nil))
                          (cons (cons (car parent) node) back-edges))

                back-edges)))
          (sexpr-dfs (cdr queue) deps seen-al parent back-edges)))

       ;; First time we've seen this node.  Compute its dependents.
       (look (hons-get node deps))
       ((when (not look))
        ;; Basically a degenerate case -- should never occur unless we're
        ;; missing a binding for some signal that occurs as the rhs of some
        ;; update-fn.
        (sexpr-dfs (cdr queue) deps seen-al parent back-edges))

       (node-deps    (cdr look))

       ;; Mark the node as started and go explore its dependents.
       (seen-al1 (hons-acons node 'started seen-al))
       ((mv seen-al1 back-edges)
        (sexpr-dfs node-deps deps seen-al1 (list node) back-edges))

       ;; Done exploring dependents, so mark the node as finished.
       (seen-al2 (hons-acons node 'finished seen-al1))

       ((when (not (mbt (suffixp seen-al seen-al2))))
        (mv seen-al1 back-edges)))

    (sexpr-dfs (cdr queue) deps seen-al2 parent back-edges)))

(defthm suffixp-sexpr-dfs
  (suffixp seen-al (mv-nth 0 (sexpr-dfs queue deptable seen-al parent
                                        back-edges)))
  :hints (("goal" :induct (sexpr-dfs queue deptable seen-al parent
                                        back-edges))))

(defthm suffixp-sexpr-dfs-cons
  (suffixp seen-al (mv-nth 0 (sexpr-dfs queue deptable (cons x seen-al) parent
                                        back-edges)))
  :hints(("Goal" :use (:instance suffixp-transitive
                       (a seen-al)
                       (b (cons x seen-al))
                       (c (mv-nth 0 (sexpr-dfs queue deptable (cons x seen-al) parent
                                               back-edges))))
          :in-theory (disable suffixp-transitive))))

(verify-guards sexpr-dfs)

(defthm sexpr-hons-assoc-equal-in-seen-al
  (implies (hons-assoc-equal k seen-al)
           (hons-assoc-equal k (mv-nth 0 (sexpr-dfs queue deptable
                                                   seen-al parent
                                                   back-edges))))
  :hints (("goal" :induct (sexpr-dfs queue deptable
                                     seen-al parent
                                     back-edges)
           :in-theory (disable (:definition sexpr-dfs))
           :expand ((sexpr-dfs queue deptable
                                     seen-al parent
                                     back-edges)))))

(defthm sexpr-subsetp-equal-alist-keys-seen-al
  (subsetp-equal (alist-keys seen-al)
                 (alist-keys (mv-nth 0 (sexpr-dfs queue
                                                 deptable
                                                 (cons (cons key 'started)
                                                       seen-al)
                                                 parent
                                                 back-edges))))
  :hints (("goal" :do-not-induct t
           :in-theory (enable subsetp-witness-rw))))






(defun sexpr-x-out-fixpoint-sigs (need-fixing fixpoints)
  (declare (xargs :guard t))
  (if need-fixing
      (b* ((x-alist (hons-acons-each need-fixing *4vx-sexpr* nil))
           (fixpoints (if *sexpr-fixpoint-rewrite*
                          (4v-sexpr-restrict-with-rw-alist fixpoints x-alist)
                        (4v-sexpr-restrict-alist fixpoints x-alist))))
        (clear-memoize-table (if *sexpr-fixpoint-rewrite*
                                 '4v-sexpr-restrict-with-rw
                               '4v-sexpr-restrict))
        (fast-alist-free x-alist)
        fixpoints)
    fixpoints))




(defun find-sexpr-least-fixpoint-top (ordered-updates)
  (declare (xargs :guard (4v-nsexpr-alist-p ordered-updates)))
  (b* (((mv fixpoint needs-fixing deptable)
        (find-sexpr-least-fixpoint ordered-updates))
       (fixpoint1 (hons-shrink-alist fixpoint nil))
       (- (fast-alist-free fixpoint)
          (fast-alist-free fixpoint1)
          (fast-alist-free deptable))
       (fixpoint (sexpr-x-out-fixpoint-sigs
                  needs-fixing fixpoint1)))
    fixpoint))

(defun sexpr-update-fns-to-deps (x)
  (declare (Xargs :guard (4v-nsexpr-alist-p x)))
  (if (atom x)
      nil
    (if (atom (car x))
        (sexpr-update-fns-to-deps (cdr x))
      (cons (cons (caar x) (4v-nsexpr-vars (cdar x)))
            (sexpr-update-fns-to-deps (cdr x))))))


(defun sexpr-fixpoints (update-fns)
  (declare (xargs :guard (4v-nsexpr-alist-p update-fns)))
  (b* ((deptable (sexpr-update-fns-to-deps update-fns))
       ((with-fast deptable update-fns))

       ;; Clear out the sexpr-dfs-loops accumulator so that we are not saving
       ;; any previous loops.
       (- (sneaky-save :sexpr-dfs-loops nil))
       ;; Depth-first search to try to put the update-fns into a good order
       ;; that will minimize back-propagation.
       ((mv dfs ?back-edges)
        (cwtime (sexpr-dfs (alist-keys update-fns)
                           deptable nil nil nil)
                :mintime 1))
       (- (sneaky-loop-debugger))

       (order (collect-keys-with-value dfs 'finished))
       (ordered-updates (fal-extract order update-fns))
       (- (fast-alist-free dfs))
       ;; Run the real fixpoint algorithm on the reordered update-fns.
       (fixpoint
        (find-sexpr-least-fixpoint-top ordered-updates)))
    (clear-memoize-table 'sexpr-rewrite)
    (clear-memoize-table '4v-nsexpr-vars-sparse)
    (clear-memoize-table '4v-nsexpr-vars-nonsparse)
    fixpoint))










(defun nat-val-alistp (x)
  ;; Alist whose every value is a natp.
  (declare (xargs :guard t))
  (if (atom x)
      t
    (and (consp (car x))
         (natp (cdar x))
         (nat-val-alistp (cdr x)))))

(defun translate-domain (al map)
  ;; Replace the keys of AL with their bindings in MAP.  We're just rewriting
  ;; the keys of the UPDATE-FNS alist with the VARMAP, here.
  (declare (xargs :guard t))
  (b* (((when (atom al)) nil)
       ((when (atom (car al)))
        (translate-domain (cdr al) map))
       (look (hons-get (caar al) map))
       ((when (not look))
        (translate-domain (cdr al) map)))
    (cons (cons (cdr look) (cdar al))
          (translate-domain (cdr al) map))))

(defthm 4v-nsexpr-alist-p-translate-domain
  (implies (4v-nsexpr-alist-p x)
           (4v-nsexpr-alist-p (translate-domain x al))))


(defun unique-mapping (x)
  (declare (xargs :guard t))
  (and (no-duplicatesp-equal (alist-keys x))
       (no-duplicatesp-equal (alist-vals x))))

(defun sexpr-var-key-alistp (x)
  ;; Alist whose every key is an non-nil atom
  (declare (xargs :guard t))
  (if (atom x)
      t
    (and (consp (car x))
         (atom (caar x))
         (caar x)
         (sexpr-var-key-alistp (cdr x)))))

(defun sexpr-var-val-alistp (x)
  ;; Alist whose every value is an non-nil atom
  (Declare (xargs :guard t))
  (if (atom x)
      t
    (and (consp (car x))
         (atom (cdar x))
         (cdar x)
         (sexpr-var-val-alistp (cdr x)))))

(defun good-sexpr-varmap (map ups)
  (declare (xargs :guard t))
  (and (sexpr-var-key-alistp map)
       (sexpr-var-val-alistp map)
       (unique-mapping map)
       (subsetp-equal (alist-keys ups) (alist-keys map))
       (subsetp-equal (4v-sexpr-vars-list (alist-vals ups))
                      (alist-keys map))))




(defun sexpr-fixpoint-with-varmap (update-fns varmap)
  (declare (xargs :guard (and (4v-nsexpr-alist-p varmap)
                              (good-sexpr-varmap varmap update-fns))))
  (if (mbt (good-sexpr-varmap varmap update-fns))
      (b* ((varmap (make-fast-alist varmap))
           (nat-update-fns (translate-domain
                            ;; We don't bother rewriting here because
                            ;; the alist simply maps vars to vars.
                            (4v-sexpr-compose-alist
                             update-fns varmap) varmap))
           (- (clear-memoize-table '4v-sexpr-compose))
           (inv-varmap (make-fast-alist (reverse-alist varmap)))
           ;; Clear out any previously saved loops.  Install the new inv-varmap
           ;; so that we can translate loops we find.
           (- (sneaky-save :sexpr-loop-debug-loops nil))
           (- (sneaky-save :sexpr-loop-debug-inv-varmap inv-varmap))
           (nat-fixpoint (sexpr-fixpoints nat-update-fns))
           (fixpoint (translate-domain
                      (4v-sexpr-compose-alist
                       nat-fixpoint inv-varmap) inv-varmap)))
        (clear-memoize-table '4v-sexpr-compose)
        (fast-alist-free varmap)
        (fast-alist-free inv-varmap)
        fixpoint)
    (sexpr-fixpoints update-fns)))

(memoize 'sexpr-fixpoint-with-varmap :condition nil)
(memoize 'sexpr-fixpoints :condition nil)

(defthm true-listp-sexpr-fixpoints
  ;; bozo really want rewrite??
  (true-listp (sexpr-fixpoints ups))
  :hints(("Goal" :in-theory (enable sexpr-fixpoints)))
  :rule-classes (:rewrite :type-prescription))

(defthm true-listp-sexpr-fixpoint-with-varmap
  (true-listp (sexpr-fixpoint-with-varmap ups map))
  :hints(("Goal" :in-theory (e/d (sexpr-fixpoint-with-varmap)
                                 (hons-assoc-equal))))
  :rule-classes :type-prescription)






;; Jared: this doesn't seem to be used now.

;; (defun sexpr-single-fixpoint (name sexpr vars)
;;   (if (member-equal name vars)
;;       (b* ((restr-al2 (make-fast-alist `((,name ,*4vx-sexpr*))))
;;            (fixpoint (4v-sexpr-restrict sexpr restr-al2))
;;            (- (fast-alist-free restr-al2)))
;;         fixpoint)
;;     sexpr))
