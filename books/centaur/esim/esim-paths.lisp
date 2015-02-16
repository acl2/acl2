; ESIM Symbolic Hardware Simulator
; Copyright (C) 2008-2015 Centaur Technology
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


; esim-paths.lisp -- path and well-formedness definitions for esim-new-probe
;
; Original authors: Jared Davis <jared@centtech.com>
;                   Sol Swords <sswords@centtech.com>

(in-package "ACL2")
(include-book "esim-sexpr-support")
(include-book "std/util/deflist" :dir :system)
(include-book "std/util/defmvtypes" :dir :system)
(include-book "std/typed-lists/cons-listp" :dir :system)
(local (include-book "esim-sexpr-support-thms"))


(defsection extend-internal-paths
  :parents (mod-internal-paths)
  :short "@(call extend-internal-paths) constructs a new list where @('a') has
been consed onto each element of @('x')."

  :long "<p>This is used to extend a list of paths with a new level of the
module hierarchy.  That is, suppose @('a') is the name of a submodule
occurrence, and that @('x = (x1 x2 ... xn)') is the list of paths for all
internal wires of that submodule.  Then we generate the list:</p>

@({
 (list (hons a x1)
       (hons a x2)
       ...
       (hons a xn))
})

<p>which can loosely be thought of as, @('a.x1'), @('a.x2'), etc.</p>"

  (defund extend-internal-paths-exec (a x acc)
    (declare (xargs :guard t))
    (if (atom x)
        acc
      (let ((acc (cons (hons a (car x)) acc)))
        (extend-internal-paths-exec a (cdr x) acc))))

  (local (in-theory (enable extend-internal-paths-exec)))

  (defun extend-internal-paths-exec-cons (a x acc)
    (declare (xargs :guard t))
    (mbe :logic (extend-internal-paths-exec a x acc)
         :exec
         (if (atom x)
             acc
           (let ((acc (cons (cons a (car x)) acc)))
             (extend-internal-paths-exec-cons a (cdr x) acc)))))

;; BOZO this might be faster as a defprojection for nreverse optimization

  (defund extend-internal-paths (a x)
    (declare (xargs :guard t :verify-guards nil))
    (mbe :logic (if (atom x)
                    nil
                  (cons (hons a (car x))
                        (extend-internal-paths a (cdr x))))
         :exec (reverse (extend-internal-paths-exec a x nil))))

  (local (in-theory (enable extend-internal-paths)))

  (defthm extend-internal-paths-exec-removal
    (equal (extend-internal-paths-exec a x acc)
           (revappend (extend-internal-paths a x) acc)))

  (verify-guards extend-internal-paths)

  (defun extend-internal-paths-cons (a x)
    (declare (xargs :guard t))
    (mbe :logic (extend-internal-paths a x)
         :exec (reverse (extend-internal-paths-exec-cons a x nil))))

  (defthm cons-listp-of-extend-internal-paths
    (cons-listp (extend-internal-paths a x)))

  (defthm len-extend-internal-paths
    (equal (len (extend-internal-paths u lst))
           (len lst))
    :hints(("Goal" :in-theory (enable extend-internal-paths)))))


(defsection mod-internal-paths
  :parents (esim)
  :short "@(call mod-internal-paths) produces a list of paths that describe the
canonical internal wires in a module."

  :long "<p>An example of a \"path\" is:</p>

@({
 (|core0| |rf_instd| |vl_mux_168| . |sbar_b[54]|)
})

<p>In this example, @('|core0|'), @('|rf_instd|'), and @('|vl_mux_168|') are
instance names, whereas @('|sbar_b[54]|') is a wire name.  The Verilog syntax
for referring to such a wire would be:</p>

@({
  core0.rf_instd.vl_mux_168.sbar_b[54]
})

<p>We memoize both @('mod-internal-paths') and @('occ-internal-paths') since
they both involve a good deal of consing.  Our original version of this
function created symbols like @('|core0/rf_instd/vl_mux_168/sbar_b[54]|')
instead of paths (lists of symbols), but that approach had poor performance due
to the amounts of string manipulation and interning required.  We now just cons
together instance and wire names to create paths, which is much faster.</p>

<p>We say that a path is <b>canonical</b> when it does not lead to an input or
output of the target module.  That is, the above path is canonical exactly if
@('|sbar_b[54]|') is an internal wire (not an input or output) of the module in
which it resides.</p>

<p>We produce only canonical paths, because it greatly reduces the number of
paths we need to construct.  Given some non-canonical path, it is possible to
canonicalize it discover its canonical version, see for instance @(see
fast-canonicalize-path).</p>"

  (mutual-recursion

   (defun mod-internal-paths (mod)
     (declare (xargs :guard t
                     :well-founded-relation nat-list-<
                     :measure (list (acl2-count mod) 1)))

; I now completely ignore the :X field!  The idea is if we are overriding a
; module, its :x field should include a :int alist that contains bindings for
; all of its mod-internal-paths, based on its occs.

     (let ((local-wires (hons-set-diff (driven-signals mod)
                                       (pat-flatten1 (gpl :o mod)))))
       (append local-wires
               (occs-internal-paths (gpl :occs mod)))))

   (defun occ-internal-paths (occ)
     (declare (xargs :guard t
                     :measure (list (acl2-count occ) 2)))
     (extend-internal-paths (gpl :u occ)
                            (mod-internal-paths (gpl :op occ))))

   (defun occs-internal-paths (occs)
     (declare (Xargs :guard t
                     :measure (list (acl2-count occs) 0)))
     (if (atom occs)
         nil
       (append (occ-internal-paths (car occs))
               (occs-internal-paths (cdr occs))))))

  (memoize 'mod-internal-paths :memo-table-init-size 10000)
  (memoize 'occ-internal-paths :memo-table-init-size 1500000)

  (unmemoize 'collect-signal-list))


(mutual-recursion
 (defun new-good-esim-probe-modulep (x)
   (declare (xargs :guard t
                   :well-founded-relation nat-list-<
                   :measure (list (acl2-count x) 3)
                   :hints (("goal" :in-theory
                            (disable mod-internals occ-internals
                                     good-esim-modulep
                                     hons-dups-p)))))
   (and (if (gpl :x x)
            ;; BOZO weaken this to set equivalence?
            ;; BOZO take advantage of the fact that the paths are honsed?
            ;; BOZO maybe hons-copy the alist keys here.
            (mbe :logic
                 (equal (alist-keys (gpl :int (gpl :x x)))
                        (mod-internal-paths x))
                 :exec
                 (alist-keys-are-p (gpl :int (gpl :x x))
                                   (mod-internal-paths x)))
          t)
        (new-good-esim-probe-occsp (gpl :occs x))))

 (defun new-good-esim-probe-occp (x)
   (declare (xargs :guard t
                   :measure (list (acl2-count x) 4)))
   (new-good-esim-probe-modulep (gpl :op x)))

 (defun new-good-esim-probe-occsp (x)
   (declare (xargs :guard t
                   :measure (list (acl2-count x) 2)))
   (or (atom x)
       (and (new-good-esim-probe-occp (car x))
            (new-good-esim-probe-occsp (cdr x))))))

(memoize 'new-good-esim-probe-modulep :condition '(gpl :occs x))




(defthm new-good-esim-probe-occsp-good-occp-lookup-in-occmap1
  (implies (and (new-good-esim-probe-occsp occs)
                (hons-assoc-equal u (occmap1 occs)))
           (new-good-esim-probe-occp (cdr (hons-assoc-equal u (occmap1 occs))))))

(defthm new-good-esim-probe-modulep-good-occp-lookup-in-occmap
  (implies (and (new-good-esim-probe-modulep mod)
                (hons-assoc-equal u (occmap mod)))
           (new-good-esim-probe-occp (cdr (hons-assoc-equal u (occmap mod))))))

(defthm new-good-esim-probe-modulep-op
  (implies (new-good-esim-probe-occp occ)
           (new-good-esim-probe-modulep (gpl :op occ))))

(defthm good-esim-occp-when-member-of-good-occsp
  (implies (and (good-esim-occsp occs)
                (member-equal occ occs))
           (good-esim-occp occ))
  :rule-classes ((:rewrite)
                 (:rewrite :corollary
                           (implies (and (member-equal occ occs)
                                         (good-esim-occsp occs))
                                    (good-esim-occp occ))))
  :hints(("Goal" :induct (len occs))))

(defthm data-for-patternp-of-inputs-when-good-esim-occp
  (implies (good-esim-occp occ)
           (data-for-patternp (gpl :i (gpl :op occ))
                              (gpl :i occ))))

(defthm data-for-patternp-of-outputs-when-good-esim-occp
  (implies (good-esim-occp occ)
           (data-for-patternp (gpl :o (gpl :op occ))
                              (gpl :o occ))))

(defthm member-of-occs-when-found-in-occmap1
  (implies (cdr (hons-assoc-equal name (occmap1 occs)))
           (member-equal (cdr (hons-assoc-equal name (occmap1 occs))) occs))
  :hints(("Goal" :in-theory (enable occmap1))))

(defthm member-of-occs-when-found-in-occmap
  (implies (cdr (hons-assoc-equal name (occmap mod)))
           (member-equal (cdr (hons-assoc-equal name (occmap mod)))
                         (gpl :occs mod))))

(defthm good-esim-occs-of-occs-when-good-esim-modulep
  (implies (good-esim-modulep mod)
           (good-esim-occsp (gpl :occs mod)))
  :hints(("Goal" :in-theory (enable good-esim-modulep))))

(defthm good-esim-modulep-of-op-when-good-esim-occ
  (implies (good-esim-occp occ)
           (good-esim-modulep (gpl :op occ))))

(defthm good-esim-modulep-of-op-when-good-module-and-among-occs
  (implies (and (good-esim-modulep mod)
                (cdr (hons-assoc-equal name (occmap mod))))
           (good-esim-modulep (gpl :op (cdr (hons-assoc-equal name (occmap mod))))))
  :hints(("Goal"
          :in-theory (disable good-esim-occp-when-member-of-good-occsp
                              good-esim-modulep
                              good-esim-occp
                              good-esim-occsp)
          :use ((:instance good-esim-occp-when-member-of-good-occsp
                           (occs (gpl :occs mod))
                           (occ  (cdr (hons-assoc-equal name (occmap mod)))))))))



(defsection fast-canonicalize-path
  :parents (mod-internal-paths)
  :short "@(call fast-canonicalize-path) produces the canonical version of a
path to an internal wire in a module."

  :long "<p><b>Signature:</b> @(call fast-canonicalize-path) returns @('(mv
successp new-path)').  On success, @('new-path') is a member of one of the
following:</p>

<ul>

<li>@('(mod-internal-paths mod)')</li>

<li>@('(gpl :i mod)'), or </li>

<li>@('(gpl :o mod)').</li>

</ul>

<p>To understand this function, note that the set of @(see mod-internal-paths)
does not include any non-canonical paths (inputs or outputs of the target
module).  For instance, if we have in Verilog something like:</p>

@({
  my_mux2 result_mux (.o(main_result), ...)
})

<p>Then a path such as:</p>

@({
  (|foo| |bar| |baz| |result_mux| . |o|)
})

<p>is not regarded as canonical and will not be included among the internal
signals alist produced esim's new-probe mode.  However, if we assume that
@('main_result') is not one of the inputs or outputs of @('foo.bar.baz'), then
the following path <i>is</i> canonical and it is equivalent in that it
describes the same wire:</p>

@({
  (|foo| |bar| |baz| . |main_result|)
})

<p>@('Fast-canonicalize-path') should be given a valid path in the sense of
@('mod-all-paths'), and tries to return the canonical equivalent.  Failure
indicates that the given path is invalid, but we do only minimal error
checking.  In other words, you should not rely on this function to see whether
a path is valid.</p>"

; Adapted from Sol's FADD proofs.  This is like CANONICALIZE-PATH from
; cnq-clocks, but with less (expensive) error checking.

; Jared: As an efficiency tweak, we now do a hons-get into the occmap instead
; of doing an assoc-occs.  This might lead us to build occmaps unnecessarily,
; but it should improve performance by a lot if we're doing tons of lookups,
; which for instance we do when dumping VCD files.

  (defund fast-canonicalize-path (path mod)
    "Returns (MV SUCCESSP NEW-PATH)"

    ;; If PATH is invalid, we return (MV NIL NIL).
    ;;
    ;; Otherwise, if PATH is valid, then SUCCESSP is T and the NEW-PATH we
    ;; return is the canonical version of PATH, and is a member of:
    ;;
    ;;  1. (mod-internal-paths mod),
    ;;  2. (gpl :i mod), or
    ;;  3. (gpl :o mod).
    ;;
    ;; This function completely ignore :X fields.  Which is fine, assuming
    ;; good-esim-probe-modulep.

    (declare (xargs :guard (good-esim-modulep mod)))
    (b* (((when (atom path))

          ;; This error checking was removed for performance.
          ;; The path leads to something in this module.  It's valid if
          ;; it's a member of :i or :o, or if it's a driven signal.
          ;; (if (or (member-of-pat-flatten path (gpl :i mod))
          ;;         (member-of-pat-flatten path (gpl :o mod))
          ;;         (member-equal path (driven-signals mod)))
          ;;     (mv t path)
          ;;   (mv nil nil))
          (mv t path))

         ;; Else, the path leads to something in a submodule.  For it to
         ;; be valid, its head must name some occurrence of this module.
         (head (car path))
         (occ  (cdr (hons-get head (make-fast-alist (occmap mod)))))
         ((unless occ)
          (mv nil nil))

         (op   (gpl :op occ))
         ((mv tail-successp new-tail) (fast-canonicalize-path (cdr path) op))
         ((unless tail-successp)
          ;; Can't even canonicalize the tail, this is an invalid path.
          (mv nil nil))

         ;; If the canonicalized tail is an input/output of the submodule, then
         ;; we need to fix it up.  We considered trying to avoid the
         ;; member-of-pat-flatten checks by returning the type of the new-path,
         ;; but it seems to be somewhat complicated.
         (tail-inputp (and (atom new-tail)
                           (member-of-pat-flatten new-tail (gpl :i op))))
         (tail-outputp (and (atom new-tail)
                            (not tail-inputp)
                            (member-of-pat-flatten new-tail (gpl :o op))))

         ((when tail-inputp)
          (mv t (cdr (assoc-pat->al new-tail (gpl :i op) (gpl :i occ)))))

         ((when tail-outputp)
          (mv t (cdr (assoc-pat->al new-tail (gpl :o op) (gpl :o occ))))))

      ;; Else, not an input/output of the submodule, so it's already a valid
      ;; internal path into the submodule.  Just tack on the head.
      (mv t (hons head new-tail)))))

(defmvtypes fast-canonicalize-path
  (booleanp nil))


(defund fast-canonicalize-paths (paths mod)
  "Returns (MV ALL-SUCCESSP NEW-PATHS)"
  (declare (xargs :guard (good-esim-modulep mod)))
  (b* (((when (atom paths))
        (mv t nil))
       ((mv okp1 new-path1)  (fast-canonicalize-path (car paths) mod))
       ((mv okp2 new-paths2) (fast-canonicalize-paths (cdr paths) mod)))
    (mv (and okp1 okp2)
        (cons new-path1 new-paths2))))

(defmvtypes fast-canonicalize-paths
  (booleanp true-listp))



(defsection follow-esim-path
  :parents (mod-internal-paths)
  :short "Walk down a list of instance names (or a path) and retrieve the ESIM
module it points to."

  :long "<p>@(call follow-esim-path) returns an ESIM module on success, or
@('nil') for failure.</p>

<p>We are given @('instnames'), which should be a list of instance names, and
@('mod'), which should be a good @(see esim) module.  We try to follow these
names down through the occurrences of @('mod') and return the submodule they
point to.</p>

<p>Note that @('instnames') need not be a true-listp, so you can use this
function to look up the module associated with an ESIM path without needing to
list-fix the path or similar.</p>"

  (defund follow-esim-path (instnames mod)
    "Returns SUBMOD or NIL."
    (declare (xargs :guard t))
    (b* (((when (atom instnames))
          mod)
         (name1  (car instnames))
         (occ    (cdr (hons-get name1 (make-fast-alist (occmap mod))))))
      (and occ
           (follow-esim-path (cdr instnames) (gpl :op occ)))))

  (local (in-theory (enable follow-esim-path)))

  (defthm good-esim-modulep-of-follow-esim-path
    (implies (good-esim-modulep mod)
             (good-esim-modulep (follow-esim-path instnames mod)))
    :hints(("Goal"
            :induct (follow-esim-path instnames mod)
            :in-theory (disable good-esim-modulep)))))




