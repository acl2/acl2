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


; esim-cut.lisp -- transform to cut wires in E modules
;
; Original authors: Jared Davis <jared@centtech.com>
;                   Sol Swords <sswords@centtech.com>

(in-package "ACL2")
(include-book "esim-primitives")
(include-book "esim-paths")
(include-book "vltoe/emodwire")
(include-book "std/util/define" :dir :system)
(include-book "std/util/defaggregate" :dir :system)
(include-book "std/util/defprojection" :dir :system)
(include-book "std/util/defalist" :dir :system)
(include-book "std/util/defmapappend" :dir :system)
(local (include-book "esim-sexpr-support-thms"))

#||
(include-book
 "tools/defconsts" :dir :system)
(defconsts (*esims* state)
  (serialize-read "/n/fv2/translations/nightly/cnr/esims.sao"
                  :verbosep t))
||#


; We always cut only internal or output wires (it's an error to try to cut
; an input wire.)
;
; Say we are cutting the wire W.
; We need to:
;
;  - Change whatever occ is driving W, and make it drive W<original_value> instead
;
;  - Insert two clockless flip-flops:
;
;    The input here isn't really very important, but it gives us an easy
;    way to pull out the original value if we want it.  The output is only
;    relevant if we're going to override the wire, and in that case, it
;    contains the value we're overriding it with.
;
;       fsm_reg W<override_value_reg> (.in(W<original_value>),
;                                      .out(W<override_value>))
;
;    This one just controls whether we're overriding W at all.
;
;       fsm_reg W<override_decision_reg> (.in(0), .out(W<override_decision>))
;
;  - Insert a ZIF mux: If we're overriding, it chooses the override value we
;    want to use (a), otherwise it chooses the original value (b).
;
;       zif_mux W<override_mux> (.sel(W<override_decision>),
;                                .a(W<override_value>),
;                                .b(W<original_value>),
;                                .o(W))
;
;  - Done.  Check for name conflicts?


; Our core transform will do this for a list of paths into some module.  At any
; point, some of these paths may be terminal.

(std::defaggregate ecutnames
  ((original      symbolp :rule-classes :type-prescription)
   (value         symbolp :rule-classes :type-prescription)
   (value-reg     symbolp :rule-classes :type-prescription)
   (decision-wire symbolp :rule-classes :type-prescription)
   (decision-reg  symbolp :rule-classes :type-prescription)
   (mux           symbolp :rule-classes :type-prescription)
   ))

(std::deflist ecutname-list-p (x)
  (ecutnames-p x)
  :guard t)

(define ecutnames->flat-names ((x ecutnames-p))
  (b* (((ecutnames x) x))
    (list x.original
          x.value
          x.value-reg
          x.decision-wire
          x.decision-reg
          x.mux)))

(std::defmapappend ecutname-list->flat-names (x)
  (ecutnames->flat-names x)
  :guard (ecutname-list-p x))

(define ecut-make-sym ((x symbolp)
                       (suffix stringp))
  :returns (name symbolp)
  ;; We originally tried not to bother to use any emodwire stuff here.  That
  ;; worked fine for most stuff (stv definition, running, etc.)  But the VCD
  ;; generation stuff relies on emodwires (for good reason, e.g., to bundle
  ;; together wires).  So, now, try to make sure our names are good emodwires,
  ;; if they were originally.
  (b* (((unless (vl2014::vl-emodwire-p x))
        (intern-in-package-of-symbol
         (str::cat (symbol-name x) suffix)
         x))
       (basename (vl2014::vl-emodwire->basename x))
       (index    (vl2014::vl-emodwire->index x))
       (new-name (str::cat basename suffix))
       ((when (equal new-name "NIL"))
        ;; Stupidity, too hard...
        (raise "This will never happen.")))
    (vl2014::vl-emodwire new-name index)))

(define ecut-wire-names ((x symbolp))
  :returns (names ecutnames-p)
  (make-ecutnames
   :original      (ecut-make-sym x "<original_value>")
   :value         (ecut-make-sym x "<override_value>")
   :value-reg     (ecut-make-sym x "<override_value_reg>")
   :decision-wire (ecut-make-sym x "<override_decision>")
   :decision-reg  (ecut-make-sym x "<override_decision_reg>")
   :mux           (ecut-make-sym x "<override_mux>")))

(std::defprojection ecut-wire-list-names (x)
  (ecut-wire-names x)
  :guard (symbol-listp x)
  :result-type ecutname-list-p)


(std::defalist ecut-wirename-alistp (x)
  :key (symbolp x)
  :val (ecutnames-p x)
  :keyp-of-nil t
  :valp-of-nil nil)

(define ecut-names-alist ((wires symbol-listp))
  :returns (alist ecut-wirename-alistp :hyp :guard)
  (pairlis$ wires
            (ecut-wire-list-names wires)))

(define ecut-update-output-pattern (pat
                                    (name-fal ecut-wirename-alistp))
  (if pat
      (if (atom pat)
          (b* ((look (hons-get pat name-fal))
               ((unless look) pat))
            (ecutnames->original (cdr look)))
        (cons (ecut-update-output-pattern (car pat) name-fal)
              (ecut-update-output-pattern (cdr pat) name-fal)))
    nil))

(define ecut-update-drivers (occs
                             (name-fal ecut-wirename-alistp))
  (if (atom occs)
      nil
    (cons (chgpl :o (ecut-update-output-pattern (gpl :o (car occs))
                                                name-fal)
                 (car occs))
          (ecut-update-drivers (cdr occs) name-fal))))

(define ecut-add-override-occs-1 ((wire symbolp "The original wire name")
                                  (names ecutnames-p "Names to use"))
  :returns occs
  (b* (((ecutnames x) names)

       (value-occ
        ;;       W<override_value_reg> (.in(W<original_value>),
        ;;                              .out(W<override_value>))
        (list :u x.value-reg
              :op *esim-fsmreg*
              :i `((,x.original))
              :o `((,x.value))))

       (decision-occ
        ;;       W<override_decision_reg> (.in(0),
        ;;                                 .out(W<override_decision>))
        (list :u  x.decision-reg
              :op *esim-fsmreg*
              :i `((acl2::f))
              :o `((,x.decision-wire))))

       (mux-occ
        ;;       W<override_mux> (.sel(W<override_decision>),
        ;;                        .a(W<override_value>),
        ;;                        .b(W<original_value>),
        ;;                        .o(W))
        (list :u  x.mux
              :op *esim-zif*
              :i  `((,x.decision-wire) ;; sel
                    (,x.value)         ;; a
                    (,x.original))     ;; b
              :o  `((,wire)))))
    (list value-occ decision-occ mux-occ)))

(define ecut-add-override-occs ((name-fal ecut-wirename-alistp))
  :returns occs
  (if (atom name-fal)
      nil
    (append (ecut-add-override-occs-1 (caar name-fal)
                                      (cdar name-fal))
            (ecut-add-override-occs (cdr name-fal)))))

(local (defthm l0
         (implies (ecut-wirename-alistp x)
                  (ECUTNAME-LIST-P (ALIST-VALS x)))
         :hints(("Goal" :induct (len x)))))

(define find-f-driver (occs)
  (if (atom occs)
      nil
    (if (member-of-pat-flatten 'f (gpl :o (car occs)))
        (car occs)
      (find-f-driver (cdr occs)))))

(defconst *ecut-f-driver-occ*
  (list :o '((f))
        :u 'ecut-f-driver-occ
        :op *esim-f*))

(define ecut-make-sure-f-is-driven-to-false (mod)
  (b* ((driver (find-f-driver (gpl :occs mod)))
       ((when driver)
        (if (equal (gpl :op driver) *esim-f*)
            mod
          (raise "F is driven by something other than *esim-f*!"))))
    (chgpl :occs (cons *ecut-f-driver-occ* (gpl :occs mod))
           mod)))

(define ecut-wires-in-module
  ((wire-list   "A plain list of wires that should exist in this module.")
   (mod         "The E module to transform."))
  (b* (((when (atom wire-list))
        mod)
       (modname (gpl :n mod))
       ((unless modname)
        (raise "Expected a name on module ~x0." mod))
       ((unless (symbol-listp wire-list))
        (raise "Expected cut wire names to be symbols in ~x0" modname))
       ((when (gpl :x mod))
        (raise "In module ~x0: Can't cut wires in primitive module." modname))

       (ins       (pat-flatten1 (gpl :i mod)))
       (occs      (gpl :occs mod))
       (driven    (collect-signal-list :o occs))
       (instnames (collect-signal-list :u occs)) ;; ugh

       (has-inputs (hons-intersection ins wire-list))
       ((when has-inputs)
        (raise "In module ~x0: Can't cut input wires, such as ~x1~%"
               modname has-inputs))

       ((unless (hons-subset wire-list driven))
        (raise "In module ~x0: trying to cut nonexistent wires: ~x1."
               modname (hons-set-diff wire-list driven)))

       (wire-dups (duplicated-members wire-list))
       ((when wire-dups)
        (raise "In module ~x0: told to cut multiple occurrences of ~x1"
               modname wire-dups))

       (mod (ecut-make-sure-f-is-driven-to-false mod))

       (name-fal (ecut-names-alist wire-list))
       ((with-fast name-fal))

       (all-new-names (ecutname-list->flat-names (alist-vals name-fal)))
       (all-old-names (hons-remove-duplicates (append ins driven instnames)))
       (dups (duplicated-members (append all-new-names all-old-names)))
       ((when dups)
        (raise "Name clashes in ~x0: ~x1" modname dups))

       (occs (ecut-update-drivers (gpl :occs mod) name-fal))
       (occs (append (ecut-add-override-occs name-fal) occs)))
    (chgpl :occs occs mod)))

(define ecut-bind-paths (x atoms-acc subs-acc)
  ;; Sort paths x into atoms (cuts for the current module) and submodule paths,
  ;; and further sort the submodule paths into an alist by the immediate
  ;; submodule name.
  (b* (((when (atom x))
        (mv atoms-acc subs-acc))
       ((when (atom (car x)))
        (ecut-bind-paths (cdr x) (cons (car x) atoms-acc) subs-acc))
       (occname (caar x))
       (occ-paths (cdr (hons-get occname subs-acc)))
       (subs-acc (hons-acons occname (cons (cdar x) occ-paths) subs-acc)))
    (ecut-bind-paths (cdr x) atoms-acc subs-acc)))

(mutual-recursion
 (defun ecut-module (paths x)
   (declare (xargs :guard t
                   :well-founded-relation nat-list-<
                   :measure (list (acl2-count x) 2)))
   (b* (((when (atom paths)) x)
        ((mv atoms subpaths) (ecut-bind-paths paths nil nil))
        (occs (ecut-occs subpaths (gpl :occs x)))
        (- (fast-alist-free subpaths))
        (x (chgpl :occs occs x)))
     (ecut-wires-in-module atoms x)))
 (defun ecut-occs (subpaths occs)
   (declare (xargs :guard t
                   :measure (list (acl2-count occs) 1)))
   (if (atom occs)
       nil
     (cons (ecut-occ subpaths (car occs))
           (ecut-occs subpaths (cdr occs)))))
 (defun ecut-occ (subpaths occ)
   (declare (xargs :guard t
                   :measure (list (acl2-count occ) 3)))
   (b* ((instname (gpl :u occ))
        (paths (cdr (hons-get instname subpaths)))
        ((when (atom paths)) occ))
     (chgpl :op (ecut-module paths (gpl :op occ))
            occ))))


#||

(defun find-module (name x)
  (if (atom x)
      nil
    (if (equal (gpl :n (car x)) name)
        (car x)
      (find-module name (Cdr x)))))

(defconst *decode16*
  (find-module '|*decode16*| *esims*))




(good-esim-modulep (ecut-module '(|dout[3]|) *decode16*))
(bad-esim-modulep (ecut-module '(|dout[3]|) *decode16*))

(include-book
 "esim-sexpr")

(esim-sexpr-general-nst (ecut-module '(|dout[3]|) *decode16*))
(esim-sexpr-general-out (ecut-module '(|dout[3]|) *decode16*))

(defconst *m*
  (find-module '|*rmux2regi_en$width=1*| *esims*))

(ecut-module '((|r1| . |q|)) *m*)
(good-esim-modulep (ecut-module '((|r1| . |q[0]|)) *m*))

||#
