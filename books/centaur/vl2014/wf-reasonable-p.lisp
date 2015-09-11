; VL 2014 -- VL Verilog Toolkit, 2014 Edition
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
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "VL2014")
(include-book "mlib/modnamespace")
(include-book "mlib/find")
(include-book "mlib/expr-tools")
(include-book "mlib/range-tools")
(include-book "util/defwellformed")
(include-book "util/warnings")
(include-book "defsort/duplicated-members" :dir :system)
(local (include-book "util/arithmetic"))
(local (include-book "util/osets"))

;; BOZO this entire thing is a giant pile and should get removed.

(defxdoc reasonable
  :parents (well-formedness)
  :short "Identify modules in our supported subset of Verilog."
  :long "<p>We say a module is <i>reasonable</i> if it</p>

<ol>
  <li>is semantically well-formed, and</li>
  <li>does not contain unsupported constructs.</li>
</ol>

<p>Even though our parser essentially establishes that the files we have just
read are syntactically well-formed, this does not necessarily mean the files
are semantically well-formed.  For instance, a module might illegally declare
the same wire twice, or perhaps we have tried to declare two modules with the
same name.  So, our reasonableness check is important for ensuring the basic
semantic correctness of the modules we are examining.</p>

<p>We also regard many perfectly valid Verilog constructs as unreasonable, for
the simple pragmatic reason that we are only really interested in dealing with
the small subset of Verilog that we actually encounter at Centaur.  There is
little motivation for us to support things like complicated port lists merely
because they are in the Verilog-2005 standard.</p>")

(defwellformed vl-portlist-reasonable-p (x)
  :parents (reasonable)
  :short "@(call vl-portlist-reasonable-p) determines if a @(see vl-portlist-p)
is @(see reasonable)."
  :long "<p>We just require that any externally visible names are unique.  A
number of additional well-formedness checks are done in @(see argresolve) and
@(see e-conversion).</p>"

  :guard (vl-portlist-p x)
  :body (let* ((names (remove nil (vl-portlist->names x)))
               (dupes (duplicated-members names)))
          (@wf-assert (not dupes)
                      :vl-bad-ports
                      "Duplicate port names: ~&0."
                      (list dupes))))

(defwellformed vl-vardecl-reasonable-p (x)
  :parents (reasonable)
  :short "@(call vl-vardecl-reasonable-p) determines if a @(see vl-vardecl-p)
is @(see reasonable)."
  :long "<p>We restrict wire declarations in the following ways:</p>
<ul>

<li>The only allowed types are @('supply0'), @('supply1'), and plain
@('wire')s.  Not permitted are types such as @('wor') and @('tri0').</li>

<li>Arrays of wires are not supported.  (Note that we do support wires with
ranges, e.g., @('wire [7:0] w').  What we do not support are, e.g., @('wire w
[7:0]'), or multi-dimensional arrays such as @('wire [7:0] w [3:0]').</li>

</ul>"

  :guard (vl-vardecl-p x)
  :body
  (b* (((vl-vardecl x) x))
    (@wf-progn
     (@wf-assert (and (equal (vl-datatype-kind x.type) :vl-coretype)
                      (member (vl-coretype->name x.type) '(:vl-logic :vl-reg))
                      (member x.nettype
                              '(nil :vl-supply0 :vl-supply1 :vl-wire)))
                 :vl-bad-variable
                 "~a0: wire has unsupported type ~a1/nettype ~a2."
                 (list x x.type x.nettype))

     (@wf-assert (let ((x.udims (vl-datatype->udims x.type))
                       (x.pdims (vl-datatype->pdims x.type)))
                   (and (not x.udims)
                        (or (atom x.pdims)
                            (atom (cdr x.pdims)))))
                 :vl-bad-variable
                 "~a0: arrays are not yet supported."
                 (list x))

     (@wf-assert (vl-simplevar-p x)
                 :vl-bad-variable
                 "~a0: variable is too complicated."
                 (list x)))))

(defwellformed-list vl-vardecllist-reasonable-p (x)
  :element vl-vardecl-reasonable-p
  :guard (vl-vardecllist-p x)
  :parents (reasonable))


(defwellformed vl-portdecl-and-moduleitem-compatible-p (portdecl item)
  :parents (reasonable)
  :short "Main function for checking whether a port declaration, which overlaps
with some module item declaration, is a reasonable overlap."
  :guard (and (vl-portdecl-p portdecl)
              (vl-moditem-p item))
  :long "<p>For instance, we might have:</p>

@({
    input x;
    wire x;
})

<p>Which is fine, or we might have:</p>

@({
    input [3:0] x;
    wire [4:0] x;
})

<p>Which is definitely not okay.  See also @(see portdecl-sign).  We expect
that after parsing, the types will agree exactly.</p>"

  :body

  (b* (((vl-portdecl portdecl) portdecl)
       ((unless (eq (tag item) :vl-vardecl))
        (@wf-assert nil
                    :vl-weird-port
                    "~a0: port ~s1 is also declared to be a ~s2."
                    (list portdecl portdecl.name (tag item))))
       ((vl-vardecl vardecl) item))

    (@wf-assert (equal portdecl.type vardecl.type)
                :vl-incompatible-port
                "~a0: the variable declaration for port ~s1 has incompatible
                  type: ~a1 vs. ~a2."
                (list portdecl portdecl.type vardecl.type))))

(local
 (defthm l0
   (implies (vl-find-moduleitem name x)
            (vl-moditem-p (vl-find-moduleitem name x)))
   :hints(("Goal" :in-theory (e/d (vl-find-moduleitem)
                                  ((force)))))))


(defwellformed vl-overlap-compatible-p (names x palist ialist)
  ;; For some very large modules (post synthesis), we found the overlap checking to be very
  ;; expensive due to slow lookups.  So, we now optimize this to use fast-alist lookups.
  :parents (reasonable)
  :guard (and (string-listp names)
              (vl-module-p x)
              (equal palist (vl-make-portdecl-alist (vl-module->portdecls x)))
              (equal ialist (vl-make-moditem-alist x))
              (subsetp-equal names (vl-portdecllist->names (vl-module->portdecls x)))
              (subsetp-equal names (vl-module->modnamespace x)))
  :body (if (atom names)
            (progn$
             ;; BOZO I hate this style where the aux function frees the fast alists,
             ;; but for now it's easier to do it this way.
             (fast-alist-free ialist)
             (fast-alist-free palist)
             (@wf-assert t))
          (@wf-progn
           (@wf-call vl-portdecl-and-moduleitem-compatible-p
                     (vl-fast-find-portdecl (car names) (vl-module->portdecls x) palist)
                     (vl-fast-find-moduleitem (car names) x ialist))
           (@wf-call vl-overlap-compatible-p (cdr names) x palist ialist))))




; Always blocks are quite hard to handle because of how complex they are.  But
; we try to support a very limited subset of them.
;
; In particular, below we sketch out an extremely restrictive set of
; "reasonable statements" which include only nonblocking assignments guarded by
; if statements, and statement blocks.  This is not quite sufficient.  We also
; need to be able to look at sensitivity lists.  It turns out that in Verilog
; code such as:
;
;   always @ (posedge clk) foo ;
;
; This sensitivity list is actually part of a statement and is not part of the
; "always" itself.  These are called Procedural Timing Control Statements, and
; in our parse tree occur as vl-ptctrlstmt-p's.
;
; We do not try to support these in any general way, and prohibit them from
; occurring in "reasonable statements".  However, our always-block recognizer
; permits a single one of these to occur at the top level, as long as it meets
; a list of requirements.

;; (defwellformed vl-assignstmt-reasonable-p (x)
;;   :guard (vl-assignstmt-p x)
;;   :body (let ((type   (vl-assignstmt->type x))
;;               (lvalue (vl-assignstmt->lvalue x)))
;;           (declare (ignorable type))

;;           (@wf-progn

;;            (@wf-note

;; ; Sol and I have had a discussion and now think that delay statements on
;; ; non-blocking assignments are okay. This should definitely become a
;; ; @wf-assert, but for now I'm just using @wf-note because blocking (foo = bar)
;; ; style assignments are often used instead of nonblocking (foo <= bar) ones.

;;             (eq type :vl-nonblocking)
;;             :vl-bad-assignment
;;             "~s0: unsoundly treating ~s1 assignment as non-blocking."
;;             (list (vl-location-string (vl-assignstmt->loc x)) type))

;; ; It would be nice to drop this requirement eventually and support assignments
;; ; to concatenations and selects.  But this makes our programming much easier;
;; ; see xf-elim-always.lisp.

;;            (@wf-assert (and (vl-atom-p lvalue)
;;                             (vl-id-p (vl-atom->guts lvalue)))
;;                        :wf-lvalue-too-hard
;;                        "~s0: assignment to ~s1 is too complicated."
;;                        (list (vl-location-string (vl-assignstmt->loc x))
;;                              (vl-pps-origexpr lvalue))))))

;; (defwellformed vl-atomicstmt-reasonable-p (x)
;;   :guard (vl-atomicstmt-p x)
;;   :body (case (tag x)
;;           (:vl-nullstmt
;;            (@wf-assert t))
;;           (:vl-assignstmt
;;            (@wf-call vl-assignstmt-reasonable-p x))
;;           (t
;;            (@wf-assert nil
;;                        :vl-unsupported-stmt
;;                        "Unsupported statement: ~x0."
;;                        (list (tag x))))))

;; (mutual-defwellformed

;;  (defwellformed vl-stmt-reasonable-p (x)
;;    :guard (vl-stmt-p x)
;;    :extra-decls ((xargs :measure (two-nats-measure (acl2-count x) 0)
;;                         :verify-guards nil))
;;    :body (cond
;;           ((vl-atomicstmt-p x)
;;            (@wf-call vl-atomicstmt-reasonable-p x))

;;           ((mbe :logic (not (consp x))
;;                 :exec nil)
;;            (prog2$
;;             (er hard 'vl-stmt-reasonable-p "Impossible case for termination.")
;;             (@wf-assert t)))

;;           (t
;;            (let ((type  (vl-compoundstmt->type x))
;;                  (stmts (vl-compoundstmt->stmts x))
;;                  (name  (vl-compoundstmt->name x))
;;                  (decls (vl-compoundstmt->decls x)))
;;              (case type
;;                (:vl-ifstmt
;;                 (@wf-call vl-stmtlist-reasonable-p stmts))
;;                (:vl-seqblockstmt
;;                 (@wf-progn
;;                  (@wf-assert (and (not name)
;;                                   (atom decls))
;;                              :vl-unsupported-block
;;                              "Block contains a name or declarations, which we don't support yet."
;;                              nil)
;;                  (@wf-call vl-stmtlist-reasonable-p stmts)))
;;                (otherwise
;;                 (@wf-assert t)))))))

;;  (defwellformed vl-stmtlist-reasonable-p (x)
;;    :guard (vl-stmtlist-p x)
;;    :extra-decls ((xargs :measure (two-nats-measure (acl2-count x) 0)))
;;    :body (if (atom x)
;;              (@wf-assert t)
;;            (@wf-progn
;;             (@wf-call vl-stmt-reasonable-p (car x))
;;             (@wf-call vl-stmtlist-reasonable-p (cdr x))))))

;; (verify-guards vl-stmt-reasonable-p)
;; (verify-guards vl-stmt-reasonable-p-warn)



;; (defund vl-edge-eventcontrol-p (x)
;;   (declare (xargs :guard (vl-eventcontrol-p x)))

;; ; Recognizes event controls like @ (posedge clk) or @ (negedge clk)

;;   (let ((starp (vl-eventcontrol->starp x))
;;         (atoms (vl-eventcontrol->atoms x)))
;;     (and (not starp)
;;          (= (len atoms) 1)
;;          (let* ((atom (car atoms))
;;                 (type (vl-evatom->type atom))
;;                 (expr (vl-evatom->expr atom)))
;;            (declare (ignorable type))
;;            (and (or (eq type :vl-posedge)
;;                     (eq type :vl-negedge))
;;                 (vl-atom-p expr)
;;                 (vl-id-p (vl-atom->guts expr)))))))

;; (defund vl-edge-eventcontrol->type (x)
;;   (declare (xargs :guard (and (vl-eventcontrol-p x)
;;                               (vl-edge-eventcontrol-p x))
;;                   :guard-hints (("Goal" :in-theory (enable vl-edge-eventcontrol-p)))))
;;   (vl-evatom->type (car (vl-eventcontrol->atoms x))))

;; (defund vl-edge-eventcontrol->name (x)
;;   (declare (xargs :guard (and (vl-eventcontrol-p x)
;;                               (vl-edge-eventcontrol-p x))
;;                   :guard-hints (("Goal" :in-theory (enable vl-edge-eventcontrol-p)))))
;;   (vl-id->name
;;    (vl-atom->guts
;;     (vl-evatom->expr
;;      (car (vl-eventcontrol->atoms x))))))



;; (defund vl-nonedge-evatom-p (x)
;;   (declare (xargs :guard (vl-evatom-p x)))
;;   (let ((type (vl-evatom->type x))
;;         (expr (vl-evatom->expr x)))
;;     (and (eq type :vl-noedge)
;;          (vl-atom-p expr)
;;          (vl-id-p (vl-atom->guts expr)))))

;; (defund vl-nonedge-evatom->name (x)
;;   (declare (xargs :guard (and (vl-evatom-p x)
;;                               (vl-nonedge-evatom-p x))
;;                   :guard-hints (("Goal" :in-theory (enable vl-nonedge-evatom-p)))))
;;   (vl-id->name
;;    (vl-atom->guts
;;     (vl-evatom->expr x))))

;; (deflist vl-nonedge-evatomlist-p (x)
;;   (vl-nonedge-evatom-p x)
;;   :guard (vl-evatomlist-p x))

;; (defprojection vl-nonedge-evatomlist->names (x)
;;   (vl-nonedge-evatom->name x)
;;   :guard (and (vl-evatomlist-p x)
;;               (vl-nonedge-evatomlist-p x)))

;; (defund vl-nonedge-eventcontrol-p (x)
;;   (declare (xargs :guard (vl-eventcontrol-p x)))

;; ; Recognizes event controls such as @ (foo or bar or baz)

;;   (let ((starp (vl-eventcontrol->starp x))
;;         (atoms (vl-eventcontrol->atoms x)))
;;     (and (not starp)
;;          (consp atoms)
;;          (vl-nonedge-evatomlist-p atoms))))

;; (defund vl-nonedge-eventcontrol->names (x)
;;   (declare (xargs :guard (and (vl-eventcontrol-p x)
;;                               (vl-nonedge-eventcontrol-p x))
;;                   :guard-hints (("Goal" :in-theory (enable vl-nonedge-eventcontrol-p)))))
;;   (vl-nonedge-evatomlist->names (vl-eventcontrol->atoms x)))

;; (defund vl-eventcontrol-reasonable-p (x)
;;   (declare (xargs :guard (vl-eventcontrol-p x)))
;;   (or (vl-nonedge-eventcontrol-p x)
;;       (vl-edge-eventcontrol-p x)))



;; (defwellformed vl-always-reasonable-p (x)
;;   :guard (vl-always-p x)
;;   :body (let ((stmt (vl-always->stmt x)))
;;           (@wf-and

;; ; We expect it to be always @ ..., and do not try to support any other kind of
;; ; always statement.

;;            (@wf-assert (and (vl-compoundstmt-p stmt)
;;                             (eq (vl-compoundstmt->type stmt) :vl-ptctrlstmt)
;;                             (eq (tag (vl-compoundstmt->ctrl stmt)) :vl-eventcontrol)
;;                             (vl-eventcontrol-reasonable-p (vl-compoundstmt->ctrl stmt)))
;;                        :vl-always-badctrl
;;                        "~s0: not a good event-control, i.e., \"@(...)\"."
;;                        (list (vl-location-string (vl-always->loc x))))

;;            (@wf-call vl-stmt-reasonable-p (car (vl-compoundstmt->stmts stmt))))))

;; (defwellformed-list vl-alwayslist-reasonable-p (x)
;;   :element vl-always-reasonable-p
;;   :guard (vl-alwayslist-p x))


(defwellformed vl-module-reasonable-p (x)
  :parents (reasonable)
  :guard (vl-module-p x)
  :extra-decls ((xargs :guard-debug t))
  :body
  (b* (((vl-module x) x)
       (pdnames       (vl-portdecllist->names x.portdecls))
       (pdnames-s     (mergesort pdnames))
       (namespace     (vl-module->modnamespace x))
       (namespace-s   (mergesort namespace))
       (overlap       (intersect pdnames-s namespace-s))
       (palist        (vl-make-portdecl-alist x.portdecls))
       (ialist        (vl-make-moditem-alist x)))
    (@wf-progn
     (@wf-call vl-portlist-reasonable-p x.ports)
     ;; (@wf-call vl-ports-and-portdecls-compatible-p ports portdecls)
     (@wf-call vl-vardecllist-reasonable-p x.vardecls)
     (@wf-note (not x.initials)
               :vl-initial-stmts
               "~l0: module ~s1 contains initial statements."
               (list x.minloc x.name))

; Not really a problem anymore
;     (@wf-note (not alwayses)
;               :vl-always-stmts
;               "~l0: module ~s1 contains always statements."
;               (list minloc name))

;     (@wf-call vl-alwayslist-reasonable-p alwayses)
     (@wf-assert (mbe :logic (no-duplicatesp-equal namespace)
                      :exec (same-lengthp namespace namespace-s))
                 :vl-namespace-error
                 "~l0: ~s1 illegally redefines ~&2."
                 (list x.minloc x.name (duplicated-members namespace)))
     (@wf-call vl-overlap-compatible-p overlap x palist ialist))))

(defwellformed-list vl-modulelist-reasonable-p (x)
  :parents (reasonable)
  :guard (vl-modulelist-p x)
  :element vl-module-reasonable-p)


(define vl-module-check-reasonable
  :parents (reasonable)
  :short "Annotate a module with any warnings concerning whether it is @(see
reasonable).  Furthermore, if @('x') is unreasonable, a fatal warning to it."
  ((x vl-module-p))
  :returns (new-x vl-module-p :hyp :fguard)
  (b* (((when (vl-module->hands-offp x))
        x)
       (warnings          (vl-module->warnings x))
       ((mv okp warnings) (vl-module-reasonable-p-warn x warnings))
       (warnings          (if okp
                              (ok)
                            (fatal :type :vl-mod-unreasonable
                                   :msg "Module ~m0 is unreasonable."
                                   :args (list (vl-module->name x)))))
       (warnings          (if (vl-module->generates x)
                              (fatal :type :vl-mod-has-generates
                                     :msg "Module ~m0 has generate blocks."
                                     :args (list (vl-module->name x)))
                            warnings))
       (x-prime (change-vl-module x :warnings warnings)))
    x-prime))

(defprojection vl-modulelist-check-reasonable (x)
  (vl-module-check-reasonable x)
  :guard (vl-modulelist-p x)
  :result-type vl-modulelist-p
  :parents (reasonable))

(define vl-design-check-reasonable ((design vl-design-p))
  :returns (new-design vl-design-p)
  (b* ((design (vl-design-fix design))
       ((vl-design design) design)
       (new-mods (vl-modulelist-check-reasonable design.mods)))
    (change-vl-design design :mods new-mods)))

