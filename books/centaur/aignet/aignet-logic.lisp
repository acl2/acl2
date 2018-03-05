; AIGNET - And-Inverter Graph Networks
; Copyright (C) 2013 Centaur Technology
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

(in-package "AIGNET")
;; (include-book "centaur/aignet/idp" :dir :system)
(include-book "litp")
(include-book "std/util/defmvtypes" :dir :system)
(include-book "std/util/defprojection" :dir :system)
(include-book "centaur/fty/deftypes" :dir :system)
(include-book "std/util/defval" :dir :system)
(include-book "std/util/defenum" :dir :system)
(include-book "std/lists/equiv" :dir :system)
(include-book "tools/defmacfun" :dir :system)
(include-book "arithmetic/nat-listp" :dir :system)
(include-book "std/basic/arith-equivs" :dir :system)
(include-book "tools/flag" :dir :system)
(include-book "std/basic/two-nats-measure" :dir :system)
(include-book "clause-processors/unify-subst" :dir :system)
(include-book "centaur/misc/prev-stobj-binding" :dir :system)
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "data-structures/list-defthms" :dir :system))
(local (in-theory (enable* acl2::arith-equiv-forwarding)))
(local (in-theory (disable nth
                           update-nth
                           resize-list
                           make-list-ac
                           acl2::nfix-when-not-natp
                           acl2::resize-list-when-empty
                           acl2::make-list-ac-redef
                           ;; set::double-containment
                           ;; set::sets-are-true-lists
                           true-listp-update-nth
                           acl2::nth-with-large-index)))
(local (std::add-default-post-define-hook :fix))

(defsection sequential-type
  :parents (stypep)
  :short "See @(see stypep)."

  (std::defenum stypep (:pi :reg :po :nxst :and :xor :const)
    :fix stype-fix
    :equiv stype-equiv
    :parents (representation)
    :short "Sequential type of a logical AIG @(see node)."

    :long "<p>Recall that AIG nodes are represented as lists like @('(:pi)'),
@('(:gate fanin0 fanin1)'), etc.</p>

<p>The <b>sequential type</b> of such a type is just its leading keyword.  The
valid sequential types are:</p>

<ul>
  <li>@(':const') for the special constant node</li>
  <li>@(':and') for an AND gate node</li>
  <li>@(':xor') for an XOR gate node</li>
  <li>@(':pi') or @(':po') for primary input/output nodes</li>
  <li>@(':reg') for register nodes (register outputs)</li>
  <li>@(':nxst') for next state nodes (register inputs)</li>
</ul>

<p>See also @(see combinational-type) for a combinational (instead of
sequential) view of AIG node types.</p>")

  (defmacro pi-stype () :pi)
  (defmacro reg-stype () :reg)
  (defmacro po-stype () :po)
  (defmacro nxst-stype () :nxst)
  (defmacro and-stype () :and)
  (defmacro xor-stype () :xor)
  (defmacro const-stype () :const))

(fty::defflexsum node
  :parents (representation)
  :short "Type of an AIG node in an aignet object, logically."
  :long "<p>See also @(see network) for network-related functions.</p>"
  :kind stype
  :kind-body (if (atom x)
                 :const
               (stype-fix (car x)))
  (:const :cond (or (atom x)
                    (not (stypep (car x)))
                    (eq (car x) :const))
   :short "A constant-0 node."
   :shape (eq x nil)
   :ctor-body nil
   :type-name const-node
   :no-ctor-macros t)
  (:pi :cond (eq (car x) :pi)
   :short "A primary input node."
   :type-name pi-node
   :shape (not (cdr x))
   :ctor-body '(:pi)
   :no-ctor-macros t)
  (:reg :cond (eq (car x) :reg)
   :short "A register node."
   :type-name reg-node
   :shape (not (cdr x))
   :ctor-body '(:reg)
   :no-ctor-macros t)
  (:and :cond (eq (car x) :and)
   :short "An AND gate node."
   :type-name and-node
   :shape (and (true-listp x) (eql (len x) 3))
   :fields ((fanin0 :type litp :acc-body (cadr x)
                    :doc "First fanin @(see literal) of the AND gate"
                    :rule-classes :type-prescription)
            (fanin1 :type litp :acc-body (caddr x)
                    :doc "Second fanin @(see literal) of the AND gate"
                    :rule-classes :type-prescription))
   :ctor-body (list :and fanin0 fanin1)
   :no-ctor-macros t)
  (:xor :cond (eq (car x) :xor)
   :short "An AND gate node."
   :type-name xor-node
   :shape (and (true-listp x) (eql (len x) 3))
   :fields ((fanin0 :type litp :acc-body (cadr x)
                    :doc "First fanin @(see literal) of the AND gate"
                    :rule-classes :type-prescription)
            (fanin1 :type litp :acc-body (caddr x)
                    :doc "Second fanin @(see literal) of the AND gate"
                    :rule-classes :type-prescription))
   :ctor-body (list :xor fanin0 fanin1)
   :no-ctor-macros t)
  (:po :cond (eq (car x) :po)
   :short "A primary output node."
   :type-name po-node
   :shape (and (true-listp x) (eql (len x) 2))
   :fields ((fanin :type litp :acc-body (cadr x)
                   :doc "Literal giving the logical function of the output."
                   :rule-classes :type-prescription))
   :ctor-body (list :po fanin)
   :no-ctor-macros t)
  (:nxst :cond (eq (car x) :nxst)
   :short "A next-state node for a register."
   :type-name nxst-node
   :shape (and (true-listp x) (eql (len x) 3))
   :fields ((fanin :type litp :acc-body (cadr x)
                   :doc "Literal giving the logical function of the next state."
                   :rule-classes :type-prescription)
            (reg :type natp :acc-body (caddr x)
                 :doc "Index of the register for which this is the next state."
                 :rule-classes :type-prescription))
   :ctor-body (list :nxst fanin reg)
   :no-ctor-macros t))

(defsection stype
  :extension stype
  (defthm stypep-of-stype
    (stypep (stype x))
    :hints(("Goal" :in-theory (enable stypep))))

  (defthm stype-not-const-implies-nonempty
    (implies (not (equal (stype (car x)) (const-stype)))
             (consp x))
    :rule-classes ((:forward-chaining :trigger-terms
                    ((stype (car x)))))))


(define regp ((x stypep))
  :returns (regp bitp)
  :parents (sequential-type)
  :short "Correlates the @(see sequential-type) of a node with the @('regp')/@('xorp') of its bit encoding.
This bit is set for @(':reg'), @(':nxst'), and @('xor') nodes, so this returns 1 for those types and 0 for others."
  (if (member (stype-fix x) '(:reg :nxst :xor))
      1
    0)
  ///
  (defcong stype-equiv equal (regp x) 1)

  (defthm regp-not-zero-implies-nonempty
    (implies (not (equal (regp (stype (car x))) 0))
             (consp x))
    :rule-classes ((:forward-chaining :trigger-terms
                    ((regp (stype (car x))))))))




(defsection combinational-type
  :parents (representation)
  :short "Combinational type of a logical AIG @(see node)."
  :long "<p>Recall that a sequential AIG can be viewed as a combinational AIG
  by ignoring the distinction between register and primary inputs/outputs.</p>

  <p>We can implement the combinational view of AIG nodes by mapping the @(see
  sequential-type) of a node to a combinational type.  The valid combinational
  type keywords are:</p>

  <ul>
  <li>@(':const') for the special constant node</li>
  <li>@(':gate') for an AND or XOR gate node</li>
  <li>@(':input') for a combinational input (primary input or register <b>output</b>)</li>
  <li>@(':output') for a combinational output (primary input or register <b>input</b>)</li>
  </ul>"

  (defmacro const-ctype () :const)
  (defmacro gate-ctype () :gate)
  (defmacro in-ctype () :input)
  (defmacro out-ctype () :output))

(define ctypep (x)
  :parents (combinational-type)
  :short "Recognizer for valid @(see combinational-type) keywords."
  :returns bool
  (member x (list (in-ctype)
                  (out-ctype)
                  (gate-ctype)
                  (const-ctype))))

(define ctype-fix (x)
  :returns (ctype ctypep)
  :parents (combinational-type)
  :short "Fixing function for @(see combinational-type) keywords."
  (if (ctypep x)
      x
    (const-ctype))
  ///
  (defthm ctype-fix-when-ctypep
    (implies (ctypep x)
             (equal (ctype-fix x) x))))

(define ctype-equiv (x y)
  :parents (combinational-type)
  :short "Equivalence relation for @(see combinational-type) keywords."
  :returns bool
  :enabled t
  (equal (ctype-fix x) (ctype-fix y))
  ///
  (defequiv ctype-equiv)
  (defcong ctype-equiv equal (ctype-fix x) 1)
  (defthm ctype-fix-under-ctype-equiv
    (ctype-equiv (ctype-fix x) x)))

;; (defthm ctype-fix-possibilities
;;   (or (equal (ctype-fix x) (const-ctype))
;;       (equal (ctype-fix x) (gate-ctype))
;;       (equal (ctype-fix x) (in-ctype))
;;       (equal (ctype-fix x) (out-ctype)))
;;   :rule-classes ((:forward-chaining :trigger-terms
;;                   ((ctype-fix x))))
;;   :hints(("Goal" :in-theory (enable ctype-fix ctypep))))

(defval *stype-ctype-map*
  :parents (ctype)
  :showdef nil
  :showval t
  `((,(const-stype) . ,(const-ctype))
    (,(and-stype) . ,(gate-ctype))
    (,(xor-stype) . ,(gate-ctype))
    (,(nxst-stype) . ,(out-ctype))
    (,(reg-stype) . ,(in-ctype))
    (,(po-stype) . ,(out-ctype))
    (,(pi-stype) . ,(in-ctype))))

(define ctype ((x stypep))
  :returns (type ctypep)
  :parents (combinational-type)
  :short "Map a @(see sequential-type) keyword to its @(see combinational-type) keywords."
  :prepwork ((local (in-theory (enable stype-fix stypep))))
  (let ((x (stype-fix x)))
    (cdr (assoc x *stype-ctype-map*)))
  ///
  (defthm ctype-possibilities
    (or (equal (ctype x) (const-ctype))
        (equal (ctype x) (gate-ctype))
        (equal (ctype x) (in-ctype))
        (equal (ctype x) (out-ctype)))
    :rule-classes ((:forward-chaining :trigger-terms
                    ((ctype x))))
    :hints(("Goal" :in-theory (enable ctype ctypep))))

  (defcong stype-equiv equal (ctype x) 1)

  (defthm ctype-not-const-implies-nonempty
    (implies (not (equal (ctype (stype (car x))) (const-ctype)))
             (consp x))
    :rule-classes ((:forward-chaining :trigger-terms
                    ((ctype (stype (car x)))))))

  (defthm stype-by-ctype
    (and (equal (equal (ctype (stype x)) (const-ctype))
                (equal (stype x) (const-stype)))
         (implies (equal (regp (stype x)) 1)
                  (and (equal (equal (ctype (stype x)) (in-ctype))
                              (equal (stype x) (reg-stype)))
                       (equal (equal (ctype (stype x)) (out-ctype))
                              (equal (stype x) (nxst-stype)))
                       (equal (equal (ctype (stype x)) (gate-ctype))
                              (equal (stype x) (xor-stype)))))
         (implies (not (equal (regp (stype x)) 1))
                  (and (equal (equal (ctype (stype x)) (in-ctype))
                              (equal (stype x) (pi-stype)))
                       (equal (equal (ctype (stype x)) (out-ctype))
                              (equal (stype x) (po-stype)))
                       (equal (equal (ctype (stype x)) (gate-ctype))
                              (equal (stype x) (and-stype))))))
    :hints(("goal" :in-theory (enable stype ctype regp))))

  (defthm stype-not-const-fwd
    (implies (not (equal (stype x) (const-stype)))
             (not (equal (ctype (stype x)) (const-ctype))))
    :rule-classes ((:forward-chaining :trigger-terms ((stype x)))))

  (defthm ctype-not-gate-fwd
    (implies (not (equal (ctype (stype x)) (gate-ctype)))
             (and (not (equal (stype x) (and-stype)))
                  (not (equal (stype x) (xor-stype)))))
    :rule-classes ((:forward-chaining :trigger-terms ((ctype (stype x))))))

  (defthm ctype-not-in-fwd
    (implies (not (equal (ctype (stype x)) (in-ctype)))
             (and (not (equal (stype x) (pi-stype)))
                  (not (equal (stype x) (reg-stype)))))
    :rule-classes ((:forward-chaining :trigger-terms ((ctype (stype x))))))

  (defthm ctype-not-out-fwd
    (implies (not (equal (ctype (stype x)) (out-ctype)))
             (and (not (equal (stype x) (po-stype)))
                  (not (equal (stype x) (nxst-stype)))))
    :rule-classes ((:forward-chaining :trigger-terms ((ctype (stype x)))))))



(define typecodep (x)
  :parents (typecode)
  :short "Recognizer for valid @(see typecode)s."
  (and (natp x)
       (< x 4)))

(define typecode-fix (x)
  :returns (code typecodep)
  :parents (typecode)
  :short "Fixing function for @(see typecode)s."
  (if (typecodep x)
      x
    0)
  ///
  (local (in-theory (enable typecodep)))

  (defthm typecode-fix-when-typecodep
    (implies (typecodep x)
             (equal (typecode-fix x)
                    x))))

(defmacro const-type () 0)
(defmacro gate-type () 1)
(defmacro in-type () 2)
(defmacro out-type () 3)

(defval *ctype-code-map*
  :parents (typecode)
  :showdef nil
  :showval t
  `((,(in-ctype) . ,(in-type))
    (,(out-ctype) . ,(out-type))
    (,(gate-ctype) . ,(gate-type))
    (,(const-ctype) . ,(const-type))))

(define typecode ((x ctypep))
  :parents (representation)
  :returns (code natp :rule-classes (:rewrite :type-prescription))
  :short "Numeric encoding of a @(see combinational-type) keyword."
  :prepwork ((local (in-theory (enable ctype-fix ctypep))))
  (cdr (assoc (ctype-fix x) *ctype-code-map*))
  ///
  (defthm typecode-bound
    (< (typecode x) 4)
    :rule-classes :linear)

  (defthm typecodep-of-typecode
    (typecodep (typecode x))))

(define code->ctype ((x typecodep))
  :returns (ctype ctypep)
  :prepwork ((local (in-theory (enable typecode-fix typecodep))))
  :parents (typecode)
  :short "Get the @(see combinational-type) keyword from its numeric encoding."
  (car (rassoc (typecode-fix x) *ctype-code-map*))
  ///
  (local (in-theory (enable typecode ctype-fix ctypep)))
  (defthm code->ctype-of-typecode
    (equal (code->ctype (typecode x))
           (ctype-fix x))
    :hints(("Goal" :in-theory (enable typecode))))

  (defthm typecode-of-code->ctype
    (equal (typecode (code->ctype x))
           (typecode-fix x)))

  (defthm normalize-typecode-equivalence
    (equal (equal (typecode x) code)
           (and (typecodep code)
                (equal (ctype-fix x) (code->ctype code))))))



(define node->type ((node node-p))
  :returns (typecode natp :rule-classes :type-prescription)
  :parents (node typecode)
  :short "Get the combinational @(see typecode) from a logical node."
  :enabled t
  (typecode (ctype (stype node))))


(define node->regp ((node node-p))
  :short "Get the @('regp')/@('xorp') bit of a node's encoding -- 1 if it is a
          @(':reg'), @(':nxst'), or @(':xor') node.  Note: returns a @(see
          bitp)."
  :returns (bit bitp)
  :enabled t
  :parents (node)
  (regp (stype node)))

(define proper-node-p (x)
  :short "Recognizer for any node except for the special constant node."
  :enabled t
  :parents (node)
  (and (node-p x)
       (not (eq (stype x) :const))))

(define co-node->fanin ((node node-p))
  :guard (equal (node->type node) (out-type))
  :returns (lit litp :rule-classes :type-prescription)
  :short "Access the fanin @(see literal) from a combinational output node,
          i.e., from a primary output or a next-state (register input) node."
  :parents (node)
  :prepwork ((local (in-theory (e/d (node->type
                                     node->regp)
                                    ((force))))))

  (lit-fix (if (equal (node->regp node) 1)
               (nxst-node->fanin node)
             (po-node->fanin node)))
  ///
  (defthm co-node->fanin-of-po-node
    (equal (co-node->fanin (po-node f))
           (lit-fix f)))
  (defthm co-node->fanin-of-nxst-node
    (equal (co-node->fanin (nxst-node f n))
           (lit-fix f))))

(define gate-node->fanin0 ((node node-p))
  :guard (equal (node->type node) (gate-type))
  :returns (lit litp :rule-classes :type-prescription)
  :short "Access the fanin 0 @(see literal) from a gate node,
          whether an AND or an XOR."
  :parents (node)
  :prepwork ((local (in-theory (e/d (node->type
                                     node->regp)
                                    ((force))))))

  (lit-fix (if (equal (node->regp node) 1)
               (xor-node->fanin0 node)
             (and-node->fanin0 node)))
  ///
  (defthm gate-node->fanin0-of-and-node
    (equal (gate-node->fanin0 (and-node f0 f1))
           (lit-fix f0)))
  (defthm gate-node->fanin0-of-xor-node
    (equal (gate-node->fanin0 (xor-node f0 f1))
           (lit-fix f0))))

(define gate-node->fanin1 ((node node-p))
  :guard (equal (node->type node) (gate-type))
  :returns (lit litp :rule-classes :type-prescription)
  :short "Access the fanin 1 @(see literal) from a gate node,
          whether an AND or an XOR."
  :parents (node)
  :prepwork ((local (in-theory (e/d (node->type
                                     node->regp)
                                    ((force))))))

  (lit-fix (if (equal (node->regp node) 1)
               (xor-node->fanin1 node)
             (and-node->fanin1 node)))
  ///
  (defthm gate-node->fanin1-of-and-node
    (equal (gate-node->fanin1 (and-node f0 f1))
           (lit-fix f1)))
  (defthm gate-node->fanin1-of-xor-node
    (equal (gate-node->fanin1 (xor-node f0 f1))
           (lit-fix f1))))

;; (defsection aignet-case
;;   :parents (base-api)
;;   :short "Macro for @(see combinational-type) case splits."
;;   :long "<p>Syntax:</p>
;;   @({
;;       (aignet-case typecode
;;         :const ...
;;         :gate ...
;;         :in ...
;;         :out ...)
;;   })

;;   <p>Where @('typecode') is the @(see typecode) for this node, i.e., it is a
;;   number, not a @(see combinational-type) keyword.</p>

;;   <p>See also @(see aignet-seq-case) for a sequential version.</p>"

;;   (defmacro aignet-case (type &key const gate in out)
;;     ;; [Jared] added "the" forms only to try to ensure that type/regp are
;;     ;; being used in a sensible way.
;;     `(case (the (unsigned-byte 2) ,type)
;;        (,(gate-type)      ,gate)
;;        (,(in-type)        ,in)
;;        (,(out-type)       ,out)
;;        (otherwise         ,const))))

(defsection aignet-case
  :parents (base-api)
  :short "Macro for node type case splits."
  :long "<p>Basic example:</p>
  @({
      (aignet-case typecode reg-bit
        :pi ...
        :po ...
        :reg ...
        :nxst ...
        :and ...
        :xor ...
        :const ...)
  })

  <p>Where @('typecode') is the @(see typecode) for this node, i.e., it is a
  number, not a @(see sequential-type) keyword, and where @('reg-bit') is a
  @(see bitp) such as from @(see regp).</p>

  <p>Alternately, you can combine:</p>

  <ul>

  <li>The @(':pi') and @(':reg') (register output) cases into a
  @(':ci') (combinational input) or @(':in') case.</li>

  <li>The @(':po') and @(':nxst') (register input) cases into a
  @(':co') (combinational output) or @(':out') case.</li>

  <li>The @(':and') and @(':xor') cases into a @(':gate') case.</li>

  </ul>

  <p>If none of @(':pi'), @(':reg'), @(':po'), @(':nxst'), @(':and'), or
  @(':xor') are used, then the @('reg-bit') argument may be skipped.  If it is
  provided anyway, it will be ignored in that case.</p>

  <p>That is, using this combined syntax you can write:</p>

  @({
      (aignet-case typecode
        :ci ...
        :co ...
        :gate ...
        :const ...)
  })"

  (defun keyword-value-keys (x)
    (declare (xargs :guard (keyword-value-listp x)))
    (if (atom x)
        nil
      (cons (car x)
            (keyword-value-keys (cddr x)))))

  (defmacro aignet-case (type &rest args)
    ;; [Jared] added "the" forms only to try to ensure that type/regp are
    ;; being used in a sensible way.
    (b* ((reg-bit-skippedp (keywordp (car args)))
         (keyvals (if reg-bit-skippedp args (cdr args)))
         ((unless (keyword-value-listp keyvals))
          (er hard? 'aignet-case "Syntax error: arguments after typecode [ ~
                                  reg-bit ] must be a keyword value list."))
         (keys (keyword-value-keys keyvals))
         (bad-keys (set-difference-eq keys '(:pi :reg :nxst :po :and :xor :in :ci :out :co :gate :const)))
         ((when bad-keys)
          (er hard? 'aignet-case "Unrecognized keys: ~x0" bad-keys))
         ((when (and reg-bit-skippedp
                     (or (member :pi keys)
                         (member :reg keys)
                         (member :nxst keys)
                         (member :po keys)
                         (member :and keys)
                         (member :xor keys))))
          (er hard? 'aignet-case "Syntax error: keys :pi, :reg, :po, :nxst, ~
                                  :and, or :xor require the reg-bit argument ~
                                  to be present."))
         ((when (and (member :ci keys)
                     (member :in keys)))
          (er hard? 'aignet-case "Can't have both :ci and :in -- they are aliases"))
         ((when (and (member :co keys)
                     (member :out keys)))
          (er hard? 'aignet-case "Can't have both :co and :out -- they are aliases"))
         ((when (and (or (member :ci keys)
                         (member :in keys))
                     (or (member :pi keys)
                         (member :reg keys))))
          (er hard? 'aignet-case "Can't have both a :ci and a :pi or :reg entry."))
         ((when (and (or (member :co keys)
                         (member :out keys))
                     (or (member :po keys)
                         (member :nxst keys))))
          (er hard? 'aignet-case "Cant have both a :co and a :po or :nxst entry."))
         ((when (and (member :gate keys)
                     (or (member :and keys)
                         (member :xor keys))))
          (er hard? 'aignet-case "Cant have both a :gate and an :and or :xor entry."))
         (reg-bit (and (not reg-bit-skippedp) (car args))))
    `(case (the (unsigned-byte 2) ,type)
       (,(gate-type) ,(if (member :gate keyvals)
                          (cadr (assoc-keyword :gate keyvals))
                        `(if (int= 1 (the bit ,reg-bit))
                             ,(cadr (assoc-keyword :xor keyvals))
                           ,(cadr (assoc-keyword :and keyvals)))))
       (,(in-type)   ,(if (assoc-keyword :ci keyvals)
                          (cadr (assoc-keyword :ci keyvals))
                        (if (assoc-keyword :in keyvals)
                            (cadr (assoc-keyword :in keyvals))
                          `(if (int= 1 (the bit ,reg-bit))
                               ,(cadr (assoc-keyword :reg keyvals))
                             ,(cadr (assoc-keyword :pi keyvals))))))
       (,(out-type)  ,(if (assoc-keyword :co keyvals)
                          (cadr (assoc-keyword :co keyvals))
                        (if (assoc-keyword :out keyvals)
                            (cadr (assoc-keyword :out keyvals))
                          `(if (int= 1 (the bit ,reg-bit))
                             ,(cadr (assoc-keyword :nxst keyvals))
                           ,(cadr (assoc-keyword :po keyvals))))))
       (otherwise    ,(cadr (assoc-keyword :const keyvals)))))))


(defsection network
  :parents (representation)
  :short "Reference guide for basic functions for working with the AIG network,
  i.e., a list of @(see node)s.")

(local (xdoc::set-default-parents network))

(fty::deflist node-list :pred node-listp :elt-type node :true-listp t :elementp-of-nil t
  ///
  (fty::deffixcong node-list-equiv equal (consp x) x)
  (local
   (defthm induct-by-list-equiv
     t
     :rule-classes ((:induction
                     :pattern (list-equiv x y)
                     :scheme (acl2::fast-list-equiv x y)))))

  (local (in-theory (enable (:induction acl2::fast-list-equiv))))

  (defrefinement list-equiv node-list-equiv
    :hints(("Goal" :in-theory (enable node-list-fix)))))

(std::deflist proper-node-listp (x)
  (proper-node-p x)
  :true-listp t
  ///
  (defthmd proper-node-listp-implies-node-listp
    (implies (proper-node-listp x)
             (node-listp x))
    :hints(("Goal" :in-theory (enable proper-node-listp
                                      node-listp)))))







(define node-count (x)
  :short "Alias for @(see len) that is only for use on Aignets."
  :long "<p>This is just @('(len x)') but we use a new function so that we can
  write more expensive rewrite rules than would be appropriate for
  @('len').</p>"
  (if (atom x)
      0
    (+ 1 (node-count (cdr x))))
  ///
  (defthm node-count-of-cons
    (equal (node-count (cons a x))
           (+ 1 (node-count x))))
  (defthm node-count-of-atom
    (implies (not (consp x))
             (equal (node-count x) 0))
    :rule-classes ((:rewrite :backchain-limit-lst 1)))
  (defthm node-count-equal-0
    (equal (equal (node-count x) 0)
           (not (consp x))))
  (defthm node-count-greater-than-0
    (equal (< 0 (node-count x))
           (consp x)))
  (defthm node-count-of-cdr-strong
    (implies (consp x)
             (equal (node-count (cdr x)) (+ -1 (node-count x)))))
  (defthm node-count-of-cdr-weak
    (<= (node-count (cdr x)) (node-count x))
    :rule-classes :linear)

  (fty::deffixcong node-list-equiv equal (node-count x) x))


(define stype-count ((type stypep)
                     (x node-listp))
  :returns (count natp :rule-classes :type-prescription)
  :short "@(call stype-count) counts the number of @(see node)s whose
  @(see sequential-type) is @('type') in the node list @('x')."
  :long "<p>This is a key function in the logical story of Aignet input,
  output, and register numbering.  See @(see representation) for more
  details.</p>"
  (cond ((atom x) 0)
        ((equal (stype-fix type) (stype (car x)))
         (+ 1 (stype-count type (cdr x))))
        (t (stype-count type (cdr x))))
  ///
  ;; (defcong stype-equiv equal (stype-count type x) 1)
  ;; (defcong list-equiv equal (stype-count type x) 2)
  (defthm stype-count-of-cons
    (equal (stype-count type (cons a b))
           (if (equal (stype-fix type) (stype a))
               (+ 1 (stype-count type b))
             (stype-count type b))))
  (defthm stype-count-of-atom
    (implies (not (consp x))
             (equal (stype-count type x)
                    0))
    :rule-classes ((:rewrite :backchain-limit-lst 1)))

  (defthm positive-stype-count-implies-consp
    (implies (< 0 (stype-count stype x))
             (and (consp x)
                  (posp (node-count x))))
    :hints(("Goal" :in-theory (enable stype-count node-count)))
    :rule-classes :forward-chaining))


(define aignet-extension-p ((new node-listp "Perhaps an extension of @('old').")
                            (old node-listp "Original @('aignet') that @('new') may extend."))
  :returns bool
  :parents (network)
  :short "@(call aignet-extension-p) determines if the aignet @('new') is the
result of building some new nodes onto another aignet @('old')."

  :long "<p>Another way of looking at this is that the aignet @('new') is an
extension of @('old') if @('old') is some suffix of @('new').</p>

<p>This is a transitive, reflexive relation. This is a useful concept because
every @('aignet')-modifying function that doesn't reinitialize the AIG produces
an extension of its input, and this relation implies many useful things.</p>

<p>In particular, any ID of the original aignet is an ID of the new aignet, and
the node of that ID (and its entire suffix) is the same in both aignets.  This
implies, for example, that the evaluations of nodes existing in the first are
the same as their evaluations in the second.</p>"

  (or (node-list-equiv old new)
      (and (consp new)
           (aignet-extension-p (cdr new) old)))
  ///
  (fty::deffixequiv aignet-extension-p)

  (defthm node-count-when-aignet-extension
    (implies (aignet-extension-p y x)
             (<= (node-count x) (node-count y)))
    :rule-classes ((:linear :trigger-terms ((node-count x)))))

  (defthm stype-count-when-aignet-extension
    (implies (aignet-extension-p y x)
             (<= (stype-count k x) (stype-count k y)))
    :rule-classes ((:linear :trigger-terms ((stype-count k x)))))

  (defthm node-count-cdr-when-aignet-extension
    (implies (and (aignet-extension-p y x)
                  (or (consp x) (consp y)))
             (< (node-count (cdr x)) (node-count y)))
    :rule-classes ((:linear :trigger-terms
                    ((node-count (cdr x))))))

  (defthm stype-count-cdr-when-aignet-extension-p
    (implies (and (aignet-extension-p y x)
                  (equal type (stype (car x)))
                  (or (not (equal (stype-fix type) (const-stype)))
                      (consp x)))
             (< (stype-count type (cdr x))
                (stype-count type y)))
    :rule-classes ((:linear :trigger-terms
                    ((stype-count type (cdr x))))))

  ;; (defcong list-equiv equal (aignet-extension-p y x) 1)
  ;; (defcong list-equiv equal (aignet-extension-p y x) 2)

  (defthmd aignet-extension-p-transitive
    (implies (and (aignet-extension-p x y)
                  (aignet-extension-p y z))
             (aignet-extension-p x z))
    :rule-classes ((:rewrite :match-free :all)))

  ;; (defthm node-count-aignet-extension-p-of-cdr
  ;;   (implies (and (aignet-extension-p (cdr y) x)
  ;;                 (consp y))
  ;;            (< (node-count x) (node-count y)))
  ;;   :hints (("goal" :induct (list-equiv x y))))
  ;; (defthm node-count-aignet-extension-p-of-cdr-not-equal
  ;;   (implies (and (aignet-extension-p (cdr y) x)
  ;;                 (consp y))
  ;;            (not (equal (node-count x) (node-count y))))
  ;;   :hints (("goal" :use node-count-aignet-extension-p-of-cdr
  ;;            :in-theory (disable node-count-aignet-extension-p-of-cdr))))
  ;; (defthm stype-count-aignet-extension-p-of-cdr
  ;;   (implies (and (aignet-extension-p (cdr y) x)
  ;;                 (consp y)
  ;;                 (equal (car y) k))
  ;;            (< (stype-count k x) (stype-count k y)))
  ;;   :hints (("goal" :induct (list-equiv x y))))
  ;; (defthm stype-count-aignet-extension-p-of-cdr-not-equal
  ;;   (implies (and (aignet-extension-p (cdr y) x)
  ;;                 (consp y)
  ;;                 (equal (car y) k))
  ;;            (not (equal (stype-count k x) (stype-count k y))))
  ;;   :hints (("goal" :use stype-count-aignet-extension-p-of-cdr
  ;;            :in-theory (disable stype-count-aignet-extension-p-of-cdr))))
  (defthm aignet-extension-p-self
    (aignet-extension-p x x))

  (defthm aignet-extension-p-cons
    (aignet-extension-p (cons x y) y))

  (defthm aignet-extension-p-cons-more
    (implies (aignet-extension-p y z)
             (aignet-extension-p (cons x y) z)))

  (defthm aignet-extension-p-cdr
    (implies (and (aignet-extension-p y z)
                  (consp z))
             (aignet-extension-p y (cdr z)))))

(defsection aignet-extension-bind-inverse
  :parents (aignet-extension-p)
  :short "Find an appropriate free variable binding that is an aignet-extension of a bound variable."
  :long "<p>An example rule using this utility:</p>
@({
 (defthm lookup-id-in-extension-inverse
     (implies (and (aignet-extension-bind-inverse :orig orig :new new)
                   (<= (nfix id) (node-count orig)))
              (equal (lookup-id id orig)
                     (lookup-id id new))))
 })

<p>Suppose this rule matches on the term @('(lookup-id id (lookup-reg->nxst n
aignet))').  Therefore, @('orig') is bound to @('(lookup-reg->nxst n aignet)').
The invocation of @('aignet-extension-bind-inverse') knows that the second
argument of @('lookup-reg->nxst') is an aignet that is (likely) an extension of
the lookup (because the lookup finds some suffix of that argument).  So it
binds @('new') to @('aignet'), in this case.  Thus, this rule can be used
instead of a whole series of rules about individual functions that look up some
suffix of an aignet, such as:</p>
@({
     (implies (<= (nfix id) (node-count (lookup-reg->nxst n aignet))))
              (equal (lookup-id id (lookup-reg->nxst n aignet))
                     (lookup-id id aignet)))

     (implies (<= (nfix id) (node-count (lookup-stype n stype aignet))))
              (equal (lookup-id id (lookup-stype n stype aignet))
                     (lookup-id id aignet)))
 })
<p>etc.</p>

<p>See also @(see aignet-extension-binding) for a similar macro that finds a
binding for a suffix aignet from a term giving some extension.</p>"
  ;; Table aignet-extension-bind-inverse, holding the various functions that look
  ;; up suffixes of the aignet -- such as lookup-id, lookup-stype,
  ;; lookup-reg->nxst.

  ;; Each entry is a key just bound to T, and the key is a term where the
  ;; variable NEW is in the position of the new aignet.
  (table aignet-lookup-fns
         nil
         '(((cdr new) . new)
           ((lookup-id n new) . new)
           ((lookup-reg->nxst n new) . new)
           ((lookup-stype n stype new) . new)
           ((find-max-fanin new) . new))
         :clear)

  (defmacro add-aignet-lookup-fn (term subst)
    `(table aignet-lookup-fns ',term ',subst))

  (defun aignet-extension-bind-scan-lookups (term var table)
    (Declare (Xargs :mode :program))
    (b* (((when (atom table)) nil)
         ((mv ok subst) (acl2::simple-one-way-unify
                         (caar table) term nil))
         ((unless ok)
          (aignet-extension-bind-scan-lookups term var (cdr table)))
         (new (acl2::substitute-into-term (cdar table) subst)))
      `((,var . ,new))))


  (defun aignet-extension-bind-inverse-fn (x var mfc state)
    (declare (xargs :mode :program
                    :stobjs state)
             (ignorable mfc))
    (aignet-extension-bind-scan-lookups
     x var (table-alist 'aignet-lookup-fns (w state))))

  (defmacro aignet-extension-bind-inverse (&key (new 'new)
                                                (orig 'orig))
    `(and (bind-free (aignet-extension-bind-inverse-fn
                      ,orig ',new mfc state)
                     (,new))
          (aignet-extension-p ,new ,orig)))

  

  (defthm node-count-when-aignet-extension-bind-inverse
    (implies (aignet-extension-bind-inverse :orig x :new y)
             (<= (node-count x) (node-count y)))
    :rule-classes ((:linear :trigger-terms ((node-count x)))))

  (defthm stype-count-when-aignet-extension-bind-inverse
    (implies (aignet-extension-bind-inverse :orig x :new y)
             (<= (stype-count k x) (stype-count k y)))
    :rule-classes ((:linear :trigger-terms ((stype-count k x)))))

  (defthm node-count-cdr-when-aignet-extension-inverse
    (implies (and (aignet-extension-bind-inverse :orig x :new y)
                  (or (consp x) (consp y)))
             (< (node-count (cdr x)) (node-count y)))
    :rule-classes ((:linear :trigger-terms
                    ((node-count (cdr x))))))

  (defthm stype-count-cdr-when-aignet-extension-inverse
    (implies (and (aignet-extension-bind-inverse :orig x :new y)
                  (equal type (stype (car x)))
                  (or (not (equal (stype-fix type) (const-stype)))
                      (consp x)))
             (< (stype-count type (cdr x))
                (stype-count type y)))
    :rule-classes ((:linear :trigger-terms
                    ((stype-count type (cdr x)))))))


(defsection aignet-extension-binding
  :parents (aignet-extension-p)
  :short "A strategy for making use of @(see aignet-extension-p) in rewrite rules."

  :long "<p>Rewrite rules using @(see aignet-extension-p) are a little odd.
For example, suppose we want a rewrite rule just based on the definition,
e.g.,</p>

@({
    (implies (and (aignet-extension-p new-aignet orig-aignet)
                  (aignet-idp id orig-aignet))
             (equal (lookup-id id new-aignet)
                    (lookup-id id orig-aignet)))
})

<p>This isn't a very good rewrite rule because it has to match the free
variable @('orig-aignet').  However, we can make it much better with a @(see
bind-free) strategy.  We'll check the syntax of new-aignet to see if it is a
call of a aignet-updating function.  Then, we'll use the @('aignet') input of
that function as the binding for @('orig-aignet') @('aignet-extension-binding')
is a macro that implements this binding strategy.  In this case, it can be used
as follows:</p>

@({
 (implies (and (aignet-extension-binding :new new-aignet :orig orig-aignet)
               (aignet-idp id orig-aignet))
          (equal (lookup-id id new-aignet)
                 (lookup-id id orig-aignet)))
 })

<p>For a given invocation of @('aignet-extension-binding'), it is assumed that
the @('new') argument is a currently bound variable and the @('orig') argument
is a variable that needs a binding.</p>

<p>See also @(see aignet-extension-bind-inverse) for a similar macro that
instead binds a new aignet given an invocation of some function that finds a
suffix.</p>"

  (defun simple-search-type-alist (term typ type-alist unify-subst)
    (declare (xargs :mode :program))
    (cond ((endp type-alist)
           (mv nil unify-subst))
          ((acl2::ts-subsetp (cadr (car type-alist)) typ)
           (mv-let (ans unify-subst)
             (acl2::one-way-unify1 term (car (car type-alist)) unify-subst)
             (if ans
                 (mv t unify-subst)
               ;; note: one-way-unify1 is a no-change-loser so unify-subst is
               ;; unchanged below
               (simple-search-type-alist term typ (cdr type-alist)
                                         unify-subst))))
          (t (simple-search-type-alist term typ (cdr type-alist) unify-subst))))


  ;; Note: We used to iterate find-prev-stobj-binding so that we could take the
  ;; term, e.g., (aignet-add-in (aignet-add-in aignet)) and find aignet,
  ;; instead of just the inner (aignet-add-in aignet).  But I think this is
  ;; generally counterproductive to our rewriting strategy and we never used
  ;; that option (the :iters keyword for aignet-extension-binding) in our
  ;; codebase so I am now removing it.

  ;; Additional possible strategic thing: keep aignet-modifying functions that
  ;; don't produce an extension in a table and don't bind their inputs.
  


  (defmacro aignet-extension-binding (&key (new 'new)
                                           (orig 'orig))
    `(and (bind-free (acl2::prev-stobj-binding ,new ',orig mfc state))
          ;; do we need this syntaxp check?
          ;; (syntaxp (not (subtermp ,new ,orig)))
          (aignet-extension-p ,new ,orig)))

  (defthm aignet-extension-p-transitive-rw
    (implies (and (aignet-extension-binding :new aignet3 :orig aignet2)
                  (aignet-extension-p aignet2 aignet1))
             (aignet-extension-p aignet3 aignet1))
    :hints(("Goal" :in-theory (enable aignet-extension-p-transitive))))




  (defthm aignet-extension-implies-node-count-gte
    (implies (aignet-extension-binding)
             (<= (node-count orig) (node-count new)))
    :rule-classes ((:linear :trigger-terms ((node-count new)))))

  (defthm aignet-extension-implies-stype-count-gte
    (implies (aignet-extension-binding)
             (<= (stype-count stype orig)
                 (stype-count stype new)))
    :rule-classes ((:linear :trigger-terms ((stype-count stype new)))))

  (defthmd aignet-extension-p-implies-consp
    (implies (and (aignet-extension-binding)
                  (consp orig))
             (consp new))
    :hints(("Goal" :in-theory (enable aignet-extension-p)))))





(define lookup-id ((id     natp)
                   (aignet node-listp))
  :returns (suffix node-listp
                   "Tail of the aignet up to (and including) the @('id')th
                    @(see node).")
  :short "Core function for looking up an AIG node in the logical AIG network
  by its ID."
  (cond ((endp aignet) (node-list-fix aignet))
        ((equal (node-count aignet) (lnfix id))
         (node-list-fix aignet))
        (t (lookup-id id (cdr aignet))))
  ///
  (fty::deffixequiv lookup-id)
  ;; (defcong nat-equiv equal (lookup-id id aignet) 1)
  (defthm node-count-of-lookup-id
    (implies (<= (nfix n) (node-count aignet))
             (equal (node-count (lookup-id n aignet))
                    (nfix n))))
  (defthm node-count-of-cdr-lookup-id
    (implies (consp (lookup-id n aignet))
             (equal (node-count (cdr (lookup-id n aignet)))
                    (+ -1 (nfix n)))))
  (defthm lookup-id-0
    (equal (lookup-id 0 aignet) nil))

  (defthmd lookup-id-in-bounds
    (iff (consp (lookup-id n aignet))
         (and (< 0 (nfix n))
              (<= (nfix n) (node-count aignet)))))

  (defthm lookup-id-in-bounds-when-positive
    (implies (posp n)
             (iff (consp (lookup-id n aignet))
                  (<= (nfix n) (node-count aignet)))))

  (defthm lookup-id-aignet-extension-p
    (aignet-extension-p aignet (lookup-id id aignet))
    :hints(("Goal" :in-theory (enable aignet-extension-p))))
  ;; (defcong list-equiv list-equiv (lookup-id id aignet) 2)
  ;; (defcong list-equiv iff (lookup-id id aignet) 2)
  (defthm lookup-id-in-extension
    (implies (and (aignet-extension-p new orig)
                  (<= (nfix id) (node-count orig)))
             (equal (lookup-id id new)
                    (lookup-id id orig)))
    :hints(("Goal" :in-theory (enable aignet-extension-p))))
  (defthm lookup-id-in-extension-inverse
    (implies (and (aignet-extension-bind-inverse)
                  (<= (nfix id) (node-count orig)))
             (equal (lookup-id id orig)
                    (lookup-id id new)))
    :hints(("Goal" :in-theory (enable aignet-extension-p))))
  (defthm node-count-of-cdr-lookup-bound-by-id
    (implies (consp (lookup-id id aignet))
             (< (node-count (cdr (lookup-id id aignet)))
                (nfix id)))
    :rule-classes :linear)
  (defthm lookup-id-of-node-count-of-suffix
    (implies (and (aignet-extension-p y x)
                  (consp x))
             (equal (lookup-id (node-count x) y)
                    (node-list-fix x)))
    :hints(("Goal" :in-theory (enable lookup-id))))
  (defthm true-listp-lookup-id-of-node-listp
    (implies (node-listp aignet)
             (true-listp (lookup-id id aignet)))
    :rule-classes :type-prescription)
  (defthm lookup-id-of-nil
    (equal (lookup-id x nil) nil))
  (defthm lookup-id-of-cons
    (equal (lookup-id id (cons node rest))
           (if (equal (nfix id) (+ 1 (node-count rest)))
               (cons (node-fix node) (node-list-fix rest))
             (lookup-id id rest))))
  (defthm lookup-id-of-node-count
    (equal (lookup-id (node-count x) x)
           (node-list-fix x)))
  (defthm node-count-of-lookup-id-when-consp
    (implies (consp (lookup-id id aignet))
             (equal (node-count (lookup-id id aignet))
                    id)))
  (defthm posp-when-consp-of-lookup-id
    (implies (consp (lookup-id id aignet))
             (posp id))
    :rule-classes :forward-chaining)

  ;; (defun check-not-known-natp (term mfc state)
  ;;   (declare (xargs :mode :program :stobjs state))
  ;;   (not (acl2::ts-subsetp (acl2::mfc-ts term mfc state)
  ;;                          acl2::*ts-non-negative-integer*)))
  (defthm lookup-id-consp-forward-to-id-bound-nfix
    (implies (and (consp (lookup-id id aignet))
                  ;; (syntaxp (check-not-known-natp term mfc state))
                  )
             (<= (nfix id) (node-count aignet)))
    :hints(("Goal" :in-theory (enable lookup-id-in-bounds)))
    :rule-classes :forward-chaining)
  (defthm lookup-id-consp-forward-to-id-bound
    (implies (and (consp (lookup-id id aignet))
                  (natp id))
             (<= id (node-count aignet)))
    :rule-classes :forward-chaining)

  (defthm lookup-id-out-of-bounds
    (implies (< (node-count aignet) (nfix id))
             (equal (lookup-id id aignet) nil))))


(define lookup-stype ((n      natp)
                      (stype  stypep)
                      (aignet node-listp))
  :returns (suffix node-listp)
  :short "Core function for looking up an input, output, or register in the
  logical AIG network by its IO number."
  :long "<p>See @(see representation) to understand IO numbers and IO
  lookups.</p>"
  (cond ((endp aignet)
         (node-list-fix aignet))
        ((and (equal (stype (car aignet)) (stype-fix stype))
              (equal (stype-count stype (cdr aignet)) (lnfix n)))
         (node-list-fix aignet))
        (t
         (lookup-stype n stype (cdr aignet))))
  ///
  ;; (defcong nat-equiv equal (lookup-stype n stype aignet) 1)
  ;; (defcong stype-equiv equal (lookup-stype n stype aignet) 2
  ;;   :hints(("Goal" :in-theory (disable stype-equiv))))
  ;; (defcong list-equiv list-equiv (lookup-stype n stype aignet) 3)
  (fty::deffixequiv lookup-stype)
  (defthm stype-count-of-lookup-stype
    (implies (< (nfix n) (stype-count stype aignet))
             (equal (stype-count stype (cdr (lookup-stype n stype aignet)))
                    (nfix n))))
  (defthm car-of-lookup-stype
    (implies (< (nfix n) (stype-count stype aignet))
             (equal (stype (car (lookup-stype n stype aignet)))
                    (stype-fix stype))))

  (defthm lookup-stype-in-bounds
    (iff (consp (lookup-stype n stype aignet))
         (< (nfix n) (stype-count stype aignet))))
  (defthm lookup-stype-aignet-extension-p
    (aignet-extension-p aignet (lookup-stype n stype aignet))
    :hints(("Goal" :in-theory (enable aignet-extension-p))))

  (defthm lookup-stype-of-stype-count
    (implies (and (aignet-extension-p new orig)
                  (equal (stype (car orig)) (stype-fix stype))
                  (not (equal (stype-fix stype) (const-stype))))
             (equal (lookup-stype (stype-count stype (cdr orig))
                                  stype
                                  new)
                    (node-list-fix orig)))
    :hints(("Goal" :in-theory (enable aignet-extension-p
                                      lookup-stype
                                      stype-count)
            :induct t)
           (and stable-under-simplificationp
                '(:cases ((< (stype-count stype (cdr new))
                             (stype-count stype orig)))))))

  (defthm lookup-stype-in-extension
    (implies (and (aignet-extension-binding)
                  (consp (lookup-stype n stype orig)))
             (equal (lookup-stype n stype new)
                    (lookup-stype n stype orig)))
    :hints(("Goal" :in-theory (enable aignet-extension-p
                                      lookup-stype-in-bounds))))

  (defthm lookup-stype-in-extension-inverse
    (implies (and (aignet-extension-bind-inverse)
                  (consp (lookup-stype n stype orig)))
             (equal (lookup-stype n stype orig)
                    (lookup-stype n stype new)))
    :hints(("Goal" :in-theory (enable aignet-extension-p))))

  (defthm stype-of-lookup-stype
    (implies (consp (lookup-stype n stype aignet))
             (equal (stype (car (lookup-stype n stype aignet)))
                    (stype-fix stype))))

  (defthmd stype-of-lookup-stype-split
    (equal (stype (car (lookup-stype n stype aignet)))
           (if (consp (lookup-stype n stype aignet))
               (stype-fix stype)
             :const)))

  (defthm aignet-extension-simplify-lookup-stype-when-counts-same
    (implies (and (aignet-extension-binding)
                  (equal (stype-count stype new)
                         (stype-count stype orig)))
             (equal (lookup-stype n stype new)
                    (lookup-stype n stype orig)))
    :hints(("Goal" :in-theory (enable aignet-extension-p
                                      lookup-stype))))

  (defthm aignet-extension-simplify-lookup-stype-inverse
    (implies (and (aignet-extension-bind-inverse)
                  (consp (lookup-stype n stype orig)))
             (equal (lookup-stype n stype orig)
                    (lookup-stype n stype new))))

  (defthm lookup-stype-out-of-bounds
    (implies (<= (stype-count stype aignet) (nfix n))
             (equal (lookup-stype n stype aignet) nil)))

  ;; (defret stype-of-lookup-stype
  ;;   (implies (stypep stype)
  ;;            (or (equal (stype (car suffix)) stype)
  ;;                (equal (stype (car suffix)) :const)))
  ;;   :rule-classes ((:forward-chaining :trigger-terms ((stype (car suffix))))))
  )


(define find-max-fanin ((aignet node-listp))
  :returns (suffix node-listp)
  :short "Finds the longest suffix whose first node is a fanin type, i.e. not a
          combinational output."
  (cond ((endp aignet) (node-list-fix aignet))
        ((not (equal (ctype (stype (car aignet))) (out-ctype)))
         (node-list-fix aignet))
        (t (find-max-fanin (cdr aignet))))
  ///
  (fty::deffixequiv find-max-fanin)

  (defthm find-max-fanin-aignet-extension-p
    (aignet-extension-p aignet (find-max-fanin aignet)))

  (defthm find-max-fanin-of-cons-fanin
    (implies (not (equal (ctype (stype node)) (out-ctype)))
             (equal (find-max-fanin (cons node aignet))
                    (cons (node-fix node)
                          (node-list-fix aignet)))))

  (defthm find-max-fanin-of-cons-output
    (implies (equal (ctype (stype node)) (out-ctype))
             (equal (find-max-fanin (cons node aignet))
                    (find-max-fanin aignet))))
  
  (defthm node-count-of-find-max-fanin
    (<= (node-count (find-max-fanin aignet))
        (node-count aignet))
    :rule-classes :linear)

  (defthm node-count-of-find-max-fanin-of-extension-inverse
    (implies (aignet-extension-bind-inverse)
             (<= (node-count (find-max-fanin orig))
                 (node-count (find-max-fanin new))))
    :hints(("Goal" :in-theory (enable find-max-fanin aignet-extension-p)))
    :rule-classes ((:linear :trigger-terms ((node-count (find-max-fanin orig))))))

  (defthm node-count-of-find-max-fanin-of-extension
    (implies (aignet-extension-binding)
             (<= (node-count (find-max-fanin orig))
                 (node-count (find-max-fanin new))))
    :hints(("Goal" :in-theory (enable find-max-fanin aignet-extension-p)))
    :rule-classes ((:linear :trigger-terms ((node-count (find-max-fanin new))))))

  (defthm node-count-of-suffix-less-than-max-fanin-when-not-output
    (implies (and (syntaxp (not (and (consp orig) (eq (car orig) 'find-max-fanin))))
                  (aignet-extension-bind-inverse)
                  (not (equal (ctype (stype (car orig))) :output)))
             (<= (node-count orig) (node-count (find-max-fanin new))))
    :rule-classes ((:linear :trigger-terms ((node-count orig)))))

  (defthmd id-less-than-max-fanin-by-stype
    (implies (and (not (equal (stype (car (lookup-id id aignet))) :po))
                  (not (equal (stype (car (lookup-id id aignet))) :nxst))
                  ;; this hyp: just because if id is out of bounds, we get const type.
                  (not (equal (stype (car (lookup-id id aignet))) :const))
                  (natp id))
             (<= id (node-count (find-max-fanin aignet))))
    :hints(("Goal" :in-theory (enable find-max-fanin lookup-id)))
    :rule-classes ((:forward-chaining :trigger-terms ((stype (car (lookup-id id aignet)))))))

  (defthmd id-less-than-max-fanin-by-ctype
    (implies (and (not (equal (ctype (stype (car (lookup-id id aignet)))) :output))
                  ;; this hyp: just because if id is out of bounds, we get const type.
                  (not (equal (ctype (stype (car (lookup-id id aignet)))) :const))
                  (natp id))
             (<= id (node-count (find-max-fanin aignet))))
    :hints(("Goal" :in-theory (enable find-max-fanin lookup-id)))
    :rule-classes ((:forward-chaining :trigger-terms ((ctype (stype (car (lookup-id id aignet)))))))))



(define lookup-reg->nxst ((reg-id natp "Node ID (not the register number) for this register.")
                          (aignet node-listp))
  :returns (suffix node-listp)
  :short "Look up the next-state node that corresponds to particular register
  node."
  :long "<p><b>Note</b>: This is different from the other lookups: it's by ID
  of the corresponding RO node, not IO number.  I think the asymmetry is worth
  it though.</p>"

  (cond ((endp aignet) nil)
        ((and (equal (stype (car aignet)) (nxst-stype))
              (b* ((ro (nxst-node->reg (car aignet))))
                (and (nat-equiv reg-id ro)
                     (< ro (node-count aignet))
                     ;; this check ensures that if we look for the nxst of a
                     ;; nonexistent reg we won't find one
                     (equal (stype (car (lookup-id ro aignet)))
                            (reg-stype)))))
         (node-list-fix aignet))
        ((and (equal (stype (car aignet)) (reg-stype))
              (nat-equiv (node-count aignet) reg-id))
         (node-list-fix aignet))
        (t (lookup-reg->nxst reg-id (cdr aignet))))
  ///
  (fty::deffixequiv lookup-reg->nxst
    :hints (("goal" :induct (lookup-reg->nxst reg-id aignet)
             :expand ((:free (reg-id) (lookup-reg->nxst reg-id aignet))
                      (lookup-reg->nxst reg-id (node-list-fix aignet))))))

  (defthm car-of-lookup-reg->nxst-when-nxst
    (implies (and (consp (lookup-reg->nxst reg-id aignet))
                  ;; (not (equal (stype (car (lookup-reg->nxst reg-id aignet)))
                  ;;             (reg-stype)))
                  (not (equal (node-count (lookup-reg->nxst reg-id aignet))
                              (nfix reg-id))))
             (and (equal (stype (car (lookup-reg->nxst reg-id aignet))) (nxst-stype))
                  (equal (nxst-node->reg (car (lookup-reg->nxst reg-id aignet)))
                         (nfix reg-id)))))

  ;; (defthm lookup-reg->nxst-count-when-reg
  ;;   (implies (equal (stype (car (lookup-reg->nxst reg-id aignet)))
  ;;                   (reg-stype))
  ;;            (equal (node-count (lookup-reg->nxst reg-id aignet))
  ;;                   (nfix reg-id))))

  (defthm aignet-extension-p-of-lookup-reg->nxst
    (aignet-extension-p aignet (lookup-reg->nxst reg-id aignet))
    :hints(("Goal" :in-theory (enable aignet-extension-p))))

  ;; (defthm stype-of-lookup-reg->nxst
  ;;   (implies (consp (lookup-reg->nxst n aignet))
  ;;            (equal (stype (car (lookup-reg->nxst n aignet)))
  ;;                   (nxst-stype))))

  (defthm node-count-of-lookup-reg->nxst
    (implies (consp (lookup-reg->nxst n aignet))
             (<= (nfix n) (node-count (lookup-reg->nxst n aignet))))
    :rule-classes :linear)

  (defthm lookup-reg->nxst-out-of-bounds
    (implies (< (node-count aignet) (nfix id))
             (equal (lookup-reg->nxst id aignet) nil)))

  (defthm lookup-reg->nxst-of-0
    (equal (lookup-reg->nxst 0 aignet) nil)
    :hints(("Goal" :in-theory (enable lookup-reg->nxst))))

  (defret stypes-of-lookup-reg->nxst
    (or (equal (stype (car suffix)) :nxst)
        (equal (stype (car suffix)) :reg)
        (equal (stype (car suffix)) :const))
    :rule-classes ((:forward-chaining :trigger-terms ((stype (car suffix)))))))


;; (defthm node-by-stype-types
;;   (implies (node-p node)
;;            (and (equal (equal (ctype (stype node)) (const-type))
;;                        (const-node-p node))
;;                 (equal (equal (ctype (stype node)) (gate-type))
;;                        (gate-node-p node))
;;                 (implies (equal (ctype (stype node)) (in-type))
;;                          (equal (equal (regp (stype node)) 1)
;;                                 (reg-node-p node)))
;;                 (implies (not (reg-node-p node))
;;                          (equal (equal (ctype (stype node)) (in-type))
;;                                 (pi-node-p node)))
;;                 (implies (equal (ctype (stype node)) (out-type))
;;                          (equal (equal (regp (stype node)) 1)
;;                                 (nxst-node-p node)))
;;                 (implies (not (nxst-node-p node))
;;                          (equal (equal (ctype (stype node)) (out-type))
;;                                 (po-node-p node)))))
;;   :hints(("Goal" :in-theory (enable node-p))))


(define aignet-idp ((id     natp)
                    (aignet node-listp))
  :short "Check whether a node ID is in bounds for this network."
  (<= (lnfix id) (node-count aignet))
  ///
  (fty::deffixequiv aignet-idp)
  (defthm bound-when-aignet-idp
    (implies (aignet-idp id aignet)
             (<= (nfix id) (node-count aignet))))
  (local (defthm <=-when-<-+-1
           (implies (and (< x (+ 1 y))
                         (integerp x) (integerp y))
                    (<= x y))))
  (defthm aignet-idp-in-extension
    (implies (and (aignet-extension-p aignet2 aignet)
                  (aignet-idp id aignet))
             (aignet-idp id aignet2)))

  (defthm lookup-id-implies-aignet-idp
    (implies (consp (lookup-id id aignet))
             (aignet-idp id aignet))
    :hints(("Goal" :in-theory (enable lookup-id))))

  (defthm aignet-idp-of-node-count-of-extension
    (implies (aignet-extension-p aignet prev)
             (aignet-idp (node-count prev) aignet))
    :hints(("Goal" :in-theory (enable aignet-extension-p))))

  (defthm aignet-idp-of-0
    (aignet-idp 0 aignet)
    :hints(("Goal" :in-theory (enable aignet-idp))))

  ;; already has inverse
  (defthm aignet-extension-simplify-lookup-id
    (implies (and (aignet-extension-binding)
                  (aignet-idp id orig))
             (equal (lookup-id id new)
                    (lookup-id id orig))))

  (defthm aignet-extension-simplify-aignet-idp
    (implies (and (aignet-extension-binding)
                  (aignet-idp id orig))
             (aignet-idp id new))))


(define aignet-litp ((lit    litp)
                     (aignet node-listp))
  :short "Check if a @(see literal) is valid for use as a fanin to another node."
  :long "<p>We return true only if the ID for the literal is in bounds for the
  network and refers to a node of acceptable type.  In particular, the literal
  may not refer to any combinational output node, i.e., it may not be a primary
  output and may also not be a next-state (register input) node.</p>"
  (and (<= (lit-id lit)
           (node-count aignet))
       (not (equal (node->type (car (lookup-id (lit-id lit) aignet)))
                   (out-type))))
  ///
  (fty::deffixequiv aignet-litp)
  (defthm lit-id-bound-when-aignet-litp
    (implies (aignet-litp lit aignet)
             (<= (lit-id lit) (node-count aignet)))
    :rule-classes ((:linear :trigger-terms ((lit-id lit)))))
  (local (defthm <=-when-<-+-1
           (implies (and (< x (+ 1 y))
                         (integerp x) (integerp y))
                    (<= x y))))
  (defthm aignet-litp-in-extension
    (implies (and (aignet-extension-p new orig)
                  (aignet-litp lit orig))
             (aignet-litp lit new)))
  (defcong lit-equiv equal (aignet-litp lit aignet) 1)
  (defcong list-equiv equal (aignet-litp lit aignet) 2)

  (defthm aignet-idp-when-aignet-litp
    (implies (aignet-litp lit aignet)
             (aignet-idp (lit-id lit) aignet))
    :hints(("Goal" :in-theory (enable aignet-idp))))

  (defthm aignet-litp-of-0-and-1
    (and (aignet-litp 0 aignet)
         (aignet-litp 1 aignet)))

  (defthm aignet-litp-of-mk-lit-lit-id
    (equal (aignet-litp (mk-lit (lit-id lit) neg) aignet)
           (aignet-litp lit aignet)))

  (defthm aignet-litp-of-mk-lit-0
    (aignet-litp (mk-lit 0 neg) aignet))
  
  (defthm aignet-litp-implies-id-lte-max-fanin
    (implies (aignet-litp lit aignet)
             (<= (lit-id lit)
                 (node-count (find-max-fanin aignet))))
    :hints(("Goal" :in-theory (enable aignet-litp find-max-fanin)))
    :rule-classes :forward-chaining)

  (defthm aignet-extension-simplify-aignet-litp
    (implies (and (aignet-extension-binding)
                  (aignet-litp lit orig))
             (aignet-litp lit new)))

  (defthm aignet-litp-of-lit-negate
    (equal (aignet-litp (lit-negate x) aignet)
           (aignet-litp x aignet))
    :hints(("Goal" :in-theory (enable lit-negate))))

  (defthm aignet-litp-of-lit-negate-cond
    (equal (aignet-litp (lit-negate-cond x neg) aignet)
           (aignet-litp x aignet))
    :hints(("Goal" :in-theory (enable lit-negate-cond))))

  (defthm not-output-when-aignet-litp
    (implies (aignet-litp lit aignet)
             (and (not (equal (ctype (stype (car (lookup-id (lit-id lit) aignet)))) :output))
                  (not (equal (stype (car (lookup-id (lit-id lit) aignet))) :po))
                  (not (equal (stype (car (lookup-id (lit-id lit) aignet))) :nxst))))))


(define aignet-nodes-ok ((aignet node-listp))
  :short "Basic well-formedness constraints for the AIG network."
  :long "<p>We require that:</p>

  <ul>

  <li>Each fanin is a well-formed in the sense of @(see aignet-litp), i.e., it
  exists somewhere ``earlier'' in the network (in the suffix of the list) so
  that the network is topologically ordered, and it is not a combinational
  output node.</li>

  <li>Each next-state (register input) node must refer to a valid register that
  exists somewhere earlier in the network.</li>

  </ul>"

  (if (endp aignet)
      t
    (and (aignet-case
           (node->type (car aignet))
           (node->regp (car aignet))
           :ci   t
           :po   (aignet-litp (co-node->fanin (car aignet))
                              (cdr aignet))
           :nxst   (and (aignet-litp (co-node->fanin (car aignet))
                                     (cdr aignet))
                        (aignet-idp (nxst-node->reg (car aignet))
                                    (cdr aignet))
                        (equal (car (lookup-id (nxst-node->reg (car aignet)) (cdr aignet)))
                               (reg-node)))
           :gate (let ((f0 (gate-node->fanin0 (car aignet)))
                       (f1 (gate-node->fanin1 (car aignet))))
                   (and (aignet-litp f0 (cdr aignet))
                        (aignet-litp f1 (cdr aignet)))))
         (aignet-nodes-ok (cdr aignet))))
  ///
  (fty::deffixequiv aignet-nodes-ok
    :hints (("goal" :induct (aignet-nodes-ok aignet)
             :expand ((aignet-nodes-ok aignet)
                      (aignet-nodes-ok (node-list-fix aignet))))))

  (defthm proper-node-list-when-aignet-nodes-ok
    (implies (and (aignet-nodes-ok aignet)
                  (node-listp aignet))
             (proper-node-listp aignet)))

  (defthm co-fanin-ordered-when-aignet-nodes-ok
    (implies (and (aignet-nodes-ok aignet)
                  (equal (node->type (car (lookup-id id aignet)))
                         (out-type)))
             (< (lit-id (co-node->fanin
                         (car (lookup-id id aignet))))
                (nfix id)))
    :hints (("goal" :induct (lookup-id id aignet)
             :in-theory (enable lookup-id)))
    :rule-classes (:rewrite
                   (:linear :trigger-terms
                    ((lit-id (co-node->fanin
                              (car (lookup-id id aignet))))))))
  (defthm nxst-reg-ordered-when-aignet-nodes-ok
    (implies (and (aignet-nodes-ok aignet)
                  (equal (node->type (car (lookup-id id aignet)))
                         (out-type))
                  (equal (node->regp (car (lookup-id id aignet)))
                         1))
             (< (nxst-node->reg (car (lookup-id id aignet)))
                (nfix id)))
    :hints (("goal" :induct (lookup-id id aignet)
             :in-theory (e/d (lookup-id aignet-idp)
                             ((force)))))
    :rule-classes (:rewrite
                   (:linear :trigger-terms
                    ((nxst-node->reg
                      (car (lookup-id id aignet)))))))
  (defthm nxst-reg-aignet-idp-when-aignet-nodes-ok
    (implies (and (aignet-nodes-ok aignet)
                  (equal (node->type (car (lookup-id id aignet)))
                         (out-type))
                  (equal (node->regp (car (lookup-id id aignet)))
                         1))
             (aignet-idp (nxst-node->reg (car (lookup-id id aignet)))
                         (cdr (lookup-id id aignet))))
    :hints (("goal" :induct (lookup-id id aignet)
             :in-theory (e/d (lookup-id aignet-idp)
                             ((force))))))
  (defthm gate-fanin0-ordered-when-aignet-nodes-ok
    (implies (and (aignet-nodes-ok aignet)
                  (equal (node->type (car (lookup-id id aignet)))
                         (gate-type)))
             (< (lit-id (gate-node->fanin0
                         (car (lookup-id id aignet))))
                (nfix id)))
    :hints (("goal" :induct (lookup-id id aignet)
             :in-theory (enable lookup-id)))
    :rule-classes (:rewrite
                   (:linear :trigger-terms
                    ((lit-id (gate-node->fanin0
                              (car (lookup-id id aignet))))))))
  (defthm gate-fanin1-ordered-when-aignet-nodes-ok
    (implies (and (aignet-nodes-ok aignet)
                  (equal (node->type (car (lookup-id id aignet))) (gate-type)))
             (< (lit-id (gate-node->fanin1
                         (car (lookup-id id aignet))))
                (nfix id)))
    :hints (("goal" :induct (lookup-id id aignet)
             :in-theory (enable lookup-id)))
    :rule-classes (:rewrite
                   (:linear :trigger-terms
                    ((lit-id (gate-node->fanin1
                              (car (lookup-id id aignet))))))))
  (local (defthm aignet-litp-in-extension-bind
           (implies (and (aignet-litp lit orig)
                         (aignet-extension-p new orig))
                    (aignet-litp lit new))))
  (defthm co-fanin-aignet-litp-when-aignet-nodes-ok
    (implies (and (aignet-nodes-ok aignet)
                  (equal (node->type (car (lookup-id id aignet))) (out-type))
                  (aignet-extension-p aignet2 (cdr (lookup-id id aignet))))
             (aignet-litp (co-node->fanin
                           (car (lookup-id id aignet)))
                          aignet2))
    :hints (("goal" :induct (lookup-id id aignet)
             :in-theory (enable lookup-id)
             :expand ((aignet-nodes-ok aignet)))))
  (defthm gate-fanin0-aignet-litp-when-aignet-nodes-ok
    (implies (and (aignet-nodes-ok aignet)
                  (equal (node->type (car (lookup-id id aignet))) (gate-type))
                  (aignet-extension-p aignet2 (cdr (lookup-id id aignet))))
             (aignet-litp (gate-node->fanin0
                           (car (lookup-id id aignet)))
                          aignet2))
    :hints (("goal" :induct (lookup-id id aignet)
             :in-theory (enable lookup-id)
             :expand ((aignet-nodes-ok aignet)))))
  (defthm gate-fanin1-aignet-litp-when-aignet-nodes-ok
    (implies (and (aignet-nodes-ok aignet)
                  (equal (node->type (car (lookup-id id aignet))) (gate-type))
                  (aignet-extension-p aignet2 (cdr (lookup-id id aignet))))
             (aignet-litp (gate-node->fanin1
                           (car (lookup-id id aignet)))
                          aignet2))
    :hints (("goal" :induct (lookup-id id aignet)
             :in-theory (enable lookup-id)
             :expand ((aignet-nodes-ok aignet)))))

  (defthm aignet-nodes-ok-of-extension
    (implies (and (aignet-extension-p y x)
                  (aignet-nodes-ok y))
             (aignet-nodes-ok x))
    :hints(("Goal" :in-theory (enable aignet-extension-p aignet-nodes-ok)
            :induct (aignet-nodes-ok y))))

  (defthm aignet-nodes-ok-of-suffix-inverse
    (implies (and (aignet-extension-bind-inverse :orig x :new y)
                  (aignet-nodes-ok y))
             (aignet-nodes-ok x))
    :hints(("Goal" :in-theory (enable aignet-extension-p aignet-nodes-ok)
            :induct (aignet-nodes-ok y))))

  (defthm id-less-than-max-fanin-when-aignet-litp
    (implies (aignet-litp lit aignet)
             (<= (lit-id lit) (node-count (find-max-fanin aignet))))
    :hints(("Goal" :in-theory (enable aignet-litp find-max-fanin)))
    :rule-classes nil)

  (defthm gate-fanin0-less-than-max-fanin
    (let ((suffix (lookup-id n aignet)))
      (implies (and (aignet-nodes-ok aignet)
                    (equal (node->type (car suffix)) (gate-type)))
               (<= (lit-id (gate-node->fanin0 (car suffix)))
                   (node-count (find-max-fanin aignet)))))
    :hints (("goal" :use ((:instance id-less-than-max-fanin-when-aignet-litp
                           (lit (gate-node->fanin0 (car (lookup-id n aignet))))))))
    :rule-classes :linear)

  (defthm gate-fanin1-less-than-max-fanin
    (let ((suffix (lookup-id n aignet)))
      (implies (and (aignet-nodes-ok aignet)
                    (equal (node->type (car suffix)) (gate-type)))
               (<= (lit-id (gate-node->fanin1 (car suffix)))
                   (node-count (find-max-fanin aignet)))))
    :hints (("goal" :use ((:instance id-less-than-max-fanin-when-aignet-litp
                           (lit (gate-node->fanin1 (car (lookup-id n aignet))))))))
    :rule-classes :linear)

  (defthm co-fanin-less-than-max-fanin
    (let ((suffix (lookup-id n aignet)))
      (implies (and (aignet-nodes-ok aignet)
                    (equal (node->type (car suffix)) (out-type)))
               (<= (lit-id (co-node->fanin (car suffix)))
                   (node-count (find-max-fanin aignet)))))
    :hints (("goal" :use ((:instance id-less-than-max-fanin-when-aignet-litp
                           (lit (co-node->fanin (car (lookup-id n aignet))))))))
    :rule-classes :linear))



;; (defthm reg-count-aignet-extension-p-by-node->type/regp
;;   (implies (and (aignet-extension-bind-inverse :orig x :new y)
;;                 (aignet-extension-p y x)
;;                 (equal (node->type (car x)) (in-type))
;;                 (equal (node->regp (car x)) 1))
;;            (< (reg-count (cdr x)) (reg-count y)))
;;   :hints(("Goal" :in-theory (enable node->type
;;                                     node->regp)))
;;   :rule-classes ((:linear :trigger-terms
;;                   ((reg-count (cdr x))))))

;; ???
;; (local (defthm node-count-cdr-when-consp
;;          (implies (consp x)
;;                   (< (node-count (cdr x)) (node-count x)))
;;          :rule-classes :linear))


(define aignet-lit-fix ((x      litp)
                        (aignet node-listp))
  :short "@(call aignet-lit-fix) fixes the @(see literal) @('x') to be a valid
  literal for this AIG network."
  :long "<p>If @('x') is a valid literal in the sense of @(see aignet-litp), it
  is returned unchanged:</p>

  @(def aignet-lit-fix-when-aignet-litp)

  <p>Otherwise we adjust it to refer to the constant node, which is
  unconditionally valid.</p>"
  :verify-guards nil
  :measure (node-count aignet)
  :hints ('(:in-theory (enable lookup-id-in-bounds)))
  :returns (fix litp :rule-classes :type-prescription)
  (b* ((id (lit-id x))
       (look (lookup-id id aignet))
       ((unless (consp look))
        (mk-lit 0 (lit-neg x)))
       ((cons node rest) look)
       ((when (eql (node->type node) (out-type)))
        (lit-negate-cond
         (aignet-lit-fix (co-node->fanin node) rest)
         (lit-neg x))))
    (lit-fix x))
  ///
  (verify-guards aignet-lit-fix)

  (local (defthm lookup-id-in-extension-bind-inverse
           (implies (and (aignet-extension-bind-inverse :orig x :new y)
                         (< (nfix id) (node-count x)))
                    (equal (lookup-id id (cdr x))
                           (lookup-id id y)))
           :hints(("Goal" :in-theory (enable aignet-extension-p lookup-id)))))

  (local (defthm <=-minus-1-rewrite
           (implies (and (natp x) (natp y))
                    (equal (< (+ -1 y) x)
                           (not (< x y))))))

  (defthm aignet-lit-fix-id-val-linear
    (<= (lit-id (aignet-lit-fix lit aignet))
        (node-count aignet))
    :rule-classes :linear)

  (defthm aignet-litp-of-aignet-lit-fix
    (aignet-litp (aignet-lit-fix x aignet) aignet)
    :hints(("Goal"
            :induct (aignet-lit-fix x aignet))
           (and stable-under-simplificationp
                '(:in-theory (enable aignet-litp
                                     lookup-id-in-bounds)))))

  (defthm aignet-litp-of-aignet-lit-fix-extension
    (implies (aignet-extension-p new orig)
             (aignet-litp (aignet-lit-fix x orig) new)))

  (defthm aignet-lit-fix-when-aignet-litp
    (implies (aignet-litp lit aignet)
             (equal (aignet-lit-fix lit aignet)
                    (lit-fix lit)))
    :hints(("Goal" :in-theory (enable aignet-litp
                                      lookup-id-in-bounds
                                      ;; aignet::equal-of-mk-lit
                                      ))))

  ;; (defcong lit-equiv equal (aignet-lit-fix lit aignet) 1)
  (local (defun-nx aignet-lit-fix-ind2a (x aignet aignet2)
           (declare (xargs :measure (node-count aignet)
                           :hints(("Goal" :in-theory (enable lookup-id-in-bounds)))))
           (b* ((id (lit-id x))
                (look (lookup-id id aignet))
                ((unless look)
                 (mk-lit 0 (lit-neg x)))
                ((cons node rest) look)
                (rest2 (cdr (lookup-id id aignet2)))
                ((when (eql (node->type node) (out-type)))
                 (aignet-lit-fix-ind2a (co-node->fanin node) rest rest2)))
             aignet2)))
  ;; (defcong list-equiv equal (aignet-lit-fix lit aignet) 2
  ;;   :hints (("goal" :induct (aignet-lit-fix-ind2a lit aignet acl2::aignet-equiv)
  ;;            :expand ((:free (aignet)
  ;;                      (aignet-lit-fix lit aignet))))))

  (defthm aignet-lit-fix-id-lte-max-fanin
    (<= (lit-id (aignet-lit-fix lit aignet))
        (node-count (find-max-fanin aignet)))
    :hints(("Goal" :use ((:instance aignet-litp-implies-id-lte-max-fanin
                          (lit (aignet-lit-fix lit aignet))))
            :in-theory (disable aignet-litp-implies-id-lte-max-fanin)))
    :rule-classes :linear)

  (local (defthm b-xor-b-not
           (equal (b-xor (b-not x) y)
                  (b-not (b-xor x y)))
           :hints(("Goal" :in-theory (enable b-xor)))))
  (local (defthm b-xor-assoc
           (equal (b-xor (b-xor x y) z)
                  (b-xor x (b-xor y z)))
           :hints(("Goal" :in-theory (enable b-xor)))))

  (defthm aignet-lit-fix-of-lit-negate
    (equal (aignet-lit-fix (lit-negate x) aignet)
           (lit-negate (aignet-lit-fix x aignet)))
    :hints(("Goal" :in-theory (enable lit-negate lit-negate-cond))))

  (defthm aignet-lit-fix-of-lit-negate-cond
    (equal (aignet-lit-fix (lit-negate-cond x neg) aignet)
           (lit-negate-cond (aignet-lit-fix x aignet) neg))
    :hints(("Goal" :in-theory (enable lit-negate-cond)))))


(define aignet-id-fix ((x natp) aignet)
  :returns (id natp :rule-classes :type-prescription)
  :short "@(call aignet-id-fix) fixes the id @('x') to be in bounds for this
  AIG network."
  :long "<p>If @('x') is in bounds then we return it unchanged.  If it is out
  of bounds, we coerce it to refer to the implicit constant node, which is
  valid in any network.</p>"
  (if (<= (lnfix x) (node-count aignet))
      (lnfix x)
    0)
  ///
  (defthm aignet-idp-of-aignet-id-fix
    (aignet-idp (aignet-id-fix x aignet) aignet)
    :hints(("Goal" :in-theory (enable aignet-idp))))

  (defthm aignet-id-fix-id-val-linear
    (<= (aignet-id-fix id aignet)
        (node-count aignet))
    :rule-classes :linear)

  (defthm aignet-id-fix-when-aignet-idp
    (implies (aignet-idp id aignet)
             (equal (aignet-id-fix id aignet)
                    (nfix id)))
    :hints(("Goal" :in-theory (enable aignet-idp))))

  (defthm aignet-id-fix-of-node-list-fix
    (equal (aignet-id-fix x (node-list-fix aignet))
           (aignet-id-fix x aignet))))


(defenum fanin-type-p (:gate0 :gate1 :co)
  :short "Kinds of fanins that may be extracted from nodes."
  :parents (fanin)
  :long "<p>The function @(see fanin) uses a fanin-type argument to determine which fanin to fetch from the network.  The possible values are:</p>
<ul>
<li>@(':co'), the unique fanin from a combinational output node</li>
<li>@(':gate0'), the first fanin from a gate node</li>
<li>@(':gate1'), the second fanin from a gate node.</li>
</ul>")


(define fanin ((type fanin-type-p)
               (aignet node-listp))
  :guard (and (consp aignet)
              (if (eq type :co)
                  (eq (ctype (stype (car aignet))) :output)
                (eq (ctype (stype (car aignet))) :gate)))
  :returns (lit litp :rule-classes :type-prescription)
  :short "@(call fanin) gets the specified kind of fanin from the first node of
          the input network and fixes it to be a valid fanin literal of the rest
          of the network."
  (aignet-lit-fix (case (fanin-type-fix type)
                    (:gate0 (gate-node->fanin0 (car aignet)))
                    (:gate1 (gate-node->fanin1 (car aignet)))
                    (otherwise (co-node->fanin (car aignet))))
                  (cdr aignet))
  ///
  (defret fanin-id-lte-node-count
    (<= (lit-id lit) (node-count aignet))
    :rule-classes :linear)

  (defret fanin-id-lte-node-count-strong
    (implies (consp aignet)
             (< (lit-id lit) (node-count aignet)))
    :rule-classes :linear)

  (defret fanin-id-lte-max-fanin
    (<= (lit-id lit) (node-count (find-max-fanin aignet)))
    :rule-classes :linear)

  (defret aignet-litp-of-fanin
    (aignet-litp lit aignet))

  (defret aignet-litp-in-extension-of-fanin
    (implies (aignet-extension-p new aignet)
             (aignet-litp lit new)))

  (defthm fanin-of-cons
    (equal (fanin type (cons node aignet))
           (aignet-lit-fix (case (fanin-type-fix type)
                             (:gate0 (gate-node->fanin0 node))
                             (:gate1 (gate-node->fanin1 node))
                             (otherwise (co-node->fanin node)))
                           aignet))))


(define fanin-if-co ((aignet node-listp))
  :returns (lit litp :rule-classes :type-prescription)
  :short "@(call fanin-if-co) produces the fanin lit of the first node of the network
          if it is a combinational output node, and otherwise produces the non-negated
          literal for the node itself.  Useful for dealing with next-states, because
          the next-state node of a register may be a next-state node (which is
          a combinational output) or the register itself, when its next-state hasn't
          been set yet."
  (if (and (consp aignet)
           (equal (ctype (stype (car aignet))) :output))
      (fanin :co aignet)
    (make-lit (node-count aignet) 0))
  ///
  
  (defret fanin-if-co-id-lte-node-count
    (<= (lit-id lit) (node-count aignet))
    :rule-classes :linear)

  (defret fanin-if-co-id-lte-node-count-strong
    (implies (equal (ctype (stype (car aignet))) :output)
             (< (lit-id lit) (node-count aignet)))
    :rule-classes :linear)

  (defret fanin-if-co-id-lte-max-fanin
    (<= (lit-id lit) (node-count (find-max-fanin aignet)))
    :rule-classes :linear)

  (defret aignet-litp-of-fanin-if-co
    (aignet-litp lit aignet)
    :hints(("Goal" :in-theory (enable aignet-litp))))

  (defret aignet-litp-in-extension-of-fanin-if-co
    (implies (aignet-extension-p new aignet)
             (aignet-litp lit new))
    :hints(("Goal" :in-theory (enable aignet-litp))))

  (defthm fanin-if-co-of-cons
    (equal (fanin-if-co (cons node aignet))
           (if (equal (ctype (stype node)) :output)
               (fanin :co (cons node aignet))
             (make-lit (+ 1 (node-count aignet)) 0))))

  (defret fanin-if-co-when-output
    (implies (equal (ctype (stype (car aignet))) :output)
             (equal lit (fanin :co aignet)))))



