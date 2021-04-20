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
(include-book "centaur/misc/universal-equiv" :dir :system)
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
                 :doc "Index (register number, not ID) of the register for which this is the next state."
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

  ;; (defthm stype-not-const-fwd
  ;;   (implies (not (equal (stype x) (const-stype)))
  ;;            (not (equal (ctype (stype x)) (const-ctype))))
  ;;   :rule-classes ((:forward-chaining :trigger-terms ((stype x)))))

  ;; (defthm ctype-not-gate-fwd
  ;;   (implies (not (equal (ctype (stype x)) (gate-ctype)))
  ;;            (and (not (equal (stype x) (and-stype)))
  ;;                 (not (equal (stype x) (xor-stype)))))
  ;;   :rule-classes ((:forward-chaining :trigger-terms ((ctype (stype x))))))

  ;; (defthm ctype-not-in-fwd
  ;;   (implies (not (equal (ctype (stype x)) (in-ctype)))
  ;;            (and (not (equal (stype x) (pi-stype)))
  ;;                 (not (equal (stype x) (reg-stype)))))
  ;;   :rule-classes ((:forward-chaining :trigger-terms ((ctype (stype x))))))

  ;; (defthm ctype-not-out-fwd
  ;;   (implies (not (equal (ctype (stype x)) (out-ctype)))
  ;;            (and (not (equal (stype x) (po-stype)))
  ;;                 (not (equal (stype x) (nxst-stype)))))
  ;;   :rule-classes ((:forward-chaining :trigger-terms ((ctype (stype x))))))

  (defthm ctype-gate-fwd
    (implies (equal (ctype (stype x)) (gate-ctype))
             (or (equal (stype x) (and-stype))
                 (equal (stype x) (xor-stype))))
    :rule-classes ((:forward-chaining :trigger-terms ((equal (ctype (stype x)) (gate-ctype))
                                                      (equal (gate-ctype) (ctype (stype x)))))))

  (defthm ctype-not-gate-fwd
    (implies (not (equal (ctype (stype x)) (gate-ctype)))
             (and (not (equal (stype x) (and-stype)))
                  (not (equal (stype x) (xor-stype)))))
    :rule-classes ((:forward-chaining :trigger-terms ((equal (ctype (stype x)) (gate-ctype))
                                                      (equal (gate-ctype) (ctype (stype x)))))))

  (defthm ctype-in-fwd
    (implies (equal (ctype (stype x)) (in-ctype))
             (or (equal (stype x) (pi-stype))
                 (equal (stype x) (reg-stype))))
    :rule-classes ((:forward-chaining :trigger-terms ((equal (ctype (stype x)) (in-ctype))
                                                      (equal (in-ctype) (ctype (stype x)))))))

  (defthm ctype-not-in-fwd
    (implies (not (equal (ctype (stype x)) (in-ctype)))
             (and (not (equal (stype x) (pi-stype)))
                  (not (equal (stype x) (reg-stype)))))
    :rule-classes ((:forward-chaining :trigger-terms ((equal (ctype (stype x)) (in-ctype))
                                                      (equal (in-ctype) (ctype (stype x)))))))

  (defthm ctype-out-fwd
    (implies (equal (ctype (stype x)) (out-ctype))
             (or (equal (stype x) (po-stype))
                 (equal (stype x) (nxst-stype))))
    :rule-classes ((:forward-chaining :trigger-terms ((equal (ctype (stype x)) (out-ctype))
                                                      (equal (out-ctype) (ctype (stype x)))))))

  (defthm ctype-not-out-fwd
    (implies (not (equal (ctype (stype x)) (out-ctype)))
             (and (not (equal (stype x) (po-stype)))
                  (not (equal (stype x) (nxst-stype)))))
    :rule-classes ((:forward-chaining :trigger-terms ((equal (ctype (stype x)) (out-ctype))
                                                      (equal (out-ctype) (ctype (stype x)))))))
  )



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
        :reg ...
        :and ...
        :xor ...
        :const ...)
  })

  <p>Where @('typecode') is the @(see typecode) for this node, i.e., it is a
  number, not a @(see sequential-type) keyword, and where @('reg-bit') is a
  @(see bitp) such as from @(see regp).</p>

  <p>An @(':otherwise') keyword can be provided to cover all the cases not mentioned.</p>

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
         (bad-keys (set-difference-eq keys '(:pi :reg :nxst :po :and :xor :in :ci :out :co :gate :const :otherwise)))
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
         (complete
          ;; Note: don't count outputs toward completeness because much of the
          ;; time we'll be dealing with a type extracted from a fanout node.
          (and (or (member :gate keys)
                   (and (member :xor keys)
                        (member :and keys)))
               (or (member :ci keys)
                   (member :in keys)
                   (and (member :pi keys)
                        (member :reg keys)))
               (member :const keys)))
         ((when (and (not complete)
                     (not (member :otherwise keys))))
          (er hard? 'aignet-case "Must at least have all fanout node types ~
                                  covered if there is no :otherwise case."))
         (reg-bit (and (not reg-bit-skippedp) (car args))))
      `(case (the (unsigned-byte 2) ,type)
         ,@(and (or (not (member :otherwise keys))
                    (member :gate keys)
                    (member :xor keys)
                    (member :and keys))
                `((,(gate-type) ,(if (member :gate keyvals)
                                     (cadr (assoc-keyword :gate keyvals))
                                   `(if (int= 1 (the bit ,reg-bit))
                                        ,(cadr (assoc-keyword :xor keyvals))
                                      ,(cadr (assoc-keyword :and keyvals)))))))
         ,@(and (or (not (member :otherwise keys))
                    (member :ci keys)
                    (member :in keys)
                    (member :reg keys))
                `((,(in-type)   ,(if (member :ci keys)
                                     (cadr (assoc-keyword :ci keyvals))
                                   (if (member :in keys)
                                       (cadr (assoc-keyword :in keyvals))
                                     `(if (int= 1 (the bit ,reg-bit))
                                          ,(cadr (assoc-keyword :reg keyvals))
                                        ,(cadr (assoc-keyword :pi keyvals))))))))
         ,@(and (or (member :co keys)
                    (member :out keys)
                    (member :nxst keys)
                    (member :po keys))
                `((,(out-type)  ,(if (assoc-keyword :co keyvals)
                                     (cadr (assoc-keyword :co keyvals))
                                   (if (assoc-keyword :out keyvals)
                                       (cadr (assoc-keyword :out keyvals))
                                     `(if (int= 1 (the bit ,reg-bit))
                                          ,(cadr (assoc-keyword :nxst keyvals))
                                        ,(cadr (assoc-keyword :po keyvals))))))))
         ;; If the type keyword list is complete, then use OTHERWISE for the const case
         ,@(and (member :const keys)
                (if complete
                    `((otherwise ,(cadr (assoc-keyword :const keyvals))))
                  `((,(const-type) ,(cadr (assoc-keyword :const keyvals))))))
         ,@(and (member :otherwise keys)
                `((otherwise    ,(cadr (assoc-keyword :otherwise keyvals)))))))))


(defsection network
  :parents (representation)
  :short "Reference guide for basic functions for working with the AIG network,
  i.e., a list of @(see node)s.")

(local (xdoc::set-default-parents network))

(fty::deflist node-list :pred node-listp :elt-type node :true-listp t :elementp-of-nil t
  ///
  (fty::deffixcong node-list-equiv equal (consp x) x))

(std::deflist proper-node-listp (x)
  (proper-node-p x)
  :true-listp t
  ///
  (defthmd proper-node-listp-implies-node-listp
    (implies (proper-node-listp x)
             (node-listp x))
    :hints(("Goal" :in-theory (enable proper-node-listp
                                      node-listp)))))



(define fanin-node-p ((x node-p))
  (not (equal (ctype (stype x)) (out-ctype)))
  ///
  (defthm fanin-node-p-implies-not-output
    (implies (fanin-node-p x)
             (and (not (equal (ctype (stype x)) (out-ctype)))
                  (not (equal (stype x) :po))
                  (not (equal (stype x) :nxst))))
    :rule-classes :forward-chaining)

  (defthm fanin-node-p-by-ctype
    (implies (and (equal ctype (ctype (stype x)))
                  (syntaxp (quotep ctype)))
             (equal (fanin-node-p x) (not (equal ctype (out-ctype)))))))

(define fanin-count ((x node-listp))
  :short "Number of fanin nodes in the list of nodes"
  :long "<p>This gives the ID of the last fanin node in the list.</p>"
  (if (atom x)
      0
    (+ (if (fanin-node-p (car x)) 1 0)
       (fanin-count (cdr x))))
  ///
  (defthm fanin-count-of-cons
    (equal (fanin-count (cons a x))
           (+ (if (fanin-node-p a) 1 0)
              (fanin-count x))))
  (defthm fanin-count-of-atom
    (implies (not (consp x))
             (equal (fanin-count x) 0))
    :rule-classes ((:rewrite :backchain-limit-lst 1)))
  ;; (defthm fanin-count-equal-0
  ;;   (equal (equal (fanin-count x) 0)
  ;;          (not (consp x))))
  ;; (defthm fanin-count-greater-than-0
  ;;   (equal (< 0 (fanin-count x))
  ;;          (consp x)))
  (defthm fanin-count-of-cdr-strong
    (implies (and (consp x)
                  (fanin-node-p (car x)))
             (equal (fanin-count (cdr x)) (+ -1 (fanin-count x)))))
  (defthm fanin-count-of-cdr-weak
    (<= (fanin-count (cdr x)) (fanin-count x))
    :rule-classes :linear)

  (fty::deffixcong node-list-equiv equal (fanin-count x) x))


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
             (consp x))
    :hints(("Goal" :in-theory (enable stype-count)))
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

  (defthm fanin-count-when-aignet-extension
    (implies (aignet-extension-p y x)
             (<= (fanin-count x) (fanin-count y)))
    :rule-classes ((:linear :trigger-terms ((fanin-count x)))))

  (defthm stype-count-when-aignet-extension
    (implies (aignet-extension-p y x)
             (<= (stype-count k x) (stype-count k y)))
    :rule-classes ((:linear :trigger-terms ((stype-count k x)))))

  (defthm fanin-count-cdr-when-aignet-extension-strong
    (implies (and (aignet-extension-p y x)
                  (consp x)
                  (fanin-node-p (car x)))
             (< (fanin-count (cdr x)) (fanin-count y)))
    :rule-classes ((:linear :trigger-terms
                    ((fanin-count (cdr x))))))

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

  ;; (defthm fanin-count-aignet-extension-p-of-cdr
  ;;   (implies (and (aignet-extension-p (cdr y) x)
  ;;                 (consp y))
  ;;            (< (fanin-count x) (fanin-count y)))
  ;;   :hints (("goal" :induct (list-equiv x y))))
  ;; (defthm fanin-count-aignet-extension-p-of-cdr-not-equal
  ;;   (implies (and (aignet-extension-p (cdr y) x)
  ;;                 (consp y))
  ;;            (not (equal (fanin-count x) (fanin-count y))))
  ;;   :hints (("goal" :use fanin-count-aignet-extension-p-of-cdr
  ;;            :in-theory (disable fanin-count-aignet-extension-p-of-cdr))))
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
                   (<= (nfix id) (fanin-count orig)))
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
     (implies (<= (nfix id) (fanin-count (lookup-reg->nxst n aignet))))
              (equal (lookup-id id (lookup-reg->nxst n aignet))
                     (lookup-id id aignet)))

     (implies (<= (nfix id) (fanin-count (lookup-stype n stype aignet))))
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



  (defthm fanin-count-when-aignet-extension-bind-inverse
    (implies (aignet-extension-bind-inverse :orig x :new y)
             (<= (fanin-count x) (fanin-count y)))
    :rule-classes ((:linear :trigger-terms ((fanin-count x)))))

  (defthm stype-count-when-aignet-extension-bind-inverse
    (implies (aignet-extension-bind-inverse :orig x :new y)
             (<= (stype-count k x) (stype-count k y)))
    :rule-classes ((:linear :trigger-terms ((stype-count k x)))))

  (defthm fanin-count-cdr-when-aignet-extension-inverse
    (implies (and (aignet-extension-bind-inverse :orig x :new y)
                  (consp x)
                  (fanin-node-p (car x)))
             (< (fanin-count (cdr x)) (fanin-count y)))
    :rule-classes ((:linear :trigger-terms
                    ((fanin-count (cdr x))))))

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




  (defthm aignet-extension-implies-fanin-count-gte
    (implies (aignet-extension-binding)
             (<= (fanin-count orig) (fanin-count new)))
    :rule-classes ((:linear :trigger-terms ((fanin-count new)))))

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
        ((and (fanin-node-p (car aignet))
              (equal (fanin-count aignet) (lnfix id)))
         (node-list-fix aignet))
        (t (lookup-id id (cdr aignet))))
  ///
  (fty::deffixequiv lookup-id)
  ;; (defcong nat-equiv equal (lookup-id id aignet) 1)
  (defthm fanin-count-of-lookup-id
    (implies (<= (nfix n) (fanin-count aignet))
             (equal (fanin-count (lookup-id n aignet))
                    (nfix n))))
  (defthm fanin-count-of-cdr-lookup-id
    (implies (consp (lookup-id n aignet))
             (equal (fanin-count (cdr (lookup-id n aignet)))
                    (+ -1 (nfix n)))))
  (defthm output-ctype-of-lookup-id
    (not (equal (ctype (stype (car (lookup-id id aignet)))) (out-ctype))))

  (defthm output-stype-of-lookup-id
    (and (not (equal (stype (car (lookup-id id aignet))) :po))
         (not (equal (stype (car (lookup-id id aignet))) :nxst))))

  (defthm fanin-node-p-of-lookup-id
    (fanin-node-p (car (lookup-id id aignet))))

  (defthm lookup-id-0
    (equal (lookup-id 0 aignet) nil))

  (defthmd lookup-id-in-bounds
    (iff (consp (lookup-id n aignet))
         (and (< 0 (nfix n))
              (<= (nfix n) (fanin-count aignet)))))

  (defthm lookup-id-in-bounds-when-positive
    (implies (posp n)
             (iff (consp (lookup-id n aignet))
                  (<= (nfix n) (fanin-count aignet)))))

  (defthm lookup-id-aignet-extension-p
    (aignet-extension-p aignet (lookup-id id aignet))
    :hints(("Goal" :in-theory (enable aignet-extension-p))))
  ;; (defcong list-equiv list-equiv (lookup-id id aignet) 2)
  ;; (defcong list-equiv iff (lookup-id id aignet) 2)
  (defthm lookup-id-in-extension
    (implies (and (aignet-extension-p new orig)
                  (<= (nfix id) (fanin-count orig)))
             (equal (lookup-id id new)
                    (lookup-id id orig)))
    :hints(("Goal" :in-theory (enable aignet-extension-p))))
  (defthm lookup-id-in-extension-inverse
    (implies (and (aignet-extension-bind-inverse)
                  (<= (nfix id) (fanin-count orig)))
             (equal (lookup-id id orig)
                    (lookup-id id new)))
    :hints(("Goal" :in-theory (enable aignet-extension-p))))
  (defthm fanin-count-of-cdr-lookup-bound-by-id
    (implies (consp (lookup-id id aignet))
             (< (fanin-count (cdr (lookup-id id aignet)))
                (nfix id)))
    :rule-classes :linear)
  (defthm lookup-id-of-fanin-count-of-suffix
    (implies (and (aignet-extension-p y x)
                  (consp x)
                  (fanin-node-p (car x)))
             (equal (lookup-id (fanin-count x) y)
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
           (if (and (fanin-node-p node)
                    (equal (nfix id) (+ 1 (fanin-count rest))))
               (cons (node-fix node) (node-list-fix rest))
             (lookup-id id rest))))
  (defthm lookup-id-of-fanin-count
    (implies (fanin-node-p (car x))
             (equal (lookup-id (fanin-count x) x)
                    (node-list-fix x))))
  (defthm fanin-count-of-lookup-id-when-consp
    (implies (consp (lookup-id id aignet))
             (equal (fanin-count (lookup-id id aignet))
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
             (<= (nfix id) (fanin-count aignet)))
    :hints(("Goal" :in-theory (enable lookup-id-in-bounds)))
    :rule-classes :forward-chaining)
  (defthm lookup-id-consp-forward-to-id-bound
    (implies (and (consp (lookup-id id aignet))
                  (natp id))
             (<= id (fanin-count aignet)))
    :rule-classes :forward-chaining)

  (defthm lookup-id-out-of-bounds
    (implies (< (fanin-count aignet) (nfix id))
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
  (defthm stype-count-of-cdr-lookup-stype
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

  (defthm consp-of-lookup-stype
    (implies (natp n)
             (equal (consp (lookup-stype n stype aignet))
                    (< (nfix n) (stype-count stype aignet)))))

  ;; (defret stype-of-lookup-stype
  ;;   (implies (stypep stype)
  ;;            (or (equal (stype (car suffix)) stype)
  ;;                (equal (stype (car suffix)) :const)))
  ;;   :rule-classes ((:forward-chaining :trigger-terms ((stype (car suffix))))))

  (defthmd stype-count-of-lookup-stype-split
    (equal (stype-count stype (lookup-stype n stype aignet))
           (if (< (nfix n) (stype-count stype aignet))
               (+ 1 (nfix n))
             0))
    :hints(("Goal" :in-theory (enable stype-count))))

  (defthm stype-count-of-lookup-stype
    (implies (< (nfix n) (stype-count stype aignet))
             (equal (stype-count stype (lookup-stype n stype aignet))
                    (+ 1 (nfix n))))
    :hints(("Goal" :in-theory (enable stype-count-of-lookup-stype-split)))))

(define aignet-idp ((id     natp)
                    (aignet node-listp))
  :short "Check whether a node ID is in bounds for this network."
  (<= (lnfix id) (fanin-count aignet))
  ///
  (fty::deffixequiv aignet-idp)
  (defthm bound-when-aignet-idp
    (implies (aignet-idp id aignet)
             (<= (nfix id) (fanin-count aignet))))
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

  (defthm aignet-idp-of-fanin-count-of-extension
    (implies (aignet-extension-p aignet prev)
             (aignet-idp (fanin-count prev) aignet))
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

(define aignet-id-fix ((id natp)
                       (aignet node-listp))
  :short "Fix an ID so that it is valid for the aignet."
  :returns (new-id (aignet-idp new-id aignet))
  (if (aignet-idp id aignet)
      (nfix id)
    0)
  ///
  (defthm aignet-id-fix-when-aignet-idp
    (implies (aignet-idp id aignet)
             (equal (aignet-id-fix id aignet) (nfix id))))

  (defthm aignet-id-fix-id-val-linear
    (<= (aignet-id-fix id aignet)
        (fanin-count aignet))
    :rule-classes :linear)

  (defthm aignet-id-fix-of-node-list-fix
    (equal (aignet-id-fix x (node-list-fix aignet))
           (aignet-id-fix x aignet))))


(defmacro aignet-litp (x aignet)
  `(aignet-idp (lit->var ,x) ,aignet))

(defxdoc aignet-litp
  :short "Abbreviation for @('(aignet-idp (lit->var x) aignet)').")

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
  ;; :measure (fanin-count aignet)
  ;; :hints ('(:in-theory (enable lookup-id-in-bounds)))
  :returns (fix litp :rule-classes :type-prescription)
  (make-lit (aignet-id-fix (lit->var x) aignet) (lit->neg x))
  ///
  (verify-guards aignet-lit-fix)

  (defthm aignet-litp-of-aignet-lit-fix
    (aignet-litp (aignet-lit-fix x aignet) aignet))

  (defthm aignet-lit-fix-when-aignet-litp
    (implies (aignet-litp x aignet)
             (equal (aignet-lit-fix x aignet) (lit-fix x))))

  (defthm lit->var-of-aignet-lit-fix
    (equal (lit->var (aignet-lit-fix x aignet))
           (aignet-id-fix (lit->var x) aignet)))

  (defthm lit->neg-of-aignet-lit-fix
    (equal (lit->neg (aignet-lit-fix x aignet))
           (lit->neg x))))

(define lookup-reg->nxst ((reg natp "Register number for this register.")
                          (aignet node-listp))
  :returns (nxst-lit litp :rule-classes :type-prescription)
  :short "Look up the next-state node that corresponds to particular register
  node."
  :long "<p><b>Note</b>: This is different from the other lookups: it's by ID
  of the corresponding RO node, not IO number.  I think the asymmetry is worth
  it though.</p>"

  (cond ((endp aignet)
         ;; Register number was out of bounds -- just use 0
         0)
        ((and (equal (stype (car aignet)) (nxst-stype))
              (b* ((ro (nxst-node->reg (car aignet))))
                (and (nat-equiv reg ro)
                     (< ro (stype-count :reg aignet)))))
         ;; Nextstate node for this reg -- return fanin
         (aignet-lit-fix (nxst-node->fanin (car aignet)) aignet))
        ((and (equal (stype (car aignet)) (reg-stype))
              (nat-equiv (stype-count :reg (cdr aignet)) reg))
         (make-lit (fanin-count aignet) 0))
        (t (lookup-reg->nxst reg (cdr aignet))))
  ///

  (defthm aignet-litp-of-lookup-reg->nxst
    (aignet-litp (lookup-reg->nxst reg aignet) aignet))

  (fty::deffixequiv lookup-reg->nxst
    :hints (("goal" :induct (lookup-reg->nxst reg aignet)
             :expand ((:free (reg) (lookup-reg->nxst reg aignet))
                      (lookup-reg->nxst reg (node-list-fix aignet))))))

  (defthm lookup-reg->nxst-id-bound
         (<= (lit->var (lookup-reg->nxst n aignet)) (fanin-count aignet))
         :hints(("Goal" :in-theory (enable lookup-reg->nxst)))
         :rule-classes :linear)

  (defthmd lookup-reg->nxst-out-of-bounds
    (implies (<= (stype-count :reg aignet) (nfix n))
             (equal (lookup-reg->nxst n aignet) 0)))

  ;; (defthm lookup-reg->nxst-count-when-reg
  ;;   (implies (equal (stype (car (lookup-reg->nxst reg-id aignet)))
  ;;                   (reg-stype))
  ;;            (equal (fanin-count (lookup-reg->nxst reg-id aignet))
  ;;                   (nfix reg-id))))

  ;; (defthm aignet-extension-p-of-lookup-reg->nxst
  ;;   (aignet-extension-p aignet (lookup-reg->nxst reg-id aignet))
  ;;   :hints(("Goal" :in-theory (enable aignet-extension-p))))

  ;; ;; (defthm stype-of-lookup-reg->nxst
  ;; ;;   (implies (consp (lookup-reg->nxst n aignet))
  ;; ;;            (equal (stype (car (lookup-reg->nxst n aignet)))
  ;; ;;                   (nxst-stype))))

  ;; (defthm fanin-count-of-lookup-reg->nxst
  ;;   (implies (consp (lookup-reg->nxst n aignet))
  ;;            (<= (nfix n) (fanin-count (lookup-reg->nxst n aignet))))
  ;;   :rule-classes :linear)

  ;; (defthm lookup-reg->nxst-out-of-bounds
  ;;   (implies (< (fanin-count aignet) (nfix id))
  ;;            (equal (lookup-reg->nxst id aignet) nil)))

  ;; (defthm lookup-reg->nxst-of-0
  ;;   (equal (lookup-reg->nxst 0 aignet) nil)
  ;;   :hints(("Goal" :in-theory (enable lookup-reg->nxst))))

  ;; (defret stypes-of-lookup-reg->nxst
  ;;   (or (equal (stype (car suffix)) :nxst)
  ;;       (equal (stype (car suffix)) :reg)
  ;;       (equal (stype (car suffix)) :const))
  ;;   :rule-classes ((:forward-chaining :trigger-terms ((stype (car suffix))))))
  )


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





;; (define aignet-litp ((lit    litp)
;;                      (aignet node-listp))
;;   :short "Check if a @(see literal) is valid for use as a fanin to another node."
;;   :long "<p>We return true only if the ID for the literal is in bounds for the
;;   network and refers to a node of acceptable type.  In particular, the literal
;;   may not refer to any combinational output node, i.e., it may not be a primary
;;   output and may also not be a next-state (register input) node.</p>"
;;   (and (<= (lit-id lit)
;;            (fanin-count aignet))
;;        (not (equal (node->type (car (lookup-id (lit-id lit) aignet)))
;;                    (out-type))))
;;   ///
;;   (fty::deffixequiv aignet-litp)
;;   (defthm lit-id-bound-when-aignet-litp
;;     (implies (aignet-litp lit aignet)
;;              (<= (lit-id lit) (fanin-count aignet)))
;;     :rule-classes ((:linear :trigger-terms ((lit-id lit)))))
;;   (local (defthm <=-when-<-+-1
;;            (implies (and (< x (+ 1 y))
;;                          (integerp x) (integerp y))
;;                     (<= x y))))
;;   (defthm aignet-litp-in-extension
;;     (implies (and (aignet-extension-p new orig)
;;                   (aignet-litp lit orig))
;;              (aignet-litp lit new)))
;;   (defcong lit-equiv equal (aignet-litp lit aignet) 1)
;;   (defcong list-equiv equal (aignet-litp lit aignet) 2)

;;   (defthm aignet-idp-when-aignet-litp
;;     (implies (aignet-litp lit aignet)
;;              (aignet-idp (lit-id lit) aignet))
;;     :hints(("Goal" :in-theory (enable aignet-idp))))

;;   (defthm aignet-litp-of-0-and-1
;;     (and (aignet-litp 0 aignet)
;;          (aignet-litp 1 aignet)))

;;   (defthm aignet-litp-of-mk-lit-lit-id
;;     (equal (aignet-litp (mk-lit (lit-id lit) neg) aignet)
;;            (aignet-litp lit aignet)))

;;   (defthm aignet-litp-of-mk-lit-0
;;     (aignet-litp (mk-lit 0 neg) aignet))

;;   (defthm aignet-litp-implies-id-lte-max-fanin
;;     (implies (aignet-litp lit aignet)
;;              (<= (lit-id lit)
;;                  (fanin-count (find-max-fanin aignet))))
;;     :hints(("Goal" :in-theory (enable aignet-litp find-max-fanin)))
;;     :rule-classes :forward-chaining)

;;   (defthm aignet-extension-simplify-aignet-litp
;;     (implies (and (aignet-extension-binding)
;;                   (aignet-litp lit orig))
;;              (aignet-litp lit new)))

;;   (defthm aignet-litp-of-lit-negate
;;     (equal (aignet-litp (lit-negate x) aignet)
;;            (aignet-litp x aignet))
;;     :hints(("Goal" :in-theory (enable lit-negate))))

;;   (defthm aignet-litp-of-lit-negate-cond
;;     (equal (aignet-litp (lit-negate-cond x neg) aignet)
;;            (aignet-litp x aignet))
;;     :hints(("Goal" :in-theory (enable lit-negate-cond))))

;;   (defthm not-output-when-aignet-litp
;;     (implies (aignet-litp lit aignet)
;;              (and (not (equal (ctype (stype (car (lookup-id (lit-id lit) aignet)))) :output))
;;                   (not (equal (stype (car (lookup-id (lit-id lit) aignet))) :po))
;;                   (not (equal (stype (car (lookup-id (lit-id lit) aignet))) :nxst))))))


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
                        (< (nxst-node->reg (car aignet))
                           (stype-count :reg (cdr aignet))))
           :gate (let ((f0 (gate-node->fanin0 (car aignet)))
                       (f1 (gate-node->fanin1 (car aignet))))
                   (and (aignet-litp f0 (cdr aignet))
                        (aignet-litp f1 (cdr aignet))))
           :otherwise nil)
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
                (stype-count :reg (lookup-id id aignet))))
    :hints (("goal" :induct (lookup-id id aignet)
             :in-theory (e/d (lookup-id aignet-idp)
                             ((force)))))
    :rule-classes (:rewrite
                   (:linear :trigger-terms
                    ((nxst-node->reg
                      (car (lookup-id id aignet)))))))
  (defthm gate-fanin0-ordered-when-aignet-nodes-ok
    (implies (and (aignet-nodes-ok aignet)
                  (equal (node->type (car (lookup-id id aignet)))
                         (gate-type)))
             (< (lit-id (gate-node->fanin0
                         (car (lookup-id id aignet))))
                (nfix id)))
    :hints (("goal" :induct (lookup-id id aignet)
             :in-theory (enable lookup-id aignet-idp)
             :expand ((aignet-nodes-ok aignet))))
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
             :in-theory (enable lookup-id aignet-idp)
             :expand ((aignet-nodes-ok aignet))))
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

  ;; (defthm id-less-than-max-fanin-when-aignet-litp
  ;;   (implies (aignet-litp lit aignet)
  ;;            (<= (lit-id lit) (fanin-count (find-max-fanin aignet))))
  ;;   :hints(("Goal" :in-theory (enable aignet-litp find-max-fanin)))
  ;;   :rule-classes nil)

  ;; (defthm gate-fanin0-less-than-max-fanin
  ;;   (let ((suffix (lookup-id n aignet)))
  ;;     (implies (and (aignet-nodes-ok aignet)
  ;;                   (equal (node->type (car suffix)) (gate-type)))
  ;;              (<= (lit-id (gate-node->fanin0 (car suffix)))
  ;;                  (fanin-count (find-max-fanin aignet)))))
  ;;   :hints (("goal" :use ((:instance id-less-than-max-fanin-when-aignet-litp
  ;;                          (lit (gate-node->fanin0 (car (lookup-id n aignet))))))))
  ;;   :rule-classes :linear)

  ;; (defthm gate-fanin1-less-than-max-fanin
  ;;   (let ((suffix (lookup-id n aignet)))
  ;;     (implies (and (aignet-nodes-ok aignet)
  ;;                   (equal (node->type (car suffix)) (gate-type)))
  ;;              (<= (lit-id (gate-node->fanin1 (car suffix)))
  ;;                  (fanin-count (find-max-fanin aignet)))))
  ;;   :hints (("goal" :use ((:instance id-less-than-max-fanin-when-aignet-litp
  ;;                          (lit (gate-node->fanin1 (car (lookup-id n aignet))))))))
  ;;   :rule-classes :linear)

  ;; (defthm co-fanin-less-than-max-fanin
  ;;   (let ((suffix (lookup-id n aignet)))
  ;;     (implies (and (aignet-nodes-ok aignet)
  ;;                   (equal (node->type (car suffix)) (out-type)))
  ;;              (<= (lit-id (co-node->fanin (car suffix)))
  ;;                  (fanin-count (find-max-fanin aignet)))))
  ;;   :hints (("goal" :use ((:instance id-less-than-max-fanin-when-aignet-litp
  ;;                          (lit (co-node->fanin (car (lookup-id n aignet))))))))
  ;;   :rule-classes :linear)
  )



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
;; (local (defthm fanin-count-cdr-when-consp
;;          (implies (consp x)
;;                   (< (fanin-count (cdr x)) (fanin-count x)))
;;          :rule-classes :linear))




;; (defenum fanin-type-p (:gate0 :gate1 :co)
;;   :short "Kinds of fanins that may be extracted from nodes."
;;   :parents (fanin)
;;   :long "<p>The function @(see fanin) uses a fanin-type argument to determine which fanin to fetch from the network.  The possible values are:</p>
;; <ul>
;; <li>@(':co'), the unique fanin from a combinational output node</li>
;; <li>@(':gate0'), the first fanin from a gate node</li>
;; <li>@(':gate1'), the second fanin from a gate node.</li>
;; </ul>")


(define fanin ((which bitp)
               (aignet node-listp))
  :guard (and (consp aignet)
              (or (eq (ctype (stype (car aignet))) :output)
                  (eq (ctype (stype (car aignet))) :gate)))
  :returns (lit litp :rule-classes :type-prescription)
  :short "@(call fanin) gets the specified fanin from the first node of
          the input network and fixes it to be a valid fanin literal of the rest
          of the network."
  (aignet-lit-fix (if (eq (ctype (stype (car aignet))) :output)
                      (co-node->fanin (car aignet))
                    (if (bit->bool which)
                        (gate-node->fanin1 (car aignet))
                      (gate-node->fanin0 (car aignet))))
                  (cdr aignet))
  ///
  (defret fanin-id-lte-fanin-count
    (<= (lit-id lit) (fanin-count (cdr aignet)))
    :rule-classes :linear)

  (defret fanin-id-lte-fanin-count-strong
    (implies (and (consp aignet)
                  (fanin-node-p (car aignet)))
             (< (lit-id lit) (fanin-count aignet)))
    :rule-classes :linear)

  ;; (defret fanin-id-lte-max-fanin
  ;;   (<= (lit-id lit) (fanin-count (find-max-fanin aignet)))
  ;;   :rule-classes :linear)

  (defret aignet-litp-of-fanin
    (aignet-litp lit aignet))

  (defret aignet-litp-in-extension-of-fanin
    (implies (aignet-extension-p new aignet)
             (aignet-litp lit new)))

  (defthm fanin-of-cons
    (equal (fanin which (cons node aignet))
           (aignet-lit-fix (if (eq (ctype (stype node)) :output)
                               (co-node->fanin node)
                             (if (bit->bool which)
                                 (gate-node->fanin1 node)
                               (gate-node->fanin0 node)))
                           aignet))))


;; (define fanin-if-co ((aignet node-listp))
;;   :returns (lit litp :rule-classes :type-prescription)
;;   :short "@(call fanin-if-co) produces the fanin lit of the first node of the network
;;           if it is a combinational output node, and otherwise produces the non-negated
;;           literal for the node itself.  Useful for dealing with next-states, because
;;           the next-state node of a register may be a next-state node (which is
;;           a combinational output) or the register itself, when its next-state hasn't
;;           been set yet."
;;   (if (and (consp aignet)
;;            (equal (ctype (stype (car aignet))) :output))
;;       (fanin 0 aignet)
;;     (make-lit (fanin-count aignet) 0))
;;   ///

;;   (defret fanin-if-co-id-lte-fanin-count
;;     (<= (lit-id lit) (fanin-count aignet))
;;     :rule-classes :linear)

;;   (defret fanin-if-co-id-lte-fanin-count-strong
;;     (implies (equal (ctype (stype (car aignet))) :output)
;;              (< (lit-id lit) (fanin-count aignet)))
;;     :rule-classes :linear)

;;   (defret fanin-if-co-id-lte-max-fanin
;;     (<= (lit-id lit) (fanin-count (find-max-fanin aignet)))
;;     :rule-classes :linear)

;;   (defret aignet-litp-of-fanin-if-co
;;     (aignet-litp lit aignet)
;;     :hints(("Goal" :in-theory (enable aignet-litp))))

;;   (defret aignet-litp-in-extension-of-fanin-if-co
;;     (implies (aignet-extension-p new aignet)
;;              (aignet-litp lit new))
;;     :hints(("Goal" :in-theory (enable aignet-litp))))

;;   (defthm fanin-if-co-of-cons
;;     (equal (fanin-if-co (cons node aignet))
;;            (if (equal (ctype (stype node)) :output)
;;                (fanin 0 (cons node aignet))
;;              (make-lit (+ 1 (fanin-count aignet)) 0))))

;;   (defret fanin-if-co-when-output
;;     (implies (equal (ctype (stype (car aignet))) :output)
;;              (equal lit (fanin 0 aignet)))))

(local (defthm fanin-count-of-append
         (equal (fanin-count (append a b))
                (+ (fanin-count a) (fanin-count b)))))

(local (defthm stype-count-of-append
         (equal (stype-count stype (append a b))
                (+ (stype-count stype a) (stype-count stype b)))))

(local (defthm lookup-id-of-append-non-fanins
         (implies (equal (fanin-count a) 0)
                  (equal (lookup-id n (append a b))
                         (lookup-id n b)))
         :hints(("Goal" :in-theory (enable lookup-id)))))

(local (defthm lookup-stype-of-append-non-stypes
         (implies (equal (stype-count stype a) 0)
                  (equal (lookup-stype n stype (append a b))
                         (lookup-stype n stype b)))
         :hints(("Goal" :in-theory (enable lookup-stype)))))

(local (defthm lookup-stype-of-append-stypes
         (implies (and (< (nfix n) (stype-count stype a))
                       (equal (stype-count stype b) 0))
                  (equal (lookup-stype n stype (append a b))
                         (append (lookup-stype n stype a)
                                 (node-list-fix b))))
         :hints(("Goal" :in-theory (enable lookup-stype)))))


(define aignet-fanins ((aignet node-listp))
  :returns (fanins node-listp)
  (if (atom aignet)
      nil
    (if (fanin-node-p (car aignet))
        (cons (node-fix (car aignet))
              (aignet-fanins (cdr aignet)))
      (aignet-fanins (cdr aignet))))
  ///
  (defret fanin-count-of-aignet-fanins
    (equal (fanin-count fanins) (fanin-count aignet)))

  (defret lookup-id-of-aignet-fanins
    (equal (lookup-id n fanins)
           (aignet-fanins (lookup-id n aignet)))
    :hints(("Goal" :in-theory (enable lookup-id))))

  (defret stype-count-of-aignet-fanins
    (equal (stype-count stype fanins)
           (if (equal (ctype stype) (out-ctype))
               0
             (stype-count stype aignet)))
    :hints(("Goal" :in-theory (enable stype-count fanin-node-p))))

  (fty::deffixequiv aignet-fanins)

  (defret lookup-stype-of-aignet-fanins
    (equal (lookup-stype n stype fanins)
           (if (equal (ctype stype) (out-ctype))
               nil
             (aignet-fanins (lookup-stype n stype aignet))))
    :hints(("Goal" :in-theory (enable lookup-stype fanin-node-p))))

  (defret car-of-aignet-fanins
    (implies (fanin-node-p (car aignet))
             (equal (car fanins)
                    (node-fix (car aignet)))))

  (defret cdr-of-aignet-fanins
    (implies (fanin-node-p (car aignet))
             (equal (cdr fanins)
                    (aignet-fanins (cdr aignet)))))

  (defthm aignet-fanins-of-append-non-fanins
    (implies (equal (fanin-count first) 0)
             (equal (aignet-fanins (append first x))
                    (aignet-fanins x))))

  (defthm aignet-fanins-idempotent
    (equal (aignet-fanins (aignet-fanins x))
           (aignet-fanins x)))

  (defthm fanin-of-aignet-fanins
    (implies (fanin-node-p (car aignet))
             (equal (fanin ftype (aignet-fanins aignet))
                    (fanin ftype aignet)))
    :hints(("Goal" :in-theory (enable fanin aignet-lit-fix aignet-id-fix aignet-idp))))

  (defthm aignet-fanins-of-cons
    (equal (aignet-fanins (cons node x))
           (if (fanin-node-p node)
               (cons (node-fix node) (aignet-fanins x))
             (aignet-fanins x)))))





(define aignet-outputs-aux ((n natp) (aignet node-listp))
  :guard (<= n (stype-count :po aignet))
  ;; :measure (nfix (- (stype-count :po aignet) (nfix n)))
  :returns (outputs node-listp)
  (if (zp n) ;; (- (stype-count :po aignet) (nfix n)))
      nil
    (cons (po-node (fanin 0 (lookup-stype (1- n) :po aignet)))
          (aignet-outputs-aux (1- n) aignet)))
  ///
  (defret fanin-count-of-aignet-outputs-aux
    (equal (fanin-count outputs) 0))

  (defret lookup-id-of-aignet-outputs-aux
    (equal (lookup-id k outputs) nil)
    :hints(("Goal" :in-theory (enable lookup-id)
            :induct <call>)))

  (defret stype-count-of-aignet-outputs-aux
    (equal (stype-count stype outputs)
           (if (equal (stype-fix stype) :po)
               (nfix n) ;; (- (stype-count :po aignet) (nfix n)))
             0)))

  (fty::deffixequiv aignet-outputs-aux)

  (local (defthm lookup-stype-of-lookup-stype
           (implies (and (<= (nfix n) (nfix k))
                         (< (nfix k) (stype-count stype aignet)))
                    (equal (lookup-stype n stype (lookup-stype k stype aignet))
                           (lookup-stype n stype aignet)))
           :hints(("Goal" :in-theory (enable lookup-stype stype-count)))))

  (defret aignet-outputs-aux-of-lookup-po
    (implies (and (<= (nfix n) (+ 1 (nfix k)))
                  (< (nfix k) (stype-count :po aignet)))
             (equal (aignet-outputs-aux n (lookup-stype k :po aignet))
                    (aignet-outputs-aux n aignet))))

  (defret lookup-stype-of-aignet-outputs-aux
    (implies (<= (nfix n) (stype-count :po aignet))
             (equal (lookup-stype k stype outputs)
                    (if (and (equal (stype-fix stype) :po)
                             (< (nfix k) (nfix n)))
                        (aignet-outputs-aux (+ 1 (nfix k)) (lookup-stype k :po aignet))
                      nil)))
    :hints(("Goal" :in-theory (enable lookup-stype)
            :induct <call>)))

  (defret lookup-reg->nxst-of-append-aignet-outputs-aux
    (equal (lookup-reg->nxst k (append outputs rest))
           (lookup-reg->nxst k rest))
    :hints(("Goal" :in-theory (enable lookup-reg->nxst))))

  (defret car-of-aignet-outputs-aux
    (implies (posp n)
             (equal (car outputs)
                    (po-node (fanin 0 (lookup-stype (1- (nfix n)) :po aignet))))))

  (defret consp-of-aignet-outputs-aux
    (equal (consp outputs)
           (posp n)))

  (defret aignet-outputs-aux-of-append-aignet-outputs-aux
    (implies (and (equal (stype-count :po rest) 0)
                  (<= (nfix n) (nfix m))
                  (<= (nfix m) (stype-count :po x))
                  (<= (fanin-count x) (fanin-count rest)))
             (equal (aignet-outputs-aux n (append (aignet-outputs-aux m x) rest))
                    (aignet-outputs-aux n x)))
    :hints(("Goal" :in-theory (enable aignet-lit-fix
                                      aignet-id-fix
                                      aignet-idp))))

  (defthm aignet-outputs-aux-of-append-non-outputs
    (implies (equal (stype-count :po first) 0)
             (equal (aignet-outputs-aux n (append first x))
                    (aignet-outputs-aux n x))))

  (defthm aignet-outputs-aux-of-cons
    (implies (<= (nfix n) (stype-count :po x))
             (equal (aignet-outputs-aux n (cons node x))
                    (aignet-outputs-aux n x)))))

(define aignet-outputs ((aignet node-listp))
  :returns (outputs node-listp)
  (aignet-outputs-aux (stype-count :po aignet) aignet)
  ///
  (defret fanin-count-of-aignet-outputs
    (equal (fanin-count outputs) 0))

  (defret lookup-id-of-aignet-outputs
    (equal (lookup-id k outputs) nil))

  (defret stype-count-of-aignet-outputs
    (equal (stype-count stype outputs)
           (if (equal (stype-fix stype) :po)
               (stype-count :po aignet)
             0)))

  (fty::deffixequiv aignet-outputs)



  (defret lookup-stype-of-aignet-outputs
    (equal (lookup-stype k stype outputs)
           (if (and (equal (stype-fix stype) :po)
                    (< (nfix k) (stype-count :po aignet)))
               (aignet-outputs (lookup-stype k :po aignet))
             nil)))

  (defret lookup-reg->nxst-of-append-aignet-outputs
    (equal (lookup-reg->nxst k (append outputs rest))
           (lookup-reg->nxst k rest)))

  (defret car-of-aignet-outputs
    (implies (posp (stype-count :po aignet))
             (equal (car outputs)
                    (po-node (fanin 0 (lookup-stype (1- (stype-count :po aignet)) :po aignet))))))

  (defret consp-of-aignet-outputs
    (equal (consp outputs)
           (posp (stype-count :po aignet))))

  (defret aignet-outputs-of-append-aignet-outputs
    (implies (and (equal (stype-count :po rest) 0)
                  ;;(<= (nfix m) (stype-count :po x))
                  (<= (fanin-count x) (fanin-count rest)))
             (equal (aignet-outputs (append (aignet-outputs x) rest))
                    (aignet-outputs x))))

  (defthm aignet-outputs-of-append-non-outputs
    (implies (equal (stype-count :po first) 0)
             (equal (aignet-outputs (append first x))
                    (aignet-outputs x))))

  (defthm aignet-outputs-of-cons
    (equal (aignet-outputs (cons node x))
           (if (equal (stype node) :po)
               (cons (po-node (aignet-lit-fix (po-node->fanin node) x))
                     (aignet-outputs x))
             (aignet-outputs x)))
    :hints(("Goal" :in-theory (enable aignet-outputs-aux
                                      fanin lookup-stype
                                      co-node->fanin)))))



(define aignet-nxsts-aux ((n natp) (aignet node-listp))
  :guard (<= n (stype-count :reg aignet))
  ;; :measure (nfix (- (stype-count :po aignet) (nfix n)))
  :returns (nxsts node-listp)
  (if (zp n) ;; (- (stype-count :po aignet) (nfix n)))
      nil
    (cons (nxst-node (lookup-reg->nxst (1- n) aignet) (1- n))
          (aignet-nxsts-aux (1- n) aignet)))
  ///
  (defret fanin-count-of-aignet-nxsts-aux
    (equal (fanin-count nxsts) 0))

  (defret lookup-id-of-aignet-nxsts-aux
    (equal (lookup-id k nxsts) nil)
    :hints(("Goal" :in-theory (enable lookup-id)
            :induct <call>)))

  (defret stype-count-of-aignet-nxsts-aux
    (equal (stype-count stype nxsts)
           (if (equal (stype-fix stype) :nxst)
               (nfix n) ;; (- (stype-count :po aignet) (nfix n)))
             0)))

  (fty::deffixequiv aignet-nxsts-aux)

  ;; (local (defthm lookup-stype-of-lookup-stype
  ;;          (implies (and (<= (nfix n) (nfix k))
  ;;                        (< (nfix k) (stype-count stype aignet)))
  ;;                   (equal (lookup-stype n stype (lookup-stype k stype aignet))
  ;;                          (lookup-stype n stype aignet)))
  ;;          :hints(("Goal" :in-theory (enable lookup-stype stype-count)))))

  ;; (defret aignet-nxsts-aux-of-lookup-nxst
  ;;   (implies (and (<= (nfix n) (+ 1 (nfix k)))
  ;;                 (< (nfix k) (stype-count :nxst aignet)))
  ;;            (equal (aignet-nxsts-aux n (lookup-stype k :nxst aignet))
  ;;                   (aignet-nxsts-aux n aignet))))

  (defret lookup-stype-of-aignet-nxsts-aux
    (implies (not (equal (stype-fix stype) :nxst))
             (equal (lookup-stype k stype nxsts) nil))
    :hints(("Goal" :in-theory (enable lookup-stype)
            :induct <call>)))

  ;; (defret lookup-reg->nxst-of-aignet-nxsts-aux-less
  ;;   (implies (<= (nfix n) (nfix k))
  ;;            (equal (lookup-reg->nxst k (append nxsts rest))
  ;;                   (lookup-reg->nxst k rest)))
  ;;   :hints(("Goal" :in-theory (enable lookup-reg->nxst))))


  (defret lookup-reg->nxst-of-aignet-nxsts-aux
    (implies (<= (fanin-count aignet) (fanin-count rest))
             (equal (lookup-reg->nxst k (append nxsts rest))
                    (if (and (< (nfix k) (nfix n))
                             (< (nfix k) (stype-count :reg rest)))
                        (lookup-reg->nxst k aignet)
                      (lookup-reg->nxst k rest))))
    :hints(("Goal" :in-theory (enable lookup-reg->nxst aignet-lit-fix aignet-id-fix aignet-idp)
            :induct <call>)))

  (defthm aignet-nxsts-aux-of-append-aignet-nxsts-aux
    (implies (and (<= (nfix n) (stype-count :reg rest))
                  (<= (fanin-count x) (fanin-count rest))
                  (<= (nfix n) (nfix m)))
             (equal (aignet-nxsts-aux n (append (aignet-nxsts-aux m x) rest))
                    (aignet-nxsts-aux n x))))

  (local (defthm foo
           (implies (equal (+ a b) c)
                    (equal (+ a b (- c)) 0))))


  (defthm aignet-nxsts-aux-of-cons
    (implies (<= (nfix n) (stype-count :reg x))
             (equal (aignet-nxsts-aux n (cons node x))
                    (if (and (equal (stype node) :nxst)
                             (< (nxst-node->reg node) (nfix n)))
                        (update-nth (- (nfix n) (+ 1 (nxst-node->reg node)))
                                    (nxst-node (aignet-lit-fix (nxst-node->fanin node)
                                                               x)
                                               (nxst-node->reg node))
                                    (aignet-nxsts-aux n x))
                      (aignet-nxsts-aux n x))))
    :hints(("Goal" :in-theory (enable lookup-reg->nxst update-nth
                                      aignet-lit-fix aignet-id-fix aignet-idp)))))

(define aignet-nxsts ((aignet node-listp))
  :returns (nxsts node-listp)
  (aignet-nxsts-aux (stype-count :reg aignet) aignet)
  ///
  (defret fanin-count-of-aignet-nxsts
    (equal (fanin-count nxsts) 0))

  (defret lookup-id-of-aignet-nxsts
    (equal (lookup-id k nxsts) nil))

  (defret stype-count-of-aignet-nxsts
    (equal (stype-count stype nxsts)
           (if (equal (stype-fix stype) :nxst)
               (stype-count :reg aignet)
             0)))

  (fty::deffixequiv aignet-nxsts)



  (defret lookup-stype-of-aignet-nxsts
    (implies (not (equal (stype-fix stype) :nxst))
             (equal (lookup-stype k stype nxsts) nil)))

  (defret lookup-reg->nxst-of-aignet-nxsts
    (implies (and (<= (fanin-count aignet) (fanin-count rest))
                  (<= (stype-count :reg aignet) (stype-count :reg rest)))
             (equal (lookup-reg->nxst k (append nxsts rest))
                    (if (< (nfix k) (stype-count :reg aignet))
                        (lookup-reg->nxst k aignet)
                      (lookup-reg->nxst k rest)))))

  (defthm aignet-nxsts-of-append-aignet-nxsts
    (implies (and (equal (stype-count :reg x) (stype-count :reg rest))
                  (<= (fanin-count x) (fanin-count rest)))
             (equal (aignet-nxsts (append (aignet-nxsts x) rest))
                    (aignet-nxsts x))))

  (defthm aignet-nxsts-of-cons
    (equal (aignet-nxsts (cons node x))
           (cond ((and (equal (stype node) :nxst)
                       (< (nxst-node->reg node) (stype-count :reg x)))
                  (update-nth (- (stype-count :reg x) (+ 1 (nxst-node->reg node)))
                              (nxst-node (aignet-lit-fix (nxst-node->fanin node)
                                                         x)
                                         (nxst-node->reg node))
                              (aignet-nxsts x)))
                 ((equal (stype node) :reg)
                  (cons (nxst-node (make-lit (+ 1 (fanin-count x)) 0)
                                   (stype-count :reg x))
                        (aignet-nxsts x)))
                 (t (aignet-nxsts x))))
    :hints(("Goal" :in-theory (enable aignet-nxsts-aux
                                      lookup-reg->nxst)))))


(define aignet-norm ((aignet node-listp))
  :returns (norm node-listp)
  (append (aignet-nxsts aignet)
          (aignet-outputs aignet)
          (aignet-fanins aignet))
  ///
  (defret fanin-count-of-aignet-norm
    (equal (fanin-count norm) (fanin-count aignet)))



  (local (FTY::DEFFIXTYPE STYPEP
           :PRED STYPEP
           :FIX STYPE-FIX
           :EQUIV STYPE-EQUIV
           :DEFINE T :forward t))

  (defret stype-count-of-aignet-norm
    (implies (not (equal (stype-fix stype) :nxst))
             (equal (stype-count stype norm)
                    (stype-count stype aignet)))
    :hints (("Goal" :cases ((equal (stype-fix stype) :const)
                            (equal (stype-fix stype) :xor)
                            (equal (stype-fix stype) :and)
                            (equal (stype-fix stype) :pi)
                            (equal (stype-fix stype) :reg)
                            (equal (stype-fix stype) :po))
             :in-theory (enable ctype))))

  ;; (defret car-lookup-id-of-aignet-norm
  ;;   (equal (car (lookup-id n norm))
  ;;          (car (lookup-id n aignet))))

  ;; (defret lookup-id-fanin-of-aignet-norm
  ;;   (equal (fanin ftype (lookup-id n norm))
  ;;          (fanin ftype (lookup-id n aignet)))
  ;;   :hints(("Goal" :in-theory (enable fanin
  ;;                                     aignet-lit-fix
  ;;                                     aignet-id-fix
  ;;                                     aignet-idp))))

  (defret lookup-id-of-aignet-norm
    (equal (lookup-id n norm)
           (aignet-fanins (lookup-id n aignet))))

  (defret lookup-reg-of-aignet-norm
    (equal (lookup-stype n :reg norm)
           (aignet-fanins (lookup-stype n :reg aignet))))

  (defret lookup-pi-of-aignet-norm
    (equal (lookup-stype n :pi norm)
           (aignet-fanins (lookup-stype n :pi aignet))))

  (defret po-fanin-of-aignet-norm
    (equal (fanin 0 (lookup-stype n :po norm))
           (fanin 0 (lookup-stype n :po aignet)))
    :hints (("goal" :cases ((< (nfix n) (stype-count :po aignet)))
             :in-theory (enable fanin
                                aignet-lit-fix
                                aignet-id-fix
                                aignet-idp))))

  (defret lookup-reg->nxst-of-aignet-norm
    (equal (lookup-reg->nxst n norm)
           (lookup-reg->nxst n aignet))
    :hints(("Goal" :in-theory (enable lookup-reg->nxst-out-of-bounds))))

  ;; (defret fanin-count-of-lookup-id-of-aignet-norm
  ;;   (equal (fanin-count (lookup-id n norm))
  ;;          (fanin-count (lookup-id n aignet))))

  (defthm aignet-norm-idempotent
    (equal (aignet-norm (aignet-norm x))
           (aignet-norm x)))

  (defthm aignet-norm-of-cons
    (equal (aignet-norm (cons node (aignet-norm x)))
           (aignet-norm (cons node x)))
    :hints(("Goal" :in-theory (enable aignet-lit-fix
                                      aignet-id-fix
                                      aignet-idp)))))

(define aignet-norm-p (x)
  (equal (ec-call (aignet-norm x)) x)
  ///
  (defthm aignet-norm-p-of-aignet-norm
    (aignet-norm-p (aignet-norm x)))

  (defthmd aignet-norm-when-aignet-norm-p
    (implies (aignet-norm-p x)
             (equal (aignet-norm x) x)))

  (fty::deffixtype aignet-norm :pred aignet-norm-p :fix aignet-norm :equiv aignet-equiv
    :define t :forward t)

  (defrefinement node-list-equiv aignet-equiv))


(defsection aignet-equiv

  (fty::deffixcong aignet-equiv equal (fanin-count x) x)
  (fty::deffixcong aignet-equiv equal (stype-count :po x) x
    :basename po-count)

  (fty::deffixcong aignet-equiv equal (car (lookup-id n x)) x
    :basename car-lookup-id)
  (fty::deffixcong aignet-equiv equal (stype-count :pi (lookup-id n x)) x
    :basename pi-count-of-lookup-id)
  (fty::deffixcong aignet-equiv equal (stype-count :reg (lookup-id n x)) x
    :basename reg-count-of-lookup-id)
  (fty::deffixcong aignet-equiv equal (lookup-reg->nxst n x) x)
  (fty::deffixcong aignet-equiv equal (fanin 0 (lookup-stype n :po x)) x
    :basename po-fanin)
  (fty::deffixcong aignet-equiv equal (stype-count :reg x) x
    :basename reg-count)
  (fty::deffixcong aignet-equiv equal (stype-count :pi x) x
    :basename pi-count)
  (fty::deffixcong aignet-equiv equal (stype-count :and x) x
    :basename and-count)
  (fty::deffixcong aignet-equiv equal (stype-count :xor x) x
    :basename xor-count)
  (fty::deffixcong aignet-equiv equal (stype-count :const x) x
    :basename const-count)
  (fty::deffixcong aignet-equiv equal (stype-count :pi (cdr (lookup-id n x))) x
    :basename pi-number)
  (fty::deffixcong aignet-equiv equal (stype-count :reg (cdr (lookup-id n x))) x
    :basename reg-number)
  (fty::deffixcong aignet-equiv equal (fanin-count (lookup-stype n :reg x)) x
    :basename reg-id)
  (fty::deffixcong aignet-equiv equal (fanin-count (lookup-stype n :pi x)) x
    :basename pi-id))
