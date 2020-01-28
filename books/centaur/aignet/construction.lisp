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
(include-book "semantics")
(include-book "deps")
(include-book "axi-reductions")
(include-book "centaur/fty/bitstruct" :dir :system)
(local (include-book "tools/trivial-ancestors-check" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
;; (local (include-book "data-structures/list-defthms" :dir :system))
(local (in-theory (enable* acl2::arith-equiv-forwarding)))
(local (in-theory (disable nth update-nth
                           acl2::nfix-when-not-natp
                           resize-list
                           ;; acl2::resize-list-when-empty
                           ;; acl2::make-list-ac-redef
                           ;; set::double-containment
                           ;; set::sets-are-true-lists
                           make-list-ac)))

(local (in-theory (disable BITOPS::commutativity-of-b-xor
                           BITOPS::BXOR-TO-BNOT
                           BITOPS::BXOR-TO-ID
                           BITOPS::B-AND-EQUAL-1-IN-HYP)))

(local (acl2::use-trivial-ancestors-check))
(local (std::add-default-post-define-hook :fix))

(local (in-theory (disable unsigned-byte-p)))

(local (defthm unsigned-byte-p-of-lit->var
         (implies (and (unsigned-byte-p (+ 1 n) (lit-fix lit))
                       (natp n))
                  (unsigned-byte-p n (lit->var lit)))
         :hints(("Goal" :in-theory (enable lit->var)))))

(local (defthmd unsigned-byte-p-of-lit-when-lit->var
         (implies (and (unsigned-byte-p (+ -1 n) (lit->var lit))
                       (litp lit)
                       (posp n))
                  (unsigned-byte-p n lit))
         :hints(("Goal" :in-theory (enable lit->var)))
         :rule-classes ((:rewrite :backchain-limit-lst (3 nil nil)))))

(local (add-macro-alias aignet-litp aignet-idp))

(local (defthm unsigned-byte-p-of-lit->var-when-aignet-litp
         (implies (and (aignet-litp lit aignet)
                       (< (fanin-count aignet) #x1fffffff))
                  (unsigned-byte-p 29 (lit->var lit)))
         :hints(("Goal" :in-theory (enable aignet-litp unsigned-byte-p)))))

(local (defthm unsigned-byte-p-when-aignet-litp
         (implies (and (aignet-litp lit aignet)
                       (litp lit)
                       (< (fanin-count aignet) #x1fffffff))
                  (unsigned-byte-p 30 lit))
         :hints(("Goal" :in-theory (enable unsigned-byte-p-of-lit-when-lit->var)))))

(local (defthm unsigned-byte-p-32-when-aignet-litp
         (implies (and (aignet-litp lit aignet)
                       (litp lit)
                       (< (fanin-count aignet) #x1fffffff))
                  (unsigned-byte-p 32 lit))
         :hints(("Goal" :use unsigned-byte-p-when-aignet-litp
                 :in-theory (disable unsigned-byte-p-when-aignet-litp)))))

(local (defthmd unsigned-byte-p-when-bit
         (implies (and (bitp x)
                       (posp n))
                  (unsigned-byte-p n x))
         :hints(("Goal" :in-theory (enable bitp)))))
                  

(local (defthm unsigned-byte-p-of-lit-negate
         (implies (and (unsigned-byte-p n (lit-fix x))
                       (posp n))
                  (unsigned-byte-p n (lit-negate x)))
         :hints(("Goal" :in-theory (enable lit-negate make-lit lit->var
                                           unsigned-byte-p-when-bit)))))

(local (defthm unsigned-byte-p-of-fanin
         (implies (< (fanin-count aignet) #x1fffffff)
                  (unsigned-byte-p 30 (fanin type (lookup-id id aignet))))
         :hints(("Goal" :use ((:instance unsigned-byte-p-when-aignet-litp
                               (lit (fanin type (lookup-id id aignet)))))
                 :in-theory (disable unsigned-byte-p-when-aignet-litp)))))

(local (defthm unsigned-byte-p-32-of-fanin
         (implies (< (fanin-count aignet) #x1fffffff)
                  (unsigned-byte-p 32 (fanin type (lookup-id id aignet))))
         :hints(("Goal" :use ((:instance unsigned-byte-p-of-fanin))
                 :in-theory (disable unsigned-byte-p-of-fanin)))))

(defmacro =30 (a b)
  `(eql (the (unsigned-byte 30) ,a)
        (the (unsigned-byte 30) ,b)))

(defmacro =2 (a b)
  `(eql (the (unsigned-byte 2) ,a)
        (the (unsigned-byte 2) ,b)))

(defmacro =b (a b)
  `(eql (the bit ,a)
        (the bit ,b)))

(defmacro <29 (a b)
  `(< (the (unsigned-byte 29) ,a)
      (the (unsigned-byte 29) ,b)))
                  

(define two-id-measure ((x natp) (y natp))
  :returns (meas o-p)
  :prepwork ((local (in-theory (enable natp))))
  (let ((x (nfix x))
        (y (nfix y)))
    (acl2::two-nats-measure
     (+ 1 (max x y))
     (+ 1 (min x y))))
  ///
  (defthm two-id-measure-symm
    (equal (two-id-measure id1 id2)
           (two-id-measure id2 id1)))

  (local (in-theory (enable aignet-idp)))

  ;; (defthm two-id-measure-of-gate
  ;;   (implies (and (equal (id->type id1 aignet) (gate-type))
  ;;                 (aignet-idp id1 aignet))
  ;;            (b* (((cons node rest) (lookup-id id1 aignet))
  ;;                 (ch1 (aignet-lit-fix (gate-node->fanin0 node) rest))
  ;;                 (ch2 (aignet-lit-fix (gate-node->fanin1 node) rest)))
  ;;              (and (o< (two-id-measure id2 (lit->var^ ch1))
  ;;                       (two-id-measure id1 id2))
  ;;                   (o< (two-id-measure id2 (lit->var^ ch2))
  ;;                       (two-id-measure id1 id2))
  ;;                   (o< (two-id-measure id2 (lit->var^ ch1))
  ;;                       (two-id-measure id2 id1))
  ;;                   (o< (two-id-measure id2 (lit->var^ ch2))
  ;;                       (two-id-measure id2 id1))))))
  
  (defthm two-id-measure-of-fanin
    (implies (and (equal (id->type id1 aignet) (gate-type))
                  (aignet-idp id1 aignet))
             (b* ((ch1 (fanin ftype (lookup-id id1 aignet))))
               (and (o< (two-id-measure id2 (lit-id ch1))
                        (two-id-measure id1 id2))
                    (o< (two-id-measure id2 (lit-id ch1))
                        (two-id-measure id2 id1))))))

  ;; (defthm two-id-measure-of-fanin
  ;;   (implies (and (aignet-nodes-ok aignet)
  ;;                 (equal (id->type id1 aignet) (out-type))
  ;;                 (aignet-idp id1 aignet))
  ;;            (b* ((ch1 (fanin ftype (lookup-id id1 aignet))))
  ;;              (and (o< (two-id-measure id2 (lit-id ch1))
  ;;                       (two-id-measure id1 id2))
  ;;                   (o< (two-id-measure id2 (lit-id ch1))
  ;;                       (two-id-measure id2 id1))))))
  )







(local (defthm maybe-bitp-compound-recognizer
         (equal (maybe-bitp x)
                (or (equal x 1)
                    (equal x 0)
                    (equal x nil)))
         :rule-classes :compound-recognizer))


(defsection maybe-litp
  :parents (litp)
  :short "Recognizer for lits and @('nil')."
  :long "<p>This is like an <a
href='https://en.wikipedia.org/wiki/Option_type'>option type</a>; when @('x')
satisfies @('maybe-litp'), then either it is a @(see litp) or nothing.</p>"

  (defund-inline maybe-litp (x)
    (declare (xargs :guard t))
    (or (not x)
        (litp x)))

  (local (in-theory (enable maybe-litp)))

  (defthm maybe-litp-compound-recognizer
    (equal (maybe-litp x)
           (or (not x)
               (litp x)))
    :rule-classes :compound-recognizer))

(defsection maybe-lit-fix
  :parents (fty::basetypes maybe-litp)
  :short "@(call maybe-lit-fix) is the identity for @(see maybe-litp)s, or
  coerces any non-@(see litp) to @('nil')."
  :long "<p>Performance note.  In the execution this is just an inlined
  identity function, i.e., it should have zero runtime cost.</p>"

  (defund-inline maybe-lit-fix (x)
    (declare (xargs :guard (maybe-litp x)
                    :guard-hints (("Goal" :in-theory (e/d (maybe-litp)
                                                          ())))))
    (mbe :logic (if x (lit-fix x) nil)
         :exec x))

  (local (in-theory (enable maybe-litp maybe-lit-fix)))

  (defthm maybe-litp-of-maybe-lit-fix
    (maybe-litp (maybe-lit-fix x))
    :rule-classes (:rewrite :type-prescription))

  (defthm maybe-lit-fix-when-maybe-litp
    (implies (maybe-litp x)
             (equal (maybe-lit-fix x) x)))

  (defthm maybe-lit-fix-under-iff
    (iff (maybe-lit-fix x) x))

  (defthm maybe-lit-fix-under-lit-equiv
    (lit-equiv (maybe-lit-fix x) x)
    :hints(("Goal" :in-theory (enable maybe-lit-fix)))))


(fty::defbitstruct simpcode
  ((neg bitp)
   (xor bitp)
   (identity bitp)
   (choice bitp)))

(defmacro simpcode! (key)
  (case key
    ((nil) nil)
    (:and 0)
    (:nand 1)
    (:xor 2)
    (:xnor 3)
    (:existing 4)
    (:nexisting 5)
    (:andchoice 8)
    (:nandchoice 9)
    (:xorchoice 10)
    (:xnorchoice 11)))

(define simpcode-negate ((x simpcode-p))
  :enabled t
  :inline t
  :prepwork ((local (include-book "centaur/bitops/equal-by-logbitp" :dir :system)))
  :guard-hints (("goal" :in-theory (enable !simpcode->neg simpcode->neg))
                (logbitp-reasoning)
                (and stable-under-simplificationp
                     '(:expand ((loghead 1 x) (logbitp 0 x)))))
  (mbe :logic (!simpcode->neg (b-not (simpcode->neg x)) x)
       :exec (logxor 1 (the (unsigned-byte 4) (simpcode-fix x)))))

(define simpcode-negate-cond ((x simpcode-p) (neg bitp))
  :enabled t
  :inline t
  :prepwork ((local (include-book "centaur/bitops/equal-by-logbitp" :dir :system)))
  :guard-hints (("goal" :in-theory (enable !simpcode->neg simpcode->neg))
                (logbitp-reasoning)
                (and stable-under-simplificationp
                     '(:expand ((loghead 1 x) (logbitp 0 x)))))
  (mbe :logic (!simpcode->neg (b-xor neg (simpcode->neg x)) x)
       :exec (logxor neg (the (unsigned-byte 4) (simpcode-fix x)))))

(local (defthm b-xor-of-b-not
         (and (equal (b-xor (b-not x) y) (b-not (b-xor x y)))
              (equal (b-xor x (b-not y)) (b-not (b-xor x y))))
         :hints(("Goal" :in-theory (enable b-not)))))

(local (defthm b-xor-associative
         (equal (b-xor (b-xor x y) z)
                (b-xor x (b-xor y z)))
         :hints(("Goal" :in-theory (enable b-xor)))))
(local (defthm b-xor-commutative2
         (equal (b-xor y (b-xor x z))
                (b-xor x (b-xor y z)))
         :hints(("Goal" :in-theory (enable b-xor)))))
(local (defthm b-xor-identity
         (equal (b-xor a (b-xor a b))
                (bfix b))
         :hints(("Goal" :in-theory (enable b-xor)))))


(define simpcode-eval ((code simpcode-p)
                       (x0 litp)
                       (x1 litp)
                       invals regvals aignet)
  :guard (and (fanin-litp x0 aignet)
              (fanin-litp x1 aignet)
              (<= (num-ins aignet) (bits-length invals))
              (<= (num-regs aignet) (bits-length regvals)))
  :returns (ans bitp :rule-classes :type-prescription)
  (b* (((simpcode code))
       ((when (eql 1 code.identity))
        (b-xor code.neg (lit-eval x0 invals regvals aignet)))
       ((when (eql 1 code.xor))
        (b-xor code.neg (eval-xor-of-lits x0 x1 invals regvals aignet))))
    (b-xor code.neg (eval-and-of-lits x0 x1 invals regvals aignet)))
  ///
  (defret simpcode-eval-of-constant-code
    (implies (syntaxp (quotep code))
             (equal ans
                    (b* (((simpcode code))
                         ((when (eql 1 code.identity))
                          (b-xor code.neg (lit-eval x0 invals regvals aignet)))
                         ((when (eql 1 code.xor))
                          (b-xor code.neg (eval-xor-of-lits x0 x1 invals regvals aignet))))
                      (b-xor code.neg (eval-and-of-lits x0 x1 invals regvals aignet))))))

  (defthm simpcode-eval-of-!simpcode->neg
    (equal (simpcode-eval (!simpcode->neg neg code) x0 x1 invals regvals aignet)
           (b-xor neg (b-xor (simpcode->neg code)
                             (simpcode-eval code x0 x1 invals regvals aignet)))))

  (defthm simpcode-eval-of-!simpcode->choice
    (equal (simpcode-eval (!simpcode->choice choice code) x0 x1 invals regvals aignet)
           (simpcode-eval code x0 x1 invals regvals aignet))))

(fty::defoption maybe-simpcode simpcode)



(defsection gatesimp

  (define gatesimp-level-p (x)
    (and (natp x) (<= x 4))
    ///
    (define gatesimp-level-fix ((x gatesimp-level-p))
      :returns (new-x gatesimp-level-p)
      (mbe :logic (if (gatesimp-level-p x) x 4)
           :exec x)
      ///
      (defret gatesimp-level-fix-when-gatesimp-level-p
        (implies (gatesimp-level-p x) (equal new-x x)))

      (fty::deffixtype gatesimp-level :pred gatesimp-level-p :fix gatesimp-level-fix :equiv gatesimp-level-equiv
        :define t))

    (defthm gatesimp-level-p-compound-recognizer
      (implies (gatesimp-level-p x)
               (natp x))
      :rule-classes :compound-recognizer))

  (local (defthm unsigned-byte-p-when-gatesimp-level-p
           (implies (gatesimp-level-p x)
                    (unsigned-byte-p 3 x))
           :hints(("Goal" :in-theory (enable gatesimp-level-p unsigned-byte-p)))))

  (local (defthm bound-when-gatesimp-level-p
           (implies (gatesimp-level-p x)
                    (<= x 4))
           :hints(("Goal" :in-theory (enable gatesimp-level-p unsigned-byte-p)))))

  (define gatesimp-xor-mode-p (x)
    (and (natp x) (<= x 2))
    ///
    (define gatesimp-xor-mode-fix ((x gatesimp-xor-mode-p))
      :returns (new-x gatesimp-xor-mode-p)
      (mbe :logic (if (gatesimp-xor-mode-p x) x 2)
           :exec x)
      ///
      (defret gatesimp-xor-mode-fix-when-gatesimp-xor-mode-p
        (implies (gatesimp-xor-mode-p x) (equal new-x x)))

      (fty::deffixtype gatesimp-xor-mode :pred gatesimp-xor-mode-p :fix gatesimp-xor-mode-fix :equiv gatesimp-xor-mode-equiv
        :define t))

    (defthm gatesimp-xor-mode-p-compound-recognizer
      (implies (gatesimp-xor-mode-p x)
               (natp x))
      :rule-classes :compound-recognizer))

  (local (defthm unsigned-byte-p-when-gatesimp-xor-mode-p
           (implies (gatesimp-xor-mode-p x)
                    (unsigned-byte-p 2 x))
           :hints(("Goal" :in-theory (enable gatesimp-xor-mode-p unsigned-byte-p)))))

  (local (defthm bound-when-gatesimp-xor-mode-p
           (implies (gatesimp-xor-mode-p x)
                    (<= x 2))
           :hints(("Goal" :in-theory (enable gatesimp-xor-mode-p unsigned-byte-p)))))

  (fty::fixtype-to-bitstruct gatesimp-level :width 3)
  (fty::fixtype-to-bitstruct gatesimp-xor-mode :width 2)

  (fty::defbitstruct gatesimp
  :parents (aignet-construction)
  :short "Structure encoding AIGNET construction settings for how much to try to
          simplify and whether to use hashing"
  :long "<p>A simple bit-encoded triple of @('level'), @('hashp'), and @('xor-mode').</p>

<p>The @('level') field is a value between 0 and 4 inclusive, determining how
hard to work to simplify new nodes.  The numbers corresponding to the levels of
simplification found in the paper:</p>
<blockquote>
R. Brummayer and A. Biere.  Local two-level And-Inverter Graph minimization
without blowup.  Proc. MEMCIS 6 (2006): 32-38,
</blockquote>

<p>The @('xor-mode') field is a value between 0 and 2 inclusive, determining
whether to use XOR nodes:</p>
<ul>
<li>If 2, XOR nodes can be created using @(see aignet-hash-xor) and
additionally, if the @('level') is 3 or greater, derived when creating the AND
of two nodes of the form @('(not (and a b))'), @('(not (and (not a) (not
b)))').</li>
<li>If 1, XOR nodes will be created when calling @(see aignet-hash-xor), but
not derived from existing AND gates.</li>
<li>If 0, no XOR nodes will be used even when calling @(see aignet-hash-xor),
instead implementing the function using AND gates.</li>
</ul>

<p>The @('hashp') field is a Boolean and determines whether structural hashing
is used.</p>

<p>To construct a gatesimp object, use either the constructor function
@('gatesimp') or the macro @('make-gatesimp'), with the usual conventions of
product types produced by @(see fty::defprod) and @(see fty::defbitstruct).</p>"

    ((hashp booleanp :default t)
     (level gatesimp-level :default 4)
     (xor-mode gatesimp-xor-mode :default 2)))

  (defthm gatesimp->level-bound
    (<= (gatesimp->level x) 4)
    :rule-classes (:rewrite :linear))

  (defthm gatesimp->xor-mode-bound
    (<= (gatesimp->xor-mode x) 2)
    :rule-classes (:rewrite :linear))

  (make-event
   `(define default-gatesimp ()
      :enabled t
      ;; not inlined, so it can be redefined
      ',(make-gatesimp))))
  

;; Signature for the various simplifiers:
;; Function name says the shape of term on which it must be called.
;; Inputs are the literals.  Outputs are either:
;;   (existing maybe-litp)  for a function that can only produce an existing literal
;; or:
;; (mv (simp-flag simp-flag-p)
;;     (new-lit1 litp)
;;     (new-lit2 litp))
;; Simp-flag says whether any simplification was achieved:
;; if NIL, none
;; if :existing, then new-lit1 has the correct function
;; if :xor, then the XOR of new-lit1, new-lit2 has the correct function
;; if :and, then the AND of new-lit1, new-lit2 has the correct function.
;; if :nand, then the NOT AND of new-lit1, new-lit2 has the correct function.
;; Literal names: x0, x1 signify the literals of the top-level operator
;;                y0, y1, y2, y3 signify the literals of (resp.) the left and right sub-operations.
;; I.e., in an expression (and (not (and a b)) (xor c d))
;;             then x0 would be (not (and a b))
;;                  x1          (xor c d))
;;                  y0          a
;;                  y1          b
;;                  y2          c
;;                  y3          d.


(define gate-reduce-check-template (x)
  :mode :program :hooks nil
  (b* (((unless (axi-term-p x))
        "Not a valid AXI term"))
    (axi-term-case x
      :const "Template can't be a constant"
      :var "Template can't be a variable"
      :gate (b* (((axi-lit x.left))
                 ((axi-lit x.right)))
              (or (axi-term-case x.left.abs
                    :const "Template can't contain a constant"
                    :var (if (eq x.left.abs.name 'x0)
                             nil
                           "Variable for left input must be x0")
                    :gate (b* (((axi-lit x.left.abs.left))
                               ((axi-lit x.left.abs.right)))
                            (or (axi-term-case x.left.abs.left.abs
                                  :const "Template can't contain a constant"
                                  :var (if (eq x.left.abs.left.abs.name 'y0)
                                           nil
                                         "Variable for left-left input must be y0")
                                  :gate "Gate nesting too deep")
                                (axi-term-case x.left.abs.right.abs
                                  :const "Template can't contain a constant"
                                  :var (if (eq x.left.abs.right.abs.name 'y1)
                                           nil
                                         "Variable for left-right input must be yy")
                                  :gate "Gate nesting too deep"))))
                  (axi-term-case x.right.abs
                    :const "Template can't contain a constant"
                    :var (if (eq x.right.abs.name 'x1)
                             nil
                           "Variable for right input must be x0")
                    :gate (b* (((axi-lit x.right.abs.left))
                               ((axi-lit x.right.abs.right)))
                            (or (axi-term-case x.right.abs.left.abs
                                  :const "Template can't contain a constant"
                                  :var (if (eq x.right.abs.left.abs.name 'y2)
                                           nil
                                         "Variable for right-left input must be y2")
                                  :gate "Gate nesting too deep")
                                (axi-term-case x.right.abs.right.abs
                                  :const "Template can't contain a constant"
                                  :var (if (eq x.right.abs.right.abs.name 'y3)
                                           nil
                                         "Variable for right-right input must be y3")
                                  :gate "Gate nesting too deep")))))))))
                          

(define axi-term-vars ((x axi-term-p))
  :measure (axi-term-count x)
  (axi-term-case x
    :const nil
    :var (list x.name)
    :gate (b* (((axi-lit x.left))
               ((axi-lit x.right)))
            (append (axi-term-vars x.left.abs)
                    (axi-term-vars x.right.abs)))))

(defun apply-template-to-lits (lits term)
  (if (atom lits)
      nil
    (cons (subst (car lits) 'x term)
          (apply-template-to-lits (cdr lits) term))))

;; (defun substitute-lits (lits all-lits)
;;   (if (atom lits)
;;       nil
;;     (cons (case (car lits)
;;             (y0 (if (member 'x0 all-lits)
;;                     '(fanin :gate0 (lookup-id (lit-id x0) aignet))
;;                   'y0))
;;             (y1 (if (member 'x0 all-lits)
;;                     '(fanin :gate1 (lookup-id (lit-id x0) aignet))
;;                   'y1))
;;             (y2 (if (member 'x1 all-lits)
;;                     '(fanin :gate0 (lookup-id (lit-id x1) aignet))
;;                   'y2))
;;             (y3 (if (member 'x1 all-lits)
;;                     '(fanin :gate1 (lookup-id (lit-id x1) aignet))
;;                   'y3))
;;             (t (car lits)))
;;           (substitute-lits (cdr lits) all-lits))))

(define axi-template-aignet-reqs ((x axi-term-p) (lits true-listp))
  :guard (not (gate-reduce-check-template x))
  :guard-hints (("goal" :in-theory (enable gate-reduce-check-template)))
  :mode :program :hooks nil
  (b* (((axi-lit x0) (axi-gate->left x))
       ((axi-lit x1) (axi-gate->right x)))
    (append (and (member 'x0 lits)
                 (axi-term-case x0.abs
                   :var nil :const nil
                   :gate ;; (append '((equal (ctype (stype (car (lookup-id (lit-id x0) aignet)))) :gate)
                         ;;           (equal y0 (fanin :gate0 (lookup-id (lit-id x0) aignet)))
                         ;;           (equal y1 (fanin :gate1 (lookup-id (lit-id x0) aignet))))
                         ;;         `((equal (regp (stype (car (lookup-id (lit-id x0) aignet))))
                         ;;                  ,(if (eq x0.abs.op 'and) 0 1))
                         ;;           (equal ,(if x0.negp 1 0) (lit->neg^ x0))))
                   (b* ((spec `(,(if (eq x0.abs.op 'and) 'eval-and-of-lits 'eval-xor-of-lits)
                                y0 y1 invals regvals aignet)))
                     `((equal (lit-eval x0 invals regvals aignet)
                              ,(if x0.negp `(b-not ,spec) spec))))))
            (and (member 'x1 lits)
                 (axi-term-case x1.abs
                   :var nil :const nil
                   :gate ;; (append '((equal (ctype (stype (car (lookup-id (lit-id x1) aignet)))) :gate)
                         ;;           (equal y2 (fanin :gate0 (lookup-id (lit-id x1) aignet)))
                         ;;           (equal y3 (fanin :gate1 (lookup-id (lit-id x1) aignet))))
                         ;;         `((equal (regp (stype (car (lookup-id (lit-id x1) aignet))))
                         ;;                  ,(if (eq x1.abs.op 'and) 0 1))
                         ;;           (equal ,(if x1.negp 1 0) (lit->neg^ x1))))
                   
                   (b* ((spec `(,(if (eq x1.abs.op 'and) 'eval-and-of-lits 'eval-xor-of-lits)
                                y2 y3 invals regvals aignet)))
                     `((equal (lit-eval x1 invals regvals aignet)
                              ,(if x1.negp `(b-not ,spec) spec)))))))))

(define axi-template-correctness-term ((x axi-term-p) (lits true-listp))
  :guard (not (gate-reduce-check-template x))
  :guard-hints (("goal" :in-theory (enable gate-reduce-check-template)))
  :mode :program :hooks nil
  (b* (((axi-lit x0) (axi-gate->left x))
       ((axi-lit x1) (axi-gate->right x))
       (op (axi-gate->op x)))
    `(,(if (eq op 'and) 'b-and 'b-xor)
      ,(if (member 'x0 lits)
           '(lit-eval x0 invals regvals aignet)
         (b* ((abs
               (axi-term-case x0.abs
                 :const 0 ;; nonsense
                 :var x0.abs.name
                 :gate `(,(if (eq x0.abs.op 'and) 'b-and 'b-xor)
                         (lit-eval y0 invals regvals aignet)
                         (lit-eval y1 invals regvals aignet)))))
           (if x0.negp `(b-not ,abs) abs)))
      ,(if (member 'x1 lits)
           '(lit-eval x1 invals regvals aignet)
         (b* ((abs
               (axi-term-case x1.abs
                 :const 0 ;; nonsense
                 :var x1.abs.name
                 :gate `(,(if (eq x1.abs.op 'and) 'b-and 'b-xor)
                         (lit-eval y2 invals regvals aignet)
                         (lit-eval y3 invals regvals aignet)))))
           (if x1.negp `(b-not ,abs) abs))))))
                     

(defmacro def-gatesimp-thms (lits &key eval-hints
                                  measure-hints
                                  no-measure
                                  (maybe-simpcode 't)
                                  (eval-hyp 't)
                                  (syntax-hyp 't)
                                  (measure-hyp 't)
                                  (choice 'nil)
                                  (choice-hyp 't)
                                  (width-hyp 't)
                                  (no-bound 'nil)
                                  eval-spec
                                  use-aignet)
  `(progn
     (defret width-of-<fn>
       (implies (and ,width-hyp
                     ,@(apply-template-to-lits lits '(unsigned-byte-p 30 (lit-fix x))))
                (and (unsigned-byte-p 30 new0)
                     (unsigned-byte-p 30 new1)
                     ,@(and choice
                            `((unsigned-byte-p 30 new2)
                              (unsigned-byte-p 30 new3))))))

     ,@(and (not no-bound)
            `((defret bound-of-<fn>
                (implies (and ,@(apply-template-to-lits lits '(< (lit-id x) gate))
                              ,@(and use-aignet
                                     (apply-template-to-lits lits '(aignet-litp x aignet)))
                              (natp gate))
                         (and (< (lit-id new0) gate)
                              (< (lit-id new1) gate)
                              ,@(and choice
                                     `((< (lit-id new2) gate)
                                       (< (lit-id new3) gate))))))))

     ,@(and (not no-measure)
            `((defret two-id-measure-of-<fn>
                (implies (and ,@(and maybe-simpcode '(code))
                              (equal 0 (simpcode->identity code))
                              ,@(and (member 'x0 lits) '((equal (lit-id x0) id0)))
                              ,@(and (member 'x1 lits) '((equal (lit-id x1) id1)))
                              ,@(and (member 'y0 lits) '((< (lit-id y0) (nfix id0))))
                              ,@(and (member 'y1 lits) '((< (lit-id y1) (nfix id0))))
                              ,@(and (member 'y2 lits) '((< (lit-id y2) (nfix id1))))
                              ,@(and (member 'y3 lits) '((< (lit-id y3) (nfix id1))))
                              ,measure-hyp
                              ,@(and use-aignet
                                     (apply-template-to-lits lits '(aignet-litp x aignet))))
                         (and (o< (two-id-measure (lit-id new0) (lit-id new1))
                                  (two-id-measure id0 id1))
                              (o< (two-id-measure (lit-id new0) (lit-id new1))
                                  (two-id-measure id1 id0))
                              ,@(and choice
                                     `((o< (two-id-measure (lit-id new2) (lit-id new3))
                                           (two-id-measure id0 id1))
                                       (o< (two-id-measure (lit-id new2) (lit-id new3))
                                           (two-id-measure id1 id0))))))
                :hints ,(or measure-hints
                            '((and stable-under-simplificationp
                                   '(:in-theory (enable two-id-measure))))))))

     (defret aignet-litp-of-<fn>
       (implies (and ,@(apply-template-to-lits lits '(aignet-litp x aignet)))
                (and (aignet-litp new0 aignet)
                     (aignet-litp new1 aignet)
                     ,@(and choice
                            `((aignet-litp new2 aignet)
                              (aignet-litp new3 aignet))))))

     (defret deps-of-<fn>
       (implies (and ,@(apply-template-to-lits lits '(not (depends-on (lit->var x) ci-id aignet)))
                     ,syntax-hyp
                     ;; ,@(and maybe-simpcode '(code))
                     )
                (and (not (depends-on (lit->var new0) ci-id aignet))
                     (not (depends-on (lit->var new1) ci-id aignet))
                     ,@(and choice
                            `((not (depends-on (lit->var new2) ci-id aignet))
                              (not (depends-on (lit->var new3) ci-id aignet)))))))

     

     ,@(and (not choice)
            `((defret choice-of-<fn>
                (implies (and ,choice-hyp)
                         (equal (simpcode->choice code) 0)))))

     (defret eval-of-<fn>
       (implies (and ,eval-hyp
                     ,syntax-hyp
                     ,@(and maybe-simpcode '(code)))
                (let ((spec ,eval-spec))
                  (and (equal (simpcode-eval code new0 new1 invals regvals aignet)
                              spec)
                       ,@(and choice
                              `((implies (equal (simpcode->choice code) 1)
                                         (equal (simpcode-eval code new2 new3 invals regvals aignet)
                                                spec)))))))
       :hints ,eval-hints)))

(defmacro def-gatesimp-thms-existing (lits &key eval-hints
                                           (eval-hyp 't)
                                           (syntax-hyp 't)
                                           eval-spec
                                           use-aignet)
  `(progn
     (defret width-of-<fn>
       (implies (and existing
                     ,@(apply-template-to-lits lits '(unsigned-byte-p 30 (lit-fix x))))
                (unsigned-byte-p 30 existing)))

     (defret bound-of-<fn>
       (implies (and existing
                     ,@(apply-template-to-lits lits '(< (lit-id x) gate))
                     ,@(and use-aignet
                            (apply-template-to-lits lits '(aignet-litp x aignet)))
                     (natp gate))
                (< (lit-id existing) gate)))

     (defret aignet-litp-of-<fn>
       (implies (and existing
                     ,@(apply-template-to-lits lits '(aignet-litp x aignet)))
                (aignet-litp existing aignet)))

     

     (defret deps-of-<fn>
       (implies (and ,@(apply-template-to-lits lits '(not (depends-on (lit->var x) ci-id aignet)))
                     ,syntax-hyp
                     ;; ,@(and maybe-simpcode '(code))
                     )
                (not (depends-on (lit->var existing) ci-id aignet))))

     (defret eval-of-<fn>
       (implies (and existing
                     ,eval-hyp
                     ,syntax-hyp)
                (equal (lit-eval existing invals regvals aignet)
                       ,eval-spec))
       :hints ,eval-hints)))


(define def-gate-reduce-fn (template body extra-lits extra-formals choice prepwork eval-hints level)
  :mode :program :hooks nil
  (b* ((err (gate-reduce-check-template template))
       ((when err) (raise "~s0: ~x1" err template))
       (lits (append extra-lits (axi-term-vars template)))
       ((mv & name-str)
        (if level
            (fmt1-to-string "SIMPLIFY-~x0-LEVEL-~x1" `((#\0 . ,template) (#\1 . ,level)) 0
                            :fmt-control-alist '((fmt-soft-right-margin . 2000)
                                                 (fmt-hard-right-margin . 2000)))
          (fmt1-to-string "SIMPLIFY-~x0" `((#\0 . ,template)) 0
                          :fmt-control-alist '((fmt-soft-right-margin . 2000)
                                               (fmt-hard-right-margin . 2000)))))
       (name (intern$ name-str "AIGNET"))
       (formals (append (apply-template-to-lits lits '(x litp :type (unsigned-byte 30)))
                        extra-formals))
       (existing-only (<= level 2)))
    `(define ,name ,formals
       :prepwork ,prepwork
       :returns ,(cond (existing-only
                        `(existing maybe-litp :rule-classes :type-prescription))
                       (t
                        `(mv (code maybe-simpcode-p)
                             (new0 litp :rule-classes :type-prescription)
                             (new1 litp :rule-classes :type-prescription)
                             ,@(and choice
                                    `((new2 litp :rule-classes :type-prescription)
                                      (new3 litp :rule-classes :type-prescription))))))
       (b* (,@(apply-template-to-lits lits '(x (lit-fix x))))
         ,body)
       ///
       ;; Note: Some level-2 reductions can only result in 0 or NIL.  Type
       ;; reasoning in these cases screws up our rewriting scheme; we don't
       ;; really want to know that it must be 0 if it's nonnil, so we disable
       ;; the type prescription rule.
       ,@(and existing-only
              `((in-theory (disable (:t ,name))))) 
       (,(if existing-only 'def-gatesimp-thms-existing 'def-gatesimp-thms)
        ,lits
        :eval-hints ,eval-hints
        :eval-hyp (and ,@(axi-template-aignet-reqs template lits))
        :eval-spec ,(axi-template-correctness-term template lits)
        ,@(and choice `(:choice ,choice)))

       (table gate-reduce-table '(,template ,level)
              '(,name ,@lits ,@(strip-cars extra-formals))))))

(defmacro def-gate-reduce (template body &key extra-lits extra-formals choice prepwork eval-hints level)
  (def-gate-reduce-fn template body extra-lits extra-formals choice prepwork eval-hints level))



(def-gate-reduce (and x0 x1)
;; (AND 0 NIL)                                            NIL                             1
;; (AND 0 (NOT NIL))                                      0                               1
;; (AND 0 0)                                              0                               1
;; (AND 0 (NOT 0))                                        NIL                             1
  (b* (((when (=30 x0 0))                  0)
       ((when (=30 x0 1))                  x1)
       ((when (=30 x1 0))                  0)
       ((when (=30 x1 1))                  x0)
       ((when (=30 x0 x1))                 x0)
       ((when (=30 x0 (lit-negate^ x1)))   0))
    nil)
  :prepwork ((local (in-theory (disable satlink::equal-of-lit-negate-component-rewrites))))
  :level 1
  :eval-hints ((and stable-under-simplificationp
                    '(:expand ((lit-eval x0 invals regvals aignet)
                               (lit-eval x1 invals regvals aignet))
                      :in-theory (enable b-xor
                                         satlink::equal-of-lit-negate-component-rewrites)))))



(def-gate-reduce (xor x0 x1)
;; Note: lits are both normalized to be non-negated before we get here.
;; (XOR 0 NIL)                                            0                               1
;; (XOR 0 0)                                              NIL                             1
  (b* (((when (=30 x0 0))                  x1)
       ((when (=30 x1 0))                  x0)
       ((when (=30 x0 x1))                 0))
    nil)
  :level 1
  :eval-hints
  (("Goal" :in-theory (enable eval-xor-of-lits))
   (and stable-under-simplificationp
        '(:expand ((lit-eval x0 invals regvals aignet)
                   (lit-eval x1 invals regvals aignet))
          :in-theory (enable b-xor)))))


(local (defthm lit-eval-when-equal-lit-negate-1
         (implies (and (equal (lit-fix x) (lit-negate y))
                       (equal 1 (lit-eval y invals regvals aignet)))
                  (equal (lit-eval x invals regvals aignet)
                         0))
         :hints(("Goal" :expand ((:free (x) (lit-eval x invals regvals aignet)))
                 :in-theory (enable b-xor)))))

(local (defthm lit-eval-when-equal-lit-negate-0
         (implies (and (equal (lit-fix x) (lit-negate y))
                       (equal 0 (lit-eval y invals regvals aignet)))
                  (equal (lit-eval x invals regvals aignet)
                         1))
         :hints(("Goal" :expand ((:free (x) (lit-eval x invals regvals aignet)))
                 :in-theory (enable b-xor)))))

(local (defthm lit-eval-when-lit-negate-equal-1
         (implies (and (equal (lit-fix y) (lit-negate x))
                       (equal 1 (lit-eval y invals regvals aignet)))
                  (equal (lit-eval x invals regvals aignet)
                         0))
         :hints(("Goal" :expand ((:free (x) (lit-eval x invals regvals aignet)))
                 :in-theory (enable b-xor)))))

(local (defthm lit-eval-when-lit-negate-equal-0
         (implies (and (equal (lit-fix y) (lit-negate x))
                       (equal 0 (lit-eval y invals regvals aignet)))
                  (equal (lit-eval x invals regvals aignet)
                         1))
         :hints(("Goal" :expand ((:free (x) (lit-eval x invals regvals aignet)))
                 :in-theory (enable b-xor)))))

(def-gate-reduce (and (and y0 y1) x1)
;; (AND (AND 0 1) 0)                                      (AND 0 1)                       2
  (b* (((when (=30 y0 x1))                                x0)
       ((when (=30 y1 x1))                                x0)
;; (AND (AND 0 1) (NOT 0))                                NIL                             2
       ((when (=30 y0 (lit-negate^ x1)))                  0)
       ((when (=30 y1 (lit-negate^ x1)))                  0))
    nil)
  :extra-lits (x0)
  :level 2
  :eval-hints ((and stable-under-simplificationp
                    '(:expand (;;(lit-eval x0 invals regvals aignet)
                               ;; ;; (lit-eval x1 invals regvals aignet)
                               ;; (lit-eval y0 invals regvals aignet)
                               ;; (lit-eval y1 invals regvals aignet)
                               ;; (id-eval (lit->var x0) invals regvals aignet)
                               (:free (x y) (eval-and-of-lits x y invals regvals aignet)))
                      :in-theory (enable b-xor b-and)))))


(def-gate-reduce (and (not (and y0 y1)) x1)
;; (AND (NOT (AND 0 1)) (NOT 0))                          (NOT 0)                         2
  (and (or (=30 (lit-negate^ y0) x1)
           (=30 (lit-negate^ y1) x1))
       x1)
  :level 2
  :eval-hints ((and stable-under-simplificationp
                    '(:expand (;; (lit-eval x0 invals regvals aignet)
                               ;; (lit-eval x1 invals regvals aignet)
                               ;; (lit-eval y0 invals regvals aignet)
                               ;; (lit-eval y1 invals regvals aignet)
                               ;; (id-eval (lit->var x0) invals regvals aignet)
                               (:free (x y) (eval-and-of-lits x y invals regvals aignet)))
                      :in-theory (enable b-xor b-and)))))

(def-gate-reduce (and (not (and y0 y1)) x1)
;; (AND (NOT (AND 0 1)) 0)                                (AND 0 (NOT 1))                 3
  (b* (((when (=30 y0 x1))   (mv (simpcode! :and) y0 (lit-negate y1)))
       ((when (=30 y1 x1))   (mv (simpcode! :and) y1 (lit-negate y0))))
    (mv nil 0 0))
  :level 3
  :eval-hints ((and stable-under-simplificationp
                    '(:expand (;; (lit-eval x0 invals regvals aignet)
                               ;; (lit-eval x1 invals regvals aignet)
                               ;; (lit-eval y0 invals regvals aignet)
                               ;; (lit-eval y1 invals regvals aignet)
                               ;; (id-eval (lit->var x0) invals regvals aignet)
                               (:free (x y) (eval-and-of-lits x y invals regvals aignet)))
                      :in-theory (enable b-xor b-and)))))

(def-gate-reduce (and (xor y0 y1) x1)
;; (AND (XOR 0 1) 0)                                      (AND 0 (NOT 1))                 3
;; (AND (XOR 0 1) (NOT 0))                                (AND (NOT 0) 1)                 3

;; Note: omitting for now -- should be handled by symmetry
;; (AND (NOT (XOR 0 1)) 0)                                (AND 0 1)                       3
;; (AND (NOT (XOR 0 1)) (NOT 0))                          (AND (NOT 0) (NOT 1))           3
  (b* (((when (=30 y0 x1))          (mv (simpcode! :and) y0 (lit-negate y1)))
       ((when (=30 y1 x1))          (mv (simpcode! :and) y1 (lit-negate y0))))
    (mv nil 0 0))
  :level 3
  :eval-hints ((and stable-under-simplificationp
                    '(:expand (;; (lit-eval x0 invals regvals aignet)
                               ;; (lit-eval x1 invals regvals aignet)
                               ;; (lit-eval y0 invals regvals aignet)
                               ;; (lit-eval y1 invals regvals aignet)
                               ;; (id-eval (lit->var x0) invals regvals aignet)
                               (:free (x y) (eval-and-of-lits x y invals regvals aignet)))
                      :in-theory (enable b-xor b-and)))))

(def-gate-reduce (and (and y0 y1) (and y2 y3))
  (and (or (b* ((ny2 (lit-negate^ y2)))
             (or (=30 y0 ny2)
                 (=30 y1 ny2)))
           (b* ((ny3 (lit-negate^ y3)))
             (or (=30 y0 ny3)
                 (=30 y1 ny3))))
       0)
  :level 2
  :eval-hints ((and stable-under-simplificationp
                    '(:expand (;; (lit-eval x0 invals regvals aignet)
                               ;; (lit-eval x1 invals regvals aignet)
                               ;; (lit-eval y0 invals regvals aignet)
                               ;; (lit-eval y1 invals regvals aignet)
                               ;; (lit-eval y2 invals regvals aignet)
                               ;; (lit-eval y3 invals regvals aignet)
                               ;; (id-eval (lit->var x0) invals regvals aignet)
                               (:free (x y) (eval-and-of-lits x y invals regvals aignet)))
                      :in-theory (enable b-xor b-and)))))

(def-gate-reduce (and (and y0 y1) (and y2 y3))
;; (AND (AND 0 1) (AND 0 2))                              (AND 1 (AND 0 2))               4
  (b* (((when (=30 y0 y2))
        (mv (simpcode! :andchoice) y1 x1 x0 y3))
       ((when (=30 y0 y3))
        (mv (simpcode! :andchoice) y1 x1 x0 y2))
       ((when (=30 y1 y2))
        (mv (simpcode! :andchoice) y0 x1 x0 y3))
       ((when (=30 y1 y3))
        (mv (simpcode! :andchoice) y0 x1 x0 y2)))
    (mv nil 0 0 0 0))
  :level 4
  :choice t
  :extra-lits (x0 x1)
  :eval-hints ((and stable-under-simplificationp
                    '(:expand (;; (lit-eval x0 invals regvals aignet)
                               ;; (lit-eval x1 invals regvals aignet)
                               ;; (lit-eval y0 invals regvals aignet)
                               ;; (lit-eval y1 invals regvals aignet)
                               ;; (lit-eval y2 invals regvals aignet)
                               ;; (lit-eval y3 invals regvals aignet)
                               ;; (id-eval (lit->var x0) invals regvals aignet)
                               ;; (id-eval (lit->var x1) invals regvals aignet)
                               (:free (x y) (eval-and-of-lits x y invals regvals aignet)))
                      :in-theory (enable b-xor b-and)))))

(def-gate-reduce (and (not (and y0 y1)) (and y2 y3))
  ;; (AND (NOT (AND 0 1)) (AND (NOT 0) 2))                  (AND (NOT 0) 2)                 2
  (and (or (b* ((ny0 (lit-negate y0)))
             (or (=30 ny0 y2)
                 (=30 ny0 y3)))
           (b* ((ny1 (lit-negate y1)))
             (or (=30 ny1 y2)
                 (=30 ny1 y3))))
       x1)
  :level 2
  :extra-lits (x1)
  :eval-hints ((and stable-under-simplificationp
                    '(:expand (;; (lit-eval x0 invals regvals aignet)
                               ;; (lit-eval x1 invals regvals aignet)
                               ;; (lit-eval y0 invals regvals aignet)
                               ;; (lit-eval y1 invals regvals aignet)
                               ;; (lit-eval y2 invals regvals aignet)
                               ;; (lit-eval y3 invals regvals aignet)
                               ;; (id-eval (lit->var x0) invals regvals aignet)
                               ;; (id-eval (lit->var x1) invals regvals aignet)
                               (:free (x y) (eval-and-of-lits x y invals regvals aignet)))
                      :in-theory (enable b-xor b-and)))))


(def-gate-reduce (and (not (and y0 y1)) (and y2 y3))
;;    (AND (NOT (AND 0 1)) (AND 0 2))                        (AND (NOT 1) (AND 0 2))         3
  (b* (((when (or (=30 y0 y2)
                  (=30 y0 y3)))
        (mv (simpcode! :and) (lit-negate^ y1) x1))
       ((when (or (=30 y1 y2)
                  (=30 y1 y3)))
        (mv (simpcode! :and) (lit-negate^ y0) x1)))
    (mv nil 0 0))
  :extra-lits (x1)
  :level 3
  :eval-hints ((and stable-under-simplificationp
                    '(:expand (;; (lit-eval x0 invals regvals aignet)
                               ;; (lit-eval x1 invals regvals aignet)
                               ;; (lit-eval y0 invals regvals aignet)
                               ;; (lit-eval y1 invals regvals aignet)
                               ;; (lit-eval y2 invals regvals aignet)
                               ;; (lit-eval y3 invals regvals aignet)
                               ;; (id-eval (lit->var x0) invals regvals aignet)
                               ;; (id-eval (lit->var x1) invals regvals aignet)
                               (:free (x y) (eval-and-of-lits x y invals regvals aignet)))
                      :in-theory (enable b-xor b-and)))))

(def-gate-reduce (and (not (and y0 y1)) (not (and y2 y3)))
;;    (AND (NOT (AND 0 1)) (NOT (AND (NOT 0) 1)))            (NOT 1)                         2
  (cond ((=30 y0 y2) (and (=30 (lit-negate y1) y3) (lit-negate y0)))
        ((=30 y0 y3) (and (=30 (lit-negate y1) y2) (lit-negate y0)))
        ((=30 y1 y2) (and (=30 (lit-negate y0) y3) (lit-negate y1)))
        ((=30 y1 y3) (and (=30 (lit-negate y0) y2) (lit-negate y1)))
        (t nil))
  :level 2
  :eval-hints ((and stable-under-simplificationp
                    '(:expand (;; (lit-eval x0 invals regvals aignet)
                               ;; (lit-eval x1 invals regvals aignet)
                               ;; (lit-eval y0 invals regvals aignet)
                               ;; (lit-eval y1 invals regvals aignet)
                               ;; (lit-eval y2 invals regvals aignet)
                               ;; (lit-eval y3 invals regvals aignet)
                               ;; (id-eval (lit->var x0) invals regvals aignet)
                               ;; (id-eval (lit->var x1) invals regvals aignet)
                               (:free (x y) (eval-and-of-lits x y invals regvals aignet)))
                      :in-theory (enable b-xor b-and)))))

(def-gate-reduce (and (not (and y0 y1)) (not (and y2 y3)))
;;     (AND (NOT (AND 0 1)) (NOT (AND (NOT 0) (NOT 1))))      (XOR 0 1)                       3
  (b* (((unless (< 1 (gatesimp->xor-mode gatesimp)))
        (mv nil 0 0))
       (ny0 (lit-negate^ y0))
       ;; NOTE: if we standardize ordering of literals one of these may be impossible
       ((when (=30 ny0 y2))
        (if (=30 (lit-negate^ y1) y3)
            (mv (simpcode! :xor) y0 y1)
          (mv nil 0 0)))
       ((when (=30 ny0 y3))
        (if (=30 (lit-negate^ y1) y2)
            (mv (simpcode! :xor) y0 y1)
          (mv nil 0 0))))
    (mv nil 0 0))
  :level 3
  :extra-formals ((gatesimp gatesimp-p :type (unsigned-byte 6)))
  :eval-hints ((and stable-under-simplificationp
                    '(:expand (;; (lit-eval x0 invals regvals aignet)
                               ;; (lit-eval x1 invals regvals aignet)
                               ;; (lit-eval y0 invals regvals aignet)
                               ;; (lit-eval y1 invals regvals aignet)
                               ;; (lit-eval y2 invals regvals aignet)
                               ;; (lit-eval y3 invals regvals aignet)
                               ;; (id-eval (lit->var x0) invals regvals aignet)
                               ;; (id-eval (lit->var x1) invals regvals aignet)
                               (:free (x y) (eval-and-of-lits x y invals regvals aignet))
                               (:free (x y) (eval-xor-of-lits x y invals regvals aignet)))
                      :in-theory (enable b-xor b-and)))))


;; (local (defthm b-and-equal-1
;;          (implies (syntaxp (or (acl2::rewriting-negative-literal-fn
;;                                 `(EQUAL (ACL2::B-AND$INLINE ,A ,B) '1) mfc state)
;;                                (acl2::rewriting-negative-literal-fn
;;                                 `(EQUAL '1 (ACL2::B-AND$INLINE ,A ,B)) mfc state)))
;;                   (iff (equal (b-and a b) 1)
;;                        (and (bit->bool a) (bit->bool b))))))

;; (local (defthm b-xor-equal-1
;;          (implies (syntaxp (or (acl2::rewriting-negative-literal-fn
;;                                 `(EQUAL (ACL2::B-XOR$INLINE ,A ,B) '1) mfc state)
;;                                (acl2::rewriting-negative-literal-fn
;;                                 `(EQUAL '1 (ACL2::B-XOR$INLINE ,A ,B)) mfc state)))
;;                   (iff (equal (b-xor a b) 1)
;;                        (equal (bfix a) (b-not b))))
;;          :hints(("Goal" :in-theory (enable bfix b-not)))))

;; (local (defthm b-xor-equal-0
;;          (implies (syntaxp (or (acl2::rewriting-negative-literal-fn
;;                                 `(EQUAL (ACL2::B-XOR$INLINE ,A ,B) '1) mfc state)
;;                                (acl2::rewriting-negative-literal-fn
;;                                 `(EQUAL '1 (ACL2::B-XOR$INLINE ,A ,B)) mfc state)))
;;                   (iff (equal (b-xor a b) 0)
;;                        (equal (bfix a) (bfix b))))
;;          :hints(("Goal" :in-theory (enable bfix)))))

(local (defthm lit-negate-equal-x
         (and (not (equal (lit-negate x) x))
              (not (equal (lit-negate x) (lit-fix x))))))
                  

(def-gate-reduce (and (xor y0 y1) (and y2 y3))
  ;; BOZO might improve perf by changing ordering of checks here
  (b* ((ny0 (lit-negate^ y0))
       (ny1 (lit-negate^ y1))
       ((when (or
               ;; NOTE: if we standardize ordering of literals one of these may be impossible
               ;; (AND (XOR 0 1) (AND 0 1))                              NIL                             2
               (and (=30 y0 y2)
                    (=30 y1 y3))
               (and (=30 y0 y3)
                    (=30 y1 y2))
               ;; NOTE: if we standardize ordering of literals one of these may be impossible
               ;; (AND (XOR 0 1) (AND (NOT 0) (NOT 1)))                  NIL                             2
               (or (and (=30 ny0 y2)
                        (=30 ny1 y3))
                   (and (=30 ny0 y3)
                        (=30 ny1 y2)))))
        0)
       ;; NOTE: if we standardize ordering of literals two of these may be impossible
       ;;     (AND (XOR 0 1) (AND (NOT 0) 1))                        (AND (NOT 0) 1)                 2
       ((when (or (and (=30 ny0 y2)
                       (=30 y1 y3))
                  (and (=30 ny0 y3)
                       (=30 y1 y2))
                  (and (=30 ny1 y2)
                       (=30 y0 y3))
                  (and (=30 ny1 y3)
                       (=30 y0 y2))))
        x1))
    nil)
    :extra-lits (x1)
    :level 2
    :eval-hints ((and stable-under-simplificationp
                      '(:expand ((:free (x y) (eval-and-of-lits x y invals regvals aignet))
                                 (:free (x y) (eval-xor-of-lits x y invals regvals aignet)))
                         :in-theory (enable b-xor b-and)
                        ))
                 ;; (and stable-under-simplificationp
                 ;;      '(:in-theory (enable b-and b-xor)))
                 ;; (and stable-under-simplificationp
                 ;;      '(:in-theory (enable satlink::equal-of-lit-negate-component-rewrites)))
                 )
    :prepwork ((local (in-theory (disable ;; satlink::equal-of-lit-negate-backchain
                                          ;; satlink::lit-negate-not-equal-when-vars-mismatch
                                          ;; satlink::equal-of-lit-negate-cond-component-rewrites
                                          satlink::equal-of-lit-negate-component-rewrites
                                          ;; satlink::equal-of-lit-fix-backchain
                                          ;; SATLINK::LIT-NEGATE-NOT-EQUAL-WHEN-NEG-MATCHES
                                          )))))


(def-gate-reduce (and (xor y0 y1) (and y2 y3))
  ;; (AND (XOR 0 1) (AND 0 2))                              (AND (NOT 1) (AND 0 2))         3
  (b* (((when (or (=30 y0 y2)
                  (=30 y0 y3)))
        (mv (simpcode! :and) (lit-negate^ y1) x1))
       ((when (or (=30 y1 y2)
                  (=30 y1 y3)))
        (mv (simpcode! :and) (lit-negate^ y0) x1))
       ;; (AND (XOR 0 1) (AND (NOT 0) 2))                        (AND 1 (AND (NOT 0) 2))         3
       (ny0 (lit-negate^ y0))
       ((when (or (=30 ny0 y2)
                  (=30 ny0 y3)))
        (mv (simpcode! :and) y1 x1))
       (ny1 (lit-negate^ y1))
       ((when (or (=30 ny1 y2)
                  (=30 ny1 y3)))
        (mv (simpcode! :and) y0 x1)))
    (mv nil 0 0))
    :extra-lits (x1)
    :level 3
    :eval-hints ((and stable-under-simplificationp
                      '(:expand (;; (lit-eval x0 invals regvals aignet)
                                 ;; (lit-eval x1 invals regvals aignet)
                                 ;; (lit-eval y0 invals regvals aignet)
                                 ;; (lit-eval y1 invals regvals aignet)
                                 ;; (lit-eval y2 invals regvals aignet)
                                 ;; (lit-eval y3 invals regvals aignet)
                                 ;; (id-eval (lit->var x0) invals regvals aignet)
                                 ;; (id-eval (lit->var x1) invals regvals aignet)
                                 (:free (x y) (eval-and-of-lits x y invals regvals aignet))
                                 (:free (x y) (eval-xor-of-lits x y invals regvals aignet)))
                        :in-theory (enable b-xor b-and)))))

(def-gate-reduce (and (xor y0 y1) (not (and y2 y3)))
  (b* ((ny0 (lit-negate^ y0))
       (ny1 (lit-negate^ y1))
       ((when (or
               ;; NOTE: if we standardize ordering of literals one of these may be impossible
               ;; (AND (XOR 0 1) (NOT (AND 0 1)))                        (XOR 0 1)                       2
               (and (=30 y0 y2)
                    (=30 y1 y3))
               (and (=30 y0 y3)
                    (=30 y1 y2))
               ;; NOTE: if we standardize ordering of literals one of these may be impossible
               ;; (AND (XOR 0 1) (NOT (AND (NOT 0) (NOT 1))))            (XOR 0 1)                       2
               (or (and (=30 ny0 y2)
                        (=30 ny1 y3))
                   (and (=30 ny0 y3)
                        (=30 ny1 y2)))))
        x0))
    nil)
  :extra-lits (x0)
  :level 2
  :eval-hints ((and stable-under-simplificationp
                    '(:expand (;; (:free (x) (lit-eval x invals regvals aignet))
                               ;; (id-eval (lit->var x0) invals regvals aignet)
                               ;; (id-eval (lit->var x1) invals regvals aignet)
                               (:free (x y) (eval-and-of-lits x y invals regvals aignet))
                               (:free (x y) (eval-xor-of-lits x y invals regvals aignet)))
                      :in-theory (enable b-xor b-and)))))


(def-gate-reduce (and (xor y0 y1) (not (and y2 y3)))
  ;; (AND (XOR 0 1) (NOT (AND (NOT 0) 1)))                  (AND 0 (NOT 1))                 3
  (b* ((ny0 (lit-negate^ y0))
       ((when (or (and (=30 ny0 y2)
                       (=30 y1 y3))
                  (and (=30 ny0 y3)
                       (=30 y1 y2))))
        (mv (simpcode! :and) y0 (lit-negate^ y1)))
       (ny1 (lit-negate^ y1))
       ((when (or (and (=30 ny1 y2)
                       (=30 y0 y3))
                  (and (=30 ny1 y3)
                       (=30 y0 y2))))
        (mv (simpcode! :and) y1 (lit-negate^ y0))))
    (mv nil 0 0))
  :level 3
  :eval-hints ((and stable-under-simplificationp
                    '(:expand (;; (:free (x) (lit-eval x invals regvals aignet))
                               ;; (id-eval (lit->var x0) invals regvals aignet)
                               ;; (id-eval (lit->var x1) invals regvals aignet)
                               (:free (x y) (eval-and-of-lits x y invals regvals aignet))
                               (:free (x y) (eval-xor-of-lits x y invals regvals aignet)))
                      :in-theory (enable b-xor b-and
                                         satlink::equal-of-lit-negate-component-rewrites))))
  :prepwork ((local (in-theory (disable satlink::equal-of-lit-negate-component-rewrites)))))


(def-gate-reduce (xor (and y0 y1) x1)
  ;; (XOR (AND 0 1) 0)                                      (AND 0 (NOT 1))                 3
  (b* (((when (=30 y0 x1))
        (mv (simpcode! :and) y0 (lit-negate^ y1)))
       ((when (=30 y1 x1))
        (mv (simpcode! :and) y1 (lit-negate^ y0)))
       ((when (=30 (lit-negate^ y0) x1))
        (mv (simpcode! :nand) y0 (lit-negate^ y1)))
       ((when (=30 (lit-negate^ y1) x1))
        (mv (simpcode! :nand) y1 (lit-negate^ y0))))
    (mv nil 0 0))
  :level 3
  :eval-hints ((and stable-under-simplificationp
                    '(:expand (;; (:free (x) (lit-eval x invals regvals aignet))
                               ;; (id-eval (lit->var x0) invals regvals aignet)
                               ;; (id-eval (lit->var x1) invals regvals aignet)
                               (:free (x y) (eval-and-of-lits x y invals regvals aignet))
                               (:free (x y) (eval-xor-of-lits x y invals regvals aignet)))
                      :in-theory (enable b-xor b-and)))))


(def-gate-reduce (xor (xor y0 y1) x1)
  ;; (XOR (XOR 0 1) 0)                                      1                               2
  (b* (((when (=30 y0 x1)) y1)
       ((when (=30 y1 x1)) y0)
       (nx1 (lit-negate^ x1))
       ((when (=30 y0 nx1)) (lit-negate^ y1))
       ((when (=30 y1 nx1)) (lit-negate^ y0)))
    nil)
  :level 2
  :eval-hints ((and stable-under-simplificationp
                    '(:expand (;; (:free (x) (lit-eval x invals regvals aignet))
                               ;; (id-eval (lit->var x0) invals regvals aignet)
                               ;; (id-eval (lit->var x1) invals regvals aignet)
                               (:free (x y) (eval-and-of-lits x y invals regvals aignet))
                               (:free (x y) (eval-xor-of-lits x y invals regvals aignet)))
                      :in-theory (enable b-xor b-and)))))

(def-gate-reduce (xor (and y0 y1) (and y2 y3))
  ;; (XOR (AND 0 1) (AND (NOT 0) 1))                        1                               2
  (b* ((ny0 (lit-negate^ y0))
       (ny1 (lit-negate^ y1))
       ((when ;; NOTE: if we standardize ordering of literals one of these may be impossible
            (or (and (=30 ny0 y2) (=30 y1 y3))
                (and (=30 ny0 y3) (=30 y1 y2))))
        y1)
       ((when ;; NOTE: if we standardize ordering of literals one of these may be impossible
            (or (and (=30 ny1 y2) (=30 y0 y3))
                (and (=30 ny1 y3) (=30 y0 y2))))
        y0))
    nil)
  :level 2
  :eval-hints ((and stable-under-simplificationp
                    '(:expand (;; (:free (x) (lit-eval x invals regvals aignet))
                               ;; (id-eval (lit->var x0) invals regvals aignet)
                               ;; (id-eval (lit->var x1) invals regvals aignet)
                               (:free (x y) (eval-and-of-lits x y invals regvals aignet))
                               (:free (x y) (eval-xor-of-lits x y invals regvals aignet)))
                      :in-theory (enable b-xor b-and
                                         satlink::equal-of-lit-negate-component-rewrites))))
  :prepwork ((local (in-theory (disable satlink::equal-of-lit-negate-component-rewrites)))))


(def-gate-reduce (xor (and y0 y1) (and y2 y3))
  ;; (XOR (AND 0 1) (AND (NOT 0) (NOT 1)))                  (NOT (XOR 0 1))                 3
  (b* ((ny0 (lit-negate^ y0))
       (ny1 (lit-negate^ y1))
       ((when ;; NOTE: if we standardize ordering of literals one of these may be impossible
            (or (and (=30 ny0 y2) (=30 ny1 y3))
                (and (=30 ny0 y3) (=30 ny1 y2))))
        (mv (simpcode! :xor) ny0 y1)))
    (mv nil 0 0))
  :level 3
  :eval-hints ((and stable-under-simplificationp
                    '(:expand (;; (:free (x) (lit-eval x invals regvals aignet))
                               ;; (id-eval (lit->var x0) invals regvals aignet)
                               ;; (id-eval (lit->var x1) invals regvals aignet)
                               (:free (x y) (eval-and-of-lits x y invals regvals aignet))
                               (:free (x y) (eval-xor-of-lits x y invals regvals aignet)))
                      :in-theory (enable b-xor b-and
                                         satlink::equal-of-lit-negate-component-rewrites))))
  :prepwork ((local (in-theory (disable satlink::equal-of-lit-negate-component-rewrites)))))

(def-gate-reduce (xor (xor y0 y1) (and y2 y3))
  ;; (XOR (XOR 0 1) (AND 0 1))                              (NOT (AND (NOT 0) (NOT 1)))     3
  ;; (XOR (XOR 0 1) (AND (NOT 0) 1))                        (AND 0 (NOT 1))                 3
  ;; (XOR (XOR 0 1) (AND (NOT 0) (NOT 1)))                  (NOT (AND 0 1))                 3
  (b* ((ny0 (lit-negate^ y0))
       (ny1 (lit-negate^ y1)))
    (cond ((=30 y0 y2)
           (cond ((=30 y1 y3)
                  ;; (XOR (XOR 0 1) (AND 0 1))                              (NOT (AND (NOT 0) (NOT 1)))     3
                  (mv (simpcode! :nand) ny0 ny1))
                 ((=30 ny1 y3)
                  ;; (XOR (XOR 0 1) (AND (NOT 0) 1))                        (AND 0 (NOT 1))                 3
                  (mv (simpcode! :and) y1 ny0))
                 (t (mv nil 0 0))))
          ((=30 y0 y3)
           (cond ((=30 y1 y2)
                  ;; (XOR (XOR 0 1) (AND 0 1))                              (NOT (AND (NOT 0) (NOT 1)))     3
                  (mv (simpcode! :nand) ny0 ny1))
                 ((=30 ny1 y2)
                  ;; (XOR (XOR 0 1) (AND (NOT 0) 1))                        (AND 0 (NOT 1))                 3
                  (mv (simpcode! :and) y1 ny0))
                 (t (mv nil 0 0))))
          ((=30 ny0 y2)
           (cond ((=30 y1 y3)
                  ;; (XOR (XOR 0 1) (AND (NOT 0) 1))                        (AND 0 (NOT 1))                 3
                  (mv (simpcode! :and) y0 ny1))
                 ((=30 ny1 y3)
                  ;; (XOR (XOR 0 1) (AND (NOT 0) (NOT 1)))                  (NOT (AND 0 1))                 3
                  (mv (simpcode! :nand) y0 y1))
                 (t (mv nil 0 0))))
          ((=30 ny0 y3)
           (cond ((=30 y1 y2)
                  ;; (XOR (XOR 0 1) (AND (NOT 0) 1))                        (AND 0 (NOT 1))                 3
                  (mv (simpcode! :and) y0 ny1))
                 ((=30 ny1 y2)
                  ;; (XOR (XOR 0 1) (AND (NOT 0) (NOT 1)))                  (NOT (AND 0 1))                 3
                  (mv (simpcode! :nand) y0 y1))
                 (t (mv nil 0 0))))
          (t (mv nil 0 0))))
  :level 3
  :eval-hints ((and stable-under-simplificationp
                    '(:expand (;; (:free (x) (lit-eval x invals regvals aignet))
                               ;; (id-eval (lit->var x0) invals regvals aignet)
                               ;; (id-eval (lit->var x1) invals regvals aignet)
                               (:free (x y) (eval-and-of-lits x y invals regvals aignet))
                               (:free (x y) (eval-xor-of-lits x y invals regvals aignet)))
                      :in-theory (enable b-xor b-and
                                         satlink::equal-of-lit-negate-component-rewrites)))))


(def-gate-reduce (xor (xor y0 y1) (xor y2 y3))
  ;; (XOR (XOR 0 1) (XOR 0 2))                              (XOR 1 2)                       3
  (b* (((when (=30 y0 y2)) (mv (simpcode! :xor) y1 y3))
       ((when (=30 y0 y3)) (mv (simpcode! :xor) y1 y2))
       ((when (=30 y1 y2)) (mv (simpcode! :xor) y0 y3))
       ((when (=30 y1 y3)) (mv (simpcode! :xor) y0 y2)))
    (mv nil 0 0))
  :level 3
  :eval-hints ((and stable-under-simplificationp
                    '(:expand (;; (:free (x) (lit-eval x invals regvals aignet))
                               ;; (id-eval (lit->var x0) invals regvals aignet)
                               ;; (id-eval (lit->var x1) invals regvals aignet)
                               (:free (x y) (eval-and-of-lits x y invals regvals aignet))
                               (:free (x y) (eval-xor-of-lits x y invals regvals aignet)))
                      :in-theory (enable b-xor b-and
                                         satlink::equal-of-lit-negate-component-rewrites)))))
  
       
(make-event
 `(defconst *gate-reduce-table* ',(table-alist 'gate-reduce-table (w state))))

(defun gate-reduce-fn (template level swap)
  (b* ((call (cdr (assoc-equal (list template level) *gate-reduce-table*))))
    (if swap
        (sublis '((x0 . x1)
                  (x1 . x0)
                  (y0 . y2)
                  (y1 . y3)
                  (y2 . y0)
                  (y3 . y1)) call)
      call)))

(defmacro gate-reduce (template &key level swap)
  (gate-reduce-fn template level swap))

(define gate-reduce-collect (alist level)
  :mode :program
  (b* (((when (atom alist)) nil)
       ((cons template swap) (car alist))
       (call (gate-reduce-fn template level swap))
       ((unless call)
        (gate-reduce-collect (cdr alist) level)))
    (cons call (gate-reduce-collect (cdr alist) level))))

(define gate-reduce-level2-bindings (calls choicep)
  :mode :program
  (b* (((when (atom calls)) nil))
    `((ans ,(car calls))
      ((when ans) (mv (simpcode! :existing) ans 0 ,@(and choicep '(0 0))))
      . ,(gate-reduce-level2-bindings (cdr calls) choicep))))

(define gate-reduce-level3-bindings (calls choicep)
  :mode :program
  (b* (((when (atom calls)) nil))
    `(((mv flag new0 new1) ,(car calls))
      ((when flag) (mv flag new0 new1 ,@(and choicep '(0 0))))
      . ,(gate-reduce-level3-bindings (cdr calls) choicep))))

(define gate-reduce-level4-bindings (calls)
  :mode :program
  (b* (((when (atom calls)) nil))
    `(((mv flag new0 new1 new2 new3) ,(car calls))
      ((when flag) (mv flag new0 new1 new2 new3))
      . ,(gate-reduce-level4-bindings (cdr calls)))))



;; This makes a nesting of reducers for a given gate layout and a given setting
;; of choicep, which corresponds to whether the function as a whole may return
;; a choice of implementations or just one.  Choicep must be t if there are any
;; level4 calls.
(define gate-reduce-2level-fn (x choicep)
  :mode :program
  (b* (((axi-gate x))
       ((axi-lit x.left))
       ((axi-lit x.right))
       (alist (append (axi-term-case x.left.abs
                        :gate (list (cons (axi-gate x.op x.left 'x1) nil))
                        :otherwise nil)
                      (axi-term-case x.right.abs
                        :gate
                        (list (cons (axi-gate x.op
                                              (axi-lit x.right.negp (axi-gate x.right.abs.op 'y0 'y1))
                                              'x1)
                                    t)) ;; swapped
                        :otherwise nil)
                      (list (cons x nil))
                      (axi-term-case x.right.abs
                        :gate
                        (axi-term-case x.left.abs
                          :gate
                          (and (not (and (eql x.right.negp x.left.negp)
                                         (eql x.right.abs.op x.left.abs.op)))
                               ;; note: if fully symmetrical we should only call once
                               (list (cons (axi-gate x.op
                                                     (axi-lit x.right.negp (axi-gate x.right.abs.op 'y0 'y1))
                                                     (axi-lit x.left.negp (axi-gate x.left.abs.op 'y2 'y3)))
                                           t)))
                          :otherwise nil)
                        :otherwise nil)))
       (l2-calls (gate-reduce-collect alist 2))
       (l3-calls (gate-reduce-collect alist 3))
       (l4-calls (gate-reduce-collect alist 4))
       (l2-bindings (gate-reduce-level2-bindings l2-calls choicep))
       ((unless (or l3-calls l4-calls))
        `(b* ,l2-bindings
           (mv nil 0 0 ,@(and choicep '(0 0)))))
       ((when l4-calls)
        `(b* (,@l2-bindings
              ,@(and l3-calls
                     `(((unless (< 2 (the (unsigned-byte 3) (lnfix level))))
                        (mv nil 0 0 0 0))
                       ,@(gate-reduce-level3-bindings l3-calls choicep)))
              ((unless (< 3 (the (unsigned-byte 3) (lnfix level))))
               (mv nil 0 0 0 0))
              . ,(gate-reduce-level4-bindings (butlast l4-calls 1)))
           ,(car (last l4-calls)))))
    `(b* (,@l2-bindings
          ((unless (< 2 (the (unsigned-byte 3) (lnfix level))))
           (mv nil 0 0 ,@(and choicep '(0 0))))
          . ,(gate-reduce-level3-bindings l3-calls choicep))
       (mv nil 0 0 ,@(and choicep '(0 0))))))

(defmacro gate-reduce-2level (x)
  (gate-reduce-2level-fn x nil))

(defmacro gate-reduce-2level+ (x)
  (gate-reduce-2level-fn x t))

(encapsulate nil
  (local (defthm unsigned-byte-p-when-litp-and-lit-var
           (implies (and (unsigned-byte-p 29 (lit->var x))
                         (litp x))
                    (unsigned-byte-p 30 x))
           :hints(("Goal" :in-theory (enable litp lit->var)))))
  (local (defthm unsigned-byte-p-by-bound
           (implies (and (unsigned-byte-p n y)
                         (<= x y)
                         (natp x))
                    (unsigned-byte-p n x))
           :hints(("Goal" :in-theory (enable unsigned-byte-p)))))
  (defthm unsigned-byte-30-of-fanin-when-id-bounded
    (implies (unsigned-byte-p 29 id)
             (unsigned-byte-p 30 (fanin type (lookup-id id aignet))))
    :hints(("Goal" :in-theory (e/d ()
                                   (fanin-id-lte-fanin-count-strong
                                    fanin-id-lte-fanin-count))
            :use ((:instance fanin-id-lte-fanin-count
                   (aignet (lookup-id id aignet)))))
           (and stable-under-simplificationp
                '(:cases ((consp (lookup-id id aignet))))))))


(local (defthm lit->var-of-gate-fanin0
         (implies (equal (ctype (stype (car x))) :gate)
                  (< (lit->var (fanin :gate0 x)) (fanin-count x)))
         :hints(("Goal" :in-theory (enable fanin aignet-id-fix aignet-idp)))
         :rule-classes :linear))

(local (defthm lit->var-of-gate-fanin1
         (implies (equal (ctype (stype (car x))) :gate)
                  (< (lit->var (fanin :gate1 x)) (fanin-count x)))
         :hints(("Goal" :in-theory (enable fanin aignet-id-fix aignet-idp)))
         :rule-classes :linear))

(local (defthm lit->var-of-any-fanin
         (<= (lit->var (fanin ftype x)) (fanin-count x))
         :hints(("Goal" :in-theory (enable fanin aignet-id-fix aignet-idp)))
         :rule-classes :linear))

(local (defthm fanin-count-of-lookup-id-bound
         (<= (fanin-count (lookup-id n aignet)) (nfix n))
         :hints (("goal" :cases ((<= (nfix n) (fanin-count aignet)))))
         :rule-classes :linear))


(define reduce-and-gate-when-one-gate ((x0 litp :type (unsigned-byte 30))
                                       (x1 litp :type (unsigned-byte 30))
                                       (gatesimp gatesimp-p :type (unsigned-byte 6))
                                       (aignet))
  :guard (and (<= 2 (gatesimp->level gatesimp))
              (fanin-litp x0 aignet)
              (fanin-litp x1 aignet)
              (eql (id->type (lit-id x0) aignet) (gate-type)))
  :returns (mv (code maybe-simpcode-p)
               (new0 litp :rule-classes :type-prescription)
               (new1 litp :rule-classes :type-prescription))
  (b* ((x0-id (lit->var^ x0))
       (x0-neg (lit->neg^ x0))
       (x0-regp (id->regp x0-id aignet))
       (y0 (gate-id->fanin0 x0-id aignet))
       (y1 (gate-id->fanin1 x0-id aignet))
       (level (gatesimp->level gatesimp)))
    (if (=b 0 x0-regp)
        (if (=b 0 x0-neg)
            (gate-reduce-2level (and (and y0 y1) x1))
          (gate-reduce-2level (and (not (and y0 y1)) x1)))
      (b* ((y0 (if (=b 0 x0-neg) y0 (lit-negate^ y0))))
        (gate-reduce-2level (and (xor y0 y1) x1)))))
  ///
  (def-gatesimp-thms (x0 x1)
    :eval-spec (b-and (lit-eval x0 invals regvals aignet)
                      (lit-eval x1 invals regvals aignet))
    :syntax-hyp (equal (id->type (lit-id x0) aignet) (gate-type))
    :measure-hyp (equal (id->type (lit-id x0) aignet) (gate-type))
    :eval-hints ((and stable-under-simplificationp
                      '(:expand ((lit-eval x0 invals regvals aignet)
                                 (id-eval (lit-id x0) invals regvals aignet)
                                 (:free (x y) (eval-and-of-lits x y invals regvals aignet))
                                 (:free (x y) (eval-xor-of-lits x y invals regvals aignet))))))
    :use-aignet t))
               
       



(define reduce-and-gate-when-both-gates ((x0 litp :type (unsigned-byte 30))
                                         (x1 litp :type (unsigned-byte 30))
                                         (gatesimp gatesimp-p :type (unsigned-byte 6))
                                         (aignet))
  :guard (and (<= 2 (gatesimp->level gatesimp))
              (fanin-litp x0 aignet)
              (fanin-litp x1 aignet)
              (eql (id->type (lit-id x0) aignet) (gate-type))
              (eql (id->type (lit-id x1) aignet) (gate-type)))
  :returns (mv (code maybe-simpcode-p)
               (new0 litp :rule-classes :type-prescription)
               (new1 litp :rule-classes :type-prescription)
               (new2 litp :rule-classes :type-prescription)
               (new3 litp :rule-classes :type-prescription))
  (b* ((x0-id (lit->var^ x0))
       (x0-neg (lit->neg^ x0))
       (x0-regp (id->regp x0-id aignet))
       (x1-id (lit->var^ x1))
       (x1-neg (lit->neg^ x1))
       (x1-regp (id->regp x1-id aignet))
       (y0 (gate-id->fanin0 x0-id aignet))
       (y1 (gate-id->fanin1 x0-id aignet))
       (y2 (gate-id->fanin0 x1-id aignet))
       (y3 (gate-id->fanin1 x1-id aignet))
       (level (gatesimp->level gatesimp)))
    (if (=b 0 x0-regp)
        (if (=b 0 x0-neg)
            ;; (and (and ...) ?)
            (if (=b 0 x1-regp)
                (if (=b 0 x1-neg)
                    (gate-reduce-2level+ (and (and y0 y1) (and y2 y3)))
                  (gate-reduce-2level+ (and (and y0 y1) (not (and y2 y3)))))
              ;; (and (and ...) (xor ...))
              (b* ((y2 (if (=b 0 x1-neg) y2 (lit-negate^ y2))))
                (gate-reduce-2level+ (and (and y0 y1) (xor y2 y3)))))
          ;; (and (not (and ...)) ?)
          (if (=b 0 x1-regp)
              (if (=b 0 x1-neg)
                  (gate-reduce-2level+ (and (not (and y0 y1)) (and y2 y3)))
                (gate-reduce-2level+ (and (not (and y0 y1)) (not (and y2 y3)))))
            ;; (and (and ...) (xor ...))
            (b* ((y2 (if (=b 0 x1-neg) y2 (lit-negate^ y2))))
              (gate-reduce-2level+ (and (not (and y0 y1)) (xor y2 y3))))))
      ;; (and (xor ...) ?)
      (b* ((y0 (if (=b 0 x0-neg) y0 (lit-negate^ y0))))
        (if (=b 0 x1-regp)
            (if (=b 0 x1-neg)
                (gate-reduce-2level+ (and (xor y0 y1) (and y2 y3)))
              (gate-reduce-2level+ (and (xor y0 y1) (not (and y2 y3)))))
          ;; (and (and ...) (xor ...))
          (b* ((y2 (if (=b 0 x1-neg) y2 (lit-negate^ y2))))
            (gate-reduce-2level+ (and (xor y0 y1) (xor y2 y3))))))))
  ///
  (local (in-theory (disable acl2::inequality-with-nfix-hyp-1
                             acl2::inequality-with-nfix-hyp-2
                             lookup-id-in-bounds-when-positive
                             default-car
                             acl2::posp-redefinition
                             lookup-id-out-of-bounds
                             not
                             default-<-2
                             o<
                             (two-id-measure)
                             ;; fanin-if-co-when-output
                             satlink::equal-of-lit-negate-cond-component-rewrites
                             satlink::equal-of-lit-negate-component-rewrites)))
  (local (defthm two-id-measure-of-0-0
           (implies (and (bind-free '((aignet . aignet)) (aignet))
                         (not (equal (stype (car (lookup-id id1 aignet))) :const)))
                    (o< (two-id-measure 0 0)
                        (two-id-measure id1 id2)))
           :hints(("Goal" :in-theory (enable two-id-measure)))))

  (def-gatesimp-thms (x0 x1)
    :eval-spec (b-and (lit-eval x0 invals regvals aignet)
                      (lit-eval x1 invals regvals aignet))
    :syntax-hyp (and (equal (id->type (lit-id x0) aignet) (gate-type))
                     (equal (id->type (lit-id x1) aignet) (gate-type)))
    :measure-hyp (and (equal (id->type (lit-id x0) aignet) (gate-type))
                      (equal (id->type (lit-id x1) aignet) (gate-type)))
    :eval-hints ((and stable-under-simplificationp
                      '(:expand ((lit-eval x0 invals regvals aignet)
                                 (id-eval (lit-id x0) invals regvals aignet)
                                 (lit-eval x1 invals regvals aignet)
                                 (id-eval (lit-id x1) invals regvals aignet)
                                 (:free (x y) (eval-and-of-lits x y invals regvals aignet))
                                 (:free (x y) (eval-xor-of-lits x y invals regvals aignet))))))
    :use-aignet t :choice t))

(define reduce-and-gate ((x0 litp :type (unsigned-byte 30))
                         (x1 litp :type (unsigned-byte 30))
                         (gatesimp gatesimp-p :type (unsigned-byte 6))
                         (aignet))
  :guard (and (fanin-litp x0 aignet)
              (fanin-litp x1 aignet))
  :returns (mv (code maybe-simpcode-p)
               (new0 litp :rule-classes :type-prescription)
               (new1 litp :rule-classes :type-prescription)
               (new2 litp :rule-classes :type-prescription)
               (new3 litp :rule-classes :type-prescription))
  (b* ((ans (gate-reduce (and x0 x1) :level 1))
       ((when ans) (mv (simpcode! :existing) ans 0 0 0))
       ((when (<= (gatesimp->level gatesimp) 1))
        (mv nil 0 0 0 0))
       (x0-type (id->type (lit->var^ x0) aignet))
       (x1-type (id->type (lit->var^ x1) aignet))
       ((when (=2 x0-type (gate-type)))
        (if (=2 x1-type (gate-type))
            (reduce-and-gate-when-both-gates x0 x1 gatesimp aignet)
          (b* (((mv code new0 new1) (reduce-and-gate-when-one-gate x0 x1 gatesimp aignet)))
          (mv code new0 new1 0 0)))))
    (if (=2 x1-type (gate-type))
        (b* (((mv code new0 new1) (reduce-and-gate-when-one-gate x1 x0 gatesimp aignet)))
          (mv code new0 new1 0 0))
      (mv nil 0 0 0 0)))
  ///
  (local (in-theory (disable o< two-id-measure (two-id-measure))))

  (def-gatesimp-thms (x0 x1)
    :eval-spec (b-and (lit-eval x0 invals regvals aignet)
                      (lit-eval x1 invals regvals aignet))
    :use-aignet t :choice t))





(define reduce-xor-gate-when-one-gate ((x0 litp :type (unsigned-byte 30))
                                       (x1 litp :type (unsigned-byte 30))
                                       (gatesimp gatesimp-p :type (unsigned-byte 6))
                                       (aignet))
  :guard (and (<= 2 (gatesimp->level gatesimp))
              (fanin-litp x0 aignet)
              (fanin-litp x1 aignet)
              (eql (id->type (lit-id x0) aignet) (gate-type)))
  :returns (mv (code maybe-simpcode-p)
               (new0 litp :rule-classes :type-prescription)
               (new1 litp :rule-classes :type-prescription))
  (b* ((x0-id (lit->var^ x0))
       (x0-neg (lit->neg^ x0))
       (x0-regp (id->regp x0-id aignet))
       (y0 (gate-id->fanin0 x0-id aignet))
       (y1 (gate-id->fanin1 x0-id aignet))
       (level (gatesimp->level gatesimp))
       ;; (?x0 (mk-lit x0-id 0))
       ((mv code new0 new1)
        (if (=b 0 x0-regp)
            (gate-reduce-2level (xor (and y0 y1) x1))
          (gate-reduce-2level (xor (xor y0 y1) x1))))
       ((when code)
        (mv (simpcode-negate-cond code x0-neg) new0 new1)))
    (mv nil 0 0))
  ///
  (def-gatesimp-thms (x0 x1)
    :eval-spec (b-xor (lit-eval x0 invals regvals aignet)
                      (lit-eval x1 invals regvals aignet))
    :syntax-hyp (equal (id->type (lit-id x0) aignet) (gate-type))
    :measure-hyp (equal (id->type (lit-id x0) aignet) (gate-type))
    :eval-hints ((and stable-under-simplificationp
                      '(:expand ((lit-eval x0 invals regvals aignet)
                                 (id-eval (lit-id x0) invals regvals aignet)
                                 (:free (x y) (eval-and-of-lits x y invals regvals aignet))
                                 (:free (x y) (eval-xor-of-lits x y invals regvals aignet))))))
    :use-aignet t))
               
       



(define reduce-xor-gate-when-both-gates ((x0 litp :type (unsigned-byte 30))
                                         (x1 litp :type (unsigned-byte 30))
                                         (gatesimp gatesimp-p :type (unsigned-byte 6))
                                         (aignet))
  :guard (and (<= 2 (gatesimp->level gatesimp))
              (fanin-litp x0 aignet)
              (fanin-litp x1 aignet)
              (eql (id->type (lit-id x0) aignet) (gate-type))
              (eql (id->type (lit-id x1) aignet) (gate-type)))
  :returns (mv (code maybe-simpcode-p)
               (new0 litp :rule-classes :type-prescription)
               (new1 litp :rule-classes :type-prescription))
  :prepwork ((local (in-theory (enable unsigned-byte-p-of-lit-when-lit->var))))
  (b* ((x0-id (lit->var^ x0))
       (x0-neg (lit->neg^ x0))
       (x0-regp (id->regp x0-id aignet))
       (x1-id (lit->var^ x1))
       (x1-neg (lit->neg^ x1))
       (x1-regp (id->regp x1-id aignet))
       (y0 (gate-id->fanin0 x0-id aignet))
       (y1 (gate-id->fanin1 x0-id aignet))
       (y2 (gate-id->fanin0 x1-id aignet))
       (y3 (gate-id->fanin1 x1-id aignet))
       (neg (b-xor x0-neg x1-neg))
       (x0 (mk-lit x0-id 0))
       (x1 (mk-lit x1-id 0))
       (level (gatesimp->level gatesimp))
       ((mv code new0 new1)
        (if (=b 0 x0-regp)
            (if (=b 0 x1-regp)
                (gate-reduce-2level (xor (and y0 y1) (and y2 y3)))
              (gate-reduce-2level (xor (and y0 y1) (xor y2 y3))))
          (if (=b 0 x1-regp)
              (gate-reduce-2level (xor (xor y0 y1) (and y2 y3)))
            (gate-reduce-2level (xor (xor y0 y1) (xor y2 y3))))))
       ((when code)
        (mv (simpcode-negate-cond code neg) new0 new1)))
    (mv nil 0 0))
  ///

  (local (in-theory (disable acl2::inequality-with-nfix-hyp-1
                             acl2::inequality-with-nfix-hyp-2
                             lookup-id-in-bounds-when-positive
                             default-car
                             acl2::posp-redefinition
                             lookup-id-out-of-bounds
                             not
                             default-<-2
                             ;; fanin-if-co-when-output
                             satlink::equal-of-lit-negate-cond-component-rewrites
                             satlink::equal-of-lit-negate-component-rewrites)))
  (def-gatesimp-thms (x0 x1)
    :eval-spec (b-xor (lit-eval x0 invals regvals aignet)
                      (lit-eval x1 invals regvals aignet))
    :syntax-hyp (and (equal (id->type (lit-id x0) aignet) (gate-type))
                   (equal (id->type (lit-id x1) aignet) (gate-type)))
    :measure-hyp (and (equal (id->type (lit-id x0) aignet) (gate-type))
                      (equal (id->type (lit-id x1) aignet) (gate-type)))
    :eval-hints ((and stable-under-simplificationp
                      '(:expand ((lit-eval x0 invals regvals aignet)
                                 (id-eval (lit-id x0) invals regvals aignet)
                                 (lit-eval x1 invals regvals aignet)
                                 (id-eval (lit-id x1) invals regvals aignet)
                                 (:free (x y) (eval-and-of-lits x y invals regvals aignet))
                                 (:free (x y) (eval-xor-of-lits x y invals regvals aignet))))))
    :use-aignet t))

(define reduce-xor-gate-normalized ((x0 litp :type (unsigned-byte 30))
                                    (x1 litp :type (unsigned-byte 30))
                                    (gatesimp gatesimp-p :type (unsigned-byte 6))
                                    (aignet))
  :guard (and (fanin-litp x0 aignet)
              (fanin-litp x1 aignet))
  :returns (mv (code maybe-simpcode-p)
               (new0 litp :rule-classes :type-prescription)
               (new1 litp :rule-classes :type-prescription))
  (b* ((ans (gate-reduce (xor x0 x1) :level 1))
       ((when ans) (mv (simpcode! :existing) ans 0))
       ((when (<= (gatesimp->level gatesimp) 1))
        (mv nil 0 0))
       (x0-type (id->type (lit->var^ x0) aignet))
       (x1-type (id->type (lit->var^ x1) aignet))
       ((when (=2 x0-type (gate-type)))
        (if (=2 x1-type (gate-type))
            (reduce-xor-gate-when-both-gates x0 x1 gatesimp aignet)
          (reduce-xor-gate-when-one-gate x0 x1 gatesimp aignet))))
    (if (=2 x1-type (gate-type))
        (reduce-xor-gate-when-one-gate x1 x0 gatesimp aignet)
      (mv nil 0 0)))
  ///
  (def-gatesimp-thms (x0 x1)
    :eval-spec (b-xor (lit-eval x0 invals regvals aignet)
                      (lit-eval x1 invals regvals aignet))
    :use-aignet t))

(define reduce-xor-gate ((x0 litp :type (unsigned-byte 30))
                         (x1 litp :type (unsigned-byte 30))
                         (gatesimp gatesimp-p :type (unsigned-byte 6))
                         (aignet))
  :guard (and (fanin-litp x0 aignet)
              (fanin-litp x1 aignet))
  :returns (mv (code maybe-simpcode-p)
               (new0 litp :rule-classes :type-prescription)
               (new1 litp :rule-classes :type-prescription))
  :prepwork ((local (in-theory (enable unsigned-byte-p-of-lit-when-lit->var))))
  (b* (((mv code new0 new1) (reduce-xor-gate-normalized (lit-abs^ x0) (lit-abs^ x1) gatesimp aignet))
       ((when code)
        (mv (simpcode-negate-cond code (b-xor (lit->neg^ x0) (lit->neg^ x1))) new0 new1)))
    (mv nil 0 0))
  ///
  (def-gatesimp-thms (x0 x1)
    :eval-spec (b-xor (lit-eval x0 invals regvals aignet)
                      (lit-eval x1 invals regvals aignet))
    :use-aignet t))



(local (defthm !simpcode->neg-of-simpcode->neg
         (implies (equal neg (simpcode->neg x))
                  (equal (!simpcode->neg neg x)
                         (simpcode-fix x)))
         :hints(("Goal" :in-theory (enable !simpcode->neg-is-simpcode
                                           simpcode-fix-in-terms-of-simpcode)))))

(local (defthm !simpcode->identity-of-simpcode->identity
         (implies (equal identity (simpcode->identity x))
                  (equal (!simpcode->identity identity x)
                         (simpcode-fix x)))
         :hints(("Goal" :in-theory (enable !simpcode->identity-is-simpcode
                                           simpcode-fix-in-terms-of-simpcode)))))

(local (defthm !simpcode->choice-of-simpcode->choice
         (implies (equal choice (simpcode->choice x))
                  (equal (!simpcode->choice choice x)
                         (simpcode-fix x)))
         :hints(("Goal" :in-theory (enable !simpcode->choice-is-simpcode
                                           simpcode-fix-in-terms-of-simpcode)))))

(define normalize-xor-gate ((code-in simpcode-p)
                            (x0 litp :type (unsigned-byte 30))
                            (x1 litp :type (unsigned-byte 30)))
  :returns (mv (code simpcode-p)
               (new0 litp :rule-classes :type-prescription)
               (new1 litp :rule-classes :type-prescription))
  :guard (and (=b 0 (simpcode->identity code-in))
              (=b 0 (simpcode->choice code-in)))
  :prepwork ((local (in-theory (enable unsigned-byte-p-of-lit-when-lit->var))))
  (b* (((simpcode code-in) (mbe :logic (!simpcode->choice 0 (!simpcode->identity 0 code-in))
                                :exec code-in)))
    (if (=b 1 code-in.xor)
        (mv (simpcode-negate-cond code-in (b-xor (lit->neg^ x0) (lit->neg^ x1)))
            (lit-abs^ x0) (lit-abs^ x1))
      (mv (simpcode-fix code-in) (lit-fix x0) (lit-fix x1))))
  ///
  (def-gatesimp-thms (x0 x1)
    :eval-spec (simpcode-eval code-in x0 x1 invals regvals aignet)
    :eval-hyp (equal 0 (simpcode->identity code-in))
    :maybe-simpcode nil
    :no-measure t
    :eval-hints (("goal" :expand ((:free (x0 x1) (simpcode-eval code-in x0 x1 invals regvals aignet)))
                  :in-theory (enable eval-xor-of-lits))))

  (defret two-id-measure-of-<fn>
    (equal (two-id-measure (lit-id new0) (lit-id new1))
           (two-id-measure (lit-id x0) (lit-id x1)))
    :hints(("Goal" :in-theory (enable two-id-measure)))))




(defsection aignet-addr-combine
  ;; Combining two integers into one (generally fixnum) key for hashing:
  ;; This is the same as hl-addr-combine (in books/system/hl-addr-combine.lisp)
  ;; but we don't need to prove anything about it here beyond verifying
  ;; guards (which are simpler here because we don't need the MBE).

  #!ACL2
  (local (defthm +-of-logcons-with-cin
           (implies (bitp cin)
                    (equal (+ cin
                              (logcons b1 r1)
                              (logcons b2 r2))
                           (logcons (b-xor cin (b-xor b1 b2))
                                    (+ (b-ior (b-and cin b1)
                                              (b-ior (b-and cin b2)
                                                     (b-and b1 b2)))
                                       (ifix r1)
                                       (ifix r2)))))
           :hints(("Goal" :in-theory (enable logcons b-ior b-and b-xor b-not)))))
  (local
   (defthm logior-to-plus
     (implies (and (natp a)
                   (integerp b)
                   (natp n)
                   (< a (ash 1 n)))
              (equal (logior a (ash b n))
                     (+ a (ash b n))))
     :hints(("Goal" :in-theory (e/d* (acl2::ihsext-inductions)
; (acl2::ash-1-removal)
                                     )
             :induct (logbitp n a)
             :expand ((:free (b) (ash b n))
                      (:free (b) (logior a b))))
            (and stable-under-simplificationp
                 '(:use ((:instance acl2::+-of-logcons-with-cin
                          (acl2::b1 (acl2::logcar a))
                          (acl2::r1 (acl2::logcdr a))
                          (acl2::b2 0)
                          (acl2::r2 (ash b (+ -1 n)))
                          (acl2::cin 0))))))))

  (local (defthm floor-of-1
           (implies (natp n)
                    (equal (floor n 1) n))
           :hints(("Goal" :in-theory (enable floor)))))

  (define aignet-addr-combine ((a :type (unsigned-byte 30))
                               (b :type (unsigned-byte 30)))
    :verify-guards nil
    (the (signed-byte 61)
         (- (the (signed-byte 61)
                 (logior (the (signed-byte 61)
                              (ash (the (signed-byte 31) a) 30))
                         (the (signed-byte 31) b))))))

  (local (in-theory (enable aignet-addr-combine)))

  (verify-guards aignet-addr-combine
    :hints ((and stable-under-simplificationp
                 '(:in-theory (enable ash unsigned-byte-p))))
    :otf-flg t))

(defsection strash
  (defstobj strash
    (strashtab :type (hash-table eql))
    :inline t)

  ;; returns (mv exists key id).
  ;; exists implies that id is a gate with the two specified fanins.
  (define strash-lookup ((lit1 litp :type (unsigned-byte 30))
                         (lit2 litp :type (unsigned-byte 30))
                         (xorp bitp :type bit)
                         strash aignet)
    :split-types t
    :inline t
    :guard (and (fanin-litp lit1 aignet)
                (fanin-litp lit2 aignet))
    :returns (mv (found)
                 (key integerp :rule-classes :type-prescription)
                 (id natp :rule-classes :type-prescription))
    (b* ((key (aignet-addr-combine (lit-fix lit1) (lit-fix lit2)))
         (id (strashtab-get key strash))
         ((when id)
          (b* (((unless (and (natp id)
                             (id-existsp id aignet)
                             (=2 (id->type id aignet) (gate-type))
                             (=b (id->regp id aignet) (lbfix xorp))
                             (=30 (gate-id->fanin0 id aignet) (lit-fix lit1))
                             (=30 (gate-id->fanin1 id aignet) (lit-fix lit2))))
                (break$)
                (er hard? 'strash-lookup "Strash lookup found bogus value!")
                (mv nil key 0)))
            (mv t key id))))
      (mv nil key 0))
    ///

    (defthm strash-lookup-correct
      (b* (((mv found & id) (strash-lookup lit1 lit2 xorp strash aignet)))
        (implies found
                 (and (aignet-idp id aignet)
                      (aignet-litp (mk-lit id bit) aignet)
                      (b* ((suff (lookup-id id aignet))
                           (node (car suff)))
                        (and (equal (stype node)
                                    (if (bit->bool xorp) :xor :and))
                             (equal (fanin :gate0 suff)
                                    (lit-fix lit1))
                             (equal (fanin :gate1 suff)
                                    (lit-fix lit2)))))))
      :hints(("Goal" :in-theory (enable aignet-litp))))

    (local (defret unsigned-byte-p-of-strash-lookup-1
             (implies (and found
                           (< (fanin-count aignet) #x1fffffff))
                      (unsigned-byte-p 29 id))
             :hints(("Goal" :in-theory (e/d (unsigned-byte-p aignet-idp)
                                            (lookup-id-consp-forward-to-id-bound))))))

    (defret unsigned-byte-p-of-strash-lookup
      (implies (and found
                    (< (fanin-count aignet) #x1fffffff)
                    (natp n)
                    (<= 29 n))
               (unsigned-byte-p n id))
      :hints(("Goal" :in-theory (e/d ()
                                     (unsigned-byte-p-of-strash-lookup-1
                                      strash-lookup))
              :use unsigned-byte-p-of-strash-lookup-1)))

    (defcong list-equiv equal (strash-lookup lit1 lit2 xorp strash aignet) 4)))




(define aignet-strash-gate ((code-in simpcode-p)
                            (x0 litp :type (unsigned-byte 30))
                            (x1 litp :type (unsigned-byte 30))
                            (hashp) ;; from gatesimp
                            (strash)
                            (aignet))
  :guard (and (fanin-litp x0 aignet)
              (fanin-litp x1 aignet)
              (=b 0 (simpcode->choice code-in)))
  :returns (mv (code simpcode-p)
               (key integerp :rule-classes :type-prescription)
               (new0 litp :rule-classes :type-prescription)
               (new1 litp :rule-classes :type-prescription))
  (b* (((simpcode code) (the (unsigned-byte 4) (mbe :logic (!simpcode->choice 0 code-in)
                                                    :exec code-in)))
       ((when (=b code.identity 1))
        ;; BOZO if code-in is identity then there's no need to call this fn --
        ;; maybe just have an assumption that it's not?
        (mv code 0 (lit-fix x0) (lit-fix x1)))
       ;; normalize order -- lesser goes first for AND, greater first for XOR
       ((mv x0 x1) (if (xor (=b 1 code.xor)
                            (< (lit-fix x0) (lit-fix x1)))
                       (mv x0 x1)
                     (mv x1 x0)))
       ((unless hashp)
        (mv code 0 (lit-fix x0) (lit-fix x1)))
       ((mv found key id) (strash-lookup x0 x1 code.xor strash aignet))
       ((when found)
        (mv (simpcode! :existing) key (mk-lit id code.neg) 0)))
    (mv code key (lit-fix x0) (lit-fix x1)))
  ///
  (defret aignet-litp-of-<fn>
    (implies (and (aignet-litp x0 aignet)
                  (aignet-litp x1 aignet))
             (and (aignet-litp new0 aignet)
                  (aignet-litp new1 aignet))))

  (defret deps-of-<fn>
    (implies (and (not (depends-on (lit->var x0) ci-id aignet))
                  (not (depends-on (lit->var x1) ci-id aignet)))
             (and (not (depends-on (lit->var new0) ci-id aignet))
                  (not (depends-on (lit->var new1) ci-id aignet))))
    :hints (("goal" :expand ((:Free (a b c)
                              (depends-on (mv-nth 2 (strash-lookup a b c strash aignet)) ci-id aignet))))))

  (defret eval-of-<fn>
    (equal (simpcode-eval code new0 new1 invals regvals aignet)
           (simpcode-eval code-in x0 x1 invals regvals aignet))
    :hints (("Goal" :expand ((:free (x n) (lit-eval (make-lit x n) invals regvals aignet))
                             (:free (x0 x1 xor strash)
                              (id-eval (mv-nth 2 (strash-lookup x0 x1 xor strash aignet))
                                       invals regvals aignet))
                             (:free (x0 x1) (simpcode-eval code-in x0 x1 invals regvals aignet))))
            (and stable-under-simplificationp
                 '(:in-theory (enable eval-xor-of-lits
                                      eval-and-of-lits)))))

  (defret width-of-<fn>
    (implies (and (< (fanin-count aignet) #x1fffffff)
                  (natp n)
                  (<= 30 n)
                  (unsigned-byte-p 30 (lit-fix x0))
                  (unsigned-byte-p 30 (lit-fix x1)))
             (and (unsigned-byte-p n new0)
                  (unsigned-byte-p n new1)))
    :hints(("Goal" :in-theory (enable unsigned-byte-p-of-lit-when-lit->var))))

  (defret choice-of-<fn>
    (equal (simpcode->choice code) 0)))



(define reduce-gate-rec ((code-in simpcode-p)
                         (x0 litp :type (unsigned-byte 30))
                         (x1 litp :type (unsigned-byte 30))
                         (gatesimp gatesimp-p :type (unsigned-byte 6))
                         (strash)
                         (aignet))
  :guard (and (fanin-litp x0 aignet)
              (fanin-litp x1 aignet)
              (=b 0 (simpcode->choice code-in)))
  :returns (mv (code simpcode-p)
               (key integerp :rule-classes :type-prescription)
               (new0 litp :rule-classes :type-prescription)
               (new1 litp :rule-classes :type-prescription))
  :measure (if (eql 1 (simpcode->identity code-in))
               0
             (two-id-measure (lit-id x0) (lit-id x1)))
  :verify-guards nil
  (b* (((simpcode code-in) (the (unsigned-byte 4)
                                (mbe :logic (!simpcode->choice 0 code-in)
                                     :exec code-in)))
       ((unless (mbt (and (fanin-litp x0 aignet)
                          (fanin-litp x1 aignet))))
        (mv code-in 0 (lit-fix x0) (lit-fix x1)))
       ((when (=b 1 code-in.identity))
        (mv code-in 0 (lit-fix x0) (lit-fix x1)))
       ((when (=b 1 code-in.xor))
        (b* (((mv new-code new-x0 new-x1)
              (reduce-xor-gate x0 x1 gatesimp aignet))
             ((unless new-code)
              (b* (((mv new-code new-x0 new-x1)
                    (normalize-xor-gate code-in x0 x1)))
                (aignet-strash-gate new-code new-x0 new-x1 (gatesimp->hashp gatesimp) strash aignet)))
             (new-code (simpcode-negate-cond new-code code-in.neg)))
          (reduce-gate-rec new-code new-x0 new-x1 gatesimp strash aignet)))
       ((mv new-code new-x0 new-x1 new-x2 new-x3)
        (reduce-and-gate x0 x1 gatesimp aignet))
       ((unless new-code)
        (aignet-strash-gate code-in x0 x1 (gatesimp->hashp gatesimp) strash aignet))
       (new-code (simpcode-negate-cond new-code code-in.neg))
       ((when (=b 0 (simpcode->choice new-code)))
        (reduce-gate-rec new-code new-x0 new-x1 gatesimp strash aignet))
       (new-code (!simpcode->choice 0 new-code))
       ((mv new-code1 new-key1 new-x0-1 new-x1-1)
        (reduce-gate-rec new-code new-x0 new-x1 gatesimp strash aignet))
       ((when (=b 1 (simpcode->identity new-code1)))
        (mv new-code1 new-key1 new-x0-1 new-x1-1)))
    (reduce-gate-rec new-code new-x2 new-x3 gatesimp strash aignet))
  ///
  (verify-guards reduce-gate-rec)

  (def-gatesimp-thms (x0 x1)
    :eval-spec (simpcode-eval code-in x0 x1 invals regvals aignet)
    :no-measure t
    :no-bound t
    :use-aignet t
    :maybe-simpcode nil
    :width-hyp (< (FANIN-COUNT AIGNET) 536870911)
    ;; :choice-hyp (equal (simpcode->choice code-in) 0)
    ;; :eval-hyp (equal (simpcode->choice code-in) 0)
    :eval-hints (("goal" :induct <call> :expand (<call>)
                  ;; :in-theory (enable eval-xor-of-lits
                  ;;                    eval-and-of-lits)
                  )
                 (and stable-under-simplificationp
                      '(:expand ((simpcode-eval code-in x0 x1 invals regvals aignet))))
                 (and stable-under-simplificationp
                      '(:in-theory (enable eval-xor-of-lits
                                           eval-and-of-lits)))
                 )))

;; (define reduce-xor-gate-rec ((x0 litp :type (unsigned-byte 30))
;;                              (x1 litp :type (unsigned-byte 30))
;;                              (gatesimp gatesimp-p :type (unsigned-byte 6))
;;                              (strash)
;;                              (aignet))
;;   :guard (and (fanin-litp x0 aignet)
;;               (fanin-litp x1 aignet))
;;   :enabled t
;;   (reduce-gate-rec (simpcode! :xor) x0 x1 gatesimp strash aignet))

;; (define reduce-and-gate-rec ((x0 litp :type (unsigned-byte 30))
;;                              (x1 litp :type (unsigned-byte 30))
;;                              (gatesimp gatesimp-p :type (unsigned-byte 6))
;;                              strash
;;                              (aignet))
;;   :guard (and (fanin-litp x0 aignet)
;;               (fanin-litp x1 aignet))
;;   :enabled t
;;   (reduce-gate-rec (simpcode! :and) x0 x1 gatesimp strash aignet))






(define aignet-xor-gate-simp/strash ((x0 litp :type (unsigned-byte 30))
                                     (x1 litp :type (unsigned-byte 30))
                                     (gatesimp gatesimp-p :type (unsigned-byte 6))
                                     (strash)
                                     (aignet))
  :guard (and (fanin-litp x0 aignet)
              (fanin-litp x1 aignet))
  :split-types t
  :returns (mv (code simpcode-p)
               (key integerp :rule-classes :type-prescription)
               (new0 litp :rule-classes :type-prescription)
               (new1 litp :rule-classes :type-prescription))
  (reduce-gate-rec (simpcode! :xor) x0 x1 gatesimp strash aignet)
  ///
  
  (defret aignet-litp-of-<fn>
    (implies (and (aignet-litp x0 aignet)
                  (aignet-litp x1 aignet))
             (and (aignet-litp new0 aignet)
                  (aignet-litp new1 aignet))))

  (defret deps-of-<fn>
    (implies (and (not (depends-on (lit->var x0) ci-id aignet))
                  (not (depends-on (lit->var x1) ci-id aignet)))
             (and (not (depends-on (lit->var new0) ci-id aignet))
                  (not (depends-on (lit->var new1) ci-id aignet)))))


  (defret eval-of-<fn>
    (equal (simpcode-eval code new0 new1 invals regvals aignet)
           (eval-xor-of-lits x0 x1 invals regvals aignet)))
  
  (defret width-of-<fn>
    (implies (and (unsigned-byte-p 30 (lit-fix x0))
                  (unsigned-byte-p 30 (lit-fix x1))
                  (< (fanin-count aignet) #x1fffffff))
             (and (unsigned-byte-p 30 new0)
                  (unsigned-byte-p 30 new1))))

  (defret choice-of-<fn>
    (equal (simpcode->choice code) 0)))


(define aignet-and-gate-simp/strash ((x0 litp :type (unsigned-byte 30))
                                     (x1 litp :type (unsigned-byte 30))
                                     (gatesimp gatesimp-p :type (unsigned-byte 6))
                                     (strash)
                                     (aignet))
  :guard (and (fanin-litp x0 aignet)
              (fanin-litp x1 aignet))
  :split-types t
  :returns (mv (code simpcode-p)
               (key integerp :rule-classes :type-prescription)
               (new0 litp :rule-classes :type-prescription)
               (new1 litp :rule-classes :type-prescription))
  (reduce-gate-rec (simpcode! :and) x0 x1 gatesimp strash aignet)
  ///
  
  (defret aignet-litp-of-<fn>
    (implies (and (aignet-litp x0 aignet)
                  (aignet-litp x1 aignet))
             (and (aignet-litp new0 aignet)
                  (aignet-litp new1 aignet))))

  (defret deps-of-<fn>
    (implies (and (not (depends-on (lit->var x0) ci-id aignet))
                  (not (depends-on (lit->var x1) ci-id aignet)))
             (and (not (depends-on (lit->var new0) ci-id aignet))
                  (not (depends-on (lit->var new1) ci-id aignet)))))

  (defret eval-of-<fn>
    (equal (simpcode-eval code new0 new1 invals regvals aignet)
           (eval-and-of-lits x0 x1 invals regvals aignet)))

  
  (defret width-of-<fn>
    (implies (and (unsigned-byte-p 30 (lit-fix x0))
                  (unsigned-byte-p 30 (lit-fix x1))
                  (< (fanin-count aignet) #x1fffffff))
             (and (unsigned-byte-p 30 new0)
                  (unsigned-byte-p 30 new1))))

  (defret choice-of-<fn>
    (equal (simpcode->choice code) 0)))


;; (defthm aignet-litp-of-new-node
;;   (implies (not (equal (ctype (stype new-node)) (out-ctype)))
;;            (aignet-litp (make-lit (+ 1 (fanin-count aignet)) neg)
;;                         (cons new-node aignet)))
;;   :hints(("Goal" :in-theory (enable aignet-litp))))



(define aignet-install-gate ((code-in simpcode-p)
                             (key integerp)
                             (x0 litp :type (unsigned-byte 30))
                             (x1 litp :type (unsigned-byte 30))
                             (gatesimp gatesimp-p :type (unsigned-byte 6))
                             (strash)
                             (aignet))
  :guard (and (fanin-litp x0 aignet)
              (fanin-litp x1 aignet))
  :guard-debug t
  :returns (mv (lit litp :rule-classes :type-prescription)
               (new-strash)
               (new-aignet))
  (b* (((simpcode code) (the (unsigned-byte 4) (simpcode-fix code-in)))
       ((when (=b 1 code.identity))
        (b* ((aignet (mbe :logic (non-exec (node-list-fix aignet)) :exec aignet)))
          (mv (lit-negate-cond^ x0 code.neg) strash aignet)))
       (id (num-fanins aignet))
       (aignet (if (=b 1 code.xor)
                   (aignet-add-xor x0 x1 aignet)
                 (aignet-add-and x0 x1 aignet)))
       (lit (mk-lit id code.neg))
       (strash (if (gatesimp->hashp (the (unsigned-byte 6) gatesimp))
                   (strashtab-put (lifix key) id strash)
                 strash)))
    (mv lit strash aignet))
  ///
  (def-aignet-preservation-thms aignet-install-gate)

  (defret aignet-litp-of-aignet-install-gate
    (implies (and (aignet-litp x0 aignet)
                  (aignet-litp x1 aignet))
             (aignet-litp lit new-aignet)))

  (defret deps-of-<fn>
    (implies (and (not (depends-on (lit->var x0) ci-id aignet))
                  (not (depends-on (lit->var x1) ci-id aignet)))
             (not (depends-on (lit->var lit) ci-id new-aignet)))
    :hints (("goal" :expand ((:free (node)
                              (depends-on (+ 1 (fanin-count aignet)) ci-id (cons node aignet)))))))

  (defret lit-eval-of-aignet-install-gate
    (equal (lit-eval lit invals regvals new-aignet)
           (simpcode-eval code-in x0 x1 invals regvals aignet))
    :hints (("goal" :expand ((:free (x n a b) (lit-eval (make-lit x n) invals regvals (cons a b)))
                             (simpcode-eval code-in x0 x1 invals regvals aignet))
             :in-theory (enable eval-and-of-lits-of-aignet-lit-fix-1
                                eval-and-of-lits-of-aignet-lit-fix-2
                                eval-xor-of-lits-of-aignet-lit-fix-1
                                eval-xor-of-lits-of-aignet-lit-fix-2
                                ))))

  (defret stype-counts-preserved-of-<fn>
    (implies (And (not (equal (stype-fix stype) :xor))
                  (not (equal (stype-fix stype) :and)))
             (equal (stype-count stype new-aignet)
                    (stype-count stype aignet))))

  (local (defthm u29-by-bound
           (implies (and (natp n)
                         (<= n #x1fffffff))
                    (unsigned-byte-p 29 n))))

  (defret unsigned-byte-p-of-aignet-install-gate
    (implies (and (unsigned-byte-p 30 x0)
                  (unsigned-byte-p 30 x1)
                  (< (fanin-count aignet) #x1fffffff))
             (unsigned-byte-p 30 lit))
    :hints(("Goal" :in-theory (enable unsigned-byte-p-of-lit-when-lit->var))))

  (defret fanin-count-of-aignet-install-gate
    (<= (fanin-count new-aignet) (+ 1 (fanin-count aignet)))
    :rule-classes :linear))

(local (in-theory (enable lit-eval-of-aignet-lit-fix)))

(define aignet-hash-and ((lit1 litp :type (unsigned-byte 30) "Literal to AND with lit2")
                         (lit2 litp :type (unsigned-byte 30))
                         (gatesimp gatesimp-p :type (unsigned-byte 6)
                                   "Configuration for how much simplification to try and whether to use hashing")
                         (strash "Stobj containing the aignet's structural hash table")
                         aignet)
  :split-types t
  :parents (aignet-construction)
  :short "Add an AND node to an AIGNET, or find a node already representing the required logical expression."
  :long "<p>See @(see aignet-construction).</p>"
  :guard (and (fanin-litp lit1 aignet)
              (fanin-litp lit2 aignet))
  :returns (mv (and-lit litp :rule-classes (:rewrite :type-prescription))
               (new-strash)
               (new-aignet))
  (b* ((lit1 (mbe :logic (non-exec (aignet-lit-fix lit1 aignet)) :exec lit1))
       (lit2 (mbe :logic (non-exec (aignet-lit-fix lit2 aignet)) :exec lit2))
       ((mv code key lit1 lit2)
        (aignet-and-gate-simp/strash lit1 lit2 gatesimp strash aignet)))
    (aignet-install-gate code key lit1 lit2 gatesimp strash aignet))

  ///

  ;; (defcong lit-equiv equal (aignet-hash-and lit1 lit2 gatesimp strash aignet) 1)
  ;; (defcong lit-equiv equal (aignet-hash-and lit1 lit2 gatesimp strash aignet) 2)
  ;; (defcong nat-equiv equal (aignet-hash-and lit1 lit2 gatesimp strash aignet) 3)

  (def-aignet-preservation-thms aignet-hash-and)

  (defret aignet-litp-of-aignet-hash-and
    (aignet-litp and-lit new-aignet))

  (defret deps-of-<fn>
    (implies (and (not (depends-on (lit->var lit1) ci-id aignet))
                  (not (depends-on (lit->var lit2) ci-id aignet)))
             (not (depends-on (lit->var and-lit) ci-id new-aignet))))

  (defret lit-eval-of-aignet-hash-and
    (equal (lit-eval and-lit invals regvals new-aignet)
           (b-and (lit-eval lit1 invals regvals aignet)
                  (lit-eval lit2 invals regvals aignet)))
    :hints(("Goal" :in-theory (enable eval-and-of-lits))))

  (defret stype-counts-preserved-of-aignet-hash-and
    (implies (and (not (equal (stype-fix stype) (and-stype)))
                  (not (equal (stype-fix stype) (xor-stype))))
             (equal (stype-count stype new-aignet)
                    (stype-count stype aignet))))

  (local (defthm unsigned-byte-p-when-aignet-litp-of-lit-fix
           (implies (and (aignet-litp lit aignet)
                         (< (fanin-count aignet) #x1fffffff))
                    (unsigned-byte-p 30 (lit-fix lit)))
           :hints (("goal" :use ((:instance unsigned-byte-p-when-aignet-litp
                                  (lit (lit-fix lit))))
                    :in-theory (disable unsigned-byte-p-when-aignet-litp)))))

  (local (defthm unsigned-byte-p-when-aignet-litp-bind
           (implies (and (bind-free '((aignet . aignet)))
                         (aignet-litp lit aignet)
                         (litp lit)
                         (< (fanin-count aignet) #x1fffffff))
                    (unsigned-byte-p 30 lit))))

  (local (defret unsigned-byte-p-of-aignet-hash-and-1
           (implies (and (< (fanin-count aignet) #x1fffffff))
                    (unsigned-byte-p 30 and-lit))
           ;; :hints ((and stable-under-simplificationp
           ;;              '(:use ((:instance unsigned-byte-p-when-aignet-litp
           ;;                       (lit and-lit) (aignet new-aignet)))
           ;;                :in-theory (disable unsigned-byte-p-when-aignet-litp))))
           ))
         
  (defret unsigned-byte-p-of-aignet-hash-and
    (implies (and (< (fanin-count aignet) #x1fffffff)
                  (natp n) (<= 30 n))
             (unsigned-byte-p n and-lit))
    :hints (("goal" :use unsigned-byte-p-of-aignet-hash-and-1
             :in-theory (disable unsigned-byte-p-of-aignet-hash-and-1))))

  (defret fanin-count-of-aignet-hash-and
    (<= (fanin-count new-aignet) (+ 1 (fanin-count aignet)))
    :rule-classes :linear))


(defines aignet-build-rec
  :mode :program
  (define aignet-build-rec (pattern next-var override-var rest-vars bindings-acc neg-fn)
    :returns (mv retval new-bindings-acc new-next-var)
    (b* (((when (atom pattern))
          (b* ((- (and (not (or (acl2::legal-variable-or-constant-namep pattern)
                                (integerp pattern) (booleanp pattern)))
                       (raise "Bad atom: ~x0" pattern)))
               (val (case pattern
                      ((t) 1)
                      ((nil) 0)
                      (t pattern)))
               ((unless override-var)
                (mv val bindings-acc next-var)))
            (mv override-var (cons (list override-var val) bindings-acc) next-var)))
         ((cons sym args) pattern))
      (case sym
        (:= (case-match args
              ((var expr)
               (b* ((- (and (not (acl2::legal-variablep var))
                            (raise "Bad variable binding: ~x0" var)))
                    ((mv & bindings-acc next-var)
                     (aignet-build-rec expr next-var var rest-vars bindings-acc neg-fn))
                    ((unless override-var)
                     (mv var bindings-acc next-var))
                    (bindings-acc (cons (list override-var var) bindings-acc)))
                 (mv override-var bindings-acc next-var)))
              (& (prog2$ (raise "Bad := form: ~x0" pattern)
                         (mv nil nil nil)))))
        ((and or xor iff) ;; associative/commutative ops
         (b* ((- (and (not (true-listp args))
                      (raise "Bad form: ~x0" pattern)))
              ((mv fn base-lit)
               (case sym
                 (and (mv 'aignet-hash-and 1))
                 (xor (mv 'aignet-hash-xor 0))
                 (or  (mv 'aignet-hash-or  0))
                 (iff (mv 'aignet-hash-iff 1))
                 (t   (mv nil nil))))
              ((when (atom args))
               (b* (((unless override-var)
                     (mv base-lit bindings-acc next-var)))
                 (mv override-var (cons (list override-var base-lit) bindings-acc) next-var))))
           (aignet-build-a/c-rec fn args next-var override-var rest-vars bindings-acc neg-fn)))
        ((if mux)
         (case-match args
           ((test then else)
            (b* (((mv test-var bindings-acc next-var)
                  (aignet-build-rec test next-var nil rest-vars bindings-acc neg-fn))
                 ((mv then-var bindings-acc next-var)
                  (aignet-build-rec then next-var nil rest-vars bindings-acc neg-fn))
                 ((mv else-var bindings-acc next-var)
                  (aignet-build-rec else next-var nil rest-vars bindings-acc neg-fn))
                 (expr `(aignet-hash-mux ,test-var ,then-var ,else-var . ,rest-vars))
                 ((mv var next-var)
                  (if override-var
                      (mv override-var next-var)
                    (mv (intern$ (coerce (explode-atom next-var 10) 'string) "AIGNET-GENSYMS")
                        (+ 1 next-var)))))
              (mv var
                  (cons `((mv ,var . ,(cdr rest-vars)) ,expr) bindings-acc)
                  next-var)))
           (& (prog2$ (raise "Bad form: ~x0" pattern)
                      (mv nil nil nil)))))
        (not
         (case-match args
           ((subexp) (b* (((mv sub-var bindings-acc next-var)
                           (aignet-build-rec subexp next-var nil rest-vars bindings-acc neg-fn))
                          ((unless override-var)
                           (mv `(,neg-fn ,sub-var) bindings-acc next-var)))
                       (mv override-var
                           (cons `(,override-var (,neg-fn ,sub-var)) bindings-acc)
                           next-var)))
           (& (prog2$ (raise "Bad form: ~x0" pattern)
                      (mv nil nil nil)))))
        (otherwise
         (prog2$ (raise "Bad form: ~x0" pattern)
                 (mv nil nil nil))))))

  (define aignet-build-a/c-rec (fn args next-var override-var rest-vars bindings-acc neg-fn)
    :returns (mv retval new-bindings-acc new-next-var)
    (b* (((when (atom (cdr args)))
          (aignet-build-rec (car args) next-var override-var rest-vars bindings-acc neg-fn))
         ((mv arg1-var bindings-acc next-var)
          (aignet-build-rec (car args) next-var nil rest-vars bindings-acc neg-fn))
         ((mv rest-var bindings-acc next-var)
          (aignet-build-a/c-rec fn (cdr args) next-var nil rest-vars bindings-acc neg-fn))
         (expr `(,fn ,arg1-var ,rest-var . ,rest-vars))
         ((mv var next-var)
          (if override-var
              (mv override-var next-var)
            (mv (intern$ (coerce (explode-atom next-var 10) 'string) "AIGNET-GENSYMS")
                (+ 1 next-var)))))
      (mv var (cons `((mv ,var . ,(cdr rest-vars)) ,expr) bindings-acc) next-var))))


(defmacro aignet-build (pattern gatesimp strash aignet)
  (b* (((mv retval bindings ?next-var) (aignet-build-rec pattern 0 nil (list gatesimp strash aignet) nil 'lit-negate)))
    `(b* ,(reverse bindings)
       (mv ,retval ,strash ,aignet))))

(defmacro aignet-build^ (pattern gatesimp strash aignet)
  (b* (((mv retval bindings ?next-var) (aignet-build-rec pattern 0 nil (list gatesimp strash aignet) nil 'lit-negate^)))
    `(b* ,(reverse bindings)
       (mv ,retval ,strash ,aignet))))

(define aignet-hash-xor ((lit1 litp :type (unsigned-byte 30) "Literal to XOR with lit2")
                         (lit2 litp :type (unsigned-byte 30))
                         (gatesimp gatesimp-p :type (unsigned-byte 6)
                                   "Configuration for how much simplification to try and whether to use hashing")
                         (strash "Stobj containing the aignet's structural hash table")
                         aignet)
  :split-types t
  :parents (aignet-construction)
  :short "Add an XOR node to an AIGNET, or find a node already representing the required logical expression."
  :long "<p>See @(see aignet-construction).</p>"
  :guard (and (fanin-litp lit1 aignet)
              (fanin-litp lit2 aignet))
  :returns (mv (xor-lit litp :rule-classes (:rewrite :type-prescription))
               (new-strash)
               (new-aignet))
  :prepwork ((local (in-theory (enable unsigned-byte-p-of-lit-when-lit->var))))
  (b* ((lit1 (mbe :logic (non-exec (aignet-lit-fix lit1 aignet)) :exec lit1))
       (lit2 (mbe :logic (non-exec (aignet-lit-fix lit2 aignet)) :exec lit2))
       ((when (eql 0 (gatesimp->xor-mode gatesimp)))
        ;; In this mode, don't build xor gates even explicitly.
        ;; Need to fix these for non-atomic operations
        (aignet-build (and (not (and lit1 lit2)) (not (and (not lit1) (not lit2))))
                      gatesimp strash aignet))
       ((mv code key lit1 lit2)
        (aignet-xor-gate-simp/strash lit1 lit2 gatesimp strash aignet)))
    (aignet-install-gate code key lit1 lit2 gatesimp strash aignet))

  ///

  ;; (defcong lit-equiv equal (aignet-hash-and lit1 lit2 gatesimp strash aignet) 1)
  ;; (defcong lit-equiv equal (aignet-hash-and lit1 lit2 gatesimp strash aignet) 2)
  ;; (defcong nat-equiv equal (aignet-hash-and lit1 lit2 gatesimp strash aignet) 3)

  (def-aignet-preservation-thms aignet-hash-xor)

  (defret aignet-litp-of-aignet-hash-xor
    (aignet-litp xor-lit new-aignet))

  (defret deps-of-<fn>
    (implies (and (not (depends-on (lit->var lit1) ci-id aignet))
                  (not (depends-on (lit->var lit2) ci-id aignet)))
             (not (depends-on (lit->var xor-lit) ci-id new-aignet))))

  (defret lit-eval-of-aignet-hash-xor
    (equal (lit-eval xor-lit invals regvals new-aignet)
           (b-xor (lit-eval lit1 invals regvals aignet)
                  (lit-eval lit2 invals regvals aignet)))
    :hints(("Goal" :in-theory (enable eval-xor-of-lits))
           (and stable-under-simplificationp
                '(:in-theory (enable b-xor b-not)))))

  (defret stype-counts-preserved-of-aignet-hash-xor
    (implies (and (not (equal (stype-fix stype) (and-stype)))
                  (not (equal (stype-fix stype) (xor-stype))))
             (equal (stype-count stype new-aignet)
                    (stype-count stype aignet))))

  (local (defthm unsigned-byte-p-when-aignet-litp-of-lit-fix
           (implies (and (aignet-litp lit aignet)
                         (< (fanin-count aignet) #x1fffffff))
                    (unsigned-byte-p 30 (lit-fix lit)))
           :hints (("goal" :use ((:instance unsigned-byte-p-when-aignet-litp
                                  (lit (lit-fix lit))))
                    :in-theory (disable unsigned-byte-p-when-aignet-litp)))))

  (local (defret unsigned-byte-p-of-aignet-hash-xor-1
           (implies (and (< (fanin-count aignet) #x1ffffffd))
                    (unsigned-byte-p 30 xor-lit))
           :hints (("goal" :use ((:instance unsigned-byte-p-when-aignet-litp
                                  (lit xor-lit) (aignet new-aignet)))
                    :in-theory (disable unsigned-byte-p-when-aignet-litp)))))

  (defret unsigned-byte-p-of-aignet-hash-xor
    (implies (and (< (fanin-count aignet) #x1ffffffd)
                  (natp n) (<= 30 n))
             (unsigned-byte-p n xor-lit))
    :hints (("goal" :use unsigned-byte-p-of-aignet-hash-xor-1
             :in-theory (disable unsigned-byte-p-of-aignet-hash-xor-1 aignet-hash-xor)))))







(define aignet-populate-strash ((n natp)
                                (strash)
                                (aignet))
  :returns (new-strash)
  :guard (<= n (num-fanins aignet))
  :measure (nfix (- (+ (num-fanins aignet)) (nfix n)))
  :guard-hints (("goal" :in-theory (enable aignet-idp)))
  (b* (((when (mbe :logic (zp (- (num-fanins aignet) (nfix n)))
                   :exec (eql n (num-fanins aignet))))
        strash)
       (slot0 (id->slot0 n aignet))
       (slot1 (id->slot1 n aignet))
       (type (snode->type slot0))
       ((unless (eql type (gate-type)))
        (aignet-populate-strash (+ 1 (lnfix n)) strash aignet))
       (lit0 (snode->fanin slot0))
       (lit1 (snode->fanin slot1))
       (xor  (snode->regp slot1))
       ((mv foundp key ?id) (strash-lookup lit0 lit1 xor strash aignet))
       ((when foundp)
        (aignet-populate-strash (+ 1 (lnfix n)) strash aignet))
       (strash (strashtab-put key n strash)))
    (aignet-populate-strash (+ 1 (lnfix n)) strash aignet)))



(defsection aignet-construction
  :parents (aignet)
  :short "How to construct an AIGNET network."
  :autodoc nil
  :long "
<p>An AIGNET network is constructed by adding nodes in topological
order: that is, an AND gate cannot be added until its two fanins are created,
and a combinational output cannot be added until its fanin exists.
Additionally, a register input cannot be added until its corresponding register
output exists.</p>

<p>First, because an AIGNET network is represented in a stobj, you must either
work on the \"live\" @('AIGNET') stobj or else create a local one using
@(see with-local-stobj).</p>

<p>Usually when constructing an AIG network one wants to structurally hash the
AND nodes, so as to avoid creating duplicate nodes with identical structure.
To do this, you additionally need a @('STRASH') stobj, which again may either
be the live one or one created locally.</p>

<h3>Basic Low-level Construction Functions</h3>

<p>To initialize a new network or clear an existing one, use:
@({ (aignet-clear aignet) })
or, to allocate a certain amount of space in order to avoid resizing arrays,
@({ (aignet-init output-cap reg-cap input-cap node-cap aignet). })</p>

<p>To initialize a strash object or clear an existing one, use:
@({ (strashtab-clear strash) })
or to allocate a certain amount of space to avoid resizing the hash table,
@({ (strashtab-init node-cap nil nil strash). })</p>

<h1>Aignet-construction functions</h1>
<p>@('(aignet-add-in aignet)') adds a new primary input node to the network and
returns <tt>(mv lit aignet)</tt>, where <tt>lit</tt> is the non-negated literal of
the new node.</p>

<p>@('(aignet-add-reg aignet)') adds a new register output node to the network and
returns <tt>(mv lit aignet)</tt>, where <tt>lit</tt> is the non-negated literal of
the new node.</p>

<p>@('(aignet-add-and lit1 lit2 aignet)') adds to the network a new AND node
conjoining <tt>lit1</tt> and <tt>lit2</tt>, and returns <tt>(mv lit aignet)</tt>,
where <tt>lit</tt> is the non-negated literal of the new node.  <tt>lit1</tt>
and <tt>lit2</tt> must be literals of the network, satisfying
@('aignet-litp') (which is true of any literal returned by a node construction
function, or its negation).  Note: this function does not do structural
hashing -- for that, see below.</p>

<p>@('(aignet-add-xor lit1 lit2 aignet)') is similar to @('aignet-add-and'),
but makes an XOR node rather than an AND.  It also does not to structural
hashing.</p>

<p>@('(aignet-add-out lit aignet)') adds to the network a new primary output with
fanin <tt>lit</tt>, and returns <tt>aignet</tt>.  (It does not return a literal
because a combinational output node is not allowed to be the fanin to another
node.)  <tt>lit</tt> must satisfy @('aignet-litp').</p>

<p>@('(aignet-set-nxst lit ro aignet)') adds to the network a new register input
with fanin <tt>lit</tt>, and connects it to a register output node whose ID is
<tt>ro</tt>.  It returns <tt>aignet</tt>.  <tt>lit</tt> must satisfy @('aignet-litp')
and <tt>ro</tt> must be the ID of a register output node that is not yet
connected to a register input.</p>

<h3>Hashing and Simplifying Constructor Functions</h3>

<p>The following functions:
@({
    (aignet-hash-and f1 f2 gatesimp strash aignet)
    (aignet-hash-or  f1 f2 gatesimp strash aignet)
    (aignet-hash-xor f1 f2 gatesimp strash aignet)
    (aignet-hash-iff f1 f2 gatesimp strash aignet)
    (aignet-hash-mux c tb fb gatesimp strash aignet) })

add nodes implementing the respective functions of input literals <tt>f1</tt>
and <tt>f2</tt> (for and/or/xor) and <tt>c</tt>, <tt>tb</tt>, and <tt>fb</tt>
for mux (signifying condition, true-branch, and false-branch), possibly with
structural hashing and lightweight simplification.  All return <code>(mv lit
strash aignet).</code> Gatesimp is a @(see gatesimp) object that specifies
whether to structurally hash the nodes, what level of effort to use in Boolean
simplification (between 0 and 4), and whether to use XOR nodes at all and if so
whether to derive them from AND nodes.  The levels of simplification correspond
to the paper:

<blockquote>
R. Brummayer and A. Biere.  Local two-level And-Inverter Graph minimization
without blowup.  Proc. MEMCIS 6 (2006): 32-38,
</blockquote>

available <a
href=\"http://megaknowledge.info/cadathlon/2007/refs/p5-verification.pdf\">here</a>.
These simplifications look at most one level deep at the fanins of each AND,
that is, examining at most four fanin nodes.  Usually at least level 1 is
desirable; level 1 deals with ANDs of constants and identical and negated
nodes.  Practically, we think for most applications building the AIGs is not a
performance bottleneck and level 3 or 4 can be used with some potential benefit
and no noticeable slowdown.</p>

<h3>@('aignet-build') macro</h3>

<p>See also @(see aignet-build), a macro that lays out the calls necessary to build a nest of logic.  This uses the structural hashing constructor functions.</p>")

(acl2::def-b*-binder aignet-build
  :body (b* (((when acl2::forms)
              (er hard? 'aignet-build "Aignet-build B* binder must be of the form ~
                      @('((aignet-build pattern gatesimp strash aignet))')."))
             ((unless (and (true-listp args)
                           (eql (len args) 4)
                           (acl2::legal-variablep (second args))
                           (acl2::legal-variablep (third args))
                           (acl2::legal-variablep (fourth args))))
              (er hard? 'aignet-build "Aignet-build B* binder must be of the form ~
                      @('((aignet-build pattern gatesimp strash aignet))')."))
             (rest-expr acl2::rest-expr)
             ((mv & bindings &)
              (aignet-build-rec (car args) 0 nil (cdr args) nil 'lit-negate)))
          `(b* ,(reverse bindings) ,rest-expr))
  :parents (aignet-construction)
  :short "B* binder to make a nest of logical functions in an @(see aignet)."
  :long "<p>See @(see aignet-build) for the non-b*-binder version of this
macro.  This version makes the bindings created by the macro, such as variables
assigned using the @(':=') operator, available in the remainder of your @('b*')
form.</p>")

(defxdoc aignet-build
  :parents (aignet-construction)
  :short "Macro that constructs a nested logical expression in an aignet"
  :long "<p>Usage:</p>
@({
  (aignet-build (and (not (:= foo (xor bar baz))) (or foo bar) baz) gatesimp strash aignet)
 -->
  (mv result-literal strash aignet)
 })
<p>The above invocation translates to something like:</p>
@({
 (b* (((mv foo strash aignet)
       (aignet-hash-xor bar baz gatesimp strash aignet))
      ((mv tmp0 strash aignet)
       (aignet-hash-or foo bar gatesimp strash aignet))
      ((mv tmp1 strash aignet)
       (aignet-hash-and tmp0 baz gatesimp strash aignet))
      ((mv tmp2 strash aignet)
       (aignet-hash-and (lit-negate foo) tmp1 gatesimp strash aignet)))
   (mv tmp2 strash aignet))
 })

<p>There is a @(see b*) binder of the same name that creates the above bindings
within an existing @('b*') form; e.g.:</p>

@({
 (b* (((aignet-build
        (:= ans (and (not (:= foo (xor bar baz))) (or foo bar) baz))
        gatesimp strash aignet)))
    (result-form))
 })
<p>expands to something like:</p>
@({
 (b* (((mv foo strash aignet)
       (aignet-hash-xor bar baz gatesimp strash aignet))
      ((mv tmp0 strash aignet)
       (aignet-hash-or foo bar gatesimp strash aignet))
      ((mv tmp1 strash aignet)
       (aignet-hash-and tmp0 baz gatesimp strash aignet))
      ((mv ans strash aignet)
       (aignet-hash-and (lit-negate foo) tmp1 gatesimp strash aignet)))
   (result-form))
 })


<h3>Supported Operators</h3>

<ul>

<li>The operators @('and'), @('or'), @('xor'), and @('iff') produce calls of
@(see aignet-hash-and), @(see aignet-hash-or), @(see aignet-hash-xor), and
@(see aignet-hash-iff), respectively.  Since these are all
associative/commutative functions, they support variably many
arguments (treated as right-associated).</li>

<li>The operators @('if') and @('mux') are synonymous and both produce a call
of @('aignet-hash-mux').</li>

<li>The operator @('not') simply uses @('lit-negate') on the literal resulting from its argument.</li>

<li>The operator @(':=') must have a variable as its first argument and an
expression as its second, and binds the variable to the literal resulting from
the expression.  That variable may be used subsequently within the operator
expression, and when using the @('b*') binder form, remains bound in the rest
of the @('b*').</li>
</ul>")



(define aignet-hash-or ((lit1 litp :type (unsigned-byte 30) "Literal to AND with lit2")
                         (lit2 litp :type (unsigned-byte 30))
                         (gatesimp gatesimp-p :type (unsigned-byte 6)
                                   "Configuration for how much simplification to try and whether to use hashing")
                         (strash "Stobj containing the aignet's structural hash table")
                         aignet)
  :split-types t
  :parents (aignet-construction)
  :short "Implement an OR of two literals node in an AIGNET, or find a node already
          representing the required logical expression."
  :long "<p>See @(see aignet-construction).</p>"
  :guard (and (fanin-litp lit1 aignet)
              (fanin-litp lit2 aignet))
  :returns (mv (result litp :rule-classes (:rewrite :type-prescription))
               (new-strash)
               (new-aignet))
  (b* (((mv lit strash aignet)
        (aignet-hash-and (lit-negate^ lit1) (lit-negate^ lit2) gatesimp strash aignet)))
    (mv (lit-negate^ lit) strash aignet))

  ///

  ;; (defcong lit-equiv equal (aignet-hash-or lit1 lit2 gatesimp strash aignet) 1)
  ;; (defcong lit-equiv equal (aignet-hash-or lit1 lit2 gatesimp strash aignet) 2)
  ;; (defcong nat-equiv equal (aignet-hash-or lit1 lit2 gatesimp strash aignet) 3)

  (def-aignet-preservation-thms aignet-hash-or)

  (defret aignet-litp-of-<fn>
    (implies (and (aignet-litp lit1 aignet)
                  (aignet-litp lit2 aignet))
             (aignet-litp result new-aignet)))

  (defret deps-of-<fn>
    (implies (and (not (depends-on (lit->var lit1) ci-id aignet))
                  (not (depends-on (lit->var lit2) ci-id aignet)))
             (not (depends-on (lit->var result) ci-id new-aignet))))

  (defret lit-eval-of-<fn>
    (equal (lit-eval result invals regvals new-aignet)
           (b-ior (lit-eval lit1 invals regvals aignet)
                  (lit-eval lit2 invals regvals aignet)))
    :hints(("Goal" :in-theory (enable eval-and-of-lits b-ior))))

  (defret stype-counts-preserved-of-<fn>
    (implies (and (not (equal (stype-fix stype) (and-stype)))
                  (not (equal (stype-fix stype) (xor-stype))))
             (equal (stype-count stype new-aignet)
                    (stype-count stype aignet))))

  (local (defthm unsigned-byte-p-when-aignet-litp-of-lit-fix
           (implies (and (aignet-litp lit aignet)
                         (< (fanin-count aignet) #x1fffffff))
                    (unsigned-byte-p 30 (lit-fix lit)))
           :hints (("goal" :use ((:instance unsigned-byte-p-when-aignet-litp
                                  (lit (lit-fix lit))))
                    :in-theory (disable unsigned-byte-p-when-aignet-litp)))))

  (local (defret unsigned-byte-p-lemma-1
           (implies (and (< (fanin-count aignet) #x1fffffff))
                    (unsigned-byte-p 30 result))
           :hints (("goal" :use ((:instance unsigned-byte-p-when-aignet-litp
                                  (lit result) (aignet new-aignet)))
                    :in-theory (disable unsigned-byte-p-when-aignet-litp)))))

  (defret unsigned-byte-p-of-<fn>
    (implies (and (< (fanin-count aignet) #x1fffffff)
                  (natp n) (<= 30 n))
             (unsigned-byte-p n result))
    :hints (("goal" :use unsigned-byte-p-lemma-1
             :in-theory (disable unsigned-byte-p-lemma-1))))

  (defret fanin-count-of-<fn>
    (<= (fanin-count new-aignet) (+ 1 (fanin-count aignet)))
    :rule-classes :linear))


(define aignet-hash-iff ((lit1 litp :type (unsigned-byte 30) "Literal to AND with lit2")
                         (lit2 litp :type (unsigned-byte 30))
                         (gatesimp gatesimp-p :type (unsigned-byte 6)
                                   "Configuration for how much simplification to try and whether to use hashing")
                         (strash "Stobj containing the aignet's structural hash table")
                         aignet)
  :split-types t
  :parents (aignet-construction)
  :short "Implement an IFF of two literals node in an AIGNET, or find a node already
          representing the required logical expression."
  :long "<p>See @(see aignet-construction).</p>"
  :guard (and (fanin-litp lit1 aignet)
              (fanin-litp lit2 aignet))
  :returns (mv (result litp :rule-classes (:rewrite :type-prescription))
               (new-strash)
               (new-aignet))
  (b* (((mv lit strash aignet)
        (aignet-hash-xor lit1 lit2 gatesimp strash aignet)))
    (mv (lit-negate lit) strash aignet))

  ///

  ;; (defcong lit-equiv equal (aignet-hash-or lit1 lit2 gatesimp strash aignet) 1)
  ;; (defcong lit-equiv equal (aignet-hash-or lit1 lit2 gatesimp strash aignet) 2)
  ;; (defcong nat-equiv equal (aignet-hash-or lit1 lit2 gatesimp strash aignet) 3)

  (def-aignet-preservation-thms aignet-hash-iff)

  (defret aignet-litp-of-<fn>
    (implies (and (aignet-litp lit1 aignet)
                  (aignet-litp lit2 aignet))
             (aignet-litp result new-aignet)))

  (defret deps-of-<fn>
    (implies (and (not (depends-on (lit->var lit1) ci-id aignet))
                  (not (depends-on (lit->var lit2) ci-id aignet)))
             (not (depends-on (lit->var result) ci-id new-aignet))))


  (defret lit-eval-of-<fn>
    (equal (lit-eval result invals regvals new-aignet)
           (b-not (b-xor (lit-eval lit1 invals regvals aignet)
                         (lit-eval lit2 invals regvals aignet))))
    :hints(("Goal" :in-theory (enable eval-and-of-lits b-ior))))

  (defret stype-counts-preserved-of-<fn>
    (implies (and (not (equal (stype-fix stype) (and-stype)))
                  (not (equal (stype-fix stype) (xor-stype))))
             (equal (stype-count stype new-aignet)
                    (stype-count stype aignet))))

  (local (defthm unsigned-byte-p-when-aignet-litp-of-lit-fix
           (implies (and (aignet-litp lit aignet)
                         (< (fanin-count aignet) #x1fffffff))
                    (unsigned-byte-p 30 (lit-fix lit)))
           :hints (("goal" :use ((:instance unsigned-byte-p-when-aignet-litp
                                  (lit (lit-fix lit))))
                    :in-theory (disable unsigned-byte-p-when-aignet-litp)))))

  (local (defret unsigned-byte-p-lemma-1
           (implies (and (< (fanin-count aignet) #x1ffffffd))
                    (unsigned-byte-p 30 result))
           :hints (("goal" :use ((:instance unsigned-byte-p-when-aignet-litp
                                  (lit result) (aignet new-aignet)))
                    :in-theory (disable unsigned-byte-p-when-aignet-litp)))))

  (defret unsigned-byte-p-of-<fn>
    (implies (and (< (fanin-count aignet) #x1ffffffd)
                  (natp n) (<= 30 n))
             (unsigned-byte-p n result))
    :hints (("goal" :use unsigned-byte-p-lemma-1
             :in-theory (disable unsigned-byte-p-lemma-1)))))

(define aignet-hash-mux ((c litp :type (unsigned-byte 30) "Literal to AND with lit2")
                         (tb litp :type (unsigned-byte 30))
                         (fb litp :type (unsigned-byte 30))
                         (gatesimp gatesimp-p :type (unsigned-byte 6)
                                   "Configuration for how much simplification to try and whether to use hashing")
                         (strash "Stobj containing the aignet's structural hash table")
                         aignet)
  :split-types t
  :parents (aignet-construction)
  :short "Implement an if-then-else of the given literals in an AIGNET, or find
          a node already representing the required logical expression."
  :long "<p>See @(see aignet-construction).</p>"
  :guard (and (fanin-litp c aignet)
              (fanin-litp tb aignet)
              (fanin-litp fb aignet))
  :returns (mv (result litp :rule-classes (:rewrite :type-prescription))
               (new-strash)
               (new-aignet))
  (b* ((aignet (mbe :logic (non-exec (node-list-fix aignet)) :exec aignet))
       (c (mbe :logic (non-exec (aignet-lit-fix c aignet))
               :exec c))
       (tb (mbe :logic (non-exec (aignet-lit-fix tb aignet))
                :exec tb))
       (fb (mbe :logic (non-exec (aignet-lit-fix fb aignet))
                :exec fb))
       ((when (eql tb fb)) (mv tb strash aignet))
       ((when (eql tb (lit-negate fb))) (aignet-hash-xor c fb gatesimp strash aignet)))
    (aignet-build (or (and c tb) (and (not c) fb)) gatesimp strash aignet))

  ///

  ;; (defcong lit-equiv equal (aignet-hash-or lit1 lit2 gatesimp strash aignet) 1)
  ;; (defcong lit-equiv equal (aignet-hash-or lit1 lit2 gatesimp strash aignet) 2)
  ;; (defcong nat-equiv equal (aignet-hash-or lit1 lit2 gatesimp strash aignet) 3)

  (def-aignet-preservation-thms aignet-hash-mux)

  (defret aignet-litp-of-<fn>
    (aignet-litp result new-aignet))

  (defret deps-of-<fn>
    (implies (and (not (depends-on (lit->var c) ci-id aignet))
                  (not (depends-on (lit->var tb) ci-id aignet))
                  (not (depends-on (lit->var fb) ci-id aignet)))
             (not (depends-on (lit->var result) ci-id new-aignet))))

  ;; (local (defthm lit-eval-of-equal-aignet-lit-fix
  ;;          (implies (and (equal y (aignet-lit-fix x aignet))
  ;;                        (bind-free
  ;;                         (progn$ (cw "x: ~x0 y: ~x0~%" y)
  ;;                                 (case-match y
  ;;                                   (('aignet-lit-fix yy 'aignet) `((yy . ,yy)))
  ;;                                   (& `((yy . ,y)))))
  ;;                         (yy))
  ;;                        (equal (aignet-lit-fix yy aignet) y)
  ;;                        (syntaxp (progn$ (cw "yy: ~x0~%" yy)
  ;;                                         (not (equal yy x)))))
  ;;                   (equal (lit-eval x invals regvals aignet)
  ;;                          (lit-eval yy invals regvals aignet)))
  ;;          :hints (("goal" :use ((:instance lit-eval-of-aignet-lit-fix
  ;;                                 (x x))
  ;;                                (:instance lit-eval-of-aignet-lit-fix
  ;;                                 (x yy)))
  ;;                   :in-theory (disable lit-eval-of-aignet-lit-fix)))))

  (local (defthm lit-eval-equal-when-aignet-lit-fix-equal
           (implies (equal (aignet-lit-fix x aignet)
                           (aignet-lit-fix y aignet))
                    (equal (equal (lit-eval x invals regvals aignet)
                                  (lit-eval y invals regvals aignet))
                           t))
           :hints (("goal" :use ((:instance lit-eval-of-aignet-lit-fix (x x))
                                 (:instance lit-eval-of-aignet-lit-fix (x y)))
                    :in-theory (disable lit-eval-of-aignet-lit-fix)))))

  (local (defthm lit-eval-equal-when-aignet-lit-fix-negated
           (implies (equal (aignet-lit-fix x aignet)
                           (lit-negate (aignet-lit-fix y aignet)))
                    (equal (lit-eval x invals regvals aignet)
                           (b-not (lit-eval y invals regvals aignet))))
           :hints (("goal" :use ((:instance lit-eval-of-aignet-lit-fix (x x))
                                 (:instance lit-eval-of-aignet-lit-fix (x y)))
                    :in-theory (disable lit-eval-of-aignet-lit-fix
                                        lit-eval-of-aignet-lit-fix-extension
                                        lit-eval-equal-when-aignet-lit-fix-equal)))))

  (defret lit-eval-of-<fn>
    (equal (lit-eval result invals regvals new-aignet)
           (b-ite (lit-eval c invals regvals aignet)
                  (lit-eval tb invals regvals aignet)
                  (lit-eval fb invals regvals aignet)))
    :hints(("Goal" :in-theory (enable b-ite))))

  (defret stype-counts-preserved-of-<fn>
    (implies (and (not (equal (stype-fix stype) (and-stype)))
                  (not (equal (stype-fix stype) (xor-stype))))
             (equal (stype-count stype new-aignet)
                    (stype-count stype aignet))))

  (local (defthm unsigned-byte-p-when-aignet-litp-of-lit-fix
           (implies (and (aignet-litp lit aignet)
                         (< (fanin-count aignet) #x1fffffff))
                    (unsigned-byte-p 30 (lit-fix lit)))
           :hints (("goal" :use ((:instance unsigned-byte-p-when-aignet-litp
                                  (lit (lit-fix lit))))
                    :in-theory (disable unsigned-byte-p-when-aignet-litp)))))

  (local (defthm unsigned-byte-p-when-aignet-litp-of-aignet-lit-fix
           (implies (< (fanin-count aignet) #x1fffffff)
                    (unsigned-byte-p 30 (aignet-lit-fix lit aignet)))
           :hints (("goal" :use ((:instance unsigned-byte-p-when-aignet-litp
                                  (lit (aignet-lit-fix lit aignet))))
                    :in-theory (disable unsigned-byte-p-when-aignet-litp)))))

  (local (defret unsigned-byte-p-lemma-1
           (implies (and (< (fanin-count aignet) #x1ffffffd))
                    (unsigned-byte-p 30 result))))

  (defret unsigned-byte-p-of-<fn>
    (implies (and (< (fanin-count aignet) #x1ffffffd)
                  (natp n) (<= 30 n))
             (unsigned-byte-p n result))
    :hints (("goal" :use unsigned-byte-p-lemma-1
             :in-theory (disable unsigned-byte-p-lemma-1
                                 <fn>)))))







(define aignet-add-ins ((n natp) aignet)
  :returns (new-aignet)
  (if (zp n)
      (mbe :logic (non-exec (node-list-fix aignet))
           :exec aignet)
    (b* ((aignet (aignet-add-in aignet)))
      (aignet-add-ins (1- n) aignet)))
  ///
  (fty::deffixequiv aignet-add-ins)

  (def-aignet-preservation-thms aignet-add-ins)

  (std::defret pi-count-of-aignet-add-ins
    (equal (stype-count :pi new-aignet)
           (+ (nfix n) (stype-count :pi aignet))))

  (std::defret other-stype-count-of-aignet-add-ins
    (implies (not (equal (stype-fix stype) :pi))
             (equal (stype-count stype new-aignet)
                    (stype-count stype aignet))))

  (std::defret car-of-aignet-add-ins
    (implies (posp n)
             (equal (car new-aignet)
                    (pi-node)))
    :hints (("goal" :induct <call> :expand (<call>))))

  (std::defret fanin-count-of-aignet-add-ins
    (equal (fanin-count new-aignet)
           (+ (nfix n) (fanin-count aignet))))

  (std::defret lookup-pi-of-aignet-add-ins
    (implies (< (nfix innum) (+ (nfix n) (stype-count :pi aignet)))
             (equal (lookup-stype innum :pi new-aignet)
                    (if (< (nfix innum) (stype-count :pi aignet))
                        (lookup-stype innum :pi aignet)
                      (aignet-add-ins (+ 1 (- (nfix innum) (stype-count :pi aignet))) aignet))))
    :hints(("Goal" :in-theory (e/d (lookup-stype) ((:d aignet-add-ins)))
            :expand (<call>
                     (:free (aignet) (aignet-add-ins 0 aignet))
                     (:free (n) (aignet-add-ins (+ 1 n) aignet)))
            :induct <call>)))

  (std::defret lookup-id-of-aignet-add-ins
    (implies (<= (nfix id) (+ (nfix n) (fanin-count aignet)))
             (equal (lookup-id id new-aignet)
                    (if (<= (nfix id) (fanin-count aignet))
                        (lookup-id id aignet)
                      (aignet-add-ins (- (nfix id) (fanin-count aignet)) aignet))))
    :hints(("Goal" :in-theory (enable lookup-id)
            :induct t)
           (and stable-under-simplificationp
                '(:expand ((aignet-add-ins 1 aignet))))))

  (std::defret lookup-other-stype-of-aignet-add-ins
    (implies (not (equal (stype-fix stype) :pi))
             (equal (lookup-stype typenum stype (aignet-add-ins n aignet))
                    (lookup-stype typenum stype aignet))))
  

  (std::defret cdr-of-aignet-add-ins-when-posp
    (implies (posp n)
             (equal (cdr new-aignet)
                    (aignet-add-ins (1- n) aignet)))
    :hints (("goal" :induct <call> :expand (<call>))))

  (std::defret lit-eval-of-aignet-add-ins
    (implies (and (<= (+ 1 (fanin-count aignet)) (nfix id))
                  (< id (+ 1 (nfix n) (fanin-count aignet))))
             (equal (lit-eval (mk-lit id neg) in-vals reg-vals new-aignet)
                    (b-xor neg
                           (nth (+ (num-ins aignet)
                                   (nfix id)
                                   (- (+ 1 (fanin-count aignet))))
                                in-vals))))
    :hints(("Goal" :in-theory (enable aignet-idp)
            :expand ((:free (aignet) (id-eval id in-vals reg-vals aignet))
                     (:free (aignet) (lit-eval (mk-lit id neg) in-vals reg-vals aignet)))))))


(define aignet-add-regs ((n natp) aignet)
  :returns (new-aignet)
  (if (zp n)
      (mbe :logic (non-exec (node-list-fix aignet))
           :exec aignet)
    (b* ((aignet (aignet-add-reg aignet)))
      (aignet-add-regs (1- n) aignet)))
  ///
  (fty::deffixequiv aignet-add-regs)

  (def-aignet-preservation-thms aignet-add-regs)

  (std::defret reg-count-of-aignet-add-regs
    (equal (stype-count :reg new-aignet)
           (+ (nfix n) (stype-count :reg aignet))))

  (std::defret other-stype-count-of-aignet-add-regs
    (implies (not (equal (stype-fix stype) :reg))
             (equal (stype-count stype new-aignet)
                    (stype-count stype aignet))))

  (std::defret car-of-aignet-add-regs
    (implies (posp n)
             (equal (car new-aignet)
                    (reg-node)))
    :hints (("goal" :induct <call> :expand (<call>))))

  (std::defret fanin-count-of-aignet-add-regs
    (equal (fanin-count new-aignet)
           (+ (nfix n) (fanin-count aignet))))

  (std::defret lookup-reg-of-aignet-add-regs
    (implies (< (nfix regnum) (+ (nfix n) (stype-count :reg aignet)))
             (equal (lookup-stype regnum :reg new-aignet)
                    (if (< (nfix regnum) (stype-count :reg aignet))
                        (lookup-stype regnum :reg aignet)
                      (aignet-add-regs (+ 1 (- (nfix regnum) (stype-count :reg aignet))) aignet))))
    :hints(("Goal" :in-theory (e/d (lookup-stype) ((:d aignet-add-regs)))
            :expand (<call>
                     (:free (aignet) (aignet-add-regs 0 aignet))
                     (:free (n) (aignet-add-regs (+ 1 n) aignet)))
            :induct <call>)))
  

  (std::defret lookup-id-of-aignet-add-regs
    (implies (<= (nfix id) (+ (nfix n) (fanin-count aignet)))
             (equal (lookup-id id new-aignet)
                    (if (<= (nfix id) (fanin-count aignet))
                        (lookup-id id aignet)
                      (aignet-add-regs (- (nfix id) (fanin-count aignet)) aignet))))
    :hints(("Goal" :in-theory (enable lookup-id)
            :induct t)
           (and stable-under-simplificationp
                '(:expand ((aignet-add-regs 1 aignet))))))

  (std::defret lookup-other-stype-of-aignet-add-regs
    (implies (not (equal (stype-fix stype) :reg))
             (equal (lookup-stype typenum stype (aignet-add-regs n aignet))
                    (lookup-stype typenum stype aignet))))

  ;; (local (std::defret fanin-id-range-p-of-aignet-add-regs-lemma
  ;;          (fanin-id-range-p (+ 1 (fanin-count aignet)) n new-aignet)
  ;;          :hints(("Goal" :in-theory (enable fanin-id-range-p)))))

  ;; (std::defret fanin-id-range-p-of-aignet-add-regs
  ;;   (implies (equal id (+ 1 (fanin-count aignet)))
  ;;            (fanin-id-range-p id n new-aignet)))

  ;; (std::defret aignet-add-regs-preserves-fanin-id-range-p
  ;;   (implies (fanin-id-range-p id count aignet)
  ;;            (fanin-id-range-p id count new-aignet))
  ;;   :hints(("Goal" :in-theory (enable fanin-id-range-p))))

  (std::defret cdr-of-aignet-add-regs-when-posp
    (implies (posp n)
             (equal (cdr new-aignet)
                    (aignet-add-regs (1- n) aignet)))
    :hints (("goal" :induct <call> :expand (<call>))))

  (std::defret lit-eval-of-aignet-add-regs
    (implies (and (<= (+ 1 (fanin-count aignet)) (nfix id))
                  (< id (+ 1 (nfix n) (fanin-count aignet))))
             (equal (lit-eval (mk-lit id neg) in-vals reg-vals new-aignet)
                    (b-xor neg
                           (nth (+ (num-regs aignet)
                                   (nfix id)
                                   (- (+ 1 (fanin-count aignet))))
                                reg-vals))))
    :hints(("Goal" :in-theory (enable lit-eval aignet-idp)
            :expand ((:free (aignet) (id-eval id in-vals reg-vals aignet))
                     (:free (aignet) (lit-eval (mk-lit id neg) in-vals reg-vals aignet)))))))



#||

(trace$ (aignet-strash-gate :entry (list 'aignet-strash-gate code-in x0 x1 hashp)))
(trace$ (reduce-and-gate :entry (list 'reduce-and-gate x0 x1 level)) (reduce-xor-gate :entry (list 'reduce-xor-gate x0 x1 level)))
(trace$ (aignet-install-gate :entry (list 'aignet-install-gate code-in key x0 x1 gatesimp) :exit (list 'aignet-install-gate (car values))))
(trace$ (reduce-and-gate-rec :entry (list 'reduce-and-gate-rec x0 x1 level)) (reduce-xor-gate-rec :entry (list 'reduce-xor-gate-rec x0 x1 level)))
(trace$ (aignet-and-gate-simp/strash :entry (list 'aignet-and-gate-simp/strash x0 x1 gatesimp)) (aignet-xor-gate-simp/strash :entry (list 'aignet-xor-gate-simp/strash x0 x1 gatesimp)))
(trace$ (aignet-hash-and :entry (list 'aignet-hash-and lit1 lit2 gatesimp) :exit (list 'aignet-hash-and (car values))))
(trace$ (aignet-hash-xor :entry (list 'aignet-hash-xor lit1 lit2 gatesimp) :exit (list 'aignet-hash-xor (car values))))



||#
