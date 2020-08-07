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

(include-book "raw-copy")
(include-book "semantics")
(include-book "stats")

(local (in-theory (disable w)))

(defxdoc aignet-transforms
  :parents (aignet)
  :short "Various types of transforms preserving different properties of the AIG"
  :long
"
<p>The following kinds of transforms are defined:</p>
<ul>
<li>@(see aignet-comb-transforms): Combinational equivalence-preserving transforms</li>

<li>@(see aignet-n-output-comb-transforms): Transforms that preserve
combinational equivalence only on the first @('n') outputs, for a given
@('n')</li>

<li>@(see aignet-m-assumption-n-output-transforms): Transforms that preserve
combinational equivalence of the first @('m') outputs, and preserve
combinational equivalence of the following @('n') outputs assuming the truth of
the first @('m') outputs, for given @('m') and @('n').</li>
</ul>

<p>Each of these transform types has a constrained function,
@('apply-<name>-transform'), which takes a source AIG @('aignet'), a
destination AIG @('aignet2'), a configuration object, and the ACL2 state and
returns a modified destination AIG and state. The constraints on these define
the contracts of each transform type.  Using this stub function, we also define
@('apply-<name>-transform!') which uses @(see swap-stobjs) to overwrite the
source AIG with the result instead of dealing with a second destination AIG.
The properties defining these transforms are all transitive, so for each type
we also define functions @('apply-<name>-transforms') and
@('apply-<name>-transforms!') which apply a sequence of transforms specified by
a list of configuration objects.</p>

<p>Each of the transform types has an implementation of its constrained
@('apply') function defined in @('centaur/aignet/transforms.lisp') and
attached to the @('apply') function when that book is included.</p>

")


(defconst *apply-transform-template*
  '(progn
     (defxdoc apply-<name>-transform
       :parents <parents>
       :short <short>
       :long <long>)
     (encapsulate
       (((apply-<name>-transform <extra-formals-*> aignet aignet2 * state) => (mv aignet2 state)
         :guard <encap-guard>
         :formals (<extra-args> aignet aignet2 config state)))

       (local (define apply-<name>-transform (<extra-define-formals> aignet aignet2 config state)
                :guard <guard>
                :returns (mv new-aignet2 new-state)
                (Declare (ignore <extra-args> config aignet2))
                (b* ((aignet2 (non-exec (node-list-fix aignet))))
                  (mv aignet2 state))))

       (local (in-theory (enable apply-<name>-transform)))
       
       (defret normalize-inputs-of-<fn>
         (implies (syntaxp (not (equal aignet2 ''nil)))
                  (equal <call>
                         (<fn> <extra-args> aignet nil config state))))

       (defret num-ins-of-<fn>
         (equal (stype-count :pi new-aignet2)
                (stype-count :pi aignet)))

       (defret num-regs-of-<fn>
         (equal (stype-count :reg new-aignet2)
                (stype-count :reg aignet)))

       (defret num-outs-of-<fn>
         (equal (stype-count :po new-aignet2)
                (stype-count :po aignet)))

       (defret <fn>-correct
         <correctness-claim-aignet2>)

       (defret w-state-of-<fn>
         (equal (w new-state)
                (w state)))

       (defret list-of-outputs-of-<fn>
         (equal (list new-aignet2 new-state) <call>)))

     (acl2::set-prev-stobjs-correspondence apply-<name>-transform
                                           :stobjs-out (aignet state)
                                           :formals (<extra-args> aignet aignet2 config state))


     (define apply-<name>-transform! (<extra-define-formals>
                                      aignet
                                      transform
                                      state)
       :parents (apply-<name>-transform)
       :guard <guard>
       :returns (mv new-aignet new-state)
       :enabled t
       :hooks nil
       (mbe :logic (non-exec (apply-<name>-transform <extra-args> aignet nil transform state))
            :exec (b* (((acl2::local-stobjs aignet2)
                        (mv aignet aignet2 state))
                       ((mv aignet2 state) (apply-<name>-transform <extra-args> aignet aignet2 transform state))
                       ((mv aignet aignet2) (swap-stobjs aignet aignet2)))
                    (mv aignet aignet2 state))))

     (define apply-<name>-transforms!-core (<extra-define-formals>
                                            aignet
                                            transforms
                                            state)
       :guard <guard>  
       :returns (mv new-aignet new-state)
       (b* (((when (atom transforms))
             (b* ((aignet (mbe :logic (non-exec (node-list-fix aignet))
                               :exec aignet)))
               (mv aignet state)))
            ((mv aignet state) (apply-<name>-transform! <extra-args> aignet (car transforms) state)))
         (apply-<name>-transforms!-core <extra-args> aignet (cdr transforms) state))
       ///
       (defret num-ins-of-<fn>
         (equal (stype-count :pi new-aignet)
                (stype-count :pi aignet)))

       (defret num-regs-of-<fn>
         (equal (stype-count :reg new-aignet)
                (stype-count :reg aignet)))

       (defret num-outs-of-<fn>
         (equal (stype-count :po new-aignet)
                (stype-count :po aignet)))

       (defret <fn>-correct
         <correctness-claim-aignet>)

       (defret w-state-of-<fn>
         (equal (w new-state)
                (w state)))

       (defret list-of-outputs-of-<fn>
         (equal (list new-aignet new-state) <call>)))

     (define apply-<name>-transforms! (<extra-define-formals>
                                       aignet
                                       transforms
                                       state)
       :parents (apply-<name>-transform)
       :guard <guard>
       :enabled t
       :hooks nil
       :returns (mv new-aignet new-state)
       (prog2$ (print-aignet-stats "Input" aignet)
               (time$ (apply-<name>-transforms!-core <extra-args> aignet transforms state)
                      :msg "All transforms: ~st seconds, ~sa bytes.~%")))

     (define apply-<name>-transforms-in-place (<extra-define-formals> aignet aignet2 transforms state)
       :guard <guard>
       :returns (mv new-aignet new-aignet2 new-state)
       (b* (((when (atom transforms))
             (b* ((aignet (mbe :logic (non-exec (node-list-fix aignet))
                               :exec aignet))
                  (aignet2 (mbe :logic (non-exec (node-list-fix aignet2))
                                :exec aignet2)))
               (mv aignet aignet2 state))))
         (mbe :logic (non-exec
                      (b* (((mv new-aignet state) (apply-<name>-transform <extra-args> aignet nil (car transforms) state)))
                        (apply-<name>-transforms-in-place <extra-args> new-aignet aignet (cdr transforms) state)))
              :exec (b* (((mv aignet2 state) (apply-<name>-transform <extra-args> aignet aignet2 (car transforms) state))
                         ((mv aignet aignet2) (swap-stobjs aignet aignet2)))
                      (apply-<name>-transforms-in-place <extra-args> aignet aignet2 (cdr transforms) state))))
       ///
       (defret <fn>-equals-apply-<name>-transforms!
         (b* (((mv new-aignet-spec new-state-spec) (apply-<name>-transforms! <extra-args> aignet transforms state)))
           (and (equal new-aignet new-aignet-spec)
                (equal new-state new-state-spec)))
         :hints(("Goal" :in-theory (enable apply-<name>-transforms!-core))))

       (defret list-of-outputs-of-<fn>
         (equal (list new-aignet new-aignet2 new-state) <call>)
         :hints(("Goal" :in-theory (disable <fn>-equals-apply-<name>-transforms!)))))

     (define apply-<name>-transforms (<extra-define-formals> aignet aignet2 transforms state)
       :parents (apply-<name>-transform)
       :guard <guard>
       :returns (mv new-aignet2 new-state)
       :guard-hints (("goal" :expand ((apply-<name>-transforms!-core <extra-args> aignet transforms state))))
       (prog2$
        (print-aignet-stats "Input" aignet)
        (time$
         (b* (((unless (consp transforms))
               (b* ((aignet2 (aignet-raw-copy aignet aignet2)))
                 (mv aignet2 state))))
           (mbe :logic (non-exec (apply-<name>-transforms!-core <extra-args> aignet transforms state))
                :exec (b* (((mv aignet2 state) (apply-<name>-transform <extra-args> aignet aignet2 (car transforms) state))
                           ((acl2::local-stobjs aignet3)
                            (mv aignet2 aignet3 state)))
                        (apply-<name>-transforms-in-place <extra-args> aignet2 aignet3 (cdr transforms) state))))
         :msg "All transforms: ~st seconds, ~sa bytes.~%"))
       ///
       (defret normalize-inputs-of-<fn>
         (implies (syntaxp (not (equal aignet2 ''nil)))
                  (equal <call>
                         (let ((aignet2 nil)) <call>))))

       (defret num-ins-of-<fn>
         (equal (stype-count :pi new-aignet2)
                (stype-count :pi aignet)))

       (defret num-regs-of-<fn>
         (equal (stype-count :reg new-aignet2)
                (stype-count :reg aignet)))

       (defret num-outs-of-<fn>
         (equal (stype-count :po new-aignet2)
                (stype-count :po aignet)))

       (defret <fn>-correct
         <correctness-claim-aignet2>)

       (defret w-state-of-<fn>
         (equal (w new-state)
                (w state)))

       (defret list-of-outputs-of-<fn>
         (equal (list new-aignet2 new-state) <call>)))))


(defun def-apply-transform-fn (name
                               extra-define-formals
                               guard
                               correctness-claim
                               parents short long)
  (declare (xargs :mode :program))
  (b* ((formals (std::parse-formals `(def-apply-transform ,name)
                                    extra-define-formals nil nil))
       (formal-guards (std::formallist->guards formals))
       (formal-names (std::formallist->names formals))
       (full-guard `(and ,guard . ,formal-guards))
       (correctness-claim-aignet2 (subst 'new-aignet2 'new-aignet correctness-claim))
       (subst
        (acl2::make-tmplsubst
         :splices `((<extra-define-formals> . ,extra-define-formals)
                    (<extra-args> . ,formal-names)
                    (<extra-formals-*> . ,(make-list (len formal-names) :initial-element '*)))
         :atoms `((<encap-guard> . ,full-guard)
                  (<guard> . ,guard)
                  (<correctness-claim-aignet> . ,correctness-claim)
                  (<correctness-claim-aignet2> . ,correctness-claim-aignet2)
                  (<parents> . ,parents)
                  (<short> . ,short)
                  (<long> . ,long))
         :strs `(("<NAME>" . ,(symbol-name name)))
         :pkg-sym 'aignet-package)))
    (acl2::template-subst-top *apply-transform-template* subst)))

(defmacro def-apply-transform (name extra-define-formals
                               &key
                               (guard 't)
                               (correctness-claim)
                               parents short long)
  (def-apply-transform-fn name extra-define-formals guard correctness-claim parents short long))

(def-apply-transform comb ()
  :correctness-claim (comb-equiv new-aignet aignet)
  :parents (aignet-comb-transforms)
  :short "Stub for an AIG transform that preserves combinational equivalence")

(def-apply-transform n-output-comb ((n natp))
  :guard (<= n (num-outs aignet))
  :correctness-claim
  (implies (< (nfix i) (nfix n))
           (equal (output-eval i invals regvals new-aignet)
                  (output-eval i invals regvals aignet)))
  :parents (aignet-n-output-comb-transforms)
  :short "Stub for an AIG transform that preserves combinational equivalence of
          the first N primary outputs")

(define output-lit-range ((start natp) (count natp) aignet)
  :returns (lits lit-listp)
  :guard (<= (+ start count) (num-outs aignet))
  :hooks (:fix)
  (if (zp count)
      nil
    (cons (outnum->fanin start aignet)
          (output-lit-range (1+ (lnfix start)) (1- count) aignet)))
  ///
  (defret len-of-<fn>
    (equal (len lits) (nfix count)))

  (local (defun nth-ind (n start count)
           (if (zp count)
               (list start n)
             (nth-ind (1- (nfix n)) (1+ (lnfix start)) (1- count)))))

  (defret nth-of-<fn>
    (implies (< (nfix n) (nfix count))
             (equal (nth n lits)
                    (outnum->fanin (+ (nfix start) (nfix n)) aignet)))
    :hints(("Goal" 
            :induct (nth-ind n start count)
            :expand ((:free (a b) (nth n (cons a b)))))))

  (defret aignet-lit-listp-of-<fn>
    (aignet-lit-listp lits aignet)))

(define lits-find-0val ((lits lit-listp)
                               invals regvals aignet)
  :returns (0-lit litp :rule-classes :type-prescription)
  :guard (and (aignet-lit-listp lits aignet)
              (<= (num-ins aignet) (bits-length invals))
              (<= (num-regs aignet) (bits-length regvals)))
  (if (atom lits)
      1
    (if (equal (lit-eval (car lits) invals regvals aignet) 0)
        (lit-fix (car lits))
      (lits-find-0val (cdr lits) invals regvals aignet)))
  ///
  (defret lits-find-0val-member-when-conjunction
    (implies (equal (aignet-eval-conjunction
                     lits invals regvals aignet)
                    0)
             (member-equal 0-lit (lit-list-fix lits)))
    :hints(("Goal" :in-theory (enable aignet-eval-conjunction))))

  (defret lits-find-0val-member-lit-listp-when-conjunction
    (implies (and (equal (aignet-eval-conjunction
                          lits invals regvals aignet)
                         0)
                  (lit-listp lits))
             (member-equal 0-lit lits))
    :hints(("Goal" :in-theory (enable aignet-eval-conjunction))))

  (defret lits-find-0val-eval-when-conjunction
    (implies (equal (aignet-eval-conjunction
                     lits invals regvals aignet)
                    0)
             (equal (lit-eval 0-lit invals regvals aignet) 0))
    :hints(("Goal" :in-theory (enable aignet-eval-conjunction)))))

(define output-range-equiv ((start natp) (n natp) invals regvals aignet aignet2)
  :guard (and (<= (+ start n) (num-outs aignet))
              (<= (+ start n) (num-outs aignet2))
              (<= (num-ins aignet) (bits-length invals))
              (<= (num-ins aignet2) (bits-length invals))
              (<= (num-regs aignet) (bits-length regvals))
              (<= (num-regs aignet2) (bits-length regvals)))
  :returns (equiv)
  :hooks (:fix)
  :measure (nfix n)
  (if (zp n)
      t
    (and (equal (output-eval start invals regvals aignet2)
                (output-eval start invals regvals aignet))
         (output-range-equiv (1+ (lnfix start)) (1- n) invals regvals aignet aignet2)))
  ///
  (defretd output-range-equiv-implies
    (implies (and equiv
                  (<= (nfix start) (nfix i))
                  (< (nfix i) (+ (nfix start) (nfix n))))
             (equal (output-eval i invals regvals aignet)
                    (output-eval i invals regvals aignet2)))
    :hints(("Goal" :in-theory (enable* acl2::arith-equiv-forwarding))))

  (defthm output-range-equiv-reflexive
    (output-range-equiv start n invals regvals aignet aignet))

  (defthm output-range-equiv-of-aignet-norm
    (output-range-equiv start n invals regvals (aignet-norm aignet) aignet))

  (defthm output-range-equiv-transitive
    (implies (and (bind-free (acl2::prev-stobj-binding aignet 'aignet2 mfc state))
                  (output-range-equiv start n invals regvals aignet aignet2)
                  (output-range-equiv start n invals regvals aignet2 aignet3))
             (output-range-equiv start n invals regvals aignet aignet3))))

(define output-range-equiv-badguy ((start natp) (n natp) invals regvals aignet aignet2)
  :guard (and (<= (+ start n) (num-outs aignet))
              (<= (+ start n) (num-outs aignet2))
              (<= (num-ins aignet) (bits-length invals))
              (<= (num-ins aignet2) (bits-length invals))
              (<= (num-regs aignet) (bits-length regvals))
              (<= (num-regs aignet2) (bits-length regvals)))
  :returns (badguy natp :rule-classes :type-prescription)
  :hooks (:fix)
  :measure (nfix n)
  (if (zp n)
      (lnfix start)
    (if (equal (output-eval start invals regvals aignet2)
               (output-eval start invals regvals aignet))
        (output-range-equiv-badguy (1+ (lnfix start)) (1- n) invals regvals aignet aignet2)
      (lnfix start)))
  ///
  (local (in-theory (enable output-range-equiv)))
  (defret output-range-equiv-badguy-lower-bound
    (<= (nfix start) badguy)
    :rule-classes :linear)

  (defret output-range-equiv-badguy-bound
    (implies (not (output-range-equiv start n invals regvals aignet aignet2))
             (< badguy (+ (nfix start) (nfix n))))
    :rule-classes :linear)

  (defret output-range-equiv-badguy-not-equal
    (implies (not (output-range-equiv start n invals regvals aignet aignet2))
             (not (equal (output-eval badguy invals regvals aignet)
                         (output-eval badguy invals regvals aignet2)))))

  (defretd output-range-equiv-by-badguy
    (implies (equal (output-eval badguy invals regvals aignet)
                    (output-eval badguy invals regvals aignet2))
             (output-range-equiv start n invals regvals aignet aignet2))))


(define conjoin-output-range ((start natp) (n natp) invals regvals aignet)
  :guard (and (<= (+ start n) (num-outs aignet))
              (<= (num-ins aignet) (bits-length invals))
              (<= (num-regs aignet) (bits-length regvals)))
  :hooks (:fix)
  :measure (nfix n)
  (if (zp n)
      1
    (mbe :logic (b-and (output-eval start invals regvals aignet)
                       (conjoin-output-range (1+ (lnfix start)) (1- n) invals regvals aignet))
         :exec (if (eql 1 (output-eval start invals regvals aignet))
                   (conjoin-output-range (1+ (lnfix start)) (1- n) invals regvals aignet)
                 0)))
  ///
  (local (in-theory (enable output-range-equiv)))
  (defthm conjoin-output-range-when-output-range-equiv
    (implies (and (bind-free (acl2::prev-stobj-binding aignet 'aignet2 mfc state))
                  (output-range-equiv start n invals regvals aignet aignet2)
                  (syntaxp (not (equal aignet aignet2))))
             (equal (conjoin-output-range start n invals regvals aignet)
                    (conjoin-output-range start n invals regvals aignet2))))

  (defthm aignet-eval-conjunction-of-output-lit-range
    (equal (aignet-eval-conjunction
            (output-lit-range start m aignet)
            invals regvals aignet)
           (conjoin-output-range start m invals regvals aignet))
    :hints(("Goal" :in-theory (enable conjoin-output-range
                                      output-lit-range
                                      output-eval
                                      aignet-eval-conjunction))))

  (defthm conjoin-output-range-of-take-ins
    (equal (conjoin-output-range start n (take (stype-count :pi aignet) invals) regvals aignet)
           (conjoin-output-range start n invals regvals aignet))
    :hints(("Goal" :in-theory (enable conjoin-output-range output-eval))))

  (defthm conjoin-output-range-of-take-regs
    (equal (conjoin-output-range start n invals (take (stype-count :reg aignet) regvals) aignet)
           (conjoin-output-range start n invals regvals aignet))
    :hints(("Goal" :in-theory (enable conjoin-output-range output-eval))))


  (defthm conjoin-output-range-of-extension
    (implies (and (aignet-extension-binding)
                  (<= (+ (nfix start) (nfix n)) (stype-count :po orig)))
             (equal (conjoin-output-range start n invals regvals new)
                    (conjoin-output-range start n invals regvals orig)))))

(local (in-theory (enable output-range-equiv-by-badguy)))

(def-apply-transform m-assumption-n-output ((m natp) (n natp))
  :guard (<= (+ m n) (num-outs aignet))
  :correctness-claim
  (and ;; (output-range-equiv m invals regvals new-aignet aignet)
       (implies (< (nfix i) (nfix m))
                (equal (output-eval i invals regvals new-aignet)
                       (output-eval i invals regvals aignet)))
       (implies (and (< (nfix i) (+ (nfix m) (nfix n)))
                     (equal (conjoin-output-range 0 m invals regvals aignet)
                            1))
                (equal (output-eval i invals regvals new-aignet)
                       (output-eval i invals regvals aignet))))
  :parents (aignet-m-assumption-n-output-transforms)
  :short "Stub for an AIG transform that preserves combinational equivalence of
          the first M primary outputs, then preserves combinational equivalence
          of the next N primary outputs under the assumption of the first N")
