; Centaur BED Library
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
; Original authors: Jared Davis <jared@centtech.com>

(in-package "BED")
(include-book "ops")
(include-book "eval")
(include-book "mk1")
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (in-theory (enable* arith-equiv-forwarding)))

(defsection up
  :parents (bed)
  :short "Preliminary implementation of UP operations described in the paper.")

(local (xdoc::set-default-parents up))

; UP-PAST-VAR and UP-PAST-OP are basically the meat of the UP_ONE paper
; described in the paper.  That is, they're the stuff that happens under the
; "else" in the interesting case.

(define up-past-var
  :short "Lift a variable through another (single) variable."
  ((vlift "The variable we are lifting.")
   (vpast "The variable we are lifting it past.")
   (left  "Left branch of vpast, with @('vlift') usually at the top.")
   (right "Right branch of vpast, with @('vlift') usually at the top.")
   ;; NOTE: currently order is irrelevant, but we will probably want it
   ;; here eventually
   (order "Ordering to use for bed construction."))
  :returns
  (mv (bed   "Reduced bed, equivalent @('(if vpast left right)'), but
              with @('vlift') lifted to the top, if possible.")
      (order "Updated order for canonicalization."))
  (b* (((mv lok lvar ltrue lfalse) (bed-match-var left))
       ((mv rok rvar rtrue rfalse) (bed-match-var right))
       ((when (and lok rok (equal lvar vlift) (equal rvar vlift)))
        ;; VLIFT on top of both LEFT and RIGHT.
        (mv (mk-var1 vlift
                     (mk-var1 vpast ltrue rtrue)
                     (mk-var1 vpast lfalse rfalse))
            order))
       ((when (and lok (equal lvar vlift)))
        ;; VLIFT on top of LEFT, not (supposed to be) in RIGHT.
        (mv (mk-var1 vlift
                     (mk-var1 vpast ltrue right)
                     (mk-var1 vpast lfalse right))
            order))
       ((when (and rok (equal rvar vlift)))
        ;; VLIFT on top of RIGHT, not (supposed to be) in LEFT.
        (mv (mk-var1 vlift
                     (mk-var1 vpast left rtrue)
                     (mk-var1 vpast left rfalse))
            order)))
    ;; Else, VLIFT isn't on either side.  There's nothing to lift here.
    (mv (mk-var1 vpast left right)
        order))
  ///
  (defthm up-past-var-correct
    (b* (((mv bed ?order) (up-past-var vlift vpast left right order)))
      (equal (bed-eval bed env)
             (if (bed-env-lookup vpast env)
                 (bed-eval left env)
               (bed-eval right env))))))

(define up-past-op
  :short "Lift a variable through a (single) operator."
  ((vlift atom "The variable we are lifting.")
   (op    bed-op-p "The operator we are lifting it past.")
   (left  "Left branch of op, with @('vlift') usually at the top.")
   (right "Right branch of op, with @('vlift') usually at the top.")
   (order "Ordering to use for bed construction."))
  :returns
  (mv (bed   "Reduced bed, equivalent @('op(left,right)'), but
              with @('vlift') lifted to the top, if possible.")
      (order "Updated order for canonicalization."))
  (b* ((op (bed-op-fix$ op))
       ((mv lok lvar ltrue lfalse) (bed-match-var left))
       ((mv rok rvar rtrue rfalse) (bed-match-var right))
       ((when (and lok rok (equal lvar vlift) (equal rvar vlift)))
        ;; VLIFT on top of both LEFT and RIGHT.
        (b* (((mv new-left order)  (mk-op1 op ltrue rtrue order))
             ((mv new-right order) (mk-op1 op lfalse rfalse order))
             (ans                  (mk-var1 vlift new-left new-right)))
          (mv ans order)))

       ((when (and lok (equal lvar vlift)))
        ;; VLIFT on top of LEFT, not (supposed to be) in RIGHT.
        (b* (((mv new-left order)  (mk-op1 op ltrue right order))
             ((mv new-right order) (mk-op1 op lfalse right order))
             (ans                  (mk-var1 vlift new-left new-right)))
          (mv ans order)))

       ((when (and rok (equal rvar vlift)))
        ;; VLIFT on top of RIGHT, not (supposed to be) in LEFT.
        (b* (((mv new-left order)  (mk-op1 op left rtrue order))
             ((mv new-right order) (mk-op1 op left rfalse order))
             (ans                  (mk-var1 vlift new-left new-right)))
          (mv ans order)))

       ;; Else, VLIFT isn't on either side.  There's nothing to lift here.
       ((mv ans order) (mk-op1 op left right order)))
    (mv ans order))
  ///
  (defthm up-past-op-correct
    (implies (force (atom vlift))
             (b* (((mv bed ?order) (up-past-op vlift op left right order)))
               (equal (bed-eval bed env)
                      (bed-op-eval op
                                   (bed-eval left env)
                                   (bed-eval right env)))))))



(define up-one-aux
  :short "Lift one variable through a bed (recursively)."
  ((vlift "The variable to lift" atom)
   (bed   "The bed to lift it through.")
   (order "Ordering for bed construction operations.")
   (memo  "Memo table mapping bed nodes to lifted equivalents."))
  :returns (mv (bed   "The resulting bed, equivalent to the input bed.")
               (order "Updated order.")
               (memo  "Updated memo table."))
  (b* (((when (atom bed))
        ;; This is already as simple as it can possibly be, no need to lift.
        ;; We may as well canonicalize it.
        (mv (if bed t nil) order memo))

       (look (hons-get bed memo))
       ((when look)
        ;; Already visited this node
        (mv (cdr look) order memo))

       ((cons a b) bed)

       ((unless (integerp b))
        (b* (((when (equal a vlift))
              ;; Found the var we were looking for.  The paper mentions that to
              ;; process unrestricted BEDs here, we need to recursively process
              ;; the left/right branches.  I don't think we need to worry about
              ;; that.  We'll assume things are restricted and we can just stop
              ;; here.
              (mv bed order (hons-acons bed bed memo)))
             ;; Found some variable other than vlift.  Recursively lift vlift
             ;; to the top of the true/false branches, then push them up past
             ;; this variable.
             ((mv left order memo)  (up-one-aux vlift (car$ b) order memo))
             ((mv right order memo) (up-one-aux vlift (cdr$ b) order memo))
             ((mv ans order)        (up-past-var vlift a left right order))
             (memo                  (hons-acons bed ans memo)))
          (mv ans order memo)))

       ;; Otherwise found an operator.  We're just going to lift.
       (op (bed-op-fix b))
       ((mv left order memo)  (up-one-aux vlift (car$ a) order memo))
       ((mv right order memo) (up-one-aux vlift (cdr$ a) order memo))
       ((mv ans order)        (up-past-op vlift op left right order))
       (memo                  (hons-acons bed ans memo)))
    (mv ans order memo)))

(define up-one ((vlift "The variable to lift." atom)
                (bed   "The bed to lift it through.")
                (order "The order to use."))
  :returns (mv (bed "The resulting bed, equivalent to the input bed.")
               (order "The new order to use."))
  (b* ((memo
        ;; Likely big enough to avoid resizing
        (* 2 (fast-alist-len order)))
       ((mv ans order memo) (up-one-aux vlift bed order memo))
       (- (fast-alist-free memo)))
    (mv ans order))
  ///
  (local (defun-sk memo-okp (env memo)
           (forall (bed)
                   (b* ((look (hons-assoc-equal bed memo)))
                     (implies look
                              (equal (bed-eval (cdr look) env)
                                     (bed-eval bed env)))))
           :rewrite :direct))

  (local (defthm memo-okp-when-atom
           (implies (atom memo)
                    (memo-okp env memo))))

  (local (defthm memo-okp-lookup
           (implies (and (case-split (memo-okp env memo))
                         (case-split (hons-assoc-equal bed memo)))
                    (equal (bed-eval (cdr (hons-assoc-equal bed memo)) env)
                           (bed-eval bed env)))))

  (local (defthm memo-okp-extend
           (implies (and (case-split (memo-okp env memo))
                         (case-split (equal (bed-eval bed env)
                                            (bed-eval ans env))))
                    (memo-okp env (hons-acons bed ans memo)))))

  (local (defthm bed-eval-when-not-var
           (implies (and (consp x)
                         (integerp (cdr x)))
                    (equal (bed-eval x env)
                           (bed-op-eval (cdr x)
                                        (bed-eval (caar x) env)
                                        (bed-eval (cdar x) env))))
           :hints(("Goal" :in-theory (enable bed-eval)))))

  (local (defthm crux
           (implies (and (memo-okp env memo)
                         (atom vlift))
                    (b* (((mv ans ?order memo) (up-one-aux vlift bed order memo)))
                      (and (equal (bed-eval ans env)
                                  (bed-eval bed env))
                           (memo-okp env memo))))
           :hints(("Goal"
                   :induct (up-one-aux vlift bed order memo)
                   :do-not '(generalize fertilize eliminate-destructors)
                   :in-theory (e/d (up-one-aux)
                                   (memo-okp hons-acons))
                   :do-not-induct t))
           :otf-flg t))

  (defthm up-one-correct
    (b* (((mv ans ?order) (up-one vlift bed order)))
      (implies (force (atom vlift))
               (equal (bed-eval ans env)
                      (bed-eval bed env))))))


(define up-one* ((vars atom-listp "The variables to lift.")
                 (bed   "The bed to rewrite.")
                 (order "The order to use for bed node construction."))
  :returns (mv (ans "Rewritten version of @('bed'), equivalent to @('bed').")
               (order "Resulting order."))
  (b* (((when (atom vars))
        (mv bed order))
       ((mv bed order)
        (time$ (up-one (car vars) bed order)
               :msg "; UP-ONE: ~st sec, ~sa bytes. (~x0 more to go)~%"
               :args (list (len (cdr vars))))))
    (up-one* (cdr vars) bed order))
  ///
  (defthm up-one*-correct
    (b* (((mv ans ?order) (up-one* vars bed order)))
      (implies (force (atom-listp vars))
               (equal (bed-eval ans env)
                      (bed-eval bed env))))
    :hints(("Goal" :induct (up-one* vars bed order)))))



#||

(define up-all-aux
  :short "Lift all variables up through a bed (recursively)."
  (;; bozo need some variable order
   (bed   "The bed to lift.")
   (order "Ordering for bed construction operations.")
   (memo  "Memo table mapping bed nodes to lifted equivalents."))
  :returns (mv (bed   "The resulting bed, equivalent to the input bed.")
               (order "Updated order.")
               (memo  "Updated memo table."))
  (b* (((when (atom bed))
        ;; This is already as simple as it can possibly be, no need to lift.
        ;; We may as well canonicalize it.
        (mv (if bed t nil) order memo))

       (look (hons-get bed memo))
       ((when look)
        ;; Already visited this node
        (mv (cdr look) order memo))

       ((cons a b) bed)

       ((when (atom a))
        ;; Variable node.  Lift all variables to the top of left and right.
        ;; Could also put them into some order, or not.
        (b* (((mv left order memo)  (up-all-aux (car$ b) order memo))
             ((mv right order memo) (up-all-aux (cdr$ b) order memo))

; BOZO i am here

             ((mv ans order)        (up-past-var vlift a left right order))
             (memo                  (hons-acons bed ans memo)))
          (mv ans order memo)))

       ;; Otherwise found an operator.  We're just going to lift.
       (op (bed-op-fix b))
       ((mv left order memo)  (up-one-aux vlift (car$ a) order memo))
       ((mv right order memo) (up-one-aux vlift (cdr$ a) order memo))
       ((mv ans order)        (up-past-op vlift op left right order))
       (memo                  (hons-acons bed ans memo)))
    (mv ans order memo)))


||#
