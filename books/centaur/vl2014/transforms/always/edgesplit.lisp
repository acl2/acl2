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
(include-book "util")
(include-book "../../mlib/stmt-tools")
(local (include-book "../../util/arithmetic"))

(defxdoc edgesplit
  :parents (always-top)
  :short "Split up edge-triggered @('always') blocks that write to multiple
registers."

  :long "<p>Our goal here is to reduce always blocks that write to several
different registers.  We only try to support always blocks with:</p>

<ul>
<li>Edge-triggered sensitivity lists,</li>
<li>Non-blocking assignments to whole identifiers,</li>
<li>If/then/else statements,</li>
<li>Begin/end blocks.</li>
</ul>

<p>For instance, a suitable block might be:</p>

@({
     always @(posedge clk or posedge reset)
       begin
         q1 <= d1;
         if (reset)
            q2 <= 0;
         else
            q2 <= d2;
       end
})

<p>We could split this block up into two always blocks:</p>

@({
     always @(posedge clk or posedge reset)
        q1 <= d1;

     always @(posedge clk or posedge reset)
        if (reset)
           q2 <= 0;
        else
           q2 <= d2;
})

<p>This is just a generally nice simplification that lets us only consider a
single register at a time.</p>

<p>BOZO we currently allow always blocks to be split up even if the assignments
have different delays.  This seems okay.  But it would be good to explore this
more and try to understand whether it's truly reasonable.</p>")

(local (xdoc::set-default-parents edgesplit))

(define vl-edgesplit-atomicstmt-p ((x vl-stmt-p))
  :guard (vl-atomicstmt-p x)
  (case (vl-stmt-kind x)
    (:vl-nullstmt t)
    (:vl-assignstmt (b* (((vl-assignstmt x) x))
                      (and (eq x.type :vl-nonblocking)
                           (vl-idexpr-p x.lvalue))))
    (otherwise
     nil)))

(defines vl-edgesplitstmt-p
  :short "Recognize statements that are simple enough for us to split up."

  :long "<p>Since all the assignments are non-blocking, there's no dependencies
between the order of the assignments and the surrounding if structures.</p>"

  :hints(("Goal" :in-theory (disable (force))))

  (define vl-edgesplitstmt-p ((x vl-stmt-p))
    :measure (vl-stmt-count x)
    (b* (((when (vl-atomicstmt-p x))
          (vl-edgesplit-atomicstmt-p x))
         (kind (vl-stmt-kind x))

         ((when (eq kind :vl-ifstmt))
          (and (vl-edgesplitstmt-p (vl-ifstmt->truebranch x))
               (vl-edgesplitstmt-p (vl-ifstmt->falsebranch x))))

         ((when (eq kind :vl-blockstmt))
          (and (vl-blockstmt->sequentialp x)
               (not (vl-blockstmt->name x))
               (not (vl-blockstmt->vardecls x))
               (not (vl-blockstmt->paramdecls x))
               (not (vl-blockstmt->imports x))
               (vl-edgesplitstmtlist-p (vl-blockstmt->stmts x)))))
      nil))

  (define vl-edgesplitstmtlist-p ((x vl-stmtlist-p))
    :measure (vl-stmtlist-count x)
    (if (atom x)
        t
      (and (vl-edgesplitstmt-p (first x))
           (vl-edgesplitstmtlist-p (rest x)))))
  ///
  (xdoc::without-xdoc ;; gets documented by the defines form
    (deflist vl-edgesplitstmtlist-p (x)
      (vl-edgesplitstmt-p x)
      :already-definedp t)))


(define vl-edgesplit-atomicstmt-lvalues
  ((x (and (vl-stmt-p x)
           (vl-atomicstmt-p x)
           (vl-edgesplit-atomicstmt-p x))))
  :returns (lvalue-names string-listp)
  (case (vl-stmt-kind x)
    (:vl-assignstmt (list (vl-idexpr->name (vl-assignstmt->lvalue x))))
    (otherwise nil))
  :prepwork ((local (in-theory (enable vl-edgesplit-atomicstmt-p)))))

(defines vl-edgesplitstmt-lvalues
  :short "Gather lvalues from simple, splittable statements."

  (define vl-edgesplitstmt-lvalues ((x (and (vl-stmt-p x)
                                            (vl-edgesplitstmt-p x))))
    :returns (lvalue-names string-listp)
    :measure (vl-stmt-count x)
    (b* (((when (vl-atomicstmt-p x))
          (vl-edgesplit-atomicstmt-lvalues x))
         (kind (vl-stmt-kind x))
         ((when (eq kind :vl-ifstmt))
          (append (vl-edgesplitstmt-lvalues (vl-ifstmt->truebranch x))
                  (vl-edgesplitstmt-lvalues (vl-ifstmt->falsebranch x))))
         ((when (eq kind :vl-blockstmt))
          (vl-edgesplitstmtlist-lvalues (vl-blockstmt->stmts x))))
      nil))

  (define vl-edgesplitstmtlist-lvalues ((x (and (vl-stmtlist-p x)
                                                (vl-edgesplitstmtlist-p x))))
    :returns (lvalue-names string-listp)
    :measure (vl-stmtlist-count x)
    (if (atom x)
        nil
      (append (vl-edgesplitstmt-lvalues (first x))
              (vl-edgesplitstmtlist-lvalues (rest x)))))

  :prepwork ((local (in-theory (e/d (vl-edgesplitstmt-p)
                                    ((force)))))))


(define vl-edgesplit-atomicstmt-for-lvalue
  :short "Determine an atomic, splittable statement's effect on a
          single lvalue."
  ((x      "The statement we're splitting into multiple always blocks."
           (and (vl-stmt-p x)
                (vl-atomicstmt-p x)
                (vl-edgesplit-atomicstmt-p x)))
   (lvalue "The particular lvalue we're splitting it up for this time."
           stringp))
  :returns (stmt "A new statement that captures this statement's effect on
                  @('lvalue').  Or, if this statement has nothing to do with
                  @('lvalue'), just a null statement."
                 vl-stmt-p :hyp :fguard)
  (case (vl-stmt-kind x)
    (:vl-assignstmt (if (equal (vl-idexpr->name (vl-assignstmt->lvalue x))
                               lvalue)
                        x
                      (make-vl-nullstmt)))
    (otherwise (make-vl-nullstmt)))
  :prepwork ((local (in-theory (enable vl-edgesplit-atomicstmt-p)))))

(defines vl-edgesplit-stmt-for-lvalue
  :short "Determine a splittable statement's effect on a single lvalue."
  :hints(("Goal" :in-theory (disable (force))))
  (define vl-edgesplit-stmt-for-lvalue
    ((x "Statement we're splitting into multiple always blocks."
        (and (vl-stmt-p x)
             (vl-edgesplitstmt-p x)))
     (lvalue "Particular lvalue we're splitting it up for."
             stringp))
    :returns (stmt vl-stmt-p :hyp :fguard)
    :measure (vl-stmt-count x)
    :verify-guards nil
    (b* (((when (vl-atomicstmt-p x))
          (vl-edgesplit-atomicstmt-for-lvalue x lvalue))
         (kind (vl-stmt-kind x))
         ((when (eq kind :vl-ifstmt))
          (b* (((vl-ifstmt x) x)
               (true  (vl-edgesplit-stmt-for-lvalue x.truebranch lvalue))
               (false (vl-edgesplit-stmt-for-lvalue x.falsebranch lvalue))
               ((when (and (eq (vl-stmt-kind true) :vl-nullstmt)
                           (eq (vl-stmt-kind false) :vl-nullstmt)))
                ;; Collapse 'if (condition) null null' --> null
                true))
            (change-vl-ifstmt x
                              :truebranch true
                              :falsebranch false)))
         ((when (eq kind :vl-blockstmt))
          (b* (((vl-blockstmt x) x)
               (stmts (vl-edgesplit-stmtlist-for-lvalue x.stmts lvalue))
               ((when (atom stmts))
                ;; Collapse 'begin end' --> null
                (make-vl-nullstmt)))
            (change-vl-blockstmt x :stmts stmts))))

      (progn$
       ;; Stupid hack to always create a vl-stmt-p
       (impossible)
       (make-vl-nullstmt))))

  (define vl-edgesplit-stmtlist-for-lvalue
    ((x "Statement list we're splitting up, between a begin/end block"
        (and (vl-stmtlist-p x)
             (vl-edgesplitstmtlist-p x)))
     (lvalue "Particular lvalue we're splitting it up for."
             stringp))
    :returns (stmts vl-stmtlist-p :hyp :fguard)
    :measure (vl-stmtlist-count x)
    (b* (((when (atom x))
          nil)
         (new1 (vl-edgesplit-stmt-for-lvalue (first x) lvalue))
         ((when (eq (vl-stmt-kind new1) :vl-nullstmt))
          ;; Collapse 'null; ___' --> ___
          (vl-edgesplit-stmtlist-for-lvalue (rest x) lvalue)))
      (cons new1
            (vl-edgesplit-stmtlist-for-lvalue (rest x) lvalue))))

  :prepwork ((local (in-theory (e/d (vl-edgesplitstmt-p)))))
  ///
  (verify-guards vl-edgesplit-stmtlist-for-lvalue))


(local (defthm crock
         (implies (vl-eventcontrol-p x)
                  (vl-delayoreventcontrol-p x))))

;; (local (defthm crock2
;;          (implies (vl-edge-control-p x)
;;                   (vl-eventcontrol-p x))
;;          :hints(("Goal" :in-theory (enable vl-edge-control-p)))))

(define vl-edgesplit-make-new-always
  :short "Create the new, split up always blocks for a single lvalue."
  ((lvalue stringp
           "Name of some lvalue.  Should be among the lvalues of the body.")
   (ctrl   (and (vl-delayoreventcontrol-p ctrl)
                (vl-edge-control-p ctrl))
           "Sensitivity list for the original always block.  This will become
            the sensitivity list for each new always block, too.")
   (body   (and (vl-stmt-p body)
                (vl-edgesplitstmt-p body))
           "The body of the always block, simple enough to split.")
   (atts   vl-atts-p
           "Attributes of the original always block, which we'll just repeat
            in each new always block we create.")
   (loc    vl-location-p
           "Location of the original always block, which we'll repeat in each
            new always block we create."))
  :returns (new-always vl-always-p :hyp :fguard)
  (b* ((new-body (vl-edgesplit-stmt-for-lvalue body lvalue))
       ((when (eq (vl-stmt-kind new-body) :vl-nullstmt))
        (raise "Programming error.  Something is horribly wrong with always
                block splitting.  It shouldn't be possible to try to split
                off a null always block for ~s0." lvalue)
        ;; Nonsensical thing for unconditional return value theorem
        (make-vl-always :type :vl-always
                        :stmt body
                        :loc loc))
       (new-stmt (make-vl-timingstmt :ctrl ctrl
                                     :body new-body))
       (new-always (make-vl-always :type :vl-always  ;; BOZO should we make these always_ffs?
                                   :stmt new-stmt
                                   :atts atts
                                   :loc loc)))
    new-always))

(defprojection vl-edgesplit-make-new-alwayses (x ctrl body atts loc)
  (vl-edgesplit-make-new-always x ctrl body atts loc)
  :guard (and (string-listp x)
              (vl-delayoreventcontrol-p ctrl)
              (vl-edge-control-p ctrl)
              (vl-stmt-p body)
              (vl-edgesplitstmt-p body)
              (vl-atts-p atts)
              (vl-location-p loc))
  :result-type vl-alwayslist-p)

(define vl-always-edgesplit ((x vl-always-p))
  :returns (new-alwayses vl-alwayslist-p :hyp :fguard)
  (b* (((vl-always x) x)
       ((unless (or (eq x.type :vl-always)
                    (eq x.type :vl-always-ff)))
        ;; Don't touch always_comb or always_latch blocks.
        (list x))

       ((mv body ctrl ?edges) (vl-match-always-at-some-edges x.stmt))
       ((unless (and body
                     (vl-edgesplitstmt-p body)))
        ;; We won't touch this always block because it's not an edge-triggered
        ;; block or doesn't have a body that seems simple enough.
        (list x))

       ;; Very simple.  Find all the registers that are written to in the block
       (lvalues      (mergesort (vl-edgesplitstmt-lvalues body))))

    ;; Now split up the block so that it separately writes to each of them.
    (vl-edgesplit-make-new-alwayses lvalues ctrl body x.atts x.loc)))

(defmapappend vl-alwayslist-edgesplit (x)
  (vl-always-edgesplit x)
  :guard (vl-alwayslist-p x))

(defthm vl-alwayslist-p-of-vl-alwayslist-edgesplit
  (implies (force (vl-alwayslist-p x))
           (vl-alwayslist-p (vl-alwayslist-edgesplit x)))
  :hints(("Goal" :induct (len x))))


(define vl-module-edgesplit ((x vl-module-p))
  :returns (new-x vl-module-p :hyp :fguard)
  (b* (((vl-module x) x)
       ((when (vl-module->hands-offp x))
        x)

       ((unless x.alwayses)
        ;; Optimization: avoid reconsing when there are no always blocks
        x)

       (alwayses (vl-alwayslist-edgesplit x.alwayses)))
    (change-vl-module x :alwayses alwayses)))

(defprojection vl-modulelist-edgesplit (x)
  (vl-module-edgesplit x)
  :guard (vl-modulelist-p x)
  :result-type vl-modulelist-p)

(define vl-design-edgesplit ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* ((x (vl-design-fix x))
       ((vl-design x) x))
    (change-vl-design x :mods (vl-modulelist-edgesplit x.mods))))




