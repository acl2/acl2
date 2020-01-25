; AIGNET - And-Inverter Graph Networks
; Copyright (C) 2017 Centaur Technology
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

(include-book "centaur/aignet/semantics" :dir :system)
(include-book "arrays")
(local (include-book "std/lists/resize-list" :dir :system ))
(local (in-theory (disable acl2::resize-list-when-atom)))
(local (std::add-default-post-define-hook :fix))

(define count-gates-rec ((id natp)
                         (traversal-num natp)
                         (u32arr) ;; traversal number
                         (aignet))
  :guard (and (< id (num-fanins aignet))
              (<= (num-fanins aignet) (u32-length u32arr)))
  :returns (mv (num-subnodes natp :rule-classes :type-prescription)
               new-u32arr)
  :measure (nfix id)
  :verify-guards nil
  :hooks ((:fix :args (id aignet)))
  (b* (((when (eql traversal-num (get-u32 id u32arr)))
        (mv 0 u32arr))
       (u32arr (set-u32 id traversal-num u32arr))
       (slot0 (id->slot id 0 aignet))
       (type (snode->type slot0)))
    (aignet-case type
      :in (mv 0 u32arr)
      :gate (b* (((mv subs0 u32arr) (count-gates-rec (lit-id (snode->fanin slot0)) traversal-num u32arr aignet))
                 ((mv subs1 u32arr) (count-gates-rec (lit-id (gate-id->fanin1 id aignet)) traversal-num u32arr aignet)))
              (mv (+ 1 subs0 subs1) u32arr))
      :const (mv 0 u32arr)))
  ///
  (local (in-theory (disable (:d count-gates-rec) nth update-nth)))

  (local (defthm len-update-nth-when-less
           (implies (< (nfix n) (len x))
                    (equal (len (update-nth n val x)) (len x)))))

  (defret len-u32arr-of-count-gates-rec
    (implies (and (< (nfix id) (num-fanins aignet))
                  (<= (num-fanins aignet) (len u32arr)))
             (equal (len new-u32arr) (len u32arr)))
    :hints (("goal" :induct <call>
             :expand ((:free (traversal-num) <call>)))))

  (Verify-guards count-gates-rec :hints(("goal" :in-theory(enable aignet-idp)))))

(define count-gates-list-rec ((lits lit-listp)
                                (traversal-num natp)
                                (u32arr)
                                (aignet))
  :guard (and (aignet-lit-listp lits aignet)
              (<= (num-fanins aignet) (u32-length u32arr)))
  :guard-hints (("goal" :in-theory (enable aignet-lit-listp aignet-idp)))
  (b* (((When (atom lits)) (mv nil u32arr))
       (new-trav-num  (+ 1 (lnfix traversal-num)))
       ((mv size u32arr) (count-gates-rec (lit-id (car lits)) new-trav-num u32arr aignet))
       ((mv rest u32arr) (count-gates-list-rec (cdr lits) new-trav-num u32arr aignet)))
    (mv (cons size rest) u32arr)))

(define count-gates-list ((lits lit-listp)
                            (aignet))
  :guard (aignet-lit-listp lits aignet)
  (b* (((acl2::local-stobjs u32arr) (mv sizes u32arr))
       (u32arr (resize-u32 (num-fanins aignet) u32arr)))
    (count-gates-list-rec lits 0 u32arr aignet)))



(define count-gates-mark-rec ((id natp)
                              (mark)
                              (aignet))
  :guard (and (< id (num-fanins aignet))
              (<= (num-fanins aignet) (bits-length mark)))
  :returns (mv (num-subnodes natp :rule-classes :type-prescription)
               new-mark)
  :measure (nfix id)
  :verify-guards nil
  (b* (((when (eql 1 (get-bit id mark)))
        (mv 0 mark))
       (mark (set-bit id 1 mark))
       (slot0 (id->slot id 0 aignet))
       (type (snode->type slot0)))
    (aignet-case type
      :in (mv 0 mark)
      :gate (b* (((mv subs0 mark) (count-gates-mark-rec (lit-id (snode->fanin slot0)) mark aignet))
                 ((mv subs1 mark) (count-gates-mark-rec (lit-id (gate-id->fanin1 id aignet)) mark aignet)))
              (mv (+ 1 subs0 subs1) mark))
      :const (mv 0 mark)
      :out (count-gates-mark-rec (lit-id (snode->fanin slot0)) mark aignet)))
  ///
  (local (in-theory (disable (:d count-gates-mark-rec) nth update-nth)))

  (local (defthm len-update-nth-when-less
           (implies (< (nfix n) (len x))
                    (equal (len (update-nth n val x)) (len x)))))

  (defret len-mark-of-count-gates-mark-rec
    (implies (and (< (nfix id) (num-fanins aignet))
                  (<= (num-fanins aignet) (len mark)))
             (equal (len new-mark) (len mark)))
    :hints (("goal" :induct <call>
             :expand ((:free () <call>)))))

  (Verify-guards count-gates-mark-rec :hints(("goal" :in-theory(enable aignet-idp)))))

(define count-gates-mark ((id natp) aignet)
  :guard (< id (num-fanins aignet))
  :returns (num-subnodes natp :rule-classes :type-prescription)
  (b* (((acl2::local-stobjs mark)
        (mv ans mark))
       (mark (resize-bits (num-fanins aignet) mark)))
    (count-gates-mark-rec id mark aignet)))
       
