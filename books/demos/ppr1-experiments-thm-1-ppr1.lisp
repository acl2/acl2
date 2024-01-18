; Copyright (C) 2023, ForrestHunt, Inc.
; Written by J Strother Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
; Release approved by DARPA with "DISTRIBUTION STATEMENT A. Approved
; for public release. Distribution is unlimited."

; Seven Proofs that PPR1 returns a PPR-TUPLE-P
; -- the Really Slow Proof

; J Moore
; October, 2023

; This book carries out the proofs of THM-1-PPR1 and THM-1-PPR1-LST that are
; skipped in ppr1-experiments.lisp because they are so slow.  For a description
; of the entire ppr1-experiment, see

; :DOC induction-coarse-v-fine-grained

; To see how long it took inspect the .cert.out file after a certification.  In
; September, 2023, it took 2165.19 seconds running the proto-Version 8.6 in CCL
; on a MacBook Pro.

(in-package "ACL2")

(include-book "ppr1-experiments")

; -----------------------------------------------------------------
; Scenario 1

(in-theory (enable ppr1 ppr1-lst))

(defthm-coarse-induction-scheme ; coarse, enabled, :expand
  (defthm thm-1-ppr1
    (implies (and
              (unsigned-byte-p #.*small-nat-bits* width)
              (unsigned-byte-p #.*small-nat-bits* rpc)
              (symbol-to-fixnat-alistp
               (table-alist 'ppr-special-syms (w state))))
             (ppr-tuple-p (ppr1 x print-base print-radix width rpc state eviscp)))
    :flag ppr1
    :rule-classes nil)
  (defthm thm-1-ppr1-lst
    (implies (and
              (unsigned-byte-p #.*small-nat-bits* width)
              (unsigned-byte-p #.*small-nat-bits* rpc)
              (symbol-to-fixnat-alistp
               (table-alist 'ppr-special-syms (w state))))
             (ppr-tuple-lst-p (ppr1-lst lst print-base print-radix width rpc
                                        pair-keywords-p state eviscp)))
    :flag ppr1-lst
    :rule-classes nil)
  :hints (("Goal" 
           :expand ((:free (print-base print-radix width rpc state eviscp)
                           (ppr1 x print-base print-radix width rpc state eviscp))
                    (:free (print-base print-radix width rpc
                                       pair-keywords-p state eviscp)
                           (ppr1-lst lst print-base print-radix width rpc
                                     pair-keywords-p state eviscp))))))
