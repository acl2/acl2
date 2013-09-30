; AIGNET - And-Inverter Graph Networks
; Copyright (C) 2013 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Sol Swords <sswords@centtech.com>


(in-package "AIGNET")
; cert_param: (hons-only)
(include-book "centaur/misc/fast-cons-memo" :dir :system)
(include-book "from-hons-aig")

(defttag fast-aig-to-aignet)


;; Provides a fast under-the-hood redefinition of aiglist-to-aignet-top.
;; (depends-on "from-hons-aig-fast-raw.lsp")
(acl2::include-raw "from-hons-aig-fast-raw.lsp")




(local (include-book "aig-sim"))

(local
 (progn
   ;; test

   (defun n2v (x)
     (declare (xargs :mode :program))
     (if (zp x)
         nil
       (cons (logbitp 0 x)
             (n2v (ash x -1)))))

   (defun prep-problem (a b)
     (declare (xargs :mode :program))
     (b* ((as (pairlis$ '(a0 a1 a2 a3 a4)
                        (n2v a)))
          (bs (pairlis$ '(b0 b1 b2 b3 b4)
                        (n2v b)))
          (ans (take 6 (n2v (+ a b)))))
       (mv (append as bs) ans)))

   (defun collect-problems (probs)
     (declare (xargs :mode :program))
     (b* (((when (atom probs))
           (mv nil nil))
          ((list a b) (car probs))
          ((mv ins outs) (prep-problem a b))
          ((mv rins routs) (collect-problems (cdr probs))))
       (mv (cons ins rins)
           (cons outs routs))))

   (defun generate-random-problems (n state)
     (declare (xargs :mode :program :stobjs statE))
     (b* (((when (zp n))
           (mv nil state))
          ((mv a state) (random$ 32 state))
          ((mv b state) (random$ 32 state))
          ((mv rest state) (generate-random-problems (1- n) state)))
       (mv (cons (list a b) rest) state)))

   (comp t) ; can be needed when host Lisp doesn't automatically compile, e.g., GCL

   (make-event
    (b* ((s0 (acl2::aig-xor 'a0 'b0))
         (c0 (acl2::aig-and 'a0 'b0))
         (s1 (acl2::aig-xor c0 (acl2::aig-xor 'a1 'b1)))
         (c1 (acl2::aig-ite c0 (acl2::aig-or 'a1 'b1)
                            (acl2::aig-and 'a1 'b1)))
         (s2 (acl2::aig-xor c1 (acl2::aig-xor 'a2 'b2)))
         (c2 (acl2::aig-ite c1 (acl2::aig-or 'a2 'b2)
                            (acl2::aig-and 'a2 'b2)))
         (s3 (acl2::aig-xor c2 (acl2::aig-xor 'a3 'b3)))
         (c3 (acl2::aig-ite c2 (acl2::aig-or 'a3 'b3)
                            (acl2::aig-and 'a3 'b3)))
         (s4 (acl2::aig-xor c3 (acl2::aig-xor 'a4 'b4)))
         (c4 (acl2::aig-ite c3 (acl2::aig-or 'a4 'b4)
                            (acl2::aig-and 'a4 'b4)))
         ((mv random-probs state)
          (generate-random-problems 10000 state))
         (probs (append 
                 '((5 8) (31 31) (18 23) (31 22) (1 31) (12 14))
                 random-probs))
         ((mv ins outs)
          (collect-problems probs))

         ((mv results ?st-alist)
          (aig-fast-biteval-seq-outs/state
           nil 
           (list s0 s1 s2 s3 s4 c4)
           nil
           ins)))
      (if (equal results outs)
          (value '(value-triple :pass))
        (er soft 'check-from-hons-aig-fast
            "Testing of from-hons-aig-fast failed!!"))))))

