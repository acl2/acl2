; SVL - Listener-based Hierachical Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2021 Centaur Technology
; Copyright (C) 2022 Intel Corporation
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
; Original author: Mertcan Temel <mert@centtech.com>

(in-package "SVL")

(include-book "centaur/sv/svex/eval" :dir :system)
(include-book "projects/rp-rewriter/top" :dir :system)

(include-book "../fnc-defs")
(include-book "svex-reduce-apply")

(local
 (include-book "../4vec-lemmas"))

(local
 (include-book "../bits-sbits"))

(local
 (rp::fetch-new-events
  (include-book "centaur/bitops/ihs-extensions" :dir :system)
  use-ihs-extensions
  :disabled t))

(local
 (rp::fetch-new-events
  (include-book "ihs/logops-lemmas" :dir :system)
  use-ihs-logops-lemmas
  :disabled t))

(local
 (rp::fetch-new-events
  (include-book "arithmetic-5/top" :dir :system)
  use-arithmetic-5
  :disabled t))

(local
 (rp::fetch-new-events
  (include-book "ihs/quotient-remainder-lemmas" :dir :system)
  use-qr-lemmas
  :disabled t))

(local
 (rp::fetch-new-events
  (include-book "centaur/bitops/equal-by-logbitp" :dir :system)
  use-equal-by-logbitp
  :disabled t))

(define all-nodes-have-bitnot? (svex &key ((depth natp) 'depth))
  (if (zp depth)
      nil
    (let* ((depth (1- depth)))
      (case-match svex
        (('sv::bitnot &)
         t)
        (('sv::bitor x y)
         (and (all-nodes-have-bitnot? x)
              (all-nodes-have-bitnot? y)))
        (('sv::bitand x y)
         (and (all-nodes-have-bitnot? x)
              (all-nodes-have-bitnot? y)))
        (('sv::bitxor x y)
         (or (all-nodes-have-bitnot? x)
             (all-nodes-have-bitnot? y))))))
  ///
  (memoize 'all-nodes-have-bitnot?))

;; (create-case-match-macro de-morgan-pattern-1
;;                          ('sv::bitnot ('sv::bitor ('sv::bitnot x)
;;                                                   ('sv::bitnot y))))

;; (create-case-match-macro de-morgan-pattern-2
;;                          ('sv::bitnot ('sv::bitand ('sv::bitnot x)
;;                                                    ('sv::bitnot y))))

;; (progn
;;   (create-case-match-macro deep1-de-morgan-pattern-1a
;;                            ('sv::bitnot ('sv::bitand ('sv::bitnot x) y))
;;                            :extra-cond (all-nodes-have-bitnot? y)
;;                            )
;;   (create-case-match-macro deep1-de-morgan-pattern-1b
;;                            ('sv::bitnot ('sv::bitand y ('sv::bitnot x)))
;;                            :extra-cond (all-nodes-have-bitnot? y)
;;                            )
;;   (create-case-match-macro deep1-de-morgan-pattern-2a
;;                            ('sv::bitnot ('sv::bitor ('sv::bitnot x) y))
;;                            :extra-cond (all-nodes-have-bitnot? y)
;;                            )
;;   (create-case-match-macro deep1-de-morgan-pattern-2b
;;                            ('sv::bitnot ('sv::bitor y ('sv::bitnot x)))
;;                            :extra-cond (all-nodes-have-bitnot? y)
;;                            ))

(create-case-match-macro xor-pattern-1
                         ('sv::bitand ('sv::bitor x y)
                                      ('sv::bitnot
                                       ('sv::bitand x y))))

(create-case-match-macro xor-pattern-2
                         ('sv::bitand ('sv::bitnot
                                       ('sv::bitand x y))
                                      ('sv::bitor x y)))

(create-case-match-macro bitnot-pattern
                         ('sv::bitnot xx))

(create-case-match-macro bitand-pattern
                         ('sv::bitand x y))

(create-case-match-macro bitor-pattern
                         ('sv::bitor x y))

(progn
  (create-case-match-macro xor-pattern-3a
                           ('sv::bitor ('sv::bitand ('sv::bitnot x) y)
                                       ('sv::bitand x ('sv::bitnot y))))
  (create-case-match-macro xor-pattern-3b
                           ('sv::bitor ('sv::bitand y ('sv::bitnot x))
                                       ('sv::bitand x ('sv::bitnot y))))
  (create-case-match-macro xor-pattern-3c
                           ('sv::bitor ('sv::bitand ('sv::bitnot x) y)
                                       ('sv::bitand ('sv::bitnot y) x)))
  (create-case-match-macro xor-pattern-3d
                           ('sv::bitor ('sv::bitand y ('sv::bitnot x))
                                       ('sv::bitand ('sv::bitnot y) x))))

(progn
  (create-case-match-macro xor-pattern-4a
                           ('sv::bitnot
                            ('sv::bitor ('sv::bitand x1 y1)
                                        ('sv::bitnot ('sv::bitor x2 y2))))
                           :extra-cond (or (and (equal x1 x2)
                                                (equal y1 y2))
                                           (and (equal y1 x2)
                                                (equal x1 y2)))))

(local
 (defsection proofs-with-logbitp

   (local
    (in-theory '(bitp
                 SV::3VEC-P

                 sv::4vec-bitnot
                 sv::3vec-bitnot
                 (:type-prescription lognot)
                 sv::4vec-bitxor
                 sv::4vec-bitand
                 sv::3vec-bitand
                 sv::4vec-bitor
                 sv::3vec-bitor
                 sv::3vec-fix
                 (:e sv::4vec->lower)
                 (:e sv::4vec->upper)
                 (:e logxor)
                 acl2::simplify-logxor
                 acl2::simplify-logior
                 acl2::simplify-logand
                 sv::4vec->lower-of-4vec-fix
                 sv::4vec->upper-of-4vec-fix
                 sv::4vec-p-of-4vec-fix
                 (:type-prescription logbitp)
                 sv::4vec->upper-of-4vec
                 sv::4vec->lower-of-4vec
                 sv::4vec-equal
                 sv::4vec-p-of-4vec
                 ifix
                 (:e acl2::zbp)
                 (:e acl2::BIT->BOOL)
                 (:e acl2::bool->bit)
                 acl2::b-xor
                 acl2::b-ior
                 acl2::b-not
                 acl2::b-and
                 acl2::bfix
                 ;;b-xor-def
                 ;;acl2::bfix-opener
                 ;;(:type-prescription acl2::bitp-of-b-xor)
                 ;;(:rewrite acl2::bfix-opener)
                 (:compound-recognizer acl2::bitp-compound-recognizer)
                 acl2::bitp-of-b-ior
                 acl2::bitp-of-b-xor
                 acl2::bitp-of-b-not
                 acl2::bitp-of-b-and
                 acl2::bool->bit-of-bit->bool
                 bitops::logbit-to-logbitp
                 bitops::logbitp-of-logior
                 bitops::logbitp-of-logxor
                 bitops::logbitp-of-logand
                 bitops::logbitp-of-lognot

                 (:e INTEGER-LENGTH)
                 (:e 4vec-p)

                 (:type-prescription acl2::binary-logior)
                 (:type-prescription acl2::binary-logxor)
                 (:type-prescription acl2::binary-logand)

                 SV::4VEC->UPPER
                 SV::4VEC->LOWER

                 )))

   (local
    (defthm bool->bit-lemma
      (equal (ACL2::ZBP (acl2::BOOL->BIT x))
             (not x))
      :hints (("Goal"
               :in-theory (e/d (acl2::zbp acl2::bool->bit) ())))))

   #|(defthm xor-pattern-1-lemma1
   (implies t ;
   (EQUAL ;
   (4VEC-BITAND ;
   (4VEC-BITOR x y) ;
   (sv::4vec-bitnot (4VEC-BITand x y))) ;
   (SV::4VEC-BITXOR x y))) ;
   :hints ((bitops::logbitp-reasoning)))|#

   (defthm xor-pattern-1-lemma1
     (implies t
              (EQUAL
               (4VEC-BITAND
                (4VEC-BITOR x y)
                (4VEC-BITOR (SV::4VEC-BITnot x)
                            (SV::4VEC-BITnot y)))
               (SV::4VEC-BITXOR x y)))
     :hints ((bitops::logbitp-reasoning)))

   (defthm xor-pattern-1-lemma2
     (implies t
              (EQUAL
               (4VEC-BITAND
                (4VEC-BITOR x y)
                (4VEC-BITOR (SV::4VEC-BITxor -1 x)
                            (SV::4VEC-BITxor -1 y)))
               (SV::4VEC-BITXOR x y)))
     :hints (("Goal"
              :use ((:instance xor-pattern-1-lemma1))
              :in-theory (e/d (4vec-bitnot-to-4vec-bitxor) ()))))

   (defthm xor-pattern-3
     (equal (4vec-bitor
             (4vec-bitand (sv::4vec-bitnot x) y)
             (4vec-bitand x (sv::4vec-bitnot y)))
            (sv::4vec-bitxor x y))
     :hints ((bitops::logbitp-reasoning)))

   (defthm xor-pattern-3-2
     (equal (4vec-bitor
             (4vec-bitand (sv::4vec-bitxor -1 x) y)
             (4vec-bitand (sv::4vec-bitxor -1 y) x))
            (sv::4vec-bitxor x y))
     :hints (("Goal"
              :use ((:instance xor-pattern-3))
              :in-theory (e/d (4VEC-BITAND-ASSOC-AND-COMM
                               4vec-bitnot-to-4vec-bitxor)
                              (SV::4VEC-BITXOR
                               4VEC-BITOR
                               4VEC-BITAND)))))

   (defthm xor-pattern-3-3
     (equal (4vec-bitor
             (4vec-bitand y (sv::4vec-bitxor -1 x))
             (4vec-bitand x (sv::4vec-bitxor -1 y)))
            (sv::4vec-bitxor x y))
     :hints (("Goal"
              :use ((:instance xor-pattern-3))
              :in-theory (e/d (4VEC-BITAND-ASSOC-AND-COMM
                               4vec-bitnot-to-4vec-bitxor)
                              (SV::4VEC-BITXOR
                               4VEC-BITOR
                               4VEC-BITAND)))))

   (defthm xor-pattern-3-4
     (equal (4vec-bitor
             (4vec-bitand (sv::4vec-bitxor -1 x) y )
             (4vec-bitand x (sv::4vec-bitxor -1 y)))
            (sv::4vec-bitxor x y))
     :hints (("Goal"
              :use ((:instance xor-pattern-3))
              :in-theory (e/d (4VEC-BITAND-ASSOC-AND-COMM
                               4vec-bitnot-to-4vec-bitxor)
                              (SV::4VEC-BITXOR
                               4VEC-BITOR
                               4VEC-BITAND)))))

   (defthm xor-pattern-3-5
     (equal (4vec-bitor
             (4vec-bitand y (sv::4vec-bitxor -1 x))
             (4vec-bitand (sv::4vec-bitxor -1 y) x))
            (sv::4vec-bitxor x y))
     :hints (("Goal"
              :use ((:instance xor-pattern-3-3))
              :in-theory (e/d (4VEC-BITAND-ASSOC-AND-COMM)
                              (SV::4VEC-BITXOR
                               4VEC-BITOR
                               4VEC-BITAND)))))



   ;; (defthmd equiv-by-negating
   ;;   (implies (and (syntaxp (and (consp x) (consp y)
   ;;                               (or (case-match x
   ;;                                     (('sv::4vec-bitxor & &) t))
   ;;                                   (case-match y
   ;;                                     (('sv::4vec-bitxor & &) t)))))
   ;;                 (sv::3vec-p x)
   ;;                 (sv::3vec-p y)
   ;;                 (equal (sv::4vec-bitxor -1 x)
   ;;                        (sv::4vec-bitxor -1 y)))
   ;;            (equal (equal x y) t))
   ;;   :hints (("Goal"
   ;;            :in-theory (e/d (SV::3VEC-P
   ;;                             SV::4VEC-BITXOR)
   ;;                            ()))))

   ))

(local
 (in-theory (disable (:DEFINITION SUBSETP-EQUAL)
                     (:REWRITE SV::SVEXLIST-P-WHEN-SUBSETP-EQUAL)

                     (:REWRITE
                      ACL2::MEMBER-EQUAL-NEWVAR-COMPONENTS-1)
                     (:DEFINITION MEMBER-EQUAL)
                     (:DEFINITION ACL2::LOOP$-AS)
                     (:TYPE-PRESCRIPTION MEMBER-EQUAL)

                     (:REWRITE
                      ACL2::MEMBER-EQUAL-NEWVAR-COMPONENTS-3)
                     (:DEFINITION ACL2::EMPTY-LOOP$-AS-TUPLEP)
                     (:DEFINITION ACL2::CDR-LOOP$-AS-TUPLE)
                     (:DEFINITION ACL2::CAR-LOOP$-AS-TUPLE)
                     (:REWRITE
                      ACL2::MEMBER-EQUAL-NEWVAR-COMPONENTS-2)
                     (:DEFINITION ACL2::APPLY$-BADGEP)
                     (:TYPE-PRESCRIPTION ACL2::LOOP$-AS)

                     (:TYPE-PRESCRIPTION SUBSETP-EQUAL))))

(define svex-convert-bitnot-to-bitxor-negate? (svex
                                               &key
                                               (negate 'negate))
  :inline t
  ;;:enabled t
  :returns (res svex-p :hyp (svex-p svex))
  (if negate
      (svex-reduce-w/-env-apply 'sv::bitxor (hons-list -1 svex))
    svex)
  ///

  (local
   (in-theory (disable SV::SVEX-APPLY$-IS-SVEX-APPLY)))

  (svex-eval-lemma-tmpl
   (defret svex-eval-of-<fn>
     (equal (svex-eval res a)
            (if negate
                (sv::4vec-bitxor -1 (svex-eval svex a))
              (svex-eval svex a)))
     :hints (("Goal"
              :expand ((SVEX-APPLY 'BITXOR
                                   (LIST -1 (SVEX-EVAL SVEX A))))
              :in-theory (e/d (SVEX-EVAL
                               SVEX-CALL->FN
                               SVEX-CALL->args
                               SVEX-APPLY
                               svex-kind)
                              ())))
     :fn svex-convert-bitnot-to-bitxor-negate?)))

(defines svex-convert-bitnot-to-bitxor
  :hints (("Goal"
           :expand ((SV::SVEX-COUNT SVEX)
                    (SV::SVEX-COUNT (CADR SVEX))
                    (SV::SVEXLIST-COUNT (CDR SVEX))
                    (SV::SVEXLIST-COUNT (CDR (CADR SVEX))))
           :in-theory (e/d (svex-kind
                            SVEX-CALL->ARGS
                            SVEX-CALL->fn
                            SV::SVEXLIST-COUNT
                            sv::svex-count)
                           ())))
  :verify-guards nil
  (define svex-convert-bitnot-to-bitxor ((svex svex-p)
                                         &key
                                         ((depth natp) 'depth)
                                         ;; depth: how   far  we   should  look   when
                                         ;; deciding to apply de-morgan. 0 does
                                         ;; not  do any  de-morgan.  1 is  only
                                         ;; level and so forth.
                                         (negate ''nil)
                                         (under-bitnot 'under-bitnot))
    :measure (sv::svex-count svex)
    :returns (res)

    ;; under-bitnot will be set when the  current term is under a "bitnot" term
    ;; and we  want to  feel its  effects. Only  "bitxor" carries  through this
    ;; value.

    ;; This function implements a complex demorgan structure where it goes down
    ;; many levels and applies de-morgan on all the levels when necessary.
    
    
    (b* (((when (not (equal (sv::svex-kind svex) :call)))
          (svex-convert-bitnot-to-bitxor-negate? svex)))
      (cond ;; ((de-morgan-pattern-1-p svex)
            ;;  (de-morgan-pattern-1-body
            ;;   svex
            ;;   (sv::svex-call (if negate 'sv::bitor 'sv::bitand)
            ;;                  (hons-list
            ;;                   (svex-convert-bitnot-to-bitxor x
            ;;                                                  :under-bitnot nil
            ;;                                                  :negate negate)
            ;;                   (svex-convert-bitnot-to-bitxor y
            ;;                                                  :under-bitnot nil
            ;;                                                  :negate negate)))))
            ;; ((de-morgan-pattern-2-p svex)
            ;;  (de-morgan-pattern-2-body
            ;;   svex
            ;;   (sv::svex-call (if negate 'sv::bitand 'sv::bitor)
            ;;                  (hons-list
            ;;                   (svex-convert-bitnot-to-bitxor x
            ;;                                                  :under-bitnot nil
            ;;                                                  :negate negate)
            ;;                   (svex-convert-bitnot-to-bitxor y
            ;;                                                  :under-bitnot nil
            ;;                                                  :negate negate)))))

            ;; ((deep1-de-morgan-pattern-1a-p svex)
            ;;  (deep1-de-morgan-pattern-1a-body
            ;;   svex
            ;;   (sv::svex-call 'sv::bitor
            ;;                  (hons-list
            ;;                   (svex-convert-bitnot-to-bitxor x)
            ;;                   (svex-convert-bitnot-to-bitxor
            ;;                    (sv::svex-call 'sv::bitnot (hons-list y)))))))
            ;; ((deep1-de-morgan-pattern-1b-p svex)
            ;;  (deep1-de-morgan-pattern-1b-body
            ;;   svex
            ;;   (sv::svex-call 'sv::bitor
            ;;                  (hons-list
            ;;                   (svex-convert-bitnot-to-bitxor
            ;;                    (sv::svex-call 'sv::bitnot (hons-list y)))
            ;;                   (svex-convert-bitnot-to-bitxor x)))))
            ;; ((deep1-de-morgan-pattern-2a-p svex)
            ;;  (deep1-de-morgan-pattern-2a-body
            ;;   svex
            ;;   (sv::svex-call 'sv::bitand
            ;;                  (hons-list
            ;;                   (svex-convert-bitnot-to-bitxor x)
            ;;                   (svex-convert-bitnot-to-bitxor
            ;;                    (sv::svex-call 'sv::bitnot (hons-list y)))))))
            ;; ((deep1-de-morgan-pattern-2b-p svex)
            ;;  (deep1-de-morgan-pattern-2b-body
            ;;   svex
            ;;   (sv::svex-call 'sv::bitand
            ;;                  (hons-list
            ;;                   (svex-convert-bitnot-to-bitxor
            ;;                    (sv::svex-call 'sv::bitnot (hons-list y)))
            ;;                   (svex-convert-bitnot-to-bitxor x)))))

            ((xor-pattern-1-p svex)
             (xor-pattern-1-body
              svex
              (svex-convert-bitnot-to-bitxor-negate?
               (svex-reduce-w/-env-apply 'sv::bitxor
                                         (hons-list (svex-convert-bitnot-to-bitxor x)
                                                    (svex-convert-bitnot-to-bitxor y))))))
            ((xor-pattern-2-p svex)
             (xor-pattern-2-body
              svex
              (svex-convert-bitnot-to-bitxor-negate?
               (svex-reduce-w/-env-apply 'sv::bitxor
                                         (hons-list (svex-convert-bitnot-to-bitxor x)
                                                    (svex-convert-bitnot-to-bitxor y))))))
            ((xor-pattern-3a-p svex)
             (xor-pattern-3a-body
              svex
              (svex-convert-bitnot-to-bitxor-negate?
               (svex-reduce-w/-env-apply 'sv::bitxor
                                         (hons-list (svex-convert-bitnot-to-bitxor x)
                                                    (svex-convert-bitnot-to-bitxor y))))))
            ((xor-pattern-3b-p svex)
             (xor-pattern-3b-body
              svex
              (svex-convert-bitnot-to-bitxor-negate?
               (svex-reduce-w/-env-apply 'sv::bitxor
                                         (hons-list (svex-convert-bitnot-to-bitxor x)
                                                    (svex-convert-bitnot-to-bitxor y))))))
            ((xor-pattern-3c-p svex)
             (xor-pattern-3c-body
              svex
              (svex-convert-bitnot-to-bitxor-negate?
               (svex-reduce-w/-env-apply 'sv::bitxor
                                         (hons-list (svex-convert-bitnot-to-bitxor x)
                                                    (svex-convert-bitnot-to-bitxor y))))))
            ((xor-pattern-3d-p svex)
             (xor-pattern-3d-body
              svex
              (svex-convert-bitnot-to-bitxor-negate?
               (svex-reduce-w/-env-apply 'sv::bitxor
                                         (hons-list (svex-convert-bitnot-to-bitxor x)
                                                    (svex-convert-bitnot-to-bitxor y))))))
            ((xor-pattern-4a-p svex)
             (xor-pattern-4a-body
              svex
              (declare (ignorable x2 y2))
              (svex-convert-bitnot-to-bitxor-negate?
               (svex-reduce-w/-env-apply 'sv::bitxor
                                         (hons-list (svex-convert-bitnot-to-bitxor x1)
                                                    (svex-convert-bitnot-to-bitxor y1))))))
            ((bitnot-pattern-p svex)
             (bitnot-pattern-body
              svex
              (cond
               (negate
                (svex-reduce-w/-env-apply
                 'sv::unfloat
                 (hons-list (svex-convert-bitnot-to-bitxor xx
                                                           :under-bitnot nil
                                                           :negate nil))))
               (under-bitnot ;; if it is  under bitnot, likely bitxor negations
                             ;; will  cancel each  other later,  so ignore  the
                             ;; complex  de-morgan   chain  for  the   sake  of
                             ;; conservativeness
                (svex-convert-bitnot-to-bitxor-negate?
                 (svex-convert-bitnot-to-bitxor xx :negate nil :under-bitnot nil)
                 :negate t))
               ((rp::and*-exec (all-nodes-have-bitnot? xx)
                               (rp::or*-exec (bitand-pattern-p xx)
                                             (bitor-pattern-p xx)))
                (bitand-pattern-body
                 xx
                 (svex-reduce-w/-env-apply
                  (if (bitand-pattern-p xx) 'sv::bitor 'sv::bitand)
                  (hons-list (svex-convert-bitnot-to-bitxor x :negate t)
                             (svex-convert-bitnot-to-bitxor y :negate t)))))
               (t
                (svex-convert-bitnot-to-bitxor xx
                                               :under-bitnot t
                                               :negate t)))))

            ((rp::and*-exec (rp::or*-exec under-bitnot negate)
                            (all-nodes-have-bitnot? svex)
                            (rp::or*-exec (bitand-pattern-p svex)
                                          (bitor-pattern-p svex)
                                          ))
             (bitand-pattern-body
              svex
              (svex-convert-bitnot-to-bitxor-negate?
               (svex-reduce-w/-env-apply
                (if (bitand-pattern-p svex) 'sv::bitor 'sv::bitand)
                (hons-list (svex-convert-bitnot-to-bitxor x :negate t :under-bitnot t)
                           (svex-convert-bitnot-to-bitxor y :negate t :under-bitnot t)))
               :negate (not negate))))
            (t
             (b* (((sv::Svex-call svex))
                  (under-bitnot (and*-exec under-bitnot (equal svex.fn 'sv::bitxor))))
               (svex-convert-bitnot-to-bitxor-negate?
                (sv::svex-call svex.fn
                               (svexlist-convert-bitnot-to-bitxor svex.args))))))))
  (define svexlist-convert-bitnot-to-bitxor ((lst svexlist-p)
                                             &key
                                             ((depth natp) 'depth)
                                             (under-bitnot 'under-bitnot))
    :measure (sv::svexlist-count lst)
    :returns (res)
    (if (atom lst)
        nil
      (hons (svex-convert-bitnot-to-bitxor (car lst))
            (svexlist-convert-bitnot-to-bitxor (cdr lst)))))
  ///


  (defret-mutual ret-val
    (defret svex-p-of-<fn>
      (implies (svex-p svex)
               (svex-p res))
      :fn svex-convert-bitnot-to-bitxor)
    (defret svexlist-p-of-<fn>
      (implies (svexlist-p lst)
               (svexlist-p res))
      :fn svexlist-convert-bitnot-to-bitxor)
    :hints (("Goal"
             ;;:CASE-SPLIT-LIMITATIONS (4 3)
             :in-theory (e/d ()
                             ((:REWRITE DEFAULT-CDR)
                              SV::SVEX-P-WHEN-MEMBER-EQUAL-OF-SVEXLIST-P
                              (:DEFINITION ACL2::LOOP$-AS)
                              (:REWRITE ACL2::AND*-REM-FIRST)
                              (:REWRITE DEFAULT-CAR)
                              SV::SVEX-P-WHEN-MAYBE-SVEX-P
                              SUBSETP-EQUAL
                              SV::SVEXLIST-P-WHEN-SUBSETP-EQUAL
                              SV::MAYBE-SVEX-P-WHEN-SVEX-P
                              MEMBER-EQUAL)))
            (and stable-under-simplificationp
                 '(:expand ((svex-p svex)
                            (SVEXLIST-P (CDR (CADR SVEX)))
                            (SVEX-P (CADR (CADR SVEX)))
                            (SVEX-P (CADR SVEX))
                            (SVEXLIST-P (CDDR SVEX))
                            (SVEX-P (CADDR SVEX))
                            (SVEXLIST-P (CDR SVEX))
                            (SVEX-CONVERT-BITNOT-TO-BITXOR SVEX))))))

  (verify-guards svex-convert-bitnot-to-bitxor-fn
    :hints (("goal"
             ;; :expand ((svex-p svex)
             ;;          (SVEXLIST-P (CDDR SVEX))
             ;;          (svexlist-p (cdr svex))
             ;;          (svex-p (cadr svex))
             ;;          (svexlist-p (cdr (cadr svex)))
             ;;          (svex-p (cadr (cadr svex)))
             ;;          (svexlist-p (cdr (cadr (cadr svex))))
             ;;          (svexlist-p (cddr (cadr svex)))
             ;;          (SVEXLIST-P (CDR (CADDR (CADR SVEX))))
             ;;          (svex-p (caddr (cadr svex))))
             :in-theory (e/d (sv::svex-kind)
                             ((:e tau-system))))
            (and stable-under-simplificationp
                 '(:expand ((svex-p svex)
                            (SVEXLIST-P (CDDR SVEX))
                            (SVEXLIST-P (CDDR (CADR (CADR SVEX))))
                            (svexlist-p (cdr svex))
                            (svex-p (cadr svex))
                            (svexlist-p (cdr (cadr svex)))
                            (svex-p (cadr (cadr svex)))
                            (svexlist-p (cdr (cadr (cadr svex))))
                            (svexlist-p (cddr (cadr svex)))
                            (SVEXLIST-P (CDR (CADDR (CADR SVEX))))
                            (svex-p (caddr (cadr svex))))))))

  (memoize 'svex-convert-bitnot-to-bitxor
           ;;:condition '(equal (svex-kind svex) :call)
           ;;:aokp t
           )

  (local
   (in-theory (disable sv::svex-apply$-is-svex-apply)))

  (defthmd 4vec-bitxor-of-minus-and-bitor/bitand
    (and (equal (sv::4vec-bitxor -1
                                 (sv::4vec-bitor x y))
                (sv::4vec-bitand (sv::4vec-bitxor -1 x)
                                 (sv::4vec-bitxor -1 y)))
         (equal (sv::4vec-bitxor -1
                                 (sv::4vec-bitand x y))
                (sv::4vec-bitor (sv::4vec-bitxor -1 x)
                                (sv::4vec-bitxor -1 y))))
    :hints (("Goal"
             :use ((:instance 4vec-and-de-morgans))
             :in-theory (e/d (4vec-bitnot-to-4vec-bitxor)
                             (4vec-and-de-morgans)))))



  (svex-eval-lemma-tmpl
   (defret-mutual <fn>-correct
     (defret svex-eval-of-<fn>-correct
       (equal (svex-eval res a)
              (if negate
                  (sv::4vec-bitnot (svex-eval svex a))
                (svex-eval svex a)))
       :fn svex-convert-bitnot-to-bitxor)
     (defret svexlist-eval-<fn>-correct
       (equal (svexlist-eval res a)
              (svexlist-eval lst a))
       :fn svexlist-convert-bitnot-to-bitxor)
     :hints (("Goal"
              :do-not-induct t
              :expand ((SVEX-CONVERT-BITNOT-TO-BITXOR SVEX
                                                      :NEGATE NEGATE))
              :in-theory (e/d (4vec-bitxor-of-minus-and-bitor/bitand
                               4vec-bitnot-to-4vec-bitxor
                               4VEC-BITAND-ASSOC-AND-COMM
                               SVEX-CALL->ARGS
                               svex-kind
                               SVEX-CALL->FN
                               4VECLIST-NTH-SAFE)
                              ()))
             (and stable-under-simplificationp
                  '(:expand ((XOR-PATTERN-4A-P SVEX)
                             (:free (x)
                                    (svex-apply 'bitnot x))
                             (:free (x)
                                    (svex-apply 'bitor x))
                             (:free (x)
                                    (svex-apply 'bitand x))
                             (:free (x)
                                    (svex-apply 'sv::unfloat x))
                             (:free (x)
                                    (svex-eval (cons 'bitxor x) a))
                             (:free (x)
                                    (svex-eval (cons 'bitnot x) a))
                             (:free (x)
                                    (svex-apply 'sv::bitxor x))
                             (:free (x)
                                    (svex-apply 'bitnot x))
                             (:free (x)
                                    (svex-apply 'bitor x))
                             (:free (x)
                                    (nth 1 x)))))))))

(define svexalist-convert-bitnot-to-bitxor ((alist sv::svex-alist-p)
                                            &key
                                            ;; depth: see svex-convert-bitnot-to-bitxor
                                            ((depth natp) 'depth))
  :returns (res sv::svex-alist-p :hyp (sv::svex-alist-p alist))
  (if (atom alist)
      (progn$ (clear-memoize-table 'svex-convert-bitnot-to-bitxor)
              nil)
    (acons (caar alist)
           (svex-convert-bitnot-to-bitxor (cdar alist)
                                          :under-bitnot nil)
           (svexalist-convert-bitnot-to-bitxor (cdr alist))))
  ///
  (local
   (in-theory (disable sv::svex-alist-eval$-is-svex-alist-eval)))

  (svex-eval-lemma-tmpl
   (defret svex-alist-eval-of-<fn>-correct
     (equal (svex-alist-eval res a)
            (svex-alist-eval alist a))
     :hints (("Goal"
              :expand ((SVEX-ALIST-EVAL ALIST A)
                       (SVEX-ALIST-EVAL NIL A))
              :in-theory (e/d (SVEX-ALIST-EVAL)
                              ()))))))
