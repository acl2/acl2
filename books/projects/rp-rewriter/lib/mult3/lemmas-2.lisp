

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2020 Regents of the University of Texas
; All rights reserved.

; Redistribution and use in source and binary forms, with or without
; modification, are permitted provided that the following conditions are
; met:

; o Redistributions of source code must retain the above copyright
;   notice, this list of conditions and the following disclaimer.

; o Redistributions in binary form must reproduce the above copyright
;   notice, this list of conditions and the following disclaimer in the
;   documentation and/or other materials provided with the distribution.

; o Neither the name of the copyright holders nor the names of its
;   contributors may be used to endorse or promote products derived
;   from this software without specific prior written permission.

; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
; "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
; LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
; A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
; HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
; SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
; LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
; DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
; THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
; (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
; OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

; Original Author(s):
; Mertcan Temel         <mert@utexas.edu>

(in-package "RP")

(include-book "projects/rp-rewriter/top" :dir :system)

(include-book "std/util/defines" :dir :system)

(include-book "std/lists/mfc-utils" :dir :system)

(local
 (fetch-new-theory
  (include-book "arithmetic-5/top" :dir :system)
  use-arith-5
  :disabled t))

(progn
  (define lte (a b)
    :verify-guards nil
    (<= a b)
    ///
    (defthm rw-<=-to-lte
      (equal (<= a b)
             (lte a b))))

  (define lt (a b)
    :verify-guards nil
    (< a b)
    ///
    (defthm rw-<-to-lte
      (equal (< a b)
             (lt a b))))

  (define gt (a b)
    :verify-guards nil
    (> a b)
    ///
    (defthm rw->-to-gt
      (equal (> a b)
             (gt a b))))

  (define gte (a b)
    :verify-guards nil
    (>= a b)
    ///
    (defthm rw->=-to-gte
      (equal (>= a b)
             (gte a b))))

  (deftheory rw-dir1
    '(rw-<-to-lte
      rw->=-to-gte
      rw->-to-gt
      rw-<=-to-lte))

  (deftheory rw-dir2
    '(lt lte gte gt)))



(defthm gte-to-lte
  (equal (gte a b)
         (lte b a))
  :hints (("Goal"
           :in-theory (e/d (rw-dir2) (rw-dir1)))))

(defthm lt-to-gt
  (equal (lt a b)
         (gt b a))
  :hints (("Goal"
           :in-theory (e/d (rw-dir2) (rw-dir1)))))


(defthm local-measure-lemma-1
   (implies (and (acl2-numberp a)
                 (acl2-numberp b))
            (and (equal (< (1+ a) (1+ b))
                        (< a b))
                 (equal (lt (1+ a) (1+ b))
                        (lt a b))
                 (equal (> (1+ a) (1+ b))
                        (> a b))
                 (equal (gt (1+ a) (1+ b))
                        (gt a b))
                 (equal (> (+ a 1) (+ b 1))
                        (> a b))
                 (equal (gt (+ a 1) (+ b 1))
                        (gt a b))
                 (equal (< (+ a 1) (+ b 1))
                        (< a b))
                 (equal (lt (+ a 1) (+ b 1))
                        (lt a b))
                 (equal (<= (1+ a) (1+ b))
                        (<= a b))
                 (equal (lte (1+ a) (1+ b))
                        (lte a b))
                 (equal (>= (1+ a) (1+ b))
                        (>= a b))
                 (equal (gte (1+ a) (1+ b))
                        (gte a b))))
   :hints (("Goal"
            :in-theory (e/d (rw-dir2
                             (:REWRITE ACL2::|(+ y x)|)
                             (:REWRITE ACL2::|(equal (if a b c) x)|)
                             (:REWRITE ACL2::EQUAL-OF-PREDICATES-REWRITE))
                            (rw-dir1)))))

(set-ignore-ok t)

(progn

  (define lte-chain-smart-fn-aux (cl a d)
     (if (or (atom cl)
             )
         (mv nil nil)
       (b* ((cur (car cl))
            ((mv rest-b rest-c)
             (lte-chain-smart-fn-aux (cdr cl) a d))
            ((unless (case-match cur (('not &) t)))
             (mv rest-b rest-c))
            (cur (cadr cur)))
         (case-match cur
           (('lte x y)
            (mv (if (and (equal x a) (not (equal y d))) y rest-b)
                (if (and (equal y d) (not (equal x a))) x rest-c)))
           (('gt y x)
            (mv (if (and (or (not rest-b) (equal rest-c d)) (equal x a) )
                    (progn$   y)
                  rest-b)
                (if (and (or (not rest-c) (equal rest-c a)) (equal y d) )
                    (progn$   x)
                  rest-c)))
           (&
            (mv rest-b rest-c))))))

  (define lte-chain-smart-fn (a d mfc state)
     :verify-guards nil
     (b* ( ;(ancestors  (mfc-ancestors mfc))
          (rcnst (access acl2::metafunction-context mfc :rcnst))
          (cl (access acl2::rewrite-constant rcnst :current-clause))
          (?top-cl (access acl2::rewrite-constant rcnst :top-clause))
          (cl (beta-search-reduce-subterms cl (expt 2 30)))
          ((mv b c)
           (lte-chain-smart-fn-aux cl a d))
          ;;(- (cw "rcnst : ~p0 ~%" (cddr rcnst)))
          (b (if (not b) c b))
          (c (if (not c) b c))

          #|(- (and (or (and b c)
          (equal a '(binary-+
          (COUNT-C-LST
          (MV-NTH '0
          (COUGH-DUPLICATES (MV-NTH '2 (C-SUM-MERGE-LST-LST C1-LST 'NIL)))))
          (COUNT-C-LST
          (MV-NTH
          '1
          (COUGH-DUPLICATES (MV-NTH '2 (C-SUM-MERGE-LST-LST C1-LST 'NIL))))))))
          (cw "a: ~p0
          b:~p1
          c:~p2
          d:~p3
          cl:~p4
          "
          a b c d cl
          )))||#)
       (if (and b c)
           (progn$
;(cw "a:~p0 b:~p1 c:~p2, d:~p3 ~%" a b c d)
            `((b . ,b)
              (c . ,c)))
         nil)))

  (defthm ge-chain-smart
     (implies (and (bind-free (lte-chain-smart-fn a d mfc state)
                              (b c))
                   (or (and (gt b a)
                            (gt c b)
                            (gt d c))

                       (and (gt b a)
                            (gte c b)
                            (gte d c))
                       (and (gte b a)
                            (gte c b)
                            (gt d c))
                       (and (gte b a)
                            (gt c b)
                            (gte d c))

                       (and (gte b a)
                            (gt c b)
                            (gt d c))
                       (and (gt b a)
                            (gte c b)
                            (gt d c))
                       (and (gt b a)
                            (gt c b)
                            (gte d c)))
                   )
              (and ;(gt d a)
               (not (lte d a))))
     :hints (("Goal"
              :in-theory (e/d (rw-dir2) (rw-dir1)))))

  (defthm lte-chain-smart
     (implies (and (bind-free (lte-chain-smart-fn a d mfc state)
                              (b c))
                   (or (and (lte a b)
                            (lte b c)
                            (lte c d))

                       (and (lte a b)
                            (lte b c)
                            (lt c d))
                       (and (lte a b)
                            (lt b c)
                            (lte c d))
                       (and (lt a b)
                            (lte b c)
                            (lte c d))

                       (and (lt a b)
                            (lte b c)
                            (lt c d))
                       (and (lte a b)
                            (lt b c)
                            (lt c d))
                       (and (lt a b)
                            (lt b c)
                            (lte c d)))
                   )
              (and ;(lte a d)
               (not (gt a d))))
     :hints (("Goal"
              :in-theory (e/d (rw-dir2) (rw-dir1)))))

  )

(defthm lte-and-gte-implies
  (and (implies (lt x y)
                (and (lte x y)
                     (not (gt x y))))
       (implies (gt x y)
                (and (gte x y)
                     (not (gt y x)))))
  :hints (("Goal"
           :in-theory (e/d (rw-dir2) (rw-dir1)))))


(defthm rewriting-positive-lte-gte-gt-lt
   (AND (IMPLIES (ACL2::rewriting-positive-literal `(lt ,a ,b))
                 (equal (lt a b)
                        (NOT (lte b a))))
        (IMPLIES (ACL2::rewriting-positive-literal `(Gt ,a ,b))
                 (equal (gt a b)
                        (NOT (lte a b))))
        (IMPLIES (ACL2::rewriting-positive-literal `(gte ,a ,b))
                 (equal (gte a b)
                        (NOT (gt b a))))
        (IMPLIES (ACL2::rewriting-positive-literal `(lte ,a ,b))
                 (equal (lte a b)
                        (NOT (gt a b)))))
   :hints (("Goal"
            :in-theory (e/d (rw-dir2)
                            (rw-dir1)))))
