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

(include-book "copying")
(std::make-returnspec-config :hints-sub-returnnames t)
(local (std::add-default-post-define-hook :fix))


(defsection aignet-lits-comb-equivalent
  (defun-sk aignet-lits-comb-equivalent (lit1 aignet1 lit2 aignet2)
    (forall (invals regvals)
            (equal (lit-eval lit2 invals regvals aignet2)
                   (lit-eval lit1 invals regvals aignet1)))
    :rewrite :direct)

  (in-theory (disable aignet-lits-comb-equivalent))

  (defthm aignet-lits-comb-equivalent-of-aignet-extension2
    (implies (and (aignet-extension-binding)
                  (aignet-lits-comb-equivalent lit1 aignet1 lit2 orig)
                  (aignet-idp (lit-id lit2) orig))
             (aignet-lits-comb-equivalent lit1 aignet1 lit2 new))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defthm aignet-lits-comb-equivalent-of-aignet-extension1
    (implies (and (aignet-extension-binding)
                  (aignet-lits-comb-equivalent lit1 orig lit2 aignet2)
                  (aignet-idp (lit-id lit1) orig))
             (aignet-lits-comb-equivalent lit1 new lit2 aignet2))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (fty::deffixcong lit-equiv equal (aignet-lits-comb-equivalent lit1 aignet1 lit2 aignet2) lit1
    :hints (("goal" :cases ((aignet-lits-comb-equivalent lit1 aignet1 lit2 aignet2)))
            (And stable-under-simplificationp
                 (b* ((lit (assoc 'aignet-lits-comb-equivalent clause)))
                   `(:expand (,lit))))))

  (defthmd aignet-lits-comb-equivalent-necc-rev
    (implies (aignet-lits-comb-equivalent lit1 aignet1 lit2 aignet2)
             (equal (lit-eval lit1 invals regvals aignet1)
                    (lit-eval lit2 invals regvals aignet2))))

  (fty::deffixcong lit-equiv equal (aignet-lits-comb-equivalent lit1 aignet1 lit2 aignet2) lit2
    :hints (("goal" :cases ((aignet-lits-comb-equivalent lit1 aignet1 lit2 aignet2)))
            (And stable-under-simplificationp
                 (b* ((lit (assoc 'aignet-lits-comb-equivalent clause)))
                   `(:expand (,lit)
                     :in-theory (e/d (aignet-lits-comb-equivalent-necc-rev)
                                     (aignet-lits-comb-equivalent-necc)))))))

  (fty::deffixequiv aignet-lits-comb-equivalent :args ((aignet1 aignet) (aignet2 aignet))
    :hints(("Goal" :in-theory (disable aignet-lits-comb-equivalent)
            :cases ((aignet-lits-comb-equivalent lit1 aignet1 lit2 aignet2)))
           (and stable-under-simplificationp
                (b* ((lit (assoc 'aignet-lits-comb-equivalent clause))
                     (other (cadr (assoc 'not clause))))
                  `(:expand (,lit)
                    :in-theory (disable aignet-lits-comb-equivalent-necc)
                    :use ((:instance aignet-lits-comb-equivalent-necc
                           (lit1 ,(cadr other))
                           (aignet1 ,(caddr other))
                           (lit2 ,(cadr (cddr other)))
                           (aignet2 ,(caddr (cddr other)))
                           (invals (mv-nth 0 (aignet-lits-comb-equivalent-witness . ,(cdr lit))))
                           (regvals (mv-nth 1 (aignet-lits-comb-equivalent-witness . ,(cdr lit))))))))))))

(define aignet-copy-is-comb-equivalent ((n natp)
                                        aignet
                                        copy
                                        aignet2)
  :non-executable t
  :verify-guards nil
  (if (zp n)
      t
    (and (or (equal (id->type (1- n) aignet) (out-type))
             (aignet-lits-comb-equivalent (make-lit (1- n) 0) aignet
                                          (get-lit (1- n) copy) aignet2))
         (aignet-copy-is-comb-equivalent (1- n) aignet copy aignet2)))
  ///
  (defthm aignet-copy-is-comb-equivalent-implies
    (implies (and (aignet-copy-is-comb-equivalent n aignet copy aignet2)
                  (< (nfix m) (nfix n))
                  (not (equal (id->type m aignet) (out-type)))
                  (equal lit (make-lit m 0)))
             (aignet-lits-comb-equivalent lit aignet (nth-lit m copy) aignet2)))

  (defthm aignet-copy-is-comb-equivalent-implies-lit-eval
    (implies (and (aignet-copy-is-comb-equivalent n aignet copy aignet2)
                  (< (nfix m) (nfix n))
                  (not (equal (id->type m aignet) (out-type))))
             (equal (lit-eval (nth-lit m copy) invals regvals aignet2)
                    (id-eval m invals regvals aignet)))
    :hints (("goal" :induct t)
            (and stable-under-simplificationp
                 '(:expand ((:free (invals regvals) (lit-eval (make-lit m 0) invals regvals aignet)))))))

  (defthm aignet-copy-is-comb-equivalent-implies-lit-eval-copy
    (implies (and (aignet-copy-is-comb-equivalent n aignet copy aignet2)
                  (< (lit->var m) (nfix n))
                  (not (equal (id->type (lit->var m) aignet) (out-type))))
             (equal (lit-eval (lit-copy m copy) invals regvals aignet2)
                    (lit-eval m invals regvals aignet)))
    :hints(("Goal" :in-theory (enable lit-copy))))

  (defthm aignet-copy-is-comb-equivalent-of-aignet-extension
    (implies (and (aignet-extension-binding)
                  (aignet-copy-is-comb-equivalent n aignet copy orig)
                  (aignet-copies-in-bounds copy orig))
             (aignet-copy-is-comb-equivalent n aignet copy new)))

  (defthm aignet-copy-is-comb-equivalent-of-update-later
    (implies (and (aignet-copy-is-comb-equivalent n aignet copy aignet2)
                  (<= (nfix n) (nfix m)))
             (aignet-copy-is-comb-equivalent n aignet
                                             (update-nth-lit m lit copy) aignet2)))

  (defthm aignet-copy-is-comb-equivalent-0
    (aignet-copy-is-comb-equivalent 0 aignet copy aignet2)))


(define aignet-copy-is-comb-equivalent-for-non-gates ((n natp)
                                                      aignet
                                                      copy
                                                      aignet2)
  :non-executable t
  :verify-guards nil
  (if (zp n)
      t
    (and (or (equal (id->type (1- n) aignet) (gate-type))
             (equal (id->type (1- n) aignet) (out-type))
             (aignet-lits-comb-equivalent (make-lit (1- n) 0) aignet
                                          (get-lit (1- n) copy) aignet2))
         (aignet-copy-is-comb-equivalent-for-non-gates (1- n) aignet copy aignet2)))
  ///
  (defthm aignet-copy-is-comb-equivalent-for-non-gates-implies
    (implies (and (aignet-copy-is-comb-equivalent-for-non-gates n aignet copy aignet2)
                  (< (nfix m) (nfix n))
                  (not (equal (id->type m aignet) (out-type)))
                  (not (equal (id->type m aignet) (gate-type)))
                  (equal lit (make-lit m 0)))
             (aignet-lits-comb-equivalent lit aignet (nth-lit m copy) aignet2)))

  (defthm aignet-copy-is-comb-equivalent-for-non-gates-implies-lit-eval
    (implies (and (aignet-copy-is-comb-equivalent-for-non-gates n aignet copy aignet2)
                  (not (equal (id->type m aignet) (out-type)))
                  (not (equal (id->type m aignet) (gate-type)))
                  (< (nfix m) (nfix n)))
             (equal (lit-eval (nth-lit m copy) invals regvals aignet2)
                    (id-eval m invals regvals aignet)))
    :hints (("goal" :induct t)
            (and stable-under-simplificationp
                 '(:expand ((:free (invals regvals) (lit-eval (make-lit m 0) invals regvals aignet)))))))

  (defthm aignet-copy-is-comb-equivalent-for-non-gates-of-aignet-extension
    (implies (and (aignet-extension-binding)
                  (aignet-copy-is-comb-equivalent-for-non-gates n aignet copy orig)
                  (aignet-copies-in-bounds copy orig))
             (aignet-copy-is-comb-equivalent-for-non-gates n aignet copy new)))

  (defthm aignet-copy-is-comb-equivalent-for-non-gates-of-update-gate
    (implies (and (aignet-copy-is-comb-equivalent-for-non-gates n aignet copy aignet2)
                  (equal (id->type m aignet) (gate-type)))
             (aignet-copy-is-comb-equivalent-for-non-gates n aignet
                                                           (update-nth-lit m new-lit copy)
                                                           aignet2))))

(defsection init-copy-comb-sweep
  (local (in-theory (enable init-copy-comb)))
  (local (std::set-define-current-function init-copy-comb))

  (local (defthm lit-eval-when-const
           (implies (equal (stype (car (lookup-id n aignet))) :const)
                    (equal (lit-eval (make-lit n neg) invals regvals aignet)
                           (bfix neg)))
           :hints(("Goal" :expand ((lit-eval (make-lit n neg) invals regvals aignet)
                                   (id-eval n invals regvals aignet))))))

  (local (defthm nth-lit-of-nil
           (equal (nth-lit n nil) 0)
           :hints(("Goal" :in-theory (enable nth-lit nth)))))

  (local (in-theory (disable aignet-copy-is-comb-equivalent-for-non-gates-of-aignet-extension
                             lookup-id-in-bounds-when-positive
                             lookup-id-out-of-bounds
                             lookup-stype-in-bounds
                             lookup-stype-out-of-bounds
                             ;; acl2::resize-list-when-atom
                             resize-list)))

  (defret comb-equivalent-of-sweep-init-copy-lemma
    (implies (<= (nfix n) (num-fanins aignet))
             (aignet-copy-is-comb-equivalent-for-non-gates n aignet new-copy new-aignet2))
    :hints(("Goal" :in-theory (enable aignet-copy-is-comb-equivalent-for-non-gates
                                      aignet-lits-comb-equivalent)
            :induct (aignet-copy-is-comb-equivalent-for-non-gates n aignet new-copy new-aignet2))
           (and stable-under-simplificationp
                (let ((witness (acl2::find-call-lst
                                'aignet-lits-comb-equivalent-witness
                                clause)))
                  `(:clause-processor
                    (acl2::simple-generalize-cp
                     clause '(((mv-nth '0 ,witness) . invals)
                              ((mv-nth '1 ,witness) . regvals))))))
           (and stable-under-simplificationp
                '(:cases ((equal (stype (car (lookup-id (+ -1 n) aignet))) :const))))
           (and stable-under-simplificationp
                '(:expand ((:free (n neg aignet) (lit-eval (make-lit n neg) invals regvals aignet))
                           (:free (count stype aignet aignet2)
                            (id-eval (fanin-count (lookup-stype count stype aignet))
                                     invals regvals aignet2))
                           (id-eval (+ -1 n) invals regvals aignet)))))
    :fn init-copy-comb))

(defsection finish-copy-comb-sweep
  (local (in-theory (enable finish-copy-comb)))
  (local (std::set-define-current-function finish-copy-comb))

  (local (defthm aignet-copy-is-comb-equivalent-implies-output-fanins-comb-equiv
           (implies (aignet-copy-is-comb-equivalent (num-fanins aignet) aignet copy aignet2)
                    (output-fanins-comb-equiv aignet copy aignet2))
           :hints(("Goal" :in-theory (e/d (output-fanins-comb-equiv)
                                          (output-fanins-comb-equiv-necc))))))

  (local (defthm aignet-copy-is-comb-equivalent-implies-nxst-fanins-comb-equiv
           (implies (aignet-copy-is-comb-equivalent (num-fanins aignet) aignet copy aignet2)
                    (nxst-fanins-comb-equiv aignet copy aignet2))
           :hints(("Goal" :in-theory (e/d (nxst-fanins-comb-equiv)
                                          (nxst-fanins-comb-equiv-necc))))))

  (defret sweep-finish-copy-comb-equivalent
    (implies (and (aignet-copy-is-comb-equivalent (num-fanins aignet) aignet copy aignet2)
                  (aignet-copies-in-bounds copy aignet2)
                  (equal (stype-count :po aignet2) 0)
                  (equal (stype-count :nxst aignet2) 0)
                  (equal (stype-count :reg aignet2)
                         (stype-count :reg aignet)))
             (comb-equiv new-aignet2 aignet))
    :hints(("Goal" :in-theory (e/d (comb-equiv) (finish-copy-comb))))
    :fn finish-copy-comb))
  
