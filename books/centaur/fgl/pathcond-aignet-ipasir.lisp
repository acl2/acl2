; GL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2008-2013 Centaur Technology
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

(include-book "pathcond-aignet")
(include-book "centaur/aignet/ipasir" :dir :system)
(local (include-book "std/util/termhints" :dir :system))
(local (std::add-default-post-define-hook :fix))


(local (defthmd cdar-when-nbalistp
         (implies (and (nbalistp nbalist)
                       (consp nbalist))
                  (cdar nbalist))
         :hints(("Goal" :in-theory (enable nbalistp)))))

(local (defthm cdar-of-nbalist-fix-type
         (let ((nbalist (nbalist-fix nbalist)))
           (implies (consp nbalist)
                    (bitp (cdar nbalist))))
         :hints(("Goal" :in-theory (enable nbalistp)))
         :rule-classes ((:type-prescription :typed-term (cdar (nbalist-fix nbalist))))))

(local (defthm aignet-pathcond-p-redef
         (equal (aignet-pathcond-p nbalist aignet)
                (b* ((nbalist (nbalist-fix nbalist)))
                  (or (atom nbalist)
                      (and (aignet-idp (caar nbalist) aignet)
                           (aignet-pathcond-p (cdr nbalist) aignet)))))
         :hints (("goal" :in-theory (e/d (nbalist-lookup-redef
                                          cdar-when-nbalistp)
                                         (aignet-pathcond-p
                                          aignet-pathcond-p-necc)))
                 (acl2::use-termhint
                  (b* ((pathcond-p (aignet-pathcond-p nbalist aignet))
                       (witness (aignet-pathcond-p-witness nbalist aignet))
                       (nbalist (nbalist-fix nbalist))
                       ;; (pathcond-p2 (aignet-pathcond-p (cdr nbalist) aignet))
                       (witness2 (aignet-pathcond-p-witness (cdr nbalist) aignet)))
                    (if pathcond-p
                        (cond ((atom nbalist) nil)
                              ((not (aignet-idp (caar nbalist) aignet))
                               `(:use ((:instance aignet-pathcond-p-necc
                                        (id ,(acl2::hq (caar nbalist)))))))
                              (t `(:use ((:instance aignet-pathcond-p-necc
                                          (id ,(acl2::hq witness2))))
                                   :expand ((aignet-pathcond-p ,(acl2::hq (cdr nbalist)) aignet)))))
                      (if (atom nbalist)
                          '(:expand ((aignet-pathcond-p nbalist aignet)))
                        `(:expand ((aignet-pathcond-p nbalist aignet))
                          :use ((:instance aignet-pathcond-p-necc
                                 (nbalist ,(acl2::hq (cdr nbalist)))
                                 (id ,(acl2::hq witness))))))))))
         :rule-classes :definition))


(local (defthm aignet-pathcond-eval-redef
         (equal (aignet-pathcond-eval aignet nbalist invals regvals)
                (b* ((nbalist (nbalist-fix nbalist)))
                  (or (atom nbalist)
                      (and (equal (id-eval (caar nbalist) invals regvals aignet)
                                  (cdar nbalist))
                           (aignet-pathcond-eval aignet (cdr nbalist) invals regvals)))))
         :hints (("goal" :in-theory (e/d (nbalist-lookup-redef
                                          cdar-when-nbalistp)
                                         (aignet-pathcond-eval
                                          aignet-pathcond-eval-necc)))
                 (acl2::use-termhint
                  (b* ((pathcond-eval (aignet-pathcond-eval aignet nbalist invals regvals))
                       (witness (aignet-pathcond-eval-witness aignet nbalist invals regvals))
                       (nbalist (nbalist-fix nbalist))
                       ;; (pathcond-p2 (aignet-pathcond-p (cdr nbalist) aignet))
                       (eq (equal (id-eval (caar nbalist) invals regvals aignet)
                                  (cdar nbalist)))
                       (witness2 (aignet-pathcond-eval-witness aignet (cdr nbalist) invals regvals)))
                    (if pathcond-eval
                        (cond ((atom nbalist) nil)
                              ((not eq)
                               `(:use ((:instance aignet-pathcond-eval-necc
                                        (id ,(acl2::hq (caar nbalist)))))))
                              (t `(:use ((:instance aignet-pathcond-eval-necc
                                          (id ,(acl2::hq witness2))))
                                   :expand ((aignet-pathcond-eval aignet ,(acl2::hq (cdr nbalist)) invals regvals)))))
                      (if (atom nbalist)
                          '(:expand ((aignet-pathcond-eval aignet nbalist invals regvals)))
                        `(:expand ((aignet-pathcond-eval aignet nbalist invals regvals))
                          :use ((:instance aignet-pathcond-eval-necc
                                 (nbalist ,(acl2::hq (cdr nbalist)))
                                 (id ,(acl2::hq witness))))))))))
         :rule-classes :definition))


(define nbalist-to-ipasir ((nbalist nbalistp)
                           (aignet)
                           (sat-lits)
                           (ipasir)
                           (aignet-refcounts))
  :guard (and (ec-call (aignet-pathcond-p nbalist aignet))
              (<= (num-fanins aignet) (u32-length aignet-refcounts))
              (sat-lits-wfp sat-lits aignet)
              (not (eq (ipasir::ipasir-get-status ipasir) :undef))
              (ipasir::ipasir-empty-new-clause ipasir))
  :guard-hints (("goal" :use ((:instance aignet-pathcond-p-necc
                               (id (caar (nbalist-fix nbalist)))))
                 :in-theory (e/d (aignet-idp)
                                 (aignet-pathcond-p-necc))))
  :measure (len (nbalist-fix nbalist))
  :returns (mv new-sat-lits
               new-ipasir)
  (b* ((nbalist (nbalist-fix nbalist))
       ((when (atom nbalist))
        (b* ((ipasir (ipasir::ipasir-cancel-new-clause ipasir))
             (ipasir (ipasir::ipasir-input ipasir)))
          (mv sat-lits ipasir)))
       ((cons id bit) (car nbalist))
       ;; For a pathcond to eval to true, each ID has to evaluate to its
       ;; corresponding bit from the nbalist.  For the corresponding lit to
       ;; eval to true, we need to NOT negate it if the resulting evaluation is
       ;; 1.  So we negate the bit.
       (lit (make-lit id (b-not bit)))
       ((mv sat-lits ipasir)
        (aignet-lit->ipasir lit t aignet-refcounts sat-lits aignet ipasir))
       (sat-lit (aignet-lit->sat-lit lit sat-lits))
       (ipasir (ipasir::ipasir-assume ipasir sat-lit)))
    (nbalist-to-ipasir (cdr nbalist) aignet sat-lits ipasir aignet-refcounts))
  ///
  (defret sat-lits-wfp-of-<fn>
    (implies (sat-lits-wfp sat-lits aignet)
             (sat-lits-wfp new-sat-lits aignet)))

  (defret sat-lit-list-listp-formula-of-<fn>
    (implies (and (sat-lit-list-listp (ipasir$a->formula ipasir) sat-lits)
                  (sat-lits-wfp sat-lits aignet)
                  (aignet-pathcond-p nbalist aignet))
             (sat-lit-list-listp (ipasir$a->formula new-ipasir) new-sat-lits)))

  (defret aignet-id-has-sat-var-of-<fn>
    (implies (aignet-id-has-sat-var id sat-lits)
             (aignet-id-has-sat-var id new-sat-lits)))

  (defret aignet-id->sat-lit-of-<fn>
    (implies (aignet-id-has-sat-var id sat-lits)
             (equal (aignet-id->sat-lit id new-sat-lits)
                    (aignet-id->sat-lit id sat-lits))))

  (local
   (defret good-cnf-of-aignet-lit->cnf-rw-make-lit
     (implies (and (equal id (lit-id x))
                   (sat-lits-wfp sat-lits aignet)
                   (aignet-litp x aignet))
              (aignet-id-has-sat-var id new-sat-lits))
     :hints (("goal" :use ((:instance good-cnf-of-aignet-lit->cnf))
              :in-theory (disable good-cnf-of-aignet-lit->cnf)))
     :fn aignet-lit->cnf))

  (local
   (defthm sat-lits-wfp-implies-sat-varp-of-lookup-aignet-id-aignet
     (implies (and (bind-free '((aignet . aignet)) (aignet))
                   (sat-lits-wfp sat-lits aignet)
                   (aignet-id-has-sat-var n sat-lits))
              (sat-varp (satlink::lit->var (aignet-id->sat-lit n sat-lits))
                        sat-lits))))


  (defret sat-lit-listp-assumption-of-<fn>
    (implies (and (sat-lit-listp (ipasir$a->assumption ipasir) sat-lits)
                  (sat-lits-wfp sat-lits aignet)
                  (aignet-pathcond-p nbalist aignet))
             (sat-lit-listp (ipasir$a->assumption new-ipasir) new-sat-lits)))

  (defret cnf-for-aignet-of-<fn>
    (implies (and (cnf-for-aignet aignet (ipasir$a->formula ipasir) sat-lits)
                  (sat-lits-wfp sat-lits aignet)
                  (aignet-pathcond-p nbalist aignet)
                  (sat-lit-list-listp (ipasir$a->formula ipasir) sat-lits))
             (cnf-for-aignet aignet (ipasir$a->formula new-ipasir) new-sat-lits)))


  (defret ipasir-new-clause-of-<fn>
    (equal (ipasir::ipasir$a->new-clause new-ipasir) nil))

  (defret ipasir-status-of-<fn>
    (equal (ipasir::ipasir$a->status new-ipasir) :input))

  (defret consp-ipasir-history-of-<fn>
    (implies (consp (ipasir::ipasir$a->history ipasir))
             (consp (ipasir::ipasir$a->history new-ipasir)))
    :hints(("Goal" :in-theory (enable ipasir::ipasir-input$a
                                      ipasir-cancel-new-clause
                                      ipasir::ipasir-assume$a))))

  (local (defthm eval-lit-of-lit-negate-cond
           (equal (eval-lit (lit-negate-cond lit neg) env)
                  (b-xor neg (eval-lit lit env)))
           :hints(("Goal" :in-theory (enable lit-negate-cond eval-lit)))))

  (local (defthm cnf-for-aignet-implies-id-eval
           (implies (and (cnf-for-aignet aignet cnf sat-lits)
                         (aignet-idp id aignet)
                         (aignet-id-has-sat-var id sat-lits)
                         (equal (eval-formula cnf cnf-vals) 1))
                    (equal (id-eval id
                                    (cnf->aignet-invals 
                                     invals cnf-vals sat-lits aignet)
                                    (cnf->aignet-regvals 
                                     regvals cnf-vals sat-lits aignet)
                                    aignet)
                           (satlink::eval-lit
                            (aignet-id->sat-lit id sat-lits)
                            cnf-vals)))
           :hints (("goal" :use ((:instance aignet-agrees-with-cnf-necc))
                    :in-theory (disable aignet-agrees-with-cnf-necc)))))

  (local (defthm eval-formula-of-append
           (equal (eval-formula (append a b) env)
                  (b-and (eval-formula a env)
                         (eval-formula b env)))
           :hints(("Goal" :in-theory (enable eval-formula)))))

  ;; (defund-nx nbalist-to-ipasir-formula-ok (nbalist
  ;;                                          aignet
  ;;                                          sat-lits
  ;;                                          ipasir
  ;;                                          aignet-refcounts
  ;;                                          env)
  ;;   (b* (((mv ?new-sat-lits new-ipasir) (nbalist-to-ipasir nbalist aignet sat-lits ipasir aignet-refcounts)))
  ;;     (equal (eval-formula (ipasir$a->formula new-ipasir) env) 1)))

  ;; (defret nbalist-to-ipasir-formula-extended
  ;;   (iff (equal (eval-formula (ipasir$a->formula new-ipasir) env) 1)
  ;;        (and (equal (eval-formula (ipasir$a->formula ipasir) env) 1)
  ;;             (nbalist-to-ipasir-formula-ok nbalist aignet sat-lits ipasir aignet-refcounts env)))
  ;;   :hints(("Goal" :in-theory (enable nbalist-to-ipasir-formula-ok))))


  (local (defun-sk nbalist-to-ipasir-normalize-ipasir-forall (nbalist aignet sat-lits aignet-refcounts)
           (forall ipasir
                   (b* (((mv new-sat-lits1 new-ipasir1)
                         (nbalist-to-ipasir nbalist aignet sat-lits ipasir aignet-refcounts))
                        ((mv new-sat-lits2 new-ipasir2)
                         (nbalist-to-ipasir nbalist aignet sat-lits nil aignet-refcounts)))
                     (implies (syntaxp (not (equal ipasir ''nil)))
                              (and (equal (ipasir$a->formula new-ipasir1)
                                          (append (ipasir$a->formula new-ipasir2)
                                                  (ipasir$a->formula ipasir)))
                                   (equal (ipasir$a->assumption new-ipasir1)
                                          (append (ipasir$a->assumption new-ipasir2)
                                                  (ipasir$a->assumption ipasir)))
                                   (equal new-sat-lits1 new-sat-lits2)))))
           :rewrite :direct))
  (local (in-theory (disable nbalist-to-ipasir-normalize-ipasir-forall)))

  (local
   (defthm nbalist-to-ipasir-normalize-ipasir-lemma
     (nbalist-to-ipasir-normalize-ipasir-forall nbalist aignet sat-lits aignet-refcounts)
     :hints (("goal" :induct (nbalist-to-ipasir nbalist aignet sat-lits ipasir aignet-refcounts))
             (and stable-under-simplificationp
                  `(:expand (,(car (last clause))
                             (:free (ipasir)
                              (nbalist-to-ipasir nbalist aignet sat-lits ipasir aignet-refcounts))))))))

  (defthm nbalist-to-ipasir-normalize-ipasir
    (b* (((mv new-sat-lits1 new-ipasir1)
          (nbalist-to-ipasir nbalist aignet sat-lits ipasir aignet-refcounts))
         ((mv new-sat-lits2 new-ipasir2)
          (nbalist-to-ipasir nbalist aignet sat-lits nil aignet-refcounts)))
      (implies (syntaxp (not (equal ipasir ''nil)))
               (and (equal (ipasir$a->formula new-ipasir1)
                           (append (ipasir$a->formula new-ipasir2)
                                   (ipasir$a->formula ipasir)))
                    (equal (ipasir$a->assumption new-ipasir1)
                           (append (ipasir$a->assumption new-ipasir2)
                                   (ipasir$a->assumption ipasir)))
                    (equal new-sat-lits1 new-sat-lits2)))))

  (defret cnf-for-aignet-of-<fn>-norm
    :pre-bind ((orig-ipasir ipasir)
               (ipasir nil))
    (implies (and (cnf-for-aignet aignet (ipasir$a->formula orig-ipasir) sat-lits)
                  (sat-lits-wfp sat-lits aignet)
                  (aignet-pathcond-p nbalist aignet)
                  (sat-lit-list-listp (ipasir$a->formula orig-ipasir) sat-lits))
             (cnf-for-aignet aignet (append (ipasir$a->formula new-ipasir)
                                            (ipasir$a->formula orig-ipasir))
                             new-sat-lits))
    :hints (("goal" :use cnf-for-aignet-of-nbalist-to-ipasir
             :in-theory (disable cnf-for-aignet-of-nbalist-to-ipasir))))

  (defret sat-lits-extension-p-of-<fn>
    (sat-lit-extension-p new-sat-lits sat-lits))

  (defret nbalist-to-ipasir-correct
    (implies (and (equal (eval-formula (ipasir$a->formula new-ipasir) env$) 1)
                  (cnf-for-aignet aignet (ipasir$a->formula ipasir) sat-lits)
                  (sat-lits-wfp sat-lits aignet)
                  (aignet-pathcond-p nbalist aignet)
                  (sat-lit-list-listp (ipasir$a->formula ipasir) sat-lits))
             (equal (eval-cube (ipasir$a->assumption new-ipasir) env$)
                    (b-and (eval-cube (ipasir$a->assumption ipasir) env$)
                           (bool->bit (aignet-pathcond-eval aignet nbalist
                                                            (cnf->aignet-invals
                                                             nil env$ new-sat-lits aignet)
                                                            (cnf->aignet-regvals
                                                             nil env$ new-sat-lits aignet))))))
    :hints (("goal" :induct <call>
             :expand (<call>
                      (:free (a b) (eval-cube (cons a b) env$))))
            (and stable-under-simplificationp
                 '(:use ((:instance cnf-for-aignet-of-nbalist-to-ipasir))
                   :in-theory (disable cnf-for-aignet-of-nbalist-to-ipasir)))))

  (local (defthm eval-cube-of-append
           (equal (satlink::eval-cube (append x y) env)
                  (b-and (satlink::eval-cube x env)
                         (satlink::eval-cube y env)))
           :hints(("Goal" :in-theory (enable satlink::eval-cube)))))

  ;; (local (defthm eval-formula-of-append
  ;;          (equal (satlink::eval-formula (append x y) env)
  ;;                 (b-and (satlink::eval-formula x env)
  ;;                        (satlink::eval-formula y env)))
  ;;          :hints(("Goal" :in-theory (enable satlink::eval-formula)))))

  (defret nbalist-to-ipasir-correct-norm
    :pre-bind ((orig-ipasir ipasir)
               (ipasir nil))
    (implies (and (equal (eval-formula (ipasir$a->formula new-ipasir) env$) 1)
                  (equal (eval-formula (ipasir$a->formula orig-ipasir) env$) 1)
                  (cnf-for-aignet aignet (ipasir$a->formula orig-ipasir) sat-lits)
                  (sat-lits-wfp sat-lits aignet)
                  (aignet-pathcond-p nbalist aignet)
                  (sat-lit-list-listp (ipasir$a->formula orig-ipasir) sat-lits)
                  (equal (eval-cube (ipasir$a->assumption orig-ipasir) env$) 1))
             (equal (eval-cube (ipasir$a->assumption new-ipasir) env$)
                    (bool->bit (aignet-pathcond-eval aignet nbalist
                                                     (cnf->aignet-invals
                                                      nil env$ new-sat-lits aignet)
                                                     (cnf->aignet-regvals
                                                      nil env$ new-sat-lits aignet)))))
    :hints (("goal" :use nbalist-to-ipasir-correct
             :in-theory (disable nbalist-to-ipasir-correct)))))

(defthm sat-lit-listp-of-append
  (implies (and (sat-lit-listp x sat-lits)
                (sat-lit-listp y sat-lits))
           (sat-lit-listp (append x y) sat-lits)))

;; (defthm sat-lit-list-listp-of-append
;;   (implies (and (sat-lit-list-listp x sat-lits)
;;                 (sat-lit-list-listp y sat-lits))
;;            (sat-lit-list-listp (append x y) sat-lits)))


(local (defthm natp-car-nth-when-nbalistp
         (implies (and (nbalistp x)
                       (< (nfix n) (len x)))
                  (natp (car (nth n x))))
         :hints(("Goal" :in-theory (enable nbalistp)))))

(local (defthm bitp-cdr-nth-when-nbalistp
         (implies (and (nbalistp x)
                       (< (nfix n) (len x)))
                  (and (bitp (cdr (nth n x)))
                       (cdr (nth n x))))
         :hints(("Goal" :in-theory (enable nbalistp)))))


(local (defthm nbalist-lookup-of-car-nth
         (implies (and (nbalistp x)
                       (< (nfix n) (len x)))
                  (equal (cdr (nth n x))
                         (nbalist-lookup (car (nth n x)) x)))
         :hints(("Goal" :in-theory (enable nbalistp nth nbalist-lookup-redef)
                 :induct (nth n x))
                (and stable-under-simplificationp
                     '(:use ((:instance bitp-cdr-nth-when-nbalistp
                              (n (1- n)) (x (cdr x))))
                       :in-theory (disable bitp-cdr-nth-when-nbalistp))))))

(local (defthm nbalist-lookup-of-car-nth-exists
         (implies (< (nfix n) (len (nbalist-fix x)))
                  (nbalist-lookup (car (nth n (nbalist-fix x))) x))
         :hints (("goal" :use ((:instance nbalist-lookup-of-car-nth
                                (x (nbalist-fix x)))
                               (:instance bitp-cdr-nth-when-nbalistp
                                (x (nbalist-fix x))))
                  :in-theory (disable nbalist-lookup-of-car-nth
                                      bitp-cdr-nth-when-nbalistp)))))

(local (defthm nbalist-lookup-of-car-nth-exists-nofix
         (implies (and (nbalistp x)
                       (< (nfix n) (len x)))
                  (nbalist-lookup (car (nth n x)) x))
         :hints (("goal" :use ((:instance nbalist-lookup-of-car-nth
                                (x (nbalist-fix x)))
                               (:instance bitp-cdr-nth-when-nbalistp
                                (x (nbalist-fix x))))
                  :in-theory (disable nbalist-lookup-of-car-nth
                                      bitp-cdr-nth-when-nbalistp)))))


(local (defthm nbalistp-of-nthcdr
         (implies (nbalistp x)
                  (nbalistp (nthcdr n x)))
         :hints(("Goal" :in-theory (enable nbalistp nthcdr)))))

(local (defthm nthcdr-of-nil
         (equal (nthcdr n nil) nil)))

(local (defthm consp-of-nthcdr
         (iff (consp (nthcdr n x))
              (< (nfix n) (len x)))))

(local (defthm car-of-nthcdr
         (equal (car (nthcdr n x))
                (nth n x))))

(local (defthm cdr-of-nthcdr
         (equal (cdr (nthcdr n x))
                (nthcdr n (cdr x)))))


(define aignet-pathcond-to-ipasir-aux ((n natp)
                                       (aignet-pathcond)
                                       (aignet)
                                       (sat-lits)
                                       (ipasir)
                                       (aignet-refcounts))
  :guard (and (<= n (aignet-pathcond-len aignet-pathcond))
              (ec-call (aignet-pathcond-p aignet-pathcond aignet))
              (<= (num-fanins aignet) (u32-length aignet-refcounts))
              (sat-lits-wfp sat-lits aignet)
              (not (eq (ipasir::ipasir-get-status ipasir) :undef))
              (ipasir::ipasir-empty-new-clause ipasir))
  :guard-hints (("goal" :use ((:instance aignet-pathcond-p-necc
                               (id (car (nth n aignet-pathcond)))
                               (nbalist aignet-pathcond)))
                 :in-theory (e/d (aignet-idp)
                                 (aignet-pathcond-p-necc))
                 :do-not-induct t))
  :measure (nfix (- (aignet-pathcond-len aignet-pathcond) (nfix n)))
  :returns (mv new-sat-lits
               new-ipasir)
  (b* (((when (mbe :logic (zp (- (aignet-pathcond-len aignet-pathcond) (nfix n)))
                   :exec (eql n (aignet-pathcond-len aignet-pathcond))))
        (b* ((ipasir (ipasir::ipasir-cancel-new-clause ipasir))
             (ipasir (ipasir::ipasir-input ipasir)))
          (mv sat-lits ipasir)))
       (id (aignet-pathcond-nthkey n aignet-pathcond))
       (bit (aignet-pathcond-lookup id aignet-pathcond))
       ;; For a pathcond to eval to true, each ID has to evaluate to its
       ;; corresponding bit from the nbalist.  For the corresponding lit to
       ;; eval to true, we need to NOT negate it if the resulting evaluation is
       ;; 1.  So we negate the bit.
       (lit (make-lit id (b-not bit)))
       ((mv sat-lits ipasir)
        (aignet-lit->ipasir lit t aignet-refcounts sat-lits aignet ipasir))
       (sat-lit (aignet-lit->sat-lit lit sat-lits))
       (ipasir (ipasir::ipasir-assume ipasir sat-lit)))
    (aignet-pathcond-to-ipasir-aux
     (1+ (lnfix n)) aignet-pathcond aignet sat-lits ipasir aignet-refcounts))
  ///
  (defthm aignet-pathcond-to-ipasir-aux-elim
    (equal (aignet-pathcond-to-ipasir-aux n aignet-pathcond aignet sat-lits ipasir aignet-refcounts)
           (nbalist-to-ipasir (nthcdr n (nbalist-fix aignet-pathcond))
                               aignet sat-lits ipasir aignet-refcounts))
    :hints(("Goal" :induct (aignet-pathcond-to-ipasir-aux n aignet-pathcond aignet sat-lits ipasir aignet-refcounts)
            :expand ((:free (ipasir)
                      (nbalist-to-ipasir (nthcdr n (nbalist-fix aignet-pathcond))
                                         aignet sat-lits ipasir aignet-refcounts)))))))
                              

(define aignet-pathcond-to-ipasir ((aignet-pathcond)
                                   (aignet)
                                   (sat-lits)
                                   (ipasir)
                                   (aignet-refcounts))
  :guard (and (ec-call (aignet-pathcond-p aignet-pathcond aignet))
              (<= (num-fanins aignet) (u32-length aignet-refcounts))
              (sat-lits-wfp sat-lits aignet)
              (not (eq (ipasir::ipasir-get-status ipasir) :undef))
              (ipasir::ipasir-empty-new-clause ipasir))
  :enabled t
  (mbe :logic (non-exec (nbalist-to-ipasir aignet-pathcond aignet sat-lits ipasir aignet-refcounts))
       :exec (aignet-pathcond-to-ipasir-aux 0 aignet-pathcond aignet sat-lits ipasir aignet-refcounts)))


       




