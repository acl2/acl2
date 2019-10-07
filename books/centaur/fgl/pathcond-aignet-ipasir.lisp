; FGL - A Symbolic Simulation Framework for ACL2
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



(local (in-theory (enable bounded-pathcond-p-redef)))




(local (in-theory (enable aignet-pathcond-eval-redef)))


(define nbalist-has-sat-lits ((nbalist nbalistp)
                              (sat-lits))
  :measure (len (nbalist-fix nbalist))
  (b* ((nbalist (nbalist-fix nbalist))
       ((when (atom nbalist))
        t))
    (and (aignet-id-has-sat-var (caar nbalist) sat-lits)
         (nbalist-has-sat-lits (cdr nbalist) sat-lits)))
  ///
  (defthm nbalist-has-sat-lits-of-sat-lits-extension
    (implies (and (sat-lit-extension-binding)
                  (sat-lit-extension-p sat-lits2 sat-lits1)
                  (nbalist-has-sat-lits nbalist sat-lits1))
             (nbalist-has-sat-lits nbalist sat-lits2))))


(local (defthm eval-lit-of-lit-negate-cond
         (equal (eval-lit (lit-negate-cond lit neg) env)
                (b-xor neg (eval-lit lit env)))
         :hints(("Goal" :in-theory (enable lit-negate-cond eval-lit)))))

(local (defthm natp-caar-of-nbalist-fix
         (implies (consp (nbalist-fix x))
                  (natp (caar (nbalist-fix x))))
         :rule-classes :type-prescription))

(defsection nbalist-to-cube
  (local (std::set-define-current-function nbalist-to-cube))
  (local (in-theory (enable nbalist-to-cube)))

  (defret aignet-lits-have-sat-vars-of-<fn>
    (implies (nbalist-has-sat-lits nbalist sat-lits)
             (aignet-lits-have-sat-vars cube sat-lits))
    :hints(("Goal" :in-theory (enable aignet-lits-have-sat-vars
                                      nbalist-has-sat-lits))))


  (local (defthm bitp-cdar-of-nbalist-fix
           (implies (consp (nbalist-fix x))
                    (bitp (cdar (nbalist-fix x))))
           :hints(("Goal" :in-theory (enable nbalist-fix)))
           :rule-classes :type-prescription))

  (defthm cnf-for-aignet-implies-aignet-pathcond-eval-when-cnf-sat
    (b* ((invals (cnf->aignet-invals invals cnf-vals sat-lits aignet))
         (regvals (cnf->aignet-regvals regvals cnf-vals sat-lits aignet)))
      (implies (and (sat-lits-wfp sat-lits aignet)
                    (cnf-for-aignet aignet cnf sat-lits)
                    (bounded-pathcond-p nbalist (+ 1 (fanin-count aignet)))
                    (nbalist-has-sat-lits nbalist sat-lits)
                    (equal 1 (satlink::eval-formula cnf cnf-vals)))
               (equal (aignet-pathcond-eval aignet nbalist invals regvals)
                      (bit->bool (satlink::eval-cube
                                  (aignet-lits->sat-lits (nbalist-to-cube nbalist) sat-lits)
                                  cnf-vals)))))
    :hints(("Goal" :in-theory (e/d (aignet-pathcond-eval-redef
                                      bounded-pathcond-p-redef
                                      nbalist-has-sat-lits
                                      aignet-lit->sat-lit
                                      aignet-idp
                                      eval-cube)
                                   ())
            :induct (nbalist-to-cube nbalist)))))
         


;; (define nbalist-to-cube ((nbalist nbalistp)
;;                          (sat-lits))
;;   :measure (len (nbalist-fix nbalist))
;;   :guard (nbalist-has-sat-lits nbalist sat-lits)
;;   :guard-hints (("goal" :in-theory (enable nbalist-has-sat-lits)))
;;   (b* ((nbalist (nbalist-fix nbalist))
;;        ((when (atom nbalist))
;;         nil))
;;     (cons (aignet-lit->sat-lit (make-lit (caar nbalist)
;;                                          (b-not (cdar nbalist)))
;;                                sat-lits)
;;           (nbalist-to-cube (cdr nbalist) sat-lits)))


;;   ///

;;   (defthm nbalist-to-cube-of-sat-lits-extension
;;     (implies (and (sat-lit-extension-binding)
;;                   (sat-lit-extension-p sat-lits2 sat-lits1)
;;                   (nbalist-has-sat-lits nbalist sat-lits1))
;;              (equal (nbalist-to-cube nbalist sat-lits2)
;;                     (nbalist-to-cube nbalist sat-lits1)))
;;     :hints(("Goal" :in-theory (enable nbalist-has-sat-lits)))))
                                      

(Defthm lit-list-listp-of-append
  (implies (and (lit-list-listp x)
                (lit-list-listp y))
           (lit-list-listp (append x y))))

(Defthm lit-listp-of-append
  (implies (and (lit-listp x)
                (lit-listp y))
           (lit-listp (append x y))))

       
(defthm sat-lit-listp-implies-lit-listp-fwd
  (implies (sat-lit-listp x sat-lits)
           (lit-listp x))
  :rule-classes :forward-chaining)

(defthm sat-lit-list-listp-implies-lit-listp-fwd
  (implies (sat-lit-list-listp x sat-lits)
           (lit-list-listp x))
  :rule-classes :forward-chaining)

(fty::deffixcong satlink::lit-list-list-equiv iff (cnf-for-aignet aignet cnf sat-lits) cnf
  :hints ((and stable-under-simplificationp
               (let* ((lit (assoc 'cnf-for-aignet clause))
                      (other (if (eq (third lit) 'cnf)
                                 '(lit-list-list-fix cnf)
                               'cnf)))
                 `(:expand (,lit)
                   :use ((:instance cnf-for-aignet-necc
                          (invals (mv-nth 0 (cnf-for-aignet-witness . ,(cdr lit))))
                          (regvals (mv-nth 1 (cnf-for-aignet-witness . ,(cdr lit))))
                          (cnf-vals (mv-nth 2 (cnf-for-aignet-witness . ,(cdr lit))))
                          (cnf ,other)))
                   :in-theory (disable cnf-for-aignet-necc))))))

(fty::deffixcong satlink::lit-list-equiv satlink::lit-list-equiv (append x y) x)
(fty::deffixcong satlink::lit-list-equiv satlink::lit-list-equiv (append x y) y)

(fty::deffixcong satlink::lit-list-list-equiv satlink::lit-list-list-equiv (append x y) x)
(fty::deffixcong satlink::lit-list-list-equiv satlink::lit-list-list-equiv (append x y) y)


(local (in-theory (enable bounded-pathcond-p-implies-aignet-idp)))

(define nbalist-to-cnf ((nbalist nbalistp)
                           (aignet)
                           (sat-lits)
                           (cnf satlink::lit-list-listp)
                           (cube satlink::lit-listp)
                           (aignet-refcounts))
  :guard (and (ec-call (bounded-pathcond-p nbalist (num-fanins aignet)))
              (<= (num-fanins aignet) (u32-length aignet-refcounts))
              (sat-lits-wfp sat-lits aignet))
  :guard-hints (("goal" :use ((:instance bounded-pathcond-p-necc
                               (id (caar (nbalist-fix nbalist)))
                               (num-fanins (num-fanins aignet))))
                 :in-theory (e/d (aignet-idp)
                                 (bounded-pathcond-p-necc))))
  :measure (len (nbalist-fix nbalist))
  :returns (mv new-sat-lits
               (new-cnf satlink::lit-list-listp)
               (new-cube satlink::lit-listp))
  (b* ((nbalist (nbalist-fix nbalist))
       ((when (atom nbalist))
        (mv sat-lits
            (satlink::lit-list-list-fix cnf)
            (satlink::lit-list-fix cube)))
       ((cons id bit) (car nbalist))
       ;; For a pathcond to eval to true, each ID has to evaluate to its
       ;; corresponding bit from the nbalist.  For the corresponding lit to
       ;; eval to true, we need to NOT negate it if the resulting evaluation is
       ;; 1.  So we negate the bit.
       (lit (make-lit id (b-not bit)))
       ((mv sat-lits cnf)
        (aignet-lit->cnf lit t aignet-refcounts sat-lits aignet cnf))
       (sat-lit (aignet-lit->sat-lit lit sat-lits))
       (cube (cons sat-lit (satlink::lit-list-fix cube))))
    (nbalist-to-cnf (cdr nbalist) aignet sat-lits cnf cube aignet-refcounts))
  ///
  (defret sat-lits-wfp-of-<fn>
    (implies (sat-lits-wfp sat-lits aignet)
             (sat-lits-wfp new-sat-lits aignet)))

  (defret sat-lit-list-listp-cnf-of-<fn>
    (implies (and (sat-lit-list-listp cnf sat-lits)
                  (sat-lits-wfp sat-lits aignet)
                  (bounded-pathcond-p nbalist (num-fanins aignet)))
             (sat-lit-list-listp new-cnf new-sat-lits))
    :hints(("Goal" :in-theory (enable aignet-idp))))

  (defret aignet-id-has-sat-var-of-<fn>
    (implies (aignet-id-has-sat-var id sat-lits)
             (aignet-id-has-sat-var id new-sat-lits)))

  (local (defret aignet-id-has-sat-var-of-aignet-lit->cnf
           :pre-bind ((x (make-lit id neg)))
           (implies (and (sat-lits-wfp sat-lits aignet)
                         (aignet-idp id aignet))
                    (aignet-id-has-sat-var id new-sat-lits))
           :hints (("goal" :use ((:instance good-cnf-of-aignet-lit->cnf
                                  (x (make-lit id neg))))))
           :fn aignet-lit->cnf))

  (defret aignet-id-has-sat-var-of-<fn>-when-nbalist-lookup
    (implies (and (nbalist-lookup id nbalist)
                  (natp id)
                  (sat-lits-wfp sat-lits aignet)
                  (bounded-pathcond-p nbalist (num-fanins aignet)))
             (aignet-id-has-sat-var id new-sat-lits))
    :hints(("Goal" :in-theory (enable nbalist-lookup hons-assoc-equal
                                      aignet-idp
                                      bounded-pathcond-p-redef))))

  (defret nbalist-has-sat-lits-of-<fn>
    (implies (and (sat-lits-wfp sat-lits aignet)
                  (bounded-pathcond-p nbalist (num-fanins aignet)))
             (nbalist-has-sat-lits nbalist new-sat-lits))
    :hints(("Goal" :in-theory (enable nbalist-has-sat-lits
                                      aignet-idp))))

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


  (defret sat-lit-listp-cube-of-<fn>
    (implies (and (sat-lit-listp cube sat-lits)
                  (sat-lits-wfp sat-lits aignet)
                  (bounded-pathcond-p nbalist (num-fanins aignet)))
             (sat-lit-listp new-cube new-sat-lits))
    :hints(("Goal" :in-theory (enable aignet-idp))))

  (defret cnf-for-aignet-of-<fn>
    (implies (and (cnf-for-aignet aignet cnf sat-lits)
                  (sat-lits-wfp sat-lits aignet)
                  (bounded-pathcond-p nbalist (num-fanins aignet))
                  (sat-lit-list-listp cnf sat-lits))
             (cnf-for-aignet aignet new-cnf new-sat-lits))
    :hints(("Goal" :in-theory (enable aignet-idp))))


  ;; (defret ipasir-new-clause-of-<fn>
  ;;   (equal (ipasir::ipasir$a->new-clause new-ipasir) nil))

  ;; (defret ipasir-status-of-<fn>
  ;;   (equal (ipasir::ipasir$a->status new-ipasir) :input))

  ;; (defret consp-ipasir-history-of-<fn>
  ;;   (implies (consp (ipasir::ipasir$a->history ipasir))
  ;;            (consp (ipasir::ipasir$a->history new-ipasir)))
  ;;   :hints(("Goal" :in-theory (enable ipasir::ipasir-input$a
  ;;                                     ipasir-cancel-new-clause
  ;;                                     ipasir::ipasir-assume$a))))


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

  ;; (defund-nx nbalist-to-cnf-formula-ok (nbalist
  ;;                                          aignet
  ;;                                          sat-lits
  ;;                                          ipasir
  ;;                                          aignet-refcounts
  ;;                                          env)
  ;;   (b* (((mv ?new-sat-lits new-ipasir) (nbalist-to-cnf nbalist aignet sat-lits ipasir aignet-refcounts)))
  ;;     (equal (eval-formula (ipasir$a->formula new-ipasir) env) 1)))

  ;; (defret nbalist-to-cnf-formula-extended
  ;;   (iff (equal (eval-formula (ipasir$a->formula new-ipasir) env) 1)
  ;;        (and (equal (eval-formula (ipasir$a->formula ipasir) env) 1)
  ;;             (nbalist-to-cnf-formula-ok nbalist aignet sat-lits ipasir aignet-refcounts env)))
  ;;   :hints(("Goal" :in-theory (enable nbalist-to-cnf-formula-ok))))


  (local (defun-sk nbalist-to-cnf-normalize-cnf-forall (nbalist aignet sat-lits aignet-refcounts)
           (forall (cnf cube)
                   (b* (((mv new-sat-lits1 new-cnf1 new-cube1)
                         (nbalist-to-cnf nbalist aignet sat-lits cnf cube aignet-refcounts))
                        ((mv new-sat-lits2 new-cnf2 new-cube2)
                         (nbalist-to-cnf nbalist aignet sat-lits nil nil aignet-refcounts)))
                     (implies (syntaxp (not (and (equal cnf ''nil)
                                                 (equal cube ''nil))))
                              (and (equal new-cnf1
                                          (append new-cnf2 (lit-list-list-fix cnf)))
                                   (equal new-cube1
                                          (append new-cube2 (lit-list-fix cube)))
                                   (equal new-sat-lits1 new-sat-lits2)))))
           :rewrite :direct))
  (local (in-theory (disable nbalist-to-cnf-normalize-cnf-forall)))

  (local
   (defthm nbalist-to-cnf-normalize-cnf-lemma
     (nbalist-to-cnf-normalize-cnf-forall nbalist aignet sat-lits aignet-refcounts)
     :hints (("goal" :induct (nbalist-to-cnf nbalist aignet sat-lits cnf cube aignet-refcounts))
             (and stable-under-simplificationp
                  `(:expand (,(car (last clause))
                             (:free (cnf cube)
                              (nbalist-to-cnf nbalist aignet sat-lits cnf cube aignet-refcounts))))))))

  (defthm nbalist-to-cnf-normalize-cnf
    (b* (((mv new-sat-lits1 new-cnf1 new-cube1)
          (nbalist-to-cnf nbalist aignet sat-lits cnf cube aignet-refcounts))
         ((mv new-sat-lits2 new-cnf2 new-cube2)
          (nbalist-to-cnf nbalist aignet sat-lits nil nil aignet-refcounts)))
      (implies (syntaxp (not (and (equal cnf ''nil)
                                  (equal cube ''nil))))
               (and (equal new-cnf1
                           (append new-cnf2 (lit-list-list-fix cnf)))
                    (equal new-cube1
                           (append new-cube2 (lit-list-fix cube)))
                    (equal new-sat-lits1 new-sat-lits2)))))

  (defret cnf-for-aignet-of-<fn>-norm
    :pre-bind ((orig-cnf cnf)
               (cnf nil))
    (implies (and (cnf-for-aignet aignet orig-cnf sat-lits)
                  (sat-lits-wfp sat-lits aignet)
                  (bounded-pathcond-p nbalist (num-fanins aignet))
                  (sat-lit-list-listp orig-cnf sat-lits))
             (cnf-for-aignet aignet (append new-cnf orig-cnf)
                             new-sat-lits))
    :hints (("goal" :use cnf-for-aignet-of-nbalist-to-cnf
             :in-theory (disable cnf-for-aignet-of-nbalist-to-cnf))))
  
  (defret sat-lits-extension-p-of-<fn>
    (sat-lit-extension-p new-sat-lits sat-lits))

  (defret nbalist-to-cnf-correct
    (implies (and (equal (eval-formula new-cnf env$) 1)
                  (cnf-for-aignet aignet cnf sat-lits)
                  (sat-lits-wfp sat-lits aignet)
                  (bounded-pathcond-p nbalist (num-fanins aignet))
                  (sat-lit-list-listp cnf sat-lits))
             (equal (eval-cube new-cube env$)
                    (b-and (eval-cube cube env$)
                           (bool->bit (aignet-pathcond-eval aignet nbalist
                                                            (cnf->aignet-invals
                                                             nil env$ new-sat-lits aignet)
                                                            (cnf->aignet-regvals
                                                             nil env$ new-sat-lits aignet))))))
    :hints (("goal" :induct <call>
             :expand (<call>
                      (:free (a b) (eval-cube (cons a b) env$)))
             :in-theory (enable aignet-idp))
            (and stable-under-simplificationp
                 '(:use ((:instance cnf-for-aignet-of-nbalist-to-cnf))
                   :in-theory (e/d ()
                                   (cnf-for-aignet-of-nbalist-to-cnf))))))

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

  (defret nbalist-to-cnf-correct-norm
    :pre-bind ((orig-cnf cnf)
               (cnf nil)
               (orig-cube cube)
               (cube nil))
    (implies (and (equal (eval-formula new-cnf env$) 1)
                  (equal (eval-formula orig-cnf env$) 1)
                  (cnf-for-aignet aignet orig-cnf sat-lits)
                  (sat-lits-wfp sat-lits aignet)
                  (bounded-pathcond-p nbalist (num-fanins aignet))
                  (sat-lit-list-listp orig-cnf sat-lits)
                  (equal (eval-cube orig-cube env$) 1))
             (equal (eval-cube new-cube env$)
                    (bool->bit (aignet-pathcond-eval aignet nbalist
                                                     (cnf->aignet-invals
                                                      nil env$ new-sat-lits aignet)
                                                     (cnf->aignet-regvals
                                                      nil env$ new-sat-lits aignet)))))
    :hints (("goal" :use nbalist-to-cnf-correct
             :in-theory (disable nbalist-to-cnf-correct)))))

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

(local (defthm natp-car-nth-when-nbalistp-type
         (implies (and (nbalistp x)
                       (< n (len x))
                       (natp n))
                  (natp (car (nth n x))))
         :rule-classes :type-prescription))

(local (defthm <-0-minus
         (iff (< 0 (+ (- x) y))
              (< x y))))


(define aignet-pathcond-to-cnf-aux ((n natp)
                                       (aignet-pathcond)
                                       (aignet)
                                       (sat-lits)
                                       (cnf lit-list-listp)
                                       (cube lit-listp)
                                       (aignet-refcounts))
  :guard (and (<= n (aignet-pathcond-len aignet-pathcond))
              (ec-call (bounded-pathcond-p aignet-pathcond (num-fanins aignet)))
              (<= (num-fanins aignet) (u32-length aignet-refcounts))
              (sat-lits-wfp sat-lits aignet))
  :guard-hints (("goal" :use ((:instance bounded-pathcond-p-necc
                               (id (car (nth n aignet-pathcond)))
                               (nbalist aignet-pathcond)
                               (num-fanins (num-fanins aignet))))
                 :in-theory (e/d (aignet-idp)
                                 (bounded-pathcond-p-necc))
                 :do-not-induct t))
  :measure (nfix (- (aignet-pathcond-len aignet-pathcond) (nfix n)))
  :returns (mv new-sat-lits
               (new-cnf lit-list-listp)
               (new-cube lit-listp))
  (b* (((when (mbe :logic (zp (- (aignet-pathcond-len aignet-pathcond) (nfix n)))
                   :exec (eql n (aignet-pathcond-len aignet-pathcond))))
        (mv sat-lits
            (lit-list-list-fix cnf)
            (lit-list-fix cube)))
       (id (aignet-pathcond-nthkey n aignet-pathcond))
       (bit (aignet-pathcond-lookup id aignet-pathcond))
       ;; For a pathcond to eval to true, each ID has to evaluate to its
       ;; corresponding bit from the nbalist.  For the corresponding lit to
       ;; eval to true, we need to NOT negate it if the resulting evaluation is
       ;; 1.  So we negate the bit.
       (lit (make-lit id (b-not bit)))
       ((mv sat-lits cnf)
        (aignet-lit->cnf lit t aignet-refcounts sat-lits aignet cnf))
       (sat-lit (aignet-lit->sat-lit lit sat-lits))
       (cube (cons sat-lit (lit-list-fix cube))))
    (aignet-pathcond-to-cnf-aux
     (1+ (lnfix n)) aignet-pathcond aignet sat-lits cnf cube aignet-refcounts))
  ///
  (defthm aignet-pathcond-to-cnf-aux-elim
    (equal (aignet-pathcond-to-cnf-aux n aignet-pathcond aignet sat-lits cnf cube aignet-refcounts)
           (nbalist-to-cnf (nthcdr n (nbalist-fix aignet-pathcond))
                               aignet sat-lits cnf cube aignet-refcounts))
    :hints(("Goal" :induct (aignet-pathcond-to-cnf-aux n aignet-pathcond aignet sat-lits cnf cube aignet-refcounts)
            :expand ((:free (cnf cube)
                      (nbalist-to-cnf (nthcdr n (nbalist-fix aignet-pathcond))
                                         aignet sat-lits cnf cube aignet-refcounts)))))))


(define aignet-pathcond-to-ipasir-aux ((n natp)
                                       (aignet-pathcond)
                                       (aignet)
                                       (sat-lits)
                                       (ipasir)
                                       (aignet-refcounts))
  :guard (and (<= n (aignet-pathcond-len aignet-pathcond))
              (ec-call (bounded-pathcond-p aignet-pathcond (num-fanins aignet)))
              (<= (num-fanins aignet) (u32-length aignet-refcounts))
              (sat-lits-wfp sat-lits aignet)
              (not (eq (ipasir::ipasir-get-status ipasir) :undef))
              (ipasir::ipasir-empty-new-clause ipasir))
  :guard-hints (("goal" :use ((:instance bounded-pathcond-p-necc
                               (id (car (nth n aignet-pathcond)))
                               (nbalist aignet-pathcond)
                               (num-fanins (num-fanins aignet))))
                 :in-theory (e/d (aignet-idp)
                                 (bounded-pathcond-p-necc))
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
  (defret aignet-pathcond-to-ipasir-aux-status
    (equal (ipasir$a->status new-ipasir) :input))

  (defret aignet-pathcond-to-ipasir-aux-new-clause
    (equal (ipasir$a->new-clause new-ipasir) nil))

  (defret aignet-pathcond-to-ipasir-aux-formula/assumption
    (b* (((mv sat-lits-spec cnf cube)
          (nbalist-to-cnf (nthcdr n (nbalist-fix aignet-pathcond))
                          aignet sat-lits
                          (ipasir::ipasir$a->formula ipasir)
                          (ipasir::ipasir$a->assumption ipasir)
                          aignet-refcounts)))
      (and (equal (ipasir$a->assumption new-ipasir)
                  cube)
           (equal (ipasir$a->formula new-ipasir)
                  cnf)
           (equal new-sat-lits sat-lits-spec)))
    :hints(("Goal" :induct (aignet-pathcond-to-ipasir-aux n aignet-pathcond aignet sat-lits ipasir aignet-refcounts)
            :expand ((:free (cnf cube)
                      (nbalist-to-cnf (nthcdr n (nbalist-fix aignet-pathcond))
                                         aignet sat-lits cnf cube aignet-refcounts))))))

  (defret aignet-pathcond-to-ipasir-aux-history
    (implies (consp (ipasir::ipasir$a->history ipasir))
             (consp (ipasir::ipasir$a->history new-ipasir)))
    :hints(("Goal" :in-theory (enable ipasir::ipasir-input$a
                                      ipasir-cancel-new-clause
                                      ipasir::ipasir-assume$a))))

  (fty::deffixequiv aignet-pathcond-to-ipasir-aux :args ((aignet-pathcond nbalist))))
                              

(define aignet-pathcond-to-ipasir ((aignet-pathcond)
                                   (aignet)
                                   (sat-lits)
                                   (ipasir)
                                   (aignet-refcounts))
  :guard (and (ec-call (bounded-pathcond-p aignet-pathcond (num-fanins aignet)))
              (<= (num-fanins aignet) (u32-length aignet-refcounts))
              (sat-lits-wfp sat-lits aignet)
              (not (eq (ipasir::ipasir-get-status ipasir) :undef))
              (ipasir::ipasir-empty-new-clause ipasir))
  :returns (mv new-sat-lits new-ipasir)
  (aignet-pathcond-to-ipasir-aux 0 aignet-pathcond aignet sat-lits ipasir aignet-refcounts)
  ///
  (defret aignet-pathcond-to-ipasir-status
    (equal (ipasir$a->status new-ipasir) :input))

  (defret aignet-pathcond-to-ipasir-new-clause
    (equal (ipasir$a->new-clause new-ipasir) nil))

  (defret aignet-pathcond-to-ipasir-formula/assumption
    (b* (((mv sat-lits-spec cnf cube)
          (nbalist-to-cnf (nbalist-fix aignet-pathcond)
                          aignet sat-lits
                          (ipasir::ipasir$a->formula ipasir)
                          (ipasir::ipasir$a->assumption ipasir)
                          aignet-refcounts)))
      (and (equal (ipasir$a->assumption new-ipasir)
                  cube)
           (equal (ipasir$a->formula new-ipasir)
                  cnf)
           (equal new-sat-lits sat-lits-spec))))

  (defret aignet-pathcond-to-ipasir-history
    (implies (consp (ipasir::ipasir$a->history ipasir))
             (consp (ipasir::ipasir$a->history new-ipasir)))
    :hints(("Goal" :in-theory (enable ipasir::ipasir-input$a
                                      ipasir-cancel-new-clause
                                      ipasir::ipasir-assume$a))))

  (fty::deffixequiv aignet-pathcond-to-ipasir :args ((aignet-pathcond nbalist))))


(define aignet-pathcond-to-cnf ((aignet-pathcond)
                                (aignet)
                                (sat-lits)
                                (cnf lit-list-listp)
                                (cube lit-listp)
                                (aignet-refcounts))
  :guard (and (ec-call (bounded-pathcond-p aignet-pathcond (num-fanins aignet)))
              (<= (num-fanins aignet) (u32-length aignet-refcounts))
              (sat-lits-wfp sat-lits aignet))
  :enabled t
  :returns (mv new-sat-lits new-cnf new-cube)
  (mbe :logic (non-exec (nbalist-to-cnf aignet-pathcond aignet sat-lits cnf cube aignet-refcounts))
       :exec (aignet-pathcond-to-cnf-aux 0 aignet-pathcond aignet sat-lits cnf cube aignet-refcounts)))


(define aignet-pathcond-to-litarr-aux ((n natp)
                                     (offset natp)
                                     (aignet-pathcond)
                                     (litarr))
  :guard (and (<= n (aignet-pathcond-len aignet-pathcond))
              (<= (+ (aignet-pathcond-len aignet-pathcond) offset) (lits-length litarr)))
  :measure (nfix (- (aignet-pathcond-len aignet-pathcond) (nfix n)))
  :returns (new-litarr)
  (b* (((when (mbe :logic (zp (- (aignet-pathcond-len aignet-pathcond) (nfix n)))
                   :exec (eql (aignet-pathcond-len aignet-pathcond) n)))
        litarr)
       (id (aignet-pathcond-nthkey n aignet-pathcond))
       (bit (aignet-pathcond-lookup id aignet-pathcond))
       ;; For a pathcond to eval to true, each ID has to evaluate to its
       ;; corresponding bit from the nbalist.  For the corresponding lit to
       ;; eval to true, we need to NOT negate it if the resulting evaluation is
       ;; 1.  So we negate the bit.
       (lit (make-lit id (b-not bit)))
       (litarr (set-lit (+ (lnfix n) (lnfix offset)) lit litarr)))
    (aignet-pathcond-to-litarr-aux (1+ (lnfix n)) offset aignet-pathcond litarr))
  ///

  (local (defthm nat-equiv-of-plus
           (implies (nat-equiv k (+ (nfix n) (nfix offset)))
                    (nat-equiv (+ (nfix k) (- (nfix offset))) n))))

  (local (defret nth-of-aignet-pathcond-to-litarr-aux
           (implies (<= (nfix n) (aignet-pathcond-len aignet-pathcond))
                    (equal (nth k new-litarr)
                           (cond ((< (nfix k) (+ (nfix n) (nfix offset))) (nth k litarr))
                                 ((< (nfix k) (+ (nfix offset) (aignet-pathcond-len aignet-pathcond)))
                                  (nth (- (nfix k) (nfix offset)) (nbalist-to-cube aignet-pathcond)))
                                 (t (nth k litarr)))))
           :hints(("Goal" :in-theory (enable* update-nth-lit
                                              acl2::arith-equiv-forwarding)
                   :induct <call>
                   :expand (<call>)))))

  (local (defret len-of-aignet-pathcond-to-litarr-aux
           (implies (<= (+ (nfix offset) (aignet-pathcond-len aignet-pathcond)) (len litarr)) 
                    (equal (len new-litarr)
                           (len litarr)))
           :hints (("goal" :induct <call> :expand (<call>)
                    :in-theory (enable update-nth-lit)))))

  (local (defret true-listp-of-aignet-pathcond-to-litarr-aux
           (implies (true-listp litarr)
                    (true-listp new-litarr))
           :hints (("goal" :induct <call> :expand (<call>)
                    :in-theory (enable update-nth-lit)))))

  (local (include-book "std/lists/nth" :dir :system))
  (local (include-book "std/lists/nthcdr" :dir :system))
  (local (include-book "std/lists/take" :dir :system))
  (local (include-book "arithmetic/top" :dir :system))
  (local (in-theory (disable acl2::nthcdr-of-cdr cdr-of-nthcdr)))

  (defret aignet-pathcond-to-litarr-aux-elim
    (implies (and (<= (nfix n) (aignet-pathcond-len aignet-pathcond))
                  (<= (+ (nfix offset) (aignet-pathcond-len aignet-pathcond)) (len litarr))
                  (true-listp litarr))
             (equal new-litarr
                    (append (take (+ (nfix n) (nfix offset)) litarr)
                            (nthcdr n (nbalist-to-cube aignet-pathcond))
                            (nthcdr (+ (nfix offset) (len (nbalist-fix aignet-pathcond))) litarr))))
    :hints (("goal" :do-not-induct t)
            (acl2::equal-by-nths-hint))))

(define aignet-pathcond-to-litarr ((offset natp)
                                 (aignet-pathcond)
                                 (litarr))
  :guard (<= (+ offset (aignet-pathcond-len aignet-pathcond)) (lits-length litarr))
  (aignet-pathcond-to-litarr-aux 0 offset aignet-pathcond litarr))



(define aignet-pathcond-to-cube-aux ((n natp)
                                     (aignet-pathcond)
                                     (cube lit-listp))
  :guard (<= n (aignet-pathcond-len aignet-pathcond))
  :measure (nfix (- (aignet-pathcond-len aignet-pathcond) (nfix n)))
  :returns (new-cube lit-listp)
  (b* (((when (mbe :logic (zp (- (aignet-pathcond-len aignet-pathcond) (nfix n)))
                   :exec (eql (aignet-pathcond-len aignet-pathcond) n)))
        (lit-list-fix cube))
       (id (aignet-pathcond-nthkey n aignet-pathcond))
       (bit (aignet-pathcond-lookup id aignet-pathcond))
       ;; For a pathcond to eval to true, each ID has to evaluate to its
       ;; corresponding bit from the nbalist.  For the corresponding lit to
       ;; eval to true, we need to NOT negate it if the resulting evaluation is
       ;; 1.  So we negate the bit.
       (lit (make-lit id (b-not bit)))
       (cube (cons lit (lit-list-fix cube))))
    (aignet-pathcond-to-cube-aux (1+ (lnfix n)) aignet-pathcond cube))
  ///
  (defret aignet-pathcond-to-cube-aux-elim
    (equal new-cube
           (revappend (nthcdr n (nbalist-to-cube aignet-pathcond))
                      (lit-list-fix cube)))
    :hints (("goal" :induct <call>
             :expand (<call>
                      (acl2::rev (nthcdr n (nbalist-to-cube aignet-pathcond))))))))

(define aignet-pathcond-to-cube ((aignet-pathcond)
                                 (cube lit-listp))
  :returns (new-cube lit-listp)
  :prepwork ((local (defthm lit-listp-of-rev
                      (implies (lit-listp X)
                               (lit-listp (acl2::rev x)))
                      :hints(("Goal" :in-theory (enable acl2::rev))))))
  (aignet-pathcond-to-cube-aux 0 aignet-pathcond cube)
  ///
  (defret aignet-pathcond-to-cube-elim
    (equal (aignet-pathcond-to-cube aignet-pathcond cube)
           (revappend (nbalist-to-cube aignet-pathcond) (lit-list-fix cube)))))
