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

(include-book "pathcond")
(include-book "logicman-transform")


(local (defun nbalist-ind (nbalist)
         (declare (xargs :measure (len (nbalist-fix nbalist))))
         (let ((nbalist (nbalist-fix nbalist)))
           (if (atom nbalist)
               nbalist
             (cons (car nbalist)
                   (nbalist-ind (cdr nbalist)))))))

(define aignet-bfr-eval (bfr invals regvals aignet)
  :verify-guards nil
  (cond ((eq bfr t) t)
        ((eq bfr nil) nil)
        (t (bit->bool (lit-eval bfr invals regvals aignet))))
  ///
  (local (defthm lit-eval-when-equal-aignet-lit-fix
           (implies (and (syntaxp (not (quotep x)))
                         (equal lit (aignet-lit-fix x aignet))
                         (syntaxp (quotep lit)))
                    (equal (lit-eval x invals regvals aignet)
                           (lit-eval lit invals regvals aignet)))))

  (defthmd aignet-bfr-eval-is-bfr-eval
    (implies (and (fgl::lbfr-mode-is :aignet)
                  (equal num-ins (num-ins (fgl::logicman->aignet fgl::logicman))))
             (equal (aignet-bfr-eval bfr
                                     (fgl::alist-to-bitarr num-ins env nil)
                                     nil
                                     (fgl::logicman->aignet fgl::logicman))
                    (fgl::bfr-eval bfr env)))
    :hints(("Goal" :in-theory (enable fgl::bfr-eval fgl::aignet-lit->bfr
                                      fgl::bfr-fix
                                      fgl::bfr->aignet-lit))))

  (defthm aignet-bfr-eval-of-bfr-map
    (implies (and (fgl::bfr-litarr-correct-p bfrs env litarr logicman2 logicman)
                  (member bfr bfrs)
                  (fgl::lbfr-mode-is :aignet logicman)
                  (fgl::lbfr-mode-is :aignet logicman2)
                  (equal num-ins (num-ins (fgl::logicman->aignet logicman)))
                  (equal num-ins (num-ins (fgl::logicman->aignet logicman2))))
             (equal (aignet-bfr-eval (fgl::bfr-map bfr litarr)
                                     (fgl::alist-to-bitarr num-ins env nil) nil
                                     (fgl::logicman->aignet logicman2))
                    (aignet-bfr-eval bfr
                                     (fgl::alist-to-bitarr num-ins env nil) nil
                                     (fgl::logicman->aignet logicman))))
    :hints(("Goal" :in-theory (e/d (aignet-bfr-eval-is-bfr-eval)
                                   (aignet-bfr-eval))))))

#!fgl
(defthm bfr-litarr-correct-p-of-repeat-nil
  (bfr-litarr-correct-p (acl2::repeat n nil) env litarr logicman2 logicman)
  :hints(("Goal" :in-theory (enable bfr-litarr-correct-p acl2::repeat))))

#!fgl
(defthm bfr-litarr-correct-p-of-take
  (implies (bfr-litarr-correct-p bfrs env litarr logicman2 logicman)
           (bfr-litarr-correct-p (take n bfrs) env litarr logicman2 logicman))
  :hints(("Goal" :in-theory (enable bfr-litarr-correct-p take))))


#!fgl
(defthm bfr-litarr-correct-p-of-nthcdr
  (implies (bfr-litarr-correct-p bfrs env litarr logicman2 logicman)
           (bfr-litarr-correct-p (nthcdr n bfrs) env litarr logicman2 logicman))
  :hints(("Goal" :in-theory (enable bfr-litarr-correct-p nthcdr))))

(define aignet-bfr-eval-cube (bfrs invals regvals aignet)
  :verify-guards nil
  (if (atom bfrs)
      t
    (and (aignet-bfr-eval (car bfrs) invals regvals aignet)
         (aignet-bfr-eval-cube (cdr bfrs) invals regvals aignet)))
  ///
  (defthm aignet-bfr-eval-cube-of-append
    (equal (aignet-bfr-eval-cube (append a b) invals regvals aignet)
           (and (aignet-bfr-eval-cube a invals regvals aignet)
                (aignet-bfr-eval-cube b invals regvals aignet))))

  (defthm aignet-bfr-eval-cube-of-cons
    (equal (aignet-bfr-eval-cube (cons a b) invals regvals aignet)
           (and (aignet-bfr-eval a invals regvals aignet)
                (aignet-bfr-eval-cube b invals regvals aignet))))

  (defthm aignet-bfr-eval-cube-of-nil
    (equal (aignet-bfr-eval-cube nil invals regvals aignet) t))

  
  (defthm aignet-bfr-eval-cube-of-bfrlist-map
    (implies (and (fgl::bfr-litarr-correct-p bfrs env litarr logicman2 logicman)
                  (fgl::lbfr-mode-is :aignet logicman)
                  (fgl::lbfr-mode-is :aignet logicman2)
                  (equal num-ins (num-ins (fgl::logicman->aignet logicman)))
                  (equal num-ins (num-ins (fgl::logicman->aignet logicman2))))
             (equal (aignet-bfr-eval-cube (fgl::bfrlist-map bfrs litarr)
                                          (fgl::alist-to-bitarr num-ins env nil) nil
                                          (fgl::logicman->aignet logicman2))
                    (aignet-bfr-eval-cube bfrs
                                          (fgl::alist-to-bitarr num-ins env nil) nil
                                          (fgl::logicman->aignet logicman))))
    :hints(("Goal" :in-theory (enable fgl::bfrlist-map)))))

;; (defthm aignet-pathcond-eval-of-rewind
;;   (implies (aignet-pathcond-eval aignet nbalist invals regvals)
;;            (aignet-pathcond-eval aignet (aignet-pathcond-rewind len nbalist) invals regvals))
;;   :hints(("Goal" :in-theory (enable aignet-pathcond-eval-redef)
;;           :induct (nbalist-ind nbalist)
;;           :expand ((aignet-pathcond-eval aignet nbalist invals regvals)
;;                    (nbalist-stobj-rewind len nbalist)))))

(local (defthm cdr-nth-when-nbalistp
         (implies (and (nbalistp x)
                       (< n (len x))
                       (natp n))
                  (bitp (cdr (nth n x))))
         :rule-classes :type-prescription))

(local (defthm cdar-of-nbalist-fix
         (implies (consp (nbalist-fix x))
                  (bitp (cdar (nbalist-fix x))))
         :rule-classes :type-prescription))

(defthm aignet-pathcond-eval-in-terms-of-nbalist-to-cube
  (equal (aignet-pathcond-eval aignet nbalist invals regvals)
         (aignet-bfr-eval-cube (nbalist-to-cube nbalist) invals regvals aignet))
  :hints(("Goal" :in-theory (enable nbalist-to-cube
                                    aignet-bfr-eval-cube
                                    aignet-bfr-eval
                                    aignet-pathcond-eval-redef
                                    lit-eval)
          :induct (nbalist-to-cube nbalist))))

(local (defthm nthcdr-when-zp
         (implies (zp n)
                  (equal (nthcdr n x) x))
         :hints(("Goal" :in-theory (enable nthcdr)))))

(defthm nbalist-to-cube-of-nbalist-stobj-rewind
  (equal (nbalist-to-cube (nbalist-stobj-rewind len nbalist))
         (nthcdr (- (len (nbalist-fix nbalist)) (nfix len)) (nbalist-to-cube nbalist)))
  :hints(("Goal" :in-theory (enable nbalist-stobj-rewind nbalist-to-cube nthcdr))))

(local (defthm natp-car-nth-of-nbalist-type
         (implies (and (nbalistp x)
                       (< n (len x))
                       (natp n))
                  (natp (car (nth n x))))
         :rule-classes :type-prescription))

(local (defthm hons-assoc-equal-of-nth-when-nbalistp
         (implies (and (nbalistp x)
                       (< (nfix n) (len x)))
                  (equal (hons-assoc-equal (car (nth n x)) x)
                         (nth n x)))
         :hints(("Goal" :in-theory (enable nth nbalistp)))))

(local (defthm nbalist-lookup-of-nth-n
         (implies (and (nbalistp x)
                       (< (nfix n) (len x)))
                  (equal (nbalist-lookup (car (nth n x)) x)
                         (cdr (nth n x))))
         :hints(("Goal" :in-theory (enable nbalist-lookup nbalistp nth hons-assoc-equal)
                 :induct (nth n x)))))

(local (defthm nbalist-lookup-of-nth-n-fix
         (implies (and (< (nfix n) (len (nbalist-fix x))))
                  (equal (nbalist-lookup (car (nth n (nbalist-fix x))) x)
                         (cdr (nth n (nbalist-fix x)))))
         :hints(("Goal" :use ((:instance nbalist-lookup-of-nth-n
                               (x (nbalist-fix x))))
                 :in-theory (disable nbalist-lookup-of-nth-n)))))



(local (defthm nthcdr-under-iff-when-true-listp
         (implies (true-listp x)
                  (iff (nthcdr n x)
                       (< (nfix n) (len x))))))

(local (include-book "std/lists/nthcdr" :dir :system))
(local (include-book "std/lists/take" :dir :system))
(local (include-book "std/lists/nth" :dir :system))


;; (local (defthm nth-of-nbalist-to-cube
;;          (equal (nth n (nbalist-to-cube nbalist))
;;                 (and (< (nfix n) (len (nbalist-fix nbalist)))
;;                      (make-lit (car (nth n (nbalist-fix nbalist)))
;;                                (b-not (cdr (nth n (nbalist-fix nbalist)))))))
;;          :hints(("Goal" :in-theory (enable nbalist-to-cube
;;                                            nth)))))


(define aignet-pathcond-collect-lits ((n natp)
                                      (max natp)
                                      aignet-pathcond)
  :guard (and (<= n max)
              (<= max (aignet-pathcond-len aignet-pathcond)))
  :measure (nfix (- (nfix max) (nfix n)))
  (if (mbe :logic (<= (nfix max) (nfix n))
           :exec (int= max n))
      nil
    (cons (b* ((id (aignet-pathcond-nthkey n aignet-pathcond)))
            (satlink::make-lit id (b-not (aignet-pathcond-lookup id aignet-pathcond))))
          (aignet-pathcond-collect-lits (1+ (lnfix n)) max aignet-pathcond)))
  ///
  (local (defthm equal-of-cons
           (equal (equal (cons a b) c)
                  (and (Consp c) (equal a (car c)) (equal b (cdr c))))))

  (defthm aignet-pathcond-collect-lits-redef
    (implies (<= (nfix max) (len (nbalist-fix aignet-pathcond)))
             (equal (aignet-pathcond-collect-lits n max aignet-pathcond)
                    (nthcdr n (take max (nbalist-to-cube aignet-pathcond)))))
    :hints(("Goal" :in-theory (enable nbalist-to-cube nthcdr take)))))

(local (defthm natp-caar-of-nbalist-fix
         (implies (consp (nbalist-fix x))
                  (natp (caar (nbalist-fix x))))
         :rule-classes :type-prescription))

(local (defthm cdar-of-nbalist-fix-when-caar-zero
         (implies (equal (caar (nbalist-fix x)) 0)
                  (equal (cdar (nbalist-fix x)) 1))
         :hints(("Goal" :in-theory (enable nbalist-fix)))))

(defthm bounded-pathcond-p-implies-bfr-listp-of-nbalist-to-cube
  (implies (and (bounded-pathcond-p nbalist bound)
                (equal (fgl::bfrstate->bound bfrstate) (1- (nfix bound)))
                (equal (fgl::bfrstate->mode bfrstate) (fgl::bfrmode :aignet)))
           (fgl::bfr-listp (remove 0 (nbalist-to-cube nbalist)) bfrstate))
  :hints(("Goal" :in-theory (enable bounded-pathcond-p-redef
                                    nbalist-to-cube
                                    fgl::bfr-p
                                    satlink::equal-of-make-lit))))



                                 
(defthm aignet-pathcond-eval-when-nbalist-lookup-0
  (implies (nbalist-lookup 0 nbalist)
           (equal (aignet-pathcond-eval aignet nbalist invals regvals) nil))
  :hints(("Goal" :in-theory (enable nbalist-lookup 
                                    nbalist-to-cube
                                    aignet-bfr-eval-cube
                                    aignet-bfr-eval
                                    hons-assoc-equal))))
    

(define aignet-pathcond-assume-list (bfrs aignet aignet-pathcond)
  :returns (mv contra new-aignet-pathcond)
  :verify-guards nil
  (b* ((aignet-pathcond (mbe :logic (non-exec (nbalist-fix aignet-pathcond))
                             :exec aignet-pathcond))
       ((when (atom bfrs))
        (mv nil aignet-pathcond))
       (bfr (car bfrs))
       ((when (or (eql bfr 0)
                  (eq bfr nil)))
        (b* ((aignet-pathcond (aignet-pathcond-falsify aignet-pathcond)))
          (mv t aignet-pathcond)))
       ((when (eq bfr t))
        (aignet-pathcond-assume-list (cdr bfrs) aignet aignet-pathcond))
       ((mv contra aignet-pathcond) (aignet-pathcond-assume bfr aignet aignet-pathcond))
       ((when contra)
        (b* ((aignet-pathcond (aignet-pathcond-falsify aignet-pathcond)))
          (mv t aignet-pathcond))))
    (aignet-pathcond-assume-list (cdr bfrs) aignet aignet-pathcond))
  ///
  (defret eval-of-<fn>
    (equal (aignet-pathcond-eval aignet new-aignet-pathcond invals regvals)
           (and (aignet-bfr-eval-cube bfrs invals regvals aignet)
                (aignet-pathcond-eval aignet aignet-pathcond invals regvals)))
    :hints(("Goal" :in-theory (e/d (aignet-bfr-eval-cube
                                    aignet-bfr-eval)
                                   (aignet-pathcond-eval-in-terms-of-nbalist-to-cube))
            :induct <call>
            :expand ((aignet-bfr-eval-cube bfrs invals regvals aignet)))))

  (defret cube-eval-of-<fn>
    (equal (aignet-bfr-eval-cube (nbalist-to-cube new-aignet-pathcond) invals regvals aignet)
           (and (aignet-bfr-eval-cube bfrs invals regvals aignet)
                (aignet-pathcond-eval aignet aignet-pathcond invals regvals)))
    :hints (("goal" :use eval-of-<fn>
             :in-theory (disable eval-of-<fn>))))

  (defret <fn>-not-contra
    (implies (and (aignet-bfr-eval-cube bfrs invals regvals aignet)
                  (aignet-pathcond-eval aignet aignet-pathcond invals regvals))
             (not contra))
    :hints(("Goal" :in-theory (e/d (aignet-bfr-eval-cube
                                    aignet-bfr-eval)
                                   (aignet-pathcond-eval-in-terms-of-nbalist-to-cube))
            :induct <call>
            :expand ((aignet-bfr-eval-cube bfrs invals regvals aignet)))))

  (defret nbalist-extension-of-<fn>
    (nbalist-extension-p new-aignet-pathcond aignet-pathcond)
    :hints (("goal" :induct t)
            (and stable-under-simplificationp
                 '(:in-theory (enable nbalist-extension-p)))))

  (defret bounded-pathcond-p-of-<fn>
    (implies (and (bounded-pathcond-p aignet-pathcond (+ 1 (fanin-count aignet)))
                  (fgl::bfr-listp bfrs (fgl::bfrstate (fgl::bfrmode :aignet)
                                                      (fanin-count aignet))))
             (bounded-pathcond-p new-aignet-pathcond (+ 1 (fanin-count aignet))))
    :hints(("Goal" :in-theory (enable fgl::bfr-listp fgl::bfr-p aignet-idp)
            :expand ((:free (bfrstate) (fgl::bfr-listp bfrs bfrstate)))
            :induct t)
           (and stable-under-simplificationp
                '(:in-theory (enable bounded-pathcond-p-redef aignet-idp))))))


(define aignet-pathcond-assume-mapped-lits (bfrs
                                            litarr
                                            aignet
                                            aignet-pathcond)
  :guard (and (< 0 (lits-length litarr))
              (fgl::bfr-listp (ec-call (remove-equal 0 bfrs)) (fgl::bfrstate (fgl::bfrmode :aignet) (1- (lits-length litarr))))
              (fgl::bfr-litarr-p (ec-call (remove-equal 0 bfrs)) litarr (1- (num-fanins aignet))))
  :guard-hints (("goal" ;; :expand ((:free (fanins) (fgl::bfr-litarr-p bfrs litarr fanins)))
                 :in-theory (enable fgl::bfr-p fgl::bfr-litarr-p)))
  :returns (mv contra new-aignet-pathcond)
  :guard-debug t
  (b* ((aignet-pathcond (mbe :logic (non-exec (nbalist-fix aignet-pathcond))
                             :exec aignet-pathcond))
       ((when (atom bfrs))
        (mv nil aignet-pathcond))
       (bfr (car bfrs))
       (new-bfr (if (eql 0 bfr) nil (fgl::bfr-map (car bfrs) litarr)))
       ((when (eq new-bfr nil))
        (b* ((aignet-pathcond (aignet-pathcond-falsify aignet-pathcond)))
          (mv t aignet-pathcond)))
       ((when (eq new-bfr t))
        (aignet-pathcond-assume-mapped-lits (cdr bfrs) litarr aignet aignet-pathcond))
       ((mv contra aignet-pathcond) (aignet-pathcond-assume new-bfr aignet aignet-pathcond))
       ((when contra)
        (b* ((aignet-pathcond (aignet-pathcond-falsify aignet-pathcond)))
          (mv t aignet-pathcond))))
    (aignet-pathcond-assume-mapped-lits (cdr bfrs) litarr aignet aignet-pathcond))
  ///
  (defret aignet-pathcond-assume-mapped-lits-redef
    (equal (aignet-pathcond-assume-mapped-lits bfrs litarr aignet aignet-pathcond)
           (aignet-pathcond-assume-list (fgl::bfrlist-map bfrs litarr) aignet aignet-pathcond))
    :hints(("Goal" :in-theory (enable fgl::bfrlist-map fgl::bfr-map
                                      aignet-pathcond-assume-list)
            :induct <call>)
           (and stable-under-simplificationp
                '(:expand ((fgl::bfrlist-map bfrs litarr)))))))


(defthm aignet-pathcond-rewind-in-terms-of-nthcdr
  (equal (nbalist-stobj-rewind len aignet-pathcond)
         (nthcdr (- (len (nbalist-fix aignet-pathcond)) (nfix len)) (nbalist-fix aignet-pathcond)))
  :hints(("Goal" :in-theory (enable nbalist-stobj-rewind))))
    
(define aignet-pathcond-eval-at-checkpoints ((checkpoints nat-listp)
                                             nbalist
                                             invals regvals aignet)
  :verify-guards nil
  :non-executable t
  :measure (len checkpoints)
  :ruler-extenders :all
  (cons (aignet-pathcond-eval aignet nbalist invals regvals)
        (if (atom checkpoints)
            nil
          (aignet-pathcond-eval-at-checkpoints
           (cdr checkpoints)
           (nbalist-stobj-rewind (if (<= (lnfix (car checkpoints)) (len (nbalist-fix nbalist)))
                                     (car checkpoints)
                                   0)
                                 nbalist)
           invals regvals aignet)))
  ///
  (fty::deffixcong nbalist-equiv equal (aignet-pathcond-eval-at-checkpoints
                                        checkpoints nbalist invals regvals aignet)
    nbalist)

  (local (in-theory (disable (:d aignet-pathcond-eval-at-checkpoints)
                             acl2-number-listp
                             rationalp-implies-acl2-numberp
                             rational-listp
                             nth
                             acl2::nth-when-too-large-cheap nthcdr acl2::nthcdr-when-zp)))

  (fty::deffixequiv aignet-pathcond-eval-at-checkpoints :args (checkpoints))

  (local (defthm len-equal-0
           (equal (equal (len x) 0)
                  (not (consp x)))))

  (defthmd logicman-pathcond-eval-checkpoints-is-aignet-pathcond-eval-at-checkpoints
    (implies (and (fgl::lbfr-mode-is :aignet logicman)
                  (fgl::pathcond-enabledp pathcond)
                  (equal num-ins (num-ins (fgl::logicman->aignet logicman))))
             (equal (fgl::logicman-pathcond-eval-checkpoints env pathcond logicman)
                    (cdr (aignet-pathcond-eval-at-checkpoints
                          (fgl::pathcond-checkpoint-ptrs pathcond)
                          (fgl::pathcond-aignet pathcond)
                          (fgl::alist-to-bitarr num-ins env nil) nil
                          (fgl::logicman->aignet logicman)))))
    :hints(("Goal" :in-theory (e/d ((:i fgl::logicman-pathcond-eval-checkpoints)
                                    fgl::pathcond-rewind-stack-len
                                    fgl::pathcond-rewind
                                    fgl::logicman-pathcond-eval)
                                   (FGL::LOGICMAN-PATHCOND-EVAL-CHECKPOINTS-OF-PATHCOND-REWIND
                                    aignet-pathcond-eval-at-checkpoints))
            :induct (fgl::logicman-pathcond-eval-checkpoints env pathcond logicman)
            :expand ((fgl::logicman-pathcond-eval-checkpoints env pathcond logicman)
                     (:free (nbalist invals regvals aignet)
                      (aignet-pathcond-eval-at-checkpoints
                       (nth 4 pathcond) nbalist invals regvals aignet))
                     (:free (nbalist invals regvals aignet)
                      (aignet-pathcond-eval-at-checkpoints
                       (cdr (nth 4 pathcond))
                       nbalist invals regvals aignet))))))

  (defthmd logicman-pathcond-eval-checkpoints!-is-aignet-pathcond-eval-at-checkpoints
    (implies (and (fgl::lbfr-mode-is :aignet logicman)
                  (equal num-ins (num-ins (fgl::logicman->aignet logicman))))
             (equal (fgl::logicman-pathcond-eval-checkpoints! env pathcond logicman)
                    (aignet-pathcond-eval-at-checkpoints
                     (fgl::pathcond-checkpoint-ptrs pathcond)
                     (fgl::pathcond-aignet pathcond)
                     (fgl::alist-to-bitarr num-ins env nil) nil
                     (fgl::logicman->aignet logicman))))
    :hints(("Goal" :expand ((fgl::logicman-pathcond-eval-checkpoints! env pathcond logicman)
                            (:free (nbalist invals regvals aignet)
                             (aignet-pathcond-eval-at-checkpoints
                              (nth 4 pathcond) nbalist invals regvals aignet)))
            :in-theory (enable logicman-pathcond-eval-checkpoints-is-aignet-pathcond-eval-at-checkpoints
                               fgl::logicman-pathcond-eval)))))

(defthm bfr-litarr-p-of-nthcdr
  (implies (fgl::bfr-litarr-p x litarr bound)
           (fgl::bfr-litarr-p (nthcdr n x) litarr bound))
  :hints(("Goal" :in-theory (enable fgl::bfr-litarr-p))))

(defthm bfr-litarr-p-of-repeat-nil
  (fgl::bfr-litarr-p (acl2::repeat n nil) litarr bound)
  :hints(("Goal" :in-theory (enable fgl::bfr-litarr-p
                                    acl2::repeat))))

(defthm bfr-litarr-p-of-take
  (implies (fgl::bfr-litarr-p x litarr bound)
           (fgl::bfr-litarr-p (take n x) litarr bound))
  :hints(("Goal" :in-theory (enable fgl::bfr-litarr-p))))

(defthm bounded-pathcond-p-nil
  (bounded-pathcond-p nil x)
  :hints(("Goal" :in-theory (enable bounded-pathcond-p-redef))))

(defthm bounded-pathcond-p-of-nthcdr
  (implies (and (bounded-pathcond-p x bound)
                (nbalistp x))
           (bounded-pathcond-p (nthcdr n x) bound))
  :hints(("Goal" :in-theory (enable bounded-pathcond-p-redef)
          :induct (nthcdr n x))))

(defthm nbalist-to-cube-of-nthcdr
  (implies (nbalistp x)
           (equal (nbalist-to-cube (nthcdr n x))
                  (nthcdr n (nbalist-to-cube x))))
  :hints(("Goal" :in-theory (enable nbalist-to-cube))))


(def-updater-independence-thm nthcdr-of-nbalist-extension
  (implies (and (nbalist-extension-p new old)
                (equal n (- (len new) (len (nbalist-fix old))))
                (nbalistp new))
           (equal (nthcdr n new)
                  (nbalist-fix old)))
  :hints(("Goal" :in-theory (enable nbalist-extension-p))))

(def-updater-independence-thm nthcdr-of-nbalist-extension-fix
  (implies (and (nbalist-extension-p new old)
                (equal n (- (len (nbalist-fix new)) (len (nbalist-fix old)))))
           (equal (nthcdr n (nbalist-fix new))
                  (nbalist-fix old)))
  :hints (("goal" :use ((:instance nthcdr-of-nbalist-extension (new (nbalist-fix new))))
           :in-theory (disable nthcdr-of-nbalist-extension))))
           


(local
 #!fgl
 (defthm bfr-listp-remove-of-take
   (implies (bfr-listp (remove 0 x))
            (bfr-listp (remove 0 (take n x))))
   :hints(("Goal" :in-theory (e/d (bfr-listp)
                                  (bfr-listp$-when-subsetp-equal
                                   bfr-p-when-member-equal-of-bfr-listp$))))))

(local (defthm remove-0-of-repeat-nil
         (equal (remove 0 (acl2::repeat n nil))
                (acl2::repeat n nil))
         :hints(("Goal" :in-theory (enable acl2::repeat)))))
                

(local
 #!fgl
 (defthm bfr-litarr-p-remove-of-take
   (implies (bfr-litarr-p (remove 0 x) litarr bound)
            (bfr-litarr-p (remove 0 (take n x)) litarr bound))
   :hints(("Goal" :in-theory (e/d (bfr-litarr-p))))))

(local
 #!fgl
 (defthm bfr-litarr-p-remove-of-nthcdr
   (implies (bfr-litarr-p (remove 0 x) litarr bound)
            (bfr-litarr-p (remove 0 (nthcdr n x)) litarr bound))
   :hints(("Goal" :in-theory (e/d (bfr-litarr-p))))))

              
(define aignet-pathcond-map-bfrs ((checkpoints nat-listp)
                                  aignet-pathcond
                                  litarr
                                  aignet)
  :guard (and (< 0 (lits-length litarr))
              (non-exec (ec-call (bounded-pathcond-p aignet-pathcond (lits-length litarr))))
              (non-exec (ec-call (fgl::bfr-litarr-p (ec-call
                                                     (remove-equal 0 (ec-call (nbalist-to-cube aignet-pathcond))))
                                                    litarr
                                                    (1- (num-fanins aignet))))))
  :guard-debug t
  :returns (mv contra (new-checkpoints nat-listp) new-aignet-pathcond)
  :measure (len checkpoints)
  :ruler-extenders :all
  (b* ((len (aignet-pathcond-len aignet-pathcond))
       (checkpoint (if (or (atom checkpoints)
                           (< len (lnfix (car checkpoints))))
                       0
                     (lnfix (car checkpoints))))
       (nlits (- len checkpoint))
       (bfrs (aignet-pathcond-collect-lits 0 nlits aignet-pathcond))
       (aignet-pathcond (aignet-pathcond-rewind checkpoint aignet-pathcond))
       ((mv contra1 new-checkpoints aignet-pathcond)
        (if (atom checkpoints)
            (mv nil nil aignet-pathcond)
          (aignet-pathcond-map-bfrs (cdr checkpoints) aignet-pathcond litarr aignet)))
       (new-len (aignet-pathcond-len aignet-pathcond))
       ((mv contra2 aignet-pathcond)
        (aignet-pathcond-assume-mapped-lits bfrs litarr aignet aignet-pathcond)))
    (mv (or contra1 contra2)
        (if (atom checkpoints)
            nil
          (cons new-len new-checkpoints))
        aignet-pathcond))
  ///
  (defret new-checkpoints-len-of-<fn>
    (equal (len new-checkpoints)
           (len checkpoints)))

  (local
   (defthmd aignet-pathcond-eval-checkpoints-equal-implies-aignet-bfr-eval-cube-equal
     (implies (equal (aignet-pathcond-eval-at-checkpoints chp1 pc1 invals regvals aig1)
                     (aignet-pathcond-eval-at-checkpoints chp2 pc2 invals regvals aig2))
              (equal (aignet-bfr-eval-cube (nbalist-to-cube pc1) invals regvals aig1)
                     (aignet-bfr-eval-cube (nbalist-to-cube pc2) invals regvals aig2)))
     :hints (("goal" :expand ((aignet-pathcond-eval-at-checkpoints chp1 pc1 invals regvals aig1)
                              (aignet-pathcond-eval-at-checkpoints chp2 pc2 invals regvals aig2))))))

  (local
   (defret aignet-pathcond-eval-at-checkpoints-equal-of-aignet-pathcond-map-bfrs
     (implies (equal (aignet-pathcond-eval-at-checkpoints
                      new-checkpoints new-aignet-pathcond invals regvals aignet)
                     (aignet-pathcond-eval-at-checkpoints
                      checkpoints aignet-pathcond invals regvals old-aignet))
              (equal (aignet-bfr-eval-cube (nbalist-to-cube new-aignet-pathcond) invals regvals aignet)
                     (aignet-bfr-eval-cube (nbalist-to-cube aignet-pathcond) invals regvals old-aignet)))
     :hints (("goal" :expand ((aignet-pathcond-eval-at-checkpoints
                               new-checkpoints new-aignet-pathcond invals regvals aignet)
                              (aignet-pathcond-eval-at-checkpoints
                               checkpoints aignet-pathcond invals regvals old-aignet))
              :in-theory (disable <fn>)))))
  (local
   (defthm aignet-bfr-eval-cube-of-bfrlist-map-take
     (implies (and (fgl::bfr-litarr-correct-p bfrs env litarr logicman2 logicman)
                   (fgl::lbfr-mode-is :aignet logicman)
                   (fgl::lbfr-mode-is :aignet logicman2)
                   (equal num-ins (num-ins (fgl::logicman->aignet logicman)))
                   (equal num-ins (num-ins (fgl::logicman->aignet logicman2))))
              (equal (aignet-bfr-eval-cube (fgl::bfrlist-map (take n bfrs) litarr)
                                           (fgl::alist-to-bitarr num-ins env nil) nil
                                           (fgl::logicman->aignet logicman2))
                     (aignet-bfr-eval-cube (take n bfrs)
                                           (fgl::alist-to-bitarr num-ins env nil) nil
                                           (fgl::logicman->aignet logicman))))
     :hints (("goal" :use ((:instance aignet-bfr-eval-cube-of-bfrlist-map
                            (bfrs (take n bfrs))))
              :in-theory (disable aignet-bfr-eval-cube-of-bfrlist-map)))))

  (local
   (defthm aignet-bfr-eval-cube-of-bfrlist-map-nthcdr
     (implies (and (fgl::bfr-litarr-correct-p bfrs env litarr logicman2 logicman)
                   (fgl::lbfr-mode-is :aignet logicman)
                   (fgl::lbfr-mode-is :aignet logicman2)
                   (equal num-ins (num-ins (fgl::logicman->aignet logicman)))
                   (equal num-ins (num-ins (fgl::logicman->aignet logicman2))))
              (equal (aignet-bfr-eval-cube (fgl::bfrlist-map (nthcdr n bfrs) litarr)
                                           (fgl::alist-to-bitarr num-ins env nil) nil
                                           (fgl::logicman->aignet logicman2))
                     (aignet-bfr-eval-cube (nthcdr n bfrs)
                                           (fgl::alist-to-bitarr num-ins env nil) nil
                                           (fgl::logicman->aignet logicman))))
     :hints (("goal" :use ((:instance aignet-bfr-eval-cube-of-bfrlist-map
                            (bfrs (nthcdr n bfrs))))
              :in-theory (disable aignet-bfr-eval-cube-of-bfrlist-map)))))


  (local (defthm aignet-bfr-eval-cube-of-nthcdr
           (implies (and (aignet-bfr-eval-cube (take n cube) invals regvals aignet)
                         (<= (nfix n) (len cube)))
                    (equal (aignet-bfr-eval-cube (nthcdr n cube) invals regvals aignet)
                           (aignet-bfr-eval-cube cube invals regvals aignet)))
           :hints(("Goal" :in-theory (enable aignet-bfr-eval-cube)))))

  (local (defthm aignet-bfr-eval-cube-of-nthcdr-when-orig
           (implies (aignet-bfr-eval-cube cube invals regvals aignet)
                    (aignet-bfr-eval-cube (nthcdr n cube) invals regvals aignet))
           :hints(("Goal" :in-theory (enable aignet-bfr-eval-cube)))))

  (local (defthm aignet-bfr-eval-cube-of-take-when-orig
           (implies (and (aignet-bfr-eval-cube cube invals regvals aignet)
                         (<= (nfix n) (len cube)))
                    (aignet-bfr-eval-cube (take n cube) invals regvals aignet))
           :hints(("Goal" :in-theory (enable aignet-bfr-eval-cube)))))
  (local (defthm nthcdr-of-len-when-true-listp
           (implies (and (equal (nfix len) (len x))
                         (true-listp x))
                    (equal (nthcdr len x) nil))))

  (defret aignet-pathcond-eval-at-checkpoints-of-aignet-pathcond-map-bfrs
    :pre-bind ((aignet (fgl::logicman->aignet logicman2)))
    (implies (and ;; (not contra)
                  (fgl::bfr-litarr-correct-p (nbalist-to-cube aignet-pathcond)
                                             env litarr logicman2 logicman)
                  (fgl::lbfr-mode-is :aignet logicman)
                  (fgl::lbfr-mode-is :aignet logicman2)
                  (equal num-ins (num-ins (fgl::logicman->aignet logicman)))
                  (equal num-ins (num-ins (fgl::logicman->aignet logicman2))))
             (equal (aignet-pathcond-eval-at-checkpoints new-checkpoints new-aignet-pathcond
                                                         (fgl::alist-to-bitarr num-ins env nil) nil aignet)
                    (aignet-pathcond-eval-at-checkpoints checkpoints aignet-pathcond
                                                         (fgl::alist-to-bitarr num-ins env nil) nil
                                                         (fgl::logicman->aignet logicman))))
    :hints(("Goal" ;; :in-theory (enable aignet-pathcond-eval-at-checkpoints)
            :induct <call>
            :in-theory (disable (:d <fn>))
            :expand ((:free (aignet) <call>)
                     (:free (a b invals regvals pathcond aignet)
                      (aignet-pathcond-eval-at-checkpoints
                       (cons a b) pathcond invals regvals aignet))
                     (:free (invals regvals pathcond aignet)
                      (aignet-pathcond-eval-at-checkpoints
                       nil pathcond invals regvals aignet))
                     (:free (pathcond invals regvals aignet)
                      (aignet-pathcond-eval-at-checkpoints
                       checkpoints pathcond invals regvals aignet))))))

  (defret aignet-pathcond-eval-of-aignet-pathcond-map-bfrs
    :pre-bind ((aignet (fgl::logicman->aignet logicman2)))
    (implies (and ;; (not contra)
                  (fgl::bfr-litarr-correct-p (nbalist-to-cube aignet-pathcond)
                                             env litarr logicman2 logicman)
                  (fgl::lbfr-mode-is :aignet logicman)
                  (fgl::lbfr-mode-is :aignet logicman2)
                  (equal num-ins (num-ins (fgl::logicman->aignet logicman)))
                  (equal num-ins (num-ins (fgl::logicman->aignet logicman2))))
             (equal (aignet-bfr-eval-cube (nbalist-to-cube new-aignet-pathcond)
                                          (fgl::alist-to-bitarr num-ins env nil) nil aignet)
                    (aignet-bfr-eval-cube (nbalist-to-cube aignet-pathcond)
                                          (fgl::alist-to-bitarr num-ins env nil) nil
                                          (fgl::logicman->aignet logicman))))
    :hints(("Goal" :use ((:instance aignet-pathcond-eval-at-checkpoints-of-aignet-pathcond-map-bfrs))
            :in-theory (disable aignet-pathcond-eval-at-checkpoints-of-aignet-pathcond-map-bfrs
                                aignet-pathcond-map-bfrs))))

  (defret bounded-pathcond-p-of-<fn>
    (implies (fgl::bfr-litarr-p (nbalist-to-cube aignet-pathcond)
                                litarr
                                (fanin-count aignet))
             (bounded-pathcond-p new-aignet-pathcond (+ 1 (fanin-count aignet)))))

  (local (defthm aignet-pathcond-assume-list-not-contra-of-bfrlist-map
           (implies (and (aignet-bfr-eval-cube some-bfrs
                                               (fgl::alist-to-bitarr num-ins env nil) nil
                                               (fgl::logicman->aignet logicman))
                         (fgl::lbfr-mode-is :aignet logicman)
                         (fgl::lbfr-mode-is :aignet logicman2)
                         (fgl::bfr-litarr-correct-p bfrs env litarr logicman2 logicman)
                         ;; (fgl::bfr-litarr-correct-p (nbalist-to-cube aignet-pathcond) env litarr logicman2 logicman)
                         (aignet-bfr-eval-cube bfrs
                                               (fgl::alist-to-bitarr num-ins env nil) nil
                                               (fgl::logicman->aignet logicman))
                         (equal num-ins (num-ins (fgl::logicman->aignet logicman)))
                         (equal num-ins (num-ins (fgl::logicman->aignet logicman2)))
                         (aignet-pathcond-eval (fgl::logicman->aignet logicman2)
                                               aignet-pathcond
                                               (fgl::alist-to-bitarr num-ins env nil) nil))
                    (not (mv-nth 0 (aignet-pathcond-assume-list
                                    (fgl::bfrlist-map bfrs litarr)
                                    (fgl::logicman->aignet logicman2)
                                    aignet-pathcond))))
           :hints (("goal" :use ((:instance aignet-pathcond-assume-list-not-contra
                                  (aignet (fgl::logicman->aignet logicman2))
                                  (bfrs (fgl::bfrlist-map bfrs litarr))
                                  (invals (fgl::alist-to-bitarr num-ins env nil))
                                  (regvals nil)))
                    :in-theory (disable aignet-pathcond-assume-list-not-contra)))))

  (local
   (defret aignet-pathcond-eval-of-aignet-pathcond-map-bfrs-bind
     :pre-bind ((aignet (fgl::logicman->aignet logicman2)))
     (implies (and (not contra)
                   (fgl::bfr-litarr-correct-p some-bfrs
                                              env litarr logicman2 logicman)
                   (fgl::bfr-litarr-correct-p (nbalist-to-cube aignet-pathcond)
                                              env litarr logicman2 logicman)
                   (fgl::lbfr-mode-is :aignet logicman)
                   (fgl::lbfr-mode-is :aignet logicman2)
                   (equal num-ins (num-ins (fgl::logicman->aignet logicman)))
                   (equal num-ins (num-ins (fgl::logicman->aignet logicman2))))
              (equal (aignet-bfr-eval-cube (nbalist-to-cube new-aignet-pathcond)
                                           (fgl::alist-to-bitarr num-ins env nil) nil aignet)
                     (aignet-bfr-eval-cube (nbalist-to-cube aignet-pathcond)
                                           (fgl::alist-to-bitarr num-ins env nil) nil
                                           (fgl::logicman->aignet logicman))))
     :hints(("Goal" :use ((:instance aignet-pathcond-eval-at-checkpoints-of-aignet-pathcond-map-bfrs))
             :in-theory (disable aignet-pathcond-eval-at-checkpoints-of-aignet-pathcond-map-bfrs
                                 aignet-pathcond-map-bfrs)))))

  (local (include-book "tools/trivial-ancestors-check" :dir :system))
  (local (acl2::use-trivial-ancestors-check))

  (defret contra-of-<fn>
    :pre-bind ((aignet (fgl::logicman->aignet logicman2)))
    (implies (and (fgl::bfr-litarr-correct-p (nbalist-to-cube aignet-pathcond)
                                             env litarr logicman2 logicman)
                  (fgl::lbfr-mode-is :aignet logicman)
                  (fgl::lbfr-mode-is :aignet logicman2)
                  (equal num-ins (num-ins (fgl::logicman->aignet logicman)))
                  (equal num-ins (num-ins (fgl::logicman->aignet logicman2)))
                  (aignet-pathcond-eval (fgl::logicman->aignet logicman)
                                        aignet-pathcond
                                        (fgl::alist-to-bitarr num-ins env nil) nil))
             (not contra))
    :hints (("goal" :induct <call>))))




#!fgl
(define logicman-pathcond-map-bfrs (pathcond
                                    litarr
                                    logicman2)
  :guard (and (< 0 (lits-length litarr))
              (ec-call (bfr-pathcond-p-fn pathcond (bfrstate (bfrmode :aignet) (1- (lits-length litarr)))))
              (lbfr-mode-is :aignet logicman2)
              (non-exec (ec-call (bfr-litarr-p (ec-call
                                                (remove-equal 0 (ec-call (aignet::nbalist-to-cube
                                                                          (pathcond-aignet pathcond)))))
                                               litarr
                                               (bfrstate->bound (logicman->bfrstate logicman2))))))
  :guard-hints (("goal" :in-theory (enable bfr-pathcond-p)))
  :returns (mv contra new-pathcond)
  (b* ((checkpoints (pathcond-checkpoint-ptrs pathcond)))
    (stobj-let ((aignet-pathcond (pathcond-aignet pathcond)))
               (contra checkpoints aignet-pathcond)
               (stobj-let ((aignet (logicman->aignet logicman2)))
                          (contra checkpoints aignet-pathcond)
                          (aignet::aignet-pathcond-map-bfrs
                           checkpoints aignet-pathcond litarr aignet)
                          (mv contra checkpoints aignet-pathcond))
               (b* ((pathcond (update-pathcond-checkpoint-ptrs checkpoints pathcond)))
                 (mv contra pathcond))))
  ///
  (defret logicman-pathcond-eval-checkpoints!-of-<fn>
    (implies (and ;; (not contra)
                  (bfr-litarr-correct-p (aignet::nbalist-to-cube (pathcond-aignet pathcond))
                                        env litarr logicman2 logicman)
                  (lbfr-mode-is :aignet logicman)
                  (lbfr-mode-is :aignet logicman2)
                  (equal (aignet::num-ins (logicman->aignet logicman))
                         (aignet::num-ins (logicman->aignet logicman2))))
             (equal (logicman-pathcond-eval-checkpoints! env new-pathcond logicman2)
                    (logicman-pathcond-eval-checkpoints! env pathcond logicman)))
    :hints(("Goal" :in-theory (enable aignet::logicman-pathcond-eval-checkpoints!-is-aignet-pathcond-eval-at-checkpoints))))

  

  (defret pathcond-enabledp-of-<fn>
    (equal (nth *pathcond-enabledp* new-pathcond)
           (nth *pathcond-enabledp* pathcond)))
  

  (defret logicman-pathcond-eval-of-<fn>
    (implies (and ;; (not contra)
                  (bfr-litarr-correct-p (aignet::nbalist-to-cube (nth *pathcond-aignet* pathcond))
                                        env litarr logicman2 logicman)
                  (lbfr-mode-is :aignet logicman)
                  (lbfr-mode-is :aignet logicman2)
                  (equal (aignet::num-ins (logicman->aignet logicman))
                         (aignet::num-ins (logicman->aignet logicman2))))
             (equal (logicman-pathcond-eval env new-pathcond logicman2)
                    (logicman-pathcond-eval env pathcond logicman)))
    :hints (("goal" :use logicman-pathcond-eval-checkpoints!-of-<fn>
             :expand ((logicman-pathcond-eval-checkpoints! env new-pathcond logicman2)
                      (logicman-pathcond-eval-checkpoints! env pathcond logicman))
             :in-theory (disable logicman-pathcond-eval-checkpoints!-of-<fn>
                                 <fn>))
            (and stable-under-simplificationp
                 '(:cases ((pathcond-enabledp pathcond))))))

  (defret contra-of-<fn>
    (implies (and ;; (not contra)
                  (bfr-litarr-correct-p (aignet::nbalist-to-cube (nth *pathcond-aignet* pathcond))
                                        env litarr logicman2 logicman)
                  (lbfr-mode-is :aignet logicman)
                  (lbfr-mode-is :aignet logicman2)
                  (equal (aignet::num-ins (logicman->aignet logicman))
                         (aignet::num-ins (logicman->aignet logicman2)))
                  (logicman-pathcond-eval env pathcond logicman)
                  (pathcond-enabledp pathcond))
             (not contra))
    :hints(("Goal" :in-theory (enable logicman-pathcond-eval))))

  (defret pathcond-rewind-stack-len-of-<fn>
    (equal (pathcond-rewind-stack-len (bfrmode :aignet) new-pathcond)
           (pathcond-rewind-stack-len (bfrmode :aignet) pathcond))
    :hints(("Goal" :in-theory (enable pathcond-rewind-stack-len))))

  (defret pathcond-rewind-ok-of-<fn>
    (equal (pathcond-rewind-ok (bfrmode :aignet) new-pathcond)
           (pathcond-rewind-ok (bfrmode :aignet) pathcond))
    :hints(("Goal" :in-theory (e/d (pathcond-rewind-ok)
                                   (<fn>)))))

  (defret logicman-pathcond-p-of-<fn>
    (implies (and (fgl::bfr-litarr-p (aignet::nbalist-to-cube (nth *pathcond-aignet* pathcond))
                                     litarr bound)
                  (equal bound (bfrstate->bound (logicman->bfrstate logicman2)))
                  (lbfr-mode-is :aignet logicman2))
             (logicman-pathcond-p new-pathcond logicman2))
    :hints(("Goal" :in-theory (enable bfr-pathcond-p))))

  (defret bounded-pathcond-p-of-<fn>
    (implies (and (fgl::bfr-litarr-p (aignet::nbalist-to-cube (nth *pathcond-aignet* pathcond))
                                     litarr bound)
                  (equal bound (bfrstate->bound (logicman->bfrstate logicman2)))
                  (lbfr-mode-is :aignet logicman2))
             (aignet::bounded-pathcond-p
              (nth *pathcond-aignet* new-pathcond)
              (+ 1 (aignet::fanin-count (logicman->aignet logicman2)))))))


                  
                  
  
  
