; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2014-2015 Centaur Technology
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

(in-package "SV")
(include-book "compose-theory-base")
;; (include-book "rewrite-base")
(local (include-book "std/basic/arith-equivs" :dir :system))
(local (include-book "std/lists/sets" :dir :system))
(local (include-book "alist-thms"))
(local (std::add-default-post-define-hook :fix))



;; (local (defthm svex-lookup-of-cons
;;          (equal (svex-lookup key (cons (cons var val) rest))
;;                 (if (and (svar-p var)
;;                          (equal (svar-fix key) var))
;;                     (svex-fix val)
;;                   (svex-lookup key rest)))
;;          :hints(("Goal" :in-theory (enable svex-lookup)))))



(defcong set-equiv svex-alist-eval-equiv (svex-alist-reduce vars al) 1
  :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))


(local (defthm svex-alist-eval-equiv-of-cons
         (implies (svex-eval-equiv val1 val2)
                  (svex-alist-eval-equiv (cons (cons key val1) rest)
                                         (cons (cons key val2) rest)))
         :hints (("goal" :in-theory (enable svex-alist-eval-equiv
                                            svex-lookup)))
         :rule-classes :congruence))


(defsection netcomp-p-of-cons-compose

  (defthm netcomp-p-of-nil
    (netcomp-p nil network)
    :hints (("goal" :use ((:instance netcomp-p-suff
                           (comp nil) (decomp network)
                           (ordering nil)))
             :in-theory (enable neteval-ordering-compile))))

  (local (defthm svex-lookup-when-eval-equiv-compile
           (implies (and (svex-alist-eval-equiv network
                                                (neteval-ordering-compile order network1))
                         (svex-lookup var network))
                    (svex-eval-equiv (svex-lookup var network)
                                     ;; (svex-compose (svex-lookup var network1)
                                     (neteval-sigordering-compile
                                      (cdr (hons-assoc-equal (svar-fix var) order))
                                      var 0
                                      network1)))))

  

  (local (defthm svex-compose-of-svex-compose
           (svex-eval-equiv (svex-compose (svex-compose x al1) al2)
                            (svex-compose x (append (svex-alist-compose al1 al2) al2)))
           :hints(("Goal" :in-theory (enable svex-eval-equiv)))))

  (defthm netcomp-p-of-singleton-lookup
    (implies (and (netcomp-p lookup-network network1)
                  (svar-p var)
                  (svex-lookup var lookup-network))
             (netcomp-p (list (cons var (svex-lookup var lookup-network)))
                        network1))
    :hints (("goal" :use ((:instance netcomp-p-of-svex-alist-reduce
                           (keys (list var))
                           (x lookup-network)
                           (y network1)))
             :expand ((svex-alist-reduce (list var) lookup-network)
                      (svex-alist-reduce nil lookup-network))
             :in-theory (disable netcomp-p-of-svex-alist-reduce))))

  (local (defthm netcomp-p-of-singleton-compose
           (implies (and (netcomp-p compose-network network1)
                         (netcomp-p lookup-network network1)
                         (svar-p var)
                         (svex-lookup var lookup-network))
                    (netcomp-p (list (cons var (svex-compose (svex-lookup var lookup-network)
                                                             compose-network)))
                               network1))
           :hints (("goal" :use ((:instance netcomp-p-of-singleton-lookup
                                  (lookup-network (svex-alist-compose lookup-network compose-network))))
                    :in-theory (disable netcomp-p-of-singleton-lookup)))))

  (local (defthm cons-bad-pair-under-svex-alist-eval-equiv
           (implies (not (svar-p var))
                    (svex-alist-eval-equiv (cons (cons var val) rest) rest))
           :hints(("Goal" :in-theory (enable svex-alist-eval-equiv svex-lookup)))))

  (defthm netcomp-p-of-cons-lookup
    (implies (and (netcomp-p lookup-network network1)
                  (netcomp-p rest-network network1)
                  (svex-lookup var lookup-network)
                  (svar-equiv var var1))
             (netcomp-p (cons (cons var (svex-lookup var1 lookup-network))
                              rest-network)
                        network1))
    :hints (("goal" :use ((:instance netcomp-p-of-append
                           (x (list (cons var (svex-lookup var lookup-network))))
                           (y rest-network)
                           (network network1)))
             :cases ((svar-p var)))))

  (defthm netcomp-p-of-cons-compose
    (implies (and (netcomp-p compose-network network1)
                  (netcomp-p lookup-network network1)
                  (netcomp-p rest-network network1)
                  (svex-lookup var lookup-network)
                  (svar-equiv var var1))
             (netcomp-p (cons (cons var (svex-compose (svex-lookup var1 lookup-network)
                                                      compose-network))
                              rest-network)
                        network1))
    :hints (("goal" :use ((:instance netcomp-p-of-append
                           (x (list (cons var (svex-compose (svex-lookup var lookup-network)
                                                            compose-network))))
                           (y rest-network)
                           (network network1)))
             :cases ((svar-p var)))))

  (defthm netcomp-p-of-svex-acons-lookup
    (implies (and (netcomp-p lookup-network network1)
                  (netcomp-p rest-network network1)
                  (svex-lookup var lookup-network))
             (netcomp-p (svex-acons var (svex-lookup var lookup-network)
                                    rest-network)
                        network1))
    :hints(("Goal" :in-theory (enable svex-acons))))

  (defthm netcomp-p-of-svex-acons-compose
    (implies (and (netcomp-p compose-network network1)
                  (netcomp-p lookup-network network1)
                  (netcomp-p rest-network network1)
                  (svex-lookup var lookup-network))
             (netcomp-p (svex-acons var (svex-compose (svex-lookup var lookup-network)
                                                      compose-network)
                                    rest-network)
                        network1))
    :hints(("Goal" :in-theory (enable svex-acons)))))


(define svex-network-compose-step ((var svar-p)
                                   (composed-vars svarlist-p)
                                   (network svex-alist-p))
  :guard (svex-lookup var network)
  :returns (new-network svex-alist-p)
  (cons (cons (svar-fix var)
              (svex-compose (svex-lookup var network)
                            (svex-alist-reduce composed-vars network)))
        (svex-alist-fix network))
  ///
  (defret svex-lookup-of-<fn>
    (equal (svex-lookup key new-network)
           (if (equal (svar-fix key) (svar-fix var))
               (svex-compose (svex-lookup var network)
                             (svex-alist-reduce composed-vars network))
             (svex-lookup key network)))
    :hints(("Goal" :in-theory (enable svex-lookup))))

  ;; (defret svex-network-join-envs-of-<fn>
  ;;   (implies (svex-lookup var network)
  ;;            (svex-envs-equivalent (svex-network-join-envs new-network env1 env2)
  ;;                                  (svex-network-join-envs network env1 env2)))
  ;;   :hints(("Goal" :in-theory (enable svex-envs-equivalent))))

  (defcong svex-alist-eval-equiv svex-alist-eval-equiv (svex-network-compose-step var composed-var network) 3
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defcong set-equiv svex-alist-eval-equiv (svex-network-compose-step var composed-var network) 2
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defret netcomp-p-of-<fn>
    (implies (and (netcomp-p network network1)
                  (svex-lookup var network))
             (netcomp-p new-network network1))))





(defthm svex-env-reduce-keys-of-alist-eval
  (svex-envs-equivalent (svex-env-reduce (svex-alist-keys network)
                                         (svex-alist-eval network env))
                        (svex-alist-eval network env))
  :hints(("Goal" :in-theory (enable svex-envs-equivalent))))


(define svex-network-compose-multistep ((vars svarlist-p)
                                        (composed-vars svarlist-p)
                                        (network svex-alist-p))
  :returns (new-network svex-alist-p)
  (append (svex-alist-compose (svex-alist-reduce vars network)
                              (svex-alist-reduce composed-vars network))
          (svex-alist-fix network))
  ///
  (defret svex-lookup-of-<fn>
    (equal (svex-lookup key new-network)
           (if (and (member-equal (svar-fix key) (svarlist-fix vars))
                    (svex-lookup key network))
               (svex-compose (svex-lookup key network)
                             (svex-alist-reduce composed-vars network))
             (svex-lookup key network))))

  ;; (defret svex-network-join-envs-of-<fn>
  ;;   (svex-envs-equivalent (svex-network-join-envs new-network env1 env2)
  ;;                         (svex-network-join-envs network env1 env2))
  ;;   :hints(("Goal" :in-theory (enable svex-envs-equivalent))))


  (defcong svex-alist-eval-equiv svex-alist-eval-equiv
    (svex-network-compose-multistep vars composed-var network) 3
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defcong set-equiv svex-alist-eval-equiv
    (svex-network-compose-multistep vars composed-var network) 2
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defcong set-equiv svex-alist-eval-equiv
    (svex-network-compose-multistep vars composed-var network) 1
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defret netcomp-p-of-<fn>
    (implies (netcomp-p network network1)
             (netcomp-p new-network network))))



(defcong svex-alist-eval-equiv svex-alist-eval-equiv (append x y) 1
  :hints ((and stable-under-simplificationp `(:expand (,(car (last clause)))))))

(defcong svex-alist-eval-equiv svex-alist-eval-equiv (append x y) 2
  :hints ((and stable-under-simplificationp `(:expand (,(car (last clause)))))))


(define svex-network-compose-combostep ((var svar-p)
                                        (update-composed-vars svarlist-p)
                                        (network-composed-vars svarlist-p)
                                        (updates svex-alist-p)
                                        (network svex-alist-p))
  :guard (svex-lookup var network)
  :returns (new-network svex-alist-p)
  (cons (cons (svar-fix var)
              (svex-compose (svex-lookup var network)
                            (append (svex-alist-reduce update-composed-vars updates)
                                    (svex-alist-reduce network-composed-vars network))))
        (svex-alist-fix updates))
  ///
  (defret svex-lookup-of-<fn>
    (equal (svex-lookup key new-network)
           (if (equal (svar-fix key) (svar-fix var))
               (svex-compose (svex-lookup var network)
                             (append (svex-alist-reduce update-composed-vars updates)
                                     (svex-alist-reduce network-composed-vars network)))
             (svex-lookup key updates)))
    :hints(("Goal" :in-theory (enable svex-lookup))))

  ;; (defret svex-network-join-envs-of-<fn>
  ;;   (implies (svex-lookup var network)
  ;;            (svex-envs-equivalent (svex-network-join-envs new-network env1 env2)
  ;;                                  (svex-network-join-envs network env1 env2)))
  ;;   :hints(("Goal" :in-theory (enable svex-envs-equivalent))))

  (defcong svex-alist-eval-equiv svex-alist-eval-equiv
    (svex-network-compose-combostep var update-composed-vars network-composed-vars updates network) 5
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defcong svex-alist-eval-equiv svex-alist-eval-equiv
    (svex-network-compose-combostep var update-composed-vars network-composed-vars updates network) 4
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defcong set-equiv svex-alist-eval-equiv
    (svex-network-compose-combostep var update-composed-vars network-composed-vars updates network) 2
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defcong set-equiv svex-alist-eval-equiv
    (svex-network-compose-combostep var update-composed-vars network-composed-vars updates network) 3
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defret netcomp-p-of-<fn>
    (implies (and (netcomp-p updates network1)
                  (netcomp-p network network1)
                  (svex-lookup var network))
             (netcomp-p new-network network1))))

