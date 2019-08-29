; SVL - Listener-based Hierachical Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2019 Centaur Technology
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
; Original author: Mertcan Temel <mert@utexas.edu>


;; Opener rules for functions defined in svl.lisp

(in-package "SVL")

(include-book "svl")

(defun hons-get-wrapper (key alist)
  (hons-get  key alist))

(in-theory (enable (:e hons-get)
                   (:e fast-alist-free)
                   (:e hons-acons)))

(in-theory (enable (:e svl-run-add-to-queue)))

(defun start-env-wrapper (names vals)
  (start-env names vals))

(defun initialize-wires-wrapper (env-wires module.wires)
  (svl-run-initialize-wires env-wires module.wires))

(encapsulate
  nil

  (def-rw-opener-error svl-run-cycle_opener-error
    (svl-run-cycle module-name inputs delayed-env svl-modules)
    :vars-to-avoid (delayed-env svl-modules))

  (rp::defthm-lambda
   svl-run-cycle-opener
   (implies
    (and (hons-get-val module-name svl-modules)
         (well-ranked-module module-name svl-modules))
    (equal (svl-run-cycle module-name inputs delayed-env svl-modules)
           (b* ((- (cw "- Using rw-rule svl-run-cycle-opener for module ~p0 ~%" module-name))
                ((svl-module module) (hons-get-val  module-name svl-modules))
                ;; create the initial queue of occurances.
                ((mv queue queue-mem)
                 (svl-run-add-to-queue
                  (hons-get-val  ':initial module.listeners)
                  nil
                  (* 4 (len module.occs))))
                ;; initialize unassigned wires to don't care with respect to
                ;; their size.
                #|(- (cw "initing the env now ~%"))||#
                (env-wires (start-env-wrapper module.inputs inputs))
                #|(- (cw "initing the wires now ~%"))||#
                ;;(env-wires (initialize-wires-wrapper env-wires module.wires))
                (env-wires
                 (svl-run-add-delayed-ins env-wires delayed-env module.delayed-inputs))
                ;; run the queue.
                ((mv env-wires next-delayed-env.modules)
                 (svl-run-queue queue queue-mem delayed-env nil
                                env-wires module.occs module.listeners
                                svl-modules
                                *big-num*))
                (next-delayed-env (make-svl-env
                                   :wires (hons-gets-fast-alist
                                           module.delayed-inputs
                                           env-wires)
                                   :modules next-delayed-env.modules))
                (outputs (svl-get-outputs module.outputs module.wires env-wires))
                (- (fast-alist-free env-wires)))
             (mv outputs next-delayed-env))))
   :hints (("Goal"
            :do-not-induct t
            :expand (svl-run-cycle MODULE-NAME inputs DELAYED-ENV svl-modules)
            :in-theory (e/d ()
                            (WELL-RANKED-MODULE
                             SVL-RUN-CYCLE_OPENER-ERROR
                             hons-get
                             FAST-ALIST-FREE
                             EQUAL-OF-SVL-ENV
                             SVL-ENV->MODULES-OF-SVL-ENV
                             SVL-ENV->WIRES-OF-SVL-ENV
                             SVL-ENV->WIRES-OF-SVL-ENV))))))
(encapsulate
  nil

  (def-rw-opener-error
    start-env_opener-error
    (start-env names vals))

  (def-rw-opener-error
    start-env-wrapper_opener-error
    (start-env-wrapper names vals))

  (defthm start-env-opener-nil
    (implies (or (atom x)
                 (atom y))
             (equal (start-env x y)
                    nil))
    :hints (("Goal"
             :expand (start-env x y)
             :in-theory (e/d () ()))))

  (defthm start-env-opener
    (equal (start-env (cons a b) (cons x y))
           (hons-acons a x (start-env b y)))
    :hints (("Goal"
             :expand (start-env (cons a b) (cons x y))
             :in-theory (e/d () ()))))

  (defthm start-env-opener-with-svex-env-p
    (equal (start-env (cons a b) (cons x y))
           (hons-acons a x (start-env b y)))
    :hints (("Goal"
             :expand (start-env (cons a b) (cons x y))
             :in-theory (e/d () ()))))

  (defthm start-env-wrapper-def
    (implies (and (sv::svarlist-p names)
                  (sv::4veclist-p vals))
             (equal (start-env-wrapper names vals)
                    (start-env names vals))))

  (defthm start-env-returns-svex-env-p
    (implies (and (sv::4veclist-p vals)
                  (sv::svarlist-p names))
             (svex-env-p (start-env names vals)))
    :hints (("Goal"
             :in-theory (e/d (start-env) ()))))

  (rp-attach-sc start-env-wrapper-def
                start-env-returns-svex-env-p))

(encapsulate
  nil

  (def-rw-opener-error
    hons-gets-vals_opener-error
    (hons-gets-vals keys alists) :vars-to-avoid (alist))

  (defthm hons-gets-vals-opener-nil
    (equal (hons-gets-vals nil alist)
           nil))

  (defthm hons-gets-vals-opener
    (equal (hons-gets-vals (cons car-keys cdr-keys) alist)
           (cons (hons-get-val car-keys alist)
                 (hons-gets-vals cdr-keys
                                 alist)))))

(encapsulate
  nil

  (def-rw-opener-error
    svl-run-occ_opener-error
    (svl-run-occ occ-name occ rest-queue queue-mem
                 delayed-env next-delayed-env.modules env-wires
                 listeners svl-modules)
    :vars-to-avoid (delayed-env next-delayed-env.modules
                                env-wires listeners svl-modules))

  (defun add-to-assign-queue-aux (occ-name listeners rest-queue queue-mem)
    (declare (xargs :guard t))
    (svl-run-add-to-queue
     (cdr (hons-get occ-name listeners)) ;;occ-listeners
     rest-queue
     (hons-acons occ-name nil queue-mem) ;;queue-mem
     ))

  (rp::defthm-lambda
   svl-run-occ-assign-opener
   (equal (svl-run-occ occ-name (cons ':assign occ-rest) rest-queue queue-mem
                       delayed-env next-delayed-env.modules env-wires
                       listeners svl-modules)
          (b* (((mv rest-queue queue-mem)
                (add-to-assign-queue-aux occ-name listeners rest-queue
                                         queue-mem)))
            #|(svl-run-add-to-queue
            (cdr (hons-get occ-name listeners)) ;;occ-listeners
            rest-queue
            (hons-acons occ-name nil queue-mem) ;;queue-mem
            )||#
            (mv (svl-run-save-assign-result
                 (svex-eval2 (occ-assign->svex2 occ-rest)
                                env-wires)
                 (occ-assign->outputs2 occ-rest)
                 env-wires) ;;env-wires
                rest-queue queue-mem next-delayed-env.modules)))
   :hints (("Goal"
            :Expand ((svl-run-occ occ-name (cons ':assign occ-rest) rest-queue queue-mem
                                  delayed-env next-delayed-env.modules env-wires
                                  listeners svl-modules))
            :in-theory (e/d (occ-kind)
                            (hons-get
                             HONS-ACONS
                             CONS-EQUAL)))))

  (defun add-to-module-queue-aux (occ-name listeners rest-queue queue-mem)
    (declare (xargs :guard t))
    (svl-run-add-to-queue (cdr (hons-get occ-name listeners)) rest-queue
                          (hons-acons occ-name nil queue-mem)))

  (defun module-get-delayed-env-aux (occ-name delayed-env)
    (declare (xargs :guard (svl-env-p delayed-env)))
    (b* ((occ-delayed-env (hons-get occ-name (svl-env->modules delayed-env))))
      (if occ-delayed-env (cdr occ-delayed-env) '(nil nil))))


  (rp::defthm-lambda
   svl-run-occ-module-opener
   (equal (svl-run-occ occ-name (cons ':module occ-rest) rest-queue  queue-mem
                       delayed-env next-delayed-env.modules env-wires
                       listeners svl-modules)
          (b* (((mv occ.inputs occ.outputs occ.name)
                (occ-module2 occ-rest))
               ((mv outputs module-next-delayed-env)
                (svl-run-cycle occ.name
                               (svl-run-get-module-occ-inputs env-wires occ.inputs)
                               (module-get-delayed-env-aux occ-name delayed-env)
                               svl-modules))
               ((mv rest-queue queue-mem)
                (add-to-module-queue-aux occ-name listeners rest-queue queue-mem)))
            (mv (svl-run-save-module-result env-wires
                                            outputs
                                            occ.outputs)
                rest-queue queue-mem
                (if (not (equal module-next-delayed-env '(nil nil)))
                    (hons-acons occ-name module-next-delayed-env next-delayed-env.modules)
                  next-delayed-env.modules))))
   :hints (("Goal"
            :Expand ((svl-run-occ occ-name (cons ':module occ-rest) rest-queue  queue-mem
                                  delayed-env next-delayed-env.modules env-wires
                                  listeners svl-modules))
            :in-theory (e/d (occ-kind)
                            (hons-get
                             HONS-ACONS
                             CONS-EQUAL))))))

(encapsulate
  nil

  (def-rw-opener-error
    svl-run-this-queue_opener-error
    (svl-run-this-queue queue queue-mem delayed-env next-delayed-env.modules
                        env-wires occs listeners svl-modules limit)
    :vars-to-avoid (delayed-env next-delayed-env.modules
                                env-wires
                                occs listeners svl-modules))

  (defthm svl-run-this-queue-opener-empty-queue-limit-reached
    (implies (consp queue)
             (equal (svl-run-this-queue queue
                                        queue-mem delayed-env
                                        next-delayed-env.modules env-wires occs listeners
                                        svl-modules 0)
                    (progn$
                     (hard-error
                      'svl-run-this-queue
                      "Limit Reached! Possibly a combinational loop between modules. ~%"
                      nil)
                     (mv env-wires nil queue-mem
                         next-delayed-env.modules))))
    :hints (("Goal"
             :expand (svl-run-this-queue queue
                                         queue-mem delayed-env
                                         next-delayed-env.modules env-wires occs listeners
                                         svl-modules 0)
             :in-theory (e/d () ()))))

  (defthm svl-run-this-queue-opener-empty-queue
    (equal (svl-run-this-queue nil
                               queue-mem delayed-env
                               next-delayed-env.modules env-wires occs listeners
                               svl-modules limit)
           (mv env-wires  nil  queue-mem next-delayed-env.modules))
    :hints (("Goal"
             :expand ((svl-run-this-queue nil
                                          queue-mem delayed-env
                                          next-delayed-env.modules env-wires occs listeners
                                          svl-modules limit))
             :in-theory (e/d () ()))))

  (rp::defthm-lambda
   svl-run-this-queue-opener-unempty-queue-occ-not-found
   (implies (and (not (zp limit))
                 (not (hons-get queue-first occs)))
            (equal (svl-run-this-queue (cons queue-first queue-rest)
                                       queue-mem delayed-env
                                       next-delayed-env.modules env-wires occs listeners
                                       svl-modules limit)
                   (b* (((mv env-wires ?rest-queue queue-mem next-delayed-env.modules)
                         (svl-run-this-queue
                          queue-rest queue-mem delayed-env next-delayed-env.modules  env-wires occs listeners
                          svl-modules (1- limit))))
                     (progn$
                      (hard-error
                       'svl-run-this-queue
                       "The occ found in the queue does not exist in the occ list ~%"
                       nil)
                      (mv env-wires nil queue-mem
                          next-delayed-env.modules)))))
   :hints (("Goal"
            :expand ((svl-run-this-queue (cons queue-first queue-rest)
                                         queue-mem delayed-env
                                         next-delayed-env.modules env-wires occs listeners
                                         svl-modules limit))
            :in-theory (e/d () ()))))

  (rp::defthm-lambda
   svl-run-this-queue-opener-unempty-queue
   (implies
    (and (not (zp limit))
         (hons-get queue-first occs))
    (equal (svl-run-this-queue (cons queue-first queue-rest)
                               queue-mem delayed-env
                               next-delayed-env.modules env-wires occs listeners
                               svl-modules limit)
           (b* (((mv env-wires rest-queue queue-mem next-delayed-env.modules)
                 (svl-run-this-queue
                  queue-rest queue-mem delayed-env next-delayed-env.modules  env-wires occs listeners
                  svl-modules (1- limit))))
             (svl-run-occ queue-first (hons-get-val queue-first occs) rest-queue queue-mem
                          delayed-env next-delayed-env.modules
                          env-wires listeners svl-modules))))
   :hints (("Goal"
            :expand ((svl-run-this-queue (cons queue-first queue-rest)
                                         queue-mem delayed-env
                                         next-delayed-env.modules env-wires occs listeners
                                         svl-modules limit))
            :in-theory (e/d () ())))))

(encapsulate
  nil

  (def-rw-opener-error
    svl-run-queue_opener-error
    (svl-run-queue queue queue-mem delayed-env
                   next-delayed-env.modules env-wires occs
                   listeners svl-modules limit)
    :vars-to-avoid (delayed-env next-delayed-env.modules
                                env-wires
                                occs listeners svl-modules))
  (defthm svl-run-queue-limit-reached
    (implies (consp queue)
             (equal (svl-run-queue queue queue-mem delayed-env next-delayed-env.modules
                                   env-wires occs listeners svl-modules 0)
                    (progn$
                     (hard-error
                      'svl-run-queue
                      "Limit Reached! Possibly a combinational loop between modules. ~%"
                      nil)
                     (mv env-wires next-delayed-env.modules))))
    :hints (("Goal"
             :expand (svl-run-queue queue queue-mem delayed-env next-delayed-env.modules
                                    env-wires occs listeners svl-modules 0)
             :in-theory (e/d () ()))))

  (defthm svl-run-queue-empty-queue
    (equal (svl-run-queue nil queue-mem delayed-env next-delayed-env.modules
                          env-wires occs listeners svl-modules limit)
           (progn$ (fast-alist-free queue-mem)
                   (mv env-wires next-delayed-env.modules)))
    :hints (("Goal"
             :expand (svl-run-queue nil queue-mem delayed-env next-delayed-env.modules
                                    env-wires occs listeners svl-modules limit)
             :in-theory (e/d () ()))))

  (rp::defthm-lambda
   svl-run-queue-unempty-queue
   (implies
    (and (not (zp limit))
         (consp queue))
    (equal (svl-run-queue queue queue-mem delayed-env next-delayed-env.modules
                          env-wires occs listeners svl-modules limit)
           (b* (((mv env-wires new-queue queue-mem next-delayed-env.modules)
                 (svl-run-this-queue queue queue-mem delayed-env
                                     next-delayed-env.modules env-wires occs
                                     listeners svl-modules (1- limit))))

             (svl-run-queue new-queue queue-mem delayed-env
                            next-delayed-env.modules env-wires occs
                            listeners svl-modules (1- limit)))))
   :hints (("Goal"
            :expand (svl-run-queue queue queue-mem delayed-env next-delayed-env.modules
                                   env-wires occs listeners svl-modules limit)
            :in-theory (e/d ()
                            (CONS-EQUAL))))))

(encapsulate
  nil

  (def-rw-opener-error
    svl-run_opener-error
    (svl-run module-name inputs svl-design)
    :vars-to-avoid (svl-design))

  (rp::defthm-lambda
   svl-run-opener
   (equal (svl-run module-name inputs svl-design)
          (b* (((mv res next-delayed-env)
                (svl-run-cycle module-name
                               inputs
                               (make-svl-env)
                               svl-design))
               (- (svl-free-env module-name next-delayed-env svl-design 1000000)))
            (mv (fast-alist-free res)
                next-delayed-env)))))

(encapsulate
  nil

  (def-rw-opener-error
    svl-run-add-delayed-ins_opener-error
    (svl-run-add-delayed-ins env-wires delayed-env occ-delayed-ins)
    :vars-to-avoid
    (env-wires delayed-env))

  (defthm svl-run-add-delayed-ins-no-delayed-input
    (equal (svl-run-add-delayed-ins env-wires delayed-env nil)
           env-wires)
    :hints (("Goal"
             :expand (svl-run-add-delayed-ins env-wires delayed-env nil)
             :in-theory (e/d () ()))))

  (rp::defthm-lambda
   svl-run-add-delayed-ins-cons
   (equal (svl-run-add-delayed-ins env-wires delayed-env (cons first rest))
          (b* ((prev-val (hons-get-val first (svl-env->wires delayed-env)))
               ((unless prev-val)
                (svl-run-add-delayed-ins env-wires delayed-env rest)))
            (svl-run-add-delayed-ins (hons-acons `(:var ,first
                                                        . 1)
                                                 prev-val
                                                 env-wires)
                                     delayed-env
                                     rest)))
   :hints (("Goal"
            :expand (svl-run-add-delayed-ins env-wires delayed-env (cons first rest))
            :in-theory (e/d () ())))))

(encapsulate
  nil

  (def-rw-opener-error
    svl-run-initialize-wires_opener-error
    (svl-run-initialize-wires env-wires wires))

  (def-rw-opener-error
    initialize-wires-wrapper_opener-error
    (initialize-wires-wrapper env-wires wires))

  (defthm svl-run-initialize-wires-opener-nil
    (equal (svl-run-initialize-wires env-wires nil)
           env-wires)
    :hints (("Goal"
             :expand (svl-run-initialize-wires env-wires nil)
             :in-theory (e/d () ()))))

  (defthm svl-run-initialize-wires-opener-cons
    (equal (svl-run-initialize-wires env-wires (cons wire rest))
           (if (hons-get  (wire-name wire) env-wires)
               (svl-run-initialize-wires env-wires rest)
             (hons-acons
              (wire-name wire)
              (4vec-part-select 0 (ifix (wire-size wire))
                                '(-1 . 0))
              (svl-run-initialize-wires env-wires rest))))
    :hints (("Goal"
             :expand (svl-run-initialize-wires env-wires (cons wire rest))
             :in-theory (e/d (HONS-ASSOC-EQUAL hons-get ) ()))))

  (defthm svl-run-initialize-wires-is-svex-env-p
    (implies (and (svex-env-p env-wires)
                  (wire-list-p module.wires))
             (svex-env-p (svl-run-initialize-wires env-wires module.wires))))

  (defthm initialize-wires-wrapper-def
    (implies (and (svex-env-p env-wires)
                  (wire-list-p module.wires))
             (equal (initialize-wires-wrapper env-wires module.wires)
                    (svl-run-initialize-wires env-wires module.wires))))

  (rp-attach-sc initialize-wires-wrapper-def
                svl-run-initialize-wires-is-svex-env-p))

(encapsulate
  nil

  (def-rw-opener-error
    svl-run-save-module-result_opener-error
    (svl-run-save-module-result env-wires occ-res-vals occ-outs)
    :vars-to-avoid (env-wires))

  (defthm svl-run-save-module-result-opener-0
    (equal (svl-run-save-module-result env-wires occ-res-vals (cons first rest))
           (b* ((wire (cdr first))
                (new-val (if (consp occ-res-vals) (car occ-res-vals) '(-1 . 0))))
             (svl-run-save-module-result
              (svl-update-wire wire new-val env-wires)
              (cdr occ-res-vals)
              rest)))
    :hints (("Goal"
             :expand (svl-run-save-module-result env-wires occ-res-vals (cons first rest))
             :in-theory (e/d () ()))))

  (defthm svl-run-save-module-result-opener
    (equal (svl-run-save-module-result env-wires (cons first-vals rest-vals) (cons first rest))
           (b* ((wire (cdr first))
                (new-val first-vals))
             (svl-run-save-module-result
              (svl-update-wire wire new-val env-wires)
              rest-vals
              rest)))
    :hints (("Goal"
             :expand (svl-run-save-module-result env-wires (cons first-vals rest-vals) (cons first rest))
             :in-theory (e/d () ()))))

  (defthm svl-run-svl-run-save-module-result-opener-nil
    (equal (svl-run-save-module-result env-wires occ-res-alist nil)
           env-wires)
    :hints (("Goal"
             :expand (svl-run-save-module-result env-wires occ-res-alist nil)
             :in-theory (e/d () ())))))

(encapsulate
  nil

  (def-rw-opener-error
    svl-run-get-module-occ-inputs_opener-error
    (svl-run-get-module-occ-inputs env-wires occ-ins)
    :vars-to-avoid (env-wires))

  (defthm
    svl-run-get-module-occ-inputs-opener-nil
    (equal (svl-run-get-module-occ-inputs env-wires  nil)
           nil)
    :hints (("Goal"
             :expand (svl-run-get-module-occ-inputs env-wires  nil)
             :in-theory (e/d () ()))))

  (rp::defthm-lambda
   svl-run-get-module-occ-inputs-opener
   (equal (svl-run-get-module-occ-inputs env-wires (cons first rest))
          (b* ((wire (cdr first))
               (val (hons-get (wire-name wire) env-wires)))
            (cons (if val
                      (if (wire-start wire)
                          (bits (wire-start wire) (wire-size wire) (cdr val))
                        (cdr val))
                    '(-1 . 0))
                  (svl-run-get-module-occ-inputs env-wires rest))))
   :hints (("Goal"
            :expand (svl-run-get-module-occ-inputs
                     env-wires  (cons first rest))
            :in-theory (e/d () ())))))

(encapsulate
  nil

  (def-rw-opener-error
    make-fast-alist_opener-error
    (make-fast-alist alist))

  (defthm make-alist-def-nil
    (equal (make-fast-alist nil)
           nil))

  (defthm make-fast-alist-def
    (equal (make-fast-alist (cons (cons a b) rest))
           (hons-acons a b (make-fast-alist rest))))

  (defthm make-fast-alist-ignore-def
    (implies (syntaxp (and (consp x)
                           (equal (car x) 'falist)))
             (equal (make-fast-alist x)
                    x))))

(encapsulate
  nil

  (def-rw-opener-error
    mv-nth_opener-error
    (mv-nth n term))

  (defthm mv-nth-def-1
    (implies (not (zp n))
             (equal (mv-nth n (cons a b))
                    (mv-nth (1- n) b)))
    :hints (("Goal"
             :expand (mv-nth n (cons a b))
             :in-theory (e/d () ()))))

  (defthm mv-nth-def-0
    (equal (mv-nth 0 (cons a b))
           a)
    :hints (("Goal"
             :expand (mv-nth 0 (cons a b))
             :in-theory (e/d () ()))))

  (defthm mv-nth-def-nil
    (equal (mv-nth n nil)
           nil)
    :hints (("Goal"
             :expand (mv-nth n nil)
             :in-theory (e/d () ())))))

(encapsulate
  nil
  (def-rw-opener-error
    hons-gets-fast-alist_opener-error
    (hons-gets-fast-alist keys fast-alist)
    :vars-to-avoid (fast-alist))

  (defthm hons-gets-fast-alist-opener-cons
    (equal (hons-gets-fast-alist (cons f r) fast-alist)
           (hons-acons f
                       (if (hons-get f fast-alist)
                           (hons-get-val f fast-alist)
                         (sv::4vec-x))
                       (hons-gets-fast-alist r fast-alist)))
    :hints (("Goal"
             :in-theory (e/d (hons-gets-fast-alist) ()))))

  (defthm hons-gets-fast-alist-opener-nil
    (equal (hons-gets-fast-alist nil fast-alist)
           nil)
    :hints (("Goal"
             :in-theory (e/d (hons-gets-fast-alist) ())))))

(encapsulate
  nil

  (def-rw-opener-error
    svl-get-outputs_opener-error
    (svl-get-outputs sigs wires alist)
    :vars-to-avoid (alist))

  (defthm svl-get-outputs-nil
    (equal (svl-get-outputs nil wires alist)
           nil)
    :hints (("Goal"
             :in-theory (e/d (svl-get-outputs) ()))))

  (rp::defthm-lambda
   svl-get-outputs-opener
   (equal (svl-get-outputs (cons sig rest) wires alist)
          (b*  ((res (hons-get sig alist))
                ((unless res)
                 (cons (sv::4vec-x)
                       (svl-get-outputs rest wires alist)))
                (wire (assoc-equal sig wires)))
            (cons (if (and (cadr wire) res)
                      (bits 0 (cadr wire) (cdr res))
                    (cdr res))
                  (svl-get-outputs rest wires alist))))
   :hints (("goal"
            :in-theory (e/d (svl-get-outputs) ())))))

(encapsulate
  nil
  (def-rw-opener-error
    svl-run-save-assign-result_opener-error
    (svl-run-save-assign-result result occ-outs env-wires)
    :vars-to-avoid (env-wires))

  (defthm svl-run-save-assign-result-nil
    (equal (svl-run-save-assign-result result nil env-wires)
           env-wires)
    :hints (("goal"
             :expand (svl-run-save-assign-result result nil env-wires)
             :in-theory (e/d () ()))))

  (defthm svl-run-save-assign-result-cons
    (equal (svl-run-save-assign-result result (cons wire rest) env-wires)
           (b* ((size (if (wire-size wire) (wire-size wire) 1))
                (env-wires (svl-update-wire wire result env-wires)))
             (svl-run-save-assign-result (4vec-rsh size result)
                                         rest
                                         env-wires)))
    :hints (("goal"
             :in-theory (e/d (svl-run-save-assign-result) ()))))

  (defthm svl-run-save-assign-result-cons-2
    (equal (svl-run-save-assign-result result (cons wire nil) env-wires)
           (b* ((env-wires (svl-update-wire wire result env-wires)))
             env-wires))
    :hints (("goal"
             :in-theory (e/d (svl-run-save-assign-result) ())))))

(encapsulate
  nil

  (def-rw-opener-error
    svl-update-wire_opener-error
    (svl-update-wire wire new-val env-wires)
    :vars-to-avoid (env-wires))

  (defthm
   svl-update-wire-def
   (equal (svl-update-wire `(,wire.name ,wire.size . ,wire.start)  new-val env-wires)
          (b* ()
            (hons-acons wire.name (sbits wire.start wire.size
                                         new-val
                                         (if (hons-get wire.name env-wires)
                                             (cdr (hons-get wire.name
                                                            env-wires))
                                           '(-1 . 0)))
                        env-wires)))
   :hints (("Goal"
            :in-theory (e/d (svl-update-wire) ()))))

  (defthm svl-update-wire-def-2
    (equal (svl-update-wire `(,wire.name)  new-val env-wires)
           (hons-acons wire.name new-val env-wires))
    :hints (("Goal"
             :in-theory (e/d (svl-update-wire) ()))))

  (defthmd
    svl-update-wire-def-on-svex-env-p
    (implies (and (svex-env-p env-wires)
                  (4vec-p new-val)
                  (sv::svar-p wire.name))
             (equal (svl-update-wire `(,wire.name ,wire.size . ,wire.start)  new-val env-wires)
                    (hons-acons wire.name (sbits wire.start wire.size
                                                 new-val
                                                 (if (hons-get wire.name
                                                               env-wires)
                                                     (hons-get-val wire.name
                                                                   env-wires)
                                                   '(-1 . 0)))
                                env-wires)))
    :hints (("Goal"
             :in-theory (e/d (svl-update-wire) ()))))

  (defthmd svl-update-wire-def-on-svex-env-p-side-cond
    (implies (and (svex-env-p env-wires)
                  (4vec-p new-val)
                  (sv::svar-p wire.name))
             (svex-env-p (hons-acons wire.name
                                     (sbits wire.start wire.size
                                            new-val
                                            (if (hons-get wire.name
                                                          env-wires)
                                                (hons-get-val wire.name
                                                              env-wires)
                                              '(-1 . 0)))
                                     env-wires))))

  (rp-attach-sc svl-update-wire-def-on-svex-env-p
                svl-update-wire-def-on-svex-env-p-side-cond)

  (defthmd svl-update-wire-def-2-on-svex-env-p
    (implies (and (svex-env-p env-wires)
                  (4vec-p new-val)
                  (sv::svar-p wire.name))
             (equal (svl-update-wire `(,wire.name)  new-val env-wires)
                    (hons-acons wire.name new-val env-wires))))

  (defthmd svl-update-wire-def-2-on-svex-env-p-side-cond
    (implies (and (svex-env-p env-wires)
                  (4vec-p new-val)
                  (sv::svar-p wire.name))
             (svex-env-p (hons-acons wire.name new-val env-wires))))

  (rp-attach-sc svl-update-wire-def-2-on-svex-env-p
                svl-update-wire-def-2-on-svex-env-p-side-cond)

  ;; becasue we want to make sure that the ones with the hypotheses are used only.
  #|(in-theory (disable svl-update-wire-def
                      svl-update-wire-def-2))||#)

;; (in-theory (enable svl-run-cycle_opener-error
;;                    start-env_opener-error
;;                    svl-run-this-queue_opener-error
;;                    hons-gets-vals_opener-error
;;                    svl-run-occ_opener-error
;;                    svl-run-add-delayed-ins_opener-error
;;                    svl-run-get-module-occ-inputs
;;                    svl-run-initialize-wires_opener-error
;;                    svl-run-save-module-result_opener-error
;;                    make-fast-alist_opener-error
;;                    hons-gets-fast-alist_opener-error
;;                    svl-get-outputs_opener-error
;;                    svl-run-save-assign-result_opener-error
;;                    initialize-wires-wrapper_opener-error
;;                    start-env-wrapper_opener-error
;;                    svl-update-wire_opener-error
;;                    svl-run-get-module-occ-inputs_opener-error
;;                    svl-run-queue_opener-error
;;                    mv-nth_opener-error
;;                    svl-run_opener-error))

(defthm GET-MAX-OCC-RANK-opener-cons
  (equal (get-max-occ-rank (cons first rest) svl-design)
         (MAX (GET-MAX-OCC-RANK rest
                                svl-design)
              (GET-OCC-RANK (cdr first)
                            svl-design)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (get-max-occ-rank) ()))))

(defthm GET-MAX-OCC-RANK-opener-nil
  (equal (get-max-occ-rank nil svl-design)
         0)
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (get-max-occ-rank) ()))))

(in-theory (enable GET-OCC-RANK
                   GET-MODULE-RANK))
