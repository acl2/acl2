; FGL - A Symbolic Simulation Framework for ACL2
;; SPDX-FileCopyrightText: Copyright 2025 Arm Limited and/or its affiliates <open-source-office@arm.com>
;; SPDX-License-Identifier: BSD-3-Clause
;; 
;; Redistribution and use in source and binary forms, with or without
;; modification, are permitted provided that the following conditions are
;; met:

;; o Redistributions of source code must retain the above copyright
;;   notice, this list of conditions and the following disclaimer.

;; o Redistributions in binary form must reproduce the above copyright
;;   notice, this list of conditions and the following disclaimer in the
;;   documentation and/or other materials provided with the distribution.

;; o Neither the name of the copyright holder nor the names of
;;   its contributors may be used to endorse or promote products derived
;;   from this software without specific prior written permission.

;; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
;; "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
;; LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
;; A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
;; HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
;; SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
;; LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
;; DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
;; THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
;; (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
;; OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

;; Author: Sol Swords <sol.swords@arm.com>

(in-package "FGL")

(include-book "trace")

(local (in-theory (disable w)))

(encapsulate nil
  (local
   (progn
     (defthm w-of-put-global
       (implies (not (equal sym 'current-acl2-world))
                (equal (w (put-global sym val state))
                       (w state)))
       :hints(("Goal" :in-theory (enable put-global w))))
     (defthm w-of-read-acl2-oracle
       (equal (w (mv-nth 2 (read-acl2-oracle state)))
              (w state))
       :hints(("Goal" :in-theory (enable read-acl2-oracle update-acl2-oracle w))))
     (defthm w-of-iprint-oracle-upddes
       (equal (w (acl2::iprint-oracle-updates state))
              (w state))
       :hints(("Goal" :in-theory (e/d (acl2::iprint-oracle-updates)
                                      (put-global)))))
     (defthm w-of-update-open-input-channels
       (equal (w (update-open-input-channels x state))
              (w state))
       :hints(("Goal" :in-theory (enable w update-open-input-channels))))))
   
  (defthm w-of-read-object
    (equal (w (mv-nth 2 (read-object channel statE)))
           (w state))
    :hints(("Goal" :in-theory (disable nth update-open-input-channels))))
  (in-theory (disable read-object)))

(fancy-ev-add-primitive read-object (and (symbolp acl2::channel)
                                         (open-input-channel-p acl2::channel :object state)))

(fancy-ev-add-primitive open-input-channel-p (and (symbolp acl2::channel)
                                                  (member-eq acl2::typ acl2::*file-types*)))




(define fancy-repl ((prompt stringp)
                    (bindings symbol-alistp)
                    (reclimit natp)
                    (interp-st interp-st-bfrs-ok)
                    state)
  :returns (mv new-interp-st new-state)
  (b* (((when (zp reclimit)) (mv interp-st state))
       (channel *standard-oi*)
       ((unless (open-input-channel-p channel :object state))
        (mv interp-st state))
       (- (cw "~s0" prompt))
       ((mv eofp obj state) (read-object channel state))
       ((when eofp) (mv interp-st state))
       ((when (eq obj :exit)) (mv interp-st state))
       ((mv errmsg trans interp-st state)
        (fancy-translate obj 10000 interp-st state t t))
       ((when errmsg)
        (cw "~@0~%" errmsg)
        (fancy-repl prompt bindings (1- reclimit) interp-st state))
       ((mv errmsg val interp-st state)
        (fancy-ev trans bindings 10000 interp-st state t t))
       (- (if errmsg
              (cw "~@0~%" errmsg)
            (cw "~x0~%" val))))
    (fancy-repl prompt bindings (1- reclimit) interp-st state)))


;; (define trace-repl (&key ((bindings symbol-alistp) 'trace-meta-bindings)
;;                          ((interp-st interp-st-bfrs-ok) 'interp-st)
;;                          (state 'state))
;;   (b* (((mv interp-st state)
;;         (fancy-repl "trace> " (cons (cons 'trace-meta-bindings bindings) bindings)
;;                     10000 interp-st state)))
;;     (


(defmacro trace-repl (&key (bindings 'trace-meta-bindings))
  `(b* ((bindings ,bindings)
        (?ign (fancy-repl "trace> " (cons (cons 'trace-meta-bindings bindings) bindings)
                          10000 interp-st state)))
     :default))


(local (def-fancy-ev-primitives foo-bar))

(local
 (define test-fancy-repl ((prompt stringp)
                          (bindings symbol-alistp)
                          state)
   :guard-hints (("goal" :in-theory (disable create-interp-st)))
   (with-local-stobj interp-st
     (mv-let (interp-st state)
       (fancy-repl prompt bindings 10000 interp-st state)
       state))))

(local
 (define test-fancy-ev ((x pseudo-termp) (alist symbol-alistp) (reclimit natp) state hard-errp aokp)
   ;; this is all just to show interp-st-bfrs-ok of create-interp-st
   :guard-hints (("goal" :in-theory (disable create-interp-st)))
   (with-local-stobj interp-st
     (mv-let (err val interp-st state)
       (fancy-ev x alist reclimit interp-st state hard-errp aokp)
       (mv err val state)))))




(define fgl-trace-entry-fancy-translate-keyvals (keyvals
                                                 (interp-st interp-st-bfrs-ok)
                                                 state)
  :returns (mv err (entry true-listp :rule-classes :type-prescription)
               interp-st state)
  (if (or (atom keyvals)
          (atom (cdr keyvals)))
      (mv nil nil interp-st state)
    (b* (((mv err trans-val interp-st state)
          (fancy-translate (cadr keyvals) 10000 interp-st state t t))
         ((when err) (mv err nil interp-st state))
         ((mv err rest interp-st state)
          (fgl-trace-entry-fancy-translate-keyvals (cddr keyvals) interp-st state))
         ((when err) (mv err nil interp-st state)))
      (mv nil (cons (car keyvals) (cons trans-val rest)) interp-st state))))


(define fgl-trace-entry-fancy-translate (keyvals
                                              restore-rules
                                              (interp-st interp-st-bfrs-ok)
                                              state)
  :returns (mv err (entry true-listp :rule-classes :type-prescription)
               new-interp-st new-state)
  (b* (((mv err trans-keyvals interp-st state)
        (fgl-trace-entry-fancy-translate-keyvals keyvals interp-st state))
       ((when err) (mv err nil interp-st state)))
    (mv nil
        (append trans-keyvals
                (and restore-rules `(:restore-rules ,restore-rules)))
        interp-st state)))

(define fgl-trace-update-fn (rune keyvals
                             restore-rules
                             (interp-st interp-st-bfrs-ok)
                             state)
  (b* (((unless (fgl-generic-rune-p rune))
        (mv "Rune must satisfy fgl-generic-rune-p" nil interp-st state))
       ((mv err entry interp-st state)
        (fgl-trace-entry-fancy-translate
         keyvals
         restore-rules
         interp-st
         state))
       ((when err) (mv err nil interp-st state))
       (old-alist (interp-st->trace-alist interp-st))
       (new-alist (cons (cons rune entry) old-alist))
       (interp-st (update-interp-st->trace-alist new-alist interp-st)))
    (mv nil entry interp-st state)))

(defmacro fgl-trace-update (rune
                            &key
                            (cond 'nil cond-p)
                            (on-entry 'nil on-entry-p)
                            (on-relieve-hyp 'nil on-relieve-hyp-p)
                            (on-eval-success 'nil on-eval-success-p)
                            (on-eval-failure 'nil on-eval-failure-p)
                            (on-success 'nil on-success-p)
                            (on-failure 'nil on-failure-p)
                            (restore-rules 'nil))
  `(fgl-trace-update-fn ',rune
                        (list . ,(append (and cond-p `(:cond ',cond))
                                         (and on-entry-p `(:on-entry ',on-entry))
                                         (and on-relieve-hyp-p `(:on-relieve-hyp ',on-relieve-hyp))
                                         (and on-eval-success-p `(:on-eval-success ',on-eval-success))
                                         (and on-eval-failure-p `(:on-eval-failure ',on-eval-failure))
                                         (and on-success-p `(:on-success ',on-success))
                                         (and on-failure-p `(:on-failure ',on-failure))))
                        ,restore-rules
                        interp-st
                        state))


(define fgl-modify-current-tracespec-fn (rune
                                         keyvals
                                         restore-rules
                                         (interp-st interp-st-bfrs-ok)
                                         state)
  (b* (((mv err entry interp-st state)
        (fgl-trace-entry-fancy-translate keyvals restore-rules interp-st state))
       ((when err)
        (mv err nil interp-st state))
       (interp-st
        (update-interp-st->tracespecs
         (cons (cons rune entry) (cdr (interp-st->tracespecs interp-st)))
         interp-st)))
    (mv nil entry interp-st state)))

(defmacro fgl-modify-current-tracespec
    (rune
     &key
     (cond 'nil cond-p)
     (on-entry 'nil on-entry-p)
     (on-relieve-hyp 'nil on-relieve-hyp-p)
     (on-eval-success 'nil on-eval-success-p)
     (on-eval-failure 'nil on-eval-failure-p)
     (on-success 'nil on-success-p)
     (on-failure 'nil on-failure-p)
     (restore-rules 'nil))
  `(fgl-modify-current-tracespec-fn ',rune
                                    (list . ,(append (and cond-p `(:cond ',cond))
                                                     (and on-entry-p `(:on-entry ',on-entry))
                                                     (and on-relieve-hyp-p `(:on-relieve-hyp ',on-relieve-hyp))
                                                     (and on-eval-success-p `(:on-eval-success ',on-eval-success))
                                                     (and on-eval-failure-p `(:on-eval-failure ',on-eval-failure))
                                                     (and on-success-p `(:on-success ',on-success))
                                                     (and on-failure-p `(:on-failure ',on-failure))))
                                    ,restore-rules
                                    interp-st
                                    state))

(defmacro fgl-delete-current-tracespec ()
  '(update-interp-st->tracespecs
    (cons nil (cdr (interp-st->tracespecs interp-st)))
    interp-st))

