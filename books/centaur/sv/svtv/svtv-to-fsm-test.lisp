; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2023 Intel Corporation
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
; Original author: Sol Swords <sol.swords@intel.com>

(in-package "SV")

(include-book "svtv-to-fsm-defs")
;; (include-book "svtv-generalize")
(include-book "centaur/fgl/top" :dir :system)
(include-book "svtv-stobj-defsvtv")
(include-book "centaur/vl/loader/top" :dir :system)
(include-book "centaur/sv/vl/top" :dir :system)
(include-book "oslib/ls" :dir :system)
(include-book "svtv-stobj-debug")
; cert_param: (uses-glucose)

(defconsts (*vl-design* state)
  (b* (((mv (vl::vl-loadresult loadres) state)
        (vl::vl-load (vl::make-vl-loadconfig :start-files '("svtv_to_fsm_test_counter.sv")))))
    (mv loadres.design state)))

(defconsts (*sv-design* *vl-good* *vl-bad*)
  (b* (((mv errmsg svex good bad)
        (vl::vl-design->sv-design "counter" *vl-design* (vl::make-vl-simpconfig))))
    (and errmsg
         (raise "~@0~%" errmsg))
    (mv svex good bad)))


(encapsulate nil
  (local (defcycle counter-phase-fsm-def
           :design *sv-design*
           :phases nil))
  (local (def-svtv-data-export counter-phase-data))
  (make-event
   (b* ((fsm (svtv-data->phase-fsm svtv-data)))
     `(define counter-phase-fsm ()
        :returns (fsm)
        ',fsm)))

  (local (defthm counter-phase-fsm-is-data-fsm
           (equal (counter-phase-fsm)
                  (svtv-data-obj->phase-fsm (counter-phase-data)))
           :hints (("goal" :in-theory (enable (counter-phase-data)
                                              (svtv-data-obj->phase-fsm))))))
  
  (defthm fsm-p-of-<fn>
    (fsm-p (counter-phase-fsm))
    :hints (("goal" :in-theory '(counter-phase-fsm-is-data-fsm
                                 fsm-p-of-svtv-data-obj->phase-fsm)))))

;; For each of these tests I want to try this both with and without :initial-state-vars t.
;; So I first define the sequence of events as a constant, with the :initial-state-vars declaration.
;; I run with the initial-state-vars just using (make-event *constant*).  Then also
;; (make-event (remove-initial-state-vars (remove-define-fsm *constant*)))
(local
 (defun remove-initial-state-vars (x)
  (if (atom x)
      x
    (case-match x
      ((':initial-state-vars 't . rest) rest)
      (& (cons (remove-initial-state-vars (car x))
               (remove-initial-state-vars (cdr x))))))))

(local
 (defun remove-define-fsm (x)
  (if (atom x)
      x
    (case-match x
      ((':define-fsm 't . rest) rest)
      (& (cons (remove-define-fsm (car x))
               (remove-define-fsm (cdr x))))))))



(defconst *counter-invar0-events*
  '(progn
                             
(defsvtv$ counter-invar0-run
  :design *sv-design*
  :cycle-phases (list (make-svtv-cyclephase :constants '(("clk" . 1)))
                      (make-svtv-cyclephase :constants '(("clk" . 0))
                                            :inputs-free t
                                            :outputs-captured t))
  :initial-state-vars t
  :stages ((:label curr
            :inputs (("inc" inc)
                     ("reset" 0))
            :overrides (("sum" sum :cond sum-ovr :output sum-prev)
                        ("sum1" sum1 :cond sum1-ovr)))
           (:label next
            :outputs (("sum" sum-out)
                      ("sum1" sum1-out)))))



;; temp




(encapsulate nil
  (local (include-book "svtv-generalize"))
  (local (include-book "svtv-to-fsm"))
  (local (def-svtv-data-export counter-invar0-run-data))
  
  (make-event '(def-svtv-refinement counter-invar0-run counter-invar0-run-data
                 :svtv-spec counter-invar0-spec :inclusive-overridekeys t
                 :phase-fsm counter-phase-fsm
                 :fsm counter-fsm :define-fsm t)))

(value-triple (acl2::tshell-ensure))


(encapsulate nil
  (local (include-book "svtv-generalize"))

  (make-event '(def-svtv-generalized-thm counter-invar0-svtv-thm
                 :svtv counter-invar0-run
                 :svtv-spec counter-invar0-spec
                 :input-vars :all
                 :output-vars (sum-out sum1-out)
                 :unsigned-byte-hyps t
                 :override-vars (sum)
                 :spec-override-vars (sum1)
                 :hyp (and (<= sum 11)
                           (<= sum1 10))
                 :concl (and (<= sum-out 11)
                             (<= sum1-out 10)))))


(encapsulate nil
  (local (include-book "svtv-to-fsm"))
  (local (include-book "svtv-generalize"))
  (make-event '(def-svtv-to-fsm-thm counter-invar0-fsm-thm
                 :svtv-spec-thmname counter-invar0-svtv-thm))

  (make-event '(def-svtv-to-fsm-thm counter-invar0-fsm-thm2
                 :svtv-spec-thmname counter-invar0-svtv-thm
                 :eliminate-override-vars (sum1)))
  (make-event '(def-svtv-to-fsm-thm counter-invar0-fsm-thm3
                 :svtv-spec-thmname counter-invar0-svtv-thm
                 :eliminate-override-vars :all))
  (make-event '(def-svtv-to-fsm-thm counter-invar0-fsm-thm4
                 :svtv-spec-thmname counter-invar0-svtv-thm
                 :eliminate-override-signals :all))

  (make-event '(def-svtv-to-fsm-thm counter-invar0-fsm-thm5
                 :svtv-spec-thmname counter-invar0-svtv-thm
                 :cycle-num-rewrite-strategy :all-free))
  (make-event '(def-svtv-to-fsm-thm counter-invar0-fsm-thm6
                 :svtv-spec-thmname counter-invar0-svtv-thm
                 :eliminate-override-vars (sum1)
                 :cycle-num-rewrite-strategy :all-free))
  (make-event '(def-svtv-to-fsm-thm counter-invar0-fsm-thm7
                 :svtv-spec-thmname counter-invar0-svtv-thm
                 :eliminate-override-vars :all
                 :cycle-num-rewrite-strategy :all-free))
  (make-event '(def-svtv-to-fsm-thm counter-invar0-fsm-thm8
                 :svtv-spec-thmname counter-invar0-svtv-thm
                 :eliminate-override-signals :all
                 :cycle-num-rewrite-strategy :all-free))

  (make-event '(def-svtv-to-fsm-thm counter-invar0-fsm-thm9
                 :svtv-spec-thmname counter-invar0-svtv-thm
                 :cycle-num-rewrite-strategy :single-var))
  (make-event '(def-svtv-to-fsm-thm counter-invar0-fsm-thm10
                 :svtv-spec-thmname counter-invar0-svtv-thm
                 :eliminate-override-vars (sum1)
                 :cycle-num-rewrite-strategy :single-var))
  (make-event '(def-svtv-to-fsm-thm counter-invar0-fsm-thm11
                 :svtv-spec-thmname counter-invar0-svtv-thm
                 :eliminate-override-vars :all
                 :cycle-num-rewrite-strategy :single-var))
  (make-event '(def-svtv-to-fsm-thm counter-invar0-fsm-thm12
                 :svtv-spec-thmname counter-invar0-svtv-thm
                 :eliminate-override-signals :all
                 :cycle-num-rewrite-strategy :single-var)))

))

(make-event *counter-invar0-events*)
(make-event
 (acl2::template-subst-top (remove-initial-state-vars (remove-define-fsm *counter-invar0-events*))
                           (acl2::make-tmplsubst :strs '(("INVAR0" . "INVAR0A"))
                                                 :pkg-sym 'sv-package)))



(defconst *counter-invar1-events*
  '(progn
(defsvtv$ counter-invar1-run
  :design *sv-design*
  :cycle-phases (list (make-svtv-cyclephase :constants '(("clk" . 1)))
                      (make-svtv-cyclephase :constants '(("clk" . 0))
                                            :inputs-free t
                                            :outputs-captured t))
  :initial-state-vars t
  :stages ((:label curr
            :inputs (("inc" inc)
                     ("reset" 0))
            :overrides (("sum" sum :cond sum-ovr :output sum-prev)
                        ("sum1" sum1)))
           (:label next
            :outputs (("sum" sum-out)
                      ("sum1" sum1-out)))))

(def-svtv-data-export counter-invar1-run-data)

(encapsulate nil
  (local (include-book "svtv-to-fsm"))
  (local (include-book "svtv-generalize"))
  (make-event
   '(progn
      (def-svtv-refinement counter-invar1-run counter-invar1-run-data
        :svtv-spec counter-invar1-spec
        :inclusive-overridekeys t
        :fsm counter-fsm)



      (def-svtv-generalized-thm counter-invar1-svtv-thm
        :svtv counter-invar1-run
        :svtv-spec counter-invar1-spec
        :input-vars :all
        :output-vars (sum-out sum1-out)
        :unsigned-byte-hyps t
        :override-vars (sum)
        :spec-override-vars ()
        :hyp (and (<= sum 11)
                  (<= sum1 10))
        :concl (and (<= sum-out 11)
                    (<= sum1-out 10)))

      (def-svtv-to-fsm-thm counter-invar1-fsm-thm
        :svtv-spec-thmname counter-invar1-svtv-thm)

      (def-svtv-to-fsm-thm counter-invar1-fsm-thm2
        :svtv-spec-thmname counter-invar1-svtv-thm
        ;; BOZO we should only have to specify one of these
        :eliminate-override-vars (sum1)
        :eliminate-override-signals ("sum1"))

      (def-svtv-to-fsm-thm counter-invar1-fsm-thm3
        :svtv-spec-thmname counter-invar1-svtv-thm
        :eliminate-override-vars :all)

      (def-svtv-to-fsm-thm counter-invar1-fsm-thm4
        :svtv-spec-thmname counter-invar1-svtv-thm
        :eliminate-override-signals :all)

      
      (def-svtv-to-fsm-thm counter-invar1-fsm-thm5
        :svtv-spec-thmname counter-invar1-svtv-thm
        :cycle-num-rewrite-strategy :all-free)

      (def-svtv-to-fsm-thm counter-invar1-fsm-thm6
        :svtv-spec-thmname counter-invar1-svtv-thm
        ;; BOZO we should only have to specify one of these
        :eliminate-override-vars (sum1)
        :eliminate-override-signals ("sum1")
        :cycle-num-rewrite-strategy :all-free)

      (def-svtv-to-fsm-thm counter-invar1-fsm-thm7
        :svtv-spec-thmname counter-invar1-svtv-thm
        :eliminate-override-vars :all
        :cycle-num-rewrite-strategy :all-free)

      (def-svtv-to-fsm-thm counter-invar1-fsm-thm8
        :svtv-spec-thmname counter-invar1-svtv-thm
        :eliminate-override-signals :all
        :cycle-num-rewrite-strategy :all-free)

      (def-svtv-to-fsm-thm counter-invar1-fsm-thm9
        :svtv-spec-thmname counter-invar1-svtv-thm
        :cycle-num-rewrite-strategy :single-var)

      (def-svtv-to-fsm-thm counter-invar1-fsm-thm10
        :svtv-spec-thmname counter-invar1-svtv-thm
        ;; BOZO we should only have to specify one of these
        :eliminate-override-vars (sum1)
        :eliminate-override-signals ("sum1")
        :cycle-num-rewrite-strategy :single-var)

      (def-svtv-to-fsm-thm counter-invar1-fsm-thm11
        :svtv-spec-thmname counter-invar1-svtv-thm
        :eliminate-override-vars :all
        :cycle-num-rewrite-strategy :single-var)

      (def-svtv-to-fsm-thm counter-invar1-fsm-thm12
        :svtv-spec-thmname counter-invar1-svtv-thm
        :eliminate-override-signals :all
        :cycle-num-rewrite-strategy :single-var))))
))

(make-event *counter-invar1-events*)
(make-event
 (acl2::template-subst-top (remove-initial-state-vars *counter-invar1-events*)
                           (acl2::make-tmplsubst :strs '(("INVAR1" . "INVAR1A"))
                                                 :pkg-sym 'sv-package)))


(defconst *counter-invar2-events*
  '(progn
                             
(defsvtv$ counter-invar2-run
  :design *sv-design*
  :cycle-phases (list (make-svtv-cyclephase :constants '(("clk" . 1)))
                      (make-svtv-cyclephase :constants '(("clk" . 0))
                                            :inputs-free t
                                            :outputs-captured t))
  ;; :initial-state-vars t
  :stages ((:label curr
            :inputs (("inc" inc)
                     ("reset" 0))
            :overrides (("sum" sum :cond sum-ovr :output sum-prev)
                        ("sum1" 5)))
           (:label next
            :outputs (("sum" sum-out)
                      ("sum1" sum1-out)))))

(encapsulate nil
  (local (include-book "svtv-to-fsm"))
  (local (include-book "svtv-generalize"))

  (local (def-svtv-data-export counter-invar2-run-data))
  (make-event
   '(progn
      (def-svtv-refinement counter-invar2-run counter-invar2-run-data
        :svtv-spec counter-invar2-spec
        :fsm counter-fsm
        :phase-fsm counter-phase-fsm
        :inclusive-overridekeys t)



      (def-svtv-generalized-thm counter-invar2-svtv-thm
        :svtv counter-invar2-run
        :svtv-spec counter-invar2-spec
        :input-vars :all
        :output-vars (sum-out sum1-out)
        :unsigned-byte-hyps t
        :override-vars (sum)
        :spec-override-vars ()
        :hyp (and (<= sum 11)
                  ;; (<= sum1 10)
                  )
        :concl (and (<= sum-out 11)
                    (<= sum1-out 10)))

      (def-svtv-to-fsm-thm counter-invar2-fsm-thm
        :svtv-spec-thmname counter-invar2-svtv-thm)

      (def-svtv-to-fsm-thm counter-invar2-fsm-thm2
        :svtv-spec-thmname counter-invar2-svtv-thm
        :eliminate-override-signals ("sum1"))

      (def-svtv-to-fsm-thm counter-invar2-fsm-thm3
        :svtv-spec-thmname counter-invar2-svtv-thm
        :eliminate-override-vars :all)

      (def-svtv-to-fsm-thm counter-invar2-fsm-thm4
        :svtv-spec-thmname counter-invar2-svtv-thm
        :eliminate-override-signals :all))))

))

(make-event *counter-invar2-events*)
(make-event
 (acl2::template-subst-top (remove-initial-state-vars *counter-invar2-events*)
                           (acl2::make-tmplsubst :strs '(("INVAR2" . "INVAR2A"))
                                                 :pkg-sym 'sv-package)))
