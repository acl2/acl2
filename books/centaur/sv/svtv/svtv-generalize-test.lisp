; SV - Symbolic Vector Hardware Analysis Framework
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
; Original author: Sol Swords <sol.swords@intel.com>

(in-package "SV")

; Matt K. mod: Avoid ACL2(p) error from clause-processor that returns a stobj.
(set-waterfall-parallelism nil)

(include-book "svtv-stobj-defsvtv")
(include-book "svtv-generalize-defs")
(local (include-book "centaur/fgl/top" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (in-theory (disable unsigned-byte-p)))
(local (std::remove-default-post-define-hook :fix))

; cert_param: (uses-glucose)

(define simple-lhs ((var svar-p)
                    (width posp))
  :returns (lhs lhs-p)
  (list (make-lhrange :w width :atom (make-lhatom-var :name var :rsh 0))))


(defconst *design*
  (make-design
   :top "mod"
   :modalist
   (list (cons "mod"
               (make-module
                :wires (list (make-wire :name "a-in"  :width 4 :low-idx 0)
                             (make-wire :name "a"     :width 4 :low-idx 0)
                             (make-wire :name "b-in"  :width 4 :low-idx 0)
                             (make-wire :name "b"     :width 4 :low-idx 0)
                             (make-wire :name "op-in" :width 2 :low-idx 0)
                             (make-wire :name "op"    :width 2 :low-idx 0)
                             (make-wire :name "res1"  :width 4 :low-idx 0)
                             (make-wire :name "res2"  :width 4 :low-idx 0)
                             (make-wire :name "res3"  :width 4 :low-idx 0))
                :assigns (list (cons (simple-lhs "a" 4)  (make-driver :value (svex-concat 4 (make-svar :name "a-in" :delay 1) 0)))
                               (cons (simple-lhs "b" 4)  (make-driver :value (svex-concat 4 (make-svar :name "b-in" :delay 1) 0)))
                               (cons (simple-lhs "op" 2) (make-driver :value (svex-concat 2 (make-svar :name "op-in" :delay 1) 0)))
                               (cons (simple-lhs "res1" 4)
                                     (make-driver :value
                                                  (svex-concat 4
                                                               (svcall ? (svcall == (svex-concat 2 "op" 0) 0)
                                                                       (svcall +
                                                                               (svex-concat 4 "a" 0)
                                                                               (svex-concat 4 "b" 0))
                                                                       (svcall ? (svcall == (svex-concat 2 "op" 0) 1)
                                                                               (svcall b-
                                                                                       (svex-concat 4 "a" 0)
                                                                                       (svex-concat 4 "b" 0))
                                                                               (svcall ? (svcall == (svex-concat 2 "op" 0) 2)
                                                                                       (svcall *
                                                                                               (svex-concat 4 "a" 0)
                                                                                               (svex-concat 4 "b" 0))
                                                                                       (svex-x))))
                                                               0)))
                               (cons (simple-lhs "res2" 4)
                                     (make-driver :value
                                                  (svex-concat 4
                                                               (svcall ? (svcall == (svex-concat 2 "op" 0) 0)
                                                                       (svcall u- (svex-concat 4 "res1" 0))
                                                                       (svex-concat 4 "res1" 0))
                                                               0)))
                               (cons (simple-lhs "res3" 4)
                                     (make-driver :value
                                                  (svex-concat 4
                                                               (svcall ? (svcall == (svex-concat 2 "op" 0) 0)
                                                                       (svcall *
                                                                               (svex-concat 4 "res2" 0)
                                                                               (svex-concat 4 "res2" 0))
                                                                       (svex-concat 4 "res2" 0))
                                                               0)))))))))



(defsvtv$ mod-run
  :design *design*
  :phases ((:overrides
            (("a" a :cond a-ovr)
             ("b" b :cond b-ovr :output b-out)
             ("op" op :cond op-ovr :output op-out)
             ("res1" res1 :cond res1-ovr :output res1-out)
             ("res2" res2 :cond res2-ovr :output res2))
            :outputs
            (("res3" res3)))))

(def-svtv-data-export mod-run-data)



(value-triple (acl2::tshell-ensure))

(local (include-book "tools/trivial-ancestors-check" :dir :system))
(local (acl2::use-trivial-ancestors-check))


(local (defconst *generalize-test-thms*
         '(progn
            

            (def-svtv-generalized-thm mod-run-res1-correct
              :override-vars (b)
              :spec-override-vars (a)
              :override-var-bindings ((op 0))
              :output-vars (res1-out)
              :unsigned-byte-hyps t
              :concl (equal res1-out (loghead 4 (+ a b))))

            (def-svtv-generalized-thm mod-run-res2-correct
              :override-vars (res1)
              :spec-override-vars (a)
              :override-var-bindings ((op 0))
              :output-vars (res2)
              :unsigned-byte-hyps t
              :concl (equal res2 (loghead 4 (- res1))))


            (def-svtv-generalized-thm mod-run-res3-correct
              :override-vars (res2)
              :spec-override-vars (a)
              :override-var-bindings ((op 0))
              :output-vars (res3)
              :unsigned-byte-hyps t
              :concl (equal res3 (loghead 4 (* res2 res2))))


            (def-svtv-generalized-thm mod-run-res3-compose
              :spec-override-vars (a)
              :override-vars (b)
              :override-var-bindings ((op 0))
              :output-vars (res3)
              :unsigned-byte-hyps t
              :concl (equal res3 (loghead 4 (* (- (loghead 4 (+ a b))) (- (loghead 4 (+ a b))))))
              :no-lemmas t)


            (def-svtv-generalized-thm mod-run-res1-correct-2
              :override-vars (b)
              :spec-override-vars (a)
              :spec-override-var-bindings ((op 0))
              :output-vars (res1-out)
              :unsigned-byte-hyps t
              :concl (equal res1-out (loghead 4 (+ a b))))



            (def-svtv-generalized-thm mod-run-res2-correct-2
              :override-vars (res1)
              :spec-override-vars (a)
              :spec-override-var-bindings ((op 0))
              :output-vars (res2)
              :unsigned-byte-hyps t
              :concl (equal res2 (loghead 4 (- res1))))


            (def-svtv-generalized-thm mod-run-res3-correct-2
              :override-vars (res2)
              :spec-override-vars (a)
              :spec-override-var-bindings ((op 0))
              :output-vars (res3)
              :unsigned-byte-hyps t
              :concl (equal res3 (loghead 4 (* res2 res2))))


            (def-svtv-generalized-thm mod-run-res3-compose-2
              :spec-override-vars (a)
              :override-vars (b)
              :spec-override-var-bindings ((op 0))
              :output-vars (res3)
              :unsigned-byte-hyps t
              :concl (equal res3 (loghead 4 (* (- (loghead 4 (+ a b))) (- (loghead 4 (+ a b))))))
              :no-lemmas t)


            (def-svtv-generalized-thm mod-run-res3-integerp-override
              :spec-override-vars (a b)
              :spec-override-var-bindings ((op 0))
              :output-vars (res3)
              :unsigned-byte-hyps t
              :concl (integerp res3)))))

(encapsulate nil
  (local (include-book "svtv-idealize-defs"))
  (local
   (encapsulate nil
     (local (include-book "svtv-generalize"))
     (make-event '(def-svtv-ideal mod-ideal mod-run mod-run-data))

     (table svtv-generalized-thm-defaults :svtv 'mod-run)
     (table svtv-generalized-thm-defaults :ideal 'mod-ideal)

     (make-event *generalize-test-thms*)

     (define mod-run-res3 ((a natp) (b natp))
       (svex-env-lookup 'res3 (mod-ideal-exec `((op-ovr . -1)
                                                (a-ovr . -1)
                                                (b-ovr . -1)
                                                (op . 0)
                                                (a . ,(loghead 4 a))
                                                (b . ,(loghead 4 b)))
                                              '(res3))))

     (make-event '(def-svtv-generalized-thm mod-run-res3-is-mod-run-res3
                    :spec-override-vars (a)
                    :override-vars (b)
                    :spec-override-var-bindings ((op 0))
                    :output-vars (res3)
                    :svtv mod-run
                    :ideal mod-ideal
                    :unsigned-byte-hyps t
                    :concl (equal res3 (mod-run-res3 a b))
                    :lemma-use-ideal t
                    :lemma-defthm defthm
                    :lemma-args (:hints (("goal" :in-theory (enable* mod-run-res3
                                                                     svtv-override-triplemaplist-envs-match-checks-when-variable-free
                                                                     4vec-p-when-integerp
                                                                     (:ruleset svtv-generalized-thm-rules)))))))
     )))



(encapsulate nil
  (local
   (encapsulate nil
     (local (include-book "svtv-generalize"))
     (make-event '(def-svtv-override-thms mod-run mod-run-data))

     (table svtv-generalized-thm-defaults :svtv 'mod-run)

     (make-event *generalize-test-thms*)
     
     (define mod-run-res3 ((a natp) (b natp))
       (svex-env-lookup 'res3 (svtv-run (mod-run)
                                        `((op-ovr . -1)
                                          (a-ovr . -1)
                                          (b-ovr . -1)
                                          (op . 0)
                                          (a . ,(loghead 4 a))
                                          (b . ,(loghead 4 b)))
                                        :include '(res3))))

     (make-event
      '(def-svtv-generalized-thm mod-run-res3-is-mod-run-res3
         :spec-override-vars (a)
         :override-vars (b)
         :spec-override-var-bindings ((op 0))
         :output-vars (res3)
         :svtv mod-run
         :unsigned-byte-hyps t
         :concl (equal res3 (mod-run-res3 a b))
         :lemma-defthm defthm
         :lemma-args (:hints (("goal" :in-theory (enable* mod-run-res3
                                                          svtv-override-triplemaplist-envs-match-checks-when-variable-free
                                                          4vec-p-when-integerp
                                                          (:ruleset svtv-generalized-thm-rules)))))))
     )))

(encapsulate nil
  (local
   (encapsulate nil
     (local (include-book "svtv-generalize"))
     (make-event '(def-svtv-override-thms mod-run mod-run-data :inclusive-overridekeys t))

     (table svtv-generalized-thm-defaults :svtv 'mod-run)

     (make-event *generalize-test-thms*)
     
     (define mod-run-res3 ((a natp) (b natp))
       (svex-env-lookup 'res3 (svtv-run (mod-run)
                                        `((op-ovr . -1)
                                          (a-ovr . -1)
                                          (b-ovr . -1)
                                          (op . 0)
                                          (a . ,(loghead 4 a))
                                          (b . ,(loghead 4 b)))
                                        :include '(res3))))

     (make-event '(def-svtv-generalized-thm mod-run-res3-is-mod-run-res3
       :spec-override-vars (a)
       :override-vars (b)
       :spec-override-var-bindings ((op 0))
       :output-vars (res3)
       :svtv mod-run
       :unsigned-byte-hyps t
       :concl (equal res3 (mod-run-res3 a b))
       :lemma-defthm defthm
       :lemma-args (:hints (("goal" :in-theory (enable* mod-run-res3
                                                        svtv-override-triplemaplist-envs-match-checks-when-variable-free
                                                        4vec-p-when-integerp
                                                        (:ruleset svtv-generalized-thm-rules)))))))
     )))



(encapsulate nil
  (local
   (encapsulate nil
     (local (include-book "svtv-generalize"))
     (make-event '(def-svtv-refinement mod-run mod-run-data :svtv-spec t))

     (table svtv-generalized-thm-defaults :svtv 'mod-run)
     (table svtv-generalized-thm-defaults :svtv-spec 'mod-run-spec)

     (make-event *generalize-test-thms*)
     
     (define mod-run-res3 ((a natp) (b natp))
       :guard-hints (("goal" :in-theory (disable acl2::hons-dups-p)))
       (svex-env-lookup 'res3 (svtv-spec-run (mod-run-spec)
                                        `((op-ovr . -1)
                                          (a-ovr . -1)
                                          (b-ovr . -1)
                                          (op . 0)
                                          (a . ,(loghead 4 a))
                                          (b . ,(loghead 4 b))))))

     (make-event
      '(def-svtv-generalized-thm mod-run-res3-is-mod-run-res3
       :spec-override-vars (a)
       :override-vars (b)
       :spec-override-var-bindings ((op 0))
       :output-vars (res3)
       :svtv mod-run
       :svtv-spec mod-run-spec
       :unsigned-byte-hyps t
       :concl (equal res3 (mod-run-res3 a b))
       :lemma-use-svtv-spec t
       :lemma-defthm defthm
       :lemma-args (:hints (("goal" :in-theory (enable* mod-run-res3
                                                        svtv-override-triplemaplist-envs-match-checks-when-variable-free
                                                        4vec-p-when-integerp
                                                        (:ruleset svtv-generalized-thm-rules)))))))
     )))


(encapsulate nil
  (local
   (encapsulate nil
     (local (include-book "svtv-generalize"))
     (make-event '(def-svtv-refinement mod-run mod-run-data :svtv-spec t :inclusive-overridekeys t))

     (table svtv-generalized-thm-defaults :svtv 'mod-run)
     (table svtv-generalized-thm-defaults :svtv-spec 'mod-run-spec)

     (make-event *generalize-test-thms*)
     
     (define mod-run-res3 ((a natp) (b natp))
       :guard-hints (("goal" :in-theory (disable acl2::hons-dups-p)))
       (svex-env-lookup 'res3 (svtv-spec-run (mod-run-spec)
                                        `((op-ovr . -1)
                                          (a-ovr . -1)
                                          (b-ovr . -1)
                                          (op . 0)
                                          (a . ,(loghead 4 a))
                                          (b . ,(loghead 4 b))))))

     (make-event '(def-svtv-generalized-thm mod-run-res3-is-mod-run-res3
       :spec-override-vars (a)
       :override-vars (b)
       :spec-override-var-bindings ((op 0))
       :output-vars (res3)
       :svtv mod-run
       :svtv-spec mod-run-spec
       :unsigned-byte-hyps t
       :concl (equal res3 (mod-run-res3 a b))
       :lemma-use-svtv-spec t
       :lemma-defthm defthm
       :lemma-args (:hints (("goal" :in-theory (enable* mod-run-res3
                                                        svtv-override-triplemaplist-envs-match-checks-when-variable-free
                                                        4vec-p-when-integerp
                                                        (:ruleset svtv-generalized-thm-rules)))))))
     )))




(defsvtv$ mod-run2
  :design *design*
  :phases ((:overrides
            (("a" a :cond a-ovr)
             ("b" b :cond b-ovr :output b-out)
             ("op" op :cond op-ovr :output op-out)
             ("res1" res1 :cond res1-ovr :output res1-out)
             ("res2" res2 :cond res2-ovr :output res2))
            :outputs
            (("res3" res3)))
           (:overrides
            (("a" a :cond a-ovr)
             ("b" b2 :cond b-ovr2 :output b-out2)
             ("op" op2 :cond op-ovr2 :output op-out2)
             ("res1" res12 :cond res1-ovr2 :output res1-out2)
             ("res2" res22 :cond res2-ovr2 :output res22))
            :outputs
            (("res3" res32)))))

(def-svtv-data-export mod-run2-data)

(encapsulate nil
  (local
   (encapsulate nil
     (local (include-book "svtv-generalize"))
     (make-event '(def-svtv-refinement mod-run2 mod-run2-data :svtv-spec t)))))

(encapsulate nil
  (local
   (encapsulate nil
     (local (include-book "svtv-generalize"))
     (make-event '(def-svtv-refinement mod-run2 mod-run2-data :svtv-spec t :inclusive-overridekeys t)))))



                                                                       
