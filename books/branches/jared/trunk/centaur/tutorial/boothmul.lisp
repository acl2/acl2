; Centaur Hardware Verification Tutorial
; Copyright (C) 2012 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Sol Swords <sswords@centtech.com>
;                  Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "intro")
(include-book "centaur/gl/bfr-satlink" :dir :system)
(include-book "booth-support")
(value-triple (set-max-mem (* 3 (expt 2 30))))
(value-triple (tshell-ensure))
; cert_param: (hons-only)

(make-event

; Disabling waterfall parallelism for unknown reasons other than that
; certification stalls out with it enabled.

 (if (and (hons-enabledp state)
          (f-get-global 'parallel-execution-enabled state))
     (er-progn (set-waterfall-parallelism nil)
               (value '(value-triple nil)))
   (value '(value-triple nil))))

; (depends-on "boothmul.v")
(defmodules *boothmul-translation*
  (vl::make-vl-loadconfig
   :start-files (list "boothmul.v")))

(defconst *boothmul*
  (b* ((mods  (vl::vl-translation->mods *boothmul-translation*))
       (boothmul (vl::vl-find-module "boothmul" mods))
       ((unless boothmul)
        (er hard? '*boothmul* "Failed to translate boothmul?"))
       (esim  (vl::vl-module->esim boothmul))
       ((unless (good-esim-modulep esim))
        (er hard? '*boothmul* "Failed to produce a good esim module")))
    esim))

(defstv boothmul-direct
  :mod *boothmul*
  :inputs '(("a"   a)
            ("b"   b))
  :outputs '(("o"    o))
  :parents (esim-tutorial) ;; xdoc stuff, not needed
  )

;; This is becoming UNTENABLE
;; (def-gl-thm boothmul-correct-direct
;;   :hyp (boothmul-direct-autohyps)
;;   :concl (b* ((in-alist  (boothmul-direct-autoins))
;;               (out-alist (stv-run (boothmul-direct) in-alist))
;;               (o         (cdr (assoc 'o out-alist))))
;;            (equal o (* a b)))
;;   :g-bindings (boothmul-direct-autobinds)
;;   :rule-classes nil)

;; (stv-run (boothmul-direct) (list (cons 'a 3)
;;                             (cons 'b 5)))


(gl::gl-satlink-mode)

(defstv boothmul-decomp
  :mod *boothmul*
  :inputs '(("a"   a)
            ("b"   b))
  :outputs '(("o"    o))
  :internals '(("minusb" minusb)
               ("temp_1" temp1))
  :overrides '(("pp0" pp0)
               ("pp1" pp1)
               ("pp2" pp2)
               ("pp3" pp3)
               ("pp4" pp4)
               ("pp5" pp5)
               ("pp6" pp6)
               ("pp7" pp7))
  :parents (esim-tutorial) ;; xdoc stuff, not needed
  )


(defun hexify-nums (x)
  (if (atom x)
      (if (natp x)
          (str::hexify x)
        x)
    (cons (hexify-nums (car x))
          (hexify-nums (cdr x)))))


(local
 (progn
   (defun my-glucose-config ()
     (declare (xargs :guard t))
     (satlink::make-config :cmdline "glucose"
                           :verbose t
                           :mintime 1/2
                           :remove-temps t))

   (defattach gl::gl-satlink-config my-glucose-config)))
; cert_param: (uses-glucose)        


(def-gl-thm boothmul-pp-correct
  :hyp (boothmul-decomp-autohyps)
  :concl (b* ((in-alist  (boothmul-decomp-autoins))
              (out-alist (stv-run (boothmul-decomp) in-alist)))
           (and (equal (cdr (assoc 'pp0 out-alist)) (boothmul-pp-spec 16 #x0 a b))
                (equal (cdr (assoc 'pp1 out-alist)) (boothmul-pp-spec 16 #x1 a b))
                (equal (cdr (assoc 'pp2 out-alist)) (boothmul-pp-spec 16 #x2 a b))
                (equal (cdr (assoc 'pp3 out-alist)) (boothmul-pp-spec 16 #x3 a b))
                (equal (cdr (assoc 'pp4 out-alist)) (boothmul-pp-spec 16 #x4 a b))
                (equal (cdr (assoc 'pp5 out-alist)) (boothmul-pp-spec 16 #x5 a b))
                (equal (cdr (assoc 'pp6 out-alist)) (boothmul-pp-spec 16 #x6 a b))
                (equal (cdr (assoc 'pp7 out-alist)) (boothmul-pp-spec 16 #x7 a b))
                ))
  :g-bindings (boothmul-decomp-autobinds))

(def-gl-thm boothmul-sum-correct
  :hyp (boothmul-decomp-autohyps)
  :concl (b* ((in-alist  (boothmul-decomp-autoins))
              (out-alist (stv-run (boothmul-decomp) in-alist))
              (o (cdr (assoc 'o out-alist)))
              (- (cw "o: ~s0~%" (str::hexify o)))
              (res (loghead 32
                            (+ (ash (logext 18 pp0) #x0)
                               (ash (logext 18 pp1) #x2)
                               (ash (logext 18 pp2) #x4)
                               (ash (logext 18 pp3) #x6)
                               (ash (logext 18 pp4) #x8)
                               (ash (logext 18 pp5) #xa)
                               (ash (logext 18 pp6) #xc)
                               (ash (logext 18 pp7) #xe))))
              (- (cw "res: ~s0~%" (str::hexify res))))
           (equal o res))
  :g-bindings (boothmul-decomp-autobinds))


;; these actually slow down the proof below, but cause it to show explicitly
;; how booth-sum-impl is expanded into the sum of partial-products that we need
;; below in booth-sum-of-products-correct.
(local (defund unhide (x) x))
(local (defthm unhide-hide
         (equal (unhide (hide x)) x)
         :hints (("goal" :in-theory (enable unhide)
                  :expand ((:free (x) (hide x)))))))
(local (defthm booth-sum-impl-redef
         (equal (booth-sum-impl n i a b sz)
                (IF (ZP N)
                    0
                    (+ (ASH (LOGEXT (+ 2 SZ)
                                    (BOOTHMUL-PP-SPEC SZ I A B))
                            (* 2 I))
                       (unhide (hide (BOOTH-SUM-IMPL (1- N)
                                                     (+ 1 I)
                                                     A B SZ))))))
         :hints(("Goal" :in-theory (enable booth-sum-impl)))))

;; this wouldn't be a GL theorem, typically, at least for large N
;; left as a fun arithmetical exercise
(defthm booth-sum-of-products-correct
  (implies (boothmul-direct-autohyps)
           (let ((pp0 (boothmul-pp-spec 16 #x0 a b))
                 (pp1 (boothmul-pp-spec 16 #x1 a b))
                 (pp2 (boothmul-pp-spec 16 #x2 a b))
                 (pp3 (boothmul-pp-spec 16 #x3 a b))
                 (pp4 (boothmul-pp-spec 16 #x4 a b))
                 (pp5 (boothmul-pp-spec 16 #x5 a b))
                 (pp6 (boothmul-pp-spec 16 #x6 a b))
                 (pp7 (boothmul-pp-spec 16 #x7 a b)))
             (equal (+ (ash (logext 18 pp0) #x0)
                       (ash (logext 18 pp1) #x2)
                       (ash (logext 18 pp2) #x4)
                       (ash (logext 18 pp3) #x6)
                       (ash (logext 18 pp4) #x8)
                       (ash (logext 18 pp5) #xa)
                       (ash (logext 18 pp6) #xc)
                       (ash (logext 18 pp7) #xe))
                    (* (logext 16 a)
                       (logext 16 b)))))
  :hints (("goal" :use ((:instance booth-sum-impl-is-multiply
                         (n 8) (sz 16)))
           :in-theory (e/d ()
                           (booth-sum-impl-is-multiply
                            ash
                            signed-byte-p
                            boothmul-pp-spec)))))


;; ideally we'd do this as a theorem solely about sexpr composition, but AIG
;; mode works pretty well too and is easier
(def-gl-thm boothmul-decomp-is-boothmul
  :hyp (boothmul-decomp-autohyps)
  :concl (b* ((in-alist1 (boothmul-decomp-autoins))
              (out-alist1 (stv-run (boothmul-decomp) in-alist1))
              ((assocs pp0
                       pp1
                       pp2
                       pp3
                       pp4
                       pp5
                       pp6
                       pp7) out-alist1)
              (in-alist2 (boothmul-decomp-autoins))
              (out-alist2 (stv-run (boothmul-decomp) in-alist2))
              (orig-in-alist (boothmul-direct-autoins))
              (orig-out-alist (stv-run (boothmul-direct) orig-in-alist)))
           (equal (cdr (assoc 'o out-alist2))
                  (cdr (assoc 'o orig-out-alist))))
  :g-bindings (boothmul-decomp-autobinds))


(defthm boothmul-pp-spec-bound
  (< (boothmul-pp-spec 16 i a b) (expt 2 18))
  :hints(("Goal" :in-theory (enable boothmul-pp-spec)))
  :rule-classes :linear)

(defthm boothmul-correct
  (implies (boothmul-direct-autohyps)
           (b* ((in-alist  (boothmul-direct-autoins))
                (out-alist (stv-run (boothmul-direct) in-alist))
                (o         (cdr (assoc 'o out-alist))))
             (equal o (loghead 32 (* (logext 16 a) (logext 16 b))))))
  :hints (("goal" :in-theory (disable stv-run
                                      (boothmul-direct) boothmul-direct
                                      (boothmul-decomp) boothmul-decomp
                                      boothmul-decomp-is-boothmul
                                      ash-of-n-0
                                      right-shift-to-logtail)
           :use ((:instance boothmul-decomp-is-boothmul
                            (pp0 0)
                            (pp1 0)
                            (pp2 0)
                            (pp3 0)
                            (pp4 0)
                            (pp5 0)
                            (pp6 0)
                            (pp7 0))))))
