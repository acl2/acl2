; VL Verilog Toolkit
; Copyright (C) 2008-2013 Centaur Technology
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
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "common")

(defmodules *translation*
  (vl::make-vl-loadconfig :start-files (list "regs.v")))

(defun esims-to-defconsts-fn (esims)
  ;; ESIMS are just a list of ESIM modules like
  ;;    ((:N *foo* ...) (:N *bar* ...))
  ;; Turn each of them into a defconst of its quoted body.
  (if (atom esims)
      nil
    (cons `(defconst ,(gpl :n (car esims))
             ',(car esims))
          (esims-to-defconsts-fn (cdr esims)))))

(value-triple
 (vl::vl-modulelist->names
  (vl::vl-design->mods
   (vl::vl-translation->good *translation*))))

(value-triple
 (vl::vl-modulelist->names
  (vl::vl-design->mods
   (vl::vl-translation->bad *translation*))))

#||
;; to debug some problematic module

(vl::vl-pps-module
 (vl::vl-find-module "mreg5$width=1"
                     (vl::vl-translation->failmods *translation*)))

(top-level
 (vl::vl-cw-ps-seq
  (vl::vl-print-warnings
   (vl::vl-module->warnings
    (vl::vl-find-module "mreg5$width=1"
                        (vl::vl-translation->failmods *translation*))))))

||#


(with-output :off (event summary)
  (make-event
   (cons 'progn (acl2::esims-to-defconsts-fn
                 (vl::vl-modulelist->esims
                  (vl::vl-design->mods
                   (vl::vl-translation->good *translation*)))))))

(defstv e1
  :mod |*ereg1$width=1*|
  :inputs '(("clk" 0 ~)
            ("d"   d0 d1 d2 d3)
            ("en"  e0 e1 e2 e3))
  :outputs '(("q"   q0 q1 q2 q3)))

(defstv e2
  :mod |*ereg2$width=1*|
  :inputs '(("clk" 0 ~)
            ("d"   d0 d1 d2 d3)
            ("en"  e0 e1 e2 e3))
  :outputs '(("q"   q0 q1 q2 q3)))

(defstv e3
  :mod |*ereg3$width=1*|
  :inputs '(("clk" 0 ~)
            ("d"   d0 d1 d2 d3)
            ("en"  e0 e1 e2 e3))
  :outputs '(("q"   q0 q1 q2 q3)))

(defstv e4
  :mod |*ereg4$width=1*|
  :inputs '(("clk" 0 ~)
            ("d"   d0 d1 d2 d3)
            ("en"  e0 e1 e2 e3))
  :outputs '(("q"   q0 q1 q2 q3)))

(defstv e5
  :mod |*ereg5$width=1*|
  :inputs '(("clk" 0 ~)
            ("d"   d0 d1 d2 d3)
            ("en"  e0 e1 e2 e3))
  :outputs '(("q"   q0 q1 q2 q3)))

(defstv e6
  :mod |*ereg6$width=1*|
  :inputs '(("clk" 0 ~)
            ("d"   d0 d1 d2 d3)
            ("en"  e0 e1 e2 e3))
  :outputs '(("q"   q0 q1 q2 q3)))

(def-gl-thm e1-same-as-e2
  :hyp (e1-autohyps)
  :concl (b* ((e1-outs (stv-run (e1) (e1-autoins)))
              (e2-outs (stv-run (e2) (e2-autoins))))
           (and (equal (cdr (assoc 'q0 e1-outs))
                       (cdr (assoc 'q0 e2-outs)))
                (equal (cdr (assoc 'q1 e1-outs))
                       (cdr (assoc 'q1 e2-outs)))
                (equal (cdr (assoc 'q2 e1-outs))
                       (cdr (assoc 'q2 e2-outs)))
                (equal (cdr (assoc 'q3 e1-outs))
                       (cdr (assoc 'q3 e2-outs)))))
  :g-bindings (e1-autobinds))

(def-gl-thm e1-same-as-e3
  :hyp (e1-autohyps)
  :concl (b* ((e1-outs (stv-run (e1) (e1-autoins)))
              (e2-outs (stv-run (e3) (e3-autoins))))
           (and (equal (cdr (assoc 'q0 e1-outs))
                       (cdr (assoc 'q0 e2-outs)))
                (equal (cdr (assoc 'q1 e1-outs))
                       (cdr (assoc 'q1 e2-outs)))
                (equal (cdr (assoc 'q2 e1-outs))
                       (cdr (assoc 'q2 e2-outs)))
                (equal (cdr (assoc 'q3 e1-outs))
                       (cdr (assoc 'q3 e2-outs)))))
  :g-bindings (e1-autobinds))

(def-gl-thm e1-same-as-e4
  :hyp (e1-autohyps)
  :concl (b* ((e1-outs (stv-run (e1) (e1-autoins)))
              (e2-outs (stv-run (e4) (e4-autoins))))
           (and (equal (cdr (assoc 'q0 e1-outs))
                       (cdr (assoc 'q0 e2-outs)))
                (equal (cdr (assoc 'q1 e1-outs))
                       (cdr (assoc 'q1 e2-outs)))
                (equal (cdr (assoc 'q2 e1-outs))
                       (cdr (assoc 'q2 e2-outs)))
                (equal (cdr (assoc 'q3 e1-outs))
                       (cdr (assoc 'q3 e2-outs)))))
  :g-bindings (e1-autobinds))

(def-gl-thm e1-same-as-e5
  :hyp (e1-autohyps)
  :concl (b* ((e1-outs (stv-run (e1) (e1-autoins)))
              (e2-outs (stv-run (e5) (e5-autoins))))
           (and (equal (cdr (assoc 'q0 e1-outs))
                       (cdr (assoc 'q0 e2-outs)))
                (equal (cdr (assoc 'q1 e1-outs))
                       (cdr (assoc 'q1 e2-outs)))
                (equal (cdr (assoc 'q2 e1-outs))
                       (cdr (assoc 'q2 e2-outs)))
                (equal (cdr (assoc 'q3 e1-outs))
                       (cdr (assoc 'q3 e2-outs)))))
  :g-bindings (e1-autobinds))

(def-gl-thm e1-same-as-e6
  :hyp (e1-autohyps)
  :concl (b* ((e1-outs (stv-run (e1) (e1-autoins)))
              (e2-outs (stv-run (e6) (e6-autoins))))
           (and (equal (cdr (assoc 'q0 e1-outs))
                       (cdr (assoc 'q0 e2-outs)))
                (equal (cdr (assoc 'q1 e1-outs))
                       (cdr (assoc 'q1 e2-outs)))
                (equal (cdr (assoc 'q2 e1-outs))
                       (cdr (assoc 'q2 e2-outs)))
                (equal (cdr (assoc 'q3 e1-outs))
                       (cdr (assoc 'q3 e2-outs)))))
  :g-bindings (e1-autobinds))







(defstv e1.4
  :mod |*ereg1$width=4*|
  :inputs '(("clk" 0 ~)
            ("d"   d0 d1 d2 d3)
            ("en"  e0 e1 e2 e3))
  :outputs '(("q"   q0 q1 q2 q3)))

(defstv e2.4
  :mod |*ereg2$width=4*|
  :inputs '(("clk" 0 ~)
            ("d"   d0 d1 d2 d3)
            ("en"  e0 e1 e2 e3))
  :outputs '(("q"   q0 q1 q2 q3)))

(defstv e3.4
  :mod |*ereg3$width=4*|
  :inputs '(("clk" 0 ~)
            ("d"   d0 d1 d2 d3)
            ("en"  e0 e1 e2 e3))
  :outputs '(("q"   q0 q1 q2 q3)))

(defstv e4.4
  :mod |*ereg4$width=4*|
  :inputs '(("clk" 0 ~)
            ("d"   d0 d1 d2 d3)
            ("en"  e0 e1 e2 e3))
  :outputs '(("q"   q0 q1 q2 q3)))

(defstv e5.4
  :mod |*ereg5$width=4*|
  :inputs '(("clk" 0 ~)
            ("d"   d0 d1 d2 d3)
            ("en"  e0 e1 e2 e3))
  :outputs '(("q"   q0 q1 q2 q3)))

(defstv e6.4
  :mod |*ereg6$width=4*|
  :inputs '(("clk" 0 ~)
            ("d"   d0 d1 d2 d3)
            ("en"  e0 e1 e2 e3))
  :outputs '(("q"   q0 q1 q2 q3)))

(def-gl-thm e1.4-same-as-e2.4
  :hyp (e1.4-autohyps)
  :concl (b* ((e1-outs (stv-run (e1.4) (e1.4-autoins)))
              (e2-outs (stv-run (e2.4) (e2.4-autoins))))
           (and (equal (cdr (assoc 'q0 e1-outs))
                       (cdr (assoc 'q0 e2-outs)))
                (equal (cdr (assoc 'q1 e1-outs))
                       (cdr (assoc 'q1 e2-outs)))
                (equal (cdr (assoc 'q2 e1-outs))
                       (cdr (assoc 'q2 e2-outs)))
                (equal (cdr (assoc 'q3 e1-outs))
                       (cdr (assoc 'q3 e2-outs)))))
  :g-bindings (e1.4-autobinds))

(def-gl-thm e1.4-same-as-e3.4
  :hyp (e1.4-autohyps)
  :concl (b* ((e1-outs (stv-run (e1.4) (e1.4-autoins)))
              (e2-outs (stv-run (e3.4) (e3.4-autoins))))
           (and (equal (cdr (assoc 'q0 e1-outs))
                       (cdr (assoc 'q0 e2-outs)))
                (equal (cdr (assoc 'q1 e1-outs))
                       (cdr (assoc 'q1 e2-outs)))
                (equal (cdr (assoc 'q2 e1-outs))
                       (cdr (assoc 'q2 e2-outs)))
                (equal (cdr (assoc 'q3 e1-outs))
                       (cdr (assoc 'q3 e2-outs)))))
  :g-bindings (e1.4-autobinds))

(def-gl-thm e1.4-same-as-e4.4
  :hyp (e1.4-autohyps)
  :concl (b* ((e1-outs (stv-run (e1.4) (e1.4-autoins)))
              (e2-outs (stv-run (e4.4) (e4.4-autoins))))
           (and (equal (cdr (assoc 'q0 e1-outs))
                       (cdr (assoc 'q0 e2-outs)))
                (equal (cdr (assoc 'q1 e1-outs))
                       (cdr (assoc 'q1 e2-outs)))
                (equal (cdr (assoc 'q2 e1-outs))
                       (cdr (assoc 'q2 e2-outs)))
                (equal (cdr (assoc 'q3 e1-outs))
                       (cdr (assoc 'q3 e2-outs)))))
  :g-bindings (e1.4-autobinds))

(def-gl-thm e1.4-same-as-e5.4
  :hyp (e1.4-autohyps)
  :concl (b* ((e1-outs (stv-run (e1.4) (e1.4-autoins)))
              (e2-outs (stv-run (e5.4) (e5.4-autoins))))
           (and (equal (cdr (assoc 'q0 e1-outs))
                       (cdr (assoc 'q0 e2-outs)))
                (equal (cdr (assoc 'q1 e1-outs))
                       (cdr (assoc 'q1 e2-outs)))
                (equal (cdr (assoc 'q2 e1-outs))
                       (cdr (assoc 'q2 e2-outs)))
                (equal (cdr (assoc 'q3 e1-outs))
                       (cdr (assoc 'q3 e2-outs)))))
  :g-bindings (e1.4-autobinds))

(def-gl-thm e1.4-same-as-e6.4
  :hyp (e1.4-autohyps)
  :concl (b* ((e1-outs (stv-run (e1.4) (e1.4-autoins)))
              (e2-outs (stv-run (e6.4) (e6.4-autoins))))
           (and (equal (cdr (assoc 'q0 e1-outs))
                       (cdr (assoc 'q0 e2-outs)))
                (equal (cdr (assoc 'q1 e1-outs))
                       (cdr (assoc 'q1 e2-outs)))
                (equal (cdr (assoc 'q2 e1-outs))
                       (cdr (assoc 'q2 e2-outs)))
                (equal (cdr (assoc 'q3 e1-outs))
                       (cdr (assoc 'q3 e2-outs)))))
  :g-bindings (e1.4-autobinds))



(defstv m1
  :mod |*mreg1$width=1*|
  :inputs '(("clk"  0   ~)
            ("sel"  s0  s1  s2  s3)
            ("d0"   d0a d0b d0c d0d)
            ("d1"   d1a d1b d1c d1d)
            ("en"   e0  e1  e2  e3))
  :outputs '(("q"   q0  q1  q2  q3)))

(defstv m2
  :mod |*mreg2$width=1*|
  :inputs '(("clk"  0   ~)
            ("sel"  s0  s1  s2  s3)
            ("d0"   d0a d0b d0c d0d)
            ("d1"   d1a d1b d1c d1d)
            ("en"   e0  e1  e2  e3))
  :outputs '(("q"   q0  q1  q2  q3)))

(defstv m3
  :mod |*mreg3$width=1*|
  :inputs '(("clk"  0   ~)
            ("sel"  s0  s1  s2  s3)
            ("d0"   d0a d0b d0c d0d)
            ("d1"   d1a d1b d1c d1d)
            ("en"   e0  e1  e2  e3))
  :outputs '(("q"   q0  q1  q2  q3)))

(defstv m4
  :mod |*mreg4$width=1*|
  :inputs '(("clk"  0   ~)
            ("sel"  s0  s1  s2  s3)
            ("d0"   d0a d0b d0c d0d)
            ("d1"   d1a d1b d1c d1d)
            ("en"   e0  e1  e2  e3))
  :outputs '(("q"   q0  q1  q2  q3)))

(defstv m5
  :mod |*mreg5$width=1*|
  :inputs '(("clk"  0   ~)
            ("sel"  s0  s1  s2  s3)
            ("d0"   d0a d0b d0c d0d)
            ("d1"   d1a d1b d1c d1d)
            ("en"   e0  e1  e2  e3))
  :outputs '(("q"   q0  q1  q2  q3)))

(def-gl-thm m1-same-as-m2
  :hyp (m1-autohyps)
  :concl (b* ((e1-outs (stv-run (m1) (m1-autoins)))
              (e2-outs (stv-run (m2) (m2-autoins))))
           (and (equal (cdr (assoc 'q0 e1-outs))
                       (cdr (assoc 'q0 e2-outs)))
                (equal (cdr (assoc 'q1 e1-outs))
                       (cdr (assoc 'q1 e2-outs)))
                (equal (cdr (assoc 'q2 e1-outs))
                       (cdr (assoc 'q2 e2-outs)))
                (equal (cdr (assoc 'q3 e1-outs))
                       (cdr (assoc 'q3 e2-outs)))))
  :g-bindings (m1-autobinds))

(def-gl-thm m1-same-as-m3
  :hyp (m1-autohyps)
  :concl (b* ((e1-outs (stv-run (m1) (m1-autoins)))
              (e2-outs (stv-run (m3) (m3-autoins))))
           (and (equal (cdr (assoc 'q0 e1-outs))
                       (cdr (assoc 'q0 e2-outs)))
                (equal (cdr (assoc 'q1 e1-outs))
                       (cdr (assoc 'q1 e2-outs)))
                (equal (cdr (assoc 'q2 e1-outs))
                       (cdr (assoc 'q2 e2-outs)))
                (equal (cdr (assoc 'q3 e1-outs))
                       (cdr (assoc 'q3 e2-outs)))))
  :g-bindings (m1-autobinds))

(def-gl-thm m1-same-as-m4
  :hyp (m1-autohyps)
  :concl (b* ((e1-outs (stv-run (m1) (m1-autoins)))
              (e2-outs (stv-run (m4) (m4-autoins))))
           (and (equal (cdr (assoc 'q0 e1-outs))
                       (cdr (assoc 'q0 e2-outs)))
                (equal (cdr (assoc 'q1 e1-outs))
                       (cdr (assoc 'q1 e2-outs)))
                (equal (cdr (assoc 'q2 e1-outs))
                       (cdr (assoc 'q2 e2-outs)))
                (equal (cdr (assoc 'q3 e1-outs))
                       (cdr (assoc 'q3 e2-outs)))))
  :g-bindings (m1-autobinds))


(def-gl-thm m1-same-as-m5
  :hyp (m1-autohyps)
  :concl (b* ((e1-outs (stv-run (m1) (m1-autoins)))
              (e2-outs (stv-run (m5) (m5-autoins))))
           (and (equal (cdr (assoc 'q0 e1-outs))
                       (cdr (assoc 'q0 e2-outs)))
                (equal (cdr (assoc 'q1 e1-outs))
                       (cdr (assoc 'q1 e2-outs)))
                (equal (cdr (assoc 'q2 e1-outs))
                       (cdr (assoc 'q2 e2-outs)))
                (equal (cdr (assoc 'q3 e1-outs))
                       (cdr (assoc 'q3 e2-outs)))))
  :g-bindings (m1-autobinds))


