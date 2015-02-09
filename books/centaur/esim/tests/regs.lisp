; ESIM Symbolic Hardware Simulator
; Copyright (C) 2008-2015 Centaur Technology
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
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "common" :ttags :all)

(defmodules *translation*
  (vl2014::make-vl-loadconfig :start-files (list "regs.v")))

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
 (vl2014::vl-modulelist->names
  (vl2014::vl-design->mods
   (vl2014::vl-translation->good *translation*))))

(value-triple
 (vl2014::vl-modulelist->names
  (vl2014::vl-design->mods
   (vl2014::vl-translation->bad *translation*))))

#||
;; to debug some problematic module

(vl2014::vl-pps-module
 (vl2014::vl-find-module "mreg5$width=1"
                     (vl2014::vl-translation->failmods *translation*)))

(top-level
 (vl2014::vl-cw-ps-seq
  (vl2014::vl-print-warnings
   (vl2014::vl-module->warnings
    (vl2014::vl-find-module "mreg5$width=1"
                        (vl2014::vl-translation->failmods *translation*))))))

||#


(with-output :off (event summary)
  (make-event
   (cons 'progn (acl2::esims-to-defconsts-fn
                 (vl2014::vl-modulelist->esims
                  (vl2014::vl-design->mods
                   (vl2014::vl-translation->good *translation*)))))))

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


