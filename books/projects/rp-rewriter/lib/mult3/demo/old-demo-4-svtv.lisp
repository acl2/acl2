
; Original Author(s):
; Mertcan Temel         <mert.temel@intel.com>

;; This  file gives  an alternative  way to  verify multiplier  with SVTV.  The
;; example here  may seem to  have more intricate  steps but this  scheme works
;; very well with industrial multipliers  embedded in much more complex designs
;; while delivering  a final correctness  theorem with the  unmodified svtv-run
;; instance of the  input design (in demo-3,  the final theorem is  in terms of
;; the modified svtv-run instance of a design with replaced adders).

;; This demo  shows how  this tool  can be  used to  verify a  multiplier module
;; translated with defsvtv. This is done by overriding the adder modules in the
;; original design before calling defsvtv.

;; In this verification flow given in  this demo file, we first create svtv-run
;; instance of the  target design we want  to verify.  Since we  want to easily
;; identify adder  modules used in  the multiplier, we create  another svtv-run
;; instance but this time we override  the definition of adder modules with the
;; ones we favor. Then we verify  the multiplier with overriden adders.  We use
;; FRAIGing and  a SAT solver  to prove the  original unmodified design  to the
;; modified one, and  we use these two  lemmas to derive our  final lemma about
;; the correctness of the original design.

;; In  this  file,  we  repeat  the same  multiplier  proof  from  demo-1.lisp:
;; DT_SB4_HC_64_64_multgen.sv (64x64 Signed, Booth radix-4 encoded, Dadda Tree)

(in-package "RP")

;; To load the verilog designs:
(include-book "centaur/sv/top" :dir :system) ;; a big book; takes around 30 seconds
(include-book "centaur/vl/loader/top" :dir :system) ;; takes around 10 seconds
(include-book "oslib/ls" :dir :system)

(value-triple (acl2::set-max-mem (* 10 (expt 2 30))))

(set-waterfall-parallelism nil)

;; for correctness proof of multiplier
(include-book "projects/rp-rewriter/lib/mult3/svtv-top" :dir :system)

;; Load VL Design.
(acl2::defconsts
  (*original-mult1-vl-design* state)
  (b* (((mv loadresult state)
        (vl::vl-load (vl::make-vl-loadconfig
                      :start-files '("DT_SB4_HC_64_64_multgen.sv")))))
    (mv (vl::vl-loadresult->design loadresult) state)))

;; Load SV design.
(acl2::defconsts
  (*original-mult1-sv-design*)
  (b* (((mv errmsg sv-design & &)
        (vl::vl-design->sv-design "DT_SB4_HC_64_64"
                                  *original-mult1-vl-design*
                                  (vl::make-vl-simpconfig))))
    (and errmsg
         (acl2::raise "~@0~%" errmsg))
    sv-design))

;; We   cannot    use   our    tool   on   a    test   vector    created   with
;; *original-mult1-sv-design*  because the  adder  modules in  this design  get
;; mixed up  with each other  when flattened.  So  we will create  another test
;; vector whose adder modules will be distinguishable from rest of the circuit.
;; For that, we  created alternative versions of the adder  modules used in the
;; input multiplier design,  and saved them in  "adders_with_plus.sv".  The new
;; definitions of these  adder modules ("ha", "fa", and  "HC_128") only consist
;; of the "+" operator.   Pay attention to the definition of  "ha"; there is an
;; extra, redundant "+ 0" term. This is a work-around to a strange problem, and
;; it can be vital to some proofs.

;; Load VL Design again for the same  design but this time override the adders.
;; When VL is parsing  the given files, if it encounters  a redefitinition of a
;; module, it  ignores it and retains  the first definition.  Therefore  in the
;; below  event,   the  redefined  adders  in   adders_with_plus.sv  will  take
;; precedence and the  definitions of the adders as given  in the target design
;; will be  ignored. So we will  be able to  get a multiplier whose  adders are
;; defined with +.
(acl2::defconsts
  (*modified-mult1-vl-design* state)
  (b* (((mv loadresult state)
        (vl::vl-load (vl::make-vl-loadconfig
                      :start-files '("adders_with_plus.sv"
                                     "DT_SB4_HC_64_64_multgen.sv")))))
    (mv (vl::vl-loadresult->design loadresult) state)))

;; Load SV design.
(acl2::defconsts
  (*modified-mult1-sv-design*)
  (b* (((mv errmsg sv-design & &)
        (vl::vl-design->sv-design "DT_SB4_HC_64_64"
                                  *modified-mult1-vl-design*
                                  (vl::make-vl-simpconfig))))
    (and errmsg
         (acl2::raise "~@0~%" errmsg))
    sv-design))

;; Create a test vector with the new sv-design
(sv::defsvtv modified-mult1-svtv
  :mod *modified-mult1-sv-design*
  :inputs '(("IN1" a)
            ("IN2" b))
  :outputs
  '(("result" res)))

;; prove  that the  new test-vector  is correct.  This should  take around  1-2
;; seconds
(local
 (defthmrp multiplier-correct-for-the-modified-svtv
  (implies (and (integerp in1)
                (integerp in2))
           (equal (sv::svtv-run (modified-mult1-svtv)
                                `((a . ,in1)
                                  (b . ,in2)))
                  `((res . ,(loghead 128 (* (logext 64 in1)
                                            (logext 64 in2)))))))))

;; Now let's prove the equivalance of the original design:

;; Create svtv for the unmodified design:
(sv::defsvtv  mult1-svtv
  :mod *original-mult1-sv-design*
  :inputs '(("IN1" a)
            ("IN2" b))
  :outputs
  '(("result" res)))





;; We will use FGL and FRAIGging to prove equivalance. This assumes that IPASIR
;; shared library is set  up and glucose is in the PATH.  Please see doc topic:
;; ipasir::building-an-ipasir-solver-library. You may  install glucose from web
;; or simply change  the sat-config below to woth with  whatever SAT solver you
;; have.


;; Below includes the necessary books and makes some configurations.
;; Including these books can take some time.
(local (include-book "centaur/fgl/top" :dir :system))
(local (include-book "centaur/ipasir/ipasir-backend" :dir :system))
(local (include-book "centaur/aignet/transforms" :dir :system))
(local (defun transforms-config ()
         (declare (Xargs :guard t))
         #!aignet
         (list (make-observability-config)
               (make-balance-config :search-higher-levels t
                                    :search-second-lit t)
               (change-fraig-config *fraig-default-config*
                                    :random-seed-name 'my-random-seed
                                    :ctrex-queue-limit 32
                                    :sim-words 1
                                    :ctrex-force-resim nil
                                    :ipasir-limit 1))))
(local (defattach fgl::fgl-aignet-transforms-config transforms-config))

(local (define monolithic-sat-with-transforms ()
         (fgl::make-fgl-satlink-monolithic-sat-config :transform t)))
(local (defattach fgl::fgl-toplevel-sat-check-config monolithic-sat-with-transforms))

(local
 (progn
   (defun my-sat-config ()
     (declare (xargs :guard t))
     (satlink::make-config :cmdline "glucose "
                           :verbose t
                           :mintime 1/2
                           :remove-temps t))
   (defattach fgl::fgl-satlink-config my-sat-config)))

(value-triple (acl2::tshell-ensure))


;; This should take around 3 seconds. 
(local
 (fgl::def-fgl-thm modified-and-original-svtv-equivalence
   (implies (and (unsigned-byte-p 64 in1) ;; for FGL the inputs need to be bounded 
                 (unsigned-byte-p 64 in2))
            (equal (sv::svtv-run (mult1-svtv)
                                 `((a . ,in1)
                                   (b . ,in2)))
                   (sv::svtv-run (modified-mult1-svtv)
                                 `((a . ,in1)
                                   (b . ,in2)))))))


;; Now we state the final correctness theorem. The lemmas we proved above
;; (modified-and-original-svtv-equivalence and
;; multiplier-correct-for-the-modified-svtv) will be used as rewrite rules to
;; prove this lemma.
(defthm multiplier-is-correct
  (implies (and (unsigned-byte-p 64 in1)
                (unsigned-byte-p 64 in2))
           (equal (sv::svtv-run (mult1-svtv)
                                `((a . ,in1)
                                  (b . ,in2)))
                  `((res . ,(loghead 128 (* (logext 64 in1)
                                            (logext 64 in2)))))))
  :hints (("Goal"
           ;; provide the necessary minimum theory:
           :in-theory '(unsigned-byte-p
                        integer-range-p
                        modified-and-original-svtv-equivalence
                        multiplier-correct-for-the-modified-svtv))))
