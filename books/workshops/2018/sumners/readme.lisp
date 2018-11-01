#| readme.lisp

IMPORTANT NOTE for building exsim: these books require some "latest" changes to
the ipasir library under acl2/books/centaur/ipasir/ .. if you don't have
these changes, these books will not compile. If it does not build, please
copy over the files in new-ipasir subdirectory over to your
acl2/books/centaur/ipasir/ directory. Note also that you do NOT have to
actually have an external IPASIR incremental SAT library installed to build and
run exsim (it's default mode uses normal SAT through SATLINK), but you do need
the ipasir-logic.lisp book to build and certify in order to certify the exsim
books here.

--------------------

This is a simple "script" for loading and running exsim through the included examples:

  toy.v -- a totally trivial little block of logic from the paper
  alu.v -- the simple ALU from SV tutorial with a little spec to check
  smq.v -- a more substantial read/write queue with a check for deadlock

The (exsim "<module>") calls below will read the <module>.v file source,
build the aignet and initialize the signal tables based on reading the
<module>.vcd.. It will then search for any states where the "fail_out"
signal goes to 1 and then produce a <module>_out.vcd file (which one
could load using "gtkwave <module>_out.vcd" to view the result).

|#

(in-package "EXSIM")
(include-book "oslib/ls" :dir :system)
(include-book "exa")
(include-book "exsim")
(include-book "extra")

; NOTE -- commenting out the following forms because they apparently can fail
; on machines for running regressions for ACL2 submissions and I have not
; figured out how the difference in setup may effect this.. 

;(defconsts (*toy* state) (vl->sv-design "toy"))
;(defconsts (*alu* state) (vl->sv-design "alu"))
;(defconsts (*smq* state) (vl->sv-design "smq"))

;(defconsts (*toy-done* state) (exsim "toy" *toy*))
;(defconsts (*alu-done* state) (exsim "alu" *alu*))
;(defconsts (*smq-done* state) (exsim "smq" *smq*))

;; Include the following (after building with ipasir installed:
;;  (include-book "centaur/ipasir/ipasir-backend" :dir :system)
;;
;; Optionally can include the following if one has extended the ipasir SAT library:
;;  (include-book "centaur/ipasir/ipasir-backend-extra" :dir :system)
;;
;; Then you can use the following to run with ipasir enabled:
;;
;; (defconst *ipasir-s-p* (change-sim-params *def-sim-params*
;;                                          :enable-fraig   t
;;                                          :use-satlink    nil
;;                                          :free-var-focus 10
;;                                          :min-clauses    1000
;;                                          :mid-clauses    5000
;;                                          :max-clauses    10000))
;;
;; (exsim "toy" *toy* :sim-params *ipasir-s-p*)
;; (exsim "alu" *alu* :sim-params *ipasir-s-p*)
;; (exsim "smq" *smq* :sim-params *ipasir-s-p*)

