(in-package "ACL2")
(set-case-split-limitations 'nil)

(include-book "refinement-sfm06-with-hazards")

;:trans1
(generate-full-system isa-step isa-p ma-step ma-p 
                      ma-to-isa good-ma ma-rank)


(include-book "acl2s/cgen/top" :dir :system :ttags :all)

;----------Data definitions----------------------------------
(defdata reg acl2s::nat)
(defdata pc-type acl2s::nat)
(defdata data integer)
(defdata register (map reg data))

(defun boolp (x)
   (declare (xargs :guard t))
  (booleanp x))

(defun bool-enum (x)
  (if (> x 100) t nil))

(acl2s::register-type bool :predicate boolp :enumerator bool-enum)

(defdata dmemory (map acl2s::nat data))
                      

(defdata operation-code (oneof 'add 'sub 'mul 'load 'loadi 'store 'bez 'jump))

       
(defdata inst (record (opcode . operation-code)
                      (rc . reg)
                      (ra . reg)
                      (rb . reg)))

(defdata imemory (map pc-type inst))

(defdata ISA-type 'ISA)

(defdata ISA-testing (record 
                      (type . ISA-type)
                      (pc . pc-type)
                      (regs . register)
                      (imem . imemory)
                      (dmem . dmemory)))


(acl2s::register-type ISA :enumerator nth-ISA-testing :predicate ISA-p) 

(defdata latch1-type 'latch1)
(defdata latch1-testing (record (type . latch1-type)
                        (validp . bool)
                        (op . operation-code)
                        (rc . reg)
                        (ra . reg)
                        (rb . reg)
                        (pch . pc-type)))

;(acl2s::register-type latch1 :enumerator nth-latch1-testing :predicate latch1p) 

(defdata latch2-type 'latch2)
(defdata latch2-testing (record (type . latch2-type)
                                (validp . bool)
                                (op . operation-code)
                                (rc . reg)
                                (ra-val . data)
                                (rb-val . data)
                                (pch . pc-type)))

;(acl2s::register-type latch2 :enumerator nth-latch2-testing :predicate latch2p) 

(defdata MA-type 'MA)
(defdata MA-testing (record  (type . MA-type)
                              (pc . pc-type)
                              (regs . register)
                              (imem . imemory)
                              (dmem . dmemory)
                              (latch1 . latch1-testing)
                              (latch2 . latch2-testing)))

(acl2s::register-type MA :enumerator nth-MA-testing :predicate MA-p)

(in-theory (disable pc-typep regp))


:set-ignore-ok t
(acl2s-defaults :set num-witnesses 0)
(acl2s-defaults :set num-counterexamples 1)
(acl2s-defaults :set testing-enabled T)
(acl2s-defaults :set search-strategy :incremental)
(acl2s-defaults :set use-fixers nil)
(in-theory (disable operation-codep ACL2::NON-NIL-IF-MGET-NON-NIL))
(acl2s-defaults :set sampling-method :random)
(acl2s-defaults :set backtrack-limit 1)
(in-theory (disable boolp))
(acl2s-defaults :set verbosity-level 2)
(acl2s-defaults :set num-trials 50)
(acl2s-defaults :set cgen-local-timeout 2)


(defthm cgen-support
  (implies (and (registerp r)
                (regp a1)
                (regp a2))
           (equal (mget a1 (mset a2 v r))
                  (if (not (equal a1 a2))
                    (mget a1 r)
                    v))))

(set-inhibit-warnings "invariant-risk")

(thm ;B-IS-A-WF-BISIM-CORE
  (LET ((U (ISA-STEP S)) (V (MA-STEP W)))
       (IMPLIES (AND
                 (ISA-P S)
                 (MA-P W)
                 (MA-testingp W)
                 (ISA-P U)
                 (MA-P V)
                 (WF-REL S W))
            (OR (WF-REL U V)
                (WF-REL S V)))))
   
