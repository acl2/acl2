(include-book "acl2s/cgen/top" :dir :system :ttags :all)
(in-package "ACL2S")

(defdata reg nat)
(defdata program-counter nat)
(defdata register (map reg integer))


(defdata operation-code 
  (enum '(add sub mul load loadi store bez jump)))

(in-theory (disable operation-codep))

(defdata dmemory (map nat integer))


(defdata inst (record (opcode . operation-code)
                      (rc . reg)
                      (ra . reg)
                      (rb . reg)))


(defdata imemory (map nat inst))



(defdata ISA (record (pc . program-counter)
                     (regs . register)
                     (imem . imemory)
                     (dmem . dmemory)))

(defdata latch1 (record (validp . boolean)
                        (op . operation-code)
                        (rc . reg)
                        (ra . reg)
                        (rb . reg)
                        (pch . program-counter)))

(defdata latch2 (record (validp . boolean)
                        (op . operation-code)
                        (rc . reg)
                        (ra-val . integer)
                        (rb-val . integer)
                        (pch . program-counter)))

(defdata MAA (record  (pc . program-counter)
                      (regs . register)
                      (imem . imemory)
                      (dmem . dmemory)
                      (ltch1 . latch1)
                      (ltch2 . latch2)))

(acl2s-defaults :set num-witnesses 0)
(acl2s-defaults :set num-counterexamples 1)
(acl2s-defaults :set num-trials 100)
(acl2s-defaults :set verbosity-level 2)
(acl2s-defaults :set search-strategy :incremental)

(set-inhibit-warnings "invariant-risk")

(in-theory (disable operation-codep ACL2::NON-NIL-IF-MGET-NON-NIL))
(acl2s-defaults :set backtrack-limit 0)#|ACL2s-ToDo-Line|#


;Here is one of the ~1000 subgoals which failed:

(test?
 (implies 
  (and (maap w)
       (equal (mget :pc w)
              (+ 1 (mget :pch (mget :ltch2 w))))
       (equal (mget :pc w)
              (mget :pch (mget :ltch1 w)))
       (equal t (mget :validp (mget :ltch2 w)))
       
       (equal (mget (mget :rb (mget (mget :pch (mget :ltch2 w)) (mget :imem w)))
                    (mget :regs w))
              (mget :rb-val (mget :ltch2 w)))
       
       (equal (mget :opcode (mget (mget :pch (mget :ltch2 w)) (mget :imem w)))
              'bez)
       
       (equal 0
              (mget (mget :ra (mget (mget :pch (mget :ltch2 w)) (mget :imem w)))
                    (mget :regs w)))
       (equal 0 (mget :ra-val (mget :ltch2 w))))
  (not (equal (mget :op (mget :ltch2 w)) 'bez))))
