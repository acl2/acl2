(in-package "ACL2")
(include-book "../Supporting-Books/seq")
(include-book "../Supporting-Books/meta")
(include-book "../Supporting-Books/det-macros")
(include-book "../Supporting-Books/records")

:set-ignore-ok t
:set-irrelevant-formals-ok t

(defun equalb (a b) (equal a b))

(defun nequal (a b) (not (equal a b))) (defun add-1 (a) (+ a 1))

(defun sub-1 (a) (- a 1))

(encapsulate ((nextdmem (x3 x2 x1) t))
     (local (defun nextdmem (x3 x2 x1)
              (declare (ignore x3) (ignore x2) (ignore x1))
              1))
     (defthm nextdmem-type (integerp (nextdmem x3 x2 x1))))

(encapsulate ((dmem_read (x2 x1) t))
     (local (defun dmem_read (x2 x1)
              (declare (ignore x2) (ignore x1))
              1))
     (defthm dmem_read-type (integerp (dmem_read x2 x1))))

(encapsulate ((rf0 (x1) t))
     (local (defun rf0 (x1) (declare (ignore x1)) 1))
     (defthm rf0-type (integerp (rf0 x1))))

(encapsulate ((imem0 (x1) t))
     (local (defun imem0 (x1) (declare (ignore x1)) 1))
     (defthm imem0-type (integerp (imem0 x1))))

(encapsulate ((src1 (x1) t))
     (local (defun src1 (x1) (declare (ignore x1)) 1))
     (defthm src1-type (integerp (src1 x1))))

(encapsulate ((src2 (x1) t))
     (local (defun src2 (x1) (declare (ignore x1)) 1))
     (defthm src2-type (integerp (src2 x1))))

(encapsulate ((opcode (x1) t))
     (local (defun opcode (x1) (declare (ignore x1)) 1))
     (defthm op-type (integerp (opcode x1))))

(encapsulate ((dest (x1) t))
     (local (defun dest (x1) (declare (ignore x1)) 1))
     (defthm dest-type (integerp (dest x1))))

(encapsulate ((alu (x3 x2 x1) t))
     (local (defun alu (x3 x2 x1)
              (declare (ignore x3) (ignore x2) (ignore x1))
              1))
     (defthm alu-type (integerp (alu x3 x2 x1))))

(encapsulate ((getregwrite (x1) t))
     (local (defun getregwrite (x1) (declare (ignore x1)) nil))
     (defthm getregwrite-type (booleanp (getregwrite x1))))

(encapsulate ((getmemtoreg (x1) t))
     (local (defun getmemtoreg (x1) (declare (ignore x1)) nil))
     (defthm getmemtoreg-type (booleanp (getmemtoreg x1))))

(encapsulate ((getuseimm (x1) t))
     (local (defun getuseimm (x1) (declare (ignore x1)) nil))
     (defthm getuseimm-type (booleanp (getuseimm x1))))

(encapsulate ((getimm (x1) t))
     (local (defun getimm (x1) (declare (ignore x1)) 1))
     (defthm getimm-type (integerp (getimm x1))))

(encapsulate ((getmemwrite (x1) t))
     (local (defun getmemwrite (x1) (declare (ignore x1)) nil))
     (defthm getmemwrite-type (booleanp (getmemwrite x1))))

(encapsulate ((getisbranch (x1) t))
     (local (defun getisbranch (x1) (declare (ignore x1)) nil))
     (defthm getisbranch-type (booleanp (getisbranch x1))))

(encapsulate ((takebranch (x3 x2 x1) t))
     (local (defun takebranch (x3 x2 x1)
              (declare (ignore x3) (ignore x2) (ignore x1))
              nil))
     (defthm takebranch-type (booleanp (takebranch x3 x2 x1))))

(encapsulate ((selecttargetpc (x3 x2 x1) t))
     (local (defun selecttargetpc (x3 x2 x1)
              (declare (ignore x3) (ignore x2) (ignore x1))
              1))
     (defthm selecttargetpc-type (integerp (selecttargetpc x3 x2 x1))))

(encapsulate ((nextbpstate (x1) t))
     (local (defun nextbpstate (x1) (declare (ignore x1)) 1))
     (defthm nextbpstate-type (integerp (nextbpstate x1))))

(encapsulate ((predictdirection (x1) t))
     (local (defun predictdirection (x1) (declare (ignore x1)) nil))
     (defthm predictdirection-type (booleanp (predictdirection x1))))

(encapsulate ((predicttarget (x1) t))
     (local (defun predicttarget (x1) (declare (ignore x1)) 1))
     (defthm predicttarget-type (integerp (predicttarget x1))))

(defun read-pimem_a (a pimem)
   (declare (xargs :measure (acl2-count pimem)))
   (if (endp pimem) (imem0 a)
       (if (g 0 (car pimem)) (imem0 a) (read-pimem_a a (cdr pimem)))))

(defun read-prf_a (a prf)
   (declare (xargs :measure (acl2-count prf)))
   (if (endp prf) (rf0 a)
       (if (g 0 (car prf)) (rf0 a)
           (cond
             ((g 1 (car prf)) (rf0 a))
             ((and (and (g 2 (car prf)) (equal a (g 3 (car prf))))
                   (g 4 (car prf)))
              (g 5 (car prf)))
             (t (read-prf_a a (cdr prf)))))))

(defun read-simem_a (a simem)
   (declare (xargs :measure (acl2-count simem)))
   (if (endp simem) (imem0 a)
       (if (g 0 (car simem)) (imem0 a)
           (cond
             ((g 1 (car simem)) (imem0 a))
             (t (read-simem_a a (cdr simem)))))))

(defun read-srf_a (a srf)
   (declare (xargs :measure (acl2-count srf)))
   (if (endp srf) (rf0 a)
       (if (g 0 (car srf)) (rf0 a)
           (cond
             ((g 1 (car srf)) (rf0 a))
             ((g 2 (car srf)) (read-prf_a a (g 3 (car srf))))
             ((and (and (g 4 (car srf))
                        (equal a (dest (g 5 (car srf)))))
                   (g 6 (car srf)))
              (g 7 (car srf)))
             (t (read-srf_a a (cdr srf)))))))

(defun u-state_a (impl spec) (seq nil 'impl impl 'spec spec))

(defun impl-state_a
        (pimem ppc bpstate ffpredicteddirection ffpredictedtarget ffwrt
               ffinst ffppc prf fdppc fdwrt fdinst fdpredicteddirection
               fdpredictedtarget deppc desrc1 desrc2 dearg1 dearg2
               dedest deop deimm deuseimm deregwrite dememwrite
               dememtoreg deisbranch dewrt depredicteddirection
               depredictedtarget emppc emis_taken_branch emtargetpc
               emarg2 emresult emdest emwrt emmispredictedtaken
               emmispredictednottaken emregwrite emmemwrite emmemtoreg
               pdmemhist_2 pdmemhist_1 pdmem mmppc mmval mmdest mmwrt
               mmregwrite mwppc mwval mwdest mwwrt mwregwrite)
   (seq nil 'pimem pimem 'ppc ppc 'bpstate bpstate
        'ffpredicteddirection ffpredicteddirection 'ffpredictedtarget
        ffpredictedtarget 'ffwrt ffwrt 'ffinst ffinst 'ffppc ffppc 'prf
        prf 'fdppc fdppc 'fdwrt fdwrt 'fdinst fdinst
        'fdpredicteddirection fdpredicteddirection 'fdpredictedtarget
        fdpredictedtarget 'deppc deppc 'desrc1 desrc1 'desrc2 desrc2
        'dearg1 dearg1 'dearg2 dearg2 'dedest dedest 'deop deop 'deimm
        deimm 'deuseimm deuseimm 'deregwrite deregwrite 'dememwrite
        dememwrite 'dememtoreg dememtoreg 'deisbranch deisbranch 'dewrt
        dewrt 'depredicteddirection depredicteddirection
        'depredictedtarget depredictedtarget 'emppc emppc
        'emis_taken_branch emis_taken_branch 'emtargetpc emtargetpc
        'emarg2 emarg2 'emresult emresult 'emdest emdest 'emwrt emwrt
        'emmispredictedtaken emmispredictedtaken
        'emmispredictednottaken emmispredictednottaken 'emregwrite
        emregwrite 'emmemwrite emmemwrite 'emmemtoreg emmemtoreg
        'pdmemhist_2 pdmemhist_2 'pdmemhist_1 pdmemhist_1 'pdmem pdmem
        'mmppc mmppc 'mmval mmval 'mmdest mmdest 'mmwrt mmwrt
        'mmregwrite mmregwrite 'mwppc mwppc 'mwval mwval 'mwdest mwdest
        'mwwrt mwwrt 'mwregwrite mwregwrite))

(defun initpimem_a (pimem) (cons (s 0 t (s 1 nil nil)) pimem))

(defun nextpimem_a (pimem) (cons (s 0 nil (s 1 nil nil)) pimem))

(defun initppc_a (pc0) pc0)

(defun nextppc_a
        (initi pc0 mem1_mispredicted_taken emppc
               mem1_mispredicted_nottaken emtargetpc stall flush ppc
               if_predict_branch_taken predicted_target)
   (cond
     (initi pc0)
     (mem1_mispredicted_taken emppc)
     (mem1_mispredicted_nottaken emtargetpc)
     ((or stall flush) ppc)
     (if_predict_branch_taken predicted_target)
     (t (add-1 ppc))))

(defun initbpstate_a (bpstate0) bpstate0)

(defun nextbpstate_a (initi bpstate0 stall bpstate)
   (cond (initi bpstate0) (stall bpstate) (t (nextbpstate bpstate))))

(defun initffpredicteddirection_a (ffpredicteddirection0)
   ffpredicteddirection0)

(defun nextffpredicteddirection_a
        (initi ffpredicteddirection0 stall ffpredicteddirection
               if_predict_branch_taken)
   (cond
     (initi ffpredicteddirection0)
     (stall ffpredicteddirection)
     (t if_predict_branch_taken)))

(defun initffpredictedtarget_a (ffpredictedtarget0)
   ffpredictedtarget0)

(defun nextffpredictedtarget_a
        (initi ffpredictedtarget0 stall ffpredictedtarget
               predicted_target)
   (cond
     (initi ffpredictedtarget0)
     (stall ffpredictedtarget)
     (t predicted_target)))

(defun initffwrt_a (ffwrt0) ffwrt0)

(defun nextffwrt_a (initi ffwrt0 squash stall ffwrt flush)
   (cond (initi ffwrt0) (squash nil) (stall ffwrt) (flush nil) (t t)))

(defun initffinst_a (ffinst0) ffinst0)

(defun nextffinst_a (initi ffinst0 stall ffinst if_inst)
   (cond (initi ffinst0) (stall ffinst) (t if_inst)))

(defun initffppc_a (ffppc0) ffppc0)

(defun nextffppc_a (initi ffppc0 stall ffppc ppc)
   (cond (initi ffppc0) (stall ffppc) (t ppc)))

(defun initprf_a (prf) (cons (s 0 t (s 1 nil nil)) prf))

(defun nextprf_a (prf initi mwwrt mwdest mwregwrite mwval)
   (cons (s 0 nil
            (s 1 initi
               (s 2 mwwrt
                  (s 3 mwdest (s 4 mwregwrite (s 5 mwval nil))))))
         prf))

(defun initfdppc_a (fdppc0) fdppc0)

(defun nextfdppc_a (initi fdppc0 stall fdppc ffppc)
   (cond (initi fdppc0) (stall fdppc) (t ffppc)))

(defun initfdwrt_a (fdwrt0) fdwrt0)

(defun nextfdwrt_a (initi fdwrt0 squash stall fdwrt ffwrt)
   (cond (initi fdwrt0) (squash nil) (stall fdwrt) (t ffwrt)))

(defun initfdinst_a (fdinst0) fdinst0)

(defun nextfdinst_a (initi fdinst0 stall fdinst ffinst)
   (cond (initi fdinst0) (stall fdinst) (t ffinst)))

(defun initfdpredicteddirection_a (fdpredicteddirection0)
   fdpredicteddirection0)

(defun nextfdpredicteddirection_a
        (initi fdpredicteddirection0 stall fdpredicteddirection
               ffpredicteddirection)
   (cond
     (initi fdpredicteddirection0)
     (stall fdpredicteddirection)
     (t ffpredicteddirection)))

(defun initfdpredictedtarget_a (fdpredictedtarget0)
   fdpredictedtarget0)

(defun nextfdpredictedtarget_a
        (initi fdpredictedtarget0 stall fdpredictedtarget
               ffpredictedtarget)
   (cond
     (initi fdpredictedtarget0)
     (stall fdpredictedtarget)
     (t ffpredictedtarget)))

(defun initdeppc_a (deppc0) deppc0)

(defun nextdeppc_a (initi deppc0 fdppc)
   (cond (initi deppc0) (t fdppc)))

(defun initdesrc1_a (desrc10) desrc10)

(defun nextdesrc1_a (initi desrc10 if_id_src1)
   (cond (initi desrc10) (t if_id_src1)))

(defun initdesrc2_a (desrc20) desrc20)

(defun nextdesrc2_a (initi desrc20 if_id_src2)
   (cond (initi desrc20) (t if_id_src2)))

(defun initdearg1_a (a1) a1)

(defun nextdearg1_a
        (initi a1 if_id_src1 prf mwwrt mwdest mwregwrite mwval)
   (cond
     (initi a1)
     (t (read-prf_a if_id_src1
            (nextprf_a prf initi mwwrt mwdest mwregwrite mwval)))))

(defun initdearg2_a (a2) a2)

(defun nextdearg2_a
        (initi a2 if_id_src2 prf mwwrt mwdest mwregwrite mwval)
   (cond
     (initi a2)
     (t (read-prf_a if_id_src2
            (nextprf_a prf initi mwwrt mwdest mwregwrite mwval)))))

(defun initdedest_a (dedest0) dedest0)

(defun nextdedest_a (initi dedest0 fdinst)
   (cond (initi dedest0) (t (dest fdinst))))

(defun initdeop_a (deop0) deop0)

(defun nextdeop_a (initi deop0 fdinst)
   (cond (initi deop0) (t (opcode fdinst))))

(defun initdeimm_a (deimm0) deimm0)

(defun nextdeimm_a (initi deimm0 fdinst)
   (cond (initi deimm0) (t (getimm fdinst))))

(defun initdeuseimm_a (deuseimm0) deuseimm0)

(defun nextdeuseimm_a (initi deuseimm0 fdinst)
   (cond (initi deuseimm0) (t (getuseimm fdinst))))

(defun initderegwrite_a (deregwrite0) deregwrite0)

(defun nextderegwrite_a (initi deregwrite0 id_regwrite)
   (cond (initi deregwrite0) (t id_regwrite)))

(defun initdememwrite_a (dememwrite0) dememwrite0)

(defun nextdememwrite_a (initi dememwrite0 id_memwrite)
   (cond (initi dememwrite0) (t id_memwrite)))

(defun initdememtoreg_a (dememtoreg0) dememtoreg0)

(defun nextdememtoreg_a (initi dememtoreg0 fdinst)
   (cond (initi dememtoreg0) (t (getmemtoreg fdinst))))

(defun initdeisbranch_a (deisbranch0) deisbranch0)

(defun nextdeisbranch_a (initi deisbranch0 fdinst)
   (cond (initi deisbranch0) (t (getisbranch fdinst))))

(defun initdewrt_a (dewrt0) dewrt0)

(defun nextdewrt_a (initi dewrt0 squash stall fdwrt)
   (cond (initi dewrt0) (squash nil) (t (and (not stall) fdwrt))))

(defun initdepredicteddirection_a (depredicteddirection0)
   depredicteddirection0)

(defun nextdepredicteddirection_a
        (initi depredicteddirection0 stall depredicteddirection
               fdpredicteddirection)
   (cond
     (initi depredicteddirection0)
     (stall depredicteddirection)
     (t fdpredicteddirection)))

(defun initdepredictedtarget_a (depredictedtarget0)
   depredictedtarget0)

(defun nextdepredictedtarget_a
        (initi depredictedtarget0 stall depredictedtarget
               fdpredictedtarget)
   (cond
     (initi depredictedtarget0)
     (stall depredictedtarget)
     (t fdpredictedtarget)))

(defun initemppc_a (emppc0) emppc0)

(defun nextemppc_a (initi emppc0 deppc)
   (cond (initi emppc0) (t deppc)))

(defun initemis_taken_branch_a (emis_taken_branch0)
   emis_taken_branch0)

(defun nextemis_taken_branch_a
        (initi emis_taken_branch0 ex_is_taken_branch)
   (cond (initi emis_taken_branch0) (t ex_is_taken_branch)))

(defun initemtargetpc_a (emtargetpc0) emtargetpc0)

(defun nextemtargetpc_a (initi emtargetpc0 ex_targetpc)
   (cond (initi emtargetpc0) (t ex_targetpc)))

(defun initemarg2_a (emarg20) emarg20)

(defun nextemarg2_a (initi emarg20 ex_fwd_src2)
   (cond (initi emarg20) (t ex_fwd_src2)))

(defun initemresult_a (emresult0) emresult0)

(defun nextemresult_a (initi emresult0 ex_result)
   (cond (initi emresult0) (t ex_result)))

(defun initemdest_a (emdest0) emdest0)

(defun nextemdest_a (initi emdest0 dedest)
   (cond (initi emdest0) (t dedest)))

(defun initemwrt_a (emwrt0) emwrt0)

(defun nextemwrt_a (initi emwrt0 squash dewrt)
   (cond (initi emwrt0) (squash nil) (t dewrt)))

(defun initemmispredictedtaken_a (emmispredictedtaken0)
   emmispredictedtaken0)

(defun nextemmispredictedtaken_a
        (initi emmispredictedtaken0 mispredicted_taken)
   (cond (initi emmispredictedtaken0) (t mispredicted_taken)))

(defun initemmispredictednottaken_a (emmispredictednottaken0)
   emmispredictednottaken0)

(defun nextemmispredictednottaken_a
        (initi emmispredictednottaken0 mispredicted_nottaken)
   (cond (initi emmispredictednottaken0) (t mispredicted_nottaken)))

(defun initemregwrite_a (emregwrite0) emregwrite0)

(defun nextemregwrite_a (initi emregwrite0 deregwrite)
   (cond (initi emregwrite0) (t deregwrite)))

(defun initemmemwrite_a (emmemwrite0) emmemwrite0)

(defun nextemmemwrite_a (initi emmemwrite0 dememwrite)
   (cond (initi emmemwrite0) (t dememwrite)))

(defun initemmemtoreg_a (emmemtoreg0) emmemtoreg0)

(defun nextemmemtoreg_a (initi emmemtoreg0 dememtoreg)
   (cond (initi emmemtoreg0) (t dememtoreg)))

(defun initpdmemhist_2_a (dmem0) dmem0)

(defun nextpdmemhist_2_a (initi dmem0 pdmemhist_1)
   (cond (initi dmem0) (t pdmemhist_1)))

(defun initpdmemhist_1_a (dmem0) dmem0)

(defun nextpdmemhist_1_a (initi dmem0 pdmem)
   (cond (initi dmem0) (t pdmem)))

(defun initpdmem_a (dmem0) dmem0)

(defun nextpdmem_a
        (initi dmem0 emwrt emmemwrite pdmem emresult emarg2)
   (cond
     (initi dmem0)
     ((and emwrt emmemwrite) (nextdmem pdmem emresult emarg2))
     (t pdmem)))

(defun initmmppc_a (mmppc0) mmppc0)

(defun nextmmppc_a (initi mmppc0 emppc)
   (cond (initi mmppc0) (t emppc)))

(defun initmmval_a (mmval0) mmval0)

(defun nextmmval_a (initi mmval0 emmemtoreg mem1_readdata emresult)
   (cond (initi mmval0) (emmemtoreg mem1_readdata) (t emresult)))

(defun initmmdest_a (mmdest0) mmdest0)

(defun nextmmdest_a (initi mmdest0 emdest)
   (cond (initi mmdest0) (t emdest)))

(defun initmmwrt_a (mmwrt0) mmwrt0)

(defun nextmmwrt_a (initi mmwrt0 emwrt)
   (cond (initi mmwrt0) (t emwrt)))

(defun initmmregwrite_a (mmregwrite0) mmregwrite0)

(defun nextmmregwrite_a (initi mmregwrite0 emregwrite)
   (cond (initi mmregwrite0) (t emregwrite)))

(defun initmwppc_a (mwppc0) mwppc0)

(defun nextmwppc_a (initi mwppc0 mmppc)
   (cond (initi mwppc0) (t mmppc)))

(defun initmwval_a (mwval0) mwval0)

(defun nextmwval_a (initi mwval0 mmval)
   (cond (initi mwval0) (t mmval)))

(defun initmwdest_a (mwdest0) mwdest0)

(defun nextmwdest_a (initi mwdest0 mmdest)
   (cond (initi mwdest0) (t mmdest)))

(defun initmwwrt_a (mwwrt0) mwwrt0)

(defun nextmwwrt_a (initi mwwrt0 mmwrt)
   (cond (initi mwwrt0) (t mmwrt)))

(defun initmwregwrite_a (mwregwrite0) mwregwrite0)

(defun nextmwregwrite_a (initi mwregwrite0 mmregwrite)
   (cond (initi mwregwrite0) (t mmregwrite)))

(defun impl-simulate_a
        (impl initi pc0 flush bpstate0 ffpredicteddirection0
              ffpredictedtarget0 ffwrt0 ffinst0 ffppc0 fdppc0 fdwrt0
              fdinst0 fdpredicteddirection0 fdpredictedtarget0 deppc0
              desrc10 desrc20 a1 a2 dedest0 deop0 deimm0 deuseimm0
              deregwrite0 dememwrite0 dememtoreg0 deisbranch0 dewrt0
              depredicteddirection0 depredictedtarget0 emppc0
              emis_taken_branch0 emtargetpc0 emarg20 emresult0 emdest0
              emwrt0 emmispredictedtaken0 emmispredictednottaken0
              emregwrite0 emmemwrite0 emmemtoreg0 dmem0 mmppc0 mmval0
              mmdest0 mmwrt0 mmregwrite0 mwppc0 mwval0 mwdest0 mwwrt0
              mwregwrite0)
   (let* ((pimem (g 'pimem impl)) (ppc (g 'ppc impl))
          (bpstate (g 'bpstate impl))
          (ffpredicteddirection (g 'ffpredicteddirection impl))
          (ffpredictedtarget (g 'ffpredictedtarget impl))
          (ffwrt (g 'ffwrt impl)) (ffinst (g 'ffinst impl))
          (ffppc (g 'ffppc impl)) (prf (g 'prf impl))
          (fdppc (g 'fdppc impl)) (fdwrt (g 'fdwrt impl))
          (fdinst (g 'fdinst impl))
          (fdpredicteddirection (g 'fdpredicteddirection impl))
          (fdpredictedtarget (g 'fdpredictedtarget impl))
          (deppc (g 'deppc impl)) (desrc1 (g 'desrc1 impl))
          (desrc2 (g 'desrc2 impl)) (dearg1 (g 'dearg1 impl))
          (dearg2 (g 'dearg2 impl)) (dedest (g 'dedest impl))
          (deop (g 'deop impl)) (deimm (g 'deimm impl))
          (deuseimm (g 'deuseimm impl))
          (deregwrite (g 'deregwrite impl))
          (dememwrite (g 'dememwrite impl))
          (dememtoreg (g 'dememtoreg impl))
          (deisbranch (g 'deisbranch impl)) (dewrt (g 'dewrt impl))
          (depredicteddirection (g 'depredicteddirection impl))
          (depredictedtarget (g 'depredictedtarget impl))
          (emppc (g 'emppc impl))
          (emis_taken_branch (g 'emis_taken_branch impl))
          (emtargetpc (g 'emtargetpc impl)) (emarg2 (g 'emarg2 impl))
          (emresult (g 'emresult impl)) (emdest (g 'emdest impl))
          (emwrt (g 'emwrt impl))
          (emmispredictedtaken (g 'emmispredictedtaken impl))
          (emmispredictednottaken (g 'emmispredictednottaken impl))
          (emregwrite (g 'emregwrite impl))
          (emmemwrite (g 'emmemwrite impl))
          (emmemtoreg (g 'emmemtoreg impl))
          (pdmemhist_2 (g 'pdmemhist_2 impl))
          (pdmemhist_1 (g 'pdmemhist_1 impl)) (pdmem (g 'pdmem impl))
          (mmppc (g 'mmppc impl)) (mmval (g 'mmval impl))
          (mmdest (g 'mmdest impl)) (mmwrt (g 'mmwrt impl))
          (mmregwrite (g 'mmregwrite impl)) (mwppc (g 'mwppc impl))
          (mwval (g 'mwval impl)) (mwdest (g 'mwdest impl))
          (mwwrt (g 'mwwrt impl)) (mwregwrite (g 'mwregwrite impl)))
     (let* ((if_inst (read-pimem_a ppc pimem))
            (predicted_direction (predictdirection bpstate))
            (predicted_target (predicttarget bpstate))
            (if_predict_branch_taken
                (and (getisbranch if_inst) predicted_direction))
            (if_id_src1 (src1 fdinst)) (if_id_src2 (src2 fdinst))
            (stall (and (and deregwrite dewrt)
                        (or (equal if_id_src1 dedest)
                            (equal if_id_src2 dedest))))
            (id_regwrite (getregwrite fdinst))
            (id_memwrite (getmemwrite fdinst))
            (ex_wb_equal_src1
                (and (and mwwrt (equal desrc1 mwdest)) mwregwrite))
            (ex_wb_equal_src2
                (and (and mwwrt (equal desrc2 mwdest)) mwregwrite))
            (ex_mem2_equal_src1
                (and (and mmwrt (equal desrc1 mmdest)) mmregwrite))
            (ex_mem2_equal_src2
                (and (and mmwrt (equal desrc2 mmdest)) mmregwrite))
            (ex_fwd_src1
                (cond
                  (ex_mem2_equal_src1 mmval)
                  (ex_wb_equal_src1 mwval)
                  (t dearg1)))
            (ex_fwd_src2
                (cond
                  (ex_mem2_equal_src2 mmval)
                  (ex_wb_equal_src2 mwval)
                  (t dearg2)))
            (ex_data2 (cond (deuseimm deimm) (t ex_fwd_src2)))
            (ex_result (alu deop ex_fwd_src1 ex_data2))
            (ex_is_taken_branch_temp
                (takebranch deop ex_fwd_src1 ex_fwd_src2))
            (ex_is_taken_branch
                (and (and ex_is_taken_branch_temp dewrt) deisbranch))
            (ex_targetpc (selecttargetpc deop ex_fwd_src1 deppc))
            (equal_targetpc (equal ex_targetpc depredictedtarget))
            (equal_targetpc_bar (not equal_targetpc))
            (ex_predicteddirection depredicteddirection)
            (mispredicted_nottaken_case1
                (and ex_is_taken_branch (not ex_predicteddirection)))
            (mispredicted_nottaken_case2
                (and ex_is_taken_branch equal_targetpc_bar))
            (mispredicted_nottaken
                (or mispredicted_nottaken_case1
                    mispredicted_nottaken_case2))
            (mispredicted_taken
                (and (and ex_predicteddirection deisbranch)
                     (not ex_is_taken_branch)))
            (mem1_readdata (dmem_read pdmem emresult))
            (mem1_is_taken_branch (and emwrt emis_taken_branch))
            (mem1_mispredicted_taken (and emmispredictedtaken emwrt))
            (mem1_mispredicted_nottaken
                (and emmispredictednottaken emwrt))
            (mem1_mispredicted
                (or mem1_mispredicted_nottaken mem1_mispredicted_taken))
            (squash mem1_mispredicted))
       (impl-state_a (nextpimem_a pimem)
           (nextppc_a initi pc0 mem1_mispredicted_taken emppc
               mem1_mispredicted_nottaken emtargetpc stall flush ppc
               if_predict_branch_taken predicted_target)
           (nextbpstate_a initi bpstate0 stall bpstate)
           (nextffpredicteddirection_a initi ffpredicteddirection0
               stall ffpredicteddirection if_predict_branch_taken)
           (nextffpredictedtarget_a initi ffpredictedtarget0 stall
               ffpredictedtarget predicted_target)
           (nextffwrt_a initi ffwrt0 squash stall ffwrt flush)
           (nextffinst_a initi ffinst0 stall ffinst if_inst)
           (nextffppc_a initi ffppc0 stall ffppc ppc)
           (nextprf_a prf initi mwwrt mwdest mwregwrite mwval)
           (nextfdppc_a initi fdppc0 stall fdppc ffppc)
           (nextfdwrt_a initi fdwrt0 squash stall fdwrt ffwrt)
           (nextfdinst_a initi fdinst0 stall fdinst ffinst)
           (nextfdpredicteddirection_a initi fdpredicteddirection0
               stall fdpredicteddirection ffpredicteddirection)
           (nextfdpredictedtarget_a initi fdpredictedtarget0 stall
               fdpredictedtarget ffpredictedtarget)
           (nextdeppc_a initi deppc0 fdppc)
           (nextdesrc1_a initi desrc10 if_id_src1)
           (nextdesrc2_a initi desrc20 if_id_src2)
           (nextdearg1_a initi a1 if_id_src1 prf mwwrt mwdest
               mwregwrite mwval)
           (nextdearg2_a initi a2 if_id_src2 prf mwwrt mwdest
               mwregwrite mwval)
           (nextdedest_a initi dedest0 fdinst)
           (nextdeop_a initi deop0 fdinst)
           (nextdeimm_a initi deimm0 fdinst)
           (nextdeuseimm_a initi deuseimm0 fdinst)
           (nextderegwrite_a initi deregwrite0 id_regwrite)
           (nextdememwrite_a initi dememwrite0 id_memwrite)
           (nextdememtoreg_a initi dememtoreg0 fdinst)
           (nextdeisbranch_a initi deisbranch0 fdinst)
           (nextdewrt_a initi dewrt0 squash stall fdwrt)
           (nextdepredicteddirection_a initi depredicteddirection0
               stall depredicteddirection fdpredicteddirection)
           (nextdepredictedtarget_a initi depredictedtarget0 stall
               depredictedtarget fdpredictedtarget)
           (nextemppc_a initi emppc0 deppc)
           (nextemis_taken_branch_a initi emis_taken_branch0
               ex_is_taken_branch)
           (nextemtargetpc_a initi emtargetpc0 ex_targetpc)
           (nextemarg2_a initi emarg20 ex_fwd_src2)
           (nextemresult_a initi emresult0 ex_result)
           (nextemdest_a initi emdest0 dedest)
           (nextemwrt_a initi emwrt0 squash dewrt)
           (nextemmispredictedtaken_a initi emmispredictedtaken0
               mispredicted_taken)
           (nextemmispredictednottaken_a initi emmispredictednottaken0
               mispredicted_nottaken)
           (nextemregwrite_a initi emregwrite0 deregwrite)
           (nextemmemwrite_a initi emmemwrite0 dememwrite)
           (nextemmemtoreg_a initi emmemtoreg0 dememtoreg)
           (nextpdmemhist_2_a initi dmem0 pdmemhist_1)
           (nextpdmemhist_1_a initi dmem0 pdmem)
           (nextpdmem_a initi dmem0 emwrt emmemwrite pdmem emresult
               emarg2)
           (nextmmppc_a initi mmppc0 emppc)
           (nextmmval_a initi mmval0 emmemtoreg mem1_readdata emresult)
           (nextmmdest_a initi mmdest0 emdest)
           (nextmmwrt_a initi mmwrt0 emwrt)
           (nextmmregwrite_a initi mmregwrite0 emregwrite)
           (nextmwppc_a initi mwppc0 mmppc)
           (nextmwval_a initi mwval0 mmval)
           (nextmwdest_a initi mwdest0 mmdest)
           (nextmwwrt_a initi mwwrt0 mmwrt)
           (nextmwregwrite_a initi mwregwrite0 mmregwrite)))))

(defun impl-initialize_a
        (impl pc0 bpstate0 ffpredicteddirection0 ffpredictedtarget0
              ffwrt0 ffinst0 ffppc0 fdppc0 fdwrt0 fdinst0
              fdpredicteddirection0 fdpredictedtarget0 deppc0 desrc10
              desrc20 a1 a2 dedest0 deop0 deimm0 deuseimm0 deregwrite0
              dememwrite0 dememtoreg0 deisbranch0 dewrt0
              depredicteddirection0 depredictedtarget0 emppc0
              emis_taken_branch0 emtargetpc0 emarg20 emresult0 emdest0
              emwrt0 emmispredictedtaken0 emmispredictednottaken0
              emregwrite0 emmemwrite0 emmemtoreg0 dmem0 mmppc0 mmval0
              mmdest0 mmwrt0 mmregwrite0 mwppc0 mwval0 mwdest0 mwwrt0
              mwregwrite0)
   (let* ((pimem (g 'pimem impl)) (ppc (g 'ppc impl))
          (bpstate (g 'bpstate impl))
          (ffpredicteddirection (g 'ffpredicteddirection impl))
          (ffpredictedtarget (g 'ffpredictedtarget impl))
          (ffwrt (g 'ffwrt impl)) (ffinst (g 'ffinst impl))
          (ffppc (g 'ffppc impl)) (prf (g 'prf impl))
          (fdppc (g 'fdppc impl)) (fdwrt (g 'fdwrt impl))
          (fdinst (g 'fdinst impl))
          (fdpredicteddirection (g 'fdpredicteddirection impl))
          (fdpredictedtarget (g 'fdpredictedtarget impl))
          (deppc (g 'deppc impl)) (desrc1 (g 'desrc1 impl))
          (desrc2 (g 'desrc2 impl)) (dearg1 (g 'dearg1 impl))
          (dearg2 (g 'dearg2 impl)) (dedest (g 'dedest impl))
          (deop (g 'deop impl)) (deimm (g 'deimm impl))
          (deuseimm (g 'deuseimm impl))
          (deregwrite (g 'deregwrite impl))
          (dememwrite (g 'dememwrite impl))
          (dememtoreg (g 'dememtoreg impl))
          (deisbranch (g 'deisbranch impl)) (dewrt (g 'dewrt impl))
          (depredicteddirection (g 'depredicteddirection impl))
          (depredictedtarget (g 'depredictedtarget impl))
          (emppc (g 'emppc impl))
          (emis_taken_branch (g 'emis_taken_branch impl))
          (emtargetpc (g 'emtargetpc impl)) (emarg2 (g 'emarg2 impl))
          (emresult (g 'emresult impl)) (emdest (g 'emdest impl))
          (emwrt (g 'emwrt impl))
          (emmispredictedtaken (g 'emmispredictedtaken impl))
          (emmispredictednottaken (g 'emmispredictednottaken impl))
          (emregwrite (g 'emregwrite impl))
          (emmemwrite (g 'emmemwrite impl))
          (emmemtoreg (g 'emmemtoreg impl))
          (pdmemhist_2 (g 'pdmemhist_2 impl))
          (pdmemhist_1 (g 'pdmemhist_1 impl)) (pdmem (g 'pdmem impl))
          (mmppc (g 'mmppc impl)) (mmval (g 'mmval impl))
          (mmdest (g 'mmdest impl)) (mmwrt (g 'mmwrt impl))
          (mmregwrite (g 'mmregwrite impl)) (mwppc (g 'mwppc impl))
          (mwval (g 'mwval impl)) (mwdest (g 'mwdest impl))
          (mwwrt (g 'mwwrt impl)) (mwregwrite (g 'mwregwrite impl)))
     (let* ((if_inst (read-pimem_a ppc pimem))
            (predicted_direction (predictdirection bpstate))
            (predicted_target (predicttarget bpstate))
            (if_predict_branch_taken
                (and (getisbranch if_inst) predicted_direction))
            (if_id_src1 (src1 fdinst)) (if_id_src2 (src2 fdinst))
            (stall (and (and deregwrite dewrt)
                        (or (equal if_id_src1 dedest)
                            (equal if_id_src2 dedest))))
            (id_regwrite (getregwrite fdinst))
            (id_memwrite (getmemwrite fdinst))
            (ex_wb_equal_src1
                (and (and mwwrt (equal desrc1 mwdest)) mwregwrite))
            (ex_wb_equal_src2
                (and (and mwwrt (equal desrc2 mwdest)) mwregwrite))
            (ex_mem2_equal_src1
                (and (and mmwrt (equal desrc1 mmdest)) mmregwrite))
            (ex_mem2_equal_src2
                (and (and mmwrt (equal desrc2 mmdest)) mmregwrite))
            (ex_fwd_src1
                (cond
                  (ex_mem2_equal_src1 mmval)
                  (ex_wb_equal_src1 mwval)
                  (t dearg1)))
            (ex_fwd_src2
                (cond
                  (ex_mem2_equal_src2 mmval)
                  (ex_wb_equal_src2 mwval)
                  (t dearg2)))
            (ex_data2 (cond (deuseimm deimm) (t ex_fwd_src2)))
            (ex_result (alu deop ex_fwd_src1 ex_data2))
            (ex_is_taken_branch_temp
                (takebranch deop ex_fwd_src1 ex_fwd_src2))
            (ex_is_taken_branch
                (and (and ex_is_taken_branch_temp dewrt) deisbranch))
            (ex_targetpc (selecttargetpc deop ex_fwd_src1 deppc))
            (equal_targetpc (equal ex_targetpc depredictedtarget))
            (equal_targetpc_bar (not equal_targetpc))
            (ex_predicteddirection depredicteddirection)
            (mispredicted_nottaken_case1
                (and ex_is_taken_branch (not ex_predicteddirection)))
            (mispredicted_nottaken_case2
                (and ex_is_taken_branch equal_targetpc_bar))
            (mispredicted_nottaken
                (or mispredicted_nottaken_case1
                    mispredicted_nottaken_case2))
            (mispredicted_taken
                (and (and ex_predicteddirection deisbranch)
                     (not ex_is_taken_branch)))
            (mem1_readdata (dmem_read pdmem emresult))
            (mem1_is_taken_branch (and emwrt emis_taken_branch))
            (mem1_mispredicted_taken (and emmispredictedtaken emwrt))
            (mem1_mispredicted_nottaken
                (and emmispredictednottaken emwrt))
            (mem1_mispredicted
                (or mem1_mispredicted_nottaken mem1_mispredicted_taken))
            (squash mem1_mispredicted))
       (impl-state_a (initpimem_a pimem) (initppc_a pc0)
           (initbpstate_a bpstate0)
           (initffpredicteddirection_a ffpredicteddirection0)
           (initffpredictedtarget_a ffpredictedtarget0)
           (initffwrt_a ffwrt0) (initffinst_a ffinst0)
           (initffppc_a ffppc0) (initprf_a prf) (initfdppc_a fdppc0)
           (initfdwrt_a fdwrt0) (initfdinst_a fdinst0)
           (initfdpredicteddirection_a fdpredicteddirection0)
           (initfdpredictedtarget_a fdpredictedtarget0)
           (initdeppc_a deppc0) (initdesrc1_a desrc10)
           (initdesrc2_a desrc20) (initdearg1_a a1) (initdearg2_a a2)
           (initdedest_a dedest0) (initdeop_a deop0)
           (initdeimm_a deimm0) (initdeuseimm_a deuseimm0)
           (initderegwrite_a deregwrite0)
           (initdememwrite_a dememwrite0)
           (initdememtoreg_a dememtoreg0)
           (initdeisbranch_a deisbranch0) (initdewrt_a dewrt0)
           (initdepredicteddirection_a depredicteddirection0)
           (initdepredictedtarget_a depredictedtarget0)
           (initemppc_a emppc0)
           (initemis_taken_branch_a emis_taken_branch0)
           (initemtargetpc_a emtargetpc0) (initemarg2_a emarg20)
           (initemresult_a emresult0) (initemdest_a emdest0)
           (initemwrt_a emwrt0)
           (initemmispredictedtaken_a emmispredictedtaken0)
           (initemmispredictednottaken_a emmispredictednottaken0)
           (initemregwrite_a emregwrite0)
           (initemmemwrite_a emmemwrite0)
           (initemmemtoreg_a emmemtoreg0) (initpdmemhist_2_a dmem0)
           (initpdmemhist_1_a dmem0) (initpdmem_a dmem0)
           (initmmppc_a mmppc0) (initmmval_a mmval0)
           (initmmdest_a mmdest0) (initmmwrt_a mmwrt0)
           (initmmregwrite_a mmregwrite0) (initmwppc_a mwppc0)
           (initmwval_a mwval0) (initmwdest_a mwdest0)
           (initmwwrt_a mwwrt0) (initmwregwrite_a mwregwrite0)))))

(defun spec-state_a (simem spc srf sdmem)
   (seq nil 'simem simem 'spc spc 'srf srf 'sdmem sdmem))

(defun initsimem_a (simem) (cons (s 0 t (s 1 nil nil)) simem))

(defun nextsimem_a (simem initi)
   (cons (s 0 nil (s 1 initi nil)) simem))

(defun initspc_a (pc0) pc0)

(defun nextspc_a
        (initi pc0 project_impl impl.ppc isa is_taken_branch targetpc
               spc)
   (cond
     (initi pc0)
     (project_impl impl.ppc)
     ((and isa is_taken_branch) targetpc)
     (isa (add-1 spc))
     (t spc)))

(defun initsrf_a (srf) (cons (s 0 t (s 1 nil nil)) srf))

(defun nextsrf_a
        (srf initi project_impl impl.prf isa inst regwrite val)
   (cons (s 0 nil
            (s 1 initi
               (s 2 project_impl
                  (s 3 impl.prf
                     (s 4 isa (s 5 inst (s 6 regwrite (s 7 val nil))))))))
         srf))

(defun initsdmem_a (dmem0) dmem0)

(defun nextsdmem_a
        (initi dmem0 project_impl impl.pdmem isa memwrite sdmem result
               arg2_temp)
   (cond
     (initi dmem0)
     (project_impl impl.pdmem)
     ((and isa memwrite) (nextdmem sdmem result arg2_temp))
     (t sdmem)))

(defun spec-simulate_a
        (spec initi pc0 project_impl impl.ppc isa impl.prf dmem0
              impl.pdmem)
   (let* ((simem (g 'simem spec)) (spc (g 'spc spec))
          (srf (g 'srf spec)) (sdmem (g 'sdmem spec)))
     (let* ((inst (read-simem_a spc simem))
            (regwrite (getregwrite inst)) (memtoreg (getmemtoreg inst))
            (memwrite (getmemwrite inst)) (isbranch (getisbranch inst))
            (useimm (getuseimm inst)) (imm (getimm inst))
            (arg1 (read-srf_a (src1 inst) srf))
            (arg2_temp (read-srf_a (src2 inst) srf))
            (arg2 (cond (useimm imm) (t arg2_temp)))
            (result (alu (opcode inst) arg1 arg2))
            (is_taken_branch_temp
                (takebranch (opcode inst) arg1 arg2_temp))
            (is_taken_branch (and is_taken_branch_temp isbranch))
            (targetpc (selecttargetpc (opcode inst) arg1 spc))
            (readdata (dmem_read sdmem result))
            (val (cond (memtoreg readdata) (t result))))
       (spec-state_a (nextsimem_a simem initi)
           (nextspc_a initi pc0 project_impl impl.ppc isa
               is_taken_branch targetpc spc)
           (nextsrf_a srf initi project_impl impl.prf isa inst regwrite
               val)
           (nextsdmem_a initi dmem0 project_impl impl.pdmem isa
               memwrite sdmem result arg2_temp)))))

(defun spec-initialize_a (spec pc0 dmem0)
   (let* ((simem (g 'simem spec)) (spc (g 'spc spec))
          (srf (g 'srf spec)) (sdmem (g 'sdmem spec)))
     (let* ((inst (read-simem_a spc simem))
            (regwrite (getregwrite inst)) (memtoreg (getmemtoreg inst))
            (memwrite (getmemwrite inst)) (isbranch (getisbranch inst))
            (useimm (getuseimm inst)) (imm (getimm inst))
            (arg1 (read-srf_a (src1 inst) srf))
            (arg2_temp (read-srf_a (src2 inst) srf))
            (arg2 (cond (useimm imm) (t arg2_temp)))
            (result (alu (opcode inst) arg1 arg2))
            (is_taken_branch_temp
                (takebranch (opcode inst) arg1 arg2_temp))
            (is_taken_branch (and is_taken_branch_temp isbranch))
            (targetpc (selecttargetpc (opcode inst) arg1 spc))
            (readdata (dmem_read sdmem result))
            (val (cond (memtoreg readdata) (t result))))
       (spec-state_a (initsimem_a simem) (initspc_a pc0)
           (initsrf_a srf) (initsdmem_a dmem0)))))

(defun simulate_a
        (st flush isa project_impl initi pc0 bpstate0
            ffpredicteddirection0 ffpredictedtarget0 ffwrt0 ffinst0
            ffppc0 fdppc0 fdwrt0 fdinst0 fdpredicteddirection0
            fdpredictedtarget0 deppc0 desrc10 desrc20 a1 a2 dedest0
            deop0 deimm0 deuseimm0 deregwrite0 dememwrite0 dememtoreg0
            deisbranch0 dewrt0 depredicteddirection0 depredictedtarget0
            emppc0 emis_taken_branch0 emtargetpc0 emarg20 emresult0
            emdest0 emwrt0 emmispredictedtaken0 emmispredictednottaken0
            emregwrite0 emmemwrite0 emmemtoreg0 dmem0 mmppc0 mmval0
            mmdest0 mmwrt0 mmregwrite0 mwppc0 mwval0 mwdest0 mwwrt0
            mwregwrite0 impl.ppc impl.prf impl.pdmem)
   (u-state_a
       (impl-simulate_a (g 'impl st) initi pc0 flush bpstate0
           ffpredicteddirection0 ffpredictedtarget0 ffwrt0 ffinst0
           ffppc0 fdppc0 fdwrt0 fdinst0 fdpredicteddirection0
           fdpredictedtarget0 deppc0 desrc10 desrc20 a1 a2 dedest0
           deop0 deimm0 deuseimm0 deregwrite0 dememwrite0 dememtoreg0
           deisbranch0 dewrt0 depredicteddirection0 depredictedtarget0
           emppc0 emis_taken_branch0 emtargetpc0 emarg20 emresult0
           emdest0 emwrt0 emmispredictedtaken0 emmispredictednottaken0
           emregwrite0 emmemwrite0 emmemtoreg0 dmem0 mmppc0 mmval0
           mmdest0 mmwrt0 mmregwrite0 mwppc0 mwval0 mwdest0 mwwrt0
           mwregwrite0)
       (spec-simulate_a (g 'spec st) initi pc0 project_impl impl.ppc
           isa impl.prf dmem0 impl.pdmem)))

(defun initialize_a
        (st flush isa project_impl initi pc0 bpstate0
            ffpredicteddirection0 ffpredictedtarget0 ffwrt0 ffinst0
            ffppc0 fdppc0 fdwrt0 fdinst0 fdpredicteddirection0
            fdpredictedtarget0 deppc0 desrc10 desrc20 a1 a2 dedest0
            deop0 deimm0 deuseimm0 deregwrite0 dememwrite0 dememtoreg0
            deisbranch0 dewrt0 depredicteddirection0 depredictedtarget0
            emppc0 emis_taken_branch0 emtargetpc0 emarg20 emresult0
            emdest0 emwrt0 emmispredictedtaken0 emmispredictednottaken0
            emregwrite0 emmemwrite0 emmemtoreg0 dmem0 mmppc0 mmval0
            mmdest0 mmwrt0 mmregwrite0 mwppc0 mwval0 mwdest0 mwwrt0
            mwregwrite0)
   (u-state_a
       (impl-initialize_a (g 'impl st) pc0 bpstate0
           ffpredicteddirection0 ffpredictedtarget0 ffwrt0 ffinst0
           ffppc0 fdppc0 fdwrt0 fdinst0 fdpredicteddirection0
           fdpredictedtarget0 deppc0 desrc10 desrc20 a1 a2 dedest0
           deop0 deimm0 deuseimm0 deregwrite0 dememwrite0 dememtoreg0
           deisbranch0 dewrt0 depredicteddirection0 depredictedtarget0
           emppc0 emis_taken_branch0 emtargetpc0 emarg20 emresult0
           emdest0 emwrt0 emmispredictedtaken0 emmispredictednottaken0
           emregwrite0 emmemwrite0 emmemtoreg0 dmem0 mmppc0 mmval0
           mmdest0 mmwrt0 mmregwrite0 mwppc0 mwval0 mwdest0 mwwrt0
           mwregwrite0)
       (spec-initialize_a (g 'spec st) pc0 dmem0)))

(defthm web_core_a
        (implies (and (integerp pc0) (integerp dmem0)
                      (integerp bpstate0) (integerp a) (integerp zero)
                      (booleanp ffwrt0) (booleanp fdwrt0)
                      (booleanp dewrt0) (booleanp emwrt0)
                      (booleanp mmwrt0) (booleanp mwwrt0)
                      (integerp fdbpstate0)
                      (booleanp fdpredicteddirection0)
                      (integerp fdpredictedtarget0)
                      (booleanp emmispredictednottaken0)
                      (integerp debpstate0)
                      (booleanp depredicteddirection0)
                      (integerp depredictedtarget0)
                      (booleanp emmispredictedtaken0)
                      (integerp embpstate0) (integerp mmbpstate0)
                      (integerp mwbpstate0)
                      (integerp ffpredictedtarget0)
                      (integerp ffbpstate0)
                      (booleanp ffpredicteddirection0)
                      (integerp emppc0) (integerp mmppc0)
                      (integerp mwppc0) (booleanp deisbranch0)
                      (booleanp emis_taken_branch0)
                      (integerp emtargetpc0) (integerp ffppc0)
                      (integerp fdppc0) (integerp deppc0)
                      (integerp mwval0) (integerp emresult0)
                      (booleanp deregwrite0) (booleanp emregwrite0)
                      (booleanp mwregwrite0) (integerp mwdest0)
                      (integerp deop0) (integerp fddest0)
                      (integerp dedest0) (integerp op0) (integerp s0)
                      (integerp a1) (integerp a2) (integerp d0)
                      (integerp d1) (integerp x0) (integerp fdop0)
                      (booleanp w0) (booleanp w1) (integerp fdsrc10)
                      (integerp fdsrc20) (integerp emdest0)
                      (integerp emval0) (integerp desrc10)
                      (integerp desrc20) (integerp fdinst0)
                      (integerp deimm0) (booleanp deuseimm0)
                      (booleanp dememtoreg0) (booleanp emmemtoreg0)
                      (integerp emimm0) (booleanp emuseimm0)
                      (booleanp dememwrite0) (booleanp emmemwrite0)
                      (integerp emarg20) (integerp ffinst0)
                      (integerp mmval0) (integerp mmdest0)
                      (booleanp mmregwrite0) (integerp mmresult0)
                      (booleanp mmmemwrite0) (integerp mmarg20))
                 (let* ((st0 (initialize_a nil nil nil nil nil pc0
                                 bpstate0 ffpredicteddirection0
                                 ffpredictedtarget0 ffwrt0 ffinst0
                                 ffppc0 fdppc0 fdwrt0 fdinst0
                                 fdpredicteddirection0
                                 fdpredictedtarget0 deppc0 desrc10
                                 desrc20 a1 a2 dedest0 deop0 deimm0
                                 deuseimm0 deregwrite0 dememwrite0
                                 dememtoreg0 deisbranch0 dewrt0
                                 depredicteddirection0
                                 depredictedtarget0 emppc0
                                 emis_taken_branch0 emtargetpc0 emarg20
                                 emresult0 emdest0 emwrt0
                                 emmispredictedtaken0
                                 emmispredictednottaken0 emregwrite0
                                 emmemwrite0 emmemtoreg0 dmem0 mmppc0
                                 mmval0 mmdest0 mmwrt0 mmregwrite0
                                 mwppc0 mwval0 mwdest0 mwwrt0
                                 mwregwrite0))
                        (st1 (simulate_a st0 t nil nil nil pc0 bpstate0
                                 ffpredicteddirection0
                                 ffpredictedtarget0 ffwrt0 ffinst0
                                 ffppc0 fdppc0 fdwrt0 fdinst0
                                 fdpredicteddirection0
                                 fdpredictedtarget0 deppc0 desrc10
                                 desrc20 a1 a2 dedest0 deop0 deimm0
                                 deuseimm0 deregwrite0 dememwrite0
                                 dememtoreg0 deisbranch0 dewrt0
                                 depredicteddirection0
                                 depredictedtarget0 emppc0
                                 emis_taken_branch0 emtargetpc0 emarg20
                                 emresult0 emdest0 emwrt0
                                 emmispredictedtaken0
                                 emmispredictednottaken0 emregwrite0
                                 emmemwrite0 emmemtoreg0 dmem0 mmppc0
                                 mmval0 mmdest0 mmwrt0 mmregwrite0
                                 mwppc0 mwval0 mwdest0 mwwrt0
                                 mwregwrite0 (g 'ppc (g 'impl st0))
                                 (g 'prf (g 'impl st0))
                                 (g 'pdmem (g 'impl st0))))
                        (st2 (simulate_a st1 t nil nil nil pc0 bpstate0
                                 ffpredicteddirection0
                                 ffpredictedtarget0 ffwrt0 ffinst0
                                 ffppc0 fdppc0 fdwrt0 fdinst0
                                 fdpredicteddirection0
                                 fdpredictedtarget0 deppc0 desrc10
                                 desrc20 a1 a2 dedest0 deop0 deimm0
                                 deuseimm0 deregwrite0 dememwrite0
                                 dememtoreg0 deisbranch0 dewrt0
                                 depredicteddirection0
                                 depredictedtarget0 emppc0
                                 emis_taken_branch0 emtargetpc0 emarg20
                                 emresult0 emdest0 emwrt0
                                 emmispredictedtaken0
                                 emmispredictednottaken0 emregwrite0
                                 emmemwrite0 emmemtoreg0 dmem0 mmppc0
                                 mmval0 mmdest0 mmwrt0 mmregwrite0
                                 mwppc0 mwval0 mwdest0 mwwrt0
                                 mwregwrite0 (g 'ppc (g 'impl st1))
                                 (g 'prf (g 'impl st1))
                                 (g 'pdmem (g 'impl st1))))
                        (st3 (simulate_a st2 t nil nil nil pc0 bpstate0
                                 ffpredicteddirection0
                                 ffpredictedtarget0 ffwrt0 ffinst0
                                 ffppc0 fdppc0 fdwrt0 fdinst0
                                 fdpredicteddirection0
                                 fdpredictedtarget0 deppc0 desrc10
                                 desrc20 a1 a2 dedest0 deop0 deimm0
                                 deuseimm0 deregwrite0 dememwrite0
                                 dememtoreg0 deisbranch0 dewrt0
                                 depredicteddirection0
                                 depredictedtarget0 emppc0
                                 emis_taken_branch0 emtargetpc0 emarg20
                                 emresult0 emdest0 emwrt0
                                 emmispredictedtaken0
                                 emmispredictednottaken0 emregwrite0
                                 emmemwrite0 emmemtoreg0 dmem0 mmppc0
                                 mmval0 mmdest0 mmwrt0 mmregwrite0
                                 mwppc0 mwval0 mwdest0 mwwrt0
                                 mwregwrite0 (g 'ppc (g 'impl st2))
                                 (g 'prf (g 'impl st2))
                                 (g 'pdmem (g 'impl st2))))
                        (st4 (simulate_a st3 t nil nil nil pc0 bpstate0
                                 ffpredicteddirection0
                                 ffpredictedtarget0 ffwrt0 ffinst0
                                 ffppc0 fdppc0 fdwrt0 fdinst0
                                 fdpredicteddirection0
                                 fdpredictedtarget0 deppc0 desrc10
                                 desrc20 a1 a2 dedest0 deop0 deimm0
                                 deuseimm0 deregwrite0 dememwrite0
                                 dememtoreg0 deisbranch0 dewrt0
                                 depredicteddirection0
                                 depredictedtarget0 emppc0
                                 emis_taken_branch0 emtargetpc0 emarg20
                                 emresult0 emdest0 emwrt0
                                 emmispredictedtaken0
                                 emmispredictednottaken0 emregwrite0
                                 emmemwrite0 emmemtoreg0 dmem0 mmppc0
                                 mmval0 mmdest0 mmwrt0 mmregwrite0
                                 mwppc0 mwval0 mwdest0 mwwrt0
                                 mwregwrite0 (g 'ppc (g 'impl st3))
                                 (g 'prf (g 'impl st3))
                                 (g 'pdmem (g 'impl st3))))
                        (st5 (simulate_a st4 t nil nil nil pc0 bpstate0
                                 ffpredicteddirection0
                                 ffpredictedtarget0 ffwrt0 ffinst0
                                 ffppc0 fdppc0 fdwrt0 fdinst0
                                 fdpredicteddirection0
                                 fdpredictedtarget0 deppc0 desrc10
                                 desrc20 a1 a2 dedest0 deop0 deimm0
                                 deuseimm0 deregwrite0 dememwrite0
                                 dememtoreg0 deisbranch0 dewrt0
                                 depredicteddirection0
                                 depredictedtarget0 emppc0
                                 emis_taken_branch0 emtargetpc0 emarg20
                                 emresult0 emdest0 emwrt0
                                 emmispredictedtaken0
                                 emmispredictednottaken0 emregwrite0
                                 emmemwrite0 emmemtoreg0 dmem0 mmppc0
                                 mmval0 mmdest0 mmwrt0 mmregwrite0
                                 mwppc0 mwval0 mwdest0 mwwrt0
                                 mwregwrite0 (g 'ppc (g 'impl st4))
                                 (g 'prf (g 'impl st4))
                                 (g 'pdmem (g 'impl st4))))
                        (st6 (simulate_a st5 t nil nil nil pc0 bpstate0
                                 ffpredicteddirection0
                                 ffpredictedtarget0 ffwrt0 ffinst0
                                 ffppc0 fdppc0 fdwrt0 fdinst0
                                 fdpredicteddirection0
                                 fdpredictedtarget0 deppc0 desrc10
                                 desrc20 a1 a2 dedest0 deop0 deimm0
                                 deuseimm0 deregwrite0 dememwrite0
                                 dememtoreg0 deisbranch0 dewrt0
                                 depredicteddirection0
                                 depredictedtarget0 emppc0
                                 emis_taken_branch0 emtargetpc0 emarg20
                                 emresult0 emdest0 emwrt0
                                 emmispredictedtaken0
                                 emmispredictednottaken0 emregwrite0
                                 emmemwrite0 emmemtoreg0 dmem0 mmppc0
                                 mmval0 mmdest0 mmwrt0 mmregwrite0
                                 mwppc0 mwval0 mwdest0 mwwrt0
                                 mwregwrite0 (g 'ppc (g 'impl st5))
                                 (g 'prf (g 'impl st5))
                                 (g 'pdmem (g 'impl st5))))
                        (t1 (not (or (or
                                      (or
                                       (or
                                        (or (g 'ffwrt (g 'impl st6))
                                         (g 'fdwrt (g 'impl st6)))
                                        (g 'dewrt (g 'impl st6)))
                                       (g 'emwrt (g 'impl st6)))
                                      (g 'mmwrt (g 'impl st6)))
                                     (g 'mwwrt (g 'impl st6)))))
                        (st7 (simulate_a st6 t nil nil nil pc0 bpstate0
                                 ffpredicteddirection0
                                 ffpredictedtarget0 ffwrt0 ffinst0
                                 ffppc0 fdppc0 fdwrt0 fdinst0
                                 fdpredicteddirection0
                                 fdpredictedtarget0 deppc0 desrc10
                                 desrc20 a1 a2 dedest0 deop0 deimm0
                                 deuseimm0 deregwrite0 dememwrite0
                                 dememtoreg0 deisbranch0 dewrt0
                                 depredicteddirection0
                                 depredictedtarget0 emppc0
                                 emis_taken_branch0 emtargetpc0 emarg20
                                 emresult0 emdest0 emwrt0
                                 emmispredictedtaken0
                                 emmispredictednottaken0 emregwrite0
                                 emmemwrite0 emmemtoreg0 dmem0 mmppc0
                                 mmval0 mmdest0 mmwrt0 mmregwrite0
                                 mwppc0 mwval0 mwdest0 mwwrt0
                                 mwregwrite0 (g 'ppc (g 'impl st6))
                                 (g 'prf (g 'impl st6))
                                 (g 'pdmem (g 'impl st6))))
                        (t2 (not (or (or
                                      (or
                                       (or
                                        (or (g 'ffwrt (g 'impl st7))
                                         (g 'fdwrt (g 'impl st7)))
                                        (g 'dewrt (g 'impl st7)))
                                       (g 'emwrt (g 'impl st7)))
                                      (g 'mmwrt (g 'impl st7)))
                                     (g 'mwwrt (g 'impl st7)))))
                        (st8 (simulate_a st7 t nil nil nil pc0 bpstate0
                                 ffpredicteddirection0
                                 ffpredictedtarget0 ffwrt0 ffinst0
                                 ffppc0 fdppc0 fdwrt0 fdinst0
                                 fdpredicteddirection0
                                 fdpredictedtarget0 deppc0 desrc10
                                 desrc20 a1 a2 dedest0 deop0 deimm0
                                 deuseimm0 deregwrite0 dememwrite0
                                 dememtoreg0 deisbranch0 dewrt0
                                 depredicteddirection0
                                 depredictedtarget0 emppc0
                                 emis_taken_branch0 emtargetpc0 emarg20
                                 emresult0 emdest0 emwrt0
                                 emmispredictedtaken0
                                 emmispredictednottaken0 emregwrite0
                                 emmemwrite0 emmemtoreg0 dmem0 mmppc0
                                 mmval0 mmdest0 mmwrt0 mmregwrite0
                                 mwppc0 mwval0 mwdest0 mwwrt0
                                 mwregwrite0 (g 'ppc (g 'impl st7))
                                 (g 'prf (g 'impl st7))
                                 (g 'pdmem (g 'impl st7))))
                        (counter (cond
                                   (t1 zero)
                                   (t2 (add-1 zero))
                                   (t (add-1 (add-1 zero)))))
                        (st9 (simulate_a st8 nil nil t nil pc0 bpstate0
                                 ffpredicteddirection0
                                 ffpredictedtarget0 ffwrt0 ffinst0
                                 ffppc0 fdppc0 fdwrt0 fdinst0
                                 fdpredicteddirection0
                                 fdpredictedtarget0 deppc0 desrc10
                                 desrc20 a1 a2 dedest0 deop0 deimm0
                                 deuseimm0 deregwrite0 dememwrite0
                                 dememtoreg0 deisbranch0 dewrt0
                                 depredicteddirection0
                                 depredictedtarget0 emppc0
                                 emis_taken_branch0 emtargetpc0 emarg20
                                 emresult0 emdest0 emwrt0
                                 emmispredictedtaken0
                                 emmispredictednottaken0 emregwrite0
                                 emmemwrite0 emmemtoreg0 dmem0 mmppc0
                                 mmval0 mmdest0 mmwrt0 mmregwrite0
                                 mwppc0 mwval0 mwdest0 mwwrt0
                                 mwregwrite0 (g 'ppc (g 'impl st8))
                                 (g 'prf (g 'impl st8))
                                 (g 'pdmem (g 'impl st8))))
                        (s_pc0 (g 'spc (g 'spec st9)))
                        (s_rf0 (g 'srf (g 'spec st9)))
                        (s_dmem0 (g 'sdmem (g 'spec st9)))
                        (st10 (simulate_a st9 nil t nil nil pc0
                                  bpstate0 ffpredicteddirection0
                                  ffpredictedtarget0 ffwrt0 ffinst0
                                  ffppc0 fdppc0 fdwrt0 fdinst0
                                  fdpredicteddirection0
                                  fdpredictedtarget0 deppc0 desrc10
                                  desrc20 a1 a2 dedest0 deop0 deimm0
                                  deuseimm0 deregwrite0 dememwrite0
                                  dememtoreg0 deisbranch0 dewrt0
                                  depredicteddirection0
                                  depredictedtarget0 emppc0
                                  emis_taken_branch0 emtargetpc0
                                  emarg20 emresult0 emdest0 emwrt0
                                  emmispredictedtaken0
                                  emmispredictednottaken0 emregwrite0
                                  emmemwrite0 emmemtoreg0 dmem0 mmppc0
                                  mmval0 mmdest0 mmwrt0 mmregwrite0
                                  mwppc0 mwval0 mwdest0 mwwrt0
                                  mwregwrite0 (g 'ppc (g 'impl st9))
                                  (g 'prf (g 'impl st9))
                                  (g 'pdmem (g 'impl st9))))
                        (s_pc1 (g 'spc (g 'spec st10)))
                        (s_rf1 (g 'srf (g 'spec st10)))
                        (s_dmem1 (g 'sdmem (g 'spec st10)))
                        (st11 (simulate_a st10 nil nil nil t pc0
                                  bpstate0 ffpredicteddirection0
                                  ffpredictedtarget0 ffwrt0 ffinst0
                                  ffppc0 fdppc0 fdwrt0 fdinst0
                                  fdpredicteddirection0
                                  fdpredictedtarget0 deppc0 desrc10
                                  desrc20 a1 a2 dedest0 deop0 deimm0
                                  deuseimm0 deregwrite0 dememwrite0
                                  dememtoreg0 deisbranch0 dewrt0
                                  depredicteddirection0
                                  depredictedtarget0 emppc0
                                  emis_taken_branch0 emtargetpc0
                                  emarg20 emresult0 emdest0 emwrt0
                                  emmispredictedtaken0
                                  emmispredictednottaken0 emregwrite0
                                  emmemwrite0 emmemtoreg0 dmem0 mmppc0
                                  mmval0 mmdest0 mmwrt0 mmregwrite0
                                  mwppc0 mwval0 mwdest0 mwwrt0
                                  mwregwrite0 (g 'ppc (g 'impl st10))
                                  (g 'prf (g 'impl st10))
                                  (g 'pdmem (g 'impl st10))))
                        (st12 (simulate_a st11 nil nil nil nil pc0
                                  bpstate0 ffpredicteddirection0
                                  ffpredictedtarget0 ffwrt0 ffinst0
                                  ffppc0 fdppc0 fdwrt0 fdinst0
                                  fdpredicteddirection0
                                  fdpredictedtarget0 deppc0 desrc10
                                  desrc20 a1 a2 dedest0 deop0 deimm0
                                  deuseimm0 deregwrite0 dememwrite0
                                  dememtoreg0 deisbranch0 dewrt0
                                  depredicteddirection0
                                  depredictedtarget0 emppc0
                                  emis_taken_branch0 emtargetpc0
                                  emarg20 emresult0 emdest0 emwrt0
                                  emmispredictedtaken0
                                  emmispredictednottaken0 emregwrite0
                                  emmemwrite0 emmemtoreg0 dmem0 mmppc0
                                  mmval0 mmdest0 mmwrt0 mmregwrite0
                                  mwppc0 mwval0 mwdest0 mwwrt0
                                  mwregwrite0 (g 'ppc (g 'impl st11))
                                  (g 'prf (g 'impl st11))
                                  (g 'pdmem (g 'impl st11))))
                        (st13 (simulate_a st12 nil nil nil nil pc0
                                  bpstate0 ffpredicteddirection0
                                  ffpredictedtarget0 ffwrt0 ffinst0
                                  ffppc0 fdppc0 fdwrt0 fdinst0
                                  fdpredicteddirection0
                                  fdpredictedtarget0 deppc0 desrc10
                                  desrc20 a1 a2 dedest0 deop0 deimm0
                                  deuseimm0 deregwrite0 dememwrite0
                                  dememtoreg0 deisbranch0 dewrt0
                                  depredicteddirection0
                                  depredictedtarget0 emppc0
                                  emis_taken_branch0 emtargetpc0
                                  emarg20 emresult0 emdest0 emwrt0
                                  emmispredictedtaken0
                                  emmispredictednottaken0 emregwrite0
                                  emmemwrite0 emmemtoreg0 dmem0 mmppc0
                                  mmval0 mmdest0 mmwrt0 mmregwrite0
                                  mwppc0 mwval0 mwdest0 mwwrt0
                                  mwregwrite0 (g 'ppc (g 'impl st12))
                                  (g 'prf (g 'impl st12))
                                  (g 'pdmem (g 'impl st12))))
                        (st14 (simulate_a st13 nil nil nil nil pc0
                                  bpstate0 ffpredicteddirection0
                                  ffpredictedtarget0 ffwrt0 ffinst0
                                  ffppc0 fdppc0 fdwrt0 fdinst0
                                  fdpredicteddirection0
                                  fdpredictedtarget0 deppc0 desrc10
                                  desrc20 a1 a2 dedest0 deop0 deimm0
                                  deuseimm0 deregwrite0 dememwrite0
                                  dememtoreg0 deisbranch0 dewrt0
                                  depredicteddirection0
                                  depredictedtarget0 emppc0
                                  emis_taken_branch0 emtargetpc0
                                  emarg20 emresult0 emdest0 emwrt0
                                  emmispredictedtaken0
                                  emmispredictednottaken0 emregwrite0
                                  emmemwrite0 emmemtoreg0 dmem0 mmppc0
                                  mmval0 mmdest0 mmwrt0 mmregwrite0
                                  mwppc0 mwval0 mwdest0 mwwrt0
                                  mwregwrite0 (g 'ppc (g 'impl st13))
                                  (g 'prf (g 'impl st13))
                                  (g 'pdmem (g 'impl st13))))
                        (st15 (simulate_a st14 nil nil nil nil pc0
                                  bpstate0 ffpredicteddirection0
                                  ffpredictedtarget0 ffwrt0 ffinst0
                                  ffppc0 fdppc0 fdwrt0 fdinst0
                                  fdpredicteddirection0
                                  fdpredictedtarget0 deppc0 desrc10
                                  desrc20 a1 a2 dedest0 deop0 deimm0
                                  deuseimm0 deregwrite0 dememwrite0
                                  dememtoreg0 deisbranch0 dewrt0
                                  depredicteddirection0
                                  depredictedtarget0 emppc0
                                  emis_taken_branch0 emtargetpc0
                                  emarg20 emresult0 emdest0 emwrt0
                                  emmispredictedtaken0
                                  emmispredictednottaken0 emregwrite0
                                  emmemwrite0 emmemtoreg0 dmem0 mmppc0
                                  mmval0 mmdest0 mmwrt0 mmregwrite0
                                  mwppc0 mwval0 mwdest0 mwwrt0
                                  mwregwrite0 (g 'ppc (g 'impl st14))
                                  (g 'prf (g 'impl st14))
                                  (g 'pdmem (g 'impl st14))))
                        (st16 (simulate_a st15 nil nil nil nil pc0
                                  bpstate0 ffpredicteddirection0
                                  ffpredictedtarget0 ffwrt0 ffinst0
                                  ffppc0 fdppc0 fdwrt0 fdinst0
                                  fdpredicteddirection0
                                  fdpredictedtarget0 deppc0 desrc10
                                  desrc20 a1 a2 dedest0 deop0 deimm0
                                  deuseimm0 deregwrite0 dememwrite0
                                  dememtoreg0 deisbranch0 dewrt0
                                  depredicteddirection0
                                  depredictedtarget0 emppc0
                                  emis_taken_branch0 emtargetpc0
                                  emarg20 emresult0 emdest0 emwrt0
                                  emmispredictedtaken0
                                  emmispredictednottaken0 emregwrite0
                                  emmemwrite0 emmemtoreg0 dmem0 mmppc0
                                  mmval0 mmdest0 mmwrt0 mmregwrite0
                                  mwppc0 mwval0 mwdest0 mwwrt0
                                  mwregwrite0 (g 'ppc (g 'impl st15))
                                  (g 'prf (g 'impl st15))
                                  (g 'pdmem (g 'impl st15))))
                        (st17 (simulate_a st16 nil nil nil nil pc0
                                  bpstate0 ffpredicteddirection0
                                  ffpredictedtarget0 ffwrt0 ffinst0
                                  ffppc0 fdppc0 fdwrt0 fdinst0
                                  fdpredicteddirection0
                                  fdpredictedtarget0 deppc0 desrc10
                                  desrc20 a1 a2 dedest0 deop0 deimm0
                                  deuseimm0 deregwrite0 dememwrite0
                                  dememtoreg0 deisbranch0 dewrt0
                                  depredicteddirection0
                                  depredictedtarget0 emppc0
                                  emis_taken_branch0 emtargetpc0
                                  emarg20 emresult0 emdest0 emwrt0
                                  emmispredictedtaken0
                                  emmispredictednottaken0 emregwrite0
                                  emmemwrite0 emmemtoreg0 dmem0 mmppc0
                                  mmval0 mmdest0 mmwrt0 mmregwrite0
                                  mwppc0 mwval0 mwdest0 mwwrt0
                                  mwregwrite0 (g 'ppc (g 'impl st16))
                                  (g 'prf (g 'impl st16))
                                  (g 'pdmem (g 'impl st16))))
                        (t1 (g 'mwwrt (g 'impl st17)))
                        (st18 (simulate_a st17 nil nil nil nil pc0
                                  bpstate0 ffpredicteddirection0
                                  ffpredictedtarget0 ffwrt0 ffinst0
                                  ffppc0 fdppc0 fdwrt0 fdinst0
                                  fdpredicteddirection0
                                  fdpredictedtarget0 deppc0 desrc10
                                  desrc20 a1 a2 dedest0 deop0 deimm0
                                  deuseimm0 deregwrite0 dememwrite0
                                  dememtoreg0 deisbranch0 dewrt0
                                  depredicteddirection0
                                  depredictedtarget0 emppc0
                                  emis_taken_branch0 emtargetpc0
                                  emarg20 emresult0 emdest0 emwrt0
                                  emmispredictedtaken0
                                  emmispredictednottaken0 emregwrite0
                                  emmemwrite0 emmemtoreg0 dmem0 mmppc0
                                  mmval0 mmdest0 mmwrt0 mmregwrite0
                                  mwppc0 mwval0 mwdest0 mwwrt0
                                  mwregwrite0 (g 'ppc (g 'impl st17))
                                  (g 'prf (g 'impl st17))
                                  (g 'pdmem (g 'impl st17))))
                        (t2 (g 'mwwrt (g 'impl st18)))
                        (st19 (simulate_a st18 nil nil nil nil pc0
                                  bpstate0 ffpredicteddirection0
                                  ffpredictedtarget0 ffwrt0 ffinst0
                                  ffppc0 fdppc0 fdwrt0 fdinst0
                                  fdpredicteddirection0
                                  fdpredictedtarget0 deppc0 desrc10
                                  desrc20 a1 a2 dedest0 deop0 deimm0
                                  deuseimm0 deregwrite0 dememwrite0
                                  dememtoreg0 deisbranch0 dewrt0
                                  depredicteddirection0
                                  depredictedtarget0 emppc0
                                  emis_taken_branch0 emtargetpc0
                                  emarg20 emresult0 emdest0 emwrt0
                                  emmispredictedtaken0
                                  emmispredictednottaken0 emregwrite0
                                  emmemwrite0 emmemtoreg0 dmem0 mmppc0
                                  mmval0 mmdest0 mmwrt0 mmregwrite0
                                  mwppc0 mwval0 mwdest0 mwwrt0
                                  mwregwrite0 (g 'ppc (g 'impl st18))
                                  (g 'prf (g 'impl st18))
                                  (g 'pdmem (g 'impl st18))))
                        (t3 (g 'mwwrt (g 'impl st19)))
                        (st20 (simulate_a st19 nil nil nil nil pc0
                                  bpstate0 ffpredicteddirection0
                                  ffpredictedtarget0 ffwrt0 ffinst0
                                  ffppc0 fdppc0 fdwrt0 fdinst0
                                  fdpredicteddirection0
                                  fdpredictedtarget0 deppc0 desrc10
                                  desrc20 a1 a2 dedest0 deop0 deimm0
                                  deuseimm0 deregwrite0 dememwrite0
                                  dememtoreg0 deisbranch0 dewrt0
                                  depredicteddirection0
                                  depredictedtarget0 emppc0
                                  emis_taken_branch0 emtargetpc0
                                  emarg20 emresult0 emdest0 emwrt0
                                  emmispredictedtaken0
                                  emmispredictednottaken0 emregwrite0
                                  emmemwrite0 emmemtoreg0 dmem0 mmppc0
                                  mmval0 mmdest0 mmwrt0 mmregwrite0
                                  mwppc0 mwval0 mwdest0 mwwrt0
                                  mwregwrite0 (g 'ppc (g 'impl st19))
                                  (g 'prf (g 'impl st19))
                                  (g 'pdmem (g 'impl st19))))
                        (t4 (g 'mwwrt (g 'impl st20)))
                        (st21 (simulate_a st20 nil nil nil nil pc0
                                  bpstate0 ffpredicteddirection0
                                  ffpredictedtarget0 ffwrt0 ffinst0
                                  ffppc0 fdppc0 fdwrt0 fdinst0
                                  fdpredicteddirection0
                                  fdpredictedtarget0 deppc0 desrc10
                                  desrc20 a1 a2 dedest0 deop0 deimm0
                                  deuseimm0 deregwrite0 dememwrite0
                                  dememtoreg0 deisbranch0 dewrt0
                                  depredicteddirection0
                                  depredictedtarget0 emppc0
                                  emis_taken_branch0 emtargetpc0
                                  emarg20 emresult0 emdest0 emwrt0
                                  emmispredictedtaken0
                                  emmispredictednottaken0 emregwrite0
                                  emmemwrite0 emmemtoreg0 dmem0 mmppc0
                                  mmval0 mmdest0 mmwrt0 mmregwrite0
                                  mwppc0 mwval0 mwdest0 mwwrt0
                                  mwregwrite0 (g 'ppc (g 'impl st20))
                                  (g 'prf (g 'impl st20))
                                  (g 'pdmem (g 'impl st20))))
                        (t5 (g 'mwwrt (g 'impl st21)))
                        (st22 (simulate_a st21 nil nil nil nil pc0
                                  bpstate0 ffpredicteddirection0
                                  ffpredictedtarget0 ffwrt0 ffinst0
                                  ffppc0 fdppc0 fdwrt0 fdinst0
                                  fdpredicteddirection0
                                  fdpredictedtarget0 deppc0 desrc10
                                  desrc20 a1 a2 dedest0 deop0 deimm0
                                  deuseimm0 deregwrite0 dememwrite0
                                  dememtoreg0 deisbranch0 dewrt0
                                  depredicteddirection0
                                  depredictedtarget0 emppc0
                                  emis_taken_branch0 emtargetpc0
                                  emarg20 emresult0 emdest0 emwrt0
                                  emmispredictedtaken0
                                  emmispredictednottaken0 emregwrite0
                                  emmemwrite0 emmemtoreg0 dmem0 mmppc0
                                  mmval0 mmdest0 mmwrt0 mmregwrite0
                                  mwppc0 mwval0 mwdest0 mwwrt0
                                  mwregwrite0 (g 'ppc (g 'impl st21))
                                  (g 'prf (g 'impl st21))
                                  (g 'pdmem (g 'impl st21))))
                        (t6 (g 'mwwrt (g 'impl st22)))
                        (rank_w (cond
                                  ((and (equal counter zero) t1)
                                   (add-1 counter))
                                  ((and
                                    (or (equal counter zero)
                                     (equal counter (add-1 zero)))
                                    t2)
                                   (add-1 (add-1 counter)))
                                  (t3 (add-1 (add-1 (add-1 counter))))
                                  (t4 (add-1
                                       (add-1 (add-1 (add-1 counter)))))
                                  (t5 (add-1
                                       (add-1
                                        (add-1 (add-1 (add-1 counter))))))
                                  (t6 (add-1
                                       (add-1
                                        (add-1
                                         (add-1
                                          (add-1 (add-1 counter)))))))
                                  (t (add-1
                                      (add-1
                                       (add-1
                                        (add-1
                                         (add-1
                                          (add-1 (add-1 counter))))))))))
                        (st23 (simulate_a st22 nil nil nil t pc0
                                  bpstate0 ffpredicteddirection0
                                  ffpredictedtarget0 ffwrt0 ffinst0
                                  ffppc0 fdppc0 fdwrt0 fdinst0
                                  fdpredicteddirection0
                                  fdpredictedtarget0 deppc0 desrc10
                                  desrc20 a1 a2 dedest0 deop0 deimm0
                                  deuseimm0 deregwrite0 dememwrite0
                                  dememtoreg0 deisbranch0 dewrt0
                                  depredicteddirection0
                                  depredictedtarget0 emppc0
                                  emis_taken_branch0 emtargetpc0
                                  emarg20 emresult0 emdest0 emwrt0
                                  emmispredictedtaken0
                                  emmispredictednottaken0 emregwrite0
                                  emmemwrite0 emmemtoreg0 dmem0 mmppc0
                                  mmval0 mmdest0 mmwrt0 mmregwrite0
                                  mwppc0 mwval0 mwdest0 mwwrt0
                                  mwregwrite0 (g 'ppc (g 'impl st22))
                                  (g 'prf (g 'impl st22))
                                  (g 'pdmem (g 'impl st22))))
                        (st24 (simulate_a st23 nil nil nil nil pc0
                                  bpstate0 ffpredicteddirection0
                                  ffpredictedtarget0 ffwrt0 ffinst0
                                  ffppc0 fdppc0 fdwrt0 fdinst0
                                  fdpredicteddirection0
                                  fdpredictedtarget0 deppc0 desrc10
                                  desrc20 a1 a2 dedest0 deop0 deimm0
                                  deuseimm0 deregwrite0 dememwrite0
                                  dememtoreg0 deisbranch0 dewrt0
                                  depredicteddirection0
                                  depredictedtarget0 emppc0
                                  emis_taken_branch0 emtargetpc0
                                  emarg20 emresult0 emdest0 emwrt0
                                  emmispredictedtaken0
                                  emmispredictednottaken0 emregwrite0
                                  emmemwrite0 emmemtoreg0 dmem0 mmppc0
                                  mmval0 mmdest0 mmwrt0 mmregwrite0
                                  mwppc0 mwval0 mwdest0 mwwrt0
                                  mwregwrite0 (g 'ppc (g 'impl st23))
                                  (g 'prf (g 'impl st23))
                                  (g 'pdmem (g 'impl st23))))
                        (st25 (simulate_a st24 t nil nil nil pc0
                                  bpstate0 ffpredicteddirection0
                                  ffpredictedtarget0 ffwrt0 ffinst0
                                  ffppc0 fdppc0 fdwrt0 fdinst0
                                  fdpredicteddirection0
                                  fdpredictedtarget0 deppc0 desrc10
                                  desrc20 a1 a2 dedest0 deop0 deimm0
                                  deuseimm0 deregwrite0 dememwrite0
                                  dememtoreg0 deisbranch0 dewrt0
                                  depredicteddirection0
                                  depredictedtarget0 emppc0
                                  emis_taken_branch0 emtargetpc0
                                  emarg20 emresult0 emdest0 emwrt0
                                  emmispredictedtaken0
                                  emmispredictednottaken0 emregwrite0
                                  emmemwrite0 emmemtoreg0 dmem0 mmppc0
                                  mmval0 mmdest0 mmwrt0 mmregwrite0
                                  mwppc0 mwval0 mwdest0 mwwrt0
                                  mwregwrite0 (g 'ppc (g 'impl st24))
                                  (g 'prf (g 'impl st24))
                                  (g 'pdmem (g 'impl st24))))
                        (st26 (simulate_a st25 t nil nil nil pc0
                                  bpstate0 ffpredicteddirection0
                                  ffpredictedtarget0 ffwrt0 ffinst0
                                  ffppc0 fdppc0 fdwrt0 fdinst0
                                  fdpredicteddirection0
                                  fdpredictedtarget0 deppc0 desrc10
                                  desrc20 a1 a2 dedest0 deop0 deimm0
                                  deuseimm0 deregwrite0 dememwrite0
                                  dememtoreg0 deisbranch0 dewrt0
                                  depredicteddirection0
                                  depredictedtarget0 emppc0
                                  emis_taken_branch0 emtargetpc0
                                  emarg20 emresult0 emdest0 emwrt0
                                  emmispredictedtaken0
                                  emmispredictednottaken0 emregwrite0
                                  emmemwrite0 emmemtoreg0 dmem0 mmppc0
                                  mmval0 mmdest0 mmwrt0 mmregwrite0
                                  mwppc0 mwval0 mwdest0 mwwrt0
                                  mwregwrite0 (g 'ppc (g 'impl st25))
                                  (g 'prf (g 'impl st25))
                                  (g 'pdmem (g 'impl st25))))
                        (st27 (simulate_a st26 t nil nil nil pc0
                                  bpstate0 ffpredicteddirection0
                                  ffpredictedtarget0 ffwrt0 ffinst0
                                  ffppc0 fdppc0 fdwrt0 fdinst0
                                  fdpredicteddirection0
                                  fdpredictedtarget0 deppc0 desrc10
                                  desrc20 a1 a2 dedest0 deop0 deimm0
                                  deuseimm0 deregwrite0 dememwrite0
                                  dememtoreg0 deisbranch0 dewrt0
                                  depredicteddirection0
                                  depredictedtarget0 emppc0
                                  emis_taken_branch0 emtargetpc0
                                  emarg20 emresult0 emdest0 emwrt0
                                  emmispredictedtaken0
                                  emmispredictednottaken0 emregwrite0
                                  emmemwrite0 emmemtoreg0 dmem0 mmppc0
                                  mmval0 mmdest0 mmwrt0 mmregwrite0
                                  mwppc0 mwval0 mwdest0 mwwrt0
                                  mwregwrite0 (g 'ppc (g 'impl st26))
                                  (g 'prf (g 'impl st26))
                                  (g 'pdmem (g 'impl st26))))
                        (st28 (simulate_a st27 t nil nil nil pc0
                                  bpstate0 ffpredicteddirection0
                                  ffpredictedtarget0 ffwrt0 ffinst0
                                  ffppc0 fdppc0 fdwrt0 fdinst0
                                  fdpredicteddirection0
                                  fdpredictedtarget0 deppc0 desrc10
                                  desrc20 a1 a2 dedest0 deop0 deimm0
                                  deuseimm0 deregwrite0 dememwrite0
                                  dememtoreg0 deisbranch0 dewrt0
                                  depredicteddirection0
                                  depredictedtarget0 emppc0
                                  emis_taken_branch0 emtargetpc0
                                  emarg20 emresult0 emdest0 emwrt0
                                  emmispredictedtaken0
                                  emmispredictednottaken0 emregwrite0
                                  emmemwrite0 emmemtoreg0 dmem0 mmppc0
                                  mmval0 mmdest0 mmwrt0 mmregwrite0
                                  mwppc0 mwval0 mwdest0 mwwrt0
                                  mwregwrite0 (g 'ppc (g 'impl st27))
                                  (g 'prf (g 'impl st27))
                                  (g 'pdmem (g 'impl st27))))
                        (st29 (simulate_a st28 t nil nil nil pc0
                                  bpstate0 ffpredicteddirection0
                                  ffpredictedtarget0 ffwrt0 ffinst0
                                  ffppc0 fdppc0 fdwrt0 fdinst0
                                  fdpredicteddirection0
                                  fdpredictedtarget0 deppc0 desrc10
                                  desrc20 a1 a2 dedest0 deop0 deimm0
                                  deuseimm0 deregwrite0 dememwrite0
                                  dememtoreg0 deisbranch0 dewrt0
                                  depredicteddirection0
                                  depredictedtarget0 emppc0
                                  emis_taken_branch0 emtargetpc0
                                  emarg20 emresult0 emdest0 emwrt0
                                  emmispredictedtaken0
                                  emmispredictednottaken0 emregwrite0
                                  emmemwrite0 emmemtoreg0 dmem0 mmppc0
                                  mmval0 mmdest0 mmwrt0 mmregwrite0
                                  mwppc0 mwval0 mwdest0 mwwrt0
                                  mwregwrite0 (g 'ppc (g 'impl st28))
                                  (g 'prf (g 'impl st28))
                                  (g 'pdmem (g 'impl st28))))
                        (st30 (simulate_a st29 t nil nil nil pc0
                                  bpstate0 ffpredicteddirection0
                                  ffpredictedtarget0 ffwrt0 ffinst0
                                  ffppc0 fdppc0 fdwrt0 fdinst0
                                  fdpredicteddirection0
                                  fdpredictedtarget0 deppc0 desrc10
                                  desrc20 a1 a2 dedest0 deop0 deimm0
                                  deuseimm0 deregwrite0 dememwrite0
                                  dememtoreg0 deisbranch0 dewrt0
                                  depredicteddirection0
                                  depredictedtarget0 emppc0
                                  emis_taken_branch0 emtargetpc0
                                  emarg20 emresult0 emdest0 emwrt0
                                  emmispredictedtaken0
                                  emmispredictednottaken0 emregwrite0
                                  emmemwrite0 emmemtoreg0 dmem0 mmppc0
                                  mmval0 mmdest0 mmwrt0 mmregwrite0
                                  mwppc0 mwval0 mwdest0 mwwrt0
                                  mwregwrite0 (g 'ppc (g 'impl st29))
                                  (g 'prf (g 'impl st29))
                                  (g 'pdmem (g 'impl st29))))
                        (t1 (not (or (or
                                      (or
                                       (or
                                        (or (g 'ffwrt (g 'impl st30))
                                         (g 'fdwrt (g 'impl st30)))
                                        (g 'dewrt (g 'impl st30)))
                                       (g 'emwrt (g 'impl st30)))
                                      (g 'mmwrt (g 'impl st30)))
                                     (g 'mwwrt (g 'impl st30)))))
                        (st31 (simulate_a st30 t nil nil nil pc0
                                  bpstate0 ffpredicteddirection0
                                  ffpredictedtarget0 ffwrt0 ffinst0
                                  ffppc0 fdppc0 fdwrt0 fdinst0
                                  fdpredicteddirection0
                                  fdpredictedtarget0 deppc0 desrc10
                                  desrc20 a1 a2 dedest0 deop0 deimm0
                                  deuseimm0 deregwrite0 dememwrite0
                                  dememtoreg0 deisbranch0 dewrt0
                                  depredicteddirection0
                                  depredictedtarget0 emppc0
                                  emis_taken_branch0 emtargetpc0
                                  emarg20 emresult0 emdest0 emwrt0
                                  emmispredictedtaken0
                                  emmispredictednottaken0 emregwrite0
                                  emmemwrite0 emmemtoreg0 dmem0 mmppc0
                                  mmval0 mmdest0 mmwrt0 mmregwrite0
                                  mwppc0 mwval0 mwdest0 mwwrt0
                                  mwregwrite0 (g 'ppc (g 'impl st30))
                                  (g 'prf (g 'impl st30))
                                  (g 'pdmem (g 'impl st30))))
                        (t2 (not (or (or
                                      (or
                                       (or
                                        (or (g 'ffwrt (g 'impl st31))
                                         (g 'fdwrt (g 'impl st31)))
                                        (g 'dewrt (g 'impl st31)))
                                       (g 'emwrt (g 'impl st31)))
                                      (g 'mmwrt (g 'impl st31)))
                                     (g 'mwwrt (g 'impl st31)))))
                        (st32 (simulate_a st31 t nil nil nil pc0
                                  bpstate0 ffpredicteddirection0
                                  ffpredictedtarget0 ffwrt0 ffinst0
                                  ffppc0 fdppc0 fdwrt0 fdinst0
                                  fdpredicteddirection0
                                  fdpredictedtarget0 deppc0 desrc10
                                  desrc20 a1 a2 dedest0 deop0 deimm0
                                  deuseimm0 deregwrite0 dememwrite0
                                  dememtoreg0 deisbranch0 dewrt0
                                  depredicteddirection0
                                  depredictedtarget0 emppc0
                                  emis_taken_branch0 emtargetpc0
                                  emarg20 emresult0 emdest0 emwrt0
                                  emmispredictedtaken0
                                  emmispredictednottaken0 emregwrite0
                                  emmemwrite0 emmemtoreg0 dmem0 mmppc0
                                  mmval0 mmdest0 mmwrt0 mmregwrite0
                                  mwppc0 mwval0 mwdest0 mwwrt0
                                  mwregwrite0 (g 'ppc (g 'impl st31))
                                  (g 'prf (g 'impl st31))
                                  (g 'pdmem (g 'impl st31))))
                        (counter (cond
                                   (t1 zero)
                                   (t2 (add-1 zero))
                                   (t (add-1 (add-1 zero)))))
                        (i_pc (g 'ppc (g 'impl st32)))
                        (i_rf (g 'prf (g 'impl st32)))
                        (i_dmem (g 'pdmem (g 'impl st32)))
                        (st33 (simulate_a st32 nil nil nil t pc0
                                  bpstate0 ffpredicteddirection0
                                  ffpredictedtarget0 ffwrt0 ffinst0
                                  ffppc0 fdppc0 fdwrt0 fdinst0
                                  fdpredicteddirection0
                                  fdpredictedtarget0 deppc0 desrc10
                                  desrc20 a1 a2 dedest0 deop0 deimm0
                                  deuseimm0 deregwrite0 dememwrite0
                                  dememtoreg0 deisbranch0 dewrt0
                                  depredicteddirection0
                                  depredictedtarget0 emppc0
                                  emis_taken_branch0 emtargetpc0
                                  emarg20 emresult0 emdest0 emwrt0
                                  emmispredictedtaken0
                                  emmispredictednottaken0 emregwrite0
                                  emmemwrite0 emmemtoreg0 dmem0 mmppc0
                                  mmval0 mmdest0 mmwrt0 mmregwrite0
                                  mwppc0 mwval0 mwdest0 mwwrt0
                                  mwregwrite0 (g 'ppc (g 'impl st32))
                                  (g 'prf (g 'impl st32))
                                  (g 'pdmem (g 'impl st32))))
                        (st34 (simulate_a st33 nil nil nil nil pc0
                                  bpstate0 ffpredicteddirection0
                                  ffpredictedtarget0 ffwrt0 ffinst0
                                  ffppc0 fdppc0 fdwrt0 fdinst0
                                  fdpredicteddirection0
                                  fdpredictedtarget0 deppc0 desrc10
                                  desrc20 a1 a2 dedest0 deop0 deimm0
                                  deuseimm0 deregwrite0 dememwrite0
                                  dememtoreg0 deisbranch0 dewrt0
                                  depredicteddirection0
                                  depredictedtarget0 emppc0
                                  emis_taken_branch0 emtargetpc0
                                  emarg20 emresult0 emdest0 emwrt0
                                  emmispredictedtaken0
                                  emmispredictednottaken0 emregwrite0
                                  emmemwrite0 emmemtoreg0 dmem0 mmppc0
                                  mmval0 mmdest0 mmwrt0 mmregwrite0
                                  mwppc0 mwval0 mwdest0 mwwrt0
                                  mwregwrite0 (g 'ppc (g 'impl st33))
                                  (g 'prf (g 'impl st33))
                                  (g 'pdmem (g 'impl st33))))
                        (st35 (simulate_a st34 nil nil nil nil pc0
                                  bpstate0 ffpredicteddirection0
                                  ffpredictedtarget0 ffwrt0 ffinst0
                                  ffppc0 fdppc0 fdwrt0 fdinst0
                                  fdpredicteddirection0
                                  fdpredictedtarget0 deppc0 desrc10
                                  desrc20 a1 a2 dedest0 deop0 deimm0
                                  deuseimm0 deregwrite0 dememwrite0
                                  dememtoreg0 deisbranch0 dewrt0
                                  depredicteddirection0
                                  depredictedtarget0 emppc0
                                  emis_taken_branch0 emtargetpc0
                                  emarg20 emresult0 emdest0 emwrt0
                                  emmispredictedtaken0
                                  emmispredictednottaken0 emregwrite0
                                  emmemwrite0 emmemtoreg0 dmem0 mmppc0
                                  mmval0 mmdest0 mmwrt0 mmregwrite0
                                  mwppc0 mwval0 mwdest0 mwwrt0
                                  mwregwrite0 (g 'ppc (g 'impl st34))
                                  (g 'prf (g 'impl st34))
                                  (g 'pdmem (g 'impl st34))))
                        (st36 (simulate_a st35 nil nil nil nil pc0
                                  bpstate0 ffpredicteddirection0
                                  ffpredictedtarget0 ffwrt0 ffinst0
                                  ffppc0 fdppc0 fdwrt0 fdinst0
                                  fdpredicteddirection0
                                  fdpredictedtarget0 deppc0 desrc10
                                  desrc20 a1 a2 dedest0 deop0 deimm0
                                  deuseimm0 deregwrite0 dememwrite0
                                  dememtoreg0 deisbranch0 dewrt0
                                  depredicteddirection0
                                  depredictedtarget0 emppc0
                                  emis_taken_branch0 emtargetpc0
                                  emarg20 emresult0 emdest0 emwrt0
                                  emmispredictedtaken0
                                  emmispredictednottaken0 emregwrite0
                                  emmemwrite0 emmemtoreg0 dmem0 mmppc0
                                  mmval0 mmdest0 mmwrt0 mmregwrite0
                                  mwppc0 mwval0 mwdest0 mwwrt0
                                  mwregwrite0 (g 'ppc (g 'impl st35))
                                  (g 'prf (g 'impl st35))
                                  (g 'pdmem (g 'impl st35))))
                        (st37 (simulate_a st36 nil nil nil nil pc0
                                  bpstate0 ffpredicteddirection0
                                  ffpredictedtarget0 ffwrt0 ffinst0
                                  ffppc0 fdppc0 fdwrt0 fdinst0
                                  fdpredicteddirection0
                                  fdpredictedtarget0 deppc0 desrc10
                                  desrc20 a1 a2 dedest0 deop0 deimm0
                                  deuseimm0 deregwrite0 dememwrite0
                                  dememtoreg0 deisbranch0 dewrt0
                                  depredicteddirection0
                                  depredictedtarget0 emppc0
                                  emis_taken_branch0 emtargetpc0
                                  emarg20 emresult0 emdest0 emwrt0
                                  emmispredictedtaken0
                                  emmispredictednottaken0 emregwrite0
                                  emmemwrite0 emmemtoreg0 dmem0 mmppc0
                                  mmval0 mmdest0 mmwrt0 mmregwrite0
                                  mwppc0 mwval0 mwdest0 mwwrt0
                                  mwregwrite0 (g 'ppc (g 'impl st36))
                                  (g 'prf (g 'impl st36))
                                  (g 'pdmem (g 'impl st36))))
                        (st38 (simulate_a st37 nil nil nil nil pc0
                                  bpstate0 ffpredicteddirection0
                                  ffpredictedtarget0 ffwrt0 ffinst0
                                  ffppc0 fdppc0 fdwrt0 fdinst0
                                  fdpredicteddirection0
                                  fdpredictedtarget0 deppc0 desrc10
                                  desrc20 a1 a2 dedest0 deop0 deimm0
                                  deuseimm0 deregwrite0 dememwrite0
                                  dememtoreg0 deisbranch0 dewrt0
                                  depredicteddirection0
                                  depredictedtarget0 emppc0
                                  emis_taken_branch0 emtargetpc0
                                  emarg20 emresult0 emdest0 emwrt0
                                  emmispredictedtaken0
                                  emmispredictednottaken0 emregwrite0
                                  emmemwrite0 emmemtoreg0 dmem0 mmppc0
                                  mmval0 mmdest0 mmwrt0 mmregwrite0
                                  mwppc0 mwval0 mwdest0 mwwrt0
                                  mwregwrite0 (g 'ppc (g 'impl st37))
                                  (g 'prf (g 'impl st37))
                                  (g 'pdmem (g 'impl st37))))
                        (st39 (simulate_a st38 nil nil nil nil pc0
                                  bpstate0 ffpredicteddirection0
                                  ffpredictedtarget0 ffwrt0 ffinst0
                                  ffppc0 fdppc0 fdwrt0 fdinst0
                                  fdpredicteddirection0
                                  fdpredictedtarget0 deppc0 desrc10
                                  desrc20 a1 a2 dedest0 deop0 deimm0
                                  deuseimm0 deregwrite0 dememwrite0
                                  dememtoreg0 deisbranch0 dewrt0
                                  depredicteddirection0
                                  depredictedtarget0 emppc0
                                  emis_taken_branch0 emtargetpc0
                                  emarg20 emresult0 emdest0 emwrt0
                                  emmispredictedtaken0
                                  emmispredictednottaken0 emregwrite0
                                  emmemwrite0 emmemtoreg0 dmem0 mmppc0
                                  mmval0 mmdest0 mmwrt0 mmregwrite0
                                  mwppc0 mwval0 mwdest0 mwwrt0
                                  mwregwrite0 (g 'ppc (g 'impl st38))
                                  (g 'prf (g 'impl st38))
                                  (g 'pdmem (g 'impl st38))))
                        (st40 (simulate_a st39 nil nil nil nil pc0
                                  bpstate0 ffpredicteddirection0
                                  ffpredictedtarget0 ffwrt0 ffinst0
                                  ffppc0 fdppc0 fdwrt0 fdinst0
                                  fdpredicteddirection0
                                  fdpredictedtarget0 deppc0 desrc10
                                  desrc20 a1 a2 dedest0 deop0 deimm0
                                  deuseimm0 deregwrite0 dememwrite0
                                  dememtoreg0 deisbranch0 dewrt0
                                  depredicteddirection0
                                  depredictedtarget0 emppc0
                                  emis_taken_branch0 emtargetpc0
                                  emarg20 emresult0 emdest0 emwrt0
                                  emmispredictedtaken0
                                  emmispredictednottaken0 emregwrite0
                                  emmemwrite0 emmemtoreg0 dmem0 mmppc0
                                  mmval0 mmdest0 mmwrt0 mmregwrite0
                                  mwppc0 mwval0 mwdest0 mwwrt0
                                  mwregwrite0 (g 'ppc (g 'impl st39))
                                  (g 'prf (g 'impl st39))
                                  (g 'pdmem (g 'impl st39))))
                        (t1 (g 'mwwrt (g 'impl st40)))
                        (st41 (simulate_a st40 nil nil nil nil pc0
                                  bpstate0 ffpredicteddirection0
                                  ffpredictedtarget0 ffwrt0 ffinst0
                                  ffppc0 fdppc0 fdwrt0 fdinst0
                                  fdpredicteddirection0
                                  fdpredictedtarget0 deppc0 desrc10
                                  desrc20 a1 a2 dedest0 deop0 deimm0
                                  deuseimm0 deregwrite0 dememwrite0
                                  dememtoreg0 deisbranch0 dewrt0
                                  depredicteddirection0
                                  depredictedtarget0 emppc0
                                  emis_taken_branch0 emtargetpc0
                                  emarg20 emresult0 emdest0 emwrt0
                                  emmispredictedtaken0
                                  emmispredictednottaken0 emregwrite0
                                  emmemwrite0 emmemtoreg0 dmem0 mmppc0
                                  mmval0 mmdest0 mmwrt0 mmregwrite0
                                  mwppc0 mwval0 mwdest0 mwwrt0
                                  mwregwrite0 (g 'ppc (g 'impl st40))
                                  (g 'prf (g 'impl st40))
                                  (g 'pdmem (g 'impl st40))))
                        (t2 (g 'mwwrt (g 'impl st41)))
                        (st42 (simulate_a st41 nil nil nil nil pc0
                                  bpstate0 ffpredicteddirection0
                                  ffpredictedtarget0 ffwrt0 ffinst0
                                  ffppc0 fdppc0 fdwrt0 fdinst0
                                  fdpredicteddirection0
                                  fdpredictedtarget0 deppc0 desrc10
                                  desrc20 a1 a2 dedest0 deop0 deimm0
                                  deuseimm0 deregwrite0 dememwrite0
                                  dememtoreg0 deisbranch0 dewrt0
                                  depredicteddirection0
                                  depredictedtarget0 emppc0
                                  emis_taken_branch0 emtargetpc0
                                  emarg20 emresult0 emdest0 emwrt0
                                  emmispredictedtaken0
                                  emmispredictednottaken0 emregwrite0
                                  emmemwrite0 emmemtoreg0 dmem0 mmppc0
                                  mmval0 mmdest0 mmwrt0 mmregwrite0
                                  mwppc0 mwval0 mwdest0 mwwrt0
                                  mwregwrite0 (g 'ppc (g 'impl st41))
                                  (g 'prf (g 'impl st41))
                                  (g 'pdmem (g 'impl st41))))
                        (t3 (g 'mwwrt (g 'impl st42)))
                        (st43 (simulate_a st42 nil nil nil nil pc0
                                  bpstate0 ffpredicteddirection0
                                  ffpredictedtarget0 ffwrt0 ffinst0
                                  ffppc0 fdppc0 fdwrt0 fdinst0
                                  fdpredicteddirection0
                                  fdpredictedtarget0 deppc0 desrc10
                                  desrc20 a1 a2 dedest0 deop0 deimm0
                                  deuseimm0 deregwrite0 dememwrite0
                                  dememtoreg0 deisbranch0 dewrt0
                                  depredicteddirection0
                                  depredictedtarget0 emppc0
                                  emis_taken_branch0 emtargetpc0
                                  emarg20 emresult0 emdest0 emwrt0
                                  emmispredictedtaken0
                                  emmispredictednottaken0 emregwrite0
                                  emmemwrite0 emmemtoreg0 dmem0 mmppc0
                                  mmval0 mmdest0 mmwrt0 mmregwrite0
                                  mwppc0 mwval0 mwdest0 mwwrt0
                                  mwregwrite0 (g 'ppc (g 'impl st42))
                                  (g 'prf (g 'impl st42))
                                  (g 'pdmem (g 'impl st42))))
                        (t4 (g 'mwwrt (g 'impl st43)))
                        (st44 (simulate_a st43 nil nil nil nil pc0
                                  bpstate0 ffpredicteddirection0
                                  ffpredictedtarget0 ffwrt0 ffinst0
                                  ffppc0 fdppc0 fdwrt0 fdinst0
                                  fdpredicteddirection0
                                  fdpredictedtarget0 deppc0 desrc10
                                  desrc20 a1 a2 dedest0 deop0 deimm0
                                  deuseimm0 deregwrite0 dememwrite0
                                  dememtoreg0 deisbranch0 dewrt0
                                  depredicteddirection0
                                  depredictedtarget0 emppc0
                                  emis_taken_branch0 emtargetpc0
                                  emarg20 emresult0 emdest0 emwrt0
                                  emmispredictedtaken0
                                  emmispredictednottaken0 emregwrite0
                                  emmemwrite0 emmemtoreg0 dmem0 mmppc0
                                  mmval0 mmdest0 mmwrt0 mmregwrite0
                                  mwppc0 mwval0 mwdest0 mwwrt0
                                  mwregwrite0 (g 'ppc (g 'impl st43))
                                  (g 'prf (g 'impl st43))
                                  (g 'pdmem (g 'impl st43))))
                        (t5 (g 'mwwrt (g 'impl st44)))
                        (st45 (simulate_a st44 nil nil nil nil pc0
                                  bpstate0 ffpredicteddirection0
                                  ffpredictedtarget0 ffwrt0 ffinst0
                                  ffppc0 fdppc0 fdwrt0 fdinst0
                                  fdpredicteddirection0
                                  fdpredictedtarget0 deppc0 desrc10
                                  desrc20 a1 a2 dedest0 deop0 deimm0
                                  deuseimm0 deregwrite0 dememwrite0
                                  dememtoreg0 deisbranch0 dewrt0
                                  depredicteddirection0
                                  depredictedtarget0 emppc0
                                  emis_taken_branch0 emtargetpc0
                                  emarg20 emresult0 emdest0 emwrt0
                                  emmispredictedtaken0
                                  emmispredictednottaken0 emregwrite0
                                  emmemwrite0 emmemtoreg0 dmem0 mmppc0
                                  mmval0 mmdest0 mmwrt0 mmregwrite0
                                  mwppc0 mwval0 mwdest0 mwwrt0
                                  mwregwrite0 (g 'ppc (g 'impl st44))
                                  (g 'prf (g 'impl st44))
                                  (g 'pdmem (g 'impl st44))))
                        (t6 (g 'mwwrt (g 'impl st45)))
                        (rank_v (cond
                                  ((and (equal counter zero) t1)
                                   (add-1 counter))
                                  ((and
                                    (or (equal counter zero)
                                     (equal counter (add-1 zero)))
                                    t2)
                                   (add-1 (add-1 counter)))
                                  (t3 (add-1 (add-1 (add-1 counter))))
                                  (t4 (add-1
                                       (add-1 (add-1 (add-1 counter)))))
                                  (t5 (add-1
                                       (add-1
                                        (add-1 (add-1 (add-1 counter))))))
                                  (t6 (add-1
                                       (add-1
                                        (add-1
                                         (add-1
                                          (add-1 (add-1 counter)))))))
                                  (t (add-1
                                      (add-1
                                       (add-1
                                        (add-1
                                         (add-1
                                          (add-1 (add-1 counter)))))))))))
                   (or (and (and (equal s_pc1 i_pc)
                                 (equal (read-srf_a a1 s_rf1)
                                        (read-prf_a a1 i_rf)))
                            (equal s_dmem1 i_dmem))
                       (and (and (equal s_pc0 i_pc)
                                 (equal (read-srf_a a1 s_rf0)
                                        (read-prf_a a1 i_rf)))
                            (equal s_dmem0 i_dmem)))))
        :rule-classes nil)
