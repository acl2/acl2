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
             ((g 2 (car prf)) (read-prf_a a (cdr prf)))
             ((and (and (g 3 (car prf)) (equal a (g 4 (car prf))))
                   (g 5 (car prf)))
              (g 6 (car prf)))
             (t (read-prf_a a (cdr prf)))))))

(defun read-simem_a (a simem)
   (declare (xargs :measure (acl2-count simem)))
   (if (endp simem) (imem0 a)
       (if (g 0 (car simem)) (imem0 a) (read-simem_a a (cdr simem)))))

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
        (pimem ppc bpstate ffbpstate ffpredicteddirection
               ffpredictedtarget ffwrt ffinst ffppc prf fdbpstate fdppc
               fdwrt fdinst fdpredicteddirection fdpredictedtarget
               debpstate deppc desrc1 desrc2 dearg1 dearg2 dedest deop
               deimm deuseimm deregwrite dememwrite dememtoreg
               deisbranch dewrt depredicteddirection depredictedtarget
               embpstate emppc emis_taken_branch emtargetpc emarg2
               emresult emdest emwrt emmispredictedtaken
               emmispredictednottaken emregwrite emmemwrite emmemtoreg
               pdmemhist_2 pdmemhist_1 pdmem mmbpstate mmppc mmval
               mmdest mmwrt mmregwrite mwbpstate mwppc mwval mwdest
               mwwrt mwregwrite)
   (seq nil 'pimem pimem 'ppc ppc 'bpstate bpstate 'ffbpstate ffbpstate
        'ffpredicteddirection ffpredicteddirection 'ffpredictedtarget
        ffpredictedtarget 'ffwrt ffwrt 'ffinst ffinst 'ffppc ffppc 'prf
        prf 'fdbpstate fdbpstate 'fdppc fdppc 'fdwrt fdwrt 'fdinst
        fdinst 'fdpredicteddirection fdpredicteddirection
        'fdpredictedtarget fdpredictedtarget 'debpstate debpstate
        'deppc deppc 'desrc1 desrc1 'desrc2 desrc2 'dearg1 dearg1
        'dearg2 dearg2 'dedest dedest 'deop deop 'deimm deimm 'deuseimm
        deuseimm 'deregwrite deregwrite 'dememwrite dememwrite
        'dememtoreg dememtoreg 'deisbranch deisbranch 'dewrt dewrt
        'depredicteddirection depredicteddirection 'depredictedtarget
        depredictedtarget 'embpstate embpstate 'emppc emppc
        'emis_taken_branch emis_taken_branch 'emtargetpc emtargetpc
        'emarg2 emarg2 'emresult emresult 'emdest emdest 'emwrt emwrt
        'emmispredictedtaken emmispredictedtaken
        'emmispredictednottaken emmispredictednottaken 'emregwrite
        emregwrite 'emmemwrite emmemwrite 'emmemtoreg emmemtoreg
        'pdmemhist_2 pdmemhist_2 'pdmemhist_1 pdmemhist_1 'pdmem pdmem
        'mmbpstate mmbpstate 'mmppc mmppc 'mmval mmval 'mmdest mmdest
        'mmwrt mmwrt 'mmregwrite mmregwrite 'mwbpstate mwbpstate 'mwppc
        mwppc 'mwval mwval 'mwdest mwdest 'mwwrt mwwrt 'mwregwrite
        mwregwrite))

(defun initpimem_a (pimem) (cons (s 0 t (s 1 nil nil)) pimem))

(defun nextpimem_a (pimem) (cons (s 0 nil (s 1 nil nil)) pimem))

(defun initppc_a (pc0) pc0)

(defun nextppc_a
        (initi pc0 commit_impl commit_pc mem1_mispredicted_taken emppc
               mem1_mispredicted_nottaken emtargetpc stall ppc
               if_predict_branch_taken predicted_target)
   (cond
     (initi pc0)
     (commit_impl commit_pc)
     (mem1_mispredicted_taken (add-1 emppc))
     (mem1_mispredicted_nottaken emtargetpc)
     (stall ppc)
     (if_predict_branch_taken predicted_target)
     (t (add-1 ppc))))

(defun initbpstate_a (bpstate0) bpstate0)

(defun nextbpstate_a
        (initi bpstate0 commit_impl commit_bpstate stall bpstate)
   (cond
     (initi bpstate0)
     (commit_impl commit_bpstate)
     (stall bpstate)
     (t (nextbpstate bpstate))))

(defun initffbpstate_a (ffbpstate0) ffbpstate0)

(defun nextffbpstate_a (initi ffbpstate0 stall ffbpstate bpstate)
   (cond (initi ffbpstate0) (stall ffbpstate) (t bpstate)))

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

(defun initffwrt_a () nil)

(defun nextffwrt_a (initi commit_impl squash stall ffwrt)
   (cond
     (initi nil)
     (commit_impl nil)
     (squash nil)
     (stall ffwrt)
     (t t)))

(defun initffinst_a (ffinst0) ffinst0)

(defun nextffinst_a (initi ffinst0 stall ffinst if_inst)
   (cond (initi ffinst0) (stall ffinst) (t if_inst)))

(defun initffppc_a (ffppc0) ffppc0)

(defun nextffppc_a (initi ffppc0 stall ffppc ppc)
   (cond (initi ffppc0) (stall ffppc) (t ppc)))

(defun initprf_a (prf) (cons (s 0 t (s 1 nil nil)) prf))

(defun nextprf_a (prf initi commit_impl mwwrt mwdest mwregwrite mwval)
   (cons (s 0 nil
            (s 1 initi
               (s 2 commit_impl
                  (s 3 mwwrt
                     (s 4 mwdest (s 5 mwregwrite (s 6 mwval nil)))))))
         prf))

(defun initfdbpstate_a (fdbpstate0) fdbpstate0)

(defun nextfdbpstate_a (initi fdbpstate0 stall fdbpstate ffbpstate)
   (cond (initi fdbpstate0) (stall fdbpstate) (t ffbpstate)))

(defun initfdppc_a (fdppc0) fdppc0)

(defun nextfdppc_a (initi fdppc0 stall fdppc ffppc)
   (cond (initi fdppc0) (stall fdppc) (t ffppc)))

(defun initfdwrt_a () nil)

(defun nextfdwrt_a (initi commit_impl squash stall fdwrt ffwrt)
   (cond
     (initi nil)
     (commit_impl nil)
     (squash nil)
     (stall fdwrt)
     (t ffwrt)))

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

(defun initdebpstate_a (debpstate0) debpstate0)

(defun nextdebpstate_a (initi debpstate0 fdbpstate)
   (cond (initi debpstate0) (t fdbpstate)))

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
        (initi a1 if_id_src1 prf commit_impl mwwrt mwdest mwregwrite
               mwval)
   (cond
     (initi a1)
     (t (read-prf_a if_id_src1
            (nextprf_a prf initi commit_impl mwwrt mwdest mwregwrite
                mwval)))))

(defun initdearg2_a (a2) a2)

(defun nextdearg2_a
        (initi a2 if_id_src2 prf commit_impl mwwrt mwdest mwregwrite
               mwval)
   (cond
     (initi a2)
     (t (read-prf_a if_id_src2
            (nextprf_a prf initi commit_impl mwwrt mwdest mwregwrite
                mwval)))))

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

(defun initdewrt_a () nil)

(defun nextdewrt_a (initi commit_impl squash stall fdwrt)
   (cond
     (initi nil)
     (commit_impl nil)
     (squash nil)
     (t (and (not stall) fdwrt))))

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

(defun initembpstate_a (embpstate0) embpstate0)

(defun nextembpstate_a (initi embpstate0 debpstate)
   (cond (initi embpstate0) (t debpstate)))

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

(defun initemwrt_a () nil)

(defun nextemwrt_a (initi commit_impl squash dewrt)
   (cond (initi nil) (commit_impl nil) (squash nil) (t dewrt)))

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
        (initi dmem0 commit_impl pdmemhist_2 emwrt emmemwrite pdmem
               emresult emarg2)
   (cond
     (initi dmem0)
     (commit_impl pdmemhist_2)
     ((and emwrt emmemwrite) (nextdmem pdmem emresult emarg2))
     (t pdmem)))

(defun initmmbpstate_a (mmbpstate0) mmbpstate0)

(defun nextmmbpstate_a (initi mmbpstate0 embpstate)
   (cond (initi mmbpstate0) (t embpstate)))

(defun initmmppc_a (mmppc0) mmppc0)

(defun nextmmppc_a (initi mmppc0 emppc)
   (cond (initi mmppc0) (t emppc)))

(defun initmmval_a (mmval0) mmval0)

(defun nextmmval_a (initi mmval0 emmemtoreg mem1_readdata emresult)
   (cond (initi mmval0) (emmemtoreg mem1_readdata) (t emresult)))

(defun initmmdest_a (mmdest0) mmdest0)

(defun nextmmdest_a (initi mmdest0 emdest)
   (cond (initi mmdest0) (t emdest)))

(defun initmmwrt_a () nil)

(defun nextmmwrt_a (initi commit_impl emwrt)
   (cond (initi nil) (commit_impl nil) (t emwrt)))

(defun initmmregwrite_a (mmregwrite0) mmregwrite0)

(defun nextmmregwrite_a (initi mmregwrite0 emregwrite)
   (cond (initi mmregwrite0) (t emregwrite)))

(defun initmwbpstate_a (mwbpstate0) mwbpstate0)

(defun nextmwbpstate_a (initi mwbpstate0 mmbpstate)
   (cond (initi mwbpstate0) (t mmbpstate)))

(defun initmwppc_a (mwppc0) mwppc0)

(defun nextmwppc_a (initi mwppc0 mmppc)
   (cond (initi mwppc0) (t mmppc)))

(defun initmwval_a (mwval0) mwval0)

(defun nextmwval_a (initi mwval0 mmval)
   (cond (initi mwval0) (t mmval)))

(defun initmwdest_a (mwdest0) mwdest0)

(defun nextmwdest_a (initi mwdest0 mmdest)
   (cond (initi mwdest0) (t mmdest)))

(defun initmwwrt_a () nil)

(defun nextmwwrt_a (initi commit_impl mmwrt)
   (cond (initi nil) (commit_impl nil) (t mmwrt)))

(defun initmwregwrite_a (mwregwrite0) mwregwrite0)

(defun nextmwregwrite_a (initi mwregwrite0 mmregwrite)
   (cond (initi mwregwrite0) (t mmregwrite)))

(defun impl-simulate_a
        (impl initi pc0 commit_impl commit_pc bpstate0 commit_bpstate
              ffbpstate0 ffpredicteddirection0 ffpredictedtarget0
              ffinst0 ffppc0 fdbpstate0 fdppc0 fdinst0
              fdpredicteddirection0 fdpredictedtarget0 debpstate0
              deppc0 desrc10 desrc20 a1 a2 dedest0 deop0 deimm0
              deuseimm0 deregwrite0 dememwrite0 dememtoreg0 deisbranch0
              depredicteddirection0 depredictedtarget0 embpstate0
              emppc0 emis_taken_branch0 emtargetpc0 emarg20 emresult0
              emdest0 emmispredictedtaken0 emmispredictednottaken0
              emregwrite0 emmemwrite0 emmemtoreg0 dmem0 mmbpstate0
              mmppc0 mmval0 mmdest0 mmregwrite0 mwbpstate0 mwppc0
              mwval0 mwdest0 mwregwrite0)
   (let* ((pimem (g 'pimem impl)) (ppc (g 'ppc impl))
          (bpstate (g 'bpstate impl)) (ffbpstate (g 'ffbpstate impl))
          (ffpredicteddirection (g 'ffpredicteddirection impl))
          (ffpredictedtarget (g 'ffpredictedtarget impl))
          (ffwrt (g 'ffwrt impl)) (ffinst (g 'ffinst impl))
          (ffppc (g 'ffppc impl)) (prf (g 'prf impl))
          (fdbpstate (g 'fdbpstate impl)) (fdppc (g 'fdppc impl))
          (fdwrt (g 'fdwrt impl)) (fdinst (g 'fdinst impl))
          (fdpredicteddirection (g 'fdpredicteddirection impl))
          (fdpredictedtarget (g 'fdpredictedtarget impl))
          (debpstate (g 'debpstate impl)) (deppc (g 'deppc impl))
          (desrc1 (g 'desrc1 impl)) (desrc2 (g 'desrc2 impl))
          (dearg1 (g 'dearg1 impl)) (dearg2 (g 'dearg2 impl))
          (dedest (g 'dedest impl)) (deop (g 'deop impl))
          (deimm (g 'deimm impl)) (deuseimm (g 'deuseimm impl))
          (deregwrite (g 'deregwrite impl))
          (dememwrite (g 'dememwrite impl))
          (dememtoreg (g 'dememtoreg impl))
          (deisbranch (g 'deisbranch impl)) (dewrt (g 'dewrt impl))
          (depredicteddirection (g 'depredicteddirection impl))
          (depredictedtarget (g 'depredictedtarget impl))
          (embpstate (g 'embpstate impl)) (emppc (g 'emppc impl))
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
          (mmbpstate (g 'mmbpstate impl)) (mmppc (g 'mmppc impl))
          (mmval (g 'mmval impl)) (mmdest (g 'mmdest impl))
          (mmwrt (g 'mmwrt impl)) (mmregwrite (g 'mmregwrite impl))
          (mwbpstate (g 'mwbpstate impl)) (mwppc (g 'mwppc impl))
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
           (nextppc_a initi pc0 commit_impl commit_pc
               mem1_mispredicted_taken emppc mem1_mispredicted_nottaken
               emtargetpc stall ppc if_predict_branch_taken
               predicted_target)
           (nextbpstate_a initi bpstate0 commit_impl commit_bpstate
               stall bpstate)
           (nextffbpstate_a initi ffbpstate0 stall ffbpstate bpstate)
           (nextffpredicteddirection_a initi ffpredicteddirection0
               stall ffpredicteddirection if_predict_branch_taken)
           (nextffpredictedtarget_a initi ffpredictedtarget0 stall
               ffpredictedtarget predicted_target)
           (nextffwrt_a initi commit_impl squash stall ffwrt)
           (nextffinst_a initi ffinst0 stall ffinst if_inst)
           (nextffppc_a initi ffppc0 stall ffppc ppc)
           (nextprf_a prf initi commit_impl mwwrt mwdest mwregwrite
               mwval)
           (nextfdbpstate_a initi fdbpstate0 stall fdbpstate ffbpstate)
           (nextfdppc_a initi fdppc0 stall fdppc ffppc)
           (nextfdwrt_a initi commit_impl squash stall fdwrt ffwrt)
           (nextfdinst_a initi fdinst0 stall fdinst ffinst)
           (nextfdpredicteddirection_a initi fdpredicteddirection0
               stall fdpredicteddirection ffpredicteddirection)
           (nextfdpredictedtarget_a initi fdpredictedtarget0 stall
               fdpredictedtarget ffpredictedtarget)
           (nextdebpstate_a initi debpstate0 fdbpstate)
           (nextdeppc_a initi deppc0 fdppc)
           (nextdesrc1_a initi desrc10 if_id_src1)
           (nextdesrc2_a initi desrc20 if_id_src2)
           (nextdearg1_a initi a1 if_id_src1 prf commit_impl mwwrt
               mwdest mwregwrite mwval)
           (nextdearg2_a initi a2 if_id_src2 prf commit_impl mwwrt
               mwdest mwregwrite mwval)
           (nextdedest_a initi dedest0 fdinst)
           (nextdeop_a initi deop0 fdinst)
           (nextdeimm_a initi deimm0 fdinst)
           (nextdeuseimm_a initi deuseimm0 fdinst)
           (nextderegwrite_a initi deregwrite0 id_regwrite)
           (nextdememwrite_a initi dememwrite0 id_memwrite)
           (nextdememtoreg_a initi dememtoreg0 fdinst)
           (nextdeisbranch_a initi deisbranch0 fdinst)
           (nextdewrt_a initi commit_impl squash stall fdwrt)
           (nextdepredicteddirection_a initi depredicteddirection0
               stall depredicteddirection fdpredicteddirection)
           (nextdepredictedtarget_a initi depredictedtarget0 stall
               depredictedtarget fdpredictedtarget)
           (nextembpstate_a initi embpstate0 debpstate)
           (nextemppc_a initi emppc0 deppc)
           (nextemis_taken_branch_a initi emis_taken_branch0
               ex_is_taken_branch)
           (nextemtargetpc_a initi emtargetpc0 ex_targetpc)
           (nextemarg2_a initi emarg20 ex_fwd_src2)
           (nextemresult_a initi emresult0 ex_result)
           (nextemdest_a initi emdest0 dedest)
           (nextemwrt_a initi commit_impl squash dewrt)
           (nextemmispredictedtaken_a initi emmispredictedtaken0
               mispredicted_taken)
           (nextemmispredictednottaken_a initi emmispredictednottaken0
               mispredicted_nottaken)
           (nextemregwrite_a initi emregwrite0 deregwrite)
           (nextemmemwrite_a initi emmemwrite0 dememwrite)
           (nextemmemtoreg_a initi emmemtoreg0 dememtoreg)
           (nextpdmemhist_2_a initi dmem0 pdmemhist_1)
           (nextpdmemhist_1_a initi dmem0 pdmem)
           (nextpdmem_a initi dmem0 commit_impl pdmemhist_2 emwrt
               emmemwrite pdmem emresult emarg2)
           (nextmmbpstate_a initi mmbpstate0 embpstate)
           (nextmmppc_a initi mmppc0 emppc)
           (nextmmval_a initi mmval0 emmemtoreg mem1_readdata emresult)
           (nextmmdest_a initi mmdest0 emdest)
           (nextmmwrt_a initi commit_impl emwrt)
           (nextmmregwrite_a initi mmregwrite0 emregwrite)
           (nextmwbpstate_a initi mwbpstate0 mmbpstate)
           (nextmwppc_a initi mwppc0 mmppc)
           (nextmwval_a initi mwval0 mmval)
           (nextmwdest_a initi mwdest0 mmdest)
           (nextmwwrt_a initi commit_impl mmwrt)
           (nextmwregwrite_a initi mwregwrite0 mmregwrite)))))

(defun impl-initialize_a
        (impl pc0 bpstate0 ffbpstate0 ffpredicteddirection0
              ffpredictedtarget0 ffinst0 ffppc0 fdbpstate0 fdppc0
              fdinst0 fdpredicteddirection0 fdpredictedtarget0
              debpstate0 deppc0 desrc10 desrc20 a1 a2 dedest0 deop0
              deimm0 deuseimm0 deregwrite0 dememwrite0 dememtoreg0
              deisbranch0 depredicteddirection0 depredictedtarget0
              embpstate0 emppc0 emis_taken_branch0 emtargetpc0 emarg20
              emresult0 emdest0 emmispredictedtaken0
              emmispredictednottaken0 emregwrite0 emmemwrite0
              emmemtoreg0 dmem0 mmbpstate0 mmppc0 mmval0 mmdest0
              mmregwrite0 mwbpstate0 mwppc0 mwval0 mwdest0 mwregwrite0)
   (let* ((pimem (g 'pimem impl)) (ppc (g 'ppc impl))
          (bpstate (g 'bpstate impl)) (ffbpstate (g 'ffbpstate impl))
          (ffpredicteddirection (g 'ffpredicteddirection impl))
          (ffpredictedtarget (g 'ffpredictedtarget impl))
          (ffwrt (g 'ffwrt impl)) (ffinst (g 'ffinst impl))
          (ffppc (g 'ffppc impl)) (prf (g 'prf impl))
          (fdbpstate (g 'fdbpstate impl)) (fdppc (g 'fdppc impl))
          (fdwrt (g 'fdwrt impl)) (fdinst (g 'fdinst impl))
          (fdpredicteddirection (g 'fdpredicteddirection impl))
          (fdpredictedtarget (g 'fdpredictedtarget impl))
          (debpstate (g 'debpstate impl)) (deppc (g 'deppc impl))
          (desrc1 (g 'desrc1 impl)) (desrc2 (g 'desrc2 impl))
          (dearg1 (g 'dearg1 impl)) (dearg2 (g 'dearg2 impl))
          (dedest (g 'dedest impl)) (deop (g 'deop impl))
          (deimm (g 'deimm impl)) (deuseimm (g 'deuseimm impl))
          (deregwrite (g 'deregwrite impl))
          (dememwrite (g 'dememwrite impl))
          (dememtoreg (g 'dememtoreg impl))
          (deisbranch (g 'deisbranch impl)) (dewrt (g 'dewrt impl))
          (depredicteddirection (g 'depredicteddirection impl))
          (depredictedtarget (g 'depredictedtarget impl))
          (embpstate (g 'embpstate impl)) (emppc (g 'emppc impl))
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
          (mmbpstate (g 'mmbpstate impl)) (mmppc (g 'mmppc impl))
          (mmval (g 'mmval impl)) (mmdest (g 'mmdest impl))
          (mmwrt (g 'mmwrt impl)) (mmregwrite (g 'mmregwrite impl))
          (mwbpstate (g 'mwbpstate impl)) (mwppc (g 'mwppc impl))
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
           (initbpstate_a bpstate0) (initffbpstate_a ffbpstate0)
           (initffpredicteddirection_a ffpredicteddirection0)
           (initffpredictedtarget_a ffpredictedtarget0) (initffwrt_a)
           (initffinst_a ffinst0) (initffppc_a ffppc0) (initprf_a prf)
           (initfdbpstate_a fdbpstate0) (initfdppc_a fdppc0)
           (initfdwrt_a) (initfdinst_a fdinst0)
           (initfdpredicteddirection_a fdpredicteddirection0)
           (initfdpredictedtarget_a fdpredictedtarget0)
           (initdebpstate_a debpstate0) (initdeppc_a deppc0)
           (initdesrc1_a desrc10) (initdesrc2_a desrc20)
           (initdearg1_a a1) (initdearg2_a a2) (initdedest_a dedest0)
           (initdeop_a deop0) (initdeimm_a deimm0)
           (initdeuseimm_a deuseimm0) (initderegwrite_a deregwrite0)
           (initdememwrite_a dememwrite0)
           (initdememtoreg_a dememtoreg0)
           (initdeisbranch_a deisbranch0) (initdewrt_a)
           (initdepredicteddirection_a depredicteddirection0)
           (initdepredictedtarget_a depredictedtarget0)
           (initembpstate_a embpstate0) (initemppc_a emppc0)
           (initemis_taken_branch_a emis_taken_branch0)
           (initemtargetpc_a emtargetpc0) (initemarg2_a emarg20)
           (initemresult_a emresult0) (initemdest_a emdest0)
           (initemwrt_a)
           (initemmispredictedtaken_a emmispredictedtaken0)
           (initemmispredictednottaken_a emmispredictednottaken0)
           (initemregwrite_a emregwrite0)
           (initemmemwrite_a emmemwrite0)
           (initemmemtoreg_a emmemtoreg0) (initpdmemhist_2_a dmem0)
           (initpdmemhist_1_a dmem0) (initpdmem_a dmem0)
           (initmmbpstate_a mmbpstate0) (initmmppc_a mmppc0)
           (initmmval_a mmval0) (initmmdest_a mmdest0) (initmmwrt_a)
           (initmmregwrite_a mmregwrite0) (initmwbpstate_a mwbpstate0)
           (initmwppc_a mwppc0) (initmwval_a mwval0)
           (initmwdest_a mwdest0) (initmwwrt_a)
           (initmwregwrite_a mwregwrite0)))))

(defun spec-state_a (simem spc srf sdmem)
   (seq nil 'simem simem 'spc spc 'srf srf 'sdmem sdmem))

(defun initsimem_a (simem) (cons (s 0 t (s 1 nil nil)) simem))

(defun nextsimem_a (simem) (cons (s 0 nil (s 1 nil nil)) simem))

(defun initspc_a (pc0) pc0)

(defun nextspc_a
        (initi pc0 project_impl project_pc isa is_taken_branch targetpc
               spc)
   (cond
     (initi pc0)
     (project_impl project_pc)
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
        (initi dmem0 project_impl impl.pdmemhist_2 isa memwrite sdmem
               result arg2_temp)
   (cond
     (initi dmem0)
     (project_impl impl.pdmemhist_2)
     ((and isa memwrite) (nextdmem sdmem result arg2_temp))
     (t sdmem)))

(defun spec-simulate_a
        (spec initi pc0 project_impl project_pc isa impl.prf dmem0
              impl.pdmemhist_2)
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
       (spec-state_a (nextsimem_a simem)
           (nextspc_a initi pc0 project_impl project_pc isa
               is_taken_branch targetpc spc)
           (nextsrf_a srf initi project_impl impl.prf isa inst regwrite
               val)
           (nextsdmem_a initi dmem0 project_impl impl.pdmemhist_2 isa
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
        (st initi isa project_impl project_pc commit_impl commit_pc
            commit_bpstate pc0 bpstate0 ffbpstate0
            ffpredicteddirection0 ffpredictedtarget0 ffinst0 ffppc0
            fdbpstate0 fdppc0 fdinst0 fdpredicteddirection0
            fdpredictedtarget0 debpstate0 deppc0 desrc10 desrc20 a1 a2
            dedest0 deop0 deimm0 deuseimm0 deregwrite0 dememwrite0
            dememtoreg0 deisbranch0 depredicteddirection0
            depredictedtarget0 embpstate0 emppc0 emis_taken_branch0
            emtargetpc0 emarg20 emresult0 emdest0 emmispredictedtaken0
            emmispredictednottaken0 emregwrite0 emmemwrite0 emmemtoreg0
            dmem0 mmbpstate0 mmppc0 mmval0 mmdest0 mmregwrite0
            mwbpstate0 mwppc0 mwval0 mwdest0 mwregwrite0 impl.prf
            impl.pdmemhist_2)
   (u-state_a
       (impl-simulate_a (g 'impl st) initi pc0 commit_impl commit_pc
           bpstate0 commit_bpstate ffbpstate0 ffpredicteddirection0
           ffpredictedtarget0 ffinst0 ffppc0 fdbpstate0 fdppc0 fdinst0
           fdpredicteddirection0 fdpredictedtarget0 debpstate0 deppc0
           desrc10 desrc20 a1 a2 dedest0 deop0 deimm0 deuseimm0
           deregwrite0 dememwrite0 dememtoreg0 deisbranch0
           depredicteddirection0 depredictedtarget0 embpstate0 emppc0
           emis_taken_branch0 emtargetpc0 emarg20 emresult0 emdest0
           emmispredictedtaken0 emmispredictednottaken0 emregwrite0
           emmemwrite0 emmemtoreg0 dmem0 mmbpstate0 mmppc0 mmval0
           mmdest0 mmregwrite0 mwbpstate0 mwppc0 mwval0 mwdest0
           mwregwrite0)
       (spec-simulate_a (g 'spec st) initi pc0 project_impl project_pc
           isa impl.prf dmem0 impl.pdmemhist_2)))

(defun initialize_a
        (st initi isa project_impl project_pc commit_impl commit_pc
            commit_bpstate pc0 bpstate0 ffbpstate0
            ffpredicteddirection0 ffpredictedtarget0 ffinst0 ffppc0
            fdbpstate0 fdppc0 fdinst0 fdpredicteddirection0
            fdpredictedtarget0 debpstate0 deppc0 desrc10 desrc20 a1 a2
            dedest0 deop0 deimm0 deuseimm0 deregwrite0 dememwrite0
            dememtoreg0 deisbranch0 depredicteddirection0
            depredictedtarget0 embpstate0 emppc0 emis_taken_branch0
            emtargetpc0 emarg20 emresult0 emdest0 emmispredictedtaken0
            emmispredictednottaken0 emregwrite0 emmemwrite0 emmemtoreg0
            dmem0 mmbpstate0 mmppc0 mmval0 mmdest0 mmregwrite0
            mwbpstate0 mwppc0 mwval0 mwdest0 mwregwrite0)
   (u-state_a
       (impl-initialize_a (g 'impl st) pc0 bpstate0 ffbpstate0
           ffpredicteddirection0 ffpredictedtarget0 ffinst0 ffppc0
           fdbpstate0 fdppc0 fdinst0 fdpredicteddirection0
           fdpredictedtarget0 debpstate0 deppc0 desrc10 desrc20 a1 a2
           dedest0 deop0 deimm0 deuseimm0 deregwrite0 dememwrite0
           dememtoreg0 deisbranch0 depredicteddirection0
           depredictedtarget0 embpstate0 emppc0 emis_taken_branch0
           emtargetpc0 emarg20 emresult0 emdest0 emmispredictedtaken0
           emmispredictednottaken0 emregwrite0 emmemwrite0 emmemtoreg0
           dmem0 mmbpstate0 mmppc0 mmval0 mmdest0 mmregwrite0
           mwbpstate0 mwppc0 mwval0 mwdest0 mwregwrite0)
       (spec-initialize_a (g 'spec st) pc0 dmem0)))

(defun equiv_ma
        (ppc_v impl.ppc prf_v a1 impl.prf pimem_v impl.pimem pdmem_v
               impl.pdmem ffwrt_v impl.ffwrt ffppc_v impl.ffppc
               ffinst_v impl.ffinst fdwrt_v impl.fdwrt fdppc_v
               impl.fdppc fdinst_v impl.fdinst dewrt_v impl.dewrt
               deppc_v impl.deppc deop_v impl.deop dearg1_v impl.dearg1
               dearg2_v impl.dearg2 dedest_v impl.dedest desrc1_v
               impl.desrc1 desrc2_v impl.desrc2 deimm_v impl.deimm
               deuseimm_v impl.deuseimm deisbranch_v impl.deisbranch
               dememtoreg_v impl.dememtoreg dememwrite_v
               impl.dememwrite deregwrite_v impl.deregwrite emwrt_v
               impl.emwrt emtargetpc_v impl.emtargetpc emdest_v
               impl.emdest emarg2_v impl.emarg2 emregwrite_v
               impl.emregwrite emresult_v impl.emresult
               emis_taken_branch_v impl.emis_taken_branch emmemtoreg_v
               impl.emmemtoreg emmemwrite_v impl.emmemwrite mmwrt_v
               impl.mmwrt mmval_v impl.mmval mmdest_v impl.mmdest
               mmregwrite_v impl.mmregwrite mwwrt_v impl.mwwrt mwval_v
               impl.mwval mwdest_v impl.mwdest mwregwrite_v
               impl.mwregwrite)
   (declare (xargs :normalize nil))
   (and (and (and (and (and (and (and (and
                                       (and
                                        (and
                                         (and
                                          (and
                                           (and
                                            (and
                                             (and
                                              (equal ppc_v impl.ppc)
                                              (equal
                                               (read-prf_a a1 prf_v)
                                               (read-prf_a a1 impl.prf)))
                                             (equal
                                              (read-pimem_a a1 pimem_v)
                                              (read-pimem_a a1
                                               impl.pimem)))
                                            (equal pdmem_v impl.pdmem))
                                           (equalb ffwrt_v impl.ffwrt))
                                          (implies ffwrt_v
                                           (and
                                            (and impl.ffwrt
                                             (equal ffppc_v impl.ffppc))
                                            (equal ffinst_v
                                             impl.ffinst))))
                                         (equalb fdwrt_v impl.fdwrt))
                                        (implies fdwrt_v
                                         (and
                                          (and impl.fdwrt
                                           (equal fdppc_v impl.fdppc))
                                          (equal fdinst_v impl.fdinst))))
                                       (equalb dewrt_v impl.dewrt))
                                      (implies dewrt_v
                                       (and
                                        (and
                                         (and
                                          (and
                                           (and
                                            (and
                                             (and
                                              (and
                                               (and
                                                (and
                                                 (and
                                                  (and
                                                   (and impl.dewrt
                                                    (equal deppc_v
                                                     impl.deppc))
                                                   (equal deop_v
                                                    impl.deop))
                                                  (equal dearg1_v
                                                   impl.dearg1))
                                                 (equal dearg2_v
                                                  impl.dearg2))
                                                (equal dedest_v
                                                 impl.dedest))
                                               (equal desrc1_v
                                                impl.desrc1))
                                              (equal desrc2_v
                                               impl.desrc2))
                                             (equal deimm_v impl.deimm))
                                            (equalb deuseimm_v
                                             impl.deuseimm))
                                           (equalb deisbranch_v
                                            impl.deisbranch))
                                          (equalb dememtoreg_v
                                           impl.dememtoreg))
                                         (equalb dememwrite_v
                                          impl.dememwrite))
                                        (equalb deregwrite_v
                                         impl.deregwrite))))
                                 (equalb emwrt_v impl.emwrt))
                            (implies emwrt_v
                                     (and
                                      (and
                                       (and
                                        (and
                                         (and
                                          (and
                                           (and
                                            (and impl.emwrt
                                             (equal emtargetpc_v
                                              impl.emtargetpc))
                                            (equal emdest_v
                                             impl.emdest))
                                           (equal emarg2_v impl.emarg2))
                                          (equalb emregwrite_v
                                           impl.emregwrite))
                                         (equal emresult_v
                                          impl.emresult))
                                        (equalb emis_taken_branch_v
                                         impl.emis_taken_branch))
                                       (equalb emmemtoreg_v
                                        impl.emmemtoreg))
                                      (equalb emmemwrite_v
                                       impl.emmemwrite))))
                       (equalb mmwrt_v impl.mmwrt))
                  (implies mmwrt_v
                           (and (and (and impl.mmwrt
                                      (equal mmval_v impl.mmval))
                                     (equal mmdest_v impl.mmdest))
                                (equalb mmregwrite_v impl.mmregwrite))))
             (equalb mwwrt_v impl.mwwrt))
        (implies mwwrt_v
                 (and (and (and impl.mwwrt (equal mwval_v impl.mwval))
                           (equal mwdest_v impl.mwdest))
                      (equalb mwregwrite_v impl.mwregwrite)))))

(defun rank
        (impl.mwwrt zero impl.mmwrt impl.emwrt impl.dewrt impl.fdwrt
            impl.ffwrt)
   (cond
     (impl.mwwrt zero)
     (impl.mmwrt (add-1 zero))
     (impl.emwrt (add-1 (add-1 zero)))
     (impl.dewrt (add-1 (add-1 (add-1 zero))))
     (impl.fdwrt (add-1 (add-1 (add-1 (add-1 zero)))))
     (impl.ffwrt (add-1 (add-1 (add-1 (add-1 (add-1 zero))))))
     (t (add-1 (add-1 (add-1 (add-1 (add-1 (add-1 zero)))))))))

(defun committedpc
        (impl.mwwrt impl.mwppc impl.mmwrt impl.mmppc impl.emwrt
            impl.emppc impl.dewrt impl.deppc impl.fdwrt impl.fdppc
            impl.ffwrt impl.ffppc impl.ppc)
   (cond
     (impl.mwwrt impl.mwppc)
     (impl.mmwrt impl.mmppc)
     (impl.emwrt impl.emppc)
     (impl.dewrt impl.deppc)
     (impl.fdwrt impl.fdppc)
     (impl.ffwrt impl.ffppc)
     (t impl.ppc)))

(defun committedbpstate
        (impl.mwwrt impl.mwbpstate impl.mmwrt impl.mmbpstate impl.emwrt
            impl.embpstate impl.dewrt impl.debpstate impl.fdwrt
            impl.fdbpstate impl.ffwrt impl.ffbpstate impl.bpstate)
   (cond
     (impl.mwwrt impl.mwbpstate)
     (impl.mmwrt impl.mmbpstate)
     (impl.emwrt impl.embpstate)
     (impl.dewrt impl.debpstate)
     (impl.fdwrt impl.fdbpstate)
     (impl.ffwrt impl.ffbpstate)
     (t impl.bpstate)))

(defthm web_core_a
         (implies (and (integerp pc0) (integerp dmem0) (integerp epc0)
                       (integerp bpstate0) (integerp a) (integerp zero)
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
                  (let* ((st0 (initialize_a nil nil nil nil pc0 nil pc0
                                  bpstate0 pc0 bpstate0 ffbpstate0
                                  ffpredicteddirection0
                                  ffpredictedtarget0 ffinst0 ffppc0
                                  fdbpstate0 fdppc0 fdinst0
                                  fdpredicteddirection0
                                  fdpredictedtarget0 debpstate0 deppc0
                                  desrc10 desrc20 a1 a2 dedest0 deop0
                                  deimm0 deuseimm0 deregwrite0
                                  dememwrite0 dememtoreg0 deisbranch0
                                  depredicteddirection0
                                  depredictedtarget0 embpstate0 emppc0
                                  emis_taken_branch0 emtargetpc0
                                  emarg20 emresult0 emdest0
                                  emmispredictedtaken0
                                  emmispredictednottaken0 emregwrite0
                                  emmemwrite0 emmemtoreg0 dmem0
                                  mmbpstate0 mmppc0 mmval0 mmdest0
                                  mmregwrite0 mwbpstate0 mwppc0 mwval0
                                  mwdest0 mwregwrite0))
                         (st1 (simulate_a st0 nil nil nil pc0 nil pc0
                                  bpstate0 pc0 bpstate0 ffbpstate0
                                  ffpredicteddirection0
                                  ffpredictedtarget0 ffinst0 ffppc0
                                  fdbpstate0 fdppc0 fdinst0
                                  fdpredicteddirection0
                                  fdpredictedtarget0 debpstate0 deppc0
                                  desrc10 desrc20 a1 a2 dedest0 deop0
                                  deimm0 deuseimm0 deregwrite0
                                  dememwrite0 dememtoreg0 deisbranch0
                                  depredicteddirection0
                                  depredictedtarget0 embpstate0 emppc0
                                  emis_taken_branch0 emtargetpc0
                                  emarg20 emresult0 emdest0
                                  emmispredictedtaken0
                                  emmispredictednottaken0 emregwrite0
                                  emmemwrite0 emmemtoreg0 dmem0
                                  mmbpstate0 mmppc0 mmval0 mmdest0
                                  mmregwrite0 mwbpstate0 mwppc0 mwval0
                                  mwdest0 mwregwrite0
                                  (g 'prf (g 'impl st0))
                                  (g 'pdmemhist_2 (g 'impl st0))))
                         (st2 (simulate_a st1 nil nil nil pc0 nil pc0
                                  bpstate0 pc0 bpstate0 ffbpstate0
                                  ffpredicteddirection0
                                  ffpredictedtarget0 ffinst0 ffppc0
                                  fdbpstate0 fdppc0 fdinst0
                                  fdpredicteddirection0
                                  fdpredictedtarget0 debpstate0 deppc0
                                  desrc10 desrc20 a1 a2 dedest0 deop0
                                  deimm0 deuseimm0 deregwrite0
                                  dememwrite0 dememtoreg0 deisbranch0
                                  depredicteddirection0
                                  depredictedtarget0 embpstate0 emppc0
                                  emis_taken_branch0 emtargetpc0
                                  emarg20 emresult0 emdest0
                                  emmispredictedtaken0
                                  emmispredictednottaken0 emregwrite0
                                  emmemwrite0 emmemtoreg0 dmem0
                                  mmbpstate0 mmppc0 mmval0 mmdest0
                                  mmregwrite0 mwbpstate0 mwppc0 mwval0
                                  mwdest0 mwregwrite0
                                  (g 'prf (g 'impl st1))
                                  (g 'pdmemhist_2 (g 'impl st1))))
                         (st3 (simulate_a st2 nil nil nil pc0 nil pc0
                                  bpstate0 pc0 bpstate0 ffbpstate0
                                  ffpredicteddirection0
                                  ffpredictedtarget0 ffinst0 ffppc0
                                  fdbpstate0 fdppc0 fdinst0
                                  fdpredicteddirection0
                                  fdpredictedtarget0 debpstate0 deppc0
                                  desrc10 desrc20 a1 a2 dedest0 deop0
                                  deimm0 deuseimm0 deregwrite0
                                  dememwrite0 dememtoreg0 deisbranch0
                                  depredicteddirection0
                                  depredictedtarget0 embpstate0 emppc0
                                  emis_taken_branch0 emtargetpc0
                                  emarg20 emresult0 emdest0
                                  emmispredictedtaken0
                                  emmispredictednottaken0 emregwrite0
                                  emmemwrite0 emmemtoreg0 dmem0
                                  mmbpstate0 mmppc0 mmval0 mmdest0
                                  mmregwrite0 mwbpstate0 mwppc0 mwval0
                                  mwdest0 mwregwrite0
                                  (g 'prf (g 'impl st2))
                                  (g 'pdmemhist_2 (g 'impl st2))))
                         (st4 (simulate_a st3 nil nil nil pc0 nil pc0
                                  bpstate0 pc0 bpstate0 ffbpstate0
                                  ffpredicteddirection0
                                  ffpredictedtarget0 ffinst0 ffppc0
                                  fdbpstate0 fdppc0 fdinst0
                                  fdpredicteddirection0
                                  fdpredictedtarget0 debpstate0 deppc0
                                  desrc10 desrc20 a1 a2 dedest0 deop0
                                  deimm0 deuseimm0 deregwrite0
                                  dememwrite0 dememtoreg0 deisbranch0
                                  depredicteddirection0
                                  depredictedtarget0 embpstate0 emppc0
                                  emis_taken_branch0 emtargetpc0
                                  emarg20 emresult0 emdest0
                                  emmispredictedtaken0
                                  emmispredictednottaken0 emregwrite0
                                  emmemwrite0 emmemtoreg0 dmem0
                                  mmbpstate0 mmppc0 mmval0 mmdest0
                                  mmregwrite0 mwbpstate0 mwppc0 mwval0
                                  mwdest0 mwregwrite0
                                  (g 'prf (g 'impl st3))
                                  (g 'pdmemhist_2 (g 'impl st3))))
                         (st5 (simulate_a st4 nil nil nil pc0 nil pc0
                                  bpstate0 pc0 bpstate0 ffbpstate0
                                  ffpredicteddirection0
                                  ffpredictedtarget0 ffinst0 ffppc0
                                  fdbpstate0 fdppc0 fdinst0
                                  fdpredicteddirection0
                                  fdpredictedtarget0 debpstate0 deppc0
                                  desrc10 desrc20 a1 a2 dedest0 deop0
                                  deimm0 deuseimm0 deregwrite0
                                  dememwrite0 dememtoreg0 deisbranch0
                                  depredicteddirection0
                                  depredictedtarget0 embpstate0 emppc0
                                  emis_taken_branch0 emtargetpc0
                                  emarg20 emresult0 emdest0
                                  emmispredictedtaken0
                                  emmispredictednottaken0 emregwrite0
                                  emmemwrite0 emmemtoreg0 dmem0
                                  mmbpstate0 mmppc0 mmval0 mmdest0
                                  mmregwrite0 mwbpstate0 mwppc0 mwval0
                                  mwdest0 mwregwrite0
                                  (g 'prf (g 'impl st4))
                                  (g 'pdmemhist_2 (g 'impl st4))))
                         (st6 (simulate_a st5 nil nil nil pc0 nil pc0
                                  bpstate0 pc0 bpstate0 ffbpstate0
                                  ffpredicteddirection0
                                  ffpredictedtarget0 ffinst0 ffppc0
                                  fdbpstate0 fdppc0 fdinst0
                                  fdpredicteddirection0
                                  fdpredictedtarget0 debpstate0 deppc0
                                  desrc10 desrc20 a1 a2 dedest0 deop0
                                  deimm0 deuseimm0 deregwrite0
                                  dememwrite0 dememtoreg0 deisbranch0
                                  depredicteddirection0
                                  depredictedtarget0 embpstate0 emppc0
                                  emis_taken_branch0 emtargetpc0
                                  emarg20 emresult0 emdest0
                                  emmispredictedtaken0
                                  emmispredictednottaken0 emregwrite0
                                  emmemwrite0 emmemtoreg0 dmem0
                                  mmbpstate0 mmppc0 mmval0 mmdest0
                                  mmregwrite0 mwbpstate0 mwppc0 mwval0
                                  mwdest0 mwregwrite0
                                  (g 'prf (g 'impl st5))
                                  (g 'pdmemhist_2 (g 'impl st5))))
                         (st7 (simulate_a st6 nil nil nil pc0 nil pc0
                                  bpstate0 pc0 bpstate0 ffbpstate0
                                  ffpredicteddirection0
                                  ffpredictedtarget0 ffinst0 ffppc0
                                  fdbpstate0 fdppc0 fdinst0
                                  fdpredicteddirection0
                                  fdpredictedtarget0 debpstate0 deppc0
                                  desrc10 desrc20 a1 a2 dedest0 deop0
                                  deimm0 deuseimm0 deregwrite0
                                  dememwrite0 dememtoreg0 deisbranch0
                                  depredicteddirection0
                                  depredictedtarget0 embpstate0 emppc0
                                  emis_taken_branch0 emtargetpc0
                                  emarg20 emresult0 emdest0
                                  emmispredictedtaken0
                                  emmispredictednottaken0 emregwrite0
                                  emmemwrite0 emmemtoreg0 dmem0
                                  mmbpstate0 mmppc0 mmval0 mmdest0
                                  mmregwrite0 mwbpstate0 mwppc0 mwval0
                                  mwdest0 mwregwrite0
                                  (g 'prf (g 'impl st6))
                                  (g 'pdmemhist_2 (g 'impl st6))))
                         (ppc_v (g 'ppc (g 'impl st7)))
                         (prf_v (g 'prf (g 'impl st7)))
                         (pdmem_v (g 'pdmem (g 'impl st7)))
                         (pimem_v (g 'pimem (g 'impl st7)))
                         (deop_v (g 'deop (g 'impl st7)))
                         (desrc2_v (g 'desrc2 (g 'impl st7)))
                         (dearg1_v (g 'dearg1 (g 'impl st7)))
                         (dearg2_v (g 'dearg2 (g 'impl st7)))
                         (dedest_v (g 'dedest (g 'impl st7)))
                         (dewrt_v (g 'dewrt (g 'impl st7)))
                         (fdwrt_v (g 'fdwrt (g 'impl st7)))
                         (fdinst_v (g 'fdinst (g 'impl st7)))
                         (emdest_v (g 'emdest (g 'impl st7)))
                         (emwrt_v (g 'emwrt (g 'impl st7)))
                         (desrc1_v (g 'desrc1 (g 'impl st7)))
                         (desrc2_v (g 'desrc2 (g 'impl st7)))
                         (deregwrite_v (g 'deregwrite (g 'impl st7)))
                         (emregwrite_v (g 'emregwrite (g 'impl st7)))
                         (deimm_v (g 'deimm (g 'impl st7)))
                         (deuseimm_v (g 'deuseimm (g 'impl st7)))
                         (emresult_v (g 'emresult (g 'impl st7)))
                         (dememtoreg_v (g 'dememtoreg (g 'impl st7)))
                         (emmemtoreg_v (g 'emmemtoreg (g 'impl st7)))
                         (dememwrite_v (g 'dememwrite (g 'impl st7)))
                         (emmemwrite_v (g 'emmemwrite (g 'impl st7)))
                         (emarg2_v (g 'emarg2 (g 'impl st7)))
                         (ffwrt_v (g 'ffwrt (g 'impl st7)))
                         (ffinst_v (g 'ffinst (g 'impl st7)))
                         (mmval_v (g 'mmval (g 'impl st7)))
                         (mmdest_v (g 'mmdest (g 'impl st7)))
                         (mmwrt_v (g 'mmwrt (g 'impl st7)))
                         (mmregwrite_v (g 'mmregwrite (g 'impl st7)))
                         (mwval_v (g 'mwval (g 'impl st7)))
                         (mwdest_v (g 'mwdest (g 'impl st7)))
                         (mwwrt_v (g 'mwwrt (g 'impl st7)))
                         (mwregwrite_v (g 'mwregwrite (g 'impl st7)))
                         (deisbranch_v (g 'deisbranch (g 'impl st7)))
                         (emis_taken_branch_v
                             (g 'emis_taken_branch (g 'impl st7)))
                         (emtargetpc_v (g 'emtargetpc (g 'impl st7)))
                         (ffppc_v (g 'ffppc (g 'impl st7)))
                         (fdppc_v (g 'fdppc (g 'impl st7)))
                         (deppc_v (g 'deppc (g 'impl st7)))
                         (i_pc0 (committedpc (g 'mwwrt (g 'impl st7))
                                    (g 'mwppc (g 'impl st7))
                                    (g 'mmwrt (g 'impl st7))
                                    (g 'mmppc (g 'impl st7))
                                    (g 'emwrt (g 'impl st7))
                                    (g 'emppc (g 'impl st7))
                                    (g 'dewrt (g 'impl st7))
                                    (g 'deppc (g 'impl st7))
                                    (g 'fdwrt (g 'impl st7))
                                    (g 'fdppc (g 'impl st7))
                                    (g 'ffwrt (g 'impl st7))
                                    (g 'ffppc (g 'impl st7))
                                    (g 'ppc (g 'impl st7))))
                         (st8 (simulate_a st7 nil nil nil pc0 t i_pc0
                                  committedbpstate pc0 bpstate0
                                  ffbpstate0 ffpredicteddirection0
                                  ffpredictedtarget0 ffinst0 ffppc0
                                  fdbpstate0 fdppc0 fdinst0
                                  fdpredicteddirection0
                                  fdpredictedtarget0 debpstate0 deppc0
                                  desrc10 desrc20 a1 a2 dedest0 deop0
                                  deimm0 deuseimm0 deregwrite0
                                  dememwrite0 dememtoreg0 deisbranch0
                                  depredicteddirection0
                                  depredictedtarget0 embpstate0 emppc0
                                  emis_taken_branch0 emtargetpc0
                                  emarg20 emresult0 emdest0
                                  emmispredictedtaken0
                                  emmispredictednottaken0 emregwrite0
                                  emmemwrite0 emmemtoreg0 dmem0
                                  mmbpstate0 mmppc0 mmval0 mmdest0
                                  mmregwrite0 mwbpstate0 mwppc0 mwval0
                                  mwdest0 mwregwrite0
                                  (g 'prf (g 'impl st7))
                                  (g 'pdmemhist_2 (g 'impl st7))))
                         (equiv_ma_0
                             (equiv_ma ppc_v (g 'ppc (g 'impl st8))
                                 prf_v a1 (g 'prf (g 'impl st8))
                                 pimem_v (g 'pimem (g 'impl st8))
                                 pdmem_v (g 'pdmem (g 'impl st8))
                                 ffwrt_v (g 'ffwrt (g 'impl st8))
                                 ffppc_v (g 'ffppc (g 'impl st8))
                                 ffinst_v (g 'ffinst (g 'impl st8))
                                 fdwrt_v (g 'fdwrt (g 'impl st8))
                                 fdppc_v (g 'fdppc (g 'impl st8))
                                 fdinst_v (g 'fdinst (g 'impl st8))
                                 dewrt_v (g 'dewrt (g 'impl st8))
                                 deppc_v (g 'deppc (g 'impl st8))
                                 deop_v (g 'deop (g 'impl st8))
                                 dearg1_v (g 'dearg1 (g 'impl st8))
                                 dearg2_v (g 'dearg2 (g 'impl st8))
                                 dedest_v (g 'dedest (g 'impl st8))
                                 desrc1_v (g 'desrc1 (g 'impl st8))
                                 desrc2_v (g 'desrc2 (g 'impl st8))
                                 deimm_v (g 'deimm (g 'impl st8))
                                 deuseimm_v (g 'deuseimm (g 'impl st8))
                                 deisbranch_v
                                 (g 'deisbranch (g 'impl st8))
                                 dememtoreg_v
                                 (g 'dememtoreg (g 'impl st8))
                                 dememwrite_v
                                 (g 'dememwrite (g 'impl st8))
                                 deregwrite_v
                                 (g 'deregwrite (g 'impl st8)) emwrt_v
                                 (g 'emwrt (g 'impl st8)) emtargetpc_v
                                 (g 'emtargetpc (g 'impl st8)) emdest_v
                                 (g 'emdest (g 'impl st8)) emarg2_v
                                 (g 'emarg2 (g 'impl st8)) emregwrite_v
                                 (g 'emregwrite (g 'impl st8))
                                 emresult_v (g 'emresult (g 'impl st8))
                                 emis_taken_branch_v
                                 (g 'emis_taken_branch (g 'impl st8))
                                 emmemtoreg_v
                                 (g 'emmemtoreg (g 'impl st8))
                                 emmemwrite_v
                                 (g 'emmemwrite (g 'impl st8)) mmwrt_v
                                 (g 'mmwrt (g 'impl st8)) mmval_v
                                 (g 'mmval (g 'impl st8)) mmdest_v
                                 (g 'mmdest (g 'impl st8)) mmregwrite_v
                                 (g 'mmregwrite (g 'impl st8)) mwwrt_v
                                 (g 'mwwrt (g 'impl st8)) mwval_v
                                 (g 'mwval (g 'impl st8)) mwdest_v
                                 (g 'mwdest (g 'impl st8)) mwregwrite_v
                                 (g 'mwregwrite (g 'impl st8))))
                         (st9 (simulate_a st8 nil nil nil pc0 nil pc0
                                  bpstate0 pc0 bpstate0 ffbpstate0
                                  ffpredicteddirection0
                                  ffpredictedtarget0 ffinst0 ffppc0
                                  fdbpstate0 fdppc0 fdinst0
                                  fdpredicteddirection0
                                  fdpredictedtarget0 debpstate0 deppc0
                                  desrc10 desrc20 a1 a2 dedest0 deop0
                                  deimm0 deuseimm0 deregwrite0
                                  dememwrite0 dememtoreg0 deisbranch0
                                  depredicteddirection0
                                  depredictedtarget0 embpstate0 emppc0
                                  emis_taken_branch0 emtargetpc0
                                  emarg20 emresult0 emdest0
                                  emmispredictedtaken0
                                  emmispredictednottaken0 emregwrite0
                                  emmemwrite0 emmemtoreg0 dmem0
                                  mmbpstate0 mmppc0 mmval0 mmdest0
                                  mmregwrite0 mwbpstate0 mwppc0 mwval0
                                  mwdest0 mwregwrite0
                                  (g 'prf (g 'impl st8))
                                  (g 'pdmemhist_2 (g 'impl st8))))
                         (equiv_ma_1
                             (equiv_ma ppc_v (g 'ppc (g 'impl st9))
                                 prf_v a1 (g 'prf (g 'impl st9))
                                 pimem_v (g 'pimem (g 'impl st9))
                                 pdmem_v (g 'pdmem (g 'impl st9))
                                 ffwrt_v (g 'ffwrt (g 'impl st9))
                                 ffppc_v (g 'ffppc (g 'impl st9))
                                 ffinst_v (g 'ffinst (g 'impl st9))
                                 fdwrt_v (g 'fdwrt (g 'impl st9))
                                 fdppc_v (g 'fdppc (g 'impl st9))
                                 fdinst_v (g 'fdinst (g 'impl st9))
                                 dewrt_v (g 'dewrt (g 'impl st9))
                                 deppc_v (g 'deppc (g 'impl st9))
                                 deop_v (g 'deop (g 'impl st9))
                                 dearg1_v (g 'dearg1 (g 'impl st9))
                                 dearg2_v (g 'dearg2 (g 'impl st9))
                                 dedest_v (g 'dedest (g 'impl st9))
                                 desrc1_v (g 'desrc1 (g 'impl st9))
                                 desrc2_v (g 'desrc2 (g 'impl st9))
                                 deimm_v (g 'deimm (g 'impl st9))
                                 deuseimm_v (g 'deuseimm (g 'impl st9))
                                 deisbranch_v
                                 (g 'deisbranch (g 'impl st9))
                                 dememtoreg_v
                                 (g 'dememtoreg (g 'impl st9))
                                 dememwrite_v
                                 (g 'dememwrite (g 'impl st9))
                                 deregwrite_v
                                 (g 'deregwrite (g 'impl st9)) emwrt_v
                                 (g 'emwrt (g 'impl st9)) emtargetpc_v
                                 (g 'emtargetpc (g 'impl st9)) emdest_v
                                 (g 'emdest (g 'impl st9)) emarg2_v
                                 (g 'emarg2 (g 'impl st9)) emregwrite_v
                                 (g 'emregwrite (g 'impl st9))
                                 emresult_v (g 'emresult (g 'impl st9))
                                 emis_taken_branch_v
                                 (g 'emis_taken_branch (g 'impl st9))
                                 emmemtoreg_v
                                 (g 'emmemtoreg (g 'impl st9))
                                 emmemwrite_v
                                 (g 'emmemwrite (g 'impl st9)) mmwrt_v
                                 (g 'mmwrt (g 'impl st9)) mmval_v
                                 (g 'mmval (g 'impl st9)) mmdest_v
                                 (g 'mmdest (g 'impl st9)) mmregwrite_v
                                 (g 'mmregwrite (g 'impl st9)) mwwrt_v
                                 (g 'mwwrt (g 'impl st9)) mwval_v
                                 (g 'mwval (g 'impl st9)) mwdest_v
                                 (g 'mwdest (g 'impl st9)) mwregwrite_v
                                 (g 'mwregwrite (g 'impl st9))))
                         (st10 (simulate_a st9 nil nil nil pc0 nil pc0
                                   bpstate0 pc0 bpstate0 ffbpstate0
                                   ffpredicteddirection0
                                   ffpredictedtarget0 ffinst0 ffppc0
                                   fdbpstate0 fdppc0 fdinst0
                                   fdpredicteddirection0
                                   fdpredictedtarget0 debpstate0 deppc0
                                   desrc10 desrc20 a1 a2 dedest0 deop0
                                   deimm0 deuseimm0 deregwrite0
                                   dememwrite0 dememtoreg0 deisbranch0
                                   depredicteddirection0
                                   depredictedtarget0 embpstate0 emppc0
                                   emis_taken_branch0 emtargetpc0
                                   emarg20 emresult0 emdest0
                                   emmispredictedtaken0
                                   emmispredictednottaken0 emregwrite0
                                   emmemwrite0 emmemtoreg0 dmem0
                                   mmbpstate0 mmppc0 mmval0 mmdest0
                                   mmregwrite0 mwbpstate0 mwppc0 mwval0
                                   mwdest0 mwregwrite0
                                   (g 'prf (g 'impl st9))
                                   (g 'pdmemhist_2 (g 'impl st9))))
                         (equiv_ma_2
                             (equiv_ma ppc_v (g 'ppc (g 'impl st10))
                                 prf_v a1 (g 'prf (g 'impl st10))
                                 pimem_v (g 'pimem (g 'impl st10))
                                 pdmem_v (g 'pdmem (g 'impl st10))
                                 ffwrt_v (g 'ffwrt (g 'impl st10))
                                 ffppc_v (g 'ffppc (g 'impl st10))
                                 ffinst_v (g 'ffinst (g 'impl st10))
                                 fdwrt_v (g 'fdwrt (g 'impl st10))
                                 fdppc_v (g 'fdppc (g 'impl st10))
                                 fdinst_v (g 'fdinst (g 'impl st10))
                                 dewrt_v (g 'dewrt (g 'impl st10))
                                 deppc_v (g 'deppc (g 'impl st10))
                                 deop_v (g 'deop (g 'impl st10))
                                 dearg1_v (g 'dearg1 (g 'impl st10))
                                 dearg2_v (g 'dearg2 (g 'impl st10))
                                 dedest_v (g 'dedest (g 'impl st10))
                                 desrc1_v (g 'desrc1 (g 'impl st10))
                                 desrc2_v (g 'desrc2 (g 'impl st10))
                                 deimm_v (g 'deimm (g 'impl st10))
                                 deuseimm_v
                                 (g 'deuseimm (g 'impl st10))
                                 deisbranch_v
                                 (g 'deisbranch (g 'impl st10))
                                 dememtoreg_v
                                 (g 'dememtoreg (g 'impl st10))
                                 dememwrite_v
                                 (g 'dememwrite (g 'impl st10))
                                 deregwrite_v
                                 (g 'deregwrite (g 'impl st10)) emwrt_v
                                 (g 'emwrt (g 'impl st10)) emtargetpc_v
                                 (g 'emtargetpc (g 'impl st10))
                                 emdest_v (g 'emdest (g 'impl st10))
                                 emarg2_v (g 'emarg2 (g 'impl st10))
                                 emregwrite_v
                                 (g 'emregwrite (g 'impl st10))
                                 emresult_v
                                 (g 'emresult (g 'impl st10))
                                 emis_taken_branch_v
                                 (g 'emis_taken_branch (g 'impl st10))
                                 emmemtoreg_v
                                 (g 'emmemtoreg (g 'impl st10))
                                 emmemwrite_v
                                 (g 'emmemwrite (g 'impl st10)) mmwrt_v
                                 (g 'mmwrt (g 'impl st10)) mmval_v
                                 (g 'mmval (g 'impl st10)) mmdest_v
                                 (g 'mmdest (g 'impl st10))
                                 mmregwrite_v
                                 (g 'mmregwrite (g 'impl st10)) mwwrt_v
                                 (g 'mwwrt (g 'impl st10)) mwval_v
                                 (g 'mwval (g 'impl st10)) mwdest_v
                                 (g 'mwdest (g 'impl st10))
                                 mwregwrite_v
                                 (g 'mwregwrite (g 'impl st10))))
                         (st11 (simulate_a st10 nil nil nil pc0 nil pc0
                                   bpstate0 pc0 bpstate0 ffbpstate0
                                   ffpredicteddirection0
                                   ffpredictedtarget0 ffinst0 ffppc0
                                   fdbpstate0 fdppc0 fdinst0
                                   fdpredicteddirection0
                                   fdpredictedtarget0 debpstate0 deppc0
                                   desrc10 desrc20 a1 a2 dedest0 deop0
                                   deimm0 deuseimm0 deregwrite0
                                   dememwrite0 dememtoreg0 deisbranch0
                                   depredicteddirection0
                                   depredictedtarget0 embpstate0 emppc0
                                   emis_taken_branch0 emtargetpc0
                                   emarg20 emresult0 emdest0
                                   emmispredictedtaken0
                                   emmispredictednottaken0 emregwrite0
                                   emmemwrite0 emmemtoreg0 dmem0
                                   mmbpstate0 mmppc0 mmval0 mmdest0
                                   mmregwrite0 mwbpstate0 mwppc0 mwval0
                                   mwdest0 mwregwrite0
                                   (g 'prf (g 'impl st10))
                                   (g 'pdmemhist_2 (g 'impl st10))))
                         (equiv_ma_3
                             (equiv_ma ppc_v (g 'ppc (g 'impl st11))
                                 prf_v a1 (g 'prf (g 'impl st11))
                                 pimem_v (g 'pimem (g 'impl st11))
                                 pdmem_v (g 'pdmem (g 'impl st11))
                                 ffwrt_v (g 'ffwrt (g 'impl st11))
                                 ffppc_v (g 'ffppc (g 'impl st11))
                                 ffinst_v (g 'ffinst (g 'impl st11))
                                 fdwrt_v (g 'fdwrt (g 'impl st11))
                                 fdppc_v (g 'fdppc (g 'impl st11))
                                 fdinst_v (g 'fdinst (g 'impl st11))
                                 dewrt_v (g 'dewrt (g 'impl st11))
                                 deppc_v (g 'deppc (g 'impl st11))
                                 deop_v (g 'deop (g 'impl st11))
                                 dearg1_v (g 'dearg1 (g 'impl st11))
                                 dearg2_v (g 'dearg2 (g 'impl st11))
                                 dedest_v (g 'dedest (g 'impl st11))
                                 desrc1_v (g 'desrc1 (g 'impl st11))
                                 desrc2_v (g 'desrc2 (g 'impl st11))
                                 deimm_v (g 'deimm (g 'impl st11))
                                 deuseimm_v
                                 (g 'deuseimm (g 'impl st11))
                                 deisbranch_v
                                 (g 'deisbranch (g 'impl st11))
                                 dememtoreg_v
                                 (g 'dememtoreg (g 'impl st11))
                                 dememwrite_v
                                 (g 'dememwrite (g 'impl st11))
                                 deregwrite_v
                                 (g 'deregwrite (g 'impl st11)) emwrt_v
                                 (g 'emwrt (g 'impl st11)) emtargetpc_v
                                 (g 'emtargetpc (g 'impl st11))
                                 emdest_v (g 'emdest (g 'impl st11))
                                 emarg2_v (g 'emarg2 (g 'impl st11))
                                 emregwrite_v
                                 (g 'emregwrite (g 'impl st11))
                                 emresult_v
                                 (g 'emresult (g 'impl st11))
                                 emis_taken_branch_v
                                 (g 'emis_taken_branch (g 'impl st11))
                                 emmemtoreg_v
                                 (g 'emmemtoreg (g 'impl st11))
                                 emmemwrite_v
                                 (g 'emmemwrite (g 'impl st11)) mmwrt_v
                                 (g 'mmwrt (g 'impl st11)) mmval_v
                                 (g 'mmval (g 'impl st11)) mmdest_v
                                 (g 'mmdest (g 'impl st11))
                                 mmregwrite_v
                                 (g 'mmregwrite (g 'impl st11)) mwwrt_v
                                 (g 'mwwrt (g 'impl st11)) mwval_v
                                 (g 'mwval (g 'impl st11)) mwdest_v
                                 (g 'mwdest (g 'impl st11))
                                 mwregwrite_v
                                 (g 'mwregwrite (g 'impl st11))))
                         (st12 (simulate_a st11 nil nil nil pc0 nil pc0
                                   bpstate0 pc0 bpstate0 ffbpstate0
                                   ffpredicteddirection0
                                   ffpredictedtarget0 ffinst0 ffppc0
                                   fdbpstate0 fdppc0 fdinst0
                                   fdpredicteddirection0
                                   fdpredictedtarget0 debpstate0 deppc0
                                   desrc10 desrc20 a1 a2 dedest0 deop0
                                   deimm0 deuseimm0 deregwrite0
                                   dememwrite0 dememtoreg0 deisbranch0
                                   depredicteddirection0
                                   depredictedtarget0 embpstate0 emppc0
                                   emis_taken_branch0 emtargetpc0
                                   emarg20 emresult0 emdest0
                                   emmispredictedtaken0
                                   emmispredictednottaken0 emregwrite0
                                   emmemwrite0 emmemtoreg0 dmem0
                                   mmbpstate0 mmppc0 mmval0 mmdest0
                                   mmregwrite0 mwbpstate0 mwppc0 mwval0
                                   mwdest0 mwregwrite0
                                   (g 'prf (g 'impl st11))
                                   (g 'pdmemhist_2 (g 'impl st11))))
                         (equiv_ma_4
                             (equiv_ma ppc_v (g 'ppc (g 'impl st12))
                                 prf_v a1 (g 'prf (g 'impl st12))
                                 pimem_v (g 'pimem (g 'impl st12))
                                 pdmem_v (g 'pdmem (g 'impl st12))
                                 ffwrt_v (g 'ffwrt (g 'impl st12))
                                 ffppc_v (g 'ffppc (g 'impl st12))
                                 ffinst_v (g 'ffinst (g 'impl st12))
                                 fdwrt_v (g 'fdwrt (g 'impl st12))
                                 fdppc_v (g 'fdppc (g 'impl st12))
                                 fdinst_v (g 'fdinst (g 'impl st12))
                                 dewrt_v (g 'dewrt (g 'impl st12))
                                 deppc_v (g 'deppc (g 'impl st12))
                                 deop_v (g 'deop (g 'impl st12))
                                 dearg1_v (g 'dearg1 (g 'impl st12))
                                 dearg2_v (g 'dearg2 (g 'impl st12))
                                 dedest_v (g 'dedest (g 'impl st12))
                                 desrc1_v (g 'desrc1 (g 'impl st12))
                                 desrc2_v (g 'desrc2 (g 'impl st12))
                                 deimm_v (g 'deimm (g 'impl st12))
                                 deuseimm_v
                                 (g 'deuseimm (g 'impl st12))
                                 deisbranch_v
                                 (g 'deisbranch (g 'impl st12))
                                 dememtoreg_v
                                 (g 'dememtoreg (g 'impl st12))
                                 dememwrite_v
                                 (g 'dememwrite (g 'impl st12))
                                 deregwrite_v
                                 (g 'deregwrite (g 'impl st12)) emwrt_v
                                 (g 'emwrt (g 'impl st12)) emtargetpc_v
                                 (g 'emtargetpc (g 'impl st12))
                                 emdest_v (g 'emdest (g 'impl st12))
                                 emarg2_v (g 'emarg2 (g 'impl st12))
                                 emregwrite_v
                                 (g 'emregwrite (g 'impl st12))
                                 emresult_v
                                 (g 'emresult (g 'impl st12))
                                 emis_taken_branch_v
                                 (g 'emis_taken_branch (g 'impl st12))
                                 emmemtoreg_v
                                 (g 'emmemtoreg (g 'impl st12))
                                 emmemwrite_v
                                 (g 'emmemwrite (g 'impl st12)) mmwrt_v
                                 (g 'mmwrt (g 'impl st12)) mmval_v
                                 (g 'mmval (g 'impl st12)) mmdest_v
                                 (g 'mmdest (g 'impl st12))
                                 mmregwrite_v
                                 (g 'mmregwrite (g 'impl st12)) mwwrt_v
                                 (g 'mwwrt (g 'impl st12)) mwval_v
                                 (g 'mwval (g 'impl st12)) mwdest_v
                                 (g 'mwdest (g 'impl st12))
                                 mwregwrite_v
                                 (g 'mwregwrite (g 'impl st12))))
                         (st13 (simulate_a st12 nil nil nil pc0 nil pc0
                                   bpstate0 pc0 bpstate0 ffbpstate0
                                   ffpredicteddirection0
                                   ffpredictedtarget0 ffinst0 ffppc0
                                   fdbpstate0 fdppc0 fdinst0
                                   fdpredicteddirection0
                                   fdpredictedtarget0 debpstate0 deppc0
                                   desrc10 desrc20 a1 a2 dedest0 deop0
                                   deimm0 deuseimm0 deregwrite0
                                   dememwrite0 dememtoreg0 deisbranch0
                                   depredicteddirection0
                                   depredictedtarget0 embpstate0 emppc0
                                   emis_taken_branch0 emtargetpc0
                                   emarg20 emresult0 emdest0
                                   emmispredictedtaken0
                                   emmispredictednottaken0 emregwrite0
                                   emmemwrite0 emmemtoreg0 dmem0
                                   mmbpstate0 mmppc0 mmval0 mmdest0
                                   mmregwrite0 mwbpstate0 mwppc0 mwval0
                                   mwdest0 mwregwrite0
                                   (g 'prf (g 'impl st12))
                                   (g 'pdmemhist_2 (g 'impl st12))))
                         (equiv_ma_5
                             (equiv_ma ppc_v (g 'ppc (g 'impl st13))
                                 prf_v a1 (g 'prf (g 'impl st13))
                                 pimem_v (g 'pimem (g 'impl st13))
                                 pdmem_v (g 'pdmem (g 'impl st13))
                                 ffwrt_v (g 'ffwrt (g 'impl st13))
                                 ffppc_v (g 'ffppc (g 'impl st13))
                                 ffinst_v (g 'ffinst (g 'impl st13))
                                 fdwrt_v (g 'fdwrt (g 'impl st13))
                                 fdppc_v (g 'fdppc (g 'impl st13))
                                 fdinst_v (g 'fdinst (g 'impl st13))
                                 dewrt_v (g 'dewrt (g 'impl st13))
                                 deppc_v (g 'deppc (g 'impl st13))
                                 deop_v (g 'deop (g 'impl st13))
                                 dearg1_v (g 'dearg1 (g 'impl st13))
                                 dearg2_v (g 'dearg2 (g 'impl st13))
                                 dedest_v (g 'dedest (g 'impl st13))
                                 desrc1_v (g 'desrc1 (g 'impl st13))
                                 desrc2_v (g 'desrc2 (g 'impl st13))
                                 deimm_v (g 'deimm (g 'impl st13))
                                 deuseimm_v
                                 (g 'deuseimm (g 'impl st13))
                                 deisbranch_v
                                 (g 'deisbranch (g 'impl st13))
                                 dememtoreg_v
                                 (g 'dememtoreg (g 'impl st13))
                                 dememwrite_v
                                 (g 'dememwrite (g 'impl st13))
                                 deregwrite_v
                                 (g 'deregwrite (g 'impl st13)) emwrt_v
                                 (g 'emwrt (g 'impl st13)) emtargetpc_v
                                 (g 'emtargetpc (g 'impl st13))
                                 emdest_v (g 'emdest (g 'impl st13))
                                 emarg2_v (g 'emarg2 (g 'impl st13))
                                 emregwrite_v
                                 (g 'emregwrite (g 'impl st13))
                                 emresult_v
                                 (g 'emresult (g 'impl st13))
                                 emis_taken_branch_v
                                 (g 'emis_taken_branch (g 'impl st13))
                                 emmemtoreg_v
                                 (g 'emmemtoreg (g 'impl st13))
                                 emmemwrite_v
                                 (g 'emmemwrite (g 'impl st13)) mmwrt_v
                                 (g 'mmwrt (g 'impl st13)) mmval_v
                                 (g 'mmval (g 'impl st13)) mmdest_v
                                 (g 'mmdest (g 'impl st13))
                                 mmregwrite_v
                                 (g 'mmregwrite (g 'impl st13)) mwwrt_v
                                 (g 'mwwrt (g 'impl st13)) mwval_v
                                 (g 'mwval (g 'impl st13)) mwdest_v
                                 (g 'mwdest (g 'impl st13))
                                 mwregwrite_v
                                 (g 'mwregwrite (g 'impl st13))))
                         (st14 (simulate_a st13 nil nil nil pc0 nil pc0
                                   bpstate0 pc0 bpstate0 ffbpstate0
                                   ffpredicteddirection0
                                   ffpredictedtarget0 ffinst0 ffppc0
                                   fdbpstate0 fdppc0 fdinst0
                                   fdpredicteddirection0
                                   fdpredictedtarget0 debpstate0 deppc0
                                   desrc10 desrc20 a1 a2 dedest0 deop0
                                   deimm0 deuseimm0 deregwrite0
                                   dememwrite0 dememtoreg0 deisbranch0
                                   depredicteddirection0
                                   depredictedtarget0 embpstate0 emppc0
                                   emis_taken_branch0 emtargetpc0
                                   emarg20 emresult0 emdest0
                                   emmispredictedtaken0
                                   emmispredictednottaken0 emregwrite0
                                   emmemwrite0 emmemtoreg0 dmem0
                                   mmbpstate0 mmppc0 mmval0 mmdest0
                                   mmregwrite0 mwbpstate0 mwppc0 mwval0
                                   mwdest0 mwregwrite0
                                   (g 'prf (g 'impl st13))
                                   (g 'pdmemhist_2 (g 'impl st13))))
                         (equiv_ma_6
                             (equiv_ma ppc_v (g 'ppc (g 'impl st14))
                                 prf_v a1 (g 'prf (g 'impl st14))
                                 pimem_v (g 'pimem (g 'impl st14))
                                 pdmem_v (g 'pdmem (g 'impl st14))
                                 ffwrt_v (g 'ffwrt (g 'impl st14))
                                 ffppc_v (g 'ffppc (g 'impl st14))
                                 ffinst_v (g 'ffinst (g 'impl st14))
                                 fdwrt_v (g 'fdwrt (g 'impl st14))
                                 fdppc_v (g 'fdppc (g 'impl st14))
                                 fdinst_v (g 'fdinst (g 'impl st14))
                                 dewrt_v (g 'dewrt (g 'impl st14))
                                 deppc_v (g 'deppc (g 'impl st14))
                                 deop_v (g 'deop (g 'impl st14))
                                 dearg1_v (g 'dearg1 (g 'impl st14))
                                 dearg2_v (g 'dearg2 (g 'impl st14))
                                 dedest_v (g 'dedest (g 'impl st14))
                                 desrc1_v (g 'desrc1 (g 'impl st14))
                                 desrc2_v (g 'desrc2 (g 'impl st14))
                                 deimm_v (g 'deimm (g 'impl st14))
                                 deuseimm_v
                                 (g 'deuseimm (g 'impl st14))
                                 deisbranch_v
                                 (g 'deisbranch (g 'impl st14))
                                 dememtoreg_v
                                 (g 'dememtoreg (g 'impl st14))
                                 dememwrite_v
                                 (g 'dememwrite (g 'impl st14))
                                 deregwrite_v
                                 (g 'deregwrite (g 'impl st14)) emwrt_v
                                 (g 'emwrt (g 'impl st14)) emtargetpc_v
                                 (g 'emtargetpc (g 'impl st14))
                                 emdest_v (g 'emdest (g 'impl st14))
                                 emarg2_v (g 'emarg2 (g 'impl st14))
                                 emregwrite_v
                                 (g 'emregwrite (g 'impl st14))
                                 emresult_v
                                 (g 'emresult (g 'impl st14))
                                 emis_taken_branch_v
                                 (g 'emis_taken_branch (g 'impl st14))
                                 emmemtoreg_v
                                 (g 'emmemtoreg (g 'impl st14))
                                 emmemwrite_v
                                 (g 'emmemwrite (g 'impl st14)) mmwrt_v
                                 (g 'mmwrt (g 'impl st14)) mmval_v
                                 (g 'mmval (g 'impl st14)) mmdest_v
                                 (g 'mmdest (g 'impl st14))
                                 mmregwrite_v
                                 (g 'mmregwrite (g 'impl st14)) mwwrt_v
                                 (g 'mwwrt (g 'impl st14)) mwval_v
                                 (g 'mwval (g 'impl st14)) mwdest_v
                                 (g 'mwdest (g 'impl st14))
                                 mwregwrite_v
                                 (g 'mwregwrite (g 'impl st14))))
                         (good_ma_v
                             (or (or equiv_ma_2 equiv_ma_5) equiv_ma_6))
                         (st15 (simulate_a st14 t nil nil pc0 nil pc0
                                   bpstate0 pc0 bpstate0 ffbpstate0
                                   ffpredicteddirection0
                                   ffpredictedtarget0 ffinst0 ffppc0
                                   fdbpstate0 fdppc0 fdinst0
                                   fdpredicteddirection0
                                   fdpredictedtarget0 debpstate0 deppc0
                                   desrc10 desrc20 a1 a2 dedest0 deop0
                                   deimm0 deuseimm0 deregwrite0
                                   dememwrite0 dememtoreg0 deisbranch0
                                   depredicteddirection0
                                   depredictedtarget0 embpstate0 emppc0
                                   emis_taken_branch0 emtargetpc0
                                   emarg20 emresult0 emdest0
                                   emmispredictedtaken0
                                   emmispredictednottaken0 emregwrite0
                                   emmemwrite0 emmemtoreg0 dmem0
                                   mmbpstate0 mmppc0 mmval0 mmdest0
                                   mmregwrite0 mwbpstate0 mwppc0 mwval0
                                   mwdest0 mwregwrite0
                                   (g 'prf (g 'impl st14))
                                   (g 'pdmemhist_2 (g 'impl st14))))
                         (st16 (simulate_a st15 nil nil nil pc0 nil pc0
                                   bpstate0 pc0 bpstate0 ffbpstate0
                                   ffpredicteddirection0
                                   ffpredictedtarget0 ffinst0 ffppc0
                                   fdbpstate0 fdppc0 fdinst0
                                   fdpredicteddirection0
                                   fdpredictedtarget0 debpstate0 deppc0
                                   desrc10 desrc20 a1 a2 dedest0 deop0
                                   deimm0 deuseimm0 deregwrite0
                                   dememwrite0 dememtoreg0 deisbranch0
                                   depredicteddirection0
                                   depredictedtarget0 embpstate0 emppc0
                                   emis_taken_branch0 emtargetpc0
                                   emarg20 emresult0 emdest0
                                   emmispredictedtaken0
                                   emmispredictednottaken0 emregwrite0
                                   emmemwrite0 emmemtoreg0 dmem0
                                   mmbpstate0 mmppc0 mmval0 mmdest0
                                   mmregwrite0 mwbpstate0 mwppc0 mwval0
                                   mwdest0 mwregwrite0
                                   (g 'prf (g 'impl st15))
                                   (g 'pdmemhist_2 (g 'impl st15))))
                         (st17 (simulate_a st16 nil nil nil pc0 nil pc0
                                   bpstate0 pc0 bpstate0 ffbpstate0
                                   ffpredicteddirection0
                                   ffpredictedtarget0 ffinst0 ffppc0
                                   fdbpstate0 fdppc0 fdinst0
                                   fdpredicteddirection0
                                   fdpredictedtarget0 debpstate0 deppc0
                                   desrc10 desrc20 a1 a2 dedest0 deop0
                                   deimm0 deuseimm0 deregwrite0
                                   dememwrite0 dememtoreg0 deisbranch0
                                   depredicteddirection0
                                   depredictedtarget0 embpstate0 emppc0
                                   emis_taken_branch0 emtargetpc0
                                   emarg20 emresult0 emdest0
                                   emmispredictedtaken0
                                   emmispredictednottaken0 emregwrite0
                                   emmemwrite0 emmemtoreg0 dmem0
                                   mmbpstate0 mmppc0 mmval0 mmdest0
                                   mmregwrite0 mwbpstate0 mwppc0 mwval0
                                   mwdest0 mwregwrite0
                                   (g 'prf (g 'impl st16))
                                   (g 'pdmemhist_2 (g 'impl st16))))
                         (st18 (simulate_a st17 nil nil nil pc0 nil pc0
                                   bpstate0 pc0 bpstate0 ffbpstate0
                                   ffpredicteddirection0
                                   ffpredictedtarget0 ffinst0 ffppc0
                                   fdbpstate0 fdppc0 fdinst0
                                   fdpredicteddirection0
                                   fdpredictedtarget0 debpstate0 deppc0
                                   desrc10 desrc20 a1 a2 dedest0 deop0
                                   deimm0 deuseimm0 deregwrite0
                                   dememwrite0 dememtoreg0 deisbranch0
                                   depredicteddirection0
                                   depredictedtarget0 embpstate0 emppc0
                                   emis_taken_branch0 emtargetpc0
                                   emarg20 emresult0 emdest0
                                   emmispredictedtaken0
                                   emmispredictednottaken0 emregwrite0
                                   emmemwrite0 emmemtoreg0 dmem0
                                   mmbpstate0 mmppc0 mmval0 mmdest0
                                   mmregwrite0 mwbpstate0 mwppc0 mwval0
                                   mwdest0 mwregwrite0
                                   (g 'prf (g 'impl st17))
                                   (g 'pdmemhist_2 (g 'impl st17))))
                         (st19 (simulate_a st18 nil nil nil pc0 nil pc0
                                   bpstate0 pc0 bpstate0 ffbpstate0
                                   ffpredicteddirection0
                                   ffpredictedtarget0 ffinst0 ffppc0
                                   fdbpstate0 fdppc0 fdinst0
                                   fdpredicteddirection0
                                   fdpredictedtarget0 debpstate0 deppc0
                                   desrc10 desrc20 a1 a2 dedest0 deop0
                                   deimm0 deuseimm0 deregwrite0
                                   dememwrite0 dememtoreg0 deisbranch0
                                   depredicteddirection0
                                   depredictedtarget0 embpstate0 emppc0
                                   emis_taken_branch0 emtargetpc0
                                   emarg20 emresult0 emdest0
                                   emmispredictedtaken0
                                   emmispredictednottaken0 emregwrite0
                                   emmemwrite0 emmemtoreg0 dmem0
                                   mmbpstate0 mmppc0 mmval0 mmdest0
                                   mmregwrite0 mwbpstate0 mwppc0 mwval0
                                   mwdest0 mwregwrite0
                                   (g 'prf (g 'impl st18))
                                   (g 'pdmemhist_2 (g 'impl st18))))
                         (st20 (simulate_a st19 nil nil nil pc0 nil pc0
                                   bpstate0 pc0 bpstate0 ffbpstate0
                                   ffpredicteddirection0
                                   ffpredictedtarget0 ffinst0 ffppc0
                                   fdbpstate0 fdppc0 fdinst0
                                   fdpredicteddirection0
                                   fdpredictedtarget0 debpstate0 deppc0
                                   desrc10 desrc20 a1 a2 dedest0 deop0
                                   deimm0 deuseimm0 deregwrite0
                                   dememwrite0 dememtoreg0 deisbranch0
                                   depredicteddirection0
                                   depredictedtarget0 embpstate0 emppc0
                                   emis_taken_branch0 emtargetpc0
                                   emarg20 emresult0 emdest0
                                   emmispredictedtaken0
                                   emmispredictednottaken0 emregwrite0
                                   emmemwrite0 emmemtoreg0 dmem0
                                   mmbpstate0 mmppc0 mmval0 mmdest0
                                   mmregwrite0 mwbpstate0 mwppc0 mwval0
                                   mwdest0 mwregwrite0
                                   (g 'prf (g 'impl st19))
                                   (g 'pdmemhist_2 (g 'impl st19))))
                         (st21 (simulate_a st20 nil nil nil pc0 nil pc0
                                   bpstate0 pc0 bpstate0 ffbpstate0
                                   ffpredicteddirection0
                                   ffpredictedtarget0 ffinst0 ffppc0
                                   fdbpstate0 fdppc0 fdinst0
                                   fdpredicteddirection0
                                   fdpredictedtarget0 debpstate0 deppc0
                                   desrc10 desrc20 a1 a2 dedest0 deop0
                                   deimm0 deuseimm0 deregwrite0
                                   dememwrite0 dememtoreg0 deisbranch0
                                   depredicteddirection0
                                   depredictedtarget0 embpstate0 emppc0
                                   emis_taken_branch0 emtargetpc0
                                   emarg20 emresult0 emdest0
                                   emmispredictedtaken0
                                   emmispredictednottaken0 emregwrite0
                                   emmemwrite0 emmemtoreg0 dmem0
                                   mmbpstate0 mmppc0 mmval0 mmdest0
                                   mmregwrite0 mwbpstate0 mwppc0 mwval0
                                   mwdest0 mwregwrite0
                                   (g 'prf (g 'impl st20))
                                   (g 'pdmemhist_2 (g 'impl st20))))
                         (i_pc0 (committedpc (g 'mwwrt (g 'impl st21))
                                    (g 'mwppc (g 'impl st21))
                                    (g 'mmwrt (g 'impl st21))
                                    (g 'mmppc (g 'impl st21))
                                    (g 'emwrt (g 'impl st21))
                                    (g 'emppc (g 'impl st21))
                                    (g 'dewrt (g 'impl st21))
                                    (g 'deppc (g 'impl st21))
                                    (g 'fdwrt (g 'impl st21))
                                    (g 'fdppc (g 'impl st21))
                                    (g 'ffwrt (g 'impl st21))
                                    (g 'ffppc (g 'impl st21))
                                    (g 'ppc (g 'impl st21))))
                         (i_rf0 (g 'prf (g 'impl st21)))
                         (i_dmem0 (g 'pdmemhist_2 (g 'impl st21)))
                         (rank_w (rank (g 'mwwrt (g 'impl st21)) zero
                                       (g 'mmwrt (g 'impl st21))
                                       (g 'emwrt (g 'impl st21))
                                       (g 'dewrt (g 'impl st21))
                                       (g 'fdwrt (g 'impl st21))
                                       (g 'ffwrt (g 'impl st21))))
                         (st22 (simulate_a st21 nil nil t i_pc0 nil pc0
                                   bpstate0 pc0 bpstate0 ffbpstate0
                                   ffpredicteddirection0
                                   ffpredictedtarget0 ffinst0 ffppc0
                                   fdbpstate0 fdppc0 fdinst0
                                   fdpredicteddirection0
                                   fdpredictedtarget0 debpstate0 deppc0
                                   desrc10 desrc20 a1 a2 dedest0 deop0
                                   deimm0 deuseimm0 deregwrite0
                                   dememwrite0 dememtoreg0 deisbranch0
                                   depredicteddirection0
                                   depredictedtarget0 embpstate0 emppc0
                                   emis_taken_branch0 emtargetpc0
                                   emarg20 emresult0 emdest0
                                   emmispredictedtaken0
                                   emmispredictednottaken0 emregwrite0
                                   emmemwrite0 emmemtoreg0 dmem0
                                   mmbpstate0 mmppc0 mmval0 mmdest0
                                   mmregwrite0 mwbpstate0 mwppc0 mwval0
                                   mwdest0 mwregwrite0
                                   (g 'prf (g 'impl st21))
                                   (g 'pdmemhist_2 (g 'impl st21))))
                         (s_pc0 (g 'spc (g 'spec st22)))
                         (s_rf0 (g 'srf (g 'spec st22)))
                         (s_dmem0 (g 'sdmem (g 'spec st22)))
                         (i_pc (committedpc (g 'mwwrt (g 'impl st22))
                                   (g 'mwppc (g 'impl st22))
                                   (g 'mmwrt (g 'impl st22))
                                   (g 'mmppc (g 'impl st22))
                                   (g 'emwrt (g 'impl st22))
                                   (g 'emppc (g 'impl st22))
                                   (g 'dewrt (g 'impl st22))
                                   (g 'deppc (g 'impl st22))
                                   (g 'fdwrt (g 'impl st22))
                                   (g 'fdppc (g 'impl st22))
                                   (g 'ffwrt (g 'impl st22))
                                   (g 'ffppc (g 'impl st22))
                                   (g 'ppc (g 'impl st22))))
                         (i_rf (g 'prf (g 'impl st22)))
                         (i_dmem (g 'pdmemhist_2 (g 'impl st22)))
                         (rank_v (rank (g 'mwwrt (g 'impl st22)) zero
                                       (g 'mmwrt (g 'impl st22))
                                       (g 'emwrt (g 'impl st22))
                                       (g 'dewrt (g 'impl st22))
                                       (g 'fdwrt (g 'impl st22))
                                       (g 'ffwrt (g 'impl st22))))
                         (st23 (simulate_a st22 nil t nil pc0 nil pc0
                                   bpstate0 pc0 bpstate0 ffbpstate0
                                   ffpredicteddirection0
                                   ffpredictedtarget0 ffinst0 ffppc0
                                   fdbpstate0 fdppc0 fdinst0
                                   fdpredicteddirection0
                                   fdpredictedtarget0 debpstate0 deppc0
                                   desrc10 desrc20 a1 a2 dedest0 deop0
                                   deimm0 deuseimm0 deregwrite0
                                   dememwrite0 dememtoreg0 deisbranch0
                                   depredicteddirection0
                                   depredictedtarget0 embpstate0 emppc0
                                   emis_taken_branch0 emtargetpc0
                                   emarg20 emresult0 emdest0
                                   emmispredictedtaken0
                                   emmispredictednottaken0 emregwrite0
                                   emmemwrite0 emmemtoreg0 dmem0
                                   mmbpstate0 mmppc0 mmval0 mmdest0
                                   mmregwrite0 mwbpstate0 mwppc0 mwval0
                                   mwdest0 mwregwrite0
                                   (g 'prf (g 'impl st22))
                                   (g 'pdmemhist_2 (g 'impl st22))))
                         (s_pc1 (g 'spc (g 'spec st23)))
                         (s_rf1 (g 'srf (g 'spec st23)))
                         (s_dmem1 (g 'sdmem (g 'spec st23)))
                         (st24 (simulate_a st23 t nil nil pc0 nil pc0
                                   bpstate0 pc0 bpstate0 ffbpstate0
                                   ffpredicteddirection0
                                   ffpredictedtarget0 ffinst0 ffppc0
                                   fdbpstate0 fdppc0 fdinst0
                                   fdpredicteddirection0
                                   fdpredictedtarget0 debpstate0 deppc0
                                   desrc10 desrc20 a1 a2 dedest0 deop0
                                   deimm0 deuseimm0 deregwrite0
                                   dememwrite0 dememtoreg0 deisbranch0
                                   depredicteddirection0
                                   depredictedtarget0 embpstate0 emppc0
                                   emis_taken_branch0 emtargetpc0
                                   emarg20 emresult0 emdest0
                                   emmispredictedtaken0
                                   emmispredictednottaken0 emregwrite0
                                   emmemwrite0 emmemtoreg0 dmem0
                                   mmbpstate0 mmppc0 mmval0 mmdest0
                                   mmregwrite0 mwbpstate0 mwppc0 mwval0
                                   mwdest0 mwregwrite0
                                   (g 'prf (g 'impl st23))
                                   (g 'pdmemhist_2 (g 'impl st23))))
                         (st25 (simulate_a st24 nil nil nil pc0 nil pc0
                                   bpstate0 pc0 bpstate0 ffbpstate0
                                   ffpredicteddirection0
                                   ffpredictedtarget0 ffinst0 ffppc0
                                   fdbpstate0 fdppc0 fdinst0
                                   fdpredicteddirection0
                                   fdpredictedtarget0 debpstate0 deppc0
                                   desrc10 desrc20 a1 a2 dedest0 deop0
                                   deimm0 deuseimm0 deregwrite0
                                   dememwrite0 dememtoreg0 deisbranch0
                                   depredicteddirection0
                                   depredictedtarget0 embpstate0 emppc0
                                   emis_taken_branch0 emtargetpc0
                                   emarg20 emresult0 emdest0
                                   emmispredictedtaken0
                                   emmispredictednottaken0 emregwrite0
                                   emmemwrite0 emmemtoreg0 dmem0
                                   mmbpstate0 mmppc0 mmval0 mmdest0
                                   mmregwrite0 mwbpstate0 mwppc0 mwval0
                                   mwdest0 mwregwrite0
                                   (g 'prf (g 'impl st24))
                                   (g 'pdmemhist_2 (g 'impl st24))))
                         (st26 (simulate_a st25 nil nil nil pc0 nil pc0
                                   bpstate0 pc0 bpstate0 ffbpstate0
                                   ffpredicteddirection0
                                   ffpredictedtarget0 ffinst0 ffppc0
                                   fdbpstate0 fdppc0 fdinst0
                                   fdpredicteddirection0
                                   fdpredictedtarget0 debpstate0 deppc0
                                   desrc10 desrc20 a1 a2 dedest0 deop0
                                   deimm0 deuseimm0 deregwrite0
                                   dememwrite0 dememtoreg0 deisbranch0
                                   depredicteddirection0
                                   depredictedtarget0 embpstate0 emppc0
                                   emis_taken_branch0 emtargetpc0
                                   emarg20 emresult0 emdest0
                                   emmispredictedtaken0
                                   emmispredictednottaken0 emregwrite0
                                   emmemwrite0 emmemtoreg0 dmem0
                                   mmbpstate0 mmppc0 mmval0 mmdest0
                                   mmregwrite0 mwbpstate0 mwppc0 mwval0
                                   mwdest0 mwregwrite0
                                   (g 'prf (g 'impl st25))
                                   (g 'pdmemhist_2 (g 'impl st25))))
                         (st27 (simulate_a st26 nil nil nil pc0 nil pc0
                                   bpstate0 pc0 bpstate0 ffbpstate0
                                   ffpredicteddirection0
                                   ffpredictedtarget0 ffinst0 ffppc0
                                   fdbpstate0 fdppc0 fdinst0
                                   fdpredicteddirection0
                                   fdpredictedtarget0 debpstate0 deppc0
                                   desrc10 desrc20 a1 a2 dedest0 deop0
                                   deimm0 deuseimm0 deregwrite0
                                   dememwrite0 dememtoreg0 deisbranch0
                                   depredicteddirection0
                                   depredictedtarget0 embpstate0 emppc0
                                   emis_taken_branch0 emtargetpc0
                                   emarg20 emresult0 emdest0
                                   emmispredictedtaken0
                                   emmispredictednottaken0 emregwrite0
                                   emmemwrite0 emmemtoreg0 dmem0
                                   mmbpstate0 mmppc0 mmval0 mmdest0
                                   mmregwrite0 mwbpstate0 mwppc0 mwval0
                                   mwdest0 mwregwrite0
                                   (g 'prf (g 'impl st26))
                                   (g 'pdmemhist_2 (g 'impl st26))))
                         (st28 (simulate_a st27 nil nil nil pc0 nil pc0
                                   bpstate0 pc0 bpstate0 ffbpstate0
                                   ffpredicteddirection0
                                   ffpredictedtarget0 ffinst0 ffppc0
                                   fdbpstate0 fdppc0 fdinst0
                                   fdpredicteddirection0
                                   fdpredictedtarget0 debpstate0 deppc0
                                   desrc10 desrc20 a1 a2 dedest0 deop0
                                   deimm0 deuseimm0 deregwrite0
                                   dememwrite0 dememtoreg0 deisbranch0
                                   depredicteddirection0
                                   depredictedtarget0 embpstate0 emppc0
                                   emis_taken_branch0 emtargetpc0
                                   emarg20 emresult0 emdest0
                                   emmispredictedtaken0
                                   emmispredictednottaken0 emregwrite0
                                   emmemwrite0 emmemtoreg0 dmem0
                                   mmbpstate0 mmppc0 mmval0 mmdest0
                                   mmregwrite0 mwbpstate0 mwppc0 mwval0
                                   mwdest0 mwregwrite0
                                   (g 'prf (g 'impl st27))
                                   (g 'pdmemhist_2 (g 'impl st27))))
                         (st29 (simulate_a st28 nil nil nil pc0 nil pc0
                                   bpstate0 pc0 bpstate0 ffbpstate0
                                   ffpredicteddirection0
                                   ffpredictedtarget0 ffinst0 ffppc0
                                   fdbpstate0 fdppc0 fdinst0
                                   fdpredicteddirection0
                                   fdpredictedtarget0 debpstate0 deppc0
                                   desrc10 desrc20 a1 a2 dedest0 deop0
                                   deimm0 deuseimm0 deregwrite0
                                   dememwrite0 dememtoreg0 deisbranch0
                                   depredicteddirection0
                                   depredictedtarget0 embpstate0 emppc0
                                   emis_taken_branch0 emtargetpc0
                                   emarg20 emresult0 emdest0
                                   emmispredictedtaken0
                                   emmispredictednottaken0 emregwrite0
                                   emmemwrite0 emmemtoreg0 dmem0
                                   mmbpstate0 mmppc0 mmval0 mmdest0
                                   mmregwrite0 mwbpstate0 mwppc0 mwval0
                                   mwdest0 mwregwrite0
                                   (g 'prf (g 'impl st28))
                                   (g 'pdmemhist_2 (g 'impl st28))))
                         (i_pc0_2 (committedpc
                                      (g 'mwwrt (g 'impl st29))
                                      (g 'mwppc (g 'impl st29))
                                      (g 'mmwrt (g 'impl st29))
                                      (g 'mmppc (g 'impl st29))
                                      (g 'emwrt (g 'impl st29))
                                      (g 'emppc (g 'impl st29))
                                      (g 'dewrt (g 'impl st29))
                                      (g 'deppc (g 'impl st29))
                                      (g 'fdwrt (g 'impl st29))
                                      (g 'fdppc (g 'impl st29))
                                      (g 'ffwrt (g 'impl st29))
                                      (g 'ffppc (g 'impl st29))
                                      (g 'ppc (g 'impl st29))))
                         (i_rf0_2 (g 'prf (g 'impl st29)))
                         (i_dmem0_2 (g 'pdmemhist_2 (g 'impl st29)))
                         (rank_w_2
                             (rank (g 'mwwrt (g 'impl st29)) zero
                                   (g 'mmwrt (g 'impl st29))
                                   (g 'emwrt (g 'impl st29))
                                   (g 'dewrt (g 'impl st29))
                                   (g 'fdwrt (g 'impl st29))
                                   (g 'ffwrt (g 'impl st29))))
                         (st30 (simulate_a st29 nil nil t i_pc0_2 nil
                                   pc0 bpstate0 pc0 bpstate0 ffbpstate0
                                   ffpredicteddirection0
                                   ffpredictedtarget0 ffinst0 ffppc0
                                   fdbpstate0 fdppc0 fdinst0
                                   fdpredicteddirection0
                                   fdpredictedtarget0 debpstate0 deppc0
                                   desrc10 desrc20 a1 a2 dedest0 deop0
                                   deimm0 deuseimm0 deregwrite0
                                   dememwrite0 dememtoreg0 deisbranch0
                                   depredicteddirection0
                                   depredictedtarget0 embpstate0 emppc0
                                   emis_taken_branch0 emtargetpc0
                                   emarg20 emresult0 emdest0
                                   emmispredictedtaken0
                                   emmispredictednottaken0 emregwrite0
                                   emmemwrite0 emmemtoreg0 dmem0
                                   mmbpstate0 mmppc0 mmval0 mmdest0
                                   mmregwrite0 mwbpstate0 mwppc0 mwval0
                                   mwdest0 mwregwrite0
                                   (g 'prf (g 'impl st29))
                                   (g 'pdmemhist_2 (g 'impl st29))))
                         (s_pc0_2 (g 'spc (g 'spec st30)))
                         (s_rf0_2 (g 'srf (g 'spec st30)))
                         (s_dmem0_2 (g 'sdmem (g 'spec st30)))
                         (i_pc_2 (committedpc (g 'mwwrt (g 'impl st30))
                                     (g 'mwppc (g 'impl st30))
                                     (g 'mmwrt (g 'impl st30))
                                     (g 'mmppc (g 'impl st30))
                                     (g 'emwrt (g 'impl st30))
                                     (g 'emppc (g 'impl st30))
                                     (g 'dewrt (g 'impl st30))
                                     (g 'deppc (g 'impl st30))
                                     (g 'fdwrt (g 'impl st30))
                                     (g 'fdppc (g 'impl st30))
                                     (g 'ffwrt (g 'impl st30))
                                     (g 'ffppc (g 'impl st30))
                                     (g 'ppc (g 'impl st30))))
                         (i_rf_2 (g 'prf (g 'impl st30)))
                         (i_dmem_2 (g 'pdmemhist_2 (g 'impl st30)))
                         (rank_v_2
                             (rank (g 'mwwrt (g 'impl st30)) zero
                                   (g 'mmwrt (g 'impl st30))
                                   (g 'emwrt (g 'impl st30))
                                   (g 'dewrt (g 'impl st30))
                                   (g 'fdwrt (g 'impl st30))
                                   (g 'ffwrt (g 'impl st30))))
                         (st31 (simulate_a st30 nil t nil pc0 nil pc0
                                   bpstate0 pc0 bpstate0 ffbpstate0
                                   ffpredicteddirection0
                                   ffpredictedtarget0 ffinst0 ffppc0
                                   fdbpstate0 fdppc0 fdinst0
                                   fdpredicteddirection0
                                   fdpredictedtarget0 debpstate0 deppc0
                                   desrc10 desrc20 a1 a2 dedest0 deop0
                                   deimm0 deuseimm0 deregwrite0
                                   dememwrite0 dememtoreg0 deisbranch0
                                   depredicteddirection0
                                   depredictedtarget0 embpstate0 emppc0
                                   emis_taken_branch0 emtargetpc0
                                   emarg20 emresult0 emdest0
                                   emmispredictedtaken0
                                   emmispredictednottaken0 emregwrite0
                                   emmemwrite0 emmemtoreg0 dmem0
                                   mmbpstate0 mmppc0 mmval0 mmdest0
                                   mmregwrite0 mwbpstate0 mwppc0 mwval0
                                   mwdest0 mwregwrite0
                                   (g 'prf (g 'impl st30))
                                   (g 'pdmemhist_2 (g 'impl st30))))
                         (s_pc1_2 (g 'spc (g 'spec st31)))
                         (s_rf1_2 (g 'srf (g 'spec st31)))
                         (s_dmem1_2 (g 'sdmem (g 'spec st31)))
                         (st32 (simulate_a st31 t nil nil pc0 nil pc0
                                   bpstate0 pc0 bpstate0 ffbpstate0
                                   ffpredicteddirection0
                                   ffpredictedtarget0 ffinst0 ffppc0
                                   fdbpstate0 fdppc0 fdinst0
                                   fdpredicteddirection0
                                   fdpredictedtarget0 debpstate0 deppc0
                                   desrc10 desrc20 a1 a2 dedest0 deop0
                                   deimm0 deuseimm0 deregwrite0
                                   dememwrite0 dememtoreg0 deisbranch0
                                   depredicteddirection0
                                   depredictedtarget0 embpstate0 emppc0
                                   emis_taken_branch0 emtargetpc0
                                   emarg20 emresult0 emdest0
                                   emmispredictedtaken0
                                   emmispredictednottaken0 emregwrite0
                                   emmemwrite0 emmemtoreg0 dmem0
                                   mmbpstate0 mmppc0 mmval0 mmdest0
                                   mmregwrite0 mwbpstate0 mwppc0 mwval0
                                   mwdest0 mwregwrite0
                                   (g 'prf (g 'impl st31))
                                   (g 'pdmemhist_2 (g 'impl st31))))
                         (st33 (simulate_a st32 nil nil nil pc0 nil pc0
                                   bpstate0 pc0 bpstate0 ffbpstate0
                                   ffpredicteddirection0
                                   ffpredictedtarget0 ffinst0 ffppc0
                                   fdbpstate0 fdppc0 fdinst0
                                   fdpredicteddirection0
                                   fdpredictedtarget0 debpstate0 deppc0
                                   desrc10 desrc20 a1 a2 dedest0 deop0
                                   deimm0 deuseimm0 deregwrite0
                                   dememwrite0 dememtoreg0 deisbranch0
                                   depredicteddirection0
                                   depredictedtarget0 embpstate0 emppc0
                                   emis_taken_branch0 emtargetpc0
                                   emarg20 emresult0 emdest0
                                   emmispredictedtaken0
                                   emmispredictednottaken0 emregwrite0
                                   emmemwrite0 emmemtoreg0 dmem0
                                   mmbpstate0 mmppc0 mmval0 mmdest0
                                   mmregwrite0 mwbpstate0 mwppc0 mwval0
                                   mwdest0 mwregwrite0
                                   (g 'prf (g 'impl st32))
                                   (g 'pdmemhist_2 (g 'impl st32))))
                         (st34 (simulate_a st33 nil nil nil pc0 nil pc0
                                   bpstate0 pc0 bpstate0 ffbpstate0
                                   ffpredicteddirection0
                                   ffpredictedtarget0 ffinst0 ffppc0
                                   fdbpstate0 fdppc0 fdinst0
                                   fdpredicteddirection0
                                   fdpredictedtarget0 debpstate0 deppc0
                                   desrc10 desrc20 a1 a2 dedest0 deop0
                                   deimm0 deuseimm0 deregwrite0
                                   dememwrite0 dememtoreg0 deisbranch0
                                   depredicteddirection0
                                   depredictedtarget0 embpstate0 emppc0
                                   emis_taken_branch0 emtargetpc0
                                   emarg20 emresult0 emdest0
                                   emmispredictedtaken0
                                   emmispredictednottaken0 emregwrite0
                                   emmemwrite0 emmemtoreg0 dmem0
                                   mmbpstate0 mmppc0 mmval0 mmdest0
                                   mmregwrite0 mwbpstate0 mwppc0 mwval0
                                   mwdest0 mwregwrite0
                                   (g 'prf (g 'impl st33))
                                   (g 'pdmemhist_2 (g 'impl st33))))
                         (st35 (simulate_a st34 nil nil nil pc0 nil pc0
                                   bpstate0 pc0 bpstate0 ffbpstate0
                                   ffpredicteddirection0
                                   ffpredictedtarget0 ffinst0 ffppc0
                                   fdbpstate0 fdppc0 fdinst0
                                   fdpredicteddirection0
                                   fdpredictedtarget0 debpstate0 deppc0
                                   desrc10 desrc20 a1 a2 dedest0 deop0
                                   deimm0 deuseimm0 deregwrite0
                                   dememwrite0 dememtoreg0 deisbranch0
                                   depredicteddirection0
                                   depredictedtarget0 embpstate0 emppc0
                                   emis_taken_branch0 emtargetpc0
                                   emarg20 emresult0 emdest0
                                   emmispredictedtaken0
                                   emmispredictednottaken0 emregwrite0
                                   emmemwrite0 emmemtoreg0 dmem0
                                   mmbpstate0 mmppc0 mmval0 mmdest0
                                   mmregwrite0 mwbpstate0 mwppc0 mwval0
                                   mwdest0 mwregwrite0
                                   (g 'prf (g 'impl st34))
                                   (g 'pdmemhist_2 (g 'impl st34))))
                         (st36 (simulate_a st35 nil nil nil pc0 nil pc0
                                   bpstate0 pc0 bpstate0 ffbpstate0
                                   ffpredicteddirection0
                                   ffpredictedtarget0 ffinst0 ffppc0
                                   fdbpstate0 fdppc0 fdinst0
                                   fdpredicteddirection0
                                   fdpredictedtarget0 debpstate0 deppc0
                                   desrc10 desrc20 a1 a2 dedest0 deop0
                                   deimm0 deuseimm0 deregwrite0
                                   dememwrite0 dememtoreg0 deisbranch0
                                   depredicteddirection0
                                   depredictedtarget0 embpstate0 emppc0
                                   emis_taken_branch0 emtargetpc0
                                   emarg20 emresult0 emdest0
                                   emmispredictedtaken0
                                   emmispredictednottaken0 emregwrite0
                                   emmemwrite0 emmemtoreg0 dmem0
                                   mmbpstate0 mmppc0 mmval0 mmdest0
                                   mmregwrite0 mwbpstate0 mwppc0 mwval0
                                   mwdest0 mwregwrite0
                                   (g 'prf (g 'impl st35))
                                   (g 'pdmemhist_2 (g 'impl st35))))
                         (i_pc0_3 (committedpc
                                      (g 'mwwrt (g 'impl st36))
                                      (g 'mwppc (g 'impl st36))
                                      (g 'mmwrt (g 'impl st36))
                                      (g 'mmppc (g 'impl st36))
                                      (g 'emwrt (g 'impl st36))
                                      (g 'emppc (g 'impl st36))
                                      (g 'dewrt (g 'impl st36))
                                      (g 'deppc (g 'impl st36))
                                      (g 'fdwrt (g 'impl st36))
                                      (g 'fdppc (g 'impl st36))
                                      (g 'ffwrt (g 'impl st36))
                                      (g 'ffppc (g 'impl st36))
                                      (g 'ppc (g 'impl st36))))
                         (i_rf0_3 (g 'prf (g 'impl st36)))
                         (i_dmem0_3 (g 'pdmemhist_2 (g 'impl st36)))
                         (rank_w_3
                             (rank (g 'mwwrt (g 'impl st36)) zero
                                   (g 'mmwrt (g 'impl st36))
                                   (g 'emwrt (g 'impl st36))
                                   (g 'dewrt (g 'impl st36))
                                   (g 'fdwrt (g 'impl st36))
                                   (g 'ffwrt (g 'impl st36))))
                         (st37 (simulate_a st36 nil nil t i_pc0_3 nil
                                   pc0 bpstate0 pc0 bpstate0 ffbpstate0
                                   ffpredicteddirection0
                                   ffpredictedtarget0 ffinst0 ffppc0
                                   fdbpstate0 fdppc0 fdinst0
                                   fdpredicteddirection0
                                   fdpredictedtarget0 debpstate0 deppc0
                                   desrc10 desrc20 a1 a2 dedest0 deop0
                                   deimm0 deuseimm0 deregwrite0
                                   dememwrite0 dememtoreg0 deisbranch0
                                   depredicteddirection0
                                   depredictedtarget0 embpstate0 emppc0
                                   emis_taken_branch0 emtargetpc0
                                   emarg20 emresult0 emdest0
                                   emmispredictedtaken0
                                   emmispredictednottaken0 emregwrite0
                                   emmemwrite0 emmemtoreg0 dmem0
                                   mmbpstate0 mmppc0 mmval0 mmdest0
                                   mmregwrite0 mwbpstate0 mwppc0 mwval0
                                   mwdest0 mwregwrite0
                                   (g 'prf (g 'impl st36))
                                   (g 'pdmemhist_2 (g 'impl st36))))
                         (s_pc0_3 (g 'spc (g 'spec st37)))
                         (s_rf0_3 (g 'srf (g 'spec st37)))
                         (s_dmem0_3 (g 'sdmem (g 'spec st37)))
                         (i_pc_3 (committedpc (g 'mwwrt (g 'impl st37))
                                     (g 'mwppc (g 'impl st37))
                                     (g 'mmwrt (g 'impl st37))
                                     (g 'mmppc (g 'impl st37))
                                     (g 'emwrt (g 'impl st37))
                                     (g 'emppc (g 'impl st37))
                                     (g 'dewrt (g 'impl st37))
                                     (g 'deppc (g 'impl st37))
                                     (g 'fdwrt (g 'impl st37))
                                     (g 'fdppc (g 'impl st37))
                                     (g 'ffwrt (g 'impl st37))
                                     (g 'ffppc (g 'impl st37))
                                     (g 'ppc (g 'impl st37))))
                         (i_rf_3 (g 'prf (g 'impl st37)))
                         (i_dmem_3 (g 'pdmemhist_2 (g 'impl st37)))
                         (rank_v_3
                             (rank (g 'mwwrt (g 'impl st37)) zero
                                   (g 'mmwrt (g 'impl st37))
                                   (g 'emwrt (g 'impl st37))
                                   (g 'dewrt (g 'impl st37))
                                   (g 'fdwrt (g 'impl st37))
                                   (g 'ffwrt (g 'impl st37))))
                         (st38 (simulate_a st37 nil t nil pc0 nil pc0
                                   bpstate0 pc0 bpstate0 ffbpstate0
                                   ffpredicteddirection0
                                   ffpredictedtarget0 ffinst0 ffppc0
                                   fdbpstate0 fdppc0 fdinst0
                                   fdpredicteddirection0
                                   fdpredictedtarget0 debpstate0 deppc0
                                   desrc10 desrc20 a1 a2 dedest0 deop0
                                   deimm0 deuseimm0 deregwrite0
                                   dememwrite0 dememtoreg0 deisbranch0
                                   depredicteddirection0
                                   depredictedtarget0 embpstate0 emppc0
                                   emis_taken_branch0 emtargetpc0
                                   emarg20 emresult0 emdest0
                                   emmispredictedtaken0
                                   emmispredictednottaken0 emregwrite0
                                   emmemwrite0 emmemtoreg0 dmem0
                                   mmbpstate0 mmppc0 mmval0 mmdest0
                                   mmregwrite0 mwbpstate0 mwppc0 mwval0
                                   mwdest0 mwregwrite0
                                   (g 'prf (g 'impl st37))
                                   (g 'pdmemhist_2 (g 'impl st37))))
                         (s_pc1_3 (g 'spc (g 'spec st38)))
                         (s_rf1_3 (g 'srf (g 'spec st38)))
                         (s_dmem1_3 (g 'sdmem (g 'spec st38)))
                         (st39 (simulate_a st38 t nil nil pc0 nil pc0
                                   bpstate0 pc0 bpstate0 ffbpstate0
                                   ffpredicteddirection0
                                   ffpredictedtarget0 ffinst0 ffppc0
                                   fdbpstate0 fdppc0 fdinst0
                                   fdpredicteddirection0
                                   fdpredictedtarget0 debpstate0 deppc0
                                   desrc10 desrc20 a1 a2 dedest0 deop0
                                   deimm0 deuseimm0 deregwrite0
                                   dememwrite0 dememtoreg0 deisbranch0
                                   depredicteddirection0
                                   depredictedtarget0 embpstate0 emppc0
                                   emis_taken_branch0 emtargetpc0
                                   emarg20 emresult0 emdest0
                                   emmispredictedtaken0
                                   emmispredictednottaken0 emregwrite0
                                   emmemwrite0 emmemtoreg0 dmem0
                                   mmbpstate0 mmppc0 mmval0 mmdest0
                                   mmregwrite0 mwbpstate0 mwppc0 mwval0
                                   mwdest0 mwregwrite0
                                   (g 'prf (g 'impl st38))
                                   (g 'pdmemhist_2 (g 'impl st38))))
                         (st40 (simulate_a st39 nil nil nil pc0 nil pc0
                                   bpstate0 pc0 bpstate0 ffbpstate0
                                   ffpredicteddirection0
                                   ffpredictedtarget0 ffinst0 ffppc0
                                   fdbpstate0 fdppc0 fdinst0
                                   fdpredicteddirection0
                                   fdpredictedtarget0 debpstate0 deppc0
                                   desrc10 desrc20 a1 a2 dedest0 deop0
                                   deimm0 deuseimm0 deregwrite0
                                   dememwrite0 dememtoreg0 deisbranch0
                                   depredicteddirection0
                                   depredictedtarget0 embpstate0 emppc0
                                   emis_taken_branch0 emtargetpc0
                                   emarg20 emresult0 emdest0
                                   emmispredictedtaken0
                                   emmispredictednottaken0 emregwrite0
                                   emmemwrite0 emmemtoreg0 dmem0
                                   mmbpstate0 mmppc0 mmval0 mmdest0
                                   mmregwrite0 mwbpstate0 mwppc0 mwval0
                                   mwdest0 mwregwrite0
                                   (g 'prf (g 'impl st39))
                                   (g 'pdmemhist_2 (g 'impl st39))))
                         (st41 (simulate_a st40 nil nil nil pc0 nil pc0
                                   bpstate0 pc0 bpstate0 ffbpstate0
                                   ffpredicteddirection0
                                   ffpredictedtarget0 ffinst0 ffppc0
                                   fdbpstate0 fdppc0 fdinst0
                                   fdpredicteddirection0
                                   fdpredictedtarget0 debpstate0 deppc0
                                   desrc10 desrc20 a1 a2 dedest0 deop0
                                   deimm0 deuseimm0 deregwrite0
                                   dememwrite0 dememtoreg0 deisbranch0
                                   depredicteddirection0
                                   depredictedtarget0 embpstate0 emppc0
                                   emis_taken_branch0 emtargetpc0
                                   emarg20 emresult0 emdest0
                                   emmispredictedtaken0
                                   emmispredictednottaken0 emregwrite0
                                   emmemwrite0 emmemtoreg0 dmem0
                                   mmbpstate0 mmppc0 mmval0 mmdest0
                                   mmregwrite0 mwbpstate0 mwppc0 mwval0
                                   mwdest0 mwregwrite0
                                   (g 'prf (g 'impl st40))
                                   (g 'pdmemhist_2 (g 'impl st40))))
                         (st42 (simulate_a st41 nil nil nil pc0 nil pc0
                                   bpstate0 pc0 bpstate0 ffbpstate0
                                   ffpredicteddirection0
                                   ffpredictedtarget0 ffinst0 ffppc0
                                   fdbpstate0 fdppc0 fdinst0
                                   fdpredicteddirection0
                                   fdpredictedtarget0 debpstate0 deppc0
                                   desrc10 desrc20 a1 a2 dedest0 deop0
                                   deimm0 deuseimm0 deregwrite0
                                   dememwrite0 dememtoreg0 deisbranch0
                                   depredicteddirection0
                                   depredictedtarget0 embpstate0 emppc0
                                   emis_taken_branch0 emtargetpc0
                                   emarg20 emresult0 emdest0
                                   emmispredictedtaken0
                                   emmispredictednottaken0 emregwrite0
                                   emmemwrite0 emmemtoreg0 dmem0
                                   mmbpstate0 mmppc0 mmval0 mmdest0
                                   mmregwrite0 mwbpstate0 mwppc0 mwval0
                                   mwdest0 mwregwrite0
                                   (g 'prf (g 'impl st41))
                                   (g 'pdmemhist_2 (g 'impl st41))))
                         (i_pc0_4 (committedpc
                                      (g 'mwwrt (g 'impl st42))
                                      (g 'mwppc (g 'impl st42))
                                      (g 'mmwrt (g 'impl st42))
                                      (g 'mmppc (g 'impl st42))
                                      (g 'emwrt (g 'impl st42))
                                      (g 'emppc (g 'impl st42))
                                      (g 'dewrt (g 'impl st42))
                                      (g 'deppc (g 'impl st42))
                                      (g 'fdwrt (g 'impl st42))
                                      (g 'fdppc (g 'impl st42))
                                      (g 'ffwrt (g 'impl st42))
                                      (g 'ffppc (g 'impl st42))
                                      (g 'ppc (g 'impl st42))))
                         (i_rf0_4 (g 'prf (g 'impl st42)))
                         (i_dmem0_4 (g 'pdmemhist_2 (g 'impl st42)))
                         (rank_w_4
                             (rank (g 'mwwrt (g 'impl st42)) zero
                                   (g 'mmwrt (g 'impl st42))
                                   (g 'emwrt (g 'impl st42))
                                   (g 'dewrt (g 'impl st42))
                                   (g 'fdwrt (g 'impl st42))
                                   (g 'ffwrt (g 'impl st42))))
                         (st43 (simulate_a st42 nil nil t i_pc0_4 nil
                                   pc0 bpstate0 pc0 bpstate0 ffbpstate0
                                   ffpredicteddirection0
                                   ffpredictedtarget0 ffinst0 ffppc0
                                   fdbpstate0 fdppc0 fdinst0
                                   fdpredicteddirection0
                                   fdpredictedtarget0 debpstate0 deppc0
                                   desrc10 desrc20 a1 a2 dedest0 deop0
                                   deimm0 deuseimm0 deregwrite0
                                   dememwrite0 dememtoreg0 deisbranch0
                                   depredicteddirection0
                                   depredictedtarget0 embpstate0 emppc0
                                   emis_taken_branch0 emtargetpc0
                                   emarg20 emresult0 emdest0
                                   emmispredictedtaken0
                                   emmispredictednottaken0 emregwrite0
                                   emmemwrite0 emmemtoreg0 dmem0
                                   mmbpstate0 mmppc0 mmval0 mmdest0
                                   mmregwrite0 mwbpstate0 mwppc0 mwval0
                                   mwdest0 mwregwrite0
                                   (g 'prf (g 'impl st42))
                                   (g 'pdmemhist_2 (g 'impl st42))))
                         (s_pc0_4 (g 'spc (g 'spec st43)))
                         (s_rf0_4 (g 'srf (g 'spec st43)))
                         (s_dmem0_4 (g 'sdmem (g 'spec st43)))
                         (i_pc_4 (committedpc (g 'mwwrt (g 'impl st43))
                                     (g 'mwppc (g 'impl st43))
                                     (g 'mmwrt (g 'impl st43))
                                     (g 'mmppc (g 'impl st43))
                                     (g 'emwrt (g 'impl st43))
                                     (g 'emppc (g 'impl st43))
                                     (g 'dewrt (g 'impl st43))
                                     (g 'deppc (g 'impl st43))
                                     (g 'fdwrt (g 'impl st43))
                                     (g 'fdppc (g 'impl st43))
                                     (g 'ffwrt (g 'impl st43))
                                     (g 'ffppc (g 'impl st43))
                                     (g 'ppc (g 'impl st43))))
                         (i_rf_4 (g 'prf (g 'impl st43)))
                         (i_dmem_4 (g 'pdmemhist_2 (g 'impl st43)))
                         (rank_v_4
                             (rank (g 'mwwrt (g 'impl st43)) zero
                                   (g 'mmwrt (g 'impl st43))
                                   (g 'emwrt (g 'impl st43))
                                   (g 'dewrt (g 'impl st43))
                                   (g 'fdwrt (g 'impl st43))
                                   (g 'ffwrt (g 'impl st43))))
                         (st44 (simulate_a st43 nil t nil pc0 nil pc0
                                   bpstate0 pc0 bpstate0 ffbpstate0
                                   ffpredicteddirection0
                                   ffpredictedtarget0 ffinst0 ffppc0
                                   fdbpstate0 fdppc0 fdinst0
                                   fdpredicteddirection0
                                   fdpredictedtarget0 debpstate0 deppc0
                                   desrc10 desrc20 a1 a2 dedest0 deop0
                                   deimm0 deuseimm0 deregwrite0
                                   dememwrite0 dememtoreg0 deisbranch0
                                   depredicteddirection0
                                   depredictedtarget0 embpstate0 emppc0
                                   emis_taken_branch0 emtargetpc0
                                   emarg20 emresult0 emdest0
                                   emmispredictedtaken0
                                   emmispredictednottaken0 emregwrite0
                                   emmemwrite0 emmemtoreg0 dmem0
                                   mmbpstate0 mmppc0 mmval0 mmdest0
                                   mmregwrite0 mwbpstate0 mwppc0 mwval0
                                   mwdest0 mwregwrite0
                                   (g 'prf (g 'impl st43))
                                   (g 'pdmemhist_2 (g 'impl st43))))
                         (s_pc1_4 (g 'spc (g 'spec st44)))
                         (s_rf1_4 (g 'srf (g 'spec st44)))
                         (s_dmem1_4 (g 'sdmem (g 'spec st44)))
                         (st45 (simulate_a st44 t nil nil pc0 nil pc0
                                   bpstate0 pc0 bpstate0 ffbpstate0
                                   ffpredicteddirection0
                                   ffpredictedtarget0 ffinst0 ffppc0
                                   fdbpstate0 fdppc0 fdinst0
                                   fdpredicteddirection0
                                   fdpredictedtarget0 debpstate0 deppc0
                                   desrc10 desrc20 a1 a2 dedest0 deop0
                                   deimm0 deuseimm0 deregwrite0
                                   dememwrite0 dememtoreg0 deisbranch0
                                   depredicteddirection0
                                   depredictedtarget0 embpstate0 emppc0
                                   emis_taken_branch0 emtargetpc0
                                   emarg20 emresult0 emdest0
                                   emmispredictedtaken0
                                   emmispredictednottaken0 emregwrite0
                                   emmemwrite0 emmemtoreg0 dmem0
                                   mmbpstate0 mmppc0 mmval0 mmdest0
                                   mmregwrite0 mwbpstate0 mwppc0 mwval0
                                   mwdest0 mwregwrite0
                                   (g 'prf (g 'impl st44))
                                   (g 'pdmemhist_2 (g 'impl st44))))
                         (st46 (simulate_a st45 nil nil nil pc0 nil pc0
                                   bpstate0 pc0 bpstate0 ffbpstate0
                                   ffpredicteddirection0
                                   ffpredictedtarget0 ffinst0 ffppc0
                                   fdbpstate0 fdppc0 fdinst0
                                   fdpredicteddirection0
                                   fdpredictedtarget0 debpstate0 deppc0
                                   desrc10 desrc20 a1 a2 dedest0 deop0
                                   deimm0 deuseimm0 deregwrite0
                                   dememwrite0 dememtoreg0 deisbranch0
                                   depredicteddirection0
                                   depredictedtarget0 embpstate0 emppc0
                                   emis_taken_branch0 emtargetpc0
                                   emarg20 emresult0 emdest0
                                   emmispredictedtaken0
                                   emmispredictednottaken0 emregwrite0
                                   emmemwrite0 emmemtoreg0 dmem0
                                   mmbpstate0 mmppc0 mmval0 mmdest0
                                   mmregwrite0 mwbpstate0 mwppc0 mwval0
                                   mwdest0 mwregwrite0
                                   (g 'prf (g 'impl st45))
                                   (g 'pdmemhist_2 (g 'impl st45))))
                         (st47 (simulate_a st46 nil nil nil pc0 nil pc0
                                   bpstate0 pc0 bpstate0 ffbpstate0
                                   ffpredicteddirection0
                                   ffpredictedtarget0 ffinst0 ffppc0
                                   fdbpstate0 fdppc0 fdinst0
                                   fdpredicteddirection0
                                   fdpredictedtarget0 debpstate0 deppc0
                                   desrc10 desrc20 a1 a2 dedest0 deop0
                                   deimm0 deuseimm0 deregwrite0
                                   dememwrite0 dememtoreg0 deisbranch0
                                   depredicteddirection0
                                   depredictedtarget0 embpstate0 emppc0
                                   emis_taken_branch0 emtargetpc0
                                   emarg20 emresult0 emdest0
                                   emmispredictedtaken0
                                   emmispredictednottaken0 emregwrite0
                                   emmemwrite0 emmemtoreg0 dmem0
                                   mmbpstate0 mmppc0 mmval0 mmdest0
                                   mmregwrite0 mwbpstate0 mwppc0 mwval0
                                   mwdest0 mwregwrite0
                                   (g 'prf (g 'impl st46))
                                   (g 'pdmemhist_2 (g 'impl st46))))
                         (i_pc0_5 (committedpc
                                      (g 'mwwrt (g 'impl st47))
                                      (g 'mwppc (g 'impl st47))
                                      (g 'mmwrt (g 'impl st47))
                                      (g 'mmppc (g 'impl st47))
                                      (g 'emwrt (g 'impl st47))
                                      (g 'emppc (g 'impl st47))
                                      (g 'dewrt (g 'impl st47))
                                      (g 'deppc (g 'impl st47))
                                      (g 'fdwrt (g 'impl st47))
                                      (g 'fdppc (g 'impl st47))
                                      (g 'ffwrt (g 'impl st47))
                                      (g 'ffppc (g 'impl st47))
                                      (g 'ppc (g 'impl st47))))
                         (i_rf0_5 (g 'prf (g 'impl st47)))
                         (i_dmem0_5 (g 'pdmemhist_2 (g 'impl st47)))
                         (rank_w_5
                             (rank (g 'mwwrt (g 'impl st47)) zero
                                   (g 'mmwrt (g 'impl st47))
                                   (g 'emwrt (g 'impl st47))
                                   (g 'dewrt (g 'impl st47))
                                   (g 'fdwrt (g 'impl st47))
                                   (g 'ffwrt (g 'impl st47))))
                         (st48 (simulate_a st47 nil nil t i_pc0_5 nil
                                   pc0 bpstate0 pc0 bpstate0 ffbpstate0
                                   ffpredicteddirection0
                                   ffpredictedtarget0 ffinst0 ffppc0
                                   fdbpstate0 fdppc0 fdinst0
                                   fdpredicteddirection0
                                   fdpredictedtarget0 debpstate0 deppc0
                                   desrc10 desrc20 a1 a2 dedest0 deop0
                                   deimm0 deuseimm0 deregwrite0
                                   dememwrite0 dememtoreg0 deisbranch0
                                   depredicteddirection0
                                   depredictedtarget0 embpstate0 emppc0
                                   emis_taken_branch0 emtargetpc0
                                   emarg20 emresult0 emdest0
                                   emmispredictedtaken0
                                   emmispredictednottaken0 emregwrite0
                                   emmemwrite0 emmemtoreg0 dmem0
                                   mmbpstate0 mmppc0 mmval0 mmdest0
                                   mmregwrite0 mwbpstate0 mwppc0 mwval0
                                   mwdest0 mwregwrite0
                                   (g 'prf (g 'impl st47))
                                   (g 'pdmemhist_2 (g 'impl st47))))
                         (s_pc0_5 (g 'spc (g 'spec st48)))
                         (s_rf0_5 (g 'srf (g 'spec st48)))
                         (s_dmem0_5 (g 'sdmem (g 'spec st48)))
                         (i_pc_5 (committedpc (g 'mwwrt (g 'impl st48))
                                     (g 'mwppc (g 'impl st48))
                                     (g 'mmwrt (g 'impl st48))
                                     (g 'mmppc (g 'impl st48))
                                     (g 'emwrt (g 'impl st48))
                                     (g 'emppc (g 'impl st48))
                                     (g 'dewrt (g 'impl st48))
                                     (g 'deppc (g 'impl st48))
                                     (g 'fdwrt (g 'impl st48))
                                     (g 'fdppc (g 'impl st48))
                                     (g 'ffwrt (g 'impl st48))
                                     (g 'ffppc (g 'impl st48))
                                     (g 'ppc (g 'impl st48))))
                         (i_rf_5 (g 'prf (g 'impl st48)))
                         (i_dmem_5 (g 'pdmemhist_2 (g 'impl st48)))
                         (rank_v_5
                             (rank (g 'mwwrt (g 'impl st48)) zero
                                   (g 'mmwrt (g 'impl st48))
                                   (g 'emwrt (g 'impl st48))
                                   (g 'dewrt (g 'impl st48))
                                   (g 'fdwrt (g 'impl st48))
                                   (g 'ffwrt (g 'impl st48))))
                         (st49 (simulate_a st48 nil t nil pc0 nil pc0
                                   bpstate0 pc0 bpstate0 ffbpstate0
                                   ffpredicteddirection0
                                   ffpredictedtarget0 ffinst0 ffppc0
                                   fdbpstate0 fdppc0 fdinst0
                                   fdpredicteddirection0
                                   fdpredictedtarget0 debpstate0 deppc0
                                   desrc10 desrc20 a1 a2 dedest0 deop0
                                   deimm0 deuseimm0 deregwrite0
                                   dememwrite0 dememtoreg0 deisbranch0
                                   depredicteddirection0
                                   depredictedtarget0 embpstate0 emppc0
                                   emis_taken_branch0 emtargetpc0
                                   emarg20 emresult0 emdest0
                                   emmispredictedtaken0
                                   emmispredictednottaken0 emregwrite0
                                   emmemwrite0 emmemtoreg0 dmem0
                                   mmbpstate0 mmppc0 mmval0 mmdest0
                                   mmregwrite0 mwbpstate0 mwppc0 mwval0
                                   mwdest0 mwregwrite0
                                   (g 'prf (g 'impl st48))
                                   (g 'pdmemhist_2 (g 'impl st48))))
                         (s_pc1_5 (g 'spc (g 'spec st49)))
                         (s_rf1_5 (g 'srf (g 'spec st49)))
                         (s_dmem1_5 (g 'sdmem (g 'spec st49)))
                         (st50 (simulate_a st49 t nil nil pc0 nil pc0
                                   bpstate0 pc0 bpstate0 ffbpstate0
                                   ffpredicteddirection0
                                   ffpredictedtarget0 ffinst0 ffppc0
                                   fdbpstate0 fdppc0 fdinst0
                                   fdpredicteddirection0
                                   fdpredictedtarget0 debpstate0 deppc0
                                   desrc10 desrc20 a1 a2 dedest0 deop0
                                   deimm0 deuseimm0 deregwrite0
                                   dememwrite0 dememtoreg0 deisbranch0
                                   depredicteddirection0
                                   depredictedtarget0 embpstate0 emppc0
                                   emis_taken_branch0 emtargetpc0
                                   emarg20 emresult0 emdest0
                                   emmispredictedtaken0
                                   emmispredictednottaken0 emregwrite0
                                   emmemwrite0 emmemtoreg0 dmem0
                                   mmbpstate0 mmppc0 mmval0 mmdest0
                                   mmregwrite0 mwbpstate0 mwppc0 mwval0
                                   mwdest0 mwregwrite0
                                   (g 'prf (g 'impl st49))
                                   (g 'pdmemhist_2 (g 'impl st49))))
                         (st51 (simulate_a st50 nil nil nil pc0 nil pc0
                                   bpstate0 pc0 bpstate0 ffbpstate0
                                   ffpredicteddirection0
                                   ffpredictedtarget0 ffinst0 ffppc0
                                   fdbpstate0 fdppc0 fdinst0
                                   fdpredicteddirection0
                                   fdpredictedtarget0 debpstate0 deppc0
                                   desrc10 desrc20 a1 a2 dedest0 deop0
                                   deimm0 deuseimm0 deregwrite0
                                   dememwrite0 dememtoreg0 deisbranch0
                                   depredicteddirection0
                                   depredictedtarget0 embpstate0 emppc0
                                   emis_taken_branch0 emtargetpc0
                                   emarg20 emresult0 emdest0
                                   emmispredictedtaken0
                                   emmispredictednottaken0 emregwrite0
                                   emmemwrite0 emmemtoreg0 dmem0
                                   mmbpstate0 mmppc0 mmval0 mmdest0
                                   mmregwrite0 mwbpstate0 mwppc0 mwval0
                                   mwdest0 mwregwrite0
                                   (g 'prf (g 'impl st50))
                                   (g 'pdmemhist_2 (g 'impl st50))))
                         (i_pc0_6 (committedpc
                                      (g 'mwwrt (g 'impl st51))
                                      (g 'mwppc (g 'impl st51))
                                      (g 'mmwrt (g 'impl st51))
                                      (g 'mmppc (g 'impl st51))
                                      (g 'emwrt (g 'impl st51))
                                      (g 'emppc (g 'impl st51))
                                      (g 'dewrt (g 'impl st51))
                                      (g 'deppc (g 'impl st51))
                                      (g 'fdwrt (g 'impl st51))
                                      (g 'fdppc (g 'impl st51))
                                      (g 'ffwrt (g 'impl st51))
                                      (g 'ffppc (g 'impl st51))
                                      (g 'ppc (g 'impl st51))))
                         (i_rf0_6 (g 'prf (g 'impl st51)))
                         (i_dmem0_6 (g 'pdmemhist_2 (g 'impl st51)))
                         (rank_w_6
                             (rank (g 'mwwrt (g 'impl st51)) zero
                                   (g 'mmwrt (g 'impl st51))
                                   (g 'emwrt (g 'impl st51))
                                   (g 'dewrt (g 'impl st51))
                                   (g 'fdwrt (g 'impl st51))
                                   (g 'ffwrt (g 'impl st51))))
                         (st52 (simulate_a st51 nil nil t i_pc0_6 nil
                                   pc0 bpstate0 pc0 bpstate0 ffbpstate0
                                   ffpredicteddirection0
                                   ffpredictedtarget0 ffinst0 ffppc0
                                   fdbpstate0 fdppc0 fdinst0
                                   fdpredicteddirection0
                                   fdpredictedtarget0 debpstate0 deppc0
                                   desrc10 desrc20 a1 a2 dedest0 deop0
                                   deimm0 deuseimm0 deregwrite0
                                   dememwrite0 dememtoreg0 deisbranch0
                                   depredicteddirection0
                                   depredictedtarget0 embpstate0 emppc0
                                   emis_taken_branch0 emtargetpc0
                                   emarg20 emresult0 emdest0
                                   emmispredictedtaken0
                                   emmispredictednottaken0 emregwrite0
                                   emmemwrite0 emmemtoreg0 dmem0
                                   mmbpstate0 mmppc0 mmval0 mmdest0
                                   mmregwrite0 mwbpstate0 mwppc0 mwval0
                                   mwdest0 mwregwrite0
                                   (g 'prf (g 'impl st51))
                                   (g 'pdmemhist_2 (g 'impl st51))))
                         (s_pc0_6 (g 'spc (g 'spec st52)))
                         (s_rf0_6 (g 'srf (g 'spec st52)))
                         (s_dmem0_6 (g 'sdmem (g 'spec st52)))
                         (i_pc_6 (committedpc (g 'mwwrt (g 'impl st52))
                                     (g 'mwppc (g 'impl st52))
                                     (g 'mmwrt (g 'impl st52))
                                     (g 'mmppc (g 'impl st52))
                                     (g 'emwrt (g 'impl st52))
                                     (g 'emppc (g 'impl st52))
                                     (g 'dewrt (g 'impl st52))
                                     (g 'deppc (g 'impl st52))
                                     (g 'fdwrt (g 'impl st52))
                                     (g 'fdppc (g 'impl st52))
                                     (g 'ffwrt (g 'impl st52))
                                     (g 'ffppc (g 'impl st52))
                                     (g 'ppc (g 'impl st52))))
                         (i_rf_6 (g 'prf (g 'impl st52)))
                         (i_dmem_6 (g 'pdmemhist_2 (g 'impl st52)))
                         (rank_v_6
                             (rank (g 'mwwrt (g 'impl st52)) zero
                                   (g 'mmwrt (g 'impl st52))
                                   (g 'emwrt (g 'impl st52))
                                   (g 'dewrt (g 'impl st52))
                                   (g 'fdwrt (g 'impl st52))
                                   (g 'ffwrt (g 'impl st52))))
                         (st53 (simulate_a st52 nil t nil pc0 nil pc0
                                   bpstate0 pc0 bpstate0 ffbpstate0
                                   ffpredicteddirection0
                                   ffpredictedtarget0 ffinst0 ffppc0
                                   fdbpstate0 fdppc0 fdinst0
                                   fdpredicteddirection0
                                   fdpredictedtarget0 debpstate0 deppc0
                                   desrc10 desrc20 a1 a2 dedest0 deop0
                                   deimm0 deuseimm0 deregwrite0
                                   dememwrite0 dememtoreg0 deisbranch0
                                   depredicteddirection0
                                   depredictedtarget0 embpstate0 emppc0
                                   emis_taken_branch0 emtargetpc0
                                   emarg20 emresult0 emdest0
                                   emmispredictedtaken0
                                   emmispredictednottaken0 emregwrite0
                                   emmemwrite0 emmemtoreg0 dmem0
                                   mmbpstate0 mmppc0 mmval0 mmdest0
                                   mmregwrite0 mwbpstate0 mwppc0 mwval0
                                   mwdest0 mwregwrite0
                                   (g 'prf (g 'impl st52))
                                   (g 'pdmemhist_2 (g 'impl st52))))
                         (s_pc1_6 (g 'spc (g 'spec st53)))
                         (s_rf1_6 (g 'srf (g 'spec st53)))
                         (s_dmem1_6 (g 'sdmem (g 'spec st53)))
                         (st54 (simulate_a st53 t nil nil pc0 nil pc0
                                   bpstate0 pc0 bpstate0 ffbpstate0
                                   ffpredicteddirection0
                                   ffpredictedtarget0 ffinst0 ffppc0
                                   fdbpstate0 fdppc0 fdinst0
                                   fdpredicteddirection0
                                   fdpredictedtarget0 debpstate0 deppc0
                                   desrc10 desrc20 a1 a2 dedest0 deop0
                                   deimm0 deuseimm0 deregwrite0
                                   dememwrite0 dememtoreg0 deisbranch0
                                   depredicteddirection0
                                   depredictedtarget0 embpstate0 emppc0
                                   emis_taken_branch0 emtargetpc0
                                   emarg20 emresult0 emdest0
                                   emmispredictedtaken0
                                   emmispredictednottaken0 emregwrite0
                                   emmemwrite0 emmemtoreg0 dmem0
                                   mmbpstate0 mmppc0 mmval0 mmdest0
                                   mmregwrite0 mwbpstate0 mwppc0 mwval0
                                   mwdest0 mwregwrite0
                                   (g 'prf (g 'impl st53))
                                   (g 'pdmemhist_2 (g 'impl st53))))
                         (i_pc0_7 (committedpc
                                      (g 'mwwrt (g 'impl st54))
                                      (g 'mwppc (g 'impl st54))
                                      (g 'mmwrt (g 'impl st54))
                                      (g 'mmppc (g 'impl st54))
                                      (g 'emwrt (g 'impl st54))
                                      (g 'emppc (g 'impl st54))
                                      (g 'dewrt (g 'impl st54))
                                      (g 'deppc (g 'impl st54))
                                      (g 'fdwrt (g 'impl st54))
                                      (g 'fdppc (g 'impl st54))
                                      (g 'ffwrt (g 'impl st54))
                                      (g 'ffppc (g 'impl st54))
                                      (g 'ppc (g 'impl st54))))
                         (i_rf0_7 (g 'prf (g 'impl st54)))
                         (i_dmem0_7 (g 'pdmemhist_2 (g 'impl st54)))
                         (rank_w_7
                             (rank (g 'mwwrt (g 'impl st54)) zero
                                   (g 'mmwrt (g 'impl st54))
                                   (g 'emwrt (g 'impl st54))
                                   (g 'dewrt (g 'impl st54))
                                   (g 'fdwrt (g 'impl st54))
                                   (g 'ffwrt (g 'impl st54))))
                         (st55 (simulate_a st54 nil nil t i_pc0_7 nil
                                   pc0 bpstate0 pc0 bpstate0 ffbpstate0
                                   ffpredicteddirection0
                                   ffpredictedtarget0 ffinst0 ffppc0
                                   fdbpstate0 fdppc0 fdinst0
                                   fdpredicteddirection0
                                   fdpredictedtarget0 debpstate0 deppc0
                                   desrc10 desrc20 a1 a2 dedest0 deop0
                                   deimm0 deuseimm0 deregwrite0
                                   dememwrite0 dememtoreg0 deisbranch0
                                   depredicteddirection0
                                   depredictedtarget0 embpstate0 emppc0
                                   emis_taken_branch0 emtargetpc0
                                   emarg20 emresult0 emdest0
                                   emmispredictedtaken0
                                   emmispredictednottaken0 emregwrite0
                                   emmemwrite0 emmemtoreg0 dmem0
                                   mmbpstate0 mmppc0 mmval0 mmdest0
                                   mmregwrite0 mwbpstate0 mwppc0 mwval0
                                   mwdest0 mwregwrite0
                                   (g 'prf (g 'impl st54))
                                   (g 'pdmemhist_2 (g 'impl st54))))
                         (s_pc0_7 (g 'spc (g 'spec st55)))
                         (s_rf0_7 (g 'srf (g 'spec st55)))
                         (s_dmem0_7 (g 'sdmem (g 'spec st55)))
                         (i_pc_7 (committedpc (g 'mwwrt (g 'impl st55))
                                     (g 'mwppc (g 'impl st55))
                                     (g 'mmwrt (g 'impl st55))
                                     (g 'mmppc (g 'impl st55))
                                     (g 'emwrt (g 'impl st55))
                                     (g 'emppc (g 'impl st55))
                                     (g 'dewrt (g 'impl st55))
                                     (g 'deppc (g 'impl st55))
                                     (g 'fdwrt (g 'impl st55))
                                     (g 'fdppc (g 'impl st55))
                                     (g 'ffwrt (g 'impl st55))
                                     (g 'ffppc (g 'impl st55))
                                     (g 'ppc (g 'impl st55))))
                         (i_rf_7 (g 'prf (g 'impl st55)))
                         (i_dmem_7 (g 'pdmemhist_2 (g 'impl st55)))
                         (rank_v_7
                             (rank (g 'mwwrt (g 'impl st55)) zero
                                   (g 'mmwrt (g 'impl st55))
                                   (g 'emwrt (g 'impl st55))
                                   (g 'dewrt (g 'impl st55))
                                   (g 'fdwrt (g 'impl st55))
                                   (g 'ffwrt (g 'impl st55))))
                         (st56 (simulate_a st55 nil t nil pc0 nil pc0
                                   bpstate0 pc0 bpstate0 ffbpstate0
                                   ffpredicteddirection0
                                   ffpredictedtarget0 ffinst0 ffppc0
                                   fdbpstate0 fdppc0 fdinst0
                                   fdpredicteddirection0
                                   fdpredictedtarget0 debpstate0 deppc0
                                   desrc10 desrc20 a1 a2 dedest0 deop0
                                   deimm0 deuseimm0 deregwrite0
                                   dememwrite0 dememtoreg0 deisbranch0
                                   depredicteddirection0
                                   depredictedtarget0 embpstate0 emppc0
                                   emis_taken_branch0 emtargetpc0
                                   emarg20 emresult0 emdest0
                                   emmispredictedtaken0
                                   emmispredictednottaken0 emregwrite0
                                   emmemwrite0 emmemtoreg0 dmem0
                                   mmbpstate0 mmppc0 mmval0 mmdest0
                                   mmregwrite0 mwbpstate0 mwppc0 mwval0
                                   mwdest0 mwregwrite0
                                   (g 'prf (g 'impl st55))
                                   (g 'pdmemhist_2 (g 'impl st55))))
                         (s_pc1_7 (g 'spc (g 'spec st56)))
                         (s_rf1_7 (g 'srf (g 'spec st56)))
                         (s_dmem1_7 (g 'sdmem (g 'spec st56))))
                    (and (and (and (and
                                    (and
                                     (and
                                      (and good_ma_v
                                       (or
                                        (or
                                         (not
                                          (and
                                           (and (equal s_pc0 i_pc0)
                                            (equal
                                             (read-srf_a a1 s_rf0)
                                             (read-prf_a a1 i_rf0)))
                                           (equal s_dmem0 i_dmem0)))
                                         (and
                                          (and (equal s_pc1 i_pc)
                                           (equal (read-srf_a a1 s_rf1)
                                            (read-prf_a a1 i_rf)))
                                          (equal s_dmem1 i_dmem)))
                                        (and
                                         (and
                                          (and (equal s_pc0 i_pc)
                                           (equal (read-srf_a a1 s_rf0)
                                            (read-prf_a a1 i_rf)))
                                          (equal s_dmem0 i_dmem))
                                         (< rank_v rank_w))))
                                      (or
                                       (or
                                        (not
                                         (and
                                          (and (equal s_pc0_2 i_pc0_2)
                                           (equal
                                            (read-srf_a a1 s_rf0_2)
                                            (read-prf_a a1 i_rf0_2)))
                                          (equal s_dmem0_2 i_dmem0_2)))
                                        (and
                                         (and (equal s_pc1_2 i_pc_2)
                                          (equal
                                           (read-srf_a a1 s_rf1_2)
                                           (read-prf_a a1 i_rf_2)))
                                         (equal s_dmem1_2 i_dmem_2)))
                                       (and
                                        (and
                                         (and (equal s_pc0_2 i_pc_2)
                                          (equal
                                           (read-srf_a a1 s_rf0_2)
                                           (read-prf_a a1 i_rf_2)))
                                         (equal s_dmem0_2 i_dmem_2))
                                        (< rank_v_2 rank_w_2))))
                                     (or
                                      (or
                                       (not
                                        (and
                                         (and (equal s_pc0_3 i_pc0_3)
                                          (equal
                                           (read-srf_a a1 s_rf0_3)
                                           (read-prf_a a1 i_rf0_3)))
                                         (equal s_dmem0_3 i_dmem0_3)))
                                       (and
                                        (and (equal s_pc1_3 i_pc_3)
                                         (equal (read-srf_a a1 s_rf1_3)
                                          (read-prf_a a1 i_rf_3)))
                                        (equal s_dmem1_3 i_dmem_3)))
                                      (and
                                       (and
                                        (and (equal s_pc0_3 i_pc_3)
                                         (equal (read-srf_a a1 s_rf0_3)
                                          (read-prf_a a1 i_rf_3)))
                                        (equal s_dmem0_3 i_dmem_3))
                                       (< rank_v_3 rank_w_3))))
                                    (or
                                     (or
                                      (not
                                       (and
                                        (and (equal s_pc0_4 i_pc0_4)
                                         (equal (read-srf_a a1 s_rf0_4)
                                          (read-prf_a a1 i_rf0_4)))
                                        (equal s_dmem0_4 i_dmem0_4)))
                                      (and
                                       (and (equal s_pc1_4 i_pc_4)
                                        (equal (read-srf_a a1 s_rf1_4)
                                         (read-prf_a a1 i_rf_4)))
                                       (equal s_dmem1_4 i_dmem_4)))
                                     (and
                                      (and
                                       (and (equal s_pc0_4 i_pc_4)
                                        (equal (read-srf_a a1 s_rf0_4)
                                         (read-prf_a a1 i_rf_4)))
                                       (equal s_dmem0_4 i_dmem_4))
                                      (< rank_v_4 rank_w_4))))
                                   (or
                                    (or
                                     (not
                                      (and
                                       (and (equal s_pc0_5 i_pc0_5)
                                        (equal (read-srf_a a1 s_rf0_5)
                                         (read-prf_a a1 i_rf0_5)))
                                       (equal s_dmem0_5 i_dmem0_5)))
                                     (and
                                      (and (equal s_pc1_5 i_pc_5)
                                       (equal (read-srf_a a1 s_rf1_5)
                                        (read-prf_a a1 i_rf_5)))
                                      (equal s_dmem1_5 i_dmem_5)))
                                    (and
                                     (and
                                      (and (equal s_pc0_5 i_pc_5)
                                       (equal (read-srf_a a1 s_rf0_5)
                                        (read-prf_a a1 i_rf_5)))
                                      (equal s_dmem0_5 i_dmem_5))
                                     (< rank_v_5 rank_w_5))))
                              (or (or (not
                                       (and
                                        (and (equal s_pc0_6 i_pc0_6)
                                         (equal (read-srf_a a1 s_rf0_6)
                                          (read-prf_a a1 i_rf0_6)))
                                        (equal s_dmem0_6 i_dmem0_6)))
                                      (and
                                       (and (equal s_pc1_6 i_pc_6)
                                        (equal (read-srf_a a1 s_rf1_6)
                                         (read-prf_a a1 i_rf_6)))
                                       (equal s_dmem1_6 i_dmem_6)))
                                  (and (and
                                        (and (equal s_pc0_6 i_pc_6)
                                         (equal (read-srf_a a1 s_rf0_6)
                                          (read-prf_a a1 i_rf_6)))
                                        (equal s_dmem0_6 i_dmem_6))
                                       (< rank_v_6 rank_w_6))))
                         (or (or (not (and
                                       (and (equal s_pc0_7 i_pc0_7)
                                        (equal (read-srf_a a1 s_rf0_7)
                                         (read-prf_a a1 i_rf0_7)))
                                       (equal s_dmem0_7 i_dmem0_7)))
                                 (and (and (equal s_pc1_7 i_pc_7)
                                       (equal (read-srf_a a1 s_rf1_7)
                                        (read-prf_a a1 i_rf_7)))
                                      (equal s_dmem1_7 i_dmem_7)))
                             (and (and (and (equal s_pc0_7 i_pc_7)
                                        (equal (read-srf_a a1 s_rf0_7)
                                         (read-prf_a a1 i_rf_7)))
                                       (equal s_dmem0_7 i_dmem_7))
                                  (< rank_v_7 rank_w_7))))))
         :rule-classes nil)

