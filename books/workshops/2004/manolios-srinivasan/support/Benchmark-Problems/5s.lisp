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

(encapsulate ((writerf (x3 x2 x1) t))
     (local (defun writerf (x3 x2 x1)
              (declare (ignore x3) (ignore x2) (ignore x1))
              1))
     (defthm writerf-type (integerp (writerf x3 x2 x1))))

(encapsulate ((readrf (x2 x1) t))
     (local (defun readrf (x2 x1) (declare (ignore x2) (ignore x1)) 1))
     (defthm readrf-type (integerp (readrf x2 x1))))

(encapsulate ((writedmem (x3 x2 x1) t))
     (local (defun writedmem (x3 x2 x1)
              (declare (ignore x3) (ignore x2) (ignore x1))
              1))
     (defthm writedmem-type (integerp (writedmem x3 x2 x1))))

(encapsulate ((readdmem (x2 x1) t))
     (local (defun readdmem (x2 x1)
              (declare (ignore x2) (ignore x1))
              1))
     (defthm readdmem-type (integerp (readdmem x2 x1))))

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
        (pimem ppc prf fdwrt fdinst fdppc deppc desrc1 desrc2 dearg1
               dearg2 dedest deop deimm deuseimm deregwrite dememwrite
               dememtoreg dewrt emppc emarg2 emresult emdest emwrt
               emregwrite emmemwrite emmemtoreg pdmemhist_1 pdmem mwval
               mwppc mwdest mwwrt mwregwrite)
   (seq nil 'pimem pimem 'ppc ppc 'prf prf 'fdwrt fdwrt 'fdinst fdinst
        'fdppc fdppc 'deppc deppc 'desrc1 desrc1 'desrc2 desrc2 'dearg1
        dearg1 'dearg2 dearg2 'dedest dedest 'deop deop 'deimm deimm
        'deuseimm deuseimm 'deregwrite deregwrite 'dememwrite
        dememwrite 'dememtoreg dememtoreg 'dewrt dewrt 'emppc emppc
        'emarg2 emarg2 'emresult emresult 'emdest emdest 'emwrt emwrt
        'emregwrite emregwrite 'emmemwrite emmemwrite 'emmemtoreg
        emmemtoreg 'pdmemhist_1 pdmemhist_1 'pdmem pdmem 'mwval mwval
        'mwppc mwppc 'mwdest mwdest 'mwwrt mwwrt 'mwregwrite
        mwregwrite))

(defun initpimem_a (pimem) (cons (s 0 t (s 1 nil nil)) pimem))

(defun nextpimem_a (pimem) (cons (s 0 nil (s 1 nil nil)) pimem))

(defun initppc_a (pc0) pc0)

(defun nextppc_a (initi pc0 commit_impl commit_pc stall ppc)
   (cond (initi pc0) (commit_impl commit_pc) (stall ppc) (t (add-1 ppc))))

(defun initprf_a (prf) (cons (s 0 t (s 1 nil nil)) prf))

(defun nextprf_a (prf initi commit_impl mwwrt mwdest mwregwrite mwval)
   (cons (s 0 nil
	    (s 1 initi
	       (s 2 commit_impl
		  (s 3 mwwrt
		     (s 4 mwdest
			(s 5 mwregwrite (s 6 mwval nil)))))))
	 prf))


(defun initfdwrt_a () nil)

(defun nextfdwrt_a (initi commit_impl stall fdwrt)
   (cond (initi nil) (commit_impl nil) (stall fdwrt) (t t)))

(defun initfdinst_a (fdinst0) fdinst0)

(defun nextfdinst_a (initi fdinst0 stall fdinst inst)
   (cond (initi fdinst0) (stall fdinst) (t inst)))

(defun initfdppc_a (fdppc0) fdppc0)

(defun nextfdppc_a (initi fdppc0 stall fdppc ppc)
   (cond (initi fdppc0) (stall fdppc) (t ppc)))

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

(defun initdewrt_a () nil)

(defun nextdewrt_a (initi commit_impl stall fdwrt)
   (cond (initi nil) (commit_impl nil) (t (and (not stall) fdwrt))))

(defun initemppc_a (emppc0) emppc0)

(defun nextemppc_a (initi emppc0 deppc)
   (cond (initi emppc0) (t deppc)))

(defun initemarg2_a (emarg20) emarg20)

(defun nextemarg2_a (initi emarg20 dearg2)
   (cond (initi emarg20) (t dearg2)))

(defun initemresult_a (emresult0) emresult0)

(defun nextemresult_a (initi emresult0 result)
   (cond (initi emresult0) (t result)))

(defun initemdest_a (emdest0) emdest0)

(defun nextemdest_a (initi emdest0 dedest)
   (cond (initi emdest0) (t dedest)))

(defun initemwrt_a () nil)

(defun nextemwrt_a (initi commit_impl dewrt)
   (cond (initi nil) (commit_impl nil) (t dewrt)))

(defun initemregwrite_a (emregwrite0) emregwrite0)

(defun nextemregwrite_a (initi emregwrite0 deregwrite)
   (cond (initi emregwrite0) (t deregwrite)))

(defun initemmemwrite_a (emmemwrite0) emmemwrite0)

(defun nextemmemwrite_a (initi emmemwrite0 dememwrite)
   (cond (initi emmemwrite0) (t dememwrite)))

(defun initemmemtoreg_a (emmemtoreg0) emmemtoreg0)

(defun nextemmemtoreg_a (initi emmemtoreg0 dememtoreg)
   (cond (initi emmemtoreg0) (t dememtoreg)))

(defun initpdmemhist_1_a (dmem0) dmem0)

(defun nextpdmemhist_1_a (initi dmem0 pdmem)
   (cond (initi dmem0) (t pdmem)))

(defun initpdmem_a (dmem0) dmem0)

(defun nextpdmem_a
        (initi dmem0 commit_impl pdmemhist_1 emwrt emmemwrite emarg2
               emresult pdmem)
   (cond
     (initi dmem0)
     (commit_impl pdmemhist_1)
     ((and emwrt emmemwrite) (writedmem emarg2 emresult pdmem))
     (t pdmem)))

(defun initmwval_a (mwval0) mwval0)

(defun nextmwval_a (initi mwval0 emmemtoreg readdata emresult)
   (cond (initi mwval0) (emmemtoreg readdata) (t emresult)))

(defun initmwppc_a (mwppc0) mwppc0)

(defun nextmwppc_a (initi mwppc0 emppc)
   (cond (initi mwppc0) (t emppc)))

(defun initmwdest_a (mwdest0) mwdest0)

(defun nextmwdest_a (initi mwdest0 emdest)
   (cond (initi mwdest0) (t emdest)))

(defun initmwwrt_a () nil)

(defun nextmwwrt_a (initi commit_impl emwrt)
   (cond (initi nil) (commit_impl nil) (t emwrt)))

(defun initmwregwrite_a (mwregwrite0) mwregwrite0)

(defun nextmwregwrite_a (initi mwregwrite0 emregwrite)
   (cond (initi mwregwrite0) (t emregwrite)))

(defun impl-simulate_a
        (impl initi pc0 commit_impl commit_pc fdinst0 fdppc0 deppc0
              desrc10 desrc20 a1 a2 dedest0 deop0 deimm0 deuseimm0
              deregwrite0 dememwrite0 dememtoreg0 emppc0 emarg20
              emresult0 emdest0 emregwrite0 emmemwrite0 emmemtoreg0
              dmem0 mwval0 mwppc0 mwdest0 mwregwrite0)
   (let  ((pimem (g 'pimem impl)) (ppc (g 'ppc impl))
          (prf (g 'prf impl)) (fdwrt (g 'fdwrt impl))
          (fdinst (g 'fdinst impl)) (fdppc (g 'fdppc impl))
          (deppc (g 'deppc impl)) (desrc1 (g 'desrc1 impl))
          (desrc2 (g 'desrc2 impl)) (dearg1 (g 'dearg1 impl))
          (dearg2 (g 'dearg2 impl)) (dedest (g 'dedest impl))
          (deop (g 'deop impl)) (deimm (g 'deimm impl))
          (deuseimm (g 'deuseimm impl))
          (deregwrite (g 'deregwrite impl))
          (dememwrite (g 'dememwrite impl))
          (dememtoreg (g 'dememtoreg impl)) (dewrt (g 'dewrt impl))
          (emppc (g 'emppc impl)) (emarg2 (g 'emarg2 impl))
          (emresult (g 'emresult impl)) (emdest (g 'emdest impl))
          (emwrt (g 'emwrt impl)) (emregwrite (g 'emregwrite impl))
          (emmemwrite (g 'emmemwrite impl))
          (emmemtoreg (g 'emmemtoreg impl))
          (pdmemhist_1 (g 'pdmemhist_1 impl)) (pdmem (g 'pdmem impl))
          (mwval (g 'mwval impl)) (mwppc (g 'mwppc impl))
          (mwdest (g 'mwdest impl)) (mwwrt (g 'mwwrt impl))
          (mwregwrite (g 'mwregwrite impl)))
     (let* ((inst (read-pimem_a ppc pimem)) (if_id_src1 (src1 fdinst))
            (if_id_src2 (src2 fdinst))
            (stall (and (and deregwrite dewrt)
                        (or (equal if_id_src1 dedest)
                            (equal if_id_src2 dedest))))
            (id_regwrite (getregwrite fdinst))
            (id_memwrite (getmemwrite fdinst))
            (ex_wb_equal_src1
                (and (and mwwrt (equal desrc1 mwdest)) mwregwrite))
            (ex_wb_equal_src2
                (and (and mwwrt (equal desrc2 mwdest)) mwregwrite))
            (ex_wb_fwd_src1 (cond (ex_wb_equal_src1 mwval) (t dearg1)))
            (ex_wb_fwd_src2 (cond (ex_wb_equal_src2 mwval) (t dearg2)))
            (ex_data2 (cond (deuseimm deimm) (t ex_wb_fwd_src2)))
            (result (alu deop ex_wb_fwd_src1 ex_data2))
            (readdata (readdmem emresult pdmem)))
       (impl-state_a (nextpimem_a pimem)
           (nextppc_a initi pc0 commit_impl commit_pc stall ppc)
           (nextprf_a prf initi commit_impl mwwrt mwdest mwregwrite
               mwval)
           (nextfdwrt_a initi commit_impl stall fdwrt)
           (nextfdinst_a initi fdinst0 stall fdinst inst)
           (nextfdppc_a initi fdppc0 stall fdppc ppc)
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
           (nextdewrt_a initi commit_impl stall fdwrt)
           (nextemppc_a initi emppc0 deppc)
           (nextemarg2_a initi emarg20 dearg2)
           (nextemresult_a initi emresult0 result)
           (nextemdest_a initi emdest0 dedest)
           (nextemwrt_a initi commit_impl dewrt)
           (nextemregwrite_a initi emregwrite0 deregwrite)
           (nextemmemwrite_a initi emmemwrite0 dememwrite)
           (nextemmemtoreg_a initi emmemtoreg0 dememtoreg)
           (nextpdmemhist_1_a initi dmem0 pdmem)
           (nextpdmem_a initi dmem0 commit_impl pdmemhist_1 emwrt
               emmemwrite emarg2 emresult pdmem)
           (nextmwval_a initi mwval0 emmemtoreg readdata emresult)
           (nextmwppc_a initi mwppc0 emppc)
           (nextmwdest_a initi mwdest0 emdest)
           (nextmwwrt_a initi commit_impl emwrt)
           (nextmwregwrite_a initi mwregwrite0 emregwrite)))))

(defun impl-initialize_a
        (impl pc0 fdinst0 fdppc0 deppc0 desrc10 desrc20 a1 a2 dedest0
              deop0 deimm0 deuseimm0 deregwrite0 dememwrite0
              dememtoreg0 emppc0 emarg20 emresult0 emdest0 emregwrite0
              emmemwrite0 emmemtoreg0 dmem0 mwval0 mwppc0 mwdest0
              mwregwrite0)
   (let  ((pimem (g 'pimem impl)) (ppc (g 'ppc impl))
          (prf (g 'prf impl)) (fdwrt (g 'fdwrt impl))
          (fdinst (g 'fdinst impl)) (fdppc (g 'fdppc impl))
          (deppc (g 'deppc impl)) (desrc1 (g 'desrc1 impl))
          (desrc2 (g 'desrc2 impl)) (dearg1 (g 'dearg1 impl))
          (dearg2 (g 'dearg2 impl)) (dedest (g 'dedest impl))
          (deop (g 'deop impl)) (deimm (g 'deimm impl))
          (deuseimm (g 'deuseimm impl))
          (deregwrite (g 'deregwrite impl))
          (dememwrite (g 'dememwrite impl))
          (dememtoreg (g 'dememtoreg impl)) (dewrt (g 'dewrt impl))
          (emppc (g 'emppc impl)) (emarg2 (g 'emarg2 impl))
          (emresult (g 'emresult impl)) (emdest (g 'emdest impl))
          (emwrt (g 'emwrt impl)) (emregwrite (g 'emregwrite impl))
          (emmemwrite (g 'emmemwrite impl))
          (emmemtoreg (g 'emmemtoreg impl))
          (pdmemhist_1 (g 'pdmemhist_1 impl)) (pdmem (g 'pdmem impl))
          (mwval (g 'mwval impl)) (mwppc (g 'mwppc impl))
          (mwdest (g 'mwdest impl)) (mwwrt (g 'mwwrt impl))
          (mwregwrite (g 'mwregwrite impl)))
     (let* ((inst (read-pimem_a ppc pimem)) (if_id_src1 (src1 fdinst))
            (if_id_src2 (src2 fdinst))
            (stall (and (and deregwrite dewrt)
                        (or (equal if_id_src1 dedest)
                            (equal if_id_src2 dedest))))
            (id_regwrite (getregwrite fdinst))
            (id_memwrite (getmemwrite fdinst))
            (ex_wb_equal_src1
                (and (and mwwrt (equal desrc1 mwdest)) mwregwrite))
            (ex_wb_equal_src2
                (and (and mwwrt (equal desrc2 mwdest)) mwregwrite))
            (ex_wb_fwd_src1 (cond (ex_wb_equal_src1 mwval) (t dearg1)))
            (ex_wb_fwd_src2 (cond (ex_wb_equal_src2 mwval) (t dearg2)))
            (ex_data2 (cond (deuseimm deimm) (t ex_wb_fwd_src2)))
            (result (alu deop ex_wb_fwd_src1 ex_data2))
            (readdata (readdmem emresult pdmem)))
       (impl-state_a (initpimem_a pimem) (initppc_a pc0)
           (initprf_a prf) (initfdwrt_a) (initfdinst_a fdinst0)
           (initfdppc_a fdppc0) (initdeppc_a deppc0)
           (initdesrc1_a desrc10) (initdesrc2_a desrc20)
           (initdearg1_a a1) (initdearg2_a a2) (initdedest_a dedest0)
           (initdeop_a deop0) (initdeimm_a deimm0)
           (initdeuseimm_a deuseimm0) (initderegwrite_a deregwrite0)
           (initdememwrite_a dememwrite0)
           (initdememtoreg_a dememtoreg0) (initdewrt_a)
           (initemppc_a emppc0) (initemarg2_a emarg20)
           (initemresult_a emresult0) (initemdest_a emdest0)
           (initemwrt_a) (initemregwrite_a emregwrite0)
           (initemmemwrite_a emmemwrite0)
           (initemmemtoreg_a emmemtoreg0) (initpdmemhist_1_a dmem0)
           (initpdmem_a dmem0) (initmwval_a mwval0)
           (initmwppc_a mwppc0) (initmwdest_a mwdest0) (initmwwrt_a)
           (initmwregwrite_a mwregwrite0)))))

(defun spec-state_a (simem spc srf sdmem)
   (seq nil 'simem simem 'spc spc 'srf srf 'sdmem sdmem))

(defun initsimem_a (simem) (cons (s 0 t (s 1 nil nil)) simem))

(defun nextsimem_a (simem) (cons (s 0 nil (s 1 nil nil)) simem))

(defun initspc_a (pc0) pc0)

(defun nextspc_a (initi pc0 project_impl project_pc isa spc)
   (cond (initi pc0) (project_impl project_pc) (isa (add-1 spc)) (t spc)))

(defun initsrf_a (srf) (cons  (s 0 t (s 1 nil nil)) srf))

(defun nextsrf_a
  (srf initi project_impl impl.prf isa inst regwrite val)
  (cons  (S 0 NIL
	    (S 1 INITI
	       (S 2 PROJECT_IMPL
		  (S 3 |IMPL.PRF|
		     (S 4 ISA
			(S 5
			   INST (S 6 REGWRITE (S 7 VAL NIL))))))))
         srf))

(defun initsdmem_a (dmem0) dmem0)

(defun nextsdmem_a
        (initi dmem0 project_impl impl.pdmemhist_1 isa memwrite
               arg2_temp result sdmem)
   (cond
     (initi dmem0)
     (project_impl impl.pdmemhist_1)
     ((and isa memwrite) (writedmem arg2_temp result sdmem))
     (t sdmem)))

(defun spec-simulate_a
        (spec initi pc0 project_impl project_pc isa impl.prf dmem0
              impl.pdmemhist_1)
   (let  ((simem (g 'simem spec)) (spc (g 'spc spec))
          (srf (g 'srf spec)) (sdmem (g 'sdmem spec)))
     (let* ((inst (read-simem_a spc simem))
            (regwrite (getregwrite inst)) (memtoreg (getmemtoreg inst))
            (memwrite (getmemwrite inst)) (useimm (getuseimm inst))
            (imm (getimm inst)) (arg1 (read-srf_a (src1 inst) srf))
            (arg2_temp (read-srf_a (src2 inst) srf))
            (arg2 (cond (useimm imm) (t arg2_temp)))
            (result (alu (opcode inst) arg1 arg2))
            (readdata (readdmem result sdmem))
            (val (cond (memtoreg readdata) (t result))))
       (spec-state_a (nextsimem_a simem)
           (nextspc_a initi pc0 project_impl project_pc isa spc)
           (nextsrf_a srf initi project_impl impl.prf isa inst regwrite
               val)
           (nextsdmem_a initi dmem0 project_impl impl.pdmemhist_1 isa
               memwrite arg2_temp result sdmem)))))

(defun spec-initialize_a (spec pc0 dmem0)
   (let  ((simem (g 'simem spec)) (spc (g 'spc spec))
          (srf (g 'srf spec)) (sdmem (g 'sdmem spec)))
     (let* ((inst (read-simem_a spc simem))
            (regwrite (getregwrite inst)) (memtoreg (getmemtoreg inst))
            (memwrite (getmemwrite inst)) (useimm (getuseimm inst))
            (imm (getimm inst)) (arg1 (read-srf_a (src1 inst) srf))
            (arg2_temp (read-srf_a (src2 inst) srf))
            (arg2 (cond (useimm imm) (t arg2_temp)))
            (result (alu (opcode inst) arg1 arg2))
            (readdata (readdmem result sdmem))
            (val (cond (memtoreg readdata) (t result))))
       (spec-state_a (initsimem_a simem) (initspc_a pc0)
           (initsrf_a srf) (initsdmem_a dmem0)))))

(defun simulate_a
        (st initi isa project_impl project_pc commit_impl commit_pc pc0
            fdinst0 fdppc0 deppc0 desrc10 desrc20 a1 a2 dedest0 deop0
            deimm0 deuseimm0 deregwrite0 dememwrite0 dememtoreg0 emppc0
            emarg20 emresult0 emdest0 emregwrite0 emmemwrite0
            emmemtoreg0 dmem0 mwval0 mwppc0 mwdest0 mwregwrite0
            impl.prf impl.pdmemhist_1)
   (u-state_a
       (impl-simulate_a (g 'impl st) initi pc0 commit_impl commit_pc
           fdinst0 fdppc0 deppc0 desrc10 desrc20 a1 a2 dedest0 deop0
           deimm0 deuseimm0 deregwrite0 dememwrite0 dememtoreg0 emppc0
           emarg20 emresult0 emdest0 emregwrite0 emmemwrite0
           emmemtoreg0 dmem0 mwval0 mwppc0 mwdest0 mwregwrite0)
       (spec-simulate_a (g 'spec st) initi pc0 project_impl project_pc
           isa impl.prf dmem0 impl.pdmemhist_1)))

(defun initialize_a
        (st initi isa project_impl project_pc commit_impl commit_pc pc0
            fdinst0 fdppc0 deppc0 desrc10 desrc20 a1 a2 dedest0 deop0
            deimm0 deuseimm0 deregwrite0 dememwrite0 dememtoreg0 emppc0
            emarg20 emresult0 emdest0 emregwrite0 emmemwrite0
            emmemtoreg0 dmem0 mwval0 mwppc0 mwdest0 mwregwrite0)
   (u-state_a
       (impl-initialize_a (g 'impl st) pc0 fdinst0 fdppc0 deppc0
           desrc10 desrc20 a1 a2 dedest0 deop0 deimm0 deuseimm0
           deregwrite0 dememwrite0 dememtoreg0 emppc0 emarg20 emresult0
           emdest0 emregwrite0 emmemwrite0 emmemtoreg0 dmem0 mwval0
           mwppc0 mwdest0 mwregwrite0)
       (spec-initialize_a (g 'spec st) pc0 dmem0)))

(defun equiv_ma
        (ppc_v impl.ppc prf_v a1 impl.prf pimem_v impl.pimem pdmem_v
               impl.pdmem fdwrt_v impl.fdwrt fdinst_v impl.fdinst
               dewrt_v impl.dewrt deop_v impl.deop dearg1_v impl.dearg1
               dearg2_v impl.dearg2 dedest_v impl.dedest desrc1_v
               impl.desrc1 desrc2_v impl.desrc2 deimm_v impl.deimm
               deuseimm_v impl.deuseimm dememtoreg_v impl.dememtoreg
               dememwrite_v impl.dememwrite deregwrite_v
               impl.deregwrite emwrt_v impl.emwrt emdest_v impl.emdest
               emregwrite_v impl.emregwrite emresult_v impl.emresult
               emmemtoreg_v impl.emmemtoreg emmemwrite_v
               impl.emmemwrite mwwrt_v impl.mwwrt mwval_v impl.mwval
               mwdest_v impl.mwdest mwregwrite_v impl.mwregwrite)
   (and (and (and (and (and (and (and (and
                                       (and
                                        (and
                                         (and (equal ppc_v impl.ppc)
                                          (equal (read-prf_a a1 prf_v)
                                           (read-prf_a a1 impl.prf)))
                                         (equal
                                          (read-pimem_a a1 pimem_v)
                                          (read-pimem_a a1 impl.pimem)))
                                        (equal pdmem_v impl.pdmem))
                                       (or (and fdwrt_v impl.fdwrt)
                                        (and (not fdwrt_v)
                                         (not impl.fdwrt))))
                                      (implies fdwrt_v
                                       (and impl.fdwrt
                                        (equal fdinst_v impl.fdinst))))
                                 (or (and dewrt_v impl.dewrt)
                                     (and (not dewrt_v)
                                      (not impl.dewrt))))
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
                                               (and impl.dewrt
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
                                           (equal desrc2_v impl.desrc2))
                                          (equal deimm_v impl.deimm))
                                         (or
                                          (and deuseimm_v
                                           impl.deuseimm)
                                          (and (not deuseimm_v)
                                           (not impl.deuseimm))))
                                        (or
                                         (and dememtoreg_v
                                          impl.dememtoreg)
                                         (and (not dememtoreg_v)
                                          (not impl.dememtoreg))))
                                       (or
                                        (and dememwrite_v
                                         impl.dememwrite)
                                        (and (not dememwrite_v)
                                         (not impl.dememwrite))))
                                      (or
                                       (and deregwrite_v
                                        impl.deregwrite)
                                       (and (not deregwrite_v)
                                        (not impl.deregwrite))))))
                       (or (and emwrt_v impl.emwrt)
                           (and (not emwrt_v) (not impl.emwrt))))
                  (implies emwrt_v
                           (and (and (and
                                      (and
                                       (and impl.emwrt
                                        (equal emdest_v impl.emdest))
                                       (or
                                        (and emregwrite_v
                                         impl.emregwrite)
                                        (and (not emregwrite_v)
                                         (not impl.emregwrite))))
                                      (equal emresult_v impl.emresult))
                                     (or
                                      (and emmemtoreg_v
                                       impl.emmemtoreg)
                                      (and (not emmemtoreg_v)
                                       (not impl.emmemtoreg))))
                                (or (and emmemwrite_v impl.emmemwrite)
                                    (and (not emmemwrite_v)
                                     (not impl.emmemwrite))))))
             (or (and mwwrt_v impl.mwwrt)
                 (and (not mwwrt_v) (not impl.mwwrt))))
        (implies mwwrt_v
                 (and (and (and impl.mwwrt (equal mwval_v impl.mwval))
                           (equal mwdest_v impl.mwdest))
                      (or (and mwregwrite_v impl.mwregwrite)
                          (and (not mwregwrite_v)
                               (not impl.mwregwrite)))))))

(defun rank (impl.mwwrt zero impl.emwrt impl.dewrt impl.fdwrt)
   (cond
     (impl.mwwrt zero)
     (impl.emwrt (add-1 zero))
     (impl.dewrt (add-1 (add-1 zero)))
     (impl.fdwrt (add-1 (add-1 (add-1 zero))))
     (t (add-1 (add-1 (add-1 (add-1 zero)))))))

(defun committedpc
        (impl.mwwrt impl.mwppc impl.emwrt impl.emppc impl.dewrt
            impl.deppc impl.fdwrt impl.fdppc impl.ppc)
   (cond
     (impl.mwwrt impl.mwppc)
     (impl.emwrt impl.emppc)
     (impl.dewrt impl.deppc)
     (impl.fdwrt impl.fdppc)
     (t impl.ppc)))

(defthm web_core_a
         (implies (and (integerp pc0) (integerp dmem0) (integerp a)
                       (integerp zero) (integerp mwval0)
                       (integerp emresult0) (booleanp deregwrite0)
                       (booleanp emregwrite0) (booleanp mwregwrite0)
                       (integerp mwdest0) (integerp deop0)
                       (integerp fddest0) (integerp dedest0)
                       (integerp op0) (integerp s0) (integerp a1)
                       (integerp a2) (integerp d0) (integerp d1)
                       (integerp x0) (integerp fdop0) (booleanp w0)
                       (booleanp w1) (integerp fdsrc10)
                       (integerp fdsrc20) (integerp emdest0)
                       (integerp emval0) (integerp desrc10)
                       (integerp desrc20) (integerp fdinst0)
                       (integerp deimm0) (booleanp deuseimm0)
                       (booleanp dememtoreg0) (booleanp emmemtoreg0)
                       (integerp emimm0) (booleanp emuseimm0)
                       (booleanp dememwrite0) (booleanp emmemwrite0)
                       (integerp emarg20) (integerp fdppc0)
                       (integerp deppc0) (integerp emppc0)
                       (integerp mwppc0))
                  (let* ((st0 (initialize_a nil nil nil nil pc0 nil pc0
                                  pc0 fdinst0 fdppc0 deppc0 desrc10
                                  desrc20 a1 a2 dedest0 deop0 deimm0
                                  deuseimm0 deregwrite0 dememwrite0
                                  dememtoreg0 emppc0 emarg20 emresult0
                                  emdest0 emregwrite0 emmemwrite0
                                  emmemtoreg0 dmem0 mwval0 mwppc0
                                  mwdest0 mwregwrite0))
                         (st1 (simulate_a st0 nil nil nil pc0 nil pc0
                                  pc0 fdinst0 fdppc0 deppc0 desrc10
                                  desrc20 a1 a2 dedest0 deop0 deimm0
                                  deuseimm0 deregwrite0 dememwrite0
                                  dememtoreg0 emppc0 emarg20 emresult0
                                  emdest0 emregwrite0 emmemwrite0
                                  emmemtoreg0 dmem0 mwval0 mwppc0
                                  mwdest0 mwregwrite0
                                  (g 'prf (g 'impl st0))
                                  (g 'pdmemhist_1 (g 'impl st0))))
                         (st2 (simulate_a st1 nil nil nil pc0 nil pc0
                                  pc0 fdinst0 fdppc0 deppc0 desrc10
                                  desrc20 a1 a2 dedest0 deop0 deimm0
                                  deuseimm0 deregwrite0 dememwrite0
                                  dememtoreg0 emppc0 emarg20 emresult0
                                  emdest0 emregwrite0 emmemwrite0
                                  emmemtoreg0 dmem0 mwval0 mwppc0
                                  mwdest0 mwregwrite0
                                  (g 'prf (g 'impl st1))
                                  (g 'pdmemhist_1 (g 'impl st1))))
                         (st3 (simulate_a st2 nil nil nil pc0 nil pc0
                                  pc0 fdinst0 fdppc0 deppc0 desrc10
                                  desrc20 a1 a2 dedest0 deop0 deimm0
                                  deuseimm0 deregwrite0 dememwrite0
                                  dememtoreg0 emppc0 emarg20 emresult0
                                  emdest0 emregwrite0 emmemwrite0
                                  emmemtoreg0 dmem0 mwval0 mwppc0
                                  mwdest0 mwregwrite0
                                  (g 'prf (g 'impl st2))
                                  (g 'pdmemhist_1 (g 'impl st2))))
                         (st4 (simulate_a st3 nil nil nil pc0 nil pc0
                                  pc0 fdinst0 fdppc0 deppc0 desrc10
                                  desrc20 a1 a2 dedest0 deop0 deimm0
                                  deuseimm0 deregwrite0 dememwrite0
                                  dememtoreg0 emppc0 emarg20 emresult0
                                  emdest0 emregwrite0 emmemwrite0
                                  emmemtoreg0 dmem0 mwval0 mwppc0
                                  mwdest0 mwregwrite0
                                  (g 'prf (g 'impl st3))
                                  (g 'pdmemhist_1 (g 'impl st3))))
                         (st5 (simulate_a st4 nil nil nil pc0 nil pc0
                                  pc0 fdinst0 fdppc0 deppc0 desrc10
                                  desrc20 a1 a2 dedest0 deop0 deimm0
                                  deuseimm0 deregwrite0 dememwrite0
                                  dememtoreg0 emppc0 emarg20 emresult0
                                  emdest0 emregwrite0 emmemwrite0
                                  emmemtoreg0 dmem0 mwval0 mwppc0
                                  mwdest0 mwregwrite0
                                  (g 'prf (g 'impl st4))
                                  (g 'pdmemhist_1 (g 'impl st4))))
                         (ppc_v (g 'ppc (g 'impl st5)))
                         (prf_v (g 'prf (g 'impl st5)))
                         (pdmem_v (g 'pdmem (g 'impl st5)))
                         (pimem_v (g 'pimem (g 'impl st5)))
                         (deop_v (g 'deop (g 'impl st5)))
                         (desrc2_v (g 'desrc2 (g 'impl st5)))
                         (dearg1_v (g 'dearg1 (g 'impl st5)))
                         (dearg2_v (g 'dearg2 (g 'impl st5)))
                         (dedest_v (g 'dedest (g 'impl st5)))
                         (dewrt_v (g 'dewrt (g 'impl st5)))
                         (mwval_v (g 'mwval (g 'impl st5)))
                         (mwdest_v (g 'mwdest (g 'impl st5)))
                         (mwwrt_v (g 'mwwrt (g 'impl st5)))
                         (fdwrt_v (g 'fdwrt (g 'impl st5)))
                         (fdinst_v (g 'fdinst (g 'impl st5)))
                         (emdest_v (g 'emdest (g 'impl st5)))
                         (emwrt_v (g 'emwrt (g 'impl st5)))
                         (desrc1_v (g 'desrc1 (g 'impl st5)))
                         (desrc2_v (g 'desrc2 (g 'impl st5)))
                         (deregwrite_v (g 'deregwrite (g 'impl st5)))
                         (emregwrite_v (g 'emregwrite (g 'impl st5)))
                         (mwregwrite_v (g 'mwregwrite (g 'impl st5)))
                         (deimm_v (g 'deimm (g 'impl st5)))
                         (deuseimm_v (g 'deuseimm (g 'impl st5)))
                         (emresult_v (g 'emresult (g 'impl st5)))
                         (dememtoreg_v (g 'dememtoreg (g 'impl st5)))
                         (emmemtoreg_v (g 'emmemtoreg (g 'impl st5)))
                         (dememwrite_v (g 'dememwrite (g 'impl st5)))
                         (emmemwrite_v (g 'emmemwrite (g 'impl st5)))
                         (emarg2_v (g 'emarg2 (g 'impl st5)))
                         (committedpc_0
                             (committedpc (g 'mwwrt (g 'impl st5))
                                 (g 'mwppc (g 'impl st5))
                                 (g 'emwrt (g 'impl st5))
                                 (g 'emppc (g 'impl st5))
                                 (g 'dewrt (g 'impl st5))
                                 (g 'deppc (g 'impl st5))
                                 (g 'fdwrt (g 'impl st5))
                                 (g 'fdppc (g 'impl st5))
                                 (g 'ppc (g 'impl st5))))
                         (st6 (simulate_a st5 nil nil nil pc0 t
                                  committedpc_0 pc0 fdinst0 fdppc0
                                  deppc0 desrc10 desrc20 a1 a2 dedest0
                                  deop0 deimm0 deuseimm0 deregwrite0
                                  dememwrite0 dememtoreg0 emppc0
                                  emarg20 emresult0 emdest0 emregwrite0
                                  emmemwrite0 emmemtoreg0 dmem0 mwval0
                                  mwppc0 mwdest0 mwregwrite0
                                  (g 'prf (g 'impl st5))
                                  (g 'pdmemhist_1 (g 'impl st5))))
                         (equiv_ma_0
                             (equiv_ma ppc_v (g 'ppc (g 'impl st6))
                                 prf_v a1 (g 'prf (g 'impl st6))
                                 pimem_v (g 'pimem (g 'impl st6))
                                 pdmem_v (g 'pdmem (g 'impl st6))
                                 fdwrt_v (g 'fdwrt (g 'impl st6))
                                 fdinst_v (g 'fdinst (g 'impl st6))
                                 dewrt_v (g 'dewrt (g 'impl st6))
                                 deop_v (g 'deop (g 'impl st6))
                                 dearg1_v (g 'dearg1 (g 'impl st6))
                                 dearg2_v (g 'dearg2 (g 'impl st6))
                                 dedest_v (g 'dedest (g 'impl st6))
                                 desrc1_v (g 'desrc1 (g 'impl st6))
                                 desrc2_v (g 'desrc2 (g 'impl st6))
                                 deimm_v (g 'deimm (g 'impl st6))
                                 deuseimm_v (g 'deuseimm (g 'impl st6))
                                 dememtoreg_v
                                 (g 'dememtoreg (g 'impl st6))
                                 dememwrite_v
                                 (g 'dememwrite (g 'impl st6))
                                 deregwrite_v
                                 (g 'deregwrite (g 'impl st6)) emwrt_v
                                 (g 'emwrt (g 'impl st6)) emdest_v
                                 (g 'emdest (g 'impl st6)) emregwrite_v
                                 (g 'emregwrite (g 'impl st6))
                                 emresult_v (g 'emresult (g 'impl st6))
                                 emmemtoreg_v
                                 (g 'emmemtoreg (g 'impl st6))
                                 emmemwrite_v
                                 (g 'emmemwrite (g 'impl st6)) mwwrt_v
                                 (g 'mwwrt (g 'impl st6)) mwval_v
                                 (g 'mwval (g 'impl st6)) mwdest_v
                                 (g 'mwdest (g 'impl st6)) mwregwrite_v
                                 (g 'mwregwrite (g 'impl st6))))
                         (st7 (simulate_a st6 nil nil nil pc0 nil pc0
                                  pc0 fdinst0 fdppc0 deppc0 desrc10
                                  desrc20 a1 a2 dedest0 deop0 deimm0
                                  deuseimm0 deregwrite0 dememwrite0
                                  dememtoreg0 emppc0 emarg20 emresult0
                                  emdest0 emregwrite0 emmemwrite0
                                  emmemtoreg0 dmem0 mwval0 mwppc0
                                  mwdest0 mwregwrite0
                                  (g 'prf (g 'impl st6))
                                  (g 'pdmemhist_1 (g 'impl st6))))
                         (equiv_ma_1
                             (equiv_ma ppc_v (g 'ppc (g 'impl st7))
                                 prf_v a1 (g 'prf (g 'impl st7))
                                 pimem_v (g 'pimem (g 'impl st7))
                                 pdmem_v (g 'pdmem (g 'impl st7))
                                 fdwrt_v (g 'fdwrt (g 'impl st7))
                                 fdinst_v (g 'fdinst (g 'impl st7))
                                 dewrt_v (g 'dewrt (g 'impl st7))
                                 deop_v (g 'deop (g 'impl st7))
                                 dearg1_v (g 'dearg1 (g 'impl st7))
                                 dearg2_v (g 'dearg2 (g 'impl st7))
                                 dedest_v (g 'dedest (g 'impl st7))
                                 desrc1_v (g 'desrc1 (g 'impl st7))
                                 desrc2_v (g 'desrc2 (g 'impl st7))
                                 deimm_v (g 'deimm (g 'impl st7))
                                 deuseimm_v (g 'deuseimm (g 'impl st7))
                                 dememtoreg_v
                                 (g 'dememtoreg (g 'impl st7))
                                 dememwrite_v
                                 (g 'dememwrite (g 'impl st7))
                                 deregwrite_v
                                 (g 'deregwrite (g 'impl st7)) emwrt_v
                                 (g 'emwrt (g 'impl st7)) emdest_v
                                 (g 'emdest (g 'impl st7)) emregwrite_v
                                 (g 'emregwrite (g 'impl st7))
                                 emresult_v (g 'emresult (g 'impl st7))
                                 emmemtoreg_v
                                 (g 'emmemtoreg (g 'impl st7))
                                 emmemwrite_v
                                 (g 'emmemwrite (g 'impl st7)) mwwrt_v
                                 (g 'mwwrt (g 'impl st7)) mwval_v
                                 (g 'mwval (g 'impl st7)) mwdest_v
                                 (g 'mwdest (g 'impl st7)) mwregwrite_v
                                 (g 'mwregwrite (g 'impl st7))))
                         (st8 (simulate_a st7 nil nil nil pc0 nil pc0
                                  pc0 fdinst0 fdppc0 deppc0 desrc10
                                  desrc20 a1 a2 dedest0 deop0 deimm0
                                  deuseimm0 deregwrite0 dememwrite0
                                  dememtoreg0 emppc0 emarg20 emresult0
                                  emdest0 emregwrite0 emmemwrite0
                                  emmemtoreg0 dmem0 mwval0 mwppc0
                                  mwdest0 mwregwrite0
                                  (g 'prf (g 'impl st7))
                                  (g 'pdmemhist_1 (g 'impl st7))))
                         (equiv_ma_2
                             (equiv_ma ppc_v (g 'ppc (g 'impl st8))
                                 prf_v a1 (g 'prf (g 'impl st8))
                                 pimem_v (g 'pimem (g 'impl st8))
                                 pdmem_v (g 'pdmem (g 'impl st8))
                                 fdwrt_v (g 'fdwrt (g 'impl st8))
                                 fdinst_v (g 'fdinst (g 'impl st8))
                                 dewrt_v (g 'dewrt (g 'impl st8))
                                 deop_v (g 'deop (g 'impl st8))
                                 dearg1_v (g 'dearg1 (g 'impl st8))
                                 dearg2_v (g 'dearg2 (g 'impl st8))
                                 dedest_v (g 'dedest (g 'impl st8))
                                 desrc1_v (g 'desrc1 (g 'impl st8))
                                 desrc2_v (g 'desrc2 (g 'impl st8))
                                 deimm_v (g 'deimm (g 'impl st8))
                                 deuseimm_v (g 'deuseimm (g 'impl st8))
                                 dememtoreg_v
                                 (g 'dememtoreg (g 'impl st8))
                                 dememwrite_v
                                 (g 'dememwrite (g 'impl st8))
                                 deregwrite_v
                                 (g 'deregwrite (g 'impl st8)) emwrt_v
                                 (g 'emwrt (g 'impl st8)) emdest_v
                                 (g 'emdest (g 'impl st8)) emregwrite_v
                                 (g 'emregwrite (g 'impl st8))
                                 emresult_v (g 'emresult (g 'impl st8))
                                 emmemtoreg_v
                                 (g 'emmemtoreg (g 'impl st8))
                                 emmemwrite_v
                                 (g 'emmemwrite (g 'impl st8)) mwwrt_v
                                 (g 'mwwrt (g 'impl st8)) mwval_v
                                 (g 'mwval (g 'impl st8)) mwdest_v
                                 (g 'mwdest (g 'impl st8)) mwregwrite_v
                                 (g 'mwregwrite (g 'impl st8))))
                         (st9 (simulate_a st8 nil nil nil pc0 nil pc0
                                  pc0 fdinst0 fdppc0 deppc0 desrc10
                                  desrc20 a1 a2 dedest0 deop0 deimm0
                                  deuseimm0 deregwrite0 dememwrite0
                                  dememtoreg0 emppc0 emarg20 emresult0
                                  emdest0 emregwrite0 emmemwrite0
                                  emmemtoreg0 dmem0 mwval0 mwppc0
                                  mwdest0 mwregwrite0
                                  (g 'prf (g 'impl st8))
                                  (g 'pdmemhist_1 (g 'impl st8))))
                         (equiv_ma_3
                             (equiv_ma ppc_v (g 'ppc (g 'impl st9))
                                 prf_v a1 (g 'prf (g 'impl st9))
                                 pimem_v (g 'pimem (g 'impl st9))
                                 pdmem_v (g 'pdmem (g 'impl st9))
                                 fdwrt_v (g 'fdwrt (g 'impl st9))
                                 fdinst_v (g 'fdinst (g 'impl st9))
                                 dewrt_v (g 'dewrt (g 'impl st9))
                                 deop_v (g 'deop (g 'impl st9))
                                 dearg1_v (g 'dearg1 (g 'impl st9))
                                 dearg2_v (g 'dearg2 (g 'impl st9))
                                 dedest_v (g 'dedest (g 'impl st9))
                                 desrc1_v (g 'desrc1 (g 'impl st9))
                                 desrc2_v (g 'desrc2 (g 'impl st9))
                                 deimm_v (g 'deimm (g 'impl st9))
                                 deuseimm_v (g 'deuseimm (g 'impl st9))
                                 dememtoreg_v
                                 (g 'dememtoreg (g 'impl st9))
                                 dememwrite_v
                                 (g 'dememwrite (g 'impl st9))
                                 deregwrite_v
                                 (g 'deregwrite (g 'impl st9)) emwrt_v
                                 (g 'emwrt (g 'impl st9)) emdest_v
                                 (g 'emdest (g 'impl st9)) emregwrite_v
                                 (g 'emregwrite (g 'impl st9))
                                 emresult_v (g 'emresult (g 'impl st9))
                                 emmemtoreg_v
                                 (g 'emmemtoreg (g 'impl st9))
                                 emmemwrite_v
                                 (g 'emmemwrite (g 'impl st9)) mwwrt_v
                                 (g 'mwwrt (g 'impl st9)) mwval_v
                                 (g 'mwval (g 'impl st9)) mwdest_v
                                 (g 'mwdest (g 'impl st9)) mwregwrite_v
                                 (g 'mwregwrite (g 'impl st9))))
                         (st10 (simulate_a st9 nil nil nil pc0 nil pc0
                                   pc0 fdinst0 fdppc0 deppc0 desrc10
                                   desrc20 a1 a2 dedest0 deop0 deimm0
                                   deuseimm0 deregwrite0 dememwrite0
                                   dememtoreg0 emppc0 emarg20 emresult0
                                   emdest0 emregwrite0 emmemwrite0
                                   emmemtoreg0 dmem0 mwval0 mwppc0
                                   mwdest0 mwregwrite0
                                   (g 'prf (g 'impl st9))
                                   (g 'pdmemhist_1 (g 'impl st9))))
                         (equiv_ma_4
                             (equiv_ma ppc_v (g 'ppc (g 'impl st10))
                                 prf_v a1 (g 'prf (g 'impl st10))
                                 pimem_v (g 'pimem (g 'impl st10))
                                 pdmem_v (g 'pdmem (g 'impl st10))
                                 fdwrt_v (g 'fdwrt (g 'impl st10))
                                 fdinst_v (g 'fdinst (g 'impl st10))
                                 dewrt_v (g 'dewrt (g 'impl st10))
                                 deop_v (g 'deop (g 'impl st10))
                                 dearg1_v (g 'dearg1 (g 'impl st10))
                                 dearg2_v (g 'dearg2 (g 'impl st10))
                                 dedest_v (g 'dedest (g 'impl st10))
                                 desrc1_v (g 'desrc1 (g 'impl st10))
                                 desrc2_v (g 'desrc2 (g 'impl st10))
                                 deimm_v (g 'deimm (g 'impl st10))
                                 deuseimm_v
                                 (g 'deuseimm (g 'impl st10))
                                 dememtoreg_v
                                 (g 'dememtoreg (g 'impl st10))
                                 dememwrite_v
                                 (g 'dememwrite (g 'impl st10))
                                 deregwrite_v
                                 (g 'deregwrite (g 'impl st10)) emwrt_v
                                 (g 'emwrt (g 'impl st10)) emdest_v
                                 (g 'emdest (g 'impl st10))
                                 emregwrite_v
                                 (g 'emregwrite (g 'impl st10))
                                 emresult_v
                                 (g 'emresult (g 'impl st10))
                                 emmemtoreg_v
                                 (g 'emmemtoreg (g 'impl st10))
                                 emmemwrite_v
                                 (g 'emmemwrite (g 'impl st10)) mwwrt_v
                                 (g 'mwwrt (g 'impl st10)) mwval_v
                                 (g 'mwval (g 'impl st10)) mwdest_v
                                 (g 'mwdest (g 'impl st10))
                                 mwregwrite_v
                                 (g 'mwregwrite (g 'impl st10))))
                         (good_ma_v
                             (or (or (or (or equiv_ma_0 equiv_ma_1)
                                      equiv_ma_2)
                                     equiv_ma_3)
                                 equiv_ma_4))
                         (st11 (simulate_a st10 t nil nil pc0 nil pc0
                                   pc0 fdinst0 fdppc0 deppc0 desrc10
                                   desrc20 a1 a2 dedest0 deop0 deimm0
                                   deuseimm0 deregwrite0 dememwrite0
                                   dememtoreg0 emppc0 emarg20 emresult0
                                   emdest0 emregwrite0 emmemwrite0
                                   emmemtoreg0 dmem0 mwval0 mwppc0
                                   mwdest0 mwregwrite0
                                   (g 'prf (g 'impl st10))
                                   (g 'pdmemhist_1 (g 'impl st10))))
                         (st12 (simulate_a st11 nil nil nil pc0 nil pc0
                                   pc0 fdinst0 fdppc0 deppc0 desrc10
                                   desrc20 a1 a2 dedest0 deop0 deimm0
                                   deuseimm0 deregwrite0 dememwrite0
                                   dememtoreg0 emppc0 emarg20 emresult0
                                   emdest0 emregwrite0 emmemwrite0
                                   emmemtoreg0 dmem0 mwval0 mwppc0
                                   mwdest0 mwregwrite0
                                   (g 'prf (g 'impl st11))
                                   (g 'pdmemhist_1 (g 'impl st11))))
                         (st13 (simulate_a st12 nil nil nil pc0 nil pc0
                                   pc0 fdinst0 fdppc0 deppc0 desrc10
                                   desrc20 a1 a2 dedest0 deop0 deimm0
                                   deuseimm0 deregwrite0 dememwrite0
                                   dememtoreg0 emppc0 emarg20 emresult0
                                   emdest0 emregwrite0 emmemwrite0
                                   emmemtoreg0 dmem0 mwval0 mwppc0
                                   mwdest0 mwregwrite0
                                   (g 'prf (g 'impl st12))
                                   (g 'pdmemhist_1 (g 'impl st12))))
                         (st14 (simulate_a st13 nil nil nil pc0 nil pc0
                                   pc0 fdinst0 fdppc0 deppc0 desrc10
                                   desrc20 a1 a2 dedest0 deop0 deimm0
                                   deuseimm0 deregwrite0 dememwrite0
                                   dememtoreg0 emppc0 emarg20 emresult0
                                   emdest0 emregwrite0 emmemwrite0
                                   emmemtoreg0 dmem0 mwval0 mwppc0
                                   mwdest0 mwregwrite0
                                   (g 'prf (g 'impl st13))
                                   (g 'pdmemhist_1 (g 'impl st13))))
                         (st15 (simulate_a st14 nil nil nil pc0 nil pc0
                                   pc0 fdinst0 fdppc0 deppc0 desrc10
                                   desrc20 a1 a2 dedest0 deop0 deimm0
                                   deuseimm0 deregwrite0 dememwrite0
                                   dememtoreg0 emppc0 emarg20 emresult0
                                   emdest0 emregwrite0 emmemwrite0
                                   emmemtoreg0 dmem0 mwval0 mwppc0
                                   mwdest0 mwregwrite0
                                   (g 'prf (g 'impl st14))
                                   (g 'pdmemhist_1 (g 'impl st14))))
                         (i_pc0 (committedpc (g 'mwwrt (g 'impl st15))
                                    (g 'mwppc (g 'impl st15))
                                    (g 'emwrt (g 'impl st15))
                                    (g 'emppc (g 'impl st15))
                                    (g 'dewrt (g 'impl st15))
                                    (g 'deppc (g 'impl st15))
                                    (g 'fdwrt (g 'impl st15))
                                    (g 'fdppc (g 'impl st15))
                                    (g 'ppc (g 'impl st15))))
                         (i_rf0 (g 'prf (g 'impl st15)))
                         (i_dmem0 (g 'pdmemhist_1 (g 'impl st15)))
                         (rank_w (rank (g 'mwwrt (g 'impl st15)) zero
                                       (g 'emwrt (g 'impl st15))
                                       (g 'dewrt (g 'impl st15))
                                       (g 'fdwrt (g 'impl st15))))
                         (st16 (simulate_a st15 nil nil t i_pc0 nil pc0
                                   pc0 fdinst0 fdppc0 deppc0 desrc10
                                   desrc20 a1 a2 dedest0 deop0 deimm0
                                   deuseimm0 deregwrite0 dememwrite0
                                   dememtoreg0 emppc0 emarg20 emresult0
                                   emdest0 emregwrite0 emmemwrite0
                                   emmemtoreg0 dmem0 mwval0 mwppc0
                                   mwdest0 mwregwrite0
                                   (g 'prf (g 'impl st15))
                                   (g 'pdmemhist_1 (g 'impl st15))))
                         (s_pc0 (g 'spc (g 'spec st16)))
                         (s_rf0 (g 'srf (g 'spec st16)))
                         (s_dmem0 (g 'sdmem (g 'spec st16)))
                         (i_pc (committedpc (g 'mwwrt (g 'impl st16))
                                   (g 'mwppc (g 'impl st16))
                                   (g 'emwrt (g 'impl st16))
                                   (g 'emppc (g 'impl st16))
                                   (g 'dewrt (g 'impl st16))
                                   (g 'deppc (g 'impl st16))
                                   (g 'fdwrt (g 'impl st16))
                                   (g 'fdppc (g 'impl st16))
                                   (g 'ppc (g 'impl st16))))
                         (i_rf (g 'prf (g 'impl st16)))
                         (i_dmem (g 'pdmemhist_1 (g 'impl st16)))
                         (rank_v (rank (g 'mwwrt (g 'impl st16)) zero
                                       (g 'emwrt (g 'impl st16))
                                       (g 'dewrt (g 'impl st16))
                                       (g 'fdwrt (g 'impl st16))))
                         (st17 (simulate_a st16 nil t nil pc0 nil pc0
                                   pc0 fdinst0 fdppc0 deppc0 desrc10
                                   desrc20 a1 a2 dedest0 deop0 deimm0
                                   deuseimm0 deregwrite0 dememwrite0
                                   dememtoreg0 emppc0 emarg20 emresult0
                                   emdest0 emregwrite0 emmemwrite0
                                   emmemtoreg0 dmem0 mwval0 mwppc0
                                   mwdest0 mwregwrite0
                                   (g 'prf (g 'impl st16))
                                   (g 'pdmemhist_1 (g 'impl st16))))
                         (s_pc1 (g 'spc (g 'spec st17)))
                         (s_rf1 (g 'srf (g 'spec st17)))
                         (s_dmem1 (g 'sdmem (g 'spec st17)))
                         (st18 (simulate_a st17 t nil nil pc0 nil pc0
                                   pc0 fdinst0 fdppc0 deppc0 desrc10
                                   desrc20 a1 a2 dedest0 deop0 deimm0
                                   deuseimm0 deregwrite0 dememwrite0
                                   dememtoreg0 emppc0 emarg20 emresult0
                                   emdest0 emregwrite0 emmemwrite0
                                   emmemtoreg0 dmem0 mwval0 mwppc0
                                   mwdest0 mwregwrite0
                                   (g 'prf (g 'impl st17))
                                   (g 'pdmemhist_1 (g 'impl st17))))
                         (st19 (simulate_a st18 nil nil nil pc0 nil pc0
                                   pc0 fdinst0 fdppc0 deppc0 desrc10
                                   desrc20 a1 a2 dedest0 deop0 deimm0
                                   deuseimm0 deregwrite0 dememwrite0
                                   dememtoreg0 emppc0 emarg20 emresult0
                                   emdest0 emregwrite0 emmemwrite0
                                   emmemtoreg0 dmem0 mwval0 mwppc0
                                   mwdest0 mwregwrite0
                                   (g 'prf (g 'impl st18))
                                   (g 'pdmemhist_1 (g 'impl st18))))
                         (st20 (simulate_a st19 nil nil nil pc0 nil pc0
                                   pc0 fdinst0 fdppc0 deppc0 desrc10
                                   desrc20 a1 a2 dedest0 deop0 deimm0
                                   deuseimm0 deregwrite0 dememwrite0
                                   dememtoreg0 emppc0 emarg20 emresult0
                                   emdest0 emregwrite0 emmemwrite0
                                   emmemtoreg0 dmem0 mwval0 mwppc0
                                   mwdest0 mwregwrite0
                                   (g 'prf (g 'impl st19))
                                   (g 'pdmemhist_1 (g 'impl st19))))
                         (st21 (simulate_a st20 nil nil nil pc0 nil pc0
                                   pc0 fdinst0 fdppc0 deppc0 desrc10
                                   desrc20 a1 a2 dedest0 deop0 deimm0
                                   deuseimm0 deregwrite0 dememwrite0
                                   dememtoreg0 emppc0 emarg20 emresult0
                                   emdest0 emregwrite0 emmemwrite0
                                   emmemtoreg0 dmem0 mwval0 mwppc0
                                   mwdest0 mwregwrite0
                                   (g 'prf (g 'impl st20))
                                   (g 'pdmemhist_1 (g 'impl st20))))
                         (i_pc0_2 (committedpc
                                      (g 'mwwrt (g 'impl st21))
                                      (g 'mwppc (g 'impl st21))
                                      (g 'emwrt (g 'impl st21))
                                      (g 'emppc (g 'impl st21))
                                      (g 'dewrt (g 'impl st21))
                                      (g 'deppc (g 'impl st21))
                                      (g 'fdwrt (g 'impl st21))
                                      (g 'fdppc (g 'impl st21))
                                      (g 'ppc (g 'impl st21))))
                         (i_rf0_2 (g 'prf (g 'impl st21)))
                         (i_dmem0_2 (g 'pdmemhist_1 (g 'impl st21)))
                         (rank_w_2
                             (rank (g 'mwwrt (g 'impl st21)) zero
                                   (g 'emwrt (g 'impl st21))
                                   (g 'dewrt (g 'impl st21))
                                   (g 'fdwrt (g 'impl st21))))
                         (st22 (simulate_a st21 nil nil t i_pc0_2 nil
                                   pc0 pc0 fdinst0 fdppc0 deppc0
                                   desrc10 desrc20 a1 a2 dedest0 deop0
                                   deimm0 deuseimm0 deregwrite0
                                   dememwrite0 dememtoreg0 emppc0
                                   emarg20 emresult0 emdest0
                                   emregwrite0 emmemwrite0 emmemtoreg0
                                   dmem0 mwval0 mwppc0 mwdest0
                                   mwregwrite0 (g 'prf (g 'impl st21))
                                   (g 'pdmemhist_1 (g 'impl st21))))
                         (s_pc0_2 (g 'spc (g 'spec st22)))
                         (s_rf0_2 (g 'srf (g 'spec st22)))
                         (s_dmem0_2 (g 'sdmem (g 'spec st22)))
                         (i_pc_2 (committedpc (g 'mwwrt (g 'impl st22))
                                     (g 'mwppc (g 'impl st22))
                                     (g 'emwrt (g 'impl st22))
                                     (g 'emppc (g 'impl st22))
                                     (g 'dewrt (g 'impl st22))
                                     (g 'deppc (g 'impl st22))
                                     (g 'fdwrt (g 'impl st22))
                                     (g 'fdppc (g 'impl st22))
                                     (g 'ppc (g 'impl st22))))
                         (i_rf_2 (g 'prf (g 'impl st22)))
                         (i_dmem_2 (g 'pdmemhist_1 (g 'impl st22)))
                         (rank_v_2
                             (rank (g 'mwwrt (g 'impl st22)) zero
                                   (g 'emwrt (g 'impl st22))
                                   (g 'dewrt (g 'impl st22))
                                   (g 'fdwrt (g 'impl st22))))
                         (st23 (simulate_a st22 nil t nil pc0 nil pc0
                                   pc0 fdinst0 fdppc0 deppc0 desrc10
                                   desrc20 a1 a2 dedest0 deop0 deimm0
                                   deuseimm0 deregwrite0 dememwrite0
                                   dememtoreg0 emppc0 emarg20 emresult0
                                   emdest0 emregwrite0 emmemwrite0
                                   emmemtoreg0 dmem0 mwval0 mwppc0
                                   mwdest0 mwregwrite0
                                   (g 'prf (g 'impl st22))
                                   (g 'pdmemhist_1 (g 'impl st22))))
                         (s_pc1_2 (g 'spc (g 'spec st23)))
                         (s_rf1_2 (g 'srf (g 'spec st23)))
                         (s_dmem1_2 (g 'sdmem (g 'spec st23)))
                         (st24 (simulate_a st23 t nil nil pc0 nil pc0
                                   pc0 fdinst0 fdppc0 deppc0 desrc10
                                   desrc20 a1 a2 dedest0 deop0 deimm0
                                   deuseimm0 deregwrite0 dememwrite0
                                   dememtoreg0 emppc0 emarg20 emresult0
                                   emdest0 emregwrite0 emmemwrite0
                                   emmemtoreg0 dmem0 mwval0 mwppc0
                                   mwdest0 mwregwrite0
                                   (g 'prf (g 'impl st23))
                                   (g 'pdmemhist_1 (g 'impl st23))))
                         (st25 (simulate_a st24 nil nil nil pc0 nil pc0
                                   pc0 fdinst0 fdppc0 deppc0 desrc10
                                   desrc20 a1 a2 dedest0 deop0 deimm0
                                   deuseimm0 deregwrite0 dememwrite0
                                   dememtoreg0 emppc0 emarg20 emresult0
                                   emdest0 emregwrite0 emmemwrite0
                                   emmemtoreg0 dmem0 mwval0 mwppc0
                                   mwdest0 mwregwrite0
                                   (g 'prf (g 'impl st24))
                                   (g 'pdmemhist_1 (g 'impl st24))))
                         (st26 (simulate_a st25 nil nil nil pc0 nil pc0
                                   pc0 fdinst0 fdppc0 deppc0 desrc10
                                   desrc20 a1 a2 dedest0 deop0 deimm0
                                   deuseimm0 deregwrite0 dememwrite0
                                   dememtoreg0 emppc0 emarg20 emresult0
                                   emdest0 emregwrite0 emmemwrite0
                                   emmemtoreg0 dmem0 mwval0 mwppc0
                                   mwdest0 mwregwrite0
                                   (g 'prf (g 'impl st25))
                                   (g 'pdmemhist_1 (g 'impl st25))))
                         (i_pc0_3 (committedpc
                                      (g 'mwwrt (g 'impl st26))
                                      (g 'mwppc (g 'impl st26))
                                      (g 'emwrt (g 'impl st26))
                                      (g 'emppc (g 'impl st26))
                                      (g 'dewrt (g 'impl st26))
                                      (g 'deppc (g 'impl st26))
                                      (g 'fdwrt (g 'impl st26))
                                      (g 'fdppc (g 'impl st26))
                                      (g 'ppc (g 'impl st26))))
                         (i_rf0_3 (g 'prf (g 'impl st26)))
                         (i_dmem0_3 (g 'pdmemhist_1 (g 'impl st26)))
                         (rank_w_3
                             (rank (g 'mwwrt (g 'impl st26)) zero
                                   (g 'emwrt (g 'impl st26))
                                   (g 'dewrt (g 'impl st26))
                                   (g 'fdwrt (g 'impl st26))))
                         (st27 (simulate_a st26 nil nil t i_pc0_3 nil
                                   pc0 pc0 fdinst0 fdppc0 deppc0
                                   desrc10 desrc20 a1 a2 dedest0 deop0
                                   deimm0 deuseimm0 deregwrite0
                                   dememwrite0 dememtoreg0 emppc0
                                   emarg20 emresult0 emdest0
                                   emregwrite0 emmemwrite0 emmemtoreg0
                                   dmem0 mwval0 mwppc0 mwdest0
                                   mwregwrite0 (g 'prf (g 'impl st26))
                                   (g 'pdmemhist_1 (g 'impl st26))))
                         (s_pc0_3 (g 'spc (g 'spec st27)))
                         (s_rf0_3 (g 'srf (g 'spec st27)))
                         (s_dmem0_3 (g 'sdmem (g 'spec st27)))
                         (i_pc_3 (committedpc (g 'mwwrt (g 'impl st27))
                                     (g 'mwppc (g 'impl st27))
                                     (g 'emwrt (g 'impl st27))
                                     (g 'emppc (g 'impl st27))
                                     (g 'dewrt (g 'impl st27))
                                     (g 'deppc (g 'impl st27))
                                     (g 'fdwrt (g 'impl st27))
                                     (g 'fdppc (g 'impl st27))
                                     (g 'ppc (g 'impl st27))))
                         (i_rf_3 (g 'prf (g 'impl st27)))
                         (i_dmem_3 (g 'pdmemhist_1 (g 'impl st27)))
                         (rank_v_3
                             (rank (g 'mwwrt (g 'impl st27)) zero
                                   (g 'emwrt (g 'impl st27))
                                   (g 'dewrt (g 'impl st27))
                                   (g 'fdwrt (g 'impl st27))))
                         (st28 (simulate_a st27 nil t nil pc0 nil pc0
                                   pc0 fdinst0 fdppc0 deppc0 desrc10
                                   desrc20 a1 a2 dedest0 deop0 deimm0
                                   deuseimm0 deregwrite0 dememwrite0
                                   dememtoreg0 emppc0 emarg20 emresult0
                                   emdest0 emregwrite0 emmemwrite0
                                   emmemtoreg0 dmem0 mwval0 mwppc0
                                   mwdest0 mwregwrite0
                                   (g 'prf (g 'impl st27))
                                   (g 'pdmemhist_1 (g 'impl st27))))
                         (s_pc1_3 (g 'spc (g 'spec st28)))
                         (s_rf1_3 (g 'srf (g 'spec st28)))
                         (s_dmem1_3 (g 'sdmem (g 'spec st28)))
                         (st29 (simulate_a st28 t nil nil pc0 nil pc0
                                   pc0 fdinst0 fdppc0 deppc0 desrc10
                                   desrc20 a1 a2 dedest0 deop0 deimm0
                                   deuseimm0 deregwrite0 dememwrite0
                                   dememtoreg0 emppc0 emarg20 emresult0
                                   emdest0 emregwrite0 emmemwrite0
                                   emmemtoreg0 dmem0 mwval0 mwppc0
                                   mwdest0 mwregwrite0
                                   (g 'prf (g 'impl st28))
                                   (g 'pdmemhist_1 (g 'impl st28))))
                         (st30 (simulate_a st29 nil nil nil pc0 nil pc0
                                   pc0 fdinst0 fdppc0 deppc0 desrc10
                                   desrc20 a1 a2 dedest0 deop0 deimm0
                                   deuseimm0 deregwrite0 dememwrite0
                                   dememtoreg0 emppc0 emarg20 emresult0
                                   emdest0 emregwrite0 emmemwrite0
                                   emmemtoreg0 dmem0 mwval0 mwppc0
                                   mwdest0 mwregwrite0
                                   (g 'prf (g 'impl st29))
                                   (g 'pdmemhist_1 (g 'impl st29))))
                         (i_pc0_4 (committedpc
                                      (g 'mwwrt (g 'impl st30))
                                      (g 'mwppc (g 'impl st30))
                                      (g 'emwrt (g 'impl st30))
                                      (g 'emppc (g 'impl st30))
                                      (g 'dewrt (g 'impl st30))
                                      (g 'deppc (g 'impl st30))
                                      (g 'fdwrt (g 'impl st30))
                                      (g 'fdppc (g 'impl st30))
                                      (g 'ppc (g 'impl st30))))
                         (i_rf0_4 (g 'prf (g 'impl st30)))
                         (i_dmem0_4 (g 'pdmemhist_1 (g 'impl st30)))
                         (rank_w_4
                             (rank (g 'mwwrt (g 'impl st30)) zero
                                   (g 'emwrt (g 'impl st30))
                                   (g 'dewrt (g 'impl st30))
                                   (g 'fdwrt (g 'impl st30))))
                         (st31 (simulate_a st30 nil nil t i_pc0_4 nil
                                   pc0 pc0 fdinst0 fdppc0 deppc0
                                   desrc10 desrc20 a1 a2 dedest0 deop0
                                   deimm0 deuseimm0 deregwrite0
                                   dememwrite0 dememtoreg0 emppc0
                                   emarg20 emresult0 emdest0
                                   emregwrite0 emmemwrite0 emmemtoreg0
                                   dmem0 mwval0 mwppc0 mwdest0
                                   mwregwrite0 (g 'prf (g 'impl st30))
                                   (g 'pdmemhist_1 (g 'impl st30))))
                         (s_pc0_4 (g 'spc (g 'spec st31)))
                         (s_rf0_4 (g 'srf (g 'spec st31)))
                         (s_dmem0_4 (g 'sdmem (g 'spec st31)))
                         (i_pc_4 (committedpc (g 'mwwrt (g 'impl st31))
                                     (g 'mwppc (g 'impl st31))
                                     (g 'emwrt (g 'impl st31))
                                     (g 'emppc (g 'impl st31))
                                     (g 'dewrt (g 'impl st31))
                                     (g 'deppc (g 'impl st31))
                                     (g 'fdwrt (g 'impl st31))
                                     (g 'fdppc (g 'impl st31))
                                     (g 'ppc (g 'impl st31))))
                         (i_rf_4 (g 'prf (g 'impl st31)))
                         (i_dmem_4 (g 'pdmemhist_1 (g 'impl st31)))
                         (rank_v_4
                             (rank (g 'mwwrt (g 'impl st31)) zero
                                   (g 'emwrt (g 'impl st31))
                                   (g 'dewrt (g 'impl st31))
                                   (g 'fdwrt (g 'impl st31))))
                         (st32 (simulate_a st31 nil t nil pc0 nil pc0
                                   pc0 fdinst0 fdppc0 deppc0 desrc10
                                   desrc20 a1 a2 dedest0 deop0 deimm0
                                   deuseimm0 deregwrite0 dememwrite0
                                   dememtoreg0 emppc0 emarg20 emresult0
                                   emdest0 emregwrite0 emmemwrite0
                                   emmemtoreg0 dmem0 mwval0 mwppc0
                                   mwdest0 mwregwrite0
                                   (g 'prf (g 'impl st31))
                                   (g 'pdmemhist_1 (g 'impl st31))))
                         (s_pc1_4 (g 'spc (g 'spec st32)))
                         (s_rf1_4 (g 'srf (g 'spec st32)))
                         (s_dmem1_4 (g 'sdmem (g 'spec st32)))
                         (st33 (simulate_a st32 t nil nil pc0 nil pc0
                                   pc0 fdinst0 fdppc0 deppc0 desrc10
                                   desrc20 a1 a2 dedest0 deop0 deimm0
                                   deuseimm0 deregwrite0 dememwrite0
                                   dememtoreg0 emppc0 emarg20 emresult0
                                   emdest0 emregwrite0 emmemwrite0
                                   emmemtoreg0 dmem0 mwval0 mwppc0
                                   mwdest0 mwregwrite0
                                   (g 'prf (g 'impl st32))
                                   (g 'pdmemhist_1 (g 'impl st32))))
                         (i_pc0_5 (committedpc
                                      (g 'mwwrt (g 'impl st33))
                                      (g 'mwppc (g 'impl st33))
                                      (g 'emwrt (g 'impl st33))
                                      (g 'emppc (g 'impl st33))
                                      (g 'dewrt (g 'impl st33))
                                      (g 'deppc (g 'impl st33))
                                      (g 'fdwrt (g 'impl st33))
                                      (g 'fdppc (g 'impl st33))
                                      (g 'ppc (g 'impl st33))))
                         (i_rf0_5 (g 'prf (g 'impl st33)))
                         (i_dmem0_5 (g 'pdmemhist_1 (g 'impl st33)))
                         (rank_w_5
                             (rank (g 'mwwrt (g 'impl st33)) zero
                                   (g 'emwrt (g 'impl st33))
                                   (g 'dewrt (g 'impl st33))
                                   (g 'fdwrt (g 'impl st33))))
                         (st34 (simulate_a st33 nil nil t i_pc0_5 nil
                                   pc0 pc0 fdinst0 fdppc0 deppc0
                                   desrc10 desrc20 a1 a2 dedest0 deop0
                                   deimm0 deuseimm0 deregwrite0
                                   dememwrite0 dememtoreg0 emppc0
                                   emarg20 emresult0 emdest0
                                   emregwrite0 emmemwrite0 emmemtoreg0
                                   dmem0 mwval0 mwppc0 mwdest0
                                   mwregwrite0 (g 'prf (g 'impl st33))
                                   (g 'pdmemhist_1 (g 'impl st33))))
                         (s_pc0_5 (g 'spc (g 'spec st34)))
                         (s_rf0_5 (g 'srf (g 'spec st34)))
                         (s_dmem0_5 (g 'sdmem (g 'spec st34)))
                         (i_pc_5 (committedpc (g 'mwwrt (g 'impl st34))
                                     (g 'mwppc (g 'impl st34))
                                     (g 'emwrt (g 'impl st34))
                                     (g 'emppc (g 'impl st34))
                                     (g 'dewrt (g 'impl st34))
                                     (g 'deppc (g 'impl st34))
                                     (g 'fdwrt (g 'impl st34))
                                     (g 'fdppc (g 'impl st34))
                                     (g 'ppc (g 'impl st34))))
                         (i_rf_5 (g 'prf (g 'impl st34)))
                         (i_dmem_5 (g 'pdmemhist_1 (g 'impl st34)))
                         (rank_v_5
                             (rank (g 'mwwrt (g 'impl st34)) zero
                                   (g 'emwrt (g 'impl st34))
                                   (g 'dewrt (g 'impl st34))
                                   (g 'fdwrt (g 'impl st34))))
                         (st35 (simulate_a st34 nil t nil pc0 nil pc0
                                   pc0 fdinst0 fdppc0 deppc0 desrc10
                                   desrc20 a1 a2 dedest0 deop0 deimm0
                                   deuseimm0 deregwrite0 dememwrite0
                                   dememtoreg0 emppc0 emarg20 emresult0
                                   emdest0 emregwrite0 emmemwrite0
                                   emmemtoreg0 dmem0 mwval0 mwppc0
                                   mwdest0 mwregwrite0
                                   (g 'prf (g 'impl st34))
                                   (g 'pdmemhist_1 (g 'impl st34))))
                         (s_pc1_5 (g 'spc (g 'spec st35)))
                         (s_rf1_5 (g 'srf (g 'spec st35)))
                         (s_dmem1_5 (g 'sdmem (g 'spec st35))))
                    (and (and (and (and
                                    (and good_ma_v
                                     (or
                                      (or
                                       (not
                                        (and
                                         (and (equal s_pc0 i_pc0)
                                          (equal (read-srf_a a1 s_rf0)
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
                                         (equal (read-srf_a a1 s_rf0_2)
                                          (read-prf_a a1 i_rf0_2)))
                                        (equal s_dmem0_2 i_dmem0_2)))
                                      (and
                                       (and (equal s_pc1_2 i_pc_2)
                                        (equal (read-srf_a a1 s_rf1_2)
                                         (read-prf_a a1 i_rf_2)))
                                       (equal s_dmem1_2 i_dmem_2)))
                                     (and
                                      (and
                                       (and (equal s_pc0_2 i_pc_2)
                                        (equal (read-srf_a a1 s_rf0_2)
                                         (read-prf_a a1 i_rf_2)))
                                       (equal s_dmem0_2 i_dmem_2))
                                      (< rank_v_2 rank_w_2))))
                                   (or
                                    (or
                                     (not
                                      (and
                                       (and (equal s_pc0_3 i_pc0_3)
                                        (equal (read-srf_a a1 s_rf0_3)
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
                              (or (or (not
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
                                  (and (and
                                        (and (equal s_pc0_4 i_pc_4)
                                         (equal (read-srf_a a1 s_rf0_4)
                                          (read-prf_a a1 i_rf_4)))
                                        (equal s_dmem0_4 i_dmem_4))
                                       (< rank_v_4 rank_w_4))))
                         (or (or (not (and
                                       (and (equal s_pc0_5 i_pc0_5)
                                        (equal (read-srf_a a1 s_rf0_5)
                                         (read-prf_a a1 i_rf0_5)))
                                       (equal s_dmem0_5 i_dmem0_5)))
                                 (and (and (equal s_pc1_5 i_pc_5)
                                       (equal (read-srf_a a1 s_rf1_5)
                                        (read-prf_a a1 i_rf_5)))
                                      (equal s_dmem1_5 i_dmem_5)))
                             (and (and (and (equal s_pc0_5 i_pc_5)
                                        (equal (read-srf_a a1 s_rf0_5)
                                         (read-prf_a a1 i_rf_5)))
                                       (equal s_dmem0_5 i_dmem_5))
                                  (< rank_v_5 rank_w_5))))))
         :rule-classes nil)

