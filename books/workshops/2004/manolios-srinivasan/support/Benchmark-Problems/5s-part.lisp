(in-package "ACL2")

(include-book "../Supporting-Books/records")
(include-book "../Supporting-Books/seq")
(include-book "../Supporting-Books/det-macros")
(include-book "../Supporting-Books/meta")




(defstub src1 (*) => *)
(defstub src2 (*) => *)
(defstub opcode (*) => *)
(defstub dest(*) => *)
(defstub alu (* * *) => *)
(defstub GetRegWrite(*) => *)
(defstub GetMemToReg(*) => *)
(defstub GetuseImm(*) => *)
(defstub GetImm(*) => *)
(defstub GetMemWrite(*) => *)

(defun MA-state (
  pPC
  pRF
  pDMem
  pIMem
  deOP
  deARG1
  deARG2
  deDEST
  deWRT
  mwVAL
  mwDEST
  mwWRT
  fdWRT
  fdINST
  emDEST
  emWRT
  deSRC1
  deSRC2
  deRegWrite
  emRegWrite
  mwRegWrite
  deImm
  deuseImm
  emResult
  deMemToReg
  emMemToReg
  deMemWrite
  emMemWrite
  emARG2
  pDMemHist_1
  pPCHist_1
  pPCHist_2
  pPCHist_3
  pPCHist_4
 )
 (seq nil 'type   'MA
  'pPC          pPC
  'pRF          pRF
  'pDMem        pDMem
  'pIMem        pIMem
  'deOP         deOP
  'deARG1       deARG1
  'deARG2       deARG2
  'deDEST       deDEST
  'deWRT        deWRT
  'mwVAL        mwVAL
  'mwDEST       mwDEST
  'mwWRT        mwWRT
  'fdWRT        fdWRT
  'fdINST       fdINST
  'emDEST       emDEST
  'emWRT        emWRT
  'deSRC1       deSRC1
  'deSRC2       deSRC2
  'deRegWrite   deRegWrite
  'emRegWrite   emRegWrite
  'mwRegWrite   mwRegWrite
  'deImm        deImm
  'deuseImm     deuseImm
  'emResult     emResult
  'deMemToReg   deMemToReg
  'emMemToReg   emMemToReg
  'deMemWrite   deMemWrite
  'emMemWrite   emMemWrite
  'emARG2       emARG2
  'pDMemHist_1  pDMemHist_1
  'pPCHist_1    pPCHist_1
  'pPCHist_2    pPCHist_2
  'pPCHist_3    pPCHist_3
  'pPCHist_4    pPCHist_4

))

(defun nextpIMem (pIMem)
  pIMem)

(defun nextpPCHist_4 (pPCHist_3)
  pPCHist_3)

(defun nextpPCHist_3 (pPCHist_2)
  pPCHist_2)

(defun nextpPCHist_2 (pPCHist_1)
  pPCHist_1)

(defun nextpPCHist_1 (pPC)
  pPC)

(defun nextpPC (pPC stall pPCHist_4 commit_impl)
   (cond
    (commit_impl pPCHist_4)
    (stall pPC)
    (t (+ 1 pPC))))

(defun nextpRF (pRF        mwWRT mwDEST
		mwRegWrite mwVAL commit_impl)
  (cond
   (commit_impl pRF)
   ((and mwWRT mwRegWrite)
    (s mwDEST mwVAL pRF))
   (t pRF)))

(defun nextfdWRT (stall commit_impl fdWRT)
  (cond
   (commit_impl nil)
   (stall fdWRT)
   (t t)))

(defun nextfdINST (inst fdINST stall)
  (cond
   (stall fdINST)
   (t inst)))

(defun nextdeSRC1 (IF_ID_Src1)
  IF_ID_Src1)

(defun nextdeSRC2 (IF_ID_Src2)
  IF_ID_Src2)

(defun nextdeARG1 (pRF mwWRT mwDEST mwRegWrite mwVAL commit_impl IF_ID_Src1)
    (g IF_ID_Src1
       (nextpRF pRF mwWRT mwDEST mwRegWrite mwVAL commit_impl))
)

(defun nextdeARG2 (pRF mwWRT mwDEST mwRegWrite mwVAL commit_impl IF_ID_Src2)
    (g IF_ID_Src2
       (nextpRF pRF mwWRT mwDEST mwRegWrite mwVAL commit_impl))
)

(defun nextdeDEST (fdINST)
  (dest fdINST))

(defun nextdeOP (fdINST)
  (opcode fdINST))

(defun nextdeImm (fdINST)
  (GetImm fdINST))

(defun nextdeuseImm (fdINST)
  (GetuseImm fdINST))

(defun nextdeRegWrite (ID_RegWrite)
  ID_RegWrite)

(defun nextdeMemWrite (ID_MemWrite)
  ID_MemWrite)

(defun nextdeMemtoReg (fdINST)
  (GetMemtoReg fdINST))

(defun nextdeWRT (stall fdWRT commit_impl)
  (cond
   (commit_impl nil)
   (t (and (not stall) fdWRT))))

(defun nextemARG2 (deARG2)
  deARG2)

(defun nextemResult (Result)
  Result)

(defun nextemDest (deDEST)
  deDEST)

(defun nextemWRT (commit_impl deWRT)
  (cond
   (commit_impl nil)
   (t deWRT)))

(defun nextemRegWrite (deRegWrite)
  deRegWrite)

(defun nextemMemWrite (deMemWrite)
  deMemWrite)

(defun nextemMemToReg (deMemToReg)
  deMemToReg)

(defun nextpDMemHist_1 (pDMem)
  pDMem)

(defun nextpDMem (commit_impl pDMemHist_1 emWRT
              emResult    emMemWrite  pDMem emARG2)
  (cond
   (commit_impl pDMemHist_1)
   ((and emWRT emMemWrite)
    (s emResult emARG2 pDMem))
   (t pDMem)))

(defun nextmwVAL (ReadData emMemToReg emResult)
  (cond
   (emMemToReg ReadData)
   (t emResult)))

(defun nextmwDEST (emDEST)
  emDEST)

(defun nextmwWRT (commit_impl emWRT)
  (cond
   (commit_impl nil)
   (t emWRT)))

(defun nextmwRegWrite (emRegWrite)
  emRegWrite)

(defun MA-step (MA commit_impl)
  (let
      ((pPC   (g 'pPC    MA))
       (pRF   (g 'pRF    MA))
       (pDMem (g 'pDMem  MA))
       (pIMem (g 'pIMem MA))
       (deOP  (g 'deOP MA))
       (deARG1 (g 'deARG1 MA))
       (deARG2 (g 'deARG2 MA))
       (deDEST (g 'deDEST MA))
       (deWRT  (g 'deWRT MA))
       (mwVAL  (g 'mwVAL MA))
       (mwDEST (g 'mwDEST MA))
       (mwWRT  (g 'mwWRT MA))
       (fdWRT  (g 'fdWRT MA))
       (fdINST (g 'fdINST MA))
       (emDEST (g 'emDEST MA))
       (emWRT  (g 'emWRT MA))
       (deSRC1 (g 'deSRC1 MA))
       (deSRC2 (g 'deSRC2 MA))
       (deRegWrite (g 'deRegWrite MA))
       (emRegWrite (g 'emRegWrite MA))
       (mwRegWrite (g 'mwRegWrite MA))
       (deImm  (g 'deImm MA))
       (deuseImm (g 'deuseImm MA))
       (emResult (g 'emResult MA))
       (deMemToReg  (g 'deMemToReg MA))
       (emMemToReg (g 'emMemToReg MA))
       (deMemWrite (g 'deMemWrite MA))
       (emMemWrite (g 'emMemWrite MA))
       (emARG2  (g 'emARG2 MA))
       (pDMemHist_1 (g 'pDMemHist_1 MA))
       (pPCHist_1 (g 'pPCHist_1 MA))
       (pPCHist_2 (g 'pPCHist_2 MA))
       (pPCHist_3 (g 'pPCHist_3 MA))
       (pPCHist_4 (g 'pPCHist_4 MA)))
    (let* ((inst (g pPC pIMem))
	   (IF_ID_Src1 (src1 fdINST))
	   (IF_ID_Src2 (src2 fdINST))
	   (stall (and deRegWrite deWRT
		       (bor
			(equal IF_ID_Src1 deDEST)
			(equal IF_ID_Src2 deDEST))))
	   (ID_RegWrite (GetRegWrite fdINST))
	   (ID_MemWrite (GetMemWrite fdINST))
	   (EX_WB_Equal_Src1
	    (and mwWRT
		 mwRegWrite
		 (equal deSRC1 mwDEST)))
	   (EX_WB_Equal_Src2
	    (and mwWRT
		 mwRegWrite
		 (equal deSRC2 mwDEST)))
	   (EX_WB_Fwd_Src1
	    (cond
	     (EX_WB_Equal_Src1 mwVAL)
	     (t deARG1)))
	   (EX_WB_Fwd_Src2
	    (cond
	     (EX_WB_Equal_Src2 mwVAL)
	     (t deARG2)))
	   (EX_Data2
	    (cond
	     (deuseImm deImm)
	     (t EX_WB_Fwd_Src2)))
	   (Result
	    (alu deOP EX_WB_Fwd_Src1 EX_Data2))
	   (ReadData  (g emResult pDMem)))
      (MA-state
       (nextpPC pPC stall pPCHist_4 commit_impl)
       (nextpRF pRF        mwWRT mwDEST
		mwRegWrite mwVAL commit_impl)
       (nextpDMem commit_impl pDMemHist_1 emWRT
                  emResult    emMemWrite  pDMem emARG2)
       (nextpIMem pIMem)
       (nextdeOP fdINST)
       (nextdeARG1 pRF mwWRT mwDEST mwRegWrite mwVAL commit_impl IF_ID_Src1)
       (nextdeARG2  pRF mwWRT mwDEST mwRegWrite mwVAL commit_impl IF_ID_Src2)
       (nextdeDEST fdINST)
       (nextdeWRT  stall fdWRT commit_impl)
       (nextmwVAL  ReadData emMemToReg emResult)
       (nextmwDEST emDEST)
       (nextmwWRT  commit_impl emWRT)
       (nextfdWRT stall commit_impl fdWRT)
       (nextfdINST inst fdINST stall)
       (nextemDEST deDEST)
       (nextemWRT  commit_impl deWRT)
       (nextdeSRC1 IF_ID_Src1)
       (nextdeSRC2 IF_ID_Src2)
       (nextdeRegWrite ID_RegWrite)
       (nextemRegWrite deRegWrite)
       (nextmwRegWrite emRegWrite)
       (nextdeImm fdINST)
       (nextdeuseImm fdINST)
       (nextemResult Result)
       (nextdeMemToReg fdINST)
       (nextemMemToReg deMemToReg)
       (nextdeMemWrite ID_MemWrite)
       (nextemMemWrite deMemWrite)
       (nextemARG2 deARG2)
       (nextpDMemHist_1 pDMem)
       (nextpPCHist_1 pPC)
       (nextpPCHist_2 pPCHist_1)
       (nextpPCHist_3 pPCHist_2)
       (nextpPCHist_4 pPCHist_3)))))


;; Specificaion

(defun ISA-state (sPC sRF sIMem sDMem)
  (seq nil 'type 'ISA
           'sPC   sPC
	   'sRF   sRF
	   'sIMem sIMem
	   'sDMem sDMem))


(defun nextsIMem (sIMem)
  sIMem)

(defun nextsPC (project_impl project_pc sPC)
  (cond
   (project_impl project_pc)
   (t (+ 1 sPC))))

(defun nextsRF (project_impl pRF sRF RegWrite val inst)
  (cond
   (project_impl pRF)
   (RegWrite (s (dest inst) val sRF))
   (t sRF)))

(defun nextsDMem (pDMemHist_1     MemWrite Result
	          arg2_temp sDMem    project_impl)
  (cond
   (project_impl pDMemHist_1)
   (MemWrite (s Result arg2_temp sDMem))
   (t sDMem)))

(defun ISA-step (ISA project_impl project_pc pDMemHist_1 pRF)
  (let* ((sPC (g 'sPC ISA))
         (sRF (g 'sRF ISA))
         (sDMem (g 'sDMem ISA))
	 (sIMem (g 'sIMem ISA))
	 (inst (g sPC sIMem))
	 (RegWrite (GetRegWrite inst))
	 (MemToReg (GetMemToReg inst))
	 (MemWrite (GetmemWrite inst))
	 (useImm   (GetuseImm inst))
	 (Imm      (GetImm inst))
	 (arg1 (g (src1 inst) sRF))
	 (arg2_temp (g (src2 inst) sRF))
	 (arg2
	  (cond
	   (useImm Imm)
	   (t arg2_temp)))
	 (Result
	  (alu
	   (opcode inst)
	   arg1 arg2))
	 (ReadData (g Result sDMem))
	 (val
	  (cond
	   (MemToReg ReadData)
	   (t Result))))
    (ISA-state
     (nextsPC project_impl project_pc sPC)
     (nextsRF project_impl pRF sRF RegWrite val inst)
     (nextsIMem sIMem)
     (nextsDMem pDMemHist_1     MemWrite Result
		arg2_temp sDMem    project_impl))))



;;  Control

(defun equiv-ma (ma1 ma2)
   (and (equal (g 'type ma1)
               (g 'type ma2))
       (equal (g 'pPC ma1)
              (g 'pPC ma2))
       (equal (g 'pRF ma1)
              (g 'pRF ma2))
       (equal (g 'pIMem ma1)
              (g 'pIMem ma2))
       (equal (g 'pDMem ma1)
              (g 'pDMem ma2))
       (equal (g 'fdWRT ma1)
              (g 'fdWRT ma2))
       (implies (g 'fdWRT ma1)
                (and (g 'fdWRT ma2)
                     (equal (g 'fdINST ma1)
                            (g 'fdINST ma2))))
       (equal (g 'deWRT ma1)
              (g 'deWRT ma2))
       (implies (g 'deWRT ma1)
                (and (g 'deWRT ma2)
                     (equal (g 'deOP ma1)
			    (g 'deOP ma2))
		     (equal (g 'deARG1 ma1)
			    (g 'deARG1 ma2))
		     (equal (g 'deARG2 ma1)
			    (g 'deARG2 ma2))
		     (equal (g 'deDEST ma1)
			    (g 'deDEST ma2))
		     (equal (g 'deSRC1 ma1)
			    (g 'deSRC1 ma2))
		     (equal (g 'deSRC2 ma1)
			    (g 'deSRC2 ma2))
		     (equal (g 'deImm ma1)
			    (g 'deImm ma2))
		     (equal (g 'deuseImm ma1)
			    (g 'deuseImm ma2))
		     (equal (g 'deRegWrite ma1)
			    (g 'deRegWrite ma2))
		     (equal (g 'deMemWrite ma1)
			    (g 'deMemWrite ma2))
		     (equal (g 'deMemToReg ma1)
			    (g 'deMemToReg ma2))))
       (equal (g 'emWRT ma1)
	      (g 'emWRT ma2))
       (implies (g 'emWRT ma1)
                (and (g 'emWRT ma2)
		     (equal (g 'emDEST ma1)
			    (g 'emDEST ma2))
		     (equal (g 'emRegWrite ma1)
			    (g 'emRegWrite ma2))
		     (equal (g 'emMemWrite ma1)
			    (g 'emMemWrite ma2))
		     (equal (g 'emMemToReg ma1)
			    (g 'emMemToReg ma2))
		     (equal (g 'emResult ma1)
			    (g 'emResult ma2))))
       (equal (g 'mwWRT ma1)
	      (g 'mwWRT ma2))
       (implies (g 'mwWRT ma1)
                (and (g 'mwWRT ma2)
		     (equal (g 'mwRegWrite ma1)
			    (g 'mwRegWrite ma2))
		     (equal (g 'mwDEST ma1)
			    (g 'mwDEST ma2))
		     (equal (g 'mwVAL ma1)
			    (g 'mwVAL ma2))))))



(defun Rank (ma)
 (let ((fdWRT (g 'fdWRT ma))
       (deWRT (g 'deWRT ma))
       (emWRT (g 'emWRT ma))
       (mwWRT (g 'mwWRT ma)))
   (cond
    (mwWRT 0)
    (emWRT 1)
    (deWRT 2)
    (fdWRT 3)
    (t 4))))

#|
(defun committed-MA (MA)
  (let ((pPC (g 'pPC MA))
	(fdWRT (g 'fdWRT MA))
	(deWRT (g 'deWRT MA))
	(emWRT (g 'emWRT MA))
	(mwWRT (g 'mwWRT MA))
	(pDMem (g 'pDMem MA))
	(pPCHist_4 (g 'pPCHist_4 MA))
	(pDMemHist_1 (g 'pDMemHist_1 MA)))
    (seq MA 'pPC pPCHist_4
	    'pDMemHist_1
            'fdWRT nil
	    'deWRT nil
	    'emWRT nil
	    'mwWRT nil)))
|#

(defun good-ma (ma)
  (let ((commit-ma (ma-step ma t)))
    (bor
     (equiv-ma ma commit-ma)
     (equiv-ma ma (ma-step commit-ma nil))
     (equiv-ma ma (ma-step
		   (ma-step commit-ma nil)
		   nil))
     (equiv-ma ma (ma-step
		   (ma-step
		    (ma-step commit-ma nil) nil)
		   nil))
     (equiv-ma ma (ma-step
		   (ma-step
		    (ma-step
		     (ma-step commit-ma nil)
		     nil)
		    nil)
		   nil)))))


(in-theory (disable g-diff-s- G-SAME-S-))

(SET-MATCH-FREE-ERROR NIL)

(defthm WEB
  (let* ((X (ma-step ma t))
	 (W (ma-step
	     (ma-step
	      (ma-step
		(ma-step X nil)
	       nil)
	      nil)
	     nil))
	 (V (ma-step W nil))
	 (Good_MA_V (good-ma V))
	 (pRF_W (g 'pRF W))
	 (pPC_W (g 'pPC W))
	 (pDMem_W (g 'pDMem W))
	 (pDMemHist_1_W (g 'pDMemHist_1 W))
	 (pPCHist_4_W (g 'pPCHist_4 W))
	 (pRF_V (g 'pRF V))
	 (pPC_V (g 'pPC V))
	 (pDMem_V (g 'pDMem V))
	 (Y ( ISA-step isa t pPCHist_4_W
		       pDMemHist_1_W pRF_W))
	 (U (ISA-step Y nil  pPCHist_4_W
		        pDMemHist_1_W pRF_W))
	 (sRF_Y (g 'sRF Y))
	 (sPC_Y (g 'sPC Y))
	 (sDMem_Y (g 'sDMem Y))
	 (sRF_U (g 'sRF U))
	 (sPC_U (g 'sPC U))
	 (sDMem_U (g 'sDMem U)))
    (implies (and
	      (equal pPC_W sPC_Y)
	      (equal pRF_W sRF_Y)
	      (equal pDMem_W sDMem_Y)
	      (not
	       (and
		(equal pPC_V sPC_U)
		(equal pRF_V sRF_U)
		(equal pDMem_V sDMem_U))))
	     (and
	      Good_MA_V
	      (equal pPC_V sPC_Y)
	      (equal pRF_V sRF_Y)
	      (equal pDMem_V sDMem_Y)
	      (< (Rank V)  (Rank W))))))
