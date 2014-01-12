signature x64Theory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val AF_def : thm
    val ByteParity_def : thm
    val CF_def : thm
    val EA_def : thm
    val Eflag_def : thm
    val FlagUnspecified_def : thm
    val OF_def : thm
    val OpSize_def : thm
    val PF_def : thm
    val REX_B : thm
    val REX_B_fupd : thm
    val REX_R : thm
    val REX_R_fupd : thm
    val REX_TY_DEF : thm
    val REX_W : thm
    val REX_W_fupd : thm
    val REX_X : thm
    val REX_X_fupd : thm
    val REX_case_def : thm
    val REX_size_def : thm
    val ROL_def : thm
    val ROR_def : thm
    val RexReg_def : thm
    val Run_def : thm
    val SAR_def : thm
    val SF_def : thm
    val ZF_def : thm
    val Zbase_TY_DEF : thm
    val Zbase_case_def : thm
    val Zbase_size_def : thm
    val Zbinop_name2string_def : thm
    val Zbinop_name_BIJ : thm
    val Zbinop_name_CASE : thm
    val Zbinop_name_TY_DEF : thm
    val Zbinop_name_size_def : thm
    val Zcond2string_def : thm
    val Zcond_BIJ : thm
    val Zcond_CASE : thm
    val Zcond_TY_DEF : thm
    val Zcond_size_def : thm
    val Zdest_src_TY_DEF : thm
    val Zdest_src_case_def : thm
    val Zdest_src_size_def : thm
    val Zea_TY_DEF : thm
    val Zea_case_def : thm
    val Zea_size_def : thm
    val Zeflags2string_def : thm
    val Zeflags_BIJ : thm
    val Zeflags_CASE : thm
    val Zeflags_TY_DEF : thm
    val Zeflags_size_def : thm
    val Zimm_rm_TY_DEF : thm
    val Zimm_rm_case_def : thm
    val Zimm_rm_size_def : thm
    val Zinst_TY_DEF : thm
    val Zinst_case_def : thm
    val Zinst_size_def : thm
    val Zmonop_name_BIJ : thm
    val Zmonop_name_CASE : thm
    val Zmonop_name_TY_DEF : thm
    val Zmonop_name_size_def : thm
    val Zreg_BIJ : thm
    val Zreg_CASE : thm
    val Zreg_TY_DEF : thm
    val Zreg_size_def : thm
    val Zrm_TY_DEF : thm
    val Zrm_case_def : thm
    val Zrm_size_def : thm
    val Zsize_TY_DEF : thm
    val Zsize_case_def : thm
    val Zsize_size_def : thm
    val Zsize_width_def : thm
    val add_with_carry_out_def : thm
    val bitify8_def : thm
    val boolify8_def : thm
    val call_dest_from_ea_def : thm
    val checkIcache_def : thm
    val dfn'Zbinop_def : thm
    val dfn'Zcall_def : thm
    val dfn'Zcmpxchg_def : thm
    val dfn'Zcpuid_def : thm
    val dfn'Zdiv_def : thm
    val dfn'Zjcc_def : thm
    val dfn'Zjmp_def : thm
    val dfn'Zlea_def : thm
    val dfn'Zloop_def : thm
    val dfn'Zmonop_def : thm
    val dfn'Zmov_def : thm
    val dfn'Zmovzx_def : thm
    val dfn'Zmul_def : thm
    val dfn'Znop_def : thm
    val dfn'Zpop_def : thm
    val dfn'Zpush_def : thm
    val dfn'Zret_def : thm
    val dfn'Zxadd_def : thm
    val dfn'Zxchg_def : thm
    val ea_Zdest_def : thm
    val ea_Zimm_rm_def : thm
    val ea_Zrm_def : thm
    val ea_Zsrc_def : thm
    val ea_base_def : thm
    val ea_index_def : thm
    val erase_eflags_def : thm
    val exception_TY_DEF : thm
    val exception_case_def : thm
    val exception_size_def : thm
    val full_immediate_def : thm
    val get_ea_address_def : thm
    val immediate16_def : thm
    val immediate32_def : thm
    val immediate64_def : thm
    val immediate8_def : thm
    val immediate_def : thm
    val instruction_TY_DEF : thm
    val instruction_case_def : thm
    val instruction_size_def : thm
    val isZm_def : thm
    val jump_to_ea_def : thm
    val maskShift_def : thm
    val mem16_def : thm
    val mem32_def : thm
    val mem64_def : thm
    val mem8_def : thm
    val prefixGroup_def : thm
    val raise'exception_def : thm
    val readDisplacement_def : thm
    val readModRM_def : thm
    val readOpcodeModRM_def : thm
    val readPrefix_primitive_def : thm
    val readPrefixes_def : thm
    val readSIB_def : thm
    val readSibDisplacement_def : thm
    val read_cond_def : thm
    val read_dest_src_ea_def : thm
    val rec'REX_def : thm
    val reg'REX_def : thm
    val restrictSize_def : thm
    val sub_with_borrow_def : thm
    val value_width_def : thm
    val word_signed_overflow_add_def : thm
    val word_signed_overflow_sub_def : thm
    val word_size_msb_def : thm
    val write'AF_def : thm
    val write'CF_def : thm
    val write'EA_def : thm
    val write'Eflag_def : thm
    val write'OF_def : thm
    val write'PF_def : thm
    val write'SF_def : thm
    val write'ZF_def : thm
    val write'mem16_def : thm
    val write'mem32_def : thm
    val write'mem64_def : thm
    val write'mem8_def : thm
    val write'rec'REX_def : thm
    val write'reg'REX_def : thm
    val write_PF_def : thm
    val write_SF_def : thm
    val write_ZF_def : thm
    val write_arith_eflags_def : thm
    val write_arith_eflags_except_CF_OF_def : thm
    val write_arith_result_def : thm
    val write_arith_result_no_CF_OF_def : thm
    val write_binop_def : thm
    val write_logical_eflags_def : thm
    val write_logical_result_def : thm
    val write_monop_def : thm
    val write_result_erase_eflags_def : thm
    val x64_decode_def : thm
    val x64_drop_def : thm
    val x64_fetch_def : thm
    val x64_next_def : thm
    val x64_pop_aux_def : thm
    val x64_pop_def : thm
    val x64_pop_rip_def : thm
    val x64_push_aux_def : thm
    val x64_push_def : thm
    val x64_push_rip_def : thm
    val x64_state_EFLAGS : thm
    val x64_state_EFLAGS_fupd : thm
    val x64_state_ICACHE : thm
    val x64_state_ICACHE_fupd : thm
    val x64_state_MEM : thm
    val x64_state_MEM_fupd : thm
    val x64_state_REG : thm
    val x64_state_REG_fupd : thm
    val x64_state_RIP : thm
    val x64_state_RIP_fupd : thm
    val x64_state_TY_DEF : thm
    val x64_state_case_def : thm
    val x64_state_exception : thm
    val x64_state_exception_fupd : thm
    val x64_state_size_def : thm

  (*  Theorems  *)
    val EXISTS_REX : thm
    val EXISTS_x64_state : thm
    val FORALL_REX : thm
    val FORALL_x64_state : thm
    val REX_11 : thm
    val REX_Axiom : thm
    val REX_accessors : thm
    val REX_accfupds : thm
    val REX_case_cong : thm
    val REX_component_equality : thm
    val REX_fn_updates : thm
    val REX_fupdcanon : thm
    val REX_fupdcanon_comp : thm
    val REX_fupdfupds : thm
    val REX_fupdfupds_comp : thm
    val REX_induction : thm
    val REX_literal_11 : thm
    val REX_literal_nchotomy : thm
    val REX_nchotomy : thm
    val REX_updates_eq_literal : thm
    val Zbase_11 : thm
    val Zbase_Axiom : thm
    val Zbase_case_cong : thm
    val Zbase_distinct : thm
    val Zbase_induction : thm
    val Zbase_nchotomy : thm
    val Zbinop_name2num_11 : thm
    val Zbinop_name2num_ONTO : thm
    val Zbinop_name2num_num2Zbinop_name : thm
    val Zbinop_name2num_thm : thm
    val Zbinop_name_Axiom : thm
    val Zbinop_name_EQ_Zbinop_name : thm
    val Zbinop_name_case_cong : thm
    val Zbinop_name_case_def : thm
    val Zbinop_name_induction : thm
    val Zbinop_name_nchotomy : thm
    val Zcond2num_11 : thm
    val Zcond2num_ONTO : thm
    val Zcond2num_num2Zcond : thm
    val Zcond2num_thm : thm
    val Zcond_Axiom : thm
    val Zcond_EQ_Zcond : thm
    val Zcond_case_cong : thm
    val Zcond_case_def : thm
    val Zcond_induction : thm
    val Zcond_nchotomy : thm
    val Zdest_src_11 : thm
    val Zdest_src_Axiom : thm
    val Zdest_src_case_cong : thm
    val Zdest_src_distinct : thm
    val Zdest_src_induction : thm
    val Zdest_src_nchotomy : thm
    val Zea_11 : thm
    val Zea_Axiom : thm
    val Zea_case_cong : thm
    val Zea_distinct : thm
    val Zea_induction : thm
    val Zea_nchotomy : thm
    val Zeflags2num_11 : thm
    val Zeflags2num_ONTO : thm
    val Zeflags2num_num2Zeflags : thm
    val Zeflags2num_thm : thm
    val Zeflags_Axiom : thm
    val Zeflags_EQ_Zeflags : thm
    val Zeflags_case_cong : thm
    val Zeflags_case_def : thm
    val Zeflags_distinct : thm
    val Zeflags_induction : thm
    val Zeflags_nchotomy : thm
    val Zimm_rm_11 : thm
    val Zimm_rm_Axiom : thm
    val Zimm_rm_case_cong : thm
    val Zimm_rm_distinct : thm
    val Zimm_rm_induction : thm
    val Zimm_rm_nchotomy : thm
    val Zinst_11 : thm
    val Zinst_Axiom : thm
    val Zinst_case_cong : thm
    val Zinst_distinct : thm
    val Zinst_induction : thm
    val Zinst_nchotomy : thm
    val Zmonop_name2num_11 : thm
    val Zmonop_name2num_ONTO : thm
    val Zmonop_name2num_num2Zmonop_name : thm
    val Zmonop_name2num_thm : thm
    val Zmonop_name_Axiom : thm
    val Zmonop_name_EQ_Zmonop_name : thm
    val Zmonop_name_case_cong : thm
    val Zmonop_name_case_def : thm
    val Zmonop_name_distinct : thm
    val Zmonop_name_induction : thm
    val Zmonop_name_nchotomy : thm
    val Zreg2num_11 : thm
    val Zreg2num_ONTO : thm
    val Zreg2num_num2Zreg : thm
    val Zreg2num_thm : thm
    val Zreg_Axiom : thm
    val Zreg_EQ_Zreg : thm
    val Zreg_case_cong : thm
    val Zreg_case_def : thm
    val Zreg_induction : thm
    val Zreg_nchotomy : thm
    val Zrm_11 : thm
    val Zrm_Axiom : thm
    val Zrm_case_cong : thm
    val Zrm_distinct : thm
    val Zrm_induction : thm
    val Zrm_nchotomy : thm
    val Zsize_11 : thm
    val Zsize_Axiom : thm
    val Zsize_case_cong : thm
    val Zsize_distinct : thm
    val Zsize_induction : thm
    val Zsize_nchotomy : thm
    val bitify8boolify8 : thm
    val boolify8_n2w : thm
    val boolify8_v2w : thm
    val boolify8bitify8 : thm
    val datatype_REX : thm
    val datatype_Zbase : thm
    val datatype_Zbinop_name : thm
    val datatype_Zcond : thm
    val datatype_Zdest_src : thm
    val datatype_Zea : thm
    val datatype_Zeflags : thm
    val datatype_Zimm_rm : thm
    val datatype_Zinst : thm
    val datatype_Zmonop_name : thm
    val datatype_Zreg : thm
    val datatype_Zrm : thm
    val datatype_Zsize : thm
    val datatype_exception : thm
    val datatype_instruction : thm
    val datatype_x64_state : thm
    val exception_11 : thm
    val exception_Axiom : thm
    val exception_case_cong : thm
    val exception_distinct : thm
    val exception_induction : thm
    val exception_nchotomy : thm
    val instruction_11 : thm
    val instruction_Axiom : thm
    val instruction_case_cong : thm
    val instruction_distinct : thm
    val instruction_induction : thm
    val instruction_nchotomy : thm
    val num2Zbinop_name_11 : thm
    val num2Zbinop_name_ONTO : thm
    val num2Zbinop_name_Zbinop_name2num : thm
    val num2Zbinop_name_thm : thm
    val num2Zcond_11 : thm
    val num2Zcond_ONTO : thm
    val num2Zcond_Zcond2num : thm
    val num2Zcond_thm : thm
    val num2Zeflags_11 : thm
    val num2Zeflags_ONTO : thm
    val num2Zeflags_Zeflags2num : thm
    val num2Zeflags_thm : thm
    val num2Zmonop_name_11 : thm
    val num2Zmonop_name_ONTO : thm
    val num2Zmonop_name_Zmonop_name2num : thm
    val num2Zmonop_name_thm : thm
    val num2Zreg_11 : thm
    val num2Zreg_ONTO : thm
    val num2Zreg_Zreg2num : thm
    val num2Zreg_thm : thm
    val readPrefix_def : thm
    val readPrefix_ind : thm
    val x64_state_11 : thm
    val x64_state_Axiom : thm
    val x64_state_accessors : thm
    val x64_state_accfupds : thm
    val x64_state_case_cong : thm
    val x64_state_component_equality : thm
    val x64_state_fn_updates : thm
    val x64_state_fupdcanon : thm
    val x64_state_fupdcanon_comp : thm
    val x64_state_fupdfupds : thm
    val x64_state_fupdfupds_comp : thm
    val x64_state_induction : thm
    val x64_state_literal_11 : thm
    val x64_state_literal_nchotomy : thm
    val x64_state_nchotomy : thm
    val x64_state_updates_eq_literal : thm

  val x64_grammars : type_grammar.grammar * term_grammar.grammar

  val inventory: {Thy: string, T: string list, C: string list, N: int list}
(*
   [bitstring] Parent theory of "x64"

   [integer_word] Parent theory of "x64"

   [machine_ieee] Parent theory of "x64"

   [state_transformer] Parent theory of "x64"

   [AF_def]  Definition

      |- ∀state. AF state = Eflag Z_AF state

   [ByteParity_def]  Definition

      |- ∀b.
           ByteParity b ⇔
           (((if word_bit 7 b then 1 else 0) +
             (if word_bit 6 b then 1 else 0) +
             (if word_bit 5 b then 1 else 0) +
             (if word_bit 4 b then 1 else 0) +
             (if word_bit 3 b then 1 else 0) +
             (if word_bit 2 b then 1 else 0) +
             (if word_bit 1 b then 1 else 0) +
             if word_bit 0 b then 1 else 0) MOD 2 =
            0)

   [CF_def]  Definition

      |- ∀state. CF state = Eflag Z_CF state

   [EA_def]  Definition

      |- ∀ea.
           EA ea =
           (λstate.
              case ea of
                Zea_i i => (restrictSize i,state)
              | Zea_m (Z16,a) => (let (v,s) = mem16 a state in (w2w v,s))
              | Zea_m (Z32,a) => (let (v,s) = mem32 a state in (w2w v,s))
              | Zea_m (Z64,a) => mem64 a state
              | Zea_m (Z8 v5,a) => (let (v,s) = mem8 a state in (w2w v,s))
              | Zea_r (Z16,r) => (restrictSize (Z16,state.REG r),state)
              | Zea_r (Z32,r) => (restrictSize (Z32,state.REG r),state)
              | Zea_r (Z64,r) => (restrictSize (Z64,state.REG r),state)
              | Zea_r (Z8 have_rex,r) =>
                  (if have_rex ∨ r ∉ {RSP; RBP; RSI; RDI} then
                     state.REG r && 255w
                   else state.REG (num2Zreg (Zreg2num r − 4)) ⋙ 8 && 255w,
                   state))

   [Eflag_def]  Definition

      |- ∀flag.
           Eflag flag =
           (λstate.
              case state.EFLAGS flag of
                NONE =>
                  raise'exception (BadFlagAccess (Zeflags2string flag))
                    state
              | SOME b => (b,state))

   [FlagUnspecified_def]  Definition

      |- ∀flag.
           FlagUnspecified flag =
           (λstate. ((),state with EFLAGS := (flag =+ NONE) state.EFLAGS))

   [OF_def]  Definition

      |- ∀state. OF state = Eflag Z_OF state

   [OpSize_def]  Definition

      |- ∀have_rex w v override.
           OpSize (have_rex,w,v,override) =
           if v = 0w then Z8 have_rex
           else if w then Z64
           else if override then Z16
           else Z32

   [PF_def]  Definition

      |- ∀state. PF state = Eflag Z_PF state

   [REX_B]  Definition

      |- ∀b b0 b1 b2. (REX b b0 b1 b2).B ⇔ b

   [REX_B_fupd]  Definition

      |- ∀f b b0 b1 b2.
           REX b b0 b1 b2 with B updated_by f = REX (f b) b0 b1 b2

   [REX_R]  Definition

      |- ∀b b0 b1 b2. (REX b b0 b1 b2).R ⇔ b0

   [REX_R_fupd]  Definition

      |- ∀f b b0 b1 b2.
           REX b b0 b1 b2 with R updated_by f = REX b (f b0) b1 b2

   [REX_TY_DEF]  Definition

      |- ∃rep.
           TYPE_DEFINITION
             (λa0'.
                ∀'REX' .
                  (∀a0'.
                     (∃a0 a1 a2 a3.
                        a0' =
                        (λa0 a1 a2 a3.
                           ind_type$CONSTR 0 (a0,a1,a2,a3)
                             (λn. ind_type$BOTTOM)) a0 a1 a2 a3) ⇒
                     'REX' a0') ⇒
                  'REX' a0') rep

   [REX_W]  Definition

      |- ∀b b0 b1 b2. (REX b b0 b1 b2).W ⇔ b1

   [REX_W_fupd]  Definition

      |- ∀f b b0 b1 b2.
           REX b b0 b1 b2 with W updated_by f = REX b b0 (f b1) b2

   [REX_X]  Definition

      |- ∀b b0 b1 b2. (REX b b0 b1 b2).X ⇔ b2

   [REX_X_fupd]  Definition

      |- ∀f b b0 b1 b2.
           REX b b0 b1 b2 with X updated_by f = REX b b0 b1 (f b2)

   [REX_case_def]  Definition

      |- ∀a0 a1 a2 a3 f. REX_CASE (REX a0 a1 a2 a3) f = f a0 a1 a2 a3

   [REX_size_def]  Definition

      |- ∀a0 a1 a2 a3.
           REX_size (REX a0 a1 a2 a3) =
           1 +
           (bool_size a0 + (bool_size a1 + (bool_size a2 + bool_size a3)))

   [ROL_def]  Definition

      |- ∀size x y.
           ROL (size,x,y) =
           case size of
             Z16 => w2w ((15 >< 0) x ⇆ w2n ((4 >< 0) y))
           | Z32 => w2w ((31 >< 0) x ⇆ w2n ((4 >< 0) y))
           | Z64 => x ⇆ w2n ((5 >< 0) y)
           | Z8 v => w2w ((7 >< 0) x ⇆ w2n ((4 >< 0) y))

   [ROR_def]  Definition

      |- ∀size x y.
           ROR (size,x,y) =
           case size of
             Z16 => w2w ((15 >< 0) x ⇄ w2n ((4 >< 0) y))
           | Z32 => w2w ((31 >< 0) x ⇄ w2n ((4 >< 0) y))
           | Z64 => x ⇄ w2n ((5 >< 0) y)
           | Z8 v => w2w ((7 >< 0) x ⇄ w2n ((4 >< 0) y))

   [RexReg_def]  Definition

      |- ∀b r. RexReg (b,r) = num2Zreg (w2n ((if b then 1w else 0w) @@ r))

   [Run_def]  Definition

      |- ∀v0.
           Run v0 =
           (λstate.
              case v0 of
                Zbinop v1 => dfn'Zbinop v1 state
              | Zcall v2 => dfn'Zcall v2 state
              | Zcmpxchg v3 => dfn'Zcmpxchg v3 state
              | Zcpuid => dfn'Zcpuid state
              | Zdiv v4 => dfn'Zdiv v4 state
              | Zjcc v5 => dfn'Zjcc v5 state
              | Zjmp v6 => dfn'Zjmp v6 state
              | Zlea v7 => dfn'Zlea v7 state
              | Zloop v8 => dfn'Zloop v8 state
              | Zmonop v9 => dfn'Zmonop v9 state
              | Zmov v10 => dfn'Zmov v10 state
              | Zmovzx v11 => dfn'Zmovzx v11 state
              | Zmul v12 => dfn'Zmul v12 state
              | Znop => (dfn'Znop,state)
              | Zpop v13 => dfn'Zpop v13 state
              | Zpush v14 => dfn'Zpush v14 state
              | Zret v15 => dfn'Zret v15 state
              | Zxadd v16 => dfn'Zxadd v16 state
              | Zxchg v17 => dfn'Zxchg v17 state)

   [SAR_def]  Definition

      |- ∀size x y.
           SAR (size,x,y) =
           case size of
             Z16 => w2w ((15 >< 0) x ≫ w2n ((4 >< 0) y))
           | Z32 => w2w ((31 >< 0) x ≫ w2n ((4 >< 0) y))
           | Z64 => x ≫ w2n ((5 >< 0) y)
           | Z8 v => w2w ((7 >< 0) x ≫ w2n ((4 >< 0) y))

   [SF_def]  Definition

      |- ∀state. SF state = Eflag Z_SF state

   [ZF_def]  Definition

      |- ∀state. ZF state = Eflag Z_ZF state

   [Zbase_TY_DEF]  Definition

      |- ∃rep.
           TYPE_DEFINITION
             (λa0.
                ∀'Zbase' .
                  (∀a0.
                     (a0 = ind_type$CONSTR 0 ARB (λn. ind_type$BOTTOM)) ∨
                     (∃a.
                        a0 =
                        (λa.
                           ind_type$CONSTR (SUC 0) a (λn. ind_type$BOTTOM))
                          a) ∨
                     (a0 =
                      ind_type$CONSTR (SUC (SUC 0)) ARB
                        (λn. ind_type$BOTTOM)) ⇒
                     'Zbase' a0) ⇒
                  'Zbase' a0) rep

   [Zbase_case_def]  Definition

      |- (∀v f v1. Zbase_CASE ZnoBase v f v1 = v) ∧
         (∀a v f v1. Zbase_CASE (ZregBase a) v f v1 = f a) ∧
         ∀v f v1. Zbase_CASE ZripBase v f v1 = v1

   [Zbase_size_def]  Definition

      |- (Zbase_size ZnoBase = 0) ∧
         (∀a. Zbase_size (ZregBase a) = 1 + Zreg_size a) ∧
         (Zbase_size ZripBase = 0)

   [Zbinop_name2string_def]  Definition

      |- (Zbinop_name2string Zadd = "Zadd") ∧
         (Zbinop_name2string Zor = "Zor") ∧
         (Zbinop_name2string Zadc = "Zadc") ∧
         (Zbinop_name2string Zsbb = "Zsbb") ∧
         (Zbinop_name2string Zand = "Zand") ∧
         (Zbinop_name2string Zsub = "Zsub") ∧
         (Zbinop_name2string Zxor = "Zxor") ∧
         (Zbinop_name2string Zcmp = "Zcmp") ∧
         (Zbinop_name2string Zrol = "Zrol") ∧
         (Zbinop_name2string Zror = "Zror") ∧
         (Zbinop_name2string Zrcl = "Zrcl") ∧
         (Zbinop_name2string Zrcr = "Zrcr") ∧
         (Zbinop_name2string Zshl = "Zshl") ∧
         (Zbinop_name2string Zshr = "Zshr") ∧
         (Zbinop_name2string Ztest = "Ztest") ∧
         (Zbinop_name2string Zsar = "Zsar")

   [Zbinop_name_BIJ]  Definition

      |- (∀a. num2Zbinop_name (Zbinop_name2num a) = a) ∧
         ∀r. (λn. n < 16) r ⇔ (Zbinop_name2num (num2Zbinop_name r) = r)

   [Zbinop_name_CASE]  Definition

      |- ∀x v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15.
           (case x of
              Zadd => v0
            | Zor => v1
            | Zadc => v2
            | Zsbb => v3
            | Zand => v4
            | Zsub => v5
            | Zxor => v6
            | Zcmp => v7
            | Zrol => v8
            | Zror => v9
            | Zrcl => v10
            | Zrcr => v11
            | Zshl => v12
            | Zshr => v13
            | Ztest => v14
            | Zsar => v15) =
           (λm.
              if m < 7 then
                if m < 3 then
                  if m < 1 then v0 else if m = 1 then v1 else v2
                else if m < 4 then v3
                else if m < 5 then v4
                else if m = 5 then v5
                else v6
              else if m < 11 then
                if m < 8 then v7
                else if m < 9 then v8
                else if m = 9 then v9
                else v10
              else if m < 13 then if m = 11 then v11 else v12
              else if m < 14 then v13
              else if m = 14 then v14
              else v15) (Zbinop_name2num x)

   [Zbinop_name_TY_DEF]  Definition

      |- ∃rep. TYPE_DEFINITION (λn. n < 16) rep

   [Zbinop_name_size_def]  Definition

      |- ∀x. Zbinop_name_size x = 0

   [Zcond2string_def]  Definition

      |- (Zcond2string Z_O = "Z_O") ∧ (Zcond2string Z_NO = "Z_NO") ∧
         (Zcond2string Z_B = "Z_B") ∧ (Zcond2string Z_NB = "Z_NB") ∧
         (Zcond2string Z_E = "Z_E") ∧ (Zcond2string Z_NE = "Z_NE") ∧
         (Zcond2string Z_NA = "Z_NA") ∧ (Zcond2string Z_A = "Z_A") ∧
         (Zcond2string Z_S = "Z_S") ∧ (Zcond2string Z_NS = "Z_NS") ∧
         (Zcond2string Z_P = "Z_P") ∧ (Zcond2string Z_NP = "Z_NP") ∧
         (Zcond2string Z_L = "Z_L") ∧ (Zcond2string Z_NL = "Z_NL") ∧
         (Zcond2string Z_NG = "Z_NG") ∧ (Zcond2string Z_G = "Z_G") ∧
         (Zcond2string Z_ALWAYS = "Z_ALWAYS")

   [Zcond_BIJ]  Definition

      |- (∀a. num2Zcond (Zcond2num a) = a) ∧
         ∀r. (λn. n < 17) r ⇔ (Zcond2num (num2Zcond r) = r)

   [Zcond_CASE]  Definition

      |- ∀x v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16.
           (case x of
              Z_O => v0
            | Z_NO => v1
            | Z_B => v2
            | Z_NB => v3
            | Z_E => v4
            | Z_NE => v5
            | Z_NA => v6
            | Z_A => v7
            | Z_S => v8
            | Z_NS => v9
            | Z_P => v10
            | Z_NP => v11
            | Z_L => v12
            | Z_NL => v13
            | Z_NG => v14
            | Z_G => v15
            | Z_ALWAYS => v16) =
           (λm.
              if m < 8 then
                if m < 3 then
                  if m < 1 then v0 else if m = 1 then v1 else v2
                else if m < 5 then if m = 3 then v3 else v4
                else if m < 6 then v5
                else if m = 6 then v6
                else v7
              else if m < 12 then
                if m < 9 then v8
                else if m < 10 then v9
                else if m = 10 then v10
                else v11
              else if m < 14 then if m = 12 then v12 else v13
              else if m < 15 then v14
              else if m = 15 then v15
              else v16) (Zcond2num x)

   [Zcond_TY_DEF]  Definition

      |- ∃rep. TYPE_DEFINITION (λn. n < 17) rep

   [Zcond_size_def]  Definition

      |- ∀x. Zcond_size x = 0

   [Zdest_src_TY_DEF]  Definition

      |- ∃rep.
           TYPE_DEFINITION
             (λa0.
                ∀'Zdest_src' .
                  (∀a0.
                     (∃a.
                        a0 =
                        (λa.
                           ind_type$CONSTR 0 (a,ARB,ARB)
                             (λn. ind_type$BOTTOM)) a) ∨
                     (∃a.
                        a0 =
                        (λa.
                           ind_type$CONSTR (SUC 0) (ARB,a,ARB)
                             (λn. ind_type$BOTTOM)) a) ∨
                     (∃a.
                        a0 =
                        (λa.
                           ind_type$CONSTR (SUC (SUC 0)) (ARB,ARB,a)
                             (λn. ind_type$BOTTOM)) a) ⇒
                     'Zdest_src' a0) ⇒
                  'Zdest_src' a0) rep

   [Zdest_src_case_def]  Definition

      |- (∀a f f1 f2. Zdest_src_CASE (Zr_rm a) f f1 f2 = f a) ∧
         (∀a f f1 f2. Zdest_src_CASE (Zrm_i a) f f1 f2 = f1 a) ∧
         ∀a f f1 f2. Zdest_src_CASE (Zrm_r a) f f1 f2 = f2 a

   [Zdest_src_size_def]  Definition

      |- (∀a.
            Zdest_src_size (Zr_rm a) =
            1 + pair_size Zreg_size Zrm_size a) ∧
         (∀a.
            Zdest_src_size (Zrm_i a) = 1 + pair_size Zrm_size (λv. 0) a) ∧
         ∀a. Zdest_src_size (Zrm_r a) = 1 + pair_size Zrm_size Zreg_size a

   [Zea_TY_DEF]  Definition

      |- ∃rep.
           TYPE_DEFINITION
             (λa0.
                ∀'Zea' .
                  (∀a0.
                     (∃a.
                        a0 =
                        (λa.
                           ind_type$CONSTR 0 (a,ARB) (λn. ind_type$BOTTOM))
                          a) ∨
                     (∃a.
                        a0 =
                        (λa.
                           ind_type$CONSTR (SUC 0) (a,ARB)
                             (λn. ind_type$BOTTOM)) a) ∨
                     (∃a.
                        a0 =
                        (λa.
                           ind_type$CONSTR (SUC (SUC 0)) (ARB,a)
                             (λn. ind_type$BOTTOM)) a) ⇒
                     'Zea' a0) ⇒
                  'Zea' a0) rep

   [Zea_case_def]  Definition

      |- (∀a f f1 f2. Zea_CASE (Zea_i a) f f1 f2 = f a) ∧
         (∀a f f1 f2. Zea_CASE (Zea_m a) f f1 f2 = f1 a) ∧
         ∀a f f1 f2. Zea_CASE (Zea_r a) f f1 f2 = f2 a

   [Zea_size_def]  Definition

      |- (∀a. Zea_size (Zea_i a) = 1 + pair_size Zsize_size (λv. 0) a) ∧
         (∀a. Zea_size (Zea_m a) = 1 + pair_size Zsize_size (λv. 0) a) ∧
         ∀a. Zea_size (Zea_r a) = 1 + pair_size Zsize_size Zreg_size a

   [Zeflags2string_def]  Definition

      |- (Zeflags2string Z_CF = "Z_CF") ∧ (Zeflags2string Z_PF = "Z_PF") ∧
         (Zeflags2string Z_AF = "Z_AF") ∧ (Zeflags2string Z_ZF = "Z_ZF") ∧
         (Zeflags2string Z_SF = "Z_SF") ∧ (Zeflags2string Z_OF = "Z_OF")

   [Zeflags_BIJ]  Definition

      |- (∀a. num2Zeflags (Zeflags2num a) = a) ∧
         ∀r. (λn. n < 6) r ⇔ (Zeflags2num (num2Zeflags r) = r)

   [Zeflags_CASE]  Definition

      |- ∀x v0 v1 v2 v3 v4 v5.
           (case x of
              Z_CF => v0
            | Z_PF => v1
            | Z_AF => v2
            | Z_ZF => v3
            | Z_SF => v4
            | Z_OF => v5) =
           (λm.
              if m < 2 then if m = 0 then v0 else v1
              else if m < 3 then v2
              else if m < 4 then v3
              else if m = 4 then v4
              else v5) (Zeflags2num x)

   [Zeflags_TY_DEF]  Definition

      |- ∃rep. TYPE_DEFINITION (λn. n < 6) rep

   [Zeflags_size_def]  Definition

      |- ∀x. Zeflags_size x = 0

   [Zimm_rm_TY_DEF]  Definition

      |- ∃rep.
           TYPE_DEFINITION
             (λa0.
                ∀'Zimm_rm' .
                  (∀a0.
                     (∃a.
                        a0 =
                        (λa.
                           ind_type$CONSTR 0 (a,ARB) (λn. ind_type$BOTTOM))
                          a) ∨
                     (∃a.
                        a0 =
                        (λa.
                           ind_type$CONSTR (SUC 0) (ARB,a)
                             (λn. ind_type$BOTTOM)) a) ⇒
                     'Zimm_rm' a0) ⇒
                  'Zimm_rm' a0) rep

   [Zimm_rm_case_def]  Definition

      |- (∀a f f1. Zimm_rm_CASE (Zimm a) f f1 = f a) ∧
         ∀a f f1. Zimm_rm_CASE (Zrm a) f f1 = f1 a

   [Zimm_rm_size_def]  Definition

      |- (∀a. Zimm_rm_size (Zimm a) = 1) ∧
         ∀a. Zimm_rm_size (Zrm a) = 1 + Zrm_size a

   [Zinst_TY_DEF]  Definition

      |- ∃rep.
           TYPE_DEFINITION
             (λa0.
                ∀'Zinst' .
                  (∀a0.
                     (∃a.
                        a0 =
                        (λa.
                           ind_type$CONSTR 0 (a,ARB) (λn. ind_type$BOTTOM))
                          a) ∨
                     (∃a.
                        a0 =
                        (λa.
                           ind_type$CONSTR (SUC 0) (ARB,a)
                             (λn. ind_type$BOTTOM)) a) ⇒
                     'Zinst' a0) ⇒
                  'Zinst' a0) rep

   [Zinst_case_def]  Definition

      |- (∀a f f1. Zinst_CASE (Zdec_fail a) f f1 = f a) ∧
         ∀a f f1. Zinst_CASE (Zfull_inst a) f f1 = f1 a

   [Zinst_size_def]  Definition

      |- (∀a. Zinst_size (Zdec_fail a) = 1 + list_size char_size a) ∧
         ∀a.
           Zinst_size (Zfull_inst a) =
           1 +
           pair_size (list_size (λv. 0))
             (pair_size instruction_size (list_size (λv. 0))) a

   [Zmonop_name_BIJ]  Definition

      |- (∀a. num2Zmonop_name (Zmonop_name2num a) = a) ∧
         ∀r. (λn. n < 4) r ⇔ (Zmonop_name2num (num2Zmonop_name r) = r)

   [Zmonop_name_CASE]  Definition

      |- ∀x v0 v1 v2 v3.
           (case x of Zdec => v0 | Zinc => v1 | Znot => v2 | Zneg => v3) =
           (λm.
              if m < 1 then v0
              else if m < 2 then v1
              else if m = 2 then v2
              else v3) (Zmonop_name2num x)

   [Zmonop_name_TY_DEF]  Definition

      |- ∃rep. TYPE_DEFINITION (λn. n < 4) rep

   [Zmonop_name_size_def]  Definition

      |- ∀x. Zmonop_name_size x = 0

   [Zreg_BIJ]  Definition

      |- (∀a. num2Zreg (Zreg2num a) = a) ∧
         ∀r. (λn. n < 16) r ⇔ (Zreg2num (num2Zreg r) = r)

   [Zreg_CASE]  Definition

      |- ∀x v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15.
           (case x of
              RAX => v0
            | RCX => v1
            | RDX => v2
            | RBX => v3
            | RSP => v4
            | RBP => v5
            | RSI => v6
            | RDI => v7
            | zR8 => v8
            | zR9 => v9
            | zR10 => v10
            | zR11 => v11
            | zR12 => v12
            | zR13 => v13
            | zR14 => v14
            | zR15 => v15) =
           (λm.
              if m < 7 then
                if m < 3 then
                  if m < 1 then v0 else if m = 1 then v1 else v2
                else if m < 4 then v3
                else if m < 5 then v4
                else if m = 5 then v5
                else v6
              else if m < 11 then
                if m < 8 then v7
                else if m < 9 then v8
                else if m = 9 then v9
                else v10
              else if m < 13 then if m = 11 then v11 else v12
              else if m < 14 then v13
              else if m = 14 then v14
              else v15) (Zreg2num x)

   [Zreg_TY_DEF]  Definition

      |- ∃rep. TYPE_DEFINITION (λn. n < 16) rep

   [Zreg_size_def]  Definition

      |- ∀x. Zreg_size x = 0

   [Zrm_TY_DEF]  Definition

      |- ∃rep.
           TYPE_DEFINITION
             (λa0.
                ∀'Zrm' .
                  (∀a0.
                     (∃a.
                        a0 =
                        (λa.
                           ind_type$CONSTR 0 (a,ARB) (λn. ind_type$BOTTOM))
                          a) ∨
                     (∃a.
                        a0 =
                        (λa.
                           ind_type$CONSTR (SUC 0) (ARB,a)
                             (λn. ind_type$BOTTOM)) a) ⇒
                     'Zrm' a0) ⇒
                  'Zrm' a0) rep

   [Zrm_case_def]  Definition

      |- (∀a f f1. Zrm_CASE (Zm a) f f1 = f a) ∧
         ∀a f f1. Zrm_CASE (Zr a) f f1 = f1 a

   [Zrm_size_def]  Definition

      |- (∀a.
            Zrm_size (Zm a) =
            1 +
            pair_size (option_size (pair_size (λv. 0) Zreg_size))
              (pair_size Zbase_size (λv. 0)) a) ∧
         ∀a. Zrm_size (Zr a) = 1 + Zreg_size a

   [Zsize_TY_DEF]  Definition

      |- ∃rep.
           TYPE_DEFINITION
             (λa0.
                ∀'Zsize' .
                  (∀a0.
                     (a0 = ind_type$CONSTR 0 ARB (λn. ind_type$BOTTOM)) ∨
                     (a0 =
                      ind_type$CONSTR (SUC 0) ARB (λn. ind_type$BOTTOM)) ∨
                     (a0 =
                      ind_type$CONSTR (SUC (SUC 0)) ARB
                        (λn. ind_type$BOTTOM)) ∨
                     (∃a.
                        a0 =
                        (λa.
                           ind_type$CONSTR (SUC (SUC (SUC 0))) a
                             (λn. ind_type$BOTTOM)) a) ⇒
                     'Zsize' a0) ⇒
                  'Zsize' a0) rep

   [Zsize_case_def]  Definition

      |- (∀v v1 v2 f. Zsize_CASE Z16 v v1 v2 f = v) ∧
         (∀v v1 v2 f. Zsize_CASE Z32 v v1 v2 f = v1) ∧
         (∀v v1 v2 f. Zsize_CASE Z64 v v1 v2 f = v2) ∧
         ∀a v v1 v2 f. Zsize_CASE (Z8 a) v v1 v2 f = f a

   [Zsize_size_def]  Definition

      |- (Zsize_size Z16 = 0) ∧ (Zsize_size Z32 = 0) ∧
         (Zsize_size Z64 = 0) ∧ ∀a. Zsize_size (Z8 a) = 1 + bool_size a

   [Zsize_width_def]  Definition

      |- ∀size.
           Zsize_width size =
           case size of Z16 => 16 | Z32 => 32 | Z64 => 64 | Z8 v => 8

   [add_with_carry_out_def]  Definition

      |- ∀size x y.
           add_with_carry_out (size,x,y) =
           (x + y,value_width size ≤ w2n x + w2n y,
            word_signed_overflow_add (size,x,y))

   [bitify8_def]  Definition

      |- ∀b7 b6 b5 b4 b3 b2 b1 b0.
           bitify8 (b7,b6,b5,b4,b3,b2,b1,b0) =
           v2w [b7; b6; b5; b4; b3; b2; b1; b0]

   [boolify8_def]  Definition

      |- ∀w.
           boolify8 w =
           (word_bit 7 w,word_bit 6 w,word_bit 5 w,word_bit 4 w,
            word_bit 3 w,word_bit 2 w,word_bit 1 w,word_bit 0 w)

   [call_dest_from_ea_def]  Definition

      |- ∀ea.
           call_dest_from_ea ea =
           (λstate.
              case ea of
                Zea_i (v3,i) => (state.RIP + i,state)
              | Zea_m (v5,a) => mem64 a state
              | Zea_r (v7,r) => (state.REG r,state))

   [checkIcache_def]  Definition

      |- ∀n.
           checkIcache n =
           (λstate.
              FOR
                (0,n − 1,
                 (λi state.
                    (let v = state.RIP + n2w i
                     in
                       if state.MEM v ≠ state.ICACHE v then
                         raise'exception (FAIL "icache miss") state
                       else ((),state)))) state)

   [dfn'Zbinop_def]  Definition

      |- ∀bop size dst_src.
           dfn'Zbinop (bop,size,dst_src) =
           (λstate.
              (let (v,s) = read_dest_src_ea (size,dst_src) state in
               let (ea,val_dst,val_src) = v
               in
                 write_binop (size,bop,val_dst,val_src,ea) s))

   [dfn'Zcall_def]  Definition

      |- ∀imm_rm.
           dfn'Zcall imm_rm =
           (λstate.
              (let s = SND (x64_push_rip state)
               in
                 jump_to_ea (FST (ea_Zimm_rm (Z64,imm_rm) s)) s))

   [dfn'Zcmpxchg_def]  Definition

      |- ∀size rm r.
           dfn'Zcmpxchg (size,rm,r) =
           (λstate.
              (let ea_src = Zea_r (size,r) in
               let v = FST (ea_Zrm (size,rm) state) in
               let (v0,s) = EA v state in
               let (v1,s) = EA ea_src s in
               let s = SND (write_binop (size,Zcmp,v1,v0,ea_src) s)
               in
                 if v1 = v0 then
                   (let (v0,s) = EA ea_src s in write'EA (v0,v) s)
                 else write'EA (v0,Zea_r (size,RAX)) s))

   [dfn'Zcpuid_def]  Definition

      |- ∀state.
           dfn'Zcpuid state =
           (let s = state with ICACHE := state.MEM in
            let s = s with REG := (RAX =+ ARB) s.REG in
            let s = s with REG := (RBX =+ ARB) s.REG in
            let s = s with REG := (RCX =+ ARB) s.REG
            in
              ((),s with REG := (RDX =+ ARB) s.REG))

   [dfn'Zdiv_def]  Definition

      |- ∀size rm.
           dfn'Zdiv (size,rm) =
           (λstate.
              (let w = value_width size in
               let ea_eax = Zea_r (size,RAX) in
               let ea_edx = Zea_r (size,RAX) in
               let (v,s) = EA ea_eax state in
               let (v,s) =
                     (let (v0,s) = EA ea_edx s in (w2n v * w + w2n v0,s))
               in
               let (v0,s) =
                     (let (v,s) = EA (FST (ea_Zrm (size,rm) s)) s
                      in
                        (w2n v,s))
               in
               let q = v DIV v0
               in
                 erase_eflags
                   (SND
                      (write'EA (n2w (v MOD v0),ea_edx)
                         (SND
                            (write'EA (n2w q,ea_eax)
                               (if (v0 = 0) ∨ w ≤ q then
                                  SND (raise'exception (FAIL "division") s)
                                else s)))))))

   [dfn'Zjcc_def]  Definition

      |- ∀cond imm.
           dfn'Zjcc (cond,imm) =
           (λstate.
              (let (v,s) = read_cond cond state
               in
                 ((),if v then s with RIP := s.RIP + imm else s)))

   [dfn'Zjmp_def]  Definition

      |- ∀rm.
           dfn'Zjmp rm =
           (λstate.
              (let (v,s) = EA (FST (ea_Zrm (Z64,rm) state)) state
               in
                 ((),s with RIP := v)))

   [dfn'Zlea_def]  Definition

      |- ∀size dst_src.
           dfn'Zlea (size,dst_src) =
           (λstate.
              write'EA
                (get_ea_address (FST (ea_Zsrc (size,dst_src) state)),
                 FST (ea_Zdest (size,dst_src) state)) state)

   [dfn'Zloop_def]  Definition

      |- ∀cond imm.
           dfn'Zloop (cond,imm) =
           (λstate.
              (let v = state.REG RCX − 1w in
               let (v0,s) =
                     read_cond cond
                       (state with REG := (RCX =+ v) state.REG)
               in
                 ((),
                  if v ≠ 0w ∧ v0 then s with RIP := s.RIP + imm else s)))

   [dfn'Zmonop_def]  Definition

      |- ∀mop size rm.
           dfn'Zmonop (mop,size,rm) =
           (λstate.
              (let v = FST (ea_Zrm (size,rm) state) in
               let (v0,s) = EA v state
               in
                 write_monop (size,mop,v0,v) s))

   [dfn'Zmov_def]  Definition

      |- ∀cond size dst_src.
           dfn'Zmov (cond,size,dst_src) =
           (λstate.
              (let (v,s) = read_cond cond state
               in
                 if v then
                   (let (v0,s0) = EA (FST (ea_Zsrc (size,dst_src) s)) s
                    in
                      write'EA (v0,FST (ea_Zdest (size,dst_src) s)) s0)
                 else ((),s)))

   [dfn'Zmovzx_def]  Definition

      |- ∀size1 dst_src size2.
           dfn'Zmovzx (size1,dst_src,size2) =
           (λstate.
              (let (v,s) =
                     (let (v0,s) =
                            EA (FST (ea_Zsrc (size1,dst_src) state)) state
                      in
                        ((v0,FST (ea_Zdest (size2,dst_src) state)),s))
               in
                 write'EA v s))

   [dfn'Zmul_def]  Definition

      |- ∀size rm.
           dfn'Zmul (size,rm) =
           (λstate.
              (let ea_eax = Zea_r (size,RAX) in
               let (v,s) = EA ea_eax state in
               let (v0,s) = EA (FST (ea_Zrm (size,rm) s)) s
               in
                 erase_eflags
                   (case size of
                      Z16 =>
                        SND
                          (write'EA
                             (n2w (w2n v * w2n v0 DIV value_width size),
                              Zea_r (size,RDX))
                             (SND (write'EA (v * v0,ea_eax) s)))
                    | Z32 =>
                        SND
                          (write'EA
                             (n2w (w2n v * w2n v0 DIV value_width size),
                              Zea_r (size,RDX))
                             (SND (write'EA (v * v0,ea_eax) s)))
                    | Z64 =>
                        SND
                          (write'EA
                             (n2w (w2n v * w2n v0 DIV value_width size),
                              Zea_r (size,RDX))
                             (SND (write'EA (v * v0,ea_eax) s)))
                    | Z8 v2 => SND (write'EA (v * v0,Zea_r (Z16,RAX)) s))))

   [dfn'Znop_def]  Definition

      |- dfn'Znop = ()

   [dfn'Zpop_def]  Definition

      |- ∀rm. dfn'Zpop rm = (λstate. x64_pop rm state)

   [dfn'Zpush_def]  Definition

      |- ∀imm_rm. dfn'Zpush imm_rm = (λstate. x64_push imm_rm state)

   [dfn'Zret_def]  Definition

      |- ∀imm.
           dfn'Zret imm = (λstate. x64_drop imm (SND (x64_pop_rip state)))

   [dfn'Zxadd_def]  Definition

      |- ∀size rm r.
           dfn'Zxadd (size,rm,r) =
           (λstate.
              (let ea_src = Zea_r (size,r) in
               let v = FST (ea_Zrm (size,rm) state) in
               let (v0,s) = EA ea_src state in
               let (v1,s) = EA v s
               in
                 write_binop (size,Zadd,v0,v1,v)
                   (SND (write'EA (v1,ea_src) s))))

   [dfn'Zxchg_def]  Definition

      |- ∀size rm r.
           dfn'Zxchg (size,rm,r) =
           (λstate.
              (let ea_src = Zea_r (size,r) in
               let v = FST (ea_Zrm (size,rm) state) in
               let (v0,s) = EA ea_src state in
               let (v1,s) = EA v s
               in
                 write'EA (v0,v) (SND (write'EA (v1,ea_src) s))))

   [ea_Zdest_def]  Definition

      |- ∀size ds.
           ea_Zdest (size,ds) =
           (λstate.
              case ds of
                Zr_rm (r,v4) => (Zea_r (size,r),state)
              | Zrm_i (rm,v6) => (FST (ea_Zrm (size,rm) state),state)
              | Zrm_r (rm_1,v8) => (FST (ea_Zrm (size,rm_1) state),state))

   [ea_Zimm_rm_def]  Definition

      |- ∀size imm_rm.
           ea_Zimm_rm (size,imm_rm) =
           (λstate.
              case imm_rm of
                Zimm imm => (Zea_i (size,imm),state)
              | Zrm rm => (FST (ea_Zrm (size,rm) state),state))

   [ea_Zrm_def]  Definition

      |- ∀size rm.
           ea_Zrm (size,rm) =
           (λstate.
              case rm of
                Zm (index,base,displacement) =>
                  (Zea_m
                     (size,
                      FST (ea_index index state) +
                      FST (ea_base base state) + displacement),state)
              | Zr r => (Zea_r (size,r),state))

   [ea_Zsrc_def]  Definition

      |- ∀size ds.
           ea_Zsrc (size,ds) =
           (λstate.
              case ds of
                Zr_rm (v3,rm) => (FST (ea_Zrm (size,rm) state),state)
              | Zrm_i (v5,i) => (Zea_i (size,i),state)
              | Zrm_r (v7,r) => (Zea_r (size,r),state))

   [ea_base_def]  Definition

      |- ∀base.
           ea_base base =
           (λstate.
              case base of
                ZnoBase => (0w,state)
              | ZregBase b => (state.REG b,state)
              | ZripBase => (state.RIP,state))

   [ea_index_def]  Definition

      |- ∀index.
           ea_index index =
           (λstate.
              case index of
                NONE => (0w,state)
              | SOME (scale,idx) => (1w ≪ w2n scale * state.REG idx,state))

   [erase_eflags_def]  Definition

      |- ∀state. erase_eflags state = ((),state with EFLAGS := K NONE)

   [exception_TY_DEF]  Definition

      |- ∃rep.
           TYPE_DEFINITION
             (λa0.
                ∀'exception' .
                  (∀a0.
                     (∃a.
                        a0 =
                        (λa.
                           ind_type$CONSTR 0 (a,ARB) (λn. ind_type$BOTTOM))
                          a) ∨
                     (∃a.
                        a0 =
                        (λa.
                           ind_type$CONSTR (SUC 0) (ARB,a)
                             (λn. ind_type$BOTTOM)) a) ∨
                     (∃a.
                        a0 =
                        (λa.
                           ind_type$CONSTR (SUC (SUC 0)) (a,ARB)
                             (λn. ind_type$BOTTOM)) a) ∨
                     (a0 =
                      ind_type$CONSTR (SUC (SUC (SUC 0))) (ARB,ARB)
                        (λn. ind_type$BOTTOM)) ⇒
                     'exception' a0) ⇒
                  'exception' a0) rep

   [exception_case_def]  Definition

      |- (∀a f f1 f2 v. exception_CASE (BadFlagAccess a) f f1 f2 v = f a) ∧
         (∀a f f1 f2 v. exception_CASE (BadMemAccess a) f f1 f2 v = f1 a) ∧
         (∀a f f1 f2 v. exception_CASE (FAIL a) f f1 f2 v = f2 a) ∧
         ∀f f1 f2 v. exception_CASE NoException f f1 f2 v = v

   [exception_size_def]  Definition

      |- (∀a.
            exception_size (BadFlagAccess a) = 1 + list_size char_size a) ∧
         (∀a. exception_size (BadMemAccess a) = 1) ∧
         (∀a. exception_size (FAIL a) = 1 + list_size char_size a) ∧
         (exception_size NoException = 0)

   [full_immediate_def]  Definition

      |- ∀size strm.
           full_immediate (size,strm) =
           if size = Z64 then immediate64 strm else immediate (size,strm)

   [get_ea_address_def]  Definition

      |- ∀ea.
           get_ea_address ea =
           case ea of Zea_i v => 0w | Zea_m (v5,a) => a | Zea_r v2 => 0w

   [immediate16_def]  Definition

      |- ∀strm.
           immediate16 strm =
           case strm of
             [] => ARB
           | [b1] => ARB
           | b1::b2::t => (sw2sw (b2 @@ b1),t)

   [immediate32_def]  Definition

      |- ∀strm.
           immediate32 strm =
           case strm of
             [] => ARB
           | [b1] => ARB
           | [b1; b2] => ARB
           | [b1; b2; b3] => ARB
           | b1::b2::b3::b4::t => (sw2sw (b4 @@ b3 @@ b2 @@ b1),t)

   [immediate64_def]  Definition

      |- ∀strm.
           immediate64 strm =
           case strm of
             [] => ARB
           | [b1] => ARB
           | [b1; b2] => ARB
           | [b1; b2; b3] => ARB
           | [b1; b2; b3; b4] => ARB
           | [b1; b2; b3; b4; b5] => ARB
           | [b1; b2; b3; b4; b5; b6] => ARB
           | [b1; b2; b3; b4; b5; b6; b7] => ARB
           | b1::b2::b3::b4::b5::b6::b7::b8::t =>
               (b8 @@ b7 @@ b6 @@ b5 @@ b4 @@ b3 @@ b2 @@ b1,t)

   [immediate8_def]  Definition

      |- ∀strm.
           immediate8 strm = case strm of [] => ARB | b::t => (sw2sw b,t)

   [immediate_def]  Definition

      |- ∀size strm.
           immediate (size,strm) =
           case size of
             Z16 => immediate16 strm
           | Z32 => immediate32 strm
           | Z64 => immediate32 strm
           | Z8 v1 => immediate8 strm

   [instruction_TY_DEF]  Definition

      |- ∃rep.
           TYPE_DEFINITION
             (λa0.
                ∀'instruction' .
                  (∀a0.
                     (∃a.
                        a0 =
                        (λa.
                           ind_type$CONSTR 0
                             (a,ARB,ARB,ARB,ARB,ARB,ARB,ARB,ARB,ARB,ARB)
                             (λn. ind_type$BOTTOM)) a) ∨
                     (∃a.
                        a0 =
                        (λa.
                           ind_type$CONSTR (SUC 0)
                             (ARB,a,ARB,ARB,ARB,ARB,ARB,ARB,ARB,ARB,ARB)
                             (λn. ind_type$BOTTOM)) a) ∨
                     (∃a.
                        a0 =
                        (λa.
                           ind_type$CONSTR (SUC (SUC 0))
                             (ARB,ARB,a,ARB,ARB,ARB,ARB,ARB,ARB,ARB,ARB)
                             (λn. ind_type$BOTTOM)) a) ∨
                     (a0 =
                      ind_type$CONSTR (SUC (SUC (SUC 0)))
                        (ARB,ARB,ARB,ARB,ARB,ARB,ARB,ARB,ARB,ARB,ARB)
                        (λn. ind_type$BOTTOM)) ∨
                     (∃a.
                        a0 =
                        (λa.
                           ind_type$CONSTR (SUC (SUC (SUC (SUC 0))))
                             (ARB,ARB,ARB,a,ARB,ARB,ARB,ARB,ARB,ARB,ARB)
                             (λn. ind_type$BOTTOM)) a) ∨
                     (∃a.
                        a0 =
                        (λa.
                           ind_type$CONSTR (SUC (SUC (SUC (SUC (SUC 0)))))
                             (ARB,ARB,ARB,ARB,a,ARB,ARB,ARB,ARB,ARB,ARB)
                             (λn. ind_type$BOTTOM)) a) ∨
                     (∃a.
                        a0 =
                        (λa.
                           ind_type$CONSTR
                             (SUC (SUC (SUC (SUC (SUC (SUC 0))))))
                             (ARB,ARB,ARB,ARB,ARB,a,ARB,ARB,ARB,ARB,ARB)
                             (λn. ind_type$BOTTOM)) a) ∨
                     (∃a.
                        a0 =
                        (λa.
                           ind_type$CONSTR
                             (SUC (SUC (SUC (SUC (SUC (SUC (SUC 0)))))))
                             (ARB,ARB,ARB,ARB,ARB,ARB,a,ARB,ARB,ARB,ARB)
                             (λn. ind_type$BOTTOM)) a) ∨
                     (∃a.
                        a0 =
                        (λa.
                           ind_type$CONSTR
                             (SUC
                                (SUC
                                   (SUC (SUC (SUC (SUC (SUC (SUC 0))))))))
                             (ARB,ARB,ARB,ARB,a,ARB,ARB,ARB,ARB,ARB,ARB)
                             (λn. ind_type$BOTTOM)) a) ∨
                     (∃a.
                        a0 =
                        (λa.
                           ind_type$CONSTR
                             (SUC
                                (SUC
                                   (SUC
                                      (SUC
                                         (SUC
                                            (SUC (SUC (SUC (SUC 0)))))))))
                             (ARB,ARB,ARB,ARB,ARB,ARB,ARB,a,ARB,ARB,ARB)
                             (λn. ind_type$BOTTOM)) a) ∨
                     (∃a.
                        a0 =
                        (λa.
                           ind_type$CONSTR
                             (SUC
                                (SUC
                                   (SUC
                                      (SUC
                                         (SUC
                                            (SUC
                                               (SUC
                                                  (SUC
                                                     (SUC (SUC 0))))))))))
                             (ARB,ARB,ARB,ARB,ARB,ARB,ARB,ARB,a,ARB,ARB)
                             (λn. ind_type$BOTTOM)) a) ∨
                     (∃a.
                        a0 =
                        (λa.
                           ind_type$CONSTR
                             (SUC
                                (SUC
                                   (SUC
                                      (SUC
                                         (SUC
                                            (SUC
                                               (SUC
                                                  (SUC
                                                     (SUC
                                                        (SUC
                                                           (SUC
                                                              0)))))))))))
                             (ARB,ARB,ARB,ARB,ARB,ARB,ARB,ARB,ARB,a,ARB)
                             (λn. ind_type$BOTTOM)) a) ∨
                     (∃a.
                        a0 =
                        (λa.
                           ind_type$CONSTR
                             (SUC
                                (SUC
                                   (SUC
                                      (SUC
                                         (SUC
                                            (SUC
                                               (SUC
                                                  (SUC
                                                     (SUC
                                                        (SUC
                                                           (SUC
                                                              (SUC
                                                                 0))))))))))))
                             (ARB,ARB,ARB,a,ARB,ARB,ARB,ARB,ARB,ARB,ARB)
                             (λn. ind_type$BOTTOM)) a) ∨
                     (a0 =
                      ind_type$CONSTR
                        (SUC
                           (SUC
                              (SUC
                                 (SUC
                                    (SUC
                                       (SUC
                                          (SUC
                                             (SUC
                                                (SUC
                                                   (SUC
                                                      (SUC
                                                         (SUC
                                                            (SUC
                                                               0)))))))))))))
                        (ARB,ARB,ARB,ARB,ARB,ARB,ARB,ARB,ARB,ARB,ARB)
                        (λn. ind_type$BOTTOM)) ∨
                     (∃a.
                        a0 =
                        (λa.
                           ind_type$CONSTR
                             (SUC
                                (SUC
                                   (SUC
                                      (SUC
                                         (SUC
                                            (SUC
                                               (SUC
                                                  (SUC
                                                     (SUC
                                                        (SUC
                                                           (SUC
                                                              (SUC
                                                                 (SUC
                                                                    (SUC
                                                                       0))))))))))))))
                             (ARB,ARB,ARB,ARB,ARB,a,ARB,ARB,ARB,ARB,ARB)
                             (λn. ind_type$BOTTOM)) a) ∨
                     (∃a.
                        a0 =
                        (λa.
                           ind_type$CONSTR
                             (SUC
                                (SUC
                                   (SUC
                                      (SUC
                                         (SUC
                                            (SUC
                                               (SUC
                                                  (SUC
                                                     (SUC
                                                        (SUC
                                                           (SUC
                                                              (SUC
                                                                 (SUC
                                                                    (SUC
                                                                       (SUC
                                                                          0)))))))))))))))
                             (ARB,a,ARB,ARB,ARB,ARB,ARB,ARB,ARB,ARB,ARB)
                             (λn. ind_type$BOTTOM)) a) ∨
                     (∃a.
                        a0 =
                        (λa.
                           ind_type$CONSTR
                             (SUC
                                (SUC
                                   (SUC
                                      (SUC
                                         (SUC
                                            (SUC
                                               (SUC
                                                  (SUC
                                                     (SUC
                                                        (SUC
                                                           (SUC
                                                              (SUC
                                                                 (SUC
                                                                    (SUC
                                                                       (SUC
                                                                          (SUC
                                                                             0))))))))))))))))
                             (ARB,ARB,ARB,ARB,ARB,ARB,ARB,ARB,ARB,ARB,a)
                             (λn. ind_type$BOTTOM)) a) ∨
                     (∃a.
                        a0 =
                        (λa.
                           ind_type$CONSTR
                             (SUC
                                (SUC
                                   (SUC
                                      (SUC
                                         (SUC
                                            (SUC
                                               (SUC
                                                  (SUC
                                                     (SUC
                                                        (SUC
                                                           (SUC
                                                              (SUC
                                                                 (SUC
                                                                    (SUC
                                                                       (SUC
                                                                          (SUC
                                                                             (SUC
                                                                                0)))))))))))))))))
                             (ARB,ARB,a,ARB,ARB,ARB,ARB,ARB,ARB,ARB,ARB)
                             (λn. ind_type$BOTTOM)) a) ∨
                     (∃a.
                        a0 =
                        (λa.
                           ind_type$CONSTR
                             (SUC
                                (SUC
                                   (SUC
                                      (SUC
                                         (SUC
                                            (SUC
                                               (SUC
                                                  (SUC
                                                     (SUC
                                                        (SUC
                                                           (SUC
                                                              (SUC
                                                                 (SUC
                                                                    (SUC
                                                                       (SUC
                                                                          (SUC
                                                                             (SUC
                                                                                (SUC
                                                                                   0))))))))))))))))))
                             (ARB,ARB,a,ARB,ARB,ARB,ARB,ARB,ARB,ARB,ARB)
                             (λn. ind_type$BOTTOM)) a) ⇒
                     'instruction' a0) ⇒
                  'instruction' a0) rep

   [instruction_case_def]  Definition

      |- (∀a f f1 f2 v f3 f4 f5 f6 f7 f8 f9 f10 f11 v1 f12 f13 f14 f15 f16.
            instruction_CASE (Zbinop a) f f1 f2 v f3 f4 f5 f6 f7 f8 f9 f10
              f11 v1 f12 f13 f14 f15 f16 =
            f a) ∧
         (∀a f f1 f2 v f3 f4 f5 f6 f7 f8 f9 f10 f11 v1 f12 f13 f14 f15 f16.
            instruction_CASE (Zcall a) f f1 f2 v f3 f4 f5 f6 f7 f8 f9 f10
              f11 v1 f12 f13 f14 f15 f16 =
            f1 a) ∧
         (∀a f f1 f2 v f3 f4 f5 f6 f7 f8 f9 f10 f11 v1 f12 f13 f14 f15 f16.
            instruction_CASE (Zcmpxchg a) f f1 f2 v f3 f4 f5 f6 f7 f8 f9
              f10 f11 v1 f12 f13 f14 f15 f16 =
            f2 a) ∧
         (∀f f1 f2 v f3 f4 f5 f6 f7 f8 f9 f10 f11 v1 f12 f13 f14 f15 f16.
            instruction_CASE Zcpuid f f1 f2 v f3 f4 f5 f6 f7 f8 f9 f10 f11
              v1 f12 f13 f14 f15 f16 =
            v) ∧
         (∀a f f1 f2 v f3 f4 f5 f6 f7 f8 f9 f10 f11 v1 f12 f13 f14 f15 f16.
            instruction_CASE (Zdiv a) f f1 f2 v f3 f4 f5 f6 f7 f8 f9 f10
              f11 v1 f12 f13 f14 f15 f16 =
            f3 a) ∧
         (∀a f f1 f2 v f3 f4 f5 f6 f7 f8 f9 f10 f11 v1 f12 f13 f14 f15 f16.
            instruction_CASE (Zjcc a) f f1 f2 v f3 f4 f5 f6 f7 f8 f9 f10
              f11 v1 f12 f13 f14 f15 f16 =
            f4 a) ∧
         (∀a f f1 f2 v f3 f4 f5 f6 f7 f8 f9 f10 f11 v1 f12 f13 f14 f15 f16.
            instruction_CASE (Zjmp a) f f1 f2 v f3 f4 f5 f6 f7 f8 f9 f10
              f11 v1 f12 f13 f14 f15 f16 =
            f5 a) ∧
         (∀a f f1 f2 v f3 f4 f5 f6 f7 f8 f9 f10 f11 v1 f12 f13 f14 f15 f16.
            instruction_CASE (Zlea a) f f1 f2 v f3 f4 f5 f6 f7 f8 f9 f10
              f11 v1 f12 f13 f14 f15 f16 =
            f6 a) ∧
         (∀a f f1 f2 v f3 f4 f5 f6 f7 f8 f9 f10 f11 v1 f12 f13 f14 f15 f16.
            instruction_CASE (Zloop a) f f1 f2 v f3 f4 f5 f6 f7 f8 f9 f10
              f11 v1 f12 f13 f14 f15 f16 =
            f7 a) ∧
         (∀a f f1 f2 v f3 f4 f5 f6 f7 f8 f9 f10 f11 v1 f12 f13 f14 f15 f16.
            instruction_CASE (Zmonop a) f f1 f2 v f3 f4 f5 f6 f7 f8 f9 f10
              f11 v1 f12 f13 f14 f15 f16 =
            f8 a) ∧
         (∀a f f1 f2 v f3 f4 f5 f6 f7 f8 f9 f10 f11 v1 f12 f13 f14 f15 f16.
            instruction_CASE (Zmov a) f f1 f2 v f3 f4 f5 f6 f7 f8 f9 f10
              f11 v1 f12 f13 f14 f15 f16 =
            f9 a) ∧
         (∀a f f1 f2 v f3 f4 f5 f6 f7 f8 f9 f10 f11 v1 f12 f13 f14 f15 f16.
            instruction_CASE (Zmovzx a) f f1 f2 v f3 f4 f5 f6 f7 f8 f9 f10
              f11 v1 f12 f13 f14 f15 f16 =
            f10 a) ∧
         (∀a f f1 f2 v f3 f4 f5 f6 f7 f8 f9 f10 f11 v1 f12 f13 f14 f15 f16.
            instruction_CASE (Zmul a) f f1 f2 v f3 f4 f5 f6 f7 f8 f9 f10
              f11 v1 f12 f13 f14 f15 f16 =
            f11 a) ∧
         (∀f f1 f2 v f3 f4 f5 f6 f7 f8 f9 f10 f11 v1 f12 f13 f14 f15 f16.
            instruction_CASE Znop f f1 f2 v f3 f4 f5 f6 f7 f8 f9 f10 f11 v1
              f12 f13 f14 f15 f16 =
            v1) ∧
         (∀a f f1 f2 v f3 f4 f5 f6 f7 f8 f9 f10 f11 v1 f12 f13 f14 f15 f16.
            instruction_CASE (Zpop a) f f1 f2 v f3 f4 f5 f6 f7 f8 f9 f10
              f11 v1 f12 f13 f14 f15 f16 =
            f12 a) ∧
         (∀a f f1 f2 v f3 f4 f5 f6 f7 f8 f9 f10 f11 v1 f12 f13 f14 f15 f16.
            instruction_CASE (Zpush a) f f1 f2 v f3 f4 f5 f6 f7 f8 f9 f10
              f11 v1 f12 f13 f14 f15 f16 =
            f13 a) ∧
         (∀a f f1 f2 v f3 f4 f5 f6 f7 f8 f9 f10 f11 v1 f12 f13 f14 f15 f16.
            instruction_CASE (Zret a) f f1 f2 v f3 f4 f5 f6 f7 f8 f9 f10
              f11 v1 f12 f13 f14 f15 f16 =
            f14 a) ∧
         (∀a f f1 f2 v f3 f4 f5 f6 f7 f8 f9 f10 f11 v1 f12 f13 f14 f15 f16.
            instruction_CASE (Zxadd a) f f1 f2 v f3 f4 f5 f6 f7 f8 f9 f10
              f11 v1 f12 f13 f14 f15 f16 =
            f15 a) ∧
         ∀a f f1 f2 v f3 f4 f5 f6 f7 f8 f9 f10 f11 v1 f12 f13 f14 f15 f16.
           instruction_CASE (Zxchg a) f f1 f2 v f3 f4 f5 f6 f7 f8 f9 f10
             f11 v1 f12 f13 f14 f15 f16 =
           f16 a

   [instruction_size_def]  Definition

      |- (∀a.
            instruction_size (Zbinop a) =
            1 +
            pair_size Zbinop_name_size
              (pair_size Zsize_size Zdest_src_size) a) ∧
         (∀a. instruction_size (Zcall a) = 1 + Zimm_rm_size a) ∧
         (∀a.
            instruction_size (Zcmpxchg a) =
            1 + pair_size Zsize_size (pair_size Zrm_size Zreg_size) a) ∧
         (instruction_size Zcpuid = 0) ∧
         (∀a.
            instruction_size (Zdiv a) =
            1 + pair_size Zsize_size Zrm_size a) ∧
         (∀a.
            instruction_size (Zjcc a) =
            1 + pair_size Zcond_size (λv. 0) a) ∧
         (∀a. instruction_size (Zjmp a) = 1 + Zrm_size a) ∧
         (∀a.
            instruction_size (Zlea a) =
            1 + pair_size Zsize_size Zdest_src_size a) ∧
         (∀a.
            instruction_size (Zloop a) =
            1 + pair_size Zcond_size (λv. 0) a) ∧
         (∀a.
            instruction_size (Zmonop a) =
            1 +
            pair_size Zmonop_name_size (pair_size Zsize_size Zrm_size) a) ∧
         (∀a.
            instruction_size (Zmov a) =
            1 +
            pair_size Zcond_size (pair_size Zsize_size Zdest_src_size) a) ∧
         (∀a.
            instruction_size (Zmovzx a) =
            1 +
            pair_size Zsize_size (pair_size Zdest_src_size Zsize_size) a) ∧
         (∀a.
            instruction_size (Zmul a) =
            1 + pair_size Zsize_size Zrm_size a) ∧
         (instruction_size Znop = 0) ∧
         (∀a. instruction_size (Zpop a) = 1 + Zrm_size a) ∧
         (∀a. instruction_size (Zpush a) = 1 + Zimm_rm_size a) ∧
         (∀a. instruction_size (Zret a) = 1) ∧
         (∀a.
            instruction_size (Zxadd a) =
            1 + pair_size Zsize_size (pair_size Zrm_size Zreg_size) a) ∧
         ∀a.
           instruction_size (Zxchg a) =
           1 + pair_size Zsize_size (pair_size Zrm_size Zreg_size) a

   [isZm_def]  Definition

      |- ∀rm. isZm rm ⇔ case rm of Zm v2 => T | Zr v3 => F

   [jump_to_ea_def]  Definition

      |- ∀ea.
           jump_to_ea ea =
           (λstate.
              (let (v,s) = call_dest_from_ea ea state
               in
                 ((),s with RIP := v)))

   [maskShift_def]  Definition

      |- ∀size w.
           maskShift (size,w) =
           if size = Z64 then w2n ((5 >< 0) w) else w2n ((4 >< 0) w)

   [mem16_def]  Definition

      |- ∀addr.
           mem16 addr =
           (λstate.
              (let (v,s) = mem8 (addr + 1w) state in
               let (v0,s) = mem8 addr s
               in
                 (v @@ v0,s)))

   [mem32_def]  Definition

      |- ∀addr.
           mem32 addr =
           (λstate.
              (let (v,s) = mem16 (addr + 2w) state in
               let (v0,s) = mem16 addr s
               in
                 (v @@ v0,s)))

   [mem64_def]  Definition

      |- ∀addr.
           mem64 addr =
           (λstate.
              (let (v,s) = mem32 (addr + 4w) state in
               let (v0,s) = mem32 addr s
               in
                 (v @@ v0,s)))

   [mem8_def]  Definition

      |- ∀addr.
           mem8 addr =
           (λstate.
              case state.MEM addr of
                NONE => raise'exception (BadMemAccess addr) state
              | SOME b => (b,state))

   [prefixGroup_def]  Definition

      |- ∀b.
           prefixGroup b =
           case b of
             240w => 1
           | 242w => 1
           | 243w => 1
           | 38w => 2
           | 46w => 2
           | 54w => 2
           | 62w => 2
           | 100w => 2
           | 101w => 2
           | 102w => 3
           | 103w => 4
           | v => if (7 >< 4) b = 4w then 5 else 0

   [raise'exception_def]  Definition

      |- ∀e.
           raise'exception e =
           (λstate.
              (ARB,
               if state.exception = NoException then
                 state with exception := e
               else state))

   [readDisplacement_def]  Definition

      |- ∀Mod strm.
           readDisplacement (Mod,strm) =
           if Mod = 1w then immediate8 strm
           else if Mod = 2w then immediate32 strm
           else (0w,strm)

   [readModRM_def]  Definition

      |- ∀REX strm.
           readModRM (REX,strm) =
           case strm of
             [] => (ARB,ARB,strm)
           | v#0 ::v#1 =>
               case (boolify8 v#0 ,v#1 ) of
                 ((T,T,v6,v8,v10,v12,v14,v15),strm1) =>
                   (RexReg (REX.R,(5 >< 3) v#0 ),
                    Zr (RexReg (REX.B,(2 >< 0) v#0 )),strm1)
               | ((F,T,v6,v8,v10,v12,T,v15),strm1) =>
                   (let (displacement,strm2) =
                          readDisplacement ((7 >< 6) v#0 ,strm1)
                    in
                      (RexReg (REX.R,(5 >< 3) v#0 ),
                       Zm
                         (NONE,ZregBase (RexReg (REX.B,(2 >< 0) v#0 )),
                          displacement),strm2))
               | ((F,T,v6,v8,v10,v12,F,T),strm1) =>
                   (let (displacement,strm2) =
                          readDisplacement ((7 >< 6) v#0 ,strm1)
                    in
                      (RexReg (REX.R,(5 >< 3) v#0 ),
                       Zm
                         (NONE,ZregBase (RexReg (REX.B,(2 >< 0) v#0 )),
                          displacement),strm2))
               | ((F,T,v6,v8,v10,T,F,F),strm1) =>
                   (let (sib,strm2) = readSIB (REX,(7 >< 6) v#0 ,strm1)
                    in
                      (RexReg (REX.R,(5 >< 3) v#0 ),sib,strm2))
               | ((F,T,v6,v8,v10,F,F,F),strm1) =>
                   (let (displacement,strm2) =
                          readDisplacement ((7 >< 6) v#0 ,strm1)
                    in
                      (RexReg (REX.R,(5 >< 3) v#0 ),
                       Zm
                         (NONE,ZregBase (RexReg (REX.B,(2 >< 0) v#0 )),
                          displacement),strm2))
               | ((v2_1,F,v6,v8,v10,v12,T,v15),strm1) =>
                   (let (displacement,strm2) =
                          readDisplacement ((7 >< 6) v#0 ,strm1)
                    in
                      (RexReg (REX.R,(5 >< 3) v#0 ),
                       Zm
                         (NONE,ZregBase (RexReg (REX.B,(2 >< 0) v#0 )),
                          displacement),strm2))
               | ((T,F,v6,v8,v10,T,F,T),strm1) =>
                   (let (displacement,strm2) =
                          readDisplacement ((7 >< 6) v#0 ,strm1)
                    in
                      (RexReg (REX.R,(5 >< 3) v#0 ),
                       Zm
                         (NONE,ZregBase (RexReg (REX.B,(2 >< 0) v#0 )),
                          displacement),strm2))
               | ((F,F,v6,v8,v10,T,F,T),strm1) =>
                   (let (displacement,strm2) = immediate32 strm1
                    in
                      (RexReg (REX.R,(5 >< 3) v#0 ),
                       Zm (NONE,ZripBase,displacement),strm2))
               | ((v2_1,F,v6,v8,v10,F,F,T),strm1) =>
                   (let (displacement,strm2) =
                          readDisplacement ((7 >< 6) v#0 ,strm1)
                    in
                      (RexReg (REX.R,(5 >< 3) v#0 ),
                       Zm
                         (NONE,ZregBase (RexReg (REX.B,(2 >< 0) v#0 )),
                          displacement),strm2))
               | ((v2_1,F,v6,v8,v10,T,F,F),strm1) =>
                   (let (sib,strm2) = readSIB (REX,(7 >< 6) v#0 ,strm1)
                    in
                      (RexReg (REX.R,(5 >< 3) v#0 ),sib,strm2))
               | ((v2_1,F,v6,v8,v10,F,F,F),strm1) =>
                   (let (displacement,strm2) =
                          readDisplacement ((7 >< 6) v#0 ,strm1)
                    in
                      (RexReg (REX.R,(5 >< 3) v#0 ),
                       Zm
                         (NONE,ZregBase (RexReg (REX.B,(2 >< 0) v#0 )),
                          displacement),strm2))

   [readOpcodeModRM_def]  Definition

      |- ∀REX strm.
           readOpcodeModRM (REX,strm) =
           (let (opcode,rm,strm1) = readModRM (REX,strm)
            in
              (n2w (Zreg2num opcode MOD 8),rm,strm1))

   [readPrefix_primitive_def]  Definition

      |- readPrefix =
         WFREC
           (@R.
              WF R ∧
              ∀p s strm h strm1 group.
                (strm = h::strm1) ∧ (group = prefixGroup h) ∧ group ≠ 0 ∧
                group ≠ 5 ∧ group ∉ s ⇒
                R (group INSERT s,h::p,strm1) (s,p,strm))
           (λreadPrefix a.
              case a of
                (s,p,strm) =>
                  I
                    (case strm of
                       [] => SOME (p,F,ARB,strm)
                     | h::strm1 =>
                         (let group = prefixGroup h
                          in
                            if group = 0 then SOME (p,F,rec'REX 0w,strm)
                            else if group = 5 then
                              SOME (p,T,rec'REX ((3 >< 0) h),strm1)
                            else if group ∈ s then NONE
                            else readPrefix (group INSERT s,h::p,strm1))))

   [readPrefixes_def]  Definition

      |- ∀strm. readPrefixes strm = readPrefix (∅,[],strm)

   [readSIB_def]  Definition

      |- ∀REX Mod strm.
           readSIB (REX,Mod,strm) =
           case strm of
             [] => (ARB,strm)
           | v#0 ::v#1 =>
               (let base = RexReg (REX.B,(2 >< 0) v#0 ) in
                let index = RexReg (REX.X,(5 >< 3) v#0 ) in
                let scaled_index =
                      if index = RSP then NONE
                      else SOME ((7 >< 6) v#0 ,index)
                in
                  if base = RBP then
                    (let (displacement,strm2) =
                           readSibDisplacement (Mod,v#1 )
                     in
                       (Zm
                          (scaled_index,
                           if Mod = 0w then ZnoBase else ZregBase base,
                           displacement),strm2))
                  else
                    (let (displacement,strm2) = readDisplacement (Mod,v#1 )
                     in
                       (Zm (scaled_index,ZregBase base,displacement),
                        strm2)))

   [readSibDisplacement_def]  Definition

      |- ∀Mod strm.
           readSibDisplacement (Mod,strm) =
           if Mod = 0w then (0w,strm)
           else if Mod = 1w then immediate8 strm
           else immediate32 strm

   [read_cond_def]  Definition

      |- ∀c.
           read_cond c =
           (λstate.
              case c of
                Z_O => OF state
              | Z_NO => (let (v,s) = OF state in (¬v,s))
              | Z_B => CF state
              | Z_NB => (let (v,s) = CF state in (¬v,s))
              | Z_E => ZF state
              | Z_NE => (let (v,s) = ZF state in (¬v,s))
              | Z_NA =>
                  (case (state.EFLAGS Z_CF,state.EFLAGS Z_ZF) of
                     (NONE,NONE) =>
                       raise'exception
                         (BadFlagAccess
                            (STRCAT "read_cond: " (Zcond2string c))) state
                   | (NONE,SOME T) => (T,state)
                   | (NONE,SOME F) =>
                       raise'exception
                         (BadFlagAccess
                            (STRCAT "read_cond: " (Zcond2string c))) state
                   | (SOME T,v3) => (T,state)
                   | (SOME F,NONE) =>
                       raise'exception
                         (BadFlagAccess
                            (STRCAT "read_cond: " (Zcond2string c))) state
                   | (SOME F,SOME T) => (T,state)
                   | (SOME F,SOME F) => (F,state))
              | Z_A =>
                  (case (state.EFLAGS Z_CF,state.EFLAGS Z_ZF) of
                     (NONE,NONE) =>
                       raise'exception
                         (BadFlagAccess
                            (STRCAT "read_cond: " (Zcond2string c))) state
                   | (NONE,SOME T) => (F,state)
                   | (NONE,SOME F) =>
                       raise'exception
                         (BadFlagAccess
                            (STRCAT "read_cond: " (Zcond2string c))) state
                   | (SOME T,v3) => (F,state)
                   | (SOME F,NONE) =>
                       raise'exception
                         (BadFlagAccess
                            (STRCAT "read_cond: " (Zcond2string c))) state
                   | (SOME F,SOME T) => (F,state)
                   | (SOME F,SOME F) => (T,state))
              | Z_S => SF state
              | Z_NS => (let (v,s) = SF state in (¬v,s))
              | Z_P => PF state
              | Z_NP => (let (v,s) = PF state in (¬v,s))
              | Z_L =>
                  (let (v,s) = SF state in
                   let (v,s) = (let (v0,s) = OF s in (v ⇔ v0,s))
                   in
                     (¬v,s))
              | Z_NL =>
                  (let (v,s) = SF state in let (v0,s) = OF s in (v ⇔ v0,s))
              | Z_NG =>
                  (case (state.EFLAGS Z_SF,state.EFLAGS Z_OF) of
                     (NONE,v3) =>
                       (case state.EFLAGS Z_ZF of
                          NONE =>
                            raise'exception
                              (BadFlagAccess
                                 (STRCAT "read_cond: " (Zcond2string c)))
                              state
                        | SOME T => (T,state)
                        | SOME F =>
                            raise'exception
                              (BadFlagAccess
                                 (STRCAT "read_cond: " (Zcond2string c)))
                              state)
                   | (SOME a,NONE) =>
                       (case state.EFLAGS Z_ZF of
                          NONE =>
                            raise'exception
                              (BadFlagAccess
                                 (STRCAT "read_cond: " (Zcond2string c)))
                              state
                        | SOME T => (T,state)
                        | SOME F =>
                            raise'exception
                              (BadFlagAccess
                                 (STRCAT "read_cond: " (Zcond2string c)))
                              state)
                   | (SOME a,SOME b) =>
                       (let (v,s) = ZF state in ((a ⇎ b) ∨ v,s)))
              | Z_G =>
                  (case (state.EFLAGS Z_SF,state.EFLAGS Z_OF) of
                     (NONE,v3) =>
                       (case state.EFLAGS Z_ZF of
                          NONE =>
                            raise'exception
                              (BadFlagAccess
                                 (STRCAT "read_cond: " (Zcond2string c)))
                              state
                        | SOME T => (F,state)
                        | SOME F =>
                            raise'exception
                              (BadFlagAccess
                                 (STRCAT "read_cond: " (Zcond2string c)))
                              state)
                   | (SOME a,NONE) =>
                       (case state.EFLAGS Z_ZF of
                          NONE =>
                            raise'exception
                              (BadFlagAccess
                                 (STRCAT "read_cond: " (Zcond2string c)))
                              state
                        | SOME T => (F,state)
                        | SOME F =>
                            raise'exception
                              (BadFlagAccess
                                 (STRCAT "read_cond: " (Zcond2string c)))
                              state)
                   | (SOME a,SOME b) =>
                       (let (v,s) = ZF state in ((a ⇔ b) ∧ ¬v,s)))
              | Z_ALWAYS => (T,state))

   [read_dest_src_ea_def]  Definition

      |- ∀sd.
           read_dest_src_ea sd =
           (λstate.
              (let v = FST (ea_Zdest sd state) in
               let (v0,s) = EA v state in
               let (v0,s) =
                     (let (v1,s) = EA (FST (ea_Zsrc sd s)) s
                      in
                        ((v0,v1),s))
               in
                 ((v,v0),s)))

   [rec'REX_def]  Definition

      |- ∀x.
           rec'REX x =
           REX (word_bit 0 x) (word_bit 2 x) (word_bit 3 x) (word_bit 1 x)

   [reg'REX_def]  Definition

      |- ∀x.
           reg'REX x =
           case x of
             REX B_1 R W_1 X =>
               word_modify
                 (CURRY
                    (λ(i,_).
                       if i = 3 then W_1
                       else if i = 2 then R
                       else if i = 1 then X
                       else B_1)) 0w

   [restrictSize_def]  Definition

      |- ∀size imm.
           restrictSize (size,imm) =
           case size of
             Z16 => imm && 65535w
           | Z32 => imm && 0xFFFFFFFFw
           | Z64 => imm
           | Z8 v => imm && 255w

   [sub_with_borrow_def]  Definition

      |- ∀size x y.
           sub_with_borrow (size,x,y) =
           (x − y,x <₊ y,word_signed_overflow_sub (size,x,y))

   [value_width_def]  Definition

      |- ∀s. value_width s = 2 ** Zsize_width s

   [word_signed_overflow_add_def]  Definition

      |- ∀size a b.
           word_signed_overflow_add (size,a,b) ⇔
           (word_size_msb (size,a) ⇔ word_size_msb (size,b)) ∧
           (word_size_msb (size,a + b) ⇎ word_size_msb (size,a))

   [word_signed_overflow_sub_def]  Definition

      |- ∀size a b.
           word_signed_overflow_sub (size,a,b) ⇔
           (word_size_msb (size,a) ⇎ word_size_msb (size,b)) ∧
           (word_size_msb (size,a − b) ⇎ word_size_msb (size,a))

   [word_size_msb_def]  Definition

      |- ∀size w.
           word_size_msb (size,w) ⇔ word_bit (Zsize_width size − 1) w

   [write'AF_def]  Definition

      |- ∀b. write'AF b = (λstate. write'Eflag (b,Z_AF) state)

   [write'CF_def]  Definition

      |- ∀b. write'CF b = (λstate. write'Eflag (b,Z_CF) state)

   [write'EA_def]  Definition

      |- ∀w ea.
           write'EA (w,ea) =
           (λstate.
              case ea of
                Zea_i i => raise'exception (FAIL "write to constant") state
              | Zea_m (Z16,a) => write'mem16 ((15 >< 0) w,a) state
              | Zea_m (Z32,a) => write'mem32 ((31 >< 0) w,a) state
              | Zea_m (Z64,a) => write'mem64 (w,a) state
              | Zea_m (Z8 v5,a) => write'mem8 ((7 >< 0) w,a) state
              | Zea_r (Z16,r) =>
                  (let v = state.REG
                   in
                     ((),
                      state with
                      REG :=
                        (r =+ bit_field_insert 15 0 ((15 >< 0) w) (v r))
                          v))
              | Zea_r (Z32,r) =>
                  ((),state with REG := (r =+ w2w ((31 >< 0) w)) state.REG)
              | Zea_r (Z64,r) => ((),state with REG := (r =+ w) state.REG)
              | Zea_r (Z8 have_rex,r) =>
                  if have_rex ∨ r ∉ {RSP; RBP; RSI; RDI} then
                    (let v = state.REG
                     in
                       ((),
                        state with
                        REG :=
                          (r =+ bit_field_insert 7 0 ((7 >< 0) w) (v r))
                            v))
                  else
                    (let v = state.REG in
                     let x = num2Zreg (Zreg2num r − 4)
                     in
                       ((),
                        state with
                        REG :=
                          (x =+ bit_field_insert 15 8 ((7 >< 0) w) (v x))
                            v)))

   [write'Eflag_def]  Definition

      |- ∀b flag.
           write'Eflag (b,flag) =
           (λstate.
              ((),state with EFLAGS := (flag =+ SOME b) state.EFLAGS))

   [write'OF_def]  Definition

      |- ∀b. write'OF b = (λstate. write'Eflag (b,Z_OF) state)

   [write'PF_def]  Definition

      |- ∀b. write'PF b = (λstate. write'Eflag (b,Z_PF) state)

   [write'SF_def]  Definition

      |- ∀b. write'SF b = (λstate. write'Eflag (b,Z_SF) state)

   [write'ZF_def]  Definition

      |- ∀b. write'ZF b = (λstate. write'Eflag (b,Z_ZF) state)

   [write'mem16_def]  Definition

      |- ∀w addr.
           write'mem16 (w,addr) =
           (λstate.
              write'mem8 ((15 >< 8) w,addr + 1w)
                (SND (write'mem8 ((7 >< 0) w,addr) state)))

   [write'mem32_def]  Definition

      |- ∀w addr.
           write'mem32 (w,addr) =
           (λstate.
              write'mem16 ((31 >< 16) w,addr + 2w)
                (SND (write'mem16 ((15 >< 0) w,addr) state)))

   [write'mem64_def]  Definition

      |- ∀w addr.
           write'mem64 (w,addr) =
           (λstate.
              write'mem32 ((63 >< 32) w,addr + 4w)
                (SND (write'mem32 ((31 >< 0) w,addr) state)))

   [write'mem8_def]  Definition

      |- ∀b addr.
           write'mem8 (b,addr) =
           (λstate.
              if IS_SOME (state.MEM addr) then
                ((),state with MEM := (addr =+ SOME b) state.MEM)
              else raise'exception (BadMemAccess addr) state)

   [write'rec'REX_def]  Definition

      |- ∀_ x. write'rec'REX (_,x) = reg'REX x

   [write'reg'REX_def]  Definition

      |- ∀_ x. write'reg'REX (_,x) = rec'REX x

   [write_PF_def]  Definition

      |- ∀w.
           write_PF w = (λstate. write'PF (ByteParity ((7 >< 0) w)) state)

   [write_SF_def]  Definition

      |- ∀s_w. write_SF s_w = (λstate. write'SF (word_size_msb s_w) state)

   [write_ZF_def]  Definition

      |- ∀size w.
           write_ZF (size,w) =
           (λstate.
              write'ZF
                (case size of
                   Z16 => w2w w = 0w
                 | Z32 => w2w w = 0w
                 | Z64 => w = 0w
                 | Z8 v => w2w w = 0w) state)

   [write_arith_eflags_def]  Definition

      |- ∀size r.
           write_arith_eflags (size,r) =
           (λstate.
              (let (w,c,x) = r
               in
                 write_arith_eflags_except_CF_OF (size,w)
                   (SND (write'OF x (SND (write'CF c state))))))

   [write_arith_eflags_except_CF_OF_def]  Definition

      |- ∀size w.
           write_arith_eflags_except_CF_OF (size,w) =
           (λstate.
              FlagUnspecified Z_AF
                (SND
                   (write_ZF (size,w)
                      (SND (write_SF (size,w) (SND (write_PF w state)))))))

   [write_arith_result_def]  Definition

      |- ∀size r ea.
           write_arith_result (size,r,ea) =
           (λstate.
              write'EA (FST r,ea)
                (SND (write_arith_eflags (size,r) state)))

   [write_arith_result_no_CF_OF_def]  Definition

      |- ∀size w ea.
           write_arith_result_no_CF_OF (size,w,ea) =
           (λstate.
              write'EA (w,ea)
                (SND (write_arith_eflags_except_CF_OF (size,w) state)))

   [write_binop_def]  Definition

      |- ∀s bop x y ea.
           write_binop (s,bop,x,y,ea) =
           (λstate.
              case bop of
                Zadd =>
                  write_arith_result (s,add_with_carry_out (s,x,y),ea)
                    state
              | Zor => write_logical_result (s,x ‖ y,ea) state
              | Zadc =>
                  (let (v,s0) = CF state
                   in
                     write_arith_result_no_CF_OF
                       (s,x + y + if v then 1w else 0w,ea)
                       (SND
                          (FlagUnspecified Z_OF
                             (SND
                                (write'CF
                                   (value_width s ≤
                                    w2n x + w2n y + if v then 1 else 0)
                                   s0)))))
              | Zsbb =>
                  (let (v,s0) = CF state
                   in
                     write_arith_result_no_CF_OF
                       (s,x − (y + if v then 1w else 0w),ea)
                       (SND
                          (FlagUnspecified Z_OF
                             (SND
                                (write'CF
                                   (w2n x < w2n y + if v then 1 else 0)
                                   s0)))))
              | Zand => write_logical_result (s,x && y,ea) state
              | Zsub =>
                  write_arith_result (s,sub_with_borrow (s,x,y),ea) state
              | Zxor => write_logical_result (s,x ⊕ y,ea) state
              | Zcmp =>
                  write_arith_eflags (s,sub_with_borrow (s,x,y)) state
              | Zrol => write_result_erase_eflags (ROL (s,x,y),ea) state
              | Zror => write_result_erase_eflags (ROR (s,x,y),ea) state
              | Zrcl =>
                  raise'exception
                    (FAIL
                       (STRCAT "Binary op not implemented: "
                          (Zbinop_name2string bop))) state
              | Zrcr =>
                  raise'exception
                    (FAIL
                       (STRCAT "Binary op not implemented: "
                          (Zbinop_name2string bop))) state
              | Zshl =>
                  write_result_erase_eflags (x ≪ maskShift (s,y),ea) state
              | Zshr =>
                  write_result_erase_eflags (x ⋙ maskShift (s,y),ea) state
              | Ztest => write_logical_eflags (s,x && y) state
              | Zsar => write_result_erase_eflags (SAR (s,x,y),ea) state)

   [write_logical_eflags_def]  Definition

      |- ∀size w.
           write_logical_eflags (size,w) =
           (λstate.
              FlagUnspecified Z_AF
                (SND
                   (write_ZF (size,w)
                      (SND
                         (write_SF (size,w)
                            (SND
                               (write_PF w
                                  (SND
                                     (write'OF F
                                        (SND (write'CF F state)))))))))))

   [write_logical_result_def]  Definition

      |- ∀size w ea.
           write_logical_result (size,w,ea) =
           (λstate.
              write'EA (w,ea) (SND (write_logical_eflags (size,w) state)))

   [write_monop_def]  Definition

      |- ∀s mop x ea.
           write_monop (s,mop,x,ea) =
           (λstate.
              case mop of
                Zdec => write_arith_result_no_CF_OF (s,x − 1w,ea) state
              | Zinc => write_arith_result_no_CF_OF (s,x + 1w,ea) state
              | Znot => write'EA (¬x,ea) state
              | Zneg =>
                  FlagUnspecified Z_CF
                    (SND (write_arith_result_no_CF_OF (s,-x,ea) state)))

   [write_result_erase_eflags_def]  Definition

      |- ∀w ea.
           write_result_erase_eflags (w,ea) =
           (λstate. write'EA (w,ea) (SND (erase_eflags state)))

   [x64_decode_def]  Definition

      |- ∀strm.
           x64_decode strm =
           case readPrefixes strm of
             NONE => Zdec_fail "Bad prefix"
           | SOME (p,have_rex,REX_1,strm1) =>
               (let op_size_override = MEM 102w p
                in
                  if REX_1.W ∧ op_size_override then
                    Zdec_fail "REX.W together with override prefix"
                  else
                    case strm1 of
                      [] => Zdec_fail "No opcode"
                    | v#0 ::v#1 =>
                        case (boolify8 v#0 ,v#1 ) of
                          ((T,T,T,T,T,T,T,T),strm2) =>
                            (let size =
                                   OpSize
                                     (have_rex,REX_1.W,1w,op_size_override)
                             in
                             let (opcode,rm,strm3) =
                                   readOpcodeModRM (REX_1,strm2)
                             in
                               case opcode of
                                 0w =>
                                   Zfull_inst
                                     (p,Zmonop (Zinc,size,rm),strm3)
                               | 1w =>
                                   Zfull_inst
                                     (p,Zmonop (Zdec,size,rm),strm3)
                               | 2w => Zfull_inst (p,Zcall (Zrm rm),strm3)
                               | 4w => Zfull_inst (p,Zjmp rm,strm3)
                               | 6w => Zfull_inst (p,Zpush (Zrm rm),strm3)
                               | v =>
                                   Zdec_fail
                                     "Unsupported opcode: INC/DEC Group 5")
                        | ((T,T,T,T,T,T,T,F),strm2) =>
                            (let (opcode,rm,strm3) =
                                   readOpcodeModRM (REX_1,strm2)
                             in
                               if opcode = 0w then
                                 Zfull_inst
                                   (p,Zmonop (Zinc,Z8 have_rex,rm),strm3)
                               else if opcode = 1w then
                                 Zfull_inst
                                   (p,Zmonop (Zdec,Z8 have_rex,rm),strm3)
                               else
                                 Zdec_fail
                                   "Unsupported opcode: INC/DEC Group 4")
                        | ((T,T,T,T,T,T,F,v29),strm2) =>
                            Zdec_fail
                              (STRCAT "Unsupported opcode: "
                                 (word_to_hex_string v#0 ))
                        | ((T,T,T,T,T,F,v25),strm2) =>
                            Zdec_fail
                              (STRCAT "Unsupported opcode: "
                                 (word_to_hex_string v#0 ))
                        | ((T,T,T,T,F,T,T,v37),strm2) =>
                            (let size =
                                   OpSize
                                     (have_rex,REX_1.W,(0 >< 0) v#0 ,
                                      op_size_override)
                             in
                             let (opcode,rm,strm3) =
                                   readOpcodeModRM (REX_1,strm2)
                             in
                               case opcode of
                                 0w =>
                                   (let (imm,strm4) =
                                          immediate (size,strm3)
                                    in
                                      Zfull_inst
                                        (p,
                                         Zbinop
                                           (Ztest,size,Zrm_i (rm,imm)),
                                         strm4))
                               | 2w =>
                                   Zfull_inst
                                     (p,Zmonop (Znot,size,rm),strm3)
                               | 3w =>
                                   Zfull_inst
                                     (p,Zmonop (Zneg,size,rm),strm3)
                               | 4w => Zfull_inst (p,Zmul (size,rm),strm3)
                               | 6w => Zfull_inst (p,Zdiv (size,rm),strm3)
                               | v =>
                                   Zdec_fail
                                     "Unsupported opcode: Unary Group 3")
                        | ((T,T,T,T,F,T,F,v37),strm2) =>
                            Zdec_fail
                              (STRCAT "Unsupported opcode: "
                                 (word_to_hex_string v#0 ))
                        | ((T,T,T,T,F,F,v33),strm2) =>
                            Zdec_fail
                              (STRCAT "Unsupported opcode: "
                                 (word_to_hex_string v#0 ))
                        | ((T,T,T,F,T,T,v45),strm2) =>
                            Zdec_fail
                              (STRCAT "Unsupported opcode: "
                                 (word_to_hex_string v#0 ))
                        | ((T,T,T,F,T,F,v48,T),strm2) =>
                            (let (imm,strm3) =
                                   if (1 >< 1) v#0 = 0w then
                                     immediate32 strm2
                                   else immediate8 strm2
                             in
                               Zfull_inst (p,Zjcc (Z_ALWAYS,imm),strm3))
                        | ((T,T,T,F,T,F,T,F),strm2) =>
                            Zdec_fail
                              (STRCAT "Unsupported opcode: "
                                 (word_to_hex_string v#0 ))
                        | ((T,T,T,F,T,F,F,F),strm2) =>
                            (let (imm,strm3) = immediate32 strm2
                             in
                               Zfull_inst (p,Zcall (Zimm imm),strm3))
                        | ((T,T,T,F,F,T,v53),strm2) =>
                            Zdec_fail
                              (STRCAT "Unsupported opcode: "
                                 (word_to_hex_string v#0 ))
                        | ((T,T,T,F,F,F,T,T),strm2) =>
                            Zdec_fail
                              (STRCAT "Unsupported opcode: "
                                 (word_to_hex_string v#0 ))
                        | ((T,T,T,F,F,F,T,F),strm2) =>
                            (let (imm,strm3) = immediate8 strm2
                             in
                               Zfull_inst (p,Zloop (Z_ALWAYS,imm),strm3))
                        | ((T,T,T,F,F,F,F,v57),strm2) =>
                            (let (imm,strm3) = immediate8 strm2
                             in
                               Zfull_inst
                                 (p,
                                  Zloop
                                    (if (0 >< 0) v#0 = 0w then Z_NE
                                     else Z_E,imm),strm3))
                        | ((T,T,F,T,T,v65),strm2) =>
                            Zdec_fail
                              (STRCAT "Unsupported opcode: "
                                 (word_to_hex_string v#0 ))
                        | ((T,T,F,T,F,T,v69),strm2) =>
                            Zdec_fail
                              (STRCAT "Unsupported opcode: "
                                 (word_to_hex_string v#0 ))
                        | ((T,T,F,T,F,F,v69),strm2) =>
                            (let (opcode,rm,strm3) =
                                   readOpcodeModRM (REX_1,strm2)
                             in
                               if opcode = 6w then
                                 Zdec_fail
                                   "Unsupported opcode: Shift Group 2"
                               else
                                 Zfull_inst
                                   (p,
                                    Zbinop
                                      (num2Zbinop_name (w2n opcode + 8),
                                       OpSize
                                         (have_rex,REX_1.W,(0 >< 0) v#0 ,
                                          op_size_override),
                                       if (1 >< 1) v#0 = 0w then
                                         Zrm_i (rm,1w)
                                       else Zrm_r (rm,RCX)),strm3))
                        | ((T,T,F,F,T,v77),strm2) =>
                            Zdec_fail
                              (STRCAT "Unsupported opcode: "
                                 (word_to_hex_string v#0 ))
                        | ((T,T,F,F,F,T,T,v85),strm2) =>
                            (let size =
                                   OpSize
                                     (have_rex,REX_1.W,(0 >< 0) v#0 ,
                                      op_size_override)
                             in
                             let (opcode,rm,strm3) =
                                   readOpcodeModRM (REX_1,strm2)
                             in
                             let (imm,strm4) = immediate (size,strm3)
                             in
                               if opcode = 0w then
                                 Zfull_inst
                                   (p,Zmov (Z_ALWAYS,size,Zrm_i (rm,imm)),
                                    strm4)
                               else
                                 Zdec_fail "Unsupported opcode: Group 11")
                        | ((T,T,F,F,F,T,F,v85),strm2) =>
                            Zdec_fail
                              (STRCAT "Unsupported opcode: "
                                 (word_to_hex_string v#0 ))
                        | ((T,T,F,F,F,F,T,v89),strm2) =>
                            if (0 >< 0) v#0 = 0w then
                              (let (imm,strm3) = immediate16 strm2
                               in
                                 Zfull_inst (p,Zret imm,strm3))
                            else Zfull_inst (p,Zret 0w,strm2)
                        | ((T,T,F,F,F,F,F,v89),strm2) =>
                            (let (opcode,rm,strm3) =
                                   readOpcodeModRM (REX_1,strm2)
                             in
                             let (imm,strm4) = immediate8 strm3
                             in
                               if opcode = 6w then
                                 Zdec_fail
                                   "Unsupported opcode: Shift Group 2"
                               else
                                 Zfull_inst
                                   (p,
                                    Zbinop
                                      (num2Zbinop_name (w2n opcode + 8),
                                       OpSize
                                         (have_rex,REX_1.W,(0 >< 0) v#0 ,
                                          op_size_override),
                                       Zrm_i (rm,imm)),strm4))
                        | ((T,F,T,T,v97),strm2) =>
                            (let size =
                                   OpSize
                                     (have_rex,REX_1.W,(3 >< 3) v#0 ,
                                      op_size_override)
                             in
                             let (imm,strm3) = full_immediate (size,strm2)
                             in
                               Zfull_inst
                                 (p,
                                  Zmov
                                    (Z_ALWAYS,size,
                                     Zrm_i
                                       (Zr
                                          (num2Zreg
                                             (w2n
                                                ((if REX_1.B then 1w
                                                  else 0w) @@
                                                 (2 >< 0) v#0 ))),imm)),
                                  strm3))
                        | ((T,F,T,F,T,T,v117),strm2) =>
                            Zdec_fail
                              (STRCAT "Unsupported opcode: "
                                 (word_to_hex_string v#0 ))
                        | ((T,F,T,F,T,F,T,v121),strm2) =>
                            Zdec_fail
                              (STRCAT "Unsupported opcode: "
                                 (word_to_hex_string v#0 ))
                        | ((T,F,T,F,T,F,F,v121),strm2) =>
                            (let size =
                                   OpSize
                                     (T,REX_1.W,(0 >< 0) v#0 ,
                                      op_size_override)
                             in
                             let (imm,strm3) = immediate (size,strm2)
                             in
                               Zfull_inst
                                 (p,Zbinop (Ztest,size,Zrm_i (Zr RAX,imm)),
                                  strm3))
                        | ((T,F,T,F,F,v113),strm2) =>
                            Zdec_fail
                              (STRCAT "Unsupported opcode: "
                                 (word_to_hex_string v#0 ))
                        | ((T,F,F,T,T,v129),strm2) =>
                            Zdec_fail
                              (STRCAT "Unsupported opcode: "
                                 (word_to_hex_string v#0 ))
                        | ((T,F,F,T,F,v129),strm2) =>
                            (let reg = RexReg (REX_1.B,(2 >< 0) v#0 )
                             in
                               if reg = RAX then Zfull_inst (p,Znop,strm2)
                               else
                                 Zfull_inst
                                   (p,
                                    Zxchg
                                      (OpSize
                                         (T,REX_1.W,1w,op_size_override),
                                       Zr RAX,reg),strm2))
                        | ((T,F,F,F,T,T,T,T),strm2) =>
                            (let (opcode,rm,strm3) =
                                   readOpcodeModRM (REX_1,strm2)
                             in
                               if opcode = 0w then
                                 Zfull_inst (p,Zpop rm,strm3)
                               else
                                 Zdec_fail "Unsupported opcode: Group 1a")
                        | ((T,F,F,F,T,T,T,F),strm2) =>
                            Zdec_fail
                              (STRCAT "Unsupported opcode: "
                                 (word_to_hex_string v#0 ))
                        | ((T,F,F,F,T,T,F,T),strm2) =>
                            (let (reg,rm,strm3) = readModRM (REX_1,strm2)
                             in
                               if isZm rm then
                                 Zfull_inst
                                   (p,
                                    Zlea
                                      (OpSize
                                         (T,REX_1.W,1w,op_size_override),
                                       Zr_rm (reg,rm)),strm3)
                               else Zdec_fail "LEA with register argument")
                        | ((T,F,F,F,T,T,F,F),strm2) =>
                            Zdec_fail
                              (STRCAT "Unsupported opcode: "
                                 (word_to_hex_string v#0 ))
                        | ((T,F,F,F,T,F,v145),strm2) =>
                            (let (reg,rm,strm3) = readModRM (REX_1,strm2)
                             in
                               Zfull_inst
                                 (p,
                                  Zmov
                                    (Z_ALWAYS,
                                     OpSize
                                       (have_rex,REX_1.W,(0 >< 0) v#0 ,
                                        op_size_override),
                                     if (1 >< 1) v#0 = 0w then
                                       Zrm_r (rm,reg)
                                     else Zr_rm (reg,rm)),strm3))
                        | ((T,F,F,F,F,T,T,v161),strm2) =>
                            (let (reg,rm,strm3) = readModRM (REX_1,strm2)
                             in
                               Zfull_inst
                                 (p,
                                  Zxchg
                                    (OpSize
                                       (have_rex,REX_1.W,(0 >< 0) v#0 ,
                                        op_size_override),rm,reg),strm3))
                        | ((T,F,F,F,F,T,F,v161),strm2) =>
                            (let (reg,rm,strm3) = readModRM (REX_1,strm2)
                             in
                               Zfull_inst
                                 (p,
                                  Zbinop
                                    (Ztest,
                                     OpSize
                                       (have_rex,REX_1.W,(0 >< 0) v#0 ,
                                        op_size_override),Zrm_r (rm,reg)),
                                  strm3))
                        | ((T,F,F,F,F,F,T,T),strm2) =>
                            (let (opcode,rm,strm3) =
                                   readOpcodeModRM (REX_1,strm2)
                             in
                             let (imm,strm4) = immediate8 strm3
                             in
                               Zfull_inst
                                 (p,
                                  Zbinop
                                    (num2Zbinop_name (w2n opcode),
                                     OpSize
                                       (F,REX_1.W,1w,op_size_override),
                                     Zrm_i (rm,imm)),strm4))
                        | ((T,F,F,F,F,F,T,F),strm2) =>
                            Zdec_fail
                              (STRCAT "Unsupported opcode: "
                                 (word_to_hex_string v#0 ))
                        | ((T,F,F,F,F,F,F,v165),strm2) =>
                            (let size =
                                   OpSize
                                     (have_rex,REX_1.W,(0 >< 0) v#0 ,
                                      op_size_override)
                             in
                             let (opcode,rm,strm3) =
                                   readOpcodeModRM (REX_1,strm2)
                             in
                             let (imm,strm4) = immediate (size,strm3)
                             in
                               Zfull_inst
                                 (p,
                                  Zbinop
                                    (num2Zbinop_name (w2n opcode),size,
                                     Zrm_i (rm,imm)),strm4))
                        | ((F,T,T,T,v177),strm2) =>
                            (let (imm,strm3) = immediate8 strm2
                             in
                               Zfull_inst
                                 (p,
                                  Zjcc
                                    (num2Zcond (w2n ((3 >< 0) v#0 )),imm),
                                  strm3))
                        | ((F,T,T,F,T,T,v197),strm2) =>
                            Zdec_fail
                              (STRCAT "Unsupported opcode: "
                                 (word_to_hex_string v#0 ))
                        | ((F,T,T,F,T,F,v200,T),strm2) =>
                            Zdec_fail
                              (STRCAT "Unsupported opcode: "
                                 (word_to_hex_string v#0 ))
                        | ((F,T,T,F,T,F,v200,F),strm2) =>
                            (let (imm,strm3) =
                                   if (1 >< 1) v#0 = 1w then
                                     immediate8 strm2
                                   else immediate32 strm2
                             in
                               Zfull_inst (p,Zpush (Zimm imm),strm3))
                        | ((F,T,T,F,F,v193),strm2) =>
                            Zdec_fail
                              (STRCAT "Unsupported opcode: "
                                 (word_to_hex_string v#0 ))
                        | ((F,T,F,T,v205),strm2) =>
                            (let reg =
                                   Zr
                                     (num2Zreg
                                        (w2n
                                           ((if REX_1.B then 1w else 0w) @@
                                            (2 >< 0) v#0 )))
                             in
                               Zfull_inst
                                 (p,
                                  if (3 >< 3) v#0 = 0w then Zpush (Zrm reg)
                                  else Zpop reg,strm2))
                        | ((F,T,F,F,v205),strm2) =>
                            Zdec_fail
                              (STRCAT "Unsupported opcode: "
                                 (word_to_hex_string v#0 ))
                        | ((F,F,v220,v224,v228,T,T,v237),[]) =>
                            Zdec_fail
                              (STRCAT "Unsupported opcode: "
                                 (word_to_hex_string v#0 ))
                        | ((F,F,v220,T,T,T,T,T),v240::v241) =>
                            Zdec_fail
                              (STRCAT "Unsupported opcode: "
                                 (word_to_hex_string v#0 ))
                        | ((F,F,T,F,T,T,T,T),v240::v241) =>
                            Zdec_fail
                              (STRCAT "Unsupported opcode: "
                                 (word_to_hex_string v#0 ))
                        | ((F,F,F,F,T,T,T,T),[v240]) =>
                            (let (b'7,b'6,b'5,b'4,b'3,b'2,b'1,b'0) =
                                   boolify8 v240
                             in
                               if ¬b'7 ∧ b'6 ∧ ¬b'5 ∧ ¬b'4 then
                                 (let (reg,rm,strm3) = readModRM (REX_1,[])
                                  in
                                    Zfull_inst
                                      (p,
                                       Zmov
                                         (num2Zcond (w2n ((3 >< 0) v240)),
                                          OpSize
                                            (T,REX_1.W,1w,
                                             op_size_override),
                                          Zr_rm (reg,rm)),strm3))
                               else if b'7 ∧ ¬b'6 ∧ ¬b'5 ∧ ¬b'4 then
                                 (let (imm,strm3) = immediate32 []
                                  in
                                    Zfull_inst
                                      (p,
                                       Zjcc
                                         (num2Zcond (w2n ((3 >< 0) v240)),
                                          imm),strm3))
                               else if
                                 b'7 ∧ ¬b'6 ∧ b'5 ∧ ¬b'4 ∧ ¬b'3 ∧ ¬b'2 ∧
                                 b'1 ∧ ¬b'0
                               then
                                 Zfull_inst (p,Zcpuid,[])
                               else if
                                 b'7 ∧ ¬b'6 ∧ b'5 ∧ b'4 ∧ ¬b'3 ∧ ¬b'2 ∧
                                 ¬b'1
                               then
                                 (let (reg,rm,strm3) = readModRM (REX_1,[])
                                  in
                                    Zfull_inst
                                      (p,
                                       Zcmpxchg
                                         (OpSize
                                            (have_rex,REX_1.W,
                                             (0 >< 0) v240,
                                             op_size_override),rm,reg),
                                       strm3))
                               else if
                                 b'7 ∧ b'6 ∧ ¬b'5 ∧ ¬b'4 ∧ ¬b'3 ∧ ¬b'2 ∧
                                 ¬b'1
                               then
                                 (let (reg,rm,strm3) = readModRM (REX_1,[])
                                  in
                                    Zfull_inst
                                      (p,
                                       Zxadd
                                         (OpSize
                                            (have_rex,REX_1.W,
                                             (0 >< 0) v240,
                                             op_size_override),rm,reg),
                                       strm3))
                               else if
                                 b'7 ∧ ¬b'6 ∧ b'5 ∧ b'4 ∧ ¬b'3 ∧ b'2 ∧ b'1
                               then
                                 (let (reg,rm,strm3) = readModRM (REX_1,[])
                                  in
                                    Zfull_inst
                                      (p,
                                       Zmovzx
                                         (OpSize
                                            (have_rex,REX_1.W,1w,
                                             op_size_override),
                                          Zr_rm (reg,rm),
                                          if (0 >< 0) v240 = 1w then Z16
                                          else Z8 have_rex),strm3))
                               else
                                 Zdec_fail
                                   (STRCAT "Unsupported opcode: 0F "
                                      (word_to_hex_string v240)))
                        | ((F,F,F,F,T,T,T,T),56w::opc::v247) =>
                            Zdec_fail
                              (STRCAT "Unsupported opcode: 0F 38 "
                                 (word_to_hex_string opc))
                        | ((F,F,F,F,T,T,T,T),58w::opc::v247) =>
                            Zdec_fail
                              (STRCAT "Unsupported opcode: 0F 3A "
                                 (word_to_hex_string opc))
                        | ((F,F,F,F,T,T,T,T),v248::opc::v247) =>
                            (let (b'7,b'6,b'5,b'4,b'3,b'2,b'1,b'0) =
                                   boolify8 v248
                             in
                               if ¬b'7 ∧ b'6 ∧ ¬b'5 ∧ ¬b'4 then
                                 (let (reg,rm,strm3) =
                                        readModRM (REX_1,opc::v247)
                                  in
                                    Zfull_inst
                                      (p,
                                       Zmov
                                         (num2Zcond (w2n ((3 >< 0) v248)),
                                          OpSize
                                            (T,REX_1.W,1w,
                                             op_size_override),
                                          Zr_rm (reg,rm)),strm3))
                               else if b'7 ∧ ¬b'6 ∧ ¬b'5 ∧ ¬b'4 then
                                 (let (imm,strm3) = immediate32 (opc::v247)
                                  in
                                    Zfull_inst
                                      (p,
                                       Zjcc
                                         (num2Zcond (w2n ((3 >< 0) v248)),
                                          imm),strm3))
                               else if
                                 b'7 ∧ ¬b'6 ∧ b'5 ∧ ¬b'4 ∧ ¬b'3 ∧ ¬b'2 ∧
                                 b'1 ∧ ¬b'0
                               then
                                 Zfull_inst (p,Zcpuid,opc::v247)
                               else if
                                 b'7 ∧ ¬b'6 ∧ b'5 ∧ b'4 ∧ ¬b'3 ∧ ¬b'2 ∧
                                 ¬b'1
                               then
                                 (let (reg,rm,strm3) =
                                        readModRM (REX_1,opc::v247)
                                  in
                                    Zfull_inst
                                      (p,
                                       Zcmpxchg
                                         (OpSize
                                            (have_rex,REX_1.W,
                                             (0 >< 0) v248,
                                             op_size_override),rm,reg),
                                       strm3))
                               else if
                                 b'7 ∧ b'6 ∧ ¬b'5 ∧ ¬b'4 ∧ ¬b'3 ∧ ¬b'2 ∧
                                 ¬b'1
                               then
                                 (let (reg,rm,strm3) =
                                        readModRM (REX_1,opc::v247)
                                  in
                                    Zfull_inst
                                      (p,
                                       Zxadd
                                         (OpSize
                                            (have_rex,REX_1.W,
                                             (0 >< 0) v248,
                                             op_size_override),rm,reg),
                                       strm3))
                               else if
                                 b'7 ∧ ¬b'6 ∧ b'5 ∧ b'4 ∧ ¬b'3 ∧ b'2 ∧ b'1
                               then
                                 (let (reg,rm,strm3) =
                                        readModRM (REX_1,opc::v247)
                                  in
                                    Zfull_inst
                                      (p,
                                       Zmovzx
                                         (OpSize
                                            (have_rex,REX_1.W,1w,
                                             op_size_override),
                                          Zr_rm (reg,rm),
                                          if (0 >< 0) v248 = 1w then Z16
                                          else Z8 have_rex),strm3))
                               else
                                 Zdec_fail
                                   (STRCAT "Unsupported opcode: 0F "
                                      (word_to_hex_string v248)))
                        | ((F,F,v220,v224,F,T,T,T),v240::v241) =>
                            Zdec_fail
                              (STRCAT "Unsupported opcode: "
                                 (word_to_hex_string v#0 ))
                        | ((F,F,v220,v224,v228,T,T,F),v240::v241) =>
                            Zdec_fail
                              (STRCAT "Unsupported opcode: "
                                 (word_to_hex_string v#0 ))
                        | ((F,F,v220,v224,v228,T,F,v237),strm2) =>
                            (let size =
                                   OpSize
                                     (have_rex,REX_1.W,(0 >< 0) v#0 ,
                                      op_size_override)
                             in
                             let (imm,strm3) = immediate (size,strm2)
                             in
                               Zfull_inst
                                 (p,
                                  Zbinop
                                    (num2Zbinop_name (w2n ((5 >< 3) v#0 )),
                                     size,Zrm_i (Zr RAX,imm)),strm3))
                        | ((F,F,v220,v224,v228,F,v233),strm2) =>
                            (let (reg,rm,strm3) = readModRM (REX_1,strm2)
                             in
                               Zfull_inst
                                 (p,
                                  Zbinop
                                    (num2Zbinop_name (w2n ((5 >< 3) v#0 )),
                                     OpSize
                                       (have_rex,REX_1.W,(0 >< 0) v#0 ,
                                        op_size_override),
                                     if (1 >< 1) v#0 = 0w then
                                       Zrm_r (rm,reg)
                                     else Zr_rm (reg,rm)),strm3)))

   [x64_drop_def]  Definition

      |- ∀imm.
           x64_drop imm =
           (λstate.
              (let s =
                     if (7 >< 0) imm ≠ 0w then
                       SND (raise'exception (FAIL "x64_drop") state)
                     else state
               in
                 ((),s with REG := (RSP =+ s.REG RSP + imm) s.REG)))

   [x64_fetch_def]  Definition

      |- ∀state.
           x64_fetch state =
           (let (r,s1) =
                  (let s =
                         SND
                           (FOR
                              (19,0,
                               (λi state.
                                  ((),
                                   THE
                                     ((SND state).MEM
                                        ((SND state).RIP + n2w i))::
                                       FST state,SND state))) ([],state))
                   in
                     (FST s,s))
            in
              (r,SND s1))

   [x64_next_def]  Definition

      |- ∀state.
           x64_next state =
           case x64_decode (FST (x64_fetch state)) of
             Zdec_fail s0 => raise'exception (FAIL s0) state
           | Zfull_inst (v2,i,strm1) =>
               (let len = 20 − LENGTH strm1 in
                let s = SND (checkIcache len state)
                in
                  Run i (s with RIP := s.RIP + n2w len))

   [x64_pop_aux_def]  Definition

      |- ∀state.
           x64_pop_aux state =
           (let v = state.REG RSP in
            let (v0,s) = mem64 v state
            in
              (v0,s with REG := (RSP =+ v + 8w) s.REG))

   [x64_pop_def]  Definition

      |- ∀rm.
           x64_pop rm =
           (λstate.
              (let (v0,s) = x64_pop_aux state
               in
                 write'EA (v0,FST (ea_Zrm (Z64,rm) state)) s))

   [x64_pop_rip_def]  Definition

      |- ∀state.
           x64_pop_rip state =
           (let (v,s) = x64_pop_aux state in ((),s with RIP := v))

   [x64_push_aux_def]  Definition

      |- ∀w.
           x64_push_aux w =
           (λstate.
              (let v = state.REG RSP − 8w
               in
                 write'mem64 (w,v)
                   (state with REG := (RSP =+ v) state.REG)))

   [x64_push_def]  Definition

      |- ∀imm_rm.
           x64_push imm_rm =
           (λstate.
              (let (v,s) = EA (FST (ea_Zimm_rm (Z64,imm_rm) state)) state
               in
                 x64_push_aux v s))

   [x64_push_rip_def]  Definition

      |- ∀state. x64_push_rip state = x64_push_aux state.RIP state

   [x64_state_EFLAGS]  Definition

      |- ∀f f0 f1 f2 c e. (x64_state f f0 f1 f2 c e).EFLAGS = f

   [x64_state_EFLAGS_fupd]  Definition

      |- ∀f3 f f0 f1 f2 c e.
           x64_state f f0 f1 f2 c e with EFLAGS updated_by f3 =
           x64_state (f3 f) f0 f1 f2 c e

   [x64_state_ICACHE]  Definition

      |- ∀f f0 f1 f2 c e. (x64_state f f0 f1 f2 c e).ICACHE = f0

   [x64_state_ICACHE_fupd]  Definition

      |- ∀f3 f f0 f1 f2 c e.
           x64_state f f0 f1 f2 c e with ICACHE updated_by f3 =
           x64_state f (f3 f0) f1 f2 c e

   [x64_state_MEM]  Definition

      |- ∀f f0 f1 f2 c e. (x64_state f f0 f1 f2 c e).MEM = f1

   [x64_state_MEM_fupd]  Definition

      |- ∀f3 f f0 f1 f2 c e.
           x64_state f f0 f1 f2 c e with MEM updated_by f3 =
           x64_state f f0 (f3 f1) f2 c e

   [x64_state_REG]  Definition

      |- ∀f f0 f1 f2 c e. (x64_state f f0 f1 f2 c e).REG = f2

   [x64_state_REG_fupd]  Definition

      |- ∀f3 f f0 f1 f2 c e.
           x64_state f f0 f1 f2 c e with REG updated_by f3 =
           x64_state f f0 f1 (f3 f2) c e

   [x64_state_RIP]  Definition

      |- ∀f f0 f1 f2 c e. (x64_state f f0 f1 f2 c e).RIP = c

   [x64_state_RIP_fupd]  Definition

      |- ∀f3 f f0 f1 f2 c e.
           x64_state f f0 f1 f2 c e with RIP updated_by f3 =
           x64_state f f0 f1 f2 (f3 c) e

   [x64_state_TY_DEF]  Definition

      |- ∃rep.
           TYPE_DEFINITION
             (λa0'.
                ∀'x64_state' .
                  (∀a0'.
                     (∃a0 a1 a2 a3 a4 a5.
                        a0' =
                        (λa0 a1 a2 a3 a4 a5.
                           ind_type$CONSTR 0 (a0,a1,a2,a3,a4,a5)
                             (λn. ind_type$BOTTOM)) a0 a1 a2 a3 a4 a5) ⇒
                     'x64_state' a0') ⇒
                  'x64_state' a0') rep

   [x64_state_case_def]  Definition

      |- ∀a0 a1 a2 a3 a4 a5 f.
           x64_state_CASE (x64_state a0 a1 a2 a3 a4 a5) f =
           f a0 a1 a2 a3 a4 a5

   [x64_state_exception]  Definition

      |- ∀f f0 f1 f2 c e. (x64_state f f0 f1 f2 c e).exception = e

   [x64_state_exception_fupd]  Definition

      |- ∀f3 f f0 f1 f2 c e.
           x64_state f f0 f1 f2 c e with exception updated_by f3 =
           x64_state f f0 f1 f2 c (f3 e)

   [x64_state_size_def]  Definition

      |- ∀a0 a1 a2 a3 a4 a5.
           x64_state_size (x64_state a0 a1 a2 a3 a4 a5) =
           1 + exception_size a5

   [EXISTS_REX]  Theorem

      |- ∀P.
           (∃R. P R) ⇔ ∃b2 b1 b0 b. P <|B := b2; R := b1; W := b0; X := b|>

   [EXISTS_x64_state]  Theorem

      |- ∀P.
           (∃x. P x) ⇔
           ∃f2 f1 f0 f c e.
             P
               <|EFLAGS := f2; ICACHE := f1; MEM := f0; REG := f; RIP := c;
                 exception := e|>

   [FORALL_REX]  Theorem

      |- ∀P.
           (∀R. P R) ⇔ ∀b2 b1 b0 b. P <|B := b2; R := b1; W := b0; X := b|>

   [FORALL_x64_state]  Theorem

      |- ∀P.
           (∀x. P x) ⇔
           ∀f2 f1 f0 f c e.
             P
               <|EFLAGS := f2; ICACHE := f1; MEM := f0; REG := f; RIP := c;
                 exception := e|>

   [REX_11]  Theorem

      |- ∀a0 a1 a2 a3 a0' a1' a2' a3'.
           (REX a0 a1 a2 a3 = REX a0' a1' a2' a3') ⇔
           (a0 ⇔ a0') ∧ (a1 ⇔ a1') ∧ (a2 ⇔ a2') ∧ (a3 ⇔ a3')

   [REX_Axiom]  Theorem

      |- ∀f. ∃fn. ∀a0 a1 a2 a3. fn (REX a0 a1 a2 a3) = f a0 a1 a2 a3

   [REX_accessors]  Theorem

      |- (∀b b0 b1 b2. (REX b b0 b1 b2).B ⇔ b) ∧
         (∀b b0 b1 b2. (REX b b0 b1 b2).R ⇔ b0) ∧
         (∀b b0 b1 b2. (REX b b0 b1 b2).W ⇔ b1) ∧
         ∀b b0 b1 b2. (REX b b0 b1 b2).X ⇔ b2

   [REX_accfupds]  Theorem

      |- (∀f R. (R with R updated_by f).B ⇔ R.B) ∧
         (∀f R. (R with W updated_by f).B ⇔ R.B) ∧
         (∀f R. (R with X updated_by f).B ⇔ R.B) ∧
         (∀f R. (R with B updated_by f).R ⇔ R.R) ∧
         (∀f R. (R with W updated_by f).R ⇔ R.R) ∧
         (∀f R. (R with X updated_by f).R ⇔ R.R) ∧
         (∀f R. (R with B updated_by f).W ⇔ R.W) ∧
         (∀f R. (R with R updated_by f).W ⇔ R.W) ∧
         (∀f R. (R with X updated_by f).W ⇔ R.W) ∧
         (∀f R. (R with B updated_by f).X ⇔ R.X) ∧
         (∀f R. (R with R updated_by f).X ⇔ R.X) ∧
         (∀f R. (R with W updated_by f).X ⇔ R.X) ∧
         (∀f R. (R with B updated_by f).B ⇔ f R.B) ∧
         (∀f R. (R with R updated_by f).R ⇔ f R.R) ∧
         (∀f R. (R with W updated_by f).W ⇔ f R.W) ∧
         ∀f R. (R with X updated_by f).X ⇔ f R.X

   [REX_case_cong]  Theorem

      |- ∀M M' f.
           (M = M') ∧
           (∀a0 a1 a2 a3.
              (M' = REX a0 a1 a2 a3) ⇒ (f a0 a1 a2 a3 = f' a0 a1 a2 a3)) ⇒
           (REX_CASE M f = REX_CASE M' f')

   [REX_component_equality]  Theorem

      |- ∀R1 R2.
           (R1 = R2) ⇔
           (R1.B ⇔ R2.B) ∧ (R1.R ⇔ R2.R) ∧ (R1.W ⇔ R2.W) ∧ (R1.X ⇔ R2.X)

   [REX_fn_updates]  Theorem

      |- (∀f b b0 b1 b2.
            REX b b0 b1 b2 with B updated_by f = REX (f b) b0 b1 b2) ∧
         (∀f b b0 b1 b2.
            REX b b0 b1 b2 with R updated_by f = REX b (f b0) b1 b2) ∧
         (∀f b b0 b1 b2.
            REX b b0 b1 b2 with W updated_by f = REX b b0 (f b1) b2) ∧
         ∀f b b0 b1 b2.
           REX b b0 b1 b2 with X updated_by f = REX b b0 b1 (f b2)

   [REX_fupdcanon]  Theorem

      |- (∀g f R.
            R with <|R updated_by f; B updated_by g|> =
            R with <|B updated_by g; R updated_by f|>) ∧
         (∀g f R.
            R with <|W updated_by f; B updated_by g|> =
            R with <|B updated_by g; W updated_by f|>) ∧
         (∀g f R.
            R with <|W updated_by f; R updated_by g|> =
            R with <|R updated_by g; W updated_by f|>) ∧
         (∀g f R.
            R with <|X updated_by f; B updated_by g|> =
            R with <|B updated_by g; X updated_by f|>) ∧
         (∀g f R.
            R with <|X updated_by f; R updated_by g|> =
            R with <|R updated_by g; X updated_by f|>) ∧
         ∀g f R.
           R with <|X updated_by f; W updated_by g|> =
           R with <|W updated_by g; X updated_by f|>

   [REX_fupdcanon_comp]  Theorem

      |- ((∀g f.
              _ record fupdateR f o  _ record fupdateB g =
              _ record fupdateB g o  _ record fupdateR f) ∧
          ∀h g f.
             _ record fupdateR f o  _ record fupdateB g o h =
             _ record fupdateB g o  _ record fupdateR f o h) ∧
         ((∀g f.
              _ record fupdateW f o  _ record fupdateB g =
              _ record fupdateB g o  _ record fupdateW f) ∧
          ∀h g f.
             _ record fupdateW f o  _ record fupdateB g o h =
             _ record fupdateB g o  _ record fupdateW f o h) ∧
         ((∀g f.
              _ record fupdateW f o  _ record fupdateR g =
              _ record fupdateR g o  _ record fupdateW f) ∧
          ∀h g f.
             _ record fupdateW f o  _ record fupdateR g o h =
             _ record fupdateR g o  _ record fupdateW f o h) ∧
         ((∀g f.
              _ record fupdateX f o  _ record fupdateB g =
              _ record fupdateB g o  _ record fupdateX f) ∧
          ∀h g f.
             _ record fupdateX f o  _ record fupdateB g o h =
             _ record fupdateB g o  _ record fupdateX f o h) ∧
         ((∀g f.
              _ record fupdateX f o  _ record fupdateR g =
              _ record fupdateR g o  _ record fupdateX f) ∧
          ∀h g f.
             _ record fupdateX f o  _ record fupdateR g o h =
             _ record fupdateR g o  _ record fupdateX f o h) ∧
         (∀g f.
             _ record fupdateX f o  _ record fupdateW g =
             _ record fupdateW g o  _ record fupdateX f) ∧
         ∀h g f.
            _ record fupdateX f o  _ record fupdateW g o h =
            _ record fupdateW g o  _ record fupdateX f o h

   [REX_fupdfupds]  Theorem

      |- (∀g f R.
            R with <|B updated_by f; B updated_by g|> =
            R with B updated_by f o g) ∧
         (∀g f R.
            R with <|R updated_by f; R updated_by g|> =
            R with R updated_by f o g) ∧
         (∀g f R.
            R with <|W updated_by f; W updated_by g|> =
            R with W updated_by f o g) ∧
         ∀g f R.
           R with <|X updated_by f; X updated_by g|> =
           R with X updated_by f o g

   [REX_fupdfupds_comp]  Theorem

      |- ((∀g f.
              _ record fupdateB f o  _ record fupdateB g =
              _ record fupdateB (f o g)) ∧
          ∀h g f.
             _ record fupdateB f o  _ record fupdateB g o h =
             _ record fupdateB (f o g) o h) ∧
         ((∀g f.
              _ record fupdateR f o  _ record fupdateR g =
              _ record fupdateR (f o g)) ∧
          ∀h g f.
             _ record fupdateR f o  _ record fupdateR g o h =
             _ record fupdateR (f o g) o h) ∧
         ((∀g f.
              _ record fupdateW f o  _ record fupdateW g =
              _ record fupdateW (f o g)) ∧
          ∀h g f.
             _ record fupdateW f o  _ record fupdateW g o h =
             _ record fupdateW (f o g) o h) ∧
         (∀g f.
             _ record fupdateX f o  _ record fupdateX g =
             _ record fupdateX (f o g)) ∧
         ∀h g f.
            _ record fupdateX f o  _ record fupdateX g o h =
            _ record fupdateX (f o g) o h

   [REX_induction]  Theorem

      |- ∀P. (∀b b0 b1 b2. P (REX b b0 b1 b2)) ⇒ ∀R. P R

   [REX_literal_11]  Theorem

      |- ∀b21 b11 b01 b1 b22 b12 b02 b2.
           (<|B := b21; R := b11; W := b01; X := b1|> =
            <|B := b22; R := b12; W := b02; X := b2|>) ⇔
           (b21 ⇔ b22) ∧ (b11 ⇔ b12) ∧ (b01 ⇔ b02) ∧ (b1 ⇔ b2)

   [REX_literal_nchotomy]  Theorem

      |- ∀R. ∃b2 b1 b0 b. R = <|B := b2; R := b1; W := b0; X := b|>

   [REX_nchotomy]  Theorem

      |- ∀RR. ∃b b0 b1 b2. RR = REX b b0 b1 b2

   [REX_updates_eq_literal]  Theorem

      |- ∀R b2 b1 b0 b.
           R with <|B := b2; R := b1; W := b0; X := b|> =
           <|B := b2; R := b1; W := b0; X := b|>

   [Zbase_11]  Theorem

      |- ∀a a'. (ZregBase a = ZregBase a') ⇔ (a = a')

   [Zbase_Axiom]  Theorem

      |- ∀f0 f1 f2.
           ∃fn.
             (fn ZnoBase = f0) ∧ (∀a. fn (ZregBase a) = f1 a) ∧
             (fn ZripBase = f2)

   [Zbase_case_cong]  Theorem

      |- ∀M M' v f v1.
           (M = M') ∧ ((M' = ZnoBase) ⇒ (v = v')) ∧
           (∀a. (M' = ZregBase a) ⇒ (f a = f' a)) ∧
           ((M' = ZripBase) ⇒ (v1 = v1')) ⇒
           (Zbase_CASE M v f v1 = Zbase_CASE M' v' f' v1')

   [Zbase_distinct]  Theorem

      |- (∀a. ZnoBase ≠ ZregBase a) ∧ ZnoBase ≠ ZripBase ∧
         ∀a. ZregBase a ≠ ZripBase

   [Zbase_induction]  Theorem

      |- ∀P. P ZnoBase ∧ (∀Z. P (ZregBase Z)) ∧ P ZripBase ⇒ ∀Z. P Z

   [Zbase_nchotomy]  Theorem

      |- ∀ZZ. (ZZ = ZnoBase) ∨ (∃Z. ZZ = ZregBase Z) ∨ (ZZ = ZripBase)

   [Zbinop_name2num_11]  Theorem

      |- ∀a a'. (Zbinop_name2num a = Zbinop_name2num a') ⇔ (a = a')

   [Zbinop_name2num_ONTO]  Theorem

      |- ∀r. r < 16 ⇔ ∃a. r = Zbinop_name2num a

   [Zbinop_name2num_num2Zbinop_name]  Theorem

      |- ∀r. r < 16 ⇔ (Zbinop_name2num (num2Zbinop_name r) = r)

   [Zbinop_name2num_thm]  Theorem

      |- (Zbinop_name2num Zadd = 0) ∧ (Zbinop_name2num Zor = 1) ∧
         (Zbinop_name2num Zadc = 2) ∧ (Zbinop_name2num Zsbb = 3) ∧
         (Zbinop_name2num Zand = 4) ∧ (Zbinop_name2num Zsub = 5) ∧
         (Zbinop_name2num Zxor = 6) ∧ (Zbinop_name2num Zcmp = 7) ∧
         (Zbinop_name2num Zrol = 8) ∧ (Zbinop_name2num Zror = 9) ∧
         (Zbinop_name2num Zrcl = 10) ∧ (Zbinop_name2num Zrcr = 11) ∧
         (Zbinop_name2num Zshl = 12) ∧ (Zbinop_name2num Zshr = 13) ∧
         (Zbinop_name2num Ztest = 14) ∧ (Zbinop_name2num Zsar = 15)

   [Zbinop_name_Axiom]  Theorem

      |- ∀x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15.
           ∃f.
             (f Zadd = x0) ∧ (f Zor = x1) ∧ (f Zadc = x2) ∧ (f Zsbb = x3) ∧
             (f Zand = x4) ∧ (f Zsub = x5) ∧ (f Zxor = x6) ∧
             (f Zcmp = x7) ∧ (f Zrol = x8) ∧ (f Zror = x9) ∧
             (f Zrcl = x10) ∧ (f Zrcr = x11) ∧ (f Zshl = x12) ∧
             (f Zshr = x13) ∧ (f Ztest = x14) ∧ (f Zsar = x15)

   [Zbinop_name_EQ_Zbinop_name]  Theorem

      |- ∀a a'. (a = a') ⇔ (Zbinop_name2num a = Zbinop_name2num a')

   [Zbinop_name_case_cong]  Theorem

      |- ∀M M' v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15.
           (M = M') ∧ ((M' = Zadd) ⇒ (v0 = v0')) ∧
           ((M' = Zor) ⇒ (v1 = v1')) ∧ ((M' = Zadc) ⇒ (v2 = v2')) ∧
           ((M' = Zsbb) ⇒ (v3 = v3')) ∧ ((M' = Zand) ⇒ (v4 = v4')) ∧
           ((M' = Zsub) ⇒ (v5 = v5')) ∧ ((M' = Zxor) ⇒ (v6 = v6')) ∧
           ((M' = Zcmp) ⇒ (v7 = v7')) ∧ ((M' = Zrol) ⇒ (v8 = v8')) ∧
           ((M' = Zror) ⇒ (v9 = v9')) ∧ ((M' = Zrcl) ⇒ (v10 = v10')) ∧
           ((M' = Zrcr) ⇒ (v11 = v11')) ∧ ((M' = Zshl) ⇒ (v12 = v12')) ∧
           ((M' = Zshr) ⇒ (v13 = v13')) ∧ ((M' = Ztest) ⇒ (v14 = v14')) ∧
           ((M' = Zsar) ⇒ (v15 = v15')) ⇒
           ((case M of
               Zadd => v0
             | Zor => v1
             | Zadc => v2
             | Zsbb => v3
             | Zand => v4
             | Zsub => v5
             | Zxor => v6
             | Zcmp => v7
             | Zrol => v8
             | Zror => v9
             | Zrcl => v10
             | Zrcr => v11
             | Zshl => v12
             | Zshr => v13
             | Ztest => v14
             | Zsar => v15) =
            case M' of
              Zadd => v0'
            | Zor => v1'
            | Zadc => v2'
            | Zsbb => v3'
            | Zand => v4'
            | Zsub => v5'
            | Zxor => v6'
            | Zcmp => v7'
            | Zrol => v8'
            | Zror => v9'
            | Zrcl => v10'
            | Zrcr => v11'
            | Zshl => v12'
            | Zshr => v13'
            | Ztest => v14'
            | Zsar => v15')

   [Zbinop_name_case_def]  Theorem

      |- (∀v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15.
            (case Zadd of
               Zadd => v0
             | Zor => v1
             | Zadc => v2
             | Zsbb => v3
             | Zand => v4
             | Zsub => v5
             | Zxor => v6
             | Zcmp => v7
             | Zrol => v8
             | Zror => v9
             | Zrcl => v10
             | Zrcr => v11
             | Zshl => v12
             | Zshr => v13
             | Ztest => v14
             | Zsar => v15) =
            v0) ∧
         (∀v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15.
            (case Zor of
               Zadd => v0
             | Zor => v1
             | Zadc => v2
             | Zsbb => v3
             | Zand => v4
             | Zsub => v5
             | Zxor => v6
             | Zcmp => v7
             | Zrol => v8
             | Zror => v9
             | Zrcl => v10
             | Zrcr => v11
             | Zshl => v12
             | Zshr => v13
             | Ztest => v14
             | Zsar => v15) =
            v1) ∧
         (∀v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15.
            (case Zadc of
               Zadd => v0
             | Zor => v1
             | Zadc => v2
             | Zsbb => v3
             | Zand => v4
             | Zsub => v5
             | Zxor => v6
             | Zcmp => v7
             | Zrol => v8
             | Zror => v9
             | Zrcl => v10
             | Zrcr => v11
             | Zshl => v12
             | Zshr => v13
             | Ztest => v14
             | Zsar => v15) =
            v2) ∧
         (∀v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15.
            (case Zsbb of
               Zadd => v0
             | Zor => v1
             | Zadc => v2
             | Zsbb => v3
             | Zand => v4
             | Zsub => v5
             | Zxor => v6
             | Zcmp => v7
             | Zrol => v8
             | Zror => v9
             | Zrcl => v10
             | Zrcr => v11
             | Zshl => v12
             | Zshr => v13
             | Ztest => v14
             | Zsar => v15) =
            v3) ∧
         (∀v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15.
            (case Zand of
               Zadd => v0
             | Zor => v1
             | Zadc => v2
             | Zsbb => v3
             | Zand => v4
             | Zsub => v5
             | Zxor => v6
             | Zcmp => v7
             | Zrol => v8
             | Zror => v9
             | Zrcl => v10
             | Zrcr => v11
             | Zshl => v12
             | Zshr => v13
             | Ztest => v14
             | Zsar => v15) =
            v4) ∧
         (∀v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15.
            (case Zsub of
               Zadd => v0
             | Zor => v1
             | Zadc => v2
             | Zsbb => v3
             | Zand => v4
             | Zsub => v5
             | Zxor => v6
             | Zcmp => v7
             | Zrol => v8
             | Zror => v9
             | Zrcl => v10
             | Zrcr => v11
             | Zshl => v12
             | Zshr => v13
             | Ztest => v14
             | Zsar => v15) =
            v5) ∧
         (∀v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15.
            (case Zxor of
               Zadd => v0
             | Zor => v1
             | Zadc => v2
             | Zsbb => v3
             | Zand => v4
             | Zsub => v5
             | Zxor => v6
             | Zcmp => v7
             | Zrol => v8
             | Zror => v9
             | Zrcl => v10
             | Zrcr => v11
             | Zshl => v12
             | Zshr => v13
             | Ztest => v14
             | Zsar => v15) =
            v6) ∧
         (∀v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15.
            (case Zcmp of
               Zadd => v0
             | Zor => v1
             | Zadc => v2
             | Zsbb => v3
             | Zand => v4
             | Zsub => v5
             | Zxor => v6
             | Zcmp => v7
             | Zrol => v8
             | Zror => v9
             | Zrcl => v10
             | Zrcr => v11
             | Zshl => v12
             | Zshr => v13
             | Ztest => v14
             | Zsar => v15) =
            v7) ∧
         (∀v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15.
            (case Zrol of
               Zadd => v0
             | Zor => v1
             | Zadc => v2
             | Zsbb => v3
             | Zand => v4
             | Zsub => v5
             | Zxor => v6
             | Zcmp => v7
             | Zrol => v8
             | Zror => v9
             | Zrcl => v10
             | Zrcr => v11
             | Zshl => v12
             | Zshr => v13
             | Ztest => v14
             | Zsar => v15) =
            v8) ∧
         (∀v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15.
            (case Zror of
               Zadd => v0
             | Zor => v1
             | Zadc => v2
             | Zsbb => v3
             | Zand => v4
             | Zsub => v5
             | Zxor => v6
             | Zcmp => v7
             | Zrol => v8
             | Zror => v9
             | Zrcl => v10
             | Zrcr => v11
             | Zshl => v12
             | Zshr => v13
             | Ztest => v14
             | Zsar => v15) =
            v9) ∧
         (∀v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15.
            (case Zrcl of
               Zadd => v0
             | Zor => v1
             | Zadc => v2
             | Zsbb => v3
             | Zand => v4
             | Zsub => v5
             | Zxor => v6
             | Zcmp => v7
             | Zrol => v8
             | Zror => v9
             | Zrcl => v10
             | Zrcr => v11
             | Zshl => v12
             | Zshr => v13
             | Ztest => v14
             | Zsar => v15) =
            v10) ∧
         (∀v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15.
            (case Zrcr of
               Zadd => v0
             | Zor => v1
             | Zadc => v2
             | Zsbb => v3
             | Zand => v4
             | Zsub => v5
             | Zxor => v6
             | Zcmp => v7
             | Zrol => v8
             | Zror => v9
             | Zrcl => v10
             | Zrcr => v11
             | Zshl => v12
             | Zshr => v13
             | Ztest => v14
             | Zsar => v15) =
            v11) ∧
         (∀v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15.
            (case Zshl of
               Zadd => v0
             | Zor => v1
             | Zadc => v2
             | Zsbb => v3
             | Zand => v4
             | Zsub => v5
             | Zxor => v6
             | Zcmp => v7
             | Zrol => v8
             | Zror => v9
             | Zrcl => v10
             | Zrcr => v11
             | Zshl => v12
             | Zshr => v13
             | Ztest => v14
             | Zsar => v15) =
            v12) ∧
         (∀v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15.
            (case Zshr of
               Zadd => v0
             | Zor => v1
             | Zadc => v2
             | Zsbb => v3
             | Zand => v4
             | Zsub => v5
             | Zxor => v6
             | Zcmp => v7
             | Zrol => v8
             | Zror => v9
             | Zrcl => v10
             | Zrcr => v11
             | Zshl => v12
             | Zshr => v13
             | Ztest => v14
             | Zsar => v15) =
            v13) ∧
         (∀v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15.
            (case Ztest of
               Zadd => v0
             | Zor => v1
             | Zadc => v2
             | Zsbb => v3
             | Zand => v4
             | Zsub => v5
             | Zxor => v6
             | Zcmp => v7
             | Zrol => v8
             | Zror => v9
             | Zrcl => v10
             | Zrcr => v11
             | Zshl => v12
             | Zshr => v13
             | Ztest => v14
             | Zsar => v15) =
            v14) ∧
         ∀v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15.
           (case Zsar of
              Zadd => v0
            | Zor => v1
            | Zadc => v2
            | Zsbb => v3
            | Zand => v4
            | Zsub => v5
            | Zxor => v6
            | Zcmp => v7
            | Zrol => v8
            | Zror => v9
            | Zrcl => v10
            | Zrcr => v11
            | Zshl => v12
            | Zshr => v13
            | Ztest => v14
            | Zsar => v15) =
           v15

   [Zbinop_name_induction]  Theorem

      |- ∀P.
           P Zadc ∧ P Zadd ∧ P Zand ∧ P Zcmp ∧ P Zor ∧ P Zrcl ∧ P Zrcr ∧
           P Zrol ∧ P Zror ∧ P Zsar ∧ P Zsbb ∧ P Zshl ∧ P Zshr ∧ P Zsub ∧
           P Ztest ∧ P Zxor ⇒
           ∀a. P a

   [Zbinop_name_nchotomy]  Theorem

      |- ∀a.
           (a = Zadd) ∨ (a = Zor) ∨ (a = Zadc) ∨ (a = Zsbb) ∨ (a = Zand) ∨
           (a = Zsub) ∨ (a = Zxor) ∨ (a = Zcmp) ∨ (a = Zrol) ∨ (a = Zror) ∨
           (a = Zrcl) ∨ (a = Zrcr) ∨ (a = Zshl) ∨ (a = Zshr) ∨
           (a = Ztest) ∨ (a = Zsar)

   [Zcond2num_11]  Theorem

      |- ∀a a'. (Zcond2num a = Zcond2num a') ⇔ (a = a')

   [Zcond2num_ONTO]  Theorem

      |- ∀r. r < 17 ⇔ ∃a. r = Zcond2num a

   [Zcond2num_num2Zcond]  Theorem

      |- ∀r. r < 17 ⇔ (Zcond2num (num2Zcond r) = r)

   [Zcond2num_thm]  Theorem

      |- (Zcond2num Z_O = 0) ∧ (Zcond2num Z_NO = 1) ∧ (Zcond2num Z_B = 2) ∧
         (Zcond2num Z_NB = 3) ∧ (Zcond2num Z_E = 4) ∧
         (Zcond2num Z_NE = 5) ∧ (Zcond2num Z_NA = 6) ∧
         (Zcond2num Z_A = 7) ∧ (Zcond2num Z_S = 8) ∧ (Zcond2num Z_NS = 9) ∧
         (Zcond2num Z_P = 10) ∧ (Zcond2num Z_NP = 11) ∧
         (Zcond2num Z_L = 12) ∧ (Zcond2num Z_NL = 13) ∧
         (Zcond2num Z_NG = 14) ∧ (Zcond2num Z_G = 15) ∧
         (Zcond2num Z_ALWAYS = 16)

   [Zcond_Axiom]  Theorem

      |- ∀x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16.
           ∃f.
             (f Z_O = x0) ∧ (f Z_NO = x1) ∧ (f Z_B = x2) ∧ (f Z_NB = x3) ∧
             (f Z_E = x4) ∧ (f Z_NE = x5) ∧ (f Z_NA = x6) ∧ (f Z_A = x7) ∧
             (f Z_S = x8) ∧ (f Z_NS = x9) ∧ (f Z_P = x10) ∧
             (f Z_NP = x11) ∧ (f Z_L = x12) ∧ (f Z_NL = x13) ∧
             (f Z_NG = x14) ∧ (f Z_G = x15) ∧ (f Z_ALWAYS = x16)

   [Zcond_EQ_Zcond]  Theorem

      |- ∀a a'. (a = a') ⇔ (Zcond2num a = Zcond2num a')

   [Zcond_case_cong]  Theorem

      |- ∀M M' v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16.
           (M = M') ∧ ((M' = Z_O) ⇒ (v0 = v0')) ∧
           ((M' = Z_NO) ⇒ (v1 = v1')) ∧ ((M' = Z_B) ⇒ (v2 = v2')) ∧
           ((M' = Z_NB) ⇒ (v3 = v3')) ∧ ((M' = Z_E) ⇒ (v4 = v4')) ∧
           ((M' = Z_NE) ⇒ (v5 = v5')) ∧ ((M' = Z_NA) ⇒ (v6 = v6')) ∧
           ((M' = Z_A) ⇒ (v7 = v7')) ∧ ((M' = Z_S) ⇒ (v8 = v8')) ∧
           ((M' = Z_NS) ⇒ (v9 = v9')) ∧ ((M' = Z_P) ⇒ (v10 = v10')) ∧
           ((M' = Z_NP) ⇒ (v11 = v11')) ∧ ((M' = Z_L) ⇒ (v12 = v12')) ∧
           ((M' = Z_NL) ⇒ (v13 = v13')) ∧ ((M' = Z_NG) ⇒ (v14 = v14')) ∧
           ((M' = Z_G) ⇒ (v15 = v15')) ∧ ((M' = Z_ALWAYS) ⇒ (v16 = v16')) ⇒
           ((case M of
               Z_O => v0
             | Z_NO => v1
             | Z_B => v2
             | Z_NB => v3
             | Z_E => v4
             | Z_NE => v5
             | Z_NA => v6
             | Z_A => v7
             | Z_S => v8
             | Z_NS => v9
             | Z_P => v10
             | Z_NP => v11
             | Z_L => v12
             | Z_NL => v13
             | Z_NG => v14
             | Z_G => v15
             | Z_ALWAYS => v16) =
            case M' of
              Z_O => v0'
            | Z_NO => v1'
            | Z_B => v2'
            | Z_NB => v3'
            | Z_E => v4'
            | Z_NE => v5'
            | Z_NA => v6'
            | Z_A => v7'
            | Z_S => v8'
            | Z_NS => v9'
            | Z_P => v10'
            | Z_NP => v11'
            | Z_L => v12'
            | Z_NL => v13'
            | Z_NG => v14'
            | Z_G => v15'
            | Z_ALWAYS => v16')

   [Zcond_case_def]  Theorem

      |- (∀v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16.
            (case Z_O of
               Z_O => v0
             | Z_NO => v1
             | Z_B => v2
             | Z_NB => v3
             | Z_E => v4
             | Z_NE => v5
             | Z_NA => v6
             | Z_A => v7
             | Z_S => v8
             | Z_NS => v9
             | Z_P => v10
             | Z_NP => v11
             | Z_L => v12
             | Z_NL => v13
             | Z_NG => v14
             | Z_G => v15
             | Z_ALWAYS => v16) =
            v0) ∧
         (∀v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16.
            (case Z_NO of
               Z_O => v0
             | Z_NO => v1
             | Z_B => v2
             | Z_NB => v3
             | Z_E => v4
             | Z_NE => v5
             | Z_NA => v6
             | Z_A => v7
             | Z_S => v8
             | Z_NS => v9
             | Z_P => v10
             | Z_NP => v11
             | Z_L => v12
             | Z_NL => v13
             | Z_NG => v14
             | Z_G => v15
             | Z_ALWAYS => v16) =
            v1) ∧
         (∀v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16.
            (case Z_B of
               Z_O => v0
             | Z_NO => v1
             | Z_B => v2
             | Z_NB => v3
             | Z_E => v4
             | Z_NE => v5
             | Z_NA => v6
             | Z_A => v7
             | Z_S => v8
             | Z_NS => v9
             | Z_P => v10
             | Z_NP => v11
             | Z_L => v12
             | Z_NL => v13
             | Z_NG => v14
             | Z_G => v15
             | Z_ALWAYS => v16) =
            v2) ∧
         (∀v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16.
            (case Z_NB of
               Z_O => v0
             | Z_NO => v1
             | Z_B => v2
             | Z_NB => v3
             | Z_E => v4
             | Z_NE => v5
             | Z_NA => v6
             | Z_A => v7
             | Z_S => v8
             | Z_NS => v9
             | Z_P => v10
             | Z_NP => v11
             | Z_L => v12
             | Z_NL => v13
             | Z_NG => v14
             | Z_G => v15
             | Z_ALWAYS => v16) =
            v3) ∧
         (∀v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16.
            (case Z_E of
               Z_O => v0
             | Z_NO => v1
             | Z_B => v2
             | Z_NB => v3
             | Z_E => v4
             | Z_NE => v5
             | Z_NA => v6
             | Z_A => v7
             | Z_S => v8
             | Z_NS => v9
             | Z_P => v10
             | Z_NP => v11
             | Z_L => v12
             | Z_NL => v13
             | Z_NG => v14
             | Z_G => v15
             | Z_ALWAYS => v16) =
            v4) ∧
         (∀v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16.
            (case Z_NE of
               Z_O => v0
             | Z_NO => v1
             | Z_B => v2
             | Z_NB => v3
             | Z_E => v4
             | Z_NE => v5
             | Z_NA => v6
             | Z_A => v7
             | Z_S => v8
             | Z_NS => v9
             | Z_P => v10
             | Z_NP => v11
             | Z_L => v12
             | Z_NL => v13
             | Z_NG => v14
             | Z_G => v15
             | Z_ALWAYS => v16) =
            v5) ∧
         (∀v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16.
            (case Z_NA of
               Z_O => v0
             | Z_NO => v1
             | Z_B => v2
             | Z_NB => v3
             | Z_E => v4
             | Z_NE => v5
             | Z_NA => v6
             | Z_A => v7
             | Z_S => v8
             | Z_NS => v9
             | Z_P => v10
             | Z_NP => v11
             | Z_L => v12
             | Z_NL => v13
             | Z_NG => v14
             | Z_G => v15
             | Z_ALWAYS => v16) =
            v6) ∧
         (∀v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16.
            (case Z_A of
               Z_O => v0
             | Z_NO => v1
             | Z_B => v2
             | Z_NB => v3
             | Z_E => v4
             | Z_NE => v5
             | Z_NA => v6
             | Z_A => v7
             | Z_S => v8
             | Z_NS => v9
             | Z_P => v10
             | Z_NP => v11
             | Z_L => v12
             | Z_NL => v13
             | Z_NG => v14
             | Z_G => v15
             | Z_ALWAYS => v16) =
            v7) ∧
         (∀v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16.
            (case Z_S of
               Z_O => v0
             | Z_NO => v1
             | Z_B => v2
             | Z_NB => v3
             | Z_E => v4
             | Z_NE => v5
             | Z_NA => v6
             | Z_A => v7
             | Z_S => v8
             | Z_NS => v9
             | Z_P => v10
             | Z_NP => v11
             | Z_L => v12
             | Z_NL => v13
             | Z_NG => v14
             | Z_G => v15
             | Z_ALWAYS => v16) =
            v8) ∧
         (∀v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16.
            (case Z_NS of
               Z_O => v0
             | Z_NO => v1
             | Z_B => v2
             | Z_NB => v3
             | Z_E => v4
             | Z_NE => v5
             | Z_NA => v6
             | Z_A => v7
             | Z_S => v8
             | Z_NS => v9
             | Z_P => v10
             | Z_NP => v11
             | Z_L => v12
             | Z_NL => v13
             | Z_NG => v14
             | Z_G => v15
             | Z_ALWAYS => v16) =
            v9) ∧
         (∀v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16.
            (case Z_P of
               Z_O => v0
             | Z_NO => v1
             | Z_B => v2
             | Z_NB => v3
             | Z_E => v4
             | Z_NE => v5
             | Z_NA => v6
             | Z_A => v7
             | Z_S => v8
             | Z_NS => v9
             | Z_P => v10
             | Z_NP => v11
             | Z_L => v12
             | Z_NL => v13
             | Z_NG => v14
             | Z_G => v15
             | Z_ALWAYS => v16) =
            v10) ∧
         (∀v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16.
            (case Z_NP of
               Z_O => v0
             | Z_NO => v1
             | Z_B => v2
             | Z_NB => v3
             | Z_E => v4
             | Z_NE => v5
             | Z_NA => v6
             | Z_A => v7
             | Z_S => v8
             | Z_NS => v9
             | Z_P => v10
             | Z_NP => v11
             | Z_L => v12
             | Z_NL => v13
             | Z_NG => v14
             | Z_G => v15
             | Z_ALWAYS => v16) =
            v11) ∧
         (∀v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16.
            (case Z_L of
               Z_O => v0
             | Z_NO => v1
             | Z_B => v2
             | Z_NB => v3
             | Z_E => v4
             | Z_NE => v5
             | Z_NA => v6
             | Z_A => v7
             | Z_S => v8
             | Z_NS => v9
             | Z_P => v10
             | Z_NP => v11
             | Z_L => v12
             | Z_NL => v13
             | Z_NG => v14
             | Z_G => v15
             | Z_ALWAYS => v16) =
            v12) ∧
         (∀v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16.
            (case Z_NL of
               Z_O => v0
             | Z_NO => v1
             | Z_B => v2
             | Z_NB => v3
             | Z_E => v4
             | Z_NE => v5
             | Z_NA => v6
             | Z_A => v7
             | Z_S => v8
             | Z_NS => v9
             | Z_P => v10
             | Z_NP => v11
             | Z_L => v12
             | Z_NL => v13
             | Z_NG => v14
             | Z_G => v15
             | Z_ALWAYS => v16) =
            v13) ∧
         (∀v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16.
            (case Z_NG of
               Z_O => v0
             | Z_NO => v1
             | Z_B => v2
             | Z_NB => v3
             | Z_E => v4
             | Z_NE => v5
             | Z_NA => v6
             | Z_A => v7
             | Z_S => v8
             | Z_NS => v9
             | Z_P => v10
             | Z_NP => v11
             | Z_L => v12
             | Z_NL => v13
             | Z_NG => v14
             | Z_G => v15
             | Z_ALWAYS => v16) =
            v14) ∧
         (∀v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16.
            (case Z_G of
               Z_O => v0
             | Z_NO => v1
             | Z_B => v2
             | Z_NB => v3
             | Z_E => v4
             | Z_NE => v5
             | Z_NA => v6
             | Z_A => v7
             | Z_S => v8
             | Z_NS => v9
             | Z_P => v10
             | Z_NP => v11
             | Z_L => v12
             | Z_NL => v13
             | Z_NG => v14
             | Z_G => v15
             | Z_ALWAYS => v16) =
            v15) ∧
         ∀v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16.
           (case Z_ALWAYS of
              Z_O => v0
            | Z_NO => v1
            | Z_B => v2
            | Z_NB => v3
            | Z_E => v4
            | Z_NE => v5
            | Z_NA => v6
            | Z_A => v7
            | Z_S => v8
            | Z_NS => v9
            | Z_P => v10
            | Z_NP => v11
            | Z_L => v12
            | Z_NL => v13
            | Z_NG => v14
            | Z_G => v15
            | Z_ALWAYS => v16) =
           v16

   [Zcond_induction]  Theorem

      |- ∀P.
           P Z_A ∧ P Z_ALWAYS ∧ P Z_B ∧ P Z_E ∧ P Z_G ∧ P Z_L ∧ P Z_NA ∧
           P Z_NB ∧ P Z_NE ∧ P Z_NG ∧ P Z_NL ∧ P Z_NO ∧ P Z_NP ∧ P Z_NS ∧
           P Z_O ∧ P Z_P ∧ P Z_S ⇒
           ∀a. P a

   [Zcond_nchotomy]  Theorem

      |- ∀a.
           (a = Z_O) ∨ (a = Z_NO) ∨ (a = Z_B) ∨ (a = Z_NB) ∨ (a = Z_E) ∨
           (a = Z_NE) ∨ (a = Z_NA) ∨ (a = Z_A) ∨ (a = Z_S) ∨ (a = Z_NS) ∨
           (a = Z_P) ∨ (a = Z_NP) ∨ (a = Z_L) ∨ (a = Z_NL) ∨ (a = Z_NG) ∨
           (a = Z_G) ∨ (a = Z_ALWAYS)

   [Zdest_src_11]  Theorem

      |- (∀a a'. (Zr_rm a = Zr_rm a') ⇔ (a = a')) ∧
         (∀a a'. (Zrm_i a = Zrm_i a') ⇔ (a = a')) ∧
         ∀a a'. (Zrm_r a = Zrm_r a') ⇔ (a = a')

   [Zdest_src_Axiom]  Theorem

      |- ∀f0 f1 f2.
           ∃fn.
             (∀a. fn (Zr_rm a) = f0 a) ∧ (∀a. fn (Zrm_i a) = f1 a) ∧
             ∀a. fn (Zrm_r a) = f2 a

   [Zdest_src_case_cong]  Theorem

      |- ∀M M' f f1 f2.
           (M = M') ∧ (∀a. (M' = Zr_rm a) ⇒ (f a = f' a)) ∧
           (∀a. (M' = Zrm_i a) ⇒ (f1 a = f1' a)) ∧
           (∀a. (M' = Zrm_r a) ⇒ (f2 a = f2' a)) ⇒
           (Zdest_src_CASE M f f1 f2 = Zdest_src_CASE M' f' f1' f2')

   [Zdest_src_distinct]  Theorem

      |- (∀a' a. Zr_rm a ≠ Zrm_i a') ∧ (∀a' a. Zr_rm a ≠ Zrm_r a') ∧
         ∀a' a. Zrm_i a ≠ Zrm_r a'

   [Zdest_src_induction]  Theorem

      |- ∀P.
           (∀p. P (Zr_rm p)) ∧ (∀p. P (Zrm_i p)) ∧ (∀p. P (Zrm_r p)) ⇒
           ∀Z. P Z

   [Zdest_src_nchotomy]  Theorem

      |- ∀ZZ. (∃p. ZZ = Zr_rm p) ∨ (∃p. ZZ = Zrm_i p) ∨ ∃p. ZZ = Zrm_r p

   [Zea_11]  Theorem

      |- (∀a a'. (Zea_i a = Zea_i a') ⇔ (a = a')) ∧
         (∀a a'. (Zea_m a = Zea_m a') ⇔ (a = a')) ∧
         ∀a a'. (Zea_r a = Zea_r a') ⇔ (a = a')

   [Zea_Axiom]  Theorem

      |- ∀f0 f1 f2.
           ∃fn.
             (∀a. fn (Zea_i a) = f0 a) ∧ (∀a. fn (Zea_m a) = f1 a) ∧
             ∀a. fn (Zea_r a) = f2 a

   [Zea_case_cong]  Theorem

      |- ∀M M' f f1 f2.
           (M = M') ∧ (∀a. (M' = Zea_i a) ⇒ (f a = f' a)) ∧
           (∀a. (M' = Zea_m a) ⇒ (f1 a = f1' a)) ∧
           (∀a. (M' = Zea_r a) ⇒ (f2 a = f2' a)) ⇒
           (Zea_CASE M f f1 f2 = Zea_CASE M' f' f1' f2')

   [Zea_distinct]  Theorem

      |- (∀a' a. Zea_i a ≠ Zea_m a') ∧ (∀a' a. Zea_i a ≠ Zea_r a') ∧
         ∀a' a. Zea_m a ≠ Zea_r a'

   [Zea_induction]  Theorem

      |- ∀P.
           (∀p. P (Zea_i p)) ∧ (∀p. P (Zea_m p)) ∧ (∀p. P (Zea_r p)) ⇒
           ∀Z. P Z

   [Zea_nchotomy]  Theorem

      |- ∀ZZ. (∃p. ZZ = Zea_i p) ∨ (∃p. ZZ = Zea_m p) ∨ ∃p. ZZ = Zea_r p

   [Zeflags2num_11]  Theorem

      |- ∀a a'. (Zeflags2num a = Zeflags2num a') ⇔ (a = a')

   [Zeflags2num_ONTO]  Theorem

      |- ∀r. r < 6 ⇔ ∃a. r = Zeflags2num a

   [Zeflags2num_num2Zeflags]  Theorem

      |- ∀r. r < 6 ⇔ (Zeflags2num (num2Zeflags r) = r)

   [Zeflags2num_thm]  Theorem

      |- (Zeflags2num Z_CF = 0) ∧ (Zeflags2num Z_PF = 1) ∧
         (Zeflags2num Z_AF = 2) ∧ (Zeflags2num Z_ZF = 3) ∧
         (Zeflags2num Z_SF = 4) ∧ (Zeflags2num Z_OF = 5)

   [Zeflags_Axiom]  Theorem

      |- ∀x0 x1 x2 x3 x4 x5.
           ∃f.
             (f Z_CF = x0) ∧ (f Z_PF = x1) ∧ (f Z_AF = x2) ∧
             (f Z_ZF = x3) ∧ (f Z_SF = x4) ∧ (f Z_OF = x5)

   [Zeflags_EQ_Zeflags]  Theorem

      |- ∀a a'. (a = a') ⇔ (Zeflags2num a = Zeflags2num a')

   [Zeflags_case_cong]  Theorem

      |- ∀M M' v0 v1 v2 v3 v4 v5.
           (M = M') ∧ ((M' = Z_CF) ⇒ (v0 = v0')) ∧
           ((M' = Z_PF) ⇒ (v1 = v1')) ∧ ((M' = Z_AF) ⇒ (v2 = v2')) ∧
           ((M' = Z_ZF) ⇒ (v3 = v3')) ∧ ((M' = Z_SF) ⇒ (v4 = v4')) ∧
           ((M' = Z_OF) ⇒ (v5 = v5')) ⇒
           ((case M of
               Z_CF => v0
             | Z_PF => v1
             | Z_AF => v2
             | Z_ZF => v3
             | Z_SF => v4
             | Z_OF => v5) =
            case M' of
              Z_CF => v0'
            | Z_PF => v1'
            | Z_AF => v2'
            | Z_ZF => v3'
            | Z_SF => v4'
            | Z_OF => v5')

   [Zeflags_case_def]  Theorem

      |- (∀v0 v1 v2 v3 v4 v5.
            (case Z_CF of
               Z_CF => v0
             | Z_PF => v1
             | Z_AF => v2
             | Z_ZF => v3
             | Z_SF => v4
             | Z_OF => v5) =
            v0) ∧
         (∀v0 v1 v2 v3 v4 v5.
            (case Z_PF of
               Z_CF => v0
             | Z_PF => v1
             | Z_AF => v2
             | Z_ZF => v3
             | Z_SF => v4
             | Z_OF => v5) =
            v1) ∧
         (∀v0 v1 v2 v3 v4 v5.
            (case Z_AF of
               Z_CF => v0
             | Z_PF => v1
             | Z_AF => v2
             | Z_ZF => v3
             | Z_SF => v4
             | Z_OF => v5) =
            v2) ∧
         (∀v0 v1 v2 v3 v4 v5.
            (case Z_ZF of
               Z_CF => v0
             | Z_PF => v1
             | Z_AF => v2
             | Z_ZF => v3
             | Z_SF => v4
             | Z_OF => v5) =
            v3) ∧
         (∀v0 v1 v2 v3 v4 v5.
            (case Z_SF of
               Z_CF => v0
             | Z_PF => v1
             | Z_AF => v2
             | Z_ZF => v3
             | Z_SF => v4
             | Z_OF => v5) =
            v4) ∧
         ∀v0 v1 v2 v3 v4 v5.
           (case Z_OF of
              Z_CF => v0
            | Z_PF => v1
            | Z_AF => v2
            | Z_ZF => v3
            | Z_SF => v4
            | Z_OF => v5) =
           v5

   [Zeflags_distinct]  Theorem

      |- Z_CF ≠ Z_PF ∧ Z_CF ≠ Z_AF ∧ Z_CF ≠ Z_ZF ∧ Z_CF ≠ Z_SF ∧
         Z_CF ≠ Z_OF ∧ Z_PF ≠ Z_AF ∧ Z_PF ≠ Z_ZF ∧ Z_PF ≠ Z_SF ∧
         Z_PF ≠ Z_OF ∧ Z_AF ≠ Z_ZF ∧ Z_AF ≠ Z_SF ∧ Z_AF ≠ Z_OF ∧
         Z_ZF ≠ Z_SF ∧ Z_ZF ≠ Z_OF ∧ Z_SF ≠ Z_OF

   [Zeflags_induction]  Theorem

      |- ∀P. P Z_AF ∧ P Z_CF ∧ P Z_OF ∧ P Z_PF ∧ P Z_SF ∧ P Z_ZF ⇒ ∀a. P a

   [Zeflags_nchotomy]  Theorem

      |- ∀a.
           (a = Z_CF) ∨ (a = Z_PF) ∨ (a = Z_AF) ∨ (a = Z_ZF) ∨ (a = Z_SF) ∨
           (a = Z_OF)

   [Zimm_rm_11]  Theorem

      |- (∀a a'. (Zimm a = Zimm a') ⇔ (a = a')) ∧
         ∀a a'. (Zrm a = Zrm a') ⇔ (a = a')

   [Zimm_rm_Axiom]  Theorem

      |- ∀f0 f1. ∃fn. (∀a. fn (Zimm a) = f0 a) ∧ ∀a. fn (Zrm a) = f1 a

   [Zimm_rm_case_cong]  Theorem

      |- ∀M M' f f1.
           (M = M') ∧ (∀a. (M' = Zimm a) ⇒ (f a = f' a)) ∧
           (∀a. (M' = Zrm a) ⇒ (f1 a = f1' a)) ⇒
           (Zimm_rm_CASE M f f1 = Zimm_rm_CASE M' f' f1')

   [Zimm_rm_distinct]  Theorem

      |- ∀a' a. Zimm a ≠ Zrm a'

   [Zimm_rm_induction]  Theorem

      |- ∀P. (∀c. P (Zimm c)) ∧ (∀Z. P (Zrm Z)) ⇒ ∀Z. P Z

   [Zimm_rm_nchotomy]  Theorem

      |- ∀ZZ. (∃c. ZZ = Zimm c) ∨ ∃Z. ZZ = Zrm Z

   [Zinst_11]  Theorem

      |- (∀a a'. (Zdec_fail a = Zdec_fail a') ⇔ (a = a')) ∧
         ∀a a'. (Zfull_inst a = Zfull_inst a') ⇔ (a = a')

   [Zinst_Axiom]  Theorem

      |- ∀f0 f1.
           ∃fn.
             (∀a. fn (Zdec_fail a) = f0 a) ∧ ∀a. fn (Zfull_inst a) = f1 a

   [Zinst_case_cong]  Theorem

      |- ∀M M' f f1.
           (M = M') ∧ (∀a. (M' = Zdec_fail a) ⇒ (f a = f' a)) ∧
           (∀a. (M' = Zfull_inst a) ⇒ (f1 a = f1' a)) ⇒
           (Zinst_CASE M f f1 = Zinst_CASE M' f' f1')

   [Zinst_distinct]  Theorem

      |- ∀a' a. Zdec_fail a ≠ Zfull_inst a'

   [Zinst_induction]  Theorem

      |- ∀P. (∀s. P (Zdec_fail s)) ∧ (∀p. P (Zfull_inst p)) ⇒ ∀Z. P Z

   [Zinst_nchotomy]  Theorem

      |- ∀ZZ. (∃s. ZZ = Zdec_fail s) ∨ ∃p. ZZ = Zfull_inst p

   [Zmonop_name2num_11]  Theorem

      |- ∀a a'. (Zmonop_name2num a = Zmonop_name2num a') ⇔ (a = a')

   [Zmonop_name2num_ONTO]  Theorem

      |- ∀r. r < 4 ⇔ ∃a. r = Zmonop_name2num a

   [Zmonop_name2num_num2Zmonop_name]  Theorem

      |- ∀r. r < 4 ⇔ (Zmonop_name2num (num2Zmonop_name r) = r)

   [Zmonop_name2num_thm]  Theorem

      |- (Zmonop_name2num Zdec = 0) ∧ (Zmonop_name2num Zinc = 1) ∧
         (Zmonop_name2num Znot = 2) ∧ (Zmonop_name2num Zneg = 3)

   [Zmonop_name_Axiom]  Theorem

      |- ∀x0 x1 x2 x3.
           ∃f.
             (f Zdec = x0) ∧ (f Zinc = x1) ∧ (f Znot = x2) ∧ (f Zneg = x3)

   [Zmonop_name_EQ_Zmonop_name]  Theorem

      |- ∀a a'. (a = a') ⇔ (Zmonop_name2num a = Zmonop_name2num a')

   [Zmonop_name_case_cong]  Theorem

      |- ∀M M' v0 v1 v2 v3.
           (M = M') ∧ ((M' = Zdec) ⇒ (v0 = v0')) ∧
           ((M' = Zinc) ⇒ (v1 = v1')) ∧ ((M' = Znot) ⇒ (v2 = v2')) ∧
           ((M' = Zneg) ⇒ (v3 = v3')) ⇒
           ((case M of Zdec => v0 | Zinc => v1 | Znot => v2 | Zneg => v3) =
            case M' of
              Zdec => v0'
            | Zinc => v1'
            | Znot => v2'
            | Zneg => v3')

   [Zmonop_name_case_def]  Theorem

      |- (∀v0 v1 v2 v3.
            (case Zdec of
               Zdec => v0
             | Zinc => v1
             | Znot => v2
             | Zneg => v3) =
            v0) ∧
         (∀v0 v1 v2 v3.
            (case Zinc of
               Zdec => v0
             | Zinc => v1
             | Znot => v2
             | Zneg => v3) =
            v1) ∧
         (∀v0 v1 v2 v3.
            (case Znot of
               Zdec => v0
             | Zinc => v1
             | Znot => v2
             | Zneg => v3) =
            v2) ∧
         ∀v0 v1 v2 v3.
           (case Zneg of
              Zdec => v0
            | Zinc => v1
            | Znot => v2
            | Zneg => v3) =
           v3

   [Zmonop_name_distinct]  Theorem

      |- Zdec ≠ Zinc ∧ Zdec ≠ Znot ∧ Zdec ≠ Zneg ∧ Zinc ≠ Znot ∧
         Zinc ≠ Zneg ∧ Znot ≠ Zneg

   [Zmonop_name_induction]  Theorem

      |- ∀P. P Zdec ∧ P Zinc ∧ P Zneg ∧ P Znot ⇒ ∀a. P a

   [Zmonop_name_nchotomy]  Theorem

      |- ∀a. (a = Zdec) ∨ (a = Zinc) ∨ (a = Znot) ∨ (a = Zneg)

   [Zreg2num_11]  Theorem

      |- ∀a a'. (Zreg2num a = Zreg2num a') ⇔ (a = a')

   [Zreg2num_ONTO]  Theorem

      |- ∀r. r < 16 ⇔ ∃a. r = Zreg2num a

   [Zreg2num_num2Zreg]  Theorem

      |- ∀r. r < 16 ⇔ (Zreg2num (num2Zreg r) = r)

   [Zreg2num_thm]  Theorem

      |- (Zreg2num RAX = 0) ∧ (Zreg2num RCX = 1) ∧ (Zreg2num RDX = 2) ∧
         (Zreg2num RBX = 3) ∧ (Zreg2num RSP = 4) ∧ (Zreg2num RBP = 5) ∧
         (Zreg2num RSI = 6) ∧ (Zreg2num RDI = 7) ∧ (Zreg2num zR8 = 8) ∧
         (Zreg2num zR9 = 9) ∧ (Zreg2num zR10 = 10) ∧ (Zreg2num zR11 = 11) ∧
         (Zreg2num zR12 = 12) ∧ (Zreg2num zR13 = 13) ∧
         (Zreg2num zR14 = 14) ∧ (Zreg2num zR15 = 15)

   [Zreg_Axiom]  Theorem

      |- ∀x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15.
           ∃f.
             (f RAX = x0) ∧ (f RCX = x1) ∧ (f RDX = x2) ∧ (f RBX = x3) ∧
             (f RSP = x4) ∧ (f RBP = x5) ∧ (f RSI = x6) ∧ (f RDI = x7) ∧
             (f zR8 = x8) ∧ (f zR9 = x9) ∧ (f zR10 = x10) ∧
             (f zR11 = x11) ∧ (f zR12 = x12) ∧ (f zR13 = x13) ∧
             (f zR14 = x14) ∧ (f zR15 = x15)

   [Zreg_EQ_Zreg]  Theorem

      |- ∀a a'. (a = a') ⇔ (Zreg2num a = Zreg2num a')

   [Zreg_case_cong]  Theorem

      |- ∀M M' v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15.
           (M = M') ∧ ((M' = RAX) ⇒ (v0 = v0')) ∧
           ((M' = RCX) ⇒ (v1 = v1')) ∧ ((M' = RDX) ⇒ (v2 = v2')) ∧
           ((M' = RBX) ⇒ (v3 = v3')) ∧ ((M' = RSP) ⇒ (v4 = v4')) ∧
           ((M' = RBP) ⇒ (v5 = v5')) ∧ ((M' = RSI) ⇒ (v6 = v6')) ∧
           ((M' = RDI) ⇒ (v7 = v7')) ∧ ((M' = zR8) ⇒ (v8 = v8')) ∧
           ((M' = zR9) ⇒ (v9 = v9')) ∧ ((M' = zR10) ⇒ (v10 = v10')) ∧
           ((M' = zR11) ⇒ (v11 = v11')) ∧ ((M' = zR12) ⇒ (v12 = v12')) ∧
           ((M' = zR13) ⇒ (v13 = v13')) ∧ ((M' = zR14) ⇒ (v14 = v14')) ∧
           ((M' = zR15) ⇒ (v15 = v15')) ⇒
           ((case M of
               RAX => v0
             | RCX => v1
             | RDX => v2
             | RBX => v3
             | RSP => v4
             | RBP => v5
             | RSI => v6
             | RDI => v7
             | zR8 => v8
             | zR9 => v9
             | zR10 => v10
             | zR11 => v11
             | zR12 => v12
             | zR13 => v13
             | zR14 => v14
             | zR15 => v15) =
            case M' of
              RAX => v0'
            | RCX => v1'
            | RDX => v2'
            | RBX => v3'
            | RSP => v4'
            | RBP => v5'
            | RSI => v6'
            | RDI => v7'
            | zR8 => v8'
            | zR9 => v9'
            | zR10 => v10'
            | zR11 => v11'
            | zR12 => v12'
            | zR13 => v13'
            | zR14 => v14'
            | zR15 => v15')

   [Zreg_case_def]  Theorem

      |- (∀v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15.
            (case RAX of
               RAX => v0
             | RCX => v1
             | RDX => v2
             | RBX => v3
             | RSP => v4
             | RBP => v5
             | RSI => v6
             | RDI => v7
             | zR8 => v8
             | zR9 => v9
             | zR10 => v10
             | zR11 => v11
             | zR12 => v12
             | zR13 => v13
             | zR14 => v14
             | zR15 => v15) =
            v0) ∧
         (∀v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15.
            (case RCX of
               RAX => v0
             | RCX => v1
             | RDX => v2
             | RBX => v3
             | RSP => v4
             | RBP => v5
             | RSI => v6
             | RDI => v7
             | zR8 => v8
             | zR9 => v9
             | zR10 => v10
             | zR11 => v11
             | zR12 => v12
             | zR13 => v13
             | zR14 => v14
             | zR15 => v15) =
            v1) ∧
         (∀v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15.
            (case RDX of
               RAX => v0
             | RCX => v1
             | RDX => v2
             | RBX => v3
             | RSP => v4
             | RBP => v5
             | RSI => v6
             | RDI => v7
             | zR8 => v8
             | zR9 => v9
             | zR10 => v10
             | zR11 => v11
             | zR12 => v12
             | zR13 => v13
             | zR14 => v14
             | zR15 => v15) =
            v2) ∧
         (∀v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15.
            (case RBX of
               RAX => v0
             | RCX => v1
             | RDX => v2
             | RBX => v3
             | RSP => v4
             | RBP => v5
             | RSI => v6
             | RDI => v7
             | zR8 => v8
             | zR9 => v9
             | zR10 => v10
             | zR11 => v11
             | zR12 => v12
             | zR13 => v13
             | zR14 => v14
             | zR15 => v15) =
            v3) ∧
         (∀v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15.
            (case RSP of
               RAX => v0
             | RCX => v1
             | RDX => v2
             | RBX => v3
             | RSP => v4
             | RBP => v5
             | RSI => v6
             | RDI => v7
             | zR8 => v8
             | zR9 => v9
             | zR10 => v10
             | zR11 => v11
             | zR12 => v12
             | zR13 => v13
             | zR14 => v14
             | zR15 => v15) =
            v4) ∧
         (∀v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15.
            (case RBP of
               RAX => v0
             | RCX => v1
             | RDX => v2
             | RBX => v3
             | RSP => v4
             | RBP => v5
             | RSI => v6
             | RDI => v7
             | zR8 => v8
             | zR9 => v9
             | zR10 => v10
             | zR11 => v11
             | zR12 => v12
             | zR13 => v13
             | zR14 => v14
             | zR15 => v15) =
            v5) ∧
         (∀v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15.
            (case RSI of
               RAX => v0
             | RCX => v1
             | RDX => v2
             | RBX => v3
             | RSP => v4
             | RBP => v5
             | RSI => v6
             | RDI => v7
             | zR8 => v8
             | zR9 => v9
             | zR10 => v10
             | zR11 => v11
             | zR12 => v12
             | zR13 => v13
             | zR14 => v14
             | zR15 => v15) =
            v6) ∧
         (∀v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15.
            (case RDI of
               RAX => v0
             | RCX => v1
             | RDX => v2
             | RBX => v3
             | RSP => v4
             | RBP => v5
             | RSI => v6
             | RDI => v7
             | zR8 => v8
             | zR9 => v9
             | zR10 => v10
             | zR11 => v11
             | zR12 => v12
             | zR13 => v13
             | zR14 => v14
             | zR15 => v15) =
            v7) ∧
         (∀v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15.
            (case zR8 of
               RAX => v0
             | RCX => v1
             | RDX => v2
             | RBX => v3
             | RSP => v4
             | RBP => v5
             | RSI => v6
             | RDI => v7
             | zR8 => v8
             | zR9 => v9
             | zR10 => v10
             | zR11 => v11
             | zR12 => v12
             | zR13 => v13
             | zR14 => v14
             | zR15 => v15) =
            v8) ∧
         (∀v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15.
            (case zR9 of
               RAX => v0
             | RCX => v1
             | RDX => v2
             | RBX => v3
             | RSP => v4
             | RBP => v5
             | RSI => v6
             | RDI => v7
             | zR8 => v8
             | zR9 => v9
             | zR10 => v10
             | zR11 => v11
             | zR12 => v12
             | zR13 => v13
             | zR14 => v14
             | zR15 => v15) =
            v9) ∧
         (∀v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15.
            (case zR10 of
               RAX => v0
             | RCX => v1
             | RDX => v2
             | RBX => v3
             | RSP => v4
             | RBP => v5
             | RSI => v6
             | RDI => v7
             | zR8 => v8
             | zR9 => v9
             | zR10 => v10
             | zR11 => v11
             | zR12 => v12
             | zR13 => v13
             | zR14 => v14
             | zR15 => v15) =
            v10) ∧
         (∀v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15.
            (case zR11 of
               RAX => v0
             | RCX => v1
             | RDX => v2
             | RBX => v3
             | RSP => v4
             | RBP => v5
             | RSI => v6
             | RDI => v7
             | zR8 => v8
             | zR9 => v9
             | zR10 => v10
             | zR11 => v11
             | zR12 => v12
             | zR13 => v13
             | zR14 => v14
             | zR15 => v15) =
            v11) ∧
         (∀v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15.
            (case zR12 of
               RAX => v0
             | RCX => v1
             | RDX => v2
             | RBX => v3
             | RSP => v4
             | RBP => v5
             | RSI => v6
             | RDI => v7
             | zR8 => v8
             | zR9 => v9
             | zR10 => v10
             | zR11 => v11
             | zR12 => v12
             | zR13 => v13
             | zR14 => v14
             | zR15 => v15) =
            v12) ∧
         (∀v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15.
            (case zR13 of
               RAX => v0
             | RCX => v1
             | RDX => v2
             | RBX => v3
             | RSP => v4
             | RBP => v5
             | RSI => v6
             | RDI => v7
             | zR8 => v8
             | zR9 => v9
             | zR10 => v10
             | zR11 => v11
             | zR12 => v12
             | zR13 => v13
             | zR14 => v14
             | zR15 => v15) =
            v13) ∧
         (∀v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15.
            (case zR14 of
               RAX => v0
             | RCX => v1
             | RDX => v2
             | RBX => v3
             | RSP => v4
             | RBP => v5
             | RSI => v6
             | RDI => v7
             | zR8 => v8
             | zR9 => v9
             | zR10 => v10
             | zR11 => v11
             | zR12 => v12
             | zR13 => v13
             | zR14 => v14
             | zR15 => v15) =
            v14) ∧
         ∀v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15.
           (case zR15 of
              RAX => v0
            | RCX => v1
            | RDX => v2
            | RBX => v3
            | RSP => v4
            | RBP => v5
            | RSI => v6
            | RDI => v7
            | zR8 => v8
            | zR9 => v9
            | zR10 => v10
            | zR11 => v11
            | zR12 => v12
            | zR13 => v13
            | zR14 => v14
            | zR15 => v15) =
           v15

   [Zreg_induction]  Theorem

      |- ∀P.
           P RAX ∧ P RBP ∧ P RBX ∧ P RCX ∧ P RDI ∧ P RDX ∧ P RSI ∧ P RSP ∧
           P zR10 ∧ P zR11 ∧ P zR12 ∧ P zR13 ∧ P zR14 ∧ P zR15 ∧ P zR8 ∧
           P zR9 ⇒
           ∀a. P a

   [Zreg_nchotomy]  Theorem

      |- ∀a.
           (a = RAX) ∨ (a = RCX) ∨ (a = RDX) ∨ (a = RBX) ∨ (a = RSP) ∨
           (a = RBP) ∨ (a = RSI) ∨ (a = RDI) ∨ (a = zR8) ∨ (a = zR9) ∨
           (a = zR10) ∨ (a = zR11) ∨ (a = zR12) ∨ (a = zR13) ∨ (a = zR14) ∨
           (a = zR15)

   [Zrm_11]  Theorem

      |- (∀a a'. (Zm a = Zm a') ⇔ (a = a')) ∧
         ∀a a'. (Zr a = Zr a') ⇔ (a = a')

   [Zrm_Axiom]  Theorem

      |- ∀f0 f1. ∃fn. (∀a. fn (Zm a) = f0 a) ∧ ∀a. fn (Zr a) = f1 a

   [Zrm_case_cong]  Theorem

      |- ∀M M' f f1.
           (M = M') ∧ (∀a. (M' = Zm a) ⇒ (f a = f' a)) ∧
           (∀a. (M' = Zr a) ⇒ (f1 a = f1' a)) ⇒
           (Zrm_CASE M f f1 = Zrm_CASE M' f' f1')

   [Zrm_distinct]  Theorem

      |- ∀a' a. Zm a ≠ Zr a'

   [Zrm_induction]  Theorem

      |- ∀P. (∀p. P (Zm p)) ∧ (∀Z. P (Zr Z)) ⇒ ∀Z. P Z

   [Zrm_nchotomy]  Theorem

      |- ∀ZZ. (∃p. ZZ = Zm p) ∨ ∃Z. ZZ = Zr Z

   [Zsize_11]  Theorem

      |- ∀a a'. (Z8 a = Z8 a') ⇔ (a ⇔ a')

   [Zsize_Axiom]  Theorem

      |- ∀f0 f1 f2 f3.
           ∃fn.
             (fn Z16 = f0) ∧ (fn Z32 = f1) ∧ (fn Z64 = f2) ∧
             ∀a. fn (Z8 a) = f3 a

   [Zsize_case_cong]  Theorem

      |- ∀M M' v v1 v2 f.
           (M = M') ∧ ((M' = Z16) ⇒ (v = v')) ∧ ((M' = Z32) ⇒ (v1 = v1')) ∧
           ((M' = Z64) ⇒ (v2 = v2')) ∧ (∀a. (M' = Z8 a) ⇒ (f a = f' a)) ⇒
           (Zsize_CASE M v v1 v2 f = Zsize_CASE M' v' v1' v2' f')

   [Zsize_distinct]  Theorem

      |- Z16 ≠ Z32 ∧ Z16 ≠ Z64 ∧ (∀a. Z16 ≠ Z8 a) ∧ Z32 ≠ Z64 ∧
         (∀a. Z32 ≠ Z8 a) ∧ ∀a. Z64 ≠ Z8 a

   [Zsize_induction]  Theorem

      |- ∀P. P Z16 ∧ P Z32 ∧ P Z64 ∧ (∀b. P (Z8 b)) ⇒ ∀Z. P Z

   [Zsize_nchotomy]  Theorem

      |- ∀ZZ. (ZZ = Z16) ∨ (ZZ = Z32) ∨ (ZZ = Z64) ∨ ∃b. ZZ = Z8 b

   [bitify8boolify8]  Theorem

      |- ∀w. bitify8 (boolify8 w) = w

   [boolify8_n2w]  Theorem

      |- ∀n.
           boolify8 (n2w n) =
           (let n1 = DIV2 n in
            let n2 = DIV2 n1 in
            let n3 = DIV2 n2 in
            let n4 = DIV2 n3 in
            let n5 = DIV2 n4 in
            let n6 = DIV2 n5 in
            let n7 = DIV2 n6
            in
              (ODD n7,ODD n6,ODD n5,ODD n4,ODD n3,ODD n2,ODD n1,ODD n))

   [boolify8_v2w]  Theorem

      |- ∀b7 b6 b5 b4 b3 b2 b1 b0.
           boolify8 (v2w [b7; b6; b5; b4; b3; b2; b1; b0]) =
           (b7,b6,b5,b4,b3,b2,b1,b0)

   [boolify8bitify8]  Theorem

      |- ∀x. boolify8 (bitify8 x) = x

   [datatype_REX]  Theorem

      |- DATATYPE (record REX B R W X)

   [datatype_Zbase]  Theorem

      |- DATATYPE (Zbase ZnoBase ZregBase ZripBase)

   [datatype_Zbinop_name]  Theorem

      |- DATATYPE
           (Zbinop_name Zadd Zor Zadc Zsbb Zand Zsub Zxor Zcmp Zrol Zror
              Zrcl Zrcr Zshl Zshr Ztest Zsar)

   [datatype_Zcond]  Theorem

      |- DATATYPE
           (Zcond Z_O Z_NO Z_B Z_NB Z_E Z_NE Z_NA Z_A Z_S Z_NS Z_P Z_NP Z_L
              Z_NL Z_NG Z_G Z_ALWAYS)

   [datatype_Zdest_src]  Theorem

      |- DATATYPE (Zdest_src Zr_rm Zrm_i Zrm_r)

   [datatype_Zea]  Theorem

      |- DATATYPE (Zea Zea_i Zea_m Zea_r)

   [datatype_Zeflags]  Theorem

      |- DATATYPE (Zeflags Z_CF Z_PF Z_AF Z_ZF Z_SF Z_OF)

   [datatype_Zimm_rm]  Theorem

      |- DATATYPE (Zimm_rm Zimm Zrm)

   [datatype_Zinst]  Theorem

      |- DATATYPE (Zinst Zdec_fail Zfull_inst)

   [datatype_Zmonop_name]  Theorem

      |- DATATYPE (Zmonop_name Zdec Zinc Znot Zneg)

   [datatype_Zreg]  Theorem

      |- DATATYPE
           (Zreg RAX RCX RDX RBX RSP RBP RSI RDI zR8 zR9 zR10 zR11 zR12
              zR13 zR14 zR15)

   [datatype_Zrm]  Theorem

      |- DATATYPE (Zrm Zm Zr)

   [datatype_Zsize]  Theorem

      |- DATATYPE (Zsize Z16 Z32 Z64 Z8)

   [datatype_exception]  Theorem

      |- DATATYPE (exception BadFlagAccess BadMemAccess FAIL NoException)

   [datatype_instruction]  Theorem

      |- DATATYPE
           (instruction Zbinop Zcall Zcmpxchg Zcpuid Zdiv Zjcc Zjmp Zlea
              Zloop Zmonop Zmov Zmovzx Zmul Znop Zpop Zpush Zret Zxadd
              Zxchg)

   [datatype_x64_state]  Theorem

      |- DATATYPE (record x64_state EFLAGS ICACHE MEM REG RIP exception)

   [exception_11]  Theorem

      |- (∀a a'. (BadFlagAccess a = BadFlagAccess a') ⇔ (a = a')) ∧
         (∀a a'. (BadMemAccess a = BadMemAccess a') ⇔ (a = a')) ∧
         ∀a a'. (FAIL a = FAIL a') ⇔ (a = a')

   [exception_Axiom]  Theorem

      |- ∀f0 f1 f2 f3.
           ∃fn.
             (∀a. fn (BadFlagAccess a) = f0 a) ∧
             (∀a. fn (BadMemAccess a) = f1 a) ∧ (∀a. fn (FAIL a) = f2 a) ∧
             (fn NoException = f3)

   [exception_case_cong]  Theorem

      |- ∀M M' f f1 f2 v.
           (M = M') ∧ (∀a. (M' = BadFlagAccess a) ⇒ (f a = f' a)) ∧
           (∀a. (M' = BadMemAccess a) ⇒ (f1 a = f1' a)) ∧
           (∀a. (M' = FAIL a) ⇒ (f2 a = f2' a)) ∧
           ((M' = NoException) ⇒ (v = v')) ⇒
           (exception_CASE M f f1 f2 v = exception_CASE M' f' f1' f2' v')

   [exception_distinct]  Theorem

      |- (∀a' a. BadFlagAccess a ≠ BadMemAccess a') ∧
         (∀a' a. BadFlagAccess a ≠ FAIL a') ∧
         (∀a. BadFlagAccess a ≠ NoException) ∧
         (∀a' a. BadMemAccess a ≠ FAIL a') ∧
         (∀a. BadMemAccess a ≠ NoException) ∧ ∀a. FAIL a ≠ NoException

   [exception_induction]  Theorem

      |- ∀P.
           (∀s. P (BadFlagAccess s)) ∧ (∀c. P (BadMemAccess c)) ∧
           (∀s. P (FAIL s)) ∧ P NoException ⇒
           ∀e. P e

   [exception_nchotomy]  Theorem

      |- ∀ee.
           (∃s. ee = BadFlagAccess s) ∨ (∃c. ee = BadMemAccess c) ∨
           (∃s. ee = FAIL s) ∨ (ee = NoException)

   [instruction_11]  Theorem

      |- (∀a a'. (Zbinop a = Zbinop a') ⇔ (a = a')) ∧
         (∀a a'. (Zcall a = Zcall a') ⇔ (a = a')) ∧
         (∀a a'. (Zcmpxchg a = Zcmpxchg a') ⇔ (a = a')) ∧
         (∀a a'. (Zdiv a = Zdiv a') ⇔ (a = a')) ∧
         (∀a a'. (Zjcc a = Zjcc a') ⇔ (a = a')) ∧
         (∀a a'. (Zjmp a = Zjmp a') ⇔ (a = a')) ∧
         (∀a a'. (Zlea a = Zlea a') ⇔ (a = a')) ∧
         (∀a a'. (Zloop a = Zloop a') ⇔ (a = a')) ∧
         (∀a a'. (Zmonop a = Zmonop a') ⇔ (a = a')) ∧
         (∀a a'. (Zmov a = Zmov a') ⇔ (a = a')) ∧
         (∀a a'. (Zmovzx a = Zmovzx a') ⇔ (a = a')) ∧
         (∀a a'. (Zmul a = Zmul a') ⇔ (a = a')) ∧
         (∀a a'. (Zpop a = Zpop a') ⇔ (a = a')) ∧
         (∀a a'. (Zpush a = Zpush a') ⇔ (a = a')) ∧
         (∀a a'. (Zret a = Zret a') ⇔ (a = a')) ∧
         (∀a a'. (Zxadd a = Zxadd a') ⇔ (a = a')) ∧
         ∀a a'. (Zxchg a = Zxchg a') ⇔ (a = a')

   [instruction_Axiom]  Theorem

      |- ∀f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17
            f18.
           ∃fn.
             (∀a. fn (Zbinop a) = f0 a) ∧ (∀a. fn (Zcall a) = f1 a) ∧
             (∀a. fn (Zcmpxchg a) = f2 a) ∧ (fn Zcpuid = f3) ∧
             (∀a. fn (Zdiv a) = f4 a) ∧ (∀a. fn (Zjcc a) = f5 a) ∧
             (∀a. fn (Zjmp a) = f6 a) ∧ (∀a. fn (Zlea a) = f7 a) ∧
             (∀a. fn (Zloop a) = f8 a) ∧ (∀a. fn (Zmonop a) = f9 a) ∧
             (∀a. fn (Zmov a) = f10 a) ∧ (∀a. fn (Zmovzx a) = f11 a) ∧
             (∀a. fn (Zmul a) = f12 a) ∧ (fn Znop = f13) ∧
             (∀a. fn (Zpop a) = f14 a) ∧ (∀a. fn (Zpush a) = f15 a) ∧
             (∀a. fn (Zret a) = f16 a) ∧ (∀a. fn (Zxadd a) = f17 a) ∧
             ∀a. fn (Zxchg a) = f18 a

   [instruction_case_cong]  Theorem

      |- ∀M M' f f1 f2 v f3 f4 f5 f6 f7 f8 f9 f10 f11 v1 f12 f13 f14 f15
            f16.
           (M = M') ∧ (∀a. (M' = Zbinop a) ⇒ (f a = f' a)) ∧
           (∀a. (M' = Zcall a) ⇒ (f1 a = f1' a)) ∧
           (∀a. (M' = Zcmpxchg a) ⇒ (f2 a = f2' a)) ∧
           ((M' = Zcpuid) ⇒ (v = v')) ∧
           (∀a. (M' = Zdiv a) ⇒ (f3 a = f3' a)) ∧
           (∀a. (M' = Zjcc a) ⇒ (f4 a = f4' a)) ∧
           (∀a. (M' = Zjmp a) ⇒ (f5 a = f5' a)) ∧
           (∀a. (M' = Zlea a) ⇒ (f6 a = f6' a)) ∧
           (∀a. (M' = Zloop a) ⇒ (f7 a = f7' a)) ∧
           (∀a. (M' = Zmonop a) ⇒ (f8 a = f8' a)) ∧
           (∀a. (M' = Zmov a) ⇒ (f9 a = f9' a)) ∧
           (∀a. (M' = Zmovzx a) ⇒ (f10 a = f10' a)) ∧
           (∀a. (M' = Zmul a) ⇒ (f11 a = f11' a)) ∧
           ((M' = Znop) ⇒ (v1 = v1')) ∧
           (∀a. (M' = Zpop a) ⇒ (f12 a = f12' a)) ∧
           (∀a. (M' = Zpush a) ⇒ (f13 a = f13' a)) ∧
           (∀a. (M' = Zret a) ⇒ (f14 a = f14' a)) ∧
           (∀a. (M' = Zxadd a) ⇒ (f15 a = f15' a)) ∧
           (∀a. (M' = Zxchg a) ⇒ (f16 a = f16' a)) ⇒
           (instruction_CASE M f f1 f2 v f3 f4 f5 f6 f7 f8 f9 f10 f11 v1
              f12 f13 f14 f15 f16 =
            instruction_CASE M' f' f1' f2' v' f3' f4' f5' f6' f7' f8' f9'
              f10' f11' v1' f12' f13' f14' f15' f16')

   [instruction_distinct]  Theorem

      |- (∀a' a. Zbinop a ≠ Zcall a') ∧ (∀a' a. Zbinop a ≠ Zcmpxchg a') ∧
         (∀a. Zbinop a ≠ Zcpuid) ∧ (∀a' a. Zbinop a ≠ Zdiv a') ∧
         (∀a' a. Zbinop a ≠ Zjcc a') ∧ (∀a' a. Zbinop a ≠ Zjmp a') ∧
         (∀a' a. Zbinop a ≠ Zlea a') ∧ (∀a' a. Zbinop a ≠ Zloop a') ∧
         (∀a' a. Zbinop a ≠ Zmonop a') ∧ (∀a' a. Zbinop a ≠ Zmov a') ∧
         (∀a' a. Zbinop a ≠ Zmovzx a') ∧ (∀a' a. Zbinop a ≠ Zmul a') ∧
         (∀a. Zbinop a ≠ Znop) ∧ (∀a' a. Zbinop a ≠ Zpop a') ∧
         (∀a' a. Zbinop a ≠ Zpush a') ∧ (∀a' a. Zbinop a ≠ Zret a') ∧
         (∀a' a. Zbinop a ≠ Zxadd a') ∧ (∀a' a. Zbinop a ≠ Zxchg a') ∧
         (∀a' a. Zcall a ≠ Zcmpxchg a') ∧ (∀a. Zcall a ≠ Zcpuid) ∧
         (∀a' a. Zcall a ≠ Zdiv a') ∧ (∀a' a. Zcall a ≠ Zjcc a') ∧
         (∀a' a. Zcall a ≠ Zjmp a') ∧ (∀a' a. Zcall a ≠ Zlea a') ∧
         (∀a' a. Zcall a ≠ Zloop a') ∧ (∀a' a. Zcall a ≠ Zmonop a') ∧
         (∀a' a. Zcall a ≠ Zmov a') ∧ (∀a' a. Zcall a ≠ Zmovzx a') ∧
         (∀a' a. Zcall a ≠ Zmul a') ∧ (∀a. Zcall a ≠ Znop) ∧
         (∀a' a. Zcall a ≠ Zpop a') ∧ (∀a' a. Zcall a ≠ Zpush a') ∧
         (∀a' a. Zcall a ≠ Zret a') ∧ (∀a' a. Zcall a ≠ Zxadd a') ∧
         (∀a' a. Zcall a ≠ Zxchg a') ∧ (∀a. Zcmpxchg a ≠ Zcpuid) ∧
         (∀a' a. Zcmpxchg a ≠ Zdiv a') ∧ (∀a' a. Zcmpxchg a ≠ Zjcc a') ∧
         (∀a' a. Zcmpxchg a ≠ Zjmp a') ∧ (∀a' a. Zcmpxchg a ≠ Zlea a') ∧
         (∀a' a. Zcmpxchg a ≠ Zloop a') ∧ (∀a' a. Zcmpxchg a ≠ Zmonop a') ∧
         (∀a' a. Zcmpxchg a ≠ Zmov a') ∧ (∀a' a. Zcmpxchg a ≠ Zmovzx a') ∧
         (∀a' a. Zcmpxchg a ≠ Zmul a') ∧ (∀a. Zcmpxchg a ≠ Znop) ∧
         (∀a' a. Zcmpxchg a ≠ Zpop a') ∧ (∀a' a. Zcmpxchg a ≠ Zpush a') ∧
         (∀a' a. Zcmpxchg a ≠ Zret a') ∧ (∀a' a. Zcmpxchg a ≠ Zxadd a') ∧
         (∀a' a. Zcmpxchg a ≠ Zxchg a') ∧ (∀a. Zcpuid ≠ Zdiv a) ∧
         (∀a. Zcpuid ≠ Zjcc a) ∧ (∀a. Zcpuid ≠ Zjmp a) ∧
         (∀a. Zcpuid ≠ Zlea a) ∧ (∀a. Zcpuid ≠ Zloop a) ∧
         (∀a. Zcpuid ≠ Zmonop a) ∧ (∀a. Zcpuid ≠ Zmov a) ∧
         (∀a. Zcpuid ≠ Zmovzx a) ∧ (∀a. Zcpuid ≠ Zmul a) ∧ Zcpuid ≠ Znop ∧
         (∀a. Zcpuid ≠ Zpop a) ∧ (∀a. Zcpuid ≠ Zpush a) ∧
         (∀a. Zcpuid ≠ Zret a) ∧ (∀a. Zcpuid ≠ Zxadd a) ∧
         (∀a. Zcpuid ≠ Zxchg a) ∧ (∀a' a. Zdiv a ≠ Zjcc a') ∧
         (∀a' a. Zdiv a ≠ Zjmp a') ∧ (∀a' a. Zdiv a ≠ Zlea a') ∧
         (∀a' a. Zdiv a ≠ Zloop a') ∧ (∀a' a. Zdiv a ≠ Zmonop a') ∧
         (∀a' a. Zdiv a ≠ Zmov a') ∧ (∀a' a. Zdiv a ≠ Zmovzx a') ∧
         (∀a' a. Zdiv a ≠ Zmul a') ∧ (∀a. Zdiv a ≠ Znop) ∧
         (∀a' a. Zdiv a ≠ Zpop a') ∧ (∀a' a. Zdiv a ≠ Zpush a') ∧
         (∀a' a. Zdiv a ≠ Zret a') ∧ (∀a' a. Zdiv a ≠ Zxadd a') ∧
         (∀a' a. Zdiv a ≠ Zxchg a') ∧ (∀a' a. Zjcc a ≠ Zjmp a') ∧
         (∀a' a. Zjcc a ≠ Zlea a') ∧ (∀a' a. Zjcc a ≠ Zloop a') ∧
         (∀a' a. Zjcc a ≠ Zmonop a') ∧ (∀a' a. Zjcc a ≠ Zmov a') ∧
         (∀a' a. Zjcc a ≠ Zmovzx a') ∧ (∀a' a. Zjcc a ≠ Zmul a') ∧
         (∀a. Zjcc a ≠ Znop) ∧ (∀a' a. Zjcc a ≠ Zpop a') ∧
         (∀a' a. Zjcc a ≠ Zpush a') ∧ (∀a' a. Zjcc a ≠ Zret a') ∧
         (∀a' a. Zjcc a ≠ Zxadd a') ∧ (∀a' a. Zjcc a ≠ Zxchg a') ∧
         (∀a' a. Zjmp a ≠ Zlea a') ∧ (∀a' a. Zjmp a ≠ Zloop a') ∧
         (∀a' a. Zjmp a ≠ Zmonop a') ∧ (∀a' a. Zjmp a ≠ Zmov a') ∧
         (∀a' a. Zjmp a ≠ Zmovzx a') ∧ (∀a' a. Zjmp a ≠ Zmul a') ∧
         (∀a. Zjmp a ≠ Znop) ∧ (∀a' a. Zjmp a ≠ Zpop a') ∧
         (∀a' a. Zjmp a ≠ Zpush a') ∧ (∀a' a. Zjmp a ≠ Zret a') ∧
         (∀a' a. Zjmp a ≠ Zxadd a') ∧ (∀a' a. Zjmp a ≠ Zxchg a') ∧
         (∀a' a. Zlea a ≠ Zloop a') ∧ (∀a' a. Zlea a ≠ Zmonop a') ∧
         (∀a' a. Zlea a ≠ Zmov a') ∧ (∀a' a. Zlea a ≠ Zmovzx a') ∧
         (∀a' a. Zlea a ≠ Zmul a') ∧ (∀a. Zlea a ≠ Znop) ∧
         (∀a' a. Zlea a ≠ Zpop a') ∧ (∀a' a. Zlea a ≠ Zpush a') ∧
         (∀a' a. Zlea a ≠ Zret a') ∧ (∀a' a. Zlea a ≠ Zxadd a') ∧
         (∀a' a. Zlea a ≠ Zxchg a') ∧ (∀a' a. Zloop a ≠ Zmonop a') ∧
         (∀a' a. Zloop a ≠ Zmov a') ∧ (∀a' a. Zloop a ≠ Zmovzx a') ∧
         (∀a' a. Zloop a ≠ Zmul a') ∧ (∀a. Zloop a ≠ Znop) ∧
         (∀a' a. Zloop a ≠ Zpop a') ∧ (∀a' a. Zloop a ≠ Zpush a') ∧
         (∀a' a. Zloop a ≠ Zret a') ∧ (∀a' a. Zloop a ≠ Zxadd a') ∧
         (∀a' a. Zloop a ≠ Zxchg a') ∧ (∀a' a. Zmonop a ≠ Zmov a') ∧
         (∀a' a. Zmonop a ≠ Zmovzx a') ∧ (∀a' a. Zmonop a ≠ Zmul a') ∧
         (∀a. Zmonop a ≠ Znop) ∧ (∀a' a. Zmonop a ≠ Zpop a') ∧
         (∀a' a. Zmonop a ≠ Zpush a') ∧ (∀a' a. Zmonop a ≠ Zret a') ∧
         (∀a' a. Zmonop a ≠ Zxadd a') ∧ (∀a' a. Zmonop a ≠ Zxchg a') ∧
         (∀a' a. Zmov a ≠ Zmovzx a') ∧ (∀a' a. Zmov a ≠ Zmul a') ∧
         (∀a. Zmov a ≠ Znop) ∧ (∀a' a. Zmov a ≠ Zpop a') ∧
         (∀a' a. Zmov a ≠ Zpush a') ∧ (∀a' a. Zmov a ≠ Zret a') ∧
         (∀a' a. Zmov a ≠ Zxadd a') ∧ (∀a' a. Zmov a ≠ Zxchg a') ∧
         (∀a' a. Zmovzx a ≠ Zmul a') ∧ (∀a. Zmovzx a ≠ Znop) ∧
         (∀a' a. Zmovzx a ≠ Zpop a') ∧ (∀a' a. Zmovzx a ≠ Zpush a') ∧
         (∀a' a. Zmovzx a ≠ Zret a') ∧ (∀a' a. Zmovzx a ≠ Zxadd a') ∧
         (∀a' a. Zmovzx a ≠ Zxchg a') ∧ (∀a. Zmul a ≠ Znop) ∧
         (∀a' a. Zmul a ≠ Zpop a') ∧ (∀a' a. Zmul a ≠ Zpush a') ∧
         (∀a' a. Zmul a ≠ Zret a') ∧ (∀a' a. Zmul a ≠ Zxadd a') ∧
         (∀a' a. Zmul a ≠ Zxchg a') ∧ (∀a. Znop ≠ Zpop a) ∧
         (∀a. Znop ≠ Zpush a) ∧ (∀a. Znop ≠ Zret a) ∧
         (∀a. Znop ≠ Zxadd a) ∧ (∀a. Znop ≠ Zxchg a) ∧
         (∀a' a. Zpop a ≠ Zpush a') ∧ (∀a' a. Zpop a ≠ Zret a') ∧
         (∀a' a. Zpop a ≠ Zxadd a') ∧ (∀a' a. Zpop a ≠ Zxchg a') ∧
         (∀a' a. Zpush a ≠ Zret a') ∧ (∀a' a. Zpush a ≠ Zxadd a') ∧
         (∀a' a. Zpush a ≠ Zxchg a') ∧ (∀a' a. Zret a ≠ Zxadd a') ∧
         (∀a' a. Zret a ≠ Zxchg a') ∧ ∀a' a. Zxadd a ≠ Zxchg a'

   [instruction_induction]  Theorem

      |- ∀P.
           (∀p. P (Zbinop p)) ∧ (∀Z. P (Zcall Z)) ∧ (∀p. P (Zcmpxchg p)) ∧
           P Zcpuid ∧ (∀p. P (Zdiv p)) ∧ (∀p. P (Zjcc p)) ∧
           (∀Z. P (Zjmp Z)) ∧ (∀p. P (Zlea p)) ∧ (∀p. P (Zloop p)) ∧
           (∀p. P (Zmonop p)) ∧ (∀p. P (Zmov p)) ∧ (∀p. P (Zmovzx p)) ∧
           (∀p. P (Zmul p)) ∧ P Znop ∧ (∀Z. P (Zpop Z)) ∧
           (∀Z. P (Zpush Z)) ∧ (∀c. P (Zret c)) ∧ (∀p. P (Zxadd p)) ∧
           (∀p. P (Zxchg p)) ⇒
           ∀i. P i

   [instruction_nchotomy]  Theorem

      |- ∀ii.
           (∃p. ii = Zbinop p) ∨ (∃Z. ii = Zcall Z) ∨
           (∃p. ii = Zcmpxchg p) ∨ (ii = Zcpuid) ∨ (∃p. ii = Zdiv p) ∨
           (∃p. ii = Zjcc p) ∨ (∃Z. ii = Zjmp Z) ∨ (∃p. ii = Zlea p) ∨
           (∃p. ii = Zloop p) ∨ (∃p. ii = Zmonop p) ∨ (∃p. ii = Zmov p) ∨
           (∃p. ii = Zmovzx p) ∨ (∃p. ii = Zmul p) ∨ (ii = Znop) ∨
           (∃Z. ii = Zpop Z) ∨ (∃Z. ii = Zpush Z) ∨ (∃c. ii = Zret c) ∨
           (∃p. ii = Zxadd p) ∨ ∃p. ii = Zxchg p

   [num2Zbinop_name_11]  Theorem

      |- ∀r r'.
           r < 16 ⇒
           r' < 16 ⇒
           ((num2Zbinop_name r = num2Zbinop_name r') ⇔ (r = r'))

   [num2Zbinop_name_ONTO]  Theorem

      |- ∀a. ∃r. (a = num2Zbinop_name r) ∧ r < 16

   [num2Zbinop_name_Zbinop_name2num]  Theorem

      |- ∀a. num2Zbinop_name (Zbinop_name2num a) = a

   [num2Zbinop_name_thm]  Theorem

      |- (num2Zbinop_name 0 = Zadd) ∧ (num2Zbinop_name 1 = Zor) ∧
         (num2Zbinop_name 2 = Zadc) ∧ (num2Zbinop_name 3 = Zsbb) ∧
         (num2Zbinop_name 4 = Zand) ∧ (num2Zbinop_name 5 = Zsub) ∧
         (num2Zbinop_name 6 = Zxor) ∧ (num2Zbinop_name 7 = Zcmp) ∧
         (num2Zbinop_name 8 = Zrol) ∧ (num2Zbinop_name 9 = Zror) ∧
         (num2Zbinop_name 10 = Zrcl) ∧ (num2Zbinop_name 11 = Zrcr) ∧
         (num2Zbinop_name 12 = Zshl) ∧ (num2Zbinop_name 13 = Zshr) ∧
         (num2Zbinop_name 14 = Ztest) ∧ (num2Zbinop_name 15 = Zsar)

   [num2Zcond_11]  Theorem

      |- ∀r r'.
           r < 17 ⇒ r' < 17 ⇒ ((num2Zcond r = num2Zcond r') ⇔ (r = r'))

   [num2Zcond_ONTO]  Theorem

      |- ∀a. ∃r. (a = num2Zcond r) ∧ r < 17

   [num2Zcond_Zcond2num]  Theorem

      |- ∀a. num2Zcond (Zcond2num a) = a

   [num2Zcond_thm]  Theorem

      |- (num2Zcond 0 = Z_O) ∧ (num2Zcond 1 = Z_NO) ∧ (num2Zcond 2 = Z_B) ∧
         (num2Zcond 3 = Z_NB) ∧ (num2Zcond 4 = Z_E) ∧
         (num2Zcond 5 = Z_NE) ∧ (num2Zcond 6 = Z_NA) ∧
         (num2Zcond 7 = Z_A) ∧ (num2Zcond 8 = Z_S) ∧ (num2Zcond 9 = Z_NS) ∧
         (num2Zcond 10 = Z_P) ∧ (num2Zcond 11 = Z_NP) ∧
         (num2Zcond 12 = Z_L) ∧ (num2Zcond 13 = Z_NL) ∧
         (num2Zcond 14 = Z_NG) ∧ (num2Zcond 15 = Z_G) ∧
         (num2Zcond 16 = Z_ALWAYS)

   [num2Zeflags_11]  Theorem

      |- ∀r r'.
           r < 6 ⇒ r' < 6 ⇒ ((num2Zeflags r = num2Zeflags r') ⇔ (r = r'))

   [num2Zeflags_ONTO]  Theorem

      |- ∀a. ∃r. (a = num2Zeflags r) ∧ r < 6

   [num2Zeflags_Zeflags2num]  Theorem

      |- ∀a. num2Zeflags (Zeflags2num a) = a

   [num2Zeflags_thm]  Theorem

      |- (num2Zeflags 0 = Z_CF) ∧ (num2Zeflags 1 = Z_PF) ∧
         (num2Zeflags 2 = Z_AF) ∧ (num2Zeflags 3 = Z_ZF) ∧
         (num2Zeflags 4 = Z_SF) ∧ (num2Zeflags 5 = Z_OF)

   [num2Zmonop_name_11]  Theorem

      |- ∀r r'.
           r < 4 ⇒
           r' < 4 ⇒
           ((num2Zmonop_name r = num2Zmonop_name r') ⇔ (r = r'))

   [num2Zmonop_name_ONTO]  Theorem

      |- ∀a. ∃r. (a = num2Zmonop_name r) ∧ r < 4

   [num2Zmonop_name_Zmonop_name2num]  Theorem

      |- ∀a. num2Zmonop_name (Zmonop_name2num a) = a

   [num2Zmonop_name_thm]  Theorem

      |- (num2Zmonop_name 0 = Zdec) ∧ (num2Zmonop_name 1 = Zinc) ∧
         (num2Zmonop_name 2 = Znot) ∧ (num2Zmonop_name 3 = Zneg)

   [num2Zreg_11]  Theorem

      |- ∀r r'. r < 16 ⇒ r' < 16 ⇒ ((num2Zreg r = num2Zreg r') ⇔ (r = r'))

   [num2Zreg_ONTO]  Theorem

      |- ∀a. ∃r. (a = num2Zreg r) ∧ r < 16

   [num2Zreg_Zreg2num]  Theorem

      |- ∀a. num2Zreg (Zreg2num a) = a

   [num2Zreg_thm]  Theorem

      |- (num2Zreg 0 = RAX) ∧ (num2Zreg 1 = RCX) ∧ (num2Zreg 2 = RDX) ∧
         (num2Zreg 3 = RBX) ∧ (num2Zreg 4 = RSP) ∧ (num2Zreg 5 = RBP) ∧
         (num2Zreg 6 = RSI) ∧ (num2Zreg 7 = RDI) ∧ (num2Zreg 8 = zR8) ∧
         (num2Zreg 9 = zR9) ∧ (num2Zreg 10 = zR10) ∧ (num2Zreg 11 = zR11) ∧
         (num2Zreg 12 = zR12) ∧ (num2Zreg 13 = zR13) ∧
         (num2Zreg 14 = zR14) ∧ (num2Zreg 15 = zR15)

   [readPrefix_def]  Theorem

      |- ∀strm s p.
           readPrefix (s,p,strm) =
           case strm of
             [] => SOME (p,F,ARB,strm)
           | h::strm1 =>
               (let group = prefixGroup h
                in
                  if group = 0 then SOME (p,F,rec'REX 0w,strm)
                  else if group = 5 then
                    SOME (p,T,rec'REX ((3 >< 0) h),strm1)
                  else if group ∈ s then NONE
                  else readPrefix (group INSERT s,h::p,strm1))

   [readPrefix_ind]  Theorem

      |- ∀P.
           (∀s p strm.
              (∀h strm1 group.
                 (strm = h::strm1) ∧ (group = prefixGroup h) ∧ group ≠ 0 ∧
                 group ≠ 5 ∧ group ∉ s ⇒
                 P (group INSERT s,h::p,strm1)) ⇒
              P (s,p,strm)) ⇒
           ∀v v1 v2. P (v,v1,v2)

   [x64_state_11]  Theorem

      |- ∀a0 a1 a2 a3 a4 a5 a0' a1' a2' a3' a4' a5'.
           (x64_state a0 a1 a2 a3 a4 a5 =
            x64_state a0' a1' a2' a3' a4' a5') ⇔
           (a0 = a0') ∧ (a1 = a1') ∧ (a2 = a2') ∧ (a3 = a3') ∧ (a4 = a4') ∧
           (a5 = a5')

   [x64_state_Axiom]  Theorem

      |- ∀f.
           ∃fn.
             ∀a0 a1 a2 a3 a4 a5.
               fn (x64_state a0 a1 a2 a3 a4 a5) = f a0 a1 a2 a3 a4 a5

   [x64_state_accessors]  Theorem

      |- (∀f f0 f1 f2 c e. (x64_state f f0 f1 f2 c e).EFLAGS = f) ∧
         (∀f f0 f1 f2 c e. (x64_state f f0 f1 f2 c e).ICACHE = f0) ∧
         (∀f f0 f1 f2 c e. (x64_state f f0 f1 f2 c e).MEM = f1) ∧
         (∀f f0 f1 f2 c e. (x64_state f f0 f1 f2 c e).REG = f2) ∧
         (∀f f0 f1 f2 c e. (x64_state f f0 f1 f2 c e).RIP = c) ∧
         ∀f f0 f1 f2 c e. (x64_state f f0 f1 f2 c e).exception = e

   [x64_state_accfupds]  Theorem

      |- (∀x f. (x with ICACHE updated_by f).EFLAGS = x.EFLAGS) ∧
         (∀x f. (x with MEM updated_by f).EFLAGS = x.EFLAGS) ∧
         (∀x f. (x with REG updated_by f).EFLAGS = x.EFLAGS) ∧
         (∀x f. (x with RIP updated_by f).EFLAGS = x.EFLAGS) ∧
         (∀x f. (x with exception updated_by f).EFLAGS = x.EFLAGS) ∧
         (∀x f. (x with EFLAGS updated_by f).ICACHE = x.ICACHE) ∧
         (∀x f. (x with MEM updated_by f).ICACHE = x.ICACHE) ∧
         (∀x f. (x with REG updated_by f).ICACHE = x.ICACHE) ∧
         (∀x f. (x with RIP updated_by f).ICACHE = x.ICACHE) ∧
         (∀x f. (x with exception updated_by f).ICACHE = x.ICACHE) ∧
         (∀x f. (x with EFLAGS updated_by f).MEM = x.MEM) ∧
         (∀x f. (x with ICACHE updated_by f).MEM = x.MEM) ∧
         (∀x f. (x with REG updated_by f).MEM = x.MEM) ∧
         (∀x f. (x with RIP updated_by f).MEM = x.MEM) ∧
         (∀x f. (x with exception updated_by f).MEM = x.MEM) ∧
         (∀x f. (x with EFLAGS updated_by f).REG = x.REG) ∧
         (∀x f. (x with ICACHE updated_by f).REG = x.REG) ∧
         (∀x f. (x with MEM updated_by f).REG = x.REG) ∧
         (∀x f. (x with RIP updated_by f).REG = x.REG) ∧
         (∀x f. (x with exception updated_by f).REG = x.REG) ∧
         (∀x f. (x with EFLAGS updated_by f).RIP = x.RIP) ∧
         (∀x f. (x with ICACHE updated_by f).RIP = x.RIP) ∧
         (∀x f. (x with MEM updated_by f).RIP = x.RIP) ∧
         (∀x f. (x with REG updated_by f).RIP = x.RIP) ∧
         (∀x f. (x with exception updated_by f).RIP = x.RIP) ∧
         (∀x f. (x with EFLAGS updated_by f).exception = x.exception) ∧
         (∀x f. (x with ICACHE updated_by f).exception = x.exception) ∧
         (∀x f. (x with MEM updated_by f).exception = x.exception) ∧
         (∀x f. (x with REG updated_by f).exception = x.exception) ∧
         (∀x f. (x with RIP updated_by f).exception = x.exception) ∧
         (∀x f. (x with EFLAGS updated_by f).EFLAGS = f x.EFLAGS) ∧
         (∀x f. (x with ICACHE updated_by f).ICACHE = f x.ICACHE) ∧
         (∀x f. (x with MEM updated_by f).MEM = f x.MEM) ∧
         (∀x f. (x with REG updated_by f).REG = f x.REG) ∧
         (∀x f. (x with RIP updated_by f).RIP = f x.RIP) ∧
         ∀x f. (x with exception updated_by f).exception = f x.exception

   [x64_state_case_cong]  Theorem

      |- ∀M M' f.
           (M = M') ∧
           (∀a0 a1 a2 a3 a4 a5.
              (M' = x64_state a0 a1 a2 a3 a4 a5) ⇒
              (f a0 a1 a2 a3 a4 a5 = f' a0 a1 a2 a3 a4 a5)) ⇒
           (x64_state_CASE M f = x64_state_CASE M' f')

   [x64_state_component_equality]  Theorem

      |- ∀x1 x2.
           (x1 = x2) ⇔
           (x1.EFLAGS = x2.EFLAGS) ∧ (x1.ICACHE = x2.ICACHE) ∧
           (x1.MEM = x2.MEM) ∧ (x1.REG = x2.REG) ∧ (x1.RIP = x2.RIP) ∧
           (x1.exception = x2.exception)

   [x64_state_fn_updates]  Theorem

      |- (∀f3 f f0 f1 f2 c e.
            x64_state f f0 f1 f2 c e with EFLAGS updated_by f3 =
            x64_state (f3 f) f0 f1 f2 c e) ∧
         (∀f3 f f0 f1 f2 c e.
            x64_state f f0 f1 f2 c e with ICACHE updated_by f3 =
            x64_state f (f3 f0) f1 f2 c e) ∧
         (∀f3 f f0 f1 f2 c e.
            x64_state f f0 f1 f2 c e with MEM updated_by f3 =
            x64_state f f0 (f3 f1) f2 c e) ∧
         (∀f3 f f0 f1 f2 c e.
            x64_state f f0 f1 f2 c e with REG updated_by f3 =
            x64_state f f0 f1 (f3 f2) c e) ∧
         (∀f3 f f0 f1 f2 c e.
            x64_state f f0 f1 f2 c e with RIP updated_by f3 =
            x64_state f f0 f1 f2 (f3 c) e) ∧
         ∀f3 f f0 f1 f2 c e.
           x64_state f f0 f1 f2 c e with exception updated_by f3 =
           x64_state f f0 f1 f2 c (f3 e)

   [x64_state_fupdcanon]  Theorem

      |- (∀x g f.
            x with <|ICACHE updated_by f; EFLAGS updated_by g|> =
            x with <|EFLAGS updated_by g; ICACHE updated_by f|>) ∧
         (∀x g f.
            x with <|MEM updated_by f; EFLAGS updated_by g|> =
            x with <|EFLAGS updated_by g; MEM updated_by f|>) ∧
         (∀x g f.
            x with <|MEM updated_by f; ICACHE updated_by g|> =
            x with <|ICACHE updated_by g; MEM updated_by f|>) ∧
         (∀x g f.
            x with <|REG updated_by f; EFLAGS updated_by g|> =
            x with <|EFLAGS updated_by g; REG updated_by f|>) ∧
         (∀x g f.
            x with <|REG updated_by f; ICACHE updated_by g|> =
            x with <|ICACHE updated_by g; REG updated_by f|>) ∧
         (∀x g f.
            x with <|REG updated_by f; MEM updated_by g|> =
            x with <|MEM updated_by g; REG updated_by f|>) ∧
         (∀x g f.
            x with <|RIP updated_by f; EFLAGS updated_by g|> =
            x with <|EFLAGS updated_by g; RIP updated_by f|>) ∧
         (∀x g f.
            x with <|RIP updated_by f; ICACHE updated_by g|> =
            x with <|ICACHE updated_by g; RIP updated_by f|>) ∧
         (∀x g f.
            x with <|RIP updated_by f; MEM updated_by g|> =
            x with <|MEM updated_by g; RIP updated_by f|>) ∧
         (∀x g f.
            x with <|RIP updated_by f; REG updated_by g|> =
            x with <|REG updated_by g; RIP updated_by f|>) ∧
         (∀x g f.
            x with <|exception updated_by f; EFLAGS updated_by g|> =
            x with <|EFLAGS updated_by g; exception updated_by f|>) ∧
         (∀x g f.
            x with <|exception updated_by f; ICACHE updated_by g|> =
            x with <|ICACHE updated_by g; exception updated_by f|>) ∧
         (∀x g f.
            x with <|exception updated_by f; MEM updated_by g|> =
            x with <|MEM updated_by g; exception updated_by f|>) ∧
         (∀x g f.
            x with <|exception updated_by f; REG updated_by g|> =
            x with <|REG updated_by g; exception updated_by f|>) ∧
         ∀x g f.
           x with <|exception updated_by f; RIP updated_by g|> =
           x with <|RIP updated_by g; exception updated_by f|>

   [x64_state_fupdcanon_comp]  Theorem

      |- ((∀g f.
              _ record fupdateICACHE f o  _ record fupdateEFLAGS g =
              _ record fupdateEFLAGS g o  _ record fupdateICACHE f) ∧
          ∀h g f.
             _ record fupdateICACHE f o  _ record fupdateEFLAGS g o h =
             _ record fupdateEFLAGS g o  _ record fupdateICACHE f o h) ∧
         ((∀g f.
              _ record fupdateMEM f o  _ record fupdateEFLAGS g =
              _ record fupdateEFLAGS g o  _ record fupdateMEM f) ∧
          ∀h g f.
             _ record fupdateMEM f o  _ record fupdateEFLAGS g o h =
             _ record fupdateEFLAGS g o  _ record fupdateMEM f o h) ∧
         ((∀g f.
              _ record fupdateMEM f o  _ record fupdateICACHE g =
              _ record fupdateICACHE g o  _ record fupdateMEM f) ∧
          ∀h g f.
             _ record fupdateMEM f o  _ record fupdateICACHE g o h =
             _ record fupdateICACHE g o  _ record fupdateMEM f o h) ∧
         ((∀g f.
              _ record fupdateREG f o  _ record fupdateEFLAGS g =
              _ record fupdateEFLAGS g o  _ record fupdateREG f) ∧
          ∀h g f.
             _ record fupdateREG f o  _ record fupdateEFLAGS g o h =
             _ record fupdateEFLAGS g o  _ record fupdateREG f o h) ∧
         ((∀g f.
              _ record fupdateREG f o  _ record fupdateICACHE g =
              _ record fupdateICACHE g o  _ record fupdateREG f) ∧
          ∀h g f.
             _ record fupdateREG f o  _ record fupdateICACHE g o h =
             _ record fupdateICACHE g o  _ record fupdateREG f o h) ∧
         ((∀g f.
              _ record fupdateREG f o  _ record fupdateMEM g =
              _ record fupdateMEM g o  _ record fupdateREG f) ∧
          ∀h g f.
             _ record fupdateREG f o  _ record fupdateMEM g o h =
             _ record fupdateMEM g o  _ record fupdateREG f o h) ∧
         ((∀g f.
              _ record fupdateRIP f o  _ record fupdateEFLAGS g =
              _ record fupdateEFLAGS g o  _ record fupdateRIP f) ∧
          ∀h g f.
             _ record fupdateRIP f o  _ record fupdateEFLAGS g o h =
             _ record fupdateEFLAGS g o  _ record fupdateRIP f o h) ∧
         ((∀g f.
              _ record fupdateRIP f o  _ record fupdateICACHE g =
              _ record fupdateICACHE g o  _ record fupdateRIP f) ∧
          ∀h g f.
             _ record fupdateRIP f o  _ record fupdateICACHE g o h =
             _ record fupdateICACHE g o  _ record fupdateRIP f o h) ∧
         ((∀g f.
              _ record fupdateRIP f o  _ record fupdateMEM g =
              _ record fupdateMEM g o  _ record fupdateRIP f) ∧
          ∀h g f.
             _ record fupdateRIP f o  _ record fupdateMEM g o h =
             _ record fupdateMEM g o  _ record fupdateRIP f o h) ∧
         ((∀g f.
              _ record fupdateRIP f o  _ record fupdateREG g =
              _ record fupdateREG g o  _ record fupdateRIP f) ∧
          ∀h g f.
             _ record fupdateRIP f o  _ record fupdateREG g o h =
             _ record fupdateREG g o  _ record fupdateRIP f o h) ∧
         ((∀g f.
              _ record fupdateexception f o  _ record fupdateEFLAGS g =
              _ record fupdateEFLAGS g o  _ record fupdateexception f) ∧
          ∀h g f.
             _ record fupdateexception f o  _ record fupdateEFLAGS g o h =
             _ record fupdateEFLAGS g o  _ record fupdateexception f o h) ∧
         ((∀g f.
              _ record fupdateexception f o  _ record fupdateICACHE g =
              _ record fupdateICACHE g o  _ record fupdateexception f) ∧
          ∀h g f.
             _ record fupdateexception f o  _ record fupdateICACHE g o h =
             _ record fupdateICACHE g o  _ record fupdateexception f o h) ∧
         ((∀g f.
              _ record fupdateexception f o  _ record fupdateMEM g =
              _ record fupdateMEM g o  _ record fupdateexception f) ∧
          ∀h g f.
             _ record fupdateexception f o  _ record fupdateMEM g o h =
             _ record fupdateMEM g o  _ record fupdateexception f o h) ∧
         ((∀g f.
              _ record fupdateexception f o  _ record fupdateREG g =
              _ record fupdateREG g o  _ record fupdateexception f) ∧
          ∀h g f.
             _ record fupdateexception f o  _ record fupdateREG g o h =
             _ record fupdateREG g o  _ record fupdateexception f o h) ∧
         (∀g f.
             _ record fupdateexception f o  _ record fupdateRIP g =
             _ record fupdateRIP g o  _ record fupdateexception f) ∧
         ∀h g f.
            _ record fupdateexception f o  _ record fupdateRIP g o h =
            _ record fupdateRIP g o  _ record fupdateexception f o h

   [x64_state_fupdfupds]  Theorem

      |- (∀x g f.
            x with <|EFLAGS updated_by f; EFLAGS updated_by g|> =
            x with EFLAGS updated_by f o g) ∧
         (∀x g f.
            x with <|ICACHE updated_by f; ICACHE updated_by g|> =
            x with ICACHE updated_by f o g) ∧
         (∀x g f.
            x with <|MEM updated_by f; MEM updated_by g|> =
            x with MEM updated_by f o g) ∧
         (∀x g f.
            x with <|REG updated_by f; REG updated_by g|> =
            x with REG updated_by f o g) ∧
         (∀x g f.
            x with <|RIP updated_by f; RIP updated_by g|> =
            x with RIP updated_by f o g) ∧
         ∀x g f.
           x with <|exception updated_by f; exception updated_by g|> =
           x with exception updated_by f o g

   [x64_state_fupdfupds_comp]  Theorem

      |- ((∀g f.
              _ record fupdateEFLAGS f o  _ record fupdateEFLAGS g =
              _ record fupdateEFLAGS (f o g)) ∧
          ∀h g f.
             _ record fupdateEFLAGS f o  _ record fupdateEFLAGS g o h =
             _ record fupdateEFLAGS (f o g) o h) ∧
         ((∀g f.
              _ record fupdateICACHE f o  _ record fupdateICACHE g =
              _ record fupdateICACHE (f o g)) ∧
          ∀h g f.
             _ record fupdateICACHE f o  _ record fupdateICACHE g o h =
             _ record fupdateICACHE (f o g) o h) ∧
         ((∀g f.
              _ record fupdateMEM f o  _ record fupdateMEM g =
              _ record fupdateMEM (f o g)) ∧
          ∀h g f.
             _ record fupdateMEM f o  _ record fupdateMEM g o h =
             _ record fupdateMEM (f o g) o h) ∧
         ((∀g f.
              _ record fupdateREG f o  _ record fupdateREG g =
              _ record fupdateREG (f o g)) ∧
          ∀h g f.
             _ record fupdateREG f o  _ record fupdateREG g o h =
             _ record fupdateREG (f o g) o h) ∧
         ((∀g f.
              _ record fupdateRIP f o  _ record fupdateRIP g =
              _ record fupdateRIP (f o g)) ∧
          ∀h g f.
             _ record fupdateRIP f o  _ record fupdateRIP g o h =
             _ record fupdateRIP (f o g) o h) ∧
         (∀g f.
             _ record fupdateexception f o  _ record fupdateexception g =
             _ record fupdateexception (f o g)) ∧
         ∀h g f.
            _ record fupdateexception f o  _ record fupdateexception g o
           h =
            _ record fupdateexception (f o g) o h

   [x64_state_induction]  Theorem

      |- ∀P. (∀f f0 f1 f2 c e. P (x64_state f f0 f1 f2 c e)) ⇒ ∀x. P x

   [x64_state_literal_11]  Theorem

      |- ∀f21 f11 f01 f1 c1 e1 f22 f12 f02 f2 c2 e2.
           (<|EFLAGS := f21; ICACHE := f11; MEM := f01; REG := f1;
              RIP := c1; exception := e1|> =
            <|EFLAGS := f22; ICACHE := f12; MEM := f02; REG := f2;
              RIP := c2; exception := e2|>) ⇔
           (f21 = f22) ∧ (f11 = f12) ∧ (f01 = f02) ∧ (f1 = f2) ∧
           (c1 = c2) ∧ (e1 = e2)

   [x64_state_literal_nchotomy]  Theorem

      |- ∀x.
           ∃f2 f1 f0 f c e.
             x =
             <|EFLAGS := f2; ICACHE := f1; MEM := f0; REG := f; RIP := c;
               exception := e|>

   [x64_state_nchotomy]  Theorem

      |- ∀xx. ∃f f0 f1 f2 c e. xx = x64_state f f0 f1 f2 c e

   [x64_state_updates_eq_literal]  Theorem

      |- ∀x f2 f1 f0 f c e.
           x with
           <|EFLAGS := f2; ICACHE := f1; MEM := f0; REG := f; RIP := c;
             exception := e|> =
           <|EFLAGS := f2; ICACHE := f1; MEM := f0; REG := f; RIP := c;
             exception := e|>


*)
end
