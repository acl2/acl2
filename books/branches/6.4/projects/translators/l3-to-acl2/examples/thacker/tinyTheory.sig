signature tinyTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val ALU_def : thm
    val Decode_def : thm
    val Encode_def : thm
    val LoadIM_curried_def : thm
    val LoadIM_tupled_primitive_def : thm
    val Next_def : thm
    val Run_def : thm
    val bitify32_def : thm
    val boolify32_def : thm
    val conditionT_BIJ : thm
    val conditionT_CASE : thm
    val conditionT_TY_DEF : thm
    val conditionT_size_def : thm
    val dfn'In_def : thm
    val dfn'Jump_def : thm
    val dfn'LoadConstant_def : thm
    val dfn'LoadDM_def : thm
    val dfn'Normal_def : thm
    val dfn'Out_def : thm
    val dfn'ReservedInstr_def : thm
    val dfn'StoreDM_def : thm
    val dfn'StoreIM_def : thm
    val enc_def : thm
    val exception_BIJ : thm
    val exception_CASE : thm
    val exception_TY_DEF : thm
    val exception_size_def : thm
    val funcT_BIJ : thm
    val funcT_CASE : thm
    val funcT_TY_DEF : thm
    val funcT_size_def : thm
    val function_def : thm
    val incPC_def : thm
    val initialize_def : thm
    val instruction_TY_DEF : thm
    val instruction_case_def : thm
    val instruction_size_def : thm
    val norm_def : thm
    val raise'exception_def : thm
    val shiftT_BIJ : thm
    val shiftT_CASE : thm
    val shiftT_TY_DEF : thm
    val shiftT_size_def : thm
    val shifter_def : thm
    val test_prog_def : thm
    val tiny_state_DM : thm
    val tiny_state_DM_fupd : thm
    val tiny_state_IM : thm
    val tiny_state_IM_fupd : thm
    val tiny_state_InData : thm
    val tiny_state_InData_fupd : thm
    val tiny_state_InRdy : thm
    val tiny_state_InRdy_fupd : thm
    val tiny_state_OutStrobe : thm
    val tiny_state_OutStrobe_fupd : thm
    val tiny_state_PC : thm
    val tiny_state_PC_fupd : thm
    val tiny_state_R : thm
    val tiny_state_R_fupd : thm
    val tiny_state_TY_DEF : thm
    val tiny_state_case_def : thm
    val tiny_state_exception : thm
    val tiny_state_exception_fupd : thm
    val tiny_state_size_def : thm

  (*  Theorems  *)
    val EXISTS_tiny_state : thm
    val FORALL_tiny_state : thm
    val LoadIM_def : thm
    val LoadIM_ind : thm
    val bitify32boolify32 : thm
    val boolify32_n2w : thm
    val boolify32_v2w : thm
    val boolify32bitify32 : thm
    val conditionT2num_11 : thm
    val conditionT2num_ONTO : thm
    val conditionT2num_num2conditionT : thm
    val conditionT2num_thm : thm
    val conditionT_Axiom : thm
    val conditionT_EQ_conditionT : thm
    val conditionT_case_cong : thm
    val conditionT_case_def : thm
    val conditionT_distinct : thm
    val conditionT_induction : thm
    val conditionT_nchotomy : thm
    val datatype_conditionT : thm
    val datatype_exception : thm
    val datatype_funcT : thm
    val datatype_instruction : thm
    val datatype_shiftT : thm
    val datatype_tiny_state : thm
    val exception2num_11 : thm
    val exception2num_ONTO : thm
    val exception2num_num2exception : thm
    val exception2num_thm : thm
    val exception_Axiom : thm
    val exception_EQ_exception : thm
    val exception_case_cong : thm
    val exception_case_def : thm
    val exception_distinct : thm
    val exception_induction : thm
    val exception_nchotomy : thm
    val funcT2num_11 : thm
    val funcT2num_ONTO : thm
    val funcT2num_num2funcT : thm
    val funcT2num_thm : thm
    val funcT_Axiom : thm
    val funcT_EQ_funcT : thm
    val funcT_case_cong : thm
    val funcT_case_def : thm
    val funcT_distinct : thm
    val funcT_induction : thm
    val funcT_nchotomy : thm
    val instruction_11 : thm
    val instruction_Axiom : thm
    val instruction_case_cong : thm
    val instruction_distinct : thm
    val instruction_induction : thm
    val instruction_nchotomy : thm
    val num2conditionT_11 : thm
    val num2conditionT_ONTO : thm
    val num2conditionT_conditionT2num : thm
    val num2conditionT_thm : thm
    val num2exception_11 : thm
    val num2exception_ONTO : thm
    val num2exception_exception2num : thm
    val num2exception_thm : thm
    val num2funcT_11 : thm
    val num2funcT_ONTO : thm
    val num2funcT_funcT2num : thm
    val num2funcT_thm : thm
    val num2shiftT_11 : thm
    val num2shiftT_ONTO : thm
    val num2shiftT_shiftT2num : thm
    val num2shiftT_thm : thm
    val shiftT2num_11 : thm
    val shiftT2num_ONTO : thm
    val shiftT2num_num2shiftT : thm
    val shiftT2num_thm : thm
    val shiftT_Axiom : thm
    val shiftT_EQ_shiftT : thm
    val shiftT_case_cong : thm
    val shiftT_case_def : thm
    val shiftT_distinct : thm
    val shiftT_induction : thm
    val shiftT_nchotomy : thm
    val tiny_state_11 : thm
    val tiny_state_Axiom : thm
    val tiny_state_accessors : thm
    val tiny_state_accfupds : thm
    val tiny_state_case_cong : thm
    val tiny_state_component_equality : thm
    val tiny_state_fn_updates : thm
    val tiny_state_fupdcanon : thm
    val tiny_state_fupdcanon_comp : thm
    val tiny_state_fupdfupds : thm
    val tiny_state_fupdfupds_comp : thm
    val tiny_state_induction : thm
    val tiny_state_literal_11 : thm
    val tiny_state_literal_nchotomy : thm
    val tiny_state_nchotomy : thm
    val tiny_state_updates_eq_literal : thm

  val tiny_grammars : type_grammar.grammar * term_grammar.grammar

  val inventory: {Thy: string, T: string list, C: string list, N: int list}
(*
   [bitstring] Parent theory of "tiny"

   [integer_word] Parent theory of "tiny"

   [machine_ieee] Parent theory of "tiny"

   [state_transformer] Parent theory of "tiny"

   [ALU_def]  Definition

      |- ∀func shift a b.
           ALU (func,shift,a,b) =
           (λstate.
              (let (v,s) = function (func,a,b) state
               in
                 (shifter (shift,v),s)))

   [Decode_def]  Definition

      |- ∀opc.
           Decode opc =
           (let (b'31,b'30,b'29,b'28,b'27,b'26,b'25,b'24,b'23,b'22,b'21,
                 b'20,b'19,b'18,b'17,b'16,b'15,b'14,b'13,b'12,b'11,b'10,
                 b'9,b'8,b'7,b'6,b'5,b'4,b'3,b'2,b'1,b'0) = boolify32 opc
            in
              if b'24 then LoadConstant ((31 >< 25) opc,(23 >< 0) opc)
              else
                (let Rw = (31 >< 25) opc in
                 let Rb = (16 >< 10) opc in
                 let Ra = (23 >< 17) opc in
                 let func = num2funcT (w2n ((9 >< 7) opc)) in
                 let shift = num2shiftT (w2n ((6 >< 5) opc)) in
                 let skip = num2conditionT (w2n ((4 >< 3) opc))
                 in
                   case (2 >< 0) opc of
                     0w => Normal (func,shift,skip,Rw,Ra,Rb)
                   | 1w => StoreDM (func,shift,skip,Rw,Ra,Rb)
                   | 2w => StoreIM (func,shift,skip,Rw,Ra,Rb)
                   | 3w => Out (func,shift,skip,Rw,Ra,Rb)
                   | 4w => LoadDM (func,shift,skip,Rw,Ra,Rb)
                   | 5w => In (func,shift,skip,Rw,Ra,Rb)
                   | 6w => Jump (func,shift,Rw,Ra,Rb)
                   | 7w => ReservedInstr
                   | v => ARB))

   [Encode_def]  Definition

      |- ∀i.
           Encode i =
           case i of
             In args_5 => enc (args_5,5w)
           | Jump (func,shift,Rw_1,Ra,Rb) =>
               enc ((func,shift,skipNever,Rw_1,Ra,Rb),6w)
           | LoadConstant (Rw,imm) => Rw @@ 1w @@ imm
           | LoadDM args_4 => enc (args_4,4w)
           | Normal args => enc (args,0w)
           | Out args_3 => enc (args_3,3w)
           | ReservedInstr => 7w
           | StoreDM args_1 => enc (args_1,1w)
           | StoreIM args_2 => enc (args_2,2w)

   [LoadIM_curried_def]  Definition

      |- ∀x x1. LoadIM x x1 = LoadIM_tupled (x,x1)

   [LoadIM_tupled_primitive_def]  Definition

      |- LoadIM_tupled =
         WFREC
           (@R.
              WF R ∧
              ∀state a i h t.
                (i = h::t) ⇒
                R ((a + 1w,t),state with IM := (a =+ Encode h) state.IM)
                  ((a,i),state))
           (λLoadIM_tupled a'.
              case a' of
                ((a,i),state) =>
                  I
                    (case i of
                       [] => ((),state)
                     | h::t =>
                         LoadIM_tupled
                           ((a + 1w,t),
                            state with IM := (a =+ Encode h) state.IM)))

   [Next_def]  Definition

      |- ∀state.
           Next state =
           (let v = Decode (state.IM state.PC)
            in
              if v ≠ ReservedInstr then Run v state else ((),state))

   [Run_def]  Definition

      |- ∀v0.
           Run v0 =
           (λstate.
              case v0 of
                In v1 => dfn'In v1 state
              | Jump v2 => dfn'Jump v2 state
              | LoadConstant v3 => dfn'LoadConstant v3 state
              | LoadDM v4 => dfn'LoadDM v4 state
              | Normal v5 => dfn'Normal v5 state
              | Out v6 => dfn'Out v6 state
              | ReservedInstr => dfn'ReservedInstr state
              | StoreDM v7 => dfn'StoreDM v7 state
              | StoreIM v8 => dfn'StoreIM v8 state)

   [bitify32_def]  Definition

      |- ∀b31 b30 b29 b28 b27 b26 b25 b24 b23 b22 b21 b20 b19 b18 b17 b16
            b15 b14 b13 b12 b11 b10 b9 b8 b7 b6 b5 b4 b3 b2 b1 b0.
           bitify32
             (b31,b30,b29,b28,b27,b26,b25,b24,b23,b22,b21,b20,b19,b18,b17,
              b16,b15,b14,b13,b12,b11,b10,b9,b8,b7,b6,b5,b4,b3,b2,b1,b0) =
           v2w
             [b31; b30; b29; b28; b27; b26; b25; b24; b23; b22; b21; b20;
              b19; b18; b17; b16; b15; b14; b13; b12; b11; b10; b9; b8; b7;
              b6; b5; b4; b3; b2; b1; b0]

   [boolify32_def]  Definition

      |- ∀w.
           boolify32 w =
           (word_bit 31 w,word_bit 30 w,word_bit 29 w,word_bit 28 w,
            word_bit 27 w,word_bit 26 w,word_bit 25 w,word_bit 24 w,
            word_bit 23 w,word_bit 22 w,word_bit 21 w,word_bit 20 w,
            word_bit 19 w,word_bit 18 w,word_bit 17 w,word_bit 16 w,
            word_bit 15 w,word_bit 14 w,word_bit 13 w,word_bit 12 w,
            word_bit 11 w,word_bit 10 w,word_bit 9 w,word_bit 8 w,
            word_bit 7 w,word_bit 6 w,word_bit 5 w,word_bit 4 w,
            word_bit 3 w,word_bit 2 w,word_bit 1 w,word_bit 0 w)

   [conditionT_BIJ]  Definition

      |- (∀a. num2conditionT (conditionT2num a) = a) ∧
         ∀r. (λn. n < 4) r ⇔ (conditionT2num (num2conditionT r) = r)

   [conditionT_CASE]  Definition

      |- ∀x v0 v1 v2 v3.
           (case x of
              skipNever => v0
            | skipNeg => v1
            | skipZero => v2
            | skipInRdy => v3) =
           (λm.
              if m < 1 then v0
              else if m < 2 then v1
              else if m = 2 then v2
              else v3) (conditionT2num x)

   [conditionT_TY_DEF]  Definition

      |- ∃rep. TYPE_DEFINITION (λn. n < 4) rep

   [conditionT_size_def]  Definition

      |- ∀x. conditionT_size x = 0

   [dfn'In_def]  Definition

      |- ∀func shift skip w a b.
           dfn'In (func,shift,skip,w,a,b) =
           (λstate.
              norm (func,shift,skip,F,F,w,a,b)
                (state with R := (w =+ state.InData) state.R))

   [dfn'Jump_def]  Definition

      |- ∀func shift w a b.
           dfn'Jump (func,shift,w,a,b) =
           (λstate.
              (let s = state with R := (w =+ w2w (state.PC + 1w)) state.R
               in
               let (v,s) =
                     (let (v,s) = ALU (func,shift,s.R a,s.R b) s
                      in
                        (w2w v,s))
               in
                 ((),s with PC := v)))

   [dfn'LoadConstant_def]  Definition

      |- ∀w imm.
           dfn'LoadConstant (w,imm) =
           (λstate.
              (let s = state with R := (w =+ w2w imm) state.R
               in
                 ((),s with PC := s.PC + 1w)))

   [dfn'LoadDM_def]  Definition

      |- ∀func shift skip w a b.
           dfn'LoadDM (func,shift,skip,w,a,b) =
           (λstate.
              norm (func,shift,skip,F,F,w,a,b)
                (state with
                 R := (w =+ state.DM (w2w (state.R b))) state.R))

   [dfn'Normal_def]  Definition

      |- ∀func shift skip w a b.
           dfn'Normal (func,shift,skip,w,a,b) =
           (λstate. norm (func,shift,skip,T,F,w,a,b) state)

   [dfn'Out_def]  Definition

      |- ∀func shift skip w a b.
           dfn'Out (func,shift,skip,w,a,b) =
           (λstate. norm (func,shift,skip,T,T,w,a,b) state)

   [dfn'ReservedInstr_def]  Definition

      |- ∀state. dfn'ReservedInstr state = raise'exception Reserved state

   [dfn'StoreDM_def]  Definition

      |- ∀func shift skip w a b.
           dfn'StoreDM (func,shift,skip,w,a,b) =
           (λstate.
              norm (func,shift,skip,T,F,w,a,b)
                (state with DM := (w2w (state.R b) =+ state.R a) state.DM))

   [dfn'StoreIM_def]  Definition

      |- ∀func shift skip w a b.
           dfn'StoreIM (func,shift,skip,w,a,b) =
           (λstate.
              norm (func,shift,skip,T,F,w,a,b)
                (state with IM := (w2w (state.R b) =+ state.R a) state.IM))

   [enc_def]  Definition

      |- ∀args opc.
           enc (args,opc) =
           (let (func,shift,skip,w,a,b) = args
            in
              w @@ 0w @@ a @@ b @@ n2w (funcT2num func) @@
              n2w (shiftT2num shift) @@ n2w (conditionT2num skip) @@ opc)

   [exception_BIJ]  Definition

      |- (∀a. num2exception (exception2num a) = a) ∧
         ∀r. (λn. n < 2) r ⇔ (exception2num (num2exception r) = r)

   [exception_CASE]  Definition

      |- ∀x v0 v1.
           (case x of NoException => v0 | Reserved => v1) =
           (λm. if m = 0 then v0 else v1) (exception2num x)

   [exception_TY_DEF]  Definition

      |- ∃rep. TYPE_DEFINITION (λn. n < 2) rep

   [exception_size_def]  Definition

      |- ∀x. exception_size x = 0

   [funcT_BIJ]  Definition

      |- (∀a. num2funcT (funcT2num a) = a) ∧
         ∀r. (λn. n < 8) r ⇔ (funcT2num (num2funcT r) = r)

   [funcT_CASE]  Definition

      |- ∀x v0 v1 v2 v3 v4 v5 v6 v7.
           (case x of
              fADD => v0
            | fSUB => v1
            | fINC => v2
            | fDEC => v3
            | fAND => v4
            | fOR => v5
            | fXOR => v6
            | fReserved => v7) =
           (λm.
              if m < 3 then if m < 1 then v0 else if m = 1 then v1 else v2
              else if m < 5 then if m = 3 then v3 else v4
              else if m < 6 then v5
              else if m = 6 then v6
              else v7) (funcT2num x)

   [funcT_TY_DEF]  Definition

      |- ∃rep. TYPE_DEFINITION (λn. n < 8) rep

   [funcT_size_def]  Definition

      |- ∀x. funcT_size x = 0

   [function_def]  Definition

      |- ∀func a b.
           function (func,a,b) =
           (λstate.
              case func of
                fADD => (a + b,state)
              | fSUB => (a − b,state)
              | fINC => (b + 1w,state)
              | fDEC => (b − 1w,state)
              | fAND => (a && b,state)
              | fOR => (a ‖ b,state)
              | fXOR => (a ⊕ b,state)
              | fReserved => raise'exception Reserved state)

   [incPC_def]  Definition

      |- ∀skip alu.
           incPC (skip,alu) =
           (λstate.
              case skip of
                skipNever => ((),state with PC := state.PC + 1w)
              | skipNeg =>
                  ((),
                   state with PC := state.PC + if alu < 0w then 2w else 1w)
              | skipZero =>
                  ((),
                   state with PC := state.PC + if alu = 0w then 2w else 1w)
              | skipInRdy =>
                  ((),
                   state with
                   PC := state.PC + if state.InRdy then 2w else 1w))

   [initialize_def]  Definition

      |- ∀p.
           initialize p =
           (λstate.
              LoadIM (0w,p)
                (state with
                 <|IM := K (Encode ReservedInstr); OutStrobe := 0w;
                   InData := 0w; InRdy := F; DM := K 0w; R := K 0w;
                   PC := 0w|>))

   [instruction_TY_DEF]  Definition

      |- ∃rep.
           TYPE_DEFINITION
             (λa0.
                ∀'instruction' .
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
                             (λn. ind_type$BOTTOM)) a) ∨
                     (∃a.
                        a0 =
                        (λa.
                           ind_type$CONSTR (SUC (SUC (SUC 0))) (a,ARB,ARB)
                             (λn. ind_type$BOTTOM)) a) ∨
                     (∃a.
                        a0 =
                        (λa.
                           ind_type$CONSTR (SUC (SUC (SUC (SUC 0))))
                             (a,ARB,ARB) (λn. ind_type$BOTTOM)) a) ∨
                     (∃a.
                        a0 =
                        (λa.
                           ind_type$CONSTR (SUC (SUC (SUC (SUC (SUC 0)))))
                             (a,ARB,ARB) (λn. ind_type$BOTTOM)) a) ∨
                     (a0 =
                      ind_type$CONSTR (SUC (SUC (SUC (SUC (SUC (SUC 0))))))
                        (ARB,ARB,ARB) (λn. ind_type$BOTTOM)) ∨
                     (∃a.
                        a0 =
                        (λa.
                           ind_type$CONSTR
                             (SUC (SUC (SUC (SUC (SUC (SUC (SUC 0)))))))
                             (a,ARB,ARB) (λn. ind_type$BOTTOM)) a) ∨
                     (∃a.
                        a0 =
                        (λa.
                           ind_type$CONSTR
                             (SUC
                                (SUC
                                   (SUC (SUC (SUC (SUC (SUC (SUC 0))))))))
                             (a,ARB,ARB) (λn. ind_type$BOTTOM)) a) ⇒
                     'instruction' a0) ⇒
                  'instruction' a0) rep

   [instruction_case_def]  Definition

      |- (∀a f f1 f2 f3 f4 f5 v f6 f7.
            instruction_CASE (In a) f f1 f2 f3 f4 f5 v f6 f7 = f a) ∧
         (∀a f f1 f2 f3 f4 f5 v f6 f7.
            instruction_CASE (Jump a) f f1 f2 f3 f4 f5 v f6 f7 = f1 a) ∧
         (∀a f f1 f2 f3 f4 f5 v f6 f7.
            instruction_CASE (LoadConstant a) f f1 f2 f3 f4 f5 v f6 f7 =
            f2 a) ∧
         (∀a f f1 f2 f3 f4 f5 v f6 f7.
            instruction_CASE (LoadDM a) f f1 f2 f3 f4 f5 v f6 f7 = f3 a) ∧
         (∀a f f1 f2 f3 f4 f5 v f6 f7.
            instruction_CASE (Normal a) f f1 f2 f3 f4 f5 v f6 f7 = f4 a) ∧
         (∀a f f1 f2 f3 f4 f5 v f6 f7.
            instruction_CASE (Out a) f f1 f2 f3 f4 f5 v f6 f7 = f5 a) ∧
         (∀f f1 f2 f3 f4 f5 v f6 f7.
            instruction_CASE ReservedInstr f f1 f2 f3 f4 f5 v f6 f7 = v) ∧
         (∀a f f1 f2 f3 f4 f5 v f6 f7.
            instruction_CASE (StoreDM a) f f1 f2 f3 f4 f5 v f6 f7 = f6 a) ∧
         ∀a f f1 f2 f3 f4 f5 v f6 f7.
           instruction_CASE (StoreIM a) f f1 f2 f3 f4 f5 v f6 f7 = f7 a

   [instruction_size_def]  Definition

      |- (∀a.
            instruction_size (In a) =
            1 +
            pair_size funcT_size
              (pair_size shiftT_size
                 (pair_size conditionT_size
                    (pair_size (λv. 0) (pair_size (λv. 0) (λv. 0))))) a) ∧
         (∀a.
            instruction_size (Jump a) =
            1 +
            pair_size funcT_size
              (pair_size shiftT_size
                 (pair_size (λv. 0) (pair_size (λv. 0) (λv. 0)))) a) ∧
         (∀a.
            instruction_size (LoadConstant a) =
            1 + pair_size (λv. 0) (λv. 0) a) ∧
         (∀a.
            instruction_size (LoadDM a) =
            1 +
            pair_size funcT_size
              (pair_size shiftT_size
                 (pair_size conditionT_size
                    (pair_size (λv. 0) (pair_size (λv. 0) (λv. 0))))) a) ∧
         (∀a.
            instruction_size (Normal a) =
            1 +
            pair_size funcT_size
              (pair_size shiftT_size
                 (pair_size conditionT_size
                    (pair_size (λv. 0) (pair_size (λv. 0) (λv. 0))))) a) ∧
         (∀a.
            instruction_size (Out a) =
            1 +
            pair_size funcT_size
              (pair_size shiftT_size
                 (pair_size conditionT_size
                    (pair_size (λv. 0) (pair_size (λv. 0) (λv. 0))))) a) ∧
         (instruction_size ReservedInstr = 0) ∧
         (∀a.
            instruction_size (StoreDM a) =
            1 +
            pair_size funcT_size
              (pair_size shiftT_size
                 (pair_size conditionT_size
                    (pair_size (λv. 0) (pair_size (λv. 0) (λv. 0))))) a) ∧
         ∀a.
           instruction_size (StoreIM a) =
           1 +
           pair_size funcT_size
             (pair_size shiftT_size
                (pair_size conditionT_size
                   (pair_size (λv. 0) (pair_size (λv. 0) (λv. 0))))) a

   [norm_def]  Definition

      |- ∀func shift skip wback strobe w a b.
           norm (func,shift,skip,wback,strobe,w,a,b) =
           (λstate.
              (let (v,s) = ALU (func,shift,state.R a,state.R b) state in
               let s = if wback then s with R := (w =+ v) s.R else s
               in
                 incPC (skip,v)
                   (if strobe then s with OutStrobe := v else s)))

   [raise'exception_def]  Definition

      |- ∀e.
           raise'exception e =
           (λstate.
              (ARB,
               if state.exception = NoException then
                 state with exception := e
               else state))

   [shiftT_BIJ]  Definition

      |- (∀a. num2shiftT (shiftT2num a) = a) ∧
         ∀r. (λn. n < 4) r ⇔ (shiftT2num (num2shiftT r) = r)

   [shiftT_CASE]  Definition

      |- ∀x v0 v1 v2 v3.
           (case x of
              noShift => v0
            | RCY1 => v1
            | RCY8 => v2
            | RCY16 => v3) =
           (λm.
              if m < 1 then v0
              else if m < 2 then v1
              else if m = 2 then v2
              else v3) (shiftT2num x)

   [shiftT_TY_DEF]  Definition

      |- ∃rep. TYPE_DEFINITION (λn. n < 4) rep

   [shiftT_size_def]  Definition

      |- ∀x. shiftT_size x = 0

   [shifter_def]  Definition

      |- ∀shift a.
           shifter (shift,a) =
           case shift of
             noShift => a
           | RCY1 => a ⇄ 1
           | RCY8 => a ⇄ 8
           | RCY16 => a ⇄ 16

   [test_prog_def]  Definition

      |- test_prog =
         [LoadConstant (0w,0w); LoadConstant (1w,1000w);
          LoadConstant (2w,1010w); LoadConstant (3w,4w);
          StoreDM (fINC,noShift,skipNever,1w,1w,1w);
          Normal (fXOR,noShift,skipZero,4w,1w,2w);
          Jump (fADD,noShift,4w,3w,0w);
          Out (fADD,noShift,skipNever,1w,1w,0w)]

   [tiny_state_DM]  Definition

      |- ∀f f0 c b c0 c1 f1 e. (tiny_state f f0 c b c0 c1 f1 e).DM = f

   [tiny_state_DM_fupd]  Definition

      |- ∀f2 f f0 c b c0 c1 f1 e.
           tiny_state f f0 c b c0 c1 f1 e with DM updated_by f2 =
           tiny_state (f2 f) f0 c b c0 c1 f1 e

   [tiny_state_IM]  Definition

      |- ∀f f0 c b c0 c1 f1 e. (tiny_state f f0 c b c0 c1 f1 e).IM = f0

   [tiny_state_IM_fupd]  Definition

      |- ∀f2 f f0 c b c0 c1 f1 e.
           tiny_state f f0 c b c0 c1 f1 e with IM updated_by f2 =
           tiny_state f (f2 f0) c b c0 c1 f1 e

   [tiny_state_InData]  Definition

      |- ∀f f0 c b c0 c1 f1 e. (tiny_state f f0 c b c0 c1 f1 e).InData = c

   [tiny_state_InData_fupd]  Definition

      |- ∀f2 f f0 c b c0 c1 f1 e.
           tiny_state f f0 c b c0 c1 f1 e with InData updated_by f2 =
           tiny_state f f0 (f2 c) b c0 c1 f1 e

   [tiny_state_InRdy]  Definition

      |- ∀f f0 c b c0 c1 f1 e. (tiny_state f f0 c b c0 c1 f1 e).InRdy ⇔ b

   [tiny_state_InRdy_fupd]  Definition

      |- ∀f2 f f0 c b c0 c1 f1 e.
           tiny_state f f0 c b c0 c1 f1 e with InRdy updated_by f2 =
           tiny_state f f0 c (f2 b) c0 c1 f1 e

   [tiny_state_OutStrobe]  Definition

      |- ∀f f0 c b c0 c1 f1 e.
           (tiny_state f f0 c b c0 c1 f1 e).OutStrobe = c0

   [tiny_state_OutStrobe_fupd]  Definition

      |- ∀f2 f f0 c b c0 c1 f1 e.
           tiny_state f f0 c b c0 c1 f1 e with OutStrobe updated_by f2 =
           tiny_state f f0 c b (f2 c0) c1 f1 e

   [tiny_state_PC]  Definition

      |- ∀f f0 c b c0 c1 f1 e. (tiny_state f f0 c b c0 c1 f1 e).PC = c1

   [tiny_state_PC_fupd]  Definition

      |- ∀f2 f f0 c b c0 c1 f1 e.
           tiny_state f f0 c b c0 c1 f1 e with PC updated_by f2 =
           tiny_state f f0 c b c0 (f2 c1) f1 e

   [tiny_state_R]  Definition

      |- ∀f f0 c b c0 c1 f1 e. (tiny_state f f0 c b c0 c1 f1 e).R = f1

   [tiny_state_R_fupd]  Definition

      |- ∀f2 f f0 c b c0 c1 f1 e.
           tiny_state f f0 c b c0 c1 f1 e with R updated_by f2 =
           tiny_state f f0 c b c0 c1 (f2 f1) e

   [tiny_state_TY_DEF]  Definition

      |- ∃rep.
           TYPE_DEFINITION
             (λa0'.
                ∀'tiny_state' .
                  (∀a0'.
                     (∃a0 a1 a2 a3 a4 a5 a6 a7.
                        a0' =
                        (λa0 a1 a2 a3 a4 a5 a6 a7.
                           ind_type$CONSTR 0 (a0,a1,a2,a3,a4,a5,a6,a7)
                             (λn. ind_type$BOTTOM)) a0 a1 a2 a3 a4 a5 a6
                          a7) ⇒
                     'tiny_state' a0') ⇒
                  'tiny_state' a0') rep

   [tiny_state_case_def]  Definition

      |- ∀a0 a1 a2 a3 a4 a5 a6 a7 f.
           tiny_state_CASE (tiny_state a0 a1 a2 a3 a4 a5 a6 a7) f =
           f a0 a1 a2 a3 a4 a5 a6 a7

   [tiny_state_exception]  Definition

      |- ∀f f0 c b c0 c1 f1 e.
           (tiny_state f f0 c b c0 c1 f1 e).exception = e

   [tiny_state_exception_fupd]  Definition

      |- ∀f2 f f0 c b c0 c1 f1 e.
           tiny_state f f0 c b c0 c1 f1 e with exception updated_by f2 =
           tiny_state f f0 c b c0 c1 f1 (f2 e)

   [tiny_state_size_def]  Definition

      |- ∀a0 a1 a2 a3 a4 a5 a6 a7.
           tiny_state_size (tiny_state a0 a1 a2 a3 a4 a5 a6 a7) =
           1 + (bool_size a3 + exception_size a7)

   [EXISTS_tiny_state]  Theorem

      |- ∀P.
           (∃t. P t) ⇔
           ∃f1 f0 c1 b c0 c f e.
             P
               <|DM := f1; IM := f0; InData := c1; InRdy := b;
                 OutStrobe := c0; PC := c; R := f; exception := e|>

   [FORALL_tiny_state]  Theorem

      |- ∀P.
           (∀t. P t) ⇔
           ∀f1 f0 c1 b c0 c f e.
             P
               <|DM := f1; IM := f0; InData := c1; InRdy := b;
                 OutStrobe := c0; PC := c; R := f; exception := e|>

   [LoadIM_def]  Theorem

      |- ∀state i a.
           LoadIM (a,i) state =
           case i of
             [] => ((),state)
           | h::t =>
               LoadIM (a + 1w,t)
                 (state with IM := (a =+ Encode h) state.IM)

   [LoadIM_ind]  Theorem

      |- ∀P.
           (∀a i state.
              (∀h t.
                 (i = h::t) ⇒
                 P (a + 1w,t)
                   (state with IM := (a =+ Encode h) state.IM)) ⇒
              P (a,i) state) ⇒
           ∀v v1 v2. P (v,v1) v2

   [bitify32boolify32]  Theorem

      |- ∀w. bitify32 (boolify32 w) = w

   [boolify32_n2w]  Theorem

      |- ∀n.
           boolify32 (n2w n) =
           (let n1 = DIV2 n in
            let n2 = DIV2 n1 in
            let n3 = DIV2 n2 in
            let n4 = DIV2 n3 in
            let n5 = DIV2 n4 in
            let n6 = DIV2 n5 in
            let n7 = DIV2 n6 in
            let n8 = DIV2 n7 in
            let n9 = DIV2 n8 in
            let n10 = DIV2 n9 in
            let n11 = DIV2 n10 in
            let n12 = DIV2 n11 in
            let n13 = DIV2 n12 in
            let n14 = DIV2 n13 in
            let n15 = DIV2 n14 in
            let n16 = DIV2 n15 in
            let n17 = DIV2 n16 in
            let n18 = DIV2 n17 in
            let n19 = DIV2 n18 in
            let n20 = DIV2 n19 in
            let n21 = DIV2 n20 in
            let n22 = DIV2 n21 in
            let n23 = DIV2 n22 in
            let n24 = DIV2 n23 in
            let n25 = DIV2 n24 in
            let n26 = DIV2 n25 in
            let n27 = DIV2 n26 in
            let n28 = DIV2 n27 in
            let n29 = DIV2 n28 in
            let n30 = DIV2 n29 in
            let n31 = DIV2 n30
            in
              (ODD n31,ODD n30,ODD n29,ODD n28,ODD n27,ODD n26,ODD n25,
               ODD n24,ODD n23,ODD n22,ODD n21,ODD n20,ODD n19,ODD n18,
               ODD n17,ODD n16,ODD n15,ODD n14,ODD n13,ODD n12,ODD n11,
               ODD n10,ODD n9,ODD n8,ODD n7,ODD n6,ODD n5,ODD n4,ODD n3,
               ODD n2,ODD n1,ODD n))

   [boolify32_v2w]  Theorem

      |- ∀b31 b30 b29 b28 b27 b26 b25 b24 b23 b22 b21 b20 b19 b18 b17 b16
            b15 b14 b13 b12 b11 b10 b9 b8 b7 b6 b5 b4 b3 b2 b1 b0.
           boolify32
             (v2w
                [b31; b30; b29; b28; b27; b26; b25; b24; b23; b22; b21;
                 b20; b19; b18; b17; b16; b15; b14; b13; b12; b11; b10; b9;
                 b8; b7; b6; b5; b4; b3; b2; b1; b0]) =
           (b31,b30,b29,b28,b27,b26,b25,b24,b23,b22,b21,b20,b19,b18,b17,
            b16,b15,b14,b13,b12,b11,b10,b9,b8,b7,b6,b5,b4,b3,b2,b1,b0)

   [boolify32bitify32]  Theorem

      |- ∀x. boolify32 (bitify32 x) = x

   [conditionT2num_11]  Theorem

      |- ∀a a'. (conditionT2num a = conditionT2num a') ⇔ (a = a')

   [conditionT2num_ONTO]  Theorem

      |- ∀r. r < 4 ⇔ ∃a. r = conditionT2num a

   [conditionT2num_num2conditionT]  Theorem

      |- ∀r. r < 4 ⇔ (conditionT2num (num2conditionT r) = r)

   [conditionT2num_thm]  Theorem

      |- (conditionT2num skipNever = 0) ∧ (conditionT2num skipNeg = 1) ∧
         (conditionT2num skipZero = 2) ∧ (conditionT2num skipInRdy = 3)

   [conditionT_Axiom]  Theorem

      |- ∀x0 x1 x2 x3.
           ∃f.
             (f skipNever = x0) ∧ (f skipNeg = x1) ∧ (f skipZero = x2) ∧
             (f skipInRdy = x3)

   [conditionT_EQ_conditionT]  Theorem

      |- ∀a a'. (a = a') ⇔ (conditionT2num a = conditionT2num a')

   [conditionT_case_cong]  Theorem

      |- ∀M M' v0 v1 v2 v3.
           (M = M') ∧ ((M' = skipNever) ⇒ (v0 = v0')) ∧
           ((M' = skipNeg) ⇒ (v1 = v1')) ∧ ((M' = skipZero) ⇒ (v2 = v2')) ∧
           ((M' = skipInRdy) ⇒ (v3 = v3')) ⇒
           ((case M of
               skipNever => v0
             | skipNeg => v1
             | skipZero => v2
             | skipInRdy => v3) =
            case M' of
              skipNever => v0'
            | skipNeg => v1'
            | skipZero => v2'
            | skipInRdy => v3')

   [conditionT_case_def]  Theorem

      |- (∀v0 v1 v2 v3.
            (case skipNever of
               skipNever => v0
             | skipNeg => v1
             | skipZero => v2
             | skipInRdy => v3) =
            v0) ∧
         (∀v0 v1 v2 v3.
            (case skipNeg of
               skipNever => v0
             | skipNeg => v1
             | skipZero => v2
             | skipInRdy => v3) =
            v1) ∧
         (∀v0 v1 v2 v3.
            (case skipZero of
               skipNever => v0
             | skipNeg => v1
             | skipZero => v2
             | skipInRdy => v3) =
            v2) ∧
         ∀v0 v1 v2 v3.
           (case skipInRdy of
              skipNever => v0
            | skipNeg => v1
            | skipZero => v2
            | skipInRdy => v3) =
           v3

   [conditionT_distinct]  Theorem

      |- skipNever ≠ skipNeg ∧ skipNever ≠ skipZero ∧
         skipNever ≠ skipInRdy ∧ skipNeg ≠ skipZero ∧ skipNeg ≠ skipInRdy ∧
         skipZero ≠ skipInRdy

   [conditionT_induction]  Theorem

      |- ∀P. P skipInRdy ∧ P skipNeg ∧ P skipNever ∧ P skipZero ⇒ ∀a. P a

   [conditionT_nchotomy]  Theorem

      |- ∀a.
           (a = skipNever) ∨ (a = skipNeg) ∨ (a = skipZero) ∨
           (a = skipInRdy)

   [datatype_conditionT]  Theorem

      |- DATATYPE (conditionT skipNever skipNeg skipZero skipInRdy)

   [datatype_exception]  Theorem

      |- DATATYPE (exception NoException Reserved)

   [datatype_funcT]  Theorem

      |- DATATYPE (funcT fADD fSUB fINC fDEC fAND fOR fXOR fReserved)

   [datatype_instruction]  Theorem

      |- DATATYPE
           (instruction In Jump LoadConstant LoadDM Normal Out
              ReservedInstr StoreDM StoreIM)

   [datatype_shiftT]  Theorem

      |- DATATYPE (shiftT noShift RCY1 RCY8 RCY16)

   [datatype_tiny_state]  Theorem

      |- DATATYPE
           (record tiny_state DM IM InData InRdy OutStrobe PC R exception)

   [exception2num_11]  Theorem

      |- ∀a a'. (exception2num a = exception2num a') ⇔ (a = a')

   [exception2num_ONTO]  Theorem

      |- ∀r. r < 2 ⇔ ∃a. r = exception2num a

   [exception2num_num2exception]  Theorem

      |- ∀r. r < 2 ⇔ (exception2num (num2exception r) = r)

   [exception2num_thm]  Theorem

      |- (exception2num NoException = 0) ∧ (exception2num Reserved = 1)

   [exception_Axiom]  Theorem

      |- ∀x0 x1. ∃f. (f NoException = x0) ∧ (f Reserved = x1)

   [exception_EQ_exception]  Theorem

      |- ∀a a'. (a = a') ⇔ (exception2num a = exception2num a')

   [exception_case_cong]  Theorem

      |- ∀M M' v0 v1.
           (M = M') ∧ ((M' = NoException) ⇒ (v0 = v0')) ∧
           ((M' = Reserved) ⇒ (v1 = v1')) ⇒
           ((case M of NoException => v0 | Reserved => v1) =
            case M' of NoException => v0' | Reserved => v1')

   [exception_case_def]  Theorem

      |- (∀v0 v1.
            (case NoException of NoException => v0 | Reserved => v1) =
            v0) ∧
         ∀v0 v1. (case Reserved of NoException => v0 | Reserved => v1) = v1

   [exception_distinct]  Theorem

      |- NoException ≠ Reserved

   [exception_induction]  Theorem

      |- ∀P. P NoException ∧ P Reserved ⇒ ∀a. P a

   [exception_nchotomy]  Theorem

      |- ∀a. (a = NoException) ∨ (a = Reserved)

   [funcT2num_11]  Theorem

      |- ∀a a'. (funcT2num a = funcT2num a') ⇔ (a = a')

   [funcT2num_ONTO]  Theorem

      |- ∀r. r < 8 ⇔ ∃a. r = funcT2num a

   [funcT2num_num2funcT]  Theorem

      |- ∀r. r < 8 ⇔ (funcT2num (num2funcT r) = r)

   [funcT2num_thm]  Theorem

      |- (funcT2num fADD = 0) ∧ (funcT2num fSUB = 1) ∧
         (funcT2num fINC = 2) ∧ (funcT2num fDEC = 3) ∧
         (funcT2num fAND = 4) ∧ (funcT2num fOR = 5) ∧
         (funcT2num fXOR = 6) ∧ (funcT2num fReserved = 7)

   [funcT_Axiom]  Theorem

      |- ∀x0 x1 x2 x3 x4 x5 x6 x7.
           ∃f.
             (f fADD = x0) ∧ (f fSUB = x1) ∧ (f fINC = x2) ∧
             (f fDEC = x3) ∧ (f fAND = x4) ∧ (f fOR = x5) ∧ (f fXOR = x6) ∧
             (f fReserved = x7)

   [funcT_EQ_funcT]  Theorem

      |- ∀a a'. (a = a') ⇔ (funcT2num a = funcT2num a')

   [funcT_case_cong]  Theorem

      |- ∀M M' v0 v1 v2 v3 v4 v5 v6 v7.
           (M = M') ∧ ((M' = fADD) ⇒ (v0 = v0')) ∧
           ((M' = fSUB) ⇒ (v1 = v1')) ∧ ((M' = fINC) ⇒ (v2 = v2')) ∧
           ((M' = fDEC) ⇒ (v3 = v3')) ∧ ((M' = fAND) ⇒ (v4 = v4')) ∧
           ((M' = fOR) ⇒ (v5 = v5')) ∧ ((M' = fXOR) ⇒ (v6 = v6')) ∧
           ((M' = fReserved) ⇒ (v7 = v7')) ⇒
           ((case M of
               fADD => v0
             | fSUB => v1
             | fINC => v2
             | fDEC => v3
             | fAND => v4
             | fOR => v5
             | fXOR => v6
             | fReserved => v7) =
            case M' of
              fADD => v0'
            | fSUB => v1'
            | fINC => v2'
            | fDEC => v3'
            | fAND => v4'
            | fOR => v5'
            | fXOR => v6'
            | fReserved => v7')

   [funcT_case_def]  Theorem

      |- (∀v0 v1 v2 v3 v4 v5 v6 v7.
            (case fADD of
               fADD => v0
             | fSUB => v1
             | fINC => v2
             | fDEC => v3
             | fAND => v4
             | fOR => v5
             | fXOR => v6
             | fReserved => v7) =
            v0) ∧
         (∀v0 v1 v2 v3 v4 v5 v6 v7.
            (case fSUB of
               fADD => v0
             | fSUB => v1
             | fINC => v2
             | fDEC => v3
             | fAND => v4
             | fOR => v5
             | fXOR => v6
             | fReserved => v7) =
            v1) ∧
         (∀v0 v1 v2 v3 v4 v5 v6 v7.
            (case fINC of
               fADD => v0
             | fSUB => v1
             | fINC => v2
             | fDEC => v3
             | fAND => v4
             | fOR => v5
             | fXOR => v6
             | fReserved => v7) =
            v2) ∧
         (∀v0 v1 v2 v3 v4 v5 v6 v7.
            (case fDEC of
               fADD => v0
             | fSUB => v1
             | fINC => v2
             | fDEC => v3
             | fAND => v4
             | fOR => v5
             | fXOR => v6
             | fReserved => v7) =
            v3) ∧
         (∀v0 v1 v2 v3 v4 v5 v6 v7.
            (case fAND of
               fADD => v0
             | fSUB => v1
             | fINC => v2
             | fDEC => v3
             | fAND => v4
             | fOR => v5
             | fXOR => v6
             | fReserved => v7) =
            v4) ∧
         (∀v0 v1 v2 v3 v4 v5 v6 v7.
            (case fOR of
               fADD => v0
             | fSUB => v1
             | fINC => v2
             | fDEC => v3
             | fAND => v4
             | fOR => v5
             | fXOR => v6
             | fReserved => v7) =
            v5) ∧
         (∀v0 v1 v2 v3 v4 v5 v6 v7.
            (case fXOR of
               fADD => v0
             | fSUB => v1
             | fINC => v2
             | fDEC => v3
             | fAND => v4
             | fOR => v5
             | fXOR => v6
             | fReserved => v7) =
            v6) ∧
         ∀v0 v1 v2 v3 v4 v5 v6 v7.
           (case fReserved of
              fADD => v0
            | fSUB => v1
            | fINC => v2
            | fDEC => v3
            | fAND => v4
            | fOR => v5
            | fXOR => v6
            | fReserved => v7) =
           v7

   [funcT_distinct]  Theorem

      |- fADD ≠ fSUB ∧ fADD ≠ fINC ∧ fADD ≠ fDEC ∧ fADD ≠ fAND ∧
         fADD ≠ fOR ∧ fADD ≠ fXOR ∧ fADD ≠ fReserved ∧ fSUB ≠ fINC ∧
         fSUB ≠ fDEC ∧ fSUB ≠ fAND ∧ fSUB ≠ fOR ∧ fSUB ≠ fXOR ∧
         fSUB ≠ fReserved ∧ fINC ≠ fDEC ∧ fINC ≠ fAND ∧ fINC ≠ fOR ∧
         fINC ≠ fXOR ∧ fINC ≠ fReserved ∧ fDEC ≠ fAND ∧ fDEC ≠ fOR ∧
         fDEC ≠ fXOR ∧ fDEC ≠ fReserved ∧ fAND ≠ fOR ∧ fAND ≠ fXOR ∧
         fAND ≠ fReserved ∧ fOR ≠ fXOR ∧ fOR ≠ fReserved ∧ fXOR ≠ fReserved

   [funcT_induction]  Theorem

      |- ∀P.
           P fADD ∧ P fAND ∧ P fDEC ∧ P fINC ∧ P fOR ∧ P fReserved ∧
           P fSUB ∧ P fXOR ⇒
           ∀a. P a

   [funcT_nchotomy]  Theorem

      |- ∀a.
           (a = fADD) ∨ (a = fSUB) ∨ (a = fINC) ∨ (a = fDEC) ∨ (a = fAND) ∨
           (a = fOR) ∨ (a = fXOR) ∨ (a = fReserved)

   [instruction_11]  Theorem

      |- (∀a a'. (In a = In a') ⇔ (a = a')) ∧
         (∀a a'. (Jump a = Jump a') ⇔ (a = a')) ∧
         (∀a a'. (LoadConstant a = LoadConstant a') ⇔ (a = a')) ∧
         (∀a a'. (LoadDM a = LoadDM a') ⇔ (a = a')) ∧
         (∀a a'. (Normal a = Normal a') ⇔ (a = a')) ∧
         (∀a a'. (Out a = Out a') ⇔ (a = a')) ∧
         (∀a a'. (StoreDM a = StoreDM a') ⇔ (a = a')) ∧
         ∀a a'. (StoreIM a = StoreIM a') ⇔ (a = a')

   [instruction_Axiom]  Theorem

      |- ∀f0 f1 f2 f3 f4 f5 f6 f7 f8.
           ∃fn.
             (∀a. fn (In a) = f0 a) ∧ (∀a. fn (Jump a) = f1 a) ∧
             (∀a. fn (LoadConstant a) = f2 a) ∧
             (∀a. fn (LoadDM a) = f3 a) ∧ (∀a. fn (Normal a) = f4 a) ∧
             (∀a. fn (Out a) = f5 a) ∧ (fn ReservedInstr = f6) ∧
             (∀a. fn (StoreDM a) = f7 a) ∧ ∀a. fn (StoreIM a) = f8 a

   [instruction_case_cong]  Theorem

      |- ∀M M' f f1 f2 f3 f4 f5 v f6 f7.
           (M = M') ∧ (∀a. (M' = In a) ⇒ (f a = f' a)) ∧
           (∀a. (M' = Jump a) ⇒ (f1 a = f1' a)) ∧
           (∀a. (M' = LoadConstant a) ⇒ (f2 a = f2' a)) ∧
           (∀a. (M' = LoadDM a) ⇒ (f3 a = f3' a)) ∧
           (∀a. (M' = Normal a) ⇒ (f4 a = f4' a)) ∧
           (∀a. (M' = Out a) ⇒ (f5 a = f5' a)) ∧
           ((M' = ReservedInstr) ⇒ (v = v')) ∧
           (∀a. (M' = StoreDM a) ⇒ (f6 a = f6' a)) ∧
           (∀a. (M' = StoreIM a) ⇒ (f7 a = f7' a)) ⇒
           (instruction_CASE M f f1 f2 f3 f4 f5 v f6 f7 =
            instruction_CASE M' f' f1' f2' f3' f4' f5' v' f6' f7')

   [instruction_distinct]  Theorem

      |- (∀a' a. In a ≠ Jump a') ∧ (∀a' a. In a ≠ LoadConstant a') ∧
         (∀a' a. In a ≠ LoadDM a') ∧ (∀a' a. In a ≠ Normal a') ∧
         (∀a' a. In a ≠ Out a') ∧ (∀a. In a ≠ ReservedInstr) ∧
         (∀a' a. In a ≠ StoreDM a') ∧ (∀a' a. In a ≠ StoreIM a') ∧
         (∀a' a. Jump a ≠ LoadConstant a') ∧ (∀a' a. Jump a ≠ LoadDM a') ∧
         (∀a' a. Jump a ≠ Normal a') ∧ (∀a' a. Jump a ≠ Out a') ∧
         (∀a. Jump a ≠ ReservedInstr) ∧ (∀a' a. Jump a ≠ StoreDM a') ∧
         (∀a' a. Jump a ≠ StoreIM a') ∧
         (∀a' a. LoadConstant a ≠ LoadDM a') ∧
         (∀a' a. LoadConstant a ≠ Normal a') ∧
         (∀a' a. LoadConstant a ≠ Out a') ∧
         (∀a. LoadConstant a ≠ ReservedInstr) ∧
         (∀a' a. LoadConstant a ≠ StoreDM a') ∧
         (∀a' a. LoadConstant a ≠ StoreIM a') ∧
         (∀a' a. LoadDM a ≠ Normal a') ∧ (∀a' a. LoadDM a ≠ Out a') ∧
         (∀a. LoadDM a ≠ ReservedInstr) ∧ (∀a' a. LoadDM a ≠ StoreDM a') ∧
         (∀a' a. LoadDM a ≠ StoreIM a') ∧ (∀a' a. Normal a ≠ Out a') ∧
         (∀a. Normal a ≠ ReservedInstr) ∧ (∀a' a. Normal a ≠ StoreDM a') ∧
         (∀a' a. Normal a ≠ StoreIM a') ∧ (∀a. Out a ≠ ReservedInstr) ∧
         (∀a' a. Out a ≠ StoreDM a') ∧ (∀a' a. Out a ≠ StoreIM a') ∧
         (∀a. ReservedInstr ≠ StoreDM a) ∧
         (∀a. ReservedInstr ≠ StoreIM a) ∧ ∀a' a. StoreDM a ≠ StoreIM a'

   [instruction_induction]  Theorem

      |- ∀P.
           (∀p. P (In p)) ∧ (∀p. P (Jump p)) ∧ (∀p. P (LoadConstant p)) ∧
           (∀p. P (LoadDM p)) ∧ (∀p. P (Normal p)) ∧ (∀p. P (Out p)) ∧
           P ReservedInstr ∧ (∀p. P (StoreDM p)) ∧ (∀p. P (StoreIM p)) ⇒
           ∀i. P i

   [instruction_nchotomy]  Theorem

      |- ∀ii.
           (∃p. ii = In p) ∨ (∃p. ii = Jump p) ∨
           (∃p. ii = LoadConstant p) ∨ (∃p. ii = LoadDM p) ∨
           (∃p. ii = Normal p) ∨ (∃p. ii = Out p) ∨ (ii = ReservedInstr) ∨
           (∃p. ii = StoreDM p) ∨ ∃p. ii = StoreIM p

   [num2conditionT_11]  Theorem

      |- ∀r r'.
           r < 4 ⇒
           r' < 4 ⇒
           ((num2conditionT r = num2conditionT r') ⇔ (r = r'))

   [num2conditionT_ONTO]  Theorem

      |- ∀a. ∃r. (a = num2conditionT r) ∧ r < 4

   [num2conditionT_conditionT2num]  Theorem

      |- ∀a. num2conditionT (conditionT2num a) = a

   [num2conditionT_thm]  Theorem

      |- (num2conditionT 0 = skipNever) ∧ (num2conditionT 1 = skipNeg) ∧
         (num2conditionT 2 = skipZero) ∧ (num2conditionT 3 = skipInRdy)

   [num2exception_11]  Theorem

      |- ∀r r'.
           r < 2 ⇒
           r' < 2 ⇒
           ((num2exception r = num2exception r') ⇔ (r = r'))

   [num2exception_ONTO]  Theorem

      |- ∀a. ∃r. (a = num2exception r) ∧ r < 2

   [num2exception_exception2num]  Theorem

      |- ∀a. num2exception (exception2num a) = a

   [num2exception_thm]  Theorem

      |- (num2exception 0 = NoException) ∧ (num2exception 1 = Reserved)

   [num2funcT_11]  Theorem

      |- ∀r r'. r < 8 ⇒ r' < 8 ⇒ ((num2funcT r = num2funcT r') ⇔ (r = r'))

   [num2funcT_ONTO]  Theorem

      |- ∀a. ∃r. (a = num2funcT r) ∧ r < 8

   [num2funcT_funcT2num]  Theorem

      |- ∀a. num2funcT (funcT2num a) = a

   [num2funcT_thm]  Theorem

      |- (num2funcT 0 = fADD) ∧ (num2funcT 1 = fSUB) ∧
         (num2funcT 2 = fINC) ∧ (num2funcT 3 = fDEC) ∧
         (num2funcT 4 = fAND) ∧ (num2funcT 5 = fOR) ∧
         (num2funcT 6 = fXOR) ∧ (num2funcT 7 = fReserved)

   [num2shiftT_11]  Theorem

      |- ∀r r'.
           r < 4 ⇒ r' < 4 ⇒ ((num2shiftT r = num2shiftT r') ⇔ (r = r'))

   [num2shiftT_ONTO]  Theorem

      |- ∀a. ∃r. (a = num2shiftT r) ∧ r < 4

   [num2shiftT_shiftT2num]  Theorem

      |- ∀a. num2shiftT (shiftT2num a) = a

   [num2shiftT_thm]  Theorem

      |- (num2shiftT 0 = noShift) ∧ (num2shiftT 1 = RCY1) ∧
         (num2shiftT 2 = RCY8) ∧ (num2shiftT 3 = RCY16)

   [shiftT2num_11]  Theorem

      |- ∀a a'. (shiftT2num a = shiftT2num a') ⇔ (a = a')

   [shiftT2num_ONTO]  Theorem

      |- ∀r. r < 4 ⇔ ∃a. r = shiftT2num a

   [shiftT2num_num2shiftT]  Theorem

      |- ∀r. r < 4 ⇔ (shiftT2num (num2shiftT r) = r)

   [shiftT2num_thm]  Theorem

      |- (shiftT2num noShift = 0) ∧ (shiftT2num RCY1 = 1) ∧
         (shiftT2num RCY8 = 2) ∧ (shiftT2num RCY16 = 3)

   [shiftT_Axiom]  Theorem

      |- ∀x0 x1 x2 x3.
           ∃f.
             (f noShift = x0) ∧ (f RCY1 = x1) ∧ (f RCY8 = x2) ∧
             (f RCY16 = x3)

   [shiftT_EQ_shiftT]  Theorem

      |- ∀a a'. (a = a') ⇔ (shiftT2num a = shiftT2num a')

   [shiftT_case_cong]  Theorem

      |- ∀M M' v0 v1 v2 v3.
           (M = M') ∧ ((M' = noShift) ⇒ (v0 = v0')) ∧
           ((M' = RCY1) ⇒ (v1 = v1')) ∧ ((M' = RCY8) ⇒ (v2 = v2')) ∧
           ((M' = RCY16) ⇒ (v3 = v3')) ⇒
           ((case M of
               noShift => v0
             | RCY1 => v1
             | RCY8 => v2
             | RCY16 => v3) =
            case M' of
              noShift => v0'
            | RCY1 => v1'
            | RCY8 => v2'
            | RCY16 => v3')

   [shiftT_case_def]  Theorem

      |- (∀v0 v1 v2 v3.
            (case noShift of
               noShift => v0
             | RCY1 => v1
             | RCY8 => v2
             | RCY16 => v3) =
            v0) ∧
         (∀v0 v1 v2 v3.
            (case RCY1 of
               noShift => v0
             | RCY1 => v1
             | RCY8 => v2
             | RCY16 => v3) =
            v1) ∧
         (∀v0 v1 v2 v3.
            (case RCY8 of
               noShift => v0
             | RCY1 => v1
             | RCY8 => v2
             | RCY16 => v3) =
            v2) ∧
         ∀v0 v1 v2 v3.
           (case RCY16 of
              noShift => v0
            | RCY1 => v1
            | RCY8 => v2
            | RCY16 => v3) =
           v3

   [shiftT_distinct]  Theorem

      |- noShift ≠ RCY1 ∧ noShift ≠ RCY8 ∧ noShift ≠ RCY16 ∧ RCY1 ≠ RCY8 ∧
         RCY1 ≠ RCY16 ∧ RCY8 ≠ RCY16

   [shiftT_induction]  Theorem

      |- ∀P. P RCY1 ∧ P RCY16 ∧ P RCY8 ∧ P noShift ⇒ ∀a. P a

   [shiftT_nchotomy]  Theorem

      |- ∀a. (a = noShift) ∨ (a = RCY1) ∨ (a = RCY8) ∨ (a = RCY16)

   [tiny_state_11]  Theorem

      |- ∀a0 a1 a2 a3 a4 a5 a6 a7 a0' a1' a2' a3' a4' a5' a6' a7'.
           (tiny_state a0 a1 a2 a3 a4 a5 a6 a7 =
            tiny_state a0' a1' a2' a3' a4' a5' a6' a7') ⇔
           (a0 = a0') ∧ (a1 = a1') ∧ (a2 = a2') ∧ (a3 ⇔ a3') ∧ (a4 = a4') ∧
           (a5 = a5') ∧ (a6 = a6') ∧ (a7 = a7')

   [tiny_state_Axiom]  Theorem

      |- ∀f.
           ∃fn.
             ∀a0 a1 a2 a3 a4 a5 a6 a7.
               fn (tiny_state a0 a1 a2 a3 a4 a5 a6 a7) =
               f a0 a1 a2 a3 a4 a5 a6 a7

   [tiny_state_accessors]  Theorem

      |- (∀f f0 c b c0 c1 f1 e. (tiny_state f f0 c b c0 c1 f1 e).DM = f) ∧
         (∀f f0 c b c0 c1 f1 e. (tiny_state f f0 c b c0 c1 f1 e).IM = f0) ∧
         (∀f f0 c b c0 c1 f1 e.
            (tiny_state f f0 c b c0 c1 f1 e).InData = c) ∧
         (∀f f0 c b c0 c1 f1 e.
            (tiny_state f f0 c b c0 c1 f1 e).InRdy ⇔ b) ∧
         (∀f f0 c b c0 c1 f1 e.
            (tiny_state f f0 c b c0 c1 f1 e).OutStrobe = c0) ∧
         (∀f f0 c b c0 c1 f1 e. (tiny_state f f0 c b c0 c1 f1 e).PC = c1) ∧
         (∀f f0 c b c0 c1 f1 e. (tiny_state f f0 c b c0 c1 f1 e).R = f1) ∧
         ∀f f0 c b c0 c1 f1 e.
           (tiny_state f f0 c b c0 c1 f1 e).exception = e

   [tiny_state_accfupds]  Theorem

      |- (∀t f. (t with IM updated_by f).DM = t.DM) ∧
         (∀t f. (t with InData updated_by f).DM = t.DM) ∧
         (∀t f. (t with InRdy updated_by f).DM = t.DM) ∧
         (∀t f. (t with OutStrobe updated_by f).DM = t.DM) ∧
         (∀t f. (t with PC updated_by f).DM = t.DM) ∧
         (∀t f. (t with R updated_by f).DM = t.DM) ∧
         (∀t f. (t with exception updated_by f).DM = t.DM) ∧
         (∀t f. (t with DM updated_by f).IM = t.IM) ∧
         (∀t f. (t with InData updated_by f).IM = t.IM) ∧
         (∀t f. (t with InRdy updated_by f).IM = t.IM) ∧
         (∀t f. (t with OutStrobe updated_by f).IM = t.IM) ∧
         (∀t f. (t with PC updated_by f).IM = t.IM) ∧
         (∀t f. (t with R updated_by f).IM = t.IM) ∧
         (∀t f. (t with exception updated_by f).IM = t.IM) ∧
         (∀t f. (t with DM updated_by f).InData = t.InData) ∧
         (∀t f. (t with IM updated_by f).InData = t.InData) ∧
         (∀t f. (t with InRdy updated_by f).InData = t.InData) ∧
         (∀t f. (t with OutStrobe updated_by f).InData = t.InData) ∧
         (∀t f. (t with PC updated_by f).InData = t.InData) ∧
         (∀t f. (t with R updated_by f).InData = t.InData) ∧
         (∀t f. (t with exception updated_by f).InData = t.InData) ∧
         (∀t f. (t with DM updated_by f).InRdy ⇔ t.InRdy) ∧
         (∀t f. (t with IM updated_by f).InRdy ⇔ t.InRdy) ∧
         (∀t f. (t with InData updated_by f).InRdy ⇔ t.InRdy) ∧
         (∀t f. (t with OutStrobe updated_by f).InRdy ⇔ t.InRdy) ∧
         (∀t f. (t with PC updated_by f).InRdy ⇔ t.InRdy) ∧
         (∀t f. (t with R updated_by f).InRdy ⇔ t.InRdy) ∧
         (∀t f. (t with exception updated_by f).InRdy ⇔ t.InRdy) ∧
         (∀t f. (t with DM updated_by f).OutStrobe = t.OutStrobe) ∧
         (∀t f. (t with IM updated_by f).OutStrobe = t.OutStrobe) ∧
         (∀t f. (t with InData updated_by f).OutStrobe = t.OutStrobe) ∧
         (∀t f. (t with InRdy updated_by f).OutStrobe = t.OutStrobe) ∧
         (∀t f. (t with PC updated_by f).OutStrobe = t.OutStrobe) ∧
         (∀t f. (t with R updated_by f).OutStrobe = t.OutStrobe) ∧
         (∀t f. (t with exception updated_by f).OutStrobe = t.OutStrobe) ∧
         (∀t f. (t with DM updated_by f).PC = t.PC) ∧
         (∀t f. (t with IM updated_by f).PC = t.PC) ∧
         (∀t f. (t with InData updated_by f).PC = t.PC) ∧
         (∀t f. (t with InRdy updated_by f).PC = t.PC) ∧
         (∀t f. (t with OutStrobe updated_by f).PC = t.PC) ∧
         (∀t f. (t with R updated_by f).PC = t.PC) ∧
         (∀t f. (t with exception updated_by f).PC = t.PC) ∧
         (∀t f. (t with DM updated_by f).R = t.R) ∧
         (∀t f. (t with IM updated_by f).R = t.R) ∧
         (∀t f. (t with InData updated_by f).R = t.R) ∧
         (∀t f. (t with InRdy updated_by f).R = t.R) ∧
         (∀t f. (t with OutStrobe updated_by f).R = t.R) ∧
         (∀t f. (t with PC updated_by f).R = t.R) ∧
         (∀t f. (t with exception updated_by f).R = t.R) ∧
         (∀t f. (t with DM updated_by f).exception = t.exception) ∧
         (∀t f. (t with IM updated_by f).exception = t.exception) ∧
         (∀t f. (t with InData updated_by f).exception = t.exception) ∧
         (∀t f. (t with InRdy updated_by f).exception = t.exception) ∧
         (∀t f. (t with OutStrobe updated_by f).exception = t.exception) ∧
         (∀t f. (t with PC updated_by f).exception = t.exception) ∧
         (∀t f. (t with R updated_by f).exception = t.exception) ∧
         (∀t f. (t with DM updated_by f).DM = f t.DM) ∧
         (∀t f. (t with IM updated_by f).IM = f t.IM) ∧
         (∀t f. (t with InData updated_by f).InData = f t.InData) ∧
         (∀t f. (t with InRdy updated_by f).InRdy ⇔ f t.InRdy) ∧
         (∀t f.
            (t with OutStrobe updated_by f).OutStrobe = f t.OutStrobe) ∧
         (∀t f. (t with PC updated_by f).PC = f t.PC) ∧
         (∀t f. (t with R updated_by f).R = f t.R) ∧
         ∀t f. (t with exception updated_by f).exception = f t.exception

   [tiny_state_case_cong]  Theorem

      |- ∀M M' f.
           (M = M') ∧
           (∀a0 a1 a2 a3 a4 a5 a6 a7.
              (M' = tiny_state a0 a1 a2 a3 a4 a5 a6 a7) ⇒
              (f a0 a1 a2 a3 a4 a5 a6 a7 = f' a0 a1 a2 a3 a4 a5 a6 a7)) ⇒
           (tiny_state_CASE M f = tiny_state_CASE M' f')

   [tiny_state_component_equality]  Theorem

      |- ∀t1 t2.
           (t1 = t2) ⇔
           (t1.DM = t2.DM) ∧ (t1.IM = t2.IM) ∧ (t1.InData = t2.InData) ∧
           (t1.InRdy ⇔ t2.InRdy) ∧ (t1.OutStrobe = t2.OutStrobe) ∧
           (t1.PC = t2.PC) ∧ (t1.R = t2.R) ∧ (t1.exception = t2.exception)

   [tiny_state_fn_updates]  Theorem

      |- (∀f2 f f0 c b c0 c1 f1 e.
            tiny_state f f0 c b c0 c1 f1 e with DM updated_by f2 =
            tiny_state (f2 f) f0 c b c0 c1 f1 e) ∧
         (∀f2 f f0 c b c0 c1 f1 e.
            tiny_state f f0 c b c0 c1 f1 e with IM updated_by f2 =
            tiny_state f (f2 f0) c b c0 c1 f1 e) ∧
         (∀f2 f f0 c b c0 c1 f1 e.
            tiny_state f f0 c b c0 c1 f1 e with InData updated_by f2 =
            tiny_state f f0 (f2 c) b c0 c1 f1 e) ∧
         (∀f2 f f0 c b c0 c1 f1 e.
            tiny_state f f0 c b c0 c1 f1 e with InRdy updated_by f2 =
            tiny_state f f0 c (f2 b) c0 c1 f1 e) ∧
         (∀f2 f f0 c b c0 c1 f1 e.
            tiny_state f f0 c b c0 c1 f1 e with OutStrobe updated_by f2 =
            tiny_state f f0 c b (f2 c0) c1 f1 e) ∧
         (∀f2 f f0 c b c0 c1 f1 e.
            tiny_state f f0 c b c0 c1 f1 e with PC updated_by f2 =
            tiny_state f f0 c b c0 (f2 c1) f1 e) ∧
         (∀f2 f f0 c b c0 c1 f1 e.
            tiny_state f f0 c b c0 c1 f1 e with R updated_by f2 =
            tiny_state f f0 c b c0 c1 (f2 f1) e) ∧
         ∀f2 f f0 c b c0 c1 f1 e.
           tiny_state f f0 c b c0 c1 f1 e with exception updated_by f2 =
           tiny_state f f0 c b c0 c1 f1 (f2 e)

   [tiny_state_fupdcanon]  Theorem

      |- (∀t g f.
            t with <|IM updated_by f; DM updated_by g|> =
            t with <|DM updated_by g; IM updated_by f|>) ∧
         (∀t g f.
            t with <|InData updated_by f; DM updated_by g|> =
            t with <|DM updated_by g; InData updated_by f|>) ∧
         (∀t g f.
            t with <|InData updated_by f; IM updated_by g|> =
            t with <|IM updated_by g; InData updated_by f|>) ∧
         (∀t g f.
            t with <|InRdy updated_by f; DM updated_by g|> =
            t with <|DM updated_by g; InRdy updated_by f|>) ∧
         (∀t g f.
            t with <|InRdy updated_by f; IM updated_by g|> =
            t with <|IM updated_by g; InRdy updated_by f|>) ∧
         (∀t g f.
            t with <|InRdy updated_by f; InData updated_by g|> =
            t with <|InData updated_by g; InRdy updated_by f|>) ∧
         (∀t g f.
            t with <|OutStrobe updated_by f; DM updated_by g|> =
            t with <|DM updated_by g; OutStrobe updated_by f|>) ∧
         (∀t g f.
            t with <|OutStrobe updated_by f; IM updated_by g|> =
            t with <|IM updated_by g; OutStrobe updated_by f|>) ∧
         (∀t g f.
            t with <|OutStrobe updated_by f; InData updated_by g|> =
            t with <|InData updated_by g; OutStrobe updated_by f|>) ∧
         (∀t g f.
            t with <|OutStrobe updated_by f; InRdy updated_by g|> =
            t with <|InRdy updated_by g; OutStrobe updated_by f|>) ∧
         (∀t g f.
            t with <|PC updated_by f; DM updated_by g|> =
            t with <|DM updated_by g; PC updated_by f|>) ∧
         (∀t g f.
            t with <|PC updated_by f; IM updated_by g|> =
            t with <|IM updated_by g; PC updated_by f|>) ∧
         (∀t g f.
            t with <|PC updated_by f; InData updated_by g|> =
            t with <|InData updated_by g; PC updated_by f|>) ∧
         (∀t g f.
            t with <|PC updated_by f; InRdy updated_by g|> =
            t with <|InRdy updated_by g; PC updated_by f|>) ∧
         (∀t g f.
            t with <|PC updated_by f; OutStrobe updated_by g|> =
            t with <|OutStrobe updated_by g; PC updated_by f|>) ∧
         (∀t g f.
            t with <|R updated_by f; DM updated_by g|> =
            t with <|DM updated_by g; R updated_by f|>) ∧
         (∀t g f.
            t with <|R updated_by f; IM updated_by g|> =
            t with <|IM updated_by g; R updated_by f|>) ∧
         (∀t g f.
            t with <|R updated_by f; InData updated_by g|> =
            t with <|InData updated_by g; R updated_by f|>) ∧
         (∀t g f.
            t with <|R updated_by f; InRdy updated_by g|> =
            t with <|InRdy updated_by g; R updated_by f|>) ∧
         (∀t g f.
            t with <|R updated_by f; OutStrobe updated_by g|> =
            t with <|OutStrobe updated_by g; R updated_by f|>) ∧
         (∀t g f.
            t with <|R updated_by f; PC updated_by g|> =
            t with <|PC updated_by g; R updated_by f|>) ∧
         (∀t g f.
            t with <|exception updated_by f; DM updated_by g|> =
            t with <|DM updated_by g; exception updated_by f|>) ∧
         (∀t g f.
            t with <|exception updated_by f; IM updated_by g|> =
            t with <|IM updated_by g; exception updated_by f|>) ∧
         (∀t g f.
            t with <|exception updated_by f; InData updated_by g|> =
            t with <|InData updated_by g; exception updated_by f|>) ∧
         (∀t g f.
            t with <|exception updated_by f; InRdy updated_by g|> =
            t with <|InRdy updated_by g; exception updated_by f|>) ∧
         (∀t g f.
            t with <|exception updated_by f; OutStrobe updated_by g|> =
            t with <|OutStrobe updated_by g; exception updated_by f|>) ∧
         (∀t g f.
            t with <|exception updated_by f; PC updated_by g|> =
            t with <|PC updated_by g; exception updated_by f|>) ∧
         ∀t g f.
           t with <|exception updated_by f; R updated_by g|> =
           t with <|R updated_by g; exception updated_by f|>

   [tiny_state_fupdcanon_comp]  Theorem

      |- ((∀g f.
              _ record fupdateIM f o  _ record fupdateDM g =
              _ record fupdateDM g o  _ record fupdateIM f) ∧
          ∀h g f.
             _ record fupdateIM f o  _ record fupdateDM g o h =
             _ record fupdateDM g o  _ record fupdateIM f o h) ∧
         ((∀g f.
              _ record fupdateInData f o  _ record fupdateDM g =
              _ record fupdateDM g o  _ record fupdateInData f) ∧
          ∀h g f.
             _ record fupdateInData f o  _ record fupdateDM g o h =
             _ record fupdateDM g o  _ record fupdateInData f o h) ∧
         ((∀g f.
              _ record fupdateInData f o  _ record fupdateIM g =
              _ record fupdateIM g o  _ record fupdateInData f) ∧
          ∀h g f.
             _ record fupdateInData f o  _ record fupdateIM g o h =
             _ record fupdateIM g o  _ record fupdateInData f o h) ∧
         ((∀g f.
              _ record fupdateInRdy f o  _ record fupdateDM g =
              _ record fupdateDM g o  _ record fupdateInRdy f) ∧
          ∀h g f.
             _ record fupdateInRdy f o  _ record fupdateDM g o h =
             _ record fupdateDM g o  _ record fupdateInRdy f o h) ∧
         ((∀g f.
              _ record fupdateInRdy f o  _ record fupdateIM g =
              _ record fupdateIM g o  _ record fupdateInRdy f) ∧
          ∀h g f.
             _ record fupdateInRdy f o  _ record fupdateIM g o h =
             _ record fupdateIM g o  _ record fupdateInRdy f o h) ∧
         ((∀g f.
              _ record fupdateInRdy f o  _ record fupdateInData g =
              _ record fupdateInData g o  _ record fupdateInRdy f) ∧
          ∀h g f.
             _ record fupdateInRdy f o  _ record fupdateInData g o h =
             _ record fupdateInData g o  _ record fupdateInRdy f o h) ∧
         ((∀g f.
              _ record fupdateOutStrobe f o  _ record fupdateDM g =
              _ record fupdateDM g o  _ record fupdateOutStrobe f) ∧
          ∀h g f.
             _ record fupdateOutStrobe f o  _ record fupdateDM g o h =
             _ record fupdateDM g o  _ record fupdateOutStrobe f o h) ∧
         ((∀g f.
              _ record fupdateOutStrobe f o  _ record fupdateIM g =
              _ record fupdateIM g o  _ record fupdateOutStrobe f) ∧
          ∀h g f.
             _ record fupdateOutStrobe f o  _ record fupdateIM g o h =
             _ record fupdateIM g o  _ record fupdateOutStrobe f o h) ∧
         ((∀g f.
              _ record fupdateOutStrobe f o  _ record fupdateInData g =
              _ record fupdateInData g o  _ record fupdateOutStrobe f) ∧
          ∀h g f.
             _ record fupdateOutStrobe f o  _ record fupdateInData g o h =
             _ record fupdateInData g o  _ record fupdateOutStrobe f o h) ∧
         ((∀g f.
              _ record fupdateOutStrobe f o  _ record fupdateInRdy g =
              _ record fupdateInRdy g o  _ record fupdateOutStrobe f) ∧
          ∀h g f.
             _ record fupdateOutStrobe f o  _ record fupdateInRdy g o h =
             _ record fupdateInRdy g o  _ record fupdateOutStrobe f o h) ∧
         ((∀g f.
              _ record fupdatePC f o  _ record fupdateDM g =
              _ record fupdateDM g o  _ record fupdatePC f) ∧
          ∀h g f.
             _ record fupdatePC f o  _ record fupdateDM g o h =
             _ record fupdateDM g o  _ record fupdatePC f o h) ∧
         ((∀g f.
              _ record fupdatePC f o  _ record fupdateIM g =
              _ record fupdateIM g o  _ record fupdatePC f) ∧
          ∀h g f.
             _ record fupdatePC f o  _ record fupdateIM g o h =
             _ record fupdateIM g o  _ record fupdatePC f o h) ∧
         ((∀g f.
              _ record fupdatePC f o  _ record fupdateInData g =
              _ record fupdateInData g o  _ record fupdatePC f) ∧
          ∀h g f.
             _ record fupdatePC f o  _ record fupdateInData g o h =
             _ record fupdateInData g o  _ record fupdatePC f o h) ∧
         ((∀g f.
              _ record fupdatePC f o  _ record fupdateInRdy g =
              _ record fupdateInRdy g o  _ record fupdatePC f) ∧
          ∀h g f.
             _ record fupdatePC f o  _ record fupdateInRdy g o h =
             _ record fupdateInRdy g o  _ record fupdatePC f o h) ∧
         ((∀g f.
              _ record fupdatePC f o  _ record fupdateOutStrobe g =
              _ record fupdateOutStrobe g o  _ record fupdatePC f) ∧
          ∀h g f.
             _ record fupdatePC f o  _ record fupdateOutStrobe g o h =
             _ record fupdateOutStrobe g o  _ record fupdatePC f o h) ∧
         ((∀g f.
              _ record fupdateR f o  _ record fupdateDM g =
              _ record fupdateDM g o  _ record fupdateR f) ∧
          ∀h g f.
             _ record fupdateR f o  _ record fupdateDM g o h =
             _ record fupdateDM g o  _ record fupdateR f o h) ∧
         ((∀g f.
              _ record fupdateR f o  _ record fupdateIM g =
              _ record fupdateIM g o  _ record fupdateR f) ∧
          ∀h g f.
             _ record fupdateR f o  _ record fupdateIM g o h =
             _ record fupdateIM g o  _ record fupdateR f o h) ∧
         ((∀g f.
              _ record fupdateR f o  _ record fupdateInData g =
              _ record fupdateInData g o  _ record fupdateR f) ∧
          ∀h g f.
             _ record fupdateR f o  _ record fupdateInData g o h =
             _ record fupdateInData g o  _ record fupdateR f o h) ∧
         ((∀g f.
              _ record fupdateR f o  _ record fupdateInRdy g =
              _ record fupdateInRdy g o  _ record fupdateR f) ∧
          ∀h g f.
             _ record fupdateR f o  _ record fupdateInRdy g o h =
             _ record fupdateInRdy g o  _ record fupdateR f o h) ∧
         ((∀g f.
              _ record fupdateR f o  _ record fupdateOutStrobe g =
              _ record fupdateOutStrobe g o  _ record fupdateR f) ∧
          ∀h g f.
             _ record fupdateR f o  _ record fupdateOutStrobe g o h =
             _ record fupdateOutStrobe g o  _ record fupdateR f o h) ∧
         ((∀g f.
              _ record fupdateR f o  _ record fupdatePC g =
              _ record fupdatePC g o  _ record fupdateR f) ∧
          ∀h g f.
             _ record fupdateR f o  _ record fupdatePC g o h =
             _ record fupdatePC g o  _ record fupdateR f o h) ∧
         ((∀g f.
              _ record fupdateexception f o  _ record fupdateDM g =
              _ record fupdateDM g o  _ record fupdateexception f) ∧
          ∀h g f.
             _ record fupdateexception f o  _ record fupdateDM g o h =
             _ record fupdateDM g o  _ record fupdateexception f o h) ∧
         ((∀g f.
              _ record fupdateexception f o  _ record fupdateIM g =
              _ record fupdateIM g o  _ record fupdateexception f) ∧
          ∀h g f.
             _ record fupdateexception f o  _ record fupdateIM g o h =
             _ record fupdateIM g o  _ record fupdateexception f o h) ∧
         ((∀g f.
              _ record fupdateexception f o  _ record fupdateInData g =
              _ record fupdateInData g o  _ record fupdateexception f) ∧
          ∀h g f.
             _ record fupdateexception f o  _ record fupdateInData g o h =
             _ record fupdateInData g o  _ record fupdateexception f o h) ∧
         ((∀g f.
              _ record fupdateexception f o  _ record fupdateInRdy g =
              _ record fupdateInRdy g o  _ record fupdateexception f) ∧
          ∀h g f.
             _ record fupdateexception f o  _ record fupdateInRdy g o h =
             _ record fupdateInRdy g o  _ record fupdateexception f o h) ∧
         ((∀g f.
              _ record fupdateexception f o  _ record fupdateOutStrobe g =
              _ record fupdateOutStrobe g o  _ record fupdateexception f) ∧
          ∀h g f.
             _ record fupdateexception f o  _ record fupdateOutStrobe g o
            h =
             _ record fupdateOutStrobe g o  _ record fupdateexception f o
            h) ∧
         ((∀g f.
              _ record fupdateexception f o  _ record fupdatePC g =
              _ record fupdatePC g o  _ record fupdateexception f) ∧
          ∀h g f.
             _ record fupdateexception f o  _ record fupdatePC g o h =
             _ record fupdatePC g o  _ record fupdateexception f o h) ∧
         (∀g f.
             _ record fupdateexception f o  _ record fupdateR g =
             _ record fupdateR g o  _ record fupdateexception f) ∧
         ∀h g f.
            _ record fupdateexception f o  _ record fupdateR g o h =
            _ record fupdateR g o  _ record fupdateexception f o h

   [tiny_state_fupdfupds]  Theorem

      |- (∀t g f.
            t with <|DM updated_by f; DM updated_by g|> =
            t with DM updated_by f o g) ∧
         (∀t g f.
            t with <|IM updated_by f; IM updated_by g|> =
            t with IM updated_by f o g) ∧
         (∀t g f.
            t with <|InData updated_by f; InData updated_by g|> =
            t with InData updated_by f o g) ∧
         (∀t g f.
            t with <|InRdy updated_by f; InRdy updated_by g|> =
            t with InRdy updated_by f o g) ∧
         (∀t g f.
            t with <|OutStrobe updated_by f; OutStrobe updated_by g|> =
            t with OutStrobe updated_by f o g) ∧
         (∀t g f.
            t with <|PC updated_by f; PC updated_by g|> =
            t with PC updated_by f o g) ∧
         (∀t g f.
            t with <|R updated_by f; R updated_by g|> =
            t with R updated_by f o g) ∧
         ∀t g f.
           t with <|exception updated_by f; exception updated_by g|> =
           t with exception updated_by f o g

   [tiny_state_fupdfupds_comp]  Theorem

      |- ((∀g f.
              _ record fupdateDM f o  _ record fupdateDM g =
              _ record fupdateDM (f o g)) ∧
          ∀h g f.
             _ record fupdateDM f o  _ record fupdateDM g o h =
             _ record fupdateDM (f o g) o h) ∧
         ((∀g f.
              _ record fupdateIM f o  _ record fupdateIM g =
              _ record fupdateIM (f o g)) ∧
          ∀h g f.
             _ record fupdateIM f o  _ record fupdateIM g o h =
             _ record fupdateIM (f o g) o h) ∧
         ((∀g f.
              _ record fupdateInData f o  _ record fupdateInData g =
              _ record fupdateInData (f o g)) ∧
          ∀h g f.
             _ record fupdateInData f o  _ record fupdateInData g o h =
             _ record fupdateInData (f o g) o h) ∧
         ((∀g f.
              _ record fupdateInRdy f o  _ record fupdateInRdy g =
              _ record fupdateInRdy (f o g)) ∧
          ∀h g f.
             _ record fupdateInRdy f o  _ record fupdateInRdy g o h =
             _ record fupdateInRdy (f o g) o h) ∧
         ((∀g f.
              _ record fupdateOutStrobe f o  _ record fupdateOutStrobe g =
              _ record fupdateOutStrobe (f o g)) ∧
          ∀h g f.
             _ record fupdateOutStrobe f o  _ record fupdateOutStrobe g o
            h =
             _ record fupdateOutStrobe (f o g) o h) ∧
         ((∀g f.
              _ record fupdatePC f o  _ record fupdatePC g =
              _ record fupdatePC (f o g)) ∧
          ∀h g f.
             _ record fupdatePC f o  _ record fupdatePC g o h =
             _ record fupdatePC (f o g) o h) ∧
         ((∀g f.
              _ record fupdateR f o  _ record fupdateR g =
              _ record fupdateR (f o g)) ∧
          ∀h g f.
             _ record fupdateR f o  _ record fupdateR g o h =
             _ record fupdateR (f o g) o h) ∧
         (∀g f.
             _ record fupdateexception f o  _ record fupdateexception g =
             _ record fupdateexception (f o g)) ∧
         ∀h g f.
            _ record fupdateexception f o  _ record fupdateexception g o
           h =
            _ record fupdateexception (f o g) o h

   [tiny_state_induction]  Theorem

      |- ∀P.
           (∀f f0 c b c0 c1 f1 e. P (tiny_state f f0 c b c0 c1 f1 e)) ⇒
           ∀t. P t

   [tiny_state_literal_11]  Theorem

      |- ∀f11 f01 c11 b1 c01 c1 f1 e1 f12 f02 c12 b2 c02 c2 f2 e2.
           (<|DM := f11; IM := f01; InData := c11; InRdy := b1;
              OutStrobe := c01; PC := c1; R := f1; exception := e1|> =
            <|DM := f12; IM := f02; InData := c12; InRdy := b2;
              OutStrobe := c02; PC := c2; R := f2; exception := e2|>) ⇔
           (f11 = f12) ∧ (f01 = f02) ∧ (c11 = c12) ∧ (b1 ⇔ b2) ∧
           (c01 = c02) ∧ (c1 = c2) ∧ (f1 = f2) ∧ (e1 = e2)

   [tiny_state_literal_nchotomy]  Theorem

      |- ∀t.
           ∃f1 f0 c1 b c0 c f e.
             t =
             <|DM := f1; IM := f0; InData := c1; InRdy := b;
               OutStrobe := c0; PC := c; R := f; exception := e|>

   [tiny_state_nchotomy]  Theorem

      |- ∀tt. ∃f f0 c b c0 c1 f1 e. tt = tiny_state f f0 c b c0 c1 f1 e

   [tiny_state_updates_eq_literal]  Theorem

      |- ∀t f1 f0 c1 b c0 c f e.
           t with
           <|DM := f1; IM := f0; InData := c1; InRdy := b; OutStrobe := c0;
             PC := c; R := f; exception := e|> =
           <|DM := f1; IM := f0; InData := c1; InRdy := b; OutStrobe := c0;
             PC := c; R := f; exception := e|>


*)
end
