-- =======================
-- Specification of x86-64
-- =======================

type byte = bits(8)
type word = bits(16)
type dword = bits(32)
type qword = bits(64)

type stream = byte list

---------------------------------------------------------------------------

-- ===============
-- The State Space
-- ===============

exception FAIL :: string

------------
-- Registers
------------

-- General purpose registers

construct Zreg
  { RAX RCX RDX RBX RSP RBP RSI RDI zR8 zR9 zR10 zR11 zR12 zR13 zR14 zR15 }

type reg = Zreg -> qword

declare REG :: reg

-- The program counter

declare RIP :: qword

---------
-- Memory
---------

exception BadMemAccess :: qword

type mem = qword -> byte option

declare MEM :: mem
declare ICACHE :: mem

component mem8 (addr :: qword) :: byte
{
   value =
      match MEM (addr)
      {
         case Some (b) => b
         case None => #BadMemAccess(addr)
      }
   assign b =
      if IsSome (MEM (addr))
         then MEM (addr) <- Some (b)
      else #BadMemAccess(addr)
}

component mem16 (addr :: qword) :: word
{
   value = ( mem8 (addr + 1) : mem8 (addr) )
   assign w =
      { mem8 (addr)     <- w<7:0>;
        mem8 (addr + 1) <- w<15:8>
      }
}

component mem32 (addr :: qword) :: dword
{
   value = ( mem16 (addr + 2) : mem16 (addr) )
   assign w =
      { mem16 (addr)     <- w<15:0>;
        mem16 (addr + 2) <- w<31:16>
      }
}

component mem64 (addr :: qword) :: qword
{
   value = ( mem32 (addr + 4) : mem32 (addr) )
   assign w =
      { mem32 (addr)     <- w<31:0>;
        mem32 (addr + 4) <- w<63:32>
      }
}

--------
-- Flags
--------

exception BadFlagAccess :: string

construct Zeflags { Z_CF Z_PF Z_AF Z_ZF Z_SF Z_OF }

type eflags = Zeflags -> bool option

declare EFLAGS :: eflags

component Eflag (flag :: Zeflags) :: bool
{
   value =
      match EFLAGS (flag)
      {
         case Some (b) => b
         case None => #BadFlagAccess([flag])
      }
  assign b = EFLAGS (flag) <- Some (b)
}

unit FlagUnspecified (flag :: Zeflags) = EFLAGS (flag) <- None

component CF :: bool { value = Eflag (Z_CF) assign b = Eflag (Z_CF) <- b }
component PF :: bool { value = Eflag (Z_PF) assign b = Eflag (Z_PF) <- b }
component AF :: bool { value = Eflag (Z_AF) assign b = Eflag (Z_AF) <- b }
component ZF :: bool { value = Eflag (Z_ZF) assign b = Eflag (Z_ZF) <- b }
component SF :: bool { value = Eflag (Z_SF) assign b = Eflag (Z_SF) <- b }
component OF :: bool { value = Eflag (Z_OF) assign b = Eflag (Z_OF) <- b }

---------------------------------------------------------------------------

-- =========
-- AST types
-- =========

construct Zsize { Z8 :: bool Z16 Z32 Z64 }

construct Zbase
{
  ZnoBase
  ZripBase
  ZregBase :: Zreg
}

construct Zrm
{
  Zr :: Zreg    -- register
  Zm :: (bits(2) * Zreg) option * Zbase * qword
                -- mem [2^{scale} * index + base + displacement]
}

-- Here XX is one of 8, 16, 32, 64.
construct Zdest_src
{
  Zrm_i :: Zrm * qword   -- mnemonic r/mXX, immXX (sign-extended)
  Zrm_r :: Zrm * Zreg    -- mnemonic r/mXX, rXX
  Zr_rm :: Zreg * Zrm    -- mnemonic rXX, r/mXX
}

construct Zimm_rm
{
   Zrm  :: Zrm    -- r/mXX
   Zimm :: qword  -- sign-extended immediate
}

construct Zmonop_name { Zdec Zinc Znot Zneg }

construct Zbinop_name
  { Zadd Zor  Zadc Zsbb Zand Zsub Zxor  Zcmp
    Zrol Zror Zrcl Zrcr Zshl Zshr Ztest Zsar }

construct Zcond
{                 -- N = not
  Z_O    Z_NO     -- O = overflow
  Z_B    Z_NB     -- B = below
  Z_E    Z_NE     -- E = equal
  Z_NA   Z_A      -- A = above
  Z_S    Z_NS     -- S = signed
  Z_P    Z_NP     -- P = parity
  Z_L    Z_NL     -- L = less
  Z_NG   Z_G      -- L = greater
  Z_ALWAYS
}

---------------------------------------------------------------------------

-- =====================
-- Instruction Semantics
-- =====================

-- Effective addresses

construct Zea
{
  Zea_i :: Zsize * qword   -- Constant
  Zea_r :: Zsize * Zreg    -- Register name
  Zea_m :: Zsize * qword   -- Memory address
}

qword ea_index (index :: (bits(2) * Zreg) option) =
   match index
   {
      case None => 0
      case Some (scale, idx) => 1 << [scale] * REG (idx)
   }

qword ea_base (base :: Zbase) =
   match base
   {
      case ZnoBase => 0
      case ZripBase => RIP
      case ZregBase (b) => REG (b)
   }

Zea ea_Zrm (size :: Zsize, rm :: Zrm) =
   match rm
   {
     case Zr (r) => Zea_r (size, r)
     case Zm (index, base, displacement) =>
        Zea_m (size, ea_index (index) + ea_base (base) + displacement)
   }

Zea ea_Zdest (size :: Zsize, ds :: Zdest_src) =
   match ds
   {
      case Zrm_i (rm, _) => ea_Zrm (size, rm)
      case Zrm_r (rm, _) => ea_Zrm (size, rm)
      case Zr_rm (r, _)  => Zea_r (size, r)
   }

Zea ea_Zsrc (size :: Zsize, ds :: Zdest_src) =
   match ds
   {
      case Zrm_i (_, i)  => Zea_i (size, i)
      case Zrm_r (_, r)  => Zea_r (size, r)
      case Zr_rm (_, rm) => ea_Zrm (size, rm)
   }

Zea ea_Zimm_rm (size :: Zsize, imm_rm :: Zimm_rm) =
   match imm_rm
   {
      case Zrm (rm)   => ea_Zrm (size, rm)
      case Zimm (imm) => Zea_i (size, imm)
   }

-- Reading / Writing an EA

qword restrictSize (size :: Zsize, imm :: qword) =
   match size
   {
      case Z8 (_) => imm && 0xFF
      case Z16    => imm && 0xFFFF
      case Z32    => imm && 0xFFFFFFFF
      case Z64    => imm
   }

component EA (ea :: Zea) :: qword
{
   value =
      match ea
      {
         case Zea_i (i) => restrictSize (i)
         case Zea_r (Z8 (have_rex), r) =>
            if have_rex or r notin set { RSP, RBP, RSI, RDI }
               then REG (r) && 0xFF
            else (REG ([[r] - 0n4]) >>+ 8) && 0xFF
         case Zea_r (s, r)      => restrictSize (s, REG (r))
         case Zea_m (Z8 (_), a) => [mem8 (a)]
         case Zea_m (Z16, a)    => [mem16 (a)]
         case Zea_m (Z32, a)    => [mem32 (a)]
         case Zea_m (Z64, a)    => mem64 (a)
      }
   assign w =
      match ea
      {
         case Zea_i (i) => #FAIL ("write to constant")
         case Zea_r (Z8 (have_rex), r) =>
            if have_rex or r notin set { RSP, RBP, RSI, RDI }
               then REG (r)<7:0> <- w<7:0>
            else REG ([[r] - 0n4])<15:8> <- w<7:0>
         case Zea_r (Z16, r)       => REG (r)<15:0> <- w<15:0>
         case Zea_r (Z32, r)       => REG (r) <- ZeroExtend (w<31:0>)
         case Zea_r (Z64, r)       => REG (r) <- w
         case Zea_m (Z8 (_), a)    => mem8 (a) <- w<7:0>
         case Zea_m (Z16, a)       => mem16 (a) <- w<15:0>
         case Zea_m (Z32, a)       => mem32 (a) <- w<31:0>
         case Zea_m (Z64, a)       => mem64 (a) <- w
      }
}

Zea * qword * qword read_dest_src_ea (sd :: Zsize * Zdest_src) =
{
   ea = ea_Zdest (sd);
   return (ea, EA (ea), EA (ea_Zsrc (sd)))
}

-- Find the destination according to procedure call semantics
qword call_dest_from_ea (ea :: Zea) =
   match ea
   {
      case Zea_i (_, i) => RIP + i
      case Zea_r (_, r) => REG (r)
      case Zea_m (_, a) => mem64 (a)
   }

qword get_ea_address (ea :: Zea) =
   match ea
   {
      case Zea_i (_, i) => 0
      case Zea_r (_, r) => 0
      case Zea_m (_, a) => a
   }

-- RIP update

-- Update RIP according to procedure call
unit jump_to_ea (ea :: Zea) = RIP <- call_dest_from_ea (ea)

-- EFLAG updates

bool ByteParity (b :: byte) =
{  count = [b<7>] + [b<6>] + [b<5>] + [b<4>] +
           [b<3>] + [b<2>] + [b<1>] + [b<0>] :: nat;
   return (count mod 2 == 0)
}

nat Zsize_width (size :: Zsize) =
   match size
   {
      case Z8 (_) => 8
      case Z16    => 16
      case Z32    => 32
      case Z64    => 64
   }

bool word_size_msb (size :: Zsize, w :: qword) = ( w<Zsize_width (size) - 1> )

unit write_PF (w :: qword) = PF <- ByteParity (w<7:0>)

unit write_SF (s_w :: Zsize * qword) = SF <- word_size_msb (s_w)

unit write_ZF (size :: Zsize, w :: qword) =
   ZF <- match size
         {
            case Z8 (_)  => [w] == 0`8
            case Z16     => [w] == 0`16
            case Z32     => [w] == 0`32
            case Z64     => w == 0
         }

unit write_logical_eflags (size :: Zsize, w :: qword) =
{
   CF <- false;
   OF <- false;
   write_PF (w);
   write_SF (size, w);
   write_ZF (size, w);
   FlagUnspecified (Z_AF)
}

unit write_arith_eflags_except_CF_OF (size :: Zsize, w :: qword) =
{
   write_PF (w);
   write_SF (size, w);
   write_ZF (size, w);
   FlagUnspecified (Z_AF)
}

type result = qword * bool * bool

unit write_arith_eflags (size :: Zsize, r :: result) =
{
   w, c, x = r;
   CF <- c;
   OF <- x;
   write_arith_eflags_except_CF_OF (size, w)
}

unit erase_eflags = EFLAGS <- InitMap (None)

-- Bin-ops

nat value_width (s :: Zsize) = 2 ** Zsize_width (s)

bool word_signed_overflow_add (size :: Zsize, a :: qword, b :: qword) =
  ( word_size_msb (size, a) == word_size_msb (size, b) and
    word_size_msb (size, a + b) != word_size_msb (size, a) )

bool word_signed_overflow_sub (size :: Zsize, a :: qword, b :: qword) =
  ( word_size_msb (size, a) != word_size_msb (size, b) and
    word_size_msb (size, a - b) != word_size_msb (size, a) )

result add_with_carry_out (size :: Zsize, x :: qword, y :: qword) =
   return (x + y, value_width (size) <= [x] + [y] :: nat,
           word_signed_overflow_add (size, x, y))

result sub_with_borrow (size :: Zsize, x :: qword, y :: qword) =
   return (x - y, x <+ y, word_signed_overflow_sub (size, x, y))

unit write_arith_result (size :: Zsize, r :: result, ea :: Zea) =
{
   write_arith_eflags (size, r);
   EA (ea) <- Fst (r)
}

unit write_arith_result_no_CF_OF (size :: Zsize, w :: qword, ea :: Zea) =
{
   write_arith_eflags_except_CF_OF (size, w);
   EA (ea) <- w
}

unit write_logical_result (size :: Zsize, w :: qword, ea :: Zea) =
{
   write_logical_eflags (size, w);
   EA (ea) <- w
}

unit write_result_erase_eflags (w :: qword, ea :: Zea) =
{
   erase_eflags;
   EA (ea) <- w
}

nat maskShift (size :: Zsize, w :: qword) =
   if size == Z64 then [w<5:0>] else [w<4:0>]

qword ROL (size :: Zsize, x :: qword, y :: qword) =
   match size
   {
      case Z8 (_) => [x<7:0>  #<< ([y<4:0>]::nat)]
      case Z16    => [x<15:0> #<< ([y<4:0>]::nat)]
      case Z32    => [x<31:0> #<< ([y<4:0>]::nat)]
      case Z64    => x #<< ([y<5:0>]::nat)
   }

qword ROR (size :: Zsize, x :: qword, y :: qword) =
   match size
   {
      case Z8 (_) => [x<7:0>  #>> ([y<4:0>]::nat)]
      case Z16    => [x<15:0> #>> ([y<4:0>]::nat)]
      case Z32    => [x<31:0> #>> ([y<4:0>]::nat)]
      case Z64    => x #>> ([y<5:0>]::nat)
   }

qword SAR (size :: Zsize, x :: qword, y :: qword) =
   match size
   {
      case Z8 (_) => [x<7:0>  >> ([y<4:0>]::nat)]
      case Z16    => [x<15:0> >> ([y<4:0>]::nat)]
      case Z32    => [x<31:0> >> ([y<4:0>]::nat)]
      case Z64    => x >> ([y<5:0>]::nat)
   }

unit write_binop
   ( s :: Zsize,
     bop :: Zbinop_name,
     x :: qword,
     y :: qword,
     ea :: Zea) =
   match bop
   {
      case Zadd  => write_arith_result (s, add_with_carry_out (s, x, y), ea)
      case Zsub  => write_arith_result (s, sub_with_borrow (s, x, y), ea)
      case Zcmp  => write_arith_eflags (s, sub_with_borrow (s, x, y))
      case Ztest => write_logical_eflags (s, x && y)
      case Zand  => write_logical_result (s, x && y, ea)
      case Zxor  => write_logical_result (s, x ?? y, ea)
      case Zor   => write_logical_result (s, x || y, ea)
      case Zrol  => write_result_erase_eflags (ROL (s, x, y), ea)
      case Zror  => write_result_erase_eflags (ROR (s, x, y), ea)
      case Zsar  => write_result_erase_eflags (SAR (s, x, y), ea)
      case Zshl  => write_result_erase_eflags (x << maskShift (s, y), ea)
      case Zshr  => write_result_erase_eflags (x >>+ maskShift (s, y), ea)
      case Zadc  =>
         {
            carry = CF;
            result = x + y + [carry];
            CF <- value_width (s) <= [x] + [y] + [carry] :: nat;
            FlagUnspecified (Z_OF);
            write_arith_result_no_CF_OF (s, result, ea)
         }
      case Zsbb  =>
         {
            carry = CF;
            result = x - (y + [carry]);
            CF <- [x] < [y] + [carry] :: nat;
            FlagUnspecified (Z_OF);
            write_arith_result_no_CF_OF (s, result, ea)
         }
      -- rcl and rcr
      case _ => #FAIL ("Binary op not implemented: " : [bop])
   }

-- Mon-ops

unit write_monop
   ( s :: Zsize,
     mop :: Zmonop_name,
     x :: qword,
     ea :: Zea) =
   match mop
   {
      case Znot => EA (ea) <- ~x
      case Zdec => write_arith_result_no_CF_OF (s, x - 1, ea)
      case Zinc => write_arith_result_no_CF_OF (s, x + 1, ea)
      case Zneg =>
         {
            write_arith_result_no_CF_OF (s, -x, ea);
            FlagUnspecified (Z_CF)
         }
   }

-- Evaluating conditions of eflags

bool read_cond (c :: Zcond) =
   match c
   {
      case Z_O  => OF
      case Z_NO => not OF
      case Z_B  => CF
      case Z_NB => not CF
      case Z_E  => ZF
      case Z_NE => not ZF
      case Z_A  => -- not CF and not ZF
         match EFLAGS (Z_CF), EFLAGS (Z_ZF)
         {
            case Some (false), Some (false) => true
            case Some (true), _ => false
            case _, Some (true) => false
            case _ => #BadFlagAccess("read_cond: " : [c])
         }
      case Z_NA => -- CF or ZF
         match EFLAGS (Z_CF), EFLAGS (Z_ZF)
         {
            case Some (true), _ => true
            case _, Some (true) => true
            case Some (false), Some (false) => false
            case _ => #BadFlagAccess("read_cond: " : [c])
         }
      case Z_S  => SF
      case Z_NS => not SF
      case Z_P  => PF
      case Z_NP => not PF
      case Z_L  => SF != OF
      case Z_NL => SF == OF
      case Z_G  => -- not ZF and SF == OF
         match EFLAGS (Z_SF), EFLAGS (Z_OF)
         {
            case Some (a), Some (b) => a == b and not ZF
            case _ =>
               match EFLAGS (Z_ZF)
               {
                  case Some (true) => false
                  case _ => #BadFlagAccess("read_cond: " : [c])
               }
         }
      case Z_NG => -- ZF or SF != OF
         match EFLAGS (Z_SF), EFLAGS (Z_OF)
         {
            case Some (a), Some (b) => a != b or ZF
            case _ =>
               match EFLAGS (Z_ZF)
               {
                  case Some (true) => true
                  case _ => #BadFlagAccess("read_cond: " : [c])
               }
         }
      case Z_ALWAYS => true
   }

-- Stack operations

qword x64_pop_aux =
{
   rsp = REG (RSP);
   top = mem64 (rsp);
   REG (RSP) <- rsp + 8;
   return top
}

unit x64_pop (rm :: Zrm) = EA (ea_Zrm (Z64, rm)) <- x64_pop_aux

unit x64_pop_rip = RIP <- x64_pop_aux

unit x64_push_aux (w :: qword) =
{
   rsp = REG (RSP) - 8;
   REG (RSP) <- rsp;
   mem64 (rsp) <- w
}

unit x64_push (imm_rm :: Zimm_rm) = x64_push_aux (EA (ea_Zimm_rm (Z64, imm_rm)))

unit x64_push_rip = x64_push_aux (RIP)

unit x64_drop (imm :: qword) =
{
   when imm<7:0> != 0 do #FAIL ("x64_drop");
   REG (RSP) <- REG (RSP) + imm
}

---------------------------------------------------------------------------

-- =====================
-- Operational Semantics
-- =====================

define Zbinop (bop :: Zbinop_name, size :: Zsize, dst_src :: Zdest_src) =
{
   ea, val_dst, val_src = read_dest_src_ea (size, dst_src);
   write_binop (size, bop, val_dst, val_src, ea)
}

define Zcall (imm_rm :: Zimm_rm) =
{
   x64_push_rip;
   jump_to_ea (ea_Zimm_rm (Z64, imm_rm))
}

define Zcmpxchg (size :: Zsize, rm :: Zrm, r :: Zreg) =
{
   ea_src = Zea_r (size, r);
   ea_acc = Zea_r (size, RAX);
   ea_dst = ea_Zrm (size, rm);
   val_dst = EA (ea_dst);
   acc = EA (ea_src);
   write_binop (size, Zcmp, acc, val_dst, ea_src);
   if acc == val_dst
      then EA (ea_dst) <- EA (ea_src)
   else EA (ea_acc) <- val_dst
}

define Zcpuid =
{
   ICACHE <- MEM;
   REG (RAX) <- UNKNOWN;
   REG (RBX) <- UNKNOWN;
   REG (RCX) <- UNKNOWN;
   REG (RDX) <- UNKNOWN
}

define Zdiv (size :: Zsize, rm :: Zrm) =
{
   w = value_width (size);
   ea_eax = Zea_r (size, RAX);
   ea_edx = Zea_r (size, RAX);
   n = [EA (ea_eax)] * w + [EA (ea_edx)] :: nat;
   d = [EA (ea_Zrm (size, rm))] :: nat;
   q = n div d;
   r = n mod d;
   when d == 0 or w <= q do #FAIL ("division");
   EA (ea_eax) <- [q];
   EA (ea_edx) <- [r];
   erase_eflags
}

-- includes jmp rel, i.e. unconditional relative jumps.
define Zjcc (cond :: Zcond, imm :: qword) =
   when read_cond (cond) do RIP <- RIP + imm

-- jmp excludes relative jumps, see jcc.
define Zjmp (rm :: Zrm) = RIP <- EA (ea_Zrm (Z64, rm))

define Zlea (size :: Zsize, dst_src :: Zdest_src) =
{
   ea_src = ea_Zsrc (size, dst_src);
   ea_dst = ea_Zdest (size, dst_src);
   EA (ea_dst) <- get_ea_address (ea_src)
}

define Zloop (cond :: Zcond, imm :: qword) =
{
   ecx1 = REG (RCX) - 1;
   REG (RCX) <- ecx1;
   when ecx1 != 0 and read_cond (cond) do RIP <- RIP + imm
}

define Zmonop (mop :: Zmonop_name, size :: Zsize, rm :: Zrm) =
{
   ea = ea_Zrm (size, rm);
   write_monop (size, mop, EA (ea), ea)
}

define Zmov (cond :: Zcond, size :: Zsize, dst_src :: Zdest_src) =
   when read_cond (cond) do
   {
      ea_src = ea_Zsrc (size, dst_src);
      ea_dst = ea_Zdest (size, dst_src);
      EA (ea_dst) <- EA (ea_src)
   }

define Zmovzx (size1 :: Zsize, dst_src :: Zdest_src, size2 :: Zsize) =
   EA (ea_Zdest (size2, dst_src)) <- EA (ea_Zsrc (size1, dst_src))

define Zmul (size :: Zsize, rm :: Zrm) =
{
   ea_eax = Zea_r (size, RAX);
   eax = EA (ea_eax);
   val_src = EA (ea_Zrm (size, rm));
   match size
   {
      case Z8 (_) => EA (Zea_r (Z16, RAX)) <- eax * val_src
      case _ =>
      {
         EA (ea_eax) <- eax * val_src;
         ea_edx = Zea_r (size, RDX);
         EA (ea_edx) <- [([eax] * [val_src] :: nat) div value_width (size)]
      }
   };
   erase_eflags  -- over appoximation
}

define Znop = ()

define Zpop (rm :: Zrm) = x64_pop (rm)

define Zpush (imm_rm :: Zimm_rm) = x64_push (imm_rm)

define Zret (imm :: qword) =
{
   x64_pop_rip;
   x64_drop (imm)
}

define Zxadd (size :: Zsize, rm :: Zrm, r :: Zreg) =
{
   ea_src = Zea_r (size, r);
   ea_dst = ea_Zrm (size, rm);
   val_src = EA (ea_src);
   val_dst = EA (ea_dst);
   EA (ea_src) <- val_dst;
   write_binop (size, Zadd, val_src, val_dst, ea_dst)
}

define Zxchg (size :: Zsize, rm :: Zrm, r :: Zreg) =
{
   ea_src = Zea_r (size, r);
   ea_dst = ea_Zrm (size, rm);
   val_src = EA (ea_src);
   val_dst = EA (ea_dst);
   EA (ea_src) <- val_dst;
   EA (ea_dst) <- val_src
}

define Run

---------------------------------------------------------------------------

-- ====================
-- Instruction Decoding
-- ====================

construct Zinst
{
  Zfull_inst :: stream * instruction * stream
  Zdec_fail  :: string
}

-- Parse immediates

qword * stream immediate8 (strm :: stream) =
   match strm
   {  case Cons (b, t) => SignExtend (b), t
      case _ => UNKNOWN
   }

qword * stream immediate16 (strm :: stream) =
   match strm {
      case Cons (b1, Cons (b2, t)) => SignExtend (b2 : b1 ), t
      case _ => UNKNOWN
   }

qword * stream immediate32 (strm :: stream) =
   match strm {
      case Cons (b1, Cons (b2, (Cons (b3, Cons (b4, t))))) =>
        SignExtend (b4 : b3 : b2 : b1), t
      case _ => UNKNOWN
   }

qword * stream immediate64 (strm :: stream) =
   match strm {
      case Cons (b1, Cons (b2, (Cons (b3, Cons (b4,
           Cons (b5, Cons (b6, (Cons (b7, Cons (b8, t)))))))))) =>
        (b8 : b7 : b6 : b5 : b4 : b3 : b2 : b1), t
      case _ => UNKNOWN
   }

qword * stream immediate (size :: Zsize, strm :: stream) =
   match size
   {
      case Z8 (_) => immediate8 (strm)
      case Z16    => immediate16 (strm)
      case _      => immediate32 (strm)
   }

qword * stream full_immediate (size :: Zsize, strm :: stream) =
 ( if size == Z64 then immediate64 (strm) else immediate (size, strm) )

---------------------------------------------------------------------------

-- Parse the ModRM and SIB bytes

register REX :: bits(4) { 3:W, 2:R, 1:X, 0:B }

Zreg RexReg (b :: bool, r :: bits(3)) = [[b]`1 : r]

qword * stream readDisplacement (Mod :: bits(2), strm :: stream) =
   if Mod == 1
      then immediate8 (strm)
   else if Mod == 2
      then immediate32 (strm)
   else (0, strm)

qword * stream readSibDisplacement (Mod :: bits(2), strm :: stream) =
   if Mod == 0
      then (0, strm)
   else if Mod == 1
      then immediate8 (strm)
   else immediate32 (strm)

Zrm * stream readSIB (REX :: REX, Mod :: bits(2), strm :: stream) =
   match strm
   {  case Cons ('SS Index Base', strm1) =>
         { base = RexReg (REX.B, Base);
           index = RexReg (REX.X, Index);
           scaled_index = if index == RSP then None else Some (SS, index);
           if base == RBP
              then {  displacement, strm2 = readSibDisplacement (Mod, strm1);
                      base = if Mod == 0 then ZnoBase else ZregBase (base);
                      return (Zm (scaled_index, base, displacement), strm2)
                   }
           else
           {  displacement, strm2 = readDisplacement (Mod, strm1);
              return (Zm (scaled_index, ZregBase (base), displacement), strm2)
           }
         }
      case _ => return (UNKNOWN, strm)
   }

Zreg * Zrm * stream readModRM (REX :: REX, strm :: stream) =
   match strm {
     case Cons ('00 RegOpc 101', strm1) =>
       { displacement, strm2 = immediate32 (strm1);
         return
            (RexReg (REX.R, RegOpc), Zm (None, ZripBase, displacement), strm2)
       }
     case Cons ('11 REG RM', strm1) =>
         return (RexReg (REX.R, REG), Zr (RexReg (REX.B, RM)), strm1)
     case Cons ('Mod RegOpc 100', strm1) =>
       { sib, strm2 = readSIB (REX, Mod, strm1);
         return (RexReg (REX.R, RegOpc), sib, strm2)
       }
     case Cons ('Mod RegOpc RM', strm1) =>
       { displacement, strm2 = readDisplacement (Mod, strm1);
         return
            (RexReg (REX.R, RegOpc),
             Zm (None, ZregBase (RexReg (REX.B, RM)), displacement),
             strm2)
       }
     case _ => return (UNKNOWN, UNKNOWN, strm)
   }

bits(3) * Zrm * stream readOpcodeModRM (REX :: REX, strm :: stream) =
{  opcode, rm, strm1 = readModRM (REX, strm);
   return ([[opcode] mod 0n8], rm, strm1)
}

---------------------------------------------------------------------------

-- Parse Prefixes

nat prefixGroup (b :: byte) =
   match b
   { case 0xF0 or 0xF2 or 0xF3 => 1
     case 0x26 or 0x2E or 0x36 or 0x3E or 0x64 or 0x65 => 2
     case 0x66 => 3
     case 0x67 => 4
     case _ => if b<7:4> == '0100' then 5 else 0
   }

(stream * bool * REX * stream) option
   readPrefix (s :: nat set, p :: stream, strm :: stream) =
   match strm
   {  case Cons (h, strm1) =>
         {  group = prefixGroup (h);
            if group == 0
               then Some (p, false, REX ('0000'), strm)
            else if group == 5
               then Some (p, true, REX (h<3:0>), strm1)
            else if group in s
               then None
            else readPrefix (group insert s, Cons (h, p), strm1)
         }
     case Nil => Some (p, false, UNKNOWN, strm)
   }

(stream * bool * REX * stream) option readPrefixes (strm :: stream) =
   readPrefix (set {}, Nil, strm)

---------------------------------------------------------------------------

-- Operand Size

-- w from REX.W
-- v from opcode
-- override from 0x66 prefix

-- r/m8, imm8        not v
-- r/m16, imm16      override and not w and v
-- r/m32, imm32      not W and v
-- r/m64, imm32      w and v

Zsize OpSize (have_rex :: bool, w :: bool, v :: bits(1), override :: bool) =
   ( if v == 0
        then Z8 (have_rex)
     else if w
        then Z64
     else if override
        then Z16
     else Z32 )

---------------------------------------------------------------------------

-- Tests

bool isZm (rm :: Zrm) =
   match rm {
     case Zm (_) => true
     case _ => false
   }

---------------------------------------------------------------------------

-- The decoder

Zinst x64_decode (strm :: stream) =
match readPrefixes (strm)
{ case None => Zdec_fail ("Bad prefix")
  case Some (p, have_rex, REX, strm1) =>
  { op_size_override = 0x66 in SetOfList(p);
    if REX.W and op_size_override
       then Zdec_fail ("REX.W together with override prefix")
    else
       match strm1
       { -- Binop (ADD..CMP)
         -- ADD r/mX, rX
         -- ADD rX, r/mX
         case Cons ('00 opc 0 x v', strm2) =>
            { reg, rm, strm3 = readModRM (REX, strm2);
              size = OpSize (have_rex, REX.W, v, op_size_override);
              binop = [opc] :: Zbinop_name;
              src_dst = if x == 0`1 then Zrm_r (rm, reg) else Zr_rm (reg, rm);
              Zfull_inst (p, Zbinop (binop, size, src_dst), strm3)
            }

         -- Binop (ADD..CMP)
         -- ADD EAX, immX
         case Cons ('00 opc 1 0 v', strm2) =>
            { size = OpSize (have_rex, REX.W, v, op_size_override);
              imm, strm3 = immediate (size, strm2);
              Zfull_inst (p, Zbinop ([opc], size, Zrm_i (Zr (RAX), imm)), strm3)
            }

         -- PUSH r/mX
         -- POP r/mX
         case Cons ('0x5 b r', strm2) =>
            { reg = Zr ([[REX.B] : r]);
              Zfull_inst
                (p, (if b == 0`1 then Zpush (Zrm (reg)) else Zpop (reg)), strm2)
            }

         -- PUSH immX
         case Cons ('0x6 10 b 0', strm2) =>
            { imm, strm3 =
                if b == 1 then immediate8 (strm2) else immediate32 (strm2);
              Zfull_inst (p, Zpush (Zimm (imm)), strm3)
            }

         -- Jcc rel8
         case Cons ('0x7 c', strm2) =>
            { imm, strm3 = immediate8 (strm2);
              Zfull_inst (p, Zjcc ([c], imm), strm3)
            }

         -- Immediate Group 1 (ADD..CMP)
         -- ADD r/mX, immX
         case Cons ('0x8 000 v', strm2) =>
            { size = OpSize (have_rex, REX.W, v, op_size_override);
              opcode, rm, strm3 = readOpcodeModRM (REX, strm2);
              imm, strm4 = immediate (size, strm3);
              binop = [opcode] :: Zbinop_name;
              Zfull_inst (p, Zbinop (binop, size, Zrm_i (rm, imm)), strm4)
            }
         -- ADD r/mX, imm8
         case Cons (0x83, strm2) =>
            { size = OpSize (false, REX.W, 1, op_size_override);
              opcode, rm, strm3 = readOpcodeModRM (REX, strm2);
              imm, strm4 = immediate8 (strm3);
              binop = [opcode] :: Zbinop_name;
              Zfull_inst (p, Zbinop (binop, size, Zrm_i (rm, imm)), strm4)
            }

         -- TEST r/mX, rX
         case Cons ('0x8 010 v', strm2) =>
            { size = OpSize (have_rex, REX.W, v, op_size_override);
              reg, rm, strm3 = readModRM (REX, strm2);
              Zfull_inst (p, Zbinop (Ztest, size, Zrm_r (rm, reg)), strm3)
            }

         -- XCHG r/mX, rX
         case Cons ('0x8 011 v', strm2) =>
            { size = OpSize (have_rex, REX.W, v, op_size_override);
              reg, rm, strm3 = readModRM (REX, strm2);
              Zfull_inst (p, Zxchg (size, rm, reg), strm3)
            }

         -- MOV r/mX, rX
         -- MOV rX, r/mX
         case Cons ('0x8 10 x v', strm2) =>
            { reg, rm, strm3 = readModRM (REX, strm2);
              size = OpSize (have_rex, REX.W, v, op_size_override);
              src_dst = if x == 0`1 then Zrm_r (rm, reg) else Zr_rm (reg, rm);
              Zfull_inst (p, Zmov (Z_ALWAYS, size, src_dst), strm3)
            }

         -- LEA r/mX, m
         case Cons ('0x8D', strm2) =>
            { size = OpSize (true, REX.W, 1, op_size_override);
              reg, rm, strm3 = readModRM (REX, strm2);
              if isZm (rm)
                 then Zfull_inst (p, Zlea (size, Zr_rm (reg, rm)), strm3)
              else Zdec_fail ("LEA with register argument")
            }

         -- Unary Group 1a
         case Cons ('0x8F', strm2) =>
            { opcode, rm, strm3 = readOpcodeModRM (REX, strm2);
              if opcode == 0
                 then Zfull_inst (p, Zpop (rm), strm3)
              else Zdec_fail ("Unsupported opcode: Group 1a")
            }

         -- XCHG EAX, rX
         case Cons ('0x9 0 r', strm2) =>
            { size = OpSize (true, REX.W, 1, op_size_override);
              reg = RexReg (REX.B, r);
              if reg == RAX
                 then Zfull_inst (p, Znop, strm2)
              else Zfull_inst (p, Zxchg (size, Zr (RAX), reg), strm2)
            }

         -- TEST EAX, immX
         case Cons ('0xA 100 v', strm2) =>
            { size = OpSize (true, REX.W, v, op_size_override);
              imm, strm3 = immediate (size, strm2);
              Zfull_inst (p, Zbinop (Ztest, size, Zrm_i (Zr (RAX), imm)), strm3)
            }

         -- MOV rX, immX
         case Cons ('0xB v r', strm2) =>
            { size = OpSize (have_rex, REX.W, v, op_size_override);
              imm, strm3 = full_immediate (size, strm2);
              reg = [[REX.B] : r] :: Zreg;
              Zfull_inst
                 (p, Zmov (Z_ALWAYS, size, Zrm_i (Zr (reg), imm)), strm3)
            }

         -- Shift Group 2
         case Cons ('0xC 000 v', strm2) =>
            { size = OpSize (have_rex, REX.W, v, op_size_override);
              opcode, rm, strm3 = readOpcodeModRM (REX, strm2);
              imm, strm4 = immediate8 (strm3);
              binop = [[opcode] + 0n8] :: Zbinop_name;
              if opcode == '110'
                 then Zdec_fail ("Unsupported opcode: Shift Group 2")
              else Zfull_inst (p, Zbinop (binop, size, Zrm_i (rm, imm)), strm4)
            }

         -- RETN
         -- RETN imm16
         case Cons ('0xC 001 v', strm2) =>
            if v == 0
               then { imm, strm3 = immediate16 (strm2);
                      Zfull_inst (p, Zret (imm), strm3)
                    }
            else Zfull_inst (p, Zret (0), strm2)

         -- Group 11
         case Cons ('0xC 011 v', strm2) =>
            { size = OpSize (have_rex, REX.W, v, op_size_override);
              opcode, rm, strm3 = readOpcodeModRM (REX, strm2);
              imm, strm4 = immediate (size, strm3);
              if opcode == '000'
                 then -- MOV r/mX, immX
                      Zfull_inst
                         (p, Zmov (Z_ALWAYS, size, Zrm_i (rm, imm)), strm4)
              else Zdec_fail ("Unsupported opcode: Group 11")
            }

         -- Shift Group 2
         case Cons ('0xD 00 b v', strm2) =>
            { size = OpSize (have_rex, REX.W, v, op_size_override);
              opcode, rm, strm3 = readOpcodeModRM (REX, strm2);
              shift = if b == 0`1 then Zrm_i (rm, 1) else Zrm_r (rm, RCX);
              binop = [[opcode] + 0n8] :: Zbinop_name;
              if opcode == '110'
                 then Zdec_fail ("Unsupported opcode: Shift Group 2")
              else Zfull_inst (p, Zbinop (binop, size, shift), strm3)
            }

         -- LOOPE rel8
         -- LOOPNE rel8
         case Cons ('0xE 000 b', strm2) =>
            { imm, strm3 = immediate8 (strm2);
              cond = if b == 0 then Z_NE else Z_E;
              Zfull_inst (p, Zloop (cond, imm), strm3)
            }

         -- LOOP rel8
         case Cons ('0xE2', strm2) =>
            { imm, strm3 = immediate8 (strm2);
              Zfull_inst (p, Zloop (Z_ALWAYS, imm), strm3)
            }

         -- CALL rel32
         case Cons ('0xE8', strm2) =>
            { imm, strm3 = immediate32 (strm2);
              Zfull_inst (p, Zcall (Zimm (imm)), strm3)
            }

         -- JMP rel8
         -- JMP rel32
         case Cons ('0xE 10 b 1', strm2) =>
            { imm, strm3 =
                if b == 0 then immediate32 (strm2) else immediate8 (strm2);
              Zfull_inst (p, Zjcc (Z_ALWAYS, imm), strm3)
            }

         -- Unary Group 3
         case Cons ('0xF 011 v', strm2) =>
            { size = OpSize (have_rex, REX.W, v, op_size_override);
              opcode, rm, strm3 = readOpcodeModRM (REX, strm2);
              match opcode
              {  -- TEST r/mX, immX
                 case '000' =>
                  { imm, strm4 = immediate (size, strm3);
                    Zfull_inst (p, Zbinop (Ztest, size, Zrm_i (rm, imm)), strm4)
                  }

                 -- NOT r/mX
                 case '010' =>
                    Zfull_inst (p, Zmonop (Znot, size, rm), strm3)

                 -- NEG r/mX
                 case '011' =>
                    Zfull_inst (p, Zmonop (Zneg, size, rm), strm3)

                 -- MUL r/mX
                 case '100' =>
                    Zfull_inst (p, Zmul (size, rm), strm3)

                 -- DIV r/mX
                 case '110' =>
                    Zfull_inst (p, Zdiv (size, rm), strm3)

                 case _ => Zdec_fail ("Unsupported opcode: Unary Group 3")
              }
            }

         -- INC/DEC Group 4
         case Cons (0xFE, strm2) =>
            { opcode, rm, strm3 = readOpcodeModRM (REX, strm2);
               if opcode == '000'
                  then Zfull_inst (p, Zmonop (Zinc, Z8 (have_rex), rm), strm3)
               else if opcode == '001'
                  then Zfull_inst (p, Zmonop (Zdec, Z8 (have_rex), rm), strm3)
               else Zdec_fail ("Unsupported opcode: INC/DEC Group 4")
            }

         -- INC/DEC Group 5
         case Cons (0xFF, strm2) =>
            { size = OpSize (have_rex, REX.W, 1, op_size_override);
              opcode, rm, strm3 = readOpcodeModRM (REX, strm2);
              match opcode
              {  -- INC r/mX
                 case '000' =>
                    Zfull_inst (p, Zmonop (Zinc, size, rm), strm3)
                 -- DEC rm/X
                 case '001' =>
                    Zfull_inst (p, Zmonop (Zdec, size, rm), strm3)
                 -- CALL rm/X
                 case '010' =>
                    Zfull_inst (p, Zcall (Zrm (rm)), strm3)
                 -- JMP rm/X
                 case '100' =>
                    Zfull_inst (p, Zjmp (rm), strm3)
                 -- PUSH rm/X
                 case '110' =>
                    Zfull_inst (p, Zpush (Zrm (rm)), strm3)
                 case _ => Zdec_fail ("Unsupported opcode: INC/DEC Group 5")
              }
            }

         -- Three byte opcodes
         case Cons (0x0F, Cons (0x38, Cons (opc, _))) =>
            Zdec_fail ("Unsupported opcode: 0F 38 " : [opc])
         case Cons (0x0F, Cons (0x3A, Cons (opc, _))) =>
            Zdec_fail ("Unsupported opcode: 0F 3A " : [opc])

         -- Two byte opcodes
         case Cons (0x0F, Cons (opc, strm2)) =>
            match opc
            {  -- CMOVcc rX, r/mX
               case '0x4 c' =>
               {  size = OpSize (true, REX.W, 1, op_size_override);
                  reg, rm, strm3 = readModRM (REX, strm2);
                  Zfull_inst (p, Zmov ([c], size, Zr_rm (reg, rm)), strm3)
               }

               -- Jcc rel32
               case '0x8 c' =>
               {  imm, strm3 = immediate32 (strm2);
                  Zfull_inst (p, Zjcc ([c], imm), strm3)
               }

               -- CPUID
               case 0xA2 => Zfull_inst (p, Zcpuid, strm2)

               -- CMPXCHG r/mX, rX
               case '0xB 000 v' =>
               {  size = OpSize (have_rex, REX.W, v, op_size_override);
                  reg, rm, strm3 = readModRM (REX, strm2);
                  Zfull_inst (p, Zcmpxchg (size, rm, reg), strm3)
               }

               -- XADD r/mX, rX
               case '0xC 000 v' =>
               {  size = OpSize (have_rex, REX.W, v, op_size_override);
                  reg, rm, strm3 = readModRM (REX, strm2);
                  Zfull_inst (p, Zxadd (size, rm, reg), strm3)
               }

               -- MOVZX rX, r/m8
               -- MOVZX rX, r/m16
               case '0xB 011 v' =>
               {  size = OpSize (have_rex, REX.W, 1, op_size_override);
                  size2 = if v == 1 then Z16 else Z8 (have_rex);
                  reg, rm, strm3 = readModRM (REX, strm2);
                  Zfull_inst (p, Zmovzx (size, Zr_rm (reg, rm), size2), strm3)
               }
              case _ => Zdec_fail ("Unsupported opcode: 0F " : [opc])
            }

         -- Unsupported
         case Cons (opc, _) =>
            Zdec_fail ("Unsupported opcode: " : [opc])

         case Nil => Zdec_fail ("No opcode")
       }
  }
}

---------------------------------------------------------------------------

-- ===================
-- Next State Function
-- ===================

stream x64_fetch =
{
  var strm = Nil;
  for i in 19 .. 0 do strm <- Cons (ValOf (MEM (RIP + [i])), strm);
  return strm
}

unit checkIcache (n :: nat) =
   for i in 0 .. n - 1 do
   {
      addr = RIP + [i];
      when MEM (addr) != ICACHE (addr) do #FAIL ("icache miss")
   }

unit x64_next =
   match x64_decode (x64_fetch)
   {
      case Zfull_inst (_, i, strm1) =>
        {
           len = 20 - Length (strm1);
           checkIcache (len);
           RIP <- RIP + [len];
           Run (i)
        }
      case Zdec_fail (s) => #FAIL (s)
   }

---------------------------------------------------------------------------
