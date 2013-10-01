---------------------------------------------------------------------------
-- Model of the 64-bit MIPS ISA (R4000)
---------------------------------------------------------------------------

type CCA   = bits(3)
type reg   = bits(5)
type byte  = bits(8)
type word  = bits(32)
type dword = bits(64)
type vAddr = bits(64)
type pAddr = bits(64)

exception UNPREDICTABLE :: string

--------------------------------------------------
-- Coprocessor 0 registers
--------------------------------------------------

register StatusRegister :: word
{
   26 : RE        -- Reverse endianness
   22 : BEV       -- Controls location of exception vectors
    9 : IM1       -- Interrupt mask
    8 : IM0       -- Interrupt mask
  4-3 : KSU       -- Operating mode
    2 : ERL       -- Error level
    1 : EXL       -- Exception level
    0 : IE        -- Interrupt enable
}

register ConfigRegister :: word
{
   15 : BE        -- Big endian
}

register CauseRegister :: word
{
   6-2 : ExcCode  -- Exception code
}

record CP0
{
-- Index    :: word            -- 0   Index to TLB array
-- Random   :: word            -- 1   Pseudorandom pointer to TLB array
-- EntryLo0 :: word            -- 2   Low half of TLB entry for even VPN
-- EntryLo1 :: word            -- 3   Low half of TLB entry for odd VPN
-- Context  :: word            -- 4   Kernel virtual page table entry (PTE)
-- PageMask :: word            -- 5   TLB page mask
-- Wired    :: word            -- 6   Number of wired TLB entries
-- HWREna   :: word            -- 7   See RDHWR instruction
-- BadVAddr :: word            -- 8   Bad virtual address
   Count    :: word            -- 9   Timer count
-- EntryHi  :: word            -- 10  High half of TLB entry
-- Compare  :: word            -- 11  Timer compare
   Status   :: StatusRegister  -- 12  Status register
   Cause    :: CauseRegister   -- 13  Cause of last exception
   EPC      :: dword           -- 14  Exception program counter
-- PRId     :: word            -- 15  Processor revision identifier
   Config   :: ConfigRegister  -- 16  Configuration register
-- LLAddr   :: word            -- 17  Load linked address
-- WatchLo  :: word            -- 18  Memory reference trap address low bits
-- WatchHi  :: word            -- 19  Memory reference trap address high bits
-- XContext :: word            -- 20  PTE entry in 64-bit mode
-- Reserved                    -- 21
-- Implementation dependent    -- 22
-- Debug    :: word            -- 23  EJTAG Debug register
-- DEPC     :: word            -- 24  Program counter EJTAG debug exception
-- PerfCnt  :: word            -- 25  Performance counter interface
-- ECC      :: word            -- 26  Second cache error checking and correcting
-- CacheErr :: word            -- 27  Cache error and status register
-- TagLo    :: word            -- 28  Cache tage register
-- TagHi    :: word            -- 29  Cache tage register
   ErrorEPC :: dword           -- 30  Error exception program counter
-- KScratch :: word            -- 31  Scratch Registers for Kernel Mode
}

construct HLStatus { HLarith, HLok, HLmthi, HLmtlo }

--================================================
-- The state space
--================================================

declare
{
   gpr          :: reg -> dword   -- general purpose registers
   PC           :: dword          -- the program counter
   HI           :: dword          -- multiply and divide register high result
   LO           :: dword          -- multiply and divide register low result
   HLStatus     :: HLStatus       -- status of the HI and LO registers
   CP0          :: CP0            -- CP0 registers
   MEM          :: vAddr -> byte  -- memory
   BranchStatus :: dword option   -- Branch to be taken after instruction
   LLbit        :: bool option    -- Load link flag
}

--------------------------------------------------
-- Gereral purpose register access
--------------------------------------------------

component GPR (n::reg) :: dword
{
   value = if n == 0 then 0 else gpr(n)
   assign value = when n <> 0 do gpr(n) <- value
}

--------------------------------------------------
-- CP0 register access
--------------------------------------------------

component CPR (n::nat, reg::bits(5), sel::bits(3)) :: dword
{
   value =
      match n, reg, sel
      {
         case 0,  9, 0 => [CP0.Count]
         case 0, 12, 0 => [CP0.&Status]
         case 0, 13, 0 => [CP0.&Cause]
         case 0, 14, 0 =>  CP0.EPC
         case 0, 16, 0 => [CP0.&Config]
         case 0, 30, 0 =>  CP0.ErrorEPC
         case _ => UNKNOWN
      }
   assign value =
      match n, reg, sel
      {
         case 0,  9, 0 => CP0.Count    <- value<31:0>
         case 0, 12, 0 => CP0.&Status  <- value<31:0>
         case 0, 13, 0 => CP0.&Cause   <- value<31:0>
         case 0, 14, 0 => CP0.EPC      <- value
         case 0, 16, 0 => CP0.&Config  <- value<31:0>
         case 0, 30, 0 => CP0.ErrorEPC <- value
         case _ => nothing
      }
}

--------------------------------------------------
-- Memory access
--------------------------------------------------

construct IorD  { INSTRUCTION, DATA }
construct LorS  { LOAD, STORE }

bits(3) BYTE       = 0`3
bits(3) HALFWORD   = 1`3
bits(3) WORD       = 3`3
bits(3) DOUBLEWORD = 7`3

nat PSIZE = 64 -- 64-bit physical memory

bool UserMode =
   CP0.Status.KSU == '10' and not CP0.Status.EXL and not CP0.Status.ERL

bool BigEndianMem = CP0.Config.BE
bits(1) ReverseEndian = [CP0.Status.RE and UserMode]
bits(1) BigEndianCPU  = [BigEndianMem] ?? ReverseEndian

pAddr * CCA AddressTranslation (vAddr::vAddr, IorD::IorD, LorS::LorS) =
   return (vAddr, UNKNOWN) -- null address translation

dword LoadMemory (CCA::CCA, AccessLength::bits(3),
                  pAddr::pAddr, vAddr::vAddr, IorD::IorD) =
{
   a = pAddr && ~0b111; -- align to 64-bit word
   if BigEndianCPU == '1' then
      MEM(a) :
      MEM(a + 1) :
      MEM(a + 2) :
      MEM(a + 3) :
      MEM(a + 4) :
      MEM(a + 5) :
      MEM(a + 6) :
      MEM(a + 7)
   else
      MEM(a + 7) :
      MEM(a + 6) :
      MEM(a + 5) :
      MEM(a + 4) :
      MEM(a + 3) :
      MEM(a + 2) :
      MEM(a + 1) :
      MEM(a)
}

unit StoreMemory (CCA::CCA, AccessLength::bits(3), MemElem::dword,
                  pAddr::pAddr, vAddr::vAddr, IorD::IorD) =
{  a = pAddr && ~0b111; -- align to 64-bit word
   l = vAddr<2:0>;
   h = l + AccessLength;
   if BigEndianCPU == '1' then
   {
      when l == 0              do MEM(a)     <- MemElem<63:56>;
      when l <=+ 1 and 1 <=+ h do MEM(a + 1) <- MemElem<55:48>;
      when l <=+ 2 and 2 <=+ h do MEM(a + 2) <- MemElem<47:40>;
      when l <=+ 3 and 3 <=+ h do MEM(a + 3) <- MemElem<39:32>;
      when l <=+ 4 and 4 <=+ h do MEM(a + 4) <- MemElem<31:24>;
      when l <=+ 5 and 5 <=+ h do MEM(a + 5) <- MemElem<23:16>;
      when l <=+ 6 and 6 <=+ h do MEM(a + 6) <- MemElem<15:8>;
      when l <=+ 7 and 7 <=+ h do MEM(a + 7) <- MemElem<7:0>
   }
   else
   {
      when l <=+ 7 and 7 <=+ h do MEM(a + 7) <- MemElem<63:56>;
      when l <=+ 6 and 6 <=+ h do MEM(a + 6) <- MemElem<55:48>;
      when l <=+ 5 and 5 <=+ h do MEM(a + 5) <- MemElem<47:40>;
      when l <=+ 4 and 4 <=+ h do MEM(a + 4) <- MemElem<39:32>;
      when l <=+ 3 and 3 <=+ h do MEM(a + 3) <- MemElem<31:24>;
      when l <=+ 2 and 2 <=+ h do MEM(a + 2) <- MemElem<23:16>;
      when l <=+ 1 and 1 <=+ h do MEM(a + 1) <- MemElem<15:8>;
      when l == 0              do MEM(a)     <- MemElem<7:0>
   }
}

--------------------------------------------------
-- Exceptions
--------------------------------------------------

construct ExceptionType { AdEL, AdES, Sys, Bp, RI, Ov, Tr }

bits(5) ExceptionCode (ExceptionType::ExceptionType) =
   match ExceptionType
   {
      case AdEL => 0x04 -- Address error (load)
      case AdES => 0x05 -- Address error (store)
      case Sys  => 0x08 -- Syscall
      case Bp   => 0x09 -- Breakpoint
      case RI   => 0x0a -- Reserved instruction
      case Ov   => 0x0c -- Arithmetic overflow
      case Tr   => 0x0d -- Trap
   }

unit SignalException (ExceptionType::ExceptionType) =
{
   when not CP0.Status.EXL do CP0.EPC <- PC;
   vectorOffset = 0x180`30;
   CP0.Cause.ExcCode <- ExceptionCode (ExceptionType);
   CP0.Status.EXL <- true;
   vectorBase = if CP0.Status.BEV then
                   0xFFFF_FFFF_BFC0_0200`64
                else
                   0xFFFF_FFFF_8000_0000;
   PC <- vectorBase<63:30> : (vectorBase<29:0> + vectorOffset)
}

--================================================
-- Instructions
--================================================

bool NotWordValue(value::dword) =
{  top = value<63:32>;
   if value<31> then
      top <> 0xFFFF_FFFF
   else
      top <> 0x0
}

-----------------------------------
-- ADDI rt, rs, immediate
-----------------------------------
define ArithI > ADDI (rs::reg, rt::reg, immediate::bits(16)) =
{
   when NotWordValue (GPR(rs)) do #UNPREDICTABLE("ADDI: NotWordValue");
   temp = GPR(rs)<32:0> + SignExtend (immediate);
   if temp<32> <> temp<31> then
      SignalException (Ov)
   else
      GPR(rt) <- SignExtend (temp<31:0>)
}

-----------------------------------
-- ADDIU rt, rs, immediate
-----------------------------------
define ArithI > ADDIU (rs::reg, rt::reg, immediate::bits(16)) =
{
   when NotWordValue (GPR(rs)) do #UNPREDICTABLE("ADDIU: NotWordValue");
   temp = GPR(rs)<31:0> + SignExtend (immediate);
   GPR(rt) <- SignExtend (temp)
}

-----------------------------------
-- DADDI rt, rs, immediate
-----------------------------------
define ArithI > DADDI (rs::reg, rt::reg, immediate::bits(16)) =
{
   temp`65 = SignExtend (GPR(rs)) + SignExtend (immediate);
   if temp<64> <> temp<63> then
      SignalException (Ov)
   else
      GPR(rt) <- temp<63:0>
}

-----------------------------------
-- DADDIU rt, rs, immediate
-----------------------------------
define ArithI > DADDIU (rs::reg, rt::reg, immediate::bits(16)) =
   GPR(rt) <- GPR(rs) + SignExtend (immediate)

-----------------------------------
-- SLTI rt, rs, immediate
-----------------------------------
define ArithI > SLTI (rs::reg, rt::reg, immediate::bits(16)) =
   GPR(rt) <- [GPR(rs) < SignExtend (immediate)]

-----------------------------------
-- SLTIU rt, rs, immediate
-----------------------------------
define ArithI > SLTIU (rs::reg, rt::reg, immediate::bits(16)) =
   GPR(rt) <- [GPR(rs) <+ SignExtend (immediate)]

-----------------------------------
-- ANDI rt, rs, immediate
-----------------------------------
define ArithI > ANDI (rs::reg, rt::reg, immediate::bits(16)) =
   GPR(rt) <- GPR(rs) && ZeroExtend (immediate)

-----------------------------------
-- ORI rt, rs, immediate
-----------------------------------
define ArithI > ORI (rs::reg, rt::reg, immediate::bits(16)) =
   GPR(rt) <- GPR(rs) || ZeroExtend (immediate)

-----------------------------------
-- XORI rt, rs, immediate
-----------------------------------
define ArithI > XORI (rs::reg, rt::reg, immediate::bits(16)) =
   GPR(rt) <- GPR(rs) ?? ZeroExtend (immediate)

-----------------------------------
-- LUI rt, immediate
-----------------------------------
define ArithI > LUI (rt::reg, immediate::bits(16)) =
   GPR(rt) <- SignExtend (immediate : 0`16)

-----------------------------------
-- ADD rd, rs, rt
-----------------------------------
define ArithR > ADD (rs::reg, rt::reg, rd::reg) =
{
   when NotWordValue (GPR(rs)) or NotWordValue (GPR(rt))
     do #UNPREDICTABLE("ADD: NotWordValue");
   temp = GPR(rs)<32:0> + GPR(rt)<32:0>;
   if temp<32> <> temp<31> then
      SignalException (Ov)
   else
      GPR(rd) <- SignExtend (temp<31:0>)
}

-----------------------------------
-- ADDU rd, rs, rt
-----------------------------------
define ArithR > ADDU (rs::reg, rt::reg, rd::reg) =
{
   when NotWordValue (GPR(rs)) or NotWordValue (GPR(rt))
     do #UNPREDICTABLE("ADDU: NotWordValue");
   temp = GPR(rs)<31:0> + GPR(rt)<31:0>;
   GPR(rd) <- SignExtend (temp)
}

-----------------------------------
-- SUB rd, rs, rt
-----------------------------------
define ArithR > SUB (rs::reg, rt::reg, rd::reg) =
{
   when NotWordValue (GPR(rs)) or NotWordValue (GPR(rt))
     do #UNPREDICTABLE("SUB: NotWordValue");
   temp = GPR(rs)<32:0> - GPR(rt)<32:0>;
   if temp<32> <> temp<31> then
      SignalException (Ov)
   else
      GPR(rd) <- SignExtend (temp<31:0>)
}

-----------------------------------
-- SUBU rd, rs, rt
-----------------------------------
define ArithR > SUBU (rs::reg, rt::reg, rd::reg) =
{
   when NotWordValue (GPR(rs)) or NotWordValue (GPR(rt))
     do #UNPREDICTABLE("SUBU: NotWordValue");
   temp = GPR(rs)<32:0> - GPR(rt)<32:0>;
   GPR(rd) <- SignExtend (temp)
}

-----------------------------------
-- DADD rd, rs, rt
-----------------------------------
define ArithR > DADD (rs::reg, rt::reg, rd::reg) =
{
   temp`65 = SignExtend (GPR(rs)) + SignExtend (GPR(rt));
   if temp<64> <> temp<63> then
      SignalException (Ov)
   else
      GPR(rd) <- temp<63:0>
}

-----------------------------------
-- DADDU rd, rs, rt
-----------------------------------
define ArithR > DADDU (rs::reg, rt::reg, rd::reg) =
   GPR(rd) <- GPR(rs) + GPR(rt)

-----------------------------------
-- DSUB rd, rs, rt
-----------------------------------
define ArithR > DSUB (rs::reg, rt::reg, rd::reg) =
{
   temp`65 = SignExtend (GPR(rs)) - SignExtend (GPR(rt));
   if temp<64> <> temp<63> then
      SignalException (Ov)
   else
      GPR(rd) <- temp<63:0>
}

-----------------------------------
-- DSUBU rd, rs, rt
-----------------------------------
define ArithR > DSUBU (rs::reg, rt::reg, rd::reg) =
   GPR(rd) <- GPR(rs) - GPR(rt)

-----------------------------------
-- SLT rd, rs, rt
-----------------------------------
define ArithR > SLT (rs::reg, rt::reg, rd::reg) =
   GPR(rd) <- [GPR(rs) < GPR(rt)]

-----------------------------------
-- SLTU rd, rs, rt
-----------------------------------
define ArithR > SLTU (rs::reg, rt::reg, rd::reg) =
   GPR(rd) <- [GPR(rs) <+ GPR(rt)]

-----------------------------------
-- AND rd, rs, rt
-----------------------------------
define ArithR > AND (rs::reg, rt::reg, rd::reg) =
   GPR(rd) <- GPR(rs) && GPR(rt)

-----------------------------------
-- OR rd, rs, rt
-----------------------------------
define ArithR > OR (rs::reg, rt::reg, rd::reg) =
   GPR(rd) <- GPR(rs) || GPR(rt)

-----------------------------------
-- XOR rd, rs, rt
-----------------------------------
define ArithR > XOR (rs::reg, rt::reg, rd::reg) =
   GPR(rd) <- GPR(rs) ?? GPR(rt)

-----------------------------------
-- NOR rd, rs, rt
-----------------------------------
define ArithR > NOR (rs::reg, rt::reg, rd::reg) =
   GPR(rd) <- ~(GPR(rs) || GPR(rt))

-----------------------------------
-- MULT rs, rt
-----------------------------------
define MultDiv > MULT (rs::reg, rt::reg) =
{
   when NotWordValue (GPR(rs)) or NotWordValue (GPR(rt))
     do #UNPREDICTABLE("MULT: NotWordValue");
   prod`64 = SignExtend (GPR(rs)<31:0>) * SignExtend (GPR(rt)<31:0>);
   LO <- SignExtend (prod<31:0>);
   HI <- SignExtend (prod<63:32>);
   HLStatus <- HLarith
}

-----------------------------------
-- MULTU rs, rt
-----------------------------------
define MultDiv > MULTU (rs::reg, rt::reg) =
{
   when NotWordValue (GPR(rs)) or NotWordValue (GPR(rt))
     do #UNPREDICTABLE("MULTU: NotWordValue");
   prod`64 = ZeroExtend (GPR(rs)<31:0>) * ZeroExtend (GPR(rt)<31:0>);
   LO <- SignExtend (prod<31:0>);
   HI <- SignExtend (prod<63:32>);
   HLStatus <- HLarith
}

-----------------------------------
-- DMULT rs, rt
-----------------------------------
define MultDiv > DMULT (rs::reg, rt::reg) =
{
   prod`128 = SignExtend (GPR(rs)) * SignExtend (GPR(rt));
   LO <- prod<63:0>;
   HI <- prod<127:64>;
   HLStatus <- HLarith
}

-----------------------------------
-- DMULTU rs, rt
-----------------------------------
define MultDiv > DMULTU (rs::reg, rt::reg) =
{
   prod`128 = ZeroExtend (GPR(rs)) * ZeroExtend (GPR(rt));
   LO <- prod<63:0>;
   HI <- prod<127:64>;
   HLStatus <- HLarith
}

-----------------------------------
-- DIV rs, rt
-----------------------------------
define MultDiv > DIV (rs::reg, rt::reg) =
{
   when GPR(rt) == 0
     do #UNPREDICTABLE("DIV: divide by zero");
   when NotWordValue (GPR(rs)) or NotWordValue (GPR(rt))
     do #UNPREDICTABLE("DIV: NotWordValue");
   q = GPR(rs)<31:0> quot GPR(rt)<31:0>;
   LO <- SignExtend (q);
   r = GPR(rs)<31:0> rem GPR(rt)<31:0>;
   HI <- SignExtend (r);
   HLStatus <- HLarith
}

-----------------------------------
-- DIVU rs, rt
-----------------------------------
define MultDiv > DIVU (rs::reg, rt::reg) =
{
   when GPR(rt) == 0
     do #UNPREDICTABLE("DIVU: divide by zero");
   when NotWordValue (GPR(rs)) or NotWordValue (GPR(rt))
     do #UNPREDICTABLE("DIVU: NotWordValue");
   q = GPR(rs)<31:0> div GPR(rt)<31:0>;
   r = GPR(rs)<31:0> mod GPR(rt)<31:0>;
   LO <- SignExtend (q);
   HI <- SignExtend (r);
   HLStatus <- HLarith
}

-----------------------------------
-- DDIV rs, rt
-----------------------------------
define MultDiv > DDIV (rs::reg, rt::reg) =
{
   when GPR(rt) == 0 do #UNPREDICTABLE("DDIV: divide by zero");
   LO <- GPR(rs) quot GPR(rt);
   HI <- GPR(rs) rem GPR(rt);
   HLStatus <- HLarith
}

-----------------------------------
-- DDIVU rs, rt
-----------------------------------
define MultDiv > DDIVU (rs::reg, rt::reg) =
{
   when GPR(rt) == 0 do #UNPREDICTABLE("DDIVU: divide by zero");
   LO <- GPR(rs) div GPR(rt);
   HI <- GPR(rs) mod GPR(rt);
   HLStatus <- HLarith
}

-----------------------------------
-- MFHI rd
-----------------------------------
define MultDiv > MFHI (rd::reg) =
{
   when HLStatus == HLmtlo do #UNPREDICTABLE("MFHI");
   when HLStatus == HLarith do HLStatus <- HLok;
   GPR(rd) <- HI
}

-----------------------------------
-- MFLO rd
-----------------------------------
define MultDiv > MFLO (rd::reg) =
{
   when HLStatus == HLmthi do #UNPREDICTABLE("MFLO");
   when HLStatus == HLarith do HLStatus <- HLok;
   GPR(rd) <- LO
}

-----------------------------------
-- MTHI rd
-----------------------------------
define MultDiv > MTHI (rd::reg) =
{
   if HLStatus == HLarith then
      HLStatus <- HLmthi
   else if HLStatus == HLmtlo then
      HLStatus <- HLok
   else nothing;
   HI <- GPR(rd)
}

-----------------------------------
-- MTLO rd
-----------------------------------
define MultDiv > MTLO (rd::reg) =
{
   if HLStatus == HLarith then
      HLStatus <- HLmtlo
   else if HLStatus == HLmthi then
      HLStatus <- HLok
   else nothing;
   LO <- GPR(rd)
}

-----------------------------------
-- SLL rd, rt, sa
-----------------------------------
define Shift > SLL (rt::reg, rd::reg, sa::bits(5)) =
   GPR(rd) <- SignExtend (GPR(rt)<31:0> << [sa])

-----------------------------------
-- SRL rd, rt, sa
-----------------------------------
define Shift > SRL (rt::reg, rd::reg, sa::bits(5)) =
{
   when NotWordValue (GPR(rt)) do #UNPREDICTABLE("SRL: NotWordValue");
   GPR(rd) <- SignExtend (GPR(rt)<31:0> >>+ [sa])
}

-----------------------------------
-- SRA rd, rt, sa
-----------------------------------
define Shift > SRA (rt::reg, rd::reg, sa::bits(5)) =
{
   when NotWordValue (GPR(rt)) do #UNPREDICTABLE("SRA: NotWordValue");
   GPR(rd) <- SignExtend (GPR(rt)<31:0> >> [sa])
}

-----------------------------------
-- SLLV rd, rt, rs
-----------------------------------
define Shift > SLLV (rs::reg, rt::reg, rd::reg) =
{
   sa = GPR(rs)<4:0>;
   GPR(rd) <- SignExtend (GPR(rt)<31:0> << [sa])
}

-----------------------------------
-- SRLV rd, rt, rs
-----------------------------------
define Shift > SRLV (rs::reg, rt::reg, rd::reg) =
{
   when NotWordValue (GPR(rt)) do #UNPREDICTABLE("SRLV: NotWordValue");
   sa = GPR(rs)<4:0>;
   GPR(rd) <- SignExtend (GPR(rt)<31:0> >>+ [sa])
}

-----------------------------------
-- SRAV rd, rt, rs
-----------------------------------
define Shift > SRAV (rs::reg, rt::reg, rd::reg) =
{
   when NotWordValue (GPR(rt)) do #UNPREDICTABLE("SRAV: NotWordValue");
   sa = GPR(rs)<4:0>;
   GPR(rd) <- SignExtend (GPR(rt)<31:0> >> [sa])
}

-----------------------------------
-- DSLL rd, rt, sa
-----------------------------------
define Shift > DSLL (rt::reg, rd::reg, sa::bits(5)) =
   GPR(rd) <- GPR(rt) << [sa]

-----------------------------------
-- DSRL rd, rt, sa
-----------------------------------
define Shift > DSRL (rt::reg, rd::reg, sa::bits(5)) =
   GPR(rd) <- GPR(rt) >>+ [sa]

-----------------------------------
-- DSRA rd, rt, sa
-----------------------------------
define Shift > DSRA (rt::reg, rd::reg, sa::bits(5)) =
   GPR(rd) <- GPR(rt) >> [sa]

-----------------------------------
-- DSLLV rd, rt, rs
-----------------------------------
define Shift > DSLLV (rs::reg, rt::reg, rd::reg) =
{
   sa = GPR(rs)<5:0>;
   GPR(rd) <- GPR(rt) << [sa]
}

-----------------------------------
-- DSRLV rd, rt, rs
-----------------------------------
define Shift > DSRLV (rs::reg, rt::reg, rd::reg) =
{
   sa = GPR(rs)<5:0>;
   GPR(rd) <- GPR(rt) >>+ [sa]
}

-----------------------------------
-- DSRAV rd, rt, rs
-----------------------------------
define Shift > DSRAV (rs::reg, rt::reg, rd::reg) =
{
   sa = GPR(rs)<5:0>;
   GPR(rd) <- GPR(rt) >> [sa]
}

-----------------------------------
-- DSLL32 rd, rt, sa
-----------------------------------
define Shift > DSLL32 (rt::reg, rd::reg, sa::bits(5)) =
   GPR(rd) <- GPR(rt) << ([sa] + 0n32)

-----------------------------------
-- DSRL32 rd, rt, sa
-----------------------------------
define Shift > DSRL32 (rt::reg, rd::reg, sa::bits(5)) =
   GPR(rd) <- GPR(rt) >>+ ([sa] + 0n32)

-----------------------------------
-- DSRA32 rd, rt, sa
-----------------------------------
define Shift > DSRA32 (rt::reg, rd::reg, sa::bits(5)) =
   GPR(rd) <- GPR(rt) >> ([sa] + 0n32)

-----------------------------------
-- TGE rs, rt
-----------------------------------
define Trap > TGE (rs::reg, rt::reg) =
   when GPR(rs) >= GPR(rt) do SignalException (Tr)

-----------------------------------
-- TGEU rs, rt
-----------------------------------
define Trap > TGEU (rs::reg, rt::reg) =
   when GPR(rs) >=+ GPR(rt) do SignalException (Tr)

-----------------------------------
-- TLT rs, rt
-----------------------------------
define Trap > TLT (rs::reg, rt::reg) =
   when GPR(rs) < GPR(rt) do SignalException (Tr)

-----------------------------------
-- TLTU rs, rt
-----------------------------------
define Trap > TLTU (rs::reg, rt::reg) =
   when GPR(rs) <+ GPR(rt) do SignalException (Tr)

-----------------------------------
-- TEQ rs, rt
-----------------------------------
define Trap > TEQ (rs::reg, rt::reg) =
   when GPR(rs) == GPR(rt) do SignalException (Tr)

-----------------------------------
-- TNE rs, rt
-----------------------------------
define Trap > TNE (rs::reg, rt::reg) =
   when GPR(rs) <> GPR(rt) do SignalException (Tr)

-----------------------------------
-- TGEI rs, immediate
-----------------------------------
define Trap > TGEI (rs::reg, immediate::bits(16)) =
   when GPR(rs) >= SignExtend (immediate) do SignalException (Tr)

-----------------------------------
-- TGEIU rs, immediate
-----------------------------------
define Trap > TGEIU (rs::reg, immediate::bits(16)) =
   when GPR(rs) >=+ SignExtend (immediate) do SignalException (Tr)

-----------------------------------
-- TLTI rs, immediate
-----------------------------------
define Trap > TLTI (rs::reg, immediate::bits(16)) =
   when GPR(rs) < SignExtend (immediate) do SignalException (Tr)

-----------------------------------
-- TLTIU rs, immediate
-----------------------------------
define Trap > TLTIU (rs::reg, immediate::bits(16)) =
   when GPR(rs) <+ SignExtend (immediate) do SignalException (Tr)

-----------------------------------
-- TEQI rs, immediate
-----------------------------------
define Trap > TEQI (rs::reg, immediate::bits(16)) =
   when GPR(rs) == SignExtend (immediate) do SignalException (Tr)

-----------------------------------
-- TNEI rs, immediate
-----------------------------------
define Trap > TNEI (rs::reg, immediate::bits(16)) =
   when GPR(rs) <> SignExtend (immediate) do SignalException (Tr)

-----------------------------------
-- LB  rt, offset(base)
-- LBU rt, offset(base)
-- LH  rt, offset(base)
-- LHU rt, offset(base)
-- LW  rt, offset(base)
-- LWU rt, offset(base)
-- LL  rt, offset(base)
-- LD  rt, offset(base)
-- LDU rt, offset(base)
-- LLD rt, offset(base)
-----------------------------------
unit loadByte (base::reg, rt::reg, offset::bits(16), unsigned::bool) =
{
   vAddr = SignExtend (offset) + GPR(base);
   pAddr, CCA = AddressTranslation (vAddr, DATA, LOAD);
   pAddr = pAddr<PSIZE - 1 : 3> : (pAddr<2:0> ?? ReverseEndian^3);
   memdoubleword = LoadMemory (CCA, BYTE, pAddr, vAddr, DATA);
   byte = vAddr<2:0> ?? BigEndianCPU^3;
   membyte`8 = memdoubleword <7 + 8 * [byte] : 8 * [byte]>;
   GPR(rt) <- if unsigned then ZeroExtend (membyte) else SignExtend (membyte)
}

unit loadHalf (base::reg, rt::reg, offset::bits(16), unsigned::bool) =
{
   vAddr = SignExtend (offset) + GPR(base);
   if vAddr<0> then
      SignalException (AdEL)
   else
   {
      pAddr, CCA = AddressTranslation (vAddr, DATA, LOAD);
      pAddr = pAddr<PSIZE - 1 : 3> : (pAddr<2:0> ?? (ReverseEndian^2 : '0'));
      memdoubleword = LoadMemory (CCA, HALFWORD, pAddr, vAddr, DATA);
      byte = vAddr<2:0> ?? (BigEndianCPU^2 : '0');
      memhalf`16 = memdoubleword <15 + 8 * [byte] : 8 * [byte]>;
      GPR(rt) <- if unsigned then
                     ZeroExtend (memhalf)
                  else
                     SignExtend (memhalf)
   }
}

unit loadWord (base::reg, rt::reg, offset::bits(16), unsigned::bool) =
{
   vAddr = SignExtend (offset) + GPR(base);
   if vAddr<1:0> <> '00' then
      SignalException (AdEL)
   else
   {
      pAddr, CCA = AddressTranslation (vAddr, DATA, LOAD);
      pAddr = pAddr<PSIZE - 1 : 3> : (pAddr<2:0> ?? (ReverseEndian : '00'));
      memdoubleword = LoadMemory (CCA, WORD, pAddr, vAddr, DATA);
      byte = vAddr<2:0> ?? (BigEndianCPU : '00');
      memword`32 = memdoubleword <31 + 8 * [byte] : 8 * [byte]>;
      GPR(rt) <- if unsigned then
                     ZeroExtend (memword)
                  else
                     SignExtend (memword)
   }
}

unit loadDoubleword (base::reg, rt::reg, offset::bits(16)) =
{
   vAddr = SignExtend (offset) + GPR(base);
   if vAddr<2:0> <> '000' then
      SignalException (AdEL)
   else
   {
      pAddr, CCA = AddressTranslation (vAddr, DATA, LOAD);
      memdoubleword = LoadMemory (CCA, DOUBLEWORD, pAddr, vAddr, DATA);
      GPR(rt) <- memdoubleword
   }
}

--

define Load > LB (base::reg, rt::reg, offset::bits(16)) =
   loadByte (base, rt, offset, false)

define Load > LBU (base::reg, rt::reg, offset::bits(16)) =
   loadByte (base, rt, offset, true)

define Load > LH (base::reg, rt::reg, offset::bits(16)) =
   loadHalf (base, rt, offset, false)

define Load > LHU (base::reg, rt::reg, offset::bits(16)) =
   loadHalf (base, rt, offset, true)

define Load > LW (base::reg, rt::reg, offset::bits(16)) =
   loadWord (base, rt, offset, false)

define Load > LWU (base::reg, rt::reg, offset::bits(16)) =
   loadWord (base, rt, offset, true)

define Load > LL (base::reg, rt::reg, offset::bits(16)) =
{
   loadWord (base, rt, offset, false);
   LLbit <- Some (true)
}

define Load > LD (base::reg, rt::reg, offset::bits(16)) =
   loadDoubleword (base, rt, offset)

define Load > LLD (base::reg, rt::reg, offset::bits(16)) =
{
   loadDoubleword (base, rt, offset);
   LLbit <- Some (true)
}

-----------------------------------
-- LWL rt, offset(base)
-----------------------------------
define Load > LWL (base::reg, rt::reg, offset::bits(16)) =
{
   vAddr = SignExtend (offset) + GPR(base);
   pAddr, CCA = AddressTranslation (vAddr, DATA, LOAD);
   pAddr = pAddr<PSIZE - 1 : 3> : (pAddr<2:0> ?? ReverseEndian^3);
   pAddr = if BigEndianMem then pAddr else pAddr && ~0b111;
   byte = vAddr<1:0> ?? BigEndianCPU^2;
   word = vAddr<2:2> ?? BigEndianCPU;
   memdoubleword = LoadMemory (CCA, '0' : byte, pAddr, vAddr, DATA);
   temp`32 =
      match word, byte
      {
         case 0, 0 => memdoubleword <7:0>   : GPR(rt)<23:0>
         case 0, 1 => memdoubleword <15:0>  : GPR(rt)<15:0>
         case 0, 2 => memdoubleword <23:0>  : GPR(rt)<7:0>
         case 0, 3 => memdoubleword <31:0>
         case 1, 0 => memdoubleword <39:32> : GPR(rt)<23:0>
         case 1, 1 => memdoubleword <47:32> : GPR(rt)<15:0>
         case 1, 2 => memdoubleword <55:32> : GPR(rt)<7:0>
         case 1, 3 => memdoubleword <63:32>
      };
   GPR(rt) <- SignExtend (temp)
}

-----------------------------------
-- LWR rt, offset(base)
-----------------------------------
define Load > LWR (base::reg, rt::reg, offset::bits(16)) =
{
   vAddr = SignExtend (offset) + GPR(base);
   pAddr, CCA = AddressTranslation (vAddr, DATA, LOAD);
   pAddr = pAddr<PSIZE - 1 : 3> : (pAddr<2:0> ?? ReverseEndian^3);
   pAddr = if BigEndianMem then pAddr else pAddr && ~0b111;
   byte = vAddr<1:0> ?? BigEndianCPU^2;
   word = vAddr<2:2> ?? BigEndianCPU;
   memdoubleword = LoadMemory (CCA, WORD - ('0' : byte), pAddr, vAddr, DATA);
   temp`32 =
      match word, byte
      {
         case 0, 0 =>                  memdoubleword <31:0>
         case 0, 1 => GPR(rt)<31:24> : memdoubleword <31:8>
         case 0, 2 => GPR(rt)<31:16> : memdoubleword <31:16>
         case 0, 3 => GPR(rt)<31:8>  : memdoubleword <31:24>
         case 1, 0 =>                  memdoubleword <63:32>
         case 1, 1 => GPR(rt)<31:24> : memdoubleword <63:40>
         case 1, 2 => GPR(rt)<31:16> : memdoubleword <63:48>
         case 1, 3 => GPR(rt)<31:8>  : memdoubleword <63:56>
      };
   GPR(rt) <- SignExtend (temp)
   -- alternative specification when byte specification <> 0 is
   -- GPR(rt)<31:0> <- temp
}

-----------------------------------
-- LDL rt, offset(base)
-----------------------------------
define Load > LDL (base::reg, rt::reg, offset::bits(16)) =
{
   vAddr = SignExtend (offset) + GPR(base);
   pAddr, CCA = AddressTranslation (vAddr, DATA, LOAD);
   pAddr = pAddr<PSIZE - 1 : 3> : (pAddr<2:0> ?? ReverseEndian^3);
   pAddr = if BigEndianMem then pAddr else pAddr && ~0b111;
   byte = vAddr<2:0> ?? BigEndianCPU^3;
   memdoubleword = LoadMemory (CCA, byte, pAddr, vAddr, DATA);
   GPR(rt) <-
      match byte
      {
         case 0 => memdoubleword <7:0>  : GPR(rt)<55:0>
         case 1 => memdoubleword <15:0> : GPR(rt)<47:0>
         case 2 => memdoubleword <23:0> : GPR(rt)<39:0>
         case 3 => memdoubleword <31:0> : GPR(rt)<31:0>
         case 4 => memdoubleword <39:0> : GPR(rt)<23:0>
         case 5 => memdoubleword <47:0> : GPR(rt)<15:0>
         case 6 => memdoubleword <55:0> : GPR(rt)<7:0>
         case 7 => memdoubleword <63:0>
      }
}

-----------------------------------
-- LDR rt, offset(base)
-----------------------------------
define Load > LDR (base::reg, rt::reg, offset::bits(16)) =
{
   vAddr = SignExtend (offset) + GPR(base);
   pAddr, CCA = AddressTranslation (vAddr, DATA, LOAD);
   pAddr = pAddr<PSIZE - 1 : 3> : (pAddr<2:0> ?? ReverseEndian^3);
   pAddr = if BigEndianMem then pAddr else pAddr && ~0b111;
   byte = vAddr<2:0> ?? BigEndianCPU^3;
   memdoubleword = LoadMemory (CCA, DOUBLEWORD - byte, pAddr, vAddr, DATA);
   GPR(rt) <-
      match byte
      {
         case 0 =>                  memdoubleword <63:0>
         case 1 => GPR(rt)<63:56> : memdoubleword <63:8>
         case 2 => GPR(rt)<63:48> : memdoubleword <63:16>
         case 3 => GPR(rt)<63:40> : memdoubleword <63:24>
         case 4 => GPR(rt)<63:32> : memdoubleword <63:32>
         case 5 => GPR(rt)<63:24> : memdoubleword <63:40>
         case 6 => GPR(rt)<63:16> : memdoubleword <63:48>
         case 7 => GPR(rt)<63:8>  : memdoubleword <63:56>
      }
}

-----------------------------------
-- SB rt, offset(base)
-----------------------------------
define Store > SB (base::reg, rt::reg, offset::bits(16)) =
{
   vAddr = SignExtend (offset) + GPR(base);
   pAddr, CCA = AddressTranslation (vAddr, DATA, STORE);
   pAddr = pAddr<PSIZE - 1 : 3> : (pAddr<2:0> ?? ReverseEndian^3);
   bytesel = vAddr<2:0> ?? BigEndianCPU^3;
   datadoubleword = GPR(rt) << (0n8 * [bytesel]);
   StoreMemory (CCA, BYTE, datadoubleword, pAddr, vAddr, DATA)
}

-----------------------------------
-- SH rt, offset(base)
-----------------------------------
define Store > SH (base::reg, rt::reg, offset::bits(16)) =
{
   vAddr = SignExtend (offset) + GPR(base);
   if vAddr<0> then
      SignalException (AdES)
   else
   {
      pAddr, CCA = AddressTranslation (vAddr, DATA, STORE);
      pAddr = pAddr<PSIZE - 1 : 3> : (pAddr<2:0> ?? (ReverseEndian^2 : '0'));
      bytesel = vAddr<2:0> ?? (BigEndianCPU^2 : '0');
      datadoubleword = GPR(rt) << (0n8 * [bytesel]);
      StoreMemory (CCA, HALFWORD, datadoubleword, pAddr, vAddr, DATA)
   }
}

-----------------------------------
-- SW  rt, offset(base)
-- SC  rt, offset(base)
-- SD  rt, offset(base)
-- SCD rt, offset(base)
-----------------------------------
unit storeWord (base::reg, rt::reg, offset::bits(16)) =
{
   vAddr = SignExtend (offset) + GPR(base);
   if vAddr<1:0> <> '00' then
      SignalException (AdES)
   else
   {
      pAddr, CCA = AddressTranslation (vAddr, DATA, STORE);
      pAddr = pAddr<PSIZE - 1 : 3> : (pAddr<2:0> ?? (ReverseEndian : '00'));
      bytesel = vAddr<2:0> ?? (BigEndianCPU : '00');
      datadoubleword = GPR(rt) << (0n8 * [bytesel]);
      StoreMemory (CCA, WORD, datadoubleword, pAddr, vAddr, DATA)
   }
}

unit storeDoubleword (base::reg, rt::reg, offset::bits(16)) =
{
   vAddr = SignExtend (offset) + GPR(base);
   if vAddr<2:0> <> '000' then
      SignalException (AdES)
   else
   {
      pAddr, CCA = AddressTranslation (vAddr, DATA, STORE);
      datadoubleword = GPR(rt);
      StoreMemory (CCA, DOUBLEWORD, datadoubleword, pAddr, vAddr, DATA)
   }
}

--

define Store > SW (base::reg, rt::reg, offset::bits(16)) =
   storeWord (base, rt, offset)

define Store > SD (base::reg, rt::reg, offset::bits(16)) =
   storeDoubleword (base, rt, offset)

define Store > SC (base::reg, rt::reg, offset::bits(16)) =
   match LLbit
   {
      case None => #UNPREDICTABLE("SC: LLbit not set")
      case Some (false) => GPR(rt) <- 0
      case Some (true) =>
        {
           storeWord (base, rt, offset);
           GPR(rt) <- 1
        }
   }

define Store > SCD (base::reg, rt::reg, offset::bits(16)) =
   match LLbit
   {
      case None => #UNPREDICTABLE("SCD: LLbit not set")
      case Some (false) => GPR(rt) <- 0
      case Some (true) =>
        {
           storeDoubleword (base, rt, offset);
           GPR(rt) <- 1
        }
   }

-----------------------------------
-- SWL rt, offset(base)
-----------------------------------
define Store > SWL (base::reg, rt::reg, offset::bits(16)) =
{
   vAddr = SignExtend (offset) + GPR(base);
   pAddr, CCA = AddressTranslation (vAddr, DATA, STORE);
   pAddr = pAddr<PSIZE - 1 : 3> : (pAddr<2:0> ?? ReverseEndian^3);
   pAddr = if BigEndianMem then pAddr else pAddr && ~0b11;
   byte = vAddr<1:0> ?? BigEndianCPU^2;
   word = vAddr<2:2> ?? BigEndianCPU;
   datadoubleword`64 =
      match byte
      {
        case 0 => [GPR(rt)<31:24>]
        case 1 => [GPR(rt)<31:16>]
        case 2 => [GPR(rt)<31:8>]
        case 3 => [GPR(rt)<31:0>]
      };
   datadoubleword =
      if word == '1' then datadoubleword << 32 else datadoubleword;
   StoreMemory (CCA, [byte], datadoubleword, pAddr, vAddr, DATA)
}

-----------------------------------
-- SWR rt, offset(base)
-----------------------------------
define Store > SWR (base::reg, rt::reg, offset::bits(16)) =
{
   vAddr = SignExtend (offset) + GPR(base);
   pAddr, CCA = AddressTranslation (vAddr, DATA, STORE);
   pAddr = pAddr<PSIZE - 1 : 3> : (pAddr<2:0> ?? ReverseEndian^3);
   pAddr = if BigEndianMem then pAddr else pAddr && ~0b11;
   byte = vAddr<1:0> ?? BigEndianCPU^2;
   word = vAddr<2:2> ?? BigEndianCPU;
   datadoubleword =
      match word, byte
      {
         case 0, 0 => [GPR(rt)<31:0>]
         case 0, 1 => [GPR(rt)<23:0>] << 8
         case 0, 2 => [GPR(rt)<15:0>] << 16
         case 0, 3 => [GPR(rt)<7:0>]  << 24
         case 1, 0 => [GPR(rt)<31:0>] << 32
         case 1, 1 => [GPR(rt)<23:0>] << 40
         case 1, 2 => [GPR(rt)<15:0>] << 48
         case 1, 3 => [GPR(rt)<7:0>]  << 56
      };
   StoreMemory (CCA, WORD - [byte], datadoubleword,  pAddr, vAddr, DATA)
}

-----------------------------------
-- SDL rt, offset(base)
-----------------------------------
define Store > SDL (base::reg, rt::reg, offset::bits(16)) =
{
   vAddr = SignExtend (offset) + GPR(base);
   pAddr, CCA = AddressTranslation (vAddr, DATA, STORE);
   pAddr = pAddr<PSIZE - 1 : 3> : (pAddr<2:0> ?? ReverseEndian^3);
   pAddr = if BigEndianMem then pAddr else pAddr && ~0b111;
   byte = vAddr<2:0> ?? BigEndianCPU^3;
   datadoubleword =
      match byte
      {
         case 0 => [GPR(rt)<63:56>]
         case 1 => [GPR(rt)<63:48>]
         case 2 => [GPR(rt)<63:40>]
         case 3 => [GPR(rt)<63:32>]
         case 4 => [GPR(rt)<63:24>]
         case 5 => [GPR(rt)<63:16>]
         case 6 => [GPR(rt)<63:8>]
         case 7 =>  GPR(rt)
      };
   StoreMemory (CCA, byte, datadoubleword,  pAddr, vAddr, DATA)
}

-----------------------------------
-- SDR rt, offset(base)
-----------------------------------
define Store > SDR (base::reg, rt::reg, offset::bits(16)) =
{
   vAddr = SignExtend (offset) + GPR(base);
   pAddr, CCA = AddressTranslation (vAddr, DATA, STORE);
   pAddr = pAddr<PSIZE - 1 : 3> : (pAddr<2:0> ?? ReverseEndian^3);
   pAddr = if BigEndianMem then pAddr else pAddr && ~0b111;
   byte = vAddr<2:0> ?? BigEndianCPU^3;
   datadoubleword =
      match byte
      {
         case 0 =>  GPR(rt)
         case 1 => [GPR(rt)<63:8>]  << 8
         case 2 => [GPR(rt)<63:16>] << 16
         case 3 => [GPR(rt)<63:24>] << 24
         case 4 => [GPR(rt)<63:32>] << 32
         case 5 => [GPR(rt)<63:40>] << 40
         case 6 => [GPR(rt)<63:48>] << 48
         case 7 => [GPR(rt)<63:56>] << 56
      };
   StoreMemory (CCA, DOUBLEWORD - byte, datadoubleword,  pAddr, vAddr, DATA)
}

-----------------------------------
-- SYNC stype
-----------------------------------
define SYNC (stype::bits(5)) = nothing

-----------------------------------
-- BREAK
-----------------------------------
define BREAK = SignalException (Bp)

-----------------------------------
-- SYSCALL
-----------------------------------
define SYSCALL = SignalException (Sys)

-----------------------------------
-- ERET
-----------------------------------
define ERET =
{
   if CP0.Status.ERL then
   {
      PC <- CP0.ErrorEPC;
      CP0.Status.ERL <- false
   }
   else
   {
      PC <- CP0.EPC;
      CP0.Status.EXL <- false
   };
   LLbit <- Some (false)
}

-----------------------------------
-- MTC0 rt, rd
-- MTC0 rt, rd, sel
-----------------------------------
define CP > MTC0 (rt::reg, rd::reg, sel::bits(3)) =
   -- Will need adapting for EntryLo1 and EntryLo0
   CPR (0, rd, sel) <- GPR(rt)

-----------------------------------
-- DMTC0 rt, rd
-- DMTC0 rt, rd, sel
-----------------------------------
define CP > DMTC0 (rt::reg, rd::reg, sel::bits(3)) =
   CPR (0, rd, sel) <- GPR(rt)

-----------------------------------
-- MFC0 rt, rd
-- MFC0 rt, rd, sel
-----------------------------------
define CP > MFC0 (rt::reg, rd::reg, sel::bits(3)) =
   -- Will need adapting for EntryLo1 and EntryLo0
   GPR(rt) <- SignExtend (CPR (0, rd, sel)<32:0>)

-----------------------------------
-- DMFC0 rt, rd
-- DMFC0 rt, rd, sel
-----------------------------------
define CP > DMFC0 (rt::reg, rd::reg, sel::bits(3)) =
   GPR(rt) <- CPR (0, rd, sel)

-----------------------------------
-- J target
-----------------------------------
define Branch > J (instr_index::bits(26)) =
   BranchStatus <- Some (PC<63:28> : instr_index : '00')

-----------------------------------
-- JAL target
-----------------------------------
define Branch > JAL (instr_index::bits(26)) =
{
   GPR(31) <- PC + 8;
   BranchStatus <- Some (PC<63:28> : instr_index : '00')
}

-----------------------------------
-- JR rs
-----------------------------------
define Branch > JR (rs::reg) =
   BranchStatus <- Some (GPR(rs))

-----------------------------------
-- JALR rs (rd = 31 implied)
-- JALR rd, rs
-----------------------------------
define Branch > JALR (rs::reg, rd::reg) =
{
   temp = GPR(rs);
   GPR(rd) <- PC + 8;
   BranchStatus <- Some (temp)
}

-----------------------------------
-- BEQ rs, rt, offset
-----------------------------------
define Branch > BEQ (rs::reg, rt::reg, offset::bits(16)) =
   when GPR(rs) == GPR(rt) do
      BranchStatus <- Some (PC + SignExtend (offset) << 2)

-----------------------------------
-- BNE rs, rt, offset
-----------------------------------
define Branch > BNE (rs::reg, rt::reg, offset::bits(16)) =
   when GPR(rs) <> GPR(rt) do
      BranchStatus <- Some (PC + SignExtend (offset) << 2)

-----------------------------------
-- BLEZ rs, offset
-----------------------------------
define Branch > BLEZ (rs::reg, offset::bits(16)) =
   when GPR(rs) <= 0 do
      BranchStatus <- Some (PC + SignExtend (offset) << 2)

-----------------------------------
-- BGTZ rs, offset
-----------------------------------
define Branch > BGTZ (rs::reg, offset::bits(16)) =
   when GPR(rs) > 0 do
      BranchStatus <- Some (PC + SignExtend (offset) << 2)

-----------------------------------
-- BLTZ rs, offset
-----------------------------------
define Branch > BLTZ (rs::reg, offset::bits(16)) =
   when GPR(rs) < 0 do
      BranchStatus <- Some (PC + SignExtend (offset) << 2)

-----------------------------------
-- BGEZ rs, offset
-----------------------------------
define Branch > BGEZ (rs::reg, offset::bits(16)) =
   when GPR(rs) >= 0 do
      BranchStatus <- Some (PC + SignExtend (offset) << 2)

-----------------------------------
-- BLTZAL rs, offset
-----------------------------------
define Branch > BLTZAL (rs::reg, offset::bits(16)) =
{
   temp = GPR(rs);
   GPR(31) <- PC + 8;
   when temp < 0 do
      BranchStatus <- Some (PC + SignExtend (offset) << 2)
}

-----------------------------------
-- BGEZAL rs, offset
-----------------------------------
define Branch > BGEZAL (rs::reg, offset::bits(16)) =
{
   temp = GPR(rs);
   GPR(31) <- PC + 8;
   when temp >= 0 do
      BranchStatus <- Some (PC + SignExtend (offset) << 2)
}

-----------------------------------
-- BEQL rs, rt, offset
-----------------------------------
define Branch > BEQL (rs::reg, rt::reg, offset::bits(16)) =
   if GPR(rs) == GPR(rt) then
      BranchStatus <- Some (PC + SignExtend (offset) << 2)
   else
      PC <- PC + 4

-----------------------------------
-- BNEL rs, rt, offset
-----------------------------------
define Branch > BNEL (rs::reg, rt::reg, offset::bits(16)) =
   if GPR(rs) <> GPR(rt) then
      BranchStatus <- Some (PC + SignExtend (offset) << 2)
   else
      PC <- PC + 4

-----------------------------------
-- BLEZL rs, offset
-----------------------------------
define Branch > BLEZL (rs::reg, offset::bits(16)) =
   if GPR(rs) <= 0 then
      BranchStatus <- Some (PC + SignExtend (offset) << 2)
   else
      PC <- PC + 4

-----------------------------------
-- BGTZL rs, offset
-----------------------------------
define Branch > BGTZL (rs::reg, offset::bits(16)) =
   if GPR(rs) > 0 then
      BranchStatus <- Some (PC + SignExtend (offset) << 2)
   else
      PC <- PC + 4

-----------------------------------
-- BLTZL rs, offset
-----------------------------------
define Branch > BLTZL (rs::reg, offset::bits(16)) =
   if GPR(rs) < 0 then
      BranchStatus <- Some (PC + SignExtend (offset) << 2)
   else
      PC <- PC + 4

-----------------------------------
-- BGEZL rs, offset
-----------------------------------
define Branch > BGEZL (rs::reg, offset::bits(16)) =
   if GPR(rs) >= 0 then
      BranchStatus <- Some (PC + SignExtend (offset) << 2)
   else
      PC <- PC + 4

-----------------------------------
-- BLTZALL rs, offset
-----------------------------------
define Branch > BLTZALL (rs::reg, offset::bits(16)) =
{
   temp = GPR(rs);
   GPR(31) <- PC + 8;
   if temp < 0 then
      BranchStatus <- Some (PC + SignExtend (offset) << 2)
   else
      PC <- PC + 4
}

-----------------------------------
-- BGEZALL rs, offset
-----------------------------------
define Branch > BGEZALL (rs::reg, offset::bits(16)) =
{
   temp = GPR(rs);
   GPR(31) <- PC + 8;
   if temp >= 0 then
      BranchStatus <- Some (PC + SignExtend (offset) << 2)
   else
      PC <- PC + 4
}

-----------------------------------
-- Rerserved instruction, i.e. unsuccessful decode.
-----------------------------------
define ReservedInstruction =
   SignalException (RI)

define Run

-------------------------------------------------------
-- Not implemented:
--
-- LWCz, SWCz, MTCz, MFCz, CTCz, CFCz, COPz, BCzT, BCzF
-- DMFCz, DMTCz, LDCz, SDCz
-- BCzTL, BCzFL
-- TLBR, TLBWI, TLBWR, TLBP, CACHE
-- Floating-point
-------------------------------------------------------

--================================================
-- Instruction decoding
--================================================

instruction Decode (w::word) =
   match w
   {
      case '000 000 rs rt rd imm5 function' =>
         match function
         {
            case '000 000' => Shift (SLL (rt, rd, imm5))
            case '000 010' => Shift (SRL (rt, rd, imm5))
            case '000 011' => Shift (SRA (rt, rd, imm5))
            case '000 100' => Shift (SLLV (rs, rt, rd))
            case '000 110' => Shift (SRLV (rs, rt, rd))
            case '000 111' => Shift (SRAV (rs, rt, rd))
            case '001 000' => Branch (JR (rs))
            case '001 001' => Branch (JALR (rs, rd))
            case '001 100' => SYSCALL
            case '001 101' => BREAK
            case '001 111' => SYNC (imm5)
            case '010 000' => MultDiv (MFHI (rd))
            case '010 001' => MultDiv (MTHI (rd))
            case '010 010' => MultDiv (MFLO (rs))
            case '010 011' => MultDiv (MTLO (rs))
            case '010 100' => Shift (DSLLV (rs, rt, rd))
            case '010 110' => Shift (DSRLV (rs, rt, rd))
            case '010 111' => Shift (DSRAV (rs, rt, rd))
            case '011 000' => MultDiv (MULT (rs, rt))
            case '011 001' => MultDiv (MULTU (rs, rt))
            case '011 010' => MultDiv (DIV (rs, rt))
            case '011 011' => MultDiv (DIVU (rs, rt))
            case '011 100' => MultDiv (DMULT (rs, rt))
            case '011 101' => MultDiv (DMULTU (rs, rt))
            case '011 110' => MultDiv (DDIV (rs, rt))
            case '011 111' => MultDiv (DDIVU (rs, rt))
            case '100 000' => ArithR (ADD (rs, rt, rd))
            case '100 001' => ArithR (ADDU (rs, rt, rd))
            case '100 010' => ArithR (SUB (rs, rt, rd))
            case '100 011' => ArithR (SUBU (rs, rt, rd))
            case '100 100' => ArithR (AND (rs, rt, rd))
            case '100 101' => ArithR (OR (rs, rt, rd))
            case '100 110' => ArithR (XOR (rs, rt, rd))
            case '100 111' => ArithR (NOR (rs, rt, rd))
            case '101 010' => ArithR (SLT (rs, rt, rd))
            case '101 011' => ArithR (SLTU (rs, rt, rd))
            case '101 100' => ArithR (DADD (rs, rt, rd))
            case '101 101' => ArithR (DADDU (rs, rt, rd))
            case '101 110' => ArithR (DSUB (rs, rt, rd))
            case '101 111' => ArithR (DSUBU (rs, rt, rd))
            case '110 000' => Trap (TGE (rs, rt))
            case '110 001' => Trap (TGEU (rs, rt))
            case '110 010' => Trap (TLT (rs, rt))
            case '110 011' => Trap (TLTU (rs, rt))
            case '110 100' => Trap (TEQ (rs, rt))
            case '110 110' => Trap (TNE (rs, rt))
            case '111 000' => Shift (DSLL (rt, rd, imm5))
            case '111 010' => Shift (DSRL (rt, rd, imm5))
            case '111 011' => Shift (DSRA (rt, rd, imm5))
            case '111 100' => Shift (DSLL32 (rt, rd, imm5))
            case '111 110' => Shift (DSRL32 (rt, rd, imm5))
            case '111 111' => Shift (DSRA32 (rt, rd, imm5))
            case _ => ReservedInstruction
         }
      case '000 001 rs function immediate' =>
         match function
         {
            case '00 000' => Branch (BLTZ (rs, immediate))
            case '00 001' => Branch (BGEZ (rs, immediate))
            case '00 010' => Branch (BLTZL (rs, immediate))
            case '00 011' => Branch (BGEZL (rs, immediate))
            case '01 000' => Trap (TGEI (rs, immediate))
            case '01 001' => Trap (TGEIU (rs, immediate))
            case '01 010' => Trap (TLTI (rs, immediate))
            case '01 011' => Trap (TLTIU (rs, immediate))
            case '01 100' => Trap (TEQI (rs, immediate))
            case '01 110' => Trap (TNEI (rs, immediate))
            case '10 000' => Branch (BLTZAL (rs, immediate))
            case '10 001' => Branch (BGEZAL (rs, immediate))
            case '10 010' => Branch (BLTZALL (rs, immediate))
            case '10 011' => Branch (BGEZALL (rs, immediate))
            case _ => ReservedInstruction
         }
      case '000 010 immediate' => Branch (J (immediate))
      case '000 011 immediate' => Branch (JAL (immediate))
      case '010 000 function rt rd 00000000 sel' =>
         match function
         {
            case '00 000' => CP (MFC0 (rt, rd, sel))
            case '00 001' => CP (DMFC0 (rt, rd, sel))
            case '00 100' => CP (MTC0 (rt, rd, sel))
            case '00 101' => CP (DMTC0 (rt, rd, sel))
            case _ => ReservedInstruction
         }
      case 'function rs rt immediate' =>
         match function
         {
            case '000 100' => Branch (BEQ (rs, rt, immediate))
            case '000 101' => Branch (BNE (rs, rt, immediate))
            case '000 110' => Branch (BLEZ (rs, immediate))
            case '000 111' => Branch (BGTZ (rs, immediate))
            case '001 000' => ArithI (ADDI (rs, rt, immediate))
            case '001 001' => ArithI (ADDIU (rs, rt, immediate))
            case '001 010' => ArithI (SLTI (rs, rt, immediate))
            case '001 011' => ArithI (SLTIU (rs, rt, immediate))
            case '001 100' => ArithI (ANDI (rs, rt, immediate))
            case '001 101' => ArithI (ORI (rs, rt, immediate))
            case '001 110' => ArithI (XORI (rs, rt, immediate))
            case '001 111' => ArithI (LUI (rt, immediate))
            case '010 100' => Branch (BEQL (rs, rt, immediate))
            case '010 101' => Branch (BNEL (rs, rt, immediate))
            case '010 110' => Branch (BLEZL (rs, immediate))
            case '010 111' => Branch (BGTZL (rs, immediate))
            case '011 000' => ArithI (DADDI (rs, rt, immediate))
            case '011 001' => ArithI (DADDIU (rs, rt, immediate))
            case '011 010' => Load (LDL (rs, rt, immediate))
            case '011 011' => Load (LDR (rs, rt, immediate))
            case '100 000' => Load (LB (rs, rt, immediate))
            case '100 001' => Load (LH (rs, rt, immediate))
            case '100 010' => Load (LWL (rs, rt, immediate))
            case '100 011' => Load (LW (rs, rt, immediate))
            case '100 100' => Load (LBU (rs, rt, immediate))
            case '100 101' => Load (LHU (rs, rt, immediate))
            case '100 110' => Load (LWR (rs, rt, immediate))
            case '100 111' => Load (LWU (rs, rt, immediate))
            case '101 000' => Store (SB (rs, rt, immediate))
            case '101 001' => Store (SH (rs, rt, immediate))
            case '101 010' => Store (SWL (rs, rt, immediate))
            case '101 011' => Store (SW (rs, rt, immediate))
            case '101 100' => Store (SDL (rs, rt, immediate))
            case '101 101' => Store (SDR (rs, rt, immediate))
            case '101 110' => Store (SWR (rs, rt, immediate))
            case '110 000' => Load (LL (rs, rt, immediate))
            case '110 100' => Load (LLD (rs, rt, immediate))
            case '110 111' => Load (LD (rs, rt, immediate))
            case '111 000' => Store (SC (rs, rt, immediate))
            case '111 100' => Store (SCD (rs, rt, immediate))
            case '111 111' => Store (SD (rs, rt, immediate))
            case _ => ReservedInstruction
         }
   }

--================================================
-- The next state function
--================================================

word Fetch =
{
   vAddr = PC;
   pAddr, CCA = AddressTranslation (vAddr, INSTRUCTION, LOAD);
   memdoubleword = LoadMemory (CCA, WORD, pAddr, vAddr, INSTRUCTION);
   bytesel = vAddr<2:0> ?? (BigEndianCPU : '00');
   memword = memdoubleword <31 + 8 * [bytesel] : 8 * [bytesel]>;
   return memword
}

unit Next =
{
   bstatus = BranchStatus;
   i = Decode (Fetch);
   BranchStatus <- None;
   Run (i);
   match bstatus
   {
      case Some (addr) =>
        if IsSome (BranchStatus) then
           #UNPREDICTABLE("Branch follows branch")
        else
           PC <- addr
      case None => nothing
   };
   PC <- PC + 4;
   CP0.Count <- CP0.Count + 1
}

{-
Testing

Runtime.LoadF "mips.spec"

  Runtime.evalQ`
    {
      CP0.Config.BE <- true;
      CP0.Config.BE <- false;
      CP0.Status.RE <- false;
      CP0.Status.RE <- true;
      CP0.Status.KSU <- '10';
      CP0.Status.EXL <- false;
      CP0.Status.ERL <- false;
      GPR(1) <- 0x1122_3344_5566_7788;
      GPR(2) <- 0;
      MEM <- InitMap(0xCC)
    }`

  Runtime.evalQ `BigEndianCPU`

  Runtime.evalQ `Run (Store (SD (2, 1, 0)))`
  Runtime.evalQ `Run (Store (SD (2, 1, 8)))`

  Runtime.evalQ `Run (Store (SW (2, 1, 0)))`
  Runtime.evalQ `Run (Store (SW (2, 1, 4)))`
  Runtime.evalQ `Run (Store (SW (2, 1, 8)))`

  Runtime.evalQ `Run (Store (SH (2, 1, 0)))`
  Runtime.evalQ `Run (Store (SH (2, 1, 2)))`
  Runtime.evalQ `Run (Store (SH (2, 1, 4)))`
  Runtime.evalQ `Run (Store (SH (2, 1, 6)))`

  Runtime.evalQ `Run (Store (SB (2, 1, 0)))`
  Runtime.evalQ `Run (Store (SB (2, 1, 1)))`
  Runtime.evalQ `Run (Store (SB (2, 1, 2)))`
  Runtime.evalQ `Run (Store (SB (2, 1, 3)))`
  Runtime.evalQ `Run (Store (SB (2, 1, 4)))`

  Runtime.evalQ `MEM(0)`;
  Runtime.evalQ `MEM(1)`;
  Runtime.evalQ `MEM(2)`;
  Runtime.evalQ `MEM(3)`;
  Runtime.evalQ `MEM(4)`;
  Runtime.evalQ `MEM(5)`;
  Runtime.evalQ `MEM(6)`;
  Runtime.evalQ `MEM(7)`;
  Runtime.evalQ `MEM(8)`;
  Runtime.evalQ `MEM(9)`;
  Runtime.evalQ `MEM(10)`;
  Runtime.evalQ `MEM(11)`;
  Runtime.evalQ `MEM(12)`;
  Runtime.evalQ `MEM(13)`;
  Runtime.evalQ `MEM(14)`;
  Runtime.evalQ `MEM(15)`;
  Runtime.evalQ `MEM(16)`;

  Runtime.evalQ `MEM`;

Runtime.LoadF "mips.spec"
HolExport.spec ("mips.spec", "mips")

-}
