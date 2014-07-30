----------------------------------------------------------------------------
-- Specification of Thacker's Tiny 3 Computer
-- See: http://www.cl.cam.ac.uk/~swm11/examples/bluespec/Tiny3/
----------------------------------------------------------------------------

{-
val () = Runtime.LoadF "tiny.spec"
val () = HolExport.monadicExport true
val () = HolExport.monadicExport false
val () = HolExport.spec ("tiny.spec", "tiny")
val () = HolExport.acl2spec ("tiny.spec", "tiny-acl2.txt")

Runtime.evalQ `function (fADD, 1, 2)`
-}

---------------------------------------------
-- Types
---------------------------------------------

type regT  = bits(7)
type wordT = bits(32)
type immT  = bits(24)
type addrT = bits(10)
type memT  = addrT -> wordT

exception Reserved

construct funcT {fADD, fSUB, fINC, fDEC, fAND, fOR, fXOR, fReserved}
construct shiftT {noShift, RCY1, RCY8, RCY16}
construct conditionT {skipNever, skipNeg, skipZero, skipInRdy}

---------------------------------------------
-- State
---------------------------------------------

declare
{
   PC :: addrT          -- Program Counter
   R :: regT -> wordT   -- Registers
   IM :: memT           -- Instruction Memory
   DM :: memT           -- Data Memory
   InRdy :: bool        -- Input Ready
   InData :: wordT      -- Input Data
   OutStrobe :: wordT   -- Output Data
}

---------------------------------------------
-- Operations
---------------------------------------------

wordT function (func::funcT, a:: wordT, b:: wordT) =
   match func
   {
     case fADD => a + b
     case fSUB => a - b
     case fINC => b + 1
     case fDEC => b - 1
     case fAND => a && b
     case fOR  => a || b
     case fXOR => a ?? b
     case _ => #Reserved
   }

wordT shifter (shift::shiftT, a::wordT) =
   match shift
   {
      case noShift => a
      case RCY1    => a #>> 1
      case RCY8    => a #>> 8
      case RCY16   => a #>> 16
   }

wordT ALU (func::funcT, shift::shiftT, a::wordT, b::wordT) =
   shifter (shift, function (func, a, b))

unit incPC (skip::conditionT, alu::wordT) =
   match skip
   {
      case skipNever => PC <- PC + 1
      case skipNeg   => PC <- PC + if alu < 0  then 2 else 1
      case skipZero  => PC <- PC + if alu == 0 then 2 else 1
      case skipInRdy => PC <- PC + if InRdy    then 2 else 1
   }

-- Common functionality
unit norm (func::funcT, shift::shiftT, skip::conditionT,
           wback::bool, strobe::bool, w::regT, a::regT, b::regT) =
{
   alu = ALU (func, shift, R(a), R(b));
   when wback do R(w) <- alu;
   when strobe do OutStrobe <- alu;
   incPC (skip, alu)
}

---------------------------------------------
-- Instructions
---------------------------------------------

define Normal (func::funcT, shift::shiftT, skip::conditionT,
               w::regT, a::regT, b::regT) =
   norm (func, shift, skip, true, false, w, a, b)


define StoreDM (func::funcT, shift::shiftT, skip::conditionT,
                w::regT, a::regT, b::regT) =
{
   DM([R(b)]) <- R(a);
   norm (func, shift, skip, true, false, w, a, b)
}

define StoreIM (func::funcT, shift::shiftT, skip::conditionT,
                w::regT, a::regT, b::regT) =
{
   IM([R(b)]) <- R(a);
   norm (func, shift, skip, true, false, w, a, b)
}

define Out (func::funcT, shift::shiftT, skip::conditionT,
            w::regT, a::regT, b::regT) =
   norm (func, shift, skip, true, true, w, a, b)

define LoadDM (func::funcT, shift::shiftT, skip::conditionT,
               w::regT, a::regT, b::regT) =
{
   R(w) <- DM([R(b)]);
   norm (func, shift, skip, false, false, w, a, b)
}

define In (func::funcT, shift::shiftT, skip::conditionT,
           w::regT, a::regT, b::regT) =
{
   R(w) <- InData;
   norm (func, shift, skip, false, false, w, a, b)
}

define Jump (func::funcT, shift::shiftT, w::regT, a::regT, b::regT) =
{
   R(w) <- ZeroExtend (PC + 1);
   PC <- [ALU (func, shift, R(a), R(b))]
}

define LoadConstant (w::regT, imm::immT) =
{
   R(w) <- ZeroExtend (imm);
   PC <- PC + 1
}

define ReservedInstr = #Reserved

define Run

---------------------------------------------
-- Decode
---------------------------------------------

instruction Decode (opc::wordT) =
   match opc
   {
      case 'Rw 1 imm`24' => LoadConstant (Rw, imm)
      case 'Rw 0 Ra Rb Function Shift Skip Op' =>
         {
            func  = [Function :: bits(3)] :: funcT;
            shift = [Shift :: bits(2)] :: shiftT;
            skip  = [Skip :: bits(2)] :: conditionT;
            match Op
            {
               case 0 => Normal (func, shift, skip, Rw, Ra, Rb)
               case 1 => StoreDM (func, shift, skip, Rw, Ra, Rb)
               case 2 => StoreIM (func, shift, skip, Rw, Ra, Rb)
               case 3 => Out (func, shift, skip, Rw, Ra, Rb)
               case 4 => LoadDM (func, shift, skip, Rw, Ra, Rb)
               case 5 => In (func, shift, skip, Rw, Ra, Rb)
               case 6 => Jump (func, shift, Rw, Ra, Rb)
               case 7 => ReservedInstr
            }
         }
   }

---------------------------------------------
-- Next State
---------------------------------------------

unit Next =
{
  i = Decode (IM (PC));
  when i <> ReservedInstr do Run (i)
}

---------------------------------------------
-- Encode
---------------------------------------------

wordT enc
  (args::funcT * shiftT * conditionT * regT * regT * regT, opc::bits(3)) =
{
   func, shift, skip, w, a, b = args;
   return (w : '0' : a : b : [func]`3 : [shift]`2 : [skip]`2 : opc)
}

wordT Encode (i::instruction) =
   match i
   {
      case LoadConstant (Rw, imm) => Rw : '1' : imm
      case Normal (args)  => enc (args, '000')
      case StoreDM (args) => enc (args, '001')
      case StoreIM (args) => enc (args, '010')
      case Out (args)     => enc (args, '011')
      case LoadDM (args)  => enc (args, '100')
      case In (args)      => enc (args, '101')
      case Jump (func, shift, Rw, Ra, Rb) =>
         enc ((func, shift, skipNever, Rw, Ra, Rb), '110')
      case ReservedInstr => 0b111
   }

---------------------------------------------
-- Load into Instruction Memory
---------------------------------------------

unit LoadIM (a::addrT, i::instruction list) measure Length (i) =
   match i
   {
      case Nil => nothing
      case Cons (h, t) =>
        {
           IM(a) <- Encode (h);
           LoadIM (a + 1, t)
        }
   }

---------------------------------------------
-- Initialization & testing
---------------------------------------------

unit initialize (p::instruction list) =
{
   PC <- 0;
   R <- InitMap (0);
   DM <- InitMap (0);
   InRdy <- false;
   InData <- 0;
   OutStrobe <- 0;
   IM <- InitMap (Encode (ReservedInstr));
   LoadIM (0, p)
}

instruction list test_prog =
   list {
      LoadConstant (0, 0),
      LoadConstant (1, 1000),
      LoadConstant (2, 1010),
      LoadConstant (3, 4),
      StoreDM (fINC, noShift, skipNever, 1, 1, 1),
      Normal (fXOR, noShift, skipZero, 4, 1, 2),
      Jump (fADD, noShift, 4, 3, 0),
      Out (fADD, noShift, skipNever, 1, 1, 0)
   }
