// Copyright (C) 2020 David S. Hardin
//
// License: (An MIT/X11-style license)
//
//   Permission is hereby granted, free of charge, to any person obtaining a
//   copy of this software and associated documentation files (the "Software"),
//   to deal in the Software without restriction, including without limitation
//   the rights to use, copy, modify, merge, publish, distribute, sublicense,
//   and/or sell copies of the Software, and to permit persons to whom the
//   Software is furnished to do so, subject to the following conditions:
//
//   The above copyright notice and this permission notice shall be included in
//   all copies or substantial portions of the Software.
//
//   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
//   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
//   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
//   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
//   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
//   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
//   DEALINGS IN THE SOFTWARE.

// ------------------------------------------------------------------------
// LEG64 Simulator


#include "leg64.h"


// Initialization

leg64St zeroRegs(leg64St s) {
  for (uint i = REG_SZ; i > 0; i--) {
    s.regs[i-1] = 0;
  }
  return s;
}


leg64St zeroDmem(leg64St s) {
  for (uint i = DMEM_SZ; i > 0; i--) {
    s.dmem[i-1] = 0;
  }
  return s;
}


leg64St zeroCmem(leg64St s) {
  for (uint i = CMEM_SZ; i > 0; i--) {
    s.cmem[i-1] = 0;
  }
  return s;
}


leg64St resetAll(leg64St s) {
  //  s.err = 0;
  s.pc = 0;
  s.sp = 0;
  // s.insCount = 0;

  s.opcode = NOP;
  s.op1 = 0;
  s.op2 = 0;
  s.op3 = 0;

  s.C = 0;
  s.N = 0;
  s.Z = 0;
  s.V = 0;
  
  s = zeroRegs(s);
  s = zeroDmem(s);
  s = zeroCmem(s);
  
  return s;
}


leg64St resetAllButCmem(leg64St s) {
  //  s.err = 0;
  s.pc = 0;
  s.sp = 0;
  //  s.insCount = 0;

  s.opcode = NOP;
  s.op1 = 0;
  s.op2 = 0;
  s.op3 = 0;

  s.C = 0;
  s.N = 0;
  s.Z = 0;
  s.V = 0;
  
  s = zeroRegs(s);
  s = zeroDmem(s);

  return s;
}


leg64St nextInst(leg64St s) {
  ui32 codewd = s.cmem[s.pc];
    
  s.opcode = codewd.slc<8>(24);
  s.op1 = codewd.slc<8>(16);
  s.op2 = codewd.slc<8>(8);
  s.op3 = codewd.slc<8>(0);
  s.pc = s.pc + 1;
    //    s.insCount++;
  return s;
}


// We define the semantics of each instruction.  Most of these functions 
// are slight abstractions of actual LLVM instructions, and have the 
// standard LLVM three-address form.  I have also held over a few M1 
// stack-based instructions to be used in register initialization,
// phi processing, etc.


// Memory Instructions


// (LDR j k): Assign the reg j the value at the memory address stored
// in reg k.

leg64St do_LDR(leg64St s) {
 ui12 addr = s.regs[s.op2] & 0xfff;

 s.regs[s.op1] = s.dmem[addr];
 return s;
}

// (STR j k): Store the value stored in reg k at the
// memory address stored in reg j.

leg64St do_STR(leg64St s) {
 ui12 addr = s.regs[s.op1] & 0xfff;

 s.dmem[addr] = s.regs[s.op2];
  return s;
}

// Arithmetic/Logic Instructions

// (ADD a b c): Set the value of the first reg to the sum of the
// second and third regs.

leg64St do_ADD(leg64St s) {
  s.regs[s.op1] = s.regs[s.op2] + s.regs[s.op3];
  return s;
}

// (ADDI a b c): Set the value of the first reg to the sum of the
// second reg and the (small) literal c

leg64St do_ADDI(leg64St s) {
  s.regs[s.op1] = s.regs[s.op2] + s.op3;
  return s;
}

// (CMP a b): Compare regs a and b
// Set the condition codes as follows:
//  Set Z if a = b
//  Set N if a - b is negative
//  Set C is a - b is positive

leg64St do_CMP(leg64St s) {
  ui64 res = s.regs[s.op1] - s.regs[s.op2];

  if (res == 0) {
    s.C = 0;
    s.N = 0;
    s.V = 0;
    s.Z = 1;
  } else if ((res & 0x8000000000000000) == 0x8000000000000000) {  // negative
    s.C = 0;
    s.N = 1;
    s.V = 0;
    s.Z = 0;
  } else { // positive
    s.C = 1;
    s.N = 0;
    s.V = 0;
    s.Z = 0;
  }
  return s;
}
      
// (CMPI a b): Compare reg a and (small) literal value b
// Set the condition codes as follows:
//  Set Z if a = b
//  Set N if a - b is negative
//  Set C is a - b is positive

leg64St do_CMPI(leg64St s) {
  ui64 res = s.regs[s.op1] - s.op2;

  if (res == 0) {
    s.C = 0;
    s.N = 0;
    s.V = 0;
    s.Z = 1;
  } else if ((res & 0x8000000000000000) == 0x8000000000000000) {  // negative
    s.C = 0;
    s.N = 1;
    s.V = 0;
    s.Z = 0;
  } else { // positive
    s.C = 1;
    s.N = 0;
    s.V = 0;
    s.Z = 0;
  }
  return s;
}


// (CONST a b c): Set the value of the first reg 
// to the constant formed by ((b << 8) | c).

leg64St do_CONST(leg64St s) {
  ui64 k = (((ui64)s.op2 << 8) | s.op3);
  s.regs[s.op1] = k;
  return s;
}


// (LSL a b c): Logical shift reg b left by the number of bits indicated by
// the constant amount (c && 0x3f), and store in reg a.

leg64St do_LSL(leg64St s) {
  s.regs[s.op1] = s.regs[s.op2] << (s.op3 & 0x3f);
  return s;
}

// (LSR a b c): Logical shift reg b right by the number of bits indicated by
// the constant amount (c && 0x3f), and store in reg a.

leg64St do_LSR(leg64St s) {
  s.regs[s.op1] = s.regs[s.op2] >> (s.op3 & 0x3f);
  return s;
}

// (ASR a b c): Arithmetic shift reg b right by the number of bits indicated by
// the constant amount (c && 0x3f), and store in reg a.

#define W 64

leg64St do_ASR(leg64St s) {
  s.regs[s.op1] = (s.regs[s.op2] >> (s.op3 & 0x3f)) |
                  ((0-(s.regs[s.op2] >> (W-1))) << (W-(s.op3 & 0x3f)));
  return s;
}


// (MUL a b c): Set the value of the first reg 
// to the product of the second and third regs.

leg64St do_MUL(leg64St s) {
  s.regs[s.op1] = s.regs[s.op2] * s.regs[s.op3];
  return s;
}

// (SUB a b c): Set the value of the first reg
// to the difference of the second and third regs.

leg64St do_SUB(leg64St s) {
  s.regs[s.op1] = s.regs[s.op2] - s.regs[s.op3];
  return s;
}

// (SUBI a b c): Set the value of reg a to the difference of 
// reg b and (small) literal c.

leg64St do_SUBI(leg64St s) {
  s.regs[s.op1] = s.regs[s.op2] - s.op3;
  return s;
}


// Transfer of Control Instructions

// (B i): adjust the pc by i

leg64St do_B(leg64St s) {
  if (s.op1 > 127) {
    s.pc = s.pc + (s.op1 - 256);
  } else {
    s.pc = s.pc + s.op1;
  }
  return s;
}

// (BEQ k): Adjust the pc by k if Z == 1

leg64St do_BEQ(leg64St s) {
  if (s.Z == 1) {
    if (s.op1 > 127) {
      s.pc = s.pc + (s.op1 - 256);
    } else {
      s.pc = s.pc + s.op1;
    }
  }
  return s;
}

// (BNE k): Adjust the pc by k if Z == 0

leg64St do_BNE(leg64St s) {
  if (s.Z == 0) {
    if (s.op1 > 127) {
      s.pc = s.pc + (s.op1 - 256);
    } else {
      s.pc = s.pc + s.op1;
    }
  }
  return s;
}

// (BLO k): Adjust the pc by k if unsigned lower
// (C == 0)

leg64St do_BLO(leg64St s) {
  if (s.C == 0) {
    if (s.op1 > 127) {
      s.pc = s.pc + (s.op1 - 256);
    } else {
      s.pc = s.pc + s.op1;
    }
  }
  return s;
}

// (BLS k): Adjust the pc by k if unsigned lower or same
// (C == 0 || Z == 1)

leg64St do_BLS(leg64St s) {
  if (s.C == 0 || s.Z == 1) {
    if (s.op1 > 127) {
      s.pc = s.pc + (s.op1 - 256);
    } else {
      s.pc = s.pc + s.op1;
    }
  }
  return s;
}

// (BHI k): Adjust the pc by k if unsigned higher
// (C == 1) && (Z == 0)

leg64St do_BHI(leg64St s) {
  if ((s.C == 1) && (s.Z == 0)) {
    if (s.op1 > 127) {
      s.pc = s.pc + (s.op1 - 256);
    } else {
      s.pc = s.pc + s.op1;
    }
  }
  return s;
}

// (BHS k): Adjust the pc by k if unsigned higher or same
// (C == 1)

leg64St do_BHS(leg64St s) {
  if (s.C == 1) {
    if (s.op1 > 127) {
      s.pc = s.pc + (s.op1 - 256);
    } else {
      s.pc = s.pc + s.op1;
    }
  }
  return s;
}

// (BMI k): Adjust the pc by k if minus
// (N == 1)

leg64St do_BMI(leg64St s) {
  if (s.N == 1) {
    if (s.op1 > 127) {
      s.pc = s.pc + (s.op1 - 256);
    } else {
      s.pc = s.pc + s.op1;
    }
  }
  return s;
}

// (BPL k): Adjust the pc by k if plus
// (N == 0)

leg64St do_BPL(leg64St s) {
  if (s.N == 0) {
    if (s.op1 > 127) {
      s.pc = s.pc + (s.op1 - 256);
    } else {
      s.pc = s.pc + s.op1;
    }
  }
  return s;
}


// (HALT): chase tail

leg64St do_HALT(leg64St s) {
  s.pc = s.pc - 1;
  //    s.insCount--;
  return s;
}


// (NOP): No operation

leg64St do_NOP(leg64St s) {
  return s;
}


// Instruction selector

leg64St do_Inst(leg64St s) {
  ui8 opc = s.opcode;
  
  if (opc == NOP) {
    return do_NOP(s);
  } else if (opc == HALT) {
    return do_HALT(s);
  } else if (opc == ADD) {
     return do_ADD(s);
  } else if (opc == ADDI) {
    return do_ADDI(s);
  } else if (opc == ASR) {
     return do_ASR(s);
  } else if (opc == CMP) {
    return do_CMP(s);
  } else if (opc == CMPI) {
    return do_CMPI(s);
  } else if (opc == CONST) {
    return do_CONST(s);
  } else if (opc == LSL) {
    return do_LSL(s);
  } else if (opc == LSR) {
    return do_LSR(s);
  } else if (opc == MUL) {
    return do_MUL(s);
  } else if (opc == SUB) {
   return do_SUB(s);
  } else if (opc == SUBI) {
    return do_SUBI(s);
  } else if (opc == LDR) {
    return do_LDR(s);
  } else if (opc == STR) {
    return do_STR(s);
  } else if (opc == B) {
    return do_B(s);
  } else if (opc == BEQ) {
    return do_BEQ(s);
  } else if (opc == BHI) {
    return do_BHI(s);
  } else if (opc == BHS) {
    return do_BHS(s);
  } else if (opc == BLO) {
    return do_BLO(s);
  } else if (opc == BLS) {
    return do_BLS(s);
  } else if (opc == BMI) {
    return do_BMI(s);
  } else if (opc == BNE) {
    return do_BNE(s);
  } else if (opc == BPL) {
    return do_BPL(s);
  } else {
    return do_HALT(s);
    //    s.err = 3;
  }
}


leg64St leg64step(leg64St s) {
  return do_Inst(nextInst(s));
}

leg64St leg64steps(leg64St s, uint count) {
  for (uint i = count;
       (i > 0); // && (s.err == 0));
       i--) {
    s = leg64step(s);
  }
  return s;
}


leg64St setupDMEM(ui12 base, leg64St s) {
  s.dmem[base]   = 10;
  s.dmem[base+1] = 43;
  s.dmem[base+2] = 4;
  s.dmem[base+3] = 22;
  s.dmem[base+4] = 7;
  s.dmem[base+5] = 14;
  s.dmem[base+6] = 43;
  s.dmem[base+7] = 92;
  s.dmem[base+8] = 22;
  s.dmem[base+9] = 43;

  return s;
}


// Produced by online GCC compiler at -O3 optimization

leg64St doFactO3(ui8 n, leg64St s) {

  //  s = resetAll(s);

  // The algorithm of *fact-program* is as follows.  regs[0] holds the input.

  s.regs[0] = n;

  s.regs[1] = 1;  // accum

  ui10 k = 0;    // Beginning code address
  
  //  '((CONST 0 0 n)     ; 0   r0 <- n
  s.cmem[k] = ((CONST & 0xff) << 24) | (n & 0xff); k=k+1;

  //    (CONST 1 0 1)     ; 1   r1 <- 1
  s.cmem[k] = ((CONST & 0xff) << 24) | (1 << 16) | 1; k=k+1;

  //    (CMPI 0 1)        ; 2
  s.cmem[k] = ((CMPI & 0xff) << 24) | (1 << 8) | 0; k=k+1;

  //      (BLS .L2)       ; 3
  s.cmem[k] = ((BLS & 0xff) << 24) | (4 << 16) | 0; k=k+1;

  // .L3  (MUL 1 1 0)     ; 4   r1 = r1 * r0 <-- loop
  s.cmem[k] = ((MUL & 0xff) << 24) | (1 << 16) | (1 << 8) | 0; k=k+1;

  //      (SUBI 0 0 1)    ; 5   r0 = r0 - 1
  s.cmem[k] = ((SUBI & 0xff) << 24) | 1; k=k+1;

  //      (CMPI 0 1)      ; 6
  s.cmem[k] = ((CMPI & 0xff) << 24) | (1 << 8) | 0; k=k+1;

  //      (BNE .L3)       ; 7
  s.cmem[k] = ((BNE & 0xff) << 24) | (0xfc << 16) | 0; k=k+1;

  // .L2  (ADDI 0 1 0)    ; 8   r0 <- r1
  s.cmem[k] = ((ADDI & 0xff) << 24) | (1 << 8) | 0; k=k+1;

  //      (HALT)))        ; 9   halt with factorial result in regs[1]
  s.cmem[k] = ((HALT & 0xff) << 24) | 0;

  s = leg64steps(s, ((4 + ((uint)(n-1) * 4)) + 2));

  return s;
}


leg64St doFact(ui8 n, leg64St s) {

  //  s = resetAll(s);

  // The algorithm of *fact-program* is as follows.  regs[0] holds the input.

  s.regs[0] = n;

  s.regs[1] = 1;      // accum

  ui10 k = 0;    // Beginning code address
  
  //    '((CONST 0 0 n)   ; 0   r0 <- n
  s.cmem[k] = ((CONST & 0xff) << 24) | (n & 0xff); k=k+1;

  //      (CONST 1 0 1)   ; 1   r1 <- 1
  s.cmem[k] = ((CONST & 0xff) << 24) | (1 << 16) | 1; k=k+1;

  //      (CONST 2 0 20)  ; 2   r2 <- 20
  s.cmem[k] = ((CONST & 0xff) << 24) | (2 << 16) | 20; k=k+1;

  //      (CMP 0 2))      ; 3
  s.cmem[k] = ((CMP & 0xff) << 24) | (2 << 8) | 0; k=k+1;

  //      (BHS .L2)       ; 4
  s.cmem[k] = ((BHS & 0xff) << 24) | (5 << 16) | 0; k=k+1;

  //      (CMPI 0 0)      ; 5
  s.cmem[k] = ((CMPI & 0xff) << 24) | 0; k=k+1;

  //      (BEQ .L2)       ; 6
  s.cmem[k] = ((BEQ & 0xff) << 24) | (3 << 16) | 0; k=k+1;

  // .L3  (MUL 1 1 0)     ; 7   r1 = r1 * r0 <-- loop
  s.cmem[k] = ((MUL & 0xff) << 24) | (1 << 16) | (1 << 8) | 0; k=k+1;

  //      (SUBI 0 0 1)    ; 8   r0 = r0 - 1
  s.cmem[k] = ((SUBI & 0xff) << 24) | 1; k=k+1;

  //      (B .L3)         ; 9
  s.cmem[k] = ((B & 0xff) << 24) | (0xfb << 16) | 0; k=k+1;

  // .L2  (ADDI 0 1 0)    ; 10  r0 <- r1
  s.cmem[k] = ((ADDI & 0xff) << 24) | (1 << 8) | 0; k=k+1;

  //      (HALT)))        ; 11  halt with factorial result in regs[1]
  s.cmem[k] = ((HALT & 0xff) << 24) | 0;

  s = leg64steps(s, (5 + ((uint)n * 5) + 4));

  return s;
}


leg64St doSumArr(ui12 arr, ui12 n, leg64St s) {

  //  s = resetAll(s);

  // The algorithm of sumarr is as follows.  regs[0] holds the base address of
  // the array, and regs[1] hold the number of array elements to add, n.

  s.regs[0] = arr;

  s.regs[1] = n;

  ui10 k = 0;    // Beginning code address

  //        ADDI  r5, r0, #0     ; 0    r5 <- r0 (array base)
  s.cmem[k] = ((ADDI & 0xff) << 24) | (5 << 16) | 0; k=k+1;

  //        CONST r0, 0          ; 1    r0 (sum) <- 0
  s.cmem[k] = ((CONST & 0xff) << 24) | 0; k=k+1;

  //        CMPI  r1, #0         ; 2    n =?= 0
  s.cmem[k] = ((CMPI & 0xff) << 24) | (1 << 16) | 0; k=k+1;

  //        BEQ   .L4            ; 3    branch to done if true
  s.cmem[k] = ((BEQ & 0xff) << 24) | (10 << 16) | 0; k=k+1;

  //        CONST r2, 0          ; 4    r2 (j) <- 0
  s.cmem[k] = ((CONST & 0xff) << 24) | (2 << 16) | 0; k=k+1;

  //  .L3:  CMP   r1, r2         ; 5    n =?= j
  s.cmem[k] = ((CMP & 0xff) << 24) | (1 << 16) | (2 << 8) | 0; k=k+1;

  //        BLS   .L4            ; 6    branch if n <= j
  s.cmem[k] = ((BLS & 0xff) << 24) | (7 << 16) | 0; k=k+1;

  //        ADDI  r3, r2, 0      ; 7    r3 <- j
  s.cmem[k] = ((ADDI & 0xff) << 24) | (3 << 16) | (2 << 8) | 0; k=k+1;

  //        LSL   r3, r3, 0      ; 8    offset <- j << 0
  s.cmem[k] = ((LSL & 0xff) << 24) | (3 << 16) | (3 << 8) | 0; k=k+1;

  //        ADD   r3, r5, r3     ; 9    r3 <- base + offset
  s.cmem[k] = ((ADD & 0xff) << 24) | (3 << 16) | (5 << 8) | 3; k=k+1;

  //        LDR   r4, r3         ; 10   r4 <- array[j]
  s.cmem[k] = ((LDR & 0xff) << 24) | (4 << 16) | (3 << 8) | 0; k=k+1;

  //        ADD   r0, r0, r4     ; 11   sum <- sum + array[j]
  s.cmem[k] = ((ADD & 0xff) << 24) | 4; k=k+1;

  //        ADDI  r2, r2, #1     ; 12   j <- j++
  s.cmem[k] = ((ADDI & 0xff) << 24) | (2 << 16) | (2 << 8) | 1; k=k+1;

  //        B     .L3            ; 13   branch to top of loop .L3
  s.cmem[k] = ((B & 0xff) << 24) | (0xf7 << 16) | 0; k=k+1;

  // .L4:  HALT                 ; 14   halt with sum in regs[0]
  s.cmem[k] = ((HALT & 0xff) << 24) | 0;
  
  s = leg64steps(s, (5 + ((uint)n * 9) + 3));
  // s = leg64steps(s, 23);

  return s;
}


#ifdef COMPILE_ME

int main (int argc, char *argv[]) {

  leg64St s;
  
  cout << endl << "FactO3" << endl;
  
  s = resetAll(s);
  s.pc = 0;

  s = doFactO3(20, s);

  cout << "r0 = " << s.regs[0] << endl;
  cout << "r1 = " << s.regs[1] << endl;
  cout << "pc = " << s.pc << endl;

  
  cout << endl << "Fact" << endl;
  
  s = resetAll(s);
  s.pc = 0;
  
  s = doFact(20, s);

  cout << "r0 = " << s.regs[0] << endl;
  cout << "r1 = " << s.regs[1] << endl;
  cout << "pc = " << s.pc << endl;


  cout << endl << "SumArr" << endl;
  
  s = resetAll(s);
  s.pc = 0;

  s = setupDMEM(8, s);
                              
  s = doSumArr(8, 6, s);

  cout << "r0 = " << s.regs[0] << endl;
  cout << "r1 = " << s.regs[1] << endl;
  cout << "r2 = " << s.regs[2] << endl;
  cout << "r3 = " << s.regs[3] << endl;
  cout << "r4 = " << s.regs[4] << endl;
  cout << "r5 = " << s.regs[5] << endl;
  cout << "pc = " << s.pc << endl;


  cout << endl << "SumArr" << endl;
  
  s = resetAll(s);
  s.pc = 0;

  s = setupDMEM(8, s);

  s = doSumArr(8, 10, s);

  cout << "r0 = " << s.regs[0] << endl;
  cout << "r1 = " << s.regs[1] << endl;
  cout << "pc = " << s.pc << endl;


  cout << endl << "SumArr" << endl;
  
  s = resetAll(s);
  s.pc = 0;

  s = setupDMEM(8, s);

  s = doSumArr(4, 8, s);

  cout << "r0 = " << s.regs[0] << endl;
  cout << "r1 = " << s.regs[1] << endl;
  cout << "pc = " << s.pc << endl;


  return 0;
}

#endif
