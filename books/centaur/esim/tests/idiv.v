/*

VL Regression Suite
Copyright (C) David L. Rager

License: (An MIT/X11-style license)

Permission is hereby granted, free of charge, to any person obtaining a
copy of this software and associated documentation files (the "Software"),
to deal in the Software without restriction, including without limitation
the rights to use, copy, modify, merge, publish, distribute, sublicense,
and/or sell copies of the Software, and to permit persons to whom the
Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
DEALINGS IN THE SOFTWARE.

Original author: David Rager <ragerdl@defthm.com>

Other entities should feel free to add to the "VL Regression Suite"
with files that have different licenses and/or copyrights.


This file is a derived work from the following, which has no specific
  license:

   http://commdspfpga.blogspot.com/2012/09/unsiged-integer-divider-in-verilog.html


The module below divides an eight bit number by a four bit number.  We
use both "output"s and "reg"s for the outputs, because VL doesn't yet
support "output reg"s.

As of August 6, 2013, I have proved that resetting the divider resets
the outputs.  Correctness of the output under non-reset conditions
remains to be done.

Something else I'd like to do is reinstate the parameters, as opposed
to hard coded "8" and "4" values.  This may require further improving
VL.

*/

//=================================================
//`timescale 1ns / 1ps

/*********************************************************************************/
/* Unsigned Integer Divider Module                   */
/*********************************************************************************/
module udivider_v5
(
 input [8-1:0] iDIVIDEND,   // 0 ~ 2**(8)-1
 input [4-1:0] iDIVISOR,   // 1 ~ 2**(4)-1
 input        iDIVVLD,
 input        iRESET,
 input        CLK,
 output reg [8-1:0] oQUOTIENT,
 output reg [4-1:0] oREMAINDER,
 output reg         oDONE
);
/*********************************************************************************/
/* Derived Parameters                    */
/*********************************************************************************/
// parameter EXT_8 = 4 + 8;
/*********************************************************************************/
/* Generate rVIVVLD_D1, rDIVVLD_D2, rSTART_D1, rSTART_D1, based on iDIVVLD   */
/*********************************************************************************/
wire wSTART;
reg rSTART_D1;
reg rDIVVLD_D1;
reg rDIVVLD_D2;

// [Jared] commenting this out after changes to VL port list parsing.  Previous
// versions of VL incorrectly permitted (and indeed, likely required!) these to
// be redeclared.
//
// See the documentation of VL2014::VL-PARSE-PORT-DECLARATION-ATTS-2005 for more
// discussion about the Verilog-2005 case, and see SystemVerilog-2012 23.2.2.2
// (page 666) for the SystemVerilog case.
//
// reg [8-1:0] oQUOTIENT;
// reg [4-1:0] oREMAINDER;
// reg 		oDONE;

always @ (posedge CLK)
begin
 if (iRESET)
  begin
  rDIVVLD_D1 <= 0;
  end else
  begin
  rDIVVLD_D1 <= iDIVVLD;
  end
end

always @ (posedge CLK)
begin
 if (iRESET)
  begin
  rDIVVLD_D2 <= 0;
  end else
  begin
  rDIVVLD_D2 <= rDIVVLD_D1;
  end
end

always @ (posedge CLK)
begin
 if (iRESET)
  begin
  rSTART_D1 <= 0;
  end else
  begin
  rSTART_D1 <= wSTART;
  end
end

assign wSTART = rDIVVLD_D1 && ~rDIVVLD_D2;
/*********************************************************************************/
/* Latch iDIVISOR and iDIVIDEND on rSTART_D1             */
/*********************************************************************************/
reg [4:0] rDIVISOR_POS;
reg [4:0] rDIVISOR_NEG;
always @ (posedge CLK)
begin
 if (iRESET)
 begin
  rDIVISOR_POS <= 0;
 end else if (wSTART)
 begin
  rDIVISOR_POS <= {1'b0, iDIVISOR};
 end
end

always @ (posedge CLK)
begin
 if (iRESET)
 begin
  rDIVISOR_NEG <= 0;
 end else if (wSTART)
 begin
  rDIVISOR_NEG <= {1'b1, ~iDIVISOR + 1};
 end
end

wire [4:0] wEXTZEROS;
assign wEXTZEROS = 0;
/*********************************************************************************/
/* Select between rDIVISOR_POS and rDIVISOR_NEG             */
/* based on subtract result                  */
/*********************************************************************************/
reg  [4:0]  rDIVISOR_TC;
reg [4:0] rREMAINDER;
wire [4:0] wREMAINDER_1;
always @ (posedge CLK)
 begin
 if (iRESET || wSTART)
 begin
 rDIVISOR_TC <= 0;
  //rDIVISOR_TC <= rDIVISOR_NEG;
 end else if (wREMAINDER_1[4])
 begin
  rDIVISOR_TC <= rDIVISOR_POS;
 end else if (~wREMAINDER_1[4])
 begin
  rDIVISOR_TC <= rDIVISOR_NEG;
 end
end
/*********************************************************************************/
/* Initialize rREMAINDER at rSTART_D1               */
/* Load and Left Shift rREMAINDER at each rLSHIFT cycle         */
/*********************************************************************************/
reg rLSHIFT;
reg [8-1:0] rQUOTIENT;
reg [7:0] rCOUNT; // 8
always @ (posedge CLK)
begin
 if (iRESET || wSTART)
 begin
  rREMAINDER <= 0;
 end else if (rSTART_D1)
 begin
  // rREMAINDER <= { wEXTZEROS[4-1:1], iDIVIDEND[8-1] };
  rREMAINDER <= { { (4-1){1'b0}}, iDIVIDEND[8-1] };
  // Extend 4 zeros to iDIVIDEND, so that iDIVISOR > rREMAINDER
 end else if (rLSHIFT)
 begin
  rREMAINDER <= { wREMAINDER_1[4-1:0], rQUOTIENT[8-1] };
  // Left shift rREMAINDER by 1 bit, shift rQUOTIENT[8-1] to
  // rREMAINDER[0]
 end
end
/*********************************************************************************/
/* Compute wREMAINDER_1 as rDIVISOR_TC + rREMAINDER          */
/*********************************************************************************/
assign wREMAINDER_1 = rDIVISOR_TC + rREMAINDER;
/*********************************************************************************/
/* Iniitalize rQUOTIENT at rSTART_D1               */
/* Left Shift rQUOTIENT at rLSHIFT cycle              */
/*********************************************************************************/
always @ (posedge CLK)
begin
 if (iRESET || wSTART )
 begin
  rQUOTIENT <= 0;
 end else if (rSTART_D1 )
 begin
  rQUOTIENT <=  {iDIVIDEND[8-2:0], 1'b0};
  // Initialize rQUOTIENT
 end else if (rLSHIFT)
 begin
  rQUOTIENT <= { rQUOTIENT[8-2:0], ~wREMAINDER_1[4] };
  // Left shift rQUOTIENT by 1 bit, shift ~wREMAINDER_1[4] to
  // rQUOTIENT[0]
 end
end
/*********************************************************************************/
/* Restore the remainder at last iteration by adding rDIVISOR_POS if a 0 Quotient*/
/*********************************************************************************/
reg [4-1:0] rRESTORE;
always @ (posedge CLK)
begin
 if (iRESET || wSTART)
 begin
  rRESTORE <= 0;
 end else if (rCOUNT == 8-1 && wREMAINDER_1[4])
 begin
  rRESTORE <= wREMAINDER_1 + rDIVISOR_POS;
 end else if (rCOUNT == 8-1 && ~wREMAINDER_1[4])
 begin
  rRESTORE <= wREMAINDER_1;
 end
end
/*********************************************************************************/
/* rLSHIFT and DONE signals generation based on iDONE          */
/*********************************************************************************/
//reg rLSHIFT;
reg rDONE;
always @ ( posedge CLK)
begin
 if (iRESET || rCOUNT == 8-1)
 begin
  rLSHIFT <= 0;
 end else if (rSTART_D1)
 begin
  rLSHIFT <= 1;
 end
end

always @ ( posedge CLK)
begin
 if (iRESET || rSTART_D1 || rCOUNT == 8-1)
 begin
  rCOUNT <= 0;
 end else if (rLSHIFT)
 begin
  rCOUNT <= rCOUNT + 1;
 end
end

always @ ( posedge CLK)
begin
 if (iRESET || rSTART_D1 || rDONE)
 begin
  rDONE <= 0;
 end else if ( rCOUNT == 8-1)
 begin
  rDONE <= 1;
 end
end
/*********************************************************************************/
/* output registers                     */
/*********************************************************************************/
always @ (posedge CLK)
begin
 if (iRESET || rSTART_D1)
 begin
  oQUOTIENT <= 0;
 end else if (rDONE)
 begin
  oQUOTIENT <= rQUOTIENT;
 end
end

always @ (posedge CLK)
begin
 if (iRESET || rSTART_D1)
 begin
  oREMAINDER <= 0;
 end else if (rDONE)
 begin
  oREMAINDER <= rRESTORE;
 end
end


always @ (posedge CLK)
begin
 if (iRESET || rSTART_D1)
 begin
  oDONE <= 0;
 end else
 begin
  oDONE <= rDONE;
 end
end
endmodule

/*********************************************************************************/
/* End of Unsigned Divider Module                */
/*********************************************************************************/

/*
Running Results:

#
#  X =        254,   D =          1,    Q =        254   R=          0
#  X       =11111110,   D =0001,    Q =11111110   R=0000
#  rPRODUCT=11111110,         rPASS=1   rERRCOUNT=   0
#
#  X =        254,   D =          2,    Q =        127   R=          0
#  X       =11111110,   D =0010,    Q =01111111   R=0000
#  rPRODUCT=11111110,         rPASS=1   rERRCOUNT=   0
#
#  X =        254,   D =          3,    Q =         84   R=          2
#  X       =11111110,   D =0011,    Q =01010100   R=0010
#  rPRODUCT=11111110,         rPASS=1   rERRCOUNT=   0
#
#  X =        254,   D =          4,    Q =         63   R=          2
#  X       =11111110,   D =0100,    Q =00111111   R=0010
#  rPRODUCT=11111110,         rPASS=1   rERRCOUNT=   0
#
#  X =        254,   D =          5,    Q =         50   R=          4
#  X       =11111110,   D =0101,    Q =00110010   R=0100
#  rPRODUCT=11111110,         rPASS=1   rERRCOUNT=   0
#
#  X =        254,   D =          6,    Q =         42   R=          2
#  X       =11111110,   D =0110,    Q =00101010   R=0010
#  rPRODUCT=11111110,         rPASS=1   rERRCOUNT=   0
#
#  X =        254,   D =          7,    Q =         36   R=          2
#  X       =11111110,   D =0111,    Q =00100100   R=0010
#  rPRODUCT=11111110,         rPASS=1   rERRCOUNT=   0
#
#  X =        254,   D =          8,    Q =         31   R=          6
#  X       =11111110,   D =1000,    Q =00011111   R=0110
#  rPRODUCT=11111110,         rPASS=1   rERRCOUNT=   0
#
#  X =        254,   D =          9,    Q =         28   R=          2
#  X       =11111110,   D =1001,    Q =00011100   R=0010
#  rPRODUCT=11111110,         rPASS=1   rERRCOUNT=   0
#
#  X =        254,   D =         10,    Q =         25   R=          4
#  X       =11111110,   D =1010,    Q =00011001   R=0100
#  rPRODUCT=11111110,         rPASS=1   rERRCOUNT=   0
#
#  X =        254,   D =         11,    Q =         23   R=          1
#  X       =11111110,   D =1011,    Q =00010111   R=0001
#  rPRODUCT=11111110,         rPASS=1   rERRCOUNT=   0
#
#  X =        254,   D =         12,    Q =         21   R=          2
#  X       =11111110,   D =1100,    Q =00010101   R=0010
#  rPRODUCT=11111110,         rPASS=1   rERRCOUNT=   0
#
#  X =        254,   D =         13,    Q =         19   R=          7
#  X       =11111110,   D =1101,    Q =00010011   R=0111
#  rPRODUCT=11111110,         rPASS=1   rERRCOUNT=   0
#
#  X =        254,   D =         14,    Q =         18   R=          2
#  X       =11111110,   D =1110,    Q =00010010   R=0010
#  rPRODUCT=11111110,         rPASS=1   rERRCOUNT=   0
#
#  X =        254,   D =         15,    Q =         16   R=         14
#  X       =11111110,   D =1111,    Q =00010000   R=1110
#  rPRODUCT=11111110,         rPASS=1   rERRCOUNT=   0
#
#
#
#  X =        255,   D =          1,    Q =        255   R=          0
#  X       =11111111,   D =0001,    Q =11111111   R=0000
#  rPRODUCT=11111111,         rPASS=1   rERRCOUNT=   0
#
#  X =        255,   D =          2,    Q =        127   R=          1
#  X       =11111111,   D =0010,    Q =01111111   R=0001
#  rPRODUCT=11111111,         rPASS=1   rERRCOUNT=   0
#
#  X =        255,   D =          3,    Q =         85   R=          0
#  X       =11111111,   D =0011,    Q =01010101   R=0000
#  rPRODUCT=11111111,         rPASS=1   rERRCOUNT=   0
#
#  X =        255,   D =          4,    Q =         63   R=          3
#  X       =11111111,   D =0100,    Q =00111111   R=0011
#  rPRODUCT=11111111,         rPASS=1   rERRCOUNT=   0
#
#  X =        255,   D =          5,    Q =         51   R=          0
#  X       =11111111,   D =0101,    Q =00110011   R=0000
#  rPRODUCT=11111111,         rPASS=1   rERRCOUNT=   0
#
#  X =        255,   D =          6,    Q =         42   R=          3
#  X       =11111111,   D =0110,    Q =00101010   R=0011
#  rPRODUCT=11111111,         rPASS=1   rERRCOUNT=   0
#
#  X =        255,   D =          7,    Q =         36   R=          3
#  X       =11111111,   D =0111,    Q =00100100   R=0011
#  rPRODUCT=11111111,         rPASS=1   rERRCOUNT=   0
#
#  X =        255,   D =          8,    Q =         31   R=          7
#  X       =11111111,   D =1000,    Q =00011111   R=0111
#  rPRODUCT=11111111,         rPASS=1   rERRCOUNT=   0
#
#  X =        255,   D =          9,    Q =         28   R=          3
#  X       =11111111,   D =1001,    Q =00011100   R=0011
#  rPRODUCT=11111111,         rPASS=1   rERRCOUNT=   0
#
#  X =        255,   D =         10,    Q =         25   R=          5
#  X       =11111111,   D =1010,    Q =00011001   R=0101
#  rPRODUCT=11111111,         rPASS=1   rERRCOUNT=   0
#
#  X =        255,   D =         11,    Q =         23   R=          2
#  X       =11111111,   D =1011,    Q =00010111   R=0010
#  rPRODUCT=11111111,         rPASS=1   rERRCOUNT=   0
#
#  X =        255,   D =         12,    Q =         21   R=          3
#  X       =11111111,   D =1100,    Q =00010101   R=0011
#  rPRODUCT=11111111,         rPASS=1   rERRCOUNT=   0
#
#  X =        255,   D =         13,    Q =         19   R=          8
#  X       =11111111,   D =1101,    Q =00010011   R=1000
#  rPRODUCT=11111111,         rPASS=1   rERRCOUNT=   0
#
#  X =        255,   D =         14,    Q =         18   R=          3
#  X       =11111111,   D =1110,    Q =00010010   R=0011
#  rPRODUCT=11111111,         rPASS=1   rERRCOUNT=   0
#
#  X =        255,   D =         15,    Q =         17   R=          0
#  X       =11111111,   D =1111,    Q =00010001   R=0000
#  rPRODUCT=11111111,         rPASS=1   rERRCOUNT=   0
#
#
#
# X ranges from           0 to         255.
# D ranges from           1 to          15.
#           0
# Expected Number of Cases: (2**8)*( (2**4) - 1) =        3840.
# Total        3840 cases examined. Number of Erros:    0
*/
