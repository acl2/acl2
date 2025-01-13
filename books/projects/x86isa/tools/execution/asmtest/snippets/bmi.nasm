; x86isa assembly snippet testing framework
;
; X86ISA Library
; Copyright (C) 2024 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Sol Swords (sswords@gmail.com)

%include "utils.mac"
	
SECTION .text			;

define_two_dw_input_one_dw_output_masked_flags blsi32, 0xb16, blsi r9d, r8d
define_two_qw_input_one_qw_output_masked_flags blsi64, 0xb16, blsi r9, r8



define_two_w_input_one_w_output_masked_flags popcnt16, 0xb02, db 0x66, 0xf3, 0x45, 0x0f, 0xb8, 0xc8
define_two_dw_input_one_dw_output_masked_flags popcnt32, 0xb02, popcnt r9d, r8d
define_two_qw_input_one_qw_output_masked_flags popcnt64, 0xb02, popcnt r9, r8
