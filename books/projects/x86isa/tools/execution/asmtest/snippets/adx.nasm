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
	
define_two_dw_input_one_dw_output_masked_flags adox32, 0xB02, adox r9d, r8d
define_two_qw_input_one_qw_output_masked_flags adox64, 0xB02, adox r9, r8


define_two_dw_input_one_dw_output_masked_flags adcx32, 0xB02, adcx r9d, r8d
define_two_qw_input_one_qw_output_masked_flags adcx64, 0xB02, adcx r9, r8
