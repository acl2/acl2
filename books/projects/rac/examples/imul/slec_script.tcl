# Global variables

set_verification_mode -system_manual
config_trace_files -simdump

# Designs

# replace directory below with one that contains rac.h, ac_int.h, and ac_fixed.h

build_design -spec imul.cpp -I/projects/pd/ares_val/davrus01/imul 
build_design -impl imul.sv

# Verification

verify -mode full_proof
