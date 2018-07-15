#--------------------------------------------------------------------
#           Hector command script
#--------------------------------------------------------------------

source $env(HECTOR_HOME)/local/command_script_aux.tcl

# The following procedure should be in some central location:

set cutpoint_index 1

proc verify_cutpoint_equivalence {cs ci} {
  global cutpoint_index
  cutpoint "cp_spec_$cutpoint_index"  = $cs
  cutpoint cp_impl_$cutpoint_index = $ci
  lemma $cs == $ci
  assume "cp_spec_$cutpoint_index"  == cp_impl_$cutpoint_index
  set cutpoint_index [expr $cutpoint_index + 1]
}

set_resource_limit 3000
set_custom_solve_script "orch_custom_bit_operations1"

proc compile_spec {} {
  create_design -name spec -top hectorWrapper
  scdtan imul64.cpp
  compile_design spec
} 

proc compile_impl {} {
  create_design -name impl -top imul64 -options "-cutpoints=imul64.tble"
  vcs -sverilog imul64.vs
  compile_design impl
} 

set_interface_definition_procedure "idf"

proc idf {} {
  notion -specstages 1 -implstages 1 pipeline
  extdef ext.* = impl.*;
  inmap impl.* = ext.*;
  inmap spec.* = ext.*;
}

set_user_assumes_lemmas_procedure "assumptionsAndLemmas"

proc assumptionsAndLemmas {} {
  verify_cutpoint_equivalence spec.tble(1) impl.tble(1)
  lemma prod_claim = spec.prod(1) == impl.prod(1)
}

proc verify {} {
  if {[compile_spec] == 0 ||
      [compile_impl] == 0 ||
      [compose] == 0 || 
      [solve] == 0} {
    puts "FAIL"
  } else {
    puts "PASS"
  }
}
