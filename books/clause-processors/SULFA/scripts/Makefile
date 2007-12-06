
PERL ?= perl

# make_interpret_sulfa_file makes the interpret_sulfa_file command, using its own 
#   mechanism to check whether the command needs to change.
sexpr-sat-solver: 
	rm -f ${@} ; \
${PERL} interpret_sulfa_file < ${@}.isf > ${@} ; \
chmod ug+x-w ${@}

sulfa-smt: 
	rm -f ${@} ; \
${PERL} interpret_sulfa_file < ${@}.isf > ${@} ; \
chmod ug+x-w ${@}

clean:
	rm -f sexpr-sat-solver *~ \#*\# 
	rm -f *acl2_with_smt* temp_command_file.lisp 
	rm -fr sat-temp-files 
	rm -fr sulfa_smt_temp 
	rm -f sulfa-smt 

# Dependencies
sulfa-smt: interpret_sulfa_file 
sulfa-smt: sulfa-smt.isf 

sexpr-sat-solver: sexpr-sat-solver.isf 

sexpr-sat-solver: interpret_sulfa_file

