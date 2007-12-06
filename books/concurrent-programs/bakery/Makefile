include ../../Makefile-generic

ACL2 = ../../../saved_acl2


apply-total-order.cert: apply-total-order.lisp
# apply-total-order.cert: $(ACL2_SYSTEM_BOOKS)/misc/total-order.cert

fairenv.cert: fairenv.lisp
fairenv.cert: measures.cert
fairenv.cert: records.cert

final-theorems.cert: final-theorems.lisp
final-theorems.cert: labels.cert
final-theorems.cert: stutter1-match.cert
final-theorems.cert: stutter2.cert
final-theorems.cert: initial-state.cert
final-theorems.cert: inv-persists.cert
final-theorems.cert: inv-sufficient.cert

initial-state.cert: initial-state.lisp
initial-state.cert: programs.cert
initial-state.cert: properties.cert

inv-persists.cert: inv-persists.lisp
inv-persists.cert: programs.cert
inv-persists.cert: properties.cert
inv-persists.cert: lexicographic-pos.cert

inv-sufficient.cert: inv-sufficient.lisp
inv-sufficient.cert: programs.cert
inv-sufficient.cert: properties.cert
inv-sufficient.cert: lexicographic-pos.cert
inv-sufficient.cert: properties-of-sets.cert

labels.cert: labels.lisp
labels.cert: properties.cert

lexicographic-pos.cert: lexicographic-pos.lisp
lexicographic-pos.cert: properties.cert
lexicographic-pos.cert: pos-temp.cert

lexicographic.cert: lexicographic.lisp
lexicographic.cert: measures.cert
# lexicographic.cert: $(ACL2_SYSTEM_BOOKS)/misc/total-order.cert

measures.cert: measures.lisp
# measures.cert: $(ACL2_SYSTEM_BOOKS)/ordinals/e0-ordinal.cert

pos-temp.cert: pos-temp.lisp
pos-temp.cert: variables.cert
pos-temp.cert: properties.cert

programs.cert: programs.lisp
programs.cert: variables.cert
programs.cert: lexicographic.cert
programs.cert: fairenv.cert

properties-of-sets.cert: properties-of-sets.lisp
properties-of-sets.cert: records.cert

properties.cert: properties.lisp
properties.cert: lexicographic.cert
properties.cert: measures.cert
properties.cert: properties-of-sets.cert
properties.cert: variables.cert
properties.cert: fairenv.cert

records.cert: records.lisp
records.cert: apply-total-order.cert

stutter1-match.cert: stutter1-match.lisp
stutter1-match.cert: programs.cert
stutter1-match.cert: properties.cert

stutter2.cert: stutter2.lisp
stutter2.cert: programs.cert
stutter2.cert: properties.cert
stutter2.cert: lexicographic-pos.cert
# stutter2.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic-2/meta/top.cert

variables.cert: variables.lisp
variables.cert: records.cert
