# Instructions:

# Before starting, see "Dependencies" below.

# In the shell, execute
# make
# to certify all books.
# To clean up (removing files *.cert, *.o, *.fasl, etc.), in the shell execute
# make clean

include ../../../../Makefile-generic

ACL2 = ../../../../../saved_acl2

# Dependencies:
# In the shell, execute
# make -s dependencies
# to obtain the result below.

collect_msg_book.cert: collect_msg_book.lisp
collect_msg_book.cert: predicatesNCie.cert
collect_msg_book.cert: node.cert

getting_rid_of_mod.cert: getting_rid_of_mod.lisp
getting_rid_of_mod.cert: routing_defuns.cert

intersect.cert: intersect.lisp
intersect.cert: ../../../../data-structures/list-defuns.cert
intersect.cert: ../../../../data-structures/list-defthms.cert
intersect.cert: predicatesNCie.cert

local_trip_book.cert: local_trip_book.lisp
local_trip_book.cert: trip_book.cert
local_trip_book.cert: ../../../../arithmetic-3/bind-free/top.cert
local_trip_book.cert: ../../../../arithmetic-3/floor-mod/floor-mod.cert

make_travel_list_book.cert: make_travel_list_book.lisp
make_travel_list_book.cert: routing_main.cert
make_travel_list_book.cert: ../../../../arithmetic-3/bind-free/top.cert
make_travel_list_book.cert: ../../../../arithmetic-3/floor-mod/floor-mod.cert

mod_lemmas.cert: mod_lemmas.lisp
mod_lemmas.cert: ../../../../arithmetic-3/bind-free/top.cert
mod_lemmas.cert: ../../../../arithmetic-3/floor-mod/floor-mod.cert

node.cert: node.lisp
node.cert: predicatesNCie.cert
node.cert: ../../../../data-structures/list-defuns.cert
node.cert: ../../../../data-structures/list-defthms.cert
node.cert: ../../../../arithmetic-3/bind-free/top.cert
node.cert: ../../../../arithmetic-3/floor-mod/floor-mod.cert

octagon_book.cert: octagon_book.lisp
octagon_book.cert: collect_msg_book.cert
octagon_book.cert: make_travel_list_book.cert
octagon_book.cert: scheduler_book.cert
octagon_book.cert: trip_thms.cert

predicatesNCie.cert: predicatesNCie.lisp

routing_defuns.cert: routing_defuns.lisp
routing_defuns.cert: predicatesNCie.cert
routing_defuns.cert: mod_lemmas.cert

routing_local_lemmas.cert: routing_local_lemmas.lisp
routing_local_lemmas.cert: getting_rid_of_mod.cert

routing_main.cert: routing_main.lisp
routing_main.cert: predicatesNCie.cert
routing_main.cert: routing_local_lemmas.cert

scheduler_book.cert: scheduler_book.lisp
scheduler_book.cert: intersect.cert

switch.cert: switch.lisp

trip_book.cert: trip_book.lisp
trip_book.cert: switch.cert
trip_book.cert: predicatesNCie.cert
trip_book.cert: ../../../../data-structures/list-defuns.cert
trip_book.cert: ../../../../data-structures/list-defthms.cert

trip_thms.cert: trip_thms.lisp
trip_thms.cert: local_trip_book.cert






