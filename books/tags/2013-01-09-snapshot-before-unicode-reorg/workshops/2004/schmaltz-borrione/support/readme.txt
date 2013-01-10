;;-------------------------------------------------------------------------
;;-------------------------------------------------------------------------
;;
;;
;; Functional Specification and Validation of the Octagon Network on 
;;              Chip using the ACL2 Theorem Prover
;;
;;
;;                          Proof Script
;;
;;
;;                         Julien Schmaltz
;;                     Joseph Fourier University
;;               46, av. Felix Viallet 38031 Grenoble Cedex
;;                             FRANCE
;;                      Julien.Schmaltz@imag.fr
;;
;;-------------------------------------------------------------------------
;;-------------------------------------------------------------------------


;; *************  NOTE: THIS PROOF IS DONE WITH ACL2 V2.9 ****************

;; we use the following books of the distribution:
;;           - list-defuns and list-defthms written by Bill Bevier
;;           - arithmetic-3 written by Robert Krug


1/ HOW TO CERTIFY THE BOOKS?

start ACL2 v2.9 and load the file certify.acl2:
ACL2 !>(ld "certify.acl2")

then, every book will be certified.

or see the Makefile

2/ PROOF STRUCTURE

The main book is "octagon_book.lisp" and contains the proof of correctness
of the function Octagon. The "book tree" looks like:


			     Octagon_book
       /                 /                    \                       \
  trip_thm      collect_msg_book     make_travel_list_book      scheduler_book
     |                  |                      |                      |
local_trip_book       node                routing_main             intersect
     |                                         |
  trip_book                           routing_local_lemmas
     |                                         |
   switch                              getting_rid_of_mod
                                               |
                                          routing_defuns
                                               |
                                            mod_lemmas

Most of the books also imports the book predicatesNCie.lisp 
wich contains the definitions of the predicates used in 
the proofs and some other functions.

     2.1/ TRIP BRANCH

     The book switch.lisp contains only the definition of the function Switch

     The book trip_book.lisp contains the definitions of two functions
     that execute the first/last and the general step of a trip.

     The book local_trip_book contains the validation of these two 
     functions, i.e. messages are not modified if the route is made of
     available moves, if not messages are lost. The main four theorems
     exported by this book are
                   1/ first_travel_=_msg
		      case where the route is valid
		   2/ first_travel_=_msg_not	
		      case where the route is not valid
		   3/ nth_travel_=_msg
		      case where the route is valid
		   4/ nth_travel_=_msg_not
		      case where the route is not valid
     The rest of the events are local to the book.
               
     The book trip_thms.lisp contains the definition and the validation
     of the function Trip. The main theorem (correctness_of_Trip)
     proves that Trip, under some hypotheses, is the identity meaning 
     that the interconnection structure is valid. 


     2.2/ COLLECT_MSG BRANCH

     The book node.lisp contains the definition of the node system, which
     includes the interfaces, local and distant communications, the memory
     functions and the decoder. This book also contains the theorems
     proving the validity of the node system.

     The book collect_msg_book.lisp contains the definition and lemmas about 
     the function collect_msg_book which executes local communications 
     and stores the distant one in a list. 

     These two books export lemmas used for the proof of the Octagon.

     
     2.3/ MAKE_TRAVEL_LIST BRANCH

     The book mod_lemmas.lisp contains the lemmas required to prove that 
     the routing algorithm terminates

     The book routing_defuns.lisp contains the definition of the function
     Route. 

     The book getting_rid_of_mod.lisp contains lemmas implementing a 
     strategy to rewrite function Route in functions that do not use
     function mod

     The book routing_local_lemmas.lisp contains lemmas needed to prove 
     Route correct.

     The book routing_main.lisp contains the main theorem on Route.
     In this book, we define a constrained function named myroute 
     using an encapsulate. This means that every function that will	
     satisfy the theorem in the encapsulate will not modify the rest of 
     the proof. This is an example of how lemmas and theorems can be reused.
     
     The book make_travel_list.lisp contains the definition and lemmas
     about the function make_travel_list which associates to distant
     requests their route.

     2.4/ SCHEDULER BRANCH

     The book intersect.lisp contains lemmas needed to prove function
     scheduler correct. They express properties of the intersection of
     routes and link this concept with other functions, e.g. no-duplicatesp.

     The book scheduler_book.lisp contains the definition and the validation
     of the function scheduler. It exports the main theorem on scheduler,
     that is that this function produces a travel list in which routes	
     do not overlap.

     2.5/ OCTAGON BOOK

     This book is the main book and contains the definition and the validation
     of the Octagon. The main theorems are:
                   1/ all_ok_status_read_Octagon
		      proves that if op_lst contains only "good" distant read
		      orders then the returned status are OK
		   2/ all_ok_status_write_Octagon
		      proves that if op_lst contains only "good" distant write
		      orders then the returned status are OK	
		   3/ mem_ok_read_Octagon
		      proves that if op_lst contains only "good" distant read
		      orders then the global memory is unchanged
		   4/ all_ok_dat_write_Octagon
                      proves that if op_lst contains only "good" distant write
		      orders the data returned to the masters are those
		      they have sent
		   5/ all_ok_dat_read_Octagon
		      proves that if op_lst contains only "good" distant read
		      orders then the returned data to each master is equal
		      to a read (call to the function nth) in the global 
		      memory at the initial global address.
		   6/ all_write_mem_Octagon
		      proves that if op_lst contains only "good" distant write
		      orders than the memory is updated like it would have 
		      been without using the network.
