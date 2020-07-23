Supporting materials for "Put Me On the RAC"

1. Simple stack data type implemented using Restricted Algorithmic C (RAC), and automatically 
translated to ACL2, at which point functional correctness proofs can be performed.

2. Example Instruction Set Architecture (ISA) simulator written in RAC, 
and used in a Codewalker proof of correctness for factorial.

Creation of the ACL2 code from the RAC sources (in the sources
directory) requires that the RAC tools are built and installed.
See books/projects/rac for more information on RAC.

To execute the supplied factorial program on the LEG64 ISA simulator:

1. Start ACL2
2. (include-book "leg64")
3. "RTL"
4. (dofact <n> nil)
