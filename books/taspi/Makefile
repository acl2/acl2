# Avoid provisional certification with `make' until we start using Makefile-deps.
override ACL2_PCERT =

top:
	acl2_system_books_temp=`cd .. ; pwd` ; make -f Makefile-actual ACL2_SYSTEM_BOOKS=$$acl2_system_books_temp

clean:
	acl2_system_books_temp=`cd .. ; pwd` ; make -f Makefile-actual clean ACL2_SYSTEM_BOOKS=$$acl2_system_books_temp
