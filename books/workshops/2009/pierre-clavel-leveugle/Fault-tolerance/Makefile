# EDIT THE FOLLOWING by replacing the directory with your ACL2 distributed
# books directory.  You are welcome to omit this line, or not as you prefer, in
# your contribution.
ACL2_SYSTEM_BOOKS ?= ../../../..

include ${ACL2_SYSTEM_BOOKS}/Makefile-generic

# OPTIONALLY EDIT THE FOLLOWING.  But do not use "time" or "nice"; at least one
# of these can cause trouble in some environments.
ACL2 = ${ACL2_SYSTEM_BOOKS}/../saved_acl2

# From make dependencies:

ATM-TMR.cert: ATM-TMR.lisp
ATM-TMR.cert: register-TMR.cert

ATM-det.cert: ATM-det.lisp
ATM-det.cert: register-det.cert

error-model.cert: error-model.lisp
# error-model.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic-3/top.cert
# error-model.cert: $(ACL2_SYSTEM_BOOKS)/make-event/defspec.cert

register-TMR.cert: register-TMR.lisp
register-TMR.cert: error-model.cert

register-det.cert: register-det.lisp
register-det.cert: error-model.cert

register.cert: register.lisp
register.cert: error-model.cert
