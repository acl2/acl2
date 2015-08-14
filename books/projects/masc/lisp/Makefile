
all: translate.cert

translate.cert: translate.lisp
	echo '(certify-book "translate")' | ${ACL2}/saved_acl2

clean:

veryclean: clean
	rm -f *.cert *.lx64fsl *.port
