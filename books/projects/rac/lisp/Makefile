
all: translate.cert

translate.cert: translate.lisp
	echo '(certify-book "translate")' | ${ACL2}

clean:

veryclean: clean
	rm -f *.cert *.*x64fsl *.port *.cert.time *.cert.out *.fasl
