ifndef ACL2
 $(error Variable ACL2 is undefined.)
endif

BUILD_DIR := $(dir $(ACL2))books/build
JOBS ?= 4

all:
	$(BUILD_DIR)/cert.pl -j $(JOBS) -a $(ACL2) *.lisp

# all: translate.cert

# translate.cert: translate.lisp
# 	echo '(certify-book "translate")' | ${ACL2}

clean:

veryclean: clean
	rm -f *.cert *.*x64fsl *.port *.cert.time *.cert.out *.fasl
