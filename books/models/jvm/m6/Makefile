# assume the current directory is currentwork/src/

include Makefile-generic


DEP       = currentwork.src.dep
PYTHON    = python 
BASE      = /home/hbl/currentwork
SRC       = $(BASE)/src
ACL2      = $(BASE)/bin/acl2/acl2-sources/saved_acl2

SUBDIR    = M6 BCV DJVM common M6-DJVM-shared small hanoi


TOP_LEVEL_BOOKS = main/djvm-is-safe.lisp      \
                  main/bcv-is-effective.lisp  \
                  DJVM/INST/inst.lisp         \
                  M6/m6-start-jvm.lisp        \
	          BCV/typechecker.lisp        \
		  M6/m6.pkg.lisp              \
		  DJVM/djvm.pkg.lisp          \
		  M6-DJVM-shared/jvm.pkg.lisp \
		  BCV/bcv.pkg.lisp            \
                  BCV/bcv-succeed-implies-bcv-simple-succeed.lisp \
		  small/bcv-is-effective.lisp  \
		  small/djvm-is-safe.lisp      \
		  hanoi/hanoi-safety.lisp      \
		  M6/ADD1-program-correct.improved.lisp  \
		  M6/factorial-program-correct.improved.lisp  \

TOP_LEVEL_BOOKS_CERT   = $(patsubst %.lisp, %.cert, $(TOP_LEVEL_BOOKS))


include $(DEP)

# ifeq ($(wildcard $(DEP)), $(DEP))
#    include $(DEP)	
# endif

dependencies:
	$(PYTHON) $(BASE)/bin/acl2_collect_dep.py -o $(DEP) $(TOP_LEVEL_BOOKS)



all: $(TOP_LEVEL_BOOKS_CERT)
	touch  done.cert


# there is still problem of dependency on pkg. 
# 
# hand coded dependencies
#

DJVM.pkg: DJVM/djvm.pkg.cert JVM.pkg BCV.pkg
	touch DJVM.pkg

BCV.pkg:  BCV/bcv.pkg.cert
	touch BCV.pkg

M6.pkg:   M6/m6.pkg.cert JVM.pkg
	touch M6.pkg

JVM.pkg:  M6-DJVM-shared/jvm.pkg.cert
	touch JVM.pkg

HANOI.pkg:  
	touch HANOI.pkg

clean: 
	cd common; make clean
	cd M6-DJVM-shared; make clean
	cd DJVM; make clean
	cd M6; make clean
	cd BCV; make clean
	cd DJVM/INST; make clean


##############################################

htmls:	
	$(PYTHON) $(BASE)/bin/lexer.py $(SRC)/$(DEP) | sort -u | grep ".lisp" > _tmp_file_list_
	rsync --quiet --delete --dirs --relative --files-from=_tmp_file_list_  $(SRC) $(SRC)/dist2 
	$(PYTHON) $(BASE)/bin/htmlize.py  $(SRC)/dist2 > /dev/null
	cd $(SRC)/dist2; find * -name *.html -print > $(SRC)/_html_to_distribute_

stirling:	clean-src-dist	
	rsync -ulvr  --exclude="*.o" --exclude="*.out" --exclude "*.cert" --exclude "*.lisp~" --exclude "*.c"  $(BASE)/src/dist/* hbl@stirling:~/currentwork/src/

clean-src-dist:
	$(PYTHON) $(BASE)/bin/lexer.py $(SRC)/$(DEP) | sort -u | grep  -v ".cert" > _source_to_distribute_
	echo "Makefile" >> _source_to_distribute_
	echo "Makefile-generic" >> _source_to_distribute_
	echo "Makefile-subdir" >> _source_to_distribute_
	echo "M6-DJVM-shared/jvm.pkg" >> _source_to_distribute_
	echo "M6/m6.pkg" >> _source_to_distribute_
	echo "DJVM/djvm.pkg" >> _source_to_distribute_
	echo "BCV/bcv.pkg" >> _source_to_distribute_
	echo "M6/Makefile" >> _source_to_distribute_
	echo "DJVM/Makefile" >> _source_to_distribute_
	echo "BCV/Makefile" >> _source_to_distribute_
	echo "common/Makefile" >> _source_to_distribute_
	echo "hanoi/hanoi.pkg" >> _source_to_distribute_
	echo "$(DEP)" >> _source_to_distribute_
	rsync --quiet --delete --dirs --relative --files-from=_source_to_distribute_  $(SRC) $(SRC)/dist 
	rsync --dirs --relative --files-from=_html_to_distribute_  $(SRC)/dist2 $(SRC)/dist

dot: 
	python $(BASE)/bin/dep2dot.py $(DEP) > $(DEP).dot
	dot -Tps -o $(DEP).ps $(DEP).dot
