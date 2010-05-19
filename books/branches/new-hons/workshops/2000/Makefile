# Below are the directories containing books to be certified.

# The following do not have any certifiable books:
# goerigk sawada shumsky wilding

# The following remain to be dealt with:
# cowles/books -- tarai4 is resource-demanding: crashes some lisps, overflows
#                 in others.  At some point we may deal with this.
#                 Also, a change will be needed for v2-6 in tarai6, to get
#                 through lemma tarai=Fb-3.

DIRS =  lusk-mccune/lusk-mccune-final manolios/pipeline \
	medina/polynomials moore-manolios/partial-functions \
	ruiz/multiset ruiz/multiset/examples \
	russinoff-kaufmann/supporting-materials russinoff-short \
	sumners1/cdeq sumners2/bdds

ALLDIRS = $(DIRS) cowles/books

include ../../Makefile-psubdirs

# The following dependency is important if we are doing a parallel make.

ruiz/multiset/examples: ruiz/multiset

tar: clean
	@for dir in $(ALLDIRS) ; \
	do \
	tar cvf $$dir.tar $$dir ; \
	done
