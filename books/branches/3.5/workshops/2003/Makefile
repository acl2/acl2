# Makefile for certifying workshop-2003 books.

# The following do not have any supporting materials with certifiable books:
# gamboa-patterson/support
# gamboa_lit-programming/support
# manolios-vroon

# Here are the directories containing books to be certified.

DIRS =  austel/support \
	cowles-gamboa-van-baalen_matrix/support \
	gamboa-cowles-van-baalen/support \
	greve-wilding_defrecord/support \
	greve-wilding_mbe/support \
	greve-wilding-vanfleet/support \
	hbl/support \
	hendrix/support \
	kaufmann/support \
	matlin-mccune/support \
	moore_rockwell/support \
	moore_vcg/support \
	ray-matthews-tuttle/support \
	schmaltz-al-sammane-et-al/support \
	schmaltz-borrione/support \
	sumners/support \
	sustik/support \
	toma-borrione/support \
	tsong/support \

include ../../Makefile-psubdirs

tar: clean
	@for dir in $(DIRS) ; \
	do \
	tar cvf $$dir.tar $$dir ; \
	done

# Note:  cowles-gamboa-van-baalen_matrix/support needs to precede
#        gamboa-cowles-van-baalen/support.  The following dependency is thus
#        important if we are doing a parallel make.

gamboa-cowles-van-baalen/support: cowles-gamboa-van-baalen_matrix/support
