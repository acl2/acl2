# Below are the directories containing books to be certified.

# Note: ray-sumners/support has been replaced by an improved version in
# books/defexec/chapter3/qsort/.

DIRS =  cowles-flat/support \
	cowles-primrec/support \
	kaufmann-sumners/support \
	manolios-kaufmann/support \
	martin-alonso-hidalgo-ruiz/support \
	martin-alonso-perez-sancho/support \
	medina-palomo-alonso/support \
	ruiz-alonso-hidalgo-martin-dags/support \
	ruiz-alonso-hidalgo-martin-theory-terms/support

include ../../Makefile-psubdirs

tar: clean
	@for dir in $(DIRS) ; \
	do \
	tar cvf $$dir.tar $$dir ; \
	done
