include $(ACL2_SYSTEM_BOOKS)/Makefile-generic

INHIBIT = (assign inhibit-output-lst (list (quote proof-tree) (quote prove) (quote observation) (quote event) (quote expansion)))

BOOKS = quicksort sort-help insertion-based-sort \
	merge-based-sort mv-root top

quicksort.cert: quicksort.lisp

sort-help.cert: sort-help.lisp
sort-help.cert: ../gen-trees/sets-lists-trees.cert

insertion-based-sort.cert: insertion-based-sort.lisp
insertion-based-sort.cert: sort-help.cert

merge-based-sort.cert: merge-based-sort.lisp
merge-based-sort.cert: sort-help.cert

mv-root.cert: mv-root.lisp
mv-root.cert: ../build/build-term-guards.cert

top.cert: top.lisp
top.cert: mv-root.cert
top.cert: merge-based-sort.cert
top.cert: insertion-based-sort.cert
