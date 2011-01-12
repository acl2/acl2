include ../Makefile-generic
-include Makefile-deps

top.cert: save.cert display.cert topics.cert defxdoc-raw.cert mkdir-raw.cert

.PHONY: moreclean
moreclean:
	rm -rf manual
	rm -rf *.time

clean: moreclean
