# This is an extremely stupid hack for converting render.xsl into a form that
# can be easily loaded into JavaScript.  There's probably a much better way to
# do this.

render.js : render.xsl
	echo "var xslt_base64 = \"" > render.tmp
	base64 < render.xsl >> render.tmp
	echo "\";" >> render.tmp
	tr -d '\n' < render.tmp > render.js
	rm render.tmp
	ls -la render.js

# We don't need to convert render-html.xsl, because we don't need it
# in javascript format.
