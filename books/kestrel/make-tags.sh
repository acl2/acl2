# 4 regexps below handle the following cases
# 1. (defsomething |a * b = b * a|
# 2. (defsomething a<=b    ; tags files treat '=' specially somehow
# 3. (defsomething foo::fie   ; allow meta-. of fie to find this
# 4. Normal case: allows (defsomething nm ...
#    Note disallowing name to begin with ,(|' to reduce false positives e.g. in backquote sexprs
# All 4 cases allow leading whitespace and foo::defsomething
# Note that defpkg and deftag are indexed

# ETAGS=etags --language=none \
#   --regex="/ *(\([^ \t:]*::\)?def[^ \t)]* +\(|[^|]+|\)/\2/i" \
#   --regex="/ *(\([^ \t:]*::\)?def[^ \t)]* +\([^ \t,('|]*=[^ \t(]*\)/\2/i" \
#   --regex="/ *(\([^ \t:]*::\)?def[^ \t)]* +[^ \t,('|:]*::\([^ \t:]*\)/\2/i" \
#   --regex="/[ \t]*(\([^ \t:]*::\)?def[^ \t:)]* +[^ \t,(|'][^ \t()]*/i"
mv -f TAGS TAGS.old
rm -f TAGS
find . -name '*.lisp' -print0 | (time xargs -0 etags --language=none --regex=@$ACL2_ROOT/books/kestrel/lisp.regex -a)
