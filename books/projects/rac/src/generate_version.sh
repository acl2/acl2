commit=$(git describe --always --dirty --match 'NOT A TAG')

echo "#include \"version.h\"\n\n" \
     "char const *const git_commit = \"$commit\";" > version.cpp.tmp;

# Only modify version.cpp if the version has changed. This avoid useless
# re-compilation
if diff -q version.cpp.tmp version.cpp >/dev/null 2>&1;
then
  rm version.cpp.tmp;
else
  mv version.cpp.tmp version.cpp;
fi
