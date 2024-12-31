if [ "$1" = "-default" ]; then
  echo "static char const *const git_commit =  \"Uknown version\";" > version.h.tmp;
else
  acl2_version=$(grep --only-matching 'ACL2 Version [[:digit:]]\+.[[:digit:]]\+' ../../../../README.md)

  # Are we inside a git ? If so get the commit hash, if not it should be
  # a release.
  if [ -d ../../../../.git ]; then
    commit=$(git describe --always --dirty --match 'NOT A TAG' || true)
    if [ $? != 0 ]; then
      commit="Uknown version"
    fi
  else
    commit="release"
  fi

  echo "static char const *const git_commit =  \"$acl2_version $commit\";" > version.h.tmp;
fi

# Only modify version.h if the version has changed. This avoid useless
# re-compilation
if diff -q version.h.tmp version.h >/dev/null 2>&1; then
  rm version.h.tmp;
else
  mv version.h.tmp version.h;
fi
