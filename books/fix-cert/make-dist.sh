#! /bin/bash

DIR="$(dirname "$0")"

pushd "$DIR" > /dev/null && DIR="$PWD" && popd > /dev/null
if [ "$?" != "0" ]; then
  echo "Script invoked without path!"
  exit 1
fi

SRC="$1"
DST="$2"


pushd "$SRC" > /dev/null && SRC="$PWD" && popd > /dev/null
if [ "$?" != "0" ]; then
  echo "Usage: $0 <acl2_build_dir> <target_dist_dir>"
  exit 1
fi

mkdir -p "$DST" && pushd "$DST" > /dev/null && DST="$PWD" && popd > /dev/null
if [ "$?" != "0" ]; then
  echo "Usage: $0 <acl2_build_dir> <target_dist_dir>"
  exit 1
fi


if [ '!' -x "$SRC"/saved_acl2 ]; then
  echo "$SRC"/saved_acl2 "not found."
  echo "Please build ACL2."
  exit 1
fi

EXEC_CMD="$(grep '^exec' "$SRC"/saved_acl2)"

if [ "$?" != "0" ]; then
  echo "Could not find \"exec ...\" part of saved_acl2 script."
  exit 1
fi




# Phase 1 -- independent of Lisp type
pushd "$SRC" > /dev/null
echo "Building ${DST}/src.zip ..."
jar cMf "${DST}/src.zip" *.lisp *.lsp *.txt GNUmakefile Makefile LICENSE TAGS || exit 1

echo "Copying html docs ..."
mkdir -p "${DST}/doc"
cp -pR doc/HTML "${DST}/doc" #|| exit 1

echo "Making directories for books ..."
find books -type d -exec mkdir -p "${DST}/{}" ';' || exit 1

echo "Copying books ..."
find books -type f -and -not -name "*.out" -exec cp -p '{}' "${DST}/{}" ';' || exit 1
> "${DST}/books/saved_dir" || exit 1
> "${DST}/books/fix-cert.out" || exit 1

popd > /dev/null


echo "Creating fix-cert.lsp ..."
( cat "${DIR}/fix-cert-pre.lsp" &&
  echo "(defconst *standard-book-list* '(" &&
  pushd "${SRC}/books" > /dev/null &&
  # sort by ascending write time: (helps with defpkg issues)
  if stat --printf='%Y\t%n\n' / > /dev/null 2>/dev/null; then
    # linux
# harshrc Aug 18 '14
# Modified critpath.pl to depchain.pl which gives a topologically sorted (dependency order) list of cert files.
# sed command has slightly changed. I hope this works fine.
      ./fix-cert/depchain.pl $(find * -name '*.cert' -exec stat --printf='%Y\t%n\n' '{}' ';' | sort | cut -f2) | sed 's/^/"/;s/\.cert.*$/"/'
  elif stat -f '%m\t%N' / > /dev/null 2>/dev/null; then
    #Darwin
      ./fix-cert/depchain.pl $(find * -name '*.cert' -exec stat -f '%m%t%N' '{}' ';' | sort | cut -f2) | sed 's/^/"/;s/\.cert.*$/"/'
  else #assume windows
      ./fix-cert/depchain.pl $(find * -name '*.cert' -printf '%T@\t%p\n' | sort | cut -f2)  | sed 's/^/"/;s/\.cert.*$/"/'
  fi &&
  #find * -name '*.cert' -printf '%C@\t%p\n' | sort | cut -f2 | sed 's/[.]cert$/"/;s/^/"/' &&
  popd > /dev/null &&
  echo "))" &&
  cat "${DIR}/fix-cert-post.lsp"
) > "${DST}/fix-cert.lsp" || exit 1


echo "Copying image & creating script ..."


echo "saved_acl2" > "${DST}/exec-files.lst" &&
cp -v "${DIR}/dummy_saved_acl2_template" "${DST}/saved_acl2" &&
chmod a+x "${DST}/saved_acl2" || exit 1

if [ -e "${DIR}/run_acl2-template" ]; then
  echo "run_acl2" >> "${DST}/exec-files.lst" || exit 1
else 
  echo "run_acl2.exe" >> "${DST}/exec-files.lst" || exit 1
fi

echo "Finding the lisp and core..."

IFS=' ' read -a exec_cmd_array <<< "$EXEC_CMD"


find_lisp () {
    local i
    i=0
    local s
    for s in ${EXEC_CMD}; do
        i=$(( i + 1 ))
        case $s in
            exec) LISP=${exec_cmd_array[i]}; echo "found lisp"; return ;;
            *) echo "Lisp executable not found."; exit 1 ;;
        esac     
    done
}

find_core () {
    local i
    i=0
    local s
    for s in ${EXEC_CMD}; do
        i=$(( i + 1 ))
        case $s in
            -I) CORE=${exec_cmd_array[i]}; echo "found core"; return ;;
            --core) CORE=${exec_cmd_array[i]}; echo "found core"; return ;;
        esac     
    done
    echo "Core file not found."; exit 1
}
                


find_lisp
find_core
# SECOND="$(echo "sh -c 'echo \"\$2\"' sh $EXEC_CMD" | sh)"

# Remove double-quotes
LISP=${LISP%\"}
LISP=${LISP#\"}
CORE=${CORE%\"}
CORE=${CORE#\"}
echo "LISP=${LISP}"
echo "CORE=${CORE}"

if [ '!' -x ${LISP} ]; then
    echo ${LISP}
    echo "$(which ${LISP})"
    LISP_RESOLVED="$(which ${LISP})"
  echo "${LISP_RESOLVED}"
  if [ '!' -x "$LISP_RESOLVED" ]; then
    echo "Not found: $LISP"
    exit 1
  fi
  LISP="$LISP_RESOLVED"
fi


# Phase 2 -- Lisp-specific
if echo "$LISP" | grep -q '.gcl$'; then
  # GCL
  cp -v "$LISP" "${DST}/saved_acl2.gcl" &&
  chmod a+x "${DST}/saved_acl2.gcl" &&
  echo "saved_acl2.gcl" >> "${DST}/exec-files.lst" &&
  if [ -e "${DIR}/run_acl2-template" ]; then
    sed 's/\#ACL2_CMD\#/\"\$\{DIR\}\/saved_acl2.gcl\"/' < "${DIR}/run_acl2-template" > "${DST}/run_acl2" &&
    chmod a+x "${DST}/run_acl2" &&
    exit 0
  else 
    cp -v "${DIR}/run_acl2-gcl.exe" "${DST}/run_acl2.exe" &&
    exit 0
  fi
  exit 1
fi

#FOURTH="$(echo "sh -c 'echo \"\$4\"' sh $EXEC_CMD" | sh)"
LISP_NAME="$(basename "$LISP")"
CORE_NAME="$(basename "$CORE")"

if [ '!' -r "${CORE}" ]; then
  echo "Not found: ${CORE}"
  exit 1
fi

if echo "$EXEC_CMD" | grep -q 'acl2::sbcl-restart'; then
  # SBCL
  cp -v "$LISP" "${DST}/${LISP_NAME}" &&
  chmod a+x "${DST}/${LISP_NAME}" &&
  cp -v "$CORE" "${DST}/${CORE_NAME}" &&
  echo "${LISP_NAME}" >> "${DST}/exec-files.lst" &&
  if [ -e "${DIR}/run_acl2-template" ]; then
    sed "s/\#ACL2_CMD\#/\"\$\{DIR\}\/${LISP_NAME}\" --core \"\$\{DIR\}\/${CORE_NAME}\" --userinit \/dev\/null --eval \"\(acl2\:\:sbcl-restart\)\"/" < "${DIR}/run_acl2-template" > "${DST}/run_acl2" &&
    chmod a+x "${DST}/run_acl2" &&
    exit 0
  else 
    cp -v "${DIR}/run_acl2-sbcl.exe" "${DST}/run_acl2.exe" &&
    exit 0
  fi
  exit 1
fi

if echo "$EXEC_CMD" | grep -q 'acl2::acl2-default-restart'; then
  # OpenMCL
  #echo "exec \"\${DIR}/${LISP_NAME}\" -I \"\${DIR}/${CORE_NAME}\" -e '(acl2::acl2-default-restart)'" '"$@"' >> "${DST}/run_acl2" &&
  cp -v "$LISP" "${DST}/${LISP_NAME}" &&
  chmod a+x "${DST}/${LISP_NAME}" &&
  cp -v "$CORE" "${DST}/${CORE_NAME}" &&
  echo "${LISP_NAME}" >> "${DST}/exec-files.lst" &&
  if [ -e "${DIR}/run_acl2-template" ]; then
    sed "s/\#ACL2_CMD\#/\"\$\{DIR\}\/${LISP_NAME}\" -I \"\$\{DIR\}\/${CORE_NAME}\" -e \"\(acl2\:\:acl2-default-restart\)\"/" < "${DIR}/run_acl2-template" > "${DST}/run_acl2" &&
    chmod a+x "${DST}/run_acl2" &&
    exit 0
  else 
    cp -v "${DIR}/run_acl2-ccl.exe" "${DST}/run_acl2.exe" &&
    exit 0
  fi
  exit 1
fi

echo "saved_acl2 script not recognized as GCL, SBCL, or CCL."
exit 1
