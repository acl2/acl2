#!/bin/bash

# safe mode
set -euo pipefail

cd "$(dirname "$0")"

mkdir src || true
cd src

VERSIONS="$1"
if [ -z "$VERSIONS" ]
then
  VERSIONS="openssl-0.9.8zh openssl-1.0.0s openssl-1.0.2q openssl-1.1.0j openssl-1.1.1p openssl-3.0.4 libressl-2.2.7 libressl-2.5.5 libressl-2.6.5 libressl-2.8.3 libressl-3.0.1 libressl-3.5.3"
fi

downloadUrl() {
  version="$1"
  case $version in
      libressl*)
          echo "https://ftp.openbsd.org/pub/OpenBSD/LibreSSL/${version}.tar.gz";;
      openssl-1.0.2q|openssl-1.1.0j|openssl-1.1.1*|openssl-3*)
          echo "https://www.openssl.org/source/${version}.tar.gz";;
      openssl-1.0.0s)
          echo "https://www.openssl.org/source/old/1.0.0/openssl-1.0.0s.tar.gz";;
      openssl-0.9.8zh)
          echo "https://www.openssl.org/source/old/0.9.x/openssl-0.9.8zh.tar.gz";;
  esac
}

for version in $VERSIONS
do
  wget $(downloadUrl "$version")
  tar -xzf "${version}.tar.gz"
done
