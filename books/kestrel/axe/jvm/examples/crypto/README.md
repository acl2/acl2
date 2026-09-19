This directory contains a growing set of Axe proofs of crypto code.  In general, each
.lisp file contains a complete Axe proof.

# Examples Included

- aes-128-encrypt-light-and-spec.lisp (proof of bouncycastle's light AES implementation)
- aes-128-encrypt-regular-and-spec.lisp (proof of another bouncycastle AES implementation)
- aes-128-encrypt-regular-and-spec-alt.lisp (variant of the proof in aes-128-encrypt-regular-and-spec.lisp)

# Upcoming Examples

We are currently (June, 2024) in the process of open sourcing many
more Axe crypto examples.  If there is a crytographic algorithm of
interest to you, please email Eric Smith, as we might already have
specified and verified it.

# Setup: Obtaining Java libraries

See ../README.md and follow the Setup instructions to install the Java
libraries there.  Note that the proofs here refer to rt.jar by the path
../jdk1.7.0_80/jre/lib/rt.jar, so do not skip the step that creates the
jdk1.7.0_80 name.

# Setup: Obtaining the Bouncycastle Crypto Code

The specific version of the Bouncycastle code that we have verified
(release 1.34, built for JDK 1.3, in the file jce-jdk13-134.jar) is no
longer available from bouncycastle.org.  A copy is kept as an asset of
the "Java build assets (1)" release of the KestrelInstitute/acl2-docker
GitHub repository (whose release notes record its provenance; Bouncy
Castle is distributed under an MIT-style license):

https://github.com/KestrelInstitute/acl2-docker/releases/tag/java-assets-1

Download it into this crypto/ directory:

curl -fsSL -O https://github.com/KestrelInstitute/acl2-docker/releases/download/java-assets-1/jce-jdk13-134.jar

(The same file is also available from
https://www.kestrel.edu/download/jce-jdk13-134.jar .)

The sha256sum, sha1sum and md5sum of jce-jdk13-134.jar are as follows:
- 86381e813b09d09825807c9d4f688fd7bead2bbef853c013467f77bf93c16c40  jce-jdk13-134.jar
- 50ba188b3f7e0339a8d3d6fb42169ebc918776cd  jce-jdk13-134.jar
- b0de021488e46dc83ea6f2c057ca9e22  jce-jdk13-134.jar
