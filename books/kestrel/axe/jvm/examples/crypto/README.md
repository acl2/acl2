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

See ../README.md and follow the Setup instructions to install the Java libraries there.

# Setup: Obtaining the Bouncycastle Crypto Code

The specific version of the Bouncycastle code that we have verified
seems to no longer be availabe from bouncycastle.org.  So, download it
from:

https://www.kestrel.edu/download/jce-jdk13-134.jar

The sha1sum and md5sum of jce-jdk13-134.jar are as follows:
- 50ba188b3f7e0339a8d3d6fb42169ebc918776cd  jce-jdk13-134.jar
- b0de021488e46dc83ea6f2c057ca9e22  jce-jdk13-134.jar
