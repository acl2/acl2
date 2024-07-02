This directory contains a growing set of Axe proofs of crypto code.  In general, each
.lisp file contains a complete Axe proof.

# Examples Included

- aes-128-encrypt-light-and-spec.lisp (proof of bouncycastle's light AES implementation)
- aes-128-encrypt-regular-and-spec.lisp (proof of another bouncycastle AES implementation)

# Upcoming Examples

We are currently (June, 2024) in the process of open sourcing many
more Axe crypto examples.  If there is a crytographic algorithm of
interest to you, please email Eric Smith, as we might already have
specified and verified it.

# Setup: Obtaining Java Libraries

The proofs in this directory need access to a specific old version of the Java
libraries (specifically, the rt.jar file).  There is no need to install it or
replace the version of Java on your system.

To obtain it, go to:

https://www.oracle.com/java/technologies/javase/javase7-archive-downloads.html

and download the file:

jdk-7u80-linux-x64.tar.gz

(To do this, I had to create an Oracle account and accept a license. I did this
on 4/20/23.)

The sha1sum and md5sum of jdk-7u80-linux-x64.tar.gz are:
- 21e5e18c3511def01590994e926a4350c0509f01  jdk-7u80-linux-x64.tar.gz
- 6152f8a7561acf795ca4701daa10a965  jdk-7u80-linux-x64.tar.gz

Then, after ensuring the .tar.gz file is in this examples/crypto/ directory, do:
tar xfz jdk-7u80-linux-x64.tar.gz

The sha1sum and md5sum of jdk1.7.0_80/jre/lib/rt.jar are as follows:
- 92bf5eaaf26a12df691c579a7297d86b5c0dac7c  jdk1.7.0_80/jre/lib/rt.jar
- 52cccf2dbdb2e675b827fd355d7e6658  jdk1.7.0_80/jre/lib/rt.jar

# Setup: Obtaining the Bouncycastle Crypto Code

To obtain the Bouncycastle .jar, do:

wget https://www.bouncycastle.org/download/jce-jdk13-134.jar

I retrieved this on 4/20/23.

The sha1sum and md5sum of jce-jdk13-134.jar are as follows:
- 50ba188b3f7e0339a8d3d6fb42169ebc918776cd  jce-jdk13-134.jar
- b0de021488e46dc83ea6f2c057ca9e22  jce-jdk13-134.jar
