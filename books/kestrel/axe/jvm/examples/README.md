Axe Examples Involving Java/JVM Code.

The [crypto/](crypto) subdirectory contains Axe proofs of cryptographic algorithms in the "classic" Axe style.

The [formal-unit-tests/](formal-unit-tests) subdirectory contains "formal unit tests": highly automated proofs about small pieces of code.

# Setup: Obtaining STP

See :doc STP, here:

https://acl2.org/doc/?topic=ACL2____STP

for information about installing the STP SMT solver, which is used by
Axe.

# Setup: Obtaining Java Libraries

The proofs in this directory need access to the bootstrap class library
of an old (Java 7) JDK -- specifically, its rt.jar file.  There is no need
to install that JDK or to replace the version of Java on your system:
rt.jar is only read, as a collection of .class files; nothing in it is
ever run.

The rt.jar we use comes from Azul Zulu 7.56.0.11, a build of OpenJDK 7u352
(licensed under the GPLv2 with the Classpath Exception).  A copy of the
Zulu archive is kept as an asset of the "Java build assets (1)" release of
the KestrelInstitute/acl2-docker GitHub repository:

https://github.com/KestrelInstitute/acl2-docker/releases/tag/java-assets-1

The release notes there record where each file came from and its
checksums.

1. Download the archive into this examples/ directory:

curl -fsSL -O https://github.com/KestrelInstitute/acl2-docker/releases/download/java-assets-1/zulu7.56.0.11-ca-jdk7.0.352-linux_x64.tar.gz

If you want to check that you have the exact right file, its sha256sum
(`shasum -a 256 FILE` on macOS, `sha256sum FILE` on Linux) is:
- 8a7387c1ed151474301b6553c6046f865dc6c1e1890bcf106acc2780c55727c8  zulu7.56.0.11-ca-jdk7.0.352-linux_x64.tar.gz

The archive is a Linux x64 JDK, but that does not matter: only rt.jar is
used, and .class files are identical on every platform, so this works
just as well on macOS, including Apple Silicon.

2. Extract just rt.jar from the archive (the rest is a JDK we don't need):

mkdir -p zulu7.56.0.11-ca-jdk7.0.352/jre/lib
tar -xzf zulu7.56.0.11-ca-jdk7.0.352-linux_x64.tar.gz -O zulu7.56.0.11-ca-jdk7.0.352-linux_x64/jre/lib/rt.jar > zulu7.56.0.11-ca-jdk7.0.352/jre/lib/rt.jar

(Alternatively, `tar xfz` the whole archive; rt.jar is then at
zulu7.56.0.11-ca-jdk7.0.352-linux_x64/jre/lib/rt.jar, and the paths in
the following steps change accordingly.)

3. Then, unzip rt.jar like this:

unzip -q zulu7.56.0.11-ca-jdk7.0.352/jre/lib/rt.jar -d zulu7.56.0.11-ca-jdk7.0.352/jre/lib/rt.jar.unzipped

4. The crypto examples refer to rt.jar by the path
../jdk1.7.0_80/jre/lib/rt.jar (the directory name of the Oracle JDK they
were originally developed with; see below), so give that name to the
directory just created:

ln -s zulu7.56.0.11-ca-jdk7.0.352 jdk1.7.0_80

5. Then, set the JAVA_BOOTSTRAP_CLASSES_ROOT environment variable to point
to the unzipped directory (the name should not end in a slash).  For
example, if you have ACL2_ROOT defined, you can do:

export JAVA_BOOTSTRAP_CLASSES_ROOT=${ACL2_ROOT}/books/kestrel/axe/jvm/examples/zulu7.56.0.11-ca-jdk7.0.352/jre/lib/rt.jar.unzipped

6. See also further setup instructions in crypto/README.md if you want to build those examples.

## Alternative: Oracle JDK 7u80

These examples were originally developed and checked against Oracle's JDK
7u80, whose rt.jar can be used instead.  Oracle offers it at

https://www.oracle.com/java/technologies/javase/javase7-archive-downloads.html

as jdk-7u80-linux-x64.tar.gz, after you create an Oracle account and
accept a license; the license does not allow it to be redistributed,
which is why the instructions above use Zulu.  Its sha1sum and md5sum are:
- 21e5e18c3511def01590994e926a4350c0509f01  jdk-7u80-linux-x64.tar.gz
- 6152f8a7561acf795ca4701daa10a965  jdk-7u80-linux-x64.tar.gz

If you have it, `tar xfz` it in this examples/ directory, which gives
jdk1.7.0_80/jre/lib/rt.jar; unzip that as in step 3 (into
jdk1.7.0_80/jre/lib/rt.jar.unzipped); skip step 4, since the directory
already has the name the crypto examples expect; and point
JAVA_BOOTSTRAP_CLASSES_ROOT at jdk1.7.0_80/jre/lib/rt.jar.unzipped.

## Docker

The Docker image ghcr.io/kestrelinstitute/kestrel-allcerts-java (built
from the testing-kestrel branch of ACL2, for linux/arm64) has all of the
above already done, and these examples already certified.  See
https://github.com/KestrelInstitute/acl2-docker for the images and how to
run them.
