Axe Examples Involving Java/JVM Code.

The [crypto/](crypto) subdirectory contains Axe proofs of cryptographic algorithms in the "classic" Axe style.

The [formal-unit-tester/](formal-unit-tester) subdirectory contains "formal unit tests": highly automated proofs about small pieces of code.

# Setup: Obtaining STP

See :doc STP, here:

https://acl2.org/doc/?topic=ACL2____STP

for information about installing the STP SMT solver, which is used by
Axe.

# Setup: Obtaining Java Libraries

The proofs in this directory need access to a specific old version of the Java
libraries (specifically, the rt.jar file).  There is no need to install it or
replace the version of Java on your system.

1. To obtain it, go to:

https://www.oracle.com/java/technologies/javase/javase7-archive-downloads.html

and download the file:

jdk-7u80-linux-x64.tar.gz

(To do this, I had to create an Oracle account and accept a license.
I successfully downloaded the file, jdk-7u80-linux-x64.tar.gz, on
4/20/23 and again on 9/27/24 and again on 3/18/25.)

If you want to check that you have the exact right file, the sha1sum
and md5sum of jdk-7u80-linux-x64.tar.gz are:
- 21e5e18c3511def01590994e926a4350c0509f01  jdk-7u80-linux-x64.tar.gz
- 6152f8a7561acf795ca4701daa10a965  jdk-7u80-linux-x64.tar.gz

2. Then, after ensuring that jdk-7u80-linux-x64.tar.gz is in this examples/ directory, do:

tar xfz jdk-7u80-linux-x64.tar.gz

The untarred files should include jdk1.7.0_80/jre/lib/rt.jar .

3. Then, unzip rt.jar like this:

unzip ./jdk1.7.0_80/jre/lib/rt.jar -d ./jdk1.7.0_80/jre/lib/rt.jar.unzipped

4. Then, set the JAVA_BOOTSTRAP_CLASSES_ROOT environment variable to point
to the unzipped directory.  For example, if you have ACL2_ROOT
defined, you can do:

export JAVA_BOOTSTRAP_CLASSES_ROOT=${ACL2_ROOT}/books/kestrel/axe/jvm/examples/jdk1.7.0_80/jre/lib/rt.jar.unzipped

5. See also further setup instructions in crypto/README.md if you want to build those examples.