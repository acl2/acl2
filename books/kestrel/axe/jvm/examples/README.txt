This directory relies on a specific old version of the Java libraries
(in rt.jar).

To obtain it, go to:

https://www.oracle.com/java/technologies/javase/javase7-archive-downloads.html

and download the file:

jdk-7u80-linux-x64.tar.gz

To do this, I had to create an Oracle account and accept a license. I retrieved
this on 4/20/23.

The sha1sum and md5sum of jdk-7u80-linux-x64.tar.gz are as follows:
21e5e18c3511def01590994e926a4350c0509f01  jdk-7u80-linux-x64.tar.gz
6152f8a7561acf795ca4701daa10a965  jdk-7u80-linux-x64.tar.gz

Then do:
tar xfz jdk-7u80-linux-x64.tar.gz

The sha1sum and md5sum of jdk1.7.0_80/jre/lib/rt.jar are as follows:
92bf5eaaf26a12df691c579a7297d86b5c0dac7c  jdk1.7.0_80/jre/lib/rt.jar
52cccf2dbdb2e675b827fd355d7e6658  jdk1.7.0_80/jre/lib/rt.jar

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

To obtain the Bouncycastle .jar, do:

wget https://www.bouncycastle.org/download/jce-jdk13-134.jar

I retrieved this on 4/20/23.
