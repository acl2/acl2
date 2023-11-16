# Docker

The easiest way to get started with the Eclipse plugin is to use
Docker.

## Prerequisites
- docker
- docker-compose

## Instructions
From the root directory of this repository, run `docker-compose -f
docker/eclipse-docker-compose.yml --project-directory . build`. This
will build the Eclipse plugin and install it in a Docker image, and
should take somewhere between 5 and 15 minutes. Then, run
`docker-compose -f docker/eclipse-docker-compose.yml
--project-directory . up` and navigate to
[localhost:8080](http://localhost:8080/vnc_auto.html) in your web
browser.



# Local installation

## Prerequisites
- A locally built version of `calculational-proof-checker`
- The `PROVE_FILE_SH`environment variable set to the path to
  `prove-file-java.sh` inside of the calculational-proof-checker directory.
- Java 17
- [Eclipse 2023-03](https://download.eclipse.org/eclipse/downloads/drops4/R-4.27-202303020300/)

## Instructions
- Go to Help -> Install new software inside of Eclipse, then click Add. 
- On the right-hand side of the popup that appears, select
  Archive... and navigate to [the plugin ZIP file](../org.neu.acl2.handproof.repository/target/org.neu.acl2.handproof.repository-1.0.0-SNAPSHOT.zip)
- Then add a name, it can be anything.
- Click on the checkbox next to `Handproof` and click on Next to
  continue the installation process.

The plugin should automatically apply itself to .proof files. To run
the proof checker process, right-click inside of the editor and select
"Validate". This will not work until you build the
calculational-proof-checker locally and also set the
`PROVE_FILE_SH`environment variable to be the path to
`prove-file-java.sh` inside of the calculational-proof-checker
directory.
