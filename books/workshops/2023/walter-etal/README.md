# Supporting material for "Proving Calculational Proofs Correct"

This repo contains the version of the calculational proof checker that
we describe in our ACL2 Workshop 2023 paper.

## Upstream Repo

The upstream version of this code is available on GitLab at
https://gitlab.com/acl2s/proof-checking/calculational-proof-checker/ .

## Examples

A good place to start is
[examples/ind-examples/pass/qsort=isort.proof](./examples/ind-examples/pass/qsort\%3Disort.proof),
but more examples can be found in [the examples
directory](./examples).

## Installing and using the Eclipse plugin using Docker

The easiest way to get started with the Eclipse plugin is to use
Docker.

### Prerequisites
- docker
- docker-compose
- 6GB of hard-drive space

### Instructions
From the root directory of this repository, run `docker-compose -f
docker/eclipse-docker-compose.yml --project-directory . up` and
navigate to
[localhost:8080/vnc\_auto.html](http://localhost:8080/vnc_auto.html)
in your web browser. This should bring up a view containing a popup
window showing "Select a directory as workspace". Leave the default
value there and click on "Launch" at the bottom-right of the popup.

### Usage
To run the checker on a file, click inside the Eclipse editor for a
`.proof` file and then click on the "Validate" button on the top
toolbar. Depending on your computer, this process may take a while, on
the order of a minute. After the process is complete, results will be
output to the "Checker Output" view on the right-hand side of the
window and will be shown in the source file itself.

Examples can be opened by going to "File -> Open" inside Eclipse and
navigating to the "checker/examples" folder, and then to the desired
example as noted previously in this README.

## Running the CLI locally

### Prerequisites
- Java 17
- An ACL2s image (see [the scripts](https://gitlab.com/acl2s/external-tool-support/scripts) repo)
- Quicklisp

### Instructions
If the ACL2s image is not on your `PATH`, you must set the `ACL2S_EXE`
environment variable to the absolute path to the image.

Similarly, if Quicklisp's `setup.lisp` is not installed at
`~/quicklisp/setup.lisp`, you will need to set the `QUICKLISP_SETUP`
environment variable to the path to `setup.lisp`.

Run `make` in this directory. This will build all of the necessary
files to run the checker locally.

### Usage
Run the `check-file.sh` script in this directory, providing the path
to the file to check as an argument. The script will check your file
and print its output to standard out.
