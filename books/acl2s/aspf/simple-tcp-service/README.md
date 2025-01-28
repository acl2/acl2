# simple-tcp-service

## What is this?

This directory contains code that is intended to make it easier to
produce services that expose TCP sockets and use ACL2s.

This directory contains several parts:
- An ASDF system providing a TCP server that allows one to create a
  customized "ACL2s service" that exposes some capabilities over a TCP
  socket using a custom protocol
- An ASDF system providing a library for encoding and decoding Defdata
  values as JSON
- A small Python module for connecting to and interacting with an
  ACL2s service
- A simple example ACL2s service

## Prerequisites
To run the examples, Quicklisp should be installed. If not installed
at `~/quicklisp`, the `QUICKLISP_SETUP` environment variable should be
set to the path to the `quicklisp/setup.lisp` file. If your ACL2 image
starts with Quicklisp loaded, this is not required. (you can check
this by exiting into raw lisp and checking whether `*features*`
contains `:QUICKLISP`)

## How do I use this?

To create a service, one needs to create a request handler for
it. This is a function that takes in the body of a message (decoded as
a UTF-8 string) and produces a string (that will be encoded using
UTF-8 and sent back to the requester).  In most cases, one can simply
use the rest of the files from the `basic-server` example with the
custom request handler (updating `load`s as appropriate).

The Python module supports both starting up a ACL2s service image in a
subprocess and connecting to an existing service (given its TCP
port). This means that the services can be running on different
computers and interacted with over a network if desired, as long as
the appropriate network configuration is performed to e.g. forward
ports if needed. One could also create several services in
subprocesses to create a worker pool and use something like Flask to
integrate the service with a REST API.
