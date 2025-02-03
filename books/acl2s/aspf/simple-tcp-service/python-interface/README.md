# ACL2s TCP Service Python Interface

This library provides a Python interface for use when interacting with
a service implemented using the ACL2s simple-tcp-service library.

This interface expects that the service in question implements the
following two commands:
- `E`, which is expected to respond with "OK" followed by the payload
  of the original command
- `Q`, which responds with "OK" and then stops the service

Message payloads are expected to be UTF-8 encoded. The first two bytes
of a message response payload are expected to denote the status of the
response, either `OK` for success or `ER` for failure.

The message format is described in `src/tcp-worker/tcp-server.lisp`.

## Usage

This library is capable of starting a service executable locally and
connecting to it, or connecting to an already-running service that is
accessible via TCP.

The first can be performed by calling the `start` method on an
`Acl2sService` object. This method takes in a path to the service
executable, which is expected to take in a file descriptor to which it
will write the port number (5 bytes, each to be interpreted as an
ASCII digit) for the TCP port that it is listening on.

One can connect to an existing service by calling the `connect`
method, which takes in the port number to connect to and optionally
the host IP to connect to (by default, `0.0.0.0`).
