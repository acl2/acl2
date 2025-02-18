# SPDX-FileCopyrightText: Copyright (c) 2021 Andrew T. Walter <me@atwalter.com>
# SPDX-License-Identifier: MIT
import time
import subprocess
import os
import socket
import struct

ACL2S_COMMAND_RUN_TIMEOUT_S = 20 # seconds in which the ACL2S process should start and run our command

class Acl2sServiceException(Exception):
    pass

class InvalidHeaderException(Acl2sServiceException):
    def __init__(self, actual_header):
        self.message = f"Expected QK but got ${actual_header}."

class MessageSizeMismatchException(Acl2sServiceException):
    def __init__(self, expected, actual):
        self.message = f"Expected message length to be ${expected} bytes, but actually only recieved ${actual} bytes."

class ConnectionTestFailedException(Acl2sServiceException):
    def __init__(self):
        self.message = "Connection test failed - ensure that the service executes correctly and supports the E echo command"

class Acl2sService:
    """A class representing a an ACL2s service. Can either connect to an
    existing ACL2s service with connect(), or start an ACL2s service
    image in a subprocess and manage it.
    """
    def __init__(self, run_timeout=ACL2S_COMMAND_RUN_TIMEOUT_S):
        self.output_read_fd = None
        self.output_write_fd = None
        self.process = None
        self.sock = None
        self.run_timeout = run_timeout

    # 1382728371 is the default random seed for ACL2s
    # See books/acl2s/defdata/random-state-basis1.lisp.
    def start(self, executable, seed=1382728371, debug=False):
        """Start the ACL2s service and connect to it.
        Returns the port that the ACL2s service is listening on.
        
        Note that the optional seed parameter must be a 63-bit unsigned
        integer (per defdata).
        
        The ACL2s service image must output the port number that it is
        listening on to the file descriptor that it is passed in.
        """
        # Create pipes for receiving data from acl2s.
        self.output_read_fd, self.output_write_fd = os.pipe()
        # TODO: preexec_fn does not work on windows. But this is probably
        # true of most of the code in this file.
        # Pipe stdout and stderr to /dev/null unless debug is True.
        stdout = subprocess.DEVNULL
        stderr = subprocess.DEVNULL
        if debug:
            stdout = None
            stderr = None
        self.process = subprocess.Popen(
            [executable, str(self.output_write_fd), str(seed)],
            stdin=subprocess.DEVNULL,
            stdout=stdout,
            stderr=stderr,
            pass_fds=[self.output_write_fd],
            # Ignore CTRL-C
            preexec_fn=os.setpgrp)
        d = os.read(self.output_read_fd, 5)
        decoded = d.decode()
        port = int(decoded)
        self.connect(port, host="0.0.0.0")
        return port

    def connect(self, port, host="0.0.0.0"):
        """Connect to a running ACL2s service on the given port.
        The `host` argument is optional, and by default is 0.0.0.0.
        
        After connecting, this service will test whether the server
        responds as expected to an E (echo) command. If this fails, a
        `ConnectionTestFailedException `is raised but the socket remains
        connected.
        """
        self.sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        self.sock.connect((host, port))
        self.sock.settimeout(self.run_timeout)
        if not self.run_command("E", "test") == ("OK", "test"):
            raise ConnectionTestFailedException()

    def disconnect(self):
        """Disconnect from a running ACL2s service.
        
        This will not stop the service, it will only close the TCP
        connection.
        """
        self.sock.close()

    def stop(self):
        """Stop the running ACL2s service and disconnect from it.
        
        If the ACL2s service was started in this Python instance using
        the `start` method of Acl2sService, the process will also be
        killed, and the file descriptors used to communicate with it at
        initialization time will be closed.
        
        The process kill and file descriptor cleanup will occur even if
        the stop command fails to execute for some reason.
        """
        try:
            self.run_command("Q")
            self.sock.close()
        finally:
            if self.process:
                self.process.kill()
            if self.output_write_fd:
                os.close(self.output_write_fd)
            if self.output_read_fd:
                os.close(self.output_read_fd)

    def write(self, body):
        """Send data to the ACL2s service."""
        body_en = body.encode(encoding="utf-8")
        nbytes = len(body_en)
        return self.sock.send(b''.join([b'QK', struct.pack('>I', nbytes), body_en]))

    def read(self):
        """Recieve data from the ACL2s service.

        This method will raise a `socket.timeout` exception if no
        message is received within the configured `run_timeout`
        duration.
        """
        header = self.sock.recv(6)
        if not header[0:2] == b'QK':
            raise InvalidHeaderException()
        nbytes = struct.unpack('>I', header[2:])[0]
        totbytes = 0
        body = []
        # Note that the message may come in as several TCP packets,
        # so we need to make sure we wait for them all here
        # TODO: add timeout or something
        while totbytes < nbytes:
            data = self.sock.recv(nbytes-totbytes)
            body.append(data)
            totbytes = totbytes + len(data)
        if not totbytes == nbytes:
            raise MessageSizeMismatchException(nbytes, totbytes)
        return b''.join(body).decode(encoding="utf-8")

    def run(self, data):
        """Send a data to the ACL2s service and wait for it to respond.

        This method will raise a `socket.timeout` exception if the Lisp
        command(s) take longer than the configured `run_timeout`
        duration to evaluate.
        """
        self.write(data)
        return self.read()

    def write_command(self, command, data=""):
        if len(command) != 1:
            raise ValueError("Command should be a single-character string.")
        return self.write(command + str(data))

    def read_command(self):
        output = self.read()
        return (output[0:2], output[2:])

    def run_command(self, command, data=""):
        """Send a command to the ACL2s service with (optionally) some
        data and wait for it to respond.

        This method will raise a `socket.timeout` exception if the Lisp
        command(s) take longer than the configured `run_timeout`
        duration to evaluate.
        """
        self.write_command(command, data)
        return self.read_command()

if __name__ == "__main__":
    # TODO: add better example
    #p = Acl2sService()
    #try:
    #    p.start()
    #    print(p.run_command("E", "foobar"))
    #finally:
    #    p.stop()
    pass
