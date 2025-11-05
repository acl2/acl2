# Copyright 2025 J. David Taylor
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the “Software”), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in all
# copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED “AS IS”, WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
# SOFTWARE.


__all__ = ["Message", "Command", "Client", "AsyncClient"]


import asyncio
import logging
import socket
import typing


logger = logging.getLogger(__name__)
#### NOTE: Uncomment or edit the following block for development or debugging.
# logging.basicConfig(
#     filename="acl2-bridge-python-client.log",
#     level=logging.INFO,
# )


class Message(typing.NamedTuple):
    """An ACL2 Bridge message"""

    type: str
    payload: str


class Command(Message):
    """An ACL2 Bridge command"""

    def encode(self):
        return "{} {}\n{}\n".format(self.type, len(self.payload), self.payload).encode()


class Client:
    """Synchronous Python bindings for the ACL2 Bridge protocol"""

    def __init__(self):
        logger.info("Initializing synchronous client")
        self._socket = None
        self._message_buff = b""
        self.address = None
        self.connected = False

    def connect(self, address):
        """Connect to a Unix socket

        `address` is the filepath of a Unix socket created by an ACL2 Bridge
        server.

        """
        assert not self.connected, f"Address {self.address}: Client already connected"
        self.address = address
        logger.info(f"Address {self.address}: Client attempting to connect")
        self._socket = socket.socket(family=socket.AF_UNIX)
        self._socket.connect(address)
        self.connected = True
        logger.info(f"Address {self.address}: Client successfully connected")

    def disconnect(self):
        """Disconnect from a Unix socket"""
        assert self.connected, "Client not connected"
        self._socket.close()
        self._socket = None
        self._message_buff = b""
        address = self.address
        self.address = None
        self.connected = False
        logger.info(f"Address {address}: Client successfully disconnected")

    def send(self, command):
        """Send a command to the bridge server"""
        assert self.connected, "Client not connected"
        assert isinstance(command, Command)
        self._socket.sendall(command.encode())
        logger.info(f"Address {self.address}: {command}")

    def receive(self):
        """Receive a message from the bridge server"""
        assert self.connected, "Client not connected"
        message = Message(*self._recv())
        logger.info(f"Address {self.address}: {message}")
        return message

    def _recv(self):
        """Parse a single message

        This method is a low-level implementation detail.
        """
        cut = self._message_buff.find(b"\n")
        while cut < 0:
            self._message_buff += self._socket.recv(2**12)
            cut = self._message_buff.find(b"\n")
        assert self._message_buff[cut] == 10, (self._message_buff, cut)

        mtype, mlen = self._message_buff[:cut].decode().split(" ")
        mlen = int(mlen)
        left = cut + 1
        right = left + mlen + 1
        if len(self._message_buff) < right:
            self._message_buff += self._socket.recv(right - len(self._message_buff))
        message = self._message_buff[left : right - 1].decode()

        assert self._message_buff[right - 1] == 10, (
            self._message_buff,
            cut,
            left,
            right,
        )
        self._message_buff = self._message_buff[right:]
        return mtype, message


class AsyncClient:
    """Asynchronous Python bindings for the ACL2 Bridge protocol"""

    def __init__(self):
        logger.info("Initializing asynchronous client")
        self._reader = None
        self._writer = None
        self._message_buff = b""
        self.address = None
        self.connected = False

    async def connect(self, address):
        """Connect to a Unix socket

        `address` is the filepath of a Unix socket created by an ACL2 Bridge
        server.

        """
        assert not self.connected, f"Address {self.address}: Client already connected"
        self.address = address
        logger.info(f"Address {self.address}: Client attempting to connect")
        self._reader, self._writer = await asyncio.open_unix_connection(
            path=self.address
        )
        self.connected = True
        logger.info(f"Address {self.address}: Client successfully connected")

    async def disconnect(self):
        """Disconnect from a Unix socket"""
        assert self.connected, "Client not connected"
        self._writer.close()
        await self._writer.wait_closed()
        self._reader = None
        self._writer = None
        self._message_buff = b""
        address = self.address
        self.address = None
        self.connected = False
        logger.info(f"Address {address}: Client successfully disconnected")

    async def send(self, command):
        """Send a command to the bridge server"""
        assert self.connected, "Client not connected"
        assert isinstance(command, Command)
        self._writer.write(command.encode())
        await self._writer.drain()
        logger.info(f"Address {self.address}: {command}")

    async def receive(self):
        """Receive a message from the bridge server"""
        assert self.connected, "Client not connected"
        message = Message(*await self._recv())
        logger.info(f"Address {self.address}: {message}")
        return message

    async def _recv(self):
        """Parse a single message

        This method is a low-level implementation detail.
        """
        cut = self._message_buff.find(b"\n")
        while cut < 0:
            self._message_buff += await self._reader.read(2**12)
            cut = self._message_buff.find(b"\n")
        assert self._message_buff[cut] == 10, (self._message_buff, cut)

        mtype, mlen = self._message_buff[:cut].decode().split(" ")
        mlen = int(mlen)
        left = cut + 1
        right = left + mlen + 1
        if len(self._message_buff) < right:
            self._message_buff += await self._reader.read(
                right - len(self._message_buff)
            )
        message = self._message_buff[left : right - 1].decode()

        assert self._message_buff[right - 1] == 10, (
            self._message_buff,
            cut,
            left,
            right,
        )
        self._message_buff = self._message_buff[right:]
        return mtype, message
