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


import asyncio

import acl2_bridge
from acl2_bridge import AsyncClient, Command


async def repl():
    # create a client
    client = AsyncClient()
    # connect to the bridge server socket
    await client.connect("./demo-bridge")
    # read the hello message
    message = await client.receive()
    assert (
        message.type == "ACL2_BRIDGE_HELLO"
    ), f"Received {message} instead of ACL2_BRIDGE_HELLO"
    # get the associated worker (we don't use this)
    worker = message.payload

    while True:
        message = await client.receive()
        if message.type == "READY":
            assert message.payload == ""
            # construct prompt with current package
            await client.send(Command("LISP", "(acl2::current-package acl2::state)"))
            message = await client.receive()
            assert (
                message.type == "RETURN"
            ), f"Received {message} instead of *CURRENT-PACKAGE*"
            current_package = message.payload[1:-1]
            message = await client.receive()
            assert message.type == "READY", f"Received {message} instead of READY"
            try:
                command = Command("LISP", input(f"{current_package}> "))
            except EOFError:
                await client.send(Command("LISP", "(bridge::stop)"))
                await client.disconnect()
                exit()
            await client.send(command)
        elif message.type == "RETURN":
            print(message.payload)
        elif message.type == "STDOUT":
            print(message.payload)
        elif message.type == "ERROR":
            print("ERROR:", message.payload)
        else:
            raise Exception(f"Received message {message}")


if __name__ == "__main__":
    asyncio.run(repl())
