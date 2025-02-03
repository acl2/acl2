# SPDX-FileCopyrightText: Copyright (c) 2021 Andrew T. Walter <me@atwalter.com>
# SPDX-License-Identifier: MIT
import os
import sys

# Set up the Python include path appropriately so it can find the
# Python interface library.
THIS_FILE_DIR = os.path.dirname(os.path.realpath(__file__))
sys.path.append(THIS_FILE_DIR+'/../../python-interface')
from acl2s import Acl2sService

PROVER_IMG = THIS_FILE_DIR + "/server"
service = Acl2sService()
service.start(PROVER_IMG)
# Test echoing, should print ("OK", "Echo!")
print(service.run_command("E", "Echo!"))
# Test another endpoint. This one generates a random string using
# ACL2s' string enumerator.
print(service.run_command("R", ""))
service.stop()
