#!/usr/bin/env bash

# echo commands as they happen
set -x

# Create the shared directory.  This is also mentioned
# in the "wallet" script.
mkdir /tmp/hdwallet

./wallet init-from-entropy 00112233445566778899aabbccddeeff pass
# should output
#   abandon
#   math
#   mimic
#   master
#   filter
#   design
#   carbon
#   crystal
#   rookie
#   group
#   knife
#   young

sum /tmp/hdwallet/wallet-state
# should output
# 56443 1 /tmp/hdwallet/wallet-state

# Remove that state and show how the same state
# can be created using the mnemonic.
rm -f /tmp/hdwallet/wallet-state
./wallet init-from-mnemonic 'abandon math mimic master filter design carbon crystal rookie group knife young' pass

sum /tmp/hdwallet/wallet-state
# should output the same as the previous sum command,
# 56443 1 /tmp/hdwallet/wallet-state

./wallet next-key
# should output E2C12CCF1D64740C7880FFA150A60B9D7679BB69

./wallet sign 50 4 1000 0011223344556677889900112233445566778899 1000000 abababab 0
# should output
#   F8 66 32 04 82 03 E8 94 00 11 22 33 44 55 66 77
#   88 99 00 11 22 33 44 55 66 77 88 99 83 0F 42 40
#   84 AB AB AB AB 26 A0 9B F3 D8 B3 FF 14 ED 13 11
#   A1 20 FD FD 81 76 03 43 5F 72 FC 83 FF 26 F9 AD
#   BD B5 CE 26 E9 C8 8C A0 7D 32 69 CA 1F 07 6A A2
#   FD 9C 99 01 B9 10 B2 C0 69 7B 03 FD 25 54 01 65
#   11 D1 13 50 49 61 91 24
