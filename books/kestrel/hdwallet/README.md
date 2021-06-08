Hierarchical Deterministic Wallet for Cryptocurrencies
======================================================

This wallet is a simple proof of concept: it is not meant as a product
to use with keys that control access to significant assets.
Nonetheless, due to its formal basis in the ACL2 theorem prover, it
could serve as a starting point for a high-assurance wallet product.

This wallet is meant for use on an air-gapped machine.  It provides
two basic functions: key generation and transaction signing.  Thus,
keys can be generated and used for signing transactions: the data of
the transaction to sign and the signed transaction must be passed
between the air-gapped machine where this wallet runs and an
Internet-connected machine that submits the signed transactions.
The private keys never leave the air-gapped machine.
Currently, this wallet does not encrypt these keys, which are stored in
plaintext in the file system: therefore, the air-gapped machine should
use disk encryption to protect the keys at rest.

This wallet complies with the BIP 32, 39, 43, and 44 standards.  Currently, only
transactions for the Ethereum mainnet are supported.

For more information see [the XDOC main technical description][xdoc-hdwallet].  For command usage see below.

[xdoc-hdwallet]: http://www.cs.utexas.edu/users/moore/acl2/manuals/latest/?topic=HDWALLET____CRYPTO-HDWALLET

## Obtaining

To obtain a pre-built Docker image with the wallet, pull it from the Docker Hub:
```
docker pull kestrelinstitute/hdwallet-on-acl2
```

## Running

### Preliminaries
```
mkdir /tmp/hdwallet
```
The `wallet` script shares your `/tmp/hdwallet` directory with the docker container.
To prevent that directory from possibly being created and owned by root, you should
create it in advance.  You can also change the `wallet` script to use a different
host directory.

To remove the file `/tmp/hdwallet/wallet-state` file, so that you can create a
new wallet with a new entropy or mnemonic, do
```
rm -f /tmp/hdwallet/wallet-state
```

### General Usage
```
wallet <command> <arg1> ... <argN>
```
`<command>` is one of the commands described below.

`<arg1> ... <argN>` are arguments to `<command>`, whose number and nature depend
on `<command>`, as described below.


### Usage: init-from-entropy Command
```
wallet init-from-entropy <entropy> <passphrase>
```
Initialize the wallet from an entropy value and a passphrase.

`<entropy>` is a sequence of 32, 40, 48, 56, or 64 contiguous hexadecimal
digits, where the letters may be lowercase or uppercase.  Each hexadecimal
digit specifies four bits: thus, this input specifies a sequence of 128, 160,
192, 224, or 256 bits.  This is an entropy value as defined in the BIP 39
standard.  This value must be generated randomly, outside of the wallet.  The
randomness of the entropy is important for the security of (the keys in) the
wallet, and therefore a good source of randomness should be used.

`<passphrase>` is any sequence of characters. Type "" for the empty sequence,
but this is not recommended for security reasons.  It is recommended to use
printable characters (uppercase and lowercase letters, numbers, and some
special characters) of the kinds used for passwords.  This input must be
chosen by the user.  It should be easy to remember by the user but hard to
guess by others, i.e. it should look seemingly random.

A 512-bit seed value is generated from entropy and passphrase as described in
BIP 39.  This seed is used to generate the wallet master key as described in
BIP 32.  Several internal keys are generated as described in BIP 43 and BIP
44, preparing the wallet for generating and using private keys for Ethereum
transactions.

In very rare cases, the initialization of the wallet may fail due to a failure
to derive the master key from the seed or to derive one of the aforementioned
internal keys.  This possibility is described in BIP 32.  If this happens, the
user should try with a different entropy or passphrase.  This command is
deterministic, and therefore trying with the same entropy and passphrase will
fail again.

Besides initializing the wallet, this command also generates and displays a
list of mnemonic words that represents the entropy value, as described in BIP
39.  The user should write down the list of words, in the order in which they
are displayed, and store them in a safe place.  These may be used to
reconstruct the wallet, on the same machine or on a different machine.

The initial state of the wallet is saved to the file.  In rare cases in which
something fails with the file system, an internal ACL2 error may be displayed.
If this happens, the user should make sure that the directory in which the
file is to be created has the right permissions, and retry the same command.

Example:
```
./wallet init-from-entropy 00112233445566778899aabbccddeeff pass
```

### Usage: init-from-mnemonic Command
```
wallet init-from-mnemonic <mnemonic> <passphrase>
```

Initialize the wallet from a list of mnemonic words and a passphrase.

`<mnemonic> `is a sequence of 12, 15, 18, 21, or 24 words, separated by single
spaces, chosen from the list of BIP 39 English mnemonic words.  This input
should be enclosed in double quotes so that it is treated as a single input,
instead of treating each word as a separate input.

`<passphrase>` is any sequence of characters. Type "" for the empty sequence,
but this is not recommended for security reasons.  It is recommended to use
printable characters (uppercase and lowercase letters, numbers, and some
special characters) of the kinds used for passwords.

This command should be used to re-initialize a wallet that was previously
created by the init-from-entropy command.  The `<mnemonic>` input should consist
of the words generated by that previous invocation of init-from-entropy, and
the `<passphrase>` should be the same used in that previous invocation as well.

This command deterministically re-generates the same 512-bit seed and internal
keys generated by the previous invocation of init-from-entropy.  Since that
invocation did not fail, this invocation of init-from-mnemonic will not fail.

The initial state of the wallet is saved to the file.  In rare cases in which
something fails with the file system, an internal ACL2 error may be displayed.
If this happens, the user should make sure that the directory in which the
file is to be created has the right permissions, and retry the same command.

Example:
```
./wallet init-from-mnemonic 'abandon math mimic master filter design carbon crystal rookie group knife young' pass
```

### Usage: next-key Command
```
wallet next-key
```
Generate the next private key to use for signing transactions.

This command has no inputs.

The wallet internally keeps track of how many of these keys have been
generated so far.  This number is 0 when the wallet is first initialized.  The
current number is assigned as index of the newly generated key, and
incremented by one.  Thus, the generated keys have indices 0, 1, 2, ..., in
order.

Besides generating the key, this command displays its index and the Ethereum
address associated to the key.  This address is derived from the public key as
described in the Ethereum Yellow Paper; the public key is derived from the
private key as standard in elliptic curve cryptography.

In very rare cases, the generation of the key may fail, as described in BIP
32. If this happens, the key is simply skipped, and the counter is still
incremented by one so that the user can proceed to generate the next key
(which therefore uses a different index).

The updated state of the wallet is saved to the file.  In rare cases in which
something fails with the file system, an internal ACL2 error may be displayed.
If this happens, the user should make sure that the directory in which the
file is to be created has the right permissions, and retry the same command.

An internal ACL2 error may be displayed if reading the file (which is done at
the beginning of this command) fails due to some file system failure.
If this happens, it is recommended to ensure that the directory in which the
file is to be created has the right permissions, and to try again the same
command.

Example:
```
./wallet next-key
```

### Usage: sign Command
```
wallet sign <nonce> <gas-price> <gas-limit> <to> <value> <data> <index>
```
Sign a transaction with a key.

`<nonce>` is a sequence of contiguous decimal digits that denotes a non-negative
integer representable in 256 bits.  This is the nonce used for the
transaction, as described in the Ethereum Yellow Paper.  The user must keep
track of the nonce associated to each Ethereum address, outside of the wallet.

`<gas-price>` is a sequence of decimal digits that denotes a non-negative
integer representable in 256 bits.  This is the gas price in Wei that the user
is willing to pay for processing the transaction, as described in the Ethereum
Yellow Paper.

`<gas-limit>` is a sequence of decimal digits that denotes a non-negative
integer representable in 256 bits.  This is the maximum amount of gas that
the user is willing to use for processing the transaction, as described in
the Ethereum Yellow Paper.  This should be based on a sufficiently accurate
estimate of the gas necessary to process the transaction.

`<to>` is a sequence of 40 contiguous hexadecimal digits, where the letters may
be lowercase or uppercase.  Each hexadecimal digit specifies four bits: thus,
this input specifies a sequence of 160 bits.  This is the Ethereum address
that denotes the recipient of the transaction.  This may be the address of an
externally owned account or of a contract.

`<value>` is a sequence of decimal digits that denotes a non-negative integer
representable in 256 bits.  This is the number of Wei transmitted to the
recipient in this transaction.

`<data>` is a sequence of an even number of contiguous hexadecimal digits, where
the letters may be lowercase or uppercase.  Each hexadecimal digit specifies
four bits: thus, this input specifies a sequence of bytes whose length is half
the number of hexadecimal digits.  This is used as the data of the
transaction, which is passed to a smart contract recipient.  Type "" for
the empty sequence, which should be used for transactions to externally owned
accounts.

`<index>` is a sequence of contiguous decimal digits that denotes a non-negative
integer that is the index of a previously generated key (via the next-key
command).  This index is used to find the private key used to sign the
transaction.

This command does not change the state of the wallet.  Instead, the bytes that
form the signed transaction are displayed.  These bytes should be copied from
the air-gapped machine where the wallet runs to a machine connected to the
Internet, so that the transaction can be submitted to the Ethereum network.

In very rare cases, the signing operation may fail.  Since the wallet uses a
deterministic elliptic curve signature algorithm, trying the same command will
fail again.  Instead, if this happens, it is recommended to change slightly
some non-critical input of this command, such as the gas limit.

An internal ACL2 error may be displayed if reading the file (which is done at
the beginning of this command) fails due to some file system failure.
If this happens, the user should make sure that the directory in which the
file is to be created has the right permissions, and retry the same command.


# Building

Here's how to build the Docker image containing the wallet.

We separate the Docker build into three layers.
The build files are in the `build` subdirectory.

```
cd build
docker pull ubuntu
docker build --file ccl.df -t ccl:latest .
docker build --file acl2-on-ccl.df -t acl2-on-ccl:latest .
docker build --file hdwallet-on-acl2.df -t hdwallet-on-acl2:latest .
```
