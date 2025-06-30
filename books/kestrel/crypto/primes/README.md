# Cryptographic Primes

This directory contains ACL2 formal proofs of primality for cryptographic primes using Pratt certificates.

You can construct a Pratt certificate for a new prime using Sage Math or Mathematica and building it by hand.  See the comments in, for example, secp256k1-group-prime.lisp.

The rest of this README also explains how to use Cursor AI to generate new prime files.

## Quick Start: Generating a New Prime File using Cursor

### Step 1: Add Required Files to Context

**IMPORTANT**: Before making any requests, ensure Cursor has the necessary files in its context:

1. **Add the rules file**: Include `books/kestrel/crypto/primes/.cursor/rules` in your context
   - Without this file, Cursor may struggle to understand the details.
   
2. **Add example files** (recommended): Include one or more existing prime files as examples:
   - `books/kestrel/crypto/primes/ed25519-base-prime.lisp` - Good template for deep certificates

### Step 2: Gather Your Prime Information
Cursor may be able to find this information automatically.  But you will at least need to know something about the name of the prime and preferably the hex or decimal value.
If you want to prepare more detail, collect:
- **Prime name** (e.g., `secp384r1-group-prime`)
- **Hex value** (from official specification)
- **Decimal value** 
- **Mathematical formula** (if applicable, e.g., `2^255 - 19` for the curve25519 prime)
- **Bit length**
- **Cryptographic context** (what protocol/curve uses this prime)
- **Official references** (RFCs, NIST specs, academic papers)

### Step 3: Use Cursor to Generate the File

Open Cursor and use a prompt like this:

```
Please create a file [prime-name].lisp that proves primality of the prime: [description].
```

### Step 4: Clean up

Review the references and comments and xdoc and make sure the file certifies.
