Smtlink
====================

*Smtlink* is a framework for integrating external *SMT* solvers into *ACL2* based on
*clause processors* and *computed hints*.

It supports both ACL2 and *ACL2(r)*. The current default SMT solver integrated is
*Z3*. *SMT-LIB* is expected to be integrated in near future.

### Requirements

* Python 2 is properly installed
* Z3 is properly installed

  One needs to build Z3 on one's own instead of using the binary release.
  Since we are using the Python interface, please follow the "python"
  section in the "z3 bindings" section in [README of Z3][Z3-README].

  To check if Z3 is properly installed, run Python, which will put you in an
  interactive loop. Then run:
  ```
  from z3 import *
  x = Real('x')
  y = Real('y')
  s = Solver()
  s.add(x + y > 5, x > 1, y > 1)
  print(s.check())
  print(s.model())
  quit()
  ```
  One should expect some results like:
  ```
  >>> print(s.check())
  sat
  >>> print(s.model())
  [y = 4, x = 2]
  ```

* ACL2 and its book directory is properly installed
* Smtlink uses Unix commands

### Build Smtlink

* Setup smtlink configuration in file *smtlink-config* in either a user specified directory *$SMT_HOME* or in directory *$HOME*.  When both environment variables are set, *$SMT_HOME* is used. The configuration takes below format:
  ```
  smt-cmd=...
  ```
  When these variables are not set, smtlink finds the smtlink-config file in current directory.
  
*  Below table explains what they stands for:
  
  Option        | Explanation                                         | Example
  ------------- | --------------------------------------------------- | -------------
  smt-cmd       | The command for running the SMT solver              | /usr/bin/env python

  
  Note that *smt-cmd* for running Z3 is the Python command since we are
  using the Python interface. The Z3 library is imported into Python in the
  scripts written out by Smtlink like is shown in "Requirements".
  
* Certify the book top.lisp in the Smtlink directory, to bake setup into certified books.

### Load and Setup Smtlink

To use Smtlink, one needs to include book:
```
(include-book "projects/smtlink/top" :dir :system)
```
Then one needs to enable *tshell* by doing
```
(value-triple (tshell-ensure))
```
and add the Smtlink computed-hint:
```
(add-default-hints '((SMT::SMT-computed-hint clause)))
```

### Reference

Yan Peng and Mark R. Greenstreet. [Extending ACL2 with SMT Solvers][publication]
In ACL2 Workshop 2015. October 2015. EPTCS 192. Pages 61-77.

[publication]: https://arxiv.org/abs/1509.06082
[Z3-README]: https://github.com/Z3Prover/z3
