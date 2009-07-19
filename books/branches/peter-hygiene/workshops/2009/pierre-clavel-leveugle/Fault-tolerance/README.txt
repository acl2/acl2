
TIMA Laboratory, Grenoble, France
March 2009
--------------------------------

The books of this directory are associated with the ATM example given in 
section 5.2 of the paper:
"ACL2 for the Verification of Fault-Tolerance Properties: First Results",
L.Pierre, R.Clavel, R.Leveugle,
Proc. International Workshop On The ACL2 Theorem Prover and Its 
Applications, Boston (MA), May 2009.

Files:

- error-model.lisp: error model of section 4.1

- register.lisp: simple architecture for the component REG (neither 
detection nor correction mechanism)

- register-det.lisp: second architecture for the component REG (section 
5.2.1), equipped with an error detection mechanism

- register-TMR.lisp: third architecture for the component REG (section 
5.2.1), TMR register

- ATM-det.lisp: ATM system version 1 (section 5.2.2), all the registers 
are instances of register-det

- ATM-TMR.lisp: ATM system version 2 (section 5.2.2), all the registers 
are instances of register-TMR
