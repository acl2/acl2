This directory contains proofs, largely AI-generated, that are
intended to establish the correctness of parts of the ACL2 system.
(Yes, proving these facts using ACL2 is logically circular, but the
point is to try to increase assurance and eliminate bugs.)

Warning: The contents of this directory have not been carefully
reviewed.

Note to the ACL2 implementors: If changes to the ACL2 sources cause
these proofs to break, feel free to comment things out and/or add
skip-proofs.  But please notify Eric Smith or someone else at Kestrel,
so we can fix them.  If ACL2 source code changes cause any of these
theorems to cease to be true, that is interesting and should probably
be investigated (keeping in mind though that most of this material is
unvetted).
