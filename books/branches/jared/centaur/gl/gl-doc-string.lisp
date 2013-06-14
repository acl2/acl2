
(in-package "GL")

(defdoc acl2::gl ":Doc-section GL
G in the Logic: a symbolic simulation framework for ACL2~/

This library supports bit-level symbolic execution of ACL2 logic-mode
programs.  Symbolic execution is supported in two ways: by a code
transformation which translates an ACL2 logic-mode function into a new
function called its *symbolic counterpart*; or by an interpreter which
traverses a term symbolically evaluating its contents.  A symbolic
execution performs analogous operations to a normal, concrete
execution, but these operations are on *symbolic objects* rather than
ordinary ACL2 objects.

Various subtopics are linked below.  To begin proving theorems using
GL, first read ~il[DEF-GL-THM], ~il[DEF-GL-CLAUSE-PROCESSOR], and
~il[GL::SHAPE-SPECS].
~/
~/")

