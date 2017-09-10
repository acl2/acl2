; This is the demo given in lecture 5.

; cd to the marktoberdorf-08/scripts/ directory and then fire up ACL2

(include-book "m1-fast")

(in-package "M1")

(quote (end of setup))

(correct "ABCXDBC" "xxxxABCxxxGxABCXDBC")

(fast "ABCXDBC" "xxxxABCxxxGxABCXDBC")

(defun run-fast (pat txt)
       (top
        (stack
         (run (m1-boyer-moore-sched pat txt)
              (make-state 0
                          (list pat
                                (- (length pat) 1)
                                txt
                                (- (length pat) 1)
                                (length pat)
                                (length txt)
                                (preprocess pat)
                                0)
                          nil
                          *m1-boyer-moore-program*)))))

(run-fast
  "trafficked"
  "Located in the very center of the campus the
Computer Sciences Complex will be a hub of
education, research, and outreach activities of
the UT Department of Computer Sciences.  This
expansive computing complex will provide offices
for faculty, professional researchers, visitors,
and postdoctoral assistants; space for graduate
students; prime research laboratory space;
undergraduate instructional laboratory space,
together with classrooms, electronic seminar
rooms, and lecture halls.  Space for staff,
administrative support, and student organizations
will also be included.  The new complex will
connect to the Applied Computational and
Administrative Sciences (ACES) building,
supporting the continued synergy between the
fundamental computer science of the Department of
Computer Sciences and the interdisciplinary
applications in ACES.  The complex will be
~236,000 Gross Square Feet (~144,400 Assignable
Square Feet) and consist of a North Building, a
South Building, and an Atrium that extends up five
floors and connects the two Buildings.  Each
Building includes a basement level plus six full
floors.  The complex will be surrounded by
high-trafficked areas including a courtyard and
plazas.")

(pe 'M1-BOYER-MOORE-IS-CORRECT)

(quote (end of demo))
(quote (The End))

