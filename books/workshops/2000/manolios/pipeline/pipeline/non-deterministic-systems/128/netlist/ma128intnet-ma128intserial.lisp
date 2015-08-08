;  Copyright (C) 2000 Panagiotis Manolios

;  This program is free software; you can redistribute it and/or modify
;  it under the terms of the GNU General Public License as published by
;  the Free Software Foundation; either version 2 of the License, or
;  (at your option) any later version.

;  This program is distributed in the hope that it will be useful,
;  but WITHOUT ANY WARRANTY; without even the implied warranty of
;  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;  GNU General Public License for more details.

;  You should have received a copy of the GNU General Public License
;  along with this program; if not, write to the Free Software
;  Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

;  Written by Panagiotis Manolios who can be reached as follows.

;  Email: pete@cs.utexas.edu

;  Postal Mail:
;  Department of Computer Science
;  The University of Texas at Austin
;  Austin, TX 78701 USA

(in-package "ACL2")

(include-book "ma128intnet")

(generate-full-system maserial-step maserial-p manet-step manet-p
		      manet-to-maserial good-manet manet-rank)

(in-theory (disable n convert-regs value-of update-valuation ALU-output excp
		    b-to-num latch1 serial-excp serial-ALU net-excp net-ALU))

(prove-web maserial-step maserial-p manet-step manet-p manet-to-maserial manet-rank)

(wrap-it-up maserial-step maserial-p manet-step manet-p
	    good-manet manet-to-maserial manet-rank)
