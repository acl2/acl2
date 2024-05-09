# Copyright (C) 2023, ForrestHunt, Inc.
# Written by Matt Kaufmann
# License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

# Usage: source ~/projects/PEARLS/acl2/acl2data/advice-counts.sh
# (replacing path to PEARLS repo as appropriate)
# in the ACL2 sources directory.

echo :ADD-BY-HINT
find books -name '*_acl2data.out' -exec fgrep '(:ADD-BY-HINT'  \{} \; | wc -l
echo :ADD-CASES-HINT
find books -name '*_acl2data.out' -exec fgrep '(:ADD-CASES-HINT'  \{} \; | wc -l
echo :ADD-INDUCT-HINT
find books -name '*_acl2data.out' -exec fgrep '(:ADD-INDUCT-HINT'  \{} \; | wc -l
echo :ADD-NONLINEARP-HINT
find books -name '*_acl2data.out' -exec fgrep '(:ADD-NONLINEARP-HINT'  \{} \; | wc -l
echo :ADD-EXPAND-HINT
find books -name '*_acl2data.out' -exec fgrep '(:ADD-EXPAND-HINT'  \{} \; | wc -l
echo :ADD-USE-HINT
find books -name '*_acl2data.out' -exec fgrep '(:ADD-USE-HINT'  \{} \; | wc -l
echo :ADD-DISABLE-HINT
find books -name '*_acl2data.out' -exec fgrep '(:ADD-DISABLE-HINT'  \{} \; | wc -l
echo :ADD-ENABLE-HINT
find books -name '*_acl2data.out' -exec fgrep '(:ADD-ENABLE-HINT'  \{} \; | wc -l
echo :ADD-DO-NOT-HINT
find books -name '*_acl2data.out' -exec fgrep '(:ADD-DO-NOT-HINT'  \{} \; | wc -l
echo :USE-LEMMA
find books -name '*_acl2data.out' -exec fgrep '(:USE-LEMMA'  \{} \; | wc -l
echo :ADD-LIBRARY
find books -name '*_acl2data.out' -exec fgrep '(:ADD-LIBRARY'  \{} \; | wc -l
echo :ADD-HYP
find books -name '*_acl2data.out' -exec fgrep '(:ADD-HYP'  \{} \; | wc -l
