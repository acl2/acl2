#!/bin/sh

set -e
set -u

HERE=`pwd`

# Test of a horrible corner case for ".." handling.
#
# We create the hierarchy
#
#       lstest-dir
#         |
#     +---+------------------+
#     |                      |
#  subdir1                subdir3 -+ (link)
#     |                            |
#   +-+---------+                  |
#   |           |                  |
#  xxxdir      subdir2  <----------+
#   |               |
#  xxx.txt        yyydir
#                   |
#                 yyy.txt
#
# When we then look at:
#
#      lstest-dir/subdir3/..
#
# We should actually arrive at latest-dir/subdir1,
# instead of just latest-dir.
#
# So paths like
#
#       lstest-dir/subdir3/../xxxdir
#
# should be valid, but paths like:
#
#       lstest-dir/subdir3/../subdir1
#
# should not be valid.

rm -rf lstest-dir

mkdir lstest-dir
touch lstest-dir/file1.txt

mkdir lstest-dir/subdir1
touch lstest-dir/subdir1/file2.txt
mkdir lstest-dir/subdir1/xxxdir
touch lstest-dir/subdir1/xxxdir/xxx.txt

mkdir lstest-dir/subdir1/subdir2
touch lstest-dir/subdir1/subdir2/file3.txt
mkdir lstest-dir/subdir1/subdir2/yyydir
touch lstest-dir/subdir1/subdir2/yyydir/yyy.txt

cd lstest-dir
ln -s subdir1/subdir2 subdir3

cd $HERE

set -x

ls -l lstest-dir/subdir3/..
[ -d lstest-dir/subdir3/../xxxdir ] && true
[ ! -d lstest-dir/subdir3/../subdir1 ] && true
