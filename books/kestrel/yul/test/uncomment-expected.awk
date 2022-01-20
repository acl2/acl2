#!/usr/bin/awk -f

# awk script to extract the expected yul program output
# from a yul optimizer test file.
# Writes the extracted yul code to FILENAME.expected

# Example:
#   awk -f ./uncomment-expected.awk  tests/*.yul
# creates a .yul.expected file for each .yul file.

# For the test files see
#   https://github.com/ethereum/solidity/tree/develop/test/libyul/yulOptimizerTests
# For the C++ code that extracts the expected program see
#   https://github.com/ethereum/solidity/blob/develop/test/TestCaseReader.cpp
# This script implements a part of what TestCaseReader::parseSimpleExpectations does.

# This is intended to work on MacOS and Ubuntu.
# The default MacOS awk (2022-01) is 20070501.
# It doesn't have BEGINFILE or ENDFILE, so we handle the file transitions by hand.

BEGIN { fname=""; expectedFname=""; }

# fname will be set to the FILENAME when it changes,
# and expectedFname will be set to FILENAME.expected when anything is written.

# linenr is set to 0 when FILENAME changes
# Then linenr will be set to the delimiter line number.
# The delimiter line "// ----"
# and the line after it: "// step: <stepname>"
# form the transition between the input yul program and the output yul program.

# We start by scanning through the input file without echoing.

# If we see a new file,
#   first check and handle the case where the previous file did not have a delimiter;
#   if there was a previous open expectedFname, close it.
#   Then update fname, linenr, and expectedFname.
# We set expectedFname to "" here, and only to a real file name when we output to it,
# so we know if it is not "" it will need to be closed.
fname != FILENAME {
    # If we got through a whole previous file without error and without finding the delimiter,
    # then fname is the previous file; linenr will be 0; and expectedFname will be "".
    # In this case, we need to issue an error about the missing delimiter.
    if ( fname != "" && linenr == 0 && expectedFname == "" ) {
        msg=(fname " ERROR: file does not contain a delimiter");
        print(msg) > "/dev/stderr";
        expectedFname = (fname ".expected");
        print(msg) > expectedFname;
    }
    if ( expectedFname != "" ) { close(expectedFname); }
    fname=FILENAME;
    linenr=0;
    expectedFname="";
}

# If not echoing yet,
# when the delimiter is seen, record the line number in 'linenr'.
linenr==0 && ($0 ~ /^\/\/ ----/) { linenr=FNR; next }

# Otherwise, if not echoing yet, skip to next record without printing.
linenr==0 { next }

# When echoing, and if the line does not start with "//", print an error
# both to stderr and to the .expected file, and go to the next file.
FNR>linenr+1 && ($0 !~ /^\/\//) {
    msg=(FILENAME ":" FNR " ERROR: line does not start with '//'.");
    print(msg) > "/dev/stderr";
    if ( expectedFname == "" ) { expectedFname = (FILENAME ".expected"); }
    print(msg) > expectedFname;
    nextfile
}

# When echoing, and if the line is past the line after 'linenr', print the line
# to the expected file
FNR>linenr+1 {
    if ( expectedFname == "" ) { expectedFname = (FILENAME ".expected"); }
    print(substr($0, 3, length($0)-2)) > expectedFname;
}

END {
    # If the last file was missing a delimiter, issue an error.
    if ( fname != "" && linenr == 0 && expectedFname == "" ) {
        msg=(fname " ERROR: file does not contain a delimiter");
        print(msg) > "/dev/stderr";
        expectedFname = (fname ".expected");
        print(msg) > expectedFname;
    }
    if ( expectedFname != "" ) { close(expectedFname); }
}
