#!/usr/bin/env bash

LISP_FILE=$1
TEMP_FILE=$2

if [ -f "$TEMP_FILE" ]
then
	rm "$TEMP_FILE"
fi

echo "Checking file $LISP_FILE..."
{
	./check-file.sh "$LISP_FILE" "$TEMP_FILE"
} &> /dev/null
FILE_STATUS=$?
typeset -i x
x=$(wc -l < "$TEMP_FILE")
if [[ $FILE_STATUS -eq 0 ]]; then
	echo $'\e[0;32m>>PASS<<\e[0m\n'
	echo "### $LISP_FILE passed" >> "testResult"
        echo $'\n' >> "testResult"
else
        echo $'\e[0;31m>>FAIL<<\e[0m\n'
        echo "### $LISP_FILE failed with the following:" >> "testResult"
        tail "$TEMP_FILE" >> "testResult"
        echo $'\n' >> "testResult"
fi
rm "$TEMP_FILE"

