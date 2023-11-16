#!/usr/bin/env bash

# Doc:
# Runs only in hand-proof-checker directory
# ./check-tests.sh -d {dirname} [-r]
# Use -d to specify a directory, and it runs check-files.sh on all the proof files in the directory.
# It then prints out whether or not each of the tests passes or fail,
# and also creates a file called testResult.
# There's a directory called testResults as well, if you run this script when there's already
# a testResult, it places testResult in testResults and gives it a number, in some order.
# If you want to run this on all the proof files in a directory recursively, use the -r flag.

DIRECTORY=0
RECURSE=0
JOBS=2

while getopts ":d:j:r" opt; do
	case $opt in
		d)
			DIRECTORY="$OPTARG"
			DIRECTORY=${DIRECTORY%"/"}
			;;
		r)
			RECURSE=1
			;;
        j)
            JOBS=$OPTARG
            ;;
		\?)
			echo "Invalid option: -$OPTARG" >&2
			exit 1
			;;
		:)
			echo "Option -$OPTARG requires an argument."
			exit 1
			;;
	esac
done

if [ $DIRECTORY == 0 ]
then
	echo "Usage: ./check-tests.sh -d {DIRECTORY}"
	exit 1
else
	if [ ! -d $DIRECTORY ]
	then
		echo "Usage: ./check-test.sh -d {DIRECTORY}"
		echo "Please make sure you submitted a valid directory"
		exit 1
	fi
fi

if [ ! -d "testResults" ]; then
	mkdir "testResults"
fi

if [ -f "testResult" ]; then
	typeset -i x
	x=`ls -1 testResults | wc -l`
	x=$((x + 1))
	mv "testResult" "testResults/testResult$x"
fi

touch testResult
dt=$(date '+%d/%m/%Y %H:%M:%S');
echo "$dt" >> testResult
echo $'\n' >> testResult

if [ -f "tempFile" ]; then
	rm "tempFile"
fi

if [ -f "tempFiles" ]; then
	rm "tempFiles"
fi

if [ -f "tempDirs" ]; then
	rm "tempDirs"
fi

if [ $RECURSE -eq 0 ]; then
	echo "Entering non-recursive mode"
	ls -1 $DIRECTORY | egrep '\.proof$' > "tempFiles"
	echo "### Checking in $DIRECTORY:" >> "testResult"
        echo $'\n' >> "testResult"

	if [ -f "parFile" ]
	then
		rm "parFile"
	fi

	touch "parFile"

	COUNTER=0
	input="tempFiles"
	while IFS= read -r line
	do
		line="${line%$'\n'}"
		echo "$DIRECTORY/$line tempFile$COUNTER" >> "parFile"
		COUNTER=$(( $COUNTER + 1 ))
	done < "$input"

	cat "parFile" | parallel -j $JOBS --colsep ' ' "./check-tests-help.sh" {1} {2}
else
	echo "Entering recursive mode"
	find $DIRECTORY -type d > "tempDirs"
	input="tempDirs"
	while IFS= read -r dir
	do
		dir="${dir%$'\n'}"
		echo "### Checking in $dir:" >> "testResult"
		ls -1 $dir | egrep '\.proof$' > "tempFiles"

		if [ -f "parFile" ]
		then
			rm "parFile"
		fi

		touch "parFile"

		COUNTER=0
		inputFile="tempFiles"
		while IFS= read -r file
		do
			file="${file%$'\n'}"
			echo "$dir/$file tempFile$COUNTER" >> "parFile"
			COUNTER=$(( $COUNTER + 1 ))
		done < "$inputFile"

		cat "parFile" | parallel -j $JOBS --colsep ' ' "./check-tests-help.sh" {1} {2}
	done < "$input"
	ls -1 $DIRECTORY | egrep '\.proof$' > "tempFiles"
fi

if [ -f "tempFile" ]; then
        rm "tempFile"
fi

if [ -f "parFile" ]; then
	rm "parFile"
fi

if [ -f "tempFiles" ]; then
        rm "tempFiles"
fi

if [ -f "tempDirs" ]; then
        rm "tempDirs"
fi

echo "Successfully checked all of the files"
