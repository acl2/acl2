#!/bin/bash

# Original Author: Yahya Sohail <yahya@yahyasohail.com>

# Run `mem-test.lsp` with all the combinations of options and collects the
# results. The ACL2 used can be specified with the `$ACL2` environment variable.
# If it is not set, we try to find `acl2` in the `$PATH`.
#
# By default, we use ACL2::N-WRITES = 100,000. This can be overriden by setting
# the `$N_WRITES` environment variable.
#
# This requires using ACL2 built with CCL since it uses CCL::HEAP-UTILIZATION to
# get heap usage information.
#
# See the comment at the top of `mem-test.lsp` for more information.

# Find ACL2 executable
if [ -n "$ACL2" ]; then
    ACL2_EXEC="$ACL2"
else
    ACL2_EXEC=$(which acl2)
    if [ -z "$ACL2_EXEC" ]; then
        echo "Error: ACL2 executable not found in PATH and ACL2 environment variable not set"
        exit 1
    fi
fi

n_writes=100000
if [ -n "$N_WRITES" ]; then
  n_writes=$N_WRITES
fi

# Arrays of memory modes and benchmarks
MEM_MODES=("symmetric" "asymmetric" "attached")
BENCHMARKS=("low" "high")

# Table header
printf "%-12s %-12s %-15s %-15s %-25s %-25s\n" \
    "Memory" "Benchmark" "BENCH Real(s)" "BENCH Run(s)" "Logical Size(b)" "Physical Size(b)"
printf "%s\n" "---------------------------------------------------------------------------------------------------------------------------------------------"

# Function to run benchmark and extract metrics
run_benchmark() {
    local mem="$1"
    local benchmark="$2"
    
    # Create input for ACL2
    input="(assign acl2::mem :$mem)
(assign acl2::benchmark :$benchmark)
(assign acl2::n-writes $n_writes)
(ld \"mem-test.lsp\")
:q
(ccl::heap-utilization)"
    
    # Run ACL2 with the input
    output=$($ACL2_EXEC <<< "$input")
    
    # Initialize variables for both event types
    benchmark_realtime=""
    benchmark_runtime=""
    
    # Extract BENCHMARK timing if present
    benchmark_section=$(echo "$output" | sed -n '/BEGIN BENCHMARK/,/END BENCHMARK/p')
    if [ -n "$benchmark_section" ]; then
        benchmark_times=$(echo "$benchmark_section" | grep -o "[0-9.]\\+ seconds realtime, [0-9.]\\+ seconds runtime")
        if [ -n "$benchmark_times" ]; then
            benchmark_realtime=$(echo "$benchmark_times" | grep -o "^[0-9.]\\+")
            benchmark_runtime=$(echo "$benchmark_times" | grep -o "[0-9.]\\+ seconds runtime" | grep -o "^[0-9.]\\+")
        fi
    fi
    
    # Extract memory sizes
    total_line=$(echo "$output" | grep "^Total ")
    logical_size=$(echo "$total_line" | awk '{print $3}')
    physical_size=$(echo "$total_line" | awk '{print $4}')
    
    # Output as a row in the table
    printf "%-12s %-12s %-15s %-15s %-25s %-25s\n" \
        "$mem" "$benchmark" "$benchmark_realtime" "$benchmark_runtime" "$logical_size" "$physical_size"
}

# Loop through all combinations
for mem in "${MEM_MODES[@]}"; do
    for benchmark in "${BENCHMARKS[@]}"; do
        run_benchmark "$mem" "$benchmark"
    done
done
