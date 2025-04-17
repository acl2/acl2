// RAC begin

const int global_array[2] = {1, 2 };

int foo() {
    return global_array[1];
}

int bar() {
    const int local_array[2] = {3, 5};
    return local_array[1];
}

int bar2() {
    int local_mutable_array[2] = {3, 5};
    local_mutable_array[1] = 4;
    return local_mutable_array[1];
}
