// Overkill System for ACL2 Testing
// Written by Jared Davis 

#include "Manager.h"

int main(int argc, char** argv)
{
    Manager m(argc, argv);
    m.startWorkers();
    return 0;
}

