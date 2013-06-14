#include <iostream>
#include <fstream>
#include <cstdlib>
using namespace std;

int main(int argc, char** argv)
{
    ifstream in;
    int size;
    int i;
    char c;
    
    if (argc != 3)
    {
        printf("Usage: %s <big-file> <size-in-kb>\n", argv[0]);
        return 1;
    }
    
    in.open(argv[1]);
    if (!in.good()) {
        printf("Error opening %s\n", argv[1]);
        return 1;
    }
   
    size = atoi(argv[2]) * 1024; 
    
    for(i = 0;i < size;++i)
        c = in.get();

    return 0;
}
