#include <stdio.h>
#include <stdlib.h>

int main(int argc, char**argv)
{
    FILE* in;
    int size;
    int i;
    char c;
    
    if (argc != 3)
    {
        printf("Usage: %s <big-file> <size-in-kb>\n", argv[0]);
        return 1;
    }

    if (!(in = fopen(argv[1], "r"))) {
        printf("Error opening %s\n", argv[1]);
        return 1;
    }

    size = atoi(argv[2]) * 1024;
    
    for(i = 0;i < size;++i) 
        c = fgetc(in);

    return 0;
}
