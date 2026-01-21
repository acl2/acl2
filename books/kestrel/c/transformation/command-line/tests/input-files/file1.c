struct foo {
    char a1[20];
    int a1_size;
    char a2[30];
    int a2_size;
};

static struct foo foo_data = { .a1_size = 0, .a2_size = 0 };

int bar () {return foo_data.a1_size;}
