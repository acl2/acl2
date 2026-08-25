struct node;

struct links {
  struct node *next;
};

struct node {
  int x;
  int z;
  struct links links;
};

static struct node n;

int main(void) {
  return n.x;
}
