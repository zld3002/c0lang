//test segfault

struct s {
    struct s *a;
    int b;
};

int main()
{
    struct s *s = alloc(struct s);
    int all = readint();
    if (all == 41) {
        s->a = alloc(struct s);
    }
    s->a->b = all;
    return all;
}
