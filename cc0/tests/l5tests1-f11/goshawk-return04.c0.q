//test return 11

struct node {
    struct node *next;
    int item;
};

typedef struct node node_t;

struct linked_list {
    node_t *head;
    node_t *tail;
};

typedef struct linked_list linked_list_t;

int get_predecessor(linked_list_t *ll, int item);
int fill_list(linked_list_t *ll);
int add_to_list(linked_list_t *ll, int item);

int main()
{
    linked_list_t *ll = alloc(linked_list_t);
    fill_list(ll);
    return get_predecessor(ll, 3);
}

//fills the list with numbers from stdin
int fill_list(linked_list_t *ll)
{
    while (!eof()) {
        add_to_list(ll, readint());
    }

    return 0;
}

//adds the given item to the tail of the linked list
int add_to_list(linked_list_t *ll, int item)
{
    node_t *node = alloc(node_t);
    node->item = item;

    if (ll->head == NULL) {
        ll->head = node;
    } else {
        ll->tail->next = node;
    }

    ll->tail = node;

    return 0;
}

//returns the item before the given item, or -1 if not found
int get_predecessor(linked_list_t *ll, int item)
{
    node_t *node = ll->head;

    if (node == NULL) {
        return -1;
    }

    while (node->next != NULL) {
        if (node->next->item == item)
            return node->item;
        node = node->next;
    }

    return -1;
}
