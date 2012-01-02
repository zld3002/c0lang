//test segfault
//code forgets to check for empty linked list

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

int main()
{
    return get_predecessor(alloc(linked_list_t), 3);
}

//returns the item before the given item, or -1 if not found
int get_predecessor(linked_list_t *ll, int item)
{
    node_t *node = ll->head;

    while (node->next != NULL) {
        if (node->next->item == item)
            return node->item;
        node = node->next;
    }

    return -1;
}
