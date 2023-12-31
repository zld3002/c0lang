//test return -1

// divide-by-zero means the reversed list is longer
// infinite-loop means the list that was constructed backwards is longer
// incorrect return means the nth index was different between the manually
// reversed list and the list that was constructed backwards

struct list {
	struct list * next;
	int data;
};

struct list * reverse(struct list * l) {
	if (l == NULL || l -> next == NULL) return l;
	struct list * after = reverse (l -> next);
	struct list * cur = after;
	while (cur -> next != NULL) {cur = cur -> next;}
	cur -> next = l;
	l -> next = NULL;
	return after;
}

int main () {
	struct list * forward = alloc (struct list);
	struct list * backward = alloc (struct list);

	int x = readint();

	forward -> data = x;
	backward -> data = x;

	struct list *new_forward = forward;

	while (!eof()) {
		x = readint();
		new_forward -> next = alloc (struct list);
		new_forward = new_forward -> next;
		new_forward -> data = x;
		
		struct list * old_backward = backward;
		backward = alloc(struct list);
		backward -> next = old_backward;
		backward -> data = x;
	}

	struct list * reversed = reverse (forward); // side-effectful, but I'm lazy

	int n = 0;

	while (reversed -> next != NULL && backward -> next != NULL) {
		if (reversed -> data != backward -> data) 
		{
			return n; // list index of error
		}
		reversed = reversed -> next;
		backward = backward -> next;
		n++;
	}
	if (reversed -> next != NULL) return 1/0;
	if (backward -> next != NULL) while (true) {}
	return -1;
}


