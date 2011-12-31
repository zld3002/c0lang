class Node { int data; Node next; }

class List {
  Node head;

  int length() {
    int len = 0;
    Node p = head;
    while(p != null) {
      len++;
      p = p.next;
    }
    return len;
  }
}

