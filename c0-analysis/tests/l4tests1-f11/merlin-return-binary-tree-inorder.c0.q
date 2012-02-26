//test return 0
//performs inorder traversal of a binary tree
struct node {
  struct node* left;
  struct node* right;
  int value;
  };

typedef struct node* nodep;

int preorder(nodep root)
{
 if(root == NULL)
 {
   return 0;
 }
 else
 {
   preorder(root->left);
   printint(root->value);
   printchar(0x20);
   preorder(root->right);
   return 1;
 }
}

nodep insert(nodep root, nodep new_node)
{
  if(root == NULL)
    return new_node;
  else
  {
    if(new_node->value < root->value)
      root->left = insert(root->left,new_node);
    else if(new_node->value > root->value)
      root->right = insert(root->right,new_node);
  }
  return root;
}

nodep new_node(int v)
{
  nodep new_node = alloc(struct node);
  new_node->value = v;
  new_node->right = NULL;
  new_node->left = NULL;
  return new_node;
}

int main()
{
  int n = 15;
  int[] a = alloc_array(int,n);
  a[0] = 50;
  a[1] = 51;
  a[2] = 49;
  a[3] = 66;
  a[4] = 8;
  a[5] = 30;
  a[6] = 93;
  a[7] = 12;
  a[8] = 27;
  a[9] = 90;
  a[10] = 8;
  a[11] = 25;
  a[12] = 63;
  a[13] = 111;
  a[14] = 69;

  nodep root = NULL;
  for(int i = 0; i < n; i++)
  {
    root = insert(root,new_node(a[i]));
  }
  preorder(root);
  printchar(0xa);
  return 0;
}

