// COMP2521 24T3 - Assignment 1
// Implementation of the Multiset ADT
// Written by Ivan Lun Hui Chen(z5557064@unsw.edu.au)
// 2024/10/12

// Acknowledgements:
// - doMsetInsert
//	 The following code was adapted from the comp2521 2024T3 avl slides.
//	 Link: https://cgi.cse.unsw.edu.au/~cs2521/24T3/lectures/Week4Mon-avl.pdf
//	 It recursively traverses through the current tree and inserts the new item
//	 with the given amount when it has traversed to the correct position in the 
//	 tree. It also rebalances the tree.
// - avlRebalance
//	 The following code was adapted from the comp2521 2024T3 avl slides.
//	 Link: https://cgi.cse.unsw.edu.au/~cs2521/24T3/lectures/Week4Mon-avl.pdf
//	 It uses the rotation functions to rebalance the tree.
// - balance
//	 The code was adapted from the comp2521 2024T3 avl slides.
//	 Link: https://cgi.cse.unsw.edu.au/~cs2521/24T3/lectures/Week4Mon-avl.pdf
//	 It uses the the heights of the nodes to check if the tree is 
//	 height-balanced.
// - rotateRight
//	 The code was adapted from the comp2521 2024T3 balancing_bst slides.
//	 Link: https://cgi.cse.unsw.edu.au/~cs2521/24T3/lectures/Week4Mon-balancing-bst.pdf
//	 It rotates the given node and relevant nodes to the right to balance the 
//	 tree.
// - rotateLeft
//	 The following code was adapted from the comp2521 2024T3 balancing_bst 
//	 slides.
//	 Link: https://cgi.cse.unsw.edu.au/~cs2521/24T3/lectures/Week4Mon-balancing-bst.pdf
//	 It rotates the given node and relevant nodes to the left to balance the 
//	 tree.
// - doMsetDelete
//	 The following code was adapted from the comp2521 2024T3 avl slides.
//	 Link: https://cgi.cse.unsw.edu.au/~cs2521/24T3/lectures/Week4Mon-avl.pdf
//	 It recursively traverses through the tree until we are at the node with the
//	 item, then deletes it or subtracts the given amount and rebalances the tree.
// - bstJoin
//	 The following code was adapted from the comp2521 2024T3 bst slides.
//	 Link: https://cgi.cse.unsw.edu.au/~cs2521/24T3/lectures/Week3Mon-bst.pdf
//	 Joins two trees into one tree.
// - mergeSort
//	 The following code was adapted from the comp2521 2024T3 divide-and-conquer-
//	 sorts slides.
//	 Link: https://cgi.cse.unsw.edu.au/~cs2521/24T3/lectures/Week2Wed-divide-and-conquer-sorts.pdf
//	 It uses the mergeSort algorithm to sort the given array in descending order.
// - merge
//	 The following code was adapted from the comp2521 2024T3 divide-and-conquer-
//	 sorts slides.
//	 Link: https://cgi.cse.unsw.edu.au/~cs2521/24T3/lectures/Week2Wed-divide-and-conquer-sorts.pdf
//	 It uses the mergeSort algorithm to sort the given array.

#include <assert.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>

#include "Mset.h"
#include "MsetStructs.h"


// Part 1
static void printNullError(void);
static void doMsetFree(struct node *tree);

static struct node *doMsetInsert(Mset s, struct node *tree, int item,
int amount);
static struct node *newNode(int item, int amount);
static void setCursorList(struct node *tree, Mset s, bool left);
static int recomputeHeight(struct node *tree);
static int max(struct node *node1, struct node *node2);
static struct node *avlRebalance(struct node *tree);
static int balance(struct node *tree);
static struct node *rotateRight(struct node *tree);
static struct node *rotateLeft(struct node *tree);

static struct node *doMsetDelete(Mset s, struct node *tree, int item,
int amount);
static void updateLink(struct node *tree);
static struct node *bstJoin(struct node *left, struct node *right);

static struct node *bstFind(struct node *tree, int item);

static void doMsetPrint(struct node *tree, FILE *file, int *size);

//Part 2
static void doMsetUnion(Mset setUnion, struct node *t1, struct node *t2);

static void doMsetIntersection(Mset setIntersection, struct node *t1, 
struct node *t2);

static bool doMsetIncluded(struct node *t1, struct node *t2);

static void copyArray(struct node *tree, struct item *elements, int *index);
static void mergeSort(struct item *elements, int lo, int hi);
static void merge(struct item *elements, int lo, int mid, int hi);

////////////////////////////////////////////////////////////////////////
// Basic Operations

/**
 * Creates a new empty multiset.
 */
Mset MsetNew(void) {
	struct mset *new = malloc(sizeof(struct mset));
	if (new == NULL) {
		printNullError();
	}
	new->tree = NULL;
	new->size = 0;
	new->totalCount = 0;
	new->listBegin = NULL;
	new->listEnd = NULL;
	new->subTreeNext = NULL;
	new->subTreePrev = NULL;
	new->smallest = INT_MAX;
	new->biggest = INT_MIN;
	return new;
}

/*
* Prints an error message and terminates the program if malloc returns NULL.
*/
static void printNullError(void) {
	fprintf(stderr, "Error: out of memory.\n");
	exit(EXIT_FAILURE);
}

/**
 * Frees all memory allocated to the multiset.
 */
void MsetFree(Mset s) {
	doMsetFree(s->tree);
	free(s);
}

/*
* Frees all the memory allocated to the tree.
*/
static void doMsetFree(struct node *tree) {
	if (tree == NULL) {
		return;
	}

	doMsetFree(tree->left);
	doMsetFree(tree->right);
	free(tree);
}

/**
 * Inserts one of an item into the multiset. Does nothing if the item is
 * equal to UNDEFINED.
 */
void MsetInsert(Mset s, int item) {
	if (item != UNDEFINED) {
		s->tree = doMsetInsert(s, s->tree, item, 1);
		s->subTreeNext = NULL;
		s->subTreePrev = NULL;
		s->totalCount++;
	}
}

/*
* Insets an item into the tree.
* The following code was adapted from the comp2521 2024T3 avl slides.
* Link: https://cgi.cse.unsw.edu.au/~cs2521/24T3/lectures/Week4Mon-avl.pdf
* It recursively traverses through the current tree and inserts the new item
* with the given amount when it has traversed to the correct position in the 
* tree. It also rebalances the tree.
*/
static struct node *doMsetInsert(Mset s, struct node *tree, int item,
int amount) {
	if (tree == NULL) {
		tree = newNode(item, amount);
		s->size++;

		if (tree->elem < s->smallest) {
			//Ensures that listBegin is the smallest element of the multiset.
			s->listBegin = tree;
			s->smallest = tree->elem;
		}

		if (tree->elem > s->biggest) {
			//Ensures that listEnd is the biggest element of the multiset.
			s->listEnd = tree;
			s->biggest = tree->elem;
		}
	} else if (item < tree->elem){
		//keeps track of the node that is the next node of the rightest node
		//in a subtree.
		s->subTreeNext = tree;
		tree->left = doMsetInsert(s, tree->left, item, amount);
		setCursorList(tree, s, true);
		tree->height = recomputeHeight(tree);
	} else if (item > tree->elem) {
		//keeps track of the node that is the next node of the leftest node
		//in a subtree.
		s->subTreePrev = tree;
		tree->right = doMsetInsert(s, tree->right, item, amount);
		setCursorList(tree, s, false);
		tree->height = recomputeHeight(tree);
	} else {
		//the current node's element is equal to item.
		tree->count += amount;
	}

	return avlRebalance(tree);
}

/*
* creates a new node for the tree with the given item and amount.
*/
static struct node *newNode(int item, int amount) {
	struct node *new = malloc(sizeof(struct node));
	if (new == NULL) {
		printNullError();
	}
	new->count = amount;
	new->elem = item;
	new->left = NULL;
	new->right = NULL;
	new->height = 0;
	new->next = NULL;
	new->prev = NULL;
	return new;
}

/*
* Sets the next pointers and prev pointers of each node in the tree to set up
* the list for the cursor operations. The operations depend on whether it is the
* left subtree or the right subtree.
*/
static void setCursorList(struct node *tree, Mset s, bool left) {
	if (left) {
		//if the node is the leftest node of the subtree and not when we are
		//backtracking.
		if (tree->left->prev == NULL && tree->left != s->subTreePrev) {
			tree->left->prev = s->subTreePrev;
			if (s->subTreePrev != NULL) {
				s->subTreePrev->next = tree->left;
			}
		}

		//sets the link between the current node and its left child if the left
		//child's next value should be the current node's value.
		if (tree->left->right == NULL) {
			tree->left->next = tree;
			tree->prev = tree->left;
		}
	} else {
		//if the node is the rightest node of the subtree and not when we are
		//backtracking.
		if (tree->right->next == NULL && tree->right != s->subTreeNext) {
			tree->right->next = s->subTreeNext;
			if (s->subTreeNext != NULL) {
				s->subTreeNext->prev = tree->right;
			}
		}

		//sets the link between the current node and its right child if the right
		//child's next value should be the current node's value.
		if (tree->right->left == NULL) {
			tree->next = tree->right;
			tree->right->prev = tree;
		}
	}
}

/*
* Calculates the height based on the left and right subtree.
*/
static int recomputeHeight(struct node *tree) {
	return max(tree->left, tree->right) + 1;
}

/*
* This compares the heights of the two nodes given and returns the greater of 
* the two.
*/
static int max(struct node *node1, struct node *node2) {
	if (node1 == NULL && node2 == NULL) {
		return -1;
	} else if (node1 == NULL) {
		return node2->height;
	} else if (node2 == NULL) {
		return node1->height;
	}

	if (node1->height > node2->height) {
		return node1->height;
	}

	return node2->height;
}

/*
* Rebalances a possibly unbalance tree.
* The following code was adapted from the comp2521 2024T3 avl slides.
* Link: https://cgi.cse.unsw.edu.au/~cs2521/24T3/lectures/Week4Mon-avl.pdf
* It uses the rotation functions to rebalance the tree.
*/
static struct node *avlRebalance(struct node *tree) {
	if (tree == NULL) {
		return NULL;
	}

	int bal = balance(tree);

	if (bal > 1) {
		//left subtree's height is greater than right subtree's height.
		if (balance(tree->left) < 0) {
			//left right imbalance case.
			tree->left = rotateLeft(tree->left);
		}
		//left left imbalance case.
		tree = rotateRight(tree);
	} else if (bal < -1) {
		//right subtree's height is greater than left subtree's height.
		if (balance(tree->right) > 0) {
			//right left imbalance case.
			tree->right = rotateRight(tree->right);
		}
		//right right imbalance case.
		tree = rotateLeft(tree);
	}

	return tree;
}

/*
* Checks the balance of the subtree at the given node.
* The following code was adapted from the comp2521 2024T3 avl slides.
* Link: https://cgi.cse.unsw.edu.au/~cs2521/24T3/lectures/Week4Mon-avl.pdf
* It uses the the heights of the child nodes to check if the tree is 
* height-balanced.
*/
static int balance(struct node *tree) {
	int lh = -1;
	int rh = -1;

	if (tree->left != NULL) {
		lh = tree->left->height;
	}
	if (tree->right != NULL) {
		rh = tree->right->height;
	}

	return lh - rh;
}

/*
* Performs a right rotation at the given node to balance the subtree.
* The following code was adapted from the comp2521 2024T3 balancing_bst slides.
* Link: https://cgi.cse.unsw.edu.au/~cs2521/24T3/lectures/Week4Mon-balancing-bst.pdf
* It rotates the given node and relevant nodes to the right to balance the tree.
*/
static struct node *rotateRight(struct node *tree) {
	if (tree == NULL || tree->left == NULL) {
		return tree;
	}

	struct node *newRoot = tree->left;
	tree->left = newRoot->right;
	newRoot->right = tree;
	tree->height = recomputeHeight(tree);
	newRoot->height = recomputeHeight(newRoot);

	return newRoot;
}

/*
* Performs a left rotation at the given node to balance the subtree.
* The following code was adapted from the comp2521 2024T3 balancing_bst slides.
* Link: https://cgi.cse.unsw.edu.au/~cs2521/24T3/lectures/Week4Mon-balancing-bst.pdf
* It rotates the given node and relevant nodes to the left to balance the tree.
*/
static struct node *rotateLeft(struct node *tree) {
	if (tree == NULL || tree->right == NULL) {
		return tree;
	}

	struct node *newRoot = tree->right;
	tree->right = newRoot->left;
	newRoot->left = tree;
	tree->height = recomputeHeight(tree);
	newRoot->height = recomputeHeight(newRoot);

	return newRoot;
}

/**
 * Inserts the given amount of an item into the multiset. Does nothing
 * if the item is equal to UNDEFINED or the given amount is 0 or less.
 */
void MsetInsertMany(Mset s, int item, int amount) {
	if (item != UNDEFINED && amount > 0) {
		s->tree = doMsetInsert(s, s->tree, item, amount);
		s->subTreeNext = NULL;
		s->subTreePrev = NULL;
		s->totalCount += amount;
	}
}

/**
 * Deletes one of an item from the multiset.
 */
void MsetDelete(Mset s, int item) {
	s->tree = doMsetDelete(s, s->tree, item, 1);
}

/*
* Deletes an item from the tree.
* The following code was adapted from the comp2521 2024T3 avl slides.
* Link: https://cgi.cse.unsw.edu.au/~cs2521/24T3/lectures/Week4Mon-avl.pdf
* It recursively traverses through the tree until we are at the node with the
* item, then deletes it or subtracts the given amount and rebalances the tree.
*/
static struct node *doMsetDelete(Mset s, struct node *tree, int item,
int amount) {
	if (tree == NULL) {
		return NULL;
	}

	if (item < tree->elem){
		tree->left = doMsetDelete(s, tree->left, item, amount);
		tree->height = recomputeHeight(tree);
	} else if (item > tree->elem) {
		tree->right = doMsetDelete(s, tree->right, item, amount);
		tree->height = recomputeHeight(tree);
	} else {
		//the current node's element is equal to item
		tree->count -= amount;
		s->totalCount -= amount;

		if (tree->count <= 0) {
			s->size--;
			s->totalCount -= tree->count;

			if (tree == s->listBegin) {
				s->listBegin = s->listBegin->next;
			}
			if (tree == s->listEnd) {
				s->listEnd = s->listEnd->prev;
			}

			updateLink(tree);
			struct node *left = tree->left;
			struct node *right = tree->right;
			free(tree);
			tree = bstJoin(left, right);
		}
	}
	return avlRebalance(tree);
}

/*
* Updates the next and prev pointers of the next and previous nodes of the 
* current node that is being deleted.
*/
static void updateLink(struct node *tree) {
	if (tree->next != NULL) {
		tree->next->prev = tree->prev;
	}
	if (tree->prev != NULL) {
		tree->prev->next = tree->next;
	}
}

/*
* The following code was adapted from the comp2521 2024T3 bst slides.
* Link: https://cgi.cse.unsw.edu.au/~cs2521/24T3/lectures/Week3Mon-bst.pdf
* Joins two trees into one tree.
*/
static struct node *bstJoin(struct node *left, struct node *right) {
	if (left == NULL) {
		return right;
	}
	if (right == NULL) {
		return left;
	}
	struct node *curr = right;
	struct node *parent = NULL;

	while (curr->left != NULL) {
		//finds leftmost node
		parent = curr;
		curr = curr->left;
	}

	if (parent != NULL) {
		//joins left subtree to right subtree
		parent->left = curr->right;
		curr->right = right;
	}

	curr->left = left;
	return curr;
}

/**
 * Deletes the given amount of an item from the multiset.
 */
void MsetDeleteMany(Mset s, int item, int amount) {
	s->tree = doMsetDelete(s, s->tree, item, amount);
}

/**
 * Returns the number of distinct elements in the multiset.
 */
int MsetSize(Mset s) {
	return s->size;
}

/**
 * Returns the sum of counts of all elements in the multiset.
 */
int MsetTotalCount(Mset s) {
	return s->totalCount;
}

/**
 * Returns the count of an item in the multiset, or 0 if it doesn't
 * occur in the multiset.
 */
int MsetGetCount(Mset s, int item) {
	struct node *node = bstFind(s->tree, item);

	if (node != NULL) {
		return node->count;
	}
	return 0;
}

/*
* Finds the given item if it exists in the tree. If not, return NULL.
*/
static struct node *bstFind(struct node *tree, int item) {
	if (tree == NULL) {
		return NULL;
	}
	if (item < tree->elem) {
		return bstFind(tree->left, item);
	} else if (item > tree->elem) {
		return bstFind(tree->right, item);
	}
	//the current node's value is equal to item
	return tree;
}

/**
 * Prints the multiset to a file.
 * The elements of the multiset should be printed in ascending order
 * inside a pair of curly braces, with elements separated by a comma
 * and space. Each element should be printed inside a pair of
 * parentheses with its count, separated by a comma and space.
 */
void MsetPrint(Mset s, FILE *file) {
	fprintf(file,"{");
	int size = MsetSize(s);
	doMsetPrint(s->tree, file, &size);
	fprintf(file,"}");
	
}

/*
* Prints the bst in the multiset to a file.
*/
static void doMsetPrint(struct node *tree, FILE *file, int *size) {
	if (tree == NULL) {
		return;
	}

	doMsetPrint(tree->left, file, size);
	fprintf(file, "(%d, %d)", tree->elem, tree->count);
	*size-=1;

	if (*size > 0) {
		fprintf(file, ", ");
	}

	doMsetPrint(tree->right, file, size);
}


////////////////////////////////////////////////////////////////////////
// Advanced Operations

/**
 * Returns a new multiset representing the union of the two given
 * multisets.
 */
Mset MsetUnion(Mset s1, Mset s2) {
	Mset setUnion = MsetNew();
	if (s1->size == 0) {
		doMsetUnion(setUnion, setUnion->tree, s2->tree);
		return setUnion;
	}

	//sets the union set with s1's tree.
	doMsetUnion(setUnion, setUnion->tree, s1->tree);
	if (s2->size == 0) {
		return setUnion;
	}
	doMsetUnion(setUnion, setUnion->tree, s2->tree);

	return setUnion;
}

/*
* Add the elements in t2 bst that are not in setUnion and updates the count if 
* the element exists in setUnion.
*/
static void doMsetUnion(Mset setUnion, struct node *t1, struct node *t2) {
	if (t2 == NULL) {
		return;
	}
	//if t2's element is found in t1, returns the element, NULL otherwise.
	struct node *foundElement = bstFind(t1, t2->elem);
	if (foundElement != NULL) {
		if (foundElement->count < t2->count) {
			//Sets the element in the union multiset to have the highest count
			//out of the two.
			setUnion->totalCount += (t2->count - foundElement->count);
			foundElement->count = t2->count;
		}
	} else {
		MsetInsertMany(setUnion, t2->elem, t2->count);
	}
	
	doMsetUnion(setUnion, t1, t2->left);
	doMsetUnion(setUnion, t1, t2->right);
}

/**
 * Returns a new multiset representing the intersection of the two
 * given multisets.
 */
Mset MsetIntersection(Mset s1, Mset s2) {
	Mset setIntersection = MsetNew();
	if (s1->size == 0 || s2->size == 0) {
		return setIntersection;
	}
	// this ensures that the first argument is the tree of the smaller multiset.
	if (s1->size >= s2->size) {
		doMsetIntersection(setIntersection, s2->tree, s1->tree);
	} else {
		doMsetIntersection(setIntersection, s1->tree, s2->tree);
	}
	return setIntersection;
}

/*
* Checks if the nodes in t1(smaller tree) exist in t2, if it exists, add to the 
* intersection multiset.
*/
static void doMsetIntersection(Mset setIntersection, struct node *t1, 
struct node *t2) {
	if (t1 == NULL) {
		return;
	}

	struct node *foundElement = bstFind(t2, t1->elem);
	if (foundElement != NULL) {
		//Ensuring that we are inserting into the union multiset with the lowest
		//count.
		if (t1->count < foundElement->count) {
			MsetInsertMany(setIntersection, t1->elem, t1->count);
		} else {
			MsetInsertMany(setIntersection, t1->elem, foundElement->count);
		}
	}

	doMsetIntersection(setIntersection, t1->left, t2);
	doMsetIntersection(setIntersection, t1->right, t2);
}

/**
 * Returns true if the multiset s1 is included in the multiset s2, and
 * false otherwise.
 */
bool MsetIncluded(Mset s1, Mset s2) {
	if (s1->size > s2->size) {
		return false;
	}
	
	return doMsetIncluded(s1->tree, s2->tree);
}

/*
* Checks if the tree t2 includes the tree t1.
*/
static bool doMsetIncluded(struct node *t1, struct node *t2) {
	//the empty set is always a subset of the other set.
	if (t1 == NULL) {
		return true;
	}

	struct node *foundElement = bstFind(t2, t1->elem);
	if (foundElement != NULL) {
		if (t1->count <= foundElement->count) {
			//recursively checks that every element of t1 is in t2.
			return true && doMsetIncluded(t1->left, t2) && 
			doMsetIncluded(t1->right, t2);
		}
	}
	return false;
}

/**
 * Returns true if the two given multisets are equal, and false
 * otherwise.
 */
bool MsetEquals(Mset s1, Mset s2) {
	if ((s1->size != s2->size) || (s1->totalCount != s2->totalCount)) {
		return false;
	}

	//The sets are only equal if and only if they both include each other.
	return doMsetIncluded(s1->tree, s2->tree) && 
	doMsetIncluded(s2->tree, s1->tree);
}

/**
 * Stores the k most common elements in the multiset into the given
 * items array in decreasing order of count and returns the number of
 * elements stored. Elements with the same count should be stored in
 * increasing order. Assumes that the items array has size k.
 */
int MsetMostCommon(Mset s, int k, struct item items[]) {
	if (k <= 0 || s->size == 0) {
		return 0;
	}

	struct item *elements = malloc(sizeof(struct item) * s->size);
	if (elements == NULL) {
		printNullError();
	}
	int index = 0;
	//copies the elements of the current tree into an array.
	copyArray(s->tree, elements, &index);
	mergeSort(elements, 0, s->size - 1);

	int i = 0;
	while (i < k && i < s->size) {
		items[i] = elements[i];
		i++;
	}
	free(elements);
	return i;
}

/*
* Copies the count and element of all the nodes of the tree into the given 
* array.
*/
static void copyArray(struct node *tree, struct item *elements, int *index) {
	if (tree == NULL) {
		return;
	}

	copyArray(tree->left, elements, index);
	struct item newItem = {tree->elem, tree->count};
	elements[*index] = newItem;
	(*index)++;
	copyArray(tree->right, elements, index);
}

/*
* Sorts the array using mergeSort.
* The following code was adapted from the comp2521 2024T3 divide-and-conquer-
* sorts slides.
* Link: https://cgi.cse.unsw.edu.au/~cs2521/24T3/lectures/Week2Wed-divide-and-conquer-sorts.pdf
* It uses the mergeSort algorithm to sort the given array in descending order.
*/
static void mergeSort(struct item *elements, int lo, int hi) {
	if (lo >= hi) {
		return;
	}

	int mid = (lo + hi) / 2;
	mergeSort(elements, lo, mid);
	mergeSort(elements, mid+1, hi);
	merge(elements, lo, mid, hi);
}

/*
* Merges the arrays.
* The following code was adapted from the comp2521 2024T3 divide-and-conquer-
* sorts slides.
* Link: https://cgi.cse.unsw.edu.au/~cs2521/24T3/lectures/Week2Wed-divide-and-conquer-sorts.pdf
* It uses the mergeSort algorithm to sort the given array.
*/
static void merge(struct item *elements, int lo, int mid, int hi) {
	struct item *tmp = malloc((hi - lo + 1) * sizeof(struct item));
	if (tmp == NULL) {
		printNullError();
	}
	int i = lo, j = mid + 1, k = 0;

	while (i <= mid && j <= hi) {
		if (elements[i].count > elements[j].count) {
			tmp[k++] = elements[i++];
		} else if (elements[i].count < elements[j].count){
			tmp[k++] = elements[j++];
		} else {
			//if the counts of the two elements are the same, sort according to
			//their element values in ascending order.
			if (elements[i].elem < elements[j].elem) {
				tmp[k++] = elements[i++];
			} else {
				tmp[k++] = elements[j++];
			}
		}
	}

	//copies the rest of the uncopied values into the tmp array.
	while (i <= mid) {
		tmp[k++] = elements[i++];
	}
	while (j <= hi) {
		tmp[k++] = elements[j++];
	}

	for (int i = lo, k = 0; i <= hi; i++, k++) {
		elements[i] = tmp[k];
	}
	free(tmp);
}

////////////////////////////////////////////////////////////////////////
// Cursor Operations

/**
 * Creates a new cursor positioned at the start of the multiset.
 * (see spec for explanation of start and end)
 */
MsetCursor MsetCursorNew(Mset s) {
	MsetCursor new = malloc(sizeof(struct cursor));
	if (new == NULL) {
		printNullError();
	}
	new->start = newNode(UNDEFINED, 0);
	new->start->next = s->listBegin;
	new->end = newNode(UNDEFINED, 0);
	new->end->prev = s->listEnd;
	new->curr = new->start;
	new->right = new->curr->next;
	new->left = NULL;
	new->s = s;
	return new;
}

/**
 * Frees all memory allocated to the given cursor.
 */
void MsetCursorFree(MsetCursor cur) {
	free(cur->start);
	free(cur->end);
	free(cur);
}

/**
 * Returns the element at the cursor's position and its count, or
 * {UNDEFINED, 0} if the cursor is positioned at the start or end of
 * the multiset.
 */
struct item MsetCursorGet(MsetCursor cur) {
	return (struct item){cur->curr->elem, cur->curr->count};
}

/**
 * Moves the cursor to the next greatest element, or to the end of the
 * multiset if there is no next greatest element. Does not move the
 * cursor if it is already at the end. Returns false if the cursor is at
 * the end after this operation, and true otherwise.
 */
bool MsetCursorNext(MsetCursor cur) {
	//the next element in the list is the end.
	if (cur->curr->next == NULL) {
		cur->left = cur->s->listEnd;
		cur->curr = cur->end;
		cur->curr->prev = cur->left;	
		cur->right = NULL;
		return false;
	}

	if (cur->curr->elem == UNDEFINED) {
		//cursor is currently at the end.
		if (cur->curr->prev != NULL) {
			return false;
		} else {
			//cursor is currently at the beginning.
			cur->left = cur->curr;
			cur->curr = cur->s->listBegin;
			cur->right = cur->curr->next;
			return true;
		}
	}
	//moves the cursor to the next element in the list.
	cur->left = cur->curr;
	cur->curr = cur->curr->next;
	cur->right = cur->curr->next;
	return true;
}

/**
 * Moves the cursor to the next smallest element, or to the start of the
 * multiset if there is no next smallest element. Does not move the
 * cursor if it is already at the start. Returns false if the cursor is
 * at the start after this operation, and true otherwise.
 */
bool MsetCursorPrev(MsetCursor cur) {
	//the previous element is the beginning.
	if (cur->curr->prev == NULL) {
		cur->right = cur->s->listBegin;
		cur->curr = cur->start;
		cur->curr->next = cur->right;
		cur->left = NULL;
		return false;
	}	
	
	if (cur->curr->elem == UNDEFINED) {
		//cursor is currently at the beginning.
		if (cur->curr->next != NULL) {
			return false;
		} else {
			//cursor is currently at the end.
			cur->right = cur->curr;
			cur->curr = cur->s->listEnd;
			cur->left = cur->curr->prev;
			return true;
		}
	}
	//moves the cursor to the previous element in the list.
	cur->right = cur->curr;
	cur->curr = cur->curr->prev;
	cur->left = cur->curr->prev;
	return true;
}

////////////////////////////////////////////////////////////////////////

