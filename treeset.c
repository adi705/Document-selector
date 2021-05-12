/* Author: Steffen Viken Valvaag <steffenv@cs.uit.no> */
#include "set.h"
#include "list.h"

#include <stdlib.h>

struct treenode;

typedef struct treenode treenode_t;

struct treenode {
    treenode_t *left;
    treenode_t *right;
    treenode_t *next;
    void *elem;
};

struct set {
    treenode_t *root;   /* Root of the binary tree */
    treenode_t *first;  /* Head of the linked list */
    int size;
    cmpfunc_t cmpfunc;
};

struct set_iter {
    treenode_t *node;
};

static treenode_t *newnode(void *elem)
{
    treenode_t *node = malloc(sizeof(treenode_t));
    if (node == NULL)
        fatal_error("out of memory");
    node->left = NULL;
    node->right = NULL;
    node->next = NULL;
    node->elem = elem;
    return node;
}

static treenode_t *addnode(set_t *set, treenode_t *prev, void *elem)
{
    treenode_t *node = newnode(elem);
    if (prev == NULL) {
        node->next = set->first;
        set->first = node;
    } else {
        node->next = prev->next;
        prev->next = node;
    }
    set->size++;
    return node;
}

set_t *set_create(cmpfunc_t cmpfunc)
{
    set_t *set = malloc(sizeof(set_t));
    if (set == NULL)
        fatal_error("out of memory");
    set->root = NULL;
    set->first = NULL;
    set->size = 0;
    set->cmpfunc = cmpfunc;
    return set;
}

void set_destroy(set_t *set)
{
    treenode_t *n = set->first;
    while (n != NULL) {
        treenode_t *tmp = n;
        n = n->next;
        free(tmp);
    }
    free(set);
}

int set_size(set_t *set)
{
    return set->size;
}

void set_add(set_t *set, void *elem)
{
    treenode_t *n = set->root;
    treenode_t *prev = NULL;

    if (n == NULL) {
        set->root = set->first = newnode(elem);
        set->size++;
    } else {
        /* Regular binary tree insertion, with the added twist that we
           need to update the next pointers of affected nodes. */
        while (n != NULL) {
            int cmp = set->cmpfunc(elem, n->elem);
            if (cmp < 0) {
                if (n->left == NULL) {
                    /* When adding a new left child, we "look back" to find
                       the last time we saw an element less than the new
                       element; that node is the previous node of the new
                       child. */ 
                    n->left = addnode(set, prev, elem);
                    return;
                } else {
                    n = n->left;
                }
            } else if (cmp > 0) {
                if (n->right == NULL) {
                    /* When adding a new right child, we are by nature
                       the previous node of our new child. */
                    n->right = addnode(set, n, elem);
                    return;
                } else {
                    /* Remember the last time we went to the right; or,
                       think of this as remembering the last element we saw
                       that was less than the new element. */
                    prev = n;
                    n = n->right;
                }
            } else {
                /* Already contained */
                return;
            }
        }
    }
}

int set_contains(set_t *set, void *elem)
{
    treenode_t *n = set->root;

    while (n != NULL) {
        int cmp = set->cmpfunc(elem, n->elem);
        if (cmp < 0) {
            n = n->left;
        } else if (cmp > 0) {
            n = n->right;
        } else {
            /* Found it */
            return 1;
        }
    }
    /* No dice */
    return 0;
}

/*
 * Builds a balanced tree from the N first elements of the
 * given sorted list.  Assigns the first, root and last node
 * pointers.
 */
static void buildtree(list_t *list, int N,
                      treenode_t **first, treenode_t **root, treenode_t **last)
{
    if (N == 1) {
        *first = *root = *last = newnode(list_popfirst(list));
    } else if (N > 1) {
        treenode_t *left = NULL;        /* root of left subtree */
        treenode_t *leftlast = NULL;    /* last node in left subtree */
        treenode_t *right = NULL;       /* root of right subtree */
        treenode_t *rightfirst = NULL;  /* first node in right subtree */

        buildtree(list, N/2, first, &left, &leftlast);
        *root = *last = newnode(list_popfirst(list));
        (*root)->left = left;
        leftlast->next = *root;
        if (N > 2) {
            buildtree(list, N - N/2 - 1, &rightfirst, &right, last);
            (*root)->right = right;
            (*root)->next = rightfirst;
        }
    }
}

/*
 * Builds a new set with a balanced tree, given a sorted list.
 * Destroys the list before returning the new set.
 */
static set_t *buildset(list_t *list, cmpfunc_t cmpfunc)
{
    set_t *set = set_create(cmpfunc);
    int size = list_size(list);
    
    if (size > 0) {
        treenode_t *last;       
        buildtree(list, size, &(set->first), &(set->root), &last);
        set->size = size;
    }
    list_destroy(list);

    return set;
}

set_t *set_union(set_t *a, set_t *b)
{
    if (a->cmpfunc != b->cmpfunc) {
        fatal_error("union of incompatible sets");
    } else {
        /* Merge the two sets into a sorted list */
        list_t *result = list_create(a->cmpfunc);
        treenode_t *na = a->first;
        treenode_t *nb = b->first;

        while (na != NULL && nb != NULL) {
            int cmp = a->cmpfunc(na->elem, nb->elem);
            if (cmp < 0) {
                /* Occurs in a only */
                list_addlast(result, na->elem);
                na = na->next;
            } else if (cmp > 0) {
                /* Occurs in b only */
                list_addlast(result, nb->elem);
                nb = nb->next;
            } else {
                /* Occurs in both a and b */
                list_addlast(result, na->elem);
                na = na->next;
                nb = nb->next;
            }
        }
        /* Plus what's left of the remaining set (either a or b) */
        for (; na != NULL; na = na->next) {
            list_addlast(result, na->elem);
        }
        for (; nb != NULL; nb = nb->next) {
            list_addlast(result, nb->elem);
        }
        /* Convert the sorted list into a balanced tree */
        return buildset(result, a->cmpfunc);
    }
}

set_t *set_intersection(set_t *a, set_t *b)
{
    if (a->cmpfunc != b->cmpfunc) {
        fatal_error("intersection of incompatible sets");
    } else {
        /* Merge the two sets into a sorted list,
           keeping common elements only */
        list_t *result = list_create(a->cmpfunc);
        treenode_t *na = a->first;
        treenode_t *nb = b->first;

        while (na != NULL && nb != NULL) {
            int cmp = a->cmpfunc(na->elem, nb->elem);
            if (cmp < 0) {
                /* Occurs in a only */
                na = na->next;
            } else if (cmp > 0) {
                /* Occurs in b only */
                nb = nb->next;
            } else {
                /* Occurs in both a and b, keep this one */
                list_addlast(result, na->elem);
                na = na->next;
                nb = nb->next;
            }
        }
        /* Convert the sorted list into a balanced tree */
        return buildset(result, a->cmpfunc);
    }
}

set_t *set_difference(set_t *a, set_t *b)
{
    if (a->cmpfunc != b->cmpfunc) {
        fatal_error("difference between incompatible sets");
    } else {
        /* Merge the two sets into a sorted list,
           keeping only elements that occur in a and not b */
        list_t *result = list_create(a->cmpfunc);
        treenode_t *na = a->first;
        treenode_t *nb = b->first;

        while (na != NULL && nb != NULL) {
            int cmp = a->cmpfunc(na->elem, nb->elem);
            if (cmp < 0) {
                /* Occurs in a only, keep this one */
                list_addlast(result, na->elem);
                na = na->next;
            } else if (cmp > 0) {
                /* Occurs in b only */
                nb = nb->next;
            } else {
                /* Occurs in both a and b */
                na = na->next;
                nb = nb->next;
            }
        }
        /* Plus what's left of a */
        for (; na != NULL; na = na->next) {
            list_addlast(result, na->elem);
        }
        /* Convert the sorted list into a balanced tree */
        return buildset(result, a->cmpfunc);
    }
}

set_t *set_copy(set_t *set)
{
    /* Insert all our elements into a list in sorted order */
    list_t *list = list_create(set->cmpfunc);
    treenode_t *n = set->first;
    while (n != NULL) {
        list_addlast(list, n->elem);
        n = n->next;
    }
    /* Convert the sorted list into a balanced tree */
    return buildset(list, set->cmpfunc);
}

set_iter_t *set_createiter(set_t *set)
{
    set_iter_t *iter = malloc(sizeof(set_iter_t));
    if (iter == NULL)
        fatal_error("out of memory");
    iter->node = set->first;
    return iter;
}

void set_destroyiter(set_iter_t *iter)
{
    free(iter);
}

int set_hasnext(set_iter_t *iter)
{
    if (iter->node == NULL)
        return 0;
    else
        return 1;
}

void *set_next(set_iter_t *iter)
{
    if (iter->node == NULL) {
        fatal_error("set iterator exhausted");
    } else {
        void *elem = iter->node->elem;
        iter->node = iter->node->next;
        return elem;
    }
}

