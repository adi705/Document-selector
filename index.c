/*Author: Aditya*/

#include "index.h"
#include "map.h"
#include "set.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

struct querynode;
typedef struct querynode querynode_t;

static char *error_msg;
static querynode_t *parse_query(list_t *query);
static set_t *eval_query(index_t *index, querynode_t *node);
static void free_query(querynode_t *root);

struct index
{
    map_t *map;			/* Maps words to sets of postings */
    list_t *postings;	/* List of postings to be destroyed */
    list_t *paths;   /* Documents in index */
};

typedef 
struct posting
{
    map_t *tf;			/* Contains the term frequency */
    set_t *paths;		/* Set of paths */
} posting_t;

index_t *index_create()
{
    index_t *index;

    index = malloc(sizeof(index_t));
    if (index == NULL)
    {
        fatal_error("out of memory");
        goto end;
    }

    index->map = map_create(compare_strings, hash_string);
    index->postings = list_create(NULL);
    index->paths = list_create(compare_strings);

end:
    return index;
}


void index_destroy(index_t *index)
{
    posting_t *tmp;

    while (list_size(index->postings) > 0)
    {
        tmp = list_popfirst(index->postings);
        map_destroy(tmp->tf, NULL, free);
        set_destroy(tmp->paths);
        free(tmp);
    }
	
    while (list_size(index->paths) > 0)
        free(list_popfirst(index->paths));

    map_destroy(index->map, free, NULL);
    list_destroy(index->postings);
    list_destroy(index->paths);
    free(index);
}

static posting_t *create_posting()
{
    posting_t *p = malloc(sizeof(posting_t));
    if (p == NULL)
    {
        fatal_error("Out of memory");
        goto end;
    }

    p->paths = set_create(compare_strings);
    p->tf = map_create(compare_pointers, hash_string);

end:
    return p;
}

void index_addpath(index_t *index, char *path, list_t *words)
{
    int *tf;
    char *word;
    posting_t *p;
    list_iter_t *it;
	
    list_addlast(index->paths, path);

    it = list_createiter(words);
    while (list_hasnext(it))
    {
        word = list_next(it);

        /* Locate/create posting for the word */
        if (map_haskey(index->map, word))
        {
            p = map_get(index->map, word);
        }
        else
        {
            p = create_posting();
            list_addlast(index->postings, p);
            map_put(index->map, strdup(word), p);
        }
		
        free(word);

        set_add(p->paths, path);

        /* Update term frequency */
        if (map_haskey(p->tf, path))
        {
            tf = map_get(p->tf, path);
            *tf = *tf + 1;
        }
        else
        {
            tf = malloc(sizeof(int));
            if (tf == NULL)
                fatal_error("Out of memory");

            *tf = 1;
        }

        map_put(p->tf, path, tf);
    }

    list_destroyiter(it);
}

static int compare_results(void *a, void *b)
{
    query_result_t *a1 = (query_result_t *) a;
    query_result_t *b1 = (query_result_t *) b;

    if (a1->score < b1->score)
        return 1;
    else if (a1->score > b1->score)
        return -1;

    return 0;
}

static query_result_t *newresult(char *path, double score)
{
    query_result_t *r;

    r = malloc(sizeof(query_result_t));
    if (r == NULL)
    {
        fatal_error("out of memory");
        goto end;
    }

    r->path = path;
    r->score = score;

end:
    return r;   
}

double calc_score(index_t *index, char *path, char *word)
{
    int *tf;
    double idf;
    posting_t *p;

    /* Return zero if not in index */
    if(!map_haskey(index->map, word))
        return 0.0;

    p = map_get(index->map, word);

    if(!map_haskey(p->tf, path))
        return 0.0;

    tf = (int *) map_get(p->tf, path);
    idf = (double) ((double)list_size(index->paths) / (double)set_size(p->paths));

    /* Normalize length */
    return log((double)(*tf)) * log(idf);
}

list_t *order_results(index_t *index, list_t *query, set_t *res)
{
    list_t *aggr = list_create(compare_results);
    set_iter_t *it;
    list_iter_t *q;
    char *path;
    double score;

    it = set_createiter(res);

    /* For all documents */
    while (set_hasnext(it))
    {
        path = set_next(it);
        score = 0.0;

        /* Calculate the score over all terms */
        q = list_createiter(query);

        while(list_hasnext(q))
            score += calc_score(index, path, list_next(q));

        list_destroyiter(q);

        /* add to accumulator */
        list_addlast(aggr, (void *)newresult(path, score));
    }

    set_destroyiter(it);
    set_destroy(res);

    list_sort(aggr);

    return aggr;
}

list_t *index_query(index_t *index, list_t *query, char **errmsg)
{
    querynode_t *q = parse_query(query);

    if (q == NULL) {
        *errmsg = error_msg;
        printf("Parse error: %s\n", error_msg);
        return NULL;
    }

    /* Evaluate and build query tree */
    set_t *r = eval_query(index, q);
    free_query(q);

    /* Return set as ordered list */
    return order_results(index, query, r);
}

typedef 
enum {
    WORD,
    OR,
    AND,
    ANDNOT,
} node_type;

struct querynode
{
    node_type type;
    char *word; /* NULL unless type == WORD */
    querynode_t *left;
    querynode_t *right;
};

static querynode_t *newnode(node_type type, char *word, querynode_t *left, querynode_t *right)
{
    querynode_t *n = malloc(sizeof(querynode_t));
    if (n == NULL)
    {
        fatal_error("out of memory");
        goto end;
    }

    n->type = type;
    n->word = word;
    n->left = left;
    n->right = right;

end:
    return n;    
}

static list_iter_t *query;
static char *currToken;

static querynode_t *parse_andnotterm();

/*
 * term ::= ( andnotterm )
 *        | <word>
 */
static querynode_t *parse_term()
{
    querynode_t *a;

    if (currToken == NULL) {
        error_msg = "unexpected end of query";
        return NULL;
    }

    if (strcmp(currToken,"(") == 0) {        
        if(list_hasnext(query)) {
            currToken = list_next(query);
        }
        else {
            error_msg = "expected expression after parenthesis";
            return NULL;
        }
        a = parse_andnotterm();
        if (a == NULL)
            return NULL;
        if (currToken == NULL || strcmp(currToken,")") != 0) {
            free_query(a);
            error_msg = "missing closing parenthesis";
            return NULL;
        }
    }
    else {
        a = newnode(WORD, strdup(currToken), NULL, NULL);
    }

    if(list_hasnext(query))
        currToken = list_next(query);
    else
        currToken = NULL;

    return a;
}

/*
 * orterm ::= term
 *          | term OR orterm
 */
static querynode_t *parse_orterm()
{
    querynode_t *a, *b;

    a = parse_term(query);
    if (a == NULL)
        return NULL;

    if(currToken != NULL && strcmp(currToken, "OR") == 0)
    {
        if(list_hasnext(query)) {
            currToken = list_next(query);
        }
        else {
            error_msg = "expected expression after OR";
            return NULL;
        }
        b = parse_orterm();
        if (b == NULL)
            return NULL;
        return newnode(OR, NULL, a, b);
    }
    else {
        return a;
    }
}

/*
 *  andterm ::= orterm
 *            | orterm AND andterm
 */
static querynode_t *parse_andterm()
{
    querynode_t *a, *b;

    a = parse_orterm();
    if (a == NULL)
        return NULL;

    if (currToken != NULL && strcmp(currToken, "AND") == 0) {
        if(list_hasnext(query)) {
            currToken = list_next(query);
        }
        else {
            error_msg = "expected expression after AND";
            return NULL;
        }
        b = parse_andterm();
        if (b == NULL)
            return NULL;
        return newnode(AND, NULL, a, b);
    }
    else {
        return a;
    }
}

/*
 * andnotterm ::= andterm
 *              | andterm ANDNOT andnotterm
 */
static querynode_t *parse_andnotterm()
{
    querynode_t *a, *b;

    a = parse_andterm();
    if (a == NULL)
        return NULL;

    if (currToken != NULL && strcmp(currToken, "ANDNOT") == 0) {
        if(list_hasnext(query)) {
            currToken = list_next(query);
        }
        else {
            error_msg = "expected expression after ANDNOT";
            return NULL;
        }

        b = parse_andnotterm();
        if (b == NULL)
            return NULL;
        return newnode(ANDNOT, NULL, a, b);
    }
    else {
        return a;
    }
}

static querynode_t *parse_query(list_t *q)
{
    querynode_t *r;

    query = list_createiter(q);
    if(list_hasnext(query)) {
        currToken = list_next(query);
    }
    else {
        error_msg = "empty query string";
        list_destroyiter(query);
        return NULL;
    }

    r = parse_andnotterm();
    list_destroyiter(query);

    if (r != NULL && currToken != NULL) {
        free_query(r);
        error_msg = "extra terms at end of query";
        return NULL;
    }

    return r;
}

static set_t *eval_query(index_t *index, querynode_t *node)
{
    set_t *left, *right, *tmp;
    if (node->type == WORD) {
        if (map_haskey(index->map, node->word)) {
            /* Return (a copy of) the set of indexed paths for this word */
            posting_t *p = map_get(index->map, node->word);
            return set_copy(p->paths);
        }
        else {
            /* Unknown word; return an empty set */
            return set_create(compare_strings);
        }
    }
    else if (node->type == OR) {
        left = eval_query(index, node->left);
        right = eval_query(index, node->right);
        tmp = set_union(left, right);
		
        set_destroy(left);
        set_destroy(right);
        return tmp;
    }
    else if (node->type == AND) {
        left = eval_query(index, node->left);
        right = eval_query(index, node->right);
        tmp = set_intersection(left, right);
		
        set_destroy(left);
        set_destroy(right);
        return tmp;
    }
    else if (node->type == ANDNOT) {
        left = eval_query(index, node->left);
        right = eval_query(index, node->right);
        tmp = set_difference(left, right);
		
        set_destroy(left);
        set_destroy(right);
        return tmp;
    }
    else {
        fatal_error("unknown query node type");
        return NULL; /* Never reached */
    }
}

static void free_query(querynode_t *root)
{
    if (root != NULL) {
        free_query(root->left);
        free_query(root->right);
        if (root->word != NULL)
            free(root->word);
        free(root);
    }
}
