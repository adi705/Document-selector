/* 
 * Authors:
 * Magnus Stenhaug <magnus.stenhaug@uit.no> 
 * Erlend Helland Graff <erlend.h.graff@uit.no> 
 */

#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include "common.h"
#include "index.h"
#include "list.h"
#include "set.h"

#define WORD_LENGTH ( 10 )
#define NUM_ITEMS ( 500 )
#define NUM_DOCS ( 50 )

typedef
struct document{
    set_t *terms;
    char path[20];
}document_t;

static document_t docs[NUM_DOCS];

/* Generates a random sequence of characters given a seed */
char *
generate_string(unsigned int *seed)
{
    int i;
    int len;
    char *s;

    len = (rand_r(seed) % WORD_LENGTH) + 1;

    /* Generate a random string of characters */
    s = calloc(sizeof(char), len + 1 );
    for(i = 0 ; i < len; i++)
        s[i] = 'a' + (rand_r(seed) % ('z' - 'a'));

    return s;
}

/* Generates a list of words which acts a a document */
void 
initialize_document(document_t *doc, unsigned int seed)
{
    int i;
    list_t *words;
    char *word;

    sprintf(doc->path, "document_%d.txt", seed);
    doc->terms = set_create(compare_strings);

    for( i = 0; i < NUM_ITEMS; i++) 
    {
        word = generate_string(&seed);
		
        if(set_contains(doc->terms, word))
            free(word);
        else
            set_add(doc->terms, word);
    }
}

/* Releases the memory used */
void 
doc_destroy(document_t *doc)
{	
    set_iter_t *iter;
	
    iter = set_createiter(doc->terms);
    while (set_hasnext(iter))
        free (set_next(iter));
	
    set_destroyiter (iter);

    set_destroy(doc->terms);
}

/* Runs a series of queries and validates the index */
void 
validate_index(index_t *ind)
{
    int i, hitCount;
    set_t *w;
    list_t *query;
    set_iter_t *iter;
    list_t *result;
    char *errmsg, *term;
    query_result_t *res;

    query = list_create(compare_strings);

    /* Validate that all words returns the document */
    for (i = 0; i < NUM_DOCS; i++)
    {
        iter = set_createiter(docs[i].terms);

        while (set_hasnext(iter))
        {
            /* Add to query */
            term = (char *) set_next(iter);
            list_addfirst(query, term);

            /* Run the query */
            result = index_query(ind, query, &errmsg);
            if (result == NULL)
            {
                fatal_error("Query resulted in the following error: %s", errmsg);
            }

            /* Validate that the path is in the result set */
            hitCount = 0;
            while (list_size (result) > 0)
            {
                res = list_popfirst (result);
                if(strcmp (res->path, docs[i].path) == 0)
                {
                    hitCount++;
                }
                free (res);
            }
            list_destroy (result);

            if (hitCount == 0)
            {
                fatal_error ("Document was not returned: term=%s path=%s", 
                             term, docs[i].path);
            }

            list_popfirst (query);
        }

        set_destroyiter (iter);
    }

    list_destroy(query);
}

int
main (int argc, char **argv)
{
    int i;
    index_t *ind;
    list_t *words;
    set_iter_t *iter;

    /* Create index */
    ind = index_create();

    /* Generate random documents */
    for (i = 0; i < NUM_DOCS; i++)
    {
        initialize_document(&docs[i], i);
		
        words = list_create(compare_strings);
        iter = set_createiter(docs[i].terms);
        while (set_hasnext(iter))
        {
            list_addfirst(words, strdup((char *)set_next(iter)));
        }
        set_destroyiter(iter);
	
        index_addpath(ind, strdup(docs[i].path), words);
		
        list_destroy(words);
    }

    printf("Running a series of single term queries to validate the index...\n");
    validate_index(ind);
    printf("Success!\n");

    index_destroy(ind);

    /* Cleanup */
    for (i = 0; i < NUM_DOCS; i++)
    {
        doc_destroy(&docs[i]);
    }
}
