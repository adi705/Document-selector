/* 
 * Authors: 
 * Steffen Viken Valvaag <steffenv@cs.uit.no> 
 * Magnus Stenhaug <magnus.stenhaug@uit.no> 
 * Erlend Helland Graff <erlend.h.graff@uit.no> 
 */

#include "index.h"
#include "httpd.h"

#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <pthread.h>
#include <ctype.h>

#define PORT_NUM 8080

static pthread_mutex_t query_lock = PTHREAD_MUTEX_INITIALIZER;

static char *root_dir;
static index_t *idx;

static void print_title (FILE *, char *);
static void print_querystring (FILE *, char *);
static void run_query (FILE *, char *);

struct tag_mapping
{
    const char *tag;
    void (*render) (FILE *fp, char *query);
};

const struct tag_mapping
tag_mappings[] =
{
    { "title",   print_title },
    { "query",   print_querystring },
    { "results", run_query }
};

#define NUM_TAGS (sizeof (tag_mappings) / sizeof (struct tag_mapping))

struct mime_entry
{
    const char *file_type;
    const char *mime_type;
};

const struct mime_entry
mime_table[] =
{
    { "html",  "text/html" },
    { "htm",   "text/html" },
    { "xml",   "application/xml" },
    { "xhtml", "application/xhtml+xml" },
    { "css",   "text/css" },
    { "txt",   "text/plain" },
    { "js",    "application/x-javascript" },
    { "gif",   "image/gif" },
    { "jpg",   "image/jpeg" },
    { "png",   "image/png" },
    { "ico",   "image/x-icon" }
};

#define NUM_MIME_TYPES (sizeof (mime_table) / sizeof (struct mime_entry))

/* Check for terminating word */
static int is_reserved_word(char *word)
{
    if(strcmp(word, "ANDNOT") == 0)
        return 1;
    else if(strcmp(word, "AND") == 0)
        return 1;
    else if(strcmp(word, "OR") == 0)
        return 1;
    else if(strcmp(word, "(") == 0)
        return 1;
    else if(strcmp(word, ")") == 0)
        return 1;
    else
        return 0;
}

/* Check for terminating char */
static int is_reserved_char(char a)
{
    if(isspace(a))
        return 1;

    switch (a)
    {
    case '(':
        return 1;
    case ')':
        return 1;
    default:
        return 0;
    }
}

static char *substring(char *start, char *end)
{
    char *s = malloc(end-start+1);
    if (s == NULL)
    {
        fatal_error("out of memory");
        goto end;
    }

    strncpy(s, start, end-start);
    s[end-start] = 0;

end:
    return s;
}

/* Splits the query into a list of tokens */
static list_t *tokenize_query(char *query)
{
    char *term;
    list_t *processed;
	
    processed = list_create(compare_strings);

    while(*query != '\0')
    {
        if(isspace(*query)) 
        {
            /* Ignore whitespace */
            query++;
            continue;
        }
        else if(*query == '(') 
        {
            list_addlast(processed, strdup("("));
            query++;
        }
        else if(*query == ')') 
        {
            list_addlast(processed, strdup(")"));
            query++;
        }
        else
        {
            char *s;
            /* Get length of term*/
            for(s=query;!is_reserved_char(*s) && *s != '\0'; s++);
            /* Copy term */
            term = substring(query, s);
            query = s;
            /* add to list */
            list_addlast(processed, term);
        }
    }

    return processed;
}

/* 
 * Processes and tokenizes the query. Would normally include
 * stemming and stopword removal
 */ 
static list_t *preprocess_query(char *query)
{
    char *word, *c, *prev;
    list_t *tokens;
    list_t *processed;
    list_iter_t *iter;

    /* Create tokens */
    tokens = tokenize_query(query);
    processed = list_create(compare_strings);
    prev = NULL;

    iter = list_createiter(tokens);
    while(list_hasnext(iter)) 
    {
        word = list_next(iter);

        /* Is a word */
        if(!is_reserved_word(word))	
        {

            /* Convert to lowercase */
            for (c = word; *c; c++)
                *c = tolower(*c);

            /* Adjacent words */
            if(prev != NULL && !is_reserved_word(prev))
                list_addlast(processed, strdup("OR"));
        }
        /* Add to processed tokens */
        list_addlast(processed, word);
        prev = word;
    }

    list_destroyiter(iter);
    list_destroy(tokens);

    return processed;
}

static void send_results(FILE *f, char *query, list_t *results)
{
    char *tmp;
    list_iter_t *it;
  
    tmp = html_escape(query);
  
    fprintf(f, "<hr/><h3>Your query for \"%s\" returned %d result(s)</h3>\n",
            tmp, list_size (results));
    free (tmp);
  
    fprintf(f, "<ol id=\"results\">\n");
    it = list_createiter (results);
    while (list_hasnext (it))
    {
        query_result_t *res = list_next (it);
        tmp = html_escape (res->path + 1);
        fprintf(f, "<li><span class=\"score\">[%.2lf]</span> <a href=\"/indexed_files/%s\">%s</a></li>\n",
                res->score, tmp, tmp);

        /* Free memory */
        free (tmp);
        free (res);
    }
    list_destroyiter (it);

    fprintf(f, "</ol>\n");
}

static void run_query(FILE *f, char *query)
{
    char *errmsg;
    list_t *result;
    list_t *tokens = NULL;
    list_iter_t *iter;

    tokens = preprocess_query(query);
	
    /* Don't run query if query is empty */
    if (!list_size (tokens))
        goto end;

    result = index_query(idx, tokens, &errmsg);
    if(result != NULL){
        send_results(f, query, result);
        list_destroy(result);
    }
    else {
        fprintf(f, "<hr/><h3>Error</h3>\n");
        fprintf(f, "<p>Your query for \"%s\" caused the following error(s): <b>%s</b></p>\n",
                query, errmsg);
    }

    /* Cleanup */
    iter = list_createiter(tokens);
    while(list_hasnext(iter))
        free(list_next(iter));
	
    list_destroyiter(iter);
	
end:
    if (tokens)
        list_destroy(tokens);
}

static void print_querystring (FILE *fp, char *query)
{
    char *q_esc = html_escape (query);
    fprintf (fp, "%s", q_esc);
    free (q_esc);
}

static void print_title (FILE *fp, char *query)
{
    char *title;

    title = "Simple Search Engine";
    fprintf (fp, title);
}

static void parse_html_template (FILE *in, FILE *out, char *query)
{
    char *tok, *c, *line = NULL;
    size_t len = 0;
    int i, read, found, num_tokens;

    num_tokens = NUM_TAGS;

    while ((read = (int) getline (&line, &len, in)) != -1)
    {    
        if ((tok = strstr (line, "<#=")))
        {
            *tok = 0;
            fprintf (out, line);
            *tok = '<';

            tok += 3;

            c = strchr (tok, '>');
            if (c)
            {
                *c++ = 0;

                found = 0;
                for (i = 0; i < num_tokens; i++)
                {
                    if (strcmp (tok, tag_mappings[i].tag) != 0)
                        continue;

                    tag_mappings[i].render (out, query);
                    found = 1;

                    break;
                }

                if (!found)
                {
                    *(c-1) = '>';
                    c = tok - 3; 
                }
            }
            else
            {
                c = tok - 3; 
            }

            fprintf (out, c);
        }
        else
        {
            fprintf (out, line);
        }
    }

    if (line)
        free(line);
}

static void handle_query(FILE *f, char *query)
{
    http_ok(f, "text/html");

    FILE *tpl = fopen("template.html", "r");
    parse_html_template (tpl, f, query);
    fclose (tpl);
}

static const char *get_mime_type (const char *path)
{
    int i;
    const char *type = "text/plain";
    char *ext = NULL;

    ext = strrchr(path, '.');
    if (!ext)
        goto end;

    ext++;

    for (i = 0; i < NUM_MIME_TYPES; i++)
    {
        if (strcmp (ext, mime_table[i].file_type) != 0)
            continue;

        type = mime_table[i].mime_type;
        break;
    }

end:
    return type;
}

static void handle_page(FILE *f, char *path, char *query)
{
    int in_root = 0;
    const char *idx_prefix = "indexed_files";
    char *fullpath;
    FILE *pagef;

    /* If path starts with "/indexed_files", the request is for a file in the search
     * directory (root_dir), else, the request is for a file in the same directory
     * as the indexer application.
     */
    if (strncmp (path, idx_prefix, strlen (idx_prefix)) == 0)
    {
        in_root = 0;
        fullpath = concatenate_strings (2, root_dir, path + strlen (idx_prefix));
    }
    else
    {
        in_root = 1;
        fullpath = strdup (path);
    }

    if (!is_valid_file (fullpath))
    {
        http_notfound(f, path);
        return;
    }

    pagef = fopen(fullpath, "r");
    if (pagef == NULL)
    {
        http_notfound(f, path);
    }
    else
    {
        char buf[1024];
        size_t n;

        /* Consider MIME-type if serving a file in the same directory
         * as the indexer application.
         */
        if (in_root)
            http_ok (f, get_mime_type (fullpath));
        else
            http_ok (f, "text/plain");

        while (!feof(pagef))
        {
            n = fread(buf, 1, sizeof(buf), pagef);
            fwrite(buf, 1, n, f);            
        }
        fclose(pagef);
    }
	
    free (fullpath);
}

static int http_handler(char *path, map_t *header, map_t *args, FILE *f)
{
    char *query = "";

    if (map_haskey(args, "query"))
    {
        query = map_get(args, "query");
    }

    if (strcmp(path, "/") == 0)
    {
        /* Serialize query processing */
        pthread_mutex_lock (&query_lock);
        handle_query (f, query);
        pthread_mutex_unlock (&query_lock);
    }
    else if(path[0] == '/')
    {
        handle_page(f, path+1, query);
    }

    return 0;
}

int main(int argc, char **argv)
{
    int status;
    char *relpath, *fullpath;
    list_t *files, *words;
    list_iter_t *iter;

    if (argc != 2)
    {
        fprintf (stderr, "Usage: %s <root-dir>\n", argv[0]);
        return 1;
    }

    root_dir = argv[1];

    /* Check that root_dir exists and is directory */
    if (!is_valid_directory (root_dir))
        return 1;

    files = find_files (root_dir);
    idx = index_create ();

    iter = list_createiter (files);

    while (list_hasnext (iter))
    {
        relpath = (char *) list_next (iter);
        fullpath = concatenate_strings (2, root_dir, relpath);
        printf ("Indexing %s\n", fullpath);

        words = list_create ((cmpfunc_t) strcmp);
        tokenize_file (fullpath, words);
        index_addpath (idx, relpath, words);

        free (fullpath);

        list_destroy (words);
    }

    list_destroyiter (iter);
    list_destroy (files);

    printf ("Serving queries on port %d\n",(int) PORT_NUM);

    status = http_server ((int) PORT_NUM, http_handler);

    index_destroy (idx);

    return status;
}
