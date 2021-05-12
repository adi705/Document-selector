/* 
 * Authors: 
 * Steffen Viken Valvaag <steffenv@cs.uit.no> 
 * Magnus Stenhaug <magnus.stenhaug@uit.no> 
 * Erlend Helland Graff <erlend.h.graff@uit.no> 
 */

#include "httpd.h"
#include "list.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <ctype.h>
#include <errno.h>
#include <signal.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <fcntl.h>
#include <pthread.h>

#define MAX_THREADS 50

static int server_is_running = 1;

struct http_conn
{
    int sock;
    http_handler_t handler;
};

static char *newstring(int length)
{
    char *r = calloc(length+1, 1);

    if (r == NULL)
        fatal_error("out of memory");

    return r;
}

static char *stripstring(char *s, int len)
{
    char *r;
    char *end = s+len-1;

    while (end >= s && isspace((int) *end))
        end--;

    while (s <= end && isspace((int) *s))
        s++;

    r = newstring(end-s+1);
    strncpy(r, s, end-s+1);
    return r;
}

static int splitstring(char *s, int sep, char **left, char **right)
{
    char *p;

    p = strchr(s, sep);
    if (p == NULL)
        return 0;

    *left = stripstring(s, p-s);
    *right = stripstring(p+1, strlen(p+1));
    return 1;    
}

static int hexdigit(char ch)
{
    if (ch >= '0' && ch <= '9')
        return ch-'0';
    if (ch >= 'A' && ch <= 'F')
        return ch-'A'+10;
    if (ch >= 'a' && ch <= 'f')
        return ch-'a'+10;

    fatal_error("bad hex digit");
    return -1;
}

static char *urldecode(char *s)
{
    char *r, *p;

    r = p = newstring(strlen(s));
    for (;;) {    
        int ch = *s++;        
        switch(ch) {
        case 0:
            return r;
        case '+':
            *p++ = ' ';
            break;
        case '%':
            *p = hexdigit(*s++) * 16;
            *p += hexdigit(*s++);
            *p++;
            break;
        default:
            *p++ = ch;
            break;
        }
    }
}

char *html_escape(char *s)
{
    char *r, *p;

    r = p = newstring(strlen(s)*6);
    for (;;) {
        int ch = *s++;
        switch(ch) {
        case 0:
            return r;
        case '<':
            strcat(p, "&lt;");
            p += 4;
            break;
        case '>':
            strcat(p, "&gt;");
            p += 4;
            break;
        case '&':
            strcat(p, "&amp;");
            p += 5;
            break;
        case '"':
            strcat(p, "&quot;");
            p += 6;
            break;
        default:
            *p++ = ch;
            break;
        }        
    }
}

void http_ok(FILE *f, const char *content_type)
{
    fprintf(f, "HTTP/1.0 200 OK\r\nContent-Type: %s\r\n\r\n", content_type);
}

void http_notfound(FILE *f, char *path)
{
    fprintf(f, "HTTP/1.0 404 Not Found\r\nContent-Type: text/html\r\n\r\n");
    fprintf(f, "<html><head><title>404 Not Found</title></head>");
    fprintf(f, "<body><p>The requested path <b>%s</b> was not found.</p></body></html>", path);
}

typedef
enum http_methods
{
    HTTP_GET,
    HTTP_POST
} http_method_t;

struct http_header
{
    http_method_t method;
    char *path;
    map_t *header_fields;
    map_t *query_fields;
};

static int http_parse_query (char *query, map_t *fields)
{
    char *buf, *p, *tmp, *key, *value;

    buf = query;

    while (buf)
    {
        if ((p = strchr (buf, '&')))
            *p = 0;
        else
            p = NULL;

        if (splitstring (buf, '=', &key, &value))
        {
            tmp = key;
            key = urldecode (tmp);
            free (tmp);
			
            tmp = value;
            value = urldecode (tmp);
            free (tmp);
			
            map_put (fields, key, value);
        }
        else
        {
            key = newstring (strlen (buf));
            strcpy (key, buf);
            value = "";
            map_put (fields, key, value);
        }

        if (p)
            *p++ = '&';

        buf = p;
    }

    return 0;
}

static void http_destroy_header (struct http_header *hdr)
{
    if (hdr->path)
    {
        free (hdr->path);
        hdr->path = NULL;
    }

    if (hdr->header_fields)
    {
        map_destroy (hdr->header_fields, free, free);
        hdr->header_fields = NULL;
    }

    if (hdr->header_fields)
    {
        map_destroy (hdr->query_fields, free, free);
        hdr->header_fields = NULL;
    }
}

static int http_parse_request_line (FILE *fp, struct http_header *hdr)
{
    int fd;
    char *method = NULL, *path = NULL, *line = NULL;
    struct timeval tv = { .tv_sec = 3, .tv_usec = 0 };
    fd_set rdfds;

    fd = fileno (fp);

    FD_ZERO(&rdfds);
    FD_SET(fd, &rdfds);

    if (select (fd + 1, &rdfds, NULL, NULL, &tv) <= 0)
        goto error;

    method = newstring(300);
    if (!method)
        goto error;

    path = newstring(300);
    if (!path)
        goto error;

    line = newstring(300);
    if (!line)
        goto error;

    /* Read and parse the request line */
    if (fscanf(fp, "%300s %300s %*s", method, path) != 2)
    {
        fprintf (stderr, "Failed to read request line!\n");
        goto error;
    }

    /* Read the remainder of the request line */
    fgets (line, 300, fp);
    free (line);
    line = NULL;

    if (strcmp(method, "GET") == 0)
        hdr->method = HTTP_GET;
    else if (strcmp(method, "POST") == 0)
        hdr->method = HTTP_POST;
    else
    {
        fprintf (stderr, "Got unknown HTTP method!\n");
        goto error;
    }

    free (method);
    method = NULL;

    hdr->path = path;

    return 0;

error:
    if (method)
        free (method);

    if (path)
        free (path);

    if (line)
        free (line);

    return -1;
}

static int http_parse_request_headers (FILE *fp, map_t *fields)
{
    char *name, *value, *line;

    line = newstring (300);
    if (!line)
        return -1;

    /* Read and parse the header fields */
    while (!feof (fp))
    {
        fgets(line, 300, fp);
        if (strcmp(line, "\r\n") == 0 || strcmp(line, "\n") == 0)
        {
            /* End of the HTTP header */
            break;
        }

        /* Parse the name and value of the header field */
        if (splitstring (line, ':', &name, &value))
            map_put (fields, name, value);
    }

    free (line);

    return 0;
}

static int http_parse_request (FILE *fp, struct http_header *hdr)
{
    int len;
    char *query;

    hdr->path = NULL;
    hdr->header_fields = NULL;
    hdr->query_fields = NULL;

    if (http_parse_request_line (fp, hdr))
        goto error;

    hdr->header_fields = map_create (compare_strings, hash_string);
    if (!hdr->header_fields)
        goto error;

    if (http_parse_request_headers (fp, hdr->header_fields))
        goto error;

    hdr->query_fields = map_create (compare_strings, hash_string);
    if (!hdr->query_fields)
        goto error;

    if (hdr->method == HTTP_POST)
    {
        if (!map_haskey (hdr->header_fields, "Content-Length"))
        {
            fprintf (stderr, "No Content-Length in POST request\n");
            goto error;
        }

        len = atoi (map_get (hdr->header_fields, "Content-Length"));
        query = newstring (len + 1);
        fread (query, 1, len, fp);

        http_parse_query (query, hdr->query_fields);
        free (query);
    }

    return 0;

error:
    http_destroy_header (hdr);

    return -1;
}

/*
 * Open file descriptor as reading and writing streams.
 * Note: do not use file descriptor directly afterwards.
 * File descriptor is closed if streams could not be opened.
 */
static int http_open_file_streams (int fd, FILE **inf, FILE **outf)
{
    int wd;
    FILE *in, *out;

    *inf = NULL;
    *outf = NULL;

    if (!(in = fdopen (fd, "r")))
    {
        perror("fdopen");
        close (fd);
        return -1;
    }

    if ((wd = dup (fd)) < 0)
    {
        perror("dup");
        fclose (in);
        return -1;
    }

    out = fdopen (wd, "w");
    if (!out)
    {
        perror("fdopen");
        close (wd);
        fclose (in);
        return -1;
    }

    *inf = in;
    *outf = out;
    return 0;
}

static void *handle_request(void *arg)
{
    int s, status;
    FILE *inf, *outf;
    char *path;
    struct http_header hdr;
    struct http_conn *conn;
    http_handler_t handler;

    /* Get arguments passed to thread */
    conn = (struct http_conn *) arg;
    s = conn->sock;
    handler = conn->handler;
    free (conn);

    if (http_open_file_streams (s, &inf, &outf))
    {
        fprintf (stderr, "Failed to open file streams!\n");
        goto end;
    }

    if (http_parse_request (inf, &hdr))
        goto end;

    path = urldecode (hdr.path);
    free (hdr.path);

    /* Invoke the request handler to write the response */
    status = handler (path, hdr.header_fields, hdr.query_fields, outf);

    free (path);

    map_destroy (hdr.header_fields, free, free);
    map_destroy (hdr.query_fields, free, free);

end:
    fclose(inf);
    fclose(outf);

    return NULL;
}

static void handle_kill_signal (int signum)
{
    server_is_running = 0;
}

int setup_kill_signals (void)
{
    struct sigaction sa;

    memset (&sa, 0, sizeof (struct sigaction));
    sa.sa_handler = handle_kill_signal;
    sigemptyset (&sa.sa_mask);

    if (sigaction (SIGQUIT, &sa, NULL) < 0) 
    {
        perror ("sigaction");
        return -1;
    }

    if (sigaction (SIGTERM, &sa, NULL) < 0) 
    {
        perror ("sigaction");
        return -1;
    }

    if (sigaction (SIGHUP, &sa, NULL) < 0) 
    {
        perror ("sigaction");
        return -1;
    }

    if (sigaction (SIGINT, &sa, NULL) < 0) 
    {
        perror ("sigaction");
        return -1;
    }

    if (sigaction (SIGTSTP, &sa, NULL) < 0) 
    {
        perror ("sigaction");
        return -1;
    }
	
    /* Ignore SIGPIPE on sockets */
    sa.sa_handler = SIG_IGN;
    if (sigaction (SIGPIPE, &sa, NULL) < 0) 
    {
        perror ("sigaction");
        return -1;
    }

    return 0;
}

int open_socket (unsigned short port)
{
    int sock, yes;
    struct sockaddr_in sin;

    sin.sin_family = AF_INET;
    sin.sin_port = htons (port);
    sin.sin_addr.s_addr = htonl (INADDR_ANY);

    sock = socket (AF_INET, SOCK_STREAM, 0);
    if (sock < 0)
    {
        perror ("socket");
        return -1;
    }

    yes = 1;
    if (setsockopt (sock, SOL_SOCKET, SO_REUSEADDR, &yes, sizeof (int)) < 0)
    {
        perror ("setsockopt");
        return -1;
    }

    if (bind (sock, (struct sockaddr *) &sin, sizeof(sin)) < 0)
    {
        perror ("bind");
        return -1;
    }

    if (listen (sock, SOMAXCONN) < 0)
    {
        perror ("listen");
        return -1;
    }

    return sock;
}

int http_server(unsigned short port, http_handler_t handler)
{
    int sock, i, t, thidx;
    struct sockaddr_in clientaddr;
    socklen_t len;
    struct http_conn *conn;
    int started[MAX_THREADS];
    pthread_t threads[MAX_THREADS];

    setup_kill_signals ();
	
    /* Set all threads to NULL */
    memset (started, 0, sizeof(started));

    sock = open_socket (port);
    if (sock < 0)
    {
        fprintf (stderr, "Failed to open socket!\n");
        return 1;
    }

    fprintf (stdout, "Running HTTP server!\n");
	
    thidx = 0;

    /*
     * Accept TCP connections.
     */
    while (server_is_running)
    {
        len = sizeof (struct sockaddr_in);      
        t = accept (sock, (struct sockaddr *) &clientaddr, &len);

        if (t < 0)
        {
            perror("accept");
            continue;
        }

        conn = malloc (sizeof (struct http_conn));
        conn->sock = t;
        conn->handler = handler;
		
        if (started[thidx])
            (void) pthread_join (threads[thidx], NULL);
		
        started[thidx] = 1;

        /* Launch a threads to handle the connection */
        if (pthread_create (&threads[thidx], NULL, handle_request, conn))
        {
            started[thidx] = 0;
            close (t);
            free (conn);
        }
		
        thidx = (thidx + 1) % MAX_THREADS;
    }
	
    for (i = 0; i < MAX_THREADS; i++)
    {
        if (started[i])
            (void) pthread_join (threads[i], NULL);
    }

    fprintf (stdout, "Quitting HTTP server!\n");

    close (sock);

    return 0;
}
