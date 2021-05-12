/* Author: Steffen Viken Valvaag <steffenv@cs.uit.no> */
#ifndef HTTPD_H
#define HTTPD_H

#include "map.h"

#include <stdio.h>

/*
 * The type of HTTP request handler functions.
 */
typedef int (*http_handler_t)(char *path, map_t *header, map_t *args, FILE *f);

/*
 * Starts a HTTP server on the given port, passing incoming
 * GET and POST requests to the given request handler.
 * 
 * Returns a status code similar to that of a main() function.
 */
int http_server(unsigned short port, http_handler_t handler);

/*
 * Sends a HTTP OK header on the given connection (file),
 * setting the Content-Type field to the given value.
 */
void http_ok(FILE *f, const char *content_type);

/*
 * Sends a HTTP Not Found header on the given connection (file),
 * indicating that the given path was not found.
 */
void http_notfound(FILE *f, char *path);

/*
 * Returns a string where the characters < > & and " have been replaced with
 * the html escape sequences &lt; &gt; &amp; and &quot;.
 */
char *html_escape(char *s);

#endif
