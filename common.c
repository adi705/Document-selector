/* 
 * Authors: 
 * Steffen Viken Valvaag <steffenv@cs.uit.no> 
 * Magnus Stenhaug <magnus.stenhaug@uit.no> 
 * Erlend Helland Graff <erlend.h.graff@uit.no> 
 */

#include "common.h"
#include "list.h"

#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include <dirent.h>
#include <stdarg.h>
#include <string.h>
#include <assert.h>
#include <unistd.h>
#include <sys/stat.h>
#include <ctype.h>


void fatal_error(char *msg, ...)
{
    fprintf (stderr, "fatal error: ");
    va_list args;
    va_start (args, msg);
    vfprintf (stderr, msg, args);
    va_end (args);
    fputc ('\n', stderr);
    exit (1);
}

void tokenize_file (const char *filename, list_t *list)
{
    FILE *fp;
    char *c, *word;
    char buf[101];

    fp = fopen (filename, "r");
    if (!fp)
    {
        perror ("fopen");
        fatal_error ("fopen() failed");
        return;
    }

    buf[100] = 0;

    while (!feof (fp))
    {
        /* Skip non-letters */
        fscanf (fp, "%*[^a-zA-Z0-9]");

        /* Scan up to 100 letters */
        if (fscanf (fp, "%100[a-zA-Z0-9]", buf) != 1)
            break;

        /* Convert to lowercase */
        for (c = buf; *c; c++)
            *c = tolower(*c);

        word = strdup (buf);
        if (!word)
            fatal_error ("out of memory");

        list_addlast (list, word);
    }

    fclose (fp);
}

char * concatenate_strings (int num_strings, const char *first, ...)
{
    int i, len;
    const char *str;
    char *ret;
    va_list args;

    /* Number of strings must be larger or equal to 1 */
    assert (num_strings >= 1);

    len = strlen (first);

    va_start (args, first);
    for (i = 1; i < num_strings; i++)
    {
        str = va_arg (args, const char *);
        len += strlen (str);
    }
    va_end (args);

    ret = malloc (len + 1);
    if (!ret)
        return NULL;

    /* Start by copying first string */
    strcpy (ret, first);

    /* Loop through the rest of the strings, concatinating them to the end */
    va_start (args, first);
    for (i = 1; i < num_strings; i++)
    {
        str = va_arg (args, const char *);
        strcat (ret, str);
    }
    va_end (args);

    return ret;
}


static int dir_filter (const struct dirent *entry)
{
    char *filename;
    struct stat statbuf;

    filename = (char *) entry->d_name;

    if (stat (filename, &statbuf) < 0)
        fatal_error("Unable to stat '%s'\n", filename);

    /* Exclude entries that are not directories */
    if ((entry->d_type != DT_DIR) && !S_ISDIR (statbuf.st_mode))
        return 0;

    /* Exclude current and parent directory */
    return (strcmp (filename, ".") && strcmp (filename, ".."));
}

static int file_filter (const struct dirent *entry)
{
    struct stat statbuf;

    if (stat (entry->d_name, &statbuf) < 0)
        fatal_error("Unable to stat '%s'\n", entry->d_name);

    /* Exclude entries that are not regular files */
    return ((entry->d_type == DT_REG) || S_ISREG (statbuf.st_mode));
}

static void _find_files (list_t *list, const char *dirname)
{
    char *path;
    int i, num_files, num_dirs;
    struct dirent **dirlist, **filelist;

    /* Scan directory 'dirname' for files and directories.
     * File entries are placed in the arrary 'filelist', and
     * directory entries are placed in the arrary 'dirlist'.
     *
     * Note: both arrays are allocated by scandir, and must be
     * destroyed afterwards.
     */
    num_dirs = scandir (dirname, &dirlist, dir_filter, alphasort);
    num_files = scandir (dirname, &filelist, file_filter, alphasort);

    /* Loop through file entries and add them to the list */
    for (i = 0; i < num_files; i++)
    {
        path = concatenate_strings (3, dirname + 1, "/", filelist[i]->d_name);
        list_addlast (list, path);

        free (filelist[i]);
    }

    free (filelist);

    /* Loop through directories, and add all contained files recursively. */
    for (i = 0; i < num_dirs; i++)
    {
        path = concatenate_strings (3, dirname, "/", dirlist[i]->d_name);
        _find_files (list, path);

        free (dirlist[i]);
    }

    free (dirlist);
}

struct list * find_files (const char *root_dir)
{
    char cwd[512];
    list_t *files = NULL;

    /* Get path to current directory, and change it */
    if (getcwd(cwd, 512) == NULL)
        fatal_error("Unable to determine current working directory\n");
    chdir (root_dir);

    files = list_create ((cmpfunc_t) strcmp);
    if (!files)
        goto end;

    _find_files (files, ".");

end:
    /* Restore current directory */
    chdir (cwd);
    return files;
}

int compare_strings(void *a, void *b)
{
    return strcmp(a, b);
}

unsigned long hash_string(void *str)
{
    unsigned char *p = str;
    unsigned long hash = 5381;
    int c;

    while ((c = *p++) != 0)
        hash = ((hash << 5) + hash) + c; /* hash * 33 + c */
    return hash;
}

int compare_pointers(void *a, void *b)
{
    if (a < b)
        return -1;
    if (a > b)
        return 1;
    return 0;	
}

int is_valid_directory (const char *dirpath)
{
    struct stat s;

    /* Try to get access to 'dirpath' */
    if (access (dirpath, F_OK) < 0)
    {
        fprintf (stderr, "Error: could not open directory '%s'.\n", dirpath);
        return 0;
    }

    /* Try to get information about 'dirpath' */
    if (stat (dirpath, &s) < 0)
    {
        fprintf (stderr, "Error: could not stat directory '%s'.\n", dirpath);
        return 0;
    }

    /* Check if 'dirpath' is a directory */
    if (!S_ISDIR (s.st_mode))
    {
        fprintf (stderr, "Error: '%s' is not a directory.\n", dirpath);
        return 0;
    }

    return 1;
}

int is_valid_file (const char *filepath)
{
    struct stat s;

    /* Try to get access to 'filepath' */
    if (access (filepath, F_OK) < 0)
        return 0;

    /* Try to get information about 'filepath' */
    if (stat (filepath, &s) < 0)
        return 0;

    /* Check if 'filepath' is a regular file */
    if (!S_ISREG (s.st_mode))
    {
        fprintf (stderr, "Error: '%s' is not a regular file.\n", filepath);
        return 0;
    }

    return 1;
}
