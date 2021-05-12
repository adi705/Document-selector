## Author: Steffen Viken Valvaag <steffenv@cs.uit.no> 
LIST_SRC=linkedlist.c
MAP_SRC=hashmap.c
SET_SRC=aatreeset.c
INDEX_SRC=index.c

INDEXER_SRC=indexer.c common.c httpd.c $(LIST_SRC) $(MAP_SRC) $(SET_SRC) $(INDEX_SRC)
ASSERT_SRC=assert_index.c common.c $(LIST_SRC) $(MAP_SRC) $(SET_SRC) $(INDEX_SRC)

HEADERS=common.h httpd.h list.h set.h map.h index.h

all: indexer assert_index

indexer: $(INDEXER_SRC) $(HEADERS) Makefile
	gcc -Wall -o $@ -D_GNU_SOURCE -D_REENTRANT $(INDEXER_SRC) -g -lpthread -lm

assert_index: $(ASSERT_SRC) $(HEADERS) Makefile
	gcc -o $@ $(ASSERT_SRC) -g -lm

clean:
	rm -f *~ *.o *.exe *.stackdump indexer assert_index
