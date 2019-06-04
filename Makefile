
CC	= gcc
CCOPT	= -Og -g -m64 -DLINUX 

SOURCE = produce_lock_info.c

EXEC_CFLAGS	= $(CCOPT)  -DSHUT_UP=1 -L. -
SOURCE_OBJECTS  = produce_lock_info.o

SOURCE_FILES = produce_lock_info.c
	
PROGS = produce_lock_info


all:	$(PROGS)

clean:
	rm -f $(SOURCE_OBJECTS) produce_lock_info

splint:
	splint -nullpass -nullassign $(SOURCE_FILES) -warnposix

produce_lock_info.o: produce_lock_info.c
	$(CC) $(CCOPT) -c produce_lock_info.c

carb_create: $(SOURCE_OBJECTS)
	$(CC) $(CCOPT)  $(SOURCE_OBJECTS) -o produce_lock_info
