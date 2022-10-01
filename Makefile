all: cleanup

cleanup: cleanup.c
	gcc cleanup.c -std=c99 -O2 -o cleanup

clean:
	rm cleanup
