# malloc

DESIGN DESCRIPTION

This malloc program uses segregated explicit free lists to manage memory allocation. 
Free blocks are stored in an array of free lists based on their size, and each block 
has a header, footer, and a structure of pointers. When a user requests to allocate 
or free memory, the program searches the appropriate free list(s) and coalesces 
neighboring free blocks if necessary. The program also rounds up the requested size 
and adds extra bytes for the header and footer. The checkheap function performs various
checks on the heap and each block to ensure correctness, including checking alignment,
header and footer consistency, and free block coalescing.


