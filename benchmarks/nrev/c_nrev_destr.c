// imperative destructive naive reverse in C

#include <stdio.h>
#include <gc.h>
#include <stdlib.h>

// List node structure
typedef struct Node {
    void *data;
    struct Node* next;
} Node;

// Create a new node
Node* cons(void *data, Node* next) {
    Node* new_node = (Node*)GC_MALLOC(sizeof(Node));
    if (new_node == NULL) {
        fprintf(stderr, "Memory allocation failed\n");
        exit(1);
    }
    new_node->data = data;
    new_node->next = next;
    return new_node;
}

// Destructively append ys to the end of xs.  Returns the modified xs.
Node* append(Node* xs, Node* ys) {
    if (xs == NULL) {
        return ys;
    } else {
        Node* ptr = xs;
        while (ptr->next != NULL) {
            ptr = ptr->next;
        }
        ptr->next = ys;
        return xs;        
    }
}

// Naive reverse function
Node* nrev(Node* xs) {
    if (xs == NULL) {
        return NULL;
    } else {
        return append(nrev(xs->next), cons(xs->data, NULL));
    }
}

// Calculate the length of the list
int len(Node* xs) {
    int length = 0;
    for (Node *ptr = xs; ptr != NULL; ptr = ptr->next) {
        length++;
    }
    return length;
}

// Create a list of ints from low to high, building it back to front.
Node* from_to(int lo, int hi) {
    Node* ptr = NULL;
    for (int i = hi-1; i >= lo; i--) {
        ptr = cons((void*)(intptr_t)i, ptr);
    }
    return ptr;
}


int main() {
    Node* biglist = from_to(0, 100000);
    Node* rev_list = nrev(biglist);
    int rev_size = len(rev_list);
    printf("Reversed list size = %d\n", rev_size);
    return 0;
}


// // For testing: print the list
// void print_list(Node* xs) {
//     Node* current = xs;
//     printf("[");
//     if (current != NULL) {
//         printf("%d", (int)(intptr_t)current->data);
//         current = current->next;
//         while (current != NULL) {
//             printf(",%d", (int)(intptr_t)current->data);
//             current = current->next;
//         }
//     }
//     printf("]\n");
// }

// // Main for testing:  print a small list, its reverse, and its length
// int main() {
//     Node* biglist = from_to(0, 9);
//     print_list(biglist);
//     Node* rev_list = nrev(biglist);
//     print_list(rev_list);
//     printf("Length of reversed list: %d\n", len(rev_list));
//     return 0;
// }
