// recursive, non-imperative naive reverse in C

#include <stdio.h>
#include <gc.h>
#include <stdlib.h>

// List node structure
typedef struct Node {
    void *data;
    struct Node* next;
} Node;

// Function to create a new node
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

// Function to append two lists
Node* append(Node* xs, Node* ys) {
    if (xs == NULL) {
        return ys;
    } else {
        return cons(xs->data, append(xs->next, ys));
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

// Function to calculate the length of the list
int len(Node* xs) {
    if (xs == NULL) {
        return 0;
    } else {
        return 1 + len(xs->next);
    }
}

// Function to create a list from low to high
Node* from_to(int lo, int hi) {
    if (lo >= hi) {
        return NULL;
    } else {
        return cons((void*)(intptr_t)lo, from_to(lo + 1, hi));
    }
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

// int main() {
//     Node* biglist = from_to(0, 10);
//     print_list(biglist);
//     Node* rev_list = nrev(biglist);
//     print_list(rev_list);
//     printf("Length of reversed list: %d\n", len(rev_list));
//     return 0;
// }
