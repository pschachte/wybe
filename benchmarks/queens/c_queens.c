// C solution to the n queens problem

#include <stdio.h>
#include <stdlib.h>

int safe(int n, int col, int diag1, int diag2, int row, int *qs) {
    for (int r = row; r < n; r++) {
        int c = qs[r];
        if (c == col || r - c == diag1 || r + c == diag2) {
            return 0;
        }
    }
    return 1;
}

int place_queens(int n, int row, int col, int *qs) {
    if (row < 0) {
        return 1;
    } else if (col >= n) {
        return 0;
    } else if (safe(n, col, row - col, row + col, row + 1, qs)) {
        qs[row] = col;
        return place_queens(n, row - 1, 0, qs) ||
                place_queens(n, row, col + 1, qs);
    } else {
        return place_queens(n, row, col + 1, qs);
    }
}

int *queens(int n) {
    int *list = (int*) malloc(n * sizeof(int));
    if (list == NULL) {
        printf("Memory allocation failed\n");
        exit(1);
    }
    if (place_queens(n, n-1, 0, list)) {
        return list;
    } else {
        free(list);
        return NULL;
    }
}

void show_queens(int *qs, int n) {
    for (int r = 0; r < n; r++) {
        for (int c = 0; c < n; c++) {
            printf("%c", (qs[r] == c) ? 'Q' : '.');
        }
        printf("\n");
    }
}

int main() {
    int n = 32;
    int *qs = queens(n);
    if (qs != NULL) {
        show_queens(qs, n);
        free(qs);
    } else {
        printf("No solution to %d queens problem.\n", n);
    }
    return 0;
}
