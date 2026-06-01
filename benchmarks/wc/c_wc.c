// Count the number of characters, words, and lines coming from standard input.
// This is a benchmark for I/O performance.

// The logic we apply is as follows:  we read and count each character.  If the
// character is a newline, we increment the line count.  Note that this means
// that a file that doesn't end with a newline will have a line count that is one
// less than the number of lines in the file.  This is consistent with the
// behavior of the Unix wc utility.  If the character is a non-whitespace
// character and the previous character was whitespace, or if this was the first
// character in the input, we increment the word count.  This means that the word
// count is a count of the sequences of one or more non-whitespace characters.
// The // whitespace characters are space, tab, newline (or linefeed), carriage
// return, form feed, and vertical tab.

#include <stdio.h>
#include <ctype.h>

int char_count = 0;
int word_count = 0;
int line_count = 0;
int before_word = 1;

int main() {
    do {
        int ch = getchar();
        if (ch == EOF) break;
        char_count++;
        if (ch == '\n') {
            line_count++;
            before_word = 1;
        } else if (isspace(ch)) {
            before_word = 1;
        } else if (before_word) {
            word_count++;
            before_word = 0;
        }
    } while (1);

    printf("%d lines, %d words, %d characters\n", line_count, word_count, char_count);
    return (0);
}

