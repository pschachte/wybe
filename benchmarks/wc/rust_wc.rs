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

use std::io::{self, Read};

fn main() -> io::Result<()> {
    let mut char_count = 0;
    let mut word_count = 0;
    let mut line_count = 0;
    let mut before_word = true;

    let stdin = io::stdin();
    let mut bytes = stdin.lock().bytes();

    while let Some(Ok(ch)) = bytes.next() {
        char_count += 1;

        if ch == b'\n' {
            line_count += 1;
            before_word = true;
        } else if ch.is_ascii_whitespace() {
            before_word = true;
        } else if before_word {
            word_count += 1;
            before_word = false;
        }
    }

    println!("{} lines, {} words, {} characters", line_count, word_count, char_count);
    Ok(())
}