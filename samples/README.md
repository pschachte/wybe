# Some small example Wybe programs.

## brainfuck.wybe

A [Brainfuck](https://esolangs.org/wiki/Brainfuck) parser and interpreter.

## json.wybe

A JSON document parser.

## quine.wybe

A [Quine](https://en.wikipedia.org/wiki/Quine_(computing)). 

To validate:
```sh
$ wybemk quine 
$ ./quine | diff ./quine.wybe -
$ echo $?
0
```
