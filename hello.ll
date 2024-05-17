; target datalayout = "e-m:o-i64:64-i128:128-n32:64-S128"
target triple = "arm64-apple-macosx14.0.0"

; Declare the string constant as a global constant.
@.1 = private unnamed_addr constant [17 x i8] c"hello from LLVM!\00"

; External declaration of the puts function
declare i32 @puts(ptr nocapture) nounwind

; Definition of main function
define i32 @main() {
  ; Call puts function to write out the string to stdout.
  call i32 @puts(ptr @.1)
  ret i32 0
}
