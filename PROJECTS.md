# Potential programming projects for Wybe

Here are some programming and research projects that would extend or
improve the Wybe language.

## Secure package and build system

This project would provide a way for the Wybe compiler to download and
compile a module from an external source, such as github or an ftp site.
This, of course, raises significant security concerns, which this
project must also address, by providing a permission system, so that
external packages must request access to any capabilities that have
security implications, such as file system or operating system access.
