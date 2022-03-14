FROM ubuntu:18.04

RUN apt-get update && \
    apt-get install -y clang libgc-dev llvm-9-dev libtinfo-dev dwdiff make wget

RUN mkdir -p /projects/wybe

RUN wget -qO- https://get.haskellstack.org/ | sh
