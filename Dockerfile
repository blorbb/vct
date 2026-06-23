# Builds the binary and puts it at /build/vct

FROM rocq/rocq-prover:9.1.1
RUN opam update && opam install -y dune menhir minisat

WORKDIR /build
COPY --chown=rocq:rocq theories ./theories
COPY --chown=rocq:rocq _CoqProject .
COPY --chown=rocq:rocq Makefile .

RUN opam exec -- make

WORKDIR /build
COPY --chown=rocq:rocq src ./src
WORKDIR /build/src
RUN opam exec -- dune build ./bin/main.exe --release
RUN cp _build/default/bin/main.exe /build/vct
WORKDIR /build
