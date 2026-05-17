# OvenMPST

A tool to manipulate and validate Multiparty Session Type (MPST) protocols with flexible interleavings and mixed choice.

## Installation

```
opam install ovenMPST
```

Or build from source:

```
dune build
```

## Usage

```
dune exec bin/main.exe -- <protocol.oven>
```

Protocol examples are in the `examples/` directory.

## Web IDE

```
cd web && yarn && make
```

## License

GPL-3.0-or-later. Authors: Francisco Ferreira, Sung-Shik Jongmans.
