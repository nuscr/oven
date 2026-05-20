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

## API Generation

- [baguette](https://github.com/nuscr/baguette): API generation for Rust using 0MQ as transport.

## License

GPL-3.0-or-later. Authors: Francisco Ferreira, Sung-Shik Jongmans.
