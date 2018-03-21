# isabelle-cakeml

Exporting CakeML to Isabelle with Lem

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.1204863.svg)](https://doi.org/10.5281/zenodo.1204863)
[![AFP](https://img.shields.io/badge/AFP-CakeML-yellow.svg)](https://devel.isa-afp.org/entries/CakeML.html)

## Purpose

CakeML is a functional programming language with a proven-correct compiler and runtime system.

This repository contains an unofficial version of the CakeML semantics that has been exported from the Lem specifications to Isabelle.
The `thy/generated/CakeML` folder roughly corresponds to the `semantics` folder in the [CakeML repository](https://github.com/CakeML/cakeml).

Additionally, there are some hand-written theory files that adapt the exported code to Isabelle and port proofs from the HOL4 formalization, e.g. termination and equivalence proofs.

## Instructions

Most of the files in this repository are generated automatically by the `bootstrap` script.
It reads configuration from the `versions` file that specifies which repository versions of Lem and CakeML to fetch.

After the specification has been exported, it builds the theories with `isabelle build`.

The `thy` folder corresponds to the contents of the AFP entry.
Both are kept in sync manually.

## Contributors

The export script and hand-written source files have been written by Lars Hupel.

Lem is a project by Peter Sewell et.al.
Contributors can be found on [its project page](https://www.cl.cam.ac.uk/~pes20/lem/) and on [GitHub](https://github.com/rems-project/lem/graphs/contributors).

CakeML is a project with many developers and contributors that can be found on [its project page](https://cakeml.org/) and on [GitHub](https://github.com/CakeML/cakeml/graphs/contributors).

In particular, Fabian Immler and Johannes Åman Pohjola have contributed Isabelle mappings for constants in the Lem specification of the CakeML semantics.
