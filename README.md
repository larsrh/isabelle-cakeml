# isabelle-cakeml
Exporting CakeML to Isabelle with Lem

## Purpose

This repository contains Lem specifications of the CakeML semantics that have been exported to Isabelle.
The `thy/generated/CakeML` folder roughly corresponds to the `semantics` folder in the [CakeML repository](https://github.com/CakeML/cakeml).
Additionally, there are some hand-written theory files that adapt the exported code to Isabelle, e.g. termination proofs and session specifications.

## Instructions

Most of the files in this repository are generated automatically by the `bootstrap` script.
It reads configuration from the `config` file that specifies which repository versions of Lem and CakeML to fetch.

After the specification has been exported, it builds the theories with `isabelle build`.

## Contributors

The export script and hand-written source files have been written by Lars Hupel.

Lem is a project by Peter Sewell et.al.
Contributors can be found on [its project page](https://www.cl.cam.ac.uk/~pes20/lem/) and on [GitHub](https://github.com/rems-project/lem/graphs/contributors).

CakeML is a project with many developers and contributors that can be found on [its project page](https://cakeml.org/) and on [GitHub](https://github.com/CakeML/cakeml/graphs/contributors).

In particular, Fabian Immler and Johannes Åman Pohjola have contributed Isabelle mappings for constants in the Lem specification of the CakeML semantics.
