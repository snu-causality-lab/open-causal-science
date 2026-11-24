# Project guide

Follow the workspace guide. The README describes the checked examples and their commands. The foundations guide owns the source map and planned cases.

Follow [the module and naming conventions](docs/structure.md) when adding or moving Lean declarations. Use the specific module needed for each import.

Use the pinned Lean toolchain and Lake manifest. Verify changed public modules with `lake build` and inspect the axiom dependencies of the statements reported in the README. Run substantial builds on GSDS. Keep local build products outside the repository history.

Record the source version, the source statement, the Lean declaration, and any change in assumptions for each case. Use published sources and public dependency revisions for the reader-facing package.
