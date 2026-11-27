# Richardson (2003), Markov properties for acyclic directed mixed graphs

<!-- topic: Graphical Markov models -->

[Paper index](../paper-checks.md)

Thomas S. Richardson, *Markov Properties for Acyclic Directed Mixed Graphs*,
Scandinavian Journal of Statistics 30, 145–157. The statement numbering below
follows §3 of the author's University of Washington technical report 353.
[Journal article](https://doi.org/10.1111/1467-9469.00323) ·
[Author's technical report](https://stat.uw.edu/sites/default/files/files/reports/1999/tr353.pdf)

## Lean results

[OrderedLocal.lean](../../OpenCausalScience/Papers/Richardson2003/OrderedLocal.lean)
uses the existing m-separation and collider-augmentation theorems. For a vertex
with no child in an ancestral set, its blanket is its district with the vertex
removed, together with the parents of that district.

- `collider_augmented_iff_markovBlanket` proves the augmented-neighbor
  characterization in Lemma 4. `markovBlanket_clique` proves the blanket
  vertices are mutually adjacent in the augmentation.
- `markovBlanket_separates` proves the separation of the vertex from the
  remainder of the ancestral set given the blanket.
- `orderedLocal_of_globalMarkov` proves the global-to-ordered-local implication
  of Theorem 2. It works with an abstract independence relation, even when a
  directed and a bidirected edge share a pair of endpoints. The given rank must
  increase strictly along every directed edge.

The ordered-local-to-global implication under the semigraphoid axioms remains
open in this formalization.

Source checked against technical report 353, PDF SHA-256
`f82baf82692a0bb0bfb71f3e25963545ef623140f11d8715ccaae89abf795422`.
