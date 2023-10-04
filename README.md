# Atomic Postconditions: Resourceful Reasoning beyond Linearization Points
## Formal Verification of the Lazy JellyFish Skip List in Iris

Artifact which extends the atomic triples from Iris with atomic postconditions, containing mechanized proofs for our elaborate case study: the Lazy JellyFish skip list, a concurrent map implementation. We also present the proofs for a simpler lazy set data structure to showcase how our arguments evolve from a simple linked list to a complex skip list. To compile this Coq development, simply run `make`.


### Prerequisites
This development is known to compile with

- Coq 8.18.0
- A development version of Iris


### Directory Structure
The `lib/` directory contains definitions and lemmas required for both structures.

- `argmax.v`: Definition of and facts about the `argmax` resource algebra.
- `gmap.v`: Additional facts about the `gmap` resource algebra.
- `zrange.v`: Definition of and facts about sets containing a range of integers.

The `atomic/` directory contains an alternative definition of logical atomicity in Iris.

- `update.v`: Definition of and facts about atomic updates. We extend the previous definition by defining atomic postconditions.
- `weakestpre.v`: Definition of and facts about atomic triples based on the new definition of atomic updates. These triples also support private postconditions.
- `proofmode.v`: Ensures that the `awp_apply` tactic refers to the new definition for atomic triples.
- `lock.v`: Alternative logically atomic specification for locks without the use of an invariant.

The `lazy_list/` and `jelly_fish/` directories contain the proofs for the lazy set and JellyFish map, respectively. Each of these directories is structured as:

- `code.v`: File with code for the data structure.
- `inv.v`: File describing the invariant resources.
- `spec/`: Directory with the proofs of atomic triples for the data structure's logically atomic specification.
- `rw_client/`: Directory with a client specification built from the logically atomic specification. This specification supports read-read and write-write concurrency, as shown by verifying a simple client example.
