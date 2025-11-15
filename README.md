# Resourceful Reasoning beyond Linearisation Points
## A Reinterpretation of Logical Atomicity in Iris

An alternative definition of logical atomicity where the public state is accessible _after_ the linearisation point. Using the Iris definition of atomic updates, we define _atomic invariants_: atomic updates that allow the $\alpha$ resource to be accessed after obtaining $\beta$ via a subsequent atomic update. This artifact contains mechanised proofs for a number of case studies, ranging from a simple spin lock to a complex skip list implementation for concurrent maps with version control.


### Prerequisites
This development is known to compile with

- Rocq 9.1.0
- Iris 4.4.0

To compile this Rocq development, simply run `make`.


### Directory Structure
The `lib/` directory contains useful definitions and lemmas not available in Rocq-std++ or Iris.

- `argmax.v`: Definition of the `argmax` resource algebra.
- `gmap.v`: Additional facts about the `gmap` resource algebra.
- `zrange.v`: Definition of sets containing a range of integers.

The `atomic/` directory contains our novel definition of logical atomicity.

- `invariant.v`: Definition of atomic invariants.
- `triple.v`: Definition of atomic triples based on atomic invariants.

The `examples/` directory contains proofs of correctness using our new atomic triples for concurrent data structures, including an alternative logically atomic specification for locks in `locks/` without the use of an invariant. The `lazy_list/` and `jelly_fish/` directories contain the proofs for a lazy set and a lazy JellyFish map, respectively. Each of these directories is structured as:

- `code.v`: File with code for the data structure.
- `inv.v`: File describing the invariant resources.
- `spec/`: Directory with the proofs of atomic triples for the data structure's logically atomic specification.
- `rw_client/`: Directory with a client specification built from the logically atomic specification. This specification supports read-read and write-write concurrency, as shown by verifying a simple client example.
