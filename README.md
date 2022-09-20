# Formal Verification of Concurrent Maps in Iris: the Lazy JellyFish Skip List

Artifact containing mechanized proofs of the lazy JellyFish skip list. We also present proofs for simpler data structures which showcase how our arguments evolve from a simple linked list to a complex skip list. To compile this Coq development, simply run ```make```.


## Prerequisites
This development is known to compile with

- Coq 8.16.0
- A development version of Iris


## Directory Structure
This development contains proofs for 4 data structures. The lib/ directory contains definitions and lemmas required for all structures. The four structures can be found in:

- lazy_list/: Proofs for an append-only lazy list.
- skip_list/:
  + lists/: Proofs for an append-only skip list based on linked lists.
  + arrays/: Proofs for an append-only skip list based on arrays.
- jellyfish/: Proofs for the lazy JellyFish skip list.

Each of these directories is structured as:

- code.v: File with code for the data structure.
- inv/: Directory with files for invariant definitions.
- spec/: Directory with files for proofs of Hoare triples for the structure's methods.
- client.v: File with proofs for an example client.
