# Nodcap---Races in Classical Linear Logic

This repository holds the code for Nodcap. Nodcap is a type system for the
π-calculus which was inspired by bounded linear logic, and an extension of the
type system CP by Phil Wadler. CP guarantees that any program it assigns a type
will be free of races and deadlocks. What sets Nodcap apart from CP is that it
allows non-determinism, and as such permits programs with races, but it does
this without losing its strong ties to classical linear logic or the guarantee
not to deadlock. 
