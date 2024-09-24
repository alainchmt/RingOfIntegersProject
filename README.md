# Certifying rings of integers in number fields
This repository contains the source code for the paper "Certifying rings of integers in number fields". 

Number fields and their rings of integers, which generalize the rational numbers and the integers, are foundational objects in number theory. 
There are several computer algebra systems and databases concerned with the computational aspects of these.
In particular, computing the ring of integers of a given number field is one of the main tasks of computational algebraic number theory. 
In this paper, we describe a formalization in Lean 4 for certifying such computations. 
In order to accomplish this, we developed several data types amenable to computation.
Moreover, many other underlying mathematical concepts and results had to be formalized, most of which are also of independent interest.
These include resultants and discriminants, as well as methods for proving irreducibility of univariate polynomials over finite fields and over the rational numbers.

To illustrate the feasibility of our strategy, we formally verified entries from the *Number fields* section of the *L-functions and modular forms database* (LMFDB).
These concern, for several number fields, the explicitly given *integral basis* of the ring of integers and the *discriminant*.
To accomplish this, we wrote SageMath code that computes the corresponding certificates and outputs a Lean proof of the statement to be verified. 

## Examples in Lean
- `DedekindProject4/ExamplesIrreducible`: Examples of irreducibility proofs for polynomials over the integers. 
- `DedekindProject4/Degree3Examples`: Verification of an integral basis for the ring of integers and discriminant of the non-monogenic degree 3 number fields in the LMFDB, unramified outside the primes 2,3 and 5.
- `DedekindProject4/Degree5Examples`: Verification of an integral basis for the ring of integers of the non-monogenic degree 5 number fields in the LMFDB, unramified outside the primes 2,3 and 5.
- `DedekindProject4/Degree6Examples`: Verification of an integral basis for the ring of integers of a degree 6 number field.  
- `DedekindProject4/Degree8Example`: Verification of an integral basis for the ring of integers of a degree 8 number field.

## SageMath Files 
- `IrreducibilityLeanProofWriter.sage`: The function `LeanProofIrreducible` writes a Lean proof of irreducibility
for a given irreducible polynomial with integer coefficients using either degree analysis (by looking at its factorizations modulo distinct primes), a prime
witness certificate, or a combination of both.
- `RingOfIntegersLeanProofWriter.sage`: Given a monic irreducible polynomial with integer coefficients and an integral basis for the ring of integers of the corresponding number field K,
the function `LeanProof` writes a Lean proof that the subring defined by this basis equals the ring of integers of K.

 
