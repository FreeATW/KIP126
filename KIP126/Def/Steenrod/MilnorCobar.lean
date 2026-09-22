import KIP126.Def.Steenrod.MilnorCobar.Proofs

/-!
# Normalized Milnor cobar construction

Public entry point. Each layer separates data, predicates, and proofs:

* `Polynomial/{Data,Predicates,Proofs}` contains raw polynomial operations,
  normalized-cochain membership, and preservation theorems.
* `MilnorCobar/{Data,Predicates,Proofs}` restricts those operations to
  cochains, defines the cocycle predicate, and states the cocycle theorems.

The second data layer uses the first layer's preservation proofs. All five
unfinished properties are in `Proofs` modules; no extra hypothesis is added.
The existing declaration names and concrete formulas are preserved.
-/
