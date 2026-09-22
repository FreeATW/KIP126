import KIP126.Def.ClassicalAdams.TowerSequence.NextCycles.Proofs
import KIP126.Def.Steenrod.MilnorCobar.Proofs
import KIP126.Def.StableHomotopy.Cohomology.Multiplication.Proofs
import Lean.Elab.Command

/-!
# Axiom regression for the completed Adams construction lemmas

Audit declarations individually: the normalized cobar differential and page
passage still have open dependencies. In particular this does not certify
`mod2SphereAdams`, the transported `h6` classes, or the final theorem.
-/

open Lean Elab Command in
run_cmd do
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``KIP126.StableHomotopy.lesHomotopyExactH,
      ``KIP126.Classical.Adams.adamsTowerMapAt_comp,
      ``KIP126.Classical.Adams.adamsBoundaries_le_cycles,
      ``KIP126.Classical.Adams.adamsCycles_succ_le,
      ``KIP126.Classical.Adams.adamsDifferentialValue_eq_of_lift,
      ``KIP126.Classical.Adams.adamsDifferentialValue_add,
      ``KIP126.Classical.Adams.adamsDifferentialValue_smul,
      ``KIP126.Classical.Adams.adamsBoundaries_le_differential_ker,
      ``KIP126.Classical.Adams.adamsPageD_comp,
      ``KIP126.Classical.Adams.adamsNextCycle_d_zero,
      ``KIP126.Classical.Adams.adamsCycle_of_lift,
      ``KIP126.Steenrod.Milnor.cupPolynomial_mem,
      ``KIP126.Steenrod.Milnor.cup_add_left,
      ``KIP126.Steenrod.Milnor.cup_add_right,
      ``KIP126.Steenrod.Milnor.cup_smul_left,
      ``KIP126.Steenrod.Milnor.cup_smul_right,
      ``KIP126.Steenrod.Milnor.h6Polynomial_mem,
      ``KIP126.Steenrod.Milnor.h6Polynomial_differential,
      ``KIP126.Steenrod.Milnor.h6SquarePolynomial_differential,
      ``KIP126.StableHomotopy.Cohomology.adamsUnit_mul,
      ``KIP126.StableHomotopy.Cohomology.cooperationDiagonal_counit_right] do
    let axioms ← liftCoreM (collectAxioms name)
    let forbidden := axioms.filter fun axiomName => !allowed.contains axiomName
    unless forbidden.isEmpty do
      throwError "{name} depends on forbidden axioms: {forbidden}"
