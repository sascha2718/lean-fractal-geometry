/-
Axiom check for `FractalGeometry`. Every endpoint below must report
`propext`, `Classical.choice`, `Quot.sound`, or a subset of these. Any additional
axiom indicates an unintended dependency.

The groups follow the module order of the library root.
-/
import FractalGeometry.Regularity
import FractalGeometry.System
import FractalGeometry.Hutchinson
import FractalGeometry.AhlforsRegular
import FractalGeometry.Homometric
import FractalGeometry.HomometricMeasures
import FractalGeometry.All
import Lean

-- Frostman and Ahlfors regular measures, and the two ball conventions for each
#print axioms FractalGeometry.IsFrostman
#print axioms FractalGeometry.IsFrostmanOpen
#print axioms FractalGeometry.IsAhlfors
#print axioms FractalGeometry.IsAhlforsClosed
#print axioms FractalGeometry.IsFrostman.isFrostmanOpen
#print axioms FractalGeometry.IsFrostmanOpen.isFrostman
#print axioms FractalGeometry.IsAhlforsClosed.isAhlfors
#print axioms FractalGeometry.IsFrostman.measure_singleton

-- the pair-distance distribution
#print axioms FractalGeometry.Phi
#print axioms FractalGeometry.pairLaw
#print axioms FractalGeometry.phi_mono
#print axioms FractalGeometry.phi_prod_eq
#print axioms FractalGeometry.phi_eq_pairLaw
#print axioms FractalGeometry.phi_le
#print axioms FractalGeometry.pairLaw_measure_singleton
#print axioms FractalGeometry.continuous_phi

-- self-similar systems, their attractors and their natural measures
#print axioms FractalGeometry.System
#print axioms FractalGeometry.System.IsAttractor
#print axioms FractalGeometry.System.StronglySeparated
#print axioms FractalGeometry.System.IsDimension
#print axioms FractalGeometry.System.IsNatural
#print axioms FractalGeometry.System.IsNatural.isProbabilityMeasure
#print axioms FractalGeometry.System.IsNatural.support_Icc
#print axioms FractalGeometry.System.logRatio_pos

-- the law of the log-ratios
#print axioms FractalGeometry.System.isProbabilityMeasure_renewalLaw
#print axioms FractalGeometry.System.integral_id_renewalLaw
#print axioms FractalGeometry.System.renewalMean_pos

-- the three worked systems
#print axioms FractalGeometry.cantorSystem_isDimension
#print axioms FractalGeometry.cantorSystem_stronglySeparated
#print axioms FractalGeometry.homogeneousSystem_isDimension
#print axioms FractalGeometry.homogeneousSystem_stronglySeparated
#print axioms FractalGeometry.pairSystem_isDimension
#print axioms FractalGeometry.pairSystem_stronglySeparated
#print axioms FractalGeometry.pairSystem_nonArithmetic_iff

-- Hutchinson's theorem: the coding map, the attractor, and the natural measure
#print axioms FractalGeometry.Hutchinson.code
#print axioms FractalGeometry.Hutchinson.code_cons
#print axioms FractalGeometry.Hutchinson.attractorSet_eq_iUnion
#print axioms FractalGeometry.Hutchinson.eq_attractorSet
#print axioms FractalGeometry.Hutchinson.naturalMeasure_selfSimilar
#print axioms FractalGeometry.Hutchinson.eq_of_selfSimilar
#print axioms FractalGeometry.System.exists_unique_isNatural
#print axioms FractalGeometry.exists_unique_isNatural_cantorSystem
#print axioms FractalGeometry.exists_unique_isNatural_homogeneousSystem
#print axioms FractalGeometry.exists_unique_isNatural_pairSystem

-- Ahlfors regularity of the natural measure of a strongly separated system
#print axioms FractalGeometry.AhlforsRegular.measure_eq_sum
#print axioms FractalGeometry.AhlforsRegular.exists_unique_meet
#print axioms FractalGeometry.AhlforsRegular.measure_closedBall_step
#print axioms FractalGeometry.AhlforsRegular.exists_uniform_lower
#print axioms FractalGeometry.AhlforsRegular.measure_closedBall_le_of_isNatural
#print axioms FractalGeometry.AhlforsRegular.exists_le_measure_closedBall_of_isNatural
#print axioms FractalGeometry.exists_isAhlforsClosed
#print axioms FractalGeometry.AhlforsRegular.exists_isFrostman_of_isNatural
#print axioms FractalGeometry.exists_isAhlfors_cantor_pair

-- the homometric digit sets and the two measures they carry
#print axioms FractalGeometry.diffMultiset_eq
#print axioms FractalGeometry.diffCount_eq
#print axioms FractalGeometry.tHom_mem_Ioo
#print axioms FractalGeometry.six_mul_rpow_tHom
#print axioms FractalGeometry.conv_reflect_eq_map_sub
#print axioms FractalGeometry.HomometricMeasures.diffLaw_selfSimilar
#print axioms FractalGeometry.HomometricMeasures.diffLaw_eq
#print axioms FractalGeometry.homometric_example

-- Check every declaration originating in the consolidated modules, including
-- private helpers and declarations outside their usual namespace. Printing a
-- selection of axioms alone does not reject a newly introduced proof hole.
open Lean Elab Command in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let roots := #[`FractalGeometry, `GeometricMeasureTheory, `BranchingProcess,
    `AnalyticESC, `BrownianImages, `ExactOverlaps]
  let mut counts : Array Nat := Array.replicate roots.size 0
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let origin := env.header.moduleNames[idx]!
      for i in [:roots.size] do
        if roots[i]!.isPrefixOf origin then
          let axioms ← Lean.collectAxioms name
          for ax in axioms do
            unless allowed.contains ax do
              throwError "Forbidden axiom {ax} in {name} (module {origin})"
          counts := counts.modify i (· + 1)
  for i in [:roots.size] do
    if counts[i]! == 0 then
      throwError "Empty axiom audit for {roots[i]!}"
    logInfo m!"{roots[i]!}: checked {counts[i]!} declarations; standard axioms only."
