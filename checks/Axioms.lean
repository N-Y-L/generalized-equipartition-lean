import Equipartition
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
# Audit the trusted dependencies of the public results

Run `lake build` before `lake env lean checks/Axioms.lean`.

The project audit selects declarations by their originating module, including private
declarations and declarations outside the `Equipartition` namespace. It traverses their
types and proofs recursively, including imported dependencies, and rejects unsafe
project declarations. The named checks below also print the public results' dependencies.
The audit fails if any closure contains anything beyond Lean's standard propositional
extensionality, classical choice, and quotient soundness principles.
The accompanying source scan is supplementary; this dependency check is authoritative.
-/

open Lean Elab Command

/-- Audit all declarations originating in the project library, regardless of namespace. -/
elab "audit_project_axioms" : command => do
  let env ← getEnv
  let declarations := env.constants.fold (init := #[]) fun declarations name info =>
    match env.getModuleIdxFor? name with
    | some index =>
        if (`Equipartition).isPrefixOf env.header.moduleNames[index.toNat]! then
          declarations.push (name, info)
        else declarations
    | none => declarations
  if declarations.isEmpty then
    throwError "No declarations from the Equipartition project modules were found"
  for (name, info) in declarations do
    if info.isUnsafe then
      throwError "Unsafe project declaration: {name}"
  -- Sharing the visited set avoids retraversing mathlib for every declaration.
  let collect : Lean.CollectAxioms.M Unit :=
    declarations.forM fun (name, _) => Lean.CollectAxioms.collect name
  let (_, state) := (collect.run env).run {}
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := state.axioms.filter fun name => !allowed.contains name
  unless unexpected.isEmpty do
    throwError "Untrusted dependencies in project declarations: {unexpected.toList}"
  logInfo m!"Audited all {declarations.size} declarations from the Equipartition project modules"

/-- Check the transitive dependency closure, then print it using Lean's standard command. -/
elab "audit_axioms " decl:ident : command => do
  let name ← liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo decl
  let actual ← Lean.collectAxioms name
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := actual.filter fun name => !allowed.contains name
  unless unexpected.isEmpty do
    throwError "Untrusted dependencies in {name}: {unexpected.toList}"
  elabCommand (← `(#print axioms $decl))

audit_project_axioms

audit_axioms Equipartition.boltzmannWeight_pos
audit_axioms Equipartition.partitionFunction_pos
audit_axioms Equipartition.canonicalExpectation_one
audit_axioms Equipartition.canonicalExpectation_const_mul
audit_axioms Equipartition.canonicalExpectation_congr
audit_axioms Equipartition.quadratic_weight_integrable
audit_axioms Equipartition.quadratic_weighted_coordinate_integrable
audit_axioms Equipartition.quadratic_weighted_square_integrable
audit_axioms Equipartition.quadratic_partitionFunction
audit_axioms Equipartition.quadratic_equipartition
audit_axioms Equipartition.gibbsMeasure_isProbabilityMeasure
audit_axioms Equipartition.integral_gibbsMeasure
audit_axioms Equipartition.hasDerivAt_observable_boltzmann
audit_axioms Equipartition.canonical_identity_with_boundary
audit_axioms Equipartition.canonical_identity_of_tendsto_zero
audit_axioms Equipartition.canonical_identity_of_integrable
audit_axioms Equipartition.canonical_coordinate_identity
audit_axioms Equipartition.canonical_interval_identity
audit_axioms Equipartition.partialDeriv_coordinate
audit_axioms Equipartition.generalized_equipartition
audit_axioms Equipartition.generalized_equipartition_temperature
audit_axioms Equipartition.generalized_equipartition_of_integrable
audit_axioms Equipartition.generalized_equipartition_gibbs
audit_axioms Equipartition.quadratic_coordinate_equipartition
audit_axioms Equipartition.hasDerivAt_insertNth
audit_axioms Equipartition.integral_eq_zero_of_slice_derivative
audit_axioms Equipartition.integral_eq_zero_of_slice_derivative_of_integrable
audit_axioms Equipartition.hasDerivAt_slice
audit_axioms Equipartition.weighted_partial_identity
audit_axioms Equipartition.weighted_partial_identity_of_integrable
audit_axioms Equipartition.canonical_partial_identity
audit_axioms Equipartition.canonical_partial_identity_of_integrable
audit_axioms Equipartition.measurableSet_coordinateDomain
audit_axioms Equipartition.integral_Ioo_of_hasDerivAt_of_traces
audit_axioms Equipartition.integral_coordinateDomain_derivative
audit_axioms Equipartition.weighted_coordinateDomain_identity
audit_axioms Equipartition.volume_unitIntervalDomain
audit_axioms Equipartition.uniform_interval_partitionFunction
audit_axioms Equipartition.uniform_interval_boundary_correction
audit_axioms Equipartition.canonical_coordinateDomain_identity
audit_axioms Equipartition.generalized_equipartition_coordinateDomain_boundary
audit_axioms Equipartition.integralOn_eq_zero_of_supported_slice_derivative
audit_axioms Equipartition.weighted_partial_identity_on_open
audit_axioms Equipartition.canonical_partial_identity_on_open
audit_axioms Equipartition.integrableOn_of_continuousOn_of_supported
audit_axioms Equipartition.weighted_partial_identity_on_open_of_hasCompactSupport
audit_axioms Equipartition.integrable_comp_abs_of_integrableOn_Ioi
audit_axioms Equipartition.laplace_weight_integrable
audit_axioms Equipartition.laplace_weighted_energy_integrable
audit_axioms Equipartition.laplace_weighted_coordinate_integrable
audit_axioms Equipartition.laplace_partitionFunction
audit_axioms Equipartition.laplace_equipartition
audit_axioms Equipartition.integral_derivative_off_countable
audit_axioms Equipartition.integral_derivative_off_countable_of_integrable
audit_axioms Equipartition.hasAESliceDeriv_of_differentiable
audit_axioms Equipartition.integral_eq_zero_of_ae_slice_derivative
audit_axioms Equipartition.integral_eq_zero_of_ae_slice_derivative_of_integrable
audit_axioms Equipartition.HasAESliceDeriv.observable_boltzmann
audit_axioms Equipartition.weighted_slice_identity
audit_axioms Equipartition.weighted_slice_identity_of_integrable
audit_axioms Equipartition.canonical_slice_identity
audit_axioms Equipartition.canonical_slice_identity_of_integrable
audit_axioms Equipartition.hasAESliceDeriv_coordinate
audit_axioms Equipartition.generalized_equipartition_slices
audit_axioms Equipartition.generalized_equipartition_slices_of_integrable
audit_axioms Equipartition.hasAESliceDeriv_abs_coordinate
audit_axioms Equipartition.canonical_vector_identity_slices
audit_axioms Equipartition.canonical_virial_identity
audit_axioms Equipartition.canonical_vector_identity
