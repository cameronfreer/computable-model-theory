/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.ExtensionRichDirectLimit
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit: extension-rich direct limits

Outside the root import spine; CI checks it explicitly.

* **Independent universes**: source, stage and index universes are separate
  (`test_factor_independent_universes`).
* **Empty stages** satisfy the extension squares (`test_empty_stages`).
* **Non-inclusion transitions**: a system whose successor maps are an arbitrary automorphism still
  supports literal stage factorization (`test_automorphism_transitions`).
* **Standard axioms** for every declaration of the production module (scanned by module, whatever
  the namespace) and for the regression rows.
* **Import isolation**: the production module imports only `ExtensionRichFamily` besides `Init`, and
  its transitive closure contains no other module of this library and nothing of `InfinitaryLogic`.
* **Positive proof controls**: `isFraisseLimit_directLimit` depends on stage factorization, the AP
  conversion, `DirectLimit.cg`, and Mathlib's `isUltrahomogeneous_iff_IsExtensionPair`.
-/

universe u v w z a

open FirstOrder FirstOrder.Language

namespace FirstOrder.Language

/-- Stage factorization with independent source, stage and index universes. -/
theorem test_factor_independent_universes {L : Language.{u, v}} {ι : Type z} [Preorder ι]
    [IsDirectedOrder ι] [Nonempty ι] (G : ι → Type w) [∀ i, L.Structure (G i)]
    (f : ∀ i j, i ≤ j → G i ↪[L] G j) [DirectedSystem G (fun i j h => f i j h)]
    {A : Type a} [L.Structure A] (hA : Structure.FG L A)
    (e : A ↪[L] Language.DirectLimit G f) :
    ∃ (i : ι) (g : A ↪[L] G i), (DirectLimit.of L ι G f i).comp g = e :=
  exists_factor_directLimit G f hA e

/-- Empty stages are allowed: no point is needed to form or extend a partial map. -/
theorem test_empty_stages {L : Language} {M : Type*} [L.Structure M] [IsEmpty M] :
    AmalgamationRich (fun _ : ℕ => M) (fun _ _ _ => Embedding.refl L M) := by
  intro i j S _ e
  refine ⟨j, le_rfl, Embedding.refl L M, ?_⟩
  ext x
  exact isEmptyElim x.1

/-- Transitions may be arbitrary automorphisms, not inclusions of substructures. -/
theorem test_automorphism_transitions {L : Language} {M : Type*} [L.Structure M] (e : M ≃[L] M)
    {A : Type*} [L.Structure A] (hA : Structure.FG L A)
    (a : A ↪[L] Language.DirectLimit (fun _ : ℕ => M)
      (Language.DirectedSystem.natLERec (fun _ => e.toEmbedding))) :
    ∃ (i : ℕ) (g : A ↪[L] M),
      (DirectLimit.of L ℕ (fun _ => M)
        (Language.DirectedSystem.natLERec (fun _ => e.toEmbedding)) i).comp g = a :=
  exists_factor_directLimit _ _ hA a

end FirstOrder.Language

open Lean in
/-- The constants a declaration depends on, transitively. -/
private partial def usedConstants (env : Environment) (todo : List Name)
    (seen : NameSet := {}) : NameSet :=
  match todo with
  | [] => seen
  | n :: rest =>
    if seen.contains n then usedConstants env rest seen
    else match env.find? n with
      | none => usedConstants env rest (seen.insert n)
      | some ci => usedConstants env (ci.getUsedConstantsAsSet.toList ++ rest) (seen.insert n)

-- Standard axioms for every declaration of the production module; its import boundary; and the
-- positive proof controls.
open Lean in
run_cmd do
  let env ← getEnv
  let target := `ComputableModelTheory.ModelTheory.ExtensionRichDirectLimit
  let family := `ComputableModelTheory.ModelTheory.ExtensionRichFamily
  let some idx := env.getModuleIdx? target | throwError "{target} is not imported"
  let mut count := 0
  for (n, _) in env.constants.toList do
    if env.getModuleIdxFor? n == some idx then
      count := count + 1
      for ax in ← collectAxioms n do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
          throwError "{n} uses nonstandard axiom {ax}"
  if count == 0 then throwError "no declarations found in {target}"
  let direct := (env.header.moduleData[idx.toNat]!).imports.map (·.module)
  unless direct.filter (· != `Init) == #[family] do
    throwError "unexpected direct imports of {target}: {direct}"
  let mut seen : NameSet := {}
  let mut todo : Array Name := direct
  while h : todo.size > 0 do
    let m := todo.back
    todo := todo.pop
    if seen.contains m then continue
    seen := seen.insert m
    if ((`ComputableModelTheory).isPrefixOf m && m != family) ||
        (`InfinitaryLogic).isPrefixOf m then
      throwError "{target} transitively imports {m}"
    if let some j := env.getModuleIdx? m then
      todo := todo ++ (env.header.moduleData[j.toNat]!).imports.map (·.module)
  let used := usedConstants env [`FirstOrder.Language.isFraisseLimit_directLimit]
  for n in [`FirstOrder.Language.exists_factor_directLimit,
      `FirstOrder.Language.amalgamationRich_of_sequenceExtension,
      `FirstOrder.Language.DirectLimit.cg,
      `FirstOrder.Language.isUltrahomogeneous_iff_IsExtensionPair] do
    unless used.contains n do throwError "the limit criterion bypasses {n}"

#assert_standard_axioms FirstOrder.Language.test_factor_independent_universes
#assert_standard_axioms FirstOrder.Language.test_empty_stages
#assert_standard_axioms FirstOrder.Language.test_automorphism_transitions
