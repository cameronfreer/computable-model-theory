/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.BackForthIso

/-!
# CHMM Corollary 3.5 — computable automorphisms extending a prescribed isomorphism

> **Corollary 3.5.** If `F` is computably homogeneous, then every isomorphism between finitely
> generated substructures of `F` extends to a computable automorphism of `F`.

"Essentially by the same proof" as Proposition 3.2: the seeded back-and-forth with `S = T = F`,
started from the prescribed match instead of the empty state.

## Three layers

* **The tuple-extension package** (`extendToAutomorphism`). A matched seed `s₀` — a pair of tuples
  whose assignment extends to an isomorphism of the substructures they generate — yields a
  computable automorphism carrying every seed coordinate to its prescribed image
  (`extendToAutomorphism_extends`). It takes a self-representation isomorphism `r` of `F`'s
  canonical age **at the map oracle `E`, as data**, and assumes no inclusion between `O` and `E`.
* **The explicit-substructure corollary** (`exists_automorphism_extending`). For finitely generated
  `A, B ≤ F` and an isomorphism `e : A ≃[L] B`, there is a computable automorphism `α` with
  `α x = e x` for **every** `x ∈ A`. Two obligations: a seed — generators of `A` paired with their
  images, matched because `e` itself realizes them (`matched_seed`) — and generation: agreement on
  the generators propagates to all of `A`, because both maps commute with term realization.
  Generator selection is classical; no computability of `e` is assumed, and no uniform effective
  extraction of generators from an abstract substructure is claimed. The finite tuple is the
  computational input; the semantic bridge only supplies it.
* **The paper-facing form** (`corollary_3_5`), at `E = O`, with `r` discharged by the identity
  representation (`RepresentationIsoIn.refl`), and its oracle-relative form under an explicit
  `O ⊆ E` (`exists_automorphism_extending_of_le`). **That constructor** requires the inclusion — its
  maps are domain-restricted identities whose computability is lifted from `O`. This does not show
  that inclusion is mathematically necessary for automorphism extension, and nothing here claims so.
-/

open Encodable FirstOrder Language Structure

namespace FirstOrder.Language

variable {O : Set (ℕ →. ℕ)} {L : Language}

/-! ### Extending a substructure isomorphism by the identity -/

section Extend

variable {M : Type*} [L.Structure M] {A B : L.Substructure M}

open Classical in
/-- `e`, read as a function on the ambient carrier: `e` on `A`, the identity off `A`. Only its
values on `A` are ever used. -/
noncomputable def equivExtend (e : A ≃[L] B) (x : M) : M :=
  if h : x ∈ A then (e ⟨x, h⟩ : M) else x

theorem equivExtend_of_mem (e : A ≃[L] B) {x : M} (h : x ∈ A) :
    equivExtend e x = (e ⟨x, h⟩ : M) := by
  simp [equivExtend, h]

/-- **`equivExtend e` commutes with term realization on `A`.** Realize the term inside `A`, apply
`e` there (an `L`-equivalence preserves terms), and read the result in `M`. -/
theorem equivExtend_realize (e : A ≃[L] B) {α : Type*} (T : L.Term α) (u : α → M)
    (hu : ∀ i, u i ∈ A) : equivExtend e (T.realize u) = T.realize (equivExtend e ∘ u) := by
  let uA : α → A := fun i ↦ ⟨u i, hu i⟩
  have hA : ((T.realize uA : A) : M) = T.realize u :=
    (HomClass.realize_term (g := A.subtype) (t := T) (v := uA)).symm
  have hmem : T.realize u ∈ A := hA ▸ (T.realize uA).2
  have he : e ⟨T.realize u, hmem⟩ = T.realize (e ∘ uA) := by
    rw [show (⟨T.realize u, hmem⟩ : A) = T.realize uA from Subtype.ext hA.symm]
    exact (HomClass.realize_term (g := e)).symm
  rw [equivExtend_of_mem e hmem, he]
  refine (HomClass.realize_term (g := B.subtype) (t := T) (v := e ∘ uA)).symm.trans ?_
  congr 1
  funext i
  exact (equivExtend_of_mem e (hu i)).symm

/-- **`equivExtend e` is injective on `A`.** -/
theorem equivExtend_injOn (e : A ≃[L] B) {x y : M} (hx : x ∈ A) (hy : y ∈ A)
    (h : equivExtend e x = equivExtend e y) : x = y := by
  rw [equivExtend_of_mem e hx, equivExtend_of_mem e hy] at h
  exact congrArg Subtype.val (e.injective (Subtype.ext h))

/-- **`equivExtend e` preserves and reflects relations on `A`.** -/
theorem equivExtend_relMap (e : A ≃[L] B) {n : ℕ} (R : L.Relations n) (u : Fin n → M)
    (hu : ∀ i, u i ∈ A) : RelMap R (equivExtend e ∘ u) ↔ RelMap R u := by
  let uA : Fin n → A := fun i ↦ ⟨u i, hu i⟩
  have h := e.map_rel R uA
  have hl : (equivExtend e ∘ u) = fun i ↦ ((e (uA i) : B) : M) :=
    funext fun i ↦ equivExtend_of_mem e (hu i)
  rw [hl]
  exact h

end Extend

variable [L.EffectiveLanguage]

/-! ### Computable isomorphisms commute with terms -/

/-- A computable isomorphism of structures commutes with term realization — the propagation step
from generators to everything they generate. -/
theorem ComputableStructureIsoIn.toFun_realize {E : Set (ℕ →. ℕ)} {S T : ComputableStructureIn O L}
    (α : ComputableStructureIsoIn E S T) {β : Type*} (t : L.Term β) (v : β → ℕ) :
    α.toFun (@Term.realize L ℕ S.inst β v t) = @Term.realize L ℕ T.inst β (α.toFun ∘ v) t := by
  induction t with
  | var _ => rfl
  | func f ts ih =>
    change α.toFun (@Structure.funMap L ℕ S.inst _ f fun i ↦ @Term.realize L ℕ S.inst β v (ts i))
      = @Structure.funMap L ℕ T.inst _ f fun i ↦ @Term.realize L ℕ T.inst β (α.toFun ∘ v) (ts i)
    rw [α.toFun_funMap]
    exact congrArg _ (funext ih)

section Automorphism

variable {E : Set (ℕ →. ℕ)} {F : ComputableStructureIn O L}

/-! ### The tuple-extension package -/

/-- **A computable automorphism extending a matched seed.** The seeded back-and-forth with
`S = T = F`; the seed determines the computation and `h₀` justifies its laws. The
self-representation `r` is data at `E`; nothing relates `O` and `E`. -/
noncomputable def extendToAutomorphism (r : RepresentationIsoIn E F.canonicalAge F.canonicalAge)
    (H : ComputablyHomogeneousIn E F) (s₀ : BackForthState) (h₀ : s₀.Matched F F) :
    ComputableStructureIsoIn E F F :=
  backForthIsoFrom r H H s₀ h₀

/-- **The prescribed match is extended**: every seed coordinate, repeated ones included, goes to its
prescribed image. -/
theorem extendToAutomorphism_extends (r : RepresentationIsoIn E F.canonicalAge F.canonicalAge)
    (H : ComputablyHomogeneousIn E F) {s₀ : BackForthState} (h₀ : s₀.Matched F F) {i x : ℕ}
    (hx : s₀.sourceTuple[i]? = some x) :
    s₀.targetTuple[i]? = some ((extendToAutomorphism r H s₀ h₀).toFun x) :=
  backForthIsoFrom_extends r H H h₀ hx

/-! ### The seed of a substructure isomorphism -/

/-- A member of `F`'s canonical age is the closure of its tuple. -/
theorem mem_canonicalAge_domainAt_encode_iff (t : Tuple ℕ) {x : ℕ} :
    x ∈ F.canonicalAge.domainAt (encode t) ↔ x ∈ @Tuple.closure ℕ L F.inst t := by
  let : L.Structure ℕ := F.inst
  rw [F.canonicalAge_domainAt_eq_closure, allTupleFor_encode, Tuple.closure_eq]
  rfl

/-- **The seed of a substructure isomorphism is matched.** Pair a tuple `a` drawn from `A` with its
image under `e`; `e` itself, restricted to the closure of `a`, realizes the pair. -/
theorem matched_seed :
    letI : L.Structure ℕ := F.inst
    ∀ {A B : L.Substructure ℕ} (e : A ≃[L] B) (a : Tuple ℕ), (∀ x ∈ a, x ∈ A) →
      (⟨a, a.map (equivExtend e)⟩ : BackForthState).Matched F F := by
  let : L.Structure ℕ := F.inst
  intro A B e a ha
  -- the closure of `a` lies in `A`
  have hcl : ∀ x, x ∈ F.canonicalAge.domainAt (encode a) → x ∈ A := by
    intro x hx
    rw [mem_canonicalAge_domainAt_encode_iff] at hx
    exact (Substructure.closure_le.2 fun y hy ↦ ha y hy) hx
  -- `equivExtend e` carries the closure of `a` into the closure of its image tuple
  have himg : ∀ x, x ∈ F.canonicalAge.domainAt (encode a) →
      equivExtend e x ∈ F.canonicalAge.domainAt (encode (a.map (equivExtend e))) := by
    intro x hx
    rw [mem_canonicalAge_domainAt_encode_iff] at hx ⊢
    obtain ⟨T, rfl⟩ := (Tuple.mem_closure_iff_exists_term a).1 hx
    rw [equivExtend_realize e T a.view fun i ↦ ha _ (List.get_mem a i)]
    refine (Tuple.mem_closure_iff_exists_term _).2
      ⟨T.relabel (Fin.cast (List.length_map _).symm), ?_⟩
    rw [Term.realize_relabel]
    congr 1
    funext i
    simp [Tuple.view]
  let f : (F.canonicalAge.memberAt (encode a)).domain ↪[L]
      (F.canonicalAge.memberAt (encode (a.map (equivExtend e)))).domain :=
    { toFun := fun x ↦ ⟨equivExtend e x, himg x x.2⟩
      inj' := fun x y h ↦ Subtype.ext (equivExtend_injOn e (hcl x x.2) (hcl y y.2)
        (congrArg Subtype.val h))
      map_fun' := fun {n} g v ↦ by
        refine Subtype.ext ?_
        change equivExtend e (Structure.funMap g fun k ↦ (v k : ℕ))
          = Structure.funMap g fun k ↦ equivExtend e (v k : ℕ)
        have h := equivExtend_realize e (Term.func g fun k ↦ Term.var k) (fun k ↦ (v k : ℕ))
          fun k ↦ hcl _ (v k).2
        simpa [Term.realize] using h
      map_rel' := fun {n} R v ↦
        equivExtend_relMap e R (fun k ↦ (v k : ℕ)) fun k ↦ hcl _ (v k).2 }
  refine ⟨f, ?_⟩
  refine PartialAgeIn.realizes_of_getElem? (by simp) fun k x hx ↦ ?_
  have hx' : a[k]? = some (x : ℕ) := by simpa using hx
  simp [hx']
  rfl

/-! ### The explicit-substructure corollary -/

/-- **CHMM Corollary 3.5, at the map oracle.** For finitely generated `A ≤ F`, any isomorphism
`e : A ≃[L] B` onto a substructure `B` extends to a computable automorphism of `F`: `α x = e x` for
every `x ∈ A`. The self-representation `r` is data at `E`; no inclusion between `O` and `E`, and no
computability of `e`, is assumed. -/
theorem exists_automorphism_extending (r : RepresentationIsoIn E F.canonicalAge F.canonicalAge)
    (H : ComputablyHomogeneousIn E F) :
    letI : L.Structure ℕ := F.inst
    ∀ {A B : L.Substructure ℕ}, A.FG → ∀ e : A ≃[L] B,
      ∃ α : ComputableStructureIsoIn E F F, ∀ x : A, α.toFun x = (e x : ℕ) := by
  let : L.Structure ℕ := F.inst
  intro A B hA e
  classical
  obtain ⟨s, hs⟩ := hA
  let a : Tuple ℕ := s.toList
  have ha : ∀ x ∈ a, x ∈ A := fun x hx ↦
    hs ▸ Substructure.subset_closure (Finset.mem_toList.1 hx)
  let α := extendToAutomorphism r H _ (matched_seed (F := F) e a ha)
  refine ⟨α, fun x ↦ ?_⟩
  -- agreement on the generators
  have hgen : ∀ k : Fin a.length, α.toFun (a.view k) = equivExtend e (a.view k) := by
    intro k
    have h := extendToAutomorphism_extends r H (matched_seed (F := F) e a ha)
      (i := k) (x := a.view k) (by simp [Tuple.view])
    simp only [List.getElem?_map, Tuple.view_eq_get, List.get_eq_getElem,
      List.getElem?_eq_getElem k.2, Option.map_some] at h
    exact (Option.some.inj h).symm
  -- generation: `A` is the closure of `a`, and both maps commute with terms
  have hxA : (x : ℕ) ∈ Tuple.closure L a := by
    rw [Tuple.closure, show {y | y ∈ a} = (s : Set ℕ) from Set.ext fun y ↦ Finset.mem_toList, hs]
    exact x.2
  obtain ⟨T, hT⟩ := (Tuple.mem_closure_iff_exists_term a).1 hxA
  rw [← equivExtend_of_mem e x.2, ← hT, ComputableStructureIsoIn.toFun_realize,
    equivExtend_realize e T a.view fun i ↦ ha _ (List.get_mem a i)]
  exact congrArg (fun w : Fin a.length → ℕ ↦ T.realize w) (funext hgen)

/-- **Under an explicit `O ⊆ E`**, the self-representation is the identity. -/
theorem exists_automorphism_extending_of_le (hOE : O ⊆ E) (H : ComputablyHomogeneousIn E F) :
    letI : L.Structure ℕ := F.inst
    ∀ {A B : L.Substructure ℕ}, A.FG → ∀ e : A ≃[L] B,
      ∃ α : ComputableStructureIsoIn E F F, ∀ x : A, α.toFun x = (e x : ℕ) :=
  exists_automorphism_extending (RepresentationIsoIn.refl F.canonicalAge hOE) H

end Automorphism

/-- **CHMM Corollary 3.5.** If `F` is computably homogeneous, then every isomorphism between
finitely generated substructures of `F` extends to a computable automorphism of `F`. -/
theorem corollary_3_5 {F : ComputableStructureIn O L} (H : ComputablyHomogeneousIn O F) :
    letI : L.Structure ℕ := F.inst
    ∀ {A B : L.Substructure ℕ}, A.FG → ∀ e : A ≃[L] B,
      ∃ α : ComputableStructureIsoIn O F F, ∀ x : A, α.toFun x = (e x : ℕ) :=
  exists_automorphism_extending_of_le subset_rfl H

end FirstOrder.Language
