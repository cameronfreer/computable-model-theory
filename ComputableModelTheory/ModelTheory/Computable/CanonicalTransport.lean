/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.PotentialEmbedding
import ComputableModelTheory.ModelTheory.Computable.UniformAtomic

/-!
# Canonical transport through generated presentations

A canonical least-term representative is chosen for every value of an indexed object, and
transported along potential embedding data. `isTermCodeFor K i x c` tests that the code `c`
decodes to a term whose variables index into the generator tuple at `i` and which realizes
`x` there; `termCodeFor K i x` is the least such code, total because the generators
generate. `transportValue K G x` decodes that code and realizes it at the range tuple in
the codomain index.

The search ranges over `L.Term ℕ` — the uniform term type of `termRealize` — rather than
the fixed-width `L.Term (Fin k)` of `TermClosure`, because transport must be computable
uniformly in the index and in potential embedding data, where the generator count varies.
The variable-bound guard replaces the width bound: it keeps every referenced variable
inside the generator range, which is what makes transport agree with the realized
embedding (`transportValue_eq_toEmbedding`). The code path is internal; the public
specification is encoding-independent.
-/

open Encodable FirstOrder Language Language.BoundedFormula

namespace FirstOrder.Language

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]

namespace ComputableAgeIn

variable (K : ComputableAgeIn O L)

/-- The code `c` decodes to a term whose variables all index into the generator tuple at
`i` and which realizes `x` at the structure of index `i` under the generators. -/
def isTermCodeFor (i x c : ℕ) : Bool :=
  (@decode (L.Term ℕ) Primcodable.toEncodable c).elim false fun t ↦
    Term.varsBelowBool (K.gens i).length t &&
      decide (K.termRealize ((i, K.gens i), t) = x)

/-- Some code witnesses the guarded realization of every value: the generators generate,
so every `x` is realized by a term over them, which relabels to a bounded natural-variable
term. -/
theorem exists_isTermCodeFor (i x : ℕ) : ∃ c, K.isTermCodeFor i x c = true := by
  letI := K.structureAt i
  obtain ⟨t, ht⟩ := (Tuple.generates_iff (K.gens i)).1 (K.generates i) x
  refine ⟨@encode (L.Term ℕ) Primcodable.toEncodable (t.relabel Fin.val), ?_⟩
  have hval : K.termRealize ((i, K.gens i), t.relabel Fin.val) = x := by
    rw [K.termRealize_relabel_view i (K.gens i) rfl t]
    exact ht
  unfold isTermCodeFor
  rw [@encodek (L.Term ℕ) Primcodable.toEncodable (t.relabel Fin.val)]
  simp only [Option.elim]
  rw [(Term.varsBelowBool_iff _ _).2 (Term.varsBelow_relabel_val t), hval]
  simp

/-- The canonical term code for `x` at index `i`: the least code of a bounded term over
the generators realizing `x`. -/
noncomputable def termCodeFor (i x : ℕ) : ℕ :=
  Nat.find (K.exists_isTermCodeFor i x)

/-- The canonical code decodes to a bounded generator term realizing `x`. -/
theorem termCodeFor_spec (i x : ℕ) :
    K.isTermCodeFor i x (K.termCodeFor i x) = true :=
  Nat.find_spec (K.exists_isTermCodeFor i x)

/-- Encoding-independent content of the canonical code: it decodes to a bounded-variable
term over the generators at `i` that realizes `x`. Downstream code uses this, not the
code-level Boolean. -/
theorem termCodeFor_spec' (i x : ℕ) :
    ∃ t : L.Term ℕ,
      @decode (L.Term ℕ) Primcodable.toEncodable (K.termCodeFor i x) = some t ∧
        Term.VarsBelow (K.gens i).length t ∧ K.termRealize ((i, K.gens i), t) = x := by
  have h := K.termCodeFor_spec i x
  unfold isTermCodeFor at h
  rcases hd : @decode (L.Term ℕ) Primcodable.toEncodable (K.termCodeFor i x) with _ | t
  · rw [hd] at h; simp at h
  · rw [hd] at h
    simp only [Option.elim, Bool.and_eq_true] at h
    exact ⟨t, rfl, (Term.varsBelowBool_iff _ _).1 h.1, of_decide_eq_true h.2⟩

/-- The canonical representing term of `x` at index `i`: the term decoded from the least
qualifying code. This is the encoding-independent handle for downstream code. -/
noncomputable def representingTerm (i x : ℕ) : L.Term ℕ :=
  (@decode (L.Term ℕ) Primcodable.toEncodable (K.termCodeFor i x)).getD default

/-- The canonical code decodes to the representing term. -/
theorem decode_termCodeFor (i x : ℕ) :
    @decode (L.Term ℕ) Primcodable.toEncodable (K.termCodeFor i x) =
      some (K.representingTerm i x) := by
  obtain ⟨t, hd, -, -⟩ := K.termCodeFor_spec' i x
  rw [representingTerm, hd, Option.getD_some]

/-- The representing term has all variables below the generator count. -/
theorem representingTerm_varsBelow (i x : ℕ) :
    Term.VarsBelow (K.gens i).length (K.representingTerm i x) := by
  obtain ⟨_, hd, hvb, -⟩ := K.termCodeFor_spec' i x
  rw [representingTerm, hd, Option.getD_some]; exact hvb

/-- The representing term realizes `x` over the generators at index `i`. -/
theorem representingTerm_realize (i x : ℕ) :
    K.termRealize ((i, K.gens i), K.representingTerm i x) = x := by
  obtain ⟨_, hd, -, hre⟩ := K.termCodeFor_spec' i x
  rw [representingTerm, hd, Option.getD_some]; exact hre

/-- Transport a value along potential embedding data: decode the canonical code of `x` over
the domain generators and realize the resulting term at the range tuple in the codomain
index. Kept code-level (not routed through `representingTerm`) so the computability proof
never composes a term-valued computation.

Total on all data. The canonical code always decodes (`decode_termCodeFor`), so the
`none → 0` fallback is unreachable; the genuine off-spec case is malformed `G` — in
particular a range tuple shorter than the domain generators, where `envFun` supplies `0`
for the missing variables, so transport still returns a (default-padded) value. -/
noncomputable def transportValue (G : PotentialEmbeddingData) (x : ℕ) : ℕ :=
  (@decode (L.Term ℕ) Primcodable.toEncodable (K.termCodeFor G.domIdx x)).elim 0
    fun t ↦ K.termRealize ((G.codIdx, G.rangeTuple), t)

-- The computability layer is factored per review finding 3. `isTermCodeFor` and
-- `termCodeFor` feed `representingTerm` (the term-valued API); `transportValue`'s own
-- computability is deliberately code-level and bypasses `representingTerm_computableIn`,
-- keeping the composition ℕ-valued (see `transportValue_computableIn`). Typed intermediates
-- keep the dependent term encoding from overwhelming elaboration.

-- The closing `option_casesOn.of_eq fun _ ↦ rfl` bridges `Option.casesOn ↔ Option.elim`
-- through `isTermCodeFor`, whose `decode` sits on the `L.Term ℕ` stack-machine
-- `Primcodable`; the typed intermediates keep that reduction within the default budget.
/-- The code test is computable in the oracle, uniformly in the index, the value, and the
candidate code. -/
theorem isTermCodeFor_computableIn :
    ComputableIn₂ O fun (p : ℕ × ℕ) (c : ℕ) ↦ K.isTermCodeFor p.1 p.2 c := by
  let α := ((ℕ × ℕ) × ℕ) × L.Term ℕ
  have hi : ComputableIn O fun q : α ↦ q.1.1.1 :=
    ComputableIn.fst.comp (ComputableIn.fst.comp ComputableIn.fst)
  have hx : ComputableIn O fun q : α ↦ q.1.1.2 :=
    ComputableIn.snd.comp (ComputableIn.fst.comp ComputableIn.fst)
  have ht : ComputableIn O fun q : α ↦ q.2 := ComputableIn.snd
  have hgens : ComputableIn O fun q : α ↦ K.gens q.1.1.1 :=
    K.gens_computableIn.comp hi
  have hlen : ComputableIn O fun q : α ↦ (K.gens q.1.1.1).length :=
    (Primrec.list_length.to_comp.computableIn).comp hgens
  have hvb : ComputableIn O fun q : α ↦
      Term.varsBelowBool (K.gens q.1.1.1).length q.2 :=
    (Term.primrec₂_varsBelowBool.to_comp.computableIn₂).comp hlen ht
  have hinput : ComputableIn O fun q : α ↦
      ((q.1.1.1, K.gens q.1.1.1), q.2) :=
    (hi.pair hgens).pair ht
  have hrealize : ComputableIn O fun q : α ↦
      K.termRealize ((q.1.1.1, K.gens q.1.1.1), q.2) :=
    K.termRealize_computableIn.comp hinput
  have heq : ComputableIn O fun q : α ↦
      decide (K.termRealize ((q.1.1.1, K.gens q.1.1.1), q.2) = q.1.1.2) :=
    (Primrec.eq (α := ℕ)).decide.to_comp.computableIn₂.comp hrealize hx
  have hbody : ComputableIn O fun q : α ↦
      Term.varsBelowBool (K.gens q.1.1.1).length q.2 &&
        decide (K.termRealize ((q.1.1.1, K.gens q.1.1.1), q.2) = q.1.1.2) :=
    (Primrec.and.to_comp.computableIn₂.comp hvb heq)
  have hdecode : ComputableIn O fun q : (ℕ × ℕ) × ℕ ↦
      @decode (L.Term ℕ) Primcodable.toEncodable q.2 :=
    (Computable.decode.computableIn).comp ComputableIn.snd
  refine (ComputableIn.option_casesOn hdecode (ComputableIn.const false) hbody.to₂).of_eq
    fun q ↦ ?_
  rcases hd : @decode (L.Term ℕ) Primcodable.toEncodable q.2 with _ | t <;>
    simp [ComputableAgeIn.isTermCodeFor, hd]

/-- The canonical code is computable in the oracle, uniformly in the index and value. -/
theorem termCodeFor_computableIn :
    ComputableIn O fun p : ℕ × ℕ ↦ K.termCodeFor p.1 p.2 :=
  (ComputableIn.find K.isTermCodeFor_computableIn
    fun p ↦ K.exists_isTermCodeFor p.1 p.2).of_eq fun _ ↦ rfl

/-- The representing term is computable in the oracle, uniformly in the index and value. -/
theorem representingTerm_computableIn :
    ComputableIn O fun p : ℕ × ℕ ↦ K.representingTerm p.1 p.2 := by
  have hdecode : ComputableIn O fun p : ℕ × ℕ ↦
      @decode (L.Term ℕ) Primcodable.toEncodable (K.termCodeFor p.1 p.2) :=
    (Computable.decode.computableIn).comp K.termCodeFor_computableIn
  exact (Primrec.option_getD.to_comp.computableIn₂.comp hdecode
    (ComputableIn.const default)).of_eq fun _ ↦ rfl

-- `termCodeFor` is opaque past this point: the computability composites below must not
-- reduce the search (`Nat.find`) through `isTermCodeFor`'s `L.Term ℕ` stack-machine
-- `Primcodable` (an unbounded `whnf`). Downstream reasoning uses `termCodeFor_spec`,
-- `decode_termCodeFor`, and the `representingTerm` lemmas, never the raw definition.
attribute [irreducible] ComputableAgeIn.termCodeFor

/-- Transport is computable in the oracle, uniformly in the potential embedding data and
the value. Proved by fusing code → decode → evaluate so the composition stays `ℕ`-valued:
the decoded term `t` is consumed as an input in the `some` branch (`option_casesOn`), never
as the output of a term-valued computability theorem. With `termCodeFor` opaque, the
composites compare by congruence rather than reducing the stack-machine `Primcodable`. -/
theorem transportValue_computableIn :
    ComputableIn O fun q : PotentialEmbeddingData × ℕ ↦ K.transportValue q.1 q.2 := by
  have hcode : ComputableIn O fun q : PotentialEmbeddingData × ℕ ↦
      K.termCodeFor q.1.domIdx q.2 :=
    ComputableIn.comp
      (α := PotentialEmbeddingData × ℕ) (β := ℕ × ℕ) (σ := ℕ)
      (f := fun p : ℕ × ℕ ↦ K.termCodeFor p.1 p.2)
      (g := fun q : PotentialEmbeddingData × ℕ ↦ (q.1.domIdx, q.2))
      K.termCodeFor_computableIn
      ((PotentialEmbeddingData.domIdx_computable.comp ComputableIn.fst).pair
        ComputableIn.snd)
  have hdecode : ComputableIn O fun q : PotentialEmbeddingData × ℕ ↦
      @decode (L.Term ℕ) Primcodable.toEncodable (K.termCodeFor q.1.domIdx q.2) :=
    (Computable.decode.computableIn).comp hcode
  have heval : ComputableIn O fun p : (PotentialEmbeddingData × ℕ) × L.Term ℕ ↦
      K.termRealize ((p.1.1.codIdx, p.1.1.rangeTuple), p.2) :=
    K.termRealize_computableIn.comp
      (((PotentialEmbeddingData.codIdx_computable.comp
          (ComputableIn.fst.comp ComputableIn.fst)).pair
        (PotentialEmbeddingData.rangeTuple_computable.comp
          (ComputableIn.fst.comp ComputableIn.fst))).pair ComputableIn.snd)
  refine (ComputableIn.option_casesOn hdecode (ComputableIn.const 0) heval.to₂).of_eq
    fun q ↦ ?_
  rcases hd : @decode (L.Term ℕ) Primcodable.toEncodable (K.termCodeFor q.1.domIdx q.2)
    with _ | t <;> simp [ComputableAgeIn.transportValue, hd]

/-- On actual data, transport agrees with the realized embedding: it carries each value of
the domain presentation to its image under `toEmbedding`. -/
theorem transportValue_eq_toEmbedding {G : PotentialEmbeddingData}
    (h : G.WellFormed K)
    (hAE : @AtomicEquivalent L ℕ ℕ (K.structureAt G.domIdx) (K.structureAt G.codIdx) _
      (K.gens G.domIdx).view (G.targetView h)) (x : ℕ) :
    K.transportValue G x = G.toEmbedding h hAE x := by
  have hcomp : G.targetView h = ⇑(G.toEmbedding h hAE) ∘ (K.gens G.domIdx).view :=
    funext fun j ↦ (G.toEmbedding_apply_gens h hAE j).symm
  have hvb := K.representingTerm_varsBelow G.domIdx x
  have hre := K.representingTerm_realize G.domIdx x
  rw [transportValue, K.decode_termCodeFor G.domIdx x]
  simp only [Option.elim]
  generalize K.representingTerm G.domIdx x = rt at hvb hre ⊢
  rw [← hre, K.termRealize_eq_realize_restrictVar G.codIdx G.rangeTuple h rt hvb,
    K.termRealize_eq_realize_restrictVar G.domIdx (K.gens G.domIdx) rfl rt hvb]
  change @Term.realize L ℕ (K.structureAt G.codIdx) _ (G.targetView h)
      (rt.restrictVar fun v ↦ (⟨v.1, hvb v.1 v.2⟩ : Fin (K.gens G.domIdx).length)) =
    G.toEmbedding h hAE (@Term.realize L ℕ (K.structureAt G.domIdx) _ (K.gens G.domIdx).view
      (rt.restrictVar fun v ↦ (⟨v.1, hvb v.1 v.2⟩ : Fin (K.gens G.domIdx).length)))
  rw [hcomp]
  exact HomClass.realize_term (G.toEmbedding h hAE)

/-- Transport along the identity potential embedding is the identity on values. Public and
`simp`-normal: composition's identity laws consume this, so it must not live only in the
audit module. -/
@[simp]
theorem transportValue_id (i x : ℕ) :
    K.transportValue (PotentialEmbeddingData.id K i) x = x := by
  rw [transportValue, K.decode_termCodeFor, Option.elim]
  exact K.representingTerm_realize i x

end ComputableAgeIn

end FirstOrder.Language
