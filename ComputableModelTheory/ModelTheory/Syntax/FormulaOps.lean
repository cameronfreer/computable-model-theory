/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Syntax.FormulaSigma

/-!
# Computability of formula constructors

The sigma-level formula constructors are primitive recursive (hence computable) for an
effective language over a `Primcodable` variable type. `sigmaEqual` and `sigmaRel` are
new total constructors mirroring mathlib's `sigmaImp`/`sigmaAll` style — `dite` on the
compatibility guard, `default` on mismatch — with `@[simp]` application lemmas on
matching inputs; `sigmaNot` and `sigmaEx` are derived. Each primitive recursion proof
factors through the `listEncode` shadow: the symbol list of the constructed formula is a
list operation on the arguments' symbol lists, and `Primrec.encode_iff` transfers.

Deferred to later stages (per the roadmap's PR 5): `relabel` and substitution for
formulas, `liftAt`, `castLE`, `toPrenex`, and the prenex/universal/existential
predicates.
-/

open Encodable

namespace FirstOrder.Language.BoundedFormula

universe u v u'

variable {L : Language.{u, v}} {α : Type u'}

/-! ### Total sigma-level constructors -/

/-- Applies `equal` to two sigma-packaged terms, or returns `default` if the variable
bounds mismatch (mirroring mathlib's `sigmaImp`). -/
def sigmaEqual : (Σ k, L.Term (α ⊕ Fin k)) → (Σ k, L.Term (α ⊕ Fin k)) →
    Σ n, L.BoundedFormula α n
  | ⟨m, t₁⟩, ⟨n, t₂⟩ =>
    if h : m = n then ⟨m, equal t₁ (Eq.mp (by rw [h]) t₂)⟩ else default

@[simp]
lemma sigmaEqual_apply {n} {t₁ t₂ : L.Term (α ⊕ Fin n)} :
    sigmaEqual ⟨n, t₁⟩ ⟨n, t₂⟩ = ⟨n, equal t₁ t₂⟩ := by
  simp only [sigmaEqual, ↓reduceDIte, eq_mp_eq_cast, cast_eq]

/-- Mismatch semantics: `sigmaEqual` on unequal variable bounds is `default`. -/
lemma sigmaEqual_of_ne {m n} (t₁ : L.Term (α ⊕ Fin m)) (t₂ : L.Term (α ⊕ Fin n))
    (h : m ≠ n) : sigmaEqual ⟨m, t₁⟩ ⟨n, t₂⟩ = default := by
  rw [sigmaEqual, dif_neg h]

/-- Applies `rel` to a packaged relation symbol and a list of sigma-packaged argument
terms at the stated variable bound, or returns `default` if the list length mismatches
the arity or any term's variable bound mismatches the stated one. -/
def sigmaRel (r : Σ m, L.Relations m) (k : ℕ)
    (ts : List (Σ k', L.Term (α ⊕ Fin k'))) : Σ n, L.BoundedFormula α n :=
  if h : ts.length = r.1 ∧ ∀ i : Fin ts.length, (ts.get i).1 = k then
    ⟨k, rel r.2 fun i ↦
      Eq.mp (by rw [h.2 (Fin.cast h.1.symm i)]) (ts.get (Fin.cast h.1.symm i)).2⟩
  else default

@[simp]
lemma sigmaRel_apply {n k : ℕ} (R : L.Relations n) (ts : Fin n → L.Term (α ⊕ Fin k)) :
    sigmaRel ⟨n, R⟩ k ((List.finRange n).map fun i ↦ ⟨k, ts i⟩) = ⟨k, rel R ts⟩ := by
  have hlen : ((List.finRange n).map fun i ↦
      (⟨k, ts i⟩ : Σ k', L.Term (α ⊕ Fin k'))).length = n := by simp
  have hget : ∀ i : Fin ((List.finRange n).map fun i ↦
      (⟨k, ts i⟩ : Σ k', L.Term (α ⊕ Fin k'))).length,
      (((List.finRange n).map fun i ↦ (⟨k, ts i⟩ : Σ k', L.Term (α ⊕ Fin k'))).get i) =
        ⟨k, ts (Fin.cast hlen i)⟩ := by
    intro i
    simp only [List.get_eq_getElem, List.getElem_map, List.getElem_finRange]
    rfl
  rw [sigmaRel, dif_pos ⟨hlen, fun i ↦ by rw [hget i]⟩]
  refine congrArg (Sigma.mk k) ?_
  refine congrArg (rel R) (funext fun i ↦ ?_)
  have hg := hget (Fin.cast hlen.symm i)
  rw [show (Fin.cast hlen (Fin.cast hlen.symm i)) = i from rfl] at hg
  rw [eq_mp_eq_cast, cast_eq_iff_heq, hg]

/-- Mismatch semantics: `sigmaRel` on an argument list of the wrong length is
`default`. -/
lemma sigmaRel_of_length_ne (r : Σ m, L.Relations m) (k : ℕ)
    (ts : List (Σ k', L.Term (α ⊕ Fin k'))) (h : ts.length ≠ r.1) :
    sigmaRel r k ts = default := by
  rw [sigmaRel, dif_neg fun hc ↦ h hc.1]

/-- Mismatch semantics: `sigmaRel` on an argument list containing a term of the wrong
variable bound is `default`. -/
lemma sigmaRel_of_bound_ne (r : Σ m, L.Relations m) (k : ℕ)
    (ts : List (Σ k', L.Term (α ⊕ Fin k'))) (i : Fin ts.length)
    (h : (ts.get i).1 ≠ k) : sigmaRel r k ts = default := by
  rw [sigmaRel, dif_neg fun hc ↦ h (hc.2 i)]

/-- The sigma-level negation, `default`-preserving through `sigmaImp`. -/
def sigmaNot (p : Σ n, L.BoundedFormula α n) : Σ n, L.BoundedFormula α n :=
  sigmaImp p ⟨p.1, falsum⟩

@[simp]
lemma sigmaNot_apply {n} (φ : L.BoundedFormula α n) : sigmaNot ⟨n, φ⟩ = ⟨n, φ.not⟩ :=
  sigmaImp_apply

/-- The sigma-level existential, through `sigmaNot` and `sigmaAll`. -/
def sigmaEx (p : Σ n, L.BoundedFormula α n) : Σ n, L.BoundedFormula α n :=
  sigmaNot (sigmaAll (sigmaNot p))

@[simp]
lemma sigmaEx_apply {n} (φ : L.BoundedFormula α (n + 1)) :
    sigmaEx ⟨n + 1, φ⟩ = ⟨n, φ.ex⟩ := by
  simp [sigmaEx, BoundedFormula.ex]

/-! ### Primitive recursiveness -/

section PrimrecOps

variable [Primcodable α] [L.EffectiveLanguage]

/-- The symbol list of a packaged bounded formula is primitive recursive: it is the
decoding of the formula's own code. -/
theorem primrec_sigmaBoundedFormula_listEncode :
    Primrec fun s : Σ n, L.BoundedFormula α n ↦ s.2.listEncode := by
  have h : Primrec fun s : Σ n, L.BoundedFormula α n ↦
      ((decode (α := List (FormulaSymbol L α)) (encode s)).getD []) :=
    Primrec.option_getD.comp (Primrec.decode.comp Primrec.encode) (Primrec.const [])
  exact h.of_eq fun ⟨n, φ⟩ ↦ by
    rw [show encode (⟨n, φ⟩ : Σ n, L.BoundedFormula α n) =
      encode φ.listEncode from rfl, encodek]
    rfl

/-- The index of a packaged bounded formula is primitive recursive: run the stack
machine on the symbol list and read off the head entry's index. -/
theorem primrec_sigmaBoundedFormula_fst :
    Primrec fun s : Σ n, L.BoundedFormula α n ↦ s.1 := by
  have h : Primrec fun s : Σ n, L.BoundedFormula α n ↦
      (((decodeStack (L := L) s.2.listEncode).head?).map Prod.fst).getD 0 :=
    Primrec.option_getD.comp
      (Primrec.option_map
        (Primrec.list_head?.comp
          (primrec_decodeStack.comp primrec_sigmaBoundedFormula_listEncode))
        ((Primrec.fst.comp Primrec.snd).to₂))
      (Primrec.const 0)
  refine h.of_eq fun ⟨n, φ⟩ ↦ ?_
  have hl : listDecode (L := L) (α := α) φ.listEncode = [⟨n, φ⟩] := by
    have h := listDecode_encode_list [(⟨n, φ⟩ : Σ n, L.BoundedFormula α n)]
    rwa [List.flatMap_singleton] at h
  rw [decodeStack_eq_map_listEncode, hl]
  rfl

/-- The pair representation of a packaged bounded formula is primitive recursive. -/
theorem primrec_sigmaRepr : Primrec (sigmaRepr (L := L) (α := α)) :=
  Primrec.pair primrec_sigmaBoundedFormula_fst primrec_sigmaBoundedFormula_listEncode

/-- The sigma-level falsum constructor is primitive recursive. -/
theorem primrec_sigmaFalsum :
    Primrec fun n : ℕ ↦ (⟨n, falsum⟩ : Σ n, L.BoundedFormula α n) := by
  have h : Primrec fun n : ℕ ↦
      encode ([Sum.inr (Sum.inr (n + 2))] : List (FormulaSymbol L α)) :=
    Primrec.encode.comp (Primrec.list_cons.comp
      (Primrec.sumInr.comp (Primrec.sumInr.comp
        (Primrec.nat_add.comp Primrec.id (Primrec.const 2))))
      (Primrec.const []))
  exact Primrec.encode_iff.1 (h.of_eq fun n ↦ rfl)

/-- The sigma-level equality constructor is primitive recursive. -/
theorem primrec₂_sigmaEqual : Primrec₂ (sigmaEqual (L := L) (α := α)) := by
  have h : Primrec fun p : (Σ k, L.Term (α ⊕ Fin k)) × (Σ k, L.Term (α ⊕ Fin k)) ↦
      if p.1.1 = p.2.1 then
        encode ([Sum.inl p.1, Sum.inl p.2] : List (FormulaSymbol L α))
      else encode (default : Σ n, L.BoundedFormula α n) :=
    Primrec.ite
      (Primrec.eq.comp ((Term.primrec_sigmaTerm_fst L α).comp Primrec.fst)
        ((Term.primrec_sigmaTerm_fst L α).comp Primrec.snd))
      (Primrec.encode.comp (Primrec.list_cons.comp (Primrec.sumInl.comp Primrec.fst)
        (Primrec.list_cons.comp (Primrec.sumInl.comp Primrec.snd) (Primrec.const []))))
      (Primrec.const _)
  refine Primrec.encode_iff.1 (h.of_eq fun p ↦ ?_)
  rcases p with ⟨⟨m, t₁⟩, ⟨n, t₂⟩⟩
  by_cases h : m = n
  · subst h
    rw [if_pos rfl, sigmaEqual_apply]
    rfl
  · rw [if_neg h, sigmaEqual, dif_neg h]

omit [Primcodable α] [L.EffectiveLanguage] in
private theorem all_fst_eq_iff (ts : List (Σ k', L.Term (α ⊕ Fin k'))) (k : ℕ) :
    (ts.all fun t ↦ t.1 = k) = true ↔ ∀ i : Fin ts.length, (ts.get i).1 = k := by
  rw [List.all_eq_true]
  constructor
  · intro H i
    simpa using H _ (List.get_mem ts i)
  · intro H x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    simpa using H ⟨i, hi⟩

/-- The sigma-level relation constructor is primitive recursive over the packaged
triple of relation symbol, variable bound, and argument list. -/
theorem primrec_sigmaRel :
    Primrec fun q : (Σ m, L.Relations m) × ℕ × List (Σ k', L.Term (α ⊕ Fin k')) ↦
      sigmaRel q.1 q.2.1 q.2.2 := by
  have hall : Primrec fun q :
      (Σ m, L.Relations m) × ℕ × List (Σ k', L.Term (α ⊕ Fin k')) ↦
      q.2.2.all fun t ↦ t.1 = q.2.1 := by
    have h : Primrec fun q :
        (Σ m, L.Relations m) × ℕ × List (Σ k', L.Term (α ⊕ Fin k')) ↦
        q.2.2.foldr (fun t r ↦ decide (t.1 = q.2.1) && r) true :=
      Primrec.list_foldr (Primrec.snd.comp Primrec.snd) (Primrec.const true)
        ((Primrec.and.comp
          (Primrec.eq.decide.comp
            ((Term.primrec_sigmaTerm_fst L α).comp (Primrec.fst.comp Primrec.snd))
            ((Primrec.fst.comp Primrec.snd).comp Primrec.fst))
          (Primrec.snd.comp Primrec.snd)).to₂)
    refine h.of_eq fun q ↦ ?_
    induction q.2.2 with
    | nil => rfl
    | cons a l ih => simp [List.all_cons, ih]
  have hr1 : Primrec fun q :
      (Σ m, L.Relations m) × ℕ × List (Σ k', L.Term (α ⊕ Fin k')) ↦ q.1.1 :=
    (primrec_relationSymbol_arity (L := L)).comp Primrec.fst
  have h : Primrec fun q :
      (Σ m, L.Relations m) × ℕ × List (Σ k', L.Term (α ⊕ Fin k')) ↦
      if q.2.2.length = q.1.1 ∧ (q.2.2.all fun t ↦ t.1 = q.2.1) then
        encode (Sum.inr (Sum.inl q.1) :: Sum.inr (Sum.inr q.2.1) ::
          q.2.2.map Sum.inl : List (FormulaSymbol L α))
      else encode (default : Σ n, L.BoundedFormula α n) :=
    Primrec.ite
      (PrimrecPred.and
        (Primrec.eq.comp
          (Primrec.list_length.comp (Primrec.snd.comp Primrec.snd)) hr1)
        (Primrec.eq.comp hall (Primrec.const true)))
      (Primrec.encode.comp (Primrec.list_cons.comp
        (Primrec.sumInr.comp (Primrec.sumInl.comp Primrec.fst))
        (Primrec.list_cons.comp
          (Primrec.sumInr.comp (Primrec.sumInr.comp (Primrec.fst.comp Primrec.snd)))
          (Primrec.list_map (Primrec.snd.comp Primrec.snd)
            (Primrec.sumInl.comp Primrec.snd).to₂))))
      (Primrec.const _)
  refine Primrec.encode_iff.1 (h.of_eq fun q ↦ ?_)
  rcases q with ⟨⟨m, R⟩, k, ts⟩
  by_cases hc : ts.length = m ∧ ∀ i : Fin ts.length, (ts.get i).1 = k
  · obtain ⟨h1, h2⟩ := hc
    subst h1
    rw [if_pos ⟨rfl, (all_fst_eq_iff ts k).2 h2⟩, sigmaRel, dif_pos ⟨rfl, h2⟩]
    refine congrArg encode ?_
    show _ = listEncode _
    rw [listEncode]
    simp only [List.cons_append, List.nil_append]
    refine congrArg₂ List.cons rfl (congrArg₂ List.cons rfl ?_)
    · conv_lhs => rw [← List.map_get_finRange ts]
      rw [List.map_map]
      refine List.map_congr_left fun j hj ↦ ?_
      refine congrArg Sum.inl ?_
      refine Sigma.ext (h2 j) ?_
      simp only [eq_mp_eq_cast]
      exact (cast_heq _ _).symm
  · rw [if_neg (fun hb ↦ hc ⟨hb.1, (all_fst_eq_iff ts k).1 hb.2⟩), sigmaRel, dif_neg hc]

/-- Mathlib's sigma-level implication is primitive recursive. -/
theorem primrec₂_sigmaImp : Primrec₂ (sigmaImp (L := L) (α := α)) := by
  have h : Primrec fun p : (Σ n, L.BoundedFormula α n) × (Σ n, L.BoundedFormula α n) ↦
      encode (imprepr (sigmaRepr p.1) (sigmaRepr p.2)).2 :=
    Primrec.encode.comp (Primrec.snd.comp
      (primrec₂_imprepr.comp (primrec_sigmaRepr.comp Primrec.fst)
        (primrec_sigmaRepr.comp Primrec.snd)))
  exact Primrec.encode_iff.1
    (h.of_eq fun p ↦ (congrArg (fun x ↦ encode x.2) (sigmaRepr_imp p.1 p.2)).symm)

/-- Mathlib's sigma-level universal quantifier is primitive recursive. -/
theorem primrec_sigmaAll : Primrec (sigmaAll (L := L) (α := α)) := by
  have h : Primrec fun p : Σ n, L.BoundedFormula α n ↦
      encode (allrepr (sigmaRepr p)).2 :=
    Primrec.encode.comp (Primrec.snd.comp (primrec_allrepr.comp primrec_sigmaRepr))
  exact Primrec.encode_iff.1
    (h.of_eq fun p ↦ (congrArg (fun x ↦ encode x.2) (sigmaRepr_all p)).symm)

/-- The sigma-level negation is primitive recursive. -/
theorem primrec_sigmaNot : Primrec (sigmaNot (L := L) (α := α)) :=
  primrec₂_sigmaImp.comp Primrec.id
    (primrec_sigmaFalsum.comp primrec_sigmaBoundedFormula_fst)

/-- The sigma-level existential quantifier is primitive recursive. -/
theorem primrec_sigmaEx : Primrec (sigmaEx (L := L) (α := α)) :=
  primrec_sigmaNot.comp (primrec_sigmaAll.comp primrec_sigmaNot)

/-- The public contract: the sigma-level falsum constructor is computable. -/
theorem computable_sigmaFalsum :
    Computable fun n : ℕ ↦ (⟨n, falsum⟩ : Σ n, L.BoundedFormula α n) :=
  primrec_sigmaFalsum.to_comp

/-- The public contract: the sigma-level equality constructor is computable. -/
theorem computable₂_sigmaEqual : Computable₂ (sigmaEqual (L := L) (α := α)) :=
  primrec₂_sigmaEqual.to_comp

/-- The public contract: the sigma-level relation constructor is computable. -/
theorem computable_sigmaRel :
    Computable fun q : (Σ m, L.Relations m) × ℕ × List (Σ k', L.Term (α ⊕ Fin k')) ↦
      sigmaRel q.1 q.2.1 q.2.2 :=
  primrec_sigmaRel.to_comp

/-- The public contract: the sigma-level implication is computable. -/
theorem computable₂_sigmaImp : Computable₂ (sigmaImp (L := L) (α := α)) :=
  primrec₂_sigmaImp.to_comp

/-- The public contract: the sigma-level universal quantifier is computable. -/
theorem computable_sigmaAll : Computable (sigmaAll (L := L) (α := α)) :=
  primrec_sigmaAll.to_comp

/-- The public contract: the sigma-level negation is computable. -/
theorem computable_sigmaNot : Computable (sigmaNot (L := L) (α := α)) :=
  primrec_sigmaNot.to_comp

/-- The public contract: the sigma-level existential quantifier is computable. -/
theorem computable_sigmaEx : Computable (sigmaEx (L := L) (α := α)) :=
  primrec_sigmaEx.to_comp

end PrimrecOps

end FirstOrder.Language.BoundedFormula
