/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.CePresentation

/-!
# The transported rank evaluators (Level-1 Pullback, computational core)

The factored partial evaluators of the rank presentation, defined **before** any
structure data so that all computational content is independent of off-domain choices:
each evaluator is the visible composition

1. partial traversal of `rankEnum` over the argument list (`listMapPart`),
2. the original partial evaluator on the reassembled source data,
3. `rankOf` on function outputs (relations return their verdict directly).

The reassembly goes through the guarded `ofSymbolArgs?`, which fails precisely on
length mismatch — impossible on-domain, harmless off-domain (the evaluators are
partial). `rankFunEval_spec` and `rankRelEval_spec` are the on-domain halting-and-value
specifications from which the rank structure's commuting squares follow; the structure
itself (`rankStr`, defined by defaulting these evaluators off-domain) and the bundled
Level-1 presentation come next.
-/

open Encodable FirstOrder Language

namespace FirstOrder.Language

namespace CePresentationIn

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]
variable (P : CePresentationIn O L)

/-- The transported function evaluator: traverse `rankEnum` over the arguments,
reassemble, run the original evaluator, and recode the output through `rankOf`. -/
noncomputable def rankFunEval : FunctionApplicationData L ℕ →. ℕ :=
  fun d ↦ (listMapPart P.rankEnum d.argsList).bind fun src ↦
    ((FunctionApplicationData.ofSymbolArgs? (d.toSymbol, src) : Option _) : Part _).bind
      fun d' ↦ (P.funEval d').bind P.rankOf

/-- The transported relation decider: traverse, reassemble, decide at the source. -/
noncomputable def rankRelEval : RelationApplicationData L ℕ →. Bool :=
  fun d ↦ (listMapPart P.rankEnum d.argsList).bind fun src ↦
    ((RelationApplicationData.ofSymbolArgs? (d.toSymbol, src) : Option _) : Part _).bind
      fun d' ↦ P.relEval d'

/-- The transported function evaluator is partial recursive in the oracle. -/
theorem rankFunEval_recursiveIn : RecursiveIn O P.rankFunEval := by
  have hA : RecursiveIn O fun d : FunctionApplicationData L ℕ ↦
      listMapPart P.rankEnum d.argsList :=
    (RecursiveIn.listMapPart P.rankEnum_recursiveIn).comp
      (FunctionApplicationData.primrec_argsList.to_comp.computableIn)
  have hAsm : RecursiveIn O fun p : FunctionApplicationData L ℕ × List ℕ ↦
      ((FunctionApplicationData.ofSymbolArgs? (p.1.toSymbol, p.2) :
        Option (FunctionApplicationData L ℕ)) : Part (FunctionApplicationData L ℕ)) :=
    ComputableIn.ofOption
      ((FunctionApplicationData.primrec_ofSymbolArgs?.to_comp.computableIn).comp
        (((FunctionApplicationData.primrec_toSymbol.to_comp.computableIn).comp
          ComputableIn.fst).pair ComputableIn.snd))
  have hEval : RecursiveIn O fun d' : FunctionApplicationData L ℕ ↦
      (P.funEval d').bind P.rankOf :=
    RecursiveIn.bind P.funEval_recursiveIn
      ((P.rankOf_recursiveIn.comp ComputableIn.snd).to₂)
  exact RecursiveIn.bind hA
    ((RecursiveIn.bind hAsm ((hEval.comp ComputableIn.snd).to₂)).to₂)

/-- The transported relation decider is partial recursive in the oracle. -/
theorem rankRelEval_recursiveIn : RecursiveIn O P.rankRelEval := by
  have hA : RecursiveIn O fun d : RelationApplicationData L ℕ ↦
      listMapPart P.rankEnum d.argsList :=
    (RecursiveIn.listMapPart P.rankEnum_recursiveIn).comp
      (RelationApplicationData.primrec_argsList.to_comp.computableIn)
  have hAsm : RecursiveIn O fun p : RelationApplicationData L ℕ × List ℕ ↦
      ((RelationApplicationData.ofSymbolArgs? (p.1.toSymbol, p.2) :
        Option (RelationApplicationData L ℕ)) : Part (RelationApplicationData L ℕ)) :=
    ComputableIn.ofOption
      ((RelationApplicationData.primrec_ofSymbolArgs?.to_comp.computableIn).comp
        (((RelationApplicationData.primrec_toSymbol.to_comp.computableIn).comp
          ComputableIn.fst).pair ComputableIn.snd))
  exact RecursiveIn.bind hA
    ((RecursiveIn.bind hAsm
      ((P.relEval_recursiveIn.comp ComputableIn.snd).to₂)).to₂)

/-- Elementwise traversal of the argument list, when every argument's rank is
realized: produces the source tuple in order. -/
private theorem argsList_traversal {arity : ℕ} (args : Fin arity → ℕ)
    (src : Fin arity → ℕ) (hsrc : ∀ k, src k ∈ P.rankEnum (args k)) :
    List.ofFn src ∈ listMapPart P.rankEnum (List.ofFn args) := by
  rw [mem_listMapPart_iff, List.forall₂_iff_get]
  refine ⟨by simp, ?_⟩
  intro i h₁ h₂
  simpa using hsrc ⟨i, by simpa using h₁⟩

/-- On-domain specification of the transported function evaluator: if every argument
rank is realized by a source element, the evaluator halts, and its value is a rank of
the source-side interpretation — the function half of the commuting square. -/
theorem rankFunEval_spec (d : FunctionApplicationData L ℕ)
    (src : Fin d.arity → ℕ) (hsrc : ∀ k, src k ∈ P.rankEnum (d.args k)) :
    ∃ y ∈ P.rankOf (@Structure.funMap L ℕ P.str d.arity d.symbol src),
      y ∈ P.rankFunEval d := by
  have hdom : ∀ k, src k ∈ P.domain :=
    fun k ↦ P.mem_domain_of_mem_rankEnum (hsrc k)
  have hlen : (List.ofFn src).length = d.toSymbol.arity := by
    simp [FunctionApplicationData.toSymbol, FunctionSymbol.arity]
  set d' : FunctionApplicationData L ℕ :=
    FunctionApplicationData.equivSubtype.symm ⟨(d.toSymbol, List.ofFn src), hlen⟩
    with hd'
  have hargs : d'.args = src := by
    funext i
    show (List.ofFn src).get (Fin.cast hlen.symm i) = src i
    simp
  have hd'args : ∀ k, d'.args k ∈ P.domain := fun k ↦ hargs ▸ hdom k
  have hfunMap : @FunctionApplicationData.funMap L ℕ P.str d' =
      @Structure.funMap L ℕ P.str d.arity d.symbol src := by
    show @Structure.funMap L ℕ P.str _ d'.symbol d'.args = _
    rw [hargs]
    exact rfl
  have hvalue := P.funEval_correct d' hd'args
  rw [hfunMap] at hvalue
  have hout : @Structure.funMap L ℕ P.str d.arity d.symbol src ∈ P.domain := by
    refine P.domain_closed _ d.symbol src fun k ↦ hdom k
  obtain ⟨y, hy⟩ := Part.dom_iff_mem.1 ((P.rankOf_dom_iff _).2 hout)
  refine ⟨y, hy, ?_⟩
  rw [rankFunEval]
  refine Part.mem_bind_iff.2 ⟨List.ofFn src, P.argsList_traversal d.args src hsrc, ?_⟩
  refine Part.mem_bind_iff.2 ⟨d', ?_, Part.mem_bind_iff.2 ⟨_, hvalue, hy⟩⟩
  rw [FunctionApplicationData.ofSymbolArgs?_of_length_eq _ hlen]
  exact Part.mem_some _

/-- On-domain specification of the transported relation decider: it halts with a
verdict equivalent to the source-side relation — the relation half of the commuting
square. -/
theorem rankRelEval_spec (d : RelationApplicationData L ℕ)
    (src : Fin d.arity → ℕ) (hsrc : ∀ k, src k ∈ P.rankEnum (d.args k)) :
    ∃ b ∈ P.rankRelEval d,
      (b = true ↔ @Structure.RelMap L ℕ P.str d.arity d.symbol src) := by
  have hdom : ∀ k, src k ∈ P.domain :=
    fun k ↦ P.mem_domain_of_mem_rankEnum (hsrc k)
  have hlen : (List.ofFn src).length = d.toSymbol.arity := by
    simp [RelationApplicationData.toSymbol, RelationSymbol.arity]
  set d' : RelationApplicationData L ℕ :=
    RelationApplicationData.equivSubtype.symm ⟨(d.toSymbol, List.ofFn src), hlen⟩
    with hd'
  have hargs : d'.args = src := by
    funext i
    show (List.ofFn src).get (Fin.cast hlen.symm i) = src i
    simp
  have hd'args : ∀ k, d'.args k ∈ P.domain := fun k ↦ hargs ▸ hdom k
  have hrelMap : @RelationApplicationData.relMap L ℕ P.str d' ↔
      @Structure.RelMap L ℕ P.str d.arity d.symbol src := by
    show @Structure.RelMap L ℕ P.str _ d'.symbol d'.args ↔ _
    rw [hargs]
    exact Iff.rfl
  obtain ⟨b, hb, hbiff⟩ := P.relEval_correct d' hd'args
  refine ⟨b, ?_, hbiff.trans hrelMap⟩
  rw [rankRelEval]
  refine Part.mem_bind_iff.2 ⟨List.ofFn src, P.argsList_traversal d.args src hsrc, ?_⟩
  refine Part.mem_bind_iff.2 ⟨d', ?_, hb⟩
  rw [RelationApplicationData.ofSymbolArgs?_of_length_eq _ hlen]
  exact Part.mem_some _

/-! ### The rank structure and the Level-1 bundle

`rankStr` is the transported evaluators, defaulted off-domain: all on-domain content
flows from the evaluator specifications, and the default is never relied upon. The
bundled presentation uses `posRank` as its enumeration, so its domain is *literally*
`Set.range posRank` through the one canonical `domain` definition — no independently
equivalent predicate exists to cohere. -/

open Classical in
/-- The rank structure: functions evaluate through `rankFunEval` (default `0`
off-domain), relations hold exactly when the decider verdicts `true`. -/
@[reducible]
noncomputable def rankStr : L.Structure ℕ where
  funMap {_} f v :=
    ((P.rankFunEval (FunctionApplicationData.ofFixed f v)).toOption).getD 0
  RelMap {_} R v :=
    true ∈ P.rankRelEval (RelationApplicationData.ofFixed R v)

/-- Commuting square, encoded form: the rank structure's interpretation is the rank of
the source interpretation. Matches the evaluator specification. -/
theorem rankStr_funMap_mem_rankOf {n : ℕ} (f : L.Functions n) (v src : Fin n → ℕ)
    (hsrc : ∀ k, src k ∈ P.rankEnum (v k)) :
    @Structure.funMap L ℕ P.rankStr n f v
      ∈ P.rankOf (@Structure.funMap L ℕ P.str n f src) := by
  classical
  obtain ⟨y, hy, hyeval⟩ :=
    P.rankFunEval_spec (FunctionApplicationData.ofFixed f v) src hsrc
  have hval : @Structure.funMap L ℕ P.rankStr n f v = y := by
    show ((P.rankFunEval (FunctionApplicationData.ofFixed f v)).toOption).getD 0 = y
    rw [Part.toOption_eq_some_iff.2 hyeval]
    rfl
  rwa [hval]

/-- Commuting square, decoded form: decoding the rank structure's output recovers the
source interpretation. What downstream isomorphism and preservation arguments
consume. -/
theorem rankEnum_rankStr_funMap {n : ℕ} (f : L.Functions n) (v src : Fin n → ℕ)
    (hsrc : ∀ k, src k ∈ P.rankEnum (v k)) :
    @Structure.funMap L ℕ P.str n f src
      ∈ P.rankEnum (@Structure.funMap L ℕ P.rankStr n f v) :=
  P.mem_rankEnum_of_mem_rankOf (P.rankStr_funMap_mem_rankOf f v src hsrc)

/-- Commuting square, relations: the rank structure holds a relation exactly when the
source does. -/
theorem rankStr_relMap_iff {n : ℕ} (R : L.Relations n) (v src : Fin n → ℕ)
    (hsrc : ∀ k, src k ∈ P.rankEnum (v k)) :
    @Structure.RelMap L ℕ P.rankStr n R v ↔ @Structure.RelMap L ℕ P.str n R src := by
  obtain ⟨b, hb, hbiff⟩ :=
    P.rankRelEval_spec (RelationApplicationData.ofFixed R v) src hsrc
  show true ∈ P.rankRelEval (RelationApplicationData.ofFixed R v) ↔ _
  constructor
  · intro htrue
    exact hbiff.1 (Part.mem_unique hb htrue)
  · intro hR
    rwa [← hbiff.2 hR]

/-- The source tuple realizing a tuple of defined ranks. -/
private noncomputable def srcOf {n : ℕ} (v : Fin n → ℕ)
    (hv : ∀ k, v k ∈ Set.range P.posRank) : Fin n → ℕ :=
  fun k ↦ (P.rankEnum (v k)).get
    ((P.rankEnum_dom_iff (v k)).2 ((P.rankIdx_dom_iff_mem_range_posRank (v k)).2 (hv k)))

private theorem srcOf_mem {n : ℕ} (v : Fin n → ℕ)
    (hv : ∀ k, v k ∈ Set.range P.posRank) (k : Fin n) :
    P.srcOf v hv k ∈ P.rankEnum (v k) :=
  Part.get_mem _

/-- The Level-1 rank presentation: the rank structure with `posRank` as its
enumeration — so its domain is definitionally `Set.range posRank` — and the factored
evaluators as its computability content. -/
noncomputable def rankPresentation : CePresentationIn O L where
  str := P.rankStr
  enum := P.posRank
  enum_computableIn := P.posRank_computableIn
  domain_closed := by
    intro n f v hv
    have hmem := P.rankStr_funMap_mem_rankOf f v (P.srcOf v hv) (P.srcOf_mem v hv)
    exact (P.rankIdx_dom_iff_mem_range_posRank _).1 (P.rankIdx_dom_of_mem_rankOf hmem)
  funEval := P.rankFunEval
  funEval_recursiveIn := P.rankFunEval_recursiveIn
  funEval_correct := by
    intro d hd
    have hspec := P.rankFunEval_spec d (P.srcOf d.args hd) (P.srcOf_mem d.args hd)
    obtain ⟨y, hy, hyeval⟩ := hspec
    have hval : @FunctionApplicationData.funMap L ℕ P.rankStr d = y := by
      show @Structure.funMap L ℕ P.rankStr _ d.symbol d.args = y
      have := P.rankStr_funMap_mem_rankOf d.symbol d.args
        (P.srcOf d.args hd) (P.srcOf_mem d.args hd)
      exact Part.mem_unique this hy
    rwa [hval]
  relEval := P.rankRelEval
  relEval_recursiveIn := P.rankRelEval_recursiveIn
  relEval_correct := by
    intro d hd
    obtain ⟨b, hb, hbiff⟩ :=
      P.rankRelEval_spec d (P.srcOf d.args hd) (P.srcOf_mem d.args hd)
    refine ⟨b, hb, hbiff.trans ?_⟩
    exact (P.rankStr_relMap_iff d.symbol d.args
      (P.srcOf d.args hd) (P.srcOf_mem d.args hd)).symm

/-- The bundled rank domain is literally the range of `posRank`. -/
@[simp]
theorem rankPresentation_domain : P.rankPresentation.domain = Set.range P.posRank :=
  rfl

end CePresentationIn

end FirstOrder.Language
