/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.PartialFiniteRoute

/-!
# The finite-search route: the executable checker

Given exact finite carrier certificates and an effectively finite language, "does this code
describe an embedding?" is a **finite** question. This file turns it into a total Boolean
function, computable in the presentation oracle.

The program is written partially and then totalized, because the only non-elementary steps are
calls to the family's stored partial evaluators `funEval` / `relEval`. Code validity is checked
**inside** the partial program rather than assumed as a hypothesis, so the result is a
proof-free `Bool` on arbitrary inputs: an invalid code is defined and rejected, never divergent
and never accepted.

The four semantic checks are

* generator images agree with the range tuple — with the tuple **lengths compared first**, so
  no `zip` truncation can accept a short generator tuple;
* the image list is duplicate-free, which on a normalized source is exactly injectivity;
* every function symbol is **preserved**, at every argument tuple over the source carrier;
* every relation symbol is **reflected as well as preserved** — the two evaluations are
  compared as booleans, not implied in one direction.

Nullary symbols are not skipped: the tuple enumeration at arity `0` is `[[]]`, so a constant or
a nullary relation is checked exactly once. No lookup is ever defaulted: a missing image makes
the comparison `false`, which rejects, rather than substituting a value.
-/

open Encodable Part FirstOrder Language

namespace FirstOrder.Language

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]
variable {B : PartialAgeIn O L}

namespace ExactFiniteCarriers

variable (C : ExactFiniteCarriers B)

/-! ### Code validity, as a total Boolean

`finiteMaps` membership is a decidable finite condition; deciding it *inside* the program is
what lets every later statement quantify over arbitrary `f : List ℕ`. -/

/-- The image list has the width of the normalized source and lands in the target. -/
def validCode (i j : ℕ) (f : List ℕ) : Bool :=
  (f.length == (C.support i).length) && f.all fun y ↦ decide (y ∈ C.support j)

theorem validCode_eq_true_iff (i j : ℕ) (f : List ℕ) :
    C.validCode i j f = true ↔ f ∈ C.finiteMaps i j := by
  rw [validCode, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, C.mem_finiteMaps_iff]
  exact and_congr Iff.rfl (forall₂_congr fun _ _ ↦ decide_eq_true_iff)

/-! ### The generator check

The length comparison is a **separate conjunct evaluated first**. A zipped scan would silently
accept a generator tuple shorter than the range tuple, since `zip` truncates to the shorter
list; scanning positions and comparing the two `getElem?` lookups cannot, because a position
past the end of either list produces `none` on that side. -/

/-- Generator images agree with the intended range tuple. -/
def generatorCheck (F : PotentialEmbeddingData) (f : List ℕ) : Bool :=
  ((B.gens F.domIdx).length == F.rangeTuple.length) &&
    (List.range (B.gens F.domIdx).length).all fun n ↦
      ((B.gens F.domIdx)[n]?.bind fun x ↦ C.applyMap F.domIdx f x) == F.rangeTuple[n]?

/-- The generator check says exactly what a realizer's coordinate equations say, read through
the code. -/
theorem generatorCheck_eq_true_iff (F : PotentialEmbeddingData) (f : List ℕ) :
    C.generatorCheck F f = true ↔
      ∃ hlen : (B.gens F.domIdx).length = F.rangeTuple.length,
        ∀ k : Fin (B.gens F.domIdx).length,
          C.applyMap F.domIdx f ((B.gens F.domIdx).get k) =
            Option.some (F.rangeTuple.get (Fin.cast hlen k)) := by
  rw [generatorCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
  constructor
  · rintro ⟨hlen, hall⟩
    refine ⟨hlen, fun k ↦ ?_⟩
    have hk := hall k.1 (List.mem_range.2 k.isLt)
    have h2 : (k : ℕ) < F.rangeTuple.length := by have := k.isLt; omega
    rw [beq_iff_eq, List.getElem?_eq_getElem k.isLt, List.getElem?_eq_getElem h2] at hk
    simpa [List.get_eq_getElem] using hk
  · rintro ⟨hlen, hk⟩
    refine ⟨hlen, fun n hn ↦ ?_⟩
    have hn1 : n < (B.gens F.domIdx).length := List.mem_range.1 hn
    have hn2 : n < F.rangeTuple.length := by omega
    rw [beq_iff_eq, List.getElem?_eq_getElem hn1, List.getElem?_eq_getElem hn2]
    simpa [List.get_eq_getElem] using hk ⟨n, hn1⟩

/-! ### Mapping an argument list through the code

`Option`-valued, and a missing image propagates as `none`. Nothing is defaulted: the callers
turn a `none` into a rejected check, never into a substituted value. -/

/-- Apply the code to every entry of an argument list. -/
def applyMapList (i : ℕ) (f : List ℕ) (as : List ℕ) : Option (List ℕ) :=
  as.foldr (fun a acc ↦ (C.applyMap i f a).bind fun b ↦ acc.map (b :: ·)) (Option.some [])

@[simp]
theorem applyMapList_nil (i : ℕ) (f : List ℕ) : C.applyMapList i f [] = Option.some [] :=
  rfl

theorem applyMapList_cons (i : ℕ) (f : List ℕ) (a : ℕ) (t : List ℕ) :
    C.applyMapList i f (a :: t) =
      (C.applyMap i f a).bind fun b ↦ (C.applyMapList i f t).map (b :: ·) :=
  rfl

variable {C}

/-- A successful list lookup is a pointwise successful lookup. -/
theorem applyMapList_forall₂ {i : ℕ} {f : List ℕ} :
    ∀ {as bs : List ℕ}, C.applyMapList i f as = Option.some bs →
      List.Forall₂ (fun a b ↦ C.applyMap i f a = Option.some b) as bs := by
  intro as
  induction as with
  | nil =>
    intro bs h
    rw [applyMapList_nil, Option.some_inj] at h
    exact h ▸ List.Forall₂.nil
  | cons a t ih =>
    intro bs h
    rw [applyMapList_cons] at h
    obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨t', ht', rfl⟩ := Option.map_eq_some_iff.1 h
    exact List.Forall₂.cons hb (ih ht')

/-- Over carrier arguments and a valid code, the list lookup succeeds. -/
theorem exists_applyMapList {i j : ℕ} {f : List ℕ} (hf : f ∈ C.finiteMaps i j) :
    ∀ {as : List ℕ}, (∀ a ∈ as, a ∈ B.domainAt i) →
      ∃ bs, C.applyMapList i f as = Option.some bs ∧ ∀ b ∈ bs, b ∈ B.domainAt j := by
  intro as
  induction as with
  | nil => exact fun _ ↦ ⟨[], rfl, by simp⟩
  | cons a t ih =>
    intro has
    obtain ⟨b, hb, hbj⟩ := C.exists_applyMap_eq_some hf (has a List.mem_cons_self)
    obtain ⟨bs, hbs, hbsj⟩ := ih fun x hx ↦ has x (List.mem_cons_of_mem a hx)
    refine ⟨b :: bs, ?_, ?_⟩
    · simp [applyMapList_cons, hb, hbs]
    · intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact hbj
      · exact hbsj y hy

variable (C)

/-! ### The instance enumerations

Every symbol paired with every argument tuple over the source carrier. At arity `0` the tuple
enumeration is `[[]]`, so a constant or a nullary relation contributes exactly one instance —
checked once, not skipped. -/

variable [EffectivelyFiniteLanguage L]

/-- Every function-symbol instance over the source carrier. -/
def funInstances (i : ℕ) : List (L.FunctionSymbol × List ℕ) :=
  (EffectivelyFiniteLanguage.functionSymbols (L := L)).flatMap fun s ↦
    (List.replicate s.arity (C.support i)).sections.map fun as ↦ (s, as)

/-- Every relation-symbol instance over the source carrier. -/
def relInstances (i : ℕ) : List (L.RelationSymbol × List ℕ) :=
  (EffectivelyFiniteLanguage.relationSymbols (L := L)).flatMap fun r ↦
    (List.replicate r.arity (C.support i)).sections.map fun as ↦ (r, as)

theorem mem_funInstances_iff (i : ℕ) (p : L.FunctionSymbol × List ℕ) :
    p ∈ C.funInstances i ↔ p.2.length = p.1.arity ∧ ∀ x ∈ p.2, x ∈ B.domainAt i := by
  obtain ⟨s, as⟩ := p
  rw [funInstances, List.mem_flatMap]
  constructor
  · rintro ⟨t, -, ht⟩
    obtain ⟨as', has', heq⟩ := List.mem_map.1 ht
    rw [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    obtain ⟨hlen, hmem⟩ := List.mem_sections_replicate.1 has'
    exact ⟨hlen, fun x hx ↦ (C.mem_support_iff_domainAt i x).1 (hmem x hx)⟩
  · rintro ⟨hlen, hmem⟩
    refine ⟨s, EffectivelyFiniteLanguage.mem_functionSymbols s, List.mem_map.2 ⟨as, ?_, rfl⟩⟩
    exact List.mem_sections_replicate.2
      ⟨hlen, fun x hx ↦ (C.mem_support_iff_domainAt i x).2 (hmem x hx)⟩

theorem mem_relInstances_iff (i : ℕ) (p : L.RelationSymbol × List ℕ) :
    p ∈ C.relInstances i ↔ p.2.length = p.1.arity ∧ ∀ x ∈ p.2, x ∈ B.domainAt i := by
  obtain ⟨r, as⟩ := p
  rw [relInstances, List.mem_flatMap]
  constructor
  · rintro ⟨t, -, ht⟩
    obtain ⟨as', has', heq⟩ := List.mem_map.1 ht
    rw [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    obtain ⟨hlen, hmem⟩ := List.mem_sections_replicate.1 has'
    exact ⟨hlen, fun x hx ↦ (C.mem_support_iff_domainAt i x).1 (hmem x hx)⟩
  · rintro ⟨hlen, hmem⟩
    refine ⟨r, EffectivelyFiniteLanguage.mem_relationSymbols r, List.mem_map.2 ⟨as, ?_, rfl⟩⟩
    exact List.mem_sections_replicate.2
      ⟨hlen, fun x hx ↦ (C.mem_support_iff_domainAt i x).2 (hmem x hx)⟩

/-! ### One instance at a time

Each instance is reduced to a **single** `Option` case followed by exactly two evaluator calls.
Everything that can be decided without the oracle — arity matching and the image lookups — is
done first, in `funInstance?` / `relInstance?`, so the partial part of the program is as small
as possible.

The source value is looked up like any other: `applyMap i f v` against `Option.some u`. If the
lookup fails the comparison is `false`, so a missing source image **rejects**. It is never
replaced by `structureAt`'s off-domain value or by any other default. -/

/-- The source and image application data of one function instance. -/
def funInstance? (i : ℕ) (f : List ℕ) (p : L.FunctionSymbol × List ℕ) :
    Option (FunctionApplicationData L ℕ × FunctionApplicationData L ℕ) :=
  (FunctionApplicationData.ofSymbolArgs? p).bind fun d ↦
    (C.applyMapList i f p.2).bind fun bs ↦
      (FunctionApplicationData.ofSymbolArgs? (p.1, bs)).map fun e ↦ (d, e)

/-- The source and image application data of one relation instance. -/
def relInstance? (i : ℕ) (f : List ℕ) (p : L.RelationSymbol × List ℕ) :
    Option (RelationApplicationData L ℕ × RelationApplicationData L ℕ) :=
  (RelationApplicationData.ofSymbolArgs? p).bind fun d ↦
    (C.applyMapList i f p.2).bind fun bs ↦
      (RelationApplicationData.ofSymbolArgs? (p.1, bs)).map fun e ↦ (d, e)

/-- **Function preservation at one instance.** -/
def funCheckOne (i j : ℕ) (f : List ℕ) (p : L.FunctionSymbol × List ℕ) : Part Bool :=
  Option.casesOn (motive := fun _ ↦ Part Bool) (C.funInstance? i f p) (Part.some false)
    fun de ↦ (B.funEval i de.1).bind fun v ↦
      (B.funEval j de.2).map fun u ↦ (C.applyMap i f v == Option.some u)

/-- **Relation equivalence at one instance.** The two truth values are compared, so the check
fails if the relation holds on one side and not the other — reflection as well as
preservation. -/
def relCheckOne (i j : ℕ) (f : List ℕ) (p : L.RelationSymbol × List ℕ) : Part Bool :=
  Option.casesOn (motive := fun _ ↦ Part Bool) (C.relInstance? i f p) (Part.some false)
    fun de ↦ (B.relEval i de.1).bind fun b₁ ↦ (B.relEval j de.2).map fun b₂ ↦ (b₁ == b₂)

/-! ### The scans and the guarded program -/

/-- Every function instance over the source carrier. -/
def functionScanPart (F : PotentialEmbeddingData) (f : List ℕ) : Part Bool :=
  foldrPart (fun p acc ↦ (C.funCheckOne F.domIdx F.codIdx f p).map (· && acc)) true
    (C.funInstances F.domIdx)

/-- Every relation instance over the source carrier. -/
def relationScanPart (F : PotentialEmbeddingData) (f : List ℕ) : Part Bool :=
  foldrPart (fun p acc ↦ (C.relCheckOne F.domIdx F.codIdx f p).map (· && acc)) true
    (C.relInstances F.domIdx)

/-- **The checker, as a partial program.** Code validity is a guard *inside* the program: an
invalid code is defined and rejected, and only a valid one reaches the partial scans. This is
what makes the totalized checker a proof-free `Bool` on arbitrary inputs, rather than a
function of a membership hypothesis. -/
def finiteMapCheckPart (F : PotentialEmbeddingData) (f : List ℕ) : Part Bool :=
  bif C.validCode F.domIdx F.codIdx f && C.generatorCheck F f && decide f.Nodup then
    (C.functionScanPart F f).bind fun b₁ ↦ (C.relationScanPart F f).map fun b₂ ↦ b₁ && b₂
  else Part.some false

/-! ### Everywhere defined

The guard does the work: on a valid code every argument tuple drawn from the source carrier is
domain-valued, so both stored evaluators halt by `funEval_correct` / `relEval_correct`, and
every image lookup succeeds by `exists_applyMap_eq_some`. -/

variable {C}

/-- A partial right fold whose steps are all defined is defined. -/
private theorem foldrPart_dom {β σ : Type*} {g : β → σ →. σ} {init : σ} :
    ∀ {l : List β}, (∀ b ∈ l, ∀ acc : σ, (g b acc).Dom) → (foldrPart g init l).Dom := by
  intro l
  induction l with
  | nil => exact fun _ ↦ trivial
  | cons b t ih =>
    intro h
    rw [foldrPart_cons]
    have hdt := ih fun x hx ↦ h x (List.mem_cons_of_mem b hx)
    exact ⟨hdt, h b List.mem_cons_self _ ⟩

/-- On a valid code, a function instance over the source carrier assembles. -/
theorem exists_funInstance? {i j : ℕ} {f : List ℕ} (hf : f ∈ C.finiteMaps i j)
    {p : L.FunctionSymbol × List ℕ} (hp : p ∈ C.funInstances i) :
    ∃ d e, C.funInstance? i f p = Option.some (d, e) ∧
      (∀ k, d.args k ∈ B.domainAt i) ∧ (∀ k, e.args k ∈ B.domainAt j) := by
  obtain ⟨hlen, hmem⟩ := (C.mem_funInstances_iff i p).1 hp
  obtain ⟨bs, hbs, hbsj⟩ := exists_applyMapList hf hmem
  have hblen : bs.length = p.1.arity :=
    ((applyMapList_forall₂ hbs).length_eq).symm.trans hlen
  refine ⟨FunctionApplicationData.equivSubtype.symm ⟨p, hlen⟩,
    FunctionApplicationData.equivSubtype.symm ⟨(p.1, bs), hblen⟩, ?_,
    fun k ↦ hmem _ (List.get_mem _ _), fun k ↦ hbsj _ (List.get_mem _ _)⟩
  simp only [funInstance?, FunctionApplicationData.ofSymbolArgs?_of_length_eq p hlen, hbs]
  show Option.map (fun e ↦ (FunctionApplicationData.equivSubtype.symm ⟨p, hlen⟩, e))
      (FunctionApplicationData.ofSymbolArgs? (p.1, bs)) = _
  rw [FunctionApplicationData.ofSymbolArgs?_of_length_eq (p.1, bs) hblen]
  rfl

/-- On a valid code, a relation instance over the source carrier assembles. -/
theorem exists_relInstance? {i j : ℕ} {f : List ℕ} (hf : f ∈ C.finiteMaps i j)
    {p : L.RelationSymbol × List ℕ} (hp : p ∈ C.relInstances i) :
    ∃ d e, C.relInstance? i f p = Option.some (d, e) ∧
      (∀ k, d.args k ∈ B.domainAt i) ∧ (∀ k, e.args k ∈ B.domainAt j) := by
  obtain ⟨hlen, hmem⟩ := (C.mem_relInstances_iff i p).1 hp
  obtain ⟨bs, hbs, hbsj⟩ := exists_applyMapList hf hmem
  have hblen : bs.length = p.1.arity :=
    ((applyMapList_forall₂ hbs).length_eq).symm.trans hlen
  refine ⟨RelationApplicationData.equivSubtype.symm ⟨p, hlen⟩,
    RelationApplicationData.equivSubtype.symm ⟨(p.1, bs), hblen⟩, ?_,
    fun k ↦ hmem _ (List.get_mem _ _), fun k ↦ hbsj _ (List.get_mem _ _)⟩
  simp only [relInstance?, RelationApplicationData.ofSymbolArgs?_of_length_eq p hlen, hbs]
  show Option.map (fun e ↦ (RelationApplicationData.equivSubtype.symm ⟨p, hlen⟩, e))
      (RelationApplicationData.ofSymbolArgs? (p.1, bs)) = _
  rw [RelationApplicationData.ofSymbolArgs?_of_length_eq (p.1, bs) hblen]
  rfl

theorem funCheckOne_dom {i j : ℕ} {f : List ℕ} (hf : f ∈ C.finiteMaps i j)
    {p : L.FunctionSymbol × List ℕ} (hp : p ∈ C.funInstances i) :
    (C.funCheckOne i j f p).Dom := by
  obtain ⟨d, e, hde, hd, he⟩ := exists_funInstance? hf hp
  have hv := B.funEval_correct i d fun k ↦ B.mem_domainAt_iff.1 (hd k)
  have hu := B.funEval_correct j e fun k ↦ B.mem_domainAt_iff.1 (he k)
  refine Part.dom_iff_mem.2
    ⟨C.applyMap i f (@FunctionApplicationData.funMap L ℕ (B.structureAt i) d) ==
      Option.some (@FunctionApplicationData.funMap L ℕ (B.structureAt j) e), ?_⟩
  rw [funCheckOne, hde]
  exact Part.mem_bind_iff.2 ⟨_, hv, (Part.mem_map_iff _).2 ⟨_, hu, rfl⟩⟩

theorem relCheckOne_dom {i j : ℕ} {f : List ℕ} (hf : f ∈ C.finiteMaps i j)
    {p : L.RelationSymbol × List ℕ} (hp : p ∈ C.relInstances i) :
    (C.relCheckOne i j f p).Dom := by
  obtain ⟨d, e, hde, hd, he⟩ := exists_relInstance? hf hp
  obtain ⟨b₁, hb₁, -⟩ := B.relEval_correct i d fun k ↦ B.mem_domainAt_iff.1 (hd k)
  obtain ⟨b₂, hb₂, -⟩ := B.relEval_correct j e fun k ↦ B.mem_domainAt_iff.1 (he k)
  refine Part.dom_iff_mem.2 ⟨b₁ == b₂, ?_⟩
  rw [relCheckOne, hde]
  exact Part.mem_bind_iff.2 ⟨b₁, hb₁, (Part.mem_map_iff _).2 ⟨b₂, hb₂, rfl⟩⟩

theorem functionScanPart_dom {F : PotentialEmbeddingData} {f : List ℕ}
    (hf : f ∈ C.finiteMaps F.domIdx F.codIdx) : (C.functionScanPart F f).Dom :=
  foldrPart_dom fun _ hp _ ↦ funCheckOne_dom hf hp

theorem relationScanPart_dom {F : PotentialEmbeddingData} {f : List ℕ}
    (hf : f ∈ C.finiteMaps F.domIdx F.codIdx) : (C.relationScanPart F f).Dom :=
  foldrPart_dom fun _ hp _ ↦ relCheckOne_dom hf hp

/-- **The program is everywhere defined.** No hypothesis on `F` or `f`: an invalid code takes
the rejecting branch, and a valid one drives every evaluator call onto domain-valued
arguments. -/
theorem finiteMapCheckPart_dom (C : ExactFiniteCarriers B) (F : PotentialEmbeddingData)
    (f : List ℕ) : (C.finiteMapCheckPart F f).Dom := by
  rw [finiteMapCheckPart]
  cases hg : C.validCode F.domIdx F.codIdx f && C.generatorCheck F f && decide f.Nodup with
  | false => exact trivial
  | true =>
    have hf : f ∈ C.finiteMaps F.domIdx F.codIdx :=
      (C.validCode_eq_true_iff _ _ f).1 (by
        rw [Bool.and_eq_true, Bool.and_eq_true] at hg
        exact hg.1.1)
    exact ⟨functionScanPart_dom hf, relationScanPart_dom hf⟩

/-! ### What the scans say

Each scan accepts exactly when every enumerated instance does. The per-instance statements are
read off the stored evaluators: a `Part` holds at most one value, so the evaluator's own
correctness clause identifies the value the check compared. -/

/-- A conjunctive partial fold accepts exactly when every step accepts. No definedness
hypothesis is needed: a rejecting or divergent step blocks acceptance either way. -/
private theorem mem_foldrPart_and {β : Type*} {g : β →. Bool} :
    ∀ {l : List β},
      true ∈ foldrPart (fun b acc ↦ (g b).map (· && acc)) true l ↔ ∀ b ∈ l, true ∈ g b := by
  intro l
  induction l with
  | nil => rw [foldrPart_nil]; simp
  | cons b t ih =>
    rw [foldrPart_cons]
    constructor
    · intro h
      obtain ⟨acc, hacc, h⟩ := Part.mem_bind_iff.1 h
      obtain ⟨v, hv, h⟩ := (Part.mem_map_iff _).1 h
      obtain ⟨rfl, rfl⟩ := Bool.and_eq_true .. ▸ h
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hv
      · exact ih.1 hacc x hx
    · intro h
      exact Part.mem_bind_iff.2 ⟨true, ih.2 fun x hx ↦ h x (List.mem_cons_of_mem b hx),
        (Part.mem_map_iff _).2 ⟨true, h b List.mem_cons_self, rfl⟩⟩

omit [EffectivelyFiniteLanguage L] in
/-- **One function instance is preserved.** The check accepts exactly when the code sends the
source value of the application to the value of the image application. -/
theorem mem_funCheckOne_iff {i j : ℕ} {f : List ℕ} {p : L.FunctionSymbol × List ℕ}
    {d e : FunctionApplicationData L ℕ} (hde : C.funInstance? i f p = Option.some (d, e))
    (hd : ∀ k, d.args k ∈ B.domainAt i) (he : ∀ k, e.args k ∈ B.domainAt j) :
    true ∈ C.funCheckOne i j f p ↔
      C.applyMap i f (@FunctionApplicationData.funMap L ℕ (B.structureAt i) d) =
        Option.some (@FunctionApplicationData.funMap L ℕ (B.structureAt j) e) := by
  have hv := B.funEval_correct i d fun k ↦ B.mem_domainAt_iff.1 (hd k)
  have hu := B.funEval_correct j e fun k ↦ B.mem_domainAt_iff.1 (he k)
  rw [funCheckOne, hde]
  constructor
  · intro h
    obtain ⟨v, hvmem, h⟩ := Part.mem_bind_iff.1 h
    obtain ⟨u, humem, h⟩ := (Part.mem_map_iff _).1 h
    rw [Part.mem_unique hvmem hv, Part.mem_unique humem hu] at h
    exact beq_iff_eq.1 h
  · intro h
    exact Part.mem_bind_iff.2 ⟨_, hv, (Part.mem_map_iff _).2 ⟨_, hu, beq_iff_eq.2 h⟩⟩

omit [EffectivelyFiniteLanguage L] in
/-- **One relation instance is preserved and reflected.** The two truth values are compared, so
the check accepts exactly when the relation holds on one side iff it holds on the other. -/
theorem mem_relCheckOne_iff {i j : ℕ} {f : List ℕ} {p : L.RelationSymbol × List ℕ}
    {d e : RelationApplicationData L ℕ} (hde : C.relInstance? i f p = Option.some (d, e))
    (hd : ∀ k, d.args k ∈ B.domainAt i) (he : ∀ k, e.args k ∈ B.domainAt j) :
    true ∈ C.relCheckOne i j f p ↔
      (@RelationApplicationData.relMap L ℕ (B.structureAt i) d ↔
        @RelationApplicationData.relMap L ℕ (B.structureAt j) e) := by
  obtain ⟨b₁, hb₁, hb₁spec⟩ := B.relEval_correct i d fun k ↦ B.mem_domainAt_iff.1 (hd k)
  obtain ⟨b₂, hb₂, hb₂spec⟩ := B.relEval_correct j e fun k ↦ B.mem_domainAt_iff.1 (he k)
  rw [relCheckOne, hde]
  constructor
  · intro h
    obtain ⟨v₁, hv₁, h⟩ := Part.mem_bind_iff.1 h
    obtain ⟨v₂, hv₂, h⟩ := (Part.mem_map_iff _).1 h
    rw [Part.mem_unique hv₁ hb₁, Part.mem_unique hv₂ hb₂] at h
    exact hb₁spec.symm.trans ((Bool.eq_iff_iff.1 (beq_iff_eq.1 h)).trans hb₂spec)
  · intro h
    refine Part.mem_bind_iff.2 ⟨b₁, hb₁, (Part.mem_map_iff _).2 ⟨b₂, hb₂, beq_iff_eq.2 ?_⟩⟩
    exact Bool.eq_iff_iff.2 (hb₁spec.trans (h.trans hb₂spec.symm))

theorem mem_functionScanPart_iff (F : PotentialEmbeddingData) (f : List ℕ) :
    true ∈ C.functionScanPart F f ↔
      ∀ p ∈ C.funInstances F.domIdx, true ∈ C.funCheckOne F.domIdx F.codIdx f p :=
  mem_foldrPart_and

theorem mem_relationScanPart_iff (F : PotentialEmbeddingData) (f : List ℕ) :
    true ∈ C.relationScanPart F f ↔
      ∀ p ∈ C.relInstances F.domIdx, true ∈ C.relCheckOne F.domIdx F.codIdx f p :=
  mem_foldrPart_and

end ExactFiniteCarriers

end FirstOrder.Language
