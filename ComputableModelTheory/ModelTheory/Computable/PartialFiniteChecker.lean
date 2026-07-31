/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Syntax.ApplicationDataComputable
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

/-! ### Equality of `Option ℕ`, isolated

`generatorCheck` compares two `Option ℕ` lookups. Deciding that through `Primrec.eq` at
`Option ℕ` is a known elaboration hazard in this library — the polymorphic `Primcodable`
eliminator on `Option` is exactly what diverges at `whnf`. So the crossing is done once here,
through encodings, and every later proof consumes `optionNatEq` and its two lemmas without ever
mentioning an encoded option value or `encode_inj`. -/

/-- Equality of `Option ℕ`, computed through encodings. -/
def optionNatEq (x y : Option ℕ) : Bool := decide (encode x = encode y)

@[simp]
theorem optionNatEq_eq_true_iff {x y : Option ℕ} : optionNatEq x y = true ↔ x = y :=
  (decide_eq_true_iff).trans Encodable.encode_inj

theorem optionNatEq_primrec : Primrec₂ optionNatEq :=
  (((Primrec.eq (α := ℕ)).decide.comp (Primrec.encode.comp Primrec.fst)
    (Primrec.encode.comp Primrec.snd))).to₂

/-- The ambient `BEq` agrees with the canonical decision — the one place the two meet. -/
theorem beq_eq_optionNatEq (x y : Option ℕ) : (x == y) = optionNatEq x y :=
  Bool.eq_iff_iff.2 (beq_iff_eq.trans optionNatEq_eq_true_iff.symm)

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

/-- **The crossing.** A pointwise-known map on an `ofFn` argument tuple lists as an `ofFn`
image tuple. Stated on bare `ℕ`-valued families so that generator agreement, `map_fun'` and
`map_rel'` can each consume this one lemma instead of separately reconciling
`equivSubtype.symm`, the carrier coercion and `List.ofFn`. -/
theorem applyMapList_ofFn {i : ℕ} {f : List ℕ} :
    ∀ {n : ℕ} {a b : Fin n → ℕ}, (∀ k, C.applyMap i f (a k) = Option.some (b k)) →
      C.applyMapList i f (List.ofFn a) = Option.some (List.ofFn b) := by
  intro n
  induction n with
  | zero => intro a b _; simp
  | succ m ih =>
    intro a b h
    rw [List.ofFn_succ, List.ofFn_succ, applyMapList_cons, h 0, Option.bind_some,
      ih fun k ↦ h k.succ, Option.map_some]

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

/-- The three total checks, as a token: `some ()` exactly when the input is worth running the
scans on. Naming it keeps the guard a separately typed intermediate, which is what lets the
guarded program be an `Option.casesOn` rather than a `Part`-level conditional. -/
def validToken (F : PotentialEmbeddingData) (f : List ℕ) : Option Unit :=
  bif C.validCode F.domIdx F.codIdx f && C.generatorCheck F f && decide f.Nodup then
    Option.some () else Option.none

omit [EffectivelyFiniteLanguage L] in
/-- The token *is* the guarded constant. A one-delta-step bridge, stated on opaque `F` and `f`
so that consumers never have to reduce the three component checks. -/
theorem validToken_eq_cond (F : PotentialEmbeddingData) (f : List ℕ) :
    C.validToken F f =
      bif (C.validCode F.domIdx F.codIdx f && C.generatorCheck F f && decide f.Nodup) then
        Option.some () else Option.none :=
  rfl

omit [EffectivelyFiniteLanguage L] in
theorem validToken_eq_some_iff (F : PotentialEmbeddingData) (f : List ℕ) :
    C.validToken F f = Option.some () ↔
      f ∈ C.finiteMaps F.domIdx F.codIdx ∧ C.generatorCheck F f = true ∧ f.Nodup := by
  rw [validToken]
  cases hv : C.validCode F.domIdx F.codIdx f && C.generatorCheck F f && decide f.Nodup with
  | false =>
    rw [Bool.cond_false]
    refine ⟨fun h ↦ absurd h (by simp), fun h ↦ ?_⟩
    have htrue : (C.validCode F.domIdx F.codIdx f && C.generatorCheck F f &&
        decide f.Nodup) = true := by
      rw [Bool.and_eq_true, Bool.and_eq_true]
      exact ⟨⟨(C.validCode_eq_true_iff _ _ f).2 h.1, h.2.1⟩, decide_eq_true h.2.2⟩
    rw [hv] at htrue
    exact absurd htrue (by simp)
  | true =>
    rw [Bool.and_eq_true, Bool.and_eq_true] at hv
    exact ⟨fun _ ↦ ⟨(C.validCode_eq_true_iff _ _ f).1 hv.1.1, hv.1.2,
      of_decide_eq_true hv.2⟩, fun _ ↦ rfl⟩

/-- **The checker, as a partial program.** Code validity is a guard *inside* the program: an
invalid code is defined and rejected, and only a valid one reaches the partial scans. This is
what makes the totalized checker a proof-free `Bool` on arbitrary inputs, rather than a
function of a membership hypothesis.

Written as an `Option.casesOn` on the token so that it is already in the shape
`RecursiveIn.option_casesOn_right` consumes — the rejecting branch stays oracle-free, and the
scans are never entered on an invalid code. -/
def finiteMapCheckPart (F : PotentialEmbeddingData) (f : List ℕ) : Part Bool :=
  Option.casesOn (motive := fun _ ↦ Part Bool) (C.validToken F f) (Part.some false)
    fun _ ↦ (C.functionScanPart F f).bind fun b₁ ↦
      (C.relationScanPart F f).map fun b₂ ↦ b₁ && b₂

/-! ### Everywhere defined

The guard does the work: on a valid code every argument tuple drawn from the source carrier is
domain-valued, so both stored evaluators halt by `funEval_correct` / `relEval_correct`, and
every image lookup succeeds by `exists_applyMap_eq_some`. -/

variable {C}

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
  cases hg : C.validToken F f with
  | none => exact trivial
  | some u =>
    have hf : f ∈ C.finiteMaps F.domIdx F.codIdx :=
      ((C.validToken_eq_some_iff F f).1 (by rwa [Unit.ext u ()] at hg)).1
    exact ⟨functionScanPart_dom hf, relationScanPart_dom hf⟩

/-! ### What the scans say

Each scan accepts exactly when every enumerated instance does. The per-instance statements are
read off the stored evaluators: a `Part` holds at most one value, so the evaluator's own
correctness clause identifies the value the check compared. -/

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
  true_mem_foldrPart_and_iff

theorem mem_relationScanPart_iff (F : PotentialEmbeddingData) (f : List ℕ) :
    true ∈ C.relationScanPart F f ↔
      ∀ p ∈ C.relInstances F.domIdx, true ∈ C.relCheckOne F.domIdx F.codIdx f p :=
  true_mem_foldrPart_and_iff

/-! ### The map a valid code determines

On a valid code every carrier element has an image in the target carrier, so the code names an
actual function between the member carriers. Everything the headline needs about it — the
lookup equation, injectivity from `Nodup`, and the `ofFn` crossing — is recorded here, before
any structure preservation is discussed. -/

omit [EffectivelyFiniteLanguage L] in
/-- The function on carriers named by a valid code. -/
noncomputable def codeFun {i j : ℕ} {f : List ℕ} (hf : f ∈ C.finiteMaps i j)
    (x : (B.memberAt i).domain) : (B.memberAt j).domain :=
  ⟨(C.exists_applyMap_eq_some hf x.2).choose, (C.exists_applyMap_eq_some hf x.2).choose_spec.2⟩

omit [EffectivelyFiniteLanguage L] in
/-- The defining equation: the code looks up exactly this value. -/
@[simp]
theorem applyMap_codeFun {i j : ℕ} {f : List ℕ} (hf : f ∈ C.finiteMaps i j)
    (x : (B.memberAt i).domain) :
    C.applyMap i f (x : ℕ) = Option.some ((codeFun hf x : (B.memberAt j).domain) : ℕ) :=
  (C.exists_applyMap_eq_some hf x.2).choose_spec.1

omit [EffectivelyFiniteLanguage L] in
/-- **`Nodup` is injectivity.** On a normalized source a duplicate-free image list forces the
named function to be injective. -/
theorem codeFun_injective {i j : ℕ} {f : List ℕ} (hf : f ∈ C.finiteMaps i j) (hn : f.Nodup) :
    Function.Injective (codeFun hf) := by
  intro x y hxy
  refine Subtype.ext (C.applyMap_injective_of_nodup hf hn x.2 y.2 ?_)
  rw [applyMap_codeFun hf x, applyMap_codeFun hf y, hxy]

omit [EffectivelyFiniteLanguage L] in
/-- The `ofFn` crossing at the named function: an argument tuple over the source carrier lists
as the tuple of its images. This is the single fact `map_fun'` and `map_rel'` consume. -/
theorem applyMapList_ofFn_codeFun {i j : ℕ} {f : List ℕ} (hf : f ∈ C.finiteMaps i j) {n : ℕ}
    (v : Fin n → (B.memberAt i).domain) :
    C.applyMapList i f (List.ofFn fun k ↦ ((v k : ℕ))) =
      Option.some (List.ofFn fun k ↦ ((codeFun hf (v k) : (B.memberAt j).domain) : ℕ)) :=
  applyMapList_ofFn fun k ↦ applyMap_codeFun hf (v k)

/-! ### The instance boundary

The only place `equivSubtype`, `Fin.cast` and application-data reassembly are allowed to
appear. Each lemma hands back the assembled instance together with **both** evaluator
identifications, so `map_fun'` and `map_rel'` never see a cast. Stated for arbitrary `n`,
including `0`: at arity zero `List.ofFn` is `[]` and the lemma still produces the single
instance the enumeration contains. -/

omit [EffectivelyFiniteLanguage L] in
/-- The function instance determined by a symbol and a carrier tuple. -/
theorem funInstance?_ofFn {i j : ℕ} {f : List ℕ} (hf : f ∈ C.finiteMaps i j) {n : ℕ}
    (s : L.Functions n) (v : Fin n → (B.memberAt i).domain) :
    ∃ d e, C.funInstance? i f ((⟨n, s⟩ : L.FunctionSymbol), List.ofFn fun k ↦ ((v k : ℕ))) =
        Option.some (d, e) ∧
      (∀ k, d.args k ∈ B.domainAt i) ∧ (∀ k, e.args k ∈ B.domainAt j) ∧
      @FunctionApplicationData.funMap L ℕ (B.structureAt i) d =
        @Structure.funMap L ℕ (B.structureAt i) n s (fun k ↦ ((v k : ℕ))) ∧
      @FunctionApplicationData.funMap L ℕ (B.structureAt j) e =
        @Structure.funMap L ℕ (B.structureAt j) n s
          (fun k ↦ ((codeFun hf (v k) : (B.memberAt j).domain) : ℕ)) := by
  have hlen : (List.ofFn fun k ↦ ((v k : ℕ))).length =
      FunctionSymbol.arity (⟨n, s⟩ : L.FunctionSymbol) := by simp [FunctionSymbol.arity]
  have hblen : (List.ofFn fun k ↦
      ((codeFun hf (v k) : (B.memberAt j).domain) : ℕ)).length =
      FunctionSymbol.arity (⟨n, s⟩ : L.FunctionSymbol) := by simp [FunctionSymbol.arity]
  refine ⟨FunctionApplicationData.equivSubtype.symm
      ⟨((⟨n, s⟩ : L.FunctionSymbol), List.ofFn fun k ↦ ((v k : ℕ))), hlen⟩,
    FunctionApplicationData.equivSubtype.symm
      ⟨((⟨n, s⟩ : L.FunctionSymbol), List.ofFn fun k ↦
        ((codeFun hf (v k) : (B.memberAt j).domain) : ℕ)), hblen⟩, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [funInstance?, FunctionApplicationData.ofSymbolArgs?_of_length_eq
        ((⟨n, s⟩ : L.FunctionSymbol), List.ofFn fun k ↦ ((v k : ℕ))) hlen,
      applyMapList_ofFn_codeFun hf v]
    show Option.map _ (FunctionApplicationData.ofSymbolArgs?
      ((⟨n, s⟩ : L.FunctionSymbol), List.ofFn fun k ↦
        ((codeFun hf (v k) : (B.memberAt j).domain) : ℕ))) = _
    rw [FunctionApplicationData.ofSymbolArgs?_of_length_eq
      ((⟨n, s⟩ : L.FunctionSymbol), List.ofFn fun k ↦
        ((codeFun hf (v k) : (B.memberAt j).domain) : ℕ)) hblen]
    rfl
  · intro k
    obtain ⟨m, hm⟩ := List.mem_ofFn.1 (List.get_mem _ (Fin.cast hlen.symm k))
    show (List.ofFn fun k ↦ ((v k : ℕ))).get (Fin.cast hlen.symm k) ∈ B.domainAt i
    exact hm ▸ (v m).2
  · intro k
    obtain ⟨m, hm⟩ := List.mem_ofFn.1 (List.get_mem _ (Fin.cast hblen.symm k))
    show (List.ofFn fun k ↦ ((codeFun hf (v k) : (B.memberAt j).domain) : ℕ)).get
      (Fin.cast hblen.symm k) ∈ B.domainAt j
    exact hm ▸ (codeFun hf (v m)).2
  · letI : L.Structure ℕ := B.structureAt i
    rw [FunctionApplicationData.funMap_equivSubtype_symm]
    exact congrArg _ (funext fun k ↦ by simp)
  · letI : L.Structure ℕ := B.structureAt j
    rw [FunctionApplicationData.funMap_equivSubtype_symm]
    exact congrArg _ (funext fun k ↦ by simp)

omit [EffectivelyFiniteLanguage L] in
/-- The relation instance determined by a symbol and a carrier tuple. -/
theorem relInstance?_ofFn {i j : ℕ} {f : List ℕ} (hf : f ∈ C.finiteMaps i j) {n : ℕ}
    (r : L.Relations n) (v : Fin n → (B.memberAt i).domain) :
    ∃ d e, C.relInstance? i f ((⟨n, r⟩ : L.RelationSymbol), List.ofFn fun k ↦ ((v k : ℕ))) =
        Option.some (d, e) ∧
      (∀ k, d.args k ∈ B.domainAt i) ∧ (∀ k, e.args k ∈ B.domainAt j) ∧
      (@RelationApplicationData.relMap L ℕ (B.structureAt i) d ↔
        @Structure.RelMap L ℕ (B.structureAt i) n r (fun k ↦ ((v k : ℕ)))) ∧
      (@RelationApplicationData.relMap L ℕ (B.structureAt j) e ↔
        @Structure.RelMap L ℕ (B.structureAt j) n r
          (fun k ↦ ((codeFun hf (v k) : (B.memberAt j).domain) : ℕ))) := by
  have hlen : (List.ofFn fun k ↦ ((v k : ℕ))).length =
      RelationSymbol.arity (⟨n, r⟩ : L.RelationSymbol) := by simp [RelationSymbol.arity]
  have hblen : (List.ofFn fun k ↦
      ((codeFun hf (v k) : (B.memberAt j).domain) : ℕ)).length =
      RelationSymbol.arity (⟨n, r⟩ : L.RelationSymbol) := by simp [RelationSymbol.arity]
  refine ⟨RelationApplicationData.equivSubtype.symm
      ⟨((⟨n, r⟩ : L.RelationSymbol), List.ofFn fun k ↦ ((v k : ℕ))), hlen⟩,
    RelationApplicationData.equivSubtype.symm
      ⟨((⟨n, r⟩ : L.RelationSymbol), List.ofFn fun k ↦
        ((codeFun hf (v k) : (B.memberAt j).domain) : ℕ)), hblen⟩, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [relInstance?, RelationApplicationData.ofSymbolArgs?_of_length_eq
        ((⟨n, r⟩ : L.RelationSymbol), List.ofFn fun k ↦ ((v k : ℕ))) hlen,
      applyMapList_ofFn_codeFun hf v]
    show Option.map _ (RelationApplicationData.ofSymbolArgs?
      ((⟨n, r⟩ : L.RelationSymbol), List.ofFn fun k ↦
        ((codeFun hf (v k) : (B.memberAt j).domain) : ℕ))) = _
    rw [RelationApplicationData.ofSymbolArgs?_of_length_eq
      ((⟨n, r⟩ : L.RelationSymbol), List.ofFn fun k ↦
        ((codeFun hf (v k) : (B.memberAt j).domain) : ℕ)) hblen]
    rfl
  · intro k
    obtain ⟨m, hm⟩ := List.mem_ofFn.1 (List.get_mem _ (Fin.cast hlen.symm k))
    show (List.ofFn fun k ↦ ((v k : ℕ))).get (Fin.cast hlen.symm k) ∈ B.domainAt i
    exact hm ▸ (v m).2
  · intro k
    obtain ⟨m, hm⟩ := List.mem_ofFn.1 (List.get_mem _ (Fin.cast hblen.symm k))
    show (List.ofFn fun k ↦ ((codeFun hf (v k) : (B.memberAt j).domain) : ℕ)).get
      (Fin.cast hblen.symm k) ∈ B.domainAt j
    exact hm ▸ (codeFun hf (v m)).2
  · letI : L.Structure ℕ := B.structureAt i
    rw [RelationApplicationData.relMap_equivSubtype_symm]
    exact iff_of_eq (congrArg _ (funext fun k ↦ by simp))
  · letI : L.Structure ℕ := B.structureAt j
    rw [RelationApplicationData.relMap_equivSubtype_symm]
    exact iff_of_eq (congrArg _ (funext fun k ↦ by simp))

omit [EffectivelyFiniteLanguage L] in
/-- **The converse of `applyMap_injective_of_nodup`.** A code injective on the normalized
source is duplicate-free.

This is what lets the reverse direction of the headline recover `Nodup` from the realizer's
injectivity: no off-domain extension of the realizer, and no `f = imageList …` identity. It
uses only the positional facts already in play — on a `Nodup` source, `findIdx` inverts
`getElem`, so equal entries of `f` are `applyMap` values at correspondingly equal source
elements. -/
theorem nodup_of_applyMap_injective {i j : ℕ} {f : List ℕ} (hf : f ∈ C.finiteMaps i j)
    (hinj : ∀ x ∈ C.support i, ∀ y ∈ C.support i,
      C.applyMap i f x = C.applyMap i f y → x = y) : f.Nodup := by
  obtain ⟨hlen, -⟩ := (C.mem_finiteMaps_iff i j f).1 hf
  have key : ∀ m : Fin f.length,
      C.applyMap i f ((C.support i).get (Fin.cast hlen m)) = Option.some (f.get m) := by
    intro m
    have hx : (C.support i).get (Fin.cast hlen m) ∈ C.support i := List.get_mem _ _
    have hlt : (C.support i).findIdx
        (fun z ↦ z == (C.support i).get (Fin.cast hlen m)) < (C.support i).length :=
      List.findIdx_lt_length.2 ⟨_, hx, by simp⟩
    have hval : (C.support i)[(C.support i).findIdx
        (fun z ↦ z == (C.support i).get (Fin.cast hlen m))] =
        (C.support i)[((Fin.cast hlen m : Fin (C.support i).length) : ℕ)] := by
      have := List.findIdx_getElem
        (p := fun z ↦ z == (C.support i).get (Fin.cast hlen m)) (xs := C.support i) (w := hlt)
      simpa [List.get_eq_getElem] using this
    have hidx := ((C.support_nodup i).getElem_inj_iff (hi := hlt)
      (hj := (Fin.cast hlen m).isLt)).1 hval
    have hmlt : (m : ℕ) < f.length := m.isLt
    rw [applyMap, hidx]
    simp [List.get_eq_getElem, hmlt]
  rw [List.nodup_iff_injective_get]
  intro m n hmn
  have hxy := hinj ((C.support i).get (Fin.cast hlen m)) (List.get_mem _ _)
    ((C.support i).get (Fin.cast hlen n)) (List.get_mem _ _) (by rw [key m, key n, hmn])
  have hval : (C.support i)[((Fin.cast hlen m : Fin (C.support i).length) : ℕ)] =
      (C.support i)[((Fin.cast hlen n : Fin (C.support i).length) : ℕ)] := by
    simpa [List.get_eq_getElem] using hxy
  exact Fin.ext (((C.support_nodup i).getElem_inj_iff (hi := (Fin.cast hlen m).isLt)
    (hj := (Fin.cast hlen n).isLt)).1 hval)

/-! ### Completeness of the enumeration

The converse direction of the boundary: the forward lemmas say instances built from carrier
tuples are enumerated; these say every enumerated instance *is* one. The cast-heavy core is
factored once, generically, so neither converse handles `Fin.cast` itself. -/

/-- A list of the right length whose entries all satisfy `P` is an `ofFn` of subtype values.
Constructive, and `n = 0` is the `[]` case with the empty tuple. -/
private theorem exists_ofFn_subtype {α : Type*} {P : α → Prop} {xs : List α} {n : ℕ}
    (hlen : xs.length = n) (hmem : ∀ x ∈ xs, P x) :
    ∃ v : Fin n → {x // P x}, xs = List.ofFn fun k ↦ (v k).1 := by
  subst hlen
  exact ⟨fun k ↦ ⟨xs.get k, hmem _ (List.get_mem _ _)⟩, (List.ofFn_get xs).symm⟩

/-- Every enumerated function instance comes from a carrier tuple. -/
theorem exists_ofFn_of_mem_funInstances {i : ℕ} {p : L.FunctionSymbol × List ℕ}
    (hp : p ∈ C.funInstances i) :
    ∃ (n : ℕ) (s : L.Functions n) (v : Fin n → (B.memberAt i).domain),
      p = ((⟨n, s⟩ : L.FunctionSymbol), List.ofFn fun k ↦ ((v k : ℕ))) := by
  obtain ⟨s, as⟩ := p
  obtain ⟨hlen, hmem⟩ := (C.mem_funInstances_iff i _).1 hp
  obtain ⟨n, sf⟩ := s
  obtain ⟨v, hv⟩ := exists_ofFn_subtype (P := fun x ↦ x ∈ (B.memberAt i).domain)
    (n := n) hlen hmem
  exact ⟨n, sf, v, Prod.ext rfl hv⟩

/-- Every enumerated relation instance comes from a carrier tuple. -/
theorem exists_ofFn_of_mem_relInstances {i : ℕ} {p : L.RelationSymbol × List ℕ}
    (hp : p ∈ C.relInstances i) :
    ∃ (n : ℕ) (r : L.Relations n) (v : Fin n → (B.memberAt i).domain),
      p = ((⟨n, r⟩ : L.RelationSymbol), List.ofFn fun k ↦ ((v k : ℕ))) := by
  obtain ⟨r, as⟩ := p
  obtain ⟨hlen, hmem⟩ := (C.mem_relInstances_iff i _).1 hp
  obtain ⟨n, rr⟩ := r
  obtain ⟨v, hv⟩ := exists_ofFn_subtype (P := fun x ↦ x ∈ (B.memberAt i).domain)
    (n := n) hlen hmem
  exact ⟨n, rr, v, Prod.ext rfl hv⟩

/-! ### The embedding an accepted code names

With the instance boundary closed this is assembly: the two scan specifications supply
`map_fun'` and `map_rel'` directly, and the subtype structure being definitional means each
obligation reduces to its `ℕ`-level counterpart by `Subtype.ext` / `Iff.rfl`. -/

/-- Every enumerated symbol instance arising from a carrier tuple is in the enumeration. -/
theorem funInstances_ofFn {i : ℕ} {n : ℕ} (s : L.Functions n)
    (v : Fin n → (B.memberAt i).domain) :
    ((⟨n, s⟩ : L.FunctionSymbol), List.ofFn fun k ↦ ((v k : ℕ))) ∈ C.funInstances i := by
  refine (C.mem_funInstances_iff i _).2 ⟨by simp [FunctionSymbol.arity], fun x hx ↦ ?_⟩
  obtain ⟨m, hm⟩ := List.mem_ofFn.1 hx
  exact hm ▸ (v m).2

theorem relInstances_ofFn {i : ℕ} {n : ℕ} (r : L.Relations n)
    (v : Fin n → (B.memberAt i).domain) :
    ((⟨n, r⟩ : L.RelationSymbol), List.ofFn fun k ↦ ((v k : ℕ))) ∈ C.relInstances i := by
  refine (C.mem_relInstances_iff i _).2 ⟨by simp [RelationSymbol.arity], fun x hx ↦ ?_⟩
  obtain ⟨m, hm⟩ := List.mem_ofFn.1 hx
  exact hm ▸ (v m).2

/-- **The embedding an accepted code names.** -/
noncomputable def codeEmbedding {F : PotentialEmbeddingData} {f : List ℕ}
    (hf : f ∈ C.finiteMaps F.domIdx F.codIdx) (hn : f.Nodup)
    (hfun : true ∈ C.functionScanPart F f) (hrel : true ∈ C.relationScanPart F f) :
    (B.memberAt F.domIdx).domain ↪[L] (B.memberAt F.codIdx).domain where
  toFun := codeFun hf
  inj' := codeFun_injective hf hn
  map_fun' {n} s v := by
    obtain ⟨d, e, hde, hd, he, hdmap, hemap⟩ := funInstance?_ofFn hf s v
    have hcheck := (mem_funCheckOne_iff hde hd he).1
      ((C.mem_functionScanPart_iff F f).1 hfun _ (funInstances_ofFn s v))
    rw [hdmap, hemap] at hcheck
    exact Subtype.ext (Option.some.inj ((applyMap_codeFun hf _).symm.trans hcheck))
  map_rel' {n} r v := by
    obtain ⟨d, e, hde, hd, he, hdmap, hemap⟩ := relInstance?_ofFn hf r v
    have hcheck := (mem_relCheckOne_iff hde hd he).1
      ((C.mem_relationScanPart_iff F f).1 hrel _ (relInstances_ofFn r v))
    rw [hdmap, hemap] at hcheck
    exact hcheck.symm

@[simp]
theorem codeEmbedding_apply {F : PotentialEmbeddingData} {f : List ℕ}
    (hf : f ∈ C.finiteMaps F.domIdx F.codIdx) (hn : f.Nodup)
    (hfun : true ∈ C.functionScanPart F f) (hrel : true ∈ C.relationScanPart F f)
    (x : (B.memberAt F.domIdx).domain) : codeEmbedding hf hn hfun hrel x = codeFun hf x :=
  rfl

omit [EffectivelyFiniteLanguage L] in
/-- **The code names the realizer.** Pointwise, so no equality of embeddings — and hence no
second structure-instance obligation — is ever needed. -/
theorem codeFun_eq_realizer {F : PotentialEmbeddingData} {f : List ℕ}
    (hf : f ∈ C.finiteMaps F.domIdx F.codIdx)
    {G : (B.memberAt F.domIdx).domain ↪[L] (B.memberAt F.codIdx).domain}
    (hcode : ∀ x : (B.memberAt F.domIdx).domain,
      C.applyMap F.domIdx f (x : ℕ) =
        Option.some ((G x : (B.memberAt F.codIdx).domain) : ℕ))
    (x : (B.memberAt F.domIdx).domain) : codeFun hf x = G x :=
  Subtype.ext (Option.some.inj ((applyMap_codeFun hf x).symm.trans (hcode x)))

/-! ### Towards the semantic endpoint

Everything here is membership-based: no `Part.get`, no definedness proof, and neither fold is
unfolded. That keeps the endpoint independent of how the program is later totalized. -/

/-- The `Part`-valued Boolean conjunction, in membership form. -/
private theorem mem_bind_and {x y : Part Bool} :
    true ∈ (x.bind fun b₁ ↦ y.map fun b₂ ↦ b₁ && b₂) ↔ true ∈ x ∧ true ∈ y := by
  constructor
  · intro h
    obtain ⟨b₁, hb₁, h⟩ := Part.mem_bind_iff.1 h
    obtain ⟨b₂, hb₂, h⟩ := (Part.mem_map_iff _).1 h
    obtain ⟨rfl, rfl⟩ := Bool.and_eq_true .. ▸ h
    exact ⟨hb₁, hb₂⟩
  · rintro ⟨hx, hy⟩
    exact Part.mem_bind_iff.2 ⟨true, hx, (Part.mem_map_iff _).2 ⟨true, hy, rfl⟩⟩

omit [EffectivelyFiniteLanguage L] in
/-- **A realized code passes the three total checks.** Generator agreement is the realizer's
own coordinate equations read through the coding clause, and `Nodup` comes from the realizer's
injectivity via `nodup_of_applyMap_injective`. -/
theorem validToken_of_finiteMapRealizes {F : PotentialEmbeddingData} {f : List ℕ}
    (h : C.FiniteMapRealizes F f) : C.validToken F f = Option.some () := by
  obtain ⟨hf, G, hG, hcode⟩ := h
  refine (C.validToken_eq_some_iff F f).2 ⟨hf, ?_, ?_⟩
  · obtain ⟨hlen, hcoord⟩ := hG
    refine (C.generatorCheck_eq_true_iff F f).2 ⟨hlen, fun k ↦ ?_⟩
    rw [show ((B.gens F.domIdx).get k) =
      ((B.gensView F.domIdx k : (B.memberAt F.domIdx).domain) : ℕ) from rfl,
      hcode (B.gensView F.domIdx k), hcoord k]
  · refine C.nodup_of_applyMap_injective hf fun x hx y hy hxy ↦ ?_
    have hx' : x ∈ B.domainAt F.domIdx := (C.mem_support_iff_domainAt F.domIdx x).1 hx
    have hy' : y ∈ B.domainAt F.domIdx := (C.mem_support_iff_domainAt F.domIdx y).1 hy
    rw [hcode ⟨x, hx'⟩, hcode ⟨y, hy'⟩] at hxy
    exact congrArg Subtype.val (G.injective (Subtype.ext (Option.some.inj hxy)))

/-- **The semantic endpoint.** The partial checker accepts exactly the codes that realize the
data.

Membership-based throughout: it case-splits only on `validToken`, uses the two scan
specifications as they stand, and never mentions `Part.get`, a definedness proof, or either
fold's internals — so it is independent of how the program is totalized below. -/
theorem mem_finiteMapCheckPart_iff (F : PotentialEmbeddingData) (f : List ℕ) :
    true ∈ C.finiteMapCheckPart F f ↔ C.FiniteMapRealizes F f := by
  rw [finiteMapCheckPart]
  cases hv : C.validToken F f with
  | none =>
    refine ⟨fun h ↦ absurd (Part.mem_unique h (Part.mem_some false)) (by simp), fun hr ↦ ?_⟩
    rw [C.validToken_of_finiteMapRealizes hr] at hv
    exact absurd hv (by simp)
  | some u =>
    obtain ⟨hf, hgen, hn⟩ := (C.validToken_eq_some_iff F f).1 (by rwa [Unit.ext u ()] at hv)
    show true ∈ ((C.functionScanPart F f).bind fun b₁ ↦
      (C.relationScanPart F f).map fun b₂ ↦ b₁ && b₂) ↔ _
    rw [mem_bind_and]
    constructor
    · rintro ⟨hfun, hrel⟩
      refine ⟨hf, codeEmbedding hf hn hfun hrel, ?_, fun x ↦ applyMap_codeFun hf x⟩
      obtain ⟨hlen, hk⟩ := (C.generatorCheck_eq_true_iff F f).1 hgen
      exact ⟨hlen, fun k ↦
        Option.some.inj ((applyMap_codeFun hf (B.gensView F.domIdx k)).symm.trans (hk k))⟩
    · rintro ⟨-, G, hG, hcode⟩
      have hmap : ∀ y : (B.memberAt F.domIdx).domain, codeFun hf y = G y :=
        fun y ↦ codeFun_eq_realizer hf hcode y
      constructor
      · rw [C.mem_functionScanPart_iff]
        intro p hp
        obtain ⟨n, s, v, rfl⟩ := C.exists_ofFn_of_mem_funInstances hp
        obtain ⟨d, e, hde, hd, he, hdmap, hemap⟩ := funInstance?_ofFn hf s v
        refine (mem_funCheckOne_iff hde hd he).2 ?_
        rw [hdmap, hemap]
        show C.applyMap F.domIdx f
            ((Structure.funMap s v : (B.memberAt F.domIdx).domain) : ℕ) =
          Option.some ((Structure.funMap s fun k ↦ codeFun hf (v k) :
            (B.memberAt F.codIdx).domain) : ℕ)
        rw [applyMap_codeFun hf]
        simp only [hmap]
        rw [G.map_fun]
        rfl
      · rw [C.mem_relationScanPart_iff]
        intro p hp
        obtain ⟨n, r, v, rfl⟩ := C.exists_ofFn_of_mem_relInstances hp
        obtain ⟨d, e, hde, hd, he, hdmap, hemap⟩ := relInstance?_ofFn hf r v
        refine (mem_relCheckOne_iff hde hd he).2 ?_
        rw [hdmap, hemap]
        show @Structure.RelMap L (B.memberAt F.domIdx).domain _ n r v ↔
          @Structure.RelMap L (B.memberAt F.codIdx).domain _ n r fun k ↦ codeFun hf (v k)
        simp only [hmap]
        exact (G.map_rel r v).symm

/-! ### The total checker

Totalization is thin, and deliberately so: the bridge to `Part` membership is the *only* place
the definedness proof appears, so the Boolean characterization is `mem_finiteMapCheckPart_iff`
composed with a one-line lemma, and later audits reason through stable public statements rather
than through `Part.get`. -/

/-- **The checker.** A total `Bool` of the data and the code, with no membership hypothesis. -/
noncomputable def finiteMapCheck (F : PotentialEmbeddingData) (f : List ℕ) : Bool :=
  (C.finiteMapCheckPart F f).get (C.finiteMapCheckPart_dom F f)

/-- The bridge. Everything downstream goes through this rather than unfolding `Part.get`. -/
theorem finiteMapCheck_eq_true_iff_mem (F : PotentialEmbeddingData) (f : List ℕ) :
    C.finiteMapCheck F f = true ↔ true ∈ C.finiteMapCheckPart F f :=
  ⟨fun h ↦ h ▸ Part.get_mem _, fun h ↦ Part.mem_unique (Part.get_mem _) h⟩

/-- **The headline.** The checker decides, on arbitrary input, whether a code realizes the
data. No validity hypothesis: `FiniteMapRealizes` carries code validity itself, and an invalid
code is rejected. -/
theorem finiteMapCheck_eq_true_iff (F : PotentialEmbeddingData) (f : List ℕ) :
    C.finiteMapCheck F f = true ↔ C.FiniteMapRealizes F f :=
  (C.finiteMapCheck_eq_true_iff_mem F f).trans (C.mem_finiteMapCheckPart_iff F f)

/-- **Observation 2.7's finite search, semantically.** Some code passes the checker exactly when
the potential embedding data is realizable — so searching the finite candidate list decides
realizability. -/
theorem exists_finiteMapCheck_iff_partialIsEmbedding (F : PotentialEmbeddingData) :
    (∃ f, C.finiteMapCheck F f = true) ↔ B.PartialIsEmbedding F := by
  rw [← C.exists_finiteMapRealizes_iff_partialIsEmbedding F]
  exact exists_congr fun f ↦ C.finiteMapCheck_eq_true_iff F f

/-- And the search may be confined to the enumerated candidates. -/
theorem exists_mem_finiteMaps_finiteMapCheck_iff (F : PotentialEmbeddingData) :
    (∃ f ∈ C.finiteMaps F.domIdx F.codIdx, C.finiteMapCheck F f = true) ↔
      B.PartialIsEmbedding F := by
  rw [← C.exists_finiteMapRealizes_iff_partialIsEmbedding F]
  exact ⟨fun ⟨f, _, h⟩ ↦ ⟨f, (C.finiteMapCheck_eq_true_iff F f).1 h⟩,
    fun ⟨f, h⟩ ↦ ⟨f, h.mem_finiteMaps, (C.finiteMapCheck_eq_true_iff F f).2 h⟩⟩

/-! ### Computability, rung 1: the total helpers

`finiteMapCheck` is a `noncomputable` Lean definition — it descends from `memberAt`, and its
`Part.get` reads a definedness proof. That is a statement about Lean's definitional evaluator,
not about effectivity: the computational content is carried by the `ComputableIn` theorems
below, which is the same arrangement as every other selector in this library.

The ladder is climbed in order — total helpers, then the per-instance partial checks, then the
scans, then the guard, then one `computableIn_get` — with a typed intermediate `have` for each
step so nothing fuses. -/

omit [EffectivelyFiniteLanguage L] in
theorem validCode_computableIn :
    ComputableIn O fun q : (ℕ × ℕ) × List ℕ ↦ C.validCode q.1.1 q.1.2 q.2 := by
  have hcode : ComputableIn O fun q : (ℕ × ℕ) × List ℕ ↦ q.2 := ComputableIn.snd
  have hsrc : ComputableIn O fun q : (ℕ × ℕ) × List ℕ ↦ C.support q.1.1 :=
    C.support_computableIn.comp (ComputableIn.fst.comp ComputableIn.fst)
  have htgt : ComputableIn O fun q : (ℕ × ℕ) × List ℕ ↦ C.support q.1.2 :=
    C.support_computableIn.comp (ComputableIn.snd.comp ComputableIn.fst)
  have hlen : ComputableIn O fun q : (ℕ × ℕ) × List ℕ ↦
      decide (q.2.length = (C.support q.1.1).length) :=
    ((Primrec.eq (α := ℕ)).decide.to_comp.computableIn₂ (O := O)).comp
      ((Primrec.list_length.to_comp.computableIn (O := O)).comp hcode)
      ((Primrec.list_length.to_comp.computableIn (O := O)).comp hsrc)
  have hall : ComputableIn O fun q : (ℕ × ℕ) × List ℕ ↦
      q.2.all fun y ↦ decide (y ∈ C.support q.1.2) :=
    ComputableIn.list_all hcode
      ((ComputableIn.list_mem (htgt.comp ComputableIn.fst) ComputableIn.snd).to₂)
  have h : ComputableIn O fun q : (ℕ × ℕ) × List ℕ ↦
      (decide (q.2.length = (C.support q.1.1).length) &&
        q.2.all fun y ↦ decide (y ∈ C.support q.1.2)) :=
    (Primrec.and.to_comp.computableIn₂ (O := O)).comp hlen hall
  exact h.of_eq fun q ↦ by rw [validCode]; rfl

/-- The repacking the generator scan's `applyMap` call needs, named with its exact type so a
mistake surfaces as a local type mismatch rather than a downstream `whnf` stall. -/
private def generatorApplyInput
    (r : ((PotentialEmbeddingData × List ℕ) × ℕ) × ℕ) : (ℕ × List ℕ) × ℕ :=
  ((r.1.1.1.domIdx, r.1.1.2), r.2)

omit [EffectivelyFiniteLanguage L] in
private theorem generatorApplyInput_computableIn :
    ComputableIn O generatorApplyInput :=
  (((PotentialEmbeddingData.domIdx_computable.comp
        (ComputableIn.fst.comp (ComputableIn.fst.comp ComputableIn.fst))).pair
      (ComputableIn.snd.comp (ComputableIn.fst.comp ComputableIn.fst))).pair
    ComputableIn.snd).of_eq fun _ ↦ rfl

omit [EffectivelyFiniteLanguage L] in
theorem generatorCheck_computableIn :
    ComputableIn O fun q : PotentialEmbeddingData × List ℕ ↦ C.generatorCheck q.1 q.2 := by
  have hgens : ComputableIn O fun q : PotentialEmbeddingData × List ℕ ↦ B.gens q.1.domIdx :=
    B.gens_computableIn.comp
      (PotentialEmbeddingData.domIdx_computable.comp ComputableIn.fst)
  have hrange : ComputableIn O fun q : PotentialEmbeddingData × List ℕ ↦ q.1.rangeTuple :=
    PotentialEmbeddingData.rangeTuple_computable.comp ComputableIn.fst
  have hlen : ComputableIn O fun q : PotentialEmbeddingData × List ℕ ↦
      decide ((B.gens q.1.domIdx).length = q.1.rangeTuple.length) :=
    ((Primrec.eq (α := ℕ)).decide.to_comp.computableIn₂ (O := O)).comp
      ((Primrec.list_length.to_comp.computableIn (O := O)).comp hgens)
      ((Primrec.list_length.to_comp.computableIn (O := O)).comp hrange)
  have hrng : ComputableIn O fun q : PotentialEmbeddingData × List ℕ ↦
      List.range (B.gens q.1.domIdx).length :=
    (Primrec.list_range.to_comp.computableIn (O := O)).comp
      ((Primrec.list_length.to_comp.computableIn (O := O)).comp hgens)
  have hsrc : ComputableIn O fun r : (PotentialEmbeddingData × List ℕ) × ℕ ↦
      (B.gens r.1.1.domIdx)[r.2]? :=
    (Computable.list_getElem?.computableIn₂ (O := O)).comp
      (hgens.comp ComputableIn.fst) ComputableIn.snd
  have htgt : ComputableIn O fun r : (PotentialEmbeddingData × List ℕ) × ℕ ↦
      r.1.1.rangeTuple[r.2]? :=
    (Computable.list_getElem?.computableIn₂ (O := O)).comp
      (hrange.comp ComputableIn.fst) ComputableIn.snd
  have happly : ComputableIn₂ O fun (r : (PotentialEmbeddingData × List ℕ) × ℕ) (x : ℕ) ↦
      C.applyMap r.1.1.domIdx r.1.2 x :=
    (C.applyMap_computableIn.comp generatorApplyInput_computableIn).to₂
  have hbind : ComputableIn O fun r : (PotentialEmbeddingData × List ℕ) × ℕ ↦
      ((B.gens r.1.1.domIdx)[r.2]?.bind fun x ↦ C.applyMap r.1.1.domIdx r.1.2 x) :=
    ComputableIn.option_bind hsrc happly
  have hstep : ComputableIn O fun r : (PotentialEmbeddingData × List ℕ) × ℕ ↦
      optionNatEq ((B.gens r.1.1.domIdx)[r.2]?.bind fun x ↦
        C.applyMap r.1.1.domIdx r.1.2 x) r.1.1.rangeTuple[r.2]? :=
    (optionNatEq_primrec.to_comp.computableIn₂ (O := O)).comp hbind htgt
  have hall : ComputableIn O fun q : PotentialEmbeddingData × List ℕ ↦
      (List.range (B.gens q.1.domIdx).length).all fun n ↦
        optionNatEq ((B.gens q.1.domIdx)[n]?.bind fun x ↦
          C.applyMap q.1.domIdx q.2 x) q.1.rangeTuple[n]? :=
    ComputableIn.list_all hrng hstep.to₂
  have h : ComputableIn O fun q : PotentialEmbeddingData × List ℕ ↦
      (decide ((B.gens q.1.domIdx).length = q.1.rangeTuple.length) &&
        (List.range (B.gens q.1.domIdx).length).all fun n ↦
          optionNatEq ((B.gens q.1.domIdx)[n]?.bind fun x ↦
            C.applyMap q.1.domIdx q.2 x) q.1.rangeTuple[n]?) :=
    (Primrec.and.to_comp.computableIn₂ (O := O)).comp hlen hall
  refine h.of_eq fun q ↦ ?_
  rw [generatorCheck]
  simp only [beq_eq_optionNatEq]
  rfl

/-- The repacking `validCode_computableIn` expects, named with its exact type. -/
private def validCodeInput (q : PotentialEmbeddingData × List ℕ) : (ℕ × ℕ) × List ℕ :=
  ((q.1.domIdx, q.1.codIdx), q.2)

omit [EffectivelyFiniteLanguage L] in
private theorem validCodeInput_computableIn : ComputableIn O validCodeInput :=
  (((PotentialEmbeddingData.domIdx_computable.comp ComputableIn.fst).pair
      (PotentialEmbeddingData.codIdx_computable.comp ComputableIn.fst)).pair
    ComputableIn.snd).of_eq fun _ ↦ rfl

omit [EffectivelyFiniteLanguage L] in
/-- `validCode` at `PotentialEmbeddingData` indices, as a **standalone adapter**.

Deliberately its own declaration rather than a `have` inside `validToken_computableIn`. Done
inline, `ComputableIn.comp` has to reconcile the ascribed type against the composed one inside
the larger declaration's expected-type context, and stalls at `whnf`. Pulled out and fully
pinned — every implicit type *and* both function parameters — it elaborates immediately, and
callers consume it opaquely. Naming the repacking alone was not enough; the composition itself
had to leave the enclosing context. -/
private theorem validCodePE_computableIn :
    ComputableIn O fun q : PotentialEmbeddingData × List ℕ ↦
      C.validCode q.1.domIdx q.1.codIdx q.2 := by
  have hbase : ComputableIn O fun r : (ℕ × ℕ) × List ℕ ↦ C.validCode r.1.1 r.1.2 r.2 :=
    C.validCode_computableIn
  have hcomposed : ComputableIn O fun q : PotentialEmbeddingData × List ℕ ↦
      C.validCode (validCodeInput q).1.1 (validCodeInput q).1.2 (validCodeInput q).2 :=
    ComputableIn.comp
      (α := PotentialEmbeddingData × List ℕ)
      (β := (ℕ × ℕ) × List ℕ)
      (σ := Bool)
      (f := fun r ↦ C.validCode r.1.1 r.1.2 r.2)
      (g := validCodeInput)
      hbase validCodeInput_computableIn
  exact hcomposed.of_eq fun _ ↦ rfl

omit [EffectivelyFiniteLanguage L] in
/-- The guard is `ComputableIn`; the token then crosses through `encode_iff`.

The crossing matters: proving this by `of_eq` against the `Option Unit`-valued function makes
`of_eq` compare structure-valued functions. Composing the `ℕ`-valued form and letting
`ComputableIn.encode_iff` take the final step keeps `Option Unit` underneath `encode`, where
nothing has to unfold it. -/
theorem validToken_computableIn :
    ComputableIn O fun q : PotentialEmbeddingData × List ℕ ↦ C.validToken q.1 q.2 := by
  have hnodup : ComputableIn O fun q : PotentialEmbeddingData × List ℕ ↦ decide q.2.Nodup :=
    ComputableIn.list_nodup ComputableIn.snd
  have hguard : ComputableIn O fun q : PotentialEmbeddingData × List ℕ ↦
      (C.validCode q.1.domIdx q.1.codIdx q.2 && C.generatorCheck q.1 q.2 &&
        decide q.2.Nodup) :=
    (Primrec.and.to_comp.computableIn₂ (O := O)).comp
      ((Primrec.and.to_comp.computableIn₂ (O := O)).comp
        C.validCodePE_computableIn C.generatorCheck_computableIn)
      hnodup
  have hcode : ComputableIn O fun q : PotentialEmbeddingData × List ℕ ↦
      (bif (C.validCode q.1.domIdx q.1.codIdx q.2 && C.generatorCheck q.1 q.2 &&
        decide q.2.Nodup) then encode (Option.some () : Option Unit)
        else encode (Option.none : Option Unit)) :=
    ComputableIn.cond hguard
      (ComputableIn.const (encode (Option.some () : Option Unit)))
      (ComputableIn.const (encode (Option.none : Option Unit)))
  have henc : ComputableIn O fun q : PotentialEmbeddingData × List ℕ ↦
      encode (C.validToken q.1 q.2) :=
    hcode.of_eq fun q ↦ by
      rw [C.validToken_eq_cond]
      cases (C.validCode q.1.domIdx q.1.codIdx q.2 && C.generatorCheck q.1 q.2 &&
        decide q.2.Nodup) <;> rfl
  exact ComputableIn.encode_iff.mp henc

/-! ### Computability, rung 2: the argument-list lookup -/

/-- The fold step's repacking for `applyMap`. -/
private def applyMapStepInput
    (x : ((ℕ × List ℕ) × List ℕ) × (ℕ × Option (List ℕ))) : (ℕ × List ℕ) × ℕ :=
  (x.1.1, x.2.1)

omit [EffectivelyFiniteLanguage L] in
private theorem applyMapStepInput_computableIn : ComputableIn O applyMapStepInput :=
  ((ComputableIn.fst.comp ComputableIn.fst).pair
    (ComputableIn.fst.comp ComputableIn.snd)).of_eq fun _ ↦ rfl

omit [EffectivelyFiniteLanguage L] in
/-- Ladder step 3 again: the composition is extracted and fully pinned, because inside
`applyMapList_computableIn` the enclosing expected type stalls `comp` exactly as it did for
`validCode`. -/
private theorem applyMapStep_computableIn :
    ComputableIn O fun x : ((ℕ × List ℕ) × List ℕ) × (ℕ × Option (List ℕ)) ↦
      C.applyMap x.1.1.1 x.1.1.2 x.2.1 := by
  have hbase : ComputableIn O fun p : (ℕ × List ℕ) × ℕ ↦ C.applyMap p.1.1 p.1.2 p.2 :=
    C.applyMap_computableIn
  have hcomposed : ComputableIn O fun x : ((ℕ × List ℕ) × List ℕ) × (ℕ × Option (List ℕ)) ↦
      C.applyMap (applyMapStepInput x).1.1 (applyMapStepInput x).1.2
        (applyMapStepInput x).2 :=
    ComputableIn.comp
      (α := ((ℕ × List ℕ) × List ℕ) × (ℕ × Option (List ℕ)))
      (β := (ℕ × List ℕ) × ℕ)
      (σ := Option ℕ)
      (f := fun p ↦ C.applyMap p.1.1 p.1.2 p.2)
      (g := applyMapStepInput)
      hbase applyMapStepInput_computableIn
  exact hcomposed.of_eq fun _ ↦ rfl

omit [EffectivelyFiniteLanguage L] in
theorem applyMapList_computableIn :
    ComputableIn O fun q : (ℕ × List ℕ) × List ℕ ↦ C.applyMapList q.1.1 q.1.2 q.2 := by
  have hcons : ComputableIn₂ O
      fun (y : (((ℕ × List ℕ) × List ℕ) × (ℕ × Option (List ℕ))) × ℕ) (l : List ℕ) ↦
        y.2 :: l :=
    (((Computable.list_cons.computableIn₂ (O := O)).comp
      (ComputableIn.snd.comp ComputableIn.fst) ComputableIn.snd)).to₂
  have hmap : ComputableIn₂ O
      fun (x : ((ℕ × List ℕ) × List ℕ) × (ℕ × Option (List ℕ))) (b : ℕ) ↦
        x.2.2.map (b :: ·) :=
    (ComputableIn.option_map
      (ComputableIn.snd.comp (ComputableIn.snd.comp ComputableIn.fst)) hcons).to₂
  have hstep : ComputableIn₂ O
      fun (q : (ℕ × List ℕ) × List ℕ) (p : ℕ × Option (List ℕ)) ↦
        (C.applyMap q.1.1 q.1.2 p.1).bind fun b ↦ p.2.map (b :: ·) :=
    (ComputableIn.option_bind C.applyMapStep_computableIn hmap).to₂
  have h : ComputableIn O fun q : (ℕ × List ℕ) × List ℕ ↦
      q.2.foldr (fun a acc ↦ (C.applyMap q.1.1 q.1.2 a).bind fun b ↦ acc.map (b :: ·))
        (Option.some []) :=
    ComputableIn.list_foldr ComputableIn.snd (ComputableIn.const (Option.some [])) hstep
  exact h.of_eq fun q ↦ rfl

/-! ### Computability, rung 2: the instance enumerations

Total list computations off the fixed symbol lists. The packaged symbol stays opaque: its arity
is read through `primrec_functionSymbol_arity` rather than by destructuring the `Sigma`, which
is what every earlier `L.FunctionSymbol` stall in this file came from. -/

theorem funInstances_computableIn : ComputableIn O fun i : ℕ ↦ C.funInstances i := by
  have hsym : ComputableIn O fun _ : ℕ ↦ EffectivelyFiniteLanguage.functionSymbols (L := L) :=
    ComputableIn.const _
  have hsec : ComputableIn O fun p : ℕ × L.FunctionSymbol ↦
      (List.replicate p.2.arity (C.support p.1)).sections :=
    (Primrec.list_sections_replicate.to_comp.computableIn₂ (O := O)).comp
      ((primrec_functionSymbol_arity.to_comp.computableIn (O := O)).comp ComputableIn.snd)
      (C.support_computableIn.comp ComputableIn.fst)
  have hpair : ComputableIn₂ O fun (p : ℕ × L.FunctionSymbol) (as : List ℕ) ↦ (p.2, as) :=
    ((ComputableIn.snd.comp ComputableIn.fst).pair ComputableIn.snd).to₂
  have hmap : ComputableIn₂ O fun (i : ℕ) (s : L.FunctionSymbol) ↦
      ((List.replicate s.arity (C.support i)).sections.map fun as ↦ (s, as)) :=
    (ComputableIn.list_map hsec hpair).to₂
  have h : ComputableIn O fun i : ℕ ↦
      (EffectivelyFiniteLanguage.functionSymbols (L := L)).flatMap fun s ↦
        (List.replicate s.arity (C.support i)).sections.map fun as ↦ (s, as) :=
    ComputableIn.list_flatMap hsym hmap
  exact h.of_eq fun i ↦ rfl

theorem relInstances_computableIn : ComputableIn O fun i : ℕ ↦ C.relInstances i := by
  have hsym : ComputableIn O fun _ : ℕ ↦ EffectivelyFiniteLanguage.relationSymbols (L := L) :=
    ComputableIn.const _
  have hsec : ComputableIn O fun p : ℕ × L.RelationSymbol ↦
      (List.replicate p.2.arity (C.support p.1)).sections :=
    (Primrec.list_sections_replicate.to_comp.computableIn₂ (O := O)).comp
      ((primrec_relationSymbol_arity.to_comp.computableIn (O := O)).comp ComputableIn.snd)
      (C.support_computableIn.comp ComputableIn.fst)
  have hpair : ComputableIn₂ O fun (p : ℕ × L.RelationSymbol) (as : List ℕ) ↦ (p.2, as) :=
    ((ComputableIn.snd.comp ComputableIn.fst).pair ComputableIn.snd).to₂
  have hmap : ComputableIn₂ O fun (i : ℕ) (r : L.RelationSymbol) ↦
      ((List.replicate r.arity (C.support i)).sections.map fun as ↦ (r, as)) :=
    (ComputableIn.list_map hsec hpair).to₂
  have h : ComputableIn O fun i : ℕ ↦
      (EffectivelyFiniteLanguage.relationSymbols (L := L)).flatMap fun r ↦
        (List.replicate r.arity (C.support i)).sections.map fun as ↦ (r, as) :=
    ComputableIn.list_flatMap hsym hmap
  exact h.of_eq fun i ↦ rfl

/-! ### Computability, rung 2: the instance decoders

Assembly of both application data is **absolute** — `primrec_ofSymbolArgs?` lifted — and only
the middle argument-list lookup is `O`-relative. -/

/-- The decoder's repacking for `applyMapList`. -/
private def funInstanceMapInput (q : (ℕ × List ℕ) × (L.FunctionSymbol × List ℕ)) :
    (ℕ × List ℕ) × List ℕ := (q.1, q.2.2)

omit [EffectivelyFiniteLanguage L] in
private theorem funInstanceMapInput_computableIn :
    ComputableIn O (funInstanceMapInput (L := L)) :=
  (ComputableIn.fst.pair (ComputableIn.snd.comp ComputableIn.snd)).of_eq fun _ ↦ rfl

omit [EffectivelyFiniteLanguage L] in
private theorem funInstanceMapped_computableIn :
    ComputableIn O fun q : (ℕ × List ℕ) × (L.FunctionSymbol × List ℕ) ↦
      C.applyMapList q.1.1 q.1.2 q.2.2 := by
  have hbase : ComputableIn O fun r : (ℕ × List ℕ) × List ℕ ↦
      C.applyMapList r.1.1 r.1.2 r.2 := C.applyMapList_computableIn
  have hcomposed : ComputableIn O fun q : (ℕ × List ℕ) × (L.FunctionSymbol × List ℕ) ↦
      C.applyMapList (funInstanceMapInput (L := L) q).1.1
        (funInstanceMapInput (L := L) q).1.2 (funInstanceMapInput (L := L) q).2 :=
    ComputableIn.comp
      (α := (ℕ × List ℕ) × (L.FunctionSymbol × List ℕ))
      (β := (ℕ × List ℕ) × List ℕ)
      (σ := Option (List ℕ))
      (f := fun r ↦ C.applyMapList r.1.1 r.1.2 r.2)
      (g := funInstanceMapInput (L := L))
      hbase funInstanceMapInput_computableIn
  exact hcomposed.of_eq fun _ ↦ rfl

omit [EffectivelyFiniteLanguage L] in
theorem funInstance?_computableIn :
    ComputableIn O fun q : (ℕ × List ℕ) × (L.FunctionSymbol × List ℕ) ↦
      C.funInstance? q.1.1 q.1.2 q.2 := by
  have hsrcData : ComputableIn O fun q : (ℕ × List ℕ) × (L.FunctionSymbol × List ℕ) ↦
      FunctionApplicationData.ofSymbolArgs? q.2 :=
    FunctionApplicationData.ofSymbolArgs?_computableIn ComputableIn.snd
  have hpair : ComputableIn₂ O
      fun (z : (((ℕ × List ℕ) × (L.FunctionSymbol × List ℕ)) ×
        FunctionApplicationData L ℕ) × List ℕ) (e : FunctionApplicationData L ℕ) ↦
        (z.1.2, e) :=
    ((ComputableIn.snd.comp (ComputableIn.fst.comp ComputableIn.fst)).pair
      ComputableIn.snd).to₂
  have htgtData : ComputableIn O
      fun z : (((ℕ × List ℕ) × (L.FunctionSymbol × List ℕ)) ×
        FunctionApplicationData L ℕ) × List ℕ ↦
        FunctionApplicationData.ofSymbolArgs? (z.1.1.2.1, z.2) :=
    FunctionApplicationData.ofSymbolArgs?_computableIn
      ((ComputableIn.fst.comp
        (ComputableIn.snd.comp (ComputableIn.fst.comp ComputableIn.fst))).pair
        ComputableIn.snd)
  have hinner : ComputableIn₂ O
      fun (y : ((ℕ × List ℕ) × (L.FunctionSymbol × List ℕ)) ×
        FunctionApplicationData L ℕ) (bs : List ℕ) ↦
        (FunctionApplicationData.ofSymbolArgs? (y.1.2.1, bs)).map fun e ↦ (y.2, e) :=
    (ComputableIn.option_map htgtData hpair).to₂
  have houter : ComputableIn₂ O
      fun (q : (ℕ × List ℕ) × (L.FunctionSymbol × List ℕ))
        (d : FunctionApplicationData L ℕ) ↦
        (C.applyMapList q.1.1 q.1.2 q.2.2).bind fun bs ↦
          (FunctionApplicationData.ofSymbolArgs? (q.2.1, bs)).map fun e ↦ (d, e) :=
    (ComputableIn.option_bind (C.funInstanceMapped_computableIn.comp ComputableIn.fst)
      hinner).to₂
  have hbig : ComputableIn O fun q : (ℕ × List ℕ) × (L.FunctionSymbol × List ℕ) ↦
      (FunctionApplicationData.ofSymbolArgs? q.2).bind fun d ↦
        (C.applyMapList q.1.1 q.1.2 q.2.2).bind fun bs ↦
          (FunctionApplicationData.ofSymbolArgs? (q.2.1, bs)).map fun e ↦ (d, e) :=
    ComputableIn.option_bind hsrcData houter
  -- structure-valued `of_eq` stalls; cross the whole `Option (data × data)` through `encode`
  exact ComputableIn.of_encode_eq hbig fun _ ↦ rfl

/-- The relation decoder's repacking for `applyMapList`. -/
private def relInstanceMapInput (q : (ℕ × List ℕ) × (L.RelationSymbol × List ℕ)) :
    (ℕ × List ℕ) × List ℕ := (q.1, q.2.2)

omit [EffectivelyFiniteLanguage L] in
private theorem relInstanceMapInput_computableIn :
    ComputableIn O (relInstanceMapInput (L := L)) :=
  (ComputableIn.fst.pair (ComputableIn.snd.comp ComputableIn.snd)).of_eq fun _ ↦ rfl

omit [EffectivelyFiniteLanguage L] in
private theorem relInstanceMapped_computableIn :
    ComputableIn O fun q : (ℕ × List ℕ) × (L.RelationSymbol × List ℕ) ↦
      C.applyMapList q.1.1 q.1.2 q.2.2 := by
  have hbase : ComputableIn O fun r : (ℕ × List ℕ) × List ℕ ↦
      C.applyMapList r.1.1 r.1.2 r.2 := C.applyMapList_computableIn
  have hcomposed : ComputableIn O fun q : (ℕ × List ℕ) × (L.RelationSymbol × List ℕ) ↦
      C.applyMapList (relInstanceMapInput (L := L) q).1.1
        (relInstanceMapInput (L := L) q).1.2 (relInstanceMapInput (L := L) q).2 :=
    ComputableIn.comp
      (α := (ℕ × List ℕ) × (L.RelationSymbol × List ℕ))
      (β := (ℕ × List ℕ) × List ℕ)
      (σ := Option (List ℕ))
      (f := fun r ↦ C.applyMapList r.1.1 r.1.2 r.2)
      (g := relInstanceMapInput (L := L))
      hbase relInstanceMapInput_computableIn
  exact hcomposed.of_eq fun _ ↦ rfl

omit [EffectivelyFiniteLanguage L] in
theorem relInstance?_computableIn :
    ComputableIn O fun q : (ℕ × List ℕ) × (L.RelationSymbol × List ℕ) ↦
      C.relInstance? q.1.1 q.1.2 q.2 := by
  have hsrcData : ComputableIn O fun q : (ℕ × List ℕ) × (L.RelationSymbol × List ℕ) ↦
      RelationApplicationData.ofSymbolArgs? q.2 :=
    RelationApplicationData.ofSymbolArgs?_computableIn ComputableIn.snd
  have hpair : ComputableIn₂ O
      fun (z : (((ℕ × List ℕ) × (L.RelationSymbol × List ℕ)) ×
        RelationApplicationData L ℕ) × List ℕ) (e : RelationApplicationData L ℕ) ↦
        (z.1.2, e) :=
    ((ComputableIn.snd.comp (ComputableIn.fst.comp ComputableIn.fst)).pair
      ComputableIn.snd).to₂
  have htgtData : ComputableIn O
      fun z : (((ℕ × List ℕ) × (L.RelationSymbol × List ℕ)) ×
        RelationApplicationData L ℕ) × List ℕ ↦
        RelationApplicationData.ofSymbolArgs? (z.1.1.2.1, z.2) :=
    RelationApplicationData.ofSymbolArgs?_computableIn
      ((ComputableIn.fst.comp
        (ComputableIn.snd.comp (ComputableIn.fst.comp ComputableIn.fst))).pair
        ComputableIn.snd)
  have hinner : ComputableIn₂ O
      fun (y : ((ℕ × List ℕ) × (L.RelationSymbol × List ℕ)) ×
        RelationApplicationData L ℕ) (bs : List ℕ) ↦
        (RelationApplicationData.ofSymbolArgs? (y.1.2.1, bs)).map fun e ↦ (y.2, e) :=
    (ComputableIn.option_map htgtData hpair).to₂
  have houter : ComputableIn₂ O
      fun (q : (ℕ × List ℕ) × (L.RelationSymbol × List ℕ))
        (d : RelationApplicationData L ℕ) ↦
        (C.applyMapList q.1.1 q.1.2 q.2.2).bind fun bs ↦
          (RelationApplicationData.ofSymbolArgs? (q.2.1, bs)).map fun e ↦ (d, e) :=
    (ComputableIn.option_bind (C.relInstanceMapped_computableIn.comp ComputableIn.fst)
      hinner).to₂
  have hbig : ComputableIn O fun q : (ℕ × List ℕ) × (L.RelationSymbol × List ℕ) ↦
      (RelationApplicationData.ofSymbolArgs? q.2).bind fun d ↦
        (C.applyMapList q.1.1 q.1.2 q.2.2).bind fun bs ↦
          (RelationApplicationData.ofSymbolArgs? (q.2.1, bs)).map fun e ↦ (d, e) :=
    ComputableIn.option_bind hsrcData houter
  exact ComputableIn.of_encode_eq hbig fun _ ↦ rfl

/-! ### Computability, rung 3: the per-instance checks -/

/-- The instance repacking for the per-instance check. The fixed parameter is
`(i, j, f) : (ℕ × ℕ) × List ℕ`, which is also the shape `foldrPart₂` needs at the scan rung, so
no repacking layer appears between rungs 3 and 4a. -/
private def funCheckInstanceInput
    (q : ((ℕ × ℕ) × List ℕ) × (L.FunctionSymbol × List ℕ)) :
    (ℕ × List ℕ) × (L.FunctionSymbol × List ℕ) :=
  ((q.1.1.1, q.1.2), q.2)

omit [EffectivelyFiniteLanguage L] in
private theorem funCheckInstanceInput_computableIn :
    ComputableIn O (funCheckInstanceInput (L := L)) :=
  (((ComputableIn.fst.comp (ComputableIn.fst.comp ComputableIn.fst)).pair
    (ComputableIn.snd.comp ComputableIn.fst)).pair ComputableIn.snd).of_eq fun _ ↦ rfl

omit [EffectivelyFiniteLanguage L] in
/-- The decoded instance at the check's parameter shape. Needs **both** remedies: the input is a
projection repacking, and the result is structure-valued. -/
private theorem funCheckInstance_computableIn :
    ComputableIn O fun q : ((ℕ × ℕ) × List ℕ) × (L.FunctionSymbol × List ℕ) ↦
      C.funInstance? q.1.1.1 q.1.2 q.2 := by
  have hbase : ComputableIn O fun r : (ℕ × List ℕ) × (L.FunctionSymbol × List ℕ) ↦
      C.funInstance? r.1.1 r.1.2 r.2 := C.funInstance?_computableIn
  have hcomposed : ComputableIn O
      fun q : ((ℕ × ℕ) × List ℕ) × (L.FunctionSymbol × List ℕ) ↦
        C.funInstance? (funCheckInstanceInput (L := L) q).1.1
          (funCheckInstanceInput (L := L) q).1.2
          (funCheckInstanceInput (L := L) q).2 :=
    ComputableIn.comp
      (α := ((ℕ × ℕ) × List ℕ) × (L.FunctionSymbol × List ℕ))
      (β := (ℕ × List ℕ) × (L.FunctionSymbol × List ℕ))
      (σ := Option (FunctionApplicationData L ℕ × FunctionApplicationData L ℕ))
      (f := fun r ↦ C.funInstance? r.1.1 r.1.2 r.2)
      (g := funCheckInstanceInput (L := L))
      hbase funCheckInstanceInput_computableIn
  exact ComputableIn.of_encode_eq hcomposed fun _ ↦ rfl

/-- The instance repacking for the per-instance check. The fixed parameter is
`(i, j, f) : (ℕ × ℕ) × List ℕ`, which is also the shape `foldrPart₂` needs at the scan rung, so
no repacking layer appears between rungs 3 and 4a. -/
private def relCheckInstanceInput
    (q : ((ℕ × ℕ) × List ℕ) × (L.RelationSymbol × List ℕ)) :
    (ℕ × List ℕ) × (L.RelationSymbol × List ℕ) :=
  ((q.1.1.1, q.1.2), q.2)

omit [EffectivelyFiniteLanguage L] in
private theorem relCheckInstanceInput_computableIn :
    ComputableIn O (relCheckInstanceInput (L := L)) :=
  (((ComputableIn.fst.comp (ComputableIn.fst.comp ComputableIn.fst)).pair
    (ComputableIn.snd.comp ComputableIn.fst)).pair ComputableIn.snd).of_eq fun _ ↦ rfl

omit [EffectivelyFiniteLanguage L] in
/-- The decoded instance at the check's parameter shape. Needs **both** remedies: the input is a
projection repacking, and the result is structure-valued. -/
private theorem relCheckInstance_computableIn :
    ComputableIn O fun q : ((ℕ × ℕ) × List ℕ) × (L.RelationSymbol × List ℕ) ↦
      C.relInstance? q.1.1.1 q.1.2 q.2 := by
  have hbase : ComputableIn O fun r : (ℕ × List ℕ) × (L.RelationSymbol × List ℕ) ↦
      C.relInstance? r.1.1 r.1.2 r.2 := C.relInstance?_computableIn
  have hcomposed : ComputableIn O
      fun q : ((ℕ × ℕ) × List ℕ) × (L.RelationSymbol × List ℕ) ↦
        C.relInstance? (relCheckInstanceInput (L := L) q).1.1
          (relCheckInstanceInput (L := L) q).1.2
          (relCheckInstanceInput (L := L) q).2 :=
    ComputableIn.comp
      (α := ((ℕ × ℕ) × List ℕ) × (L.RelationSymbol × List ℕ))
      (β := (ℕ × List ℕ) × (L.RelationSymbol × List ℕ))
      (σ := Option (RelationApplicationData L ℕ × RelationApplicationData L ℕ))
      (f := fun r ↦ C.relInstance? r.1.1 r.1.2 r.2)
      (g := relCheckInstanceInput (L := L))
      hbase relCheckInstanceInput_computableIn
  exact ComputableIn.of_encode_eq hcomposed fun _ ↦ rfl

end ExactFiniteCarriers

end FirstOrder.Language
