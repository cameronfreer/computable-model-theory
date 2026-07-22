/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.DecidablePresentation
import ComputableModelTheory.ModelTheory.Computable.InitialSegmentPresentation

/-!
# Computable isomorphism of coded-domain presentations

CHMM Definition 2.3, over the Level-1 representation notion: a **computable
isomorphism** between c.e. presentations is a pair of partial maps, recursive in the
oracle, whose domains are *exactly* the presentation domains, inverse to each other
there, preserving function interpretations and preserving-and-reflecting relation
interpretations on realized pairs.

The structure carries only the forward-direction structure laws; the inverse-side
laws (`invFun_funMap`, `invFun_relMap`), injectivity, and surjectivity are derived.
Identity is the domain-restricted partial identity (through `firstIdxOf` — a total
identity would overclaim the domain), symmetry swaps the maps, and composition binds
them.

The semantic bridge: a presentation induces a structure on its domain subtype
(`subtypeStr`), and a computable isomorphism induces a first-order equivalence
(`toEquiv`) of the induced structures — noncomputably, by reading off the partial
maps' values.
-/

open Encodable Part FirstOrder Language

namespace FirstOrder.Language

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]

/-- A computable isomorphism of c.e. presentations: partial recursive back-and-forth
maps whose domains are exactly the presentation domains, mutually inverse there, with
the forward map preserving functions and preserving-and-reflecting relations. -/
structure CeIsoIn (P Q : CePresentationIn O L) where
  /-- The forward map. -/
  toFun : ℕ →. ℕ
  /-- The backward map. -/
  invFun : ℕ →. ℕ
  toFun_recursiveIn : RecursiveIn O toFun
  invFun_recursiveIn : RecursiveIn O invFun
  /-- The forward map halts exactly on the source domain. -/
  toFun_dom : ∀ x, (toFun x).Dom ↔ x ∈ P.domain
  /-- The backward map halts exactly on the target domain. -/
  invFun_dom : ∀ y, (invFun y).Dom ↔ y ∈ Q.domain
  /-- Forward values land in the target domain. -/
  toFun_mem : ∀ {x y}, y ∈ toFun x → y ∈ Q.domain
  /-- The backward map inverts the forward map. -/
  invFun_toFun : ∀ {x y}, y ∈ toFun x → x ∈ invFun y
  /-- The forward map inverts the backward map. -/
  toFun_invFun : ∀ {y x}, x ∈ invFun y → y ∈ toFun x
  /-- The forward map preserves function interpretations on realized pairs. -/
  toFun_funMap : ∀ (n : ℕ) (f : L.Functions n) (v w : Fin n → ℕ),
    (∀ k, w k ∈ toFun (v k)) →
      @Structure.funMap L ℕ Q.str n f w ∈ toFun (@Structure.funMap L ℕ P.str n f v)
  /-- The forward map preserves and reflects relation interpretations on realized
  pairs. -/
  toFun_relMap : ∀ (n : ℕ) (R : L.Relations n) (v w : Fin n → ℕ),
    (∀ k, w k ∈ toFun (v k)) →
      (@Structure.RelMap L ℕ Q.str n R w ↔ @Structure.RelMap L ℕ P.str n R v)

namespace CeIsoIn

variable {P Q W : CePresentationIn O L} (e : CeIsoIn P Q)

/-! ### Derived laws -/

theorem mem_domain_of_mem_toFun {x y : ℕ} (h : y ∈ e.toFun x) : x ∈ P.domain :=
  (e.toFun_dom x).1 (Part.dom_iff_mem.2 ⟨y, h⟩)

theorem invFun_mem {y x : ℕ} (h : x ∈ e.invFun y) : x ∈ P.domain :=
  e.mem_domain_of_mem_toFun (e.toFun_invFun h)

theorem mem_domain_of_mem_invFun {y x : ℕ} (h : x ∈ e.invFun y) : y ∈ Q.domain :=
  (e.invFun_dom y).1 (Part.dom_iff_mem.2 ⟨x, h⟩)

/-- The forward map is injective on realized pairs. -/
theorem toFun_injective {x₁ x₂ y : ℕ} (h₁ : y ∈ e.toFun x₁) (h₂ : y ∈ e.toFun x₂) :
    x₁ = x₂ :=
  Part.mem_unique (e.invFun_toFun h₁) (e.invFun_toFun h₂)

/-- The forward map is surjective onto the target domain. -/
theorem toFun_surjective {y : ℕ} (hy : y ∈ Q.domain) :
    ∃ x ∈ P.domain, y ∈ e.toFun x := by
  obtain ⟨x, hx⟩ := Part.dom_iff_mem.1 ((e.invFun_dom y).2 hy)
  exact ⟨x, e.invFun_mem hx, e.toFun_invFun hx⟩

/-- The inverse-side function law, derived. -/
theorem invFun_funMap (n : ℕ) (f : L.Functions n) (w v : Fin n → ℕ)
    (hv : ∀ k, v k ∈ e.invFun (w k)) :
    @Structure.funMap L ℕ P.str n f v ∈ e.invFun (@Structure.funMap L ℕ Q.str n f w) := by
  have hw : ∀ k, w k ∈ e.toFun (v k) := fun k ↦ e.toFun_invFun (hv k)
  exact e.invFun_toFun (e.toFun_funMap n f v w hw)

/-- The inverse-side relation law, derived. -/
theorem invFun_relMap (n : ℕ) (R : L.Relations n) (w v : Fin n → ℕ)
    (hv : ∀ k, v k ∈ e.invFun (w k)) :
    @Structure.RelMap L ℕ P.str n R v ↔ @Structure.RelMap L ℕ Q.str n R w :=
  (e.toFun_relMap n R v w fun k ↦ e.toFun_invFun (hv k)).symm

/-! ### Identity, symmetry, composition -/

/-- The domain-restricted partial identity: halts exactly on the domain, by searching
the enumeration. A total identity would overclaim the domain. -/
noncomputable def domId (P : CePresentationIn O L) : ℕ →. ℕ :=
  fun x ↦ (P.firstIdxOf x).map fun _ ↦ x

theorem domId_recursiveIn (P : CePresentationIn O L) :
    RecursiveIn O (domId P) :=
  RecursiveIn.map P.firstIdxOf_recursiveIn
    ((ComputableIn.fst).to₂ : ComputableIn₂ O fun (x : ℕ) (_ : ℕ) ↦ x)

theorem domId_dom (P : CePresentationIn O L) (x : ℕ) :
    ((domId P) x).Dom ↔ x ∈ P.domain :=
  P.firstIdxOf_dom_iff x

theorem mem_domId_iff {P : CePresentationIn O L} {x y : ℕ} :
    y ∈ domId P x ↔ x ∈ P.domain ∧ y = x := by
  rw [domId]
  constructor
  · intro h
    obtain ⟨i, hi, hy⟩ := (Part.mem_map_iff _).1 h
    exact ⟨(P.firstIdxOf_dom_iff x).1 (Part.dom_iff_mem.2 ⟨i, hi⟩), hy.symm⟩
  · rintro ⟨hx, rfl⟩
    obtain ⟨i, hi⟩ := Part.dom_iff_mem.1 ((P.firstIdxOf_dom_iff _).2 hx)
    exact (Part.mem_map_iff _).2 ⟨i, hi, rfl⟩

/-- The identity isomorphism. -/
noncomputable def refl (P : CePresentationIn O L) : CeIsoIn P P where
  toFun := domId P
  invFun := domId P
  toFun_recursiveIn := domId_recursiveIn P
  invFun_recursiveIn := domId_recursiveIn P
  toFun_dom := domId_dom P
  invFun_dom := domId_dom P
  toFun_mem := fun h ↦ ((mem_domId_iff.1 h).2 ▸ (mem_domId_iff.1 h).1)
  invFun_toFun := fun h ↦ by
    obtain ⟨hx, rfl⟩ := mem_domId_iff.1 h
    exact mem_domId_iff.2 ⟨hx, rfl⟩
  toFun_invFun := fun h ↦ by
    obtain ⟨hx, rfl⟩ := mem_domId_iff.1 h
    exact mem_domId_iff.2 ⟨hx, rfl⟩
  toFun_funMap := fun n f v w hw ↦ by
    have hv : ∀ k, v k ∈ P.domain ∧ w k = v k := fun k ↦ mem_domId_iff.1 (hw k)
    have hwv : w = v := funext fun k ↦ (hv k).2
    subst hwv
    exact mem_domId_iff.2
      ⟨P.domain_closed n f w fun k ↦ (hv k).1, rfl⟩
  toFun_relMap := fun n R v w hw ↦ by
    have hwv : w = v := funext fun k ↦ (mem_domId_iff.1 (hw k)).2
    rw [hwv]

/-- The inverse isomorphism. -/
def symm : CeIsoIn Q P where
  toFun := e.invFun
  invFun := e.toFun
  toFun_recursiveIn := e.invFun_recursiveIn
  invFun_recursiveIn := e.toFun_recursiveIn
  toFun_dom := e.invFun_dom
  invFun_dom := e.toFun_dom
  toFun_mem := fun h ↦ e.invFun_mem h
  invFun_toFun := fun h ↦ e.toFun_invFun h
  toFun_invFun := fun h ↦ e.invFun_toFun h
  toFun_funMap := fun n f v w hw ↦ e.invFun_funMap n f v w hw
  toFun_relMap := fun n R v w hw ↦ e.invFun_relMap n R v w hw

/-- Composition of isomorphisms. -/
def trans (e₁ : CeIsoIn P Q) (e₂ : CeIsoIn Q W) : CeIsoIn P W where
  toFun x := (e₁.toFun x).bind e₂.toFun
  invFun z := (e₂.invFun z).bind e₁.invFun
  toFun_recursiveIn :=
    RecursiveIn.bind e₁.toFun_recursiveIn
      ((e₂.toFun_recursiveIn.comp ComputableIn.snd).to₂)
  invFun_recursiveIn :=
    RecursiveIn.bind e₂.invFun_recursiveIn
      ((e₁.invFun_recursiveIn.comp ComputableIn.snd).to₂)
  toFun_dom := fun x ↦ by
    constructor
    · intro h
      obtain ⟨z, hz⟩ := Part.dom_iff_mem.1 h
      obtain ⟨y, hy, -⟩ := Part.mem_bind_iff.1 hz
      exact e₁.mem_domain_of_mem_toFun hy
    · intro hx
      obtain ⟨y, hy⟩ := Part.dom_iff_mem.1 ((e₁.toFun_dom x).2 hx)
      obtain ⟨z, hz⟩ :=
        Part.dom_iff_mem.1 ((e₂.toFun_dom y).2 (e₁.toFun_mem hy))
      exact Part.dom_iff_mem.2 ⟨z, Part.mem_bind_iff.2 ⟨y, hy, hz⟩⟩
  invFun_dom := fun z ↦ by
    constructor
    · intro h
      obtain ⟨x, hx⟩ := Part.dom_iff_mem.1 h
      obtain ⟨y, hy, -⟩ := Part.mem_bind_iff.1 hx
      exact e₂.mem_domain_of_mem_invFun hy
    · intro hz
      obtain ⟨y, hy⟩ := Part.dom_iff_mem.1 ((e₂.invFun_dom z).2 hz)
      obtain ⟨x, hx⟩ :=
        Part.dom_iff_mem.1 ((e₁.invFun_dom y).2 (e₂.invFun_mem hy))
      exact Part.dom_iff_mem.2 ⟨x, Part.mem_bind_iff.2 ⟨y, hy, hx⟩⟩
  toFun_mem := fun h ↦ by
    obtain ⟨y, -, hz⟩ := Part.mem_bind_iff.1 h
    exact e₂.toFun_mem hz
  invFun_toFun := fun h ↦ by
    obtain ⟨y, hy, hz⟩ := Part.mem_bind_iff.1 h
    exact Part.mem_bind_iff.2 ⟨y, e₂.invFun_toFun hz, e₁.invFun_toFun hy⟩
  toFun_invFun := fun h ↦ by
    obtain ⟨y, hy, hx⟩ := Part.mem_bind_iff.1 h
    exact Part.mem_bind_iff.2 ⟨y, e₁.toFun_invFun hx, e₂.toFun_invFun hy⟩
  toFun_funMap := fun n f v w hw ↦ by
    have hmid : ∀ k, ∃ y, y ∈ e₁.toFun (v k) ∧ w k ∈ e₂.toFun y :=
      fun k ↦ Part.mem_bind_iff.1 (hw k)
    choose u hu hwu using hmid
    exact Part.mem_bind_iff.2
      ⟨_, e₁.toFun_funMap n f v u hu, e₂.toFun_funMap n f u w hwu⟩
  toFun_relMap := fun n R v w hw ↦ by
    have hmid : ∀ k, ∃ y, y ∈ e₁.toFun (v k) ∧ w k ∈ e₂.toFun y :=
      fun k ↦ Part.mem_bind_iff.1 (hw k)
    choose u hu hwu using hmid
    exact (e₂.toFun_relMap n R u w hwu).trans (e₁.toFun_relMap n R v u hu)

/-! ### The semantic bridge -/

/-- The structure a presentation induces on its domain subtype — the semantic reading
of the coded data. -/
@[reducible]
def _root_.FirstOrder.Language.CePresentationIn.subtypeStr
    (P : CePresentationIn O L) : L.Structure P.domain where
  funMap {n} f v :=
    ⟨@Structure.funMap L ℕ P.str n f fun k ↦ (v k).1,
      P.domain_closed n f _ fun k ↦ (v k).2⟩
  RelMap {n} R v := @Structure.RelMap L ℕ P.str n R fun k ↦ (v k).1

instance (P : CePresentationIn O L) : L.Structure P.domain :=
  P.subtypeStr

/-- The subtype element a forward map assigns to a domain element. -/
noncomputable def toSubtypeFun (x : P.domain) : Q.domain :=
  ⟨(e.toFun x.1).get ((e.toFun_dom x.1).2 x.2), e.toFun_mem (Part.get_mem _)⟩

theorem toSubtypeFun_mem (x : P.domain) : (e.toSubtypeFun x).1 ∈ e.toFun x.1 :=
  Part.get_mem _

/-- The induced first-order equivalence of the induced structures: the semantic
content of a computable isomorphism. -/
noncomputable def toEquiv : P.domain ≃[L] Q.domain where
  toFun := e.toSubtypeFun
  invFun := e.symm.toSubtypeFun
  left_inv := fun x ↦ Subtype.ext
    (Part.mem_unique
      (e.symm.toSubtypeFun_mem (e.toSubtypeFun x))
      (e.invFun_toFun (e.toSubtypeFun_mem x)))
  right_inv := fun y ↦ Subtype.ext
    (Part.mem_unique
      (e.toSubtypeFun_mem (e.symm.toSubtypeFun y))
      (e.toFun_invFun (e.symm.toSubtypeFun_mem y)))
  map_fun' := fun {n} f v ↦ Subtype.ext
    (Part.mem_unique
      (e.toSubtypeFun_mem _)
      (e.toFun_funMap n f (fun k ↦ (v k).1) (fun k ↦ (e.toSubtypeFun (v k)).1)
        fun k ↦ e.toSubtypeFun_mem (v k)))
  map_rel' := fun {n} R v ↦
    e.toFun_relMap n R (fun k ↦ (v k).1) (fun k ↦ (e.toSubtypeFun (v k)).1)
      fun k ↦ e.toSubtypeFun_mem (v k)

end CeIsoIn

/-! ### The decidable-domain specialization -/

/-- A computable isomorphism of decidable-domain presentations: guarded **total**
maps, correct on the domains. -/
structure DecidableIsoIn (P Q : DecidablePresentationIn O L) where
  /-- The total forward map. -/
  toFunTotal : ℕ → ℕ
  /-- The total backward map. -/
  invFunTotal : ℕ → ℕ
  toFunTotal_computableIn : ComputableIn O toFunTotal
  invFunTotal_computableIn : ComputableIn O invFunTotal
  toFunTotal_mem : ∀ {x}, x ∈ P.domain → toFunTotal x ∈ Q.domain
  invFunTotal_mem : ∀ {y}, y ∈ Q.domain → invFunTotal y ∈ P.domain
  invFunTotal_toFunTotal : ∀ {x}, x ∈ P.domain → invFunTotal (toFunTotal x) = x
  toFunTotal_invFunTotal : ∀ {y}, y ∈ Q.domain → toFunTotal (invFunTotal y) = y
  toFunTotal_funMap : ∀ (n : ℕ) (f : L.Functions n) (v : Fin n → ℕ),
    (∀ k, v k ∈ P.domain) →
      toFunTotal (@Structure.funMap L ℕ P.str n f v)
        = @Structure.funMap L ℕ Q.str n f fun k ↦ toFunTotal (v k)
  toFunTotal_relMap : ∀ (n : ℕ) (R : L.Relations n) (v : Fin n → ℕ),
    (∀ k, v k ∈ P.domain) →
      (@Structure.RelMap L ℕ Q.str n R (fun k ↦ toFunTotal (v k)) ↔
        @Structure.RelMap L ℕ P.str n R v)

namespace DecidableIsoIn

variable {P Q : DecidablePresentationIn O L} (d : DecidableIsoIn P Q)

/-- Guard a total map by a decision procedure: halts exactly where the guard
accepts. -/
noncomputable def guard (b : ℕ → Bool) (f : ℕ → ℕ) : ℕ →. ℕ :=
  fun x ↦ (encode (!b x)).casesOn (motive := fun _ ↦ Part ℕ)
    (Part.some (f x)) fun _ ↦ Part.none

theorem guard_recursiveIn {b : ℕ → Bool} {f : ℕ → ℕ} (hb : ComputableIn O b)
    (hf : ComputableIn O f) : RecursiveIn O (guard b f) :=
  RecursiveIn.nat_casesOn_right
    (ComputableIn.encode.comp
      ((Primrec.not.to_comp.computableIn (O := O)).comp hb)) hf
    (((RecursiveIn.none (σ := ℕ)).comp
      (ComputableIn.fst (β := ℕ))).to₂)

theorem mem_guard_iff {b : ℕ → Bool} {f : ℕ → ℕ} {x y : ℕ} :
    y ∈ guard b f x ↔ b x = true ∧ y = f x := by
  rcases hb : b x with - | -
  · rw [guard, hb]
    show y ∈ (Part.none : Part ℕ) ↔ _
    simp
  · rw [guard, hb]
    show y ∈ Part.some (f x) ↔ _
    rw [Part.mem_some_iff]
    simp

theorem guard_dom_iff {b : ℕ → Bool} {f : ℕ → ℕ} {x : ℕ} :
    (guard b f x).Dom ↔ b x = true := by
  rw [Part.dom_iff_mem]
  constructor
  · rintro ⟨y, hy⟩
    exact (mem_guard_iff.1 hy).1
  · intro hb
    exact ⟨f x, mem_guard_iff.2 ⟨hb, rfl⟩⟩

/-- The inclusion into the c.e. isomorphism level: guard the total maps by the domain
deciders. -/
noncomputable def toCeIsoIn : CeIsoIn P.toCePresentation Q.toCePresentation where
  toFun := guard P.domainB d.toFunTotal
  invFun := guard Q.domainB d.invFunTotal
  toFun_recursiveIn := guard_recursiveIn P.domainB_computableIn
    d.toFunTotal_computableIn
  invFun_recursiveIn := guard_recursiveIn Q.domainB_computableIn
    d.invFunTotal_computableIn
  toFun_dom := fun x ↦ guard_dom_iff.trans
    ((P.mem_domain_iff).symm.trans (Set.ext_iff.1 P.toCePresentation_domain.symm x))
  invFun_dom := fun y ↦ guard_dom_iff.trans
    ((Q.mem_domain_iff).symm.trans (Set.ext_iff.1 Q.toCePresentation_domain.symm y))
  toFun_mem := fun h ↦ by
    obtain ⟨hb, rfl⟩ := mem_guard_iff.1 h
    rw [Q.toCePresentation_domain]
    exact d.toFunTotal_mem hb
  invFun_toFun := fun h ↦ by
    obtain ⟨hb, rfl⟩ := mem_guard_iff.1 h
    exact mem_guard_iff.2
      ⟨d.toFunTotal_mem hb, (d.invFunTotal_toFunTotal hb).symm⟩
  toFun_invFun := fun h ↦ by
    obtain ⟨hb, rfl⟩ := mem_guard_iff.1 h
    exact mem_guard_iff.2
      ⟨d.invFunTotal_mem hb, (d.toFunTotal_invFunTotal hb).symm⟩
  toFun_funMap := fun n f v w hw ↦ by
    have hv : ∀ k, P.domainB (v k) = true ∧ w k = d.toFunTotal (v k) :=
      fun k ↦ mem_guard_iff.1 (hw k)
    have hwv : w = fun k ↦ d.toFunTotal (v k) := funext fun k ↦ (hv k).2
    subst hwv
    refine mem_guard_iff.2 ⟨P.domain_closed n f v fun k ↦ (hv k).1, ?_⟩
    exact (d.toFunTotal_funMap n f v fun k ↦ (hv k).1).symm
  toFun_relMap := fun n R v w hw ↦ by
    have hv : ∀ k, P.domainB (v k) = true ∧ w k = d.toFunTotal (v k) :=
      fun k ↦ mem_guard_iff.1 (hw k)
    have hwv : w = fun k ↦ d.toFunTotal (v k) := funext fun k ↦ (hv k).2
    subst hwv
    exact d.toFunTotal_relMap n R v fun k ↦ (hv k).1

end DecidableIsoIn

/-! ### Uniform isomorphisms of indexed families -/

/-- A uniform family of computable isomorphisms: per-index isomorphisms **plus**
uniform-in-index recursiveness of both maps as explicit fields — one computability
proof per index does not provide this. -/
structure UniformCeIsoFamilyIn (P Q : ℕ → CePresentationIn O L) where
  /-- The per-index isomorphisms. -/
  isoAt : ∀ i, CeIsoIn (P i) (Q i)
  /-- The forward maps are recursive uniformly in the index. -/
  toFun_uniform : RecursiveIn O fun q : ℕ × ℕ ↦ (isoAt q.1).toFun q.2
  /-- The backward maps are recursive uniformly in the index. -/
  invFun_uniform : RecursiveIn O fun q : ℕ × ℕ ↦ (isoAt q.1).invFun q.2

/-! ### Canonicalization: relative, nonuniform, and uniform

Three sharply distinct statements. **Relative to the supplied enumeration**, every
Level-1 presentation is computably isomorphic to its rank presentation — the maps are
built from the given `enum`. **Nonuniformly**, an initial-segment presentation
carrying the rank data exists (#16's corollary; the shape is not computable from the
data). **Genuinely uniform** canonicalization of a family exists only under the
stronger hypothesis of uniform-in-index rank data, supplied as explicit fields — the
#16 obstruction rules out producing it from arbitrary Level-1 families. -/

namespace CePresentationIn

variable (P : CePresentationIn O L)

/-- Canonicalization relative to the supplied enumeration: the rank recoding is a
computable isomorphism. -/
noncomputable def rankIso : CeIsoIn P P.rankPresentation where
  toFun := P.rankOf
  invFun := P.rankEnum
  toFun_recursiveIn := P.rankOf_recursiveIn
  invFun_recursiveIn := P.rankEnum_recursiveIn
  toFun_dom := P.rankOf_dom_iff
  invFun_dom := fun r ↦ (P.rankEnum_dom_iff r).trans
    (P.rankIdx_dom_iff_mem_range_posRank r)
  toFun_mem := fun h ↦
    (P.rankIdx_dom_iff_mem_range_posRank _).1 (P.rankIdx_dom_of_mem_rankOf h)
  invFun_toFun := fun h ↦ P.mem_rankEnum_of_mem_rankOf h
  toFun_invFun := fun h ↦ P.rankOf_rankEnum h
  toFun_funMap := fun _ f v w hw ↦
    P.rankStr_funMap_mem_rankOf f w v fun k ↦ P.mem_rankEnum_of_mem_rankOf (hw k)
  toFun_relMap := fun _ R v w hw ↦
    P.rankStr_relMap_iff R w v fun k ↦ P.mem_rankEnum_of_mem_rankOf (hw k)

/-- Nonuniform canonicalization: some initial-segment presentation carries the rank
recoding, and the presentation is computably isomorphic to that recoding. The
initial-segment shape and its certificates are not computable from the data. -/
theorem exists_initialSegment_iso :
    ∃ Q : ComputableInitialSegmentPresentationIn O L,
      Q.str = P.rankPresentation.str ∧ Q.domain = P.rankPresentation.domain ∧
        Nonempty (CeIsoIn P P.rankPresentation) :=
  let ⟨Q, h₁, h₂⟩ := CePresentationIn.exists_initialSegment P
  ⟨Q, h₁, h₂, ⟨P.rankIso⟩⟩

end CePresentationIn

/-- Uniform-in-index rank data for a family: explicit input, per the certificate
discipline. Per-index rank recursiveness does not provide it. -/
structure UniformRankDataIn (P : ℕ → CePresentationIn O L) : Prop where
  rankOf_uniform : RecursiveIn O fun q : ℕ × ℕ ↦ (P q.1).rankOf q.2
  rankEnum_uniform : RecursiveIn O fun q : ℕ × ℕ ↦ (P q.1).rankEnum q.2

/-- Genuinely uniform canonicalization, under the stronger hypothesis: uniform rank
data yields a uniform family isomorphism onto the rank presentations. -/
noncomputable def uniformRankIsoFamily (P : ℕ → CePresentationIn O L)
    (h : UniformRankDataIn P) :
    UniformCeIsoFamilyIn P fun i ↦ (P i).rankPresentation where
  isoAt i := (P i).rankIso
  toFun_uniform := h.rankOf_uniform
  invFun_uniform := h.rankEnum_uniform

end FirstOrder.Language
