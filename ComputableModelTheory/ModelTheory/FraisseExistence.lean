/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.ExtensionRichDirectLimit
import ComputableModelTheory.ModelTheory.RepresentativeAge

/-! # Classical Fraïssé existence

A countable family of representatives with countable carriers, finitely generated, with
amalgamation and joint embedding, has a Fraïssé sequence (`exists_fraisseSequence`); with
hereditary closure, the direct limit of that sequence is a countable Fraïssé limit of the
representative class (`exists_isFraisseLimit_representativeClass`). For a Mathlib `IsFraisse` class
in a language with countably many function symbols, choosing one representative per isomorphism
class gives `exists_isFraisseLimit_of_isFraisse`; there finite generation supplies countable
carriers.

**The construction.** The stages are representatives. An enumeration of the outgoing embeddings
`Σ j, F i ↪[L] F j` of each representative is frozen in advance (identities make these types
inhabited even for empty carriers). At time `Nat.pair m k`, outgoing embedding `k` of stage `m` is
amalgamated against the literal composed transition from stage `m` to the current stage
(`Nat.left_le_pair` makes stage `m` already exist), and the next representative is then taken in by
joint embedding. The joint-embedding step is composed onto both legs, so the scheduled amalgamation
square survives it.

The recursion state records, for every earlier time, the transition into the current stage together
with its source representative, so that the state is non-dependent. One coherence lemma
(`chainState_snd`) identifies the recorded transition with the composite of the chain maps.

**Outputs.** The scheduled square and the coverage of every representative are proved separately
(`chain_square`, `chain_cover`), as `SequenceExtension` and coverage, before the direct limit is
packaged. The limit's carrier is the direct limit itself, in the representatives' universe — not
`ℕ`: finite and empty limits are allowed. Countable representative carriers are a premise: they are
what enumerates the outgoing embeddings (`Structure.FG.countable_embedding`); essential countability
of the class alone does not. Countability of the function symbols enters only at the
`IsFraisseLimit` packaging. This is classical existence, by choice; nothing here is effective.
-/

universe u v w z

namespace FirstOrder.Language

open CategoryTheory FirstOrder Structure

variable {L : Language.{u, v}}

/-! ### Composites of a chain -/

section NatLERec

variable {G : ℕ → Type w} [∀ n, L.Structure (G n)] (c : ∀ n, G n ↪[L] G (n + 1))

theorem natLERec_self (m : ℕ) : DirectedSystem.natLERec c m m le_rfl = Embedding.refl L (G m) := by
  ext x
  simp [DirectedSystem.coe_natLERec, Nat.leRecOn_self]

theorem natLERec_succ {m t : ℕ} (h : m ≤ t) :
    DirectedSystem.natLERec c m (t + 1) (h.trans t.le_succ) =
      (c t).comp (DirectedSystem.natLERec c m t h) := by
  ext x
  simp [DirectedSystem.coe_natLERec, Nat.leRecOn_succ h]

end NatLERec

variable {I : Type z} (F : I → Bundled.{w} L.Structure)

/-! ### One step: amalgamate a request, then take in a representative -/

/-- The data of one step from the current stage `F cur`: a next stage, the chain map into it, an
extension of the requested outgoing embedding `e` commuting with the transition `τ`, and an
embedding of the representative `F r` to be taken in. -/
structure StepData {i j cur : I} (e : F i ↪[L] F j) (τ : F i ↪[L] F cur) (r : I) where
  /-- The next stage. -/
  next : I
  /-- The chain map. -/
  map : F cur ↪[L] F next
  /-- The extension of the requested embedding. -/
  ext : F j ↪[L] F next
  /-- The scheduled amalgamation square. -/
  square : ext.comp e = map.comp τ
  /-- The representative taken in. -/
  cover : F r ↪[L] F next

/-- Amalgamation, then joint embedding, supplies a step; the joint-embedding map is composed onto
both legs of the amalgamation square. -/
theorem nonempty_stepData
    (hap : ∀ i j k (f : F i ↪[L] F j) (g : F i ↪[L] F k),
      ∃ (l : I) (a : F j ↪[L] F l) (b : F k ↪[L] F l), a.comp f = b.comp g)
    (hjep : ∀ i j, ∃ k, Nonempty (F i ↪[L] F k) ∧ Nonempty (F j ↪[L] F k))
    {i j cur : I} (e : F i ↪[L] F j) (τ : F i ↪[L] F cur) (r : I) :
    Nonempty (StepData F e τ r) := by
  obtain ⟨l, a, b, hab⟩ := hap i j cur e τ
  obtain ⟨k, ⟨p⟩, ⟨q⟩⟩ := hjep l r
  refine ⟨⟨k, p.comp b, p.comp a, ?_, q⟩⟩
  rw [Embedding.comp_assoc, hab, ← Embedding.comp_assoc]

/-- A choice of step for every request: the only use of AP and JEP. -/
abbrev Stepper : Type _ :=
  ∀ {i j cur : I} (e : F i ↪[L] F j) (τ : F i ↪[L] F cur) (r : I), StepData F e τ r

/-- The schedule: an enumeration of the representatives, and of the outgoing embeddings of each
representative into representatives. -/
structure Schedule where
  /-- The representative taken in at each step. -/
  rep : ℕ → I
  /-- The outgoing embeddings of each representative. -/
  out : ∀ i, ℕ → Σ j, F i ↪[L] F j

/-! ### The recursion -/

/-- The recursion state: the current representative and, for every time, a transition into it
recorded with its source representative. -/
abbrev ChainState : Type _ :=
  Σ cur : I, ℕ → Σ i, F i ↪[L] F cur

variable {F} (S : Stepper F) (σ : Schedule F)

/-- One step at time `t`: serve request `Nat.unpair t` against the recorded transition, take in
`σ.rep t`, and compose the new chain map onto every recorded transition. -/
noncomputable def chainStep (t : ℕ) (st : ChainState F) :
    Σ st' : ChainState F, F st.1 ↪[L] F st'.1 :=
  let x := st.2 t.unpair.1
  let d := S (σ.out x.1 t.unpair.2).2 x.2 (σ.rep t)
  ⟨⟨d.next, fun m ↦ if m = t + 1 then ⟨d.next, Embedding.refl L _⟩
    else ⟨(st.2 m).1, d.map.comp (st.2 m).2⟩⟩, d.map⟩

/-- The recursion states. -/
noncomputable def chainState : ℕ → ChainState F
  | 0 => ⟨σ.rep 0, fun _ ↦ ⟨σ.rep 0, Embedding.refl L _⟩⟩
  | t + 1 => (chainStep S σ t (chainState t)).1

/-- The representative at stage `n`. -/
noncomputable def chainIdx (n : ℕ) : I :=
  (chainState S σ n).1

/-- The chain map from stage `n` to stage `n + 1`. -/
noncomputable def chainMap (n : ℕ) : F (chainIdx S σ n) ↪[L] F (chainIdx S σ (n + 1)) :=
  (chainStep S σ n (chainState S σ n)).2

theorem chainState_succ_snd (t m : ℕ) :
    (chainState S σ (t + 1)).2 m = if m = t + 1 then ⟨chainIdx S σ (t + 1), Embedding.refl L _⟩
      else ⟨((chainState S σ t).2 m).1, (chainMap S σ t).comp ((chainState S σ t).2 m).2⟩ :=
  rfl

/-- **Coherence**: the transition recorded at time `t` for an earlier time `m` is the composite of
the chain maps, from its own stage. -/
theorem chainState_snd {t m : ℕ} (h : m ≤ t) :
    (chainState S σ t).2 m = ⟨chainIdx S σ m, DirectedSystem.natLERec (chainMap S σ) m t h⟩ := by
  induction t generalizing m with
  | zero =>
    obtain rfl := Nat.le_zero.mp h
    rw [natLERec_self]
    rfl
  | succ t ih =>
    rw [chainState_succ_snd]
    split_ifs with hm
    · subst hm
      rw [natLERec_self]
    · have hmt : m ≤ t := Nat.le_of_lt_succ (lt_of_le_of_ne h hm)
      rw [ih hmt, natLERec_succ (chainMap S σ) hmt]

/-- The step's square, for an arbitrary recorded transition and request. -/
theorem chainStep_square (t : ℕ) (x : Σ i, F i ↪[L] F (chainIdx S σ t))
    (hx : (chainState S σ t).2 t.unpair.1 = x) (r : Σ j, F x.1 ↪[L] F j)
    (hr : σ.out x.1 t.unpair.2 = r) :
    ∃ g : F r.1 ↪[L] F (chainIdx S σ (t + 1)), g.comp r.2 = (chainMap S σ t).comp x.2 := by
  subst hx hr
  exact ⟨_, (S _ _ (σ.rep t)).square⟩

/-! ### The two outputs: the scheduled square and coverage -/

/-- **The scheduled square.** If outgoing embedding `k` of stage `m`'s representative is `e`, then
at time `Nat.pair m k` it is extended along the composed transition from stage `m`. -/
theorem chain_square (m k : ℕ) {j : I} (e : F (chainIdx S σ m) ↪[L] F j)
    (he : σ.out (chainIdx S σ m) k = ⟨j, e⟩) :
    ∃ g : F j ↪[L] F (chainIdx S σ (Nat.pair m k + 1)),
      g.comp e = DirectedSystem.natLERec (chainMap S σ) m (Nat.pair m k + 1)
        ((Nat.left_le_pair m k).trans (Nat.le_succ _)) := by
  have hmt := Nat.left_le_pair m k
  rw [natLERec_succ (chainMap S σ) hmt]
  have hu := Nat.unpair_pair m k
  exact chainStep_square S σ _ ⟨chainIdx S σ m, DirectedSystem.natLERec (chainMap S σ) m _ hmt⟩
    (by rw [hu]; exact chainState_snd S σ hmt) ⟨j, e⟩ (by rw [hu]; exact he)

/-- **Coverage**: the representative `σ.rep t` embeds in stage `t + 1`. -/
theorem chain_cover (t : ℕ) : Nonempty (F (σ.rep t) ↪[L] F (chainIdx S σ (t + 1))) :=
  ⟨(S _ _ (σ.rep t)).cover⟩

/-! ### Fraïssé sequences and limits -/

variable (F)

/-- **A Fraïssé sequence exists.** For a countable, inhabited family of finitely generated
representatives with countable carriers, AP and JEP, there are stages and chain maps such that
every representative embeds in a stage and the whole-stage extension property holds against the
representative class. No hereditary closure is used. -/
theorem exists_fraisseSequence [Countable I] [Nonempty I] [∀ i, Countable (F i)]
    (hfg : ∀ i, Structure.FG L (F i))
    (hjep : ∀ i j, ∃ k, Nonempty (F i ↪[L] F k) ∧ Nonempty (F j ↪[L] F k))
    (hap : ∀ i j k (f : F i ↪[L] F j) (g : F i ↪[L] F k),
      ∃ (l : I) (a : F j ↪[L] F l) (b : F k ↪[L] F l), a.comp f = b.comp g) :
    ∃ (s : ℕ → I) (c : ∀ n, F (s n) ↪[L] F (s (n + 1))),
      (∀ r, ∃ n, Nonempty (F r ↪[L] F (s n))) ∧
      SequenceExtension (G := fun n ↦ F (s n)) (fun i j h ↦ DirectedSystem.natLERec c i j h)
        (representativeClass F) := by
  classical
  obtain ⟨rep, hrep⟩ := exists_surjective_nat I
  have hout : ∀ i, ∃ out : ℕ → Σ j, F i ↪[L] F j, Function.Surjective out := fun i ↦ by
    have : ∀ j, Countable (F i ↪[L] F j) := fun j ↦ (hfg i).countable_embedding (F j)
    have : Nonempty (Σ j, F i ↪[L] F j) := ⟨⟨i, Embedding.refl L _⟩⟩
    exact exists_surjective_nat _
  choose out hout using hout
  let S : Stepper F := fun e τ r ↦ (nonempty_stepData F hap hjep e τ r).some
  let σ : Schedule F := ⟨rep, out⟩
  refine ⟨chainIdx S σ, chainMap S σ, fun r ↦ ?_, ?_⟩
  · obtain ⟨t, rfl⟩ := hrep r
    exact ⟨t + 1, chain_cover S σ t⟩
  · rintro m N ⟨l, ⟨u⟩⟩ e
    obtain ⟨k, hk⟩ := hout (chainIdx S σ m) ⟨l, u.toEmbedding.comp e⟩
    obtain ⟨g, hg⟩ := chain_square S σ m k _ hk
    refine ⟨Nat.pair m k + 1, (Nat.left_le_pair m k).trans (Nat.le_succ _),
      g.comp u.toEmbedding, ?_⟩
    rw [Embedding.comp_assoc, hg]

/-- **Classical Fraïssé existence.** A countable, inhabited family of finitely generated
representatives with countable carriers, hereditary closure, JEP and AP has a countable Fraïssé
limit of its representative class, in the representatives' universe. The carrier is a direct limit,
not necessarily `ℕ`; it may be finite or empty. -/
theorem exists_isFraisseLimit_representativeClass [Countable (Σ n, L.Functions n)] [Countable I]
    [Nonempty I] [∀ i, Countable (F i)] (hfg : ∀ i, Structure.FG L (F i))
    (hsub : ∀ i (S : L.Substructure (F i)), S.FG → ∃ j, Nonempty (S ≃[L] F j))
    (hjep : ∀ i j, ∃ k, Nonempty (F i ↪[L] F k) ∧ Nonempty (F j ↪[L] F k))
    (hap : ∀ i j k (f : F i ↪[L] F j) (g : F i ↪[L] F k),
      ∃ (l : I) (a : F j ↪[L] F l) (b : F k ↪[L] F l), a.comp f = b.comp g) :
    ∃ (M : Bundled.{w} L.Structure) (_ : Countable M),
      IsFraisseLimit (representativeClass F) M := by
  obtain ⟨s, c, hcov, hext⟩ := exists_fraisseSequence F hfg hjep hap
  have : Countable (Language.DirectLimit (fun n ↦ F (s n))
      (fun i j h ↦ DirectedSystem.natLERec c i j h)) :=
    countable_directLimit _ _
  refine ⟨⟨Language.DirectLimit (fun n ↦ F (s n)) (fun i j h ↦ DirectedSystem.natLERec c i j h),
    inferInstance⟩, this, ?_⟩
  exact isFraisseLimit_directLimit _ _ (fun n ↦ mem_representativeClass F (s n))
    (representativeClass_hereditary F hsub) (representativeClass_amalgamation F hap)
    (fun _ h ↦ representativeClass_fg F hfg h)
    (fun N ⟨l, ⟨u⟩⟩ ↦ (hcov l).imp fun _ ⟨g⟩ ↦ ⟨g.comp u.toEmbedding⟩) hext

/-! ### From a Fraïssé class -/

section IsFraisse

variable {K : Set (Bundled.{w} L.Structure)}

/-- One chosen representative of each isomorphism class in `K`. -/
noncomputable def classRep (K : Set (Bundled.{w} L.Structure))
    (q : (Quotient.mk' '' K : Set (Quotient (equivSetoid (L := L))))) : Bundled.{w} L.Structure :=
  q.1.out

theorem classRep_mem [hK : IsFraisse K] (q : (Quotient.mk' '' K : Set (Quotient equivSetoid))) :
    classRep K q ∈ K := by
  obtain ⟨M, hM, hq⟩ := q.2
  have hn : Nonempty (classRep K q ≃[L] M) := by
    rw [classRep, ← hq]
    exact Quotient.mk_out (s := equivSetoid) M
  exact (hK.is_equiv_invariant hn).2 hM

/-- Every member of `K` is isomorphic to a chosen representative. -/
theorem exists_equiv_classRep {M : Bundled.{w} L.Structure} (hM : M ∈ K) :
    ∃ q, Nonempty (M ≃[L] classRep K q) :=
  ⟨⟨Quotient.mk' M, M, hM, rfl⟩, ⟨(Quotient.mk_out (s := equivSetoid) M).some.symm⟩⟩

/-- A Fraïssé class is the representative class of its chosen representatives. -/
theorem eq_representativeClass_classRep [hK : IsFraisse K] :
    K = representativeClass (classRep K) := by
  ext M
  exact ⟨exists_equiv_classRep, fun ⟨q, hq⟩ ↦ (hK.is_equiv_invariant hq).2 (classRep_mem q)⟩

/-- **Existence for a Fraïssé class.** Every Fraïssé class in a language with countably many
function symbols has a countable Fraïssé limit, in its own universe. Countable carriers are not a
separate premise here: a finitely generated structure in such a language is countable. -/
theorem exists_isFraisseLimit_of_isFraisse [Countable (Σ n, L.Functions n)]
    (K : Set (Bundled.{w} L.Structure)) [hK : IsFraisse K] :
    ∃ (M : Bundled.{w} L.Structure) (_ : Countable M), IsFraisseLimit K M := by
  have hKF := eq_representativeClass_classRep (K := K)
  have : Countable (Quotient.mk' '' K : Set (Quotient (equivSetoid (L := L)))) :=
    hK.is_essentially_countable.to_subtype
  have : Nonempty (Quotient.mk' '' K : Set (Quotient (equivSetoid (L := L)))) := by
    obtain ⟨M, hM⟩ := hK.is_nonempty
    exact ⟨⟨Quotient.mk' M, M, hM, rfl⟩⟩
  have hfg : ∀ q, Structure.FG L (classRep K q) := fun q ↦ hK.FG _ (classRep_mem q)
  have : ∀ q, Countable (classRep K q) := fun q ↦ Structure.cg_iff_countable.1 (hfg q).cg
  obtain ⟨M, hM, hlim⟩ := exists_isFraisseLimit_representativeClass (classRep K) hfg
    (fun q S hS ↦ exists_equiv_classRep (hK.hereditary _ (classRep_mem q) (age.fg_substructure hS)))
    (fun i j ↦ by
      obtain ⟨P, hP, ⟨a⟩, ⟨b⟩⟩ := hK.jointEmbedding _ (classRep_mem i) _ (classRep_mem j)
      obtain ⟨k, ⟨u⟩⟩ := exists_equiv_classRep hP
      exact ⟨k, ⟨u.toEmbedding.comp a⟩, ⟨u.toEmbedding.comp b⟩⟩)
    (fun i j k f g ↦ by
      obtain ⟨Q, a, b, hQ, hab⟩ := hK.amalgamation _ _ _ f g (classRep_mem i) (classRep_mem j)
        (classRep_mem k)
      obtain ⟨l, ⟨u⟩⟩ := exists_equiv_classRep hQ
      exact ⟨l, u.toEmbedding.comp a, u.toEmbedding.comp b, by
        rw [Embedding.comp_assoc, hab, ← Embedding.comp_assoc]⟩)
  rw [← hKF] at hlim
  exact ⟨M, hM, hlim⟩

end IsFraisse

end FirstOrder.Language
