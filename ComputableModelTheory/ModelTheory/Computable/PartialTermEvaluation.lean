/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.PartialAge
import ComputableModelTheory.ModelTheory.Computable.UniformAtomic

/-!
# Partial term evaluation over an empty-capable family

Term evaluation in a `PartialAgeIn`: the member's function interpretation is only a
**partial** evaluator, correct on-domain, so the value-stack machine of
`ComputableAgeIn.termValueStack` must run inside `Part`. Its engine is the partial fold
`foldrPart`.

Variables are natural numbers and the environment is a `Tuple ℕ` read by
`ComputableAgeIn.envFun` — deliberately the same reading as the total uniform evaluator,
so the `restrictVar`/`relabel` bridge transfers verbatim. Fixing the variable type at `ℕ`
keeps the stack's element type `ℕ ⊕ Σ n, L.Functions n` — a single `Primcodable` type
independent of any arity — which is what `foldrPart₂` folds over.

Two shape decisions record the fact that the machine is **partial**, not merely a total
machine run inside `Part`:

* a variable lookup is *undefined* off the end of the environment, rather than reading a
  default; so a halting run certifies `Term.VarsBelow env.length` for the term
  (`varsBelow_of_partialRealize_dom`) — a statement about the term traversal under an
  on-domain environment, not a claim about off-domain evaluator behavior;
* a completed stack is accepted only when it holds **exactly one** value
  (`soleStackValue`, characterized by `soleStackValue_eq_some_iff`). Arity mismatch and
  argument underflow leave the step undefined instead of resetting the stack, and there
  is no `head?`-style fallback that would read a malformed stack.

Correctness runs in the on-domain direction only. Under an on-domain environment and
bounded variables the machine halts with exactly the ordinary realization
(`partialRealize_eq_some`), which then lies in the member's carrier
(`partialRealize_mem_domainAt`) by the family's derived domain-closure. Nothing is
claimed about the stored evaluators off-domain.
-/

open Encodable Part FirstOrder Language

namespace FirstOrder.Language

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]

namespace Term

omit [L.EffectiveLanguage] in
/-- A variable term is bounded exactly when its letter is. -/
theorem varsBelow_var_iff {k n : ℕ} : VarsBelow (L := L) k (Term.var n) ↔ n < k := by
  simp [VarsBelow, varFinset]

omit [L.EffectiveLanguage] in
/-- Bounded variables pass to the arguments of an application. -/
theorem VarsBelow.func_arg {k n : ℕ} {f : L.Functions n} {ts : Fin n → L.Term ℕ}
    (h : VarsBelow k (Term.func f ts)) (j : Fin n) : VarsBelow k (ts j) := by
  intro v hv
  exact h v (by simp only [varFinset, Finset.mem_biUnion, Finset.mem_univ, true_and]; exact ⟨j, hv⟩)

section Bridge

variable [L.Structure ℕ]

omit [L.EffectiveLanguage] in
/-- A relabeled `Fin`-variable term realizes over the list environment as it does over the
tuple view — the `relabel` half of the bridge, at any structure on `ℕ`. -/
theorem realize_envFun_relabel_val {k : ℕ} {env : Tuple ℕ} (hk : env.length = k)
    (t : L.Term (Fin k)) :
    (t.relabel Fin.val).realize (ComputableAgeIn.envFun env) =
      t.realize fun x : Fin k ↦ env.view (Fin.cast hk.symm x) := by
  rw [Term.realize_relabel]
  congr 1
  funext x
  show (env[(x : ℕ)]?).getD 0 = env.get (Fin.cast hk.symm x)
  rw [List.getElem?_eq_getElem (show (x : ℕ) < env.length by omega)]
  rfl

omit [L.EffectiveLanguage] in
/-- A bounded natural-variable term realizes over the list environment as its restriction
does over the tuple view — the `restrictVar` half of the bridge, at any structure on
`ℕ`. -/
theorem realize_envFun_restrictVar {k : ℕ} {env : Tuple ℕ} (hk : env.length = k)
    (t : L.Term ℕ) (hv : VarsBelow k t) :
    t.realize (ComputableAgeIn.envFun env) =
      (t.restrictVar fun x ↦ (⟨x.1, hv x.1 x.2⟩ : Fin k)).realize
        fun x : Fin k ↦ env.view (Fin.cast hk.symm x) := by
  refine (Term.realize_restrictVar (ComputableAgeIn.envFun env) fun v ↦ ?_).symm
  show env.get (Fin.cast hk.symm _) = (env[(v : ℕ)]?).getD 0
  rw [List.getElem?_eq_getElem (show (v : ℕ) < env.length by
    have := hv v.1 v.2
    omega)]
  rfl

end Bridge

end Term

namespace FunctionApplicationData

omit [L.EffectiveLanguage] in
/-- Application data assembled from a symbol and the listed values of a `Fin`-indexed
tuple evaluates to the ordinary interpretation of that tuple. -/
theorem funMap_equivSubtype_symm_map_finRange {M : Type*} [L.Structure M] {n : ℕ}
    (f : L.Functions n) (w : Fin n → M)
    (h : ((List.finRange n).map w).length =
      FunctionSymbol.arity (⟨n, f⟩ : L.FunctionSymbol)) :
    (equivSubtype.symm ⟨((⟨n, f⟩ : L.FunctionSymbol), (List.finRange n).map w), h⟩).funMap =
      Structure.funMap f w := by
  rw [funMap_equivSubtype_symm]
  exact congrArg _ (funext fun k ↦ by
    rw [List.get_eq_getElem, List.getElem_map, List.getElem_finRange]
    exact congrArg w (Fin.ext rfl))

end FunctionApplicationData

/-- Acceptance of a completed value stack: the value of a stack holding **exactly one**
value, and nothing otherwise. The length guard is checked before the head is read, so a
malformed stack is rejected rather than truncated. -/
def soleStackValue (vs : List ℕ) : Option ℕ :=
  if vs.length = 1 then vs.head? else none

@[simp]
theorem soleStackValue_singleton (v : ℕ) : soleStackValue [v] = Option.some v :=
  rfl

/-- Acceptance is exactly the singleton shape. -/
theorem soleStackValue_eq_some_iff {vs : List ℕ} {v : ℕ} :
    soleStackValue vs = Option.some v ↔ vs = [v] := by
  match vs with
  | [] => simp [soleStackValue]
  | [_] => simp [soleStackValue]
  | _ :: _ :: _ => simp [soleStackValue]

namespace PartialAgeIn

variable (A : PartialAgeIn O L)

/-! ### The partial value-stack machine -/

/-- One step of the partial value-stack machine at member `i`: a variable pushes its
environment entry and is **undefined** off the end of the environment; a function symbol
consumes its arity in values through the uniform application data and calls the family's
partial evaluator. Arity mismatch — in particular argument underflow — leaves the step
undefined; there is no resetting fallback. -/
def partialValueStep (i : ℕ) (env : Tuple ℕ) (g : ℕ ⊕ (Σ j, L.Functions j))
    (acc : List ℕ) : Part (List ℕ) :=
  match g with
  | Sum.inl n => ((env[n]? : Option ℕ) : Part ℕ).map (· :: acc)
  | Sum.inr s =>
    (((FunctionApplicationData.ofSymbolArgs? ((s, acc.take s.1) :
        L.FunctionSymbol × List ℕ) : Option (FunctionApplicationData L ℕ)) :
      Part (FunctionApplicationData L ℕ)).bind
        fun d ↦ (A.funEval i d).map (· :: acc.drop s.1))

/-- The partial value-stack machine: the partial fold of the step over the symbol list. -/
def partialValueStack (i : ℕ) (env : Tuple ℕ)
    (l : List (ℕ ⊕ (Σ j, L.Functions j))) : Part (List ℕ) :=
  foldrPart (A.partialValueStep i env) [] l

/-- Partial uniform term evaluation: run the machine on the term's code and accept only a
one-value stack. -/
def partialRealize (i : ℕ) (env : Tuple ℕ) (t : L.Term ℕ) : Part ℕ :=
  (A.partialValueStack i env t.listEncode).bind fun vs ↦
    ((soleStackValue vs : Option ℕ) : Part ℕ)

@[simp]
theorem partialValueStack_nil (i : ℕ) (env : Tuple ℕ) :
    A.partialValueStack i env [] = Part.some [] :=
  rfl

theorem partialValueStack_cons (i : ℕ) (env : Tuple ℕ) (g : ℕ ⊕ (Σ j, L.Functions j))
    (l : List (ℕ ⊕ (Σ j, L.Functions j))) :
    A.partialValueStack i env (g :: l) =
      (A.partialValueStack i env l).bind fun acc ↦ A.partialValueStep i env g acc :=
  foldrPart_cons _ _ _ _

/-! ### On-domain correctness -/

variable {A}

/-- A bounded term realizes into the member's carrier over an on-domain environment: the
generation law's derived domain-closure, run up the term. -/
theorem realize_mem_domainAt {i : ℕ} {env : Tuple ℕ}
    (henv : ∀ x ∈ env, x ∈ A.domainAt i) :
    ∀ {t : L.Term ℕ}, Term.VarsBelow env.length t →
      @Term.realize L ℕ (A.structureAt i) ℕ (ComputableAgeIn.envFun env) t ∈
        A.domainAt i := by
  letI : L.Structure ℕ := A.structureAt i
  intro t
  induction t with
  | var n =>
    intro ht
    have hn : n < env.length := Term.varsBelow_var_iff.1 ht
    show ComputableAgeIn.envFun env n ∈ A.domainAt i
    rw [ComputableAgeIn.envFun, List.getElem?_eq_getElem hn, Option.getD_some]
    exact henv _ (List.getElem_mem hn)
  | @func n f ts ih =>
    intro ht
    rw [Term.realize_func]
    exact A.domainAt_closed f fun k ↦ ih k (ht.func_arg k)

/-- The machine equation, in the form the induction needs: running the machine on a term's
code prepended to any tail pushes exactly the term's value onto the tail's stack. -/
theorem partialValueStack_listEncode_append {i : ℕ} {env : Tuple ℕ}
    (henv : ∀ x ∈ env, x ∈ A.domainAt i) :
    ∀ (t : L.Term ℕ), Term.VarsBelow env.length t →
      ∀ l : List (ℕ ⊕ (Σ j, L.Functions j)),
        A.partialValueStack i env (t.listEncode ++ l) =
          (A.partialValueStack i env l).map fun acc ↦
            @Term.realize L ℕ (A.structureAt i) ℕ (ComputableAgeIn.envFun env) t :: acc := by
  letI : L.Structure ℕ := A.structureAt i
  intro t
  induction t with
  | var n =>
    intro ht l
    have hn : n < env.length := Term.varsBelow_var_iff.1 ht
    have hstep : ∀ acc : List ℕ, A.partialValueStep i env (Sum.inl n) acc =
        Part.some (ComputableAgeIn.envFun env n :: acc) := by
      intro acc
      show ((env[n]? : Option ℕ) : Part ℕ).map (· :: acc) = _
      rw [List.getElem?_eq_getElem hn]
      show Part.some (env[n] :: acc) = _
      rw [ComputableAgeIn.envFun, List.getElem?_eq_getElem hn, Option.getD_some]
    rw [Term.listEncode, List.singleton_append, A.partialValueStack_cons]
    simp only [hstep]
    exact Part.bind_some_eq_map _ _
  | @func n f ts ih =>
    intro ht l
    set v : ℕ → ℕ := ComputableAgeIn.envFun env with hv
    set vs : List ℕ := (List.finRange n).map fun j ↦ (ts j).realize v with hvs
    have hvslen : vs.length = n := by simp [hvs]
    have hvsdom : ∀ x ∈ vs, x ∈ A.domainAt i := by
      intro x hx
      obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
      exact realize_mem_domainAt henv (ht.func_arg j)
    -- the arguments already on the stack, for any tail
    have hinner : ∀ js : List (Fin n),
        A.partialValueStack i env ((js.flatMap fun j ↦ (ts j).listEncode) ++ l) =
          (A.partialValueStack i env l).map fun acc ↦
            (js.map fun j ↦ (ts j).realize v) ++ acc := by
      intro js
      induction js with
      | nil =>
        rw [List.flatMap_nil, List.nil_append]
        exact (Part.map_id' (fun _ ↦ rfl) _).symm
      | cons j js ihjs =>
        rw [List.flatMap_cons, List.append_assoc, ih j (ht.func_arg j), ihjs,
          Part.map_map]
        rfl
    -- one function step on a stack whose top holds exactly the arguments
    have hstep : ∀ acc : List ℕ,
        A.partialValueStep i env (Sum.inr (⟨n, f⟩ : Σ j, L.Functions j)) (vs ++ acc) =
          Part.some ((Term.func f ts).realize v :: acc) := by
      intro acc
      have harity : vs.length = FunctionSymbol.arity (⟨n, f⟩ : L.FunctionSymbol) := hvslen
      have htake : (vs ++ acc).take n = vs := List.take_left' hvslen
      have hdrop : (vs ++ acc).drop n = acc := List.drop_left' hvslen
      show (((FunctionApplicationData.ofSymbolArgs?
          (((⟨n, f⟩ : L.FunctionSymbol), (vs ++ acc).take n)) :
        Option (FunctionApplicationData L ℕ)) : Part (FunctionApplicationData L ℕ)).bind
          fun d ↦ (A.funEval i d).map (· :: (vs ++ acc).drop n)) = _
      rw [show ((vs ++ acc).take n) = vs from htake, show ((vs ++ acc).drop n) = acc from hdrop,
        FunctionApplicationData.ofSymbolArgs?_of_length_eq _ harity]
      set d : FunctionApplicationData L ℕ :=
        FunctionApplicationData.equivSubtype.symm ⟨((⟨n, f⟩ : L.FunctionSymbol), vs), harity⟩
        with hd
      have hdargs : ∀ k, d.args k ∈ A.domainAt i := by
        intro k
        exact hvsdom _ (vs.get_mem _)
      have hfun : A.funEval i d = Part.some d.funMap :=
        Part.eq_some_iff.2 (A.funEval_correct i d fun k ↦ hdargs k)
      have hdval : d.funMap = (Term.func f ts).realize v := by
        rw [hd, Term.realize_func]
        exact FunctionApplicationData.funMap_equivSubtype_symm_map_finRange f
          (fun j ↦ (ts j).realize v) harity
      show (Part.some d).bind (fun e ↦ (A.funEval i e).map (· :: acc)) = _
      rw [Part.bind_some, hfun, hdval]
      rfl
    rw [Term.listEncode, List.cons_append, A.partialValueStack_cons, hinner (List.finRange n),
      Part.bind_map]
    simp only [← hvs, hstep]
    exact Part.bind_some_eq_map _ _

/-- The machine equation: on an on-domain environment and a bounded term, the stack halts
with exactly one value, the term's realization. -/
theorem partialValueStack_listEncode {i : ℕ} {env : Tuple ℕ} {t : L.Term ℕ}
    (henv : ∀ x ∈ env, x ∈ A.domainAt i) (ht : Term.VarsBelow env.length t) :
    A.partialValueStack i env t.listEncode =
      Part.some [@Term.realize L ℕ (A.structureAt i) ℕ (ComputableAgeIn.envFun env) t] := by
  have h := partialValueStack_listEncode_append henv t ht []
  rw [List.append_nil, A.partialValueStack_nil] at h
  rw [h]
  rfl

/-- Partial evaluation halts with the ordinary realization, on an on-domain environment
and a bounded term. -/
theorem partialRealize_eq_some {i : ℕ} {env : Tuple ℕ} {t : L.Term ℕ}
    (henv : ∀ x ∈ env, x ∈ A.domainAt i) (ht : Term.VarsBelow env.length t) :
    A.partialRealize i env t =
      Part.some (@Term.realize L ℕ (A.structureAt i) ℕ (ComputableAgeIn.envFun env) t) := by
  rw [partialRealize, partialValueStack_listEncode henv ht, Part.bind_some]
  rfl

theorem partialRealize_dom {i : ℕ} {env : Tuple ℕ} {t : L.Term ℕ}
    (henv : ∀ x ∈ env, x ∈ A.domainAt i) (ht : Term.VarsBelow env.length t) :
    (A.partialRealize i env t).Dom := by
  rw [partialRealize_eq_some henv ht]
  trivial

/-- The value stays inside the member's carrier. -/
theorem partialRealize_mem_domainAt {i : ℕ} {env : Tuple ℕ} {t : L.Term ℕ} {x : ℕ}
    (henv : ∀ x ∈ env, x ∈ A.domainAt i) (ht : Term.VarsBelow env.length t)
    (hx : x ∈ A.partialRealize i env t) : x ∈ A.domainAt i := by
  rw [partialRealize_eq_some henv ht, Part.mem_some_iff] at hx
  exact hx ▸ realize_mem_domainAt henv ht

/-! ### The converse: halting certifies bounded variables -/

/-- A halting run of the machine bounds every variable it read. -/
theorem lt_length_of_dom_of_mem {i : ℕ} {env : Tuple ℕ} :
    ∀ {l : List (ℕ ⊕ (Σ j, L.Functions j))}, (A.partialValueStack i env l).Dom →
      ∀ {n : ℕ}, Sum.inl n ∈ l → n < env.length := by
  intro l
  induction l with
  | nil => intro _ n hn; exact absurd hn (List.not_mem_nil)
  | cons g l ih =>
    intro h n hn
    rw [A.partialValueStack_cons] at h
    obtain ⟨y, hy⟩ := Part.dom_iff_mem.1 h
    obtain ⟨acc, hacc, hstep⟩ := Part.mem_bind_iff.1 hy
    rcases List.mem_cons.1 hn with rfl | hn'
    · obtain ⟨a, ha, -⟩ := (Part.mem_map_iff _).1 hstep
      obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.1 (Part.mem_ofOption.1 ha)
      exact hlt
    · exact ih (Part.dom_iff_mem.2 ⟨acc, hacc⟩) hn'

theorem partialValueStack_dom_of_partialRealize_dom {i : ℕ} {env : Tuple ℕ}
    {t : L.Term ℕ} (h : (A.partialRealize i env t).Dom) :
    (A.partialValueStack i env t.listEncode).Dom := by
  obtain ⟨y, hy⟩ := Part.dom_iff_mem.1 h
  obtain ⟨vs, hvs, -⟩ := Part.mem_bind_iff.1 hy
  exact Part.dom_iff_mem.2 ⟨vs, hvs⟩

/-- Halting certifies that the term's variables lie below the environment length. This
characterizes the term traversal under the given environment; it makes no claim about the
stored evaluators off-domain. -/
theorem varsBelow_of_partialRealize_dom {i : ℕ} {env : Tuple ℕ} {t : L.Term ℕ}
    (h : (A.partialRealize i env t).Dom) : Term.VarsBelow env.length t := fun v hv ↦
  lt_length_of_dom_of_mem (partialValueStack_dom_of_partialRealize_dom h)
    ((Term.mem_varFinset_iff_inl_mem_listEncode t v).1 hv)

/-- Halting is exactly bounded variables, on an on-domain environment. -/
theorem partialRealize_dom_iff {i : ℕ} {env : Tuple ℕ} {t : L.Term ℕ}
    (henv : ∀ x ∈ env, x ∈ A.domainAt i) :
    (A.partialRealize i env t).Dom ↔ Term.VarsBelow env.length t :=
  ⟨varsBelow_of_partialRealize_dom, partialRealize_dom henv⟩

/-! ### The `Fin`-variable bridge -/

/-- Relabeled `Fin`-variable terms evaluate to ordinary realization at the tuple view. -/
theorem partialRealize_relabel_view {i : ℕ} {env : Tuple ℕ} {k : ℕ}
    (henv : ∀ x ∈ env, x ∈ A.domainAt i) (hk : env.length = k) (t : L.Term (Fin k)) :
    A.partialRealize i env (t.relabel Fin.val) =
      Part.some (@Term.realize L ℕ (A.structureAt i) _
        (fun x : Fin k ↦ env.view (Fin.cast hk.symm x)) t) := by
  letI : L.Structure ℕ := A.structureAt i
  rw [partialRealize_eq_some henv (hk ▸ Term.varsBelow_relabel_val t)]
  exact congrArg _ (Term.realize_envFun_relabel_val hk t)

/-- Bounded natural-variable terms evaluate to the realization of their restriction. -/
theorem partialRealize_eq_realize_restrictVar {i : ℕ} {env : Tuple ℕ} {k : ℕ}
    (henv : ∀ x ∈ env, x ∈ A.domainAt i) (hk : env.length = k) (t : L.Term ℕ)
    (hvb : Term.VarsBelow k t) :
    A.partialRealize i env t =
      Part.some (@Term.realize L ℕ (A.structureAt i) _
        (fun x : Fin k ↦ env.view (Fin.cast hk.symm x))
        (t.restrictVar fun x ↦ (⟨x.1, hvb x.1 x.2⟩ : Fin k))) := by
  letI : L.Structure ℕ := A.structureAt i
  rw [partialRealize_eq_some henv (hk ▸ hvb)]
  exact congrArg _ (Term.realize_envFun_restrictVar hk t hvb)

end PartialAgeIn

end FirstOrder.Language
