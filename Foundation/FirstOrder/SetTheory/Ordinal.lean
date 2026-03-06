module

public import Foundation.FirstOrder.SetTheory.Function

@[expose] public section
/-!
# Ordinals and transitive sets

reference: Ralf Schindler, "Set Theory, Exploring Independence and Truth" [Sch14]
-/

namespace LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V ⊧ₘ* 𝗭]

/-! ### Transitive set -/

class IsTransitive (x : V) : Prop where
  transitive : ∀ y ∈ x, y ⊆ x

omit [Nonempty V] [V ⊧ₘ* 𝗭] in
lemma isTransitive_def {x : V} : IsTransitive x ↔ ∀ y ∈ x, y ⊆ x :=
  ⟨fun h ↦ h.transitive, fun h ↦ ⟨h⟩⟩

def IsTransitive.dfn : Semisentence ℒₛₑₜ 1 := “x. ∀ y ∈ x, y ⊆ x”

instance IsTransitive.defined : ℒₛₑₜ-predicate[V] IsTransitive via IsTransitive.dfn :=
  ⟨fun v ↦ by simp [IsTransitive.dfn, isTransitive_def]⟩

instance IsTransitive.definable : ℒₛₑₜ-predicate[V] IsTransitive := IsTransitive.defined.to_definable

namespace IsTransitive

omit [Nonempty V] [V ⊧ₘ* 𝗭] in
lemma mem_trans {x y z : V} (H : IsTransitive z) (hxy : x ∈ y) (hyz : y ∈ z) : x ∈ z := H.transitive y hyz x hxy

@[simp] protected instance empty : IsTransitive (∅ : V) := ⟨fun x ↦ by simp⟩

lemma succ {x : V} (h : IsTransitive x) : IsTransitive (succ x) := ⟨by
  intro y hy
  rcases show y = x ∨ y ∈ x by simpa [mem_succ_iff] using hy with (rfl | hy)
  · simp
  · exact subset_trans (h.transitive y hy) (by simp)⟩

@[simp] lemma nat : x ∈ (ω : V) → IsTransitive x := by
  apply naturalNumber_induction
  · definability
  case zero =>
    simp [zero_def]
  case succ =>
    intro x hx ih
    exact ih.succ

lemma union {x y : V} [hx : IsTransitive x] [hy : IsTransitive y] : IsTransitive (x ∪ y) := ⟨by
  simp only [mem_union_iff]
  rintro z (hzx | hzy)
  · exact subset_trans (hx.transitive z hzx) (by simp)
  · exact subset_trans (hy.transitive z hzy) (by simp)⟩

lemma sUnion {X : V} (h : ∀ x ∈ X, IsTransitive x) : IsTransitive (⋃ˢ X) := ⟨by
  intro x hx
  have : ∃ y ∈ X, x ∈ y := by simpa [mem_sUnion_iff] using hx
  rcases this with ⟨y, hyX, hxy⟩
  exact subset_trans ((h y hyX).transitive x hxy) (subset_sUnion_of_mem hyX)⟩

lemma sInter {X : V} (h : ∀ x ∈ X, IsTransitive x) : IsTransitive (⋂ˢ X) := by
  rcases eq_empty_or_isNonempty X with (rfl | hX)
  · simp
  refine ⟨?_⟩
  intro y hy
  apply subset_sInter_iff_of_nonempty.mpr
  intro z hzX
  have : y ∈ z := mem_sInter_iff_of_nonempty.mp hy z hzX
  exact (h z hzX).transitive y this

/-
@[simp] lemma IsTransitive.ω : IsTransitive (ω : V) := by
  intro x hx
  induction x using naturalNumber_induction
  · definability
  case zero =>
    simp [zero_def]
  case succ x hx' ih =>
    intro z hz
    rcases show z = x ∨ z ∈ x by simpa using hz with (rfl | hz)
    · exact hx'
    · exact ih hx' z hz
-/

@[simp] protected instance ω : IsTransitive (ω : V) := ⟨by
  apply naturalNumber_induction
  · definability
  case zero =>
    simp [zero_def]
  case succ =>
    intro x hx ih z hz
    rcases show z = x ∨ z ∈ x by simpa [mem_succ_iff] using hz with (rfl | hz)
    · exact hx
    · exact ih z hz⟩

end IsTransitive

/-! ### Ordinals -/

/-- Neumann ordinal -/
class IsOrdinal (x : V) : Prop extends IsTransitive x where
  trichotomy : ∀ y ∈ x, ∀ z ∈ x, y ∈ z ∨ y = z ∨ z ∈ y

omit [Nonempty V] [V ⊧ₘ* 𝗭] in
lemma isOrdinal_iff {x : V} :
    IsOrdinal x ↔ IsTransitive x ∧ ∀ y ∈ x, ∀ z ∈ x, y ∈ z ∨ y = z ∨ z ∈ y :=
  ⟨fun h ↦ ⟨⟨h.transitive⟩, h.trichotomy⟩, fun h ↦ { transitive := h.1.transitive, trichotomy := h.2 }⟩

def IsOrdinal.dfn : Semisentence ℒₛₑₜ 1 := “x. !IsTransitive.dfn x ∧ ∀ y ∈ x, ∀ z ∈ x, y ∈ z ∨ y = z ∨ z ∈ y”

instance IsOrdinal.defined : ℒₛₑₜ-predicate[V] IsOrdinal via IsOrdinal.dfn := ⟨fun δ ↦ by simp [isOrdinal_iff, dfn]⟩

instance IsOrdinal.definable : ℒₛₑₜ-predicate[V] IsOrdinal := IsOrdinal.defined.to_definable

namespace IsOrdinal

variable {α β γ : V}

lemma of_mem [h : IsOrdinal α] (lt : β ∈ α) : IsOrdinal β where
  transitive γ hzy δ hvz := by
    have hzx : γ ∈ α := h.transitive _ lt _ hzy
    have hvx : δ ∈ α := h.transitive _ hzx _ hvz
    rcases show β ∈ δ ∨ β = δ ∨ δ ∈ β from h.trichotomy _ lt _ hvx with (hzv | rfl | hvz)
    · have : β ∉ δ := mem_asymm₃ hvz hzy
      contradiction
    · have : γ ∉ β := mem_asymm hvz
      contradiction
    · assumption
  trichotomy γ hzy δ hvy := by
    have hzx : γ ∈ α := h.transitive _ lt _ hzy
    have hvx : δ ∈ α := h.transitive _ lt _ hvy
    exact h.trichotomy γ hzx δ hvx

@[simp] protected instance empty : IsOrdinal (∅ : V) where
  trichotomy := by simp

@[simp] protected instance zero : IsOrdinal (0 : V) := .empty

protected instance succ [h : IsOrdinal α] : IsOrdinal (succ α) where
  transitive := h.toIsTransitive.succ.transitive
  trichotomy β₁ h₁ β₂ h₂ := by
    rcases show β₁ = α ∨ β₁ ∈ α by simpa [mem_succ_iff] using h₁ with (rfl | h₁)
    · rcases show β₂ = β₁ ∨ β₂ ∈ β₁ by simpa [mem_succ_iff] using h₂ with (rfl | h₂) <;> simp_all
    · rcases show β₂ = α ∨ β₂ ∈ α by simpa [mem_succ_iff] using h₂ with (rfl | h₂)
      · simp_all
      · exact h.trichotomy β₁ h₁ β₂ h₂

protected instance nat : α ∈ (ω : V) → IsOrdinal (α : V) := by
  apply naturalNumber_induction
  · definability
  case zero => simp [zero_def]
  case succ => intro α hα H; exact H.succ

lemma mem_of_ssubset [hα : IsOrdinal α] [hβ : IsOrdinal β] : α ⊊ β → α ∈ β := by
  intro ss
  have : ∃ γ, (γ ∈ β ∧ γ ∉ α) ∧ ∀ δ ∈ β, δ ∉ α → δ ∉ γ := by
    have : IsNonempty (β \ α) := (isNonempty_sdiff_of_ssubset ss)
    simpa using foundation (β \ α)
  rcases this with ⟨γ, ⟨hγβ, hγα⟩, Hγ⟩
  have Hγα : γ ⊆ α := by
    intro ξ hξγ
    have hξβ : ξ ∈ β := hβ.transitive γ hγβ _ hξγ
    by_contra! hξα
    have : ξ ∉ γ := Hγ ξ hξβ hξα
    contradiction
  have Hαγ : α ⊆ γ := by
    intro ξ hξα
    have : ξ ∈ β := ss.subset _ hξα
    have : ξ ∈ γ ∨ (ξ = γ ∨ γ ∈ ξ) := hβ.trichotomy ξ this γ hγβ
    rcases this with (hξγ | C)
    · exact hξγ
    · have : γ ∈ α := by
        rcases C with (rfl | h)
        · assumption
        · exact hα.transitive _ hξα _ h
      contradiction
  have : α = γ := subset_antisymm Hαγ Hγα
  rcases this
  assumption

@[grind =] lemma ssubset_iff [hα : IsOrdinal α] [hβ : IsOrdinal β] : α ⊊ β ↔ α ∈ β :=
  ⟨mem_of_ssubset, fun hαβ ↦ ⟨hβ.transitive _ hαβ, ne_of_mem hαβ⟩⟩

@[grind =] lemma subset_iff [hα : IsOrdinal α] [hβ : IsOrdinal β] : α ⊆ β ↔ α = β ∨ α ∈ β := by
  constructor
  · intro ss
    by_cases eq : α = β
    · simp_all
    · right; exact mem_of_ssubset ⟨ss, eq⟩
  · rintro (rfl | h)
    · simp
    · exact hβ.transitive α h

open Classical in
@[grind =_] lemma mem_iff_subset_and_not_subset [hα : IsOrdinal α] [hβ : IsOrdinal β] :
    α ∈ β ↔ α ⊆ β ∧ ¬β ⊆ α := calc
  α ∈ β ↔ α ⊊ β          := ssubset_iff.symm
  _     ↔ α ⊆ β ∧ α ≠ β  := by rfl
  _     ↔ α ⊆ β ∧ ¬β ⊆ α := by grind

variable (α β)

lemma subset_or_supset [hα : IsOrdinal α] [hβ : IsOrdinal β] : α ⊆ β ∨ β ⊆ α := by
  by_contra! Aαβ
  let C : V := {α' ∈ succ α ; ∃ β, IsOrdinal β ∧ ¬α' ⊆ β ∧ ¬β ⊆ α'}
  have hαC : α ∈ C := by
    simp only [mem_sep_iff, mem_succ_iff, mem_irrefl, or_false, true_and, C]
    exact ⟨β, hβ, Aαβ⟩
  have : ∃ α₀, (α₀ ∈ succ α ∧ ∃ β, IsOrdinal β ∧ ¬α₀ ⊆ β ∧ ¬β ⊆ α₀) ∧ ∀ γ ∈ C, γ ∉ α₀ := by
    have : IsNonempty C := ⟨α, hαC⟩
    simpa [C] using foundation C
  rcases this with ⟨α₀, ⟨hα₀sα, β₀, ordβ₀, Hα₀β₀⟩, Hα₀⟩
  have ordα₀ : IsOrdinal α₀ := by
    rcases mem_succ_iff.mp hα₀sα with (rfl | hα₀α)
    · assumption
    · exact hα.of_mem hα₀α
  let γ₀ := α₀ ∪ β₀
  have : IsOrdinal γ₀ := isOrdinal_iff.mpr ⟨IsTransitive.union, by
    intro ξ hξγ₀ ζ hζγ₀
    rcases show ξ ∈ α₀ ∨ ξ ∈ β₀ by simpa [γ₀] using hξγ₀ with (hξα₀ | hξβ₀)
    · have : IsOrdinal ξ := of_mem hξα₀
      rcases show ζ ∈ α₀ ∨ ζ ∈ β₀ by simpa [γ₀] using hζγ₀ with (hζα₀ | hζβ₀)
      · exact ordα₀.trichotomy ξ hξα₀ ζ hζα₀
      · have : IsOrdinal ζ := of_mem hζβ₀
        have : ξ ⊆ ζ ∨ ζ ⊆ ξ := by
          by_contra! A
          have : ξ ∈ C := mem_sep_iff.mpr ⟨hα.succ.transitive α₀ hα₀sα ξ hξα₀, ζ, of_mem hζβ₀, A⟩
          exact Hα₀ ξ this hξα₀
        grind
    · have : IsOrdinal ξ := of_mem hξβ₀
      rcases show ζ ∈ α₀ ∨ ζ ∈ β₀ by simpa [γ₀] using hζγ₀ with (hζα₀ | hζβ₀)
      · have : IsOrdinal ζ := of_mem hζα₀
        have : ξ ⊆ ζ ∨ ζ ⊆ ξ := by
          by_contra! A
          have : ζ ∈ C := mem_sep_iff.mpr ⟨hα.succ.transitive α₀ hα₀sα ζ hζα₀, ξ, inferInstance, by grind⟩
          exact Hα₀ _ this hζα₀
        grind
      · have : ζ ∈ ξ ∨ ζ = ξ ∨ ξ ∈ ζ := ordβ₀.trichotomy ζ hζβ₀ ξ hξβ₀
        grind⟩
  have : γ₀ = α₀ ∨ γ₀ = β₀ := by
    by_contra! A
    have : α₀ ∈ γ₀ := ssubset_iff.mp ⟨by simp [γ₀], by grind⟩
    have hα₀β₀ : α₀ ∈ β₀ := by simpa [γ₀] using this
    have : β₀ ∈ γ₀ := ssubset_iff.mp ⟨by simp [γ₀], by grind⟩
    have hβ₀α₀ : β₀ ∈ α₀ := by simpa [γ₀] using this
    exact mem_asymm hα₀β₀ hβ₀α₀
  rcases this with (e | e)
  · have : β₀ ⊆ α₀ := by simpa [γ₀] using e
    grind
  · have : α₀ ⊆ β₀ := by simpa [γ₀] using e
    grind

lemma mem_trichotomy [hα : IsOrdinal α] [hβ : IsOrdinal β] : α ∈ β ∨ α = β ∨ β ∈ α := by
  have : α ⊆ β ∨ β ⊆ α := subset_or_supset α β
  grind

variable {α β}

lemma of_transitive_of_isOrdinal (tr : IsTransitive α) (H : ∀ β ∈ α, IsOrdinal β) : IsOrdinal α where
  trichotomy ξ hξα ζ hζα :=
    have : IsOrdinal ξ := H ξ hξα
    have : IsOrdinal ζ := H ζ hζα
    mem_trichotomy ξ ζ

@[simp] protected instance ω : IsOrdinal (ω : V) :=
  of_transitive_of_isOrdinal inferInstance fun _ hn ↦ IsOrdinal.nat hn

protected lemma sUnion {X : V} (h : ∀ α ∈ X, IsOrdinal α) : IsOrdinal (⋃ˢ X) :=
  of_transitive_of_isOrdinal (IsTransitive.sUnion fun α hαX ↦ (h α hαX).toIsTransitive)
    fun β hβ ↦ by
      have : ∃ γ ∈ X, β ∈ γ := by simpa [mem_sUnion_iff] using hβ
      rcases this with ⟨γ, hγX, hβγ⟩
      have : IsOrdinal γ := h γ hγX
      exact of_mem hβγ

protected lemma sInter {X : V} (h : ∀ α ∈ X, IsOrdinal α) : IsOrdinal (⋂ˢ X) := by
  rcases eq_empty_or_isNonempty X with (rfl | hX)
  · simp
  · apply of_transitive_of_isOrdinal (IsTransitive.sInter fun α hαX ↦ (h α hαX).toIsTransitive)
    rcases hX.nonempty with ⟨α₀, hα₀X⟩
    have : IsOrdinal α₀ := h α₀ hα₀X
    intro α hα
    have : ∀ y ∈ X, α ∈ y := by simpa using hα
    have : α ∈ α₀ := this α₀ hα₀X
    exact of_mem this

lemma sInter_mem {X : V} [IsNonempty X] (h : ∀ α ∈ X, IsOrdinal α) : ⋂ˢ X ∈ X := by
  by_contra! hXX
  have : IsOrdinal (⋂ˢ X) := IsOrdinal.sInter h
  have : ⋂ˢ X ∈ ⋂ˢ X := mem_sInter_iff_of_nonempty.mpr fun α hαX ↦ by
    have : IsOrdinal α := h α hαX
    have : ⋂ˢ X ⊆ α := sInter_subset_of_mem_of_nonempty hαX
    rcases subset_iff.mp this with (rfl | hXα)
    · contradiction
    · assumption
  simp_all

lemma empty_mem_iff_nonempty [IsOrdinal α] : ∅ ∈ α ↔ IsNonempty α := by
  have : ∅ = α ∨ ∅ ∈ α := subset_iff.mp (show ∅ ⊆ α by simp)
  rcases this with (rfl | h)
  · simp
  · simp only [h, true_iff]
    exact ⟨∅, h⟩

lemma not_exists_set_of_all_ordinals : ¬ ∃ X : V, ∀ α : V, α ∈ X ↔ IsOrdinal α := by
  rintro ⟨X, hX⟩
  let Ω : V := ⋃ˢ X
  have hΩord : IsOrdinal Ω := IsOrdinal.sUnion fun α hαX ↦ (hX α).1 hαX
  have hsuccΩX : succ Ω ∈ X := (hX (succ Ω)).2 (IsOrdinal.succ (α := Ω))
  have hsuccΩsub : succ Ω ⊆ Ω := by
    simpa [Ω] using subset_sUnion_of_mem hsuccΩX
  have hΩΩ : Ω ∈ Ω := hsuccΩsub Ω (by simp)
  exact (mem_irrefl Ω) hΩΩ

lemma not_exists_set_containing_all_ordinals : ¬ ∃ X : V, ∀ α : V, IsOrdinal α → α ∈ X := by
  rintro ⟨X, hX⟩
  let O : V := {α ∈ X ; IsOrdinal α}
  have hO : ∀ α : V, α ∈ O ↔ IsOrdinal α := by
    intro α
    constructor
    · intro hαO
      exact (mem_sep_iff.mp hαO).2
    · intro hαord
      exact mem_sep_iff.mpr ⟨hX α hαord, hαord⟩
  exact not_exists_set_of_all_ordinals ⟨O, hO⟩

lemma not_injective_functionLike_relation_to_set
    [V ⊧ₘ* 𝗭𝗙]
    (X : V)
    (R : V → V → Prop)
    (hR : ℒₛₑₜ-relation[V] R)
    (hRfun : ∀ α : V, IsOrdinal α → ∃! y : V, y ∈ X ∧ R α y) :
    ¬ (∀ α β y : V, IsOrdinal α → IsOrdinal β → R α y → R β y → α = β) := by
  intro hRinj
  let S : V → V → Prop := fun y α ↦
    (∃ β : V, IsOrdinal β ∧ R β y ∧ α = β) ∨
    ((¬∃ β : V, IsOrdinal β ∧ R β y) ∧ α = ∅)
  have hS : ℒₛₑₜ-relation[V] S := by
    letI : ℒₛₑₜ-relation[V] R := hR
    change ℒₛₑₜ-relation[V] (fun y α ↦
      (∃ β : V, IsOrdinal β ∧ R β y ∧ α = β) ∨
      ((¬∃ β : V, IsOrdinal β ∧ R β y) ∧ α = ∅))
    definability
  have hSfun : ∀ y : V, y ∈ X → ∃! α : V, S y α := by
    intro y hyX
    by_cases hy : ∃ β : V, IsOrdinal β ∧ R β y
    · rcases hy with ⟨β, hβord, hβy⟩
      refine ⟨β, Or.inl ⟨β, hβord, hβy, rfl⟩, ?_⟩
      intro α hα
      rcases hα with (hα | hα)
      · rcases hα with ⟨β₁, hβ₁ord, hβ₁y, rfl⟩
        exact hRinj α β y hβ₁ord hβord hβ₁y hβy
      · exact (hα.1 ⟨β, hβord, hβy⟩).elim
    · refine ⟨∅, Or.inr ⟨hy, rfl⟩, ?_⟩
      intro α hα
      rcases hα with (hα | hα)
      · rcases hα with ⟨β, hβord, hβy, -⟩
        exact (hy ⟨β, hβord, hβy⟩).elim
      · exact hα.2
  rcases replacement_exists_on (X := X) S hS hSfun with ⟨Y, hY⟩
  have hall : ∀ α : V, IsOrdinal α → α ∈ Y := by
    intro α hαord
    rcases (hRfun α hαord).exists with ⟨y, hyX, hαy⟩
    exact (hY α).2 ⟨y, hyX, Or.inl ⟨α, hαord, hαy, rfl⟩⟩
  exact not_exists_set_containing_all_ordinals ⟨Y, hall⟩

noncomputable def memRelOn (X : V) : V :=
  {p ∈ X ×ˢ X ; ∃ x ∈ X, ∃ y ∈ X, p = ⟨x, y⟩ₖ ∧ x ∈ y}

def memRelOn.dfn : Semisentence ℒₛₑₜ 2 :=
  f“R X. ∀ p, p ∈ R ↔ p ∈ !prod.dfn X X ∧ ∃ x ∈ X, ∃ y ∈ X, p = !kpair.dfn x y ∧ x ∈ y”

instance memRelOn.defined : ℒₛₑₜ-function₁[V] memRelOn via memRelOn.dfn :=
  ⟨fun v ↦ by rw [mem_ext_iff]; simp [memRelOn.dfn, memRelOn, mem_sep_iff]⟩

instance memRelOn.definable : ℒₛₑₜ-function₁[V] memRelOn := memRelOn.defined.to_definable

lemma memRelOn_subset_prod (X : V) : memRelOn X ⊆ X ×ˢ X := by
  intro p hp
  exact (mem_sep_iff.mp hp).1

@[simp] lemma kpair_mem_memRelOn_iff {X x y : V} :
    ⟨x, y⟩ₖ ∈ memRelOn X ↔ x ∈ X ∧ y ∈ X ∧ x ∈ y := by
  constructor
  · intro hxy
    have hxy' : ⟨x, y⟩ₖ ∈ X ×ˢ X := (mem_sep_iff.mp hxy).1
    have hX : x ∈ X ∧ y ∈ X := by simpa [mem_prod_iff] using hxy'
    have : ∃ x' ∈ X, ∃ y' ∈ X, ⟨x, y⟩ₖ = ⟨x', y'⟩ₖ ∧ x' ∈ y' := (mem_sep_iff.mp hxy).2
    rcases this with ⟨x', hx'X, y', hy'X, hEq, hx'y'⟩
    rcases kpair_inj hEq.symm with ⟨rfl, rfl⟩
    exact ⟨hX.1, hX.2, hx'y'⟩
  · rintro ⟨hxX, hyX, hxy⟩
    refine mem_sep_iff.mpr ?_
    refine ⟨by simpa [mem_prod_iff] using And.intro hxX hyX, x, hxX, y, hyX, rfl, hxy⟩

lemma strictLinearOrderOn_memRelOn [hα : IsOrdinal α] :
    IsStrictLinearOrderOn (memRelOn α) α := by
  refine ⟨memRelOn_subset_prod α, ?_, ?_, ?_⟩
  · intro x hx hxx
    exact (mem_irrefl x) ((kpair_mem_memRelOn_iff.mp hxx).2.2)
  · intro x hx y hy z hz hxy hyz
    have hxy' : x ∈ y := (kpair_mem_memRelOn_iff.mp hxy).2.2
    have hyz' : y ∈ z := (kpair_mem_memRelOn_iff.mp hyz).2.2
    have hzord : IsOrdinal z := hα.of_mem hz
    exact kpair_mem_memRelOn_iff.mpr ⟨hx, hz, hzord.toIsTransitive.transitive _ hyz' _ hxy'⟩
  · intro x hx y hy
    rcases hα.trichotomy x hx y hy with (hxy | hEq | hyx)
    · exact Or.inl <| kpair_mem_memRelOn_iff.mpr ⟨hx, hy, hxy⟩
    · exact Or.inr (Or.inl hEq)
    · exact Or.inr (Or.inr <| kpair_mem_memRelOn_iff.mpr ⟨hy, hx, hyx⟩)

lemma wellOrderOn_memRelOn [hα : IsOrdinal α] :
    IsWellOrderOn (memRelOn α) α := by
  refine ⟨strictLinearOrderOn_memRelOn (α := α), ?_⟩
  intro A hAX hAne
  have hANonempty : IsNonempty A := ne_empty_iff_isNonempty.mp hAne
  have hMin : ∃ m ∈ A, ∀ a ∈ A, a ∉ m := by simpa using foundation A
  rcases hMin with ⟨m, hmA, hmLeast⟩
  refine ⟨m, hmA, ?_⟩
  intro a haA
  have hmα : m ∈ α := hAX _ hmA
  have haα : a ∈ α := hAX _ haA
  rcases hα.trichotomy a haα m hmα with (ham | hEq | hma)
  · exact (hmLeast a haA ham).elim
  · exact Or.inl hEq
  · exact Or.inr <| kpair_mem_memRelOn_iff.mpr ⟨hmα, haα, hma⟩

lemma initialSegment_memRelOn_eq [hα : IsOrdinal α] {β : V} (hβα : β ∈ α) :
    initialSegment (memRelOn α) α β = β := by
  ext x
  constructor
  · intro hx
    have hxb : ⟨x, β⟩ₖ ∈ memRelOn α := (mem_initialSegment_iff.mp hx).2
    exact (kpair_mem_memRelOn_iff.mp hxb).2.2
  · intro hxb
    have hxα : x ∈ α := hα.toIsTransitive.transitive _ hβα _ hxb
    exact mem_initialSegment_iff.mpr ⟨hxα, kpair_mem_memRelOn_iff.mpr ⟨hxα, hβα, hxb⟩⟩

@[simp] lemma initialSegment_memRelOn_succ_eq [hα : IsOrdinal α] :
    initialSegment (memRelOn (succ α)) (succ α) α = α :=
  initialSegment_memRelOn_eq (α := succ α) (by simp)

lemma kpair_mem_initSegIsoRel_memRelOn_of_isOrderIso
    {S Y Λ α y f : V} [hΛ : IsOrdinal Λ]
    (hαΛ : α ∈ Λ) (hyY : y ∈ Y)
    (hIso : IsOrderIso (memRelOn α) α S (initialSegment S Y y) f) :
    ⟨α, y⟩ₖ ∈ initSegIsoRel (memRelOn Λ) Λ S Y := by
  have hIsoLift : IsOrderIso (memRelOn Λ) α S (initialSegment S Y y) f := by
    refine ⟨IsOrderIso.mem_function hIso, IsOrderIso.injective hIso, IsOrderIso.range_eq hIso, ?_⟩
    intro x₁ hx₁ x₂ hx₂
    have hx₁Λ : x₁ ∈ Λ := hΛ.toIsTransitive.transitive _ hαΛ _ hx₁
    have hx₂Λ : x₂ ∈ Λ := hΛ.toIsTransitive.transitive _ hαΛ _ hx₂
    have hmemΛ : ⟨x₁, x₂⟩ₖ ∈ memRelOn Λ ↔ x₁ ∈ x₂ := by
      constructor
      · intro h
        exact (kpair_mem_memRelOn_iff.mp h).2.2
      · intro h
        exact kpair_mem_memRelOn_iff.mpr ⟨hx₁Λ, hx₂Λ, h⟩
    have hmemα : ⟨x₁, x₂⟩ₖ ∈ memRelOn α ↔ x₁ ∈ x₂ := by
      constructor
      · intro h
        exact (kpair_mem_memRelOn_iff.mp h).2.2
      · intro h
        exact kpair_mem_memRelOn_iff.mpr ⟨hx₁, hx₂, h⟩
    calc
      ⟨x₁, x₂⟩ₖ ∈ memRelOn Λ ↔ x₁ ∈ x₂ := hmemΛ
      _ ↔ ⟨x₁, x₂⟩ₖ ∈ memRelOn α := hmemα.symm
      _ ↔ ⟨f ‘ x₁, f ‘ x₂⟩ₖ ∈ S := IsOrderIso.rel_iff hIso hx₁ hx₂
  have hIsoSeg :
      IsOrderIso (memRelOn Λ) (initialSegment (memRelOn Λ) Λ α) S (initialSegment S Y y) f := by
    simpa [initialSegment_memRelOn_eq (α := Λ) hαΛ] using hIsoLift
  exact kpair_mem_initSegIsoRel_iff.mpr ⟨hαΛ, hyY, ⟨f, hIsoSeg⟩⟩

lemma exists_ordinal_isOrderIso_of_wellOrderOn
    [V ⊧ₘ* 𝗭𝗙] {S Y : V} (hSwo : IsWellOrderOn S Y) :
    ∃ α : V, IsOrdinal α ∧ ∃ f : V, IsOrderIso (memRelOn α) α S Y f := by
  let Rm : V → V → Prop := fun α y ↦
    y ∈ Y ∧ ∃ f : V, IsOrderIso (memRelOn α) α S (initialSegment S Y y) f
  have hRmdef : ℒₛₑₜ-relation[V] Rm := by
    letI : ℒₛₑₜ-function₁[V] memRelOn := memRelOn.definable
    letI : ℒₛₑₜ-function₃[V] initialSegment := initialSegment.definable
    letI : ℒₛₑₜ-relation₅[V] IsOrderIso := IsOrderIso.definable
    unfold Rm
    definability
  have hNotAllMapped :
      ¬ ∀ α : V, IsOrdinal α → ∃ y ∈ Y, Rm α y := by
    intro hAll
    have hRmfun : ∀ α : V, IsOrdinal α → ∃! y : V, y ∈ Y ∧ Rm α y := by
      intro α hαord
      rcases hAll α hαord with ⟨y, hyY, hyRm⟩
      refine ⟨y, ⟨hyY, hyRm⟩, ?_⟩
      intro y' hy'
      have hy'Y : y' ∈ Y := hy'.1
      rcases hyRm.2 with ⟨f, hf⟩
      rcases hy'.2.2 with ⟨f', hf'⟩
      have hab : ⟨α, y⟩ₖ ∈ initSegIsoRel (memRelOn (succ α)) (succ α) S Y :=
        kpair_mem_initSegIsoRel_memRelOn_of_isOrderIso
          (S := S) (Y := Y) (Λ := succ α) (α := α) (y := y) (f := f)
          (by simp) hyY hf
      have hab' : ⟨α, y'⟩ₖ ∈ initSegIsoRel (memRelOn (succ α)) (succ α) S Y :=
        kpair_mem_initSegIsoRel_memRelOn_of_isOrderIso
          (S := S) (Y := Y) (Λ := succ α) (α := α) (y := y') (f := f')
          (by simp) hy'Y hf'
      have hEq : y = y' := initSegIsoRel_value_unique
        (hRwo := wellOrderOn_memRelOn (α := succ α))
        (hSwo := hSwo) hab hab'
      simp [hEq]
    have hRminj :
        ∀ α β y : V, IsOrdinal α → IsOrdinal β → Rm α y → Rm β y → α = β := by
      intro α β y hαord hβord hαy hβy
      have hyY : y ∈ Y := hαy.1
      rcases hαy.2 with ⟨fα, hfα⟩
      rcases hβy.2 with ⟨fβ, hfβ⟩
      let Λ : V := succ (α ∪ β)
      have hαuβord : IsOrdinal (α ∪ β) := by
        rcases IsOrdinal.subset_or_supset (α := α) (β := β) with (hαβ | hβα)
        · have : α ∪ β = β := union_eq_iff_left.mpr hαβ
          simpa [this]
        · have : α ∪ β = α := union_eq_iff_right.mpr hβα
          simpa [this]
      have hαΛord : IsOrdinal Λ := IsOrdinal.succ (α := α ∪ β)
      have hαΛ : α ∈ Λ := by
        have hαsub : α ⊆ α ∪ β := subset_union_left α β
        rcases (IsOrdinal.subset_iff (α := α) (β := α ∪ β)).1 hαsub with (hEq | hMem)
        · rw [mem_succ_iff]; exact Or.inl hEq
        · rw [mem_succ_iff]; exact Or.inr hMem
      have hβΛ : β ∈ Λ := by
        have hβsub : β ⊆ α ∪ β := subset_union_right α β
        rcases (IsOrdinal.subset_iff (α := β) (β := α ∪ β)).1 hβsub with (hEq | hMem)
        · rw [mem_succ_iff]; exact Or.inl hEq
        · rw [mem_succ_iff]; exact Or.inr hMem
      have hαpair : ⟨α, y⟩ₖ ∈ initSegIsoRel (memRelOn Λ) Λ S Y :=
        kpair_mem_initSegIsoRel_memRelOn_of_isOrderIso
          (S := S) (Y := Y) (Λ := Λ) (α := α) (y := y) (f := fα) hαΛ hyY hfα
      have hβpair : ⟨β, y⟩ₖ ∈ initSegIsoRel (memRelOn Λ) Λ S Y :=
        kpair_mem_initSegIsoRel_memRelOn_of_isOrderIso
          (S := S) (Y := Y) (Λ := Λ) (α := β) (y := y) (f := fβ) hβΛ hyY hfβ
      exact initSegIsoRel_injective
        (hRwo := by
          letI : IsOrdinal Λ := hαΛord
          exact wellOrderOn_memRelOn (α := Λ))
        (hSwo := hSwo) α β y hαpair hβpair
    have : ¬ (∀ α β y : V, IsOrdinal α → IsOrdinal β → Rm α y → Rm β y → α = β) :=
      not_injective_functionLike_relation_to_set
        (X := Y) (R := Rm) hRmdef hRmfun
    exact this hRminj
  have hExistsUnmapped : ∃ α : V, IsOrdinal α ∧ ¬∃ y ∈ Y, Rm α y := by
    by_contra! hNo
    exact hNotAllMapped (by
      intro α hαord
      rcases hNo α hαord with ⟨y, hyY, hyRm⟩
      exact ⟨y, hyY, hyRm⟩)
  rcases hExistsUnmapped with ⟨α, hαord, hαUnmapped⟩
  have hαwo : IsWellOrderOn (memRelOn α) α := by
    letI : IsOrdinal α := hαord
    exact wellOrderOn_memRelOn (α := α)
  rcases wellOrder_comparable_by_initSegIsoRel (hRwo := hαwo) (hSwo := hSwo) with
    hFull | hLeft | hRight
  · exact ⟨α, hαord, ⟨initSegIsoRel (memRelOn α) α S Y, hFull⟩⟩
  · rcases hLeft with ⟨a₀, ha₀α, hIso⟩
    refine ⟨a₀, hαord.of_mem ha₀α, ?_⟩
    refine ⟨initSegIsoRel (memRelOn α) α S Y, ?_⟩
    have hIso' : IsOrderIso (memRelOn α) a₀ S Y (initSegIsoRel (memRelOn α) α S Y) := by
      simpa [initialSegment_memRelOn_eq (α := α) ha₀α] using hIso
    have ha₀ord : IsOrdinal a₀ := hαord.of_mem ha₀α
    exact ⟨hIso'.mem_function, hIso'.injective, hIso'.range_eq, fun x₁ hx₁ x₂ hx₂ ↦ by
      have hx₁α : x₁ ∈ α := hαord.toIsTransitive.transitive _ ha₀α _ hx₁
      have hx₂α : x₂ ∈ α := hαord.toIsTransitive.transitive _ ha₀α _ hx₂
      rw [show ⟨x₁, x₂⟩ₖ ∈ memRelOn a₀ ↔ ⟨x₁, x₂⟩ₖ ∈ memRelOn α from by
        simp [kpair_mem_memRelOn_iff, hx₁, hx₂, hx₁α, hx₂α]]
      exact hIso'.rel_iff hx₁ hx₂⟩
  · rcases hRight with ⟨b₀, hb₀Y, hIso⟩
    have hRmαb₀ : Rm α b₀ := ⟨hb₀Y, initSegIsoRel (memRelOn α) α S Y, hIso⟩
    exact (hαUnmapped ⟨b₀, hb₀Y, hRmαb₀⟩).elim

end IsOrdinal

variable (V)

@[ext]
structure Ordinal where
  val : V
  ordinal : IsOrdinal val

variable {V}

attribute [coe] Ordinal.val

attribute [instance] Ordinal.ordinal

instance : Coe (Ordinal V) V := ⟨Ordinal.val⟩

@[coe] def IsOrdinal.toOrdinal (α : V) [IsOrdinal α] : Ordinal V := ⟨α, inferInstance⟩

omit [Nonempty V] [V ⊧ₘ* 𝗭] in
@[simp] lemma IsOrdinal.toOrdinal_val (α : V) [IsOrdinal α] : (IsOrdinal.toOrdinal α).val = α := rfl

omit [Nonempty V] [V ⊧ₘ* 𝗭] in
@[simp] lemma Ordinal.val_toOrdinal (α : Ordinal V) : IsOrdinal.toOrdinal α.val = α := rfl

namespace Ordinal

variable {α β γ : Ordinal V}

instance : LT (Ordinal V) := ⟨fun α β ↦ α.val ∈ β.val⟩

instance : LE (Ordinal V) := ⟨fun α β ↦ α.val ⊆ β.val⟩

omit [Nonempty V] [V ⊧ₘ* 𝗭] in
lemma lt_def : α < β ↔ α.val ∈ β.val := by rfl

omit [Nonempty V] [V ⊧ₘ* 𝗭] in
lemma le_def : α ≤ β ↔ α.val ⊆ β.val := by rfl

instance : IsOrdinal α.val := α.ordinal

noncomputable instance : LinearOrder (Ordinal V) where
  le_refl α := subset_refl α.val
  le_trans α β γ := subset_trans
  lt_iff_le_not_ge α β := IsOrdinal.mem_iff_subset_and_not_subset
  le_antisymm α β := by simpa [le_def, Ordinal.ext_iff] using subset_antisymm (x := α.val) (y := β.val)
  le_total α β := IsOrdinal.subset_or_supset α.val β.val
  toDecidableLE := Classical.decRel LE.le

noncomputable instance : OrderBot (Ordinal V) where
  bot := IsOrdinal.toOrdinal ∅
  bot_le _ := empty_subset _

@[simp] lemma bot_val_eq : (⊥ : Ordinal V).val = ∅ := rfl

lemma pos_iff_nonempty : ⊥ < α ↔ IsNonempty α.val := IsOrdinal.empty_mem_iff_nonempty

lemma eq_bot_or_pos : α = ⊥ ∨ α > ⊥ := by exact eq_bot_or_bot_lt α

protected noncomputable def succ (α : Ordinal V) : Ordinal V where
  val := succ α
  ordinal := inferInstance

@[simp] lemma succ_val (α : Ordinal V) : α.succ.val = succ α.val := rfl

@[simp] lemma lt_succ (α : Ordinal V) : α < α.succ := lt_def.mpr <| by simp

protected noncomputable def ω : Ordinal V := IsOrdinal.toOrdinal ω

private lemma isOrderIso_memRelOn_of_parent
    {S Y α a f : V} (hαord : IsOrdinal α) (haα : a ∈ α)
    (hIso : IsOrderIso (IsOrdinal.memRelOn α) a S Y f) :
    IsOrderIso (IsOrdinal.memRelOn a) a S Y f := by
  refine ⟨hIso.mem_function, hIso.injective, hIso.range_eq, ?_⟩
  intro x₁ hx₁ x₂ hx₂
  have hx₁α : x₁ ∈ α := hαord.toIsTransitive.transitive _ haα _ hx₁
  have hx₂α : x₂ ∈ α := hαord.toIsTransitive.transitive _ haα _ hx₂
  rw [show ⟨x₁, x₂⟩ₖ ∈ IsOrdinal.memRelOn a ↔ ⟨x₁, x₂⟩ₖ ∈ IsOrdinal.memRelOn α from by
      simp [IsOrdinal.kpair_mem_memRelOn_iff, hx₁, hx₂, hx₁α, hx₂α]]
  exact hIso.rel_iff hx₁ hx₂

private lemma isOrderIso_initialSegment_of_kpair
    {S Y α a y f : V} (hαord : IsOrdinal α)
    (hf : IsOrderIso (IsOrdinal.memRelOn α) α S Y f)
    (haα : a ∈ α) (hayf : ⟨a, y⟩ₖ ∈ f) :
    IsOrderIso (IsOrdinal.memRelOn a) a S (initialSegment S Y y)
      (f ↾ (initialSegment (IsOrdinal.memRelOn α) α a)) := by
  have hRes :
      IsOrderIso (IsOrdinal.memRelOn α) (initialSegment (IsOrdinal.memRelOn α) α a)
        S (initialSegment S Y y) (f ↾ (initialSegment (IsOrdinal.memRelOn α) α a)) :=
    IsOrderIso.restrict_initialSegment hf haα hayf
  have hRes' :
      IsOrderIso (IsOrdinal.memRelOn α) a S (initialSegment S Y y)
        (f ↾ (initialSegment (IsOrdinal.memRelOn α) α a)) := by
    simpa [IsOrdinal.initialSegment_memRelOn_eq (α := α) haα] using hRes
  exact isOrderIso_memRelOn_of_parent hαord haα hRes'

private lemma ordinal_eq_of_isOrderIso_to_same_initialSegment
    [V ⊧ₘ* 𝗭𝗙] {S Y α β y f g : V}
    (hSwo : IsWellOrderOn S Y) (hαord : IsOrdinal α) (hβord : IsOrdinal β)
    (hyY : y ∈ Y)
    (hαy : IsOrderIso (IsOrdinal.memRelOn α) α S (initialSegment S Y y) f)
    (hβy : IsOrderIso (IsOrdinal.memRelOn β) β S (initialSegment S Y y) g) :
    α = β := by
  letI : IsOrdinal α := hαord
  letI : IsOrdinal β := hβord
  let Λ : V := succ (α ∪ β)
  have hαuβord : IsOrdinal (α ∪ β) := by
    rcases IsOrdinal.subset_or_supset (α := α) (β := β) with (hαβ | hβα)
    · have : α ∪ β = β := union_eq_iff_left.mpr hαβ
      simpa [this]
    · have : α ∪ β = α := union_eq_iff_right.mpr hβα
      simpa [this]
  have hΛord : IsOrdinal Λ := IsOrdinal.succ (α := α ∪ β)
  have hαΛ : α ∈ Λ := by
    have hαsub : α ⊆ α ∪ β := subset_union_left α β
    rcases (IsOrdinal.subset_iff (α := α) (β := α ∪ β)).1 hαsub with (hEq | hMem)
    · rw [mem_succ_iff]; exact Or.inl hEq
    · rw [mem_succ_iff]; exact Or.inr hMem
  have hβΛ : β ∈ Λ := by
    have hβsub : β ⊆ α ∪ β := subset_union_right α β
    rcases (IsOrdinal.subset_iff (α := β) (β := α ∪ β)).1 hβsub with (hEq | hMem)
    · rw [mem_succ_iff]; exact Or.inl hEq
    · rw [mem_succ_iff]; exact Or.inr hMem
  have hαpair : ⟨α, y⟩ₖ ∈ initSegIsoRel (IsOrdinal.memRelOn Λ) Λ S Y :=
    IsOrdinal.kpair_mem_initSegIsoRel_memRelOn_of_isOrderIso
      (S := S) (Y := Y) (Λ := Λ) (α := α) (y := y) (f := f) hαΛ hyY hαy
  have hβpair : ⟨β, y⟩ₖ ∈ initSegIsoRel (IsOrdinal.memRelOn Λ) Λ S Y :=
    IsOrdinal.kpair_mem_initSegIsoRel_memRelOn_of_isOrderIso
      (S := S) (Y := Y) (Λ := Λ) (α := β) (y := y) (f := g) hβΛ hyY hβy
  exact initSegIsoRel_injective
    (hRwo := by
      letI : IsOrdinal Λ := hΛord
      exact IsOrdinal.wellOrderOn_memRelOn (α := Λ))
    (hSwo := hSwo) α β y hαpair hβpair

lemma ordinal_isOrderIso_unique_of_wellOrderOn
    [V ⊧ₘ* 𝗭𝗙] {S Y α β : V} (hSwo : IsWellOrderOn S Y)
    (hαord : IsOrdinal α) (hβord : IsOrdinal β)
    (hαiso : ∃ f : V, IsOrderIso (IsOrdinal.memRelOn α) α S Y f)
    (hβiso : ∃ f : V, IsOrderIso (IsOrdinal.memRelOn β) β S Y f) :
    α = β := by
  rcases hαiso with ⟨f, hf⟩
  rcases hβiso with ⟨g, hg⟩
  apply subset_antisymm
  · intro a haα
    rcases exists_of_mem_function hf.mem_function a haα with ⟨y, hyY, hayf⟩
    have hαy : IsOrderIso (IsOrdinal.memRelOn a) a S (initialSegment S Y y)
        (f ↾ (initialSegment (IsOrdinal.memRelOn α) α a)) :=
      isOrderIso_initialSegment_of_kpair hαord hf haα hayf
    have hyRangeG : y ∈ range g := by simpa [hg.range_eq] using hyY
    rcases mem_range_iff.mp hyRangeG with ⟨b, hbg⟩
    have hbβ : b ∈ β := (mem_of_mem_functions hg.mem_function hbg).1
    have hβy : IsOrderIso (IsOrdinal.memRelOn b) b S (initialSegment S Y y)
        (g ↾ (initialSegment (IsOrdinal.memRelOn β) β b)) :=
      isOrderIso_initialSegment_of_kpair hβord hg hbβ hbg
    have hab : a = b := ordinal_eq_of_isOrderIso_to_same_initialSegment
      (hSwo := hSwo) (hαord := hαord.of_mem haα) (hβord := hβord.of_mem hbβ)
      (hyY := hyY) hαy hβy
    simpa [hab] using hbβ
  · intro b hbβ
    rcases exists_of_mem_function hg.mem_function b hbβ with ⟨y, hyY, hbyg⟩
    have hβy : IsOrderIso (IsOrdinal.memRelOn b) b S (initialSegment S Y y)
        (g ↾ (initialSegment (IsOrdinal.memRelOn β) β b)) :=
      isOrderIso_initialSegment_of_kpair hβord hg hbβ hbyg
    have hyRangeF : y ∈ range f := by simpa [hf.range_eq] using hyY
    rcases mem_range_iff.mp hyRangeF with ⟨a, haf⟩
    have haα : a ∈ α := (mem_of_mem_functions hf.mem_function haf).1
    have hαy : IsOrderIso (IsOrdinal.memRelOn a) a S (initialSegment S Y y)
        (f ↾ (initialSegment (IsOrdinal.memRelOn α) α a)) :=
      isOrderIso_initialSegment_of_kpair hαord hf haα haf
    have hba : b = a := ordinal_eq_of_isOrderIso_to_same_initialSegment
      (hSwo := hSwo) (hαord := hβord.of_mem hbβ) (hβord := hαord.of_mem haα)
      (hyY := hyY) hβy hαy
    simpa [hba] using haα

lemma existsUnique_ordinal_isOrderIso_of_wellOrderOn
    [V ⊧ₘ* 𝗭𝗙] {S Y : V} (hSwo : IsWellOrderOn S Y) :
    ∃! α : V, IsOrdinal α ∧ ∃ f : V, IsOrderIso (IsOrdinal.memRelOn α) α S Y f := by
  rcases IsOrdinal.exists_ordinal_isOrderIso_of_wellOrderOn (S := S) (Y := Y) hSwo with
    ⟨α, hαord, f, hf⟩
  refine ⟨α, ⟨hαord, ⟨f, hf⟩⟩, ?_⟩
  intro β hβ
  exact ordinal_isOrderIso_unique_of_wellOrderOn hSwo hβ.1 hαord hβ.2 ⟨f, hf⟩

noncomputable def wellOrderTypeVal
    [V ⊧ₘ* 𝗭𝗙] (S Y : V) (hSwo : IsWellOrderOn S Y) : V :=
  Classical.choose <| existsUnique_ordinal_isOrderIso_of_wellOrderOn (S := S) (Y := Y) hSwo

lemma wellOrderTypeVal_spec
    [V ⊧ₘ* 𝗭𝗙] (S Y : V) (hSwo : IsWellOrderOn S Y) :
    IsOrdinal (wellOrderTypeVal S Y hSwo) ∧
      ∃ f : V, IsOrderIso (IsOrdinal.memRelOn (wellOrderTypeVal S Y hSwo))
        (wellOrderTypeVal S Y hSwo) S Y f :=
  (Classical.choose_spec <| existsUnique_ordinal_isOrderIso_of_wellOrderOn (S := S) (Y := Y) hSwo).1

noncomputable def wellOrderType
    [V ⊧ₘ* 𝗭𝗙] (S Y : V) (hSwo : IsWellOrderOn S Y) : Ordinal V :=
  { val := wellOrderTypeVal S Y hSwo
    ordinal := (wellOrderTypeVal_spec S Y hSwo).1 }

lemma wellOrderType_isOrderIso
    [V ⊧ₘ* 𝗭𝗙] (S Y : V) (hSwo : IsWellOrderOn S Y) :
    ∃ f : V, IsOrderIso
      (IsOrdinal.memRelOn (wellOrderType S Y hSwo).val) (wellOrderType S Y hSwo).val S Y f := by
  simpa [wellOrderType] using (wellOrderTypeVal_spec S Y hSwo).2

lemma wellOrderTypeVal_eq_iff_isOrderIso
    [V ⊧ₘ* 𝗭𝗙] {S Y α : V} (hSwo : IsWellOrderOn S Y) :
    α = wellOrderTypeVal S Y hSwo ↔
      IsOrdinal α ∧ ∃ f : V, IsOrderIso (IsOrdinal.memRelOn α) α S Y f := by
  constructor
  · intro hα
    simpa [hα] using wellOrderTypeVal_spec S Y hSwo
  · intro hα
    exact (existsUnique_ordinal_isOrderIso_of_wellOrderOn (S := S) (Y := Y) hSwo).unique
      hα (wellOrderTypeVal_spec S Y hSwo)

noncomputable def wellOrderTypeValTotal
    [V ⊧ₘ* 𝗭𝗙] (S Y : V) : V := by
  classical
  by_cases hSwo : IsWellOrderOn S Y
  · exact wellOrderTypeVal S Y hSwo
  · exact ∅

@[simp] lemma wellOrderTypeValTotal_of_wellOrderOn
    [V ⊧ₘ* 𝗭𝗙] {S Y : V} (hSwo : IsWellOrderOn S Y) :
    wellOrderTypeValTotal S Y = wellOrderTypeVal S Y hSwo := by
  simp [wellOrderTypeValTotal, hSwo]

@[simp] lemma wellOrderTypeValTotal_of_not_wellOrderOn
    [V ⊧ₘ* 𝗭𝗙] {S Y : V} (hSwo : ¬ IsWellOrderOn S Y) :
    wellOrderTypeValTotal S Y = ∅ := by
  simp [wellOrderTypeValTotal, hSwo]

lemma wellOrderTypeValTotal_eq_iff_wellOrder_or_fallback
    [V ⊧ₘ* 𝗭𝗙] (S Y α : V) :
    α = wellOrderTypeValTotal S Y ↔
      (IsWellOrderOn S Y ∧ IsOrdinal α ∧
        ∃ f : V, IsOrderIso (IsOrdinal.memRelOn α) α S Y f) ∨
      (¬IsWellOrderOn S Y ∧ α = ∅) := by
  by_cases hSwo : IsWellOrderOn S Y
  · constructor
    · intro hα
      left
      refine ⟨hSwo, ?_⟩
      have : α = wellOrderTypeVal S Y hSwo := by
        simpa [wellOrderTypeValTotal, hSwo] using hα
      exact (wellOrderTypeVal_eq_iff_isOrderIso (hSwo := hSwo)).1 this
    · rintro (⟨-, hα⟩ | hfalse)
      · have : α = wellOrderTypeVal S Y hSwo :=
          (wellOrderTypeVal_eq_iff_isOrderIso (hSwo := hSwo)).2 hα
        simpa [wellOrderTypeValTotal, hSwo] using this
      · exact (hfalse.1 hSwo).elim
  · constructor
    · intro hα
      right
      exact ⟨hSwo, by simpa [wellOrderTypeValTotal, hSwo] using hα⟩
    · rintro (hfalse | ⟨-, hα⟩)
      · exact (hSwo hfalse.1).elim
      · simpa [wellOrderTypeValTotal, hSwo] using hα

instance wellOrderTypeValTotal_eq_definable
    [V ⊧ₘ* 𝗭𝗙] :
    ℒₛₑₜ-relation₃[V] (fun α S Y ↦ α = wellOrderTypeValTotal S Y) := by
  let R : V → V → V → Prop := fun α S Y ↦
    (IsWellOrderOn S Y ∧ IsOrdinal α ∧
      ∃ f : V, IsOrderIso (IsOrdinal.memRelOn α) α S Y f) ∨
    (¬IsWellOrderOn S Y ∧ α = ∅)
  have hWdef : ℒₛₑₜ-relation[V] IsWellOrderOn := by
    unfold IsWellOrderOn IsStrictLinearOrderOn IsLeastOf
    definability
  have hR : ℒₛₑₜ-relation₃[V] R := by
    letI : ℒₛₑₜ-relation[V] IsWellOrderOn := hWdef
    letI : ℒₛₑₜ-function₁[V] IsOrdinal.memRelOn := IsOrdinal.memRelOn.definable
    letI : ℒₛₑₜ-relation₅[V] IsOrderIso := IsOrderIso.definable
    show ℒₛₑₜ-relation₃[V] (fun α S Y ↦
      (IsWellOrderOn S Y ∧ IsOrdinal α ∧
        ∃ f : V, IsOrderIso (IsOrdinal.memRelOn α) α S Y f) ∨
      (¬IsWellOrderOn S Y ∧ α = ∅))
    definability
  have hEq : (fun α S Y ↦ α = wellOrderTypeValTotal S Y) = R := by
    funext α S Y
    exact propext (wellOrderTypeValTotal_eq_iff_wellOrder_or_fallback S Y α)
  simpa [R, hEq] using hR

instance wellOrderTypeValTotal.definable
    [V ⊧ₘ* 𝗭𝗙] : ℒₛₑₜ-function₂[V] wellOrderTypeValTotal :=
  wellOrderTypeValTotal_eq_definable (V := V)

noncomputable def minimal (α : Ordinal V) (P : V → Prop) (hP : ℒₛₑₜ-predicate P := by definability) : Ordinal V where
  val := ⋂ˢ {x ∈ ↑α ; P x}
  ordinal := IsOrdinal.sInter fun ξ hξ ↦
    have : ξ ∈ (α : V) ∧ P ξ := by simpa using hξ
    IsOrdinal.of_mem this.1

section minimal

variable (P : V → Prop) (hP : ℒₛₑₜ-predicate P)

@[simp] lemma minimal_val (α : Ordinal V) : (minimal α P).val = ⋂ˢ {x ∈ ↑α ; P x} := rfl

@[simp] lemma minimal_bot_eq : minimal ⊥ P hP = ⊥ := by ext; simp [minimal_val]

variable {P hP}

private lemma minimal_prop_of_exists_aux (H : ∃ β < α, P β) :
    α.minimal P < α ∧ P (α.minimal P) ∧ ∀ ξ < α, P ξ → α.minimal P ≤ ξ := by
  let X := {x ∈ ↑α ; P x}
  have : IsNonempty X := by
    rcases H with ⟨β, hαβ, Pβ⟩
    exact ⟨β, by simp [X, lt_def.mp hαβ, Pβ]⟩
  have : ⋂ˢ X ∈ X := IsOrdinal.sInter_mem (X := X) fun β hβ ↦ by
    have : β ∈ α.val ∧ P β := by simpa [X] using hβ
    exact IsOrdinal.of_mem this.1
  have : ⋂ˢ X ∈ α.val ∧ P (⋂ˢ X) := by simpa [X] using this
  refine ⟨this.1, by simpa using this.2, ?_⟩
  intro ξ hξα Pξ
  suffices ⋂ˢ X ⊆ ξ from le_def.mpr (by simpa using this)
  apply sInter_subset_of_mem_of_nonempty
  simp [X, Pξ, lt_def.mp hξα]

lemma minimal_lt_of_exists (H : ∃ β < α, P β) : α.minimal P < α := (minimal_prop_of_exists_aux H).1

lemma minimal_prop_of_exists (H : ∃ β < α, P β) : P (α.minimal P) := (minimal_prop_of_exists_aux H).2.1

lemma minimal_le_of_exists_aux (H : ∃ β < α, P β) : ∀ ξ < α, P ξ → α.minimal P ≤ ξ := (minimal_prop_of_exists_aux H).2.2

lemma minimal_le_of_exists (H : ∃ β < α, P β) : ∀ ξ : Ordinal V, P ξ → α.minimal P ≤ ξ := by
  intro ξ Pξ
  rcases show ξ < α ∨ α ≤ ξ from lt_or_ge ξ α with (lt | le)
  · exact minimal_le_of_exists_aux H ξ lt Pξ
  · calc
      α.minimal P hP ≤ α := le_of_lt <| minimal_lt_of_exists H
      _              ≤ ξ := le

end minimal

end Ordinal

lemma exists_minimal (P : V → Prop) (hP : ℒₛₑₜ-predicate P) (h : ∃ α : Ordinal V, P α) :
    ∃ β : Ordinal V, P β ∧ ∀ ξ : Ordinal V, P ξ → β ≤ ξ := by
  rcases h with ⟨α, hα⟩
  have exs : ∃ β < α.succ, P β := ⟨α, by simp, hα⟩
  refine ⟨α.succ.minimal P, Ordinal.minimal_prop_of_exists exs, Ordinal.minimal_le_of_exists exs⟩

lemma exists_least_ordinal_of_exists
    (P : V → Prop) (hP : ℒₛₑₜ-predicate P)
    (h : ∃ α : V, IsOrdinal α ∧ P α) :
    ∃ α : V, IsOrdinal α ∧ P α ∧ ∀ ξ : V, IsOrdinal ξ → P ξ → α ⊆ ξ := by
  rcases h with ⟨α, hαord, hαP⟩
  let αo : Ordinal V := IsOrdinal.toOrdinal α
  have h' : ∃ β : Ordinal V, P β := ⟨αo, by simpa [αo] using hαP⟩
  rcases exists_minimal P hP h' with ⟨β, hβP, hβleast⟩
  refine ⟨β.val, β.ordinal, ?_, ?_⟩
  · simpa using hβP
  · intro ξ hξord hξP
    let ξo : Ordinal V := IsOrdinal.toOrdinal ξ
    have hβle : β ≤ ξo := hβleast ξo (by simpa [ξo] using hξP)
    simpa [Ordinal.le_def, ξo] using hβle

lemma strictIncreasing_function_no_value_lt_self
    (F : V → V)
    (hFdef : ℒₛₑₜ-function₁[V] F)
    (hFstrict : ∀ β γ : V, IsOrdinal β → IsOrdinal γ → β ∈ γ → F β ∈ F γ) :
    ∀ α : V, IsOrdinal α → ¬ F α ∈ α := by
  intro α hα
  by_contra hFαα
  let P : V → Prop := fun ξ ↦ F ξ ∈ ξ
  have hP : ℒₛₑₜ-predicate[V] P := by
    letI : ℒₛₑₜ-function₁[V] F := hFdef
    unfold P
    definability
  rcases exists_least_ordinal_of_exists (P := P) hP ⟨α, hα, hFαα⟩ with
    ⟨α₀, hα₀ord, hFα₀α₀, hleast⟩
  have hFα₀ord : IsOrdinal (F α₀) := IsOrdinal.of_mem hFα₀α₀
  have hFFα₀Fα₀ : F (F α₀) ∈ F α₀ := hFstrict (F α₀) α₀ hFα₀ord hα₀ord hFα₀α₀
  have hα₀_sub_Fα₀ : α₀ ⊆ F α₀ := hleast (F α₀) hFα₀ord hFFα₀Fα₀
  have : F α₀ ∈ F α₀ := hα₀_sub_Fα₀ _ hFα₀α₀
  exact (mem_irrefl (F α₀)) this

lemma strictIncreasing_function_subset_value
    (F : V → V)
    (hFdef : ℒₛₑₜ-function₁[V] F)
    (hFstrict : ∀ β γ : V, IsOrdinal β → IsOrdinal γ → β ∈ γ → F β ∈ F γ)
    (hFord : ∀ α : V, IsOrdinal α → IsOrdinal (F α)) :
    ∀ α : V, IsOrdinal α → α ⊆ F α := by
  intro α hα
  have hFαord : IsOrdinal (F α) := hFord α hα
  have hnot : ¬ F α ∈ α :=
    strictIncreasing_function_no_value_lt_self F hFdef hFstrict α hα
  letI : IsOrdinal α := hα
  letI : IsOrdinal (F α) := hFαord
  rcases IsOrdinal.mem_trichotomy (α := F α) (β := α) with (hFαα | hEq | hαFα)
  · exact (hnot hFαα).elim
  · simp [hEq]
  · exact (IsOrdinal.subset_iff (α := α) (β := F α)).2 (Or.inr hαFα)

lemma transfinite_induction (P : V → Prop) (hP : ℒₛₑₜ-predicate P)
    (ih : ∀ α : Ordinal V, (∀ β < α, P β) → P α) : ∀ α : Ordinal V, P α := by
  by_contra! exs
  have : ∃ β : Ordinal V, ¬P ↑β ∧ ∀ (ξ : Ordinal V), ¬P ↑ξ → β ≤ ξ :=
    exists_minimal (fun x ↦ ¬P x) (by definability) exs
  rcases this with ⟨β, Pβ, H⟩
  have : P β := ih β fun ξ hξβ ↦ by
    by_contra! Pξ
    have : β ≤ ξ := H ξ Pξ
    exact not_lt_of_ge this hξβ
  contradiction

/-! ### Well-foundedness -/

class IsWellFoundedRel (D : outParam (V → Prop)) (R : V → V → Prop) : Prop where
  wf : ∀ S : V, (∀ x ∈ S, D x) → IsNonempty S → ∃ z ∈ S, ∀ x ∈ S, ¬R x z

instance IsWellFoundedRel.mem : IsWellFoundedRel (fun _ : V ↦ True) (· ∈ ·) where
  wf S _ _ := foundation S

class SetLike (R : V → V → Prop) where
  leftSet (x : V) : ∃ y : V, ∀ z, z ∈ y ↔ R z x

namespace SetLike

variable (R : V → V → Prop) [SetLike R]

lemma left_existsUnique (x : V) : ∃! s : V, ∀ z, z ∈ s ↔ R z x := by
  have : ∃ y, ∀ z, z ∈ y ↔ R z x := leftSet x
  rcases this with ⟨y, hy⟩
  apply ExistsUnique.intro y hy
  intro y' hy'
  ext; simp_all

noncomputable def left (x : V) : V := Classical.choose! <| left_existsUnique R x

@[simp] lemma mem_left (x y : V) : y ∈ left R x ↔ R y x := Classical.choose!_spec (left_existsUnique R x) y

end SetLike

end LO.FirstOrder.SetTheory
