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

lemma succ_subset_of_mem [hα : IsOrdinal α] [hβ : IsOrdinal β] (h : α ∈ β) :
    succ α ⊆ β := by
  intro γ hγ
  rcases mem_succ_iff.mp hγ with (rfl | hγα)
  · exact h
  · exact hβ.transitive α h γ hγα

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

lemma strictLinearOrderOn_memRelOn_subset [hα : IsOrdinal α] {X : V}
    (hX : X ⊆ α) :
    IsStrictLinearOrderOn (memRelOn X) X := by
  refine ⟨memRelOn_subset_prod X, ?_, ?_, ?_⟩
  · intro x hx hxx
    exact (mem_irrefl x) ((kpair_mem_memRelOn_iff.mp hxx).2.2)
  · intro x hx y hy z hz hxy hyz
    have hxy' : x ∈ y := (kpair_mem_memRelOn_iff.mp hxy).2.2
    have hyz' : y ∈ z := (kpair_mem_memRelOn_iff.mp hyz).2.2
    have hzα : z ∈ α := hX z hz
    have hzord : IsOrdinal z := hα.of_mem hzα
    exact kpair_mem_memRelOn_iff.mpr ⟨hx, hz, hzord.toIsTransitive.transitive _ hyz' _ hxy'⟩
  · intro x hx y hy
    have hxα : x ∈ α := hX x hx
    have hyα : y ∈ α := hX y hy
    rcases hα.trichotomy x hxα y hyα with (hxy | hEq | hyx)
    · exact Or.inl <| kpair_mem_memRelOn_iff.mpr ⟨hx, hy, hxy⟩
    · exact Or.inr (Or.inl hEq)
    · exact Or.inr (Or.inr <| kpair_mem_memRelOn_iff.mpr ⟨hy, hx, hyx⟩)

lemma wellOrderOn_memRelOn_subset [hα : IsOrdinal α] {X : V}
    (hX : X ⊆ α) :
    IsWellOrderOn (memRelOn X) X := by
  refine ⟨strictLinearOrderOn_memRelOn_subset (α := α) hX, ?_⟩
  intro A hAX hAne
  have hANonempty : IsNonempty A := ne_empty_iff_isNonempty.mp hAne
  have hMin : ∃ m ∈ A, ∀ a ∈ A, a ∉ m := by
    simpa using foundation A
  rcases hMin with ⟨m, hmA, hmLeast⟩
  refine ⟨m, hmA, ?_⟩
  intro a haA
  have hmX : m ∈ X := hAX _ hmA
  have haX : a ∈ X := hAX _ haA
  have hmα : m ∈ α := hX _ hmX
  have haα : a ∈ α := hX _ haX
  rcases hα.trichotomy m hmα a haα with (hma | hEq | ham)
  · exact Or.inr <| kpair_mem_memRelOn_iff.mpr ⟨hmX, haX, hma⟩
  · exact Or.inl hEq.symm
  · exact (hmLeast a haA ham).elim

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

def IsLimitOrdinal (α : V) : Prop :=
  IsOrdinal α ∧ α ≠ 0 ∧ ¬ ∃ β, α = succ β

instance IsLimitOrdinal.definable : ℒₛₑₜ-predicate[V] IsLimitOrdinal := by
  unfold IsLimitOrdinal
  definability

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

/-! ### Hartogs theorem -/

def IsWellOrderSubsetCodeCollection (X α C : V) : Prop :=
  ∀ p : V, p ∈ C ↔
    p ∈ ℘ X ×ˢ ℘ (X ×ˢ X) ∧
      ∃ Y S, p = ⟨Y, S⟩ₖ ∧ IsWellOrderOn S Y ∧
        ∃ f : V, IsOrderIso (IsOrdinal.memRelOn α) α S Y f

instance IsWellOrderSubsetCodeCollection.definable :
    ℒₛₑₜ-relation₃[V] IsWellOrderSubsetCodeCollection := by
  have hWdef : ℒₛₑₜ-relation[V] IsWellOrderOn := by
    unfold IsWellOrderOn IsStrictLinearOrderOn IsLeastOf
    definability
  letI : ℒₛₑₜ-relation[V] IsWellOrderOn := hWdef
  letI : ℒₛₑₜ-function₁[V] IsOrdinal.memRelOn := IsOrdinal.memRelOn.definable
  letI : ℒₛₑₜ-relation₅[V] IsOrderIso := IsOrderIso.definable
  unfold IsWellOrderSubsetCodeCollection
  definability

lemma existsUnique_wellOrderSubsetCodeCollection
    (X α : V) :
    ∃! C : V, C ∈ ℘ (℘ X ×ˢ ℘ (X ×ˢ X)) ∧ IsWellOrderSubsetCodeCollection X α C := by
  let P : V → Prop := fun p ↦
    ∃ Y S, p = ⟨Y, S⟩ₖ ∧ IsWellOrderOn S Y ∧
      ∃ f : V, IsOrderIso (IsOrdinal.memRelOn α) α S Y f
  have hP : ℒₛₑₜ-predicate[V] P := by
    have hWdef : ℒₛₑₜ-relation[V] IsWellOrderOn := by
      unfold IsWellOrderOn IsStrictLinearOrderOn IsLeastOf
      definability
    letI : ℒₛₑₜ-relation[V] IsWellOrderOn := hWdef
    letI : ℒₛₑₜ-function₁[V] IsOrdinal.memRelOn := IsOrdinal.memRelOn.definable
    letI : ℒₛₑₜ-relation₅[V] IsOrderIso := IsOrderIso.definable
    unfold P
    definability
  rcases separation_existsUnique (℘ X ×ˢ ℘ (X ×ˢ X)) P hP with ⟨C, hC, hCuniq⟩
  refine ⟨C, ?_, ?_⟩
  · have hCsub : C ⊆ ℘ X ×ˢ ℘ (X ×ˢ X) := by
      intro p hp
      exact (hC p).1 hp |>.1
    exact ⟨mem_power_iff.mpr hCsub, hC⟩
  · intro C' hC'
    exact hCuniq C' hC'.2

private lemma isWellOrderOn_of_isOrderIso_of_subset_prod
    {R X S Y f : V}
    (hRwo : IsWellOrderOn R X)
    (hSsub : S ⊆ Y ×ˢ Y)
    (hIso : IsOrderIso R X S Y f) :
    IsWellOrderOn S Y := by
  have hInv : IsOrderIso S Y R X (inverse f) := hIso.inv
  refine ⟨⟨hSsub, ?_, ?_, ?_⟩, ?_⟩
  · intro y hyY hyy
    rcases exists_of_mem_function hInv.mem_function y hyY with ⟨x, hxX, hyxInv⟩
    have hyVal : (inverse f) ‘ y = x := value_eq_of_kpair_mem hInv.mem_function hyxInv
    have hxx : ⟨x, x⟩ₖ ∈ R := by
      have : ⟨(inverse f) ‘ y, (inverse f) ‘ y⟩ₖ ∈ R := (hInv.rel_iff hyY hyY).1 hyy
      simpa [hyVal] using this
    exact hRwo.1.irrefl hxX hxx
  · intro y₁ hy₁ y₂ hy₂ y₃ hy₃ hy₁₂ hy₂₃
    rcases exists_of_mem_function hInv.mem_function y₁ hy₁ with ⟨x₁, hx₁X, hy₁x₁⟩
    rcases exists_of_mem_function hInv.mem_function y₂ hy₂ with ⟨x₂, hx₂X, hy₂x₂⟩
    rcases exists_of_mem_function hInv.mem_function y₃ hy₃ with ⟨x₃, hx₃X, hy₃x₃⟩
    have hy₁Val : (inverse f) ‘ y₁ = x₁ := value_eq_of_kpair_mem hInv.mem_function hy₁x₁
    have hy₂Val : (inverse f) ‘ y₂ = x₂ := value_eq_of_kpair_mem hInv.mem_function hy₂x₂
    have hy₃Val : (inverse f) ‘ y₃ = x₃ := value_eq_of_kpair_mem hInv.mem_function hy₃x₃
    have hx₁₂ : ⟨x₁, x₂⟩ₖ ∈ R := by
      have : ⟨(inverse f) ‘ y₁, (inverse f) ‘ y₂⟩ₖ ∈ R := (hInv.rel_iff hy₁ hy₂).1 hy₁₂
      simpa [hy₁Val, hy₂Val] using this
    have hx₂₃ : ⟨x₂, x₃⟩ₖ ∈ R := by
      have : ⟨(inverse f) ‘ y₂, (inverse f) ‘ y₃⟩ₖ ∈ R := (hInv.rel_iff hy₂ hy₃).1 hy₂₃
      simpa [hy₂Val, hy₃Val] using this
    have hx₁₃ : ⟨x₁, x₃⟩ₖ ∈ R := hRwo.1.trans hx₁X hx₂X hx₃X hx₁₂ hx₂₃
    exact (hInv.rel_iff hy₁ hy₃).2 (by simpa [hy₁Val, hy₃Val] using hx₁₃)
  · intro y₁ hy₁ y₂ hy₂
    rcases exists_of_mem_function hInv.mem_function y₁ hy₁ with ⟨x₁, hx₁X, hy₁x₁⟩
    rcases exists_of_mem_function hInv.mem_function y₂ hy₂ with ⟨x₂, hx₂X, hy₂x₂⟩
    rcases hRwo.1.trichotomy hx₁X hx₂X with (hx₁₂ | hEq | hx₂₁)
    · exact Or.inl <|
        (hInv.rel_iff hy₁ hy₂).2 <| by
          have hy₁Val : (inverse f) ‘ y₁ = x₁ := value_eq_of_kpair_mem hInv.mem_function hy₁x₁
          have hy₂Val : (inverse f) ‘ y₂ = x₂ := value_eq_of_kpair_mem hInv.mem_function hy₂x₂
          simpa [hy₁Val, hy₂Val] using hx₁₂
    · have hyEq : y₁ = y₂ := by
        have hy₂x₁ : ⟨y₂, x₁⟩ₖ ∈ inverse f := by simpa [hEq] using hy₂x₂
        exact hInv.injective _ _ _ hy₁x₁ hy₂x₁
      exact Or.inr <| Or.inl hyEq
    · exact Or.inr <| Or.inr <|
        (hInv.rel_iff hy₂ hy₁).2 <| by
          have hy₁Val : (inverse f) ‘ y₁ = x₁ := value_eq_of_kpair_mem hInv.mem_function hy₁x₁
          have hy₂Val : (inverse f) ‘ y₂ = x₂ := value_eq_of_kpair_mem hInv.mem_function hy₂x₂
          simpa [hy₁Val, hy₂Val] using hx₂₁
  · intro A hAY hAne
    let B : V := (inverse f) “ A
    have hBsub : B ⊆ X := image_subset_of_mem_function hInv.mem_function
    have hBne : B ≠ ∅ := by
      rcases ne_empty_iff_isNonempty.mp hAne with ⟨a, haA⟩
      have haY : a ∈ Y := hAY _ haA
      rcases exists_of_mem_function hInv.mem_function a haY with ⟨x, -, haxInv⟩
      have hxB : x ∈ B := mem_image_iff.mpr ⟨a, haA, haxInv⟩
      intro hB0
      rw [hB0] at hxB
      simp at hxB
    rcases hRwo.2 B hBsub hBne with ⟨m, hmB, hmLeast⟩
    rcases mem_image_iff.mp hmB with ⟨y, hyA, hymInv⟩
    have hyY : y ∈ Y := hAY _ hyA
    have hyVal : (inverse f) ‘ y = m := value_eq_of_kpair_mem hInv.mem_function hymInv
    refine ⟨y, hyA, ?_⟩
    intro a haA
    have haY : a ∈ Y := hAY _ haA
    rcases exists_of_mem_function hInv.mem_function a haY with ⟨x, -, haxInv⟩
    have hxB : x ∈ B := mem_image_iff.mpr ⟨a, haA, haxInv⟩
    have haVal : (inverse f) ‘ a = x := value_eq_of_kpair_mem hInv.mem_function haxInv
    rcases hmLeast x hxB with (hxm | hmx)
    · left
      have haxInv' : ⟨a, m⟩ₖ ∈ inverse f := by simpa [hxm] using haxInv
      exact hInv.injective _ _ _ haxInv' hymInv
    · right
      exact (hInv.rel_iff hyY haY).2 (by simpa [hyVal, haVal] using hmx)

lemma exists_wellOrderOn_subset_isOrderIso_of_cardLE
    {α X : V}
    (hαord : IsOrdinal α)
    (hαX : α ≤# X) :
    ∃ Y S f, Y ⊆ X ∧ IsWellOrderOn S Y ∧ IsOrderIso (IsOrdinal.memRelOn α) α S Y f := by
  letI : IsOrdinal α := hαord
  rcases hαX with ⟨f, hf, hfInj⟩
  let Y : V := range f
  let S : V := {p ∈ Y ×ˢ Y ; ∃ x₁ ∈ α, ∃ x₂ ∈ α, p = ⟨f ‘ x₁, f ‘ x₂⟩ₖ ∧ x₁ ∈ x₂}
  have hSsub : S ⊆ Y ×ˢ Y := sep_subset
  have hIso : IsOrderIso (IsOrdinal.memRelOn α) α S Y f := by
    refine ⟨mem_function_range_of_mem_function hf, hfInj, rfl, ?_⟩
    intro x₁ hx₁ x₂ hx₂
    constructor
    · intro hx₁₂
      have hy₁ : f ‘ x₁ ∈ Y := by simpa [Y] using value_mem_range hf hx₁
      have hy₂ : f ‘ x₂ ∈ Y := by simpa [Y] using value_mem_range hf hx₂
      refine mem_sep_iff.mpr ?_
      refine ⟨by simpa [mem_prod_iff] using And.intro hy₁ hy₂, x₁, hx₁, x₂, hx₂, rfl, ?_⟩
      exact (IsOrdinal.kpair_mem_memRelOn_iff.mp hx₁₂).2.2
    · intro hy₁₂
      rcases mem_sep_iff.mp hy₁₂ with ⟨-, u, huα, v, hvα, hEq, huv⟩
      rcases kpair_inj hEq with ⟨huVal, hvVal⟩
      letI : IsFunction f := IsFunction.of_mem hf
      have hx₁dom : x₁ ∈ domain f := by simpa [domain_eq_of_mem_function hf] using hx₁
      have hx₂dom : x₂ ∈ domain f := by simpa [domain_eq_of_mem_function hf] using hx₂
      have hudom : u ∈ domain f := by simpa [domain_eq_of_mem_function hf] using huα
      have hvdom : v ∈ domain f := by simpa [domain_eq_of_mem_function hf] using hvα
      have hx₁pair : ⟨x₁, f ‘ x₁⟩ₖ ∈ f :=
        (IsFunction.value_eq_iff_kpair_mem (f := f) (x := x₁) (y := f ‘ x₁) hx₁dom).mp rfl
      have hx₂pair : ⟨x₂, f ‘ x₂⟩ₖ ∈ f :=
        (IsFunction.value_eq_iff_kpair_mem (f := f) (x := x₂) (y := f ‘ x₂) hx₂dom).mp rfl
      have hupair : ⟨u, f ‘ u⟩ₖ ∈ f :=
        (IsFunction.value_eq_iff_kpair_mem (f := f) (x := u) (y := f ‘ u) hudom).mp rfl
      have hvpair : ⟨v, f ‘ v⟩ₖ ∈ f :=
        (IsFunction.value_eq_iff_kpair_mem (f := f) (x := v) (y := f ‘ v) hvdom).mp rfl
      have hux : u = x₁ := by
        exact (hfInj _ _ _ hx₁pair (by simpa [huVal] using hupair)).symm
      have hvx : v = x₂ := by
        exact (hfInj _ _ _ hx₂pair (by simpa [hvVal] using hvpair)).symm
      exact IsOrdinal.kpair_mem_memRelOn_iff.mpr ⟨hx₁, hx₂, by simpa [hux, hvx] using huv⟩
  have hSwo : IsWellOrderOn S Y :=
    isWellOrderOn_of_isOrderIso_of_subset_prod
      (hRwo := IsOrdinal.wellOrderOn_memRelOn (α := α))
      hSsub hIso
  exact ⟨Y, S, f, range_subset_of_mem_function hf, hSwo, hIso⟩

lemma exists_ordinal_not_cardLE
    [V ⊧ₘ* 𝗭𝗙] (X : V) :
    ∃ α : V, IsOrdinal α ∧ ¬ α ≤# X := by
  by_contra hNo
  have hAll : ∀ α : V, IsOrdinal α → α ≤# X := by
    intro α hαord
    by_contra hαX
    exact hNo ⟨α, hαord, hαX⟩
  let R : V → V → Prop := fun α C ↦ IsWellOrderSubsetCodeCollection X α C
  have hRdef : ℒₛₑₜ-relation[V] R := by
    letI : ℒₛₑₜ-relation₃[V] IsWellOrderSubsetCodeCollection :=
      IsWellOrderSubsetCodeCollection.definable (V := V)
    unfold R
    definability
  have hRfun : ∀ α : V, IsOrdinal α → ∃! C : V, C ∈ ℘ (℘ X ×ˢ ℘ (X ×ˢ X)) ∧ R α C := by
    intro α hαord
    simpa [R] using existsUnique_wellOrderSubsetCodeCollection (V := V) X α
  have hRinj :
      ∀ α β C : V, IsOrdinal α → IsOrdinal β → R α C → R β C → α = β := by
    intro α β C hαord hβord hαC hβC
    rcases exists_wellOrderOn_subset_isOrderIso_of_cardLE (α := α) (X := X) hαord (hAll α hαord) with
      ⟨Y, S, f, hYX, hSwo, hIso⟩
    have hCode : ⟨Y, S⟩ₖ ∈ C := by
      refine (hαC _).2 ?_
      refine ⟨?_, Y, S, rfl, hSwo, f, hIso⟩
      refine mem_prod_iff.mpr ⟨Y, mem_power_iff.mpr hYX, S, ?_, rfl⟩
      refine mem_power_iff.mpr ?_
      exact subset_trans hSwo.1.subset_prod (prod_subset_prod_of_subset hYX hYX)
    rcases (hβC _).1 hCode with ⟨-, Y', S', hPair, hSwo', g, hg⟩
    rcases kpair_inj hPair with ⟨rfl, rfl⟩
    exact (existsUnique_ordinal_isOrderIso_of_wellOrderOn (S := S) (Y := Y) hSwo).unique
      ⟨hαord, ⟨f, hIso⟩⟩
      ⟨hβord, ⟨g, hg⟩⟩
  have : ¬ (∀ α β C : V, IsOrdinal α → IsOrdinal β → R α C → R β C → α = β) :=
    IsOrdinal.not_injective_functionLike_relation_to_set
      (X := ℘ (℘ X ×ˢ ℘ (X ×ˢ X))) (R := R) hRdef hRfun
  exact this hRinj

lemma exists_ordinal_not_injective_into
    [V ⊧ₘ* 𝗭𝗙] (X : V) :
    ∃ α : V, IsOrdinal α ∧ ¬ ∃ f ∈ X ^ α, Injective f := by
  simpa [CardLE] using exists_ordinal_not_cardLE (V := V) X

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

noncomputable def ordinalMax (α β : V) : V := α ∪ β

instance ordinalMax.definable : ℒₛₑₜ-function₂[V] ordinalMax := by
  simpa [ordinalMax] using (union.definable (V := V) : ℒₛₑₜ-function₂[V] Union.union)

lemma ordinalMax_isOrdinal {α β : V} (hα : IsOrdinal α) (hβ : IsOrdinal β) :
    IsOrdinal (ordinalMax α β) := by
  rcases IsOrdinal.subset_or_supset (α := α) (β := β) with (hαβ | hβα)
  · have : ordinalMax α β = β := by
      exact union_eq_iff_left.mpr hαβ
    simpa [this] using hβ
  · have : ordinalMax α β = α := by
      exact union_eq_iff_right.mpr hβα
    simpa [this] using hα

def IsOrdinalPair (p : V) : Prop :=
  ∃ α β : V, p = ⟨α, β⟩ₖ ∧ IsOrdinal α ∧ IsOrdinal β

instance IsOrdinalPair.definable : ℒₛₑₜ-predicate[V] IsOrdinalPair := by
  letI : ℒₛₑₜ-function₂[V] kpair := kpair.definable
  letI : ℒₛₑₜ-predicate[V] IsOrdinal := IsOrdinal.definable
  unfold IsOrdinalPair
  definability

namespace IsOrdinalPair

lemma mk {α β : V} (hα : IsOrdinal α) (hβ : IsOrdinal β) :
    IsOrdinalPair ⟨α, β⟩ₖ := ⟨α, β, rfl, hα, hβ⟩

lemma fst {p : V} (hp : IsOrdinalPair p) : IsOrdinal (kpair.π₁ p) := by
  rcases hp with ⟨α, β, rfl, hα, hβ⟩
  simpa using hα

lemma snd {p : V} (hp : IsOrdinalPair p) : IsOrdinal (kpair.π₂ p) := by
  rcases hp with ⟨α, β, rfl, hα, hβ⟩
  simpa using hβ

lemma eq_kpair_proj {p : V} (hp : IsOrdinalPair p) :
    p = ⟨kpair.π₁ p, kpair.π₂ p⟩ₖ := by
  rcases hp with ⟨α, β, rfl, hα, hβ⟩
  simp

lemma max_isOrdinal {p : V} (hp : IsOrdinalPair p) :
    IsOrdinal (ordinalMax (kpair.π₁ p) (kpair.π₂ p)) :=
  ordinalMax_isOrdinal hp.fst hp.snd

end IsOrdinalPair

def OrdinalLex2 (α₁ β₁ α₂ β₂ : V) : Prop :=
  α₁ ∈ α₂ ∨ (α₁ = α₂ ∧ β₁ ∈ β₂)

def OrdinalLex3 (α₁ β₁ γ₁ α₂ β₂ γ₂ : V) : Prop :=
  α₁ ∈ α₂ ∨ (α₁ = α₂ ∧ OrdinalLex2 β₁ γ₁ β₂ γ₂)

private lemma ordinalLex2_irrefl {α β : V} :
    ¬ OrdinalLex2 α β α β := by
  intro h
  rcases h with h | ⟨hEq, hββ⟩
  · exact (mem_irrefl α h).elim
  · exact (mem_irrefl β hββ).elim

omit [Nonempty V] [V ⊧ₘ* 𝗭] in
private lemma ordinalLex2_trans
    {α₁ β₁ α₂ β₂ α₃ β₃ : V}
    (hα₃ : IsOrdinal α₃) (hβ₃ : IsOrdinal β₃)
    (h₁₂ : OrdinalLex2 α₁ β₁ α₂ β₂)
    (h₂₃ : OrdinalLex2 α₂ β₂ α₃ β₃) :
    OrdinalLex2 α₁ β₁ α₃ β₃ := by
  rcases h₁₂ with hα₁₂ | ⟨hαEq, hβ₁₂⟩
  · rcases h₂₃ with hα₂₃ | ⟨hαEq', hβ₂₃⟩
    · exact Or.inl <| hα₃.toIsTransitive.transitive _ hα₂₃ _ hα₁₂
    · exact Or.inl <| by simpa [hαEq'] using hα₁₂
  · rcases h₂₃ with hα₂₃ | ⟨hαEq', hβ₂₃⟩
    · exact Or.inl <| by simpa [hαEq] using hα₂₃
    · refine Or.inr ?_
      refine ⟨hαEq.trans hαEq', ?_⟩
      exact hβ₃.toIsTransitive.transitive _ hβ₂₃ _ hβ₁₂

private lemma ordinalLex2_trichotomy
    {α₁ β₁ α₂ β₂ : V}
    (hα₁ : IsOrdinal α₁) (hβ₁ : IsOrdinal β₁)
    (hα₂ : IsOrdinal α₂) (hβ₂ : IsOrdinal β₂) :
    OrdinalLex2 α₁ β₁ α₂ β₂ ∨
      (α₁ = α₂ ∧ β₁ = β₂) ∨
      OrdinalLex2 α₂ β₂ α₁ β₁ := by
  rcases IsOrdinal.mem_trichotomy (α := α₁) (β := α₂) with (hα₁₂ | hαEq | hα₂₁)
  · exact Or.inl <| Or.inl hα₁₂
  · rcases IsOrdinal.mem_trichotomy (α := β₁) (β := β₂) with (hβ₁₂ | hβEq | hβ₂₁)
    · exact Or.inl <| Or.inr ⟨hαEq, hβ₁₂⟩
    · exact Or.inr <| Or.inl ⟨hαEq, hβEq⟩
    · exact Or.inr <| Or.inr <| Or.inr ⟨hαEq.symm, hβ₂₁⟩
  · exact Or.inr <| Or.inr <| Or.inl hα₂₁

private lemma ordinalLex3_irrefl {α β γ : V} :
    ¬ OrdinalLex3 α β γ α β γ := by
  intro h
  rcases h with h | ⟨hEq, hrest⟩
  · exact (mem_irrefl α h).elim
  · exact ordinalLex2_irrefl hrest

omit [Nonempty V] [V ⊧ₘ* 𝗭] in
private lemma ordinalLex3_trans
    {α₁ β₁ γ₁ α₂ β₂ γ₂ α₃ β₃ γ₃ : V}
    (hα₃ : IsOrdinal α₃) (hβ₃ : IsOrdinal β₃) (hγ₃ : IsOrdinal γ₃)
    (h₁₂ : OrdinalLex3 α₁ β₁ γ₁ α₂ β₂ γ₂)
    (h₂₃ : OrdinalLex3 α₂ β₂ γ₂ α₃ β₃ γ₃) :
    OrdinalLex3 α₁ β₁ γ₁ α₃ β₃ γ₃ := by
  rcases h₁₂ with hα₁₂ | ⟨hαEq, hrest₁₂⟩
  · rcases h₂₃ with hα₂₃ | ⟨hαEq', hrest₂₃⟩
    · exact Or.inl <| hα₃.toIsTransitive.transitive _ hα₂₃ _ hα₁₂
    · exact Or.inl <| by simpa [hαEq'] using hα₁₂
  · rcases h₂₃ with hα₂₃ | ⟨hαEq', hrest₂₃⟩
    · exact Or.inl <| by simpa [hαEq] using hα₂₃
    · refine Or.inr ?_
      refine ⟨hαEq.trans hαEq', ?_⟩
      exact ordinalLex2_trans hβ₃ hγ₃ hrest₁₂ hrest₂₃

private lemma ordinalLex3_trichotomy
    {α₁ β₁ γ₁ α₂ β₂ γ₂ : V}
    (hα₁ : IsOrdinal α₁) (hβ₁ : IsOrdinal β₁) (hγ₁ : IsOrdinal γ₁)
    (hα₂ : IsOrdinal α₂) (hβ₂ : IsOrdinal β₂) (hγ₂ : IsOrdinal γ₂) :
    OrdinalLex3 α₁ β₁ γ₁ α₂ β₂ γ₂ ∨
      (β₁ = β₂ ∧ γ₁ = γ₂) ∨
      OrdinalLex3 α₂ β₂ γ₂ α₁ β₁ γ₁ := by
  rcases IsOrdinal.mem_trichotomy (α := α₁) (β := α₂) with (hα₁₂ | hαEq | hα₂₁)
  · exact Or.inl <| Or.inl hα₁₂
  · rcases ordinalLex2_trichotomy hβ₁ hγ₁ hβ₂ hγ₂ with (hrest | hEq | hrest)
    · exact Or.inl <| Or.inr ⟨hαEq, hrest⟩
    · exact Or.inr <| Or.inl hEq
    · exact Or.inr <| Or.inr <| Or.inr ⟨hαEq.symm, hrest⟩
  · exact Or.inr <| Or.inr <| Or.inl hα₂₁

def OrdinalPairLT (p q : V) : Prop :=
  IsOrdinalPair p ∧ IsOrdinalPair q ∧
    OrdinalLex3
      (ordinalMax (kpair.π₁ p) (kpair.π₂ p)) (kpair.π₁ p) (kpair.π₂ p)
      (ordinalMax (kpair.π₁ q) (kpair.π₂ q)) (kpair.π₁ q) (kpair.π₂ q)

instance OrdinalPairLT.definable : ℒₛₑₜ-relation[V] OrdinalPairLT := by
  letI : ℒₛₑₜ-predicate[V] IsOrdinalPair := IsOrdinalPair.definable
  letI : ℒₛₑₜ-function₂[V] ordinalMax := ordinalMax.definable (V := V)
  letI : ℒₛₑₜ-function₁[V] kpair.π₁ := kpair.π₁.definable
  letI : ℒₛₑₜ-function₁[V] kpair.π₂ := kpair.π₂.definable
  unfold OrdinalPairLT OrdinalLex3 OrdinalLex2
  definability

private lemma ordinalPairLT_kpair_iff_of_ordinals
    {α₁ β₁ α₂ β₂ : V}
    (hα₁ : IsOrdinal α₁) (hβ₁ : IsOrdinal β₁)
    (hα₂ : IsOrdinal α₂) (hβ₂ : IsOrdinal β₂) :
    OrdinalPairLT ⟨α₁, β₁⟩ₖ ⟨α₂, β₂⟩ₖ ↔
      OrdinalLex3
        (ordinalMax α₁ β₁) α₁ β₁
        (ordinalMax α₂ β₂) α₂ β₂ := by
  simp [OrdinalPairLT, IsOrdinalPair, OrdinalLex3, OrdinalLex2, hα₁, hβ₁, hα₂, hβ₂]

lemma ordinalPairLT_irrefl {p : V} (hp : IsOrdinalPair p) : ¬ OrdinalPairLT p p := by
  rcases hp with ⟨α, β, rfl, hα, hβ⟩
  have hμ : IsOrdinal (ordinalMax α β) := ordinalMax_isOrdinal hα hβ
  rw [ordinalPairLT_kpair_iff_of_ordinals hα hβ hα hβ]
  exact ordinalLex3_irrefl

lemma ordinalPairLT_trans {p q r : V}
    (hp : IsOrdinalPair p) (hq : IsOrdinalPair q) (hr : IsOrdinalPair r)
    (hpq : OrdinalPairLT p q) (hqr : OrdinalPairLT q r) :
    OrdinalPairLT p r := by
  rcases hp with ⟨α₁, β₁, rfl, hα₁, hβ₁⟩
  rcases hq with ⟨α₂, β₂, rfl, hα₂, hβ₂⟩
  rcases hr with ⟨α₃, β₃, rfl, hα₃, hβ₃⟩
  have hμ₁ : IsOrdinal (ordinalMax α₁ β₁) := ordinalMax_isOrdinal hα₁ hβ₁
  have hμ₂ : IsOrdinal (ordinalMax α₂ β₂) := ordinalMax_isOrdinal hα₂ hβ₂
  have hμ₃ : IsOrdinal (ordinalMax α₃ β₃) := ordinalMax_isOrdinal hα₃ hβ₃
  rw [ordinalPairLT_kpair_iff_of_ordinals hα₁ hβ₁ hα₃ hβ₃]
  rw [ordinalPairLT_kpair_iff_of_ordinals hα₁ hβ₁ hα₂ hβ₂] at hpq
  rw [ordinalPairLT_kpair_iff_of_ordinals hα₂ hβ₂ hα₃ hβ₃] at hqr
  exact ordinalLex3_trans hμ₃ hα₃ hβ₃ hpq hqr

lemma ordinalPairLT_trichotomy {p q : V}
    (hp : IsOrdinalPair p) (hq : IsOrdinalPair q) :
    OrdinalPairLT p q ∨ p = q ∨ OrdinalPairLT q p := by
  rcases hp with ⟨α₁, β₁, rfl, hα₁, hβ₁⟩
  rcases hq with ⟨α₂, β₂, rfl, hα₂, hβ₂⟩
  have hμ₁ : IsOrdinal (ordinalMax α₁ β₁) := ordinalMax_isOrdinal hα₁ hβ₁
  have hμ₂ : IsOrdinal (ordinalMax α₂ β₂) := ordinalMax_isOrdinal hα₂ hβ₂
  rcases ordinalLex3_trichotomy hμ₁ hα₁ hβ₁ hμ₂ hα₂ hβ₂ with (h | hEq | h)
  · left
    exact (ordinalPairLT_kpair_iff_of_ordinals hα₁ hβ₁ hα₂ hβ₂).2 h
  · rcases hEq with ⟨hαEq, hβEq⟩
    right
    left
    simpa [kpair_iff] using And.intro hαEq hβEq
  · right
    right
    exact (ordinalPairLT_kpair_iff_of_ordinals hα₂ hβ₂ hα₁ hβ₁).2 h

lemma exists_least_ordinalPairLT_of_ne_empty {A : V}
    (hA : ∀ p ∈ A, IsOrdinalPair p) (hAne : A ≠ ∅) :
    ∃ m, m ∈ A ∧ ∀ p ∈ A, p = m ∨ OrdinalPairLT m p := by
  let MaxProp : V → Prop := fun μ ↦
    ∃ p ∈ A, ordinalMax (kpair.π₁ p) (kpair.π₂ p) = μ
  have hMaxProp : ℒₛₑₜ-predicate[V] MaxProp := by
    letI : ℒₛₑₜ-function₂[V] ordinalMax := ordinalMax.definable (V := V)
    letI : ℒₛₑₜ-function₁[V] kpair.π₁ := kpair.π₁.definable
    letI : ℒₛₑₜ-function₁[V] kpair.π₂ := kpair.π₂.definable
    change ℒₛₑₜ-predicate[V] (fun μ ↦
      ∃ p ∈ A, ordinalMax (kpair.π₁ p) (kpair.π₂ p) = μ)
    definability
  have hMaxExists : ∃ μ : V, IsOrdinal μ ∧ MaxProp μ := by
    rcases ne_empty_iff_isNonempty.mp hAne with ⟨p, hpA⟩
    have hpOrd : IsOrdinalPair p := hA p hpA
    exact ⟨ordinalMax (kpair.π₁ p) (kpair.π₂ p), hpOrd.max_isOrdinal, ⟨p, hpA, rfl⟩⟩
  rcases exists_least_ordinal_of_exists (P := MaxProp) hMaxProp hMaxExists with
    ⟨μ, hμord, hμProp, hμleast⟩
  let FstProp : V → Prop := fun α ↦
    ∃ p ∈ A, ordinalMax (kpair.π₁ p) (kpair.π₂ p) = μ ∧ kpair.π₁ p = α
  have hFstProp : ℒₛₑₜ-predicate[V] FstProp := by
    letI : ℒₛₑₜ-function₂[V] ordinalMax := ordinalMax.definable (V := V)
    letI : ℒₛₑₜ-function₁[V] kpair.π₁ := kpair.π₁.definable
    letI : ℒₛₑₜ-function₁[V] kpair.π₂ := kpair.π₂.definable
    change ℒₛₑₜ-predicate[V] (fun α ↦
      ∃ p ∈ A, ordinalMax (kpair.π₁ p) (kpair.π₂ p) = μ ∧ kpair.π₁ p = α)
    definability
  have hFstExists : ∃ α : V, IsOrdinal α ∧ FstProp α := by
    rcases hμProp with ⟨p, hpA, hpμ⟩
    have hpOrd : IsOrdinalPair p := hA p hpA
    exact ⟨kpair.π₁ p, hpOrd.fst, ⟨p, hpA, hpμ, rfl⟩⟩
  rcases exists_least_ordinal_of_exists (P := FstProp) hFstProp hFstExists with
    ⟨α, hαord, hαProp, hαleast⟩
  let SndProp : V → Prop := fun β ↦
    ∃ p ∈ A, ordinalMax (kpair.π₁ p) (kpair.π₂ p) = μ ∧ kpair.π₁ p = α ∧ kpair.π₂ p = β
  have hSndProp : ℒₛₑₜ-predicate[V] SndProp := by
    letI : ℒₛₑₜ-function₂[V] ordinalMax := ordinalMax.definable (V := V)
    letI : ℒₛₑₜ-function₁[V] kpair.π₁ := kpair.π₁.definable
    letI : ℒₛₑₜ-function₁[V] kpair.π₂ := kpair.π₂.definable
    change ℒₛₑₜ-predicate[V] (fun β ↦
      ∃ p ∈ A, ordinalMax (kpair.π₁ p) (kpair.π₂ p) = μ ∧ kpair.π₁ p = α ∧ kpair.π₂ p = β)
    definability
  have hSndExists : ∃ β : V, IsOrdinal β ∧ SndProp β := by
    rcases hαProp with ⟨p, hpA, hpμ, hpα⟩
    have hpOrd : IsOrdinalPair p := hA p hpA
    exact ⟨kpair.π₂ p, hpOrd.snd, ⟨p, hpA, hpμ, hpα, rfl⟩⟩
  rcases exists_least_ordinal_of_exists (P := SndProp) hSndProp hSndExists with
    ⟨β, hβord, hβProp, hβleast⟩
  rcases hβProp with ⟨m, hmA, hmμ, hmα, hmβ⟩
  have hmOrd : IsOrdinalPair m := hA m hmA
  have hmEq : m = ⟨α, β⟩ₖ := by
    calc
      m = ⟨kpair.π₁ m, kpair.π₂ m⟩ₖ := hmOrd.eq_kpair_proj
      _ = ⟨α, β⟩ₖ := by simp [hmα, hmβ]
  have hmMax : ordinalMax α β = μ := by
    simpa [hmα, hmβ] using hmμ
  refine ⟨m, hmA, ?_⟩
  intro p hpA
  have hpOrd : IsOrdinalPair p := hA p hpA
  have hpEq : p = ⟨kpair.π₁ p, kpair.π₂ p⟩ₖ := hpOrd.eq_kpair_proj
  have hνord : IsOrdinal (ordinalMax (kpair.π₁ p) (kpair.π₂ p)) := hpOrd.max_isOrdinal
  have hμsub : μ ⊆ ordinalMax (kpair.π₁ p) (kpair.π₂ p) := by
    exact hμleast _ hνord ⟨p, hpA, rfl⟩
  let ν : V := ordinalMax (kpair.π₁ p) (kpair.π₂ p)
  have hνdef : ν = ordinalMax (kpair.π₁ p) (kpair.π₂ p) := rfl
  have hνord' : IsOrdinal ν := by simpa [ν] using hνord
  letI : IsOrdinal μ := hμord
  letI : IsOrdinal ν := hνord'
  rcases (IsOrdinal.subset_iff (α := μ) (β := ν)).1 (by simpa [ν] using hμsub) with (hμEq | hμν)
  · have hαsub : α ⊆ kpair.π₁ p := by
      have hpμ : ordinalMax (kpair.π₁ p) (kpair.π₂ p) = μ := hνdef.symm.trans hμEq.symm
      exact hαleast _ hpOrd.fst ⟨p, hpA, hpμ, rfl⟩
    letI : IsOrdinal α := hαord
    letI : IsOrdinal (kpair.π₁ p) := hpOrd.fst
    rcases (IsOrdinal.subset_iff (α := α) (β := kpair.π₁ p)).1 hαsub with (hαEq | hαp)
    · have hβsub : β ⊆ kpair.π₂ p := by
        have hpμ : ordinalMax (kpair.π₁ p) (kpair.π₂ p) = μ := hνdef.symm.trans hμEq.symm
        exact hβleast _ hpOrd.snd ⟨p, hpA, hpμ, hαEq.symm, rfl⟩
      letI : IsOrdinal β := hβord
      letI : IsOrdinal (kpair.π₂ p) := hpOrd.snd
      rcases (IsOrdinal.subset_iff (α := β) (β := kpair.π₂ p)).1 hβsub with (hβEq | hβp)
      · left
        calc
          p = ⟨kpair.π₁ p, kpair.π₂ p⟩ₖ := hpEq
          _ = ⟨α, β⟩ₖ := by simp [hαEq, hβEq]
          _ = m := hmEq.symm
      · right
        rw [hmEq, hpEq]
        have hmaxEq : ordinalMax α β = ordinalMax (kpair.π₁ p) (kpair.π₂ p) := by
          calc
            ordinalMax α β = μ := hmMax
            _ = ν := hμEq
            _ = ordinalMax (kpair.π₁ p) (kpair.π₂ p) := hνdef
        exact (ordinalPairLT_kpair_iff_of_ordinals hαord hβord hpOrd.fst hpOrd.snd).2 <|
          Or.inr ⟨hmaxEq, Or.inr ⟨hαEq, hβp⟩⟩
    · right
      rw [hmEq, hpEq]
      have hmaxEq : ordinalMax α β = ordinalMax (kpair.π₁ p) (kpair.π₂ p) := by
        calc
          ordinalMax α β = μ := hmMax
          _ = ν := hμEq
          _ = ordinalMax (kpair.π₁ p) (kpair.π₂ p) := hνdef
      exact (ordinalPairLT_kpair_iff_of_ordinals hαord hβord hpOrd.fst hpOrd.snd).2 <|
        Or.inr ⟨hmaxEq, Or.inl hαp⟩
  · right
    rw [hmEq, hpEq]
    have hmaxp : ordinalMax α β ∈ ordinalMax (kpair.π₁ p) (kpair.π₂ p) := by
      simpa [hmMax, hνdef] using hμν
    exact (ordinalPairLT_kpair_iff_of_ordinals hαord hβord hpOrd.fst hpOrd.snd).2 <|
      Or.inl hmaxp

private lemma fst_mem_succ_ordinalMax {α β : V}
    (hα : IsOrdinal α) (hβ : IsOrdinal β) :
    α ∈ succ (ordinalMax α β) := by
  letI : IsOrdinal α := hα
  letI : IsOrdinal (ordinalMax α β) := ordinalMax_isOrdinal hα hβ
  rcases (IsOrdinal.subset_iff (α := α) (β := ordinalMax α β)).1 (by simp [ordinalMax]) with
    (hEq | hαμ)
  · simp only [mem_succ_iff]; exact Or.inl hEq
  · exact mem_succ_iff.mpr <| Or.inr hαμ

private lemma snd_mem_succ_ordinalMax {α β : V}
    (hα : IsOrdinal α) (hβ : IsOrdinal β) :
    β ∈ succ (ordinalMax α β) := by
  letI : IsOrdinal β := hβ
  letI : IsOrdinal (ordinalMax α β) := ordinalMax_isOrdinal hα hβ
  rcases (IsOrdinal.subset_iff (α := β) (β := ordinalMax α β)).1 (by simp [ordinalMax]) with
    (hEq | hβμ)
  · simp only [mem_succ_iff]; exact Or.inl hEq
  · exact mem_succ_iff.mpr <| Or.inr hβμ

private lemma ordinalPairLT_mem_prod_succ_max {p q : V}
    (hp : IsOrdinalPair p) (hqp : OrdinalPairLT q p) :
    q ∈ succ (ordinalMax (kpair.π₁ p) (kpair.π₂ p)) ×ˢ
        succ (ordinalMax (kpair.π₁ p) (kpair.π₂ p)) := by
  rcases hp with ⟨α, β, rfl, hα, hβ⟩
  have hq : IsOrdinalPair q := hqp.1
  rcases hq with ⟨γ, δ, rfl, hγ, hδ⟩
  let μ : V := ordinalMax α β
  let ν : V := ordinalMax γ δ
  have hμord : IsOrdinal μ := by simpa [μ] using ordinalMax_isOrdinal hα hβ
  have hνord : IsOrdinal ν := by simpa [ν] using ordinalMax_isOrdinal hγ hδ
  have hγνs : γ ∈ succ ν := by simpa [ν] using fst_mem_succ_ordinalMax hγ hδ
  have hδνs : δ ∈ succ ν := by simpa [ν] using snd_mem_succ_ordinalMax hγ hδ
  have hqp' : OrdinalLex3 ν γ δ μ α β := by
    simpa [μ, ν] using (ordinalPairLT_kpair_iff_of_ordinals hγ hδ hα hβ).1 hqp
  have hγμs : γ ∈ succ μ := by
    rcases hqp' with hνμ | ⟨hEq, _⟩
    · have hsuccνsubμ : succ ν ⊆ μ := IsOrdinal.succ_subset_of_mem hνμ
      exact mem_succ_iff.mpr <| Or.inr (hsuccνsubμ _ hγνs)
    · simpa [hEq] using hγνs
  have hδμs : δ ∈ succ μ := by
    rcases hqp' with hνμ | ⟨hEq, _⟩
    · have hsuccνsubμ : succ ν ⊆ μ := IsOrdinal.succ_subset_of_mem hνμ
      exact mem_succ_iff.mpr <| Or.inr (hsuccνsubμ _ hδνs)
    · simpa [hEq] using hδνs
  simpa [μ, kpair_mem_iff] using And.intro hγμs hδμs

noncomputable def ordinalPairInitialSegment (p : V) : V :=
  {q ∈ succ (ordinalMax (kpair.π₁ p) (kpair.π₂ p)) ×ˢ
      succ (ordinalMax (kpair.π₁ p) (kpair.π₂ p)) ; OrdinalPairLT q p}

lemma mem_ordinalPairInitialSegment_iff {p q : V} :
    q ∈ ordinalPairInitialSegment p ↔
      q ∈ succ (ordinalMax (kpair.π₁ p) (kpair.π₂ p)) ×ˢ
        succ (ordinalMax (kpair.π₁ p) (kpair.π₂ p)) ∧
      OrdinalPairLT q p := by
  simp [ordinalPairInitialSegment]

lemma mem_ordinalPairInitialSegment_iff_of_isOrdinalPair {p q : V}
    (hp : IsOrdinalPair p) :
    q ∈ ordinalPairInitialSegment p ↔ OrdinalPairLT q p := by
  constructor
  · intro hq
    exact (mem_ordinalPairInitialSegment_iff.mp hq).2
  · intro hqp
    exact mem_ordinalPairInitialSegment_iff.mpr ⟨ordinalPairLT_mem_prod_succ_max hp hqp, hqp⟩

private lemma ordinalPairLT_kpair_zero_fst_iff
    {β γ α : V}
    (hβ : IsOrdinal β) (hγ : IsOrdinal γ) (hα : IsOrdinal α) :
    OrdinalPairLT ⟨β, γ⟩ₖ ⟨0, α⟩ₖ ↔ β ∈ α ∧ γ ∈ α := by
  have h0 : IsOrdinal (0 : V) := by infer_instance
  have hmax0α : ordinalMax (0 : V) α = α := by
    simp [ordinalMax, zero_def]
  rw [ordinalPairLT_kpair_iff_of_ordinals hβ hγ h0 hα]
  constructor
  · intro h
    let μ : V := ordinalMax β γ
    have hμord : IsOrdinal μ := by simpa [μ] using ordinalMax_isOrdinal hβ hγ
    have hβμs : β ∈ succ μ := by simpa [μ] using fst_mem_succ_ordinalMax hβ hγ
    have hγμs : γ ∈ succ μ := by simpa [μ] using snd_mem_succ_ordinalMax hβ hγ
    have hμα : μ ∈ α := by
      rcases h with hμα | ⟨hEq, hlex⟩
      · simpa [hmax0α] using hμα
      · rcases hlex with hβ0 | ⟨hβ0, hγα⟩
        · simp [zero_def] at hβ0
        · have hμγ : μ = γ := by simp [μ, ordinalMax, hβ0, zero_def]
          have hγαEq : γ = α := by
            calc
              γ = μ := hμγ.symm
              _ = ordinalMax (0 : V) α := hEq
              _ = α := hmax0α
          exact ((mem_irrefl α) (hγαEq ▸ hγα)).elim
    have hsuccμsubα : succ μ ⊆ α := IsOrdinal.succ_subset_of_mem hμα
    exact ⟨hsuccμsubα _ hβμs, hsuccμsubα _ hγμs⟩
  · rintro ⟨hβα, hγα⟩
    rcases IsOrdinal.subset_or_supset (α := β) (β := γ) with (hβγ | hγβ)
    · have hμγ : ordinalMax β γ = γ := union_eq_iff_left.mpr hβγ
      exact Or.inl <| by rw [hmax0α, hμγ]; exact hγα
    · have hμβ : ordinalMax β γ = β := union_eq_iff_right.mpr hγβ
      exact Or.inl <| by rw [hmax0α, hμβ]; exact hβα

lemma ordinalPairInitialSegment_zero_fst_eq_prod {α : V}
    (hα : IsOrdinal α) :
    ordinalPairInitialSegment ⟨0, α⟩ₖ = α ×ˢ α := by
  have h0 : IsOrdinal (0 : V) := by infer_instance
  have hp : IsOrdinalPair ⟨0, α⟩ₖ := IsOrdinalPair.mk h0 hα
  ext q
  constructor
  · intro hq
    have hlt : OrdinalPairLT q ⟨0, α⟩ₖ := (mem_ordinalPairInitialSegment_iff_of_isOrdinalPair hp).mp hq
    have hqpair : IsOrdinalPair q := hlt.1
    rcases hqpair with ⟨β, γ, rfl, hβ, hγ⟩
    simpa [kpair_mem_iff] using
      (ordinalPairLT_kpair_zero_fst_iff hβ hγ hα).1 hlt
  · intro hq
    rcases mem_prod_iff.mp hq with ⟨β, hβα, γ, hγα, rfl⟩
    have hβ : IsOrdinal β := hα.of_mem hβα
    have hγ : IsOrdinal γ := hα.of_mem hγα
    exact (mem_ordinalPairInitialSegment_iff_of_isOrdinalPair hp).2 <|
      (ordinalPairLT_kpair_zero_fst_iff hβ hγ hα).2 ⟨hβα, hγα⟩

lemma ordinalPairInitialSegment_eq_iff {S p : V} :
    S = ordinalPairInitialSegment p ↔
      ∀ q, q ∈ S ↔
        q ∈ succ (ordinalMax (kpair.π₁ p) (kpair.π₂ p)) ×ˢ
          succ (ordinalMax (kpair.π₁ p) (kpair.π₂ p)) ∧
        OrdinalPairLT q p := by
  constructor
  · intro h q
    subst h
    exact mem_ordinalPairInitialSegment_iff
  · intro h
    ext q
    rw [mem_ordinalPairInitialSegment_iff]
    exact h q

instance ordinalPairInitialSegment_eq_definable :
    ℒₛₑₜ-relation[V] (fun S p ↦ S = ordinalPairInitialSegment p) := by
  let R : V → V → Prop := fun S p ↦
    ∀ q, q ∈ S ↔
      q ∈ succ (ordinalMax (kpair.π₁ p) (kpair.π₂ p)) ×ˢ
        succ (ordinalMax (kpair.π₁ p) (kpair.π₂ p)) ∧
      OrdinalPairLT q p
  have hR : ℒₛₑₜ-relation[V] R := by
    letI : ℒₛₑₜ-function₂[V] ordinalMax := ordinalMax.definable (V := V)
    letI : ℒₛₑₜ-function₁[V] kpair.π₁ := kpair.π₁.definable
    letI : ℒₛₑₜ-function₁[V] kpair.π₂ := kpair.π₂.definable
    letI : ℒₛₑₜ-function₁[V] succ := succ.definable
    letI : ℒₛₑₜ-function₂[V] prod := prod.definable
    letI : ℒₛₑₜ-relation[V] OrdinalPairLT := OrdinalPairLT.definable
    show ℒₛₑₜ-relation[V] (fun S p ↦
      ∀ q, q ∈ S ↔
        q ∈ succ (ordinalMax (kpair.π₁ p) (kpair.π₂ p)) ×ˢ
          succ (ordinalMax (kpair.π₁ p) (kpair.π₂ p)) ∧
        OrdinalPairLT q p)
    definability
  have hEq : (fun S p ↦ S = ordinalPairInitialSegment p) = R := by
    funext S p
    exact propext ordinalPairInitialSegment_eq_iff
  exact hEq ▸ hR

instance ordinalPairInitialSegment.definable :
    ℒₛₑₜ-function₁[V] ordinalPairInitialSegment :=
  ordinalPairInitialSegment_eq_definable

noncomputable def ordinalPairRelOn (X : V) : V :=
  {r ∈ X ×ˢ X ; ∃ p ∈ X, ∃ q ∈ X, r = ⟨p, q⟩ₖ ∧ OrdinalPairLT p q}

lemma ordinalPairRelOn_eq_iff {R X : V} :
    R = ordinalPairRelOn X ↔
      ∀ r, r ∈ R ↔
        r ∈ X ×ˢ X ∧ ∃ p ∈ X, ∃ q ∈ X, r = ⟨p, q⟩ₖ ∧ OrdinalPairLT p q := by
  constructor
  · intro hR r
    subst hR
    simp [ordinalPairRelOn]
  · intro hR
    ext r
    have hRel :
        r ∈ ordinalPairRelOn X ↔
          r ∈ X ×ˢ X ∧ ∃ p ∈ X, ∃ q ∈ X, r = ⟨p, q⟩ₖ ∧ OrdinalPairLT p q := by
      simp [ordinalPairRelOn]
    exact (hR r).trans hRel.symm

instance ordinalPairRelOn_eq_definable :
    ℒₛₑₜ-relation[V] (fun R X ↦ R = ordinalPairRelOn X) := by
  let Q : V → V → Prop := fun R X ↦
    ∀ r, r ∈ R ↔
      r ∈ X ×ˢ X ∧ ∃ p ∈ X, ∃ q ∈ X, r = ⟨p, q⟩ₖ ∧ OrdinalPairLT p q
  have hQ : ℒₛₑₜ-relation[V] Q := by
    letI : ℒₛₑₜ-function₂[V] prod := prod.definable
    letI : ℒₛₑₜ-function₂[V] kpair := kpair.definable
    letI : ℒₛₑₜ-relation[V] OrdinalPairLT := OrdinalPairLT.definable
    show ℒₛₑₜ-relation[V] (fun R X ↦
      ∀ r, r ∈ R ↔
        r ∈ X ×ˢ X ∧ ∃ p ∈ X, ∃ q ∈ X, r = ⟨p, q⟩ₖ ∧ OrdinalPairLT p q)
    definability
  have hEq : (fun R X ↦ R = ordinalPairRelOn X) = Q := by
    funext R X
    exact propext ordinalPairRelOn_eq_iff
  exact hEq ▸ hQ

instance ordinalPairRelOn.definable : ℒₛₑₜ-function₁[V] ordinalPairRelOn :=
  ordinalPairRelOn_eq_definable

lemma ordinalPairRelOn_subset_prod (X : V) : ordinalPairRelOn X ⊆ X ×ˢ X := by
  exact sep_subset

@[simp] lemma kpair_mem_ordinalPairRelOn_iff {X p q : V} :
    ⟨p, q⟩ₖ ∈ ordinalPairRelOn X ↔ p ∈ X ∧ q ∈ X ∧ OrdinalPairLT p q := by
  constructor
  · intro hpq
    have hpqX : ⟨p, q⟩ₖ ∈ X ×ˢ X := (mem_sep_iff.mp hpq).1
    have hpXqX : p ∈ X ∧ q ∈ X := by
      simpa [mem_prod_iff] using hpqX
    rcases (mem_sep_iff.mp hpq).2 with ⟨p', hp'X, q', hq'X, hpqEq, hp'q'⟩
    rcases kpair_inj hpqEq.symm with ⟨rfl, rfl⟩
    exact ⟨hpXqX.1, hpXqX.2, hp'q'⟩
  · rintro ⟨hpX, hqX, hpq⟩
    refine mem_sep_iff.mpr ?_
    refine ⟨by simpa [mem_prod_iff] using And.intro hpX hqX, p, hpX, q, hqX, rfl, hpq⟩

lemma strictLinearOrderOn_ordinalPairRelOn {X : V}
    (hX : ∀ p ∈ X, IsOrdinalPair p) :
    IsStrictLinearOrderOn (ordinalPairRelOn X) X := by
  refine ⟨ordinalPairRelOn_subset_prod X, ?_, ?_, ?_⟩
  · intro p hpX hpp
    exact ordinalPairLT_irrefl (hX p hpX) (kpair_mem_ordinalPairRelOn_iff.mp hpp).2.2
  · intro p hpX q hqX r hrX hpq hqr
    exact kpair_mem_ordinalPairRelOn_iff.mpr ⟨hpX, hrX,
      ordinalPairLT_trans (hX p hpX) (hX q hqX) (hX r hrX)
        (kpair_mem_ordinalPairRelOn_iff.mp hpq).2.2
        (kpair_mem_ordinalPairRelOn_iff.mp hqr).2.2⟩
  · intro p hpX q hqX
    rcases ordinalPairLT_trichotomy (hX p hpX) (hX q hqX) with (hpq | hpq | hqp)
    · exact Or.inl <| kpair_mem_ordinalPairRelOn_iff.mpr ⟨hpX, hqX, hpq⟩
    · exact Or.inr <| Or.inl hpq
    · exact Or.inr <| Or.inr <| kpair_mem_ordinalPairRelOn_iff.mpr ⟨hqX, hpX, hqp⟩

lemma wellOrderOn_ordinalPairRelOn {X : V}
    (hX : ∀ p ∈ X, IsOrdinalPair p) :
    IsWellOrderOn (ordinalPairRelOn X) X := by
  refine ⟨strictLinearOrderOn_ordinalPairRelOn hX, ?_⟩
  intro A hAX hAne
  have hA : ∀ p ∈ A, IsOrdinalPair p := fun p hpA ↦ hX p (hAX _ hpA)
  rcases exists_least_ordinalPairLT_of_ne_empty hA hAne with ⟨m, hmA, hmLeast⟩
  refine ⟨m, hmA, ?_⟩
  intro p hpA
  rcases hmLeast p hpA with (hpEq | hmp)
  · exact Or.inl hpEq
  · exact Or.inr <| kpair_mem_ordinalPairRelOn_iff.mpr ⟨hAX _ hmA, hAX _ hpA, hmp⟩

lemma ordinalPairInitialSegment_isOrdinalPair {p q : V}
    (hq : q ∈ ordinalPairInitialSegment p) : IsOrdinalPair q :=
  (mem_ordinalPairInitialSegment_iff.mp hq).2.1

lemma wellOrderOn_ordinalPairRelOn_ordinalPairInitialSegment (p : V) :
    IsWellOrderOn (ordinalPairRelOn (ordinalPairInitialSegment p)) (ordinalPairInitialSegment p) :=
  wellOrderOn_ordinalPairRelOn fun _ hq ↦ ordinalPairInitialSegment_isOrdinalPair hq

lemma initialSegment_ordinalPairRelOn_eq {p q : V}
    (hpq : OrdinalPairLT p q) :
    initialSegment (ordinalPairRelOn (ordinalPairInitialSegment q))
      (ordinalPairInitialSegment q) p = ordinalPairInitialSegment p := by
  have hp : IsOrdinalPair p := hpq.1
  have hq : IsOrdinalPair q := hpq.2.1
  have hpq_mem : p ∈ ordinalPairInitialSegment q :=
    (mem_ordinalPairInitialSegment_iff_of_isOrdinalPair hq).2 hpq
  ext x
  constructor
  · intro hx
    have hxp : ⟨x, p⟩ₖ ∈ ordinalPairRelOn (ordinalPairInitialSegment q) :=
      (mem_initialSegment_iff.mp hx).2
    exact (mem_ordinalPairInitialSegment_iff_of_isOrdinalPair hp).2
      ((kpair_mem_ordinalPairRelOn_iff.mp hxp).2.2)
  · intro hx
    have hxp : OrdinalPairLT x p :=
      (mem_ordinalPairInitialSegment_iff_of_isOrdinalPair hp).1 hx
    have hxq : OrdinalPairLT x q :=
      ordinalPairLT_trans hxp.1 hp hq hxp hpq
    have hxq_mem : x ∈ ordinalPairInitialSegment q :=
      (mem_ordinalPairInitialSegment_iff_of_isOrdinalPair hq).2 hxq
    exact mem_initialSegment_iff.mpr ⟨hxq_mem,
      kpair_mem_ordinalPairRelOn_iff.mpr ⟨hxq_mem, hpq_mem, hxp⟩⟩

lemma ordinalPairInitialSegment_subset {p q : V}
    (hpq : OrdinalPairLT p q) :
    ordinalPairInitialSegment p ⊆ ordinalPairInitialSegment q := by
  have hp : IsOrdinalPair p := hpq.1
  have hq : IsOrdinalPair q := hpq.2.1
  intro x hx
  have hxp : OrdinalPairLT x p :=
    (mem_ordinalPairInitialSegment_iff_of_isOrdinalPair hp).1 hx
  exact (mem_ordinalPairInitialSegment_iff_of_isOrdinalPair hq).2 <|
    ordinalPairLT_trans hxp.1 hp hq hxp hpq

noncomputable def ordinalPairInitialSegmentType
    [V ⊧ₘ* 𝗭𝗙] (p : V) : V :=
  Ordinal.wellOrderTypeValTotal
    (ordinalPairRelOn (ordinalPairInitialSegment p))
    (ordinalPairInitialSegment p)

lemma ordinalPairInitialSegmentType_spec
    [V ⊧ₘ* 𝗭𝗙] (p : V) :
    IsOrdinal (ordinalPairInitialSegmentType p) ∧
      ∃ f : V, IsOrderIso
        (IsOrdinal.memRelOn (ordinalPairInitialSegmentType p))
        (ordinalPairInitialSegmentType p)
        (ordinalPairRelOn (ordinalPairInitialSegment p))
        (ordinalPairInitialSegment p) f := by
  let hSwo :
      IsWellOrderOn (ordinalPairRelOn (ordinalPairInitialSegment p))
        (ordinalPairInitialSegment p) :=
    wellOrderOn_ordinalPairRelOn_ordinalPairInitialSegment (p := p)
  simpa [ordinalPairInitialSegmentType, Ordinal.wellOrderTypeValTotal_of_wellOrderOn hSwo] using
    (Ordinal.wellOrderTypeVal_spec
      (S := ordinalPairRelOn (ordinalPairInitialSegment p))
      (Y := ordinalPairInitialSegment p)
      hSwo)

lemma ordinalPairInitialSegmentType_isOrdinal
    [V ⊧ₘ* 𝗭𝗙] (p : V) : IsOrdinal (ordinalPairInitialSegmentType p) :=
  (ordinalPairInitialSegmentType_spec (V := V) p).1

private lemma isOrderIso_initialSegment_of_memRelOn
    {S Y β a y f : V}
    (hβord : IsOrdinal β)
    (hf : IsOrderIso (IsOrdinal.memRelOn β) β S Y f)
    (haβ : a ∈ β) (hayf : ⟨a, y⟩ₖ ∈ f) :
    IsOrderIso (IsOrdinal.memRelOn a) a S (initialSegment S Y y)
      (f ↾ (initialSegment (IsOrdinal.memRelOn β) β a)) := by
  have hRes :
      IsOrderIso (IsOrdinal.memRelOn β) (initialSegment (IsOrdinal.memRelOn β) β a)
        S (initialSegment S Y y)
        (f ↾ (initialSegment (IsOrdinal.memRelOn β) β a)) :=
    IsOrderIso.restrict_initialSegment hf haβ hayf
  refine ⟨?_, hRes.injective, hRes.range_eq, ?_⟩
  · simpa [IsOrdinal.initialSegment_memRelOn_eq (α := β) haβ] using hRes.mem_function
  · intro x₁ hx₁ x₂ hx₂
    have hx₁β : x₁ ∈ β := hβord.toIsTransitive.transitive _ haβ _ hx₁
    have hx₂β : x₂ ∈ β := hβord.toIsTransitive.transitive _ haβ _ hx₂
    have hx₁I : x₁ ∈ initialSegment (IsOrdinal.memRelOn β) β a := by
      simpa [IsOrdinal.initialSegment_memRelOn_eq (α := β) haβ] using hx₁
    have hx₂I : x₂ ∈ initialSegment (IsOrdinal.memRelOn β) β a := by
      simpa [IsOrdinal.initialSegment_memRelOn_eq (α := β) haβ] using hx₂
    rw [show ⟨x₁, x₂⟩ₖ ∈ IsOrdinal.memRelOn a ↔ ⟨x₁, x₂⟩ₖ ∈ IsOrdinal.memRelOn β from by
      simp [IsOrdinal.kpair_mem_memRelOn_iff, hx₁, hx₂, hx₁β, hx₂β]]
    exact hRes.rel_iff hx₁I hx₂I

lemma ordinalPairInitialSegmentType_strictIncreasing
    [V ⊧ₘ* 𝗭𝗙] {p q : V}
    (hpq : OrdinalPairLT p q) :
    ordinalPairInitialSegmentType p ∈ ordinalPairInitialSegmentType q := by
  let α := ordinalPairInitialSegmentType p
  let β := ordinalPairInitialSegmentType q
  let S := ordinalPairRelOn (ordinalPairInitialSegment q)
  let Y := ordinalPairInitialSegment q
  have hp : IsOrdinalPair p := hpq.1
  have hq : IsOrdinalPair q := hpq.2.1
  have hαord : IsOrdinal α := ordinalPairInitialSegmentType_isOrdinal (V := V) p
  have hβord : IsOrdinal β := ordinalPairInitialSegmentType_isOrdinal (V := V) q
  have hpY : p ∈ Y := by
    exact (mem_ordinalPairInitialSegment_iff_of_isOrdinalPair hq).2 hpq
  have hSwo : IsWellOrderOn S Y := by
    simpa [S, Y] using wellOrderOn_ordinalPairRelOn_ordinalPairInitialSegment (p := q)
  rcases (ordinalPairInitialSegmentType_spec (V := V) q).2 with ⟨f, hf⟩
  have hpRange : p ∈ range f := by
    simpa [Y, hf.range_eq] using hpY
  rcases mem_range_iff.mp hpRange with ⟨a, haf⟩
  have haβ : a ∈ β := (mem_of_mem_functions hf.mem_function haf).1
  have hIsoA :
      IsOrderIso (IsOrdinal.memRelOn a) a S (initialSegment S Y p)
        (f ↾ (initialSegment (IsOrdinal.memRelOn β) β a)) :=
    isOrderIso_initialSegment_of_memRelOn hβord hf haβ haf
  rcases (ordinalPairInitialSegmentType_spec (V := V) p).2 with ⟨g, hg⟩
  have hIsoα :
      IsOrderIso (IsOrdinal.memRelOn α) α S (initialSegment S Y p) g := by
    refine ⟨?_, hg.injective, ?_, ?_⟩
    · simpa [α, S, Y, initialSegment_ordinalPairRelOn_eq hpq] using hg.mem_function
    · simpa [α, S, Y, initialSegment_ordinalPairRelOn_eq hpq] using hg.range_eq
    · intro x₁ hx₁ x₂ hx₂
      have hmem := hg.rel_iff hx₁ hx₂
      have hx₁p : g ‘ x₁ ∈ ordinalPairInitialSegment p :=
        by
          rw [← hg.range_eq]
          exact value_mem_range hg.mem_function hx₁
      have hx₂p : g ‘ x₂ ∈ ordinalPairInitialSegment p :=
        by
          rw [← hg.range_eq]
          exact value_mem_range hg.mem_function hx₂
      have hx₁q : g ‘ x₁ ∈ Y := by
        simpa [Y] using ordinalPairInitialSegment_subset hpq _ hx₁p
      have hx₂q : g ‘ x₂ ∈ Y := by
        simpa [Y] using ordinalPairInitialSegment_subset hpq _ hx₂p
      have hrel :
          ⟨g ‘ x₁, g ‘ x₂⟩ₖ ∈ ordinalPairRelOn (ordinalPairInitialSegment p) ↔
            ⟨g ‘ x₁, g ‘ x₂⟩ₖ ∈ S := by
        constructor
        · intro h
          have hlt : OrdinalPairLT (g ‘ x₁) (g ‘ x₂) :=
            (kpair_mem_ordinalPairRelOn_iff.mp h).2.2
          simpa [S] using
            (kpair_mem_ordinalPairRelOn_iff.mpr ⟨hx₁q, hx₂q, hlt⟩)
        · intro h
          have h' : ⟨g ‘ x₁, g ‘ x₂⟩ₖ ∈ ordinalPairRelOn (ordinalPairInitialSegment q) := by
            simpa [S] using h
          exact kpair_mem_ordinalPairRelOn_iff.mpr
            ⟨hx₁p, hx₂p, (kpair_mem_ordinalPairRelOn_iff.mp h').2.2⟩
      exact hmem.trans hrel
  let Λ : V := succ (α ∪ β)
  have hαuβord : IsOrdinal (α ∪ β) := by
    rcases IsOrdinal.subset_or_supset (α := α) (β := β) with (hαβ | hβα)
    · have hEq : α ∪ β = β := union_eq_iff_left.mpr hαβ
      simpa [hEq] using hβord
    · have hEq : α ∪ β = α := union_eq_iff_right.mpr hβα
      simpa [hEq] using hαord
  have hΛord : IsOrdinal Λ := by
    simpa [Λ] using IsOrdinal.succ (α := α ∪ β)
  have hαΛ : α ∈ Λ := by
    have hαsub : α ⊆ α ∪ β := subset_union_left α β
    rcases (IsOrdinal.subset_iff (α := α) (β := α ∪ β)).1 hαsub with (hEq | hMem)
    · exact mem_succ_iff.mpr <| Or.inl hEq
    · exact mem_succ_iff.mpr <| Or.inr hMem
  have hβΛ : β ∈ Λ := by
    have hβsub : β ⊆ α ∪ β := subset_union_right α β
    rcases (IsOrdinal.subset_iff (α := β) (β := α ∪ β)).1 hβsub with (hEq | hMem)
    · exact mem_succ_iff.mpr <| Or.inl hEq
    · exact mem_succ_iff.mpr <| Or.inr hMem
  have haΛ : a ∈ Λ := hΛord.toIsTransitive.transitive _ hβΛ _ haβ
  have hαpair :
      ⟨α, p⟩ₖ ∈ initSegIsoRel (IsOrdinal.memRelOn Λ) Λ S Y := by
    exact IsOrdinal.kpair_mem_initSegIsoRel_memRelOn_of_isOrderIso
      (S := S) (Y := Y) (Λ := Λ) (α := α) (y := p) (f := g)
      hαΛ hpY hIsoα
  have hapair :
      ⟨a, p⟩ₖ ∈ initSegIsoRel (IsOrdinal.memRelOn Λ) Λ S Y := by
    exact IsOrdinal.kpair_mem_initSegIsoRel_memRelOn_of_isOrderIso
      (S := S) (Y := Y) (Λ := Λ) (α := a) (y := p)
      (f := f ↾ (initialSegment (IsOrdinal.memRelOn β) β a))
      haΛ hpY hIsoA
  have hEq : α = a := initSegIsoRel_injective
    (hRwo := by
      letI : IsOrdinal Λ := hΛord
      exact IsOrdinal.wellOrderOn_memRelOn (α := Λ))
    (hSwo := hSwo) α a p hαpair hapair
  simpa [α, hEq] using haβ

lemma ordinalPairLT_zero_fst_zero_fst_iff {β γ : V}
    (hβ : IsOrdinal β) (hγ : IsOrdinal γ) :
    OrdinalPairLT ⟨0, β⟩ₖ ⟨0, γ⟩ₖ ↔ β ∈ γ := by
  have h0 : IsOrdinal (0 : V) := by infer_instance
  constructor
  · intro h
    exact (ordinalPairLT_kpair_zero_fst_iff h0 hβ hγ).1 h |>.2
  · intro hβγ
    have h0γ : (0 : V) ∈ γ := by
      simpa [zero_def] using (IsOrdinal.empty_mem_iff_nonempty (α := γ)).2 ⟨β, hβγ⟩
    exact (ordinalPairLT_kpair_zero_fst_iff h0 hβ hγ).2 ⟨h0γ, hβγ⟩

/--
Order type of the ordinal-pair initial segment at the pair `(0, α)`.
-/
noncomputable def ordinalPairZeroFstType
    [V ⊧ₘ* 𝗭𝗙] (α : V) : V :=
  ordinalPairInitialSegmentType ⟨0, α⟩ₖ

lemma ordinalPairZeroFstType_isOrdinal
    [V ⊧ₘ* 𝗭𝗙] (α : V) : IsOrdinal (ordinalPairZeroFstType α) :=
  ordinalPairInitialSegmentType_isOrdinal (V := V) ⟨0, α⟩ₖ

lemma ordinalPairZeroFstType_strictIncreasing
    [V ⊧ₘ* 𝗭𝗙] {β γ : V}
    (hβ : IsOrdinal β) (hγ : IsOrdinal γ) (hβγ : β ∈ γ) :
    ordinalPairZeroFstType β ∈ ordinalPairZeroFstType γ := by
  exact ordinalPairInitialSegmentType_strictIncreasing (V := V) <|
    (ordinalPairLT_zero_fst_zero_fst_iff hβ hγ).2 hβγ

instance ordinalPairInitialSegmentType_eq_definable
    [V ⊧ₘ* 𝗭𝗙] :
    ℒₛₑₜ-relation[V] (fun α p ↦ α = ordinalPairInitialSegmentType p) := by
  letI : ℒₛₑₜ-function₁[V] ordinalPairInitialSegment := ordinalPairInitialSegment.definable
  letI : ℒₛₑₜ-function₁[V] ordinalPairRelOn := ordinalPairRelOn.definable
  letI : ℒₛₑₜ-function₂[V] Ordinal.wellOrderTypeValTotal :=
    Ordinal.wellOrderTypeValTotal.definable (V := V)
  unfold ordinalPairInitialSegmentType
  definability

instance ordinalPairInitialSegmentType.definable
    [V ⊧ₘ* 𝗭𝗙] : ℒₛₑₜ-function₁[V] ordinalPairInitialSegmentType :=
  ordinalPairInitialSegmentType_eq_definable (V := V)

instance ordinalPairZeroFstType_eq_definable
    [V ⊧ₘ* 𝗭𝗙] :
    ℒₛₑₜ-relation[V] (fun β α ↦ β = ordinalPairZeroFstType α) := by
  letI : ℒₛₑₜ-function₁[V] ordinalPairInitialSegmentType :=
    ordinalPairInitialSegmentType.definable (V := V)
  letI : ℒₛₑₜ-function₂[V] kpair := kpair.definable
  unfold ordinalPairZeroFstType
  definability

instance ordinalPairZeroFstType.definable
    [V ⊧ₘ* 𝗭𝗙] : ℒₛₑₜ-function₁[V] ordinalPairZeroFstType :=
  ordinalPairZeroFstType_eq_definable (V := V)

lemma subset_ordinalPairZeroFstType
    [V ⊧ₘ* 𝗭𝗙] :
    ∀ α : V, IsOrdinal α → α ⊆ ordinalPairZeroFstType α := by
  exact strictIncreasing_function_subset_value
    ordinalPairZeroFstType
    (ordinalPairZeroFstType.definable (V := V))
    (fun β γ hβ hγ hβγ ↦ ordinalPairZeroFstType_strictIncreasing (V := V) hβ hγ hβγ)
    (fun α _ ↦ ordinalPairZeroFstType_isOrdinal (V := V) α)

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

lemma subset_of_ordinal_of_isOrderIso_memRelOn_subset
    {α X : V} [hα : IsOrdinal α] {β : Ordinal V} {f : V}
    (hX : X ⊆ α)
    (hIso : IsOrderIso (IsOrdinal.memRelOn β.val) β.val (IsOrdinal.memRelOn X) X f) :
    β.val ⊆ α := by
  let F : V → V := fun ξ ↦ f ‘ ξ
  have hFdef : ℒₛₑₜ-function₁[V] F := by
    letI : ℒₛₑₜ-function₂[V] value := value.definable
    change ℒₛₑₜ-function₁[V] (fun ξ ↦ value f ξ)
    definability
  let P : V → Prop := fun ξ ↦ ξ ∈ β.val → ξ ⊆ F ξ
  have hP : ℒₛₑₜ-predicate[V] P := by
    letI : ℒₛₑₜ-function₁[V] F := hFdef
    change ℒₛₑₜ-predicate[V] (fun ξ ↦ ξ ∈ β.val → ξ ⊆ F ξ)
    definability
  have hPall : ∀ ξ : Ordinal V, P ξ := by
    apply transfinite_induction (P := P) hP
    intro ξ ih hξβ η hηξ
    have hηβ : η ∈ β.val := β.ordinal.toIsTransitive.transitive _ hξβ _ hηξ
    have hηord : IsOrdinal η := β.ordinal.of_mem hηβ
    let ηo : Ordinal V := IsOrdinal.toOrdinal η
    have hηlt : ηo < ξ := Ordinal.lt_def.mpr (by simpa [ηo] using hηξ)
    have hηsub : η ⊆ F η := ih ηo hηlt hηβ
    have hηX : F η ∈ X := by
      have hηR : F η ∈ range f := by simpa [F] using value_mem_range hIso.mem_function hηβ
      simpa [hIso.range_eq] using hηR
    have hξX : F ξ ∈ X := by
      have hξR : F ξ ∈ range f := by simpa [F] using value_mem_range hIso.mem_function hξβ
      simpa [hIso.range_eq] using hξR
    have hFηord : IsOrdinal (F η) := hα.of_mem (hX _ hηX)
    have hFξord : IsOrdinal (F ξ) := hα.of_mem (hX _ hξX)
    have hFηFξ : F η ∈ F ξ := by
      have hηξRel : ⟨η, ξ⟩ₖ ∈ IsOrdinal.memRelOn β.val :=
        IsOrdinal.kpair_mem_memRelOn_iff.mpr ⟨hηβ, hξβ, hηξ⟩
      exact (IsOrdinal.kpair_mem_memRelOn_iff.mp ((hIso.rel_iff hηβ hξβ).1 hηξRel)).2.2
    letI : IsOrdinal η := hηord
    letI : IsOrdinal (F η) := hFηord
    rcases (IsOrdinal.subset_iff (α := η) (β := F η)).1 hηsub with (hEq | hMem)
    · exact hEq ▸ hFηFξ
    · exact hFξord.toIsTransitive.transitive _ hFηFξ _ hMem
  intro ξ hξβ
  have hξord : IsOrdinal ξ := β.ordinal.of_mem hξβ
  let ξo : Ordinal V := IsOrdinal.toOrdinal ξ
  have hξsub : ξ ⊆ F ξ := hPall ξo hξβ
  have hξX : F ξ ∈ X := by
    have hξR : F ξ ∈ range f := by simpa [F] using value_mem_range hIso.mem_function hξβ
    simpa [hIso.range_eq] using hξR
  have hξα : F ξ ∈ α := hX _ hξX
  have hFξord : IsOrdinal (F ξ) := hα.of_mem hξα
  letI : IsOrdinal ξ := hξord
  letI : IsOrdinal (F ξ) := hFξord
  rcases (IsOrdinal.subset_iff (α := ξ) (β := F ξ)).1 hξsub with (hEq | hMem)
  · exact hEq.symm ▸ hξα
  · exact hα.toIsTransitive.transitive _ hξα _ hMem

lemma wellOrderTypeVal_memRelOn_subset_subset
    [V ⊧ₘ* 𝗭𝗙] {α X : V} [hα : IsOrdinal α]
    (hX : X ⊆ α) :
    Ordinal.wellOrderTypeVal (IsOrdinal.memRelOn X) X
      (IsOrdinal.wellOrderOn_memRelOn_subset (α := α) hX) ⊆ α := by
  let hXwo : IsWellOrderOn (IsOrdinal.memRelOn X) X :=
    IsOrdinal.wellOrderOn_memRelOn_subset (α := α) hX
  let β : Ordinal V := Ordinal.wellOrderType (IsOrdinal.memRelOn X) X hXwo
  rcases Ordinal.wellOrderType_isOrderIso (S := IsOrdinal.memRelOn X) (Y := X) (hSwo := hXwo) with ⟨f, hf⟩
  change β.val ⊆ α
  exact
    subset_of_ordinal_of_isOrderIso_memRelOn_subset (α := α) (β := β) (X := X) (f := f) hX hf

lemma wellOrderType_memRelOn_subset_le
    [V ⊧ₘ* 𝗭𝗙] {α X : V} [hα : IsOrdinal α]
    (hX : X ⊆ α) :
    Ordinal.wellOrderType (IsOrdinal.memRelOn X) X
      (IsOrdinal.wellOrderOn_memRelOn_subset (α := α) hX) ≤
      IsOrdinal.toOrdinal α := by
  simpa [Ordinal.le_def, Ordinal.wellOrderType] using
    wellOrderTypeVal_memRelOn_subset_subset (α := α) (X := X) hX

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
