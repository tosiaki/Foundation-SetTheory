module

public import Foundation.FirstOrder.SetTheory.ZF

@[expose] public section
/-!
# Basic definitions and lemmata for relations and functions
-/

namespace LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V ⊧ₘ* 𝗭]

/-! ### Relations -/

noncomputable def domain (R : V) : V := {x ∈ ⋃ˢ ⋃ˢ R ; ∃ y, ⟨x, y⟩ₖ ∈ R}

noncomputable def range (R : V) : V := {y ∈ ⋃ˢ ⋃ˢ R ; ∃ x, ⟨x, y⟩ₖ ∈ R}

section domain

lemma mem_sUnion_sUnion_of_kpair_mem_left {x y R : V} (h : ⟨x, y⟩ₖ ∈ R) : x ∈ ⋃ˢ ⋃ˢ R := by
  simp only [mem_sUnion_iff]
  refine ⟨{x, y}, ⟨⟨x, y⟩ₖ, h, by simp [kpair]⟩, by simp⟩

lemma mem_domain_iff {R x : V} : x ∈ domain R ↔ ∃ y, ⟨x, y⟩ₖ ∈ R := by
  simpa [domain] using fun _ ↦  mem_sUnion_sUnion_of_kpair_mem_left

def domain.dfn : Semisentence ℒₛₑₜ 2 := f“d R. ∀ x, x ∈ d ↔ ∃ y, !kpair.dfn x y ∈ R”

instance domain.defined : ℒₛₑₜ-function₁[V] domain via domain.dfn := ⟨fun v ↦ by simp [dfn, mem_ext_iff (y := domain _), mem_domain_iff]⟩

instance domain.definable : ℒₛₑₜ-function₁[V] domain := domain.defined.to_definable

lemma mem_domain_of_kpair_mem {R x y : V} (h : ⟨x, y⟩ₖ ∈ R) : x ∈ domain R := mem_domain_iff.mpr ⟨y, h⟩

@[simp] lemma domain_empty : domain (∅ : V) = ∅ := by ext; simp [mem_domain_iff]

@[simp] lemma domain_prod (x y : V) [IsNonempty y] : domain (x ×ˢ y) = x := by
  ext z
  suffices z ∈ x → ∃ x, x ∈ y by simpa [mem_domain_iff]
  intro _
  exact IsNonempty.nonempty

lemma domain_subset_of_subset_prod {R X Y : V} (h : R ⊆ X ×ˢ Y) : domain R ⊆ X := by
  intro x hx
  have : ∃ y, ⟨x, y⟩ₖ ∈ R := by simpa [mem_domain_iff] using hx
  rcases this with ⟨y, hy⟩
  have : x ∈ X ∧ y ∈ Y := by simpa using h _ hy
  exact this.1

@[simp]
lemma domain_union {R₁ R₂ : V} : domain (R₁ ∪ R₂) = domain R₁ ∪ domain R₂ := by
  ext p
  constructor <;> (simp_all only [mem_union_iff, mem_domain_iff]; grind)

lemma domain_inter_subset {R₁ R₂ : V} : domain (R₁ ∩ R₂) ⊆ domain R₁ ∩ domain R₂ := by
  intro p; simp only [mem_domain_iff, mem_inter_iff]; grind

@[simp, grind .] lemma domain_insert {x y R : V} : domain (insert (⟨x, y⟩ₖ) R) = insert x (domain R) := by
  ext z; simp only [mem_domain_iff, mem_insert, kpair_iff]; grind

end domain

section range

lemma mem_sUnion_sUnion_of_kpair_mem_right {x y R : V} (h : ⟨x, y⟩ₖ ∈ R) : y ∈ ⋃ˢ ⋃ˢ R := by
  simp only [mem_sUnion_iff]
  refine ⟨{x, y}, ⟨⟨x, y⟩ₖ, h, by simp [kpair]⟩, by simp⟩

lemma mem_range_iff {R y : V} : y ∈ range R ↔ ∃ x, ⟨x, y⟩ₖ ∈ R := by
  simpa [range] using fun _ ↦ mem_sUnion_sUnion_of_kpair_mem_right

def range.dfn : Semisentence ℒₛₑₜ 2 := f“r R. ∀ y, y ∈ r ↔ ∃ x, !kpair.dfn x y ∈ R”

instance range.defined : ℒₛₑₜ-function₁[V] range via range.dfn := ⟨fun v ↦ by simp [dfn, mem_ext_iff (y := range _), mem_range_iff]⟩

instance range.definable : ℒₛₑₜ-function₁[V] range := range.defined.to_definable

lemma mem_range_of_kpair_mem {R x y : V} (h : ⟨x, y⟩ₖ ∈ R) : y ∈ range R := mem_range_iff.mpr ⟨x, h⟩

@[simp] lemma range_empty : range (∅ : V) = ∅ := by ext; simp [mem_range_iff]

@[simp] lemma range_prod (x y : V) [IsNonempty x] : range (x ×ˢ y) = y := by
  ext z
  suffices z ∈ y → ∃ v, v ∈ x by simpa [mem_range_iff]
  intro _
  exact IsNonempty.nonempty

lemma range_subset_of_subset_prod {R X Y : V} (h : R ⊆ X ×ˢ Y) : range R ⊆ Y := by
  intro y hy
  have : ∃ x, ⟨x, y⟩ₖ ∈ R := by simpa [mem_range_iff] using hy
  rcases this with ⟨x, hx⟩
  have : x ∈ X ∧ y ∈ Y := by simpa using h _ hx
  exact this.2

@[simp]
lemma range_union {R₁ R₂ : V} : range (R₁ ∪ R₂) = range R₁ ∪ range R₂ := by
  ext p
  constructor <;> (simp_all only [mem_union_iff, mem_range_iff]; grind)

lemma range_inter_subset {R₁ R₂ : V} : range (R₁ ∩ R₂) ⊆ range R₁ ∩ range R₂ := by
  intro p; simp only [mem_range_iff, mem_inter_iff]; grind

@[simp, grind =] lemma range_insert {x y R : V} : range (insert (⟨x, y⟩ₖ) R) = insert y (range R) := by
  ext z; simp only [mem_range_iff, mem_insert, kpair_iff]; grind

end range

/-! ### Functions -/

noncomputable def function (Y X : V) : V := {f ∈ ℘ (X ×ˢ Y) ; ∀ x ∈ X, ∃! y, ⟨x, y⟩ₖ ∈ f}

noncomputable instance : Pow V V := ⟨fun Y X ↦ function Y X⟩

lemma function_def {Y X : V} : Y ^ X = function Y X := rfl

lemma mem_function_iff {f Y X : V} : f ∈ Y ^ X ↔ f ⊆ X ×ˢ Y ∧ ∀ x ∈ X, ∃! y, ⟨x, y⟩ₖ ∈ f := by simp [function, function_def]

def function.dfn : Semisentence ℒₛₑₜ 3 := f“F Y X. ∀ f, f ∈ F ↔ f ⊆ !prod.dfn X Y ∧ ∀ x ∈ X, ∃! y, !kpair.dfn x y ∈ f”

instance function.defined : ℒₛₑₜ-function₂[V] (·^·) via function.dfn :=
  ⟨fun v ↦ by simp [function.dfn, mem_ext_iff (y := (v 1)^(v 2)), mem_function_iff]⟩

instance function.definable : ℒₛₑₜ-function₂[V] (·^·) := function.defined.to_definable

lemma mem_function.intro {f X Y : V} (prod : f ⊆ X ×ˢ Y) (total : ∀ x ∈ X, ∃! y, ⟨x, y⟩ₖ ∈ f) : f ∈ Y ^ X :=
  mem_function_iff.mpr ⟨prod, total⟩

lemma subset_prod_of_mem_function {f X Y : V} (h : f ∈ Y ^ X) : f ⊆ X ×ˢ Y := mem_function_iff.mp h |>.1

lemma mem_of_mem_functions {f X Y : V} (h : f ∈ Y ^ X) (hx : ⟨x, y⟩ₖ ∈ f) : x ∈ X ∧ y ∈ Y := by
  simpa using subset_prod_of_mem_function h _ hx

lemma function_subset_power_prod (X Y : V) : Y ^ X ⊆ ℘ (X ×ˢ Y) := fun f hf ↦ by simpa using subset_prod_of_mem_function hf

lemma exists_unique_of_mem_function {f X Y : V} (h : f ∈ Y ^ X) : ∀ x ∈ X, ∃! y, ⟨x, y⟩ₖ ∈ f := mem_function_iff.mp h |>.2

lemma exists_of_mem_function {f X Y : V} (h : f ∈ Y ^ X) : ∀ x ∈ X, ∃ y ∈ Y, ⟨x, y⟩ₖ ∈ f := by
  intro x hx
  rcases (exists_unique_of_mem_function h x hx).exists with ⟨y, hy⟩
  have : x ∈ X ∧ y ∈ Y := mem_of_mem_functions h hy
  exact ⟨y, this.2, hy⟩

lemma domain_eq_of_mem_function {f X Y : V} (h : f ∈ Y ^ X) : domain f = X := by
  ext x
  suffices (∃ y, ⟨x, y⟩ₖ ∈ f) ↔ x ∈ X by simpa [mem_domain_iff]
  constructor
  · rintro ⟨y, hxy⟩
    have : x ∈ X ∧ y ∈ Y := mem_of_mem_functions h hxy
    exact this.1
  · intro hx
    rcases exists_of_mem_function h x hx with ⟨y, hy⟩
    exact ⟨y, hy.2⟩

lemma range_subset_of_mem_function {f X Y : V} (h : f ∈ Y ^ X) : range f ⊆ Y := by
  intro y hy
  have : ∃ x, ⟨x, y⟩ₖ ∈ f := by simpa [mem_range_iff] using hy
  rcases this with ⟨x, hxy⟩
  have : x ∈ X ∧ y ∈ Y := mem_of_mem_functions h hxy
  exact this.2

lemma mem_function_range_of_mem_function {f X Y : V} (h : f ∈ Y ^ X) : f ∈ range f ^ X := by
  have : f ⊆ X ×ˢ range f := by
    intro p hp
    have : ∃ x ∈ X, ∃ y ∈ Y, p = ⟨x, y⟩ₖ := by
      simpa [mem_prod_iff] using subset_prod_of_mem_function h _ hp
    rcases this with ⟨x, hx, y, hy, rfl⟩
    simpa [hx, mem_range_iff] using ⟨x, hp⟩
  apply mem_function.intro this
  intro x hx
  rcases exists_unique_of_mem_function h x hx |>.exists with ⟨y, hf⟩
  apply ExistsUnique.intro y hf
  intro y' hf'
  have : y' = y := exists_unique_of_mem_function h x hx |>.unique hf' hf
  assumption

lemma mem_function_of_mem_function_of_subset {f X Y₁ Y₂ : V} (h : f ∈ Y₁ ^ X) (hY : Y₁ ⊆ Y₂) : f ∈ Y₂ ^ X := by
  have : f ⊆ X ×ˢ Y₂ := calc
    f ⊆ X ×ˢ Y₁ := subset_prod_of_mem_function h
    _ ⊆ X ×ˢ Y₂ := prod_subset_prod_of_subset (by rfl) hY
  apply mem_function.intro this
  intro x hx
  rcases exists_unique_of_mem_function h x hx |>.exists with ⟨y, hf⟩
  apply ExistsUnique.intro y hf
  intro y' hf'
  have : y' = y := exists_unique_of_mem_function h x hx |>.unique hf' hf
  assumption

lemma function_subset_function_of_subset {Y₁ Y₂ : V} (hY : Y₁ ⊆ Y₂) (X : V) : Y₁ ^ X ⊆ Y₂ ^ X :=
  fun _ hf ↦ mem_function_of_mem_function_of_subset hf hY

@[simp] lemma empty_function_empty : (∅ : V) ^ (∅ : V) = {∅} := by ext z; simp [mem_function_iff]

/-- Functions over arbitrary domain and range -/
class IsFunction (f : V) : Prop where
  mem_func : ∃ X Y : V, f ∈ Y ^ X

lemma isFunction_def {f : V} : IsFunction f ↔ ∃ X Y : V, f ∈ Y ^ X := ⟨fun h ↦ h.mem_func, fun h ↦ ⟨h⟩⟩

def IsFunction.dfn : Semisentence ℒₛₑₜ 1 := f“f. ∃ X Y, f ∈ !function.dfn Y X”

instance IsFunction.defined : ℒₛₑₜ-predicate[V] IsFunction via dfn := ⟨fun v ↦ by simp [isFunction_def, dfn]⟩

instance IsFunction.definable : ℒₛₑₜ-predicate[V] IsFunction := defined.to_definable

lemma isFunction_iff {f : V} : IsFunction f ↔ f ∈ range f ^ domain f := by
  constructor
  · rintro ⟨X, Y, hf⟩
    simpa [domain_eq_of_mem_function hf] using mem_function_range_of_mem_function hf
  · intro h
    exact ⟨_, _, h⟩

namespace IsFunction

lemma of_mem {f X Y : V} (h : f ∈ Y ^ X) : IsFunction f := ⟨X, Y, h⟩

lemma mem_function (f : V) [hf : IsFunction f] : f ∈ range f ^ domain f := isFunction_iff.mp hf

@[grind ->] lemma ofSubset (f g : V) [hf : IsFunction f] : g ⊆ f → IsFunction g := by
  intro hgf
  apply isFunction_iff.mpr
  apply mem_function.intro
  · intro p hp
    have hpf : p ∈ f := hgf _ hp
    rcases show ∃ x ∈ domain f, ∃ y ∈ range f, p = ⟨x, y⟩ₖ from by
        simpa [mem_prod_iff] using subset_prod_of_mem_function hf.mem_function _ hpf with
      ⟨x, -, y, -, rfl⟩
    have hxg : x ∈ domain g := mem_domain_of_kpair_mem hp
    have hyg : y ∈ range g := mem_range_of_kpair_mem hp
    simpa [mem_prod_iff] using And.intro hxg hyg
  · intro x hx
    rcases mem_domain_iff.mp hx with ⟨y, hxy⟩
    refine ExistsUnique.intro y hxy ?_
    intro y' hxy'
    have hyf : ⟨x, y⟩ₖ ∈ f := hgf _ hxy
    have hy'f : ⟨x, y'⟩ₖ ∈ f := hgf _ hxy'
    have hux : ∃! z, ⟨x, z⟩ₖ ∈ f := exists_unique_of_mem_function hf.mem_function x (mem_domain_of_kpair_mem hyf)
    exact hux.unique hy'f hyf

lemma unique {f : V} [hf : IsFunction f] {x y₁ y₂} (h₁ : ⟨x, y₁⟩ₖ ∈ f) (h₂ : ⟨x, y₂⟩ₖ ∈ f) : y₁ = y₂ := by
  have : ∃! y, ⟨x, y⟩ₖ ∈ f := exists_unique_of_mem_function (isFunction_iff.mp hf) x (mem_domain_of_kpair_mem h₁)
  exact this.unique h₁ h₂

@[simp] instance empty : IsFunction (∅ : V) := ⟨∅, ∅, by simp⟩

protected def insert (f x y : V) (hx : x ∉ domain f) [hf : IsFunction f] : IsFunction (insert ⟨x, y⟩ₖ f) := by
  refine ⟨insert x (domain f), insert y (range f), ?_⟩
  apply mem_function.intro
  · have : f ⊆ domain f ×ˢ range f := subset_prod_of_mem_function hf.mem_function
    exact insert_kpair_subset_insert_prod_insert_of_subset_prod this x y
  · intro z hz
    rcases show z = x ∨ z ∈ domain f by simpa using hz with (rfl | hz)
    · apply ExistsUnique.intro y (by simp)
      rintro y' H'
      rcases show y' = y ∨ ⟨z, y'⟩ₖ ∈ f by simpa using H' with (rfl | H')
      · rfl
      have : z ∈ domain f := mem_domain_of_kpair_mem H'
      contradiction
    · rcases mem_domain_iff.mp hz with ⟨v, hzv⟩
      have : v ∈ range f := mem_range_of_kpair_mem hzv
      apply ExistsUnique.intro v (by simp [hzv])
      rintro w Hw
      rcases show z = x ∧ w = y ∨ ⟨z, w⟩ₖ ∈ f by simpa using Hw with (⟨rfl, rfl⟩ | Hw)
      · have : z ∈ domain f := mem_domain_of_kpair_mem hzv
        contradiction
      exact hf.unique Hw hzv

@[simp] instance (x y : V) : IsFunction ({⟨x, y⟩ₖ} : V) := by simpa using IsFunction.insert ∅ x y (by simp)

end IsFunction

lemma function_eq_of_subset {X Y f g : V} (hf : f ∈ Y ^ X) (hg : g ∈ Y ^ X) (h : f ⊆ g) : f = g := by
  have : IsFunction f := IsFunction.of_mem hf
  have : IsFunction g := IsFunction.of_mem hg
  apply subset_antisymm h
  intro p hp
  rcases show ∃ x ∈ X, ∃ y ∈ Y, p = ⟨x, y⟩ₖ from by
    simpa [mem_prod_iff] using subset_prod_of_mem_function hg _ hp with ⟨x, hx, y, hy, rfl⟩
  rcases show ∃ y' ∈ Y, ⟨x, y'⟩ₖ ∈ f from exists_of_mem_function hf x hx with ⟨y', hy', Hf⟩
  have : ⟨x, y'⟩ₖ ∈ g := h _ Hf
  rcases show y = y' from IsFunction.unique hp (h _ Hf)
  assumption

lemma function_ext {X Y f g : V} (hf : f ∈ Y ^ X) (hg : g ∈ Y ^ X)
    (h : ∀ x ∈ X, ∀ y ∈ Y, ⟨x, y⟩ₖ ∈ f → ⟨x, y⟩ₖ ∈ g) : f = g := by
  apply function_eq_of_subset hf hg
  intro p hp
  rcases show ∃ x ∈ X, ∃ y ∈ Y, p = ⟨x, y⟩ₖ from by
    simpa [mem_prod_iff] using subset_prod_of_mem_function hf _ hp with ⟨x, hx, y, hy, rfl⟩
  exact h x hx y hy hp

@[grind <=] lemma two_val_function_mem_iff_not {X f x : V} (hf : f ∈ (2 ^ X : V)) (hx : x ∈ X) : ⟨x, 0⟩ₖ ∈ f ↔ ⟨x, 1⟩ₖ ∉ f := by
  have : IsFunction f := IsFunction.of_mem hf
  constructor
  · intro h0 h1
    have : (0 : V) = 1 := IsFunction.unique h0 h1
    simp_all
  · intro h1
    rcases exists_of_mem_function hf x hx with ⟨i, hi, hf⟩
    rcases show i = 0 ∨ i = 1 by simpa using hi with (rfl | rfl)
    · assumption
    · contradiction

def Injective (R : V) : Prop := ∀ x₁ x₂ y, ⟨x₁, y⟩ₖ ∈ R → ⟨x₂, y⟩ₖ ∈ R → x₁ = x₂

def Injective.dfn : Semisentence ℒₛₑₜ 1 := f“f. ∀ x₁ x₂ y, !kpair.dfn x₁ y ∈ f → !kpair.dfn x₂ y ∈ f → x₁ = x₂”

instance Injective.defined : ℒₛₑₜ-predicate[V] Injective via dfn := ⟨fun v ↦ by simp [Injective, dfn]⟩

instance Injective.definable : ℒₛₑₜ-predicate[V] Injective := defined.to_definable

lemma Injective.empty : Injective (∅ : V) := fun x₁ x₂ y ↦ by simp

/-- Identity -/
noncomputable def identity (X : V) : V := {p ∈ X ×ˢ X ; ∃ x ∈ X, p = ⟨x, x⟩ₖ}

lemma mem_identity_iff {X p : V} : p ∈ identity X ↔ ∃ x ∈ X, p = ⟨x, x⟩ₖ := by
  suffices ∀ x ∈ X, p = ⟨x, x⟩ₖ → p ∈ X ×ˢ X by simpa [identity]
  rintro x hx rfl
  simp [hx]

def identity.dfn : Semisentence ℒₛₑₜ 2 := f“i X. ∀ p, p ∈ i ↔ ∃ x ∈ X, p = !kpair.dfn x x”

instance identity.defined : ℒₛₑₜ-function₁[V] identity via dfn := ⟨fun v ↦ by simp [dfn, mem_ext_iff (y := identity (v 1)), mem_identity_iff]⟩

instance identity.definable : ℒₛₑₜ-function₁[V] identity := defined.to_definable

@[simp] lemma kpair_mem_identity_iff {X x : V} : ⟨x, y⟩ₖ ∈ identity X ↔ x ∈ X ∧ x = y := by
  simp only [mem_identity_iff, kpair_iff, exists_eq_right_right', and_congr_left_iff]
  grind

@[simp] lemma identity_mem_function (X : V) : identity X ∈ X ^ X := by
  refine mem_function.intro ?_ ?_
  · intro p hp
    have : ∃ x ∈ X, p = ⟨x, x⟩ₖ := by simpa [mem_identity_iff] using hp
    rcases this with ⟨x, hx, rfl⟩
    simp_all
  · intro x hx
    apply ExistsUnique.intro x (by simp [hx])
    simp only [kpair_mem_identity_iff, and_imp]
    grind

instance IsFunction.identity (X : V) : IsFunction (identity X) := IsFunction.of_mem (identity_mem_function X)

@[simp] lemma identity_injective (X : V) : Injective (identity X) := by
  intro x₁ x₂ y h₁ h₂
  rcases show x₁ ∈ X ∧ x₁ = y by simpa using h₁ with ⟨hx₁, rfl⟩
  rcases show x₂ ∈ X ∧ x₂ = x₁ by simpa using h₂ with ⟨hx₂, rfl⟩
  rfl

/-- Composition -/
noncomputable def compose (R S : V) : V := {p ∈ domain R ×ˢ range S ; ∃ x y z, ⟨x, y⟩ₖ ∈ R ∧ ⟨y, z⟩ₖ ∈ S ∧ p = ⟨x, z⟩ₖ}

lemma mem_compose_iff {R S p : V} : p ∈ compose R S ↔ ∃ x y z, ⟨x, y⟩ₖ ∈ R ∧ ⟨y, z⟩ₖ ∈ S ∧ p = ⟨x, z⟩ₖ := by
  simp only [compose, exists_and_left, mem_sep_iff, and_iff_right_iff_imp, forall_exists_index, and_imp]
  rintro x y hxy z hyz rfl
  simp [mem_domain_of_kpair_mem hxy, mem_range_of_kpair_mem hyz]

@[simp] lemma kpair_mem_compose_iff {R S x z : V} :
    ⟨x, z⟩ₖ ∈ compose R S ↔ ∃ y, ⟨x, y⟩ₖ ∈ R ∧ ⟨y, z⟩ₖ ∈ S := by
  simp only [mem_compose_iff, kpair_iff, exists_and_left, exists_eq_right_right']
  grind

lemma compose_subset_prod {X Y Z R S : V} (hR : R ⊆ X ×ˢ Y) (hS : S ⊆ Y ×ˢ Z) : compose R S ⊆ X ×ˢ Z := by
  intro p hp
  rcases mem_compose_iff.mp hp with ⟨x, y, z, hxy, hyz, rfl⟩
  have : x ∈ X ∧ y ∈ Y := by simpa using hR _ hxy
  have : y ∈ Y ∧ z ∈ Z := by simpa using hS _ hyz
  simp_all

lemma compose_function {X Y Z f g : V} (hf : f ∈ Y ^ X) (hg : g ∈ Z ^ Y) : compose f g ∈ Z ^ X := by
  have : IsFunction f := IsFunction.of_mem hf
  have : IsFunction g := IsFunction.of_mem hg
  apply mem_function.intro ?_ ?_
  · exact compose_subset_prod (subset_prod_of_mem_function hf) (subset_prod_of_mem_function hg)
  · intro x hx
    have : ∃ y ∈ Y, ⟨x, y⟩ₖ ∈ f := exists_of_mem_function hf x hx
    rcases this with ⟨y, hy, hxy⟩
    have : ∃ z ∈ Z, ⟨y, z⟩ₖ ∈ g := exists_of_mem_function hg y hy
    rcases this with ⟨z, hz, hyz⟩
    apply ExistsUnique.intro z (by simpa using ⟨y, hxy, hyz⟩)
    intro z' hz'
    have : ∃ y', ⟨x, y'⟩ₖ ∈ f ∧ ⟨y', z'⟩ₖ ∈ g := by simpa using hz'
    rcases this with ⟨y', hxy', hy'z'⟩
    rcases IsFunction.unique hxy hxy'
    rcases IsFunction.unique hyz hy'z'
    rfl

lemma compose_injective {R S : V} (hR : Injective R) (hS : Injective S) : Injective (compose R S) := by
  intro x₁ x₂ z h₁ h₂
  have : ∃ y₁, ⟨x₁, y₁⟩ₖ ∈ R ∧ ⟨y₁, z⟩ₖ ∈ S := by simpa using h₁
  rcases this with ⟨y₁, hx₁y₁, hy₁z⟩
  have : ∃ y₂, ⟨x₂, y₂⟩ₖ ∈ R ∧ ⟨y₂, z⟩ₖ ∈ S := by simpa using h₂
  rcases this with ⟨y₂, hx₂y₂, hy₂z⟩
  have : y₁ = y₂ := hS y₁ y₂ z hy₁z hy₂z
  rcases this
  exact hR x₁ x₂ y₁ hx₁y₁ hx₂y₂

/-- Inverse/converse relation. -/
noncomputable def inverse (R : V) : V :=
  {p ∈ range R ×ˢ domain R ; ∃ x y, ⟨x, y⟩ₖ ∈ R ∧ p = ⟨y, x⟩ₖ}

def inverse.dfn : Semisentence ℒₛₑₜ 2 := f“I R.
  ∀ p, p ∈ I ↔
    p ∈ !prod.dfn (!range.dfn R) (!domain.dfn R) ∧
    ∃ x y, !kpair.dfn x y ∈ R ∧ p = !kpair.dfn y x”

instance inverse.defined : ℒₛₑₜ-function₁[V] inverse via inverse.dfn :=
  ⟨fun v ↦ by
    simp [inverse.dfn]
    simp [inverse, mem_ext_iff]⟩

instance inverse.definable : ℒₛₑₜ-function₁[V] inverse := inverse.defined.to_definable

lemma mem_inverse_iff {R p : V} :
    p ∈ inverse R ↔ ∃ x y, ⟨x, y⟩ₖ ∈ R ∧ p = ⟨y, x⟩ₖ := by
  constructor
  · intro hp
    rcases mem_sep_iff.mp hp with ⟨-, hswap⟩
    exact hswap
  · rintro ⟨x, y, hxy, rfl⟩
    refine mem_sep_iff.mpr ?_
    refine ⟨?_, x, y, hxy, rfl⟩
    have hyR : y ∈ range R := mem_range_of_kpair_mem hxy
    have hxD : x ∈ domain R := mem_domain_of_kpair_mem hxy
    simpa [mem_prod_iff] using And.intro hyR hxD

@[simp] lemma kpair_mem_inverse_iff {R x y : V} :
    ⟨x, y⟩ₖ ∈ inverse R ↔ ⟨y, x⟩ₖ ∈ R := by
  constructor
  · intro hxy
    rcases mem_inverse_iff.mp hxy with ⟨x', y', hy'x', hp⟩
    rcases kpair_inj hp with ⟨rfl, rfl⟩
    exact hy'x'
  · intro hyx
    exact mem_inverse_iff.mpr ⟨y, x, hyx, rfl⟩

@[simp] lemma domain_inverse (R : V) : domain (inverse R) = range R := by
  ext z
  constructor
  · intro hz
    rcases mem_domain_iff.mp hz with ⟨w, hzw⟩
    exact mem_range_iff.mpr ⟨w, kpair_mem_inverse_iff.mp hzw⟩
  · intro hz
    rcases mem_range_iff.mp hz with ⟨w, hwz⟩
    exact mem_domain_iff.mpr ⟨w, kpair_mem_inverse_iff.mpr hwz⟩

@[simp] lemma range_inverse (R : V) : range (inverse R) = domain R := by
  ext z
  constructor
  · intro hz
    rcases mem_range_iff.mp hz with ⟨w, hwz⟩
    exact mem_domain_iff.mpr ⟨w, kpair_mem_inverse_iff.mp hwz⟩
  · intro hz
    rcases mem_domain_iff.mp hz with ⟨w, hzw⟩
    exact mem_range_iff.mpr ⟨w, kpair_mem_inverse_iff.mpr hzw⟩

lemma inverse_mem_function_of_mem_function_of_injective {f X Y : V}
    (hf : f ∈ Y ^ X) (hinj : Injective f) :
    inverse f ∈ X ^ range f := by
  apply mem_function.intro
  · intro p hp
    have : p ∈ range f ×ˢ domain f := (mem_sep_iff.mp hp).1
    simpa [domain_eq_of_mem_function hf, mem_prod_iff] using this
  · intro y hyR
    rcases mem_range_iff.mp hyR with ⟨x, hxyf⟩
    refine ExistsUnique.intro x ?_ ?_
    · exact kpair_mem_inverse_iff.mpr hxyf
    · intro x' hyx'
      exact hinj x' x y (kpair_mem_inverse_iff.mp hyx') hxyf

lemma inverse_injective_of_mem_function {f X Y : V} (hf : f ∈ Y ^ X) : Injective (inverse f) := by
  have hfunc : IsFunction f := IsFunction.of_mem hf
  intro y₁ y₂ x hy₁ hy₂
  exact hfunc.unique (kpair_mem_inverse_iff.mp hy₁) (kpair_mem_inverse_iff.mp hy₂)

/- This definition of value is adapted from NM's contribution to Metamath: https://us.metamath.org/mpeuni/fv3.html -/
noncomputable def value (f x : V) := {z ∈ ⋃ˢ range f ; ∃ y, z ∈ y ∧ ⟨x, y⟩ₖ ∈ f}

/-- If `x` is in `domain f`, then `f ‘ x` is the value of `f` at `x`, else it is `∅`. -/
scoped notation f:arg " ‘ " x:arg => value f x

def value.dfn : Semisentence ℒₛₑₜ 3 := f“v f x. ∀ z, z ∈ v ↔ z ∈ !sUnion.dfn (!range.dfn f) ∧ ∃ y, z ∈ y ∧ !kpair.dfn x y ∈ f”

instance value.defined : ℒₛₑₜ-function₂[V] value via value.dfn :=
  ⟨fun v ↦ by simp [dfn, value]; simp only [mem_ext_iff, mem_sep_iff]⟩

instance value.definable : ℒₛₑₜ-function₂[V] value := value.defined.to_definable

lemma value_mem_range {f x : V} {X Y : V} (hf : f ∈ Y ^ X) (hx : x ∈ X) : f ‘ x ∈ range f := by
  simp_all only [mem_function_iff, value, mem_range_iff]
  obtain ⟨hfleft, hfright⟩ := hf
  specialize hfright x hx
  obtain ⟨y, hy⟩ := ExistsUnique.exists hfright
  have h1 {w : V} : ⟨x, w⟩ₖ ∈ f → w = y := by
    intro h; exact hfright.unique h hy
  have h2 : y = {z ∈ ⋃ˢ range f ; ∃ y, z ∈ y ∧ ⟨x, y⟩ₖ ∈ f} := by
    ext z
    simp only [mem_sep_iff, mem_sUnion_iff, mem_range_iff]
    constructor <;> intro h <;> grind
  grind

namespace IsFunction

lemma value_eq_iff_kpair_mem {f x y : V} [IsFunction f] (hx : x ∈ domain f) :
    f ‘ x = y ↔ ⟨x, y⟩ₖ ∈ f := by
  constructor
  · intro hxy
    rcases mem_domain_iff.mp hx with ⟨y', hxy'⟩
    have hval : f ‘ x = y' := by
      ext z
      constructor
      · intro hz
        rcases show z ∈ ⋃ˢ range f ∧ ∃ w, z ∈ w ∧ ⟨x, w⟩ₖ ∈ f by
            simpa [value, mem_sep_iff] using hz with
          ⟨-, w, hzw, hxw⟩
        have : w = y' := IsFunction.unique hxw hxy'
        simpa [this] using hzw
      · intro hzy'
        have hy'R : y' ∈ range f := mem_range_of_kpair_mem hxy'
        have hzU : z ∈ ⋃ˢ range f := mem_sUnion_iff.mpr ⟨y', hy'R, hzy'⟩
        exact mem_sep_iff.mpr ⟨hzU, y', hzy', hxy'⟩
    rw [hval] at hxy
    simpa [hxy] using hxy'
  · intro hxy
    ext z
    constructor
    · intro hz
      rcases show z ∈ ⋃ˢ range f ∧ ∃ y', z ∈ y' ∧ ⟨x, y'⟩ₖ ∈ f by
          simpa [value, mem_sep_iff] using hz with
        ⟨-, y', hzy', hxy'⟩
      have : y' = y := IsFunction.unique hxy' hxy
      simpa [this] using hzy'
    · intro hzy
      have hyR : y ∈ range f := mem_range_of_kpair_mem hxy
      have hzU : z ∈ ⋃ˢ range f := mem_sUnion_iff.mpr ⟨y, hyR, hzy⟩
      exact mem_sep_iff.mpr ⟨hzU, y, hzy, hxy⟩

end IsFunction

lemma value_eq_of_kpair_mem {f X Y x y : V} (hf : f ∈ Y ^ X) (hxy : ⟨x, y⟩ₖ ∈ f) :
    f ‘ x = y := by
  have hfunc : IsFunction f := IsFunction.of_mem hf
  have hx : x ∈ X := (mem_of_mem_functions hf hxy).1
  have huniq := exists_unique_of_mem_function hf x hx
  apply subset_antisymm
  · intro z hz
    have : z ∈ y := by
      have hz' : z ∈ ⋃ˢ range f ∧ ∃ w, z ∈ w ∧ ⟨x, w⟩ₖ ∈ f := by simpa [value] using hz
      rcases hz'.2 with ⟨w, hzw, hxwf⟩
      have : w = y := huniq.unique hxwf hxy
      rwa [this] at hzw
    exact this
  · intro z hzy
    suffices z ∈ ⋃ˢ range f ∧ ∃ w, z ∈ w ∧ ⟨x, w⟩ₖ ∈ f by simpa [value] using this
    exact ⟨mem_sUnion_iff.mpr ⟨y, mem_range_of_kpair_mem hxy, hzy⟩, y, hzy, hxy⟩

lemma value_compose_eq {X Y Z f g x : V}
    (hf : f ∈ Y ^ X) (hg : g ∈ Z ^ Y) (hx : x ∈ X) :
    (compose f g) ‘ x = g ‘ (f ‘ x) := by
  rcases exists_of_mem_function hf x hx with ⟨y, hyY, hxy⟩
  rcases exists_of_mem_function hg y hyY with ⟨z, -, hyz⟩
  have hcomp : ⟨x, z⟩ₖ ∈ compose f g := kpair_mem_compose_iff.mpr ⟨y, hxy, hyz⟩
  have hvalComp : (compose f g) ‘ x = z :=
    value_eq_of_kpair_mem (compose_function hf hg) hcomp
  have hvalF : f ‘ x = y := value_eq_of_kpair_mem hf hxy
  have hvalG : g ‘ y = z := value_eq_of_kpair_mem hg hyz
  calc
    (compose f g) ‘ x = z := hvalComp
    _ = g ‘ y := hvalG.symm
    _ = g ‘ (f ‘ x) := by rw [hvalF]

/-- Restricting the domain of a relation -/
noncomputable def restrict (R A : V) : V := R ∩ (A ×ˢ range R)

/-- Restricting the domain of a relation -/
scoped notation R:arg " ↾ " A:arg => restrict R A

def restrict.dfn : Semisentence ℒₛₑₜ 3 := f“r R A. r = !inter.dfn R (!prod.dfn A (!range.dfn R))”

instance restrict.defined : ℒₛₑₜ-function₂[V] restrict via restrict.dfn :=
  ⟨fun v ↦ by simp [dfn, restrict]⟩

instance restrict.definable : ℒₛₑₜ-function₂[V] restrict := restrict.defined.to_definable

lemma mem_restrict_iff {R A p : V} :
    p ∈ (R ↾ A) ↔ p ∈ R ∧ ∃ x ∈ A, ∃ y, p = ⟨x, y⟩ₖ := by
  constructor
  · intro hp
    rcases show p ∈ R ∧ p ∈ A ×ˢ range R by simpa [restrict] using hp with ⟨hpR, hpP⟩
    rcases show ∃ x ∈ A, ∃ y ∈ range R, p = ⟨x, y⟩ₖ by simpa [mem_prod_iff] using hpP with
      ⟨x, hxA, y, -, rfl⟩
    exact ⟨hpR, x, hxA, y, rfl⟩
  · rintro ⟨hpR, x, hxA, y, rfl⟩
    have hyR : y ∈ range R := mem_range_of_kpair_mem hpR
    have hpP : ⟨x, y⟩ₖ ∈ A ×ˢ range R := by simpa [mem_prod_iff] using ⟨hxA, hyR⟩
    simpa [restrict] using And.intro hpR hpP

@[simp] lemma restrict_subset (f A : V) : f ↾ A ⊆ f := by
  intro p hp
  exact (mem_restrict_iff.mp hp).1

lemma IsFunction.restrict (f A : V) [hf : IsFunction f] : IsFunction (f ↾ A) := by
  exact IsFunction.ofSubset f (f ↾ A) (restrict_subset f A)

lemma IsFunction.restrict_eq_self (f A : V) [hf : IsFunction f] (hA : domain f ⊆ A) : f ↾ A = f := by
  apply subset_antisymm
  · intro p hp
    exact (mem_restrict_iff.mp hp).1
  · intro p hp
    rcases show ∃ x ∈ domain f, ∃ y ∈ range f, p = ⟨x, y⟩ₖ from by
        simpa [mem_prod_iff] using subset_prod_of_mem_function hf.mem_function p hp with
      ⟨x, hxd, y, -, rfl⟩
    exact mem_restrict_iff.mpr ⟨hp, x, hA x hxd, y, rfl⟩

lemma domain_restrict_eq (R A : V) : domain (R ↾ A) = domain R ∩ A := by
  ext z
  apply Iff.intro <;> intro h
  · simp_all only [mem_domain_iff, mem_inter_iff, restrict]
    aesop
  · simp_all only [mem_domain_iff, mem_inter_iff, restrict]
    obtain ⟨⟨y, hy⟩, hzA⟩ := h
    use y
    simp_all only [kpair_mem_iff, true_and, mem_range_iff]
    use z

@[simp] lemma kpair_mem_restrict_iff {R A x y : V} :
    ⟨x, y⟩ₖ ∈ (R ↾ A) ↔ ⟨x, y⟩ₖ ∈ R ∧ x ∈ A := by
  simp [mem_restrict_iff]

lemma restrict_restrict_eq_restrict_inter (R A B : V) : (R ↾ A) ↾ B = R ↾ (A ∩ B) := by
  ext p
  simp only [mem_restrict_iff, mem_inter_iff]
  constructor
  · rintro ⟨⟨hpR, x, hxA, y, rfl⟩, x', hx'B, y', hxy⟩
    rcases kpair_inj hxy with ⟨rfl, rfl⟩
    exact ⟨hpR, x, ⟨hxA, hx'B⟩, y, rfl⟩
  · rintro ⟨hpR, x, hxAB, y, rfl⟩
    exact ⟨⟨hpR, x, hxAB.1, y, rfl⟩, x, hxAB.2, y, rfl⟩

lemma restrict_restrict_of_subset {R A B : V} (h : B ⊆ A) : (R ↾ A) ↾ B = R ↾ B := by
  simpa [inter_eq_right_of_subset h] using restrict_restrict_eq_restrict_inter R A B


/--
Restricting an inserted relation to a set that does not contain the inserted first coordinate
recovers the original restriction.
-/
lemma restrict_insert_kpair_eq_restrict_of_not_mem
    {f x y A : V} (hxA : x ∉ A) :
    (insert ⟨x, y⟩ₖ f) ↾ A = f ↾ A := by
  ext p
  constructor
  · intro hp
    rcases mem_restrict_iff.mp hp with ⟨hp', a, haA, b, rfl⟩
    rcases show ⟨a, b⟩ₖ = ⟨x, y⟩ₖ ∨ ⟨a, b⟩ₖ ∈ f by simpa using hp' with (hxy | hf)
    · rcases kpair_inj hxy with ⟨rfl, rfl⟩
      exact (hxA haA).elim
    · exact mem_restrict_iff.mpr ⟨hf, a, haA, b, rfl⟩
  · intro hp
    rcases mem_restrict_iff.mp hp with ⟨hf, a, haA, b, rfl⟩
    exact mem_restrict_iff.mpr ⟨by simp [hf], a, haA, b, rfl⟩

/-- Image of a set under a relation -/
noncomputable def image (R A : V) : V := range (restrict R A)

/-- Image of a set under a relation -/
scoped notation R:arg " “ " A:arg => image R A

def image.dfn : Semisentence ℒₛₑₜ 3 := f“B R A. B = !range.dfn (!restrict.dfn R A)”

instance image.defined : ℒₛₑₜ-function₂[V] image via image.dfn :=
  ⟨fun v ↦ by simp [dfn, image]⟩

instance image.definable : ℒₛₑₜ-function₂[V] image := image.defined.to_definable

/--
If `F` is definable and maps `X` into `Y`, then separation on `X ×ˢ Y`
produces a set-theoretic function graph representing `F` on `X`.
-/
lemma graph_exists_mem_function_of_definableFunction
    (X Y : V) (F : V → V) (hFdef : ℒₛₑₜ-function₁[V] F)
    (hF : ∀ x ∈ X, F x ∈ Y) :
    ∃ f : V, f ∈ Y ^ X ∧
      ∀ x ∈ X, ∀ y, ⟨x, y⟩ₖ ∈ f ↔ y = F x := by
  let P : V → Prop := fun p ↦ ∃ x ∈ X, p = ⟨x, F x⟩ₖ
  have hP : ℒₛₑₜ-predicate[V] P := by
    letI : ℒₛₑₜ-function₁[V] F := hFdef
    change ℒₛₑₜ-predicate[V] (fun p ↦ ∃ x ∈ X, p = ⟨x, F x⟩ₖ)
    definability
  refine ⟨sep (X ×ˢ Y) P hP, ?_, ?_⟩
  · apply mem_function.intro
    · exact sep_subset
    · intro x hxX
      refine ExistsUnique.intro (F x) ?_ ?_
      · rw [mem_sep_iff]
        refine ⟨?_, x, hxX, rfl⟩
        simpa [mem_prod_iff] using And.intro hxX (hF x hxX)
      · intro y hxy
        rw [mem_sep_iff] at hxy
        rcases hxy with ⟨-, x', -, hp⟩
        rcases kpair_inj hp with ⟨hxx', hy⟩
        subst hxx'
        exact hy
  · intro x hxX y
    constructor
    · intro hxy
      rw [mem_sep_iff] at hxy
      rcases hxy with ⟨-, x', -, hp⟩
      rcases kpair_inj hp with ⟨hxx', hy⟩
      subst hxx'
      exact hy
    · intro hy
      subst y
      rw [mem_sep_iff]
      refine ⟨?_, x, hxX, rfl⟩
      simpa [mem_prod_iff] using And.intro hxX (hF x hxX)

/--
Graph construction from a definable unary function on a fixed set `X`.
-/
lemma replacement_graph_exists_on_of_definableFunction [V ⊧ₘ* 𝗭𝗙]
    (X : V) (F : V → V) (hFdef : ℒₛₑₜ-function₁[V] F) :
    ∃ f : V, IsFunction f ∧ domain f = X ∧
      ∀ x ∈ X, ∀ y, ⟨x, y⟩ₖ ∈ f ↔ y = F x := by
  let R : V → V → Prop := fun x y ↦ Function.Graph F y x
  have hR : ℒₛₑₜ-relation[V] R := by
    letI : ℒₛₑₜ-function₁[V] F := hFdef
    change ℒₛₑₜ-relation[V] (fun x y ↦ Function.Graph F y x)
    definability
  have hfun : ∀ x : V, x ∈ X → ∃! y : V, R x y := by
    intro x _
    simpa [R] using functionGraph_functionLike F x
  let S : V → V → Prop := fun x p ↦ ∃ y : V, R x y ∧ p = ⟨x, y⟩ₖ
  have hS : ℒₛₑₜ-relation[V] S := by
    letI : ℒₛₑₜ-relation[V] R := hR
    change ℒₛₑₜ-relation[V] (fun x p ↦ ∃ y : V, R x y ∧ p = ⟨x, y⟩ₖ)
    definability
  have hfunS : ∀ x : V, x ∈ X → ∃! p : V, S x p := by
    intro x hx
    rcases hfun x hx with ⟨y, hy, hyu⟩
    refine ⟨⟨x, y⟩ₖ, ⟨y, hy, rfl⟩, ?_⟩
    intro p hp
    rcases hp with ⟨y', hy', hp⟩
    have : y' = y := hyu y' hy'
    rcases this
    simp [hp]
  rcases replacement_exists_on (X := X) S hS hfunS with ⟨f, hf⟩
  have hmem : ∀ p : V, p ∈ f ↔ ∃ x ∈ X, ∃ y, R x y ∧ p = ⟨x, y⟩ₖ := by
    intro p
    constructor
    · intro hp
      rcases (hf p).1 hp with ⟨x, hxX, hpS⟩
      rcases hpS with ⟨y, hy, rfl⟩
      exact ⟨x, hxX, y, hy, rfl⟩
    · rintro ⟨x, hxX, y, hy, rfl⟩
      exact (hf _).2 ⟨x, hxX, ⟨y, hy, rfl⟩⟩
  have hgraph : ∀ x ∈ X, ∀ y, ⟨x, y⟩ₖ ∈ f ↔ R x y := by
    intro x hxX y
    constructor
    · intro hxy
      rcases (hmem _).1 hxy with ⟨x', hx'X, y', hy', hxy'⟩
      rcases kpair_inj hxy' with ⟨rfl, rfl⟩
      exact hy'
    · intro hxy
      exact (hmem _).2 ⟨x, hxX, y, hxy, rfl⟩
  have hdomain : domain f = X := by
    apply subset_antisymm
    · intro x hx
      rcases mem_domain_iff.mp hx with ⟨y, hxy⟩
      rcases (hmem _).1 hxy with ⟨x', hx'X, y', -, hxy'⟩
      rcases kpair_inj hxy' with ⟨rfl, -⟩
      exact hx'X
    · intro x hxX
      rcases hfun x hxX with ⟨y, hy, -⟩
      exact mem_domain_iff.mpr ⟨y, (hgraph x hxX y).2 hy⟩
  have hfunc_mem : f ∈ range f ^ domain f := by
    apply mem_function.intro
    · intro p hp
      rcases (hmem _).1 hp with ⟨x, hxX, y, hy, rfl⟩
      have hxyf : ⟨x, y⟩ₖ ∈ f := (hgraph x hxX y).2 hy
      have hxd : x ∈ domain f := mem_domain_of_kpair_mem hxyf
      have hyr : y ∈ range f := mem_range_of_kpair_mem hxyf
      simpa [mem_prod_iff] using ⟨hxd, hyr⟩
    · intro x hx
      rcases mem_domain_iff.mp hx with ⟨y₀, hxy₀⟩
      refine ExistsUnique.intro y₀ hxy₀ ?_
      intro y₁ hxy₁
      have hxX : x ∈ X := by simpa [hdomain] using hx
      have hR₀ : R x y₀ := (hgraph x hxX y₀).1 hxy₀
      have hR₁ : R x y₁ := (hgraph x hxX y₁).1 hxy₁
      exact (hfun x hxX).unique hR₁ hR₀
  refine ⟨f, IsFunction.of_mem hfunc_mem, hdomain, ?_⟩
  intro x hx y
  simpa [R, Function.Graph] using hgraph x hx y

/-! ### Orders and initial-segment isomorphisms -/

/-- A strict total order relation on `X`. -/
def IsStrictLinearOrderOn (R X : V) : Prop :=
  R ⊆ X ×ˢ X ∧
  (∀ x ∈ X, ⟨x, x⟩ₖ ∉ R) ∧
  (∀ x ∈ X, ∀ y ∈ X, ∀ z ∈ X, ⟨x, y⟩ₖ ∈ R → ⟨y, z⟩ₖ ∈ R → ⟨x, z⟩ₖ ∈ R) ∧
  (∀ x ∈ X, ∀ y ∈ X, ⟨x, y⟩ₖ ∈ R ∨ x = y ∨ ⟨y, x⟩ₖ ∈ R)

namespace IsStrictLinearOrderOn

lemma subset_prod {R X : V} (h : IsStrictLinearOrderOn R X) : R ⊆ X ×ˢ X := h.1

lemma irrefl {R X x : V} (h : IsStrictLinearOrderOn R X) (hx : x ∈ X) : ⟨x, x⟩ₖ ∉ R := h.2.1 x hx

lemma trans {R X x y z : V} (h : IsStrictLinearOrderOn R X) (hx : x ∈ X) (hy : y ∈ X) (hz : z ∈ X)
    (hxy : ⟨x, y⟩ₖ ∈ R) (hyz : ⟨y, z⟩ₖ ∈ R) : ⟨x, z⟩ₖ ∈ R := h.2.2.1 x hx y hy z hz hxy hyz

lemma trichotomy {R X x y : V} (h : IsStrictLinearOrderOn R X) (hx : x ∈ X) (hy : y ∈ X) :
    ⟨x, y⟩ₖ ∈ R ∨ x = y ∨ ⟨y, x⟩ₖ ∈ R := h.2.2.2 x hx y hy

lemma asymm {R X x y : V} (h : IsStrictLinearOrderOn R X) (hx : x ∈ X) (hy : y ∈ X)
    (hxy : ⟨x, y⟩ₖ ∈ R) (hyx : ⟨y, x⟩ₖ ∈ R) : False := by
  have hxx : ⟨x, x⟩ₖ ∈ R := h.trans hx hy hx hxy hyx
  exact h.irrefl hx hxx

end IsStrictLinearOrderOn

/-- `m` is the least element of `A` with respect to strict order `R`. -/
def IsLeastOf (R A m : V) : Prop :=
  m ∈ A ∧ ∀ a ∈ A, a = m ∨ ⟨m, a⟩ₖ ∈ R

/-- `R` well-orders `X` (strict-order form). -/
def IsWellOrderOn (R X : V) : Prop :=
  IsStrictLinearOrderOn R X ∧
  ∀ A, A ⊆ X → A ≠ ∅ → ∃ m, IsLeastOf R A m

/-! ### Ordered sum/product of strict orders -/

/-- Carrier for a disjoint-union presentation without tags. -/
noncomputable def orderedUnionCarrier (X Y : V) : V := X ∪ Y

/--
Ordered-sum relation on the plain union carrier:
- on `X`, follow `R`;
- every `X`-element is below every `Y`-element;
- on `Y`, follow `S`.

This is intended to be used with a disjointness hypothesis `X ∩ Y = ∅`.
-/
noncomputable def orderedUnionRel (R X S Y : V) : V :=
  {p ∈ orderedUnionCarrier X Y ×ˢ orderedUnionCarrier X Y ;
    ∃ x₁ x₂, p = ⟨x₁, x₂⟩ₖ ∧
      ((x₁ ∈ X ∧ x₂ ∈ X ∧ ⟨x₁, x₂⟩ₖ ∈ R) ∨
       (x₁ ∈ X ∧ x₂ ∈ Y) ∨
       (x₁ ∈ Y ∧ x₂ ∈ Y ∧ ⟨x₁, x₂⟩ₖ ∈ S))}

def orderedUnionRel.dfn : Semisentence ℒₛₑₜ 5 := f“T R X S Y.
  ∀ p, p ∈ T ↔
    p ∈ !prod.dfn (!union.dfn X Y) (!union.dfn X Y) ∧
    ∃ x₁ x₂, p = !kpair.dfn x₁ x₂ ∧
      ((x₁ ∈ X ∧ x₂ ∈ X ∧ !kpair.dfn x₁ x₂ ∈ R) ∨
       (x₁ ∈ X ∧ x₂ ∈ Y) ∨
       (x₁ ∈ Y ∧ x₂ ∈ Y ∧ !kpair.dfn x₁ x₂ ∈ S))”

instance orderedUnionRel.defined : ℒₛₑₜ-function₄[V] orderedUnionRel via orderedUnionRel.dfn :=
  ⟨fun v ↦ by
    simp [orderedUnionRel.dfn]
    simp [orderedUnionRel, orderedUnionCarrier, mem_ext_iff]⟩

instance orderedUnionRel.definable : ℒₛₑₜ-function₄[V] orderedUnionRel :=
  orderedUnionRel.defined.to_definable

lemma orderedUnionRel_subset_prod (R X S Y : V) :
    orderedUnionRel R X S Y ⊆ orderedUnionCarrier X Y ×ˢ orderedUnionCarrier X Y := sep_subset

@[simp] lemma mem_orderedUnionCarrier_iff {X Y z : V} :
    z ∈ orderedUnionCarrier X Y ↔ z ∈ X ∨ z ∈ Y := by
  simp [orderedUnionCarrier]

@[simp] lemma kpair_mem_orderedUnionRel_iff {R X S Y a b : V} :
    ⟨a, b⟩ₖ ∈ orderedUnionRel R X S Y ↔
      a ∈ orderedUnionCarrier X Y ∧
      b ∈ orderedUnionCarrier X Y ∧
      ((a ∈ X ∧ b ∈ X ∧ ⟨a, b⟩ₖ ∈ R) ∨
       (a ∈ X ∧ b ∈ Y) ∨
       (a ∈ Y ∧ b ∈ Y ∧ ⟨a, b⟩ₖ ∈ S)) := by
  constructor
  · intro h
    rcases mem_sep_iff.mp h with ⟨hprod, hrel⟩
    rcases hrel with ⟨x₁, x₂, hp, hcases⟩
    rcases kpair_inj hp with ⟨rfl, rfl⟩
    exact ⟨(kpair_mem_iff.mp hprod).1, (kpair_mem_iff.mp hprod).2, hcases⟩
  · rintro ⟨ha, hb, hcases⟩
    refine mem_sep_iff.mpr ?_
    refine ⟨?_, ?_⟩
    · simpa [kpair_mem_iff] using And.intro ha hb
    · exact ⟨a, b, rfl, hcases⟩

/-- Carrier of the disjoint sum `X ⊕ Y`, encoded by tags `0` and `1`. -/
noncomputable def orderSumCarrier (X Y : V) : V := (X ×ˢ {0}) ∪ (Y ×ˢ {1})

def orderSumCarrier.dfn : Semisentence ℒₛₑₜ 3 :=
  f“C X Y.
    ∃ z o, !isEmpty z ∧ !succ.dfn o z ∧
      C = !union.dfn (!prod.dfn X (!singleton.dfn z)) (!prod.dfn Y (!singleton.dfn o))”

instance orderSumCarrier.defined : ℒₛₑₜ-function₂[V] orderSumCarrier via orderSumCarrier.dfn :=
  ⟨fun v ↦ by
    simp [orderSumCarrier.dfn, orderSumCarrier, isEmpty_iff_eq_empty, succ, zero_def, one_def]⟩

instance orderSumCarrier.definable : ℒₛₑₜ-function₂[V] orderSumCarrier :=
  orderSumCarrier.defined.to_definable

@[simp] lemma mem_orderSumCarrier_iff {X Y x i : V} :
    ⟨x, i⟩ₖ ∈ orderSumCarrier X Y ↔ (x ∈ X ∧ i = 0) ∨ (x ∈ Y ∧ i = 1) := by
  simp [orderSumCarrier, kpair_mem_iff]

lemma mem_orderSumCarrier_cases {X Y p : V} (hp : p ∈ orderSumCarrier X Y) :
    (∃ x, x ∈ X ∧ p = ⟨x, 0⟩ₖ) ∨ (∃ y, y ∈ Y ∧ p = ⟨y, 1⟩ₖ) := by
  rcases mem_union_iff.mp hp with (hpX | hpY)
  · rcases show ∃ x ∈ X, ∃ i ∈ ({0} : V), p = ⟨x, i⟩ₖ from by
      simpa [mem_prod_iff] using hpX with ⟨x, hxX, i, hi0, rfl⟩
    have : i = 0 := by simpa using hi0
    subst this
    exact Or.inl ⟨x, hxX, rfl⟩
  · rcases show ∃ y ∈ Y, ∃ i ∈ ({1} : V), p = ⟨y, i⟩ₖ from by
      simpa [mem_prod_iff] using hpY with ⟨y, hyY, i, hi1, rfl⟩
    have : i = 1 := by simpa using hi1
    subst this
    exact Or.inr ⟨y, hyY, rfl⟩

/-- Generic projection to a fixed tag. -/
noncomputable def tagProj (i x : V) : V := ⟨x, i⟩ₖ

def tagProj.dfn : Semisentence ℒₛₑₜ 3 := f“p i x. p = !kpair.dfn x i”

instance tagProj.defined : ℒₛₑₜ-function₂[V] tagProj via tagProj.dfn :=
  ⟨fun v ↦ by simp [tagProj.dfn, tagProj]⟩

instance tagProj.definable : ℒₛₑₜ-function₂[V] tagProj :=
  tagProj.defined.to_definable

/-- Lift a relation on `X` to the tagged copy `X × {i}` using `tagProj i`. -/
noncomputable def taggedRel (R X i : V) : V :=
  {p ∈ (X ×ˢ {i}) ×ˢ (X ×ˢ {i}) ;
    ∃ x₁ x₂, p = ⟨tagProj i x₁, tagProj i x₂⟩ₖ ∧ ⟨x₁, x₂⟩ₖ ∈ R}

def taggedRel.dfn : Semisentence ℒₛₑₜ 4 := f“T R X i.
  ∀ p, p ∈ T ↔
    p ∈ !prod.dfn (!prod.dfn X (!singleton.dfn i)) (!prod.dfn X (!singleton.dfn i)) ∧
    ∃ x₁ x₂, p = !kpair.dfn (!tagProj.dfn i x₁) (!tagProj.dfn i x₂) ∧ !kpair.dfn x₁ x₂ ∈ R”

instance taggedRel.defined : ℒₛₑₜ-function₃[V] taggedRel via taggedRel.dfn :=
  ⟨fun v ↦ by
    simp [taggedRel.dfn]
    simp [taggedRel, tagProj, mem_ext_iff]⟩

instance taggedRel.definable : ℒₛₑₜ-function₃[V] taggedRel :=
  taggedRel.defined.to_definable

@[simp] lemma kpair_mem_taggedRel_iff {R X i x₁ x₂ : V} :
    ⟨tagProj i x₁, tagProj i x₂⟩ₖ ∈ taggedRel R X i ↔
      x₁ ∈ X ∧ x₂ ∈ X ∧ ⟨x₁, x₂⟩ₖ ∈ R := by
  constructor
  · intro h
    rcases mem_sep_iff.mp h with ⟨hprod, hrel⟩
    rcases hrel with ⟨u, v, hp, huv⟩
    rcases kpair_inj hp with ⟨hu, hv⟩
    have hu' : u = x₁ := by simpa [tagProj] using (kpair_inj hu).1.symm
    have hv' : v = x₂ := by simpa [tagProj] using (kpair_inj hv).1.symm
    subst hu'
    subst hv'
    have hx₁ : u ∈ X := by
      have : tagProj i u ∈ X ×ˢ {i} := (kpair_mem_iff.mp hprod).1
      simpa [tagProj, mem_prod_iff, kpair_mem_iff] using this
    have hx₂ : v ∈ X := by
      have : tagProj i v ∈ X ×ˢ {i} := (kpair_mem_iff.mp hprod).2
      simpa [tagProj, mem_prod_iff, kpair_mem_iff] using this
    exact ⟨hx₁, hx₂, huv⟩
  · rintro ⟨hx₁, hx₂, hR⟩
    refine mem_sep_iff.mpr ?_
    refine ⟨?_, ?_⟩
    · have hx₁t : tagProj i x₁ ∈ X ×ˢ {i} := by
        simpa [tagProj, mem_prod_iff, kpair_mem_iff] using hx₁
      have hx₂t : tagProj i x₂ ∈ X ×ˢ {i} := by
        simpa [tagProj, mem_prod_iff, kpair_mem_iff] using hx₂
      simpa [kpair_mem_iff] using And.intro hx₁t hx₂t
    · exact ⟨x₁, x₂, rfl, hR⟩

/--
Ordered sum relation:
- on the left copy it follows `R`,
- every left element is below every right element,
- on the right copy it follows `S`.
-/
noncomputable def orderSumRel (R X S Y : V) : V :=
  orderedUnionRel
    (taggedRel R X 0) (X ×ˢ {0})
    (taggedRel S Y 1) (Y ×ˢ {1})

def orderSumRel.dfn : Semisentence ℒₛₑₜ 5 := f“T R X S Y.
  ∃ z o, !isEmpty z ∧ !succ.dfn o z ∧
    T = !orderedUnionRel.dfn
      (!taggedRel.dfn R X z) (!prod.dfn X (!singleton.dfn z))
      (!taggedRel.dfn S Y o) (!prod.dfn Y (!singleton.dfn o))”

instance orderSumRel.defined : ℒₛₑₜ-function₄[V] orderSumRel via orderSumRel.dfn :=
  ⟨fun v ↦ by
    simp [orderSumRel.dfn, orderSumRel, zero_def, one_def, succ]⟩

instance orderSumRel.definable : ℒₛₑₜ-function₄[V] orderSumRel :=
  orderSumRel.defined.to_definable

/--
Projection graph from tagged carrier to plain carrier:
`⟨x,0⟩ ↦ x` on the left and `⟨y,1⟩ ↦ y` on the right.
-/
noncomputable def orderSumProjection (X Y : V) : V :=
  {p ∈ orderSumCarrier X Y ×ˢ orderedUnionCarrier X Y ;
    ∃ z, (z ∈ X ∧ p = ⟨⟨z, 0⟩ₖ, z⟩ₖ) ∨ (z ∈ Y ∧ p = ⟨⟨z, 1⟩ₖ, z⟩ₖ)}

lemma orderSumRel_subset_prod (R X S Y : V) :
    orderSumRel R X S Y ⊆ orderSumCarrier X Y ×ˢ orderSumCarrier X Y := by
  simpa [orderSumRel, orderSumCarrier, orderedUnionCarrier] using
    (orderedUnionRel_subset_prod
      (taggedRel R X 0) (X ×ˢ {0}) (taggedRel S Y 1) (Y ×ˢ {1}))

@[simp] lemma kpair_mem_orderSumRel_left_left_iff {R X S Y x₁ x₂ : V} :
    ⟨⟨x₁, 0⟩ₖ, ⟨x₂, 0⟩ₖ⟩ₖ ∈ orderSumRel R X S Y ↔ x₁ ∈ X ∧ x₂ ∈ X ∧ ⟨x₁, x₂⟩ₖ ∈ R := by
  constructor
  · intro h
    have h' : ⟨⟨x₁, 0⟩ₖ, ⟨x₂, 0⟩ₖ⟩ₖ ∈ orderedUnionRel
        (taggedRel R X 0) (X ×ˢ {0}) (taggedRel S Y 1) (Y ×ˢ {1}) := h
    rcases kpair_mem_orderedUnionRel_iff.mp h' with ⟨_, _, hcase⟩
    rcases hcase with (⟨hx₁mem, _, htagged⟩ | ⟨_, hx₂mem⟩ | ⟨hx₁mem, _⟩)
    · have hR' : x₁ ∈ X ∧ x₂ ∈ X ∧ ⟨x₁, x₂⟩ₖ ∈ R := by
        have : ⟨tagProj 0 x₁, tagProj 0 x₂⟩ₖ ∈ taggedRel R X 0 := by
          simp only [tagProj]; exact htagged
        exact kpair_mem_taggedRel_iff.mp this
      exact hR'
    · have : (0 : V) ∈ ({1} : V) := (kpair_mem_iff.mp hx₂mem).2
      simp at this
    · have : (0 : V) ∈ ({1} : V) := (kpair_mem_iff.mp hx₁mem).2
      simp at this
  · rintro ⟨hx₁X, hx₂X, hR⟩
    show ⟨⟨x₁, 0⟩ₖ, ⟨x₂, 0⟩ₖ⟩ₖ ∈ orderedUnionRel
        (taggedRel R X 0) (X ×ˢ {0}) (taggedRel S Y 1) (Y ×ˢ {1})
    refine kpair_mem_orderedUnionRel_iff.mpr ⟨?_, ?_, ?_⟩
    · simp [mem_orderedUnionCarrier_iff, kpair_mem_iff, hx₁X]
    · simp [mem_orderedUnionCarrier_iff, kpair_mem_iff, hx₂X]
    · left
      refine ⟨by simp [kpair_mem_iff, hx₁X], by simp [kpair_mem_iff, hx₂X], ?_⟩
      show ⟨tagProj 0 x₁, tagProj 0 x₂⟩ₖ ∈ taggedRel R X 0
      exact kpair_mem_taggedRel_iff.mpr ⟨hx₁X, hx₂X, hR⟩

@[simp] lemma kpair_mem_orderSumRel_left_right_iff {R X S Y x y : V} :
    ⟨⟨x, 0⟩ₖ, ⟨y, 1⟩ₖ⟩ₖ ∈ orderSumRel R X S Y ↔ x ∈ X ∧ y ∈ Y := by
  constructor
  · intro h
    have h' : ⟨⟨x, 0⟩ₖ, ⟨y, 1⟩ₖ⟩ₖ ∈ orderedUnionRel
        (taggedRel R X 0) (X ×ˢ {0}) (taggedRel S Y 1) (Y ×ˢ {1}) := h
    rcases kpair_mem_orderedUnionRel_iff.mp h' with ⟨hx, hy, _⟩
    constructor
    · rcases mem_orderedUnionCarrier_iff.mp hx with (hX | hY)
      · exact (kpair_mem_iff.mp hX).1
      · have : (0 : V) ∈ ({1} : V) := (kpair_mem_iff.mp hY).2; simp at this
    · rcases mem_orderedUnionCarrier_iff.mp hy with (hX | hY)
      · have : (1 : V) ∈ ({0} : V) := (kpair_mem_iff.mp hX).2; simp at this
      · exact (kpair_mem_iff.mp hY).1
  · rintro ⟨hxX, hyY⟩
    show ⟨⟨x, 0⟩ₖ, ⟨y, 1⟩ₖ⟩ₖ ∈ orderedUnionRel
        (taggedRel R X 0) (X ×ˢ {0}) (taggedRel S Y 1) (Y ×ˢ {1})
    refine kpair_mem_orderedUnionRel_iff.mpr ⟨?_, ?_, ?_⟩
    · simp [mem_orderedUnionCarrier_iff, kpair_mem_iff, hxX]
    · simp [mem_orderedUnionCarrier_iff, kpair_mem_iff, hyY]
    · exact Or.inr <| Or.inl ⟨by simp [kpair_mem_iff, hxX], by simp [kpair_mem_iff, hyY]⟩

@[simp] lemma kpair_mem_orderSumRel_right_right_iff {R X S Y y₁ y₂ : V} :
    ⟨⟨y₁, 1⟩ₖ, ⟨y₂, 1⟩ₖ⟩ₖ ∈ orderSumRel R X S Y ↔ y₁ ∈ Y ∧ y₂ ∈ Y ∧ ⟨y₁, y₂⟩ₖ ∈ S := by
  constructor
  · intro h
    have h' : ⟨⟨y₁, 1⟩ₖ, ⟨y₂, 1⟩ₖ⟩ₖ ∈ orderedUnionRel
        (taggedRel R X 0) (X ×ˢ {0}) (taggedRel S Y 1) (Y ×ˢ {1}) := h
    rcases kpair_mem_orderedUnionRel_iff.mp h' with ⟨_, _, hcase⟩
    rcases hcase with (⟨hy₁mem, _, _⟩ | ⟨hy₁mem, _⟩ | ⟨_, _, htagged⟩)
    · have : (1 : V) ∈ ({0} : V) := (kpair_mem_iff.mp hy₁mem).2; simp at this
    · have : (1 : V) ∈ ({0} : V) := (kpair_mem_iff.mp hy₁mem).2; simp at this
    · have hS' : y₁ ∈ Y ∧ y₂ ∈ Y ∧ ⟨y₁, y₂⟩ₖ ∈ S := by
        have : ⟨tagProj 1 y₁, tagProj 1 y₂⟩ₖ ∈ taggedRel S Y 1 := by
          simp only [tagProj]; exact htagged
        exact kpair_mem_taggedRel_iff.mp this
      exact hS'
  · rintro ⟨hy₁Y, hy₂Y, hS⟩
    show ⟨⟨y₁, 1⟩ₖ, ⟨y₂, 1⟩ₖ⟩ₖ ∈ orderedUnionRel
        (taggedRel R X 0) (X ×ˢ {0}) (taggedRel S Y 1) (Y ×ˢ {1})
    refine kpair_mem_orderedUnionRel_iff.mpr ⟨?_, ?_, ?_⟩
    · simp [mem_orderedUnionCarrier_iff, kpair_mem_iff, hy₁Y]
    · simp [mem_orderedUnionCarrier_iff, kpair_mem_iff, hy₂Y]
    · right; right
      refine ⟨by simp [kpair_mem_iff, hy₁Y], by simp [kpair_mem_iff, hy₂Y], ?_⟩
      show ⟨tagProj 1 y₁, tagProj 1 y₂⟩ₖ ∈ taggedRel S Y 1
      exact kpair_mem_taggedRel_iff.mpr ⟨hy₁Y, hy₂Y, hS⟩

@[simp] lemma kpair_mem_orderSumRel_right_left_iff {R X S Y y x : V} :
    ⟨⟨y, 1⟩ₖ, ⟨x, 0⟩ₖ⟩ₖ ∈ orderSumRel R X S Y ↔ False := by
  constructor
  · intro h
    have h' : ⟨⟨y, 1⟩ₖ, ⟨x, 0⟩ₖ⟩ₖ ∈ orderedUnionRel
        (taggedRel R X 0) (X ×ˢ {0}) (taggedRel S Y 1) (Y ×ˢ {1}) := h
    rcases kpair_mem_orderedUnionRel_iff.mp h' with ⟨_, _, hcase⟩
    rcases hcase with (⟨hymem, _, _⟩ | ⟨hymem, _⟩ | ⟨_, hxmem, _⟩)
    · have : (1 : V) ∈ ({0} : V) := (kpair_mem_iff.mp hymem).2; simp at this
    · have : (1 : V) ∈ ({0} : V) := (kpair_mem_iff.mp hymem).2; simp at this
    · have : (0 : V) ∈ ({1} : V) := (kpair_mem_iff.mp hxmem).2; simp at this
  · intro h
    exact False.elim h

lemma orderSum_isStrictLinearOrderOn
    {R X S Y : V}
    (hR : IsStrictLinearOrderOn R X)
    (hS : IsStrictLinearOrderOn S Y) :
    IsStrictLinearOrderOn (orderSumRel R X S Y) (orderSumCarrier X Y) := by
  refine ⟨orderSumRel_subset_prod R X S Y, ?_, ?_, ?_⟩
  · intro p hp
    rcases mem_orderSumCarrier_cases hp with (⟨x, hxX, rfl⟩ | ⟨y, hyY, rfl⟩)
    · intro hxx
      exact hR.irrefl hxX (kpair_mem_orderSumRel_left_left_iff.mp hxx).2.2
    · intro hyy
      exact hS.irrefl hyY (kpair_mem_orderSumRel_right_right_iff.mp hyy).2.2
  · intro p hp q hq r hr hpq hqr
    rcases mem_orderSumCarrier_cases hp with (⟨x, hxX, rfl⟩ | ⟨x, hxY, rfl⟩)
    · rcases mem_orderSumCarrier_cases hq with (⟨y, hyX, rfl⟩ | ⟨y, hyY, rfl⟩)
      · rcases mem_orderSumCarrier_cases hr with (⟨z, hzX, rfl⟩ | ⟨z, hzY, rfl⟩)
        · have hxy : ⟨x, y⟩ₖ ∈ R := (kpair_mem_orderSumRel_left_left_iff.mp hpq).2.2
          have hyz : ⟨y, z⟩ₖ ∈ R := (kpair_mem_orderSumRel_left_left_iff.mp hqr).2.2
          exact (kpair_mem_orderSumRel_left_left_iff.mpr
            ⟨hxX, hzX, hR.trans hxX hyX hzX hxy hyz⟩)
        · exact kpair_mem_orderSumRel_left_right_iff.mpr ⟨hxX, hzY⟩
      · rcases mem_orderSumCarrier_cases hr with (⟨z, hzX, rfl⟩ | ⟨z, hzY, rfl⟩)
        · exact (kpair_mem_orderSumRel_right_left_iff.mp hqr).elim
        · exact kpair_mem_orderSumRel_left_right_iff.mpr ⟨hxX, hzY⟩
    · rcases mem_orderSumCarrier_cases hq with (⟨y, hyX, rfl⟩ | ⟨y, hyY, rfl⟩)
      · exact (kpair_mem_orderSumRel_right_left_iff.mp hpq).elim
      · rcases mem_orderSumCarrier_cases hr with (⟨z, hzX, rfl⟩ | ⟨z, hzY, rfl⟩)
        · exact (kpair_mem_orderSumRel_right_left_iff.mp hqr).elim
        · have hxy : ⟨x, y⟩ₖ ∈ S := (kpair_mem_orderSumRel_right_right_iff.mp hpq).2.2
          have hyz : ⟨y, z⟩ₖ ∈ S := (kpair_mem_orderSumRel_right_right_iff.mp hqr).2.2
          exact (kpair_mem_orderSumRel_right_right_iff.mpr
            ⟨hxY, hzY, hS.trans hxY hyY hzY hxy hyz⟩)
  · intro p hp q hq
    rcases mem_orderSumCarrier_cases hp with (⟨x, hxX, rfl⟩ | ⟨x, hxY, rfl⟩)
    · rcases mem_orderSumCarrier_cases hq with (⟨y, hyX, rfl⟩ | ⟨y, hyY, rfl⟩)
      · rcases hR.trichotomy hxX hyX with (hxy | hEq | hyx)
        · exact Or.inl <| kpair_mem_orderSumRel_left_left_iff.mpr ⟨hxX, hyX, hxy⟩
        · exact Or.inr <| Or.inl <| by simp [hEq]
        · exact Or.inr <| Or.inr <| kpair_mem_orderSumRel_left_left_iff.mpr ⟨hyX, hxX, hyx⟩
      · exact Or.inl <| kpair_mem_orderSumRel_left_right_iff.mpr ⟨hxX, hyY⟩
    · rcases mem_orderSumCarrier_cases hq with (⟨y, hyX, rfl⟩ | ⟨y, hyY, rfl⟩)
      · exact Or.inr <| Or.inr <| kpair_mem_orderSumRel_left_right_iff.mpr ⟨hyX, hxY⟩
      · rcases hS.trichotomy hxY hyY with (hxy | hEq | hyx)
        · exact Or.inl <| kpair_mem_orderSumRel_right_right_iff.mpr ⟨hxY, hyY, hxy⟩
        · exact Or.inr <| Or.inl <| by simp [hEq]
        · exact Or.inr <| Or.inr <| kpair_mem_orderSumRel_right_right_iff.mpr ⟨hyY, hxY, hyx⟩

lemma orderSum_isWellOrderOn
    {R X S Y : V}
    (hR : IsWellOrderOn R X)
    (hS : IsWellOrderOn S Y) :
    IsWellOrderOn (orderSumRel R X S Y) (orderSumCarrier X Y) := by
  refine ⟨orderSum_isStrictLinearOrderOn hR.1 hS.1, ?_⟩
  intro A hA hAne
  let A₀ : V := {x ∈ X ; ⟨x, 0⟩ₖ ∈ A}
  have hA₀sub : A₀ ⊆ X := sep_subset
  by_cases hA₀empty : A₀ = ∅
  · let A₁ : V := {y ∈ Y ; ⟨y, 1⟩ₖ ∈ A}
    have hA₁sub : A₁ ⊆ Y := sep_subset
    have hA₁ne : A₁ ≠ ∅ := by
      intro hA₁0
      have hAisNonempty : IsNonempty A := ne_empty_iff_isNonempty.mp hAne
      rcases hAisNonempty with ⟨a, haA⟩
      have haC : a ∈ orderSumCarrier X Y := hA _ haA
      rcases mem_orderSumCarrier_cases haC with (⟨x, hxX, ha⟩ | ⟨y, hyY, ha⟩)
      · have : x ∈ A₀ := by simpa [A₀, ha] using And.intro hxX haA
        have : x ∈ (∅ : V) := by simp [hA₀empty] at this
        simp at this
      · have : y ∈ A₁ := by simpa [A₁, ha] using And.intro hyY haA
        have : y ∈ (∅ : V) := by simp [hA₁0] at this
        simp at this
    rcases hS.2 A₁ hA₁sub hA₁ne with ⟨m, hmA₁, hmLeast⟩
    refine ⟨⟨m, 1⟩ₖ, ?_⟩
    refine ⟨?_, ?_⟩
    · exact (mem_sep_iff.mp hmA₁).2
    · intro a haA
      have haC : a ∈ orderSumCarrier X Y := hA _ haA
      rcases mem_orderSumCarrier_cases haC with (⟨x, hxX, rfl⟩ | ⟨y, hyY, rfl⟩)
      · have hxA₀ : x ∈ A₀ := by simpa [A₀] using And.intro hxX haA
        have : x ∈ (∅ : V) := by simp [hA₀empty] at hxA₀
        simp at this
      · have hyA₁ : y ∈ A₁ := by simpa [A₁] using And.intro hyY haA
        rcases hmLeast y hyA₁ with (hyEq | hmy)
        · left
          simp [hyEq]
        · right
          exact kpair_mem_orderSumRel_right_right_iff.mpr
            ⟨(mem_sep_iff.mp hmA₁).1, hyY, hmy⟩
  · have hA₀ne : A₀ ≠ ∅ := hA₀empty
    rcases hR.2 A₀ hA₀sub hA₀ne with ⟨m, hmA₀, hmLeast⟩
    refine ⟨⟨m, 0⟩ₖ, ?_⟩
    refine ⟨?_, ?_⟩
    · exact (mem_sep_iff.mp hmA₀).2
    · intro a haA
      have haC : a ∈ orderSumCarrier X Y := hA _ haA
      rcases mem_orderSumCarrier_cases haC with (⟨x, hxX, rfl⟩ | ⟨y, hyY, rfl⟩)
      · have hxA₀ : x ∈ A₀ := by simpa [A₀] using And.intro hxX haA
        rcases hmLeast x hxA₀ with (hxEq | hmx)
        · left
          simp [hxEq]
        · right
          exact kpair_mem_orderSumRel_left_left_iff.mpr
            ⟨(mem_sep_iff.mp hmA₀).1, hxX, hmx⟩
      · right
        exact kpair_mem_orderSumRel_left_right_iff.mpr
          ⟨(mem_sep_iff.mp hmA₀).1, hyY⟩

/--
Lexicographic product relation with priority on the second coordinate:
`(x₁,y₁) < (x₂,y₂)` iff `y₁ <_S y₂` or (`y₁ = y₂` and `x₁ <_R x₂`).
-/
noncomputable def orderProdRel (R X S Y : V) : V := {p ∈ (X ×ˢ Y) ×ˢ (X ×ˢ Y) ;
  ∃ x₁ y₁ x₂ y₂, p = ⟨⟨x₁, y₁⟩ₖ, ⟨x₂, y₂⟩ₖ⟩ₖ ∧
    (⟨y₁, y₂⟩ₖ ∈ S ∨ (y₁ = y₂ ∧ ⟨x₁, x₂⟩ₖ ∈ R))}

def orderProdRel.dfn : Semisentence ℒₛₑₜ 5 := f“T R X S Y.
  ∀ p, p ∈ T ↔
    p ∈ !prod.dfn (!prod.dfn X Y) (!prod.dfn X Y) ∧
    ∃ x₁ y₁ x₂ y₂, p = !kpair.dfn (!kpair.dfn x₁ y₁) (!kpair.dfn x₂ y₂) ∧
      (!kpair.dfn y₁ y₂ ∈ S ∨ (y₁ = y₂ ∧ !kpair.dfn x₁ x₂ ∈ R))”

instance orderProdRel.defined : ℒₛₑₜ-function₄[V] orderProdRel via orderProdRel.dfn :=
  ⟨fun v ↦ by
    simp [orderProdRel.dfn]
    simp [orderProdRel, mem_ext_iff, mem_sep_iff]⟩

instance orderProdRel.definable : ℒₛₑₜ-function₄[V] orderProdRel :=
  orderProdRel.defined.to_definable

lemma orderProdRel_subset_prod (R X S Y : V) :
    orderProdRel R X S Y ⊆ (X ×ˢ Y) ×ˢ (X ×ˢ Y) := sep_subset

@[simp] lemma kpair_mem_orderProdRel_iff {R X S Y x₁ y₁ x₂ y₂ : V} :
    ⟨⟨x₁, y₁⟩ₖ, ⟨x₂, y₂⟩ₖ⟩ₖ ∈ orderProdRel R X S Y ↔
      x₁ ∈ X ∧ y₁ ∈ Y ∧ x₂ ∈ X ∧ y₂ ∈ Y ∧
      (⟨y₁, y₂⟩ₖ ∈ S ∨ (y₁ = y₂ ∧ ⟨x₁, x₂⟩ₖ ∈ R)) := by
  constructor
  · intro h
    rcases mem_sep_iff.mp h with ⟨hprod, hrel⟩
    have hxy₁ : ⟨x₁, y₁⟩ₖ ∈ X ×ˢ Y := (kpair_mem_iff.mp hprod).1
    have hxy₂ : ⟨x₂, y₂⟩ₖ ∈ X ×ˢ Y := (kpair_mem_iff.mp hprod).2
    have hx₁ : x₁ ∈ X := (kpair_mem_iff.mp hxy₁).1
    have hy₁ : y₁ ∈ Y := (kpair_mem_iff.mp hxy₁).2
    have hx₂ : x₂ ∈ X := (kpair_mem_iff.mp hxy₂).1
    have hy₂ : y₂ ∈ Y := (kpair_mem_iff.mp hxy₂).2
    rcases hrel with ⟨u₁, v₁, u₂, v₂, hp, hlex⟩
    rcases kpair_inj hp with ⟨h₁, h₂⟩
    rcases kpair_inj h₁ with ⟨rfl, rfl⟩
    rcases kpair_inj h₂ with ⟨rfl, rfl⟩
    exact ⟨hx₁, hy₁, hx₂, hy₂, hlex⟩
  · rintro ⟨hx₁, hy₁, hx₂, hy₂, hlex⟩
    refine mem_sep_iff.mpr ?_
    refine ⟨?_, ?_⟩
    · simpa [mem_prod_iff] using
        And.intro (And.intro hx₁ hy₁) (And.intro hx₂ hy₂)
    · exact ⟨x₁, y₁, x₂, y₂, rfl, hlex⟩

lemma orderProd_isStrictLinearOrderOn
    {R X S Y : V}
    (hR : IsStrictLinearOrderOn R X)
    (hS : IsStrictLinearOrderOn S Y) :
    IsStrictLinearOrderOn (orderProdRel R X S Y) (X ×ˢ Y) := by
  refine ⟨orderProdRel_subset_prod R X S Y, ?_, ?_, ?_⟩
  · intro p hp
    rcases show ∃ x ∈ X, ∃ y ∈ Y, p = ⟨x, y⟩ₖ from by simpa [mem_prod_iff] using hp with
      ⟨x, hxX, y, hyY, rfl⟩
    intro hpp
    have : ⟨y, y⟩ₖ ∈ S ∨ (y = y ∧ ⟨x, x⟩ₖ ∈ R) := (kpair_mem_orderProdRel_iff.mp hpp).2.2.2.2
    rcases this with (hyy | hxx)
    · exact hS.irrefl hyY hyy
    · exact hR.irrefl hxX hxx.2
  · intro p hp q hq r hr hpq hqr
    rcases show ∃ x₁ ∈ X, ∃ y₁ ∈ Y, p = ⟨x₁, y₁⟩ₖ from by simpa [mem_prod_iff] using hp with
      ⟨x₁, hx₁X, y₁, hy₁Y, rfl⟩
    rcases show ∃ x₂ ∈ X, ∃ y₂ ∈ Y, q = ⟨x₂, y₂⟩ₖ from by simpa [mem_prod_iff] using hq with
      ⟨x₂, hx₂X, y₂, hy₂Y, rfl⟩
    rcases show ∃ x₃ ∈ X, ∃ y₃ ∈ Y, r = ⟨x₃, y₃⟩ₖ from by simpa [mem_prod_iff] using hr with
      ⟨x₃, hx₃X, y₃, hy₃Y, rfl⟩
    have h12 : ⟨y₁, y₂⟩ₖ ∈ S ∨ (y₁ = y₂ ∧ ⟨x₁, x₂⟩ₖ ∈ R) := (kpair_mem_orderProdRel_iff.mp hpq).2.2.2.2
    have h23 : ⟨y₂, y₃⟩ₖ ∈ S ∨ (y₂ = y₃ ∧ ⟨x₂, x₃⟩ₖ ∈ R) := (kpair_mem_orderProdRel_iff.mp hqr).2.2.2.2
    have h13 : ⟨y₁, y₃⟩ₖ ∈ S ∨ (y₁ = y₃ ∧ ⟨x₁, x₃⟩ₖ ∈ R) := by
      rcases h12 with (h12S | h12R)
      · rcases h23 with (h23S | h23R)
        · exact Or.inl <| hS.trans hy₁Y hy₂Y hy₃Y h12S h23S
        · exact Or.inl <| h23R.1 ▸ h12S
      · rcases h23 with (h23S | h23R)
        · exact Or.inl <| h12R.1.symm ▸ h23S
        · exact Or.inr ⟨h12R.1.trans h23R.1, hR.trans hx₁X hx₂X hx₃X h12R.2 h23R.2⟩
    exact kpair_mem_orderProdRel_iff.mpr ⟨hx₁X, hy₁Y, hx₃X, hy₃Y, h13⟩
  · intro p hp q hq
    rcases show ∃ x₁ ∈ X, ∃ y₁ ∈ Y, p = ⟨x₁, y₁⟩ₖ from by simpa [mem_prod_iff] using hp with
      ⟨x₁, hx₁X, y₁, hy₁Y, rfl⟩
    rcases show ∃ x₂ ∈ X, ∃ y₂ ∈ Y, q = ⟨x₂, y₂⟩ₖ from by simpa [mem_prod_iff] using hq with
      ⟨x₂, hx₂X, y₂, hy₂Y, rfl⟩
    rcases hS.trichotomy hy₁Y hy₂Y with (hy₁₂ | hyy | hy₂₁)
    · exact Or.inl <| kpair_mem_orderProdRel_iff.mpr ⟨hx₁X, hy₁Y, hx₂X, hy₂Y, Or.inl hy₁₂⟩
    · rcases hR.trichotomy hx₁X hx₂X with (hx₁₂ | hxx | hx₂₁)
      · exact Or.inl <| kpair_mem_orderProdRel_iff.mpr ⟨hx₁X, hy₁Y, hx₂X, hy₂Y, Or.inr ⟨hyy, hx₁₂⟩⟩
      · exact Or.inr <| Or.inl <| by simp [hyy, hxx]
      · exact Or.inr <| Or.inr <| kpair_mem_orderProdRel_iff.mpr ⟨hx₂X, hy₂Y, hx₁X, hy₁Y, Or.inr ⟨hyy.symm, hx₂₁⟩⟩
    · exact Or.inr <| Or.inr <| kpair_mem_orderProdRel_iff.mpr ⟨hx₂X, hy₂Y, hx₁X, hy₁Y, Or.inl hy₂₁⟩

lemma orderProd_isWellOrderOn
    {R X S Y : V}
    (hR : IsWellOrderOn R X)
    (hS : IsWellOrderOn S Y) :
    IsWellOrderOn (orderProdRel R X S Y) (X ×ˢ Y) := by
  refine ⟨orderProd_isStrictLinearOrderOn hR.1 hS.1, ?_⟩
  intro A hA hAne
  let B : V := {y ∈ Y ; ∃ x ∈ X, ⟨x, y⟩ₖ ∈ A}
  have hBsub : B ⊆ Y := sep_subset
  have hBne : B ≠ ∅ := by
    intro hB0
    have hAisNonempty : IsNonempty A := ne_empty_iff_isNonempty.mp hAne
    rcases hAisNonempty with ⟨a, haA⟩
    rcases show ∃ x ∈ X, ∃ y ∈ Y, a = ⟨x, y⟩ₖ from by
      simpa [mem_prod_iff] using hA _ haA with ⟨x, hxX, y, hyY, rfl⟩
    have hyB : y ∈ B := by
      exact mem_sep_iff.mpr ⟨hyY, ⟨x, hxX, haA⟩⟩
    have : y ∈ (∅ : V) := by simp [hB0] at hyB
    simp at this
  rcases hS.2 B hBsub hBne with ⟨y₀, hy₀B, hy₀Least⟩
  let C : V := {x ∈ X ; ⟨x, y₀⟩ₖ ∈ A}
  have hCsub : C ⊆ X := sep_subset
  have hCne : C ≠ ∅ := by
    intro hC0
    rcases mem_sep_iff.mp hy₀B with ⟨hy₀Y, hy₀w⟩
    rcases hy₀w with ⟨x, hxX, hxyA⟩
    have hxC : x ∈ C := by exact mem_sep_iff.mpr ⟨hxX, hxyA⟩
    have : x ∈ (∅ : V) := by simp [hC0] at hxC
    simp at this
  rcases hR.2 C hCsub hCne with ⟨x₀, hx₀C, hx₀Least⟩
  refine ⟨⟨x₀, y₀⟩ₖ, ?_⟩
  refine ⟨(mem_sep_iff.mp hx₀C).2, ?_⟩
  intro a haA
  rcases show ∃ x ∈ X, ∃ y ∈ Y, a = ⟨x, y⟩ₖ from by
    simpa [mem_prod_iff] using hA _ haA with ⟨x, hxX, y, hyY, rfl⟩
  have hyB : y ∈ B := mem_sep_iff.mpr ⟨hyY, ⟨x, hxX, haA⟩⟩
  rcases hy₀Least y hyB with (hyEq | hyLt)
  · have hxC : x ∈ C := by simpa [C, hyEq] using And.intro hxX haA
    rcases hx₀Least x hxC with (hxEq | hxLt)
    · left
      simp [hxEq, hyEq]
    · right
      exact kpair_mem_orderProdRel_iff.mpr
        ⟨(mem_sep_iff.mp hx₀C).1, (mem_sep_iff.mp hy₀B).1, hxX, hyY, Or.inr ⟨hyEq.symm, hxLt⟩⟩
  · right
    exact kpair_mem_orderProdRel_iff.mpr
      ⟨(mem_sep_iff.mp hx₀C).1, (mem_sep_iff.mp hy₀B).1, hxX, hyY, Or.inl hyLt⟩

/-- Initial segment of `(X, R)` below `a`. -/
noncomputable def initialSegment (R X a : V) : V := {x ∈ X ; ⟨x, a⟩ₖ ∈ R}

def initialSegment.dfn : Semisentence ℒₛₑₜ 4 :=
  f“I R X a. ∀ x, x ∈ I ↔ x ∈ X ∧ !kpair.dfn x a ∈ R”

instance initialSegment.defined : ℒₛₑₜ-function₃[V] initialSegment via initialSegment.dfn :=
  ⟨fun v ↦ by
    simp [initialSegment.dfn, initialSegment]; simp only [mem_ext_iff, mem_sep_iff]⟩

instance initialSegment.definable : ℒₛₑₜ-function₃[V] initialSegment := initialSegment.defined.to_definable

lemma mem_initialSegment_iff {R X a x : V} :
    x ∈ initialSegment R X a ↔ x ∈ X ∧ ⟨x, a⟩ₖ ∈ R := by
  simp [initialSegment]

lemma initialSegment_subset (R X a : V) : initialSegment R X a ⊆ X := by
  intro x hx
  exact (mem_initialSegment_iff.mp hx).1

/-- `f` is an order isomorphism between `(X, R)` and `(Y, S)`. -/
def IsOrderIso (R X S Y f : V) : Prop :=
  f ∈ Y ^ X ∧
  Injective f ∧
  range f = Y ∧
  ∀ x₁ ∈ X, ∀ x₂ ∈ X, ⟨x₁, x₂⟩ₖ ∈ R ↔ ⟨f ‘ x₁, f ‘ x₂⟩ₖ ∈ S

lemma isOrderIso_definable : ℒₛₑₜ-relation₅[V] IsOrderIso := by
  unfold IsOrderIso
  definability

instance IsOrderIso.definable : ℒₛₑₜ-relation₅[V] IsOrderIso := isOrderIso_definable


/--
Transport order isomorphisms on each component to an isomorphism between plain ordered unions.
-/
lemma orderedUnionRel_isOrderIso_of_componentIsos
    {R X S Y R' X' S' Y' f g : V}
    (hXY : X ∩ Y = ∅)
    (hX'Y' : X' ∩ Y' = ∅)
    (hf : IsOrderIso R X R' X' f)
    (hg : IsOrderIso S Y S' Y' g) :
    IsOrderIso
      (orderedUnionRel R X S Y) (orderedUnionCarrier X Y)
      (orderedUnionRel R' X' S' Y') (orderedUnionCarrier X' Y')
      (f ∪ g) := by
  have hfFun : f ∈ X' ^ X := hf.1
  have hgFun : g ∈ Y' ^ Y := hg.1
  have hfgFun : f ∪ g ∈ orderedUnionCarrier X' Y' ^ orderedUnionCarrier X Y := by
    apply mem_function.intro
    · intro p hp
      rcases mem_union_iff.mp hp with (hpF | hpG)
      · rcases show ∃ x ∈ X, ∃ y ∈ X', p = ⟨x, y⟩ₖ from by
          simpa [mem_prod_iff] using subset_prod_of_mem_function hfFun p hpF with ⟨x, hxX, y, hyX', rfl⟩
        simp [orderedUnionCarrier, mem_prod_iff, hxX, hyX']
      · rcases show ∃ x ∈ Y, ∃ y ∈ Y', p = ⟨x, y⟩ₖ from by
          simpa [mem_prod_iff] using subset_prod_of_mem_function hgFun p hpG with ⟨x, hxY, y, hyY', rfl⟩
        simp [orderedUnionCarrier, mem_prod_iff, hxY, hyY']
    · intro x hxU
      rcases (mem_orderedUnionCarrier_iff.mp hxU) with (hxX | hxY)
      · rcases exists_unique_of_mem_function hfFun x hxX with ⟨y, hxyF, huniqF⟩
        refine ⟨y, mem_union_iff.mpr (Or.inl hxyF), ?_⟩
        intro y' hxy'
        rcases mem_union_iff.mp hxy' with (hxy'F | hxy'G)
        · exact huniqF y' hxy'F
        · have hxY' : x ∈ Y := (mem_of_mem_functions hgFun hxy'G).1
          have : x ∈ X ∩ Y := mem_inter_iff.mpr ⟨hxX, hxY'⟩
          simp [hXY] at this
      · rcases exists_unique_of_mem_function hgFun x hxY with ⟨y, hxyG, huniqG⟩
        refine ⟨y, mem_union_iff.mpr (Or.inr hxyG), ?_⟩
        intro y' hxy'
        rcases mem_union_iff.mp hxy' with (hxy'F | hxy'G)
        · have hxX' : x ∈ X := (mem_of_mem_functions hfFun hxy'F).1
          have : x ∈ X ∩ Y := mem_inter_iff.mpr ⟨hxX', hxY⟩
          simp [hXY] at this
        · exact huniqG y' hxy'G
  have hfgInj : Injective (f ∪ g) := by
    intro x₁ x₂ y hx₁y hx₂y
    rcases mem_union_iff.mp hx₁y with (hx₁yF | hx₁yG)
    · rcases mem_union_iff.mp hx₂y with (hx₂yF | hx₂yG)
      · exact hf.2.1 _ _ _ hx₁yF hx₂yF
      · have hyX' : y ∈ X' := (mem_of_mem_functions hfFun hx₁yF).2
        have hyY' : y ∈ Y' := (mem_of_mem_functions hgFun hx₂yG).2
        have : y ∈ X' ∩ Y' := mem_inter_iff.mpr ⟨hyX', hyY'⟩
        simp [hX'Y'] at this
    · rcases mem_union_iff.mp hx₂y with (hx₂yF | hx₂yG)
      · have hyY' : y ∈ Y' := (mem_of_mem_functions hgFun hx₁yG).2
        have hyX' : y ∈ X' := (mem_of_mem_functions hfFun hx₂yF).2
        have : y ∈ X' ∩ Y' := mem_inter_iff.mpr ⟨hyX', hyY'⟩
        simp [hX'Y'] at this
      · exact hg.2.1 _ _ _ hx₁yG hx₂yG
  have hfgRange : range (f ∪ g) = orderedUnionCarrier X' Y' := by
    apply subset_antisymm
    · intro y hyR
      rcases mem_range_iff.mp hyR with ⟨x, hxy⟩
      rcases mem_union_iff.mp hxy with (hxyF | hxyG)
      · exact mem_orderedUnionCarrier_iff.mpr (Or.inl (mem_of_mem_functions hfFun hxyF).2)
      · exact mem_orderedUnionCarrier_iff.mpr (Or.inr (mem_of_mem_functions hgFun hxyG).2)
    · intro y hyU
      rcases mem_orderedUnionCarrier_iff.mp hyU with (hyX' | hyY')
      · have hyRf : y ∈ range f := by simpa [hf.2.2.1] using hyX'
        rcases mem_range_iff.mp hyRf with ⟨x, hxyF⟩
        exact mem_range_iff.mpr ⟨x, mem_union_iff.mpr (Or.inl hxyF)⟩
      · have hyRg : y ∈ range g := by simpa [hg.2.2.1] using hyY'
        rcases mem_range_iff.mp hyRg with ⟨x, hxyG⟩
        exact mem_range_iff.mpr ⟨x, mem_union_iff.mpr (Or.inr hxyG)⟩
  have hvalX : ∀ x ∈ X, (f ∪ g) ‘ x = f ‘ x := by
    intro x hxX
    rcases exists_of_mem_function hfFun x hxX with ⟨y, -, hxyF⟩
    have hvalU : (f ∪ g) ‘ x = y := value_eq_of_kpair_mem hfgFun (mem_union_iff.mpr (Or.inl hxyF))
    have hvalF : f ‘ x = y := value_eq_of_kpair_mem hfFun hxyF
    exact hvalU.trans hvalF.symm
  have hvalY : ∀ y ∈ Y, (f ∪ g) ‘ y = g ‘ y := by
    intro y hyY
    rcases exists_of_mem_function hgFun y hyY with ⟨z, -, hyzG⟩
    have hvalU : (f ∪ g) ‘ y = z := value_eq_of_kpair_mem hfgFun (mem_union_iff.mpr (Or.inr hyzG))
    have hvalG : g ‘ y = z := value_eq_of_kpair_mem hgFun hyzG
    exact hvalU.trans hvalG.symm
  have hmapX : ∀ x ∈ X, (f ∪ g) ‘ x ∈ X' := by
    intro x hxX
    rcases exists_of_mem_function hfFun x hxX with ⟨y, hyX', hxyF⟩
    have hvalU : (f ∪ g) ‘ x = y := value_eq_of_kpair_mem hfgFun (mem_union_iff.mpr (Or.inl hxyF))
    simpa [hvalU] using hyX'
  have hmapY : ∀ y ∈ Y, (f ∪ g) ‘ y ∈ Y' := by
    intro y hyY
    rcases exists_of_mem_function hgFun y hyY with ⟨z, hzY', hyzG⟩
    have hvalU : (f ∪ g) ‘ y = z := value_eq_of_kpair_mem hfgFun (mem_union_iff.mpr (Or.inr hyzG))
    simpa [hvalU] using hzY'
  have hpreX : ∀ x, x ∈ orderedUnionCarrier X Y → (f ∪ g) ‘ x ∈ X' → x ∈ X := by
    intro x hxU hxImgX'
    rcases mem_orderedUnionCarrier_iff.mp hxU with (hxX | hxY)
    · exact hxX
    · have hxImgY' : (f ∪ g) ‘ x ∈ Y' := hmapY x hxY
      have : (f ∪ g) ‘ x ∈ X' ∩ Y' := mem_inter_iff.mpr ⟨hxImgX', hxImgY'⟩
      simp [hX'Y'] at this
  have hpreY : ∀ x, x ∈ orderedUnionCarrier X Y → (f ∪ g) ‘ x ∈ Y' → x ∈ Y := by
    intro x hxU hxImgY'
    rcases mem_orderedUnionCarrier_iff.mp hxU with (hxX | hxY)
    · have hxImgX' : (f ∪ g) ‘ x ∈ X' := hmapX x hxX
      have : (f ∪ g) ‘ x ∈ X' ∩ Y' := mem_inter_iff.mpr ⟨hxImgX', hxImgY'⟩
      simp [hX'Y'] at this
    · exact hxY
  refine ⟨hfgFun, hfgInj, hfgRange, ?_⟩
  intro x₁ hx₁U x₂ hx₂U
  constructor
  · intro hrel
    rcases kpair_mem_orderedUnionRel_iff.mp hrel with ⟨_, _, hcases⟩
    rcases hcases with (hXX | hXY' | hYY)
    · rcases hXX with ⟨hx₁X, hx₂X, hR⟩
      have hx₁R : ⟨f ‘ x₁, f ‘ x₂⟩ₖ ∈ R' := (hf.2.2.2 x₁ hx₁X x₂ hx₂X).mp hR
      have hval₁ : (f ∪ g) ‘ x₁ = f ‘ x₁ := hvalX x₁ hx₁X
      have hval₂ : (f ∪ g) ‘ x₂ = f ‘ x₂ := hvalX x₂ hx₂X
      refine kpair_mem_orderedUnionRel_iff.mpr ?_
      refine ⟨?_, ?_, Or.inl ?_⟩
      · exact mem_orderedUnionCarrier_iff.mpr (Or.inl (hmapX x₁ hx₁X))
      · exact mem_orderedUnionCarrier_iff.mpr (Or.inl (hmapX x₂ hx₂X))
      · exact ⟨hmapX x₁ hx₁X, hmapX x₂ hx₂X, by simpa [hval₁, hval₂] using hx₁R⟩
    · rcases hXY' with ⟨hx₁X, hx₂Y⟩
      refine kpair_mem_orderedUnionRel_iff.mpr ?_
      refine ⟨?_, ?_, Or.inr (Or.inl ?_)⟩
      · exact mem_orderedUnionCarrier_iff.mpr (Or.inl (hmapX x₁ hx₁X))
      · exact mem_orderedUnionCarrier_iff.mpr (Or.inr (hmapY x₂ hx₂Y))
      · exact ⟨hmapX x₁ hx₁X, hmapY x₂ hx₂Y⟩
    · rcases hYY with ⟨hx₁Y, hx₂Y, hS⟩
      have hx₁S : ⟨g ‘ x₁, g ‘ x₂⟩ₖ ∈ S' := (hg.2.2.2 x₁ hx₁Y x₂ hx₂Y).mp hS
      have hval₁ : (f ∪ g) ‘ x₁ = g ‘ x₁ := hvalY x₁ hx₁Y
      have hval₂ : (f ∪ g) ‘ x₂ = g ‘ x₂ := hvalY x₂ hx₂Y
      refine kpair_mem_orderedUnionRel_iff.mpr ?_
      refine ⟨?_, ?_, Or.inr (Or.inr ?_)⟩
      · exact mem_orderedUnionCarrier_iff.mpr (Or.inr (hmapY x₁ hx₁Y))
      · exact mem_orderedUnionCarrier_iff.mpr (Or.inr (hmapY x₂ hx₂Y))
      · exact ⟨hmapY x₁ hx₁Y, hmapY x₂ hx₂Y, by simpa [hval₁, hval₂] using hx₁S⟩
  · intro hrel
    rcases kpair_mem_orderedUnionRel_iff.mp hrel with ⟨_, _, hcases⟩
    rcases hcases with (hXX | hXY' | hYY)
    · rcases hXX with ⟨hx₁X', hx₂X', hR'⟩
      have hx₁X : x₁ ∈ X := hpreX x₁ hx₁U hx₁X'
      have hx₂X : x₂ ∈ X := hpreX x₂ hx₂U hx₂X'
      have hval₁ : (f ∪ g) ‘ x₁ = f ‘ x₁ := hvalX x₁ hx₁X
      have hval₂ : (f ∪ g) ‘ x₂ = f ‘ x₂ := hvalX x₂ hx₂X
      have hR : ⟨x₁, x₂⟩ₖ ∈ R := (hf.2.2.2 x₁ hx₁X x₂ hx₂X).mpr (by simpa [hval₁, hval₂] using hR')
      refine kpair_mem_orderedUnionRel_iff.mpr ?_
      refine ⟨hx₁U, hx₂U, Or.inl ⟨hx₁X, hx₂X, hR⟩⟩
    · rcases hXY' with ⟨hx₁X', hx₂Y'⟩
      have hx₁X : x₁ ∈ X := hpreX x₁ hx₁U hx₁X'
      have hx₂Y : x₂ ∈ Y := hpreY x₂ hx₂U hx₂Y'
      refine kpair_mem_orderedUnionRel_iff.mpr ?_
      refine ⟨hx₁U, hx₂U, Or.inr (Or.inl ⟨hx₁X, hx₂Y⟩)⟩
    · rcases hYY with ⟨hx₁Y', hx₂Y', hS'⟩
      have hx₁Y : x₁ ∈ Y := hpreY x₁ hx₁U hx₁Y'
      have hx₂Y : x₂ ∈ Y := hpreY x₂ hx₂U hx₂Y'
      have hval₁ : (f ∪ g) ‘ x₁ = g ‘ x₁ := hvalY x₁ hx₁Y
      have hval₂ : (f ∪ g) ‘ x₂ = g ‘ x₂ := hvalY x₂ hx₂Y
      have hS : ⟨x₁, x₂⟩ₖ ∈ S := (hg.2.2.2 x₁ hx₁Y x₂ hx₂Y).mpr (by simpa [hval₁, hval₂] using hS')
      refine kpair_mem_orderedUnionRel_iff.mpr ?_
      refine ⟨hx₁U, hx₂U, Or.inr (Or.inr ⟨hx₁Y, hx₂Y, hS⟩)⟩

lemma orderedUnionRel_iso_of_componentIsos
    {R X S Y R' X' S' Y' f g : V}
    (hXY : X ∩ Y = ∅)
    (hX'Y' : X' ∩ Y' = ∅)
    (hf : IsOrderIso R X R' X' f)
    (hg : IsOrderIso S Y S' Y' g) :
    ∃ h,
      IsOrderIso
        (orderedUnionRel R X S Y) (orderedUnionCarrier X Y)
        (orderedUnionRel R' X' S' Y') (orderedUnionCarrier X' Y')
        h := ⟨f ∪ g, orderedUnionRel_isOrderIso_of_componentIsos hXY hX'Y' hf hg⟩


/--
The original ordered set `(X, R)` is order-isomorphic to its tagged copy
`(X ×ˢ {i}, taggedRel R X i)`.
-/
lemma taggedRel_isOrderIso
    {R X i : V} :
    ∃ f, IsOrderIso R X (taggedRel R X i) (X ×ˢ {i}) f ∧
      ∀ x ∈ X, ∀ y, ⟨x, y⟩ₖ ∈ f ↔ y = tagProj i x := by
  have htagDef : ℒₛₑₜ-function₁[V] (fun x ↦ tagProj i x) := by
    letI : ℒₛₑₜ-function₂[V] tagProj := tagProj.definable
    change ℒₛₑₜ-function₁[V] (fun x ↦ tagProj i x)
    definability
  have htag : ∀ x ∈ X, tagProj i x ∈ X ×ˢ {i} := by
    intro x hxX
    simpa [tagProj, mem_prod_iff, kpair_mem_iff] using hxX
  rcases graph_exists_mem_function_of_definableFunction
      X (X ×ˢ {i}) (fun x ↦ tagProj i x) htagDef htag with
    ⟨f, hfFun, hgraph⟩
  refine ⟨f, ?_, hgraph⟩
  refine ⟨hfFun, ?_, ?_, ?_⟩
  · intro x₁ x₂ y hx₁y hx₂y
    have hx₁X : x₁ ∈ X := (mem_of_mem_functions hfFun hx₁y).1
    have hx₂X : x₂ ∈ X := (mem_of_mem_functions hfFun hx₂y).1
    have hy₁ : y = tagProj i x₁ := (hgraph x₁ hx₁X y).1 hx₁y
    have hy₂ : y = tagProj i x₂ := (hgraph x₂ hx₂X y).1 hx₂y
    have hEq : tagProj i x₁ = tagProj i x₂ := hy₁.symm.trans hy₂
    simpa [tagProj] using (kpair_inj hEq).1
  · apply subset_antisymm
    · exact range_subset_of_mem_function hfFun
    · intro y hy
      rcases show ∃ x ∈ X, y = tagProj i x from by
          simpa [tagProj, mem_prod_iff, kpair_mem_iff] using hy with
        ⟨x, hxX, rfl⟩
      exact mem_range_iff.mpr ⟨x, (hgraph x hxX _).2 rfl⟩
  · intro x₁ hx₁ x₂ hx₂
    have hx₁f : ⟨x₁, tagProj i x₁⟩ₖ ∈ f := (hgraph x₁ hx₁ _).2 rfl
    have hx₂f : ⟨x₂, tagProj i x₂⟩ₖ ∈ f := (hgraph x₂ hx₂ _).2 rfl
    have hval₁ : f ‘ x₁ = tagProj i x₁ := value_eq_of_kpair_mem hfFun hx₁f
    have hval₂ : f ‘ x₂ = tagProj i x₂ := value_eq_of_kpair_mem hfFun hx₂f
    constructor
    · intro hR
      have htagged : ⟨tagProj i x₁, tagProj i x₂⟩ₖ ∈ taggedRel R X i :=
        kpair_mem_taggedRel_iff.mpr ⟨hx₁, hx₂, hR⟩
      simpa [hval₁, hval₂] using htagged
    · intro htagged
      have : ⟨tagProj i x₁, tagProj i x₂⟩ₖ ∈ taggedRel R X i := by
        simpa [hval₁, hval₂] using htagged
      exact (kpair_mem_taggedRel_iff.mp this).2.2

namespace IsOrderIso

lemma mem_function {R X S Y f : V} (h : IsOrderIso R X S Y f) : f ∈ Y ^ X := h.1

lemma injective {R X S Y f : V} (h : IsOrderIso R X S Y f) : Injective f := h.2.1

lemma range_eq {R X S Y f : V} (h : IsOrderIso R X S Y f) : range f = Y := h.2.2.1

lemma domain_eq {R X S Y f : V} (h : IsOrderIso R X S Y f) : domain f = X :=
  domain_eq_of_mem_function h.mem_function

lemma rel_iff {R X S Y f x₁ x₂ : V} (h : IsOrderIso R X S Y f) (hx₁ : x₁ ∈ X) (hx₂ : x₂ ∈ X) :
    ⟨x₁, x₂⟩ₖ ∈ R ↔ ⟨f ‘ x₁, f ‘ x₂⟩ₖ ∈ S := h.2.2.2 x₁ hx₁ x₂ hx₂

lemma rel_of_pairs {R X S Y f x₁ x₂ y₁ y₂ : V} (h : IsOrderIso R X S Y f)
    (hx₁ : x₁ ∈ X) (hx₂ : x₂ ∈ X) (hxy₁ : ⟨x₁, y₁⟩ₖ ∈ f) (hxy₂ : ⟨x₂, y₂⟩ₖ ∈ f) :
    ⟨x₁, x₂⟩ₖ ∈ R ↔ ⟨y₁, y₂⟩ₖ ∈ S := by
  have hy₁ : f ‘ x₁ = y₁ := value_eq_of_kpair_mem h.mem_function hxy₁
  have hy₂ : f ‘ x₂ = y₂ := value_eq_of_kpair_mem h.mem_function hxy₂
  rw [h.rel_iff hx₁ hx₂, hy₁, hy₂]

lemma comp {R X S Y T Z f g : V}
    (hf : IsOrderIso R X S Y f) (hg : IsOrderIso S Y T Z g) :
    IsOrderIso R X T Z (compose f g) := by
  have hfgFun : compose f g ∈ Z ^ X := compose_function hf.mem_function hg.mem_function
  have hfgInj : Injective (compose f g) := compose_injective hf.injective hg.injective
  have hfgRange : range (compose f g) = Z := by
    apply subset_antisymm
    · exact range_subset_of_mem_function hfgFun
    · intro z hzZ
      have hzRg : z ∈ range g := by simpa [hg.range_eq] using hzZ
      rcases mem_range_iff.mp hzRg with ⟨y, hyz⟩
      have hyY : y ∈ Y := (mem_of_mem_functions hg.mem_function hyz).1
      have hyRf : y ∈ range f := by simpa [hf.range_eq] using hyY
      rcases mem_range_iff.mp hyRf with ⟨x, hxy⟩
      exact mem_range_iff.mpr ⟨x, kpair_mem_compose_iff.mpr ⟨y, hxy, hyz⟩⟩
  have hfgRel :
      ∀ x₁ ∈ X, ∀ x₂ ∈ X,
        ⟨x₁, x₂⟩ₖ ∈ R ↔ ⟨(compose f g) ‘ x₁, (compose f g) ‘ x₂⟩ₖ ∈ T := by
    intro x₁ hx₁X x₂ hx₂X
    rcases exists_of_mem_function hf.mem_function x₁ hx₁X with ⟨y₁, hy₁Y, hxy₁⟩
    rcases exists_of_mem_function hf.mem_function x₂ hx₂X with ⟨y₂, hy₂Y, hxy₂⟩
    have hy₁ : f ‘ x₁ = y₁ := value_eq_of_kpair_mem hf.mem_function hxy₁
    have hy₂ : f ‘ x₂ = y₂ := value_eq_of_kpair_mem hf.mem_function hxy₂
    have hz₁ : (compose f g) ‘ x₁ = g ‘ y₁ := by
      simpa [hy₁] using value_compose_eq hf.mem_function hg.mem_function hx₁X
    have hz₂ : (compose f g) ‘ x₂ = g ‘ y₂ := by
      simpa [hy₂] using value_compose_eq hf.mem_function hg.mem_function hx₂X
    have hRS : ⟨x₁, x₂⟩ₖ ∈ R ↔ ⟨y₁, y₂⟩ₖ ∈ S :=
      hf.rel_of_pairs hx₁X hx₂X hxy₁ hxy₂
    have hST : ⟨y₁, y₂⟩ₖ ∈ S ↔ ⟨g ‘ y₁, g ‘ y₂⟩ₖ ∈ T :=
      hg.rel_iff hy₁Y hy₂Y
    exact hRS.trans <| by simpa [hz₁, hz₂] using hST
  exact ⟨hfgFun, hfgInj, hfgRange, hfgRel⟩

lemma restrict_initialSegment
    {R X S Y f x y : V}
    (h : IsOrderIso R X S Y f)
    (hx : x ∈ X)
    (hxy : ⟨x, y⟩ₖ ∈ f) :
    IsOrderIso R (initialSegment R X x) S (initialSegment S Y y) (f ↾ (initialSegment R X x)) := by
  have hfun : f ∈ Y ^ X := h.mem_function
  have hres_fun : f ↾ (initialSegment R X x) ∈ initialSegment S Y y ^ initialSegment R X x := by
    apply mem_function.intro
    · intro p hp
      rcases mem_restrict_iff.mp hp with ⟨hpf, u, huI, v, rfl⟩
      have huX : u ∈ X := (mem_initialSegment_iff.mp huI).1
      have huxR : ⟨u, x⟩ₖ ∈ R := (mem_initialSegment_iff.mp huI).2
      have hvY : v ∈ Y := (mem_of_mem_functions hfun hpf).2
      have hvyS : ⟨v, y⟩ₖ ∈ S := (h.rel_of_pairs huX hx hpf hxy).1 huxR
      have hvI : v ∈ initialSegment S Y y := mem_initialSegment_iff.mpr ⟨hvY, hvyS⟩
      simpa [mem_prod_iff] using And.intro huI hvI
    · intro u huI
      have huX : u ∈ X := (mem_initialSegment_iff.mp huI).1
      have huxR : ⟨u, x⟩ₖ ∈ R := (mem_initialSegment_iff.mp huI).2
      rcases exists_unique_of_mem_function hfun u huX with ⟨v, huvf, huvuniq⟩
      have hvY : v ∈ Y := (mem_of_mem_functions hfun huvf).2
      have hvyS : ⟨v, y⟩ₖ ∈ S := (h.rel_of_pairs huX hx huvf hxy).1 huxR
      refine ExistsUnique.intro v ?_ ?_
      · exact kpair_mem_restrict_iff.mpr ⟨huvf, huI⟩
      · intro w huwres
        have huw : ⟨u, w⟩ₖ ∈ f := (kpair_mem_restrict_iff.mp huwres).1
        exact huvuniq w huw
  have hres_inj : Injective (f ↾ (initialSegment R X x)) := by
    intro u₁ u₂ v hu₁ hu₂
    have hu₁f : ⟨u₁, v⟩ₖ ∈ f := (kpair_mem_restrict_iff.mp hu₁).1
    have hu₂f : ⟨u₂, v⟩ₖ ∈ f := (kpair_mem_restrict_iff.mp hu₂).1
    exact h.injective _ _ _ hu₁f hu₂f
  have hres_range : range (f ↾ (initialSegment R X x)) = initialSegment S Y y := by
    apply subset_antisymm
    · intro v hv
      rcases mem_range_iff.mp hv with ⟨u, huvres⟩
      have huvf : ⟨u, v⟩ₖ ∈ f := (kpair_mem_restrict_iff.mp huvres).1
      have huI : u ∈ initialSegment R X x := (kpair_mem_restrict_iff.mp huvres).2
      have huX : u ∈ X := (mem_initialSegment_iff.mp huI).1
      have huxR : ⟨u, x⟩ₖ ∈ R := (mem_initialSegment_iff.mp huI).2
      have hvY : v ∈ Y := (mem_of_mem_functions hfun huvf).2
      have hvyS : ⟨v, y⟩ₖ ∈ S := (h.rel_of_pairs huX hx huvf hxy).1 huxR
      exact mem_initialSegment_iff.mpr ⟨hvY, hvyS⟩
    · intro v hvI
      have hvY : v ∈ Y := (mem_initialSegment_iff.mp hvI).1
      have hvyS : ⟨v, y⟩ₖ ∈ S := (mem_initialSegment_iff.mp hvI).2
      have hvRangeF : v ∈ range f := by rw [h.range_eq]; exact hvY
      rcases mem_range_iff.mp hvRangeF with ⟨u, huvf⟩
      have huX : u ∈ X := (mem_of_mem_functions hfun huvf).1
      have huxR : ⟨u, x⟩ₖ ∈ R := (h.rel_of_pairs huX hx huvf hxy).2 hvyS
      have huI : u ∈ initialSegment R X x := mem_initialSegment_iff.mpr ⟨huX, huxR⟩
      exact mem_range_iff.mpr ⟨u, kpair_mem_restrict_iff.mpr ⟨huvf, huI⟩⟩
  have hres_rel :
      ∀ u₁ ∈ initialSegment R X x, ∀ u₂ ∈ initialSegment R X x,
        ⟨u₁, u₂⟩ₖ ∈ R ↔ ⟨(f ↾ (initialSegment R X x)) ‘ u₁, (f ↾ (initialSegment R X x)) ‘ u₂⟩ₖ ∈ S := by
    intro u₁ hu₁I u₂ hu₂I
    have hu₁X : u₁ ∈ X := (mem_initialSegment_iff.mp hu₁I).1
    have hu₂X : u₂ ∈ X := (mem_initialSegment_iff.mp hu₂I).1
    rcases exists_of_mem_function hres_fun u₁ hu₁I with ⟨v₁, hv₁I, hu₁v₁res⟩
    rcases exists_of_mem_function hres_fun u₂ hu₂I with ⟨v₂, hv₂I, hu₂v₂res⟩
    have hu₁v₁f : ⟨u₁, v₁⟩ₖ ∈ f := (kpair_mem_restrict_iff.mp hu₁v₁res).1
    have hu₂v₂f : ⟨u₂, v₂⟩ₖ ∈ f := (kpair_mem_restrict_iff.mp hu₂v₂res).1
    have hv₁eq : (f ↾ (initialSegment R X x)) ‘ u₁ = v₁ := value_eq_of_kpair_mem hres_fun hu₁v₁res
    have hv₂eq : (f ↾ (initialSegment R X x)) ‘ u₂ = v₂ := value_eq_of_kpair_mem hres_fun hu₂v₂res
    have hpair : ⟨u₁, u₂⟩ₖ ∈ R ↔ ⟨v₁, v₂⟩ₖ ∈ S := h.rel_of_pairs hu₁X hu₂X hu₁v₁f hu₂v₂f
    simpa [hv₁eq, hv₂eq] using hpair
  exact ⟨hres_fun, hres_inj, hres_range, hres_rel⟩

lemma inv {R X S Y f : V} (h : IsOrderIso R X S Y f) :
    IsOrderIso S Y R X (inverse f) := by
  have hInvRange : inverse f ∈ X ^ range f :=
    inverse_mem_function_of_mem_function_of_injective h.mem_function h.injective
  have hInvMem : inverse f ∈ X ^ Y := by simpa [h.range_eq] using hInvRange
  have hInvInj : Injective (inverse f) := inverse_injective_of_mem_function h.mem_function
  have hInvRangeEq : range (inverse f) = X := by simp [h.domain_eq]
  have hInvRel :
      ∀ y₁ ∈ Y, ∀ y₂ ∈ Y,
        ⟨y₁, y₂⟩ₖ ∈ S ↔ ⟨(inverse f) ‘ y₁, (inverse f) ‘ y₂⟩ₖ ∈ R := by
    intro y₁ hy₁Y y₂ hy₂Y
    rcases exists_of_mem_function hInvMem y₁ hy₁Y with ⟨x₁, hx₁X, hy₁x₁⟩
    rcases exists_of_mem_function hInvMem y₂ hy₂Y with ⟨x₂, hx₂X, hy₂x₂⟩
    have hx₁y₁ : ⟨x₁, y₁⟩ₖ ∈ f := kpair_mem_inverse_iff.mp hy₁x₁
    have hx₂y₂ : ⟨x₂, y₂⟩ₖ ∈ f := kpair_mem_inverse_iff.mp hy₂x₂
    have hy₁val : (inverse f) ‘ y₁ = x₁ := value_eq_of_kpair_mem hInvMem hy₁x₁
    have hy₂val : (inverse f) ‘ y₂ = x₂ := value_eq_of_kpair_mem hInvMem hy₂x₂
    have hrel : ⟨x₁, x₂⟩ₖ ∈ R ↔ ⟨y₁, y₂⟩ₖ ∈ S :=
      h.rel_of_pairs hx₁X hx₂X hx₁y₁ hx₂y₂
    simpa [hy₁val, hy₂val] using hrel.symm
  exact ⟨hInvMem, hInvInj, hInvRangeEq, hInvRel⟩

lemma symm {R X S Y f : V} (h : IsOrderIso R X S Y f) :
    ∃ g, IsOrderIso S Y R X g := ⟨inverse f, h.inv⟩

end IsOrderIso

/--
For disjoint `X, Y`, tagged ordered sum is order-isomorphic to the plain-union ordered sum.
-/
lemma orderSumProjection_isOrderIso
    {R X S Y : V}
    (hXY : X ∩ Y = ∅) :
    IsOrderIso
      (orderSumRel R X S Y) (orderSumCarrier X Y)
      (orderedUnionRel R X S Y) (orderedUnionCarrier X Y)
      (orderSumProjection X Y) := by
  rcases taggedRel_isOrderIso (R := R) (X := X) (i := (0 : V)) with ⟨f, hf, hfGraph⟩
  rcases taggedRel_isOrderIso (R := S) (X := Y) (i := (1 : V)) with ⟨g, hg, hgGraph⟩
  have hTaggedDisj : (X ×ˢ {0}) ∩ (Y ×ˢ {1}) = ∅ := by
    rw [← isEmpty_iff_eq_empty]
    intro p hp
    rcases mem_inter_iff.mp hp with ⟨hpX, hpY⟩
    rcases show ∃ x ∈ X, ∃ i ∈ ({0} : V), p = ⟨x, i⟩ₖ from by
        simpa [mem_prod_iff] using hpX with
      ⟨x, hxX, i, hi0, hpXi⟩
    rcases show ∃ y ∈ Y, ∃ j ∈ ({1} : V), p = ⟨y, j⟩ₖ from by
        simpa [mem_prod_iff] using hpY with
      ⟨y, hyY, j, hj1, hpYj⟩
    have hi : i = 0 := by simpa using hi0
    have hj : j = 1 := by simpa using hj1
    subst hi
    subst hj
    exact zero_ne_one ((kpair_inj (hpXi.symm.trans hpYj)).2)
  have hIsoUnion :
      IsOrderIso
        (orderSumRel R X S Y) (orderSumCarrier X Y)
        (orderedUnionRel R X S Y) (orderedUnionCarrier X Y)
        (inverse f ∪ inverse g) := by
    simpa [orderSumRel, orderSumCarrier] using
      orderedUnionRel_isOrderIso_of_componentIsos
        (R := taggedRel R X 0) (X := X ×ˢ {0}) (S := taggedRel S Y 1) (Y := Y ×ˢ {1})
        (R' := R) (X' := X) (S' := S) (Y' := Y)
        (f := inverse f) (g := inverse g)
        hTaggedDisj hXY hf.inv hg.inv
  have hProjEq : inverse f ∪ inverse g = orderSumProjection X Y := by
    ext p
    constructor
    · intro hp
      rcases mem_union_iff.mp hp with (hpF | hpG)
      · rcases mem_inverse_iff.mp hpF with ⟨x, y, hxy, rfl⟩
        have hxX : x ∈ X := (mem_of_mem_functions hf.mem_function hxy).1
        have hy : y = tagProj 0 x := (hfGraph x hxX y).1 hxy
        subst hy
        refine mem_sep_iff.mpr ?_
        refine ⟨?_, x, Or.inl ⟨hxX, rfl⟩⟩
        have htag : tagProj 0 x ∈ orderSumCarrier X Y := by
          simp [tagProj, mem_orderSumCarrier_iff, hxX]
        have hxU : x ∈ orderedUnionCarrier X Y := by
          simp [orderedUnionCarrier, hxX]
        simpa [mem_prod_iff] using And.intro htag hxU
      · rcases mem_inverse_iff.mp hpG with ⟨y, z, hyz, rfl⟩
        have hzY : y ∈ Y := (mem_of_mem_functions hg.mem_function hyz).1
        have hz : z = tagProj 1 y := (hgGraph y hzY z).1 hyz
        subst hz
        refine mem_sep_iff.mpr ?_
        refine ⟨?_, y, Or.inr ⟨hzY, rfl⟩⟩
        have htag : tagProj 1 y ∈ orderSumCarrier X Y := by
          simp [tagProj, mem_orderSumCarrier_iff, hzY]
        have hyU : y ∈ orderedUnionCarrier X Y := by
          simp [orderedUnionCarrier, hzY]
        simpa [mem_prod_iff] using And.intro htag hyU
    · intro hp
      rcases mem_sep_iff.mp hp with ⟨-, z, hpz⟩
      rcases hpz with (⟨hzX, rfl⟩ | ⟨hzY, rfl⟩)
      · exact mem_union_iff.mpr <| Or.inl <| kpair_mem_inverse_iff.mpr <|
          (hfGraph z hzX (tagProj 0 z)).2 rfl
      · exact mem_union_iff.mpr <| Or.inr <| kpair_mem_inverse_iff.mpr <|
          (hgGraph z hzY (tagProj 1 z)).2 rfl
  simpa [hProjEq] using hIsoUnion

/-- Initial segments by `a` and `b` are order-isomorphic. -/
def InitSegIso (R X S Y a b : V) : Prop :=
  ∃ f, IsOrderIso R (initialSegment R X a) S (initialSegment S Y b) f

lemma initSegIso_definable (R X S Y : V) : ℒₛₑₜ-relation[V] (InitSegIso R X S Y) := by
  letI : ℒₛₑₜ-relation₅[V] IsOrderIso := isOrderIso_definable
  letI : ℒₛₑₜ-function₃[V] initialSegment := initialSegment.definable
  unfold InitSegIso
  definability

instance InitSegIso.definable (R X S Y : V) : ℒₛₑₜ-relation[V] (InitSegIso R X S Y) :=
  initSegIso_definable R X S Y

/--
Relation on `X ×ˢ Y`: `a` and `b` are related when their initial segments
are order-isomorphic.
-/
noncomputable def initSegIsoRel (R X S Y : V) : V :=
  {p ∈ X ×ˢ Y ; ∃ a ∈ X, ∃ b ∈ Y, p = ⟨a, b⟩ₖ ∧ InitSegIso R X S Y a b}

lemma mem_initSegIsoRel_iff {R X S Y p : V} :
    p ∈ initSegIsoRel R X S Y ↔
      p ∈ X ×ˢ Y ∧ ∃ a ∈ X, ∃ b ∈ Y, p = ⟨a, b⟩ₖ ∧ InitSegIso R X S Y a b := by
  simp [initSegIsoRel]

@[simp] lemma kpair_mem_initSegIsoRel_iff {R X S Y a b : V} :
    ⟨a, b⟩ₖ ∈ initSegIsoRel R X S Y ↔
      a ∈ X ∧ b ∈ Y ∧ InitSegIso R X S Y a b := by
  constructor
  · intro h
    rcases (mem_initSegIsoRel_iff.mp h) with ⟨hprod, a', ha'X, b', hb'Y, hp, hiso⟩
    rcases kpair_inj hp with ⟨rfl, rfl⟩
    have : a ∈ X ∧ b ∈ Y := by simpa [mem_prod_iff] using hprod
    exact ⟨this.1, this.2, hiso⟩
  · rintro ⟨haX, hbY, hiso⟩
    refine mem_initSegIsoRel_iff.mpr ?_
    refine ⟨?_, a, haX, b, hbY, rfl, hiso⟩
    simpa [mem_prod_iff] using And.intro haX hbY

lemma IsOrderIso.unique_of_wellOrder
    {R X S Y f g : V}
    (hRwo : IsWellOrderOn R X)
    (hSlin : IsStrictLinearOrderOn S Y)
    (hf : IsOrderIso R X S Y f)
    (hg : IsOrderIso R X S Y g) : f = g := by
  by_contra hfg
  let A : V := {x ∈ X ; ∃ y₁ y₂, ⟨x, y₁⟩ₖ ∈ f ∧ ⟨x, y₂⟩ₖ ∈ g ∧ y₁ ≠ y₂}
  have hA_sub : A ⊆ X := sep_subset
  have hA_nonempty : IsNonempty A := by
    have hneqMem : ∃ p, (p ∈ f ∧ p ∉ g) ∨ (p ∈ g ∧ p ∉ f) := by
      by_contra h
      apply hfg
      ext p
      constructor
      · intro hp
        by_contra hpg
        exact h ⟨p, Or.inl ⟨hp, hpg⟩⟩
      · intro hp
        by_contra hpf
        exact h ⟨p, Or.inr ⟨hp, hpf⟩⟩
    rcases hneqMem with ⟨p, hp | hp⟩
    · rcases hp with ⟨hpf, hpng⟩
      rcases show ∃ x ∈ X, ∃ y ∈ Y, p = ⟨x, y⟩ₖ from by
          simpa [mem_prod_iff] using subset_prod_of_mem_function hf.mem_function p hpf with
        ⟨x, hxX, y₁, hy₁Y, rfl⟩
      rcases exists_of_mem_function hg.mem_function x hxX with ⟨y₂, hy₂Y, hxy₂g⟩
      have hyne : y₁ ≠ y₂ := by
        intro hEq
        apply hpng
        simpa [hEq] using hxy₂g
      exact ⟨x, mem_sep_iff.mpr ⟨hxX, y₁, y₂, hpf, hxy₂g, hyne⟩⟩
    · rcases hp with ⟨hpg, hpnf⟩
      rcases show ∃ x ∈ X, ∃ y ∈ Y, p = ⟨x, y⟩ₖ from by
          simpa [mem_prod_iff] using subset_prod_of_mem_function hg.mem_function p hpg with
        ⟨x, hxX, y₂, hy₂Y, rfl⟩
      rcases exists_of_mem_function hf.mem_function x hxX with ⟨y₁, hy₁Y, hxy₁f⟩
      have hyne : y₁ ≠ y₂ := by
        intro hEq
        apply hpnf
        simpa [hEq] using hxy₁f
      exact ⟨x, mem_sep_iff.mpr ⟨hxX, y₁, y₂, hxy₁f, hpg, hyne⟩⟩
  have hA_ne : A ≠ ∅ := by
    intro hA0
    rcases hA_nonempty with ⟨x, hxA⟩
    simp [hA0] at hxA
  rcases hRwo.2 A hA_sub hA_ne with ⟨m, hmA, hmLeast⟩
  rcases (show m ∈ X ∧ ∃ y₁ y₂, ⟨m, y₁⟩ₖ ∈ f ∧ ⟨m, y₂⟩ₖ ∈ g ∧ y₁ ≠ y₂ from mem_sep_iff.mp hmA) with
    ⟨hmX, y₁, y₂, hmy₁f, hmy₂g, hyne⟩
  have hy₁Y : y₁ ∈ Y := (mem_of_mem_functions hf.mem_function hmy₁f).2
  have hy₂Y : y₂ ∈ Y := (mem_of_mem_functions hg.mem_function hmy₂g).2
  rcases hSlin.trichotomy hy₁Y hy₂Y with (hy₁₂ | hEq | hy₂₁)
  · have hy₁R : y₁ ∈ range g := by
      rw [hg.range_eq]
      exact hy₁Y
    rcases mem_range_iff.mp hy₁R with ⟨u, huy₁g⟩
    have huX : u ∈ X := (mem_of_mem_functions hg.mem_function huy₁g).1
    have hu_lt_m : ⟨u, m⟩ₖ ∈ R := (hg.rel_of_pairs huX hmX huy₁g hmy₂g).2 hy₁₂
    rcases exists_of_mem_function hf.mem_function u huX with ⟨z, hzY, huzf⟩
    have hz_ne_y₁ : z ≠ y₁ := by
      intro hzEq
      have hu_eq_m : u = m := hf.injective _ _ _ (by rw [hzEq] at huzf; exact huzf) hmy₁f
      subst hu_eq_m
      have hg_func : IsFunction g := IsFunction.of_mem hg.mem_function
      have : y₁ = y₂ := hg_func.unique huy₁g hmy₂g
      exact hyne this
    have huA : u ∈ A := by
      exact mem_sep_iff.mpr ⟨huX, z, y₁, huzf, huy₁g, hz_ne_y₁⟩
    have hleast_u : u = m ∨ ⟨m, u⟩ₖ ∈ R := hmLeast u huA
    rcases hleast_u with (hu_eq_m | hm_lt_u)
    · exact hRwo.1.irrefl hmX (by simpa [hu_eq_m] using hu_lt_m)
    · exact (hRwo.1.asymm hmX huX hm_lt_u hu_lt_m).elim
  · exact hyne hEq
  · have hy₂R : y₂ ∈ range f := by
      rw [hf.range_eq]
      exact hy₂Y
    rcases mem_range_iff.mp hy₂R with ⟨u, huy₂f⟩
    have huX : u ∈ X := (mem_of_mem_functions hf.mem_function huy₂f).1
    have hu_lt_m : ⟨u, m⟩ₖ ∈ R := (hf.rel_of_pairs huX hmX huy₂f hmy₁f).2 hy₂₁
    rcases exists_of_mem_function hg.mem_function u huX with ⟨z, hzY, huzg⟩
    have hz_ne_y₂ : z ≠ y₂ := by
      intro hzEq
      have hu_eq_m : u = m := hg.injective _ _ _ (by rw [hzEq] at huzg; exact huzg) hmy₂g
      subst hu_eq_m
      have hf_func : IsFunction f := IsFunction.of_mem hf.mem_function
      have : y₂ = y₁ := hf_func.unique huy₂f hmy₁f
      exact hyne this.symm
    have huA : u ∈ A := by
      exact mem_sep_iff.mpr ⟨huX, y₂, z, huy₂f, huzg, hz_ne_y₂.symm⟩
    have hleast_u : u = m ∨ ⟨m, u⟩ₖ ∈ R := hmLeast u huA
    rcases hleast_u with (hu_eq_m | hm_lt_u)
    · exact hRwo.1.irrefl hmX (by simpa [hu_eq_m] using hu_lt_m)
    · exact (hRwo.1.asymm hmX huX hm_lt_u hu_lt_m).elim

namespace InitSegIso

lemma witnesses_mem {R X S Y a b : V} (h : InitSegIso R X S Y a b) :
    ∃ f, f ∈ initialSegment S Y b ^ initialSegment R X a := by
  rcases h with ⟨f, hf⟩
  exact ⟨f, hf.1⟩

lemma witness_unique
    {R X S Y a b f g : V}
    (hRwo : IsWellOrderOn R (initialSegment R X a))
    (hSlin : IsStrictLinearOrderOn S (initialSegment S Y b))
    (hf : IsOrderIso R (initialSegment R X a) S (initialSegment S Y b) f)
    (hg : IsOrderIso R (initialSegment R X a) S (initialSegment S Y b) g) :
    f = g :=
  IsOrderIso.unique_of_wellOrder hRwo hSlin hf hg

lemma witness_value_coherent
    {R X S Y a b f g x y₁ y₂ : V}
    (hRwo : IsWellOrderOn R (initialSegment R X a))
    (hSlin : IsStrictLinearOrderOn S (initialSegment S Y b))
    (hf : IsOrderIso R (initialSegment R X a) S (initialSegment S Y b) f)
    (hg : IsOrderIso R (initialSegment R X a) S (initialSegment S Y b) g)
    (hxy₁ : ⟨x, y₁⟩ₖ ∈ f)
    (hxy₂ : ⟨x, y₂⟩ₖ ∈ g) :
    y₁ = y₂ := by
  have hfg : f = g := witness_unique hRwo hSlin hf hg
  subst hfg
  have : IsFunction f := IsFunction.of_mem hf.mem_function
  exact IsFunction.unique hxy₁ hxy₂

@[symm] lemma symm [V ⊧ₘ* 𝗭𝗙] {R X S Y a b : V} (h : InitSegIso R X S Y a b) :
    InitSegIso S Y R X b a := by
  rcases h with ⟨f, hf⟩
  rcases IsOrderIso.symm hf with ⟨g, hg⟩
  exact ⟨g, hg⟩

end InitSegIso

lemma initSegIsoRel_subset_prod (R X S Y : V) : initSegIsoRel R X S Y ⊆ X ×ˢ Y := by
  intro p hp
  exact (mem_initSegIsoRel_iff.mp hp).1

lemma domain_initSegIsoRel_subset (R X S Y : V) : domain (initSegIsoRel R X S Y) ⊆ X := by
  exact domain_subset_of_subset_prod (initSegIsoRel_subset_prod R X S Y)

lemma range_initSegIsoRel_subset (R X S Y : V) : range (initSegIsoRel R X S Y) ⊆ Y := by
  exact range_subset_of_subset_prod (initSegIsoRel_subset_prod R X S Y)

lemma mem_domain_initSegIsoRel_iff {R X S Y a : V} :
    a ∈ domain (initSegIsoRel R X S Y) ↔ a ∈ X ∧ ∃ b ∈ Y, InitSegIso R X S Y a b := by
  constructor
  · intro ha
    rcases mem_domain_iff.mp ha with ⟨b, hab⟩
    rcases (kpair_mem_initSegIsoRel_iff.mp hab) with ⟨haX, hbY, hiso⟩
    exact ⟨haX, b, hbY, hiso⟩
  · rintro ⟨haX, b, hbY, hiso⟩
    exact mem_domain_iff.mpr ⟨b, kpair_mem_initSegIsoRel_iff.mpr ⟨haX, hbY, hiso⟩⟩

@[simp] lemma kpair_mem_initSegIsoRel_swap_iff [V ⊧ₘ* 𝗭𝗙] {R X S Y a b : V} :
    ⟨a, b⟩ₖ ∈ initSegIsoRel R X S Y ↔ ⟨b, a⟩ₖ ∈ initSegIsoRel S Y R X := by
  constructor
  · intro hab
    rcases kpair_mem_initSegIsoRel_iff.mp hab with ⟨haX, hbY, habIso⟩
    exact kpair_mem_initSegIsoRel_iff.mpr ⟨hbY, haX, InitSegIso.symm habIso⟩
  · intro hba
    rcases kpair_mem_initSegIsoRel_iff.mp hba with ⟨hbY, haX, hbaIso⟩
    exact kpair_mem_initSegIsoRel_iff.mpr ⟨haX, hbY, InitSegIso.symm hbaIso⟩

lemma domain_initSegIsoRel_swap_eq_range [V ⊧ₘ* 𝗭𝗙] (R X S Y : V) :
    domain (initSegIsoRel S Y R X) = range (initSegIsoRel R X S Y) := by
  ext z
  constructor
  · intro hz
    rcases mem_domain_iff.mp hz with ⟨x, hzx⟩
    have hxz : ⟨x, z⟩ₖ ∈ initSegIsoRel R X S Y := (kpair_mem_initSegIsoRel_swap_iff.mp hzx)
    exact mem_range_iff.mpr ⟨x, hxz⟩
  · intro hz
    rcases mem_range_iff.mp hz with ⟨x, hxz⟩
    have hzx : ⟨z, x⟩ₖ ∈ initSegIsoRel S Y R X := (kpair_mem_initSegIsoRel_swap_iff.mp hxz)
    exact mem_domain_iff.mpr ⟨x, hzx⟩

lemma initialSegment_of_initialSegment_eq
    {R X a₁ a₂ : V}
    (hRlin : IsStrictLinearOrderOn R X)
    (ha₁X : a₁ ∈ X) (ha₂X : a₂ ∈ X)
    (ha₁a₂ : ⟨a₁, a₂⟩ₖ ∈ R) :
    initialSegment R (initialSegment R X a₂) a₁ = initialSegment R X a₁ := by
  ext x
  simp only [mem_initialSegment_iff]
  constructor
  · rintro ⟨⟨hxX, _⟩, hxa₁⟩
    exact ⟨hxX, hxa₁⟩
  · rintro ⟨hxX, hxa₁⟩
    exact ⟨⟨hxX, hRlin.trans hxX ha₁X ha₂X hxa₁ ha₁a₂⟩, hxa₁⟩

lemma initialSegment_of_initialSegment_eq'
    {S Y b₁ b₂ : V}
    (hSlin : IsStrictLinearOrderOn S Y)
    (hb₁Y : b₁ ∈ Y) (hb₂Y : b₂ ∈ Y)
    (hb₁b₂ : ⟨b₁, b₂⟩ₖ ∈ S) :
    initialSegment S (initialSegment S Y b₂) b₁ = initialSegment S Y b₁ :=
  initialSegment_of_initialSegment_eq hSlin hb₁Y hb₂Y hb₁b₂

lemma initSegIsoRel_exists_lt_of_lt
    {R X S Y a₁ a₂ b₂ : V}
    (hRlin : IsStrictLinearOrderOn R X)
    (hSlin : IsStrictLinearOrderOn S Y)
    (ha₁a₂ : ⟨a₁, a₂⟩ₖ ∈ R)
    (ha₂b₂ : ⟨a₂, b₂⟩ₖ ∈ initSegIsoRel R X S Y) :
    ∃ b₁, ⟨b₁, b₂⟩ₖ ∈ S ∧ ⟨a₁, b₁⟩ₖ ∈ initSegIsoRel R X S Y := by
  rcases (kpair_mem_initSegIsoRel_iff.mp ha₂b₂) with ⟨ha₂X, hb₂Y, hIso₂⟩
  rcases hIso₂ with ⟨g, hg⟩
  have ha₁X : a₁ ∈ X := by
    exact (show a₁ ∈ X ∧ a₂ ∈ X by simpa [mem_prod_iff] using hRlin.subset_prod _ ha₁a₂).1
  have ha₁I₂ : a₁ ∈ initialSegment R X a₂ := mem_initialSegment_iff.mpr ⟨ha₁X, ha₁a₂⟩
  have hgfun : g ∈ initialSegment S Y b₂ ^ initialSegment R X a₂ := hg.1
  rcases exists_of_mem_function hgfun a₁ ha₁I₂ with ⟨b₁, hb₁I₂, ha₁b₁g⟩
  have hb₁b₂ : ⟨b₁, b₂⟩ₖ ∈ S := (mem_initialSegment_iff.mp hb₁I₂).2
  have hb₁Y : b₁ ∈ Y := (mem_initialSegment_iff.mp hb₁I₂).1
  have hNested := hg.restrict_initialSegment ha₁I₂ ha₁b₁g
  have hRewriteR := initialSegment_of_initialSegment_eq hRlin ha₁X ha₂X ha₁a₂
  have hRewriteS := initialSegment_of_initialSegment_eq' hSlin hb₁Y hb₂Y hb₁b₂
  have hIso₁ : InitSegIso R X S Y a₁ b₁ := by
    rw [hRewriteR, hRewriteS] at hNested
    exact ⟨g ↾ (initialSegment R X a₁), hNested⟩
  exact ⟨b₁, hb₁b₂, kpair_mem_initSegIsoRel_iff.mpr ⟨ha₁X, hb₁Y, hIso₁⟩⟩

lemma domain_initSegIsoRel_eq_or_eq_initialSegment_of_least_not_mem
    {R X S Y : V}
    (hRwo : IsWellOrderOn R X)
    (hSlin : IsStrictLinearOrderOn S Y) :
    domain (initSegIsoRel R X S Y) = X ∨
      ∃ a₀, a₀ ∈ X ∧ a₀ ∉ domain (initSegIsoRel R X S Y) ∧
        domain (initSegIsoRel R X S Y) = initialSegment R X a₀ := by
  let D : V := domain (initSegIsoRel R X S Y)
  have hDsubX : D ⊆ X := domain_initSegIsoRel_subset R X S Y
  by_cases hDX : D = X
  · left
    exact hDX
  · right
    have hXD_nonempty : IsNonempty (X \ D) := isNonempty_sdiff_of_ssubset ⟨hDsubX, by
      intro hXD; exact (hDX hXD).elim⟩
    have hXD_ne : X \ D ≠ ∅ := ne_empty_iff_isNonempty.mpr hXD_nonempty
    have hXD_sub : X \ D ⊆ X := fun x hx ↦ (mem_sdiff_iff.mp hx).1
    rcases hRwo.2 (X \ D) hXD_sub hXD_ne with ⟨a₀, ha₀XD, ha₀Least⟩
    have ha₀X : a₀ ∈ X := (mem_sdiff_iff.mp ha₀XD).1
    have ha₀nD : a₀ ∉ D := (mem_sdiff_iff.mp ha₀XD).2
    have hD_sub_seg : D ⊆ initialSegment R X a₀ := by
      intro a haD
      have haX : a ∈ X := hDsubX _ haD
      rcases hRwo.1.trichotomy haX ha₀X with (haa₀ | hEq | ha₀a)
      · exact mem_initialSegment_iff.mpr ⟨haX, haa₀⟩
      · subst hEq
        exact (ha₀nD haD).elim
      · have : a₀ ∈ D := by
          rcases mem_domain_iff.mp haD with ⟨b, hab⟩
          rcases initSegIsoRel_exists_lt_of_lt hRwo.1 hSlin ha₀a hab with ⟨b₀, -, ha₀b₀⟩
          exact mem_domain_iff.mpr ⟨b₀, ha₀b₀⟩
        exact (ha₀nD this).elim
    have hseg_sub_D : initialSegment R X a₀ ⊆ D := by
      intro a haSeg
      have haX : a ∈ X := (mem_initialSegment_iff.mp haSeg).1
      have haa₀ : ⟨a, a₀⟩ₖ ∈ R := (mem_initialSegment_iff.mp haSeg).2
      by_contra haD
      have haXD : a ∈ X \ D := by simp [haX, haD]
      have hleast := ha₀Least a haXD
      rcases hleast with (hEq | ha₀a)
      · subst hEq
        exact hRwo.1.irrefl ha₀X haa₀
      · exact (hRwo.1.asymm haX ha₀X haa₀ ha₀a).elim
    refine ⟨a₀, ha₀X, ha₀nD, ?_⟩
    exact subset_antisymm hD_sub_seg hseg_sub_D

lemma range_initSegIsoRel_eq_or_eq_initialSegment_of_least_not_mem [V ⊧ₘ* 𝗭𝗙]
    {R X S Y : V}
    (hRlin : IsStrictLinearOrderOn R X)
    (hSwo : IsWellOrderOn S Y) :
    range (initSegIsoRel R X S Y) = Y ∨
      ∃ b₀, b₀ ∈ Y ∧ b₀ ∉ range (initSegIsoRel R X S Y) ∧
        range (initSegIsoRel R X S Y) = initialSegment S Y b₀ := by
  have hswap : domain (initSegIsoRel S Y R X) = range (initSegIsoRel R X S Y) :=
    domain_initSegIsoRel_swap_eq_range R X S Y
  have hdom :
      domain (initSegIsoRel S Y R X) = Y ∨
        ∃ b₀, b₀ ∈ Y ∧ b₀ ∉ domain (initSegIsoRel S Y R X) ∧
          domain (initSegIsoRel S Y R X) = initialSegment S Y b₀ :=
    domain_initSegIsoRel_eq_or_eq_initialSegment_of_least_not_mem
      (R := S) (X := Y) (S := R) (Y := X) hSwo hRlin
  rcases hdom with hfull | ⟨b₀, hb₀Y, hb₀n, hEq⟩
  · left
    simpa [hswap] using hfull
  · right
    refine ⟨b₀, hb₀Y, ?_, ?_⟩
    · simpa [hswap] using hb₀n
    · exact hswap.symm.trans hEq

lemma initSegIsoRel_value_unique [V ⊧ₘ* 𝗭𝗙]
    {R X S Y a b₁ b₂ : V}
    (hRwo : IsWellOrderOn R X)
    (hSwo : IsWellOrderOn S Y)
    (hab₁ : ⟨a, b₁⟩ₖ ∈ initSegIsoRel R X S Y)
    (hab₂ : ⟨a, b₂⟩ₖ ∈ initSegIsoRel R X S Y) :
    b₁ = b₂ := by
  by_contra hbne
  let A : V := {x ∈ X ; ∃ y₁ y₂,
    ⟨x, y₁⟩ₖ ∈ initSegIsoRel R X S Y ∧
    ⟨x, y₂⟩ₖ ∈ initSegIsoRel R X S Y ∧ y₁ ≠ y₂}
  have haX : a ∈ X := (kpair_mem_initSegIsoRel_iff.mp hab₁).1
  have haA : a ∈ A := mem_sep_iff.mpr ⟨haX, b₁, b₂, hab₁, hab₂, hbne⟩
  have hA_sub : A ⊆ X := sep_subset
  have hA_ne : A ≠ ∅ := by
    intro hA0
    rw [hA0] at haA
    simp at haA
  rcases hRwo.2 A hA_sub hA_ne with ⟨m, hmA, hmLeast⟩
  rcases (mem_sep_iff.mp hmA) with ⟨hmX, y₁, y₂, hmy₁, hmy₂, hyne⟩
  have hy₁Y : y₁ ∈ Y := (kpair_mem_initSegIsoRel_iff.mp hmy₁).2.1
  have hy₂Y : y₂ ∈ Y := (kpair_mem_initSegIsoRel_iff.mp hmy₂).2.1
  rcases hSwo.1.trichotomy hy₁Y hy₂Y with (hy₁₂ | hEq | hy₂₁)
  · have hy₂m_sw : ⟨y₂, m⟩ₖ ∈ initSegIsoRel S Y R X :=
      (kpair_mem_initSegIsoRel_swap_iff.mp hmy₂)
    rcases initSegIsoRel_exists_lt_of_lt (R := S) (X := Y) (S := R) (Y := X)
        hSwo.1 hRwo.1 hy₁₂ hy₂m_sw with ⟨x₁, hx₁m, hy₁x₁_sw⟩
    have hx₁y₁ : ⟨x₁, y₁⟩ₖ ∈ initSegIsoRel R X S Y :=
      (kpair_mem_initSegIsoRel_swap_iff.mpr hy₁x₁_sw)
    rcases initSegIsoRel_exists_lt_of_lt (R := R) (X := X) (S := S) (Y := Y)
        hRwo.1 hSwo.1 hx₁m hmy₁ with ⟨z, hzy₁, hx₁z⟩
    have hzY : z ∈ Y := (kpair_mem_initSegIsoRel_iff.mp hx₁z).2.1
    have hz_ne_y₁ : z ≠ y₁ := by
      intro hzEq
      subst hzEq
      exact hSwo.1.irrefl hy₁Y hzy₁
    have hx₁X : x₁ ∈ X := by
      exact (show x₁ ∈ X ∧ m ∈ X by simpa [mem_prod_iff] using hRwo.1.subset_prod _ hx₁m).1
    have hx₁A : x₁ ∈ A := mem_sep_iff.mpr ⟨hx₁X, z, y₁, hx₁z, hx₁y₁, hz_ne_y₁⟩
    have hleast_x₁ : x₁ = m ∨ ⟨m, x₁⟩ₖ ∈ R := hmLeast x₁ hx₁A
    rcases hleast_x₁ with (hx₁mEq | hmx₁)
    · subst hx₁mEq
      exact hRwo.1.irrefl hmX hx₁m
    · exact (hRwo.1.asymm hmX hx₁X hmx₁ hx₁m).elim
  · exact hyne hEq
  · have hy₁m_sw : ⟨y₁, m⟩ₖ ∈ initSegIsoRel S Y R X :=
      (kpair_mem_initSegIsoRel_swap_iff.mp hmy₁)
    rcases initSegIsoRel_exists_lt_of_lt (R := S) (X := Y) (S := R) (Y := X)
        hSwo.1 hRwo.1 hy₂₁ hy₁m_sw with ⟨x₂, hx₂m, hy₂x₂_sw⟩
    have hx₂y₂ : ⟨x₂, y₂⟩ₖ ∈ initSegIsoRel R X S Y :=
      (kpair_mem_initSegIsoRel_swap_iff.mpr hy₂x₂_sw)
    rcases initSegIsoRel_exists_lt_of_lt (R := R) (X := X) (S := S) (Y := Y)
        hRwo.1 hSwo.1 hx₂m hmy₂ with ⟨z, hzy₂, hx₂z⟩
    have hzY : z ∈ Y := (kpair_mem_initSegIsoRel_iff.mp hx₂z).2.1
    have hz_ne_y₂ : z ≠ y₂ := by
      intro hzEq
      subst hzEq
      exact hSwo.1.irrefl hy₂Y hzy₂
    have hx₂X : x₂ ∈ X := by
      exact (show x₂ ∈ X ∧ m ∈ X by simpa [mem_prod_iff] using hRwo.1.subset_prod _ hx₂m).1
    have hx₂A : x₂ ∈ A := mem_sep_iff.mpr ⟨hx₂X, z, y₂, hx₂z, hx₂y₂, hz_ne_y₂⟩
    have hleast_x₂ : x₂ = m ∨ ⟨m, x₂⟩ₖ ∈ R := hmLeast x₂ hx₂A
    rcases hleast_x₂ with (hx₂mEq | hmx₂)
    · subst hx₂mEq
      exact hRwo.1.irrefl hmX hx₂m
    · exact (hRwo.1.asymm hmX hx₂X hmx₂ hx₂m).elim

lemma initSegIsoRel_total_unique [V ⊧ₘ* 𝗭𝗙]
    {R X S Y a : V}
    (hRwo : IsWellOrderOn R X)
    (hSwo : IsWellOrderOn S Y)
    (haD : a ∈ domain (initSegIsoRel R X S Y)) :
    ∃! b, ⟨a, b⟩ₖ ∈ initSegIsoRel R X S Y := by
  rcases mem_domain_iff.mp haD with ⟨b, hab⟩
  refine ⟨b, hab, ?_⟩
  intro b' hab'
  exact initSegIsoRel_value_unique hRwo hSwo hab' hab

lemma initSegIsoRel_injective [V ⊧ₘ* 𝗭𝗙]
    {R X S Y : V}
    (hRwo : IsWellOrderOn R X)
    (hSwo : IsWellOrderOn S Y) :
    Injective (initSegIsoRel R X S Y) := by
  intro x₁ x₂ y hx₁ hx₂
  have hyx₁ : ⟨y, x₁⟩ₖ ∈ initSegIsoRel S Y R X := (kpair_mem_initSegIsoRel_swap_iff.mp hx₁)
  have hyx₂ : ⟨y, x₂⟩ₖ ∈ initSegIsoRel S Y R X := (kpair_mem_initSegIsoRel_swap_iff.mp hx₂)
  exact initSegIsoRel_value_unique hSwo hRwo hyx₁ hyx₂

lemma initSegIsoRel_isOrderIso_domain_range [V ⊧ₘ* 𝗭𝗙]
    {R X S Y : V}
    (hRwo : IsWellOrderOn R X)
    (hSwo : IsWellOrderOn S Y) :
    IsOrderIso R (domain (initSegIsoRel R X S Y)) S (range (initSegIsoRel R X S Y))
      (initSegIsoRel R X S Y) := by
  let F : V := initSegIsoRel R X S Y
  have hFfun : F ∈ range F ^ domain F := by
    apply mem_function.intro
    · intro p hp
      rcases show ∃ a ∈ X, ∃ b ∈ Y, p = ⟨a, b⟩ₖ from by
          simpa [mem_prod_iff] using (initSegIsoRel_subset_prod R X S Y p hp) with
        ⟨a, haX, b, hbY, rfl⟩
      have hab : ⟨a, b⟩ₖ ∈ F := by simpa [F] using hp
      have haD : a ∈ domain F := mem_domain_of_kpair_mem hab
      have hbR : b ∈ range F := mem_range_of_kpair_mem hab
      simpa [mem_prod_iff] using And.intro haD hbR
    · intro a haD
      exact initSegIsoRel_total_unique hRwo hSwo haD
  have hFinj : Injective F := initSegIsoRel_injective hRwo hSwo
  have hFrel :
      ∀ a₁ ∈ domain F, ∀ a₂ ∈ domain F, ⟨a₁, a₂⟩ₖ ∈ R ↔ ⟨F ‘ a₁, F ‘ a₂⟩ₖ ∈ S := by
    intro a₁ ha₁D a₂ ha₂D
    rcases exists_of_mem_function hFfun a₁ ha₁D with ⟨b₁, hb₁R, ha₁b₁⟩
    rcases exists_of_mem_function hFfun a₂ ha₂D with ⟨b₂, hb₂R, ha₂b₂⟩
    have hb₁val : F ‘ a₁ = b₁ := value_eq_of_kpair_mem hFfun ha₁b₁
    have hb₂val : F ‘ a₂ = b₂ := value_eq_of_kpair_mem hFfun ha₂b₂
    have hforward : ⟨a₁, a₂⟩ₖ ∈ R → ⟨b₁, b₂⟩ₖ ∈ S := by
      intro ha₁₂
      rcases initSegIsoRel_exists_lt_of_lt (R := R) (X := X) (S := S) (Y := Y)
          hRwo.1 hSwo.1 ha₁₂ ha₂b₂ with ⟨b₁', hb₁'b₂, ha₁b₁'⟩
      have hb₁'eq : b₁' = b₁ := initSegIsoRel_value_unique hRwo hSwo ha₁b₁' ha₁b₁
      simpa [hb₁'eq] using hb₁'b₂
    have hback : ⟨b₁, b₂⟩ₖ ∈ S → ⟨a₁, a₂⟩ₖ ∈ R := by
      intro hb₁₂
      have hb₂a₂_sw : ⟨b₂, a₂⟩ₖ ∈ initSegIsoRel S Y R X :=
        (kpair_mem_initSegIsoRel_swap_iff.mp ha₂b₂)
      rcases initSegIsoRel_exists_lt_of_lt (R := S) (X := Y) (S := R) (Y := X)
          hSwo.1 hRwo.1 hb₁₂ hb₂a₂_sw with ⟨a₁', ha₁'a₂, hb₁a₁'_sw⟩
      have ha₁'b₁ : ⟨a₁', b₁⟩ₖ ∈ F := (kpair_mem_initSegIsoRel_swap_iff.mpr hb₁a₁'_sw)
      have ha₁'eq : a₁' = a₁ := hFinj _ _ _ ha₁'b₁ ha₁b₁
      simpa [ha₁'eq] using ha₁'a₂
    have hiff : ⟨a₁, a₂⟩ₖ ∈ R ↔ ⟨b₁, b₂⟩ₖ ∈ S := ⟨hforward, hback⟩
    simpa [hb₁val, hb₂val] using hiff
  exact ⟨hFfun, hFinj, rfl, hFrel⟩

lemma initSegIsoRel_not_iso_between_initialSegments_of_outside
    {R X S Y a₀ b₀ : V}
    (ha₀X : a₀ ∈ X)
    (hb₀Y : b₀ ∈ Y)
    (ha₀nD : a₀ ∉ domain (initSegIsoRel R X S Y)) :
    ¬ IsOrderIso R (initialSegment R X a₀) S (initialSegment S Y b₀) (initSegIsoRel R X S Y) := by
  intro hIso
  have hInit : InitSegIso R X S Y a₀ b₀ := ⟨initSegIsoRel R X S Y, hIso⟩
  have hab : ⟨a₀, b₀⟩ₖ ∈ initSegIsoRel R X S Y :=
    kpair_mem_initSegIsoRel_iff.mpr ⟨ha₀X, hb₀Y, hInit⟩
  have ha₀D : a₀ ∈ domain (initSegIsoRel R X S Y) := mem_domain_of_kpair_mem hab
  have hb₀R : b₀ ∈ range (initSegIsoRel R X S Y) := mem_range_of_kpair_mem hab
  exact (ha₀nD ha₀D).elim

lemma initSegIsoRel_not_both_proper_initialSegments [V ⊧ₘ* 𝗭𝗙]
    {R X S Y a₀ b₀ : V}
    (hRwo : IsWellOrderOn R X)
    (hSwo : IsWellOrderOn S Y)
    (ha₀X : a₀ ∈ X)
    (hb₀Y : b₀ ∈ Y)
    (hDom : domain (initSegIsoRel R X S Y) = initialSegment R X a₀)
    (hRan : range (initSegIsoRel R X S Y) = initialSegment S Y b₀) :
    False := by
  have hIsoDR := initSegIsoRel_isOrderIso_domain_range hRwo hSwo
  have ha₀nD : a₀ ∉ domain (initSegIsoRel R X S Y) := by
    rw [hDom]
    intro ha₀
    exact hRwo.1.irrefl ha₀X (mem_initialSegment_iff.mp ha₀).2
  have hIsoSeg : IsOrderIso R (initialSegment R X a₀) S (initialSegment S Y b₀)
      (initSegIsoRel R X S Y) := by
    simpa [hDom, hRan] using hIsoDR
  exact initSegIsoRel_not_iso_between_initialSegments_of_outside
    ha₀X hb₀Y ha₀nD hIsoSeg

lemma wellOrder_comparable_by_initSegIsoRel [V ⊧ₘ* 𝗭𝗙]
    {R X S Y : V}
    (hRwo : IsWellOrderOn R X)
    (hSwo : IsWellOrderOn S Y) :
    IsOrderIso R X S Y (initSegIsoRel R X S Y) ∨
      (∃ a₀, a₀ ∈ X ∧
        IsOrderIso R (initialSegment R X a₀) S Y (initSegIsoRel R X S Y)) ∨
      (∃ b₀, b₀ ∈ Y ∧
        IsOrderIso R X S (initialSegment S Y b₀) (initSegIsoRel R X S Y)) := by
  have hIsoDR := initSegIsoRel_isOrderIso_domain_range hRwo hSwo
  rcases domain_initSegIsoRel_eq_or_eq_initialSegment_of_least_not_mem
      (R := R) (X := X) (S := S) (Y := Y) hRwo hSwo.1 with
    hDomFull | ⟨a₀, ha₀X, ha₀nD, hDomSeg⟩
  · rcases range_initSegIsoRel_eq_or_eq_initialSegment_of_least_not_mem
      (R := R) (X := X) (S := S) (Y := Y) hRwo.1 hSwo with
      hRanFull | ⟨b₀, hb₀Y, hb₀nR, hRanSeg⟩
    · left
      simpa [hDomFull, hRanFull] using hIsoDR
    · right
      right
      refine ⟨b₀, hb₀Y, ?_⟩
      simpa [hDomFull, hRanSeg] using hIsoDR
  · rcases range_initSegIsoRel_eq_or_eq_initialSegment_of_least_not_mem
      (R := R) (X := X) (S := S) (Y := Y) hRwo.1 hSwo with
      hRanFull | ⟨b₀, hb₀Y, hb₀nR, hRanSeg⟩
    · right
      left
      refine ⟨a₀, ha₀X, ?_⟩
      simpa [hDomSeg, hRanFull] using hIsoDR
    · exact (initSegIsoRel_not_both_proper_initialSegments
        (R := R) (X := X) (S := S) (Y := Y)
        hRwo hSwo ha₀X hb₀Y hDomSeg hRanSeg).elim

/-! ### Cardinality comparison -/

@[simp] lemma kpair_mem_sUnion_iff {C x y : V} :
    ⟨x, y⟩ₖ ∈ ⋃ˢ C ↔ ∃ f ∈ C, ⟨x, y⟩ₖ ∈ f := by
  simp [mem_sUnion_iff]

lemma IsFunction.sUnion_of_coherent {C : V}
    (hfunc : ∀ f ∈ C, IsFunction f)
    (hcoh : ∀ f ∈ C, ∀ g ∈ C, ∀ x y₁ y₂,
      ⟨x, y₁⟩ₖ ∈ f → ⟨x, y₂⟩ₖ ∈ g → y₁ = y₂) :
    IsFunction (⋃ˢ C) := by
  have hmem : ⋃ˢ C ∈ range (⋃ˢ C) ^ domain (⋃ˢ C) := by
    apply mem_function.intro
    · intro p hp
      rcases mem_sUnion_iff.mp hp with ⟨f, hfC, hpf⟩
      have hff : IsFunction f := hfunc f hfC
      have hmem : f ∈ range f ^ domain f := IsFunction.mem_function f
      rcases show ∃ x ∈ domain f, ∃ y ∈ range f, p = ⟨x, y⟩ₖ from by
          simpa [mem_prod_iff] using subset_prod_of_mem_function hmem p hpf with
        ⟨x, hxd, y, hyd, rfl⟩
      have hxyU : ⟨x, y⟩ₖ ∈ ⋃ˢ C := mem_sUnion_iff.mpr ⟨f, hfC, by simpa⟩
      have hxU : x ∈ domain (⋃ˢ C) := mem_domain_of_kpair_mem hxyU
      have hyU : y ∈ range (⋃ˢ C) := mem_range_of_kpair_mem hxyU
      simpa [mem_prod_iff] using And.intro hxU hyU
    · intro x hx
      rcases mem_domain_iff.mp hx with ⟨y, hxyU⟩
      refine ExistsUnique.intro y hxyU ?_
      intro y' hxy'U
      rcases mem_sUnion_iff.mp hxyU with ⟨f, hfC, hxyf⟩
      rcases mem_sUnion_iff.mp hxy'U with ⟨g, hgC, hxyg⟩
      exact (hcoh f hfC g hgC x y y' hxyf hxyg).symm
  exact IsFunction.of_mem hmem

def CardLE (X Y : V) : Prop := ∃ f ∈ Y ^ X, Injective f

infix:50 " ≤# " => CardLE

lemma cardLE_of_subset {X Y : V} (h : X ⊆ Y) : X ≤# Y :=
  ⟨identity X, mem_function_of_mem_function_of_subset (identity_mem_function X) h, by simp⟩

@[simp] lemma cardLE_empty (X : V) : ∅ ≤# X := cardLE_of_subset (by simp)

@[simp, refl] lemma CardLE.refl (X : V) : X ≤# X := cardLE_of_subset (by simp)

@[trans] lemma CardLE.trans {X Y Z : V} : X ≤# Y → Y ≤# Z → X ≤# Z := by
  rintro ⟨f, hf, f_inj⟩
  rintro ⟨g, hg, g_inj⟩
  refine ⟨compose f g, compose_function hf hg, compose_injective f_inj g_inj⟩

def CardLT (X Y : V) : Prop := X ≤# Y ∧ ¬Y ≤# X

infix:50 " <# " => CardLT

def CardLE.dfn : Semisentence ℒₛₑₜ 2 := f“X Y. ∃ f ∈ !function.dfn Y X, !Injective.dfn f”

instance CardLE.defined : ℒₛₑₜ-relation[V] CardLE via dfn := ⟨fun v ↦ by simp [CardLE, dfn]⟩

instance CardLE.definable : ℒₛₑₜ-relation[V] CardLE := defined.to_definable

def CardLT.dfn : Semisentence ℒₛₑₜ 2 := “X Y. !CardLE.dfn X Y ∧ ¬!CardLE.dfn Y X”

instance CardLT.defined : ℒₛₑₜ-relation[V] CardLT via dfn := ⟨fun v ↦ by simp [CardLT, dfn]⟩

instance CardLT.definable : ℒₛₑₜ-relation[V] CardLT := defined.to_definable

def CardEQ (X Y : V) : Prop := X ≤# Y ∧ Y ≤# X

infix:60 " ≋ " => CardEQ

def CardEQ.dfn : Semisentence ℒₛₑₜ 2 := “X Y. !CardLE.dfn X Y ∧ !CardLE.dfn Y X”

instance CardEQ.defined : ℒₛₑₜ-relation[V] CardEQ via dfn := ⟨fun v ↦ by simp [CardEQ, dfn]⟩

instance CardEQ.definable : ℒₛₑₜ-relation[V] CardEQ := defined.to_definable

lemma CardEQ.le {X Y : V} (h : X ≋ Y) : X ≤# Y := h.1

lemma CardEQ.ge {X Y : V} (h : X ≋ Y) : Y ≤# X := h.2

@[simp, refl] lemma CardEQ.refl (X : V) : X ≋ X := ⟨by rfl, by rfl⟩

@[symm] lemma CardEQ.symm {X Y : V} : X ≋ Y → Y ≋ X := fun e ↦ ⟨e.2, e.1⟩

@[trans] lemma CardEQ.trans {X Y Z : V} : X ≋ Y → Y ≋ Z → X ≋ Z := fun eXY eYZ ↦
  ⟨eXY.le.trans eYZ.le, eYZ.ge.trans eXY.ge⟩

lemma cardLT_power (X : V) : X <# ℘ X := by
  have : X ≤# ℘ X := by
    let F : V := {p ∈ X ×ˢ ℘ X ; ∃ x ∈ X, p = ⟨x, {x}⟩ₖ}
    have : F ∈ ℘ X ^ X := by
      apply mem_function.intro
      · simp [F]
      · intro x hx
        apply ExistsUnique.intro {x} (by simp [F, hx])
        intro y hy
        have : y ⊆ X ∧ y = {x} := by simpa [hx, F] using hy
        simp [this]
    have : Injective F := by
      intro x₁ x₂ s h₁ h₂
      rcases show (x₁ ∈ X ∧ s ⊆ X) ∧ x₁ ∈ X ∧ s = {x₁} by simpa [F] using h₁ with ⟨_, _, rfl⟩
      have : (x₂ ∈ X ∧ x₁ ∈ X) ∧ x₁ ∈ X ∧ x₂ = x₁ := by simpa [F] using h₂
      simp [this.2.2]
    refine ⟨F, by assumption, by assumption⟩
  have : ¬℘ X ≤# X := by
    rintro ⟨F, hF, injF⟩
    have : IsFunction F := IsFunction.of_mem hF
    let D : V := {x ∈ X ; ∃ s ∈ ℘ X, ⟨s, x⟩ₖ ∈ F ∧ x ∉ s}
    have : ∃ d ∈ X, ⟨D, d⟩ₖ ∈ F := exists_of_mem_function hF D (by simp [D])
    rcases this with ⟨d, hd, Hd⟩
    have : d ∈ D ↔ d ∉ D := calc
      d ∈ D ↔ ∃ s ⊆ X, ⟨s, d⟩ₖ ∈ F ∧ d ∉ s := by simp [hd, D]
      _     ↔ d ∉ D := ?_
    · grind
    constructor
    · rintro ⟨S, hS, hSF, hdS⟩
      rcases show D = S from injF _ _ _ Hd hSF
      assumption
    · intro h
      refine ⟨D, by simpa [hd] using mem_of_mem_functions hF Hd, Hd, h⟩
  refine ⟨by assumption, by assumption⟩

lemma two_pow_cardEQ_power (X : V) : 2 ^ X ≋ ℘ X := by
  constructor
  · let F : V := {p ∈ (2 ^ X) ×ˢ ℘ X ; ∃ f s, p = ⟨f, s⟩ₖ ∧ ∀ x, x ∈ s ↔ ⟨x, 1⟩ₖ ∈ f}
    refine ⟨F, ?_, ?_⟩
    · apply mem_function.intro
      · simp [F]
      · intro f hf
        let s : V := {x ∈ X ; ⟨x, 1⟩ₖ ∈ f}
        have ss_s : s ⊆ X := by simp [s]
        have mem_s : ∀ x, x ∈ s ↔ ⟨x, 1⟩ₖ ∈ f := by
          simp only [mem_sep_iff, and_iff_right_iff_imp, s]
          intro x hx
          exact mem_of_mem_functions hf hx |>.1
        apply ExistsUnique.intro s ?_ ?_
        · simp [F, hf, ss_s, mem_s]
        · intro t ht
          ext x
          have ht : (f ∈ ((2 : V) ^ X) ∧ t ⊆ X) ∧ ∀ x, x ∈ t ↔ ⟨x, 1⟩ₖ ∈ f := by simpa [F] using ht
          simp [ht, mem_s]
    · intro f₁ f₂ s h₁ h₂
      have : (f₁ ∈ (2 ^ X : V) ∧ s ⊆ X) ∧ ∀ x, x ∈ s ↔ ⟨x, 1⟩ₖ ∈ f₁ := by simpa [F] using h₁
      rcases this with ⟨⟨f₁func, hs⟩, H₁⟩
      have : (f₂ ∈ (2 ^ X : V) ∧ s ⊆ X) ∧ ∀ x, x ∈ s ↔ ⟨x, 1⟩ₖ ∈ f₂ := by simpa [F] using h₂
      rcases this with ⟨⟨f₂func, _⟩, H₂⟩
      apply function_ext f₁func f₂func
      intro x hx i hi
      rcases show i = 0 ∨ i = 1 by simpa using hi with (rfl | rfl)
      · contrapose
        suffices ⟨x, 1⟩ₖ ∈ f₂ → ⟨x, 1⟩ₖ ∈ f₁ by grind
        grind
      · grind
  · let F : V := {p ∈ ℘ X ×ˢ (2 ^ X) ; ∃ f s, p = ⟨s, f⟩ₖ ∧ ∀ x, ⟨x, 1⟩ₖ ∈ f ↔ x ∈ s}
    refine ⟨F, ?_, ?_⟩
    · apply mem_function.intro
      · simp [F]
      · intro s hs
        have hs : s ⊆ X := by simpa using hs
        let f : V := {p ∈ X ×ˢ 2 ; ∃ x, (x ∈ s → p = ⟨x, 1⟩ₖ) ∧ (x ∉ s → p = ⟨x, 0⟩ₖ)}
        have kp1_mem_f : ∀ x, ⟨x, 1⟩ₖ ∈ f ↔ x ∈ s := by
          intro x
          have : x ∈ s → x ∈ X := fun hx ↦ hs _ hx
          simp only [mem_sep_iff, kpair_mem_iff, mem_two_iff, one_ne_zero, or_true, and_true,
            kpair_iff, and_false, imp_false, not_not, f]; grind
        have f_func : f ∈ (2 ^ X : V) := by
          apply mem_function.intro (by simp [f])
          intro x hx
          by_cases hxS : x ∈ s
          · apply ExistsUnique.intro 1
            · simp only [mem_sep_iff, kpair_mem_iff, hx, mem_two_iff, one_ne_zero, or_true, and_self,
              kpair_iff, and_true, and_false, imp_false, not_not, true_and, f]; grind
            · intro i hi
              simp [f, hx] at hi
              grind only
          · apply ExistsUnique.intro 0
            · simp only [mem_sep_iff, kpair_mem_iff, hx, mem_two_iff, zero_ne_one, or_false,
              and_self, kpair_iff, and_false, imp_false, and_true, true_and, f]; grind
            · intro i hi
              simp [f, hx] at hi
              grind only
        apply ExistsUnique.intro f ?_ ?_
        · simp [F, hs, kp1_mem_f, f_func]
        · intro g hg
          have : (s ⊆ X ∧ g ∈ (2 ^ X : V)) ∧ ∀ x, ⟨x, 1⟩ₖ ∈ g ↔ x ∈ s := by simpa [F] using hg
          rcases this with ⟨⟨_, g_func⟩, Hg⟩
          apply function_ext g_func f_func
          intro x hx i hi
          rcases show i = 0 ∨ i = 1 by simpa using hi with (rfl | rfl)
          · suffices ⟨x, 1⟩ₖ ∈ f → ⟨x, 1⟩ₖ ∈ g by grind
            grind
          · grind
    · intro s₁ s₂ f h₁ h₂
      have : (s₁ ⊆ X ∧ f ∈ (2 ^ X : V)) ∧ ∀ x, ⟨x, 1⟩ₖ ∈ f ↔ x ∈ s₁ := by simpa [F] using h₁
      have : (s₂ ⊆ X ∧ f ∈ (2 ^ X : V)) ∧ ∀ x, ⟨x, 1⟩ₖ ∈ f ↔ x ∈ s₂ := by simpa [F] using h₂
      ext z; grind

end LO.FirstOrder.SetTheory
