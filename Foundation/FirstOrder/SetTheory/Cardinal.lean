module

public import Foundation.FirstOrder.SetTheory.Recursion

namespace LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V ⊧ₘ* 𝗭]

lemma mem_ω_eq_zero_or_eq_succ {n : V} (hn : n ∈ (ω : V)) :
    n = 0 ∨ ∃ m ∈ (ω : V), n = succ m := by
  let P : V → Prop := fun k ↦ k = 0 ∨ ∃ m ∈ (ω : V), k = succ m
  have hP : ℒₛₑₜ-predicate[V] P := by
    change ℒₛₑₜ-predicate[V] (fun k ↦ k = 0 ∨ ∃ m ∈ (ω : V), k = succ m)
    definability
  have hAll : ∀ k ∈ (ω : V), P k := by
    apply naturalNumber_induction (P := P) hP
    · exact Or.inl rfl
    · intro k hk hkP
      exact Or.inr ⟨k, hk, rfl⟩
  exact hAll n hn

lemma cantorBernstein_nested
    [V ⊧ₘ* 𝗭𝗙]
    {X Y g : V}
    (hXY : X ⊆ Y)
    (hg : g ∈ X ^ Y)
    (hgInj : Injective g) :
    ∃ h, Bijective h Y X := by
  let F : V → V := fun A ↦ g “ A
  have hgY : g ∈ Y ^ Y := mem_function_of_mem_function_of_subset hg hXY
  have hFdef : ℒₛₑₜ-function₁[V] F := by
    change ℒₛₑₜ-function₁[V] (fun A ↦ image g A)
    definability
  let G : V → V := IsOrdinal.SuccLimitRecursionStep (Y \ X) F
  have hGdef : ℒₛₑₜ-function₁[V] G := by
    simpa [G] using IsOrdinal.succLimitRecursionStep_definable (Y \ X) F hFdef
  let iter : V → V := IsOrdinal.transfiniteRecursionValueFn G
  have hIterDef : ℒₛₑₜ-function₁[V] iter := by
    simpa [iter] using IsOrdinal.transfiniteRecursionValueFn_definable (F := G) hGdef
  have hIterZero : iter 0 = Y \ X := by
    simpa [iter, G] using
      IsOrdinal.succLimitRecursionStep_zero_transfiniteRecursionValueFn (a₀ := Y \ X) (F := F) hFdef
  have hIterSucc :
      ∀ {n : V}, IsOrdinal n → iter (succ n) = g “ (iter n) := by
    intro n hn
    simpa [iter, G, F] using
      IsOrdinal.succLimitRecursionStep_successor_transfiniteRecursionValueFn
        (a₀ := Y \ X) (F := F) hFdef (hα := hn)
  have hIterSubY : ∀ n ∈ (ω : V), iter n ⊆ Y := by
    have hP : ℒₛₑₜ-predicate[V] (fun n ↦ iter n ⊆ Y) := by
      letI : ℒₛₑₜ-function₁[V] iter := hIterDef
      change ℒₛₑₜ-predicate[V] (fun n ↦ iter n ⊆ Y)
      definability
    apply naturalNumber_induction (P := fun n ↦ iter n ⊆ Y) hP
    · intro z hz
      exact (mem_sdiff_iff.mp (by simpa [hIterZero] using hz)).1
    · intro n hn ih z hz
      rw [hIterSucc (IsOrdinal.of_mem hn)] at hz
      exact image_subset_of_mem_function hgY _ hz
  let r : V := IsOrdinal.transfiniteRecursionValueFnReplacementGraph G hGdef (ω : V)
  have hr :
      IsFunction r ∧ domain r = (ω : V) ∧
        ∀ n ∈ (ω : V), ∀ A, ⟨n, A⟩ₖ ∈ r ↔ A = iter n := by
    simpa [r, iter] using
      IsOrdinal.transfiniteRecursionValueFnReplacementGraph_spec (F := G) hGdef (ω : V)
  let D : V := ⋃ˢ range r
  have hmemD : ∀ z : V, z ∈ D ↔ ∃ n ∈ (ω : V), z ∈ iter n := by
    intro z
    constructor
    · intro hz
      rcases mem_sUnion_iff.mp hz with ⟨A, hAr, hzA⟩
      rcases mem_range_iff.mp hAr with ⟨n, hnA⟩
      have hnω : n ∈ (ω : V) := by
        have hnd : n ∈ domain r := mem_domain_of_kpair_mem hnA
        simpa [hr.2.1] using hnd
      have hAeq : A = iter n := (hr.2.2 n hnω A).1 hnA
      exact ⟨n, hnω, by simpa [hAeq] using hzA⟩
    · rintro ⟨n, hnω, hzn⟩
      have hnA : ⟨n, iter n⟩ₖ ∈ r := (hr.2.2 n hnω (iter n)).2 rfl
      have hIterR : iter n ∈ range r := mem_range_iff.mpr ⟨n, hnA⟩
      exact mem_sUnion_iff.mpr ⟨iter n, hIterR, hzn⟩
  have hDSubY : D ⊆ Y := by
    intro z hz
    rcases (hmemD z).1 hz with ⟨n, hnω, hzn⟩
    exact hIterSubY n hnω z hzn
  have hImageDSubD : (g “ D) ⊆ D := by
    intro z hz
    rcases mem_image_iff.mp hz with ⟨y, hyD, hyz⟩
    rcases (hmemD y).1 hyD with ⟨n, hnω, hyn⟩
    have hzSucc : z ∈ iter (succ n) := by
      rw [hIterSucc (IsOrdinal.of_mem hnω)]
      exact mem_image_iff.mpr ⟨y, hyn, hyz⟩
    exact (hmemD z).2 ⟨succ n, ω_succ_closed hnω, hzSucc⟩
  have hImageEq : (g “ D) = D ∩ X := by
    apply subset_antisymm
    · intro z hz
      exact mem_inter_iff.mpr ⟨hImageDSubD z hz, image_subset_of_mem_function hg _ hz⟩
    · intro z hz
      have ⟨hzD, hzX⟩ := mem_inter_iff.mp hz
      rcases (hmemD z).1 hzD with ⟨n, hnω, hzn⟩
      rcases mem_ω_eq_zero_or_eq_succ hnω with (rfl | ⟨m, hmω, rfl⟩)
      · have hz0 : z ∈ Y \ X := by simpa [hIterZero] using hzn
        exact (mem_sdiff_iff.mp hz0).2 hzX |> False.elim
      · rw [hIterSucc (IsOrdinal.of_mem hmω)] at hzn
        exact image_mono (fun u hu ↦ (hmemD u).2 ⟨m, hmω, hu⟩) _ hzn
  have hNotDImpMemX : ∀ y ∈ Y, y ∉ D → y ∈ X := by
    intro y hyY hyD
    by_cases hyX : y ∈ X
    · exact hyX
    · have hyDiff : y ∈ Y \ X := mem_sdiff_iff.mpr ⟨hyY, hyX⟩
      have hyD' : y ∈ D := (hmemD y).2 ⟨0, zero_mem_ω, by simpa [hIterZero] using hyDiff⟩
      exact (hyD hyD').elim
  let h : V := (g ↾ D) ∪ identity (Y \ D)
  have hhMem :
      ∀ y x : V,
        ⟨y, x⟩ₖ ∈ h ↔
          y ∈ Y ∧ x ∈ X ∧
            ((y ∈ D ∧ ⟨y, x⟩ₖ ∈ g) ∨ (y ∉ D ∧ x = y)) := by
    intro y x
    constructor
    · intro hyx
      rcases mem_union_iff.mp hyx with (hyxD | hyxId)
      · have hyxg : ⟨y, x⟩ₖ ∈ g := (kpair_mem_restrict_iff.mp hyxD).1
        have hyD : y ∈ D := (kpair_mem_restrict_iff.mp hyxD).2
        have hyY : y ∈ Y := hDSubY y hyD
        have hxX : x ∈ X := (mem_of_mem_functions hg hyxg).2
        exact ⟨hyY, hxX, Or.inl ⟨hyD, hyxg⟩⟩
      · have hy_mem : y ∈ Y \ D := (kpair_mem_identity_iff.mp hyxId).1
        have hxy : y = x := (kpair_mem_identity_iff.mp hyxId).2
        have hyYD : y ∈ Y ∧ y ∉ D := mem_sdiff_iff.mp hy_mem
        have hyY : y ∈ Y := hyYD.1
        have hyNotD : y ∉ D := hyYD.2
        have hxX : x ∈ X := by
          rw [← hxy]
          exact hNotDImpMemX y hyY hyNotD
        exact ⟨hyY, hxX, Or.inr ⟨hyNotD, hxy.symm⟩⟩
    · rintro ⟨hyY, hxX, hyx⟩
      rcases hyx with (⟨hyD, hyxg⟩ | ⟨hyNotD, hxy⟩)
      · exact mem_union_iff.mpr <| Or.inl <| kpair_mem_restrict_iff.mpr ⟨hyxg, hyD⟩
      · exact mem_union_iff.mpr <| Or.inr <| by
          exact (kpair_mem_identity_iff.mpr ⟨mem_sdiff_iff.mpr ⟨hyY, hyNotD⟩, hxy.symm⟩)
  have hhFun : h ∈ X ^ Y := by
    apply mem_function.intro
    · intro p hp
      rcases mem_union_iff.mp hp with (hpD | hpId)
      · have hpg : p ∈ g := (mem_restrict_iff.mp hpD).1
        exact subset_prod_of_mem_function hg _ hpg
      · rcases mem_identity_iff.mp hpId with ⟨y, hy_mem, rfl⟩
        have hyYD : y ∈ Y ∧ y ∉ D := mem_sdiff_iff.mp hy_mem
        have hyX : y ∈ X := hNotDImpMemX y hyYD.1 hyYD.2
        simpa [mem_prod_iff] using And.intro hyYD.1 hyX
    · intro y hyY
      by_cases hyD : y ∈ D
      · rcases exists_of_mem_function hg y hyY with ⟨x, hxX, hyxg⟩
        refine ExistsUnique.intro x ((hhMem y x).2 ⟨hyY, hxX, Or.inl ⟨hyD, hyxg⟩⟩) ?_
        intro x' hyx'
        rcases (hhMem y x').1 hyx' with ⟨-, -, hyx'⟩
        rcases hyx' with (⟨-, hyx'g⟩ | ⟨hyNotD, -⟩)
        · exact (IsFunction.of_mem hg).unique hyx'g hyxg
        · exact absurd hyD hyNotD
      · have hyX : y ∈ X := hNotDImpMemX y hyY hyD
        refine ExistsUnique.intro y ((hhMem y y).2 ⟨hyY, hyX, Or.inr ⟨hyD, rfl⟩⟩) ?_
        intro x hyx
        rcases (hhMem y x).1 hyx with ⟨-, -, hyx'⟩
        rcases hyx' with (⟨hyD', -⟩ | ⟨hyNotD, hxy⟩)
        · exact (hyD hyD').elim
        · exact hxy
  have hhInj : Injective h := by
    intro y₁ y₂ x hy₁ hy₂
    rcases (hhMem y₁ x).1 hy₁ with ⟨-, -, hy₁'⟩
    rcases (hhMem y₂ x).1 hy₂ with ⟨-, -, hy₂'⟩
    rcases hy₁' with (⟨hy₁D, hy₁xg⟩ | ⟨hy₁NotD, hx₁⟩)
    · rcases hy₂' with (⟨hy₂D, hy₂xg⟩ | ⟨hy₂NotD, hx₂⟩)
      · exact hgInj _ _ x hy₁xg hy₂xg
      · have hxD : x ∈ D := hImageDSubD _ (mem_image_of_kpair_mem hy₁D hy₁xg)
        have hy₂D : y₂ ∈ D := by simpa [hx₂] using hxD
        exact (hy₂NotD hy₂D).elim
    · rcases hy₂' with (⟨hy₂D, hy₂xg⟩ | ⟨hy₂NotD, hx₂⟩)
      · have hxD : x ∈ D := hImageDSubD _ (mem_image_of_kpair_mem hy₂D hy₂xg)
        have hy₁D : y₁ ∈ D := by simpa [hx₁] using hxD
        exact (hy₁NotD hy₁D).elim
      · calc
          y₁ = x := hx₁.symm
          _ = y₂ := hx₂
  have hhRange : range h = X := by
    apply subset_antisymm
    · exact range_subset_of_mem_function hhFun
    · intro x hxX
      by_cases hxImg : x ∈ g “ D
      · rcases mem_image_iff.mp hxImg with ⟨y, hyD, hyxg⟩
        have hyY : y ∈ Y := hDSubY y hyD
        exact mem_range_iff.mpr ⟨y, (hhMem y x).2 ⟨hyY, hxX, Or.inl ⟨hyD, hyxg⟩⟩⟩
      · have hxNotD : x ∉ D := by
          intro hxD
          have hxDX : x ∈ D ∩ X := mem_inter_iff.mpr ⟨hxD, hxX⟩
          exact hxImg (by simpa [hImageEq] using hxDX)
        have hxY : x ∈ Y := hXY x hxX
        exact mem_range_iff.mpr ⟨x, (hhMem x x).2 ⟨hxY, hxX, Or.inr ⟨hxNotD, rfl⟩⟩⟩
  exact ⟨h, hhFun, hhInj, hhRange⟩

lemma CardEQ.exists_bijective
    [V ⊧ₘ* 𝗭𝗙]
    {X Y : V}
    (h : X ≋ Y) :
    ∃ f, Bijective f X Y := by
  rcases h with ⟨⟨f, hf, hfInj⟩, ⟨g, hg, hgInj⟩⟩
  let X' : V := range f
  have hfBij : Bijective f X X' := ⟨mem_function_range_of_mem_function hf, hfInj, rfl⟩
  have hX'Sub : X' ⊆ Y := range_subset_of_mem_function hf
  have hgfMem : compose g f ∈ X' ^ Y := by
    exact compose_function hg (mem_function_range_of_mem_function hf)
  have hgfInj : Injective (compose g f) := compose_injective hgInj hfInj
  rcases cantorBernstein_nested hX'Sub hgfMem hgfInj with ⟨h, hh⟩
  exact ⟨compose f (inverse h), hfBij.comp hh.symm⟩

lemma cardEQ_iff_exists_bijective
    [V ⊧ₘ* 𝗭𝗙]
    {X Y : V} :
    X ≋ Y ↔ ∃ f, Bijective f X Y := by
  constructor
  · exact CardEQ.exists_bijective
  · exact cardEQ_of_exists_bijective

lemma CardEQ.prod
    [V ⊧ₘ* 𝗭𝗙]
    {X X' Y Y' : V}
    (hX : X ≋ X') (hY : Y ≋ Y') :
    (X ×ˢ Y) ≋ (X' ×ˢ Y') := by
  rcases CardEQ.exists_bijective hX with ⟨f, hf⟩
  rcases CardEQ.exists_bijective hY with ⟨g, hg⟩
  let F : V → V := fun p ↦ kpair (f ‘ (kpair.π₁ p)) (g ‘ (kpair.π₂ p))
  have hFdef : ℒₛₑₜ-function₁[V] F := by
    letI : ℒₛₑₜ-function₁[V] kpair.π₁ := kpair.π₁.definable
    letI : ℒₛₑₜ-function₁[V] kpair.π₂ := kpair.π₂.definable
    letI : ℒₛₑₜ-function₂[V] value := value.definable
    letI : ℒₛₑₜ-function₂[V] kpair := kpair.definable
    change ℒₛₑₜ-function₁[V] (fun p ↦ kpair (value f (kpair.π₁ p)) (value g (kpair.π₂ p)))
    definability
  have hF : ∀ p ∈ X ×ˢ Y, F p ∈ X' ×ˢ Y' := by
    intro p hp
    rcases mem_prod_iff.mp hp with ⟨x, hxX, y, hyY, rfl⟩
    rcases exists_of_mem_function hf.mem_function x hxX with ⟨x', hx'X, hxx'⟩
    rcases exists_of_mem_function hg.mem_function y hyY with ⟨y', hy'Y, hyy'⟩
    have hfx : f ‘ x = x' := value_eq_of_kpair_mem hf.mem_function hxx'
    have hgy : g ‘ y = y' := value_eq_of_kpair_mem hg.mem_function hyy'
    simpa [F, hfx, hgy, mem_prod_iff] using And.intro hx'X hy'Y
  rcases graph_exists_mem_function_of_definableFunction (X ×ˢ Y) (X' ×ˢ Y') F hFdef hF with
    ⟨h, hhFun, hhGraph⟩
  have hhInj : Injective h := by
    intro p₁ p₂ q hp₁ hp₂
    rcases mem_prod_iff.mp (mem_of_mem_functions hhFun hp₁).1 with ⟨x₁, hx₁X, y₁, hy₁Y, rfl⟩
    rcases mem_prod_iff.mp (mem_of_mem_functions hhFun hp₂).1 with ⟨x₂, hx₂X, y₂, hy₂Y, rfl⟩
    have hq₁ : q = ⟨f ‘ x₁, g ‘ y₁⟩ₖ := by
      simpa [F] using (hhGraph ⟨x₁, y₁⟩ₖ (by simpa [mem_prod_iff] using And.intro hx₁X hy₁Y) q).1 hp₁
    have hq₂ : q = ⟨f ‘ x₂, g ‘ y₂⟩ₖ := by
      simpa [F] using (hhGraph ⟨x₂, y₂⟩ₖ (by simpa [mem_prod_iff] using And.intro hx₂X hy₂Y) q).1 hp₂
    have hqEq : ⟨f ‘ x₁, g ‘ y₁⟩ₖ = ⟨f ‘ x₂, g ‘ y₂⟩ₖ := hq₁.symm.trans hq₂
    rcases kpair_inj hqEq with ⟨hfx, hgy⟩
    letI : IsFunction f := IsFunction.of_mem hf.mem_function
    letI : IsFunction g := IsFunction.of_mem hg.mem_function
    have hx₁dom : x₁ ∈ domain f := by simpa [domain_eq_of_mem_function hf.mem_function] using hx₁X
    have hx₂dom : x₂ ∈ domain f := by simpa [domain_eq_of_mem_function hf.mem_function] using hx₂X
    have hy₁dom : y₁ ∈ domain g := by simpa [domain_eq_of_mem_function hg.mem_function] using hy₁Y
    have hy₂dom : y₂ ∈ domain g := by simpa [domain_eq_of_mem_function hg.mem_function] using hy₂Y
    have hx₁pair : ⟨x₁, f ‘ x₁⟩ₖ ∈ f :=
      (IsFunction.value_eq_iff_kpair_mem (f := f) (x := x₁) (y := f ‘ x₁) hx₁dom).mp rfl
    have hx₂pair : ⟨x₂, f ‘ x₂⟩ₖ ∈ f :=
      (IsFunction.value_eq_iff_kpair_mem (f := f) (x := x₂) (y := f ‘ x₂) hx₂dom).mp rfl
    have hy₁pair : ⟨y₁, g ‘ y₁⟩ₖ ∈ g :=
      (IsFunction.value_eq_iff_kpair_mem (f := g) (x := y₁) (y := g ‘ y₁) hy₁dom).mp rfl
    have hy₂pair : ⟨y₂, g ‘ y₂⟩ₖ ∈ g :=
      (IsFunction.value_eq_iff_kpair_mem (f := g) (x := y₂) (y := g ‘ y₂) hy₂dom).mp rfl
    have hx₂pair' : ⟨x₂, f ‘ x₁⟩ₖ ∈ f := by simpa [hfx] using hx₂pair
    have hy₂pair' : ⟨y₂, g ‘ y₁⟩ₖ ∈ g := by simpa [hgy] using hy₂pair
    have hxx : x₁ = x₂ := hf.injective _ _ _ hx₁pair hx₂pair'
    have hyy : y₁ = y₂ := hg.injective _ _ _ hy₁pair hy₂pair'
    simp [hxx, hyy]
  have hhRange : range h = X' ×ˢ Y' := by
    apply subset_antisymm
    · exact range_subset_of_mem_function hhFun
    · intro q hq
      rcases mem_prod_iff.mp hq with ⟨x', hx'X, y', hy'Y, rfl⟩
      have hx'Rf : x' ∈ range f := by simpa [hf.range_eq] using hx'X
      have hy'Rg : y' ∈ range g := by simpa [hg.range_eq] using hy'Y
      rcases mem_range_iff.mp hx'Rf with ⟨x, hxx'⟩
      rcases mem_range_iff.mp hy'Rg with ⟨y, hyy'⟩
      have hxX : x ∈ X := (mem_of_mem_functions hf.mem_function hxx').1
      have hyY : y ∈ Y := (mem_of_mem_functions hg.mem_function hyy').1
      have hfx : f ‘ x = x' := value_eq_of_kpair_mem hf.mem_function hxx'
      have hgy : g ‘ y = y' := value_eq_of_kpair_mem hg.mem_function hyy'
      refine mem_range_iff.mpr ⟨⟨x, y⟩ₖ, ?_⟩
      exact (hhGraph ⟨x, y⟩ₖ (by simpa [mem_prod_iff] using And.intro hxX hyY) ⟨x', y'⟩ₖ).2 <| by
        simp [F, hfx, hgy]
  exact CardEQ.of_bijective ⟨hhFun, hhInj, hhRange⟩

lemma Bijective.isOrderIso_empty {f X Y : V} (h : Bijective f X Y) :
    IsOrderIso (∅ : V) X (∅ : V) Y f := by
  refine ⟨h.mem_function, h.injective, h.range_eq, ?_⟩
  intro x₁ hx₁ x₂ hx₂
  simp

lemma CardEQ.tagProd {X i : V} :
    X ≋ (X ×ˢ {i}) := by
  rcases taggedRel_isOrderIso (R := (∅ : V)) (X := X) (i := i) with ⟨f, hf, _⟩
  exact CardEQ.of_bijective (IsOrderIso.bijective hf)

lemma prod_singleton_inter_prod_singleton_eq_empty_of_ne {X Y i j : V}
    (hij : i ≠ j) :
    (X ×ˢ ({i} : V)) ∩ (Y ×ˢ ({j} : V)) = ∅ := by
  rw [← isEmpty_iff_eq_empty]
  intro p hp
  rcases mem_inter_iff.mp hp with ⟨hpXi, hpYj⟩
  rcases show ∃ x ∈ X, ∃ i' ∈ ({i} : V), p = ⟨x, i'⟩ₖ from by
      simpa [mem_prod_iff] using hpXi with ⟨x, hxX, i', hi', hpEq⟩
  rcases show ∃ y ∈ Y, ∃ j' ∈ ({j} : V), p = ⟨y, j'⟩ₖ from by
      simpa [mem_prod_iff] using hpYj with ⟨y, hyY, j', hj', hpEq'⟩
  have hi : i' = i := by simpa using hi'
  have hj : j' = j := by simpa using hj'
  subst hi
  subst hj
  exact hij ((kpair_inj (hpEq.symm.trans hpEq')).2)

lemma prod_inter_prod_eq_empty_of_left_disjoint {A B C : V}
    (hAB : A ∩ B = ∅) :
    (A ×ˢ C) ∩ (B ×ˢ C) = ∅ := by
  rw [← isEmpty_iff_eq_empty]
  intro p hp
  rcases mem_inter_iff.mp hp with ⟨hpAC, hpBC⟩
  rcases show ∃ a ∈ A, ∃ c₁ ∈ C, p = ⟨a, c₁⟩ₖ from by
      simpa [mem_prod_iff] using hpAC with ⟨a, haA, c₁, hc₁C, hpa⟩
  rcases show ∃ b ∈ B, ∃ c₂ ∈ C, p = ⟨b, c₂⟩ₖ from by
      simpa [mem_prod_iff] using hpBC with ⟨b, hbB, c₂, hc₂C, hpb⟩
  have hab : a = b := (kpair_inj (hpa.symm.trans hpb)).1
  have haAB : a ∈ A ∩ B := mem_inter_iff.mpr ⟨haA, by simpa [hab] using hbB⟩
  have haEmpty : a ∈ (∅ : V) := by simp [hAB] at haAB
  exact (not_mem_empty haEmpty).elim

lemma prod_inter_prod_eq_empty_of_right_disjoint {A B C : V}
    (hBC : B ∩ C = ∅) :
    (A ×ˢ B) ∩ (A ×ˢ C) = ∅ := by
  rw [← isEmpty_iff_eq_empty]
  intro p hp
  rcases mem_inter_iff.mp hp with ⟨hpAB, hpAC⟩
  rcases show ∃ a₁ ∈ A, ∃ b ∈ B, p = ⟨a₁, b⟩ₖ from by
      simpa [mem_prod_iff] using hpAB with ⟨a₁, ha₁A, b, hbB, hpb⟩
  rcases show ∃ a₂ ∈ A, ∃ c ∈ C, p = ⟨a₂, c⟩ₖ from by
      simpa [mem_prod_iff] using hpAC with ⟨a₂, ha₂A, c, hcC, hpc⟩
  have hbc : b = c := (kpair_inj (hpb.symm.trans hpc)).2
  have hbBC : b ∈ B ∩ C := mem_inter_iff.mpr ⟨hbB, by simpa [hbc] using hcC⟩
  have hbEmpty : b ∈ (∅ : V) := by simp [hBC] at hbBC
  exact (not_mem_empty hbEmpty).elim

lemma orderedUnionCarrier_inter_eq_empty_of_inter_eq_empty {A B C : V}
    (hAC : A ∩ C = ∅)
    (hBC : B ∩ C = ∅) :
    orderedUnionCarrier A B ∩ C = ∅ := by
  rw [← isEmpty_iff_eq_empty]
  intro p hp
  rcases mem_inter_iff.mp hp with ⟨hpAB, hpC⟩
  rcases mem_orderedUnionCarrier_iff.mp hpAB with (hpA | hpB)
  · have hpAC : p ∈ A ∩ C := mem_inter_iff.mpr ⟨hpA, hpC⟩
    have hpEmpty : p ∈ (∅ : V) := by simp [hAC] at hpAC
    exact (not_mem_empty hpEmpty).elim
  · have hpBC : p ∈ B ∩ C := mem_inter_iff.mpr ⟨hpB, hpC⟩
    have hpEmpty : p ∈ (∅ : V) := by simp [hBC] at hpBC
    exact (not_mem_empty hpEmpty).elim

lemma CardEQ.orderedUnionCarrier
    [V ⊧ₘ* 𝗭𝗙]
    {X X' Y Y' : V}
    (hXY : X ∩ Y = ∅)
    (hX'Y' : X' ∩ Y' = ∅)
    (hX : X ≋ X') (hY : Y ≋ Y') :
    orderedUnionCarrier X Y ≋ orderedUnionCarrier X' Y' := by
  rcases CardEQ.exists_bijective hX with ⟨f, hf⟩
  rcases CardEQ.exists_bijective hY with ⟨g, hg⟩
  have hfIso : IsOrderIso (∅ : V) X (∅ : V) X' f := hf.isOrderIso_empty
  have hgIso : IsOrderIso (∅ : V) Y (∅ : V) Y' g := hg.isOrderIso_empty
  exact CardEQ.of_bijective <| IsOrderIso.bijective <|
    orderedUnionRel_isOrderIso_of_componentIsos hXY hX'Y' hfIso hgIso

lemma CardEQ.orderSumCarrier
    [V ⊧ₘ* 𝗭𝗙]
    {X X' Y Y' : V}
    (hX : X ≋ X') (hY : Y ≋ Y') :
    orderSumCarrier X Y ≋ orderSumCarrier X' Y' := by
  have hLeft : (X ×ˢ ({0} : V)) ∩ (Y ×ˢ ({1} : V)) = ∅ :=
    prod_singleton_inter_prod_singleton_eq_empty_of_ne (X := X) (Y := Y) zero_ne_one
  have hRight : (X' ×ˢ ({0} : V)) ∩ (Y' ×ˢ ({1} : V)) = ∅ :=
    prod_singleton_inter_prod_singleton_eq_empty_of_ne (X := X') (Y := Y') zero_ne_one
  have hX0 : (X ×ˢ ({0} : V)) ≋ (X' ×ˢ ({0} : V)) :=
    CardEQ.prod (V := V) hX (CardEQ.refl ({0} : V))
  have hY1 : (Y ×ˢ ({1} : V)) ≋ (Y' ×ˢ ({1} : V)) :=
    CardEQ.prod (V := V) hY (CardEQ.refl ({1} : V))
  simpa [orderSumCarrier, orderedUnionCarrier] using
    (CardEQ.orderedUnionCarrier (V := V) hLeft hRight hX0 hY1)

lemma prod_cardEQ_comm {X Y : V} :
    (X ×ˢ Y) ≋ (Y ×ˢ X) := by
  let f : V := {p ∈ (X ×ˢ Y) ×ˢ (Y ×ˢ X) ;
    ∃ x ∈ X, ∃ y ∈ Y, p = ⟨⟨x, y⟩ₖ, ⟨y, x⟩ₖ⟩ₖ}
  have hfFun : f ∈ (Y ×ˢ X) ^ (X ×ˢ Y) := by
    apply mem_function.intro
    · intro p hp
      exact (mem_sep_iff.mp hp).1
    · intro p hp
      rcases mem_prod_iff.mp hp with ⟨x, hxX, y, hyY, rfl⟩
      refine ExistsUnique.intro ⟨y, x⟩ₖ ?_ ?_
      · refine mem_sep_iff.mpr ?_
        refine ⟨?_, x, hxX, y, hyY, rfl⟩
        simpa [mem_prod_iff] using And.intro hp (And.intro hyY hxX)
      · intro q hq
        rcases mem_sep_iff.mp hq with ⟨-, x', hx'X, y', hy'Y, hpq⟩
        rcases kpair_inj hpq with ⟨hxy, hq⟩
        rcases kpair_inj hxy with ⟨rfl, rfl⟩
        simpa using hq
  have hfInj : Injective f := by
    intro p₁ p₂ q hp₁ hp₂
    rcases mem_sep_iff.mp hp₁ with ⟨-, x₁, hx₁X, y₁, hy₁Y, hp₁eq⟩
    rcases mem_sep_iff.mp hp₂ with ⟨-, x₂, hx₂X, y₂, hy₂Y, hp₂eq⟩
    rcases kpair_inj hp₁eq with ⟨hp₁dom, hq₁⟩
    rcases kpair_inj hp₂eq with ⟨hp₂dom, hq₂⟩
    have hq : ⟨y₁, x₁⟩ₖ = ⟨y₂, x₂⟩ₖ := hq₁.symm.trans hq₂
    rcases kpair_inj hq with ⟨hy, hx⟩
    simp [hp₁dom, hp₂dom, hx, hy]
  have hfRange : range f = Y ×ˢ X := by
    apply subset_antisymm
    · exact range_subset_of_mem_function hfFun
    · intro q hq
      rcases mem_prod_iff.mp hq with ⟨y, hyY, x, hxX, rfl⟩
      refine mem_range_iff.mpr ⟨⟨x, y⟩ₖ, ?_⟩
      refine mem_sep_iff.mpr ?_
      refine ⟨?_, x, hxX, y, hyY, rfl⟩
      simpa [mem_prod_iff] using And.intro (And.intro hxX hyY) hq
  exact CardEQ.of_bijective ⟨hfFun, hfInj, hfRange⟩

lemma prod_cardEQ_assoc {X Y Z : V} :
    ((X ×ˢ Y) ×ˢ Z) ≋ (X ×ˢ (Y ×ˢ Z)) := by
  let f : V := {p ∈ ((X ×ˢ Y) ×ˢ Z) ×ˢ (X ×ˢ (Y ×ˢ Z)) ;
    ∃ x ∈ X, ∃ y ∈ Y, ∃ z ∈ Z, p = ⟨⟨⟨x, y⟩ₖ, z⟩ₖ, ⟨x, ⟨y, z⟩ₖ⟩ₖ⟩ₖ}
  have hfFun : f ∈ (X ×ˢ (Y ×ˢ Z)) ^ ((X ×ˢ Y) ×ˢ Z) := by
    apply mem_function.intro
    · intro p hp
      exact (mem_sep_iff.mp hp).1
    · intro p hp
      rcases mem_prod_iff.mp hp with ⟨xy, hxy, z, hzZ, rfl⟩
      rcases mem_prod_iff.mp hxy with ⟨x, hxX, y, hyY, rfl⟩
      refine ExistsUnique.intro ⟨x, ⟨y, z⟩ₖ⟩ₖ ?_ ?_
      · refine mem_sep_iff.mpr ?_
        refine ⟨?_, x, hxX, y, hyY, z, hzZ, rfl⟩
        have hyz : ⟨y, z⟩ₖ ∈ Y ×ˢ Z := by simpa [mem_prod_iff] using And.intro hyY hzZ
        simpa [mem_prod_iff] using And.intro hp (And.intro hxX hyz)
      · intro q hq
        rcases mem_sep_iff.mp hq with ⟨-, x', hx'X, y', hy'Y, z', hz'Z, hpq⟩
        rcases kpair_inj hpq with ⟨hdom, hqEq⟩
        rcases kpair_inj hdom with ⟨hxy, hz⟩
        rcases kpair_inj hxy with ⟨hx, hy⟩
        simpa [hx, hy, hz] using hqEq
  have hfInj : Injective f := by
    intro p₁ p₂ q hp₁ hp₂
    rcases mem_sep_iff.mp hp₁ with ⟨-, x₁, hx₁X, y₁, hy₁Y, z₁, hz₁Z, hp₁eq⟩
    rcases mem_sep_iff.mp hp₂ with ⟨-, x₂, hx₂X, y₂, hy₂Y, z₂, hz₂Z, hp₂eq⟩
    rcases kpair_inj hp₁eq with ⟨hp₁dom, hq₁⟩
    rcases kpair_inj hp₂eq with ⟨hp₂dom, hq₂⟩
    have hq : ⟨x₁, ⟨y₁, z₁⟩ₖ⟩ₖ = ⟨x₂, ⟨y₂, z₂⟩ₖ⟩ₖ := hq₁.symm.trans hq₂
    rcases kpair_inj hq with ⟨hx, hyz⟩
    rcases kpair_inj hyz with ⟨hy, hz⟩
    simp [hp₁dom, hp₂dom, hx, hy, hz]
  have hfRange : range f = X ×ˢ (Y ×ˢ Z) := by
    apply subset_antisymm
    · exact range_subset_of_mem_function hfFun
    · intro q hq
      rcases mem_prod_iff.mp hq with ⟨x, hxX, yz, hyz, rfl⟩
      rcases mem_prod_iff.mp hyz with ⟨y, hyY, z, hzZ, rfl⟩
      refine mem_range_iff.mpr ⟨⟨⟨x, y⟩ₖ, z⟩ₖ, ?_⟩
      refine mem_sep_iff.mpr ?_
      have hxy : ⟨x, y⟩ₖ ∈ X ×ˢ Y := by simpa [mem_prod_iff] using And.intro hxX hyY
      have hp : ⟨⟨x, y⟩ₖ, z⟩ₖ ∈ (X ×ˢ Y) ×ˢ Z := by simpa [mem_prod_iff] using And.intro hxy hzZ
      refine ⟨?_, x, hxX, y, hyY, z, hzZ, rfl⟩
      simpa [mem_prod_iff] using And.intro hp hq
  exact CardEQ.of_bijective ⟨hfFun, hfInj, hfRange⟩

lemma orderSumCarrier_cardEQ_comm [V ⊧ₘ* 𝗭𝗙] {X Y : V} :
    orderSumCarrier X Y ≋ orderSumCarrier Y X := by
  have hLeft : (X ×ˢ ({0} : V)) ∩ (Y ×ˢ ({1} : V)) = ∅ :=
    prod_singleton_inter_prod_singleton_eq_empty_of_ne (X := X) (Y := Y) zero_ne_one
  have hRight : (X ×ˢ ({1} : V)) ∩ (Y ×ˢ ({0} : V)) = ∅ :=
    prod_singleton_inter_prod_singleton_eq_empty_of_ne (X := X) (Y := Y) one_ne_zero
  have hX : (X ×ˢ ({0} : V)) ≋ (X ×ˢ ({1} : V)) := by
    exact CardEQ.trans
      (CardEQ.symm (CardEQ.tagProd (X := X) (i := (0 : V))))
      (CardEQ.tagProd (X := X) (i := (1 : V)))
  have hY : (Y ×ˢ ({1} : V)) ≋ (Y ×ˢ ({0} : V)) := by
    exact CardEQ.trans
      (CardEQ.symm (CardEQ.tagProd (X := Y) (i := (1 : V))))
      (CardEQ.tagProd (X := Y) (i := (0 : V)))
  simpa [orderSumCarrier, orderedUnionCarrier, union_comm] using
    (CardEQ.orderedUnionCarrier (V := V) hLeft hRight hX hY)

lemma orderSumCarrier_cardEQ_assoc {X Y Z : V} :
    orderSumCarrier (orderSumCarrier X Y) Z ≋ orderSumCarrier X (orderSumCarrier Y Z) := by
  let f : V := {p ∈ orderSumCarrier (orderSumCarrier X Y) Z ×ˢ orderSumCarrier X (orderSumCarrier Y Z) ;
    (∃ x ∈ X, p = ⟨⟨⟨x, 0⟩ₖ, 0⟩ₖ, ⟨x, 0⟩ₖ⟩ₖ) ∨
    (∃ y ∈ Y, p = ⟨⟨⟨y, 1⟩ₖ, 0⟩ₖ, ⟨⟨y, 0⟩ₖ, 1⟩ₖ⟩ₖ) ∨
    (∃ z ∈ Z, p = ⟨⟨z, 1⟩ₖ, ⟨⟨z, 1⟩ₖ, 1⟩ₖ⟩ₖ)}
  have hfFun : f ∈ orderSumCarrier X (orderSumCarrier Y Z) ^ orderSumCarrier (orderSumCarrier X Y) Z := by
    apply mem_function.intro
    · intro p hp
      exact (mem_sep_iff.mp hp).1
    · intro p hp
      rcases mem_orderSumCarrier_cases hp with (⟨u, huXY, rfl⟩ | ⟨z, hzZ, rfl⟩)
      · rcases mem_orderSumCarrier_cases huXY with (⟨x, hxX, rfl⟩ | ⟨y, hyY, rfl⟩)
        · refine ExistsUnique.intro ⟨x, 0⟩ₖ ?_ ?_
          · refine mem_sep_iff.mpr ?_
            refine ⟨?_, Or.inl ⟨x, hxX, rfl⟩⟩
            simp [mem_prod_iff, mem_orderSumCarrier_iff, hxX]
          · intro q hq
            rcases mem_sep_iff.mp hq with ⟨-, hq | hq | hq⟩
            · rcases hq with ⟨x', hx'X, hpq⟩
              rcases kpair_inj hpq with ⟨hdom, hqEq⟩
              rcases kpair_inj hdom with ⟨hxy, h00⟩
              rcases kpair_inj hxy with ⟨rfl, h00'⟩
              have : (0 : V) = 0 := h00
              have : (0 : V) = 0 := h00'
              simpa using hqEq
            · rcases hq with ⟨y', hy'Y, hpq⟩
              rcases kpair_inj hpq with ⟨hdom, _⟩
              rcases kpair_inj hdom with ⟨hxy, _⟩
              exact False.elim <| zero_ne_one ((kpair_inj hxy).2)
            · rcases hq with ⟨z', hz'Z, hpq⟩
              rcases kpair_inj hpq with ⟨hdom, _⟩
              exact False.elim <| zero_ne_one ((kpair_inj hdom).2)
        · refine ExistsUnique.intro ⟨⟨y, 0⟩ₖ, 1⟩ₖ ?_ ?_
          · refine mem_sep_iff.mpr ?_
            refine ⟨?_, Or.inr <| Or.inl ⟨y, hyY, rfl⟩⟩
            simp [mem_prod_iff, mem_orderSumCarrier_iff, hyY]
          · intro q hq
            rcases mem_sep_iff.mp hq with ⟨-, hq | hq | hq⟩
            · rcases hq with ⟨x', hx'X, hpq⟩
              rcases kpair_inj hpq with ⟨hdom, _⟩
              rcases kpair_inj hdom with ⟨hxy, _⟩
              exact False.elim <| one_ne_zero ((kpair_inj hxy).2)
            · rcases hq with ⟨y', hy'Y, hpq⟩
              rcases kpair_inj hpq with ⟨hdom, hqEq⟩
              rcases kpair_inj hdom with ⟨hyy, h00⟩
              rcases kpair_inj hyy with ⟨rfl, h11⟩
              have : (0 : V) = 0 := h00
              have : (1 : V) = 1 := h11
              simpa using hqEq
            · rcases hq with ⟨z', hz'Z, hpq⟩
              rcases kpair_inj hpq with ⟨hdom, _⟩
              exact False.elim <| zero_ne_one ((kpair_inj hdom).2)
      · refine ExistsUnique.intro ⟨⟨z, 1⟩ₖ, 1⟩ₖ ?_ ?_
        · refine mem_sep_iff.mpr ?_
          refine ⟨?_, Or.inr <| Or.inr ⟨z, hzZ, rfl⟩⟩
          simp [mem_prod_iff, mem_orderSumCarrier_iff, hzZ]
        · intro q hq
          rcases mem_sep_iff.mp hq with ⟨-, hq | hq | hq⟩
          · rcases hq with ⟨x', hx'X, hpq⟩
            rcases kpair_inj hpq with ⟨hdom, _⟩
            exact False.elim <| one_ne_zero ((kpair_inj hdom).2)
          · rcases hq with ⟨y', hy'Y, hpq⟩
            rcases kpair_inj hpq with ⟨hdom, _⟩
            exact False.elim <| one_ne_zero ((kpair_inj hdom).2)
          · rcases hq with ⟨z', hz'Z, hpq⟩
            rcases kpair_inj hpq with ⟨hz, hqEq⟩
            subst hqEq
            rcases kpair_inj hz with ⟨rfl, _⟩
            rfl
  have hfInj : Injective f := by
    intro p₁ p₂ q hp₁ hp₂
    rcases mem_sep_iff.mp hp₁ with ⟨-, hp₁ | hp₁ | hp₁⟩
    · rcases hp₁ with ⟨x₁, hx₁X, hp₁eq⟩
      rcases kpair_inj hp₁eq with ⟨hp₁dom, hq₁⟩
      subst hp₁dom; subst hq₁
      rcases mem_sep_iff.mp hp₂ with ⟨-, hp₂ | hp₂ | hp₂⟩
      · rcases hp₂ with ⟨x₂, hx₂X, hpq⟩
        rcases kpair_inj hpq with ⟨hp₂dom, hq₂⟩
        rcases kpair_inj hq₂ with ⟨hx, _⟩
        subst hx; subst hp₂dom
        rfl
      · rcases hp₂ with ⟨y₂, hy₂Y, hpq⟩
        rcases kpair_inj hpq with ⟨_, hq₂⟩
        exact False.elim <| zero_ne_one ((kpair_inj hq₂).2)
      · rcases hp₂ with ⟨z₂, hz₂Z, hpq⟩
        rcases kpair_inj hpq with ⟨_, hq₂⟩
        exact False.elim <| zero_ne_one ((kpair_inj hq₂).2)
    · rcases hp₁ with ⟨y₁, hy₁Y, hp₁eq⟩
      rcases kpair_inj hp₁eq with ⟨hp₁dom, hq₁⟩
      subst hp₁dom; subst hq₁
      rcases mem_sep_iff.mp hp₂ with ⟨-, hp₂ | hp₂ | hp₂⟩
      · rcases hp₂ with ⟨x₂, hx₂X, hpq⟩
        rcases kpair_inj hpq with ⟨_, hq₂⟩
        exact False.elim <| one_ne_zero ((kpair_inj hq₂).2)
      · rcases hp₂ with ⟨y₂, hy₂Y, hpq⟩
        rcases kpair_inj hpq with ⟨hp₂dom, hq₂⟩
        rcases kpair_inj hq₂ with ⟨hy0, _⟩
        rcases kpair_inj hy0 with ⟨hy, _⟩
        subst hy; subst hp₂dom
        rfl
      · rcases hp₂ with ⟨z₂, hz₂Z, hpq⟩
        rcases kpair_inj hpq with ⟨_, hq₂⟩
        rcases kpair_inj hq₂ with ⟨hzy, _⟩
        exact False.elim <| zero_ne_one ((kpair_inj hzy).2)
    · rcases hp₁ with ⟨z₁, hz₁Z, hp₁eq⟩
      rcases kpair_inj hp₁eq with ⟨hp₁dom, hq₁⟩
      subst hp₁dom; subst hq₁
      rcases mem_sep_iff.mp hp₂ with ⟨-, hp₂ | hp₂ | hp₂⟩
      · rcases hp₂ with ⟨x₂, hx₂X, hpq⟩
        rcases kpair_inj hpq with ⟨_, hq₂⟩
        exact False.elim <| one_ne_zero ((kpair_inj hq₂).2)
      · rcases hp₂ with ⟨y₂, hy₂Y, hpq⟩
        rcases kpair_inj hpq with ⟨_, hq₂⟩
        rcases kpair_inj hq₂ with ⟨hzy, _⟩
        exact False.elim <| one_ne_zero ((kpair_inj hzy).2)
      · rcases hp₂ with ⟨z₂, hz₂Z, hpq⟩
        rcases kpair_inj hpq with ⟨hp₂dom, hq₂⟩
        rcases kpair_inj hq₂ with ⟨hz1, _⟩
        rcases kpair_inj hz1 with ⟨hz, _⟩
        subst hz; subst hp₂dom
        rfl
  have hfRange : range f = orderSumCarrier X (orderSumCarrier Y Z) := by
    apply subset_antisymm
    · exact range_subset_of_mem_function hfFun
    · intro q hq
      rcases mem_orderSumCarrier_cases hq with (⟨x, hxX, rfl⟩ | ⟨u, huYZ, rfl⟩)
      · refine mem_range_iff.mpr ⟨⟨⟨x, 0⟩ₖ, 0⟩ₖ, ?_⟩
        refine mem_sep_iff.mpr ?_
        refine ⟨?_, Or.inl ⟨x, hxX, rfl⟩⟩
        simp [mem_prod_iff, mem_orderSumCarrier_iff, hxX]
      · rcases mem_orderSumCarrier_cases huYZ with (⟨y, hyY, rfl⟩ | ⟨z, hzZ, rfl⟩)
        · refine mem_range_iff.mpr ⟨⟨⟨y, 1⟩ₖ, 0⟩ₖ, ?_⟩
          refine mem_sep_iff.mpr ?_
          refine ⟨?_, Or.inr <| Or.inl ⟨y, hyY, rfl⟩⟩
          simp [mem_prod_iff, mem_orderSumCarrier_iff, hyY]
        · refine mem_range_iff.mpr ⟨⟨z, 1⟩ₖ, ?_⟩
          refine mem_sep_iff.mpr ?_
          refine ⟨?_, Or.inr <| Or.inr ⟨z, hzZ, rfl⟩⟩
          simp [mem_prod_iff, mem_orderSumCarrier_iff, hzZ]
  exact CardEQ.of_bijective ⟨hfFun, hfInj, hfRange⟩

lemma prod_orderSumCarrier_cardEQ_distrib {X Y Z : V} :
    (X ×ˢ orderSumCarrier Y Z) ≋ (orderSumCarrier (X ×ˢ Y) (X ×ˢ Z)) := by
  let f : V := {p ∈ (X ×ˢ orderSumCarrier Y Z) ×ˢ orderSumCarrier (X ×ˢ Y) (X ×ˢ Z) ;
    (∃ x ∈ X, ∃ y ∈ Y, p = ⟨⟨x, ⟨y, 0⟩ₖ⟩ₖ, ⟨⟨x, y⟩ₖ, 0⟩ₖ⟩ₖ) ∨
    (∃ x ∈ X, ∃ z ∈ Z, p = ⟨⟨x, ⟨z, 1⟩ₖ⟩ₖ, ⟨⟨x, z⟩ₖ, 1⟩ₖ⟩ₖ)}
  have hfFun : f ∈ orderSumCarrier (X ×ˢ Y) (X ×ˢ Z) ^ (X ×ˢ orderSumCarrier Y Z) := by
    apply mem_function.intro
    · intro p hp
      exact (mem_sep_iff.mp hp).1
    · intro p hp
      rcases mem_prod_iff.mp hp with ⟨x, hxX, u, huYZ, rfl⟩
      rcases mem_orderSumCarrier_cases huYZ with (⟨y, hyY, rfl⟩ | ⟨z, hzZ, rfl⟩)
      · refine ExistsUnique.intro ⟨⟨x, y⟩ₖ, 0⟩ₖ ?_ ?_
        · refine mem_sep_iff.mpr ?_
          refine ⟨?_, Or.inl ⟨x, hxX, y, hyY, rfl⟩⟩
          simp [mem_prod_iff, mem_orderSumCarrier_iff, hxX, hyY]
        · intro q hq
          rcases mem_sep_iff.mp hq with ⟨-, hq | hq⟩
          · rcases hq with ⟨x', hx'X, y', hy'Y, hpq⟩
            rcases kpair_inj hpq with ⟨hdom, hqEq⟩
            rcases kpair_inj hdom with ⟨hx, hy0⟩
            rcases kpair_inj hy0 with ⟨hy, h00⟩
            rw [hx, hy]
            exact hqEq
          · rcases hq with ⟨x', hx'X, z', hz'Z, hpq⟩
            rcases kpair_inj hpq with ⟨hdom, _⟩
            rcases kpair_inj hdom with ⟨hx, hy1⟩
            rcases kpair_inj hy1 with ⟨-, h01⟩
            exact False.elim <| zero_ne_one h01
      · refine ExistsUnique.intro ⟨⟨x, z⟩ₖ, 1⟩ₖ ?_ ?_
        · refine mem_sep_iff.mpr ?_
          refine ⟨?_, Or.inr ⟨x, hxX, z, hzZ, rfl⟩⟩
          simp [mem_prod_iff, mem_orderSumCarrier_iff, hxX, hzZ]
        · intro q hq
          rcases mem_sep_iff.mp hq with ⟨-, hq | hq⟩
          · rcases hq with ⟨x', hx'X, y', hy'Y, hpq⟩
            rcases kpair_inj hpq with ⟨hdom, _⟩
            rcases kpair_inj hdom with ⟨hx, hz0⟩
            rcases kpair_inj hz0 with ⟨-, h10⟩
            exact False.elim <| one_ne_zero h10
          · rcases hq with ⟨x', hx'X, z', hz'Z, hpq⟩
            rcases kpair_inj hpq with ⟨hdom, hqEq⟩
            subst hqEq
            rcases kpair_inj hdom with ⟨hx, hz1⟩
            rcases kpair_inj hz1 with ⟨hz, _⟩
            subst hx; subst hz
            rfl
  have hfInj : Injective f := by
    intro p₁ p₂ q hp₁ hp₂
    rcases mem_sep_iff.mp hp₁ with ⟨-, hp₁ | hp₁⟩
    · rcases hp₁ with ⟨x₁, hx₁X, y₁, hy₁Y, hp₁eq⟩
      rcases kpair_inj hp₁eq with ⟨hp₁dom, hq₁⟩
      subst hp₁dom; subst hq₁
      rcases mem_sep_iff.mp hp₂ with ⟨-, hp₂ | hp₂⟩
      · rcases hp₂ with ⟨x₂, hx₂X, y₂, hy₂Y, hpq⟩
        rcases kpair_inj hpq with ⟨hp₂dom, hq₂⟩
        subst hp₂dom
        rcases kpair_inj hq₂ with ⟨hxy, _⟩
        rcases kpair_inj hxy with ⟨hx, hy⟩
        subst hx; subst hy
        rfl
      · rcases hp₂ with ⟨x₂, hx₂X, z₂, hz₂Z, hpq⟩
        rcases kpair_inj hpq with ⟨hp₂dom, hq₂⟩
        subst hp₂dom
        exact (zero_ne_one (kpair_inj hq₂).2).elim
    · rcases hp₁ with ⟨x₁, hx₁X, z₁, hz₁Z, hp₁eq⟩
      rcases kpair_inj hp₁eq with ⟨hp₁dom, hq₁⟩
      subst hp₁dom; subst hq₁
      rcases mem_sep_iff.mp hp₂ with ⟨-, hp₂ | hp₂⟩
      · rcases hp₂ with ⟨x₂, hx₂X, y₂, hy₂Y, hpq⟩
        rcases kpair_inj hpq with ⟨hp₂dom, hq₂⟩
        subst hp₂dom
        exact (zero_ne_one (kpair_inj hq₂).2.symm).elim
      · rcases hp₂ with ⟨x₂, hx₂X, z₂, hz₂Z, hpq⟩
        rcases kpair_inj hpq with ⟨hp₂dom, hq₂⟩
        subst hp₂dom
        rcases kpair_inj hq₂ with ⟨hxz, _⟩
        rcases kpair_inj hxz with ⟨hx, hz⟩
        subst hx; subst hz
        rfl
  have hfRange : range f = orderSumCarrier (X ×ˢ Y) (X ×ˢ Z) := by
    apply subset_antisymm
    · exact range_subset_of_mem_function hfFun
    · intro q hq
      rcases mem_orderSumCarrier_cases hq with (⟨xy, hxy, rfl⟩ | ⟨xz, hxz, rfl⟩)
      · rcases mem_prod_iff.mp hxy with ⟨x, hxX, y, hyY, rfl⟩
        refine mem_range_iff.mpr ⟨⟨x, ⟨y, 0⟩ₖ⟩ₖ, ?_⟩
        refine mem_sep_iff.mpr ?_
        have hy0 : ⟨y, 0⟩ₖ ∈ orderSumCarrier Y Z := by simp [mem_orderSumCarrier_iff, hyY]
        have hp : ⟨x, ⟨y, 0⟩ₖ⟩ₖ ∈ X ×ˢ orderSumCarrier Y Z := by
          simpa [mem_prod_iff] using And.intro hxX hy0
        refine ⟨?_, Or.inl ⟨x, hxX, y, hyY, rfl⟩⟩
        simpa [mem_prod_iff] using And.intro hp hq
      · rcases mem_prod_iff.mp hxz with ⟨x, hxX, z, hzZ, rfl⟩
        refine mem_range_iff.mpr ⟨⟨x, ⟨z, 1⟩ₖ⟩ₖ, ?_⟩
        refine mem_sep_iff.mpr ?_
        have hz1 : ⟨z, 1⟩ₖ ∈ orderSumCarrier Y Z := by simp [mem_orderSumCarrier_iff, hzZ]
        have hp : ⟨x, ⟨z, 1⟩ₖ⟩ₖ ∈ X ×ˢ orderSumCarrier Y Z := by
          simpa [mem_prod_iff] using And.intro hxX hz1
        refine ⟨?_, Or.inr ⟨x, hxX, z, hzZ, rfl⟩⟩
        simpa [mem_prod_iff] using And.intro hp hq
  exact CardEQ.of_bijective ⟨hfFun, hfInj, hfRange⟩

lemma succ_sdiff_singleton_cardEQ_of_mem_ω
    {α β : V}
    (hαω : α ∈ (ω : V))
    (hβ : β ∈ succ α) :
    succ α \ {β} ≋ α := by
  classical
  letI : IsOrdinal α := IsOrdinal.nat hαω
  letI : IsOrdinal (succ α) := IsOrdinal.succ (α := α)
  have hαord : IsOrdinal α := inferInstance
  have hβord : IsOrdinal β := IsOrdinal.of_mem hβ
  letI : IsOrdinal β := hβord
  have hsuccαω : succ α ∈ (ω : V) := ω_succ_closed hαω
  have hβsubα : β ⊆ α := by
    rcases mem_succ_iff.mp hβ with (rfl | hβα)
    · simp
    · exact hαord.transitive β hβα
  let F : V → V := fun ξ ↦ if ξ ∈ β then ξ else succ ξ
  have hFdef : ℒₛₑₜ-function₁[V] F := by
    let R : (Fin 2 → V) → Prop := fun v ↦
      (v 1 ∈ β ∧ v 0 = v 1) ∨ (v 1 ∉ β ∧ v 0 = succ (v 1))
    have hR : Language.Definable (L := ℒₛₑₜ) (M := V) R := by
      change Language.Definable (L := ℒₛₑₜ) (M := V) (fun v : Fin 2 → V ↦
        (v 1 ∈ β ∧ v 0 = v 1) ∨ (v 1 ∉ β ∧ v 0 = succ (v 1)))
      definability
    change Language.Definable (L := ℒₛₑₜ) (M := V)
      (fun v : Fin 2 → V ↦ v 0 = if v 1 ∈ β then v 1 else succ (v 1))
    exact Language.Definable.of_iff (L := ℒₛₑₜ) hR <| by
      intro v
      by_cases hv : v 1 ∈ β <;> simp [R, hv]
  have hFmap : ∀ ξ ∈ α, F ξ ∈ succ α \ {β} := by
    intro ξ hξα
    have hξord : IsOrdinal ξ := hαord.of_mem hξα
    letI : IsOrdinal ξ := hξord
    by_cases hξβ : ξ ∈ β
    · have hξneβ : ξ ≠ β := ne_of_mem hξβ
      exact mem_sdiff_iff.mpr ⟨
        by simpa [F, hξβ, mem_succ_iff] using Or.inr hξα,
        by simpa [F, hξβ, mem_singleton_iff] using hξneβ⟩
    · have hsuccξsubα : succ ξ ⊆ α := IsOrdinal.succ_subset_of_mem hξα
      have hsuccξsα : succ ξ ∈ succ α := by
        have : succ ξ = α ∨ succ ξ ∈ α :=
          (IsOrdinal.subset_iff (α := succ ξ) (β := α)).1 hsuccξsubα
        simpa [mem_succ_iff] using this
      have hsuccξneβ : succ ξ ≠ β := by
        intro hEq
        exact hξβ (hEq.symm ▸ mem_succ_self ξ)
      exact mem_sdiff_iff.mpr ⟨
        by simpa [F, hξβ] using hsuccξsα,
        by simpa [F, hξβ, mem_singleton_iff] using hsuccξneβ⟩
  rcases graph_exists_mem_function_of_definableFunction
      α (succ α \ {β}) F hFdef hFmap with
    ⟨f, hfFun, hgraph⟩
  have hfInj : Injective f := by
    intro ξ₁ ξ₂ y hξ₁y hξ₂y
    have hξ₁α : ξ₁ ∈ α := (mem_of_mem_functions hfFun hξ₁y).1
    have hξ₂α : ξ₂ ∈ α := (mem_of_mem_functions hfFun hξ₂y).1
    have hy₁ : y = F ξ₁ := (hgraph ξ₁ hξ₁α y).1 hξ₁y
    have hy₂ : y = F ξ₂ := (hgraph ξ₂ hξ₂α y).1 hξ₂y
    by_cases hξ₁β : ξ₁ ∈ β
    · by_cases hξ₂β : ξ₂ ∈ β
      · simpa [F, hξ₁β, hξ₂β] using hy₁.symm.trans hy₂
      · have : ξ₂ ∈ β := by
          have hEq : ξ₁ = succ ξ₂ := by simpa [F, hξ₁β, hξ₂β] using hy₁.symm.trans hy₂
          exact hβord.transitive ξ₁ hξ₁β ξ₂ (hEq.symm ▸ mem_succ_self ξ₂)
        exact (hξ₂β this).elim
    · by_cases hξ₂β : ξ₂ ∈ β
      · have : ξ₁ ∈ β := by
          have hEq : succ ξ₁ = ξ₂ := by simpa [F, hξ₁β, hξ₂β] using hy₁.symm.trans hy₂
          exact hβord.transitive ξ₂ hξ₂β ξ₁ (hEq ▸ mem_succ_self ξ₁)
        exact (hξ₁β this).elim
      · have hEq : succ ξ₁ = succ ξ₂ := by simpa [F, hξ₁β, hξ₂β] using hy₁.symm.trans hy₂
        exact succ_inj hEq
  have hrange : range f = succ α \ {β} := by
    apply subset_antisymm
    · exact range_subset_of_mem_function hfFun
    · intro y hy
      by_cases hyβ : y ∈ β
      · have hyα : y ∈ α := hβsubα y hyβ
        exact mem_range_iff.mpr ⟨y, (hgraph y hyα y).2 (by
          show y = F y
          simp [F, hyβ])⟩
      · have hySucc : y ∈ succ α := (mem_sdiff_iff.mp hy).1
        have hyω : y ∈ (ω : V) := by
          exact IsOrdinal.ω.toIsTransitive.transitive (succ α) hsuccαω y hySucc
        rcases mem_ω_eq_zero_or_eq_succ hyω with (hy0 | ⟨ξ, hξω, rfl⟩)
        · have hβne0 : β ≠ 0 := by
            intro hβ0
            exact (mem_sdiff_iff.mp hy).2 (by simp [hy0, hβ0])
          have h0β : (0 : V) ∈ β := by
            have hβne : β ≠ ∅ := by simpa [zero_def] using hβne0
            have hβne' : IsNonempty β := ne_empty_iff_isNonempty.mp hβne
            simpa [zero_def] using (IsOrdinal.empty_mem_iff_nonempty (α := β)).2 hβne'
          exact (hyβ (hy0 ▸ h0β)).elim
        · have hξord : IsOrdinal ξ := IsOrdinal.nat hξω
          letI : IsOrdinal ξ := hξord
          have hsuccξsα : succ ξ ∈ succ α := (mem_sdiff_iff.mp hy).1
          have hξα : ξ ∈ α := by
            rcases mem_succ_iff.mp hsuccξsα with (hEq | hsuccξα)
            · exact hEq.symm ▸ mem_succ_self ξ
            · exact hαord.transitive (succ ξ) hsuccξα ξ (mem_succ_self ξ)
          have hξβ : ξ ∉ β := by
            intro hξβ
            have hsuccξsubβ : succ ξ ⊆ β := IsOrdinal.succ_subset_of_mem hξβ
            have : succ ξ = β ∨ succ ξ ∈ β :=
              (IsOrdinal.subset_iff (α := succ ξ) (β := β)).1 hsuccξsubβ
            rcases this with (hEq | hsuccξβ)
            · exact (mem_sdiff_iff.mp hy).2 (by simp [hEq])
            · exact hyβ hsuccξβ
          exact mem_range_iff.mpr ⟨ξ, (hgraph ξ hξα (succ ξ)).2 (by
            show succ ξ = F ξ
            simp [F, hξβ])⟩
  exact CardEQ.symm <| CardEQ.of_bijective ⟨hfFun, hfInj, hrange⟩

lemma not_cardLE_succ_of_mem_ω [V ⊧ₘ* 𝗭𝗙] {α : V}
    (hαω : α ∈ (ω : V)) :
    ¬ succ α ≤# α := by
  let P : V → Prop := fun ξ ↦ ¬ succ ξ ≤# ξ
  have hP : ℒₛₑₜ-predicate[V] P := by
    letI : ℒₛₑₜ-relation[V] CardLE := CardLE.definable
    change ℒₛₑₜ-predicate[V] (fun ξ ↦ ¬ succ ξ ≤# ξ)
    definability
  have hAll : ∀ ξ ∈ (ω : V), P ξ := by
    apply naturalNumber_induction (P := P) hP
    · intro h
      rcases h with ⟨f, hfFun, -⟩
      rcases exists_of_mem_function hfFun 0 (by simp) with ⟨y, hy0, -⟩
      have : y ∈ (∅ : V) := by simp [zero_def] at hy0
      exact not_mem_empty this
    · intro ξ hξω ih h
      rcases h with ⟨f, hfFun, hfInj⟩
      let y : V := f ‘ (succ ξ)
      have htop : ⟨succ ξ, y⟩ₖ ∈ f := by
        rcases exists_of_mem_function hfFun (succ ξ) (by simp) with ⟨y', -, htop'⟩
        have hyEq : y = y' := by
          simpa [y] using value_eq_of_kpair_mem hfFun htop'
        simpa [hyEq] using htop'
      have hy : y ∈ succ ξ := (mem_of_mem_functions hfFun htop).2
      let g : V := f ↾ (succ ξ)
      have hgFun₀ : g ∈ succ ξ ^ succ ξ := by
        apply mem_function.intro
        · intro p hp
          rcases mem_restrict_iff.mp hp with ⟨hpf, x, hx, z, rfl⟩
          have hz : z ∈ succ ξ := (mem_of_mem_functions hfFun hpf).2
          simpa [mem_prod_iff] using And.intro hx hz
        · intro x hx
          have hxs : x ∈ succ (succ ξ) := by simpa [mem_succ_iff] using Or.inr hx
          rcases exists_unique_of_mem_function hfFun x hxs with ⟨z, hxzf, huniq⟩
          refine ExistsUnique.intro z (kpair_mem_restrict_iff.mpr ⟨hxzf, hx⟩) ?_
          intro z' hxz'g
          exact huniq z' ((kpair_mem_restrict_iff.mp hxz'g).1)
      have hgInj : Injective g := by
        intro x₁ x₂ z hx₁z hx₂z
        exact hfInj _ _ _ (kpair_mem_restrict_iff.mp hx₁z).1 (kpair_mem_restrict_iff.mp hx₂z).1
      have hRangeSub : range g ⊆ succ ξ \ {y} := by
        intro z hz
        rcases mem_range_iff.mp hz with ⟨x, hxz⟩
        have hxf : ⟨x, z⟩ₖ ∈ f := (kpair_mem_restrict_iff.mp hxz).1
        have hx : x ∈ succ ξ := (kpair_mem_restrict_iff.mp hxz).2
        have hzCod : z ∈ succ ξ := (mem_of_mem_functions hgFun₀ hxz).2
        have hzNe : z ≠ y := by
          intro hEq
          have hxEq : x = succ ξ := hfInj x (succ ξ) y (hEq ▸ hxf) htop
          have : succ ξ ∈ succ ξ := hxEq ▸ hx
          exact (mem_irrefl (succ ξ)) this
        exact mem_sdiff_iff.mpr ⟨hzCod, by simpa [mem_singleton_iff] using hzNe⟩
      have hgFunRange : g ∈ range g ^ succ ξ := mem_function_range_of_mem_function hgFun₀
      have hgFun : g ∈ (succ ξ \ {y}) ^ succ ξ :=
        mem_function_of_mem_function_of_subset hgFunRange hRangeSub
      rcases CardEQ.exists_bijective (succ_sdiff_singleton_cardEQ_of_mem_ω hξω hy) with ⟨e, heBij⟩
      have hcomp : succ ξ ≤# ξ := ⟨compose g e, compose_function hgFun heBij.mem_function,
        compose_injective hgInj heBij.injective⟩
      exact ih hcomp
  exact hAll α hαω

lemma not_exists_injective_function_from_succ_of_mem_ω [V ⊧ₘ* 𝗭𝗙] {α : V}
    (hαω : α ∈ (ω : V)) :
    ¬ ∃ f, f ∈ α ^ succ α ∧ Injective f := by
  simpa [CardLE] using not_cardLE_succ_of_mem_ω (α := α) hαω

lemma succ_cardEQ_self_of_ω_subset {α : V} [hα : IsOrdinal α]
    (hωα : (ω : V) ⊆ α) :
    succ α ≋ α := by
  classical
  have hαnotω : α ∉ (ω : V) := by
    intro hαω
    have hsuccαω : succ α ∈ (ω : V) := ω_succ_closed hαω
    exact mem_asymm (by simp) (hωα _ hsuccαω)
  let F : V → V := fun ξ ↦
    if ξ ∈ (ω : V) then succ ξ else if ξ = α then 0 else ξ
  have hFdef : ℒₛₑₜ-function₁[V] F := by
    let R : (Fin 2 → V) → Prop := fun v ↦
      (v 1 ∈ (ω : V) ∧ v 0 = succ (v 1)) ∨
      (v 1 ∉ (ω : V) ∧ v 1 = α ∧ v 0 = 0) ∨
      (v 1 ∉ (ω : V) ∧ v 1 ≠ α ∧ v 0 = v 1)
    have hR : Language.Definable (L := ℒₛₑₜ) (M := V) R := by
      change Language.Definable (L := ℒₛₑₜ) (M := V) (fun v : Fin 2 → V ↦
        (v 1 ∈ (ω : V) ∧ v 0 = succ (v 1)) ∨
        (v 1 ∉ (ω : V) ∧ v 1 = α ∧ v 0 = 0) ∨
        (v 1 ∉ (ω : V) ∧ v 1 ≠ α ∧ v 0 = v 1))
      definability
    change Language.Definable (L := ℒₛₑₜ) (M := V)
      (fun v : Fin 2 → V ↦ v 0 = if v 1 ∈ (ω : V) then succ (v 1) else if v 1 = α then 0 else v 1)
    exact Language.Definable.of_iff (L := ℒₛₑₜ) hR <| by
      intro v
      by_cases hvω : v 1 ∈ (ω : V) <;> by_cases hvα : v 1 = α <;> simp [R, hvω, hvα, hαnotω]
  have hFmap : ∀ ξ ∈ succ α, F ξ ∈ α := by
    intro ξ hξsα
    by_cases hξω : ξ ∈ (ω : V)
    · exact hωα _ (by simp [F, hξω])
    · by_cases hξα : ξ = α
      · subst hξα
        simpa [F, hαnotω] using hωα 0 zero_mem_ω
      · have hξα' : ξ ∈ α := by
          rcases mem_succ_iff.mp hξsα with (rfl | hξα')
          · exact (hξα rfl).elim
          · exact hξα'
        simpa [F, hξω, hξα] using hξα'
  rcases graph_exists_mem_function_of_definableFunction
      (succ α) α F hFdef hFmap with
    ⟨f, hfFun, hgraph⟩
  have hfInj : Injective f := by
    intro x₁ x₂ y hx₁y hx₂y
    have hx₁sα : x₁ ∈ succ α := (mem_of_mem_functions hfFun hx₁y).1
    have hx₂sα : x₂ ∈ succ α := (mem_of_mem_functions hfFun hx₂y).1
    have hy₁ : y = F x₁ := (hgraph x₁ hx₁sα y).1 hx₁y
    have hy₂ : y = F x₂ := (hgraph x₂ hx₂sα y).1 hx₂y
    have hEq : F x₁ = F x₂ := hy₁.symm.trans hy₂
    by_cases hx₁ω : x₁ ∈ (ω : V)
    · by_cases hx₂ω : x₂ ∈ (ω : V)
      · exact succ_inj (by simpa [F, hx₁ω, hx₂ω] using hEq)
      · by_cases hx₂α : x₂ = α
        · have : x₁ ∈ (0 : V) := by
            have h : succ x₁ = 0 := by simpa [F, hx₁ω, hx₂ω, hx₂α, hαnotω] using hEq
            simpa [h] using mem_succ_self x₁
          exact (not_mem_empty this).elim
        · have : x₂ ∈ (ω : V) := by
            have h : succ x₁ = x₂ := by simpa [F, hx₁ω, hx₂ω, hx₂α] using hEq
            exact h.symm ▸ ω_succ_closed hx₁ω
          exact (hx₂ω this).elim
    · by_cases hx₁α : x₁ = α
      · by_cases hx₂ω : x₂ ∈ (ω : V)
        · have : x₂ ∈ (0 : V) := by
            have h : 0 = succ x₂ := by simpa [F, hx₁ω, hx₁α, hx₂ω, hαnotω] using hEq
            simpa [h.symm] using mem_succ_self x₂
          exact (not_mem_empty this).elim
        · by_cases hx₂α : x₂ = α
          · exact hx₁α.trans hx₂α.symm
          · have : x₂ ∈ (ω : V) := by
              have h : 0 = x₂ := by simpa [F, hx₁ω, hx₁α, hx₂ω, hx₂α, hαnotω] using hEq
              exact h ▸ zero_mem_ω
            exact (hx₂ω this).elim
      · by_cases hx₂ω : x₂ ∈ (ω : V)
        · have : x₁ ∈ (ω : V) := by
            have h : x₁ = succ x₂ := by simpa [F, hx₁ω, hx₁α, hx₂ω] using hEq
            exact h ▸ ω_succ_closed hx₂ω
          exact (hx₁ω this).elim
        · by_cases hx₂α : x₂ = α
          · have : x₁ ∈ (ω : V) := by
              have h : x₁ = 0 := by simpa [F, hx₁ω, hx₁α, hx₂ω, hx₂α, hαnotω] using hEq
              exact h ▸ zero_mem_ω
            exact (hx₁ω this).elim
          · simpa [F, hx₁ω, hx₁α, hx₂ω, hx₂α] using hEq
  have hrange : range f = α := by
    apply subset_antisymm
    · exact range_subset_of_mem_function hfFun
    · intro y hyα
      by_cases hyω : y ∈ (ω : V)
      · rcases mem_ω_eq_zero_or_eq_succ hyω with (rfl | ⟨ξ, hξω, rfl⟩)
        · exact mem_range_iff.mpr ⟨α, (hgraph α (by simp) 0).2 (by simp [F, hαnotω])⟩
        · have hξsα : ξ ∈ succ α := by
            simpa [mem_succ_iff] using Or.inr (hωα ξ hξω)
          exact mem_range_iff.mpr ⟨ξ, (hgraph ξ hξsα (succ ξ)).2 (by simp [F, hξω])⟩
      · have hysα : y ∈ succ α := by
          simpa [mem_succ_iff] using Or.inr hyα
        have hyneα : y ≠ α := ne_of_mem hyα
        exact mem_range_iff.mpr ⟨y, (hgraph y hysα y).2 (by simp [F, hyω, hyneα])⟩
  exact CardEQ.of_bijective ⟨hfFun, hfInj, hrange⟩

def IsCardinal (κ : V) : Prop :=
  IsOrdinal κ ∧ ∀ α ∈ κ, ¬ α ≋ κ

instance IsCardinal.definable : ℒₛₑₜ-predicate[V] IsCardinal := by
  unfold IsCardinal
  definability

lemma not_isCardinal_succ_of_ω_subset {α : V} [IsOrdinal α]
    (hωα : (ω : V) ⊆ α) :
    ¬ IsCardinal (succ α) := by
  intro h
  exact h.2 α (by simp) (CardEQ.symm (succ_cardEQ_self_of_ω_subset (α := α) hωα))

lemma isCardinal_of_mem_ω [V ⊧ₘ* 𝗭𝗙] {α : V} (hαω : α ∈ (ω : V)) :
    IsCardinal α := by
  letI : IsOrdinal α := IsOrdinal.nat hαω
  refine ⟨inferInstance, ?_⟩
  intro β hβα hβαeq
  letI : IsOrdinal β := IsOrdinal.of_mem hβα
  have hβω : β ∈ (ω : V) :=
    IsOrdinal.ω.toIsTransitive.transitive α hαω β hβα
  have hsuccβleα : succ β ≤# α :=
    cardLE_of_subset (IsOrdinal.succ_subset_of_mem hβα)
  exact not_cardLE_succ_of_mem_ω (α := β) hβω (hsuccβleα.trans hβαeq.ge)

lemma mem_ω_of_isOrdinal_of_cardEQ_mem_ω [V ⊧ₘ* 𝗭𝗙] {α β : V}
    (hα : IsOrdinal α) (hβω : β ∈ (ω : V)) (hαβ : α ≋ β) :
    α ∈ (ω : V) := by
  letI : IsOrdinal α := hα
  letI : IsOrdinal β := IsOrdinal.nat hβω
  by_contra hαω
  have hωα : (ω : V) ⊆ α := by
    rcases IsOrdinal.subset_or_supset (α := (ω : V)) (β := α) with (hωα | hαωsub)
    · exact hωα
    · rcases (IsOrdinal.subset_iff (α := α) (β := (ω : V))).1 hαωsub with (hEq | hαω')
      · exact hEq.symm ▸ subset_refl (ω : V)
      · exact (hαω hαω').elim
  have hsuccβleα : succ β ≤# α := by
    exact cardLE_of_subset <| subset_trans (IsOrdinal.succ_subset_of_mem hβω) hωα
  exact not_cardLE_succ_of_mem_ω (α := β) hβω (hsuccβleα.trans hαβ.le)

lemma ordinalPairZeroFstType_mem_ω [V ⊧ₘ* 𝗭𝗙] {α : V} (hαω : α ∈ (ω : V)) :
    ordinalPairZeroFstType α ∈ (ω : V) := by
  let αo : Ordinal V := ⟨α, IsOrdinal.nat hαω⟩
  exact mem_ω_of_isOrdinal_of_cardEQ_mem_ω
    (ordinalPairZeroFstType_isOrdinal (V := V) α)
    (Ordinal.mulValue_mem_ω hαω hαω)
    (Ordinal.zeroFstType_cardEQ_mulValue (V := V) αo)

private lemma exists_mem_prod_eq_ordinalPairInitialSegmentType_of_mem_ordinalPairZeroFstType
    [V ⊧ₘ* 𝗭𝗙] {α : V}
    (hα : IsOrdinal α) (hατ : α ∈ ordinalPairZeroFstType α) :
    ∃ p ∈ α ×ˢ α, α = ordinalPairInitialSegmentType p := by
  let τ : V := ordinalPairZeroFstType α
  have hτord : IsOrdinal τ := by
    simpa [τ] using ordinalPairZeroFstType_isOrdinal (V := V) α
  letI : IsOrdinal α := hα
  letI : IsOrdinal τ := hτord
  have hαprod : ordinalPairInitialSegment ⟨0, α⟩ₖ = α ×ˢ α :=
    ordinalPairInitialSegment_zero_fst_eq_prod (α := α) hα
  rcases (ordinalPairInitialSegmentType_spec (V := V) ⟨0, α⟩ₖ).2 with ⟨f, hf0⟩
  have hf :
      IsOrderIso (IsOrdinal.memRelOn τ) τ
        (ordinalPairRelOn (α ×ˢ α)) (α ×ˢ α) f := by
    simpa [τ, ordinalPairZeroFstType, hαprod] using hf0
  rcases exists_of_mem_function hf.mem_function α hατ with ⟨p, hpαprod, hαpf⟩
  have hpαseg : p ∈ ordinalPairInitialSegment ⟨0, α⟩ₖ := by
    simpa [hαprod] using hpαprod
  have hqαpair : IsOrdinalPair ⟨0, α⟩ₖ :=
    IsOrdinalPair.mk (by infer_instance) hα
  have hpLTα : OrdinalPairLT p ⟨0, α⟩ₖ :=
    (mem_ordinalPairInitialSegment_iff_of_isOrdinalPair hqαpair).1 hpαseg
  have hIseg :
      initialSegment (ordinalPairRelOn (α ×ˢ α)) (α ×ˢ α) p =
        ordinalPairInitialSegment p := by
    simpa [hαprod] using initialSegment_ordinalPairRelOn_eq hpLTα
  let fα : V := f ↾ (initialSegment (IsOrdinal.memRelOn τ) τ α)
  have hfα0 :
      IsOrderIso (IsOrdinal.memRelOn τ)
        (initialSegment (IsOrdinal.memRelOn τ) τ α)
        (ordinalPairRelOn (α ×ˢ α))
        (initialSegment (ordinalPairRelOn (α ×ˢ α)) (α ×ˢ α) p)
        fα := by
    simpa [fα] using IsOrderIso.restrict_initialSegment hf hατ hαpf
  have hfα :
      IsOrderIso (IsOrdinal.memRelOn α) α
        (ordinalPairRelOn (ordinalPairInitialSegment p))
        (ordinalPairInitialSegment p) fα := by
    refine ⟨?_, hfα0.injective, ?_, ?_⟩
    · simpa [fα, hIseg, IsOrdinal.initialSegment_memRelOn_eq (α := τ) hατ] using hfα0.mem_function
    · simpa [hIseg] using hfα0.range_eq
    · intro x₁ hx₁α x₂ hx₂α
      have hx₁I : x₁ ∈ initialSegment (IsOrdinal.memRelOn τ) τ α := by
        simpa [IsOrdinal.initialSegment_memRelOn_eq (α := τ) hατ] using hx₁α
      have hx₂I : x₂ ∈ initialSegment (IsOrdinal.memRelOn τ) τ α := by
        simpa [IsOrdinal.initialSegment_memRelOn_eq (α := τ) hατ] using hx₂α
      have hx₁τ : x₁ ∈ τ := hτord.toIsTransitive.transitive _ hατ _ hx₁α
      have hx₂τ : x₂ ∈ τ := hτord.toIsTransitive.transitive _ hατ _ hx₂α
      have hy₁I : fα ‘ x₁ ∈
          initialSegment (ordinalPairRelOn (α ×ˢ α)) (α ×ˢ α) p := by
        rw [← hfα0.range_eq]
        exact value_mem_range hfα0.mem_function hx₁I
      have hy₂I : fα ‘ x₂ ∈
          initialSegment (ordinalPairRelOn (α ×ˢ α)) (α ×ˢ α) p := by
        rw [← hfα0.range_eq]
        exact value_mem_range hfα0.mem_function hx₂I
      have hy₁p : fα ‘ x₁ ∈ ordinalPairInitialSegment p := by
        rw [hIseg] at hy₁I
        exact hy₁I
      have hy₂p : fα ‘ x₂ ∈ ordinalPairInitialSegment p := by
        rw [hIseg] at hy₂I
        exact hy₂I
      have hy₁αprod : fα ‘ x₁ ∈ α ×ˢ α := by
        simpa [hαprod] using ordinalPairInitialSegment_subset hpLTα _ hy₁p
      have hy₂αprod : fα ‘ x₂ ∈ α ×ˢ α := by
        simpa [hαprod] using ordinalPairInitialSegment_subset hpLTα _ hy₂p
      have hleft :
          ⟨x₁, x₂⟩ₖ ∈ IsOrdinal.memRelOn α ↔
            ⟨x₁, x₂⟩ₖ ∈ IsOrdinal.memRelOn τ := by
        simp [IsOrdinal.kpair_mem_memRelOn_iff, hx₁α, hx₂α, hx₁τ, hx₂τ]
      have hright :
          ⟨fα ‘ x₁, fα ‘ x₂⟩ₖ ∈ ordinalPairRelOn (α ×ˢ α) ↔
            ⟨fα ‘ x₁, fα ‘ x₂⟩ₖ ∈ ordinalPairRelOn (ordinalPairInitialSegment p) := by
        rw [kpair_mem_ordinalPairRelOn_iff, kpair_mem_ordinalPairRelOn_iff]
        simp [hy₁αprod, hy₂αprod, hy₁p, hy₂p]
      exact hleft.trans <| (hfα0.rel_iff hx₁I hx₂I).trans hright
  have hSwo :
      IsWellOrderOn (ordinalPairRelOn (ordinalPairInitialSegment p))
        (ordinalPairInitialSegment p) :=
    wellOrderOn_ordinalPairRelOn_ordinalPairInitialSegment (p := p)
  rcases (ordinalPairInitialSegmentType_spec (V := V) p).2 with ⟨g, hg⟩
  refine ⟨p, hpαprod, ?_⟩
  exact
    Ordinal.ordinal_isOrderIso_unique_of_wellOrderOn
      hSwo hα (ordinalPairInitialSegmentType_isOrdinal (V := V) p)
      ⟨fα, hfα⟩ ⟨g, hg⟩

lemma ordinalPairZeroFstType_ω [V ⊧ₘ* 𝗭𝗙] :
    ordinalPairZeroFstType (ω : V) = (ω : V) := by
  let τ : V := ordinalPairZeroFstType (ω : V)
  have hτord : IsOrdinal τ := by
    simpa [τ] using ordinalPairZeroFstType_isOrdinal (V := V) (ω : V)
  letI : IsOrdinal τ := hτord
  have hωprod : ordinalPairInitialSegment ⟨0, (ω : V)⟩ₖ = (ω : V) ×ˢ (ω : V) :=
    ordinalPairInitialSegment_zero_fst_eq_prod (α := (ω : V)) (by infer_instance)
  have hωsubτ : (ω : V) ⊆ τ := by
    simpa [τ] using subset_ordinalPairZeroFstType (V := V) (ω : V) (by infer_instance)
  rcases (IsOrdinal.subset_iff (α := (ω : V)) (β := τ)).1 hωsubτ with (hEq | hωτ)
  · simpa [τ] using hEq.symm
  · rcases (ordinalPairInitialSegmentType_spec (V := V) ⟨0, (ω : V)⟩ₖ).2 with ⟨f, hf0⟩
    have hf :
        IsOrderIso (IsOrdinal.memRelOn τ) τ
          (ordinalPairRelOn ((ω : V) ×ˢ (ω : V))) ((ω : V) ×ˢ (ω : V)) f := by
      simpa [τ, ordinalPairZeroFstType, hωprod] using hf0
    rcases exists_of_mem_function hf.mem_function (ω : V) hωτ with ⟨p, hpωprod, hωpf⟩
    have hpωseg : p ∈ ordinalPairInitialSegment ⟨0, (ω : V)⟩ₖ := by
      simpa [hωprod] using hpωprod
    have hqωpair : IsOrdinalPair ⟨0, (ω : V)⟩ₖ :=
      IsOrdinalPair.mk (by infer_instance) (by infer_instance)
    have hpLTω : OrdinalPairLT p ⟨0, (ω : V)⟩ₖ :=
      (mem_ordinalPairInitialSegment_iff_of_isOrdinalPair hqωpair).1 hpωseg
    have hIseg :
        initialSegment (ordinalPairRelOn ((ω : V) ×ˢ (ω : V))) ((ω : V) ×ˢ (ω : V)) p =
          ordinalPairInitialSegment p := by
      simpa [hωprod] using initialSegment_ordinalPairRelOn_eq hpLTω
    let fω : V := f ↾ (initialSegment (IsOrdinal.memRelOn τ) τ (ω : V))
    have hfω0 :
        IsOrderIso (IsOrdinal.memRelOn τ)
          (initialSegment (IsOrdinal.memRelOn τ) τ (ω : V))
          (ordinalPairRelOn ((ω : V) ×ˢ (ω : V)))
          (initialSegment (ordinalPairRelOn ((ω : V) ×ˢ (ω : V))) ((ω : V) ×ˢ (ω : V)) p)
          fω := by
      simpa [fω] using IsOrderIso.restrict_initialSegment hf hωτ hωpf
    have hfω :
        IsOrderIso (IsOrdinal.memRelOn (ω : V)) (ω : V)
          (ordinalPairRelOn (ordinalPairInitialSegment p))
          (ordinalPairInitialSegment p) fω := by
      refine ⟨?_, hfω0.injective, ?_, ?_⟩
      · simpa [fω, hIseg, IsOrdinal.initialSegment_memRelOn_eq (α := τ) hωτ] using hfω0.mem_function
      · simpa [hIseg] using hfω0.range_eq
      · intro x₁ hx₁ω x₂ hx₂ω
        have hx₁I : x₁ ∈ initialSegment (IsOrdinal.memRelOn τ) τ (ω : V) := by
          simpa [IsOrdinal.initialSegment_memRelOn_eq (α := τ) hωτ] using hx₁ω
        have hx₂I : x₂ ∈ initialSegment (IsOrdinal.memRelOn τ) τ (ω : V) := by
          simpa [IsOrdinal.initialSegment_memRelOn_eq (α := τ) hωτ] using hx₂ω
        have hx₁τ : x₁ ∈ τ := hτord.toIsTransitive.transitive _ hωτ _ hx₁ω
        have hx₂τ : x₂ ∈ τ := hτord.toIsTransitive.transitive _ hωτ _ hx₂ω
        have hy₁I : fω ‘ x₁ ∈
            initialSegment (ordinalPairRelOn ((ω : V) ×ˢ (ω : V))) ((ω : V) ×ˢ (ω : V)) p := by
          rw [← hfω0.range_eq]
          exact value_mem_range hfω0.mem_function hx₁I
        have hy₂I : fω ‘ x₂ ∈
            initialSegment (ordinalPairRelOn ((ω : V) ×ˢ (ω : V))) ((ω : V) ×ˢ (ω : V)) p := by
          rw [← hfω0.range_eq]
          exact value_mem_range hfω0.mem_function hx₂I
        have hy₁p : fω ‘ x₁ ∈ ordinalPairInitialSegment p := by
          rw [hIseg] at hy₁I
          exact hy₁I
        have hy₂p : fω ‘ x₂ ∈ ordinalPairInitialSegment p := by
          rw [hIseg] at hy₂I
          exact hy₂I
        have hy₁ωprod : fω ‘ x₁ ∈ (ω : V) ×ˢ (ω : V) := by
          simpa [hωprod] using ordinalPairInitialSegment_subset hpLTω _ hy₁p
        have hy₂ωprod : fω ‘ x₂ ∈ (ω : V) ×ˢ (ω : V) := by
          simpa [hωprod] using ordinalPairInitialSegment_subset hpLTω _ hy₂p
        have hleft :
            ⟨x₁, x₂⟩ₖ ∈ IsOrdinal.memRelOn (ω : V) ↔
              ⟨x₁, x₂⟩ₖ ∈ IsOrdinal.memRelOn τ := by
          simp [IsOrdinal.kpair_mem_memRelOn_iff, hx₁ω, hx₂ω, hx₁τ, hx₂τ]
        have hright :
            ⟨fω ‘ x₁, fω ‘ x₂⟩ₖ ∈ ordinalPairRelOn ((ω : V) ×ˢ (ω : V)) ↔
              ⟨fω ‘ x₁, fω ‘ x₂⟩ₖ ∈ ordinalPairRelOn (ordinalPairInitialSegment p) := by
          rw [kpair_mem_ordinalPairRelOn_iff, kpair_mem_ordinalPairRelOn_iff]
          simp [hy₁ωprod, hy₂ωprod, hy₁p, hy₂p]
        exact hleft.trans <| (hfω0.rel_iff hx₁I hx₂I).trans hright
    have hSwo :
        IsWellOrderOn (ordinalPairRelOn (ordinalPairInitialSegment p))
          (ordinalPairInitialSegment p) :=
      wellOrderOn_ordinalPairRelOn_ordinalPairInitialSegment (p := p)
    rcases (ordinalPairInitialSegmentType_spec (V := V) p).2 with ⟨g, hg⟩
    have hωeqp : (ω : V) = ordinalPairInitialSegmentType p :=
      Ordinal.ordinal_isOrderIso_unique_of_wellOrderOn
        hSwo (by infer_instance) (ordinalPairInitialSegmentType_isOrdinal (V := V) p)
        ⟨fω, hfω⟩ ⟨g, hg⟩
    rcases mem_prod_iff.mp hpωprod with ⟨β, hβω, γ, hγω, rfl⟩
    have hβord : IsOrdinal β := IsOrdinal.nat hβω
    have hγord : IsOrdinal γ := IsOrdinal.nat hγω
    let μ : V := ordinalMax β γ
    have hμord : IsOrdinal μ := by
      simpa [μ] using ordinalMax_isOrdinal hβord hγord
    letI : IsOrdinal μ := hμord
    have hμω : μ ∈ (ω : V) := by
      rcases IsOrdinal.subset_or_supset (α := β) (β := γ) with (hβγ | hγβ)
      · have hEq : μ = γ := by
          simpa [μ, ordinalMax] using (union_eq_iff_left.mpr hβγ : β ∪ γ = γ)
        simpa [hEq] using hγω
      · have hEq : μ = β := by
          simpa [μ, ordinalMax] using (union_eq_iff_right.mpr hγβ : β ∪ γ = β)
        simpa [hEq] using hβω
    let δ : V := succ μ
    have hδω : δ ∈ (ω : V) := by
      simpa [δ] using ω_succ_closed hμω
    have hδord : IsOrdinal δ := IsOrdinal.nat hδω
    have hβδ : β ∈ δ := by
      have hβsub : β ⊆ μ := by simp [μ, ordinalMax]
      rcases (IsOrdinal.subset_iff (α := β) (β := μ)).1 hβsub with (hEq | hβμ)
      · exact mem_succ_iff.mpr (Or.inl (by simpa [δ] using hEq))
      · exact mem_succ_iff.mpr (Or.inr (by simpa [δ] using hβμ))
    have hγδ : γ ∈ δ := by
      have hγsub : γ ⊆ μ := by simp [μ, ordinalMax]
      rcases (IsOrdinal.subset_iff (α := γ) (β := μ)).1 hγsub with (hEq | hγμ)
      · exact mem_succ_iff.mpr (Or.inl (by simpa [δ] using hEq))
      · exact mem_succ_iff.mpr (Or.inr (by simpa [δ] using hγμ))
    have hpδprod : ⟨β, γ⟩ₖ ∈ δ ×ˢ δ := by
      simpa [mem_prod_iff] using And.intro hβδ hγδ
    have hqδpair : IsOrdinalPair ⟨0, δ⟩ₖ :=
      IsOrdinalPair.mk (by infer_instance) hδord
    have hpLTδ : OrdinalPairLT ⟨β, γ⟩ₖ ⟨0, δ⟩ₖ := by
      have hpδseg : ⟨β, γ⟩ₖ ∈ ordinalPairInitialSegment ⟨0, δ⟩ₖ := by
        simpa [ordinalPairInitialSegment_zero_fst_eq_prod (α := δ) hδord] using hpδprod
      exact (mem_ordinalPairInitialSegment_iff_of_isOrdinalPair hqδpair).1 hpδseg
    have htypepδ :
        ordinalPairInitialSegmentType ⟨β, γ⟩ₖ ∈ ordinalPairZeroFstType δ := by
      simpa [ordinalPairZeroFstType] using
        (ordinalPairInitialSegmentType_strictIncreasing (V := V) hpLTδ)
    have htypepω : ordinalPairInitialSegmentType ⟨β, γ⟩ₖ ∈ (ω : V) :=
      IsOrdinal.ω.toIsTransitive.transitive _ (ordinalPairZeroFstType_mem_ω (V := V) hδω) _
        htypepδ
    have : (ω : V) ∈ (ω : V) := by
      simp [hωeqp] at htypepω
    exact False.elim ((mem_irrefl (ω : V)) this)

lemma isCardinal_ω [V ⊧ₘ* 𝗭𝗙] : IsCardinal (ω : V) := by
  refine ⟨inferInstance, ?_⟩
  intro α hαω hαωeq
  letI : IsOrdinal α := IsOrdinal.nat hαω
  have hsuccαleω : succ α ≤# (ω : V) :=
    cardLE_of_subset (IsOrdinal.succ_subset_of_mem hαω)
  exact not_cardLE_succ_of_mem_ω (α := α) hαω (hsuccαleω.trans hαωeq.ge)

lemma isLimitOrdinal_of_isCardinal_of_ω_subset {κ : V}
    (hκ : IsCardinal κ) (hωκ : (ω : V) ⊆ κ) :
    IsLimitOrdinal κ := by
  refine ⟨hκ.1, ?_, ?_⟩
  · intro hk0
    have : (0 : V) ∈ (0 : V) := hk0 ▸ hωκ 0 zero_mem_ω
    exact (mem_irrefl 0) this
  · rintro ⟨α, rfl⟩
    letI : IsOrdinal (succ α) := hκ.1
    letI : IsOrdinal α := IsOrdinal.of_mem (by simp : α ∈ succ α)
    have hωα : (ω : V) ⊆ α := by
      intro n hnω
      have hnsα : n ∈ succ α := hωκ n hnω
      rcases mem_succ_iff.mp hnsα with (rfl | hnα)
      · exfalso
        have hαω : n ∈ (ω : V) := by simpa using hnω
        have hsuccαω : succ n ∈ (ω : V) := ω_succ_closed hαω
        have : succ n ∈ succ n := hωκ _ hsuccαω
        exact (mem_irrefl (succ n)) this
      · exact hnα
    exact (not_isCardinal_succ_of_ω_subset (α := α) hωα) hκ

lemma IsCardinal.eq_of_cardEQ {α β : V}
    (hα : IsCardinal α) (hβ : IsCardinal β) (h : α ≋ β) : α = β := by
  letI : IsOrdinal α := hα.1
  letI : IsOrdinal β := hβ.1
  rcases IsOrdinal.mem_trichotomy (α := α) (β := β) with (hαβ | rfl | hβα)
  · exact (hβ.2 α hαβ h).elim
  · rfl
  · exact (hα.2 β hβα (CardEQ.symm h)).elim

lemma eq_of_isCardinal_of_cardEQ {α β : V}
    (hα : IsCardinal α) (hβ : IsCardinal β) (h : α ≋ β) : α = β :=
  IsCardinal.eq_of_cardEQ hα hβ h

lemma IsCardinal.subset_of_cardEQ_of_isOrdinal {κ α : V}
    (hκ : IsCardinal κ) (hα : IsOrdinal α) (h : κ ≋ α) : κ ⊆ α := by
  letI : IsOrdinal κ := hκ.1
  rcases IsOrdinal.mem_trichotomy (α := κ) (β := α) with (hκα | rfl | hακ)
  · exact hα.transitive κ hκα
  · simp
  · exact (hκ.2 α hακ (CardEQ.symm h)).elim

lemma exists_isCardinal_cardEQ_of_isOrdinal [V ⊧ₘ* 𝗭𝗙] {α : V}
    (hα : IsOrdinal α) :
    ∃ κ, IsCardinal κ ∧ κ ≋ α := by
  let P : V → Prop := fun ξ ↦ ξ ≋ α
  have hP : ℒₛₑₜ-predicate[V] P := by
    letI : ℒₛₑₜ-relation[V] CardEQ := CardEQ.definable
    change ℒₛₑₜ-predicate[V] (fun ξ ↦ ξ ≋ α)
    definability
  rcases exists_least_ordinal_of_exists P hP ⟨α, hα, CardEQ.refl α⟩ with
    ⟨κ, hκord, hκα, hκleast⟩
  refine ⟨κ, ⟨hκord, ?_⟩, hκα⟩
  intro β hβκ hβα
  have hκsubβ : κ ⊆ β := hκleast β (hκord.of_mem hβκ) (CardEQ.trans hβα hκα)
  have hβsubκ : β ⊆ κ := hκord.transitive β hβκ
  have hEq : κ = β := subset_antisymm hκsubβ hβsubκ
  exact (mem_irrefl κ) (hEq ▸ hβκ)

lemma isCardinal_sUnion [V ⊧ₘ* 𝗭𝗙] {C : V}
    (hC : ∀ κ ∈ C, IsCardinal κ) :
    IsCardinal (⋃ˢ C) := by
  have hUord : IsOrdinal (⋃ˢ C) :=
    IsOrdinal.sUnion fun κ hκC ↦ (hC κ hκC).1
  refine ⟨hUord, ?_⟩
  intro α hαU hαeq
  have hαord : IsOrdinal α := hUord.of_mem hαU
  letI : IsOrdinal α := hαord
  rcases mem_sUnion_iff.mp hαU with ⟨κ, hκC, hακ⟩
  have hκ : IsCardinal κ := hC κ hκC
  have hκleU : κ ≤# ⋃ˢ C := cardLE_of_subset (subset_sUnion_of_mem hκC)
  have hκleα : κ ≤# α := hκleU.trans hαeq.ge
  rcases Ordinal.exists_wellOrderOn_subset_isOrderIso_of_cardLE
      (α := κ) (X := α) hκ.1 hκleα with ⟨Y, S, f, hYsub, hSwo, hf⟩
  let hYwo : IsWellOrderOn (IsOrdinal.memRelOn Y) Y :=
    IsOrdinal.wellOrderOn_memRelOn_subset (α := α) hYsub
  let β : Ordinal V := Ordinal.wellOrderType (IsOrdinal.memRelOn Y) Y hYwo
  have hβsub : β.val ⊆ α :=
    wellOrderTypeVal_memRelOn_subset_subset (α := α) (X := Y) hYsub
  rcases Ordinal.wellOrderType_isOrderIso
      (S := IsOrdinal.memRelOn Y) (Y := Y) (hSwo := hYwo) with ⟨g, hg⟩
  have hκY : κ ≋ Y := CardEQ.of_bijective (IsOrderIso.bijective hf)
  have hβY : β.val ≋ Y := CardEQ.of_bijective (IsOrderIso.bijective hg)
  have hκβ : κ ≋ β.val := CardEQ.trans hκY (CardEQ.symm hβY)
  have hβακ : β.val ∈ κ := by
    rcases (IsOrdinal.subset_iff (α := β.val) (β := α)).1 hβsub with (hβα | hβα)
    · exact hβα ▸ hακ
    · exact hκ.1.toIsTransitive.transitive α hακ β.val hβα
  exact (hκ.2 β.val hβακ (CardEQ.symm hκβ)).elim

lemma existsUnique_hartogs [V ⊧ₘ* 𝗭𝗙] (X : V) :
    ∃! α : V, IsOrdinal α ∧ ¬ α ≤# X ∧
      ∀ ξ : V, IsOrdinal ξ → ¬ ξ ≤# X → α ⊆ ξ := by
  let P : V → Prop := fun α ↦ ¬ α ≤# X
  have hP : ℒₛₑₜ-predicate[V] P := by
    letI : ℒₛₑₜ-relation[V] CardLE := CardLE.definable
    change ℒₛₑₜ-predicate[V] (fun α ↦ ¬ α ≤# X)
    definability
  rcases exists_least_ordinal_of_exists (P := P) hP (Ordinal.exists_ordinal_not_cardLE (V := V) X) with
    ⟨α, hαord, hαX, hαleast⟩
  refine ⟨α, ⟨hαord, hαX, hαleast⟩, ?_⟩
  intro β hβ
  exact subset_antisymm
    (hβ.2.2 α hαord hαX)
    (hαleast β hβ.1 hβ.2.1)

/--
The least ordinal that does not inject into `X`.
-/
noncomputable def hartogs [V ⊧ₘ* 𝗭𝗙] (X : V) : V :=
  Classical.choose! (existsUnique_hartogs (V := V) X)

lemma hartogs_spec [V ⊧ₘ* 𝗭𝗙] (X : V) :
    IsOrdinal (hartogs X) ∧ ¬ hartogs X ≤# X ∧
      ∀ ξ : V, IsOrdinal ξ → ¬ ξ ≤# X → hartogs X ⊆ ξ :=
  Classical.choose!_spec (existsUnique_hartogs (V := V) X)

lemma hartogs_isOrdinal [V ⊧ₘ* 𝗭𝗙] (X : V) : IsOrdinal (hartogs X) :=
  (hartogs_spec (V := V) X).1

lemma hartogs_not_cardLE [V ⊧ₘ* 𝗭𝗙] (X : V) : ¬ hartogs X ≤# X :=
  (hartogs_spec (V := V) X).2.1

lemma hartogs_least [V ⊧ₘ* 𝗭𝗙] (X ξ : V)
    (hξ : IsOrdinal ξ) (hξX : ¬ ξ ≤# X) :
    hartogs X ⊆ ξ :=
  (hartogs_spec (V := V) X).2.2 ξ hξ hξX

lemma hartogs_eq_iff [V ⊧ₘ* 𝗭𝗙] (X α : V) :
    α = hartogs X ↔
      IsOrdinal α ∧ ¬ α ≤# X ∧
        ∀ ξ : V, IsOrdinal ξ → ¬ ξ ≤# X → α ⊆ ξ := by
  simp [hartogs]

instance hartogs_eq_definable [V ⊧ₘ* 𝗭𝗙] :
    ℒₛₑₜ-relation[V] (fun α X ↦ α = hartogs X) := by
  let R : V → V → Prop := fun α X ↦
    IsOrdinal α ∧ ¬ α ≤# X ∧
      ∀ ξ : V, IsOrdinal ξ → ¬ ξ ≤# X → α ⊆ ξ
  have hR : ℒₛₑₜ-relation[V] R := by
    letI : ℒₛₑₜ-relation[V] CardLE := CardLE.definable
    show ℒₛₑₜ-relation[V] (fun α X ↦
      IsOrdinal α ∧ ¬ α ≤# X ∧
        ∀ ξ : V, IsOrdinal ξ → ¬ ξ ≤# X → α ⊆ ξ)
    definability
  have hEq : (fun α X ↦ α = hartogs X) = R := by
    funext α X
    exact propext (hartogs_eq_iff (V := V) X α)
  exact hEq ▸ hR

instance hartogs.definable [V ⊧ₘ* 𝗭𝗙] : ℒₛₑₜ-function₁[V] hartogs :=
  hartogs_eq_definable (V := V)

lemma hartogs_isCardinal [V ⊧ₘ* 𝗭𝗙] (X : V) :
    IsCardinal (hartogs X) := by
  refine ⟨hartogs_isOrdinal (V := V) X, ?_⟩
  intro β hβ hβeq
  have hβord : IsOrdinal β := (hartogs_isOrdinal (V := V) X).of_mem hβ
  have hβleX : β ≤# X := by
    by_contra hβX
    have hhartogsβ : hartogs X ⊆ β := hartogs_least (V := V) X β hβord hβX
    have hβhartogs : β ⊆ hartogs X := (hartogs_isOrdinal (V := V) X).transitive β hβ
    have hEq : hartogs X = β := subset_antisymm hhartogsβ hβhartogs
    exact (mem_irrefl β) (hEq ▸ hβ)
  exact hartogs_not_cardLE (V := V) X (hβeq.ge.trans hβleX)

lemma existsUnique_isCardinal_cardEQ (X : V)
    (hX : ∃ κ, IsCardinal κ ∧ κ ≋ X) :
    ∃! κ, IsCardinal κ ∧ κ ≋ X := by
  rcases hX with ⟨κ, hκ, hkX⟩
  refine ⟨κ, ⟨hκ, hkX⟩, ?_⟩
  intro ξ hξ
  exact IsCardinal.eq_of_cardEQ hξ.1 hκ (CardEQ.trans hξ.2 (CardEQ.symm hkX))

/--
The cardinality of `X` if a cardinal equinumerous with `X` exists, and `∅` otherwise.
-/
noncomputable def card (X : V) : V :=
  Classical.extendedChoose! existsUnique_isCardinal_cardEQ ∅ X

lemma card_spec {X : V} (hX : ∃ κ, IsCardinal κ ∧ κ ≋ X) :
    IsCardinal (card X) ∧ card X ≋ X := by
  simpa [card] using
    (Classical.extendedchoose!_spec
      (h := existsUnique_isCardinal_cardEQ) (default := (∅ : V)) (x := X) hX)

lemma card_isCardinal {X : V} (hX : ∃ κ, IsCardinal κ ∧ κ ≋ X) :
    IsCardinal (card X) :=
  (card_spec hX).1

lemma card_cardEQ {X : V} (hX : ∃ κ, IsCardinal κ ∧ κ ≋ X) :
    card X ≋ X :=
  (card_spec hX).2

lemma card_isCardinal_of_isOrdinal [V ⊧ₘ* 𝗭𝗙] {α : V} (hα : IsOrdinal α) :
    IsCardinal (card α) :=
  card_isCardinal (exists_isCardinal_cardEQ_of_isOrdinal (V := V) hα)

lemma card_cardEQ_of_isOrdinal [V ⊧ₘ* 𝗭𝗙] {α : V} (hα : IsOrdinal α) :
    card α ≋ α :=
  card_cardEQ (exists_isCardinal_cardEQ_of_isOrdinal (V := V) hα)

lemma card_subset_of_isOrdinal [V ⊧ₘ* 𝗭𝗙] {α : V} (hα : IsOrdinal α) :
    card α ⊆ α := by
  exact IsCardinal.subset_of_cardEQ_of_isOrdinal
    (card_isCardinal_of_isOrdinal (V := V) hα) hα
    (card_cardEQ_of_isOrdinal (V := V) hα)

@[simp] lemma card_eq_empty_of_not_exists {X : V}
    (hX : ¬ ∃ κ, IsCardinal κ ∧ κ ≋ X) : card X = ∅ := by
  simpa [card] using
    (Classical.extendedchoose!_spec_not
      (h := existsUnique_isCardinal_cardEQ) (default := (∅ : V)) (x := X) hX)

lemma card_eq_iff (X κ : V) :
    κ = card X ↔
      (IsCardinal κ ∧ κ ≋ X) ∨
      (¬ ∃ α : V, IsCardinal α ∧ α ≋ X) ∧ κ = ∅ := by
  by_cases hX : ∃ α : V, IsCardinal α ∧ α ≋ X
  · have hEq : κ = card X ↔ IsCardinal κ ∧ κ ≋ X := by
      simpa [card] using
        (Classical.extendedChoose!_eq_iff
          (h := existsUnique_isCardinal_cardEQ) (default := (∅ : V)) (hpx := hX)
          (x := X) (y := κ))
    constructor
    · intro hk
      exact Or.inl (hEq.mp hk)
    · rintro (hk | hk)
      · exact hEq.mpr hk
      · exact (hk.1 hX).elim
  · constructor
    · intro hk
      exact Or.inr ⟨hX, by simpa [card_eq_empty_of_not_exists hX] using hk⟩
    · rintro (hk | hk)
      · exact (hX ⟨κ, hk⟩).elim
      · simpa [card_eq_empty_of_not_exists hX] using hk.2

lemma cardLE_iff_card_subset_card [V ⊧ₘ* 𝗭𝗙] {X Y : V}
    (hX : ∃ κ, IsCardinal κ ∧ κ ≋ X)
    (hY : ∃ κ, IsCardinal κ ∧ κ ≋ Y) :
    X ≤# Y ↔ card X ⊆ card Y := by
  have hcardX : IsCardinal (card X) ∧ card X ≋ X := card_spec hX
  have hcardY : IsCardinal (card Y) ∧ card Y ≋ Y := card_spec hY
  letI : IsOrdinal (card X) := hcardX.1.1
  letI : IsOrdinal (card Y) := hcardY.1.1
  constructor
  · intro hXY
    have hκle : card X ≤# card Y := (hcardX.2.le.trans hXY).trans hcardY.2.ge
    rcases hκle with ⟨f, hf, hfInj⟩
    let R : V := range f
    have hRsub : R ⊆ card Y := range_subset_of_mem_function hf
    have hfBij : Bijective f (card X) R := ⟨mem_function_range_of_mem_function hf, hfInj, rfl⟩
    let hRwo : IsWellOrderOn (IsOrdinal.memRelOn R) R :=
      IsOrdinal.wellOrderOn_memRelOn_subset (α := card Y) hRsub
    let β : Ordinal V := Ordinal.wellOrderType (IsOrdinal.memRelOn R) R hRwo
    have hβsub : β.val ⊆ card Y :=
      wellOrderTypeVal_memRelOn_subset_subset (α := card Y) (X := R) hRsub
    rcases Ordinal.wellOrderType_isOrderIso (S := IsOrdinal.memRelOn R) (Y := R) (hSwo := hRwo) with
      ⟨g, hg⟩
    have hβR : β.val ≋ R := CardEQ.of_bijective (IsOrderIso.bijective hg)
    have hκβ : card X ≋ β.val :=
      CardEQ.trans (CardEQ.of_bijective hfBij) (CardEQ.symm hβR)
    exact subset_trans
      (IsCardinal.subset_of_cardEQ_of_isOrdinal hcardX.1 β.ordinal hκβ)
      hβsub
  · intro h
    exact (hcardX.2.ge.trans (cardLE_of_subset h)).trans hcardY.2.le

lemma cardLE_iff_card_le_card [V ⊧ₘ* 𝗭𝗙] {X Y : V}
    (hX : ∃ κ, IsCardinal κ ∧ κ ≋ X)
    (hY : ∃ κ, IsCardinal κ ∧ κ ≋ Y) :
    X ≤# Y ↔
      (⟨card X, (card_spec hX).1.1⟩ : Ordinal V) ≤
        ⟨card Y, (card_spec hY).1.1⟩ := by
  simpa [Ordinal.le_def] using cardLE_iff_card_subset_card (X := X) (Y := Y) hX hY

instance card_eq_definable : ℒₛₑₜ-relation[V] (fun κ X ↦ κ = card X) := by
  let R : V → V → Prop := fun κ X ↦
    (IsCardinal κ ∧ κ ≋ X) ∨
    (¬ ∃ α : V, IsCardinal α ∧ α ≋ X) ∧ κ = ∅
  have hR : ℒₛₑₜ-relation[V] R := by
    letI : ℒₛₑₜ-predicate[V] IsCardinal := IsCardinal.definable
    letI : ℒₛₑₜ-relation[V] CardEQ := CardEQ.definable
    show ℒₛₑₜ-relation[V] (fun κ X ↦
      (IsCardinal κ ∧ κ ≋ X) ∨
      (¬ ∃ α : V, IsCardinal α ∧ α ≋ X) ∧ κ = ∅)
    definability
  have hEq : (fun κ X ↦ κ = card X) = R := by
    funext κ X
    exact propext (card_eq_iff X κ)
  exact hEq ▸ hR

instance card.definable : ℒₛₑₜ-function₁[V] card := card_eq_definable

def IsCofinal (A X : V) : Prop := A ⊆ X ∧ ⋃ˢ A = X

instance IsCofinal.definable : ℒₛₑₜ-relation[V] IsCofinal := by
  letI : ℒₛₑₜ-function₁[V] sUnion := sUnion.definable
  unfold IsCofinal
  definability

def IsStrictIncreasingFunction (f α X : V) : Prop :=
  f ∈ X ^ α ∧ ∀ β ∈ α, ∀ γ ∈ α, β ∈ γ → f ‘ β ∈ f ‘ γ

instance IsStrictIncreasingFunction.definable :
    ℒₛₑₜ-relation₃[V] IsStrictIncreasingFunction := by
  letI : ℒₛₑₜ-function₂[V] (· ^ ·) := function.definable
  letI : ℒₛₑₜ-function₂[V] value := value.definable
  unfold IsStrictIncreasingFunction
  definability

lemma IsStrictIncreasingFunction.mem_function {f α X : V}
    (h : IsStrictIncreasingFunction f α X) :
    f ∈ X ^ α := h.1

def IsCofinalFunction (f α X : V) : Prop :=
  IsStrictIncreasingFunction f α X ∧ IsCofinal (range f) X

instance IsCofinalFunction.definable : ℒₛₑₜ-relation₃[V] IsCofinalFunction := by
  letI : ℒₛₑₜ-function₁[V] range := range.definable
  letI : ℒₛₑₜ-relation₃[V] IsStrictIncreasingFunction := IsStrictIncreasingFunction.definable
  letI : ℒₛₑₜ-relation[V] IsCofinal := IsCofinal.definable
  unfold IsCofinalFunction
  definability

lemma IsCofinalFunction.mem_function {f α X : V}
    (h : IsCofinalFunction f α X) :
    f ∈ X ^ α := h.1.1

lemma IsCofinalFunction.isCofinal {f α X : V}
    (h : IsCofinalFunction f α X) :
    IsCofinal (range f) X := h.2

def IsNondecreasingFunction (f α X : V) : Prop :=
  f ∈ X ^ α ∧ ∀ β ∈ α, ∀ γ ∈ α, β ∈ γ → f ‘ β ⊆ f ‘ γ

instance IsNondecreasingFunction.definable :
    ℒₛₑₜ-relation₃[V] IsNondecreasingFunction := by
  letI : ℒₛₑₜ-function₂[V] (· ^ ·) := function.definable
  letI : ℒₛₑₜ-function₂[V] value := value.definable
  unfold IsNondecreasingFunction
  definability

lemma IsNondecreasingFunction.mem_function {f α X : V}
    (h : IsNondecreasingFunction f α X) :
    f ∈ X ^ α := h.1

lemma IsNondecreasingFunction.comp_isCofinalFunction
    {f α β g X : V}
    (hf : IsCofinalFunction f α β) (hg : IsNondecreasingFunction g β X):
    IsNondecreasingFunction (compose f g) α X := by
  have hfFun : f ∈ β ^ α := hf.mem_function
  have hgFun : g ∈ X ^ β := hg.mem_function
  refine ⟨compose_function hfFun hgFun, ?_⟩
  intro ξ hξα ζ hζα hξζ
  have hfξβ : f ‘ ξ ∈ β := hf.isCofinal.1 _ (value_mem_range hfFun hξα)
  have hfζβ : f ‘ ζ ∈ β := hf.isCofinal.1 _ (value_mem_range hfFun hζα)
  have hsub : g ‘ (f ‘ ξ) ⊆ g ‘ (f ‘ ζ) := hg.2 _ hfξβ _ hfζβ (hf.1.2 _ hξα _ hζα hξζ)
  simpa [value_compose_eq hfFun hgFun hξα, value_compose_eq hfFun hgFun hζα] using hsub

lemma IsNondecreasingFunction.isCofinal_comp_isCofinalFunction
    {f α β g X : V}
    (hf : IsCofinalFunction f α β) (hg : IsNondecreasingFunction g β X)
    (hgCof : IsCofinal (range g) X) (hX : IsOrdinal X) :
    IsCofinal (range (compose f g)) X := by
  have hfFun : f ∈ β ^ α := hf.mem_function
  have hgFun : g ∈ X ^ β := hg.mem_function
  refine ⟨range_subset_of_mem_function (compose_function hfFun hgFun), ?_⟩
  ext z
  constructor
  · intro hz
    rcases mem_sUnion_iff.mp hz with ⟨y, hyRange, hzy⟩
    have hyX : y ∈ X := (range_subset_of_mem_function (compose_function hfFun hgFun)) _ hyRange
    exact hX.toIsTransitive.transitive _ hyX _ hzy
  · intro hzX
    have hzUnion : z ∈ ⋃ˢ range g := by rw [hgCof.2]; exact hzX
    rcases mem_sUnion_iff.mp hzUnion with ⟨y, hyRangeG, hzy⟩
    rcases mem_range_iff.mp hyRangeG with ⟨b, hbyg⟩
    have hbβ : b ∈ β := (mem_of_mem_functions hgFun hbyg).1
    have hbUnion : b ∈ ⋃ˢ range f := by rw [hf.isCofinal.2]; exact hbβ
    rcases mem_sUnion_iff.mp hbUnion with ⟨c, hcRangeF, hbc⟩
    rcases mem_range_iff.mp hcRangeF with ⟨a, haf⟩
    have hbygVal : g ‘ b = y := value_eq_of_kpair_mem hgFun hbyg
    have hsub : g ‘ b ⊆ g ‘ c := hg.2 _ hbβ _ (hf.isCofinal.1 _ hcRangeF) hbc
    have hzgc : z ∈ g ‘ c := by
      have hzgb : z ∈ g ‘ b := by simpa [hbygVal] using hzy
      exact hsub _ hzgb
    rcases exists_of_mem_function hgFun c (hf.isCofinal.1 _ hcRangeF) with ⟨u, -, hcug⟩
    have hcgc : ⟨c, g ‘ c⟩ₖ ∈ g := by
      have hcgVal : g ‘ c = u := value_eq_of_kpair_mem hgFun hcug
      simpa [hcgVal] using hcug
    refine mem_sUnion_iff.mpr ⟨g ‘ c, ?_, hzgc⟩
    exact mem_range_iff.mpr ⟨a, kpair_mem_compose_iff.mpr ⟨c, haf, hcgc⟩⟩

lemma isLimitOrdinal_of_isNondecreasingFunction_of_isCofinal
    {f β α : V}
    (hβ : IsOrdinal β) (hα : IsLimitOrdinal α)
    (hf : IsNondecreasingFunction f β α)
    (hCof : IsCofinal (range f) α) :
    IsLimitOrdinal β := by
  refine ⟨hβ, ?_, ?_⟩
  · intro h0
    have hfFun : f ∈ α ^ β := hf.mem_function
    have hdom : domain f = ∅ := by simpa [h0] using (domain_eq_of_mem_function hfFun)
    have hrange : range f = ∅ := by
      apply subset_empty_iff_eq_empty.mp
      intro y hy
      rcases mem_range_iff.mp hy with ⟨x, hxy⟩
      have hxDom : x ∈ domain f := mem_domain_of_kpair_mem hxy
      simp [hdom] at hxDom
    have hα0 : α = 0 := by
      simpa [hrange, zero_def] using hCof.2.symm
    exact hα.2.1 hα0
  · intro hsucc
    rcases hsucc with ⟨γ, rfl⟩
    have hfFun : f ∈ α ^ succ γ := hf.mem_function
    have hγmem : γ ∈ succ γ := by simp
    have hfγα : f ‘ γ ∈ α := hCof.1 _ (value_mem_range hfFun hγmem)
    have hαsub : α ⊆ f ‘ γ := by
      intro z hzα
      have hzUnion : z ∈ ⋃ˢ range f := by rw [hCof.2]; exact hzα
      rcases mem_sUnion_iff.mp hzUnion with ⟨y, hyRange, hzy⟩
      rcases mem_range_iff.mp hyRange with ⟨ξ, hξy⟩
      have hξSucc : ξ ∈ succ γ := (mem_of_mem_functions hfFun hξy).1
      have hξval : f ‘ ξ = y := value_eq_of_kpair_mem hfFun hξy
      rcases mem_succ_iff.mp hξSucc with (hξEq | hξγ)
      · have hyEq : y = f ‘ γ := by simpa [hξEq] using hξval.symm
        simpa [hyEq] using hzy
      · have hsub : f ‘ ξ ⊆ f ‘ γ := hf.2 _ hξSucc _ hγmem hξγ
        have hyfγ : y ⊆ f ‘ γ := by simpa [hξval] using hsub
        exact hyfγ _ hzy
    have hfγsub : f ‘ γ ⊆ α := hα.1.transitive _ hfγα
    have hEq : α = f ‘ γ := subset_antisymm hαsub hfγsub
    have : α ∈ α := hEq.symm ▸ hfγα
    exact (mem_irrefl α) this

def HasCofinalFunction (X : V) : Prop :=
  ∃ α : V, IsOrdinal α ∧ ∃ f : V, IsCofinalFunction f α X

instance HasCofinalFunction.definable : ℒₛₑₜ-predicate[V] HasCofinalFunction := by
  letI : ℒₛₑₜ-relation₃[V] IsCofinalFunction := IsCofinalFunction.definable
  unfold HasCofinalFunction
  definability

lemma existsUnique_cofinality (X : V)
    (hX : HasCofinalFunction X) :
    ∃! α : V, IsOrdinal α ∧ (∃ f : V, IsCofinalFunction f α X) ∧
      ∀ ξ : V, IsOrdinal ξ → (∃ g : V, IsCofinalFunction g ξ X) → α ⊆ ξ := by
  let P : V → Prop := fun α ↦ ∃ f : V, IsCofinalFunction f α X
  have hP : ℒₛₑₜ-predicate[V] P := by
    letI : ℒₛₑₜ-relation₃[V] IsCofinalFunction := IsCofinalFunction.definable
    change ℒₛₑₜ-predicate[V] (fun α ↦ ∃ f : V, IsCofinalFunction f α X)
    definability
  rcases exists_least_ordinal_of_exists (P := P) hP hX with
    ⟨α, hαord, hαP, hαleast⟩
  refine ⟨α, ⟨hαord, hαP, hαleast⟩, ?_⟩
  intro β hβ
  exact subset_antisymm
    (hβ.2.2 α hαord hαP)
    (hαleast β hβ.1 hβ.2.1)

/--
The least ordinal that is the domain of a strictly increasing cofinal function into `X`,
if such an ordinal exists, and `∅` otherwise.
-/
noncomputable def cofinality (X : V) : V :=
  Classical.extendedChoose! existsUnique_cofinality ∅ X

lemma cofinality_spec {X : V} (hX : HasCofinalFunction X) :
    IsOrdinal (cofinality X) ∧ (∃ f : V, IsCofinalFunction f (cofinality X) X) ∧
      ∀ ξ : V, IsOrdinal ξ → (∃ g : V, IsCofinalFunction g ξ X) → cofinality X ⊆ ξ := by
  simpa [cofinality] using
    (Classical.extendedchoose!_spec
      (h := existsUnique_cofinality) (default := (∅ : V)) (x := X) hX)

lemma cofinality_isOrdinal {X : V} (hX : HasCofinalFunction X) :
    IsOrdinal (cofinality X) :=
  (cofinality_spec hX).1

lemma cofinality_hasFunction {X : V} (hX : HasCofinalFunction X) :
    ∃ f : V, IsCofinalFunction f (cofinality X) X :=
  (cofinality_spec hX).2.1

lemma cofinality_least {X ξ : V} (hX : HasCofinalFunction X)
    (hξ : IsOrdinal ξ) (hξcof : ∃ g : V, IsCofinalFunction g ξ X) :
    cofinality X ⊆ ξ :=
  (cofinality_spec hX).2.2 ξ hξ hξcof

@[simp] lemma cofinality_eq_empty_of_not_hasCofinalFunction {X : V}
    (hX : ¬ HasCofinalFunction X) :
    cofinality X = ∅ := by
  simpa [cofinality] using
    (Classical.extendedchoose!_spec_not
      (h := existsUnique_cofinality) (default := (∅ : V)) (x := X) hX)

lemma cofinality_eq_iff (X α : V) :
    α = cofinality X ↔
      (IsOrdinal α ∧ (∃ f : V, IsCofinalFunction f α X) ∧
        ∀ ξ : V, IsOrdinal ξ → (∃ g : V, IsCofinalFunction g ξ X) → α ⊆ ξ) ∨
      (¬ HasCofinalFunction X ∧ α = ∅) := by
  by_cases hX : HasCofinalFunction X
  · have hEq :
        α = cofinality X ↔
          IsOrdinal α ∧ (∃ f : V, IsCofinalFunction f α X) ∧
            ∀ ξ : V, IsOrdinal ξ → (∃ g : V, IsCofinalFunction g ξ X) → α ⊆ ξ := by
      simpa [cofinality] using
        (Classical.extendedChoose!_eq_iff
          (h := existsUnique_cofinality) (default := (∅ : V)) (hpx := hX)
          (x := X) (y := α))
    constructor
    · intro hα
      exact Or.inl (hEq.mp hα)
    · rintro (hα | hα)
      · exact hEq.mpr hα
      · exact (hα.1 hX).elim
  · constructor
    · intro hα
      exact Or.inr ⟨hX, by simpa [cofinality_eq_empty_of_not_hasCofinalFunction hX] using hα⟩
    · rintro (hα | hα)
      · exact (hX ⟨α, hα.1, hα.2.1⟩).elim
      · simpa [cofinality_eq_empty_of_not_hasCofinalFunction hX] using hα.2

instance cofinality_eq_definable :
    ℒₛₑₜ-relation[V] (fun α X ↦ α = cofinality X) := by
  let R : V → V → Prop := fun α X ↦
    (IsOrdinal α ∧ (∃ f : V, IsCofinalFunction f α X) ∧
      ∀ ξ : V, IsOrdinal ξ → (∃ g : V, IsCofinalFunction g ξ X) → α ⊆ ξ) ∨
    (¬ HasCofinalFunction X ∧ α = ∅)
  have hR : ℒₛₑₜ-relation[V] R := by
    letI : ℒₛₑₜ-relation₃[V] IsCofinalFunction := IsCofinalFunction.definable
    letI : ℒₛₑₜ-predicate[V] HasCofinalFunction := HasCofinalFunction.definable
    show ℒₛₑₜ-relation[V] (fun α X ↦
      (IsOrdinal α ∧ (∃ f : V, IsCofinalFunction f α X) ∧
        ∀ ξ : V, IsOrdinal ξ → (∃ g : V, IsCofinalFunction g ξ X) → α ⊆ ξ) ∨
      (¬ HasCofinalFunction X ∧ α = ∅))
    definability
  have hEq : (fun α X ↦ α = cofinality X) = R := by
    funext α X
    exact propext (cofinality_eq_iff X α)
  exact hEq ▸ hR

instance cofinality.definable : ℒₛₑₜ-function₁[V] cofinality :=
  cofinality_eq_definable

def IsSmallCoveringFunction (f α X : V) : Prop :=
  f ∈ ℘ X ^ α ∧ (∀ Y ∈ range f, Y <# X) ∧ ⋃ˢ range f = X

instance IsSmallCoveringFunction.definable :
    ℒₛₑₜ-relation₃[V] IsSmallCoveringFunction := by
  letI : ℒₛₑₜ-function₁[V] power := power.definable
  letI : ℒₛₑₜ-function₂[V] (· ^ ·) := function.definable
  letI : ℒₛₑₜ-function₁[V] range := range.definable
  letI : ℒₛₑₜ-function₁[V] sUnion := sUnion.definable
  letI : ℒₛₑₜ-relation[V] CardLT := CardLT.definable
  unfold IsSmallCoveringFunction
  definability

lemma IsSmallCoveringFunction.mem_function {f α X : V}
    (h : IsSmallCoveringFunction f α X) :
    f ∈ ℘ X ^ α := h.1

def HasSmallCoveringFunction (X : V) : Prop :=
  ∃ α : V, IsOrdinal α ∧ ∃ f : V, IsSmallCoveringFunction f α X

instance HasSmallCoveringFunction.definable :
    ℒₛₑₜ-predicate[V] HasSmallCoveringFunction := by
  letI : ℒₛₑₜ-relation₃[V] IsSmallCoveringFunction := IsSmallCoveringFunction.definable
  unfold HasSmallCoveringFunction
  definability

lemma existsUnique_coveringNumber (X : V)
    (hX : HasSmallCoveringFunction X) :
    ∃! α : V, IsOrdinal α ∧ (∃ f : V, IsSmallCoveringFunction f α X) ∧
      ∀ ξ : V, IsOrdinal ξ → (∃ g : V, IsSmallCoveringFunction g ξ X) → α ⊆ ξ := by
  let P : V → Prop := fun α ↦ ∃ f : V, IsSmallCoveringFunction f α X
  have hP : ℒₛₑₜ-predicate[V] P := by
    letI : ℒₛₑₜ-relation₃[V] IsSmallCoveringFunction := IsSmallCoveringFunction.definable
    change ℒₛₑₜ-predicate[V] (fun α ↦ ∃ f : V, IsSmallCoveringFunction f α X)
    definability
  rcases exists_least_ordinal_of_exists (P := P) hP hX with
    ⟨α, hαord, hαP, hαleast⟩
  refine ⟨α, ⟨hαord, hαP, hαleast⟩, ?_⟩
  intro β hβ
  exact subset_antisymm
    (hβ.2.2 α hαord hαP)
    (hαleast β hβ.1 hβ.2.1)

/--
The least ordinal that is the domain of a function into `℘ X` whose values are all
cardinal-strictly-smaller than `X` and whose union is `X`, if such an ordinal exists,
and `∅` otherwise.
-/
noncomputable def coveringNumber (X : V) : V :=
  Classical.extendedChoose! existsUnique_coveringNumber ∅ X

lemma coveringNumber_spec {X : V} (hX : HasSmallCoveringFunction X) :
    IsOrdinal (coveringNumber X) ∧
      (∃ f : V, IsSmallCoveringFunction f (coveringNumber X) X) ∧
      ∀ ξ : V, IsOrdinal ξ → (∃ g : V, IsSmallCoveringFunction g ξ X) →
        coveringNumber X ⊆ ξ := by
  simpa [coveringNumber] using
    (Classical.extendedchoose!_spec
      (h := existsUnique_coveringNumber) (default := (∅ : V)) (x := X) hX)

lemma coveringNumber_isOrdinal {X : V} (hX : HasSmallCoveringFunction X) :
    IsOrdinal (coveringNumber X) :=
  (coveringNumber_spec hX).1

lemma coveringNumber_hasFunction {X : V} (hX : HasSmallCoveringFunction X) :
    ∃ f : V, IsSmallCoveringFunction f (coveringNumber X) X :=
  (coveringNumber_spec hX).2.1

lemma coveringNumber_least {X ξ : V} (hX : HasSmallCoveringFunction X)
    (hξ : IsOrdinal ξ) (hξcover : ∃ g : V, IsSmallCoveringFunction g ξ X) :
    coveringNumber X ⊆ ξ :=
  (coveringNumber_spec hX).2.2 ξ hξ hξcover

@[simp] lemma coveringNumber_eq_empty_of_not_hasSmallCoveringFunction {X : V}
    (hX : ¬ HasSmallCoveringFunction X) :
    coveringNumber X = ∅ := by
  simpa [coveringNumber] using
    (Classical.extendedchoose!_spec_not
      (h := existsUnique_coveringNumber) (default := (∅ : V)) (x := X) hX)

lemma coveringNumber_eq_iff (X α : V) :
    α = coveringNumber X ↔
      (IsOrdinal α ∧ (∃ f : V, IsSmallCoveringFunction f α X) ∧
        ∀ ξ : V, IsOrdinal ξ → (∃ g : V, IsSmallCoveringFunction g ξ X) → α ⊆ ξ) ∨
      (¬ HasSmallCoveringFunction X ∧ α = ∅) := by
  by_cases hX : HasSmallCoveringFunction X
  · have hEq :
        α = coveringNumber X ↔
          IsOrdinal α ∧ (∃ f : V, IsSmallCoveringFunction f α X) ∧
            ∀ ξ : V, IsOrdinal ξ → (∃ g : V, IsSmallCoveringFunction g ξ X) → α ⊆ ξ := by
      simpa [coveringNumber] using
        (Classical.extendedChoose!_eq_iff
          (h := existsUnique_coveringNumber) (default := (∅ : V)) (hpx := hX)
          (x := X) (y := α))
    constructor
    · intro hα
      exact Or.inl (hEq.mp hα)
    · rintro (hα | hα)
      · exact hEq.mpr hα
      · exact (hα.1 hX).elim
  · constructor
    · intro hα
      exact Or.inr ⟨hX, by simpa [coveringNumber_eq_empty_of_not_hasSmallCoveringFunction hX] using hα⟩
    · rintro (hα | hα)
      · exact (hX ⟨α, hα.1, hα.2.1⟩).elim
      · simpa [coveringNumber_eq_empty_of_not_hasSmallCoveringFunction hX] using hα.2

instance coveringNumber_eq_definable :
    ℒₛₑₜ-relation[V] (fun α X ↦ α = coveringNumber X) := by
  let R : V → V → Prop := fun α X ↦
    (IsOrdinal α ∧ (∃ f : V, IsSmallCoveringFunction f α X) ∧
      ∀ ξ : V, IsOrdinal ξ → (∃ g : V, IsSmallCoveringFunction g ξ X) → α ⊆ ξ) ∨
    (¬ HasSmallCoveringFunction X ∧ α = ∅)
  have hR : ℒₛₑₜ-relation[V] R := by
    letI : ℒₛₑₜ-relation₃[V] IsSmallCoveringFunction := IsSmallCoveringFunction.definable
    letI : ℒₛₑₜ-predicate[V] HasSmallCoveringFunction := HasSmallCoveringFunction.definable
    show ℒₛₑₜ-relation[V] (fun α X ↦
      (IsOrdinal α ∧ (∃ f : V, IsSmallCoveringFunction f α X) ∧
        ∀ ξ : V, IsOrdinal ξ → (∃ g : V, IsSmallCoveringFunction g ξ X) → α ⊆ ξ) ∨
      (¬ HasSmallCoveringFunction X ∧ α = ∅))
    definability
  have hEq : (fun α X ↦ α = coveringNumber X) = R := by
    funext α X
    exact propext (coveringNumber_eq_iff X α)
  exact hEq ▸ hR

instance coveringNumber.definable : ℒₛₑₜ-function₁[V] coveringNumber :=
  coveringNumber_eq_definable

lemma coveringNumber_isCardinal [V ⊧ₘ* 𝗭𝗙] (X : V) :
    IsCardinal (coveringNumber X) := by
  by_cases hX : HasSmallCoveringFunction X
  · have hαord : IsOrdinal (coveringNumber X) := coveringNumber_isOrdinal hX
    refine ⟨hαord, ?_⟩
    rcases coveringNumber_hasFunction hX with ⟨f, hf⟩
    have hfFun : f ∈ ℘ X ^ coveringNumber X := hf.mem_function
    intro β hβα hβαeq
    have hβord : IsOrdinal β := hαord.of_mem hβα
    rcases CardEQ.exists_bijective (V := V) hβαeq with ⟨e, heBij⟩
    have heFun : e ∈ coveringNumber X ^ β := heBij.mem_function
    let g : V := compose e f
    have hgFun : g ∈ ℘ X ^ β := compose_function heFun hfFun
    have hRange : range g = range f := by
      unfold g
      exact compose_range_eq_of_range_eq
        heFun (mem_function_range_of_mem_function hfFun) heBij.range_eq rfl
    have hg : IsSmallCoveringFunction g β X := by
      refine ⟨hgFun, ?_, ?_⟩
      · intro Y hY
        rw [hRange] at hY
        exact hf.2.1 Y hY
      · simpa [hRange] using hf.2.2
    have hαsubβ : coveringNumber X ⊆ β :=
      coveringNumber_least hX hβord ⟨g, hg⟩
    have hβsubα : β ⊆ coveringNumber X := hαord.transitive β hβα
    have hEq : coveringNumber X = β := subset_antisymm hαsubβ hβsubα
    exact (mem_irrefl β) (hEq.symm ▸ hβα)
  · have h0 : IsCardinal (∅ : V) := isCardinal_of_mem_ω (V := V) (by simp)
    simpa [coveringNumber_eq_empty_of_not_hasSmallCoveringFunction hX] using h0

lemma identity_isCofinalFunction_of_isLimitOrdinal {α : V}
    (hα : IsLimitOrdinal α) :
    IsCofinalFunction (identity α) α α := by
  refine ⟨?_, ?_⟩
  · refine ⟨identity_mem_function α, ?_⟩
    intro β hβα γ hγα hβγ
    have hβpair : ⟨β, β⟩ₖ ∈ identity α := by
      simpa using (show β ∈ α ∧ β = β from ⟨hβα, rfl⟩)
    have hγpair : ⟨γ, γ⟩ₖ ∈ identity α := by
      simpa using (show γ ∈ α ∧ γ = γ from ⟨hγα, rfl⟩)
    have hβval : (identity α) ‘ β = β := value_eq_of_kpair_mem (identity_mem_function α) hβpair
    have hγval : (identity α) ‘ γ = γ := value_eq_of_kpair_mem (identity_mem_function α) hγpair
    simpa [hβval, hγval] using hβγ
  · have hRange : range (identity α) = α := by
      ext z
      constructor
      · intro hz
        rcases mem_range_iff.mp hz with ⟨x, hx⟩
        rcases kpair_mem_identity_iff.mp hx with ⟨hxα, hxz⟩
        simpa [hxz] using hxα
      · intro hz
        exact mem_range_iff.mpr ⟨z, by
          simpa using (show z ∈ α ∧ z = z from ⟨hz, rfl⟩)⟩
    refine ⟨?_, ?_⟩
    · simp [hRange]
    · simpa [hRange] using hα.sUnion_eq

lemma IsCofinalFunction.comp {f α β g X : V}
    (hf : IsCofinalFunction f α β) (hg : IsCofinalFunction g β X)
    (hX : IsOrdinal X) :
    IsCofinalFunction (compose f g) α X := by
  have hfFun : f ∈ β ^ α := hf.mem_function
  have hgFun : g ∈ X ^ β := hg.mem_function
  have hfRangeSub : range f ⊆ β := hf.isCofinal.1
  have hfRangeEq : ⋃ˢ range f = β := hf.isCofinal.2
  have hgRangeSub : range g ⊆ X := hg.isCofinal.1
  have hgRangeEq : ⋃ˢ range g = X := hg.isCofinal.2
  refine ⟨?_, ?_⟩
  · refine ⟨compose_function hfFun hgFun, ?_⟩
    intro ξ hξα ζ hζα hξζ
    have hfξβ : f ‘ ξ ∈ β := hfRangeSub _ (value_mem_range hfFun hξα)
    have hfζβ : f ‘ ζ ∈ β := hfRangeSub _ (value_mem_range hfFun hζα)
    have hfg : g ‘ (f ‘ ξ) ∈ g ‘ (f ‘ ζ) := hg.1.2 _ hfξβ _ hfζβ (hf.1.2 _ hξα _ hζα hξζ)
    simpa [value_compose_eq hfFun hgFun hξα, value_compose_eq hfFun hgFun hζα] using hfg
  · refine ⟨range_subset_of_mem_function (compose_function hfFun hgFun), ?_⟩
    ext z
    constructor
    · intro hz
      rcases mem_sUnion_iff.mp hz with ⟨y, hyRange, hzy⟩
      have hyX : y ∈ X := (range_subset_of_mem_function (compose_function hfFun hgFun)) _ hyRange
      exact hX.toIsTransitive.transitive _ hyX _ hzy
    · intro hzX
      have hzUnion : z ∈ ⋃ˢ range g := by rw [hgRangeEq]; exact hzX
      rcases mem_sUnion_iff.mp hzUnion with ⟨y, hyRangeG, hzy⟩
      rcases mem_range_iff.mp hyRangeG with ⟨b, hbyg⟩
      have hbβ : b ∈ β := (mem_of_mem_functions hgFun hbyg).1
      have hbUnion : b ∈ ⋃ˢ range f := by rw [hfRangeEq]; exact hbβ
      rcases mem_sUnion_iff.mp hbUnion with ⟨c, hcRangeF, hbc⟩
      rcases mem_range_iff.mp hcRangeF with ⟨a, haf⟩
      have hcβ : c ∈ β := hfRangeSub _ hcRangeF
      have hbygVal : g ‘ b = y := value_eq_of_kpair_mem hgFun hbyg
      have hgbgc : g ‘ b ∈ g ‘ c := hg.1.2 _ hbβ _ hcβ hbc
      have hgcX : g ‘ c ∈ X := hgRangeSub _ (value_mem_range hgFun hcβ)
      have hgcOrd : IsOrdinal (g ‘ c) := hX.of_mem hgcX
      have hzgc : z ∈ g ‘ c := by
        have hzgb : z ∈ g ‘ b := by simpa [hbygVal] using hzy
        exact hgcOrd.toIsTransitive.transitive _ hgbgc _ hzgb
      rcases exists_of_mem_function hgFun c hcβ with ⟨u, -, hcug⟩
      have hcgc : ⟨c, g ‘ c⟩ₖ ∈ g := by
        have hcgVal : g ‘ c = u := value_eq_of_kpair_mem hgFun hcug
        simpa [hcgVal] using hcug
      refine mem_sUnion_iff.mpr ⟨g ‘ c, ?_, hzgc⟩
      exact mem_range_iff.mpr ⟨a, kpair_mem_compose_iff.mpr ⟨c, haf, hcgc⟩⟩

lemma hasCofinalFunction_of_isLimitOrdinal {α : V}
    (hα : IsLimitOrdinal α) :
    HasCofinalFunction α := by
  exact ⟨α, hα.1, ⟨identity α, identity_isCofinalFunction_of_isLimitOrdinal hα⟩⟩

lemma cofinality_subset_of_isLimitOrdinal {α : V}
    (hα : IsLimitOrdinal α) :
    cofinality α ⊆ α := by
  have hHas : HasCofinalFunction α := hasCofinalFunction_of_isLimitOrdinal hα
  exact cofinality_least hHas hα.1
    ⟨identity α, identity_isCofinalFunction_of_isLimitOrdinal hα⟩

lemma cofinality_isLimitOrdinal_of_isLimitOrdinal {α : V}
    (hα : IsLimitOrdinal α) :
    IsLimitOrdinal (cofinality α) := by
  have hHas : HasCofinalFunction α := hasCofinalFunction_of_isLimitOrdinal hα
  refine ⟨cofinality_isOrdinal hHas, ?_, ?_⟩
  · intro h0
    rcases cofinality_hasFunction hHas with ⟨f, hf⟩
    have hfFun : f ∈ α ^ cofinality α := hf.mem_function
    have hdom : domain f = ∅ := by
      simpa [h0] using (domain_eq_of_mem_function hfFun)
    have hrange : range f = ∅ := by
      apply subset_empty_iff_eq_empty.mp
      intro y hy
      rcases mem_range_iff.mp hy with ⟨x, hxy⟩
      have hxDom : x ∈ domain f := mem_domain_of_kpair_mem hxy
      simp [hdom] at hxDom
    have hα0 : α = 0 := by
      simpa [hrange, zero_def] using (hf.isCofinal.2.symm)
    exact hα.2.1 hα0
  · intro hsucc
    rcases hsucc with ⟨β, hβ⟩
    rcases cofinality_hasFunction hHas with ⟨f, hf⟩
    have hfFun : f ∈ α ^ succ β := by
      simpa [hβ] using hf.mem_function
    have hstrict : ∀ ξ ∈ succ β, ∀ ζ ∈ succ β, ξ ∈ ζ → f ‘ ξ ∈ f ‘ ζ := by
      simpa [hβ] using hf.1.2
    have hβmem : β ∈ succ β := by simp
    have hfβα : f ‘ β ∈ α := hf.isCofinal.1 _ (value_mem_range hfFun hβmem)
    have hfβord : IsOrdinal (f ‘ β) := hα.1.of_mem hfβα
    have hαsub : α ⊆ f ‘ β := by
      intro z hzα
      have hzUnion : z ∈ ⋃ˢ range f := by
        rw [hf.isCofinal.2]
        exact hzα
      rcases mem_sUnion_iff.mp hzUnion with ⟨y, hyRange, hzy⟩
      rcases mem_range_iff.mp hyRange with ⟨ξ, hξy⟩
      have hξSucc : ξ ∈ succ β := (mem_of_mem_functions hfFun hξy).1
      have hξval : f ‘ ξ = y := value_eq_of_kpair_mem hfFun hξy
      rcases mem_succ_iff.mp hξSucc with (hξEq | hξβ)
      · have hyEq : y = f ‘ β := by simpa [hξEq] using hξval.symm
        simpa [hyEq] using hzy
      · have hyfβ : y ∈ f ‘ β := by
          have hFξFβ : f ‘ ξ ∈ f ‘ β := hstrict ξ hξSucc β hβmem hξβ
          simpa [hξval] using hFξFβ
        exact hfβord.toIsTransitive.transitive _ hyfβ _ hzy
    have hfβsub : f ‘ β ⊆ α := hα.1.transitive _ hfβα
    have hEq : α = f ‘ β := subset_antisymm hαsub hfβsub
    have : α ∈ α := hEq.symm ▸ hfβα
    exact (mem_irrefl α) this

lemma cofinality_cofinality_eq_of_isLimitOrdinal {α : V}
    (hα : IsLimitOrdinal α) :
    cofinality (cofinality α) = cofinality α := by
  have hHasα : HasCofinalFunction α := hasCofinalFunction_of_isLimitOrdinal hα
  have hcofLim : IsLimitOrdinal (cofinality α) := cofinality_isLimitOrdinal_of_isLimitOrdinal hα
  have hHasCof : HasCofinalFunction (cofinality α) := hasCofinalFunction_of_isLimitOrdinal hcofLim
  have hLeft : cofinality (cofinality α) ⊆ cofinality α :=
    cofinality_subset_of_isLimitOrdinal hcofLim
  have hRight : cofinality α ⊆ cofinality (cofinality α) := by
    rcases cofinality_hasFunction hHasCof with ⟨f, hf⟩
    rcases cofinality_hasFunction hHasα with ⟨g, hg⟩
    exact cofinality_least hHasα (cofinality_isOrdinal hHasCof)
      ⟨compose f g, hf.comp hg hα.1⟩
  exact subset_antisymm hLeft hRight

lemma IsOrderIso.isCofinalFunction_of_isCofinal
    {α β X f : V} [IsOrdinal β]
    (hf : IsOrderIso (IsOrdinal.memRelOn β) β (IsOrdinal.memRelOn X) X f)
    (hX : IsCofinal X α) :
    IsCofinalFunction f β α := by
  have hfFunX : f ∈ X ^ β := hf.mem_function
  refine ⟨⟨mem_function_of_mem_function_of_subset hfFunX hX.1, ?_⟩, ?_⟩
  · intro ξ hξβ ζ hζβ hξζ
    have hξζRel : ⟨ξ, ζ⟩ₖ ∈ IsOrdinal.memRelOn β := by
      exact IsOrdinal.kpair_mem_memRelOn_iff.mpr ⟨hξβ, hζβ, hξζ⟩
    exact (IsOrdinal.kpair_mem_memRelOn_iff.mp ((hf.rel_iff hξβ hζβ).1 hξζRel)).2.2
  · refine ⟨?_, ?_⟩
    · simpa [hf.range_eq] using hX.1
    · simpa [hf.range_eq] using hX.2

lemma cofinality_subset_wellOrderTypeVal_memRelOn_of_isCofinal [V ⊧ₘ* 𝗭𝗙]
    {α X : V} (hα : IsLimitOrdinal α) (hX : IsCofinal X α) :
    cofinality α ⊆
      Ordinal.wellOrderTypeVal (IsOrdinal.memRelOn X) X
        (by
          letI : IsOrdinal α := hα.1
          exact IsOrdinal.wellOrderOn_memRelOn_subset (α := α) hX.1) := by
  letI : IsOrdinal α := hα.1
  let hXwo : IsWellOrderOn (IsOrdinal.memRelOn X) X :=
    IsOrdinal.wellOrderOn_memRelOn_subset (α := α) hX.1
  let β : V := Ordinal.wellOrderTypeVal (IsOrdinal.memRelOn X) X hXwo
  have hHas : HasCofinalFunction α := hasCofinalFunction_of_isLimitOrdinal hα
  have hβord : IsOrdinal β := by
    simpa [β] using (Ordinal.wellOrderTypeVal_spec (IsOrdinal.memRelOn X) X hXwo).1
  rcases Ordinal.wellOrderType_isOrderIso (S := IsOrdinal.memRelOn X) (Y := X) (hSwo := hXwo) with
    ⟨f, hf⟩
  exact cofinality_least hHas hβord ⟨f, hf.isCofinalFunction_of_isCofinal hX⟩

lemma cofinality_le_wellOrderType_memRelOn_of_isCofinal [V ⊧ₘ* 𝗭𝗙]
    {α X : V} (hα : IsLimitOrdinal α) (hX : IsCofinal X α) :
    ({ val := cofinality α
       ordinal := by
         exact cofinality_isOrdinal (hasCofinalFunction_of_isLimitOrdinal hα) } : Ordinal V) ≤
      Ordinal.wellOrderType (IsOrdinal.memRelOn X) X
        (by
          letI : IsOrdinal α := hα.1
          exact IsOrdinal.wellOrderOn_memRelOn_subset (α := α) hX.1) := by
  have hHas : HasCofinalFunction α := hasCofinalFunction_of_isLimitOrdinal hα
  let κ : Ordinal V := ⟨cofinality α, cofinality_isOrdinal hHas⟩
  letI : IsOrdinal α := hα.1
  simpa [κ, Ordinal.le_def, Ordinal.wellOrderType] using
    cofinality_subset_wellOrderTypeVal_memRelOn_of_isCofinal hα hX

lemma exists_isCofinalFunction_subset_of_mem_function_of_isCofinal [V ⊧ₘ* 𝗭𝗙]
    {f β α : V}
    (hβ : IsOrdinal β) (hα : IsLimitOrdinal α)
    (hf : f ∈ α ^ β)
    (hCof : IsCofinal (range f) α) :
    ∃ γ : V, IsOrdinal γ ∧ γ ⊆ β ∧ ∃ g : V, IsCofinalFunction g γ α := by
  letI : IsOrdinal β := hβ
  have hfFun : f ∈ α ^ β := hf
  let P : V → Prop := fun ξ ↦ ∀ η ∈ ξ, f ‘ η ∈ f ‘ ξ
  have hP : ℒₛₑₜ-predicate[V] P := by
    letI : ℒₛₑₜ-function₂[V] value := value.definable
    change ℒₛₑₜ-predicate[V] (fun ξ ↦ ∀ η ∈ ξ, f ‘ η ∈ f ‘ ξ)
    definability
  let R : V := sep β P hP
  have hRsub : R ⊆ β := sep_subset
  let hRwo : IsWellOrderOn (IsOrdinal.memRelOn R) R :=
    IsOrdinal.wellOrderOn_memRelOn_subset (α := β) hRsub
  let γ : V := Ordinal.wellOrderTypeVal (IsOrdinal.memRelOn R) R hRwo
  have hγord : IsOrdinal γ := by
    simpa [γ] using (Ordinal.wellOrderTypeVal_spec (IsOrdinal.memRelOn R) R hRwo).1
  rcases Ordinal.wellOrderType_isOrderIso (S := IsOrdinal.memRelOn R) (Y := R) (hSwo := hRwo) with
    ⟨e, he⟩
  have heFunβ : e ∈ β ^ γ := mem_function_of_mem_function_of_subset he.mem_function hRsub
  let g : V := compose e f
  have hgStrict : IsStrictIncreasingFunction g γ α := by
    refine ⟨compose_function heFunβ hfFun, ?_⟩
    intro ξ hξγ ζ hζγ hξζ
    have hξζRel : ⟨ξ, ζ⟩ₖ ∈ IsOrdinal.memRelOn γ :=
      IsOrdinal.kpair_mem_memRelOn_iff.mpr ⟨hξγ, hζγ, hξζ⟩
    have heRel : ⟨e ‘ ξ, e ‘ ζ⟩ₖ ∈ IsOrdinal.memRelOn R := (he.rel_iff hξγ hζγ).1 hξζRel
    have heζR : e ‘ ζ ∈ R := (IsOrdinal.kpair_mem_memRelOn_iff.mp heRel).2.1
    have heξζ : e ‘ ξ ∈ e ‘ ζ := (IsOrdinal.kpair_mem_memRelOn_iff.mp heRel).2.2
    have hRec : ∀ η ∈ e ‘ ζ, f ‘ η ∈ f ‘ (e ‘ ζ) := (mem_sep_iff.mp heζR).2
    have hmem : f ‘ (e ‘ ξ) ∈ f ‘ (e ‘ ζ) := hRec _ heξζ
    simpa [g, value_compose_eq heFunβ hfFun hξγ, value_compose_eq heFunβ hfFun hζγ] using hmem
  have hgCof : IsCofinal (range g) α := by
    letI : IsFunction f := IsFunction.of_mem hfFun
    refine ⟨range_subset_of_mem_function hgStrict.mem_function, ?_⟩
    ext z
    constructor
    · intro hz
      rcases mem_sUnion_iff.mp hz with ⟨y, hyRange, hzy⟩
      have hyα : y ∈ α := (range_subset_of_mem_function hgStrict.mem_function) _ hyRange
      exact hα.1.toIsTransitive.transitive _ hyα _ hzy
    · intro hzα
      have hzUnion : z ∈ ⋃ˢ range f := by rw [hCof.2]; exact hzα
      rcases mem_sUnion_iff.mp hzUnion with ⟨y, hyRangeF, hzy⟩
      rcases mem_range_iff.mp hyRangeF with ⟨ξ₀, hξ₀pair⟩
      have hξ₀β : ξ₀ ∈ β := (mem_of_mem_functions hfFun hξ₀pair).1
      have hξ₀val : f ‘ ξ₀ = y := value_eq_of_kpair_mem hfFun hξ₀pair
      let Q : V → Prop := fun ξ ↦ ξ ∈ β ∧ z ∈ f ‘ ξ
      have hQ : ℒₛₑₜ-predicate[V] Q := by
        letI : ℒₛₑₜ-function₂[V] value := value.definable
        change ℒₛₑₜ-predicate[V] (fun ξ ↦ ξ ∈ β ∧ z ∈ f ‘ ξ)
        definability
      have hEx : ∃ ξ : V, IsOrdinal ξ ∧ Q ξ := by
        refine ⟨ξ₀, hβ.of_mem hξ₀β, hξ₀β, ?_⟩
        simpa [hξ₀val] using hzy
      rcases exists_least_ordinal_of_exists (P := Q) hQ hEx with
        ⟨ξ, hξord, hξQ, hξleast⟩
      have hξβ : ξ ∈ β := hξQ.1
      have hzfξ : z ∈ f ‘ ξ := hξQ.2
      have hfξα : f ‘ ξ ∈ α := hCof.1 _ (value_mem_range hfFun hξβ)
      have hfξord : IsOrdinal (f ‘ ξ) := hα.1.of_mem hfξα
      have hξR : ξ ∈ R := by
        refine mem_sep_iff.mpr ⟨hξβ, ?_⟩
        intro η hηξ
        have hηβ : η ∈ β := hβ.toIsTransitive.transitive _ hξβ _ hηξ
        have hfηα : f ‘ η ∈ α := hCof.1 _ (value_mem_range hfFun hηβ)
        have hfηord : IsOrdinal (f ‘ η) := hα.1.of_mem hfηα
        letI : IsOrdinal (f ‘ η) := hfηord
        letI : IsOrdinal (f ‘ ξ) := hfξord
        rcases IsOrdinal.mem_trichotomy (α := f ‘ η) (β := f ‘ ξ) with (hηξ' | hEq | hξη')
        · exact hηξ'
        · have hzfη : z ∈ f ‘ η := by simpa [hEq] using hzfξ
          have hξsubη : ξ ⊆ η := hξleast η (hβ.of_mem hηβ) ⟨hηβ, hzfη⟩
          exact False.elim ((mem_irrefl η) (hξsubη _ hηξ))
        · have hzfη : z ∈ f ‘ η :=
            hfηord.toIsTransitive.transitive _ hξη' _ hzfξ
          have hξsubη : ξ ⊆ η := hξleast η (hβ.of_mem hηβ) ⟨hηβ, hzfη⟩
          exact False.elim ((mem_irrefl η) (hξsubη _ hηξ))
      have hξRangeE : ξ ∈ range e := by rw [he.range_eq]; exact hξR
      rcases mem_range_iff.mp hξRangeE with ⟨u, hue⟩
      have hξpair : ⟨ξ, f ‘ ξ⟩ₖ ∈ f := by
        have hξdom : ξ ∈ domain f := by simpa [domain_eq_of_mem_function hfFun] using hξβ
        exact (IsFunction.value_eq_iff_kpair_mem (f := f) (x := ξ) (y := f ‘ ξ) hξdom).mp rfl
      have hug : ⟨u, f ‘ ξ⟩ₖ ∈ g := by
        show ⟨u, f ‘ ξ⟩ₖ ∈ compose e f
        exact kpair_mem_compose_iff.mpr ⟨ξ, hue, hξpair⟩
      exact mem_sUnion_iff.mpr ⟨f ‘ ξ, mem_range_iff.mpr ⟨u, hug⟩, hzfξ⟩
  have hγsubβ : γ ⊆ β := by
    simpa [γ] using wellOrderTypeVal_memRelOn_subset_subset (α := β) (X := R) hRsub
  exact ⟨γ, hγord, hγsubβ, g, ⟨hgStrict, hgCof⟩⟩

lemma not_isCofinal_range_of_mem_function_of_mem_cofinality [V ⊧ₘ* 𝗭𝗙]
    {f β α : V}
    (hα : IsLimitOrdinal α) (hβ : β ∈ cofinality α)
    (hf : f ∈ α ^ β) :
    ¬ IsCofinal (range f) α := by
  have hHas : HasCofinalFunction α := hasCofinalFunction_of_isLimitOrdinal hα
  have hcofOrd : IsOrdinal (cofinality α) := cofinality_isOrdinal hHas
  have hβord : IsOrdinal β := hcofOrd.of_mem hβ
  intro hCof
  rcases exists_isCofinalFunction_subset_of_mem_function_of_isCofinal hβord hα hf hCof with
    ⟨γ, hγord, hγsubβ, g, hg⟩
  have hcofSubβ : cofinality α ⊆ β :=
    subset_trans (cofinality_least hHas hγord ⟨g, hg⟩) hγsubβ
  letI : IsOrdinal β := hβord
  letI : IsOrdinal (cofinality α) := hcofOrd
  rcases (IsOrdinal.subset_iff (α := cofinality α) (β := β)).1 hcofSubβ with (hEq | hcofβ)
  · have : cofinality α ∈ cofinality α := by
      simp [hEq] at hβ
    exact mem_irrefl (cofinality α) this
  · have : cofinality α ∈ cofinality α :=
      hcofOrd.toIsTransitive.transitive _ hβ _ hcofβ
    exact mem_irrefl (cofinality α) this

lemma exists_isCofinalFunction_subset_of_isNondecreasingFunction_of_isCofinal [V ⊧ₘ* 𝗭𝗙]
    {f β α : V}
    (hβ : IsOrdinal β) (hα : IsLimitOrdinal α)
    (hf : IsNondecreasingFunction f β α)
    (hCof : IsCofinal (range f) α) :
    ∃ γ : V, IsOrdinal γ ∧ γ ⊆ β ∧ ∃ g : V, IsCofinalFunction g γ α := by
  exact exists_isCofinalFunction_subset_of_mem_function_of_isCofinal
    hβ hα hf.mem_function hCof

private lemma replacement_graph_exists_on_of_definableRelation [V ⊧ₘ* 𝗭𝗙]
    (X : V) (R : V → V → Prop) (hR : ℒₛₑₜ-relation[V] R)
    (hfun : ∀ x : V, x ∈ X → ∃! y : V, R x y) :
    ∃ f : V, IsFunction f ∧ domain f = X ∧
      ∀ x ∈ X, ∀ y, ⟨x, y⟩ₖ ∈ f ↔ R x y := by
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
    have : y' = y := hyu _ hy'
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
  have hfFun : f ∈ range f ^ X := by
    apply mem_function.intro
    · intro p hp
      rcases (hmem _).1 hp with ⟨x, hxX, y, -, rfl⟩
      simpa [mem_prod_iff] using And.intro hxX (mem_range_iff.mpr ⟨x, by simpa⟩)
    · intro x hxX
      rcases hfun x hxX with ⟨y, hy, hyu⟩
      refine ⟨y, (hgraph x hxX y).2 hy, ?_⟩
      intro y' hxy'
      exact hyu _ ((hgraph x hxX y').1 hxy')
  exact ⟨f, IsFunction.of_mem hfFun, domain_eq_of_mem_function hfFun, hgraph⟩

private lemma range_cardLE_of_mem_function_of_subset_of_isOrdinal [V ⊧ₘ* 𝗭𝗙]
    {f A β X : V}
    (hβ : IsOrdinal β) (hAβ : A ⊆ β) (hf : f ∈ X ^ A) :
    range f ≤# β := by
  let R : V → V → Prop := fun y ξ ↦
    ξ ∈ A ∧ f ‘ ξ = y ∧
      ∀ ν : V, IsOrdinal ν → ν ∈ A → f ‘ ν = y → ξ ⊆ ν
  have hR : ℒₛₑₜ-relation[V] R := by
    letI : ℒₛₑₜ-function₂[V] value := value.definable
    change ℒₛₑₜ-relation[V] (fun y ξ ↦
      ξ ∈ A ∧ f ‘ ξ = y ∧
        ∀ ν : V, IsOrdinal ν → ν ∈ A → f ‘ ν = y → ξ ⊆ ν)
    definability
  have hfun : ∀ y : V, y ∈ range f → ∃! ξ : V, R y ξ := by
    intro y hyRange
    let Q : V → Prop := fun ξ ↦ ξ ∈ A ∧ f ‘ ξ = y
    have hQ : ℒₛₑₜ-predicate[V] Q := by
      letI : ℒₛₑₜ-function₂[V] value := value.definable
      change ℒₛₑₜ-predicate[V] (fun ξ ↦ ξ ∈ A ∧ f ‘ ξ = y)
      definability
    have hEx : ∃ ξ : V, IsOrdinal ξ ∧ Q ξ := by
      rcases mem_range_iff.mp hyRange with ⟨ξ₀, hξ₀pair⟩
      have hξ₀A : ξ₀ ∈ A := (mem_of_mem_functions hf hξ₀pair).1
      refine ⟨ξ₀, IsOrdinal.of_mem (hAβ _ hξ₀A), hξ₀A, ?_⟩
      exact value_eq_of_kpair_mem hf hξ₀pair
    rcases exists_least_ordinal_of_exists (P := Q) hQ hEx with
      ⟨ξ, hξord, hξQ, hξleast⟩
    refine ⟨ξ, ⟨hξQ.1, hξQ.2, ?_⟩, ?_⟩
    · intro ν hνord hνA hfy
      exact hξleast ν hνord ⟨hνA, hfy⟩
    · intro μ hμ
      rcases hμ with ⟨hμA, hfμ, hμleast⟩
      exact subset_antisymm
        (hμleast ξ hξord hξQ.1 hξQ.2)
        (hξleast μ (IsOrdinal.of_mem (hAβ _ hμA)) ⟨hμA, hfμ⟩)
  rcases replacement_graph_exists_on_of_definableRelation (X := range f) R hR hfun with
    ⟨s, hsFunc, hsDom, hsGraph⟩
  letI : IsFunction s := hsFunc
  have hsRangeSub : range s ⊆ β := by
    intro ξ hξRange
    rcases mem_range_iff.mp hξRange with ⟨y, hyξ⟩
    have hyRange : y ∈ range f := by
      simpa [hsDom] using mem_domain_of_kpair_mem hyξ
    exact hAβ _ ((hsGraph y hyRange ξ).1 hyξ).1
  have hsFun : s ∈ β ^ range f := by
    apply mem_function.intro
    · intro p hp
      rcases show ∃ y ∈ domain s, ∃ ξ ∈ range s, p = ⟨y, ξ⟩ₖ from by
          simpa [mem_prod_iff] using subset_prod_of_mem_function (IsFunction.mem_function s) _ hp with
        ⟨y, hyDom, ξ, hξRange, rfl⟩
      have hyRange : y ∈ range f := by simpa [hsDom] using hyDom
      have hξβ : ξ ∈ β := hsRangeSub _ hξRange
      exact mem_prod_iff.mpr ⟨y, hyRange, ξ, hξβ, rfl⟩
    · intro y hyRange
      rcases hfun y hyRange with ⟨ξ, hξ, hξuniq⟩
      refine ⟨ξ, (hsGraph y hyRange ξ).2 hξ, ?_⟩
      intro ξ' hyξ'
      exact hξuniq _ ((hsGraph y hyRange ξ').1 hyξ')
  have hsInj : Injective s := by
    intro y₁ y₂ ξ hy₁ hy₂
    have hy₁Range : y₁ ∈ range f := by
      simpa [hsDom] using mem_domain_of_kpair_mem hy₁
    have hy₂Range : y₂ ∈ range f := by
      simpa [hsDom] using mem_domain_of_kpair_mem hy₂
    have hR₁ : R y₁ ξ := (hsGraph y₁ hy₁Range ξ).1 hy₁
    have hR₂ : R y₂ ξ := (hsGraph y₂ hy₂Range ξ).1 hy₂
    exact hR₁.2.1.symm.trans hR₂.2.1
  exact ⟨s, hsFun, hsInj⟩

private lemma cardLE_power_of_nonempty_domain [V ⊧ₘ* 𝗭𝗙] {X Y : V} [IsNonempty X] :
    Y ≤# Y ^ X := by
  let R : V → V → Prop := fun y g ↦
    y ∈ Y ∧ g ∈ Y ^ X ∧ ∀ ξ ∈ X, ∀ z, ⟨ξ, z⟩ₖ ∈ g ↔ z = y
  have hR : ℒₛₑₜ-relation[V] R := by
    change ℒₛₑₜ-relation[V] (fun y g ↦
      y ∈ Y ∧ g ∈ Y ^ X ∧ ∀ ξ ∈ X, ∀ z, ⟨ξ, z⟩ₖ ∈ g ↔ z = y)
    definability
  have hfun : ∀ y : V, y ∈ Y → ∃! g : V, R y g := by
    intro y hyY
    have hConstDef : ℒₛₑₜ-function₁[V] (fun _ : V ↦ y) := by
      change ℒₛₑₜ-function₁[V] (fun _ : V ↦ y)
      definability
    rcases graph_exists_mem_function_of_definableFunction
        X Y (fun _ : V ↦ y) hConstDef (fun _ _ ↦ hyY) with
      ⟨g, hgFun, hgGraph⟩
    refine ⟨g, ⟨hyY, hgFun, ?_⟩, ?_⟩
    · intro ξ hξX z
      simpa using hgGraph ξ hξX z
    · intro g' hg'
      rcases hg' with ⟨-, hg'Fun, hg'Graph⟩
      apply subset_antisymm
      · intro p hp
        rcases show ∃ ξ ∈ X, ∃ z ∈ Y, p = ⟨ξ, z⟩ₖ from by
            simpa [mem_prod_iff] using subset_prod_of_mem_function hg'Fun _ hp with
          ⟨ξ, hξX, z, hzY, rfl⟩
        have hzy : z = y := (hg'Graph ξ hξX z).1 hp
        exact (hgGraph ξ hξX z).2 hzy
      · intro p hp
        rcases show ∃ ξ ∈ X, ∃ z ∈ Y, p = ⟨ξ, z⟩ₖ from by
            simpa [mem_prod_iff] using subset_prod_of_mem_function hgFun _ hp with
          ⟨ξ, hξX, z, hzY, rfl⟩
        have hzy : z = y := (hgGraph ξ hξX z).1 hp
        exact (hg'Graph ξ hξX z).2 hzy
  rcases replacement_graph_exists_on_of_definableRelation (X := Y) R hR hfun with
    ⟨s, hsFunc, hsDom, hsGraph⟩
  letI : IsFunction s := hsFunc
  have hsRangeSub : range s ⊆ Y ^ X := by
    intro g hgRange
    rcases mem_range_iff.mp hgRange with ⟨y, hyg⟩
    have hyY : y ∈ Y := by simpa [hsDom] using mem_domain_of_kpair_mem hyg
    exact ((hsGraph y hyY g).1 hyg).2.1
  have hsFun : s ∈ (Y ^ X) ^ Y := by
    apply mem_function.intro
    · intro p hp
      rcases show ∃ y ∈ domain s, ∃ g ∈ range s, p = ⟨y, g⟩ₖ from by
          simpa [mem_prod_iff] using subset_prod_of_mem_function (IsFunction.mem_function s) _ hp with
        ⟨y, hyDom, g, hgRange, rfl⟩
      have hyY : y ∈ Y := by simpa [hsDom] using hyDom
      have hgPow : g ∈ Y ^ X := hsRangeSub _ hgRange
      exact mem_prod_iff.mpr ⟨y, hyY, g, hgPow, rfl⟩
    · intro y hyY
      rcases hfun y hyY with ⟨g, hg, hguniq⟩
      refine ⟨g, (hsGraph y hyY g).2 hg, ?_⟩
      intro g' hyg'
      exact hguniq _ ((hsGraph y hyY g').1 hyg')
  rcases IsNonempty.nonempty (a := X) with ⟨x₀, hx₀X⟩
  have hsInj : Injective s := by
    intro y₁ y₂ g hy₁ hy₂
    have hy₁Y : y₁ ∈ Y := by simpa [hsDom] using mem_domain_of_kpair_mem hy₁
    have hy₂Y : y₂ ∈ Y := by simpa [hsDom] using mem_domain_of_kpair_mem hy₂
    rcases (hsGraph y₁ hy₁Y g).1 hy₁ with ⟨-, -, hGraph₁⟩
    rcases (hsGraph y₂ hy₂Y g).1 hy₂ with ⟨-, -, hGraph₂⟩
    have hx₂ : ⟨x₀, y₂⟩ₖ ∈ g := (hGraph₂ x₀ hx₀X y₂).2 rfl
    exact ((hGraph₁ x₀ hx₀X y₂).1 hx₂).symm
  exact ⟨s, hsFun, hsInj⟩

lemma cofinality_codomain_subset_domain_of_isNondecreasingFunction_of_isCofinal [V ⊧ₘ* 𝗭𝗙]
    {f β α : V}
    (hβ : IsOrdinal β) (hα : IsLimitOrdinal α)
    (hf : IsNondecreasingFunction f β α)
    (hCof : IsCofinal (range f) α) :
    cofinality α ⊆ cofinality β := by
  have hβlim : IsLimitOrdinal β :=
    isLimitOrdinal_of_isNondecreasingFunction_of_isCofinal hβ hα hf hCof
  have hHasα : HasCofinalFunction α := hasCofinalFunction_of_isLimitOrdinal hα
  have hHasβ : HasCofinalFunction β := hasCofinalFunction_of_isLimitOrdinal hβlim
  rcases cofinality_hasFunction hHasβ with ⟨g, hg⟩
  have hcompNondec : IsNondecreasingFunction (compose g f) (cofinality β) α :=
    IsNondecreasingFunction.comp_isCofinalFunction hg hf
  have hcompCof : IsCofinal (range (compose g f)) α :=
    IsNondecreasingFunction.isCofinal_comp_isCofinalFunction hg hf hCof hα.1
  rcases exists_isCofinalFunction_subset_of_isNondecreasingFunction_of_isCofinal
      (hβ := cofinality_isOrdinal hHasβ) (hα := hα) hcompNondec hcompCof with
    ⟨γ, hγord, hγsub, hγf, hhγf⟩
  exact subset_trans (cofinality_least hHasα hγord ⟨hγf, hhγf⟩) hγsub

lemma cofinality_domain_subset_codomain_of_isNondecreasingFunction_of_isCofinal [V ⊧ₘ* 𝗭𝗙]
    {f β α : V}
    (hβ : IsOrdinal β) (hα : IsLimitOrdinal α)
    (hf : IsNondecreasingFunction f β α)
    (hCof : IsCofinal (range f) α) :
    cofinality β ⊆ cofinality α := by
  have hfFun : f ∈ α ^ β := hf.mem_function
  have hβlim : IsLimitOrdinal β :=
    isLimitOrdinal_of_isNondecreasingFunction_of_isCofinal hβ hα hf hCof
  have hHasα : HasCofinalFunction α := hasCofinalFunction_of_isLimitOrdinal hα
  have hHasβ : HasCofinalFunction β := hasCofinalFunction_of_isLimitOrdinal hβlim
  let δ : V := cofinality α
  have hδord : IsOrdinal δ := cofinality_isOrdinal hHasα
  rcases cofinality_hasFunction hHasα with ⟨g, hg⟩
  have hgFun : g ∈ α ^ δ := hg.mem_function
  let Hit : V → V → Prop := fun ξ η ↦
    η ∈ β ∧ g ‘ ξ ∈ f ‘ η ∧
      ∀ ν : V, IsOrdinal ν → ν ∈ β → g ‘ ξ ∈ f ‘ ν → η ⊆ ν
  have hHitDef : ℒₛₑₜ-relation[V] Hit := by
    letI : ℒₛₑₜ-function₂[V] value := value.definable
    change ℒₛₑₜ-relation[V] (fun ξ η ↦
      η ∈ β ∧ g ‘ ξ ∈ f ‘ η ∧
        ∀ ν : V, IsOrdinal ν → ν ∈ β → g ‘ ξ ∈ f ‘ ν → η ⊆ ν)
    definability
  have hHitFun : ∀ ξ : V, ξ ∈ δ → ∃! η : V, Hit ξ η := by
    intro ξ hξδ
    let Q : V → Prop := fun η ↦ η ∈ β ∧ g ‘ ξ ∈ f ‘ η
    have hQ : ℒₛₑₜ-predicate[V] Q := by
      letI : ℒₛₑₜ-function₂[V] value := value.definable
      change ℒₛₑₜ-predicate[V] (fun η ↦ η ∈ β ∧ g ‘ ξ ∈ f ‘ η)
      definability
    have hEx : ∃ η : V, IsOrdinal η ∧ Q η := by
      have hgξα : g ‘ ξ ∈ α := hg.isCofinal.1 _ (value_mem_range hgFun hξδ)
      have hgξUnion : g ‘ ξ ∈ ⋃ˢ range f := by rw [hCof.2]; exact hgξα
      rcases mem_sUnion_iff.mp hgξUnion with ⟨y, hyRangeF, hξy⟩
      rcases mem_range_iff.mp hyRangeF with ⟨η₀, hη₀pair⟩
      have hη₀β : η₀ ∈ β := (mem_of_mem_functions hfFun hη₀pair).1
      have hη₀val : f ‘ η₀ = y := value_eq_of_kpair_mem hfFun hη₀pair
      refine ⟨η₀, hβ.of_mem hη₀β, hη₀β, ?_⟩
      simpa [hη₀val] using hξy
    rcases exists_least_ordinal_of_exists (P := Q) hQ hEx with ⟨η, hηord, hηQ, hηleast⟩
    refine ⟨η, ?_, ?_⟩
    · exact ⟨hηQ.1, hηQ.2, fun ν hνord hνβ hξν ↦ hηleast ν hνord ⟨hνβ, hξν⟩⟩
    · intro μ hμ
      exact subset_antisymm
        (hμ.2.2 η hηord hηQ.1 hηQ.2)
        (hηleast μ (hβ.of_mem hμ.1) ⟨hμ.1, hμ.2.1⟩)
  rcases replacement_graph_exists_on_of_definableRelation (X := δ) Hit hHitDef hHitFun with
    ⟨s, hsFunction, hsDom, hsGraph⟩
  letI : IsFunction s := hsFunction
  have hsRangeSub : range s ⊆ β := by
    intro η hηRange
    rcases mem_range_iff.mp hηRange with ⟨ξ, hξη⟩
    have hξδ : ξ ∈ δ := by simpa [hsDom] using mem_domain_of_kpair_mem hξη
    exact ((hsGraph ξ hξδ η).1 hξη).1
  have hsFun : s ∈ β ^ δ := by
    apply mem_function.intro
    · intro p hp
      rcases show ∃ ξ ∈ domain s, ∃ η ∈ range s, p = ⟨ξ, η⟩ₖ from by
          simpa [mem_prod_iff] using subset_prod_of_mem_function (IsFunction.mem_function s) _ hp with
        ⟨ξ, hξdom, η, hηRange, rfl⟩
      have hξδ : ξ ∈ δ := by simpa [hsDom] using hξdom
      have hηβ : η ∈ β := hsRangeSub _ hηRange
      exact mem_prod_iff.mpr ⟨ξ, hξδ, η, hηβ, rfl⟩
    · intro ξ hξδ
      rcases hHitFun ξ hξδ with ⟨η, hη, hηuniq⟩
      refine ⟨η, (hsGraph ξ hξδ η).2 hη, ?_⟩
      intro η' hξη'
      exact hηuniq _ ((hsGraph ξ hξδ η').1 hξη')
  have hsNondec : IsNondecreasingFunction s δ β := by
    refine ⟨hsFun, ?_⟩
    intro ξ hξδ ζ hζδ hξζ
    have hsξβ : s ‘ ξ ∈ β := hsRangeSub _ (value_mem_range hsFun hξδ)
    have hsζβ : s ‘ ζ ∈ β := hsRangeSub _ (value_mem_range hsFun hζδ)
    have hξdom : ξ ∈ domain s := by simpa [domain_eq_of_mem_function hsFun] using hξδ
    have hζdom : ζ ∈ domain s := by simpa [domain_eq_of_mem_function hsFun] using hζδ
    have hξpair : ⟨ξ, s ‘ ξ⟩ₖ ∈ s :=
      (IsFunction.value_eq_iff_kpair_mem (f := s) (x := ξ) (y := s ‘ ξ) hξdom).mp rfl
    have hζpair : ⟨ζ, s ‘ ζ⟩ₖ ∈ s :=
      (IsFunction.value_eq_iff_kpair_mem (f := s) (x := ζ) (y := s ‘ ζ) hζdom).mp rfl
    have hHitξ : Hit ξ (s ‘ ξ) := (hsGraph ξ hξδ (s ‘ ξ)).1 hξpair
    have hHitζ : Hit ζ (s ‘ ζ) := (hsGraph ζ hζδ (s ‘ ζ)).1 hζpair
    have hfsζα : f ‘ (s ‘ ζ) ∈ α := hCof.1 _ (value_mem_range hfFun hsζβ)
    have hfsζord : IsOrdinal (f ‘ (s ‘ ζ)) := hα.1.of_mem hfsζα
    have hgξζ : g ‘ ξ ∈ g ‘ ζ := hg.1.2 _ hξδ _ hζδ hξζ
    have hgξfsζ : g ‘ ξ ∈ f ‘ (s ‘ ζ) :=
      hfsζord.toIsTransitive.transitive _ hHitζ.2.1 _ hgξζ
    exact hHitξ.2.2 _ (hβ.of_mem hsζβ) hsζβ hgξfsζ
  have hsCof : IsCofinal (range s) β := by
    refine ⟨hsRangeSub, ?_⟩
    ext η
    constructor
    · intro hηUnion
      rcases mem_sUnion_iff.mp hηUnion with ⟨y, hyRange, hηy⟩
      have hyβ : y ∈ β := hsRangeSub _ hyRange
      exact hβ.toIsTransitive.transitive _ hyβ _ hηy
    · intro hηβ
      have hfηα : f ‘ η ∈ α := hCof.1 _ (value_mem_range hfFun hηβ)
      have hfηUnion : f ‘ η ∈ ⋃ˢ range g := by rw [hg.isCofinal.2]; exact hfηα
      rcases mem_sUnion_iff.mp hfηUnion with ⟨y, hyRangeG, hfηy⟩
      rcases mem_range_iff.mp hyRangeG with ⟨ξ, hξpairG⟩
      have hξδ : ξ ∈ δ := (mem_of_mem_functions hgFun hξpairG).1
      have hξval : g ‘ ξ = y := value_eq_of_kpair_mem hgFun hξpairG
      have hsξβ : s ‘ ξ ∈ β := hsRangeSub _ (value_mem_range hsFun hξδ)
      have hξdom : ξ ∈ domain s := by simpa [domain_eq_of_mem_function hsFun] using hξδ
      have hξpairS : ⟨ξ, s ‘ ξ⟩ₖ ∈ s :=
        (IsFunction.value_eq_iff_kpair_mem (f := s) (x := ξ) (y := s ‘ ξ) hξdom).mp rfl
      have hHitξ : Hit ξ (s ‘ ξ) := (hsGraph ξ hξδ (s ‘ ξ)).1 hξpairS
      have hfηord : IsOrdinal (f ‘ η) := hα.1.of_mem hfηα
      have hEqImpossible : η = s ‘ ξ → False := by
        intro hEq
        have hgξfη : g ‘ ξ ∈ f ‘ η := by simpa [hEq] using hHitξ.2.1
        have : f ‘ η ∈ f ‘ η :=
          hfηord.toIsTransitive.transitive _ hgξfη _ (by simpa [hξval] using hfηy)
        exact (mem_irrefl (f ‘ η)) this
      have hLtImpossible : s ‘ ξ ∈ η → False := by
        intro hsξη
        have hsub : f ‘ (s ‘ ξ) ⊆ f ‘ η := hf.2 _ hsξβ _ hηβ hsξη
        have hgξfη : g ‘ ξ ∈ f ‘ η := hsub _ hHitξ.2.1
        have : f ‘ η ∈ f ‘ η :=
          hfηord.toIsTransitive.transitive _ hgξfη _ (by simpa [hξval] using hfηy)
        exact (mem_irrefl (f ‘ η)) this
      letI : IsOrdinal η := hβ.of_mem hηβ
      letI : IsOrdinal (s ‘ ξ) := hβ.of_mem hsξβ
      rcases IsOrdinal.mem_trichotomy (α := η) (β := s ‘ ξ) with (hηs | hEq | hsη)
      · exact mem_sUnion_iff.mpr ⟨s ‘ ξ, value_mem_range hsFun hξδ, hηs⟩
      · exact False.elim (hEqImpossible hEq)
      · exact False.elim (hLtImpossible hsη)
  rcases exists_isCofinalFunction_subset_of_isNondecreasingFunction_of_isCofinal
      (hβ := hδord) (hα := hβlim) hsNondec hsCof with
    ⟨γ, hγord, hγsub, hγf, hhγf⟩
  exact subset_trans (cofinality_least hHasβ hγord ⟨hγf, hhγf⟩) hγsub

lemma cofinality_eq_of_isNondecreasingFunction_of_isCofinal [V ⊧ₘ* 𝗭𝗙]
    {f β α : V}
    (hβ : IsOrdinal β) (hα : IsLimitOrdinal α)
    (hf : IsNondecreasingFunction f β α)
    (hCof : IsCofinal (range f) α) :
    cofinality β = cofinality α := by
  exact subset_antisymm
    (cofinality_domain_subset_codomain_of_isNondecreasingFunction_of_isCofinal hβ hα hf hCof)
    (cofinality_codomain_subset_domain_of_isNondecreasingFunction_of_isCofinal hβ hα hf hCof)

lemma cofinality_mem_of_isLimitOrdinal_of_not_isCardinal [V ⊧ₘ* 𝗭𝗙] {α : V}
    (hα : IsLimitOrdinal α) (hNotCard : ¬ IsCardinal α) :
    cofinality α ∈ α := by
  have hWitness : ∃ β : V, β ∈ α ∧ β ≋ α := by
    by_contra hNo
    apply hNotCard
    refine ⟨hα.1, ?_⟩
    intro β hβα hβeq
    exact hNo ⟨β, hβα, hβeq⟩
  rcases hWitness with ⟨β, hβα, hβeq⟩
  have hβord : IsOrdinal β := hα.1.of_mem hβα
  rcases CardEQ.exists_bijective (V := V) hβeq with ⟨f, hfBij⟩
  have hRangeCof : IsCofinal (range f) α := by
    refine ⟨?_, ?_⟩
    · simp [hfBij.range_eq]
    · simpa [hfBij.range_eq] using hα.sUnion_eq
  have hHasα : HasCofinalFunction α := hasCofinalFunction_of_isLimitOrdinal hα
  rcases exists_isCofinalFunction_subset_of_mem_function_of_isCofinal
      hβord hα hfBij.mem_function hRangeCof with
    ⟨γ, hγord, hγsubβ, g, hg⟩
  have hcofsubβ : cofinality α ⊆ β :=
    subset_trans (cofinality_least hHasα hγord ⟨g, hg⟩) hγsubβ
  letI : IsOrdinal (cofinality α) := cofinality_isOrdinal hHasα
  letI : IsOrdinal β := hβord
  rcases (IsOrdinal.subset_iff (α := cofinality α) (β := β)).1 hcofsubβ with (hEq | hMem)
  · exact hEq.symm ▸ hβα
  · exact hα.1.toIsTransitive.transitive _ hβα _ hMem

def IsLimitCardinal [V ⊧ₘ* 𝗭𝗙] (κ : V) : Prop :=
  IsCardinal κ ∧ (ω : V) ⊆ κ ∧ ¬ ∃ ξ : V, κ = hartogs ξ

instance IsLimitCardinal.definable [V ⊧ₘ* 𝗭𝗙] : ℒₛₑₜ-predicate[V] IsLimitCardinal := by
  letI : ℒₛₑₜ-function₁[V] hartogs := hartogs.definable
  unfold IsLimitCardinal
  definability

def IsRegular (κ : V) : Prop := cofinality κ = κ

instance IsRegular.definable : ℒₛₑₜ-predicate[V] IsRegular := by
  letI : ℒₛₑₜ-function₁[V] cofinality := cofinality.definable
  unfold IsRegular
  definability

def IsWeaklyInaccessible [V ⊧ₘ* 𝗭𝗙] (κ : V) : Prop :=
  IsLimitCardinal κ ∧ IsRegular κ

instance IsWeaklyInaccessible.definable [V ⊧ₘ* 𝗭𝗙] :
    ℒₛₑₜ-predicate[V] IsWeaklyInaccessible := by
  letI : ℒₛₑₜ-predicate[V] IsLimitCardinal := IsLimitCardinal.definable
  unfold IsWeaklyInaccessible
  definability

lemma cofinality_isCardinal_of_isLimitOrdinal [V ⊧ₘ* 𝗭𝗙] {α : V}
    (hα : IsLimitOrdinal α) :
    IsCardinal (cofinality α) := by
  have hcofLim : IsLimitOrdinal (cofinality α) :=
    cofinality_isLimitOrdinal_of_isLimitOrdinal hα
  by_contra hNotCard
  have hmem : cofinality (cofinality α) ∈ cofinality α :=
    cofinality_mem_of_isLimitOrdinal_of_not_isCardinal hcofLim hNotCard
  have hEq : cofinality (cofinality α) = cofinality α :=
    cofinality_cofinality_eq_of_isLimitOrdinal hα
  exact mem_irrefl (cofinality (cofinality α)) (hEq.symm ▸ hmem)

lemma cofinality_isRegular_of_isLimitOrdinal [V ⊧ₘ* 𝗭𝗙] {α : V}
    (hα : IsLimitOrdinal α) :
    IsRegular (cofinality α) := by
  exact cofinality_cofinality_eq_of_isLimitOrdinal hα

lemma cofinality_isRegularCardinal_of_isLimitOrdinal [V ⊧ₘ* 𝗭𝗙] {α : V}
    (hα : IsLimitOrdinal α) :
    IsCardinal (cofinality α) ∧ IsRegular (cofinality α) := by
  exact ⟨cofinality_isCardinal_of_isLimitOrdinal hα, cofinality_isRegular_of_isLimitOrdinal hα⟩

lemma exists_isCardinal_cardEQ_of_wellOrderOn [V ⊧ₘ* 𝗭𝗙] {S Y : V}
    (hSwo : IsWellOrderOn S Y) :
    ∃ κ, IsCardinal κ ∧ κ ≋ Y := by
  let α : V := Ordinal.wellOrderTypeVal S Y hSwo
  have hαord : IsOrdinal α := by
    simpa [α] using (Ordinal.wellOrderTypeVal_spec S Y hSwo).1
  have hαY : α ≋ Y := by
    rcases Ordinal.wellOrderType_isOrderIso S Y hSwo with ⟨f, hf⟩
    exact CardEQ.of_bijective (IsOrderIso.bijective hf)
  rcases exists_isCardinal_cardEQ_of_isOrdinal (V := V) hαord with ⟨κ, hκ, hkα⟩
  exact ⟨κ, hκ, CardEQ.trans hkα hαY⟩

lemma cofinality_subset_card_of_isCofinal [V ⊧ₘ* 𝗭𝗙] {α X : V}
    (hα : IsLimitOrdinal α) (hX : IsCofinal X α) :
    cofinality α ⊆ card X := by
  letI : IsOrdinal α := hα.1
  let hXwo : IsWellOrderOn (IsOrdinal.memRelOn X) X :=
    IsOrdinal.wellOrderOn_memRelOn_subset (α := α) hX.1
  let β : V := Ordinal.wellOrderTypeVal (IsOrdinal.memRelOn X) X hXwo
  have hXcard : ∃ κ, IsCardinal κ ∧ κ ≋ X :=
    exists_isCardinal_cardEQ_of_wellOrderOn (V := V) hXwo
  have hcofCard : IsCardinal (cofinality α) :=
    cofinality_isCardinal_of_isLimitOrdinal hα
  have hcardCof : card (cofinality α) = cofinality α := by
    symm
    exact (card_eq_iff (cofinality α) (cofinality α)).2 <| Or.inl ⟨hcofCard, CardEQ.refl _⟩
  rcases Ordinal.wellOrderType_isOrderIso (S := IsOrdinal.memRelOn X) (Y := X) (hSwo := hXwo) with
    ⟨f, hf⟩
  have hβX : β ≋ X := CardEQ.of_bijective (IsOrderIso.bijective hf)
  have hcofβ : cofinality α ⊆ β :=
    cofinality_subset_wellOrderTypeVal_memRelOn_of_isCofinal hα hX
  have hcofX : cofinality α ≤# X :=
    (cardLE_of_subset hcofβ).trans hβX.le
  simpa [hcardCof] using
    (cardLE_iff_card_subset_card (V := V) (X := cofinality α) (Y := X)
      ⟨cofinality α, hcofCard, CardEQ.refl _⟩ hXcard).1 hcofX

lemma not_isCofinal_of_card_mem_cofinality [V ⊧ₘ* 𝗭𝗙] {α X : V}
    (hα : IsLimitOrdinal α) (hcardX : card X ∈ cofinality α) :
    ¬ IsCofinal X α := by
  intro hX
  have hsub : cofinality α ⊆ card X :=
    cofinality_subset_card_of_isCofinal (V := V) hα hX
  exact mem_irrefl (card X) (hsub (card X) hcardX)

lemma hasSmallCoveringFunction_of_isCardinal_of_ω_subset [V ⊧ₘ* 𝗭𝗙] {κ : V}
    (hκ : IsCardinal κ) (hωκ : (ω : V) ⊆ κ) :
    HasSmallCoveringFunction κ := by
  have hκlim : IsLimitOrdinal κ := isLimitOrdinal_of_isCardinal_of_ω_subset hκ hωκ
  have hHasCof : HasCofinalFunction κ := hasCofinalFunction_of_isLimitOrdinal hκlim
  rcases cofinality_hasFunction hHasCof with ⟨f, hf⟩
  have hfPow : f ∈ ℘ κ ^ cofinality κ := by
    refine mem_function_of_mem_function_of_subset hf.mem_function ?_
    intro Y hYκ
    exact mem_power_iff.mpr (hκ.1.transitive _ hYκ)
  refine ⟨cofinality κ, cofinality_isOrdinal hHasCof, f, ?_⟩
  refine ⟨hfPow, ?_, hf.isCofinal.2⟩
  intro Y hY
  have hYκ : Y ∈ κ := hf.isCofinal.1 _ hY
  have hYsubκ : Y ⊆ κ := hκ.1.transitive _ hYκ
  refine ⟨cardLE_of_subset hYsubκ, ?_⟩
  intro hκleY
  exact hκ.2 Y hYκ ⟨cardLE_of_subset hYsubκ, hκleY⟩

lemma coveringNumber_subset_cofinality_of_isCardinal_of_ω_subset [V ⊧ₘ* 𝗭𝗙] {κ : V}
    (hκ : IsCardinal κ) (hωκ : (ω : V) ⊆ κ) :
    coveringNumber κ ⊆ cofinality κ := by
  have hHasCover : HasSmallCoveringFunction κ :=
    hasSmallCoveringFunction_of_isCardinal_of_ω_subset (V := V) hκ hωκ
  have hκlim : IsLimitOrdinal κ := isLimitOrdinal_of_isCardinal_of_ω_subset hκ hωκ
  have hHasCof : HasCofinalFunction κ := hasCofinalFunction_of_isLimitOrdinal hκlim
  rcases cofinality_hasFunction hHasCof with ⟨f, hf⟩
  exact coveringNumber_least hHasCover (cofinality_isOrdinal hHasCof)
    ⟨f, by
      refine ⟨mem_function_of_mem_function_of_subset hf.mem_function ?_, ?_, hf.isCofinal.2⟩
      · intro Y hYκ
        exact mem_power_iff.mpr (hκ.1.transitive _ hYκ)
      · intro Y hY
        have hYκ : Y ∈ κ := hf.isCofinal.1 _ hY
        have hYsubκ : Y ⊆ κ := hκ.1.transitive _ hYκ
        refine ⟨cardLE_of_subset hYsubκ, ?_⟩
        intro hκleY
        exact hκ.2 Y hYκ ⟨cardLE_of_subset hYsubκ, hκleY⟩⟩

private lemma initialSegment_memRelOn_subset_eq_inter {α X x : V} [IsOrdinal α]
    (_hX : X ⊆ α) (hx : x ∈ X) :
    initialSegment (IsOrdinal.memRelOn X) X x = X ∩ x := by
  ext z
  constructor
  · intro hz
    rcases mem_initialSegment_iff.mp hz with ⟨hzX, hzx⟩
    exact mem_inter_iff.mpr ⟨hzX, (IsOrdinal.kpair_mem_memRelOn_iff.mp hzx).2.2⟩
  · intro hz
    rcases mem_inter_iff.mp hz with ⟨hzX, hzx⟩
    refine mem_initialSegment_iff.mpr ?_
    exact ⟨hzX, IsOrdinal.kpair_mem_memRelOn_iff.mpr ⟨hzX, hx, hzx⟩⟩

private lemma wellOrderTypeValTotal_memRelOn_inter_mem [V ⊧ₘ* 𝗭𝗙] {α X x : V} [hα : IsOrdinal α]
    (hX : X ⊆ α) (hx : x ∈ X) :
    Ordinal.wellOrderTypeValTotal (IsOrdinal.memRelOn (X ∩ x)) (X ∩ x) ∈
      Ordinal.wellOrderTypeValTotal (IsOrdinal.memRelOn X) X := by
  let hXwo : IsWellOrderOn (IsOrdinal.memRelOn X) X :=
    IsOrdinal.wellOrderOn_memRelOn_subset (α := α) hX
  have hxα : x ∈ α := hX _ hx
  have hIxSub : X ∩ x ⊆ α := by
    intro z hz
    rcases mem_inter_iff.mp hz with ⟨-, hzx⟩
    exact hα.toIsTransitive.transitive _ hxα _ hzx
  let hIxwo : IsWellOrderOn (IsOrdinal.memRelOn (X ∩ x)) (X ∩ x) :=
    IsOrdinal.wellOrderOn_memRelOn_subset (α := α) hIxSub
  let β : V := Ordinal.wellOrderTypeVal (IsOrdinal.memRelOn X) X hXwo
  have hβord : IsOrdinal β := by
    simpa [β] using (Ordinal.wellOrderTypeVal_spec (IsOrdinal.memRelOn X) X hXwo).1
  rcases Ordinal.wellOrderType_isOrderIso (S := IsOrdinal.memRelOn X) (Y := X) (hSwo := hXwo) with
    ⟨f, hf⟩
  have hxRange : x ∈ range f := by
    simpa [hf.range_eq] using hx
  rcases mem_range_iff.mp hxRange with ⟨b, hbfx⟩
  have hbβ : b ∈ β := (mem_of_mem_functions hf.mem_function hbfx).1
  have hRes :
      IsOrderIso (IsOrdinal.memRelOn β) (initialSegment (IsOrdinal.memRelOn β) β b)
        (IsOrdinal.memRelOn X) (initialSegment (IsOrdinal.memRelOn X) X x)
        (f ↾ (initialSegment (IsOrdinal.memRelOn β) β b)) :=
    hf.restrict_initialSegment hbβ hbfx
  have hRes'' :
      IsOrderIso (IsOrdinal.memRelOn β) b
        (IsOrdinal.memRelOn X) (X ∩ x)
        (f ↾ (initialSegment (IsOrdinal.memRelOn β) β b)) := by
    simpa [IsOrdinal.initialSegment_memRelOn_eq (α := β) hbβ,
      initialSegment_memRelOn_subset_eq_inter (α := α) hX hx] using hRes
  have hRes' :
      IsOrderIso (IsOrdinal.memRelOn b) b
        (IsOrdinal.memRelOn (X ∩ x)) (X ∩ x)
        (f ↾ (initialSegment (IsOrdinal.memRelOn β) β b)) := by
    have hResFun : (f ↾ (initialSegment (IsOrdinal.memRelOn β) β b)) ∈ (X ∩ x) ^ b := hRes''.mem_function
    refine ⟨hResFun, hRes''.injective, hRes''.range_eq, ?_⟩
    intro u hu v hv
    have huvDom :
        ⟨u, v⟩ₖ ∈ IsOrdinal.memRelOn β ↔ ⟨u, v⟩ₖ ∈ IsOrdinal.memRelOn b := by
      constructor
      · intro huvβ
        exact IsOrdinal.kpair_mem_memRelOn_iff.mpr
          ⟨hu, hv, (IsOrdinal.kpair_mem_memRelOn_iff.mp huvβ).2.2⟩
      · intro huvb
        have huβ : u ∈ β := hβord.toIsTransitive.transitive _ hbβ _ hu
        have hvβ : v ∈ β := hβord.toIsTransitive.transitive _ hbβ _ hv
        exact IsOrdinal.kpair_mem_memRelOn_iff.mpr
          ⟨huβ, hvβ, (IsOrdinal.kpair_mem_memRelOn_iff.mp huvb).2.2⟩
    have huImg : (f ↾ (initialSegment (IsOrdinal.memRelOn β) β b)) ‘ u ∈ X ∩ x :=
      range_subset_of_mem_function hResFun _ (value_mem_range hResFun hu)
    have hvImg : (f ↾ (initialSegment (IsOrdinal.memRelOn β) β b)) ‘ v ∈ X ∩ x :=
      range_subset_of_mem_function hResFun _ (value_mem_range hResFun hv)
    have huvCod :
        ⟨(f ↾ (initialSegment (IsOrdinal.memRelOn β) β b)) ‘ u,
          (f ↾ (initialSegment (IsOrdinal.memRelOn β) β b)) ‘ v⟩ₖ ∈ IsOrdinal.memRelOn X ↔
        ⟨(f ↾ (initialSegment (IsOrdinal.memRelOn β) β b)) ‘ u,
          (f ↾ (initialSegment (IsOrdinal.memRelOn β) β b)) ‘ v⟩ₖ ∈ IsOrdinal.memRelOn (X ∩ x) := by
      constructor
      · intro h
        exact IsOrdinal.kpair_mem_memRelOn_iff.mpr
          ⟨huImg, hvImg, (IsOrdinal.kpair_mem_memRelOn_iff.mp h).2.2⟩
      · intro h
        exact IsOrdinal.kpair_mem_memRelOn_iff.mpr
          ⟨(mem_inter_iff.mp huImg).1, (mem_inter_iff.mp hvImg).1,
            (IsOrdinal.kpair_mem_memRelOn_iff.mp h).2.2⟩
    constructor
    · intro huvb
      have huvβ : ⟨u, v⟩ₖ ∈ IsOrdinal.memRelOn β := huvDom.2 huvb
      have huvX :
          ⟨(f ↾ (initialSegment (IsOrdinal.memRelOn β) β b)) ‘ u,
            (f ↾ (initialSegment (IsOrdinal.memRelOn β) β b)) ‘ v⟩ₖ ∈ IsOrdinal.memRelOn X :=
        (hRes''.rel_iff hu hv).1 huvβ
      exact huvCod.1 huvX
    · intro huvIx
      have huvX :
          ⟨(f ↾ (initialSegment (IsOrdinal.memRelOn β) β b)) ‘ u,
            (f ↾ (initialSegment (IsOrdinal.memRelOn β) β b)) ‘ v⟩ₖ ∈ IsOrdinal.memRelOn X :=
        huvCod.2 huvIx
      have huvβ : ⟨u, v⟩ₖ ∈ IsOrdinal.memRelOn β := (hRes''.rel_iff hu hv).2 huvX
      exact huvDom.1 huvβ
  have hbEq :
      b = Ordinal.wellOrderTypeVal (IsOrdinal.memRelOn (X ∩ x)) (X ∩ x) hIxwo := by
    exact (Ordinal.wellOrderTypeVal_eq_iff_isOrderIso (S := IsOrdinal.memRelOn (X ∩ x))
      (Y := X ∩ x) (α := b) (hSwo := hIxwo)).2 ⟨hβord.of_mem hbβ, ⟨_, hRes'⟩⟩
  have hMem :
      Ordinal.wellOrderTypeVal (IsOrdinal.memRelOn (X ∩ x)) (X ∩ x) hIxwo ∈ β := by
    simpa [hbEq] using hbβ
  simpa [β, Ordinal.wellOrderTypeValTotal_of_wellOrderOn hXwo,
    Ordinal.wellOrderTypeValTotal_of_wellOrderOn hIxwo] using hMem

private lemma wellOrderTypeValTotal_memRelOn_inter_strictIncreasing [V ⊧ₘ* 𝗭𝗙]
    {α X x y : V} [hα : IsOrdinal α]
    (hX : X ⊆ α) (hx : x ∈ X) (hy : y ∈ X) (hxy : x ∈ y) :
    Ordinal.wellOrderTypeValTotal (IsOrdinal.memRelOn (X ∩ x)) (X ∩ x) ∈
      Ordinal.wellOrderTypeValTotal (IsOrdinal.memRelOn (X ∩ y)) (X ∩ y) := by
  have hyα : y ∈ α := hX _ hy
  have hIySub : X ∩ y ⊆ α := by
    intro z hz
    rcases mem_inter_iff.mp hz with ⟨-, hzy⟩
    exact hα.toIsTransitive.transitive _ hyα _ hzy
  have hxIy : x ∈ X ∩ y := mem_inter_iff.mpr ⟨hx, hxy⟩
  have hEq : (X ∩ y) ∩ x = X ∩ x := by
    ext z
    constructor
    · intro hz
      rcases mem_inter_iff.mp hz with ⟨hzIy, hzx⟩
      exact mem_inter_iff.mpr ⟨(mem_inter_iff.mp hzIy).1, hzx⟩
    · intro hz
      rcases mem_inter_iff.mp hz with ⟨hzX, hzx⟩
      have hzy : z ∈ y := hα.of_mem hyα |> fun hyord => hyord.toIsTransitive.transitive _ hxy _ hzx
      exact mem_inter_iff.mpr ⟨mem_inter_iff.mpr ⟨hzX, hzy⟩, hzx⟩
  simpa [hEq] using
    wellOrderTypeValTotal_memRelOn_inter_mem (V := V) (α := α) (X := X ∩ y) hIySub hxIy

private lemma mem_ω_or_ω_subset_of_isOrdinal {α : V} [IsOrdinal α] :
    α ∈ (ω : V) ∨ (ω : V) ⊆ α := by
  rcases IsOrdinal.subset_or_supset (α := α) (β := (ω : V)) with (hαω | hωα)
  · rcases (IsOrdinal.subset_iff (α := α) (β := (ω : V))).1 hαω with (hEq | hMem)
    · exact Or.inr (hEq.symm ▸ subset_refl (ω : V))
    · exact Or.inl hMem
  · exact Or.inr hωα

private lemma mem_ω_of_subset_ω_of_ne_ω {α : V} [IsOrdinal α]
    (hαω : α ⊆ (ω : V)) (hαne : α ≠ (ω : V)) :
    α ∈ (ω : V) := by
  rcases (IsOrdinal.subset_iff (α := α) (β := (ω : V))).1 hαω with (hEq | hMem)
  · exact False.elim (hαne hEq)
  · exact hMem

noncomputable def cardAdd (X Y : V) : V :=
  card (orderSumCarrier X Y)

noncomputable def cardMul (X Y : V) : V :=
  card (X ×ˢ Y)

instance cardAdd.definable [V ⊧ₘ* 𝗭𝗙] : ℒₛₑₜ-function₂[V] cardAdd := by
  letI : ℒₛₑₜ-function₁[V] card := card.definable (V := V)
  letI : ℒₛₑₜ-function₂[V] orderSumCarrier := orderSumCarrier.definable
  change ℒₛₑₜ-function₂[V] (fun X Y ↦ card (orderSumCarrier X Y))
  definability

instance cardMul.definable [V ⊧ₘ* 𝗭𝗙] : ℒₛₑₜ-function₂[V] cardMul := by
  letI : ℒₛₑₜ-function₁[V] card := card.definable (V := V)
  letI : ℒₛₑₜ-function₂[V] prod := prod.definable
  change ℒₛₑₜ-function₂[V] (fun X Y ↦ card (X ×ˢ Y))
  definability

lemma exists_isCardinal_cardEQ_orderSumCarrier_of_isOrdinal [V ⊧ₘ* 𝗭𝗙] {α β : V}
    (hα : IsOrdinal α) (hβ : IsOrdinal β) :
    ∃ κ, IsCardinal κ ∧ κ ≋ orderSumCarrier α β := by
  exact exists_isCardinal_cardEQ_of_wellOrderOn (V := V) <|
    orderSum_isWellOrderOn
      (hR := IsOrdinal.wellOrderOn_memRelOn (α := α))
      (hS := IsOrdinal.wellOrderOn_memRelOn (α := β))

lemma exists_isCardinal_cardEQ_prod_of_isOrdinal [V ⊧ₘ* 𝗭𝗙] {α β : V}
    (hα : IsOrdinal α) (hβ : IsOrdinal β) :
    ∃ κ, IsCardinal κ ∧ κ ≋ (α ×ˢ β) := by
  exact exists_isCardinal_cardEQ_of_wellOrderOn (V := V) <|
    orderProd_isWellOrderOn
      (hR := IsOrdinal.wellOrderOn_memRelOn (α := α))
      (hS := IsOrdinal.wellOrderOn_memRelOn (α := β))

lemma cardAdd_spec_of_isOrdinal [V ⊧ₘ* 𝗭𝗙] {α β : V}
    (hα : IsOrdinal α) (hβ : IsOrdinal β) :
    IsCardinal (cardAdd α β) ∧ cardAdd α β ≋ orderSumCarrier α β := by
  simpa [cardAdd] using
    (card_spec
      (X := orderSumCarrier α β)
      (exists_isCardinal_cardEQ_orderSumCarrier_of_isOrdinal (V := V) hα hβ))

lemma cardMul_spec_of_isOrdinal [V ⊧ₘ* 𝗭𝗙] {α β : V}
    (hα : IsOrdinal α) (hβ : IsOrdinal β) :
    IsCardinal (cardMul α β) ∧ cardMul α β ≋ (α ×ˢ β) := by
  simpa [cardMul] using
    (card_spec
      (X := α ×ˢ β)
      (exists_isCardinal_cardEQ_prod_of_isOrdinal (V := V) hα hβ))

lemma cardAdd_isCardinal_of_isOrdinal [V ⊧ₘ* 𝗭𝗙] {α β : V}
    (hα : IsOrdinal α) (hβ : IsOrdinal β) :
    IsCardinal (cardAdd α β) :=
  (cardAdd_spec_of_isOrdinal (V := V) hα hβ).1

lemma cardAdd_cardEQ_of_isOrdinal [V ⊧ₘ* 𝗭𝗙] {α β : V}
    (hα : IsOrdinal α) (hβ : IsOrdinal β) :
    cardAdd α β ≋ orderSumCarrier α β :=
  (cardAdd_spec_of_isOrdinal (V := V) hα hβ).2

lemma cardMul_isCardinal_of_isOrdinal [V ⊧ₘ* 𝗭𝗙] {α β : V}
    (hα : IsOrdinal α) (hβ : IsOrdinal β) :
    IsCardinal (cardMul α β) :=
  (cardMul_spec_of_isOrdinal (V := V) hα hβ).1

lemma cardMul_cardEQ_of_isOrdinal [V ⊧ₘ* 𝗭𝗙] {α β : V}
    (hα : IsOrdinal α) (hβ : IsOrdinal β) :
    cardMul α β ≋ (α ×ˢ β) :=
  (cardMul_spec_of_isOrdinal (V := V) hα hβ).2

lemma cardAdd_spec_of_isCardinal [V ⊧ₘ* 𝗭𝗙] {κ μ : V}
    (hκ : IsCardinal κ) (hμ : IsCardinal μ) :
    IsCardinal (cardAdd κ μ) ∧ cardAdd κ μ ≋ orderSumCarrier κ μ :=
  cardAdd_spec_of_isOrdinal (V := V) hκ.1 hμ.1

lemma cardMul_spec_of_isCardinal [V ⊧ₘ* 𝗭𝗙] {κ μ : V}
    (hκ : IsCardinal κ) (hμ : IsCardinal μ) :
    IsCardinal (cardMul κ μ) ∧ cardMul κ μ ≋ (κ ×ˢ μ) :=
  cardMul_spec_of_isOrdinal (V := V) hκ.1 hμ.1

lemma cardAdd_eq_addValue_of_mem_ω [V ⊧ₘ* 𝗭𝗙] {α β : V}
    (hαω : α ∈ (ω : V)) (hβω : β ∈ (ω : V)) :
    cardAdd α β = Ordinal.addValue ⟨α, IsOrdinal.of_mem hαω⟩ ⟨β, IsOrdinal.of_mem hβω⟩ := by
  let αo : Ordinal V := ⟨α, IsOrdinal.of_mem hαω⟩
  let βo : Ordinal V := ⟨β, IsOrdinal.of_mem hβω⟩
  letI : IsOrdinal αo.val := αo.ordinal
  letI : IsOrdinal βo.val := βo.ordinal
  have hcardAdd := cardAdd_spec_of_isOrdinal (V := V) αo.ordinal βo.ordinal
  have haddω : Ordinal.addValue αo βo ∈ (ω : V) :=
    Ordinal.addValue_mem_ω (α := αo) (β := βo) hαω hβω
  have haddCard : IsCardinal (Ordinal.addValue αo βo) :=
    isCardinal_of_mem_ω (V := V) haddω
  have haddEQ : Ordinal.addValue αo βo ≋ orderSumCarrier α β := by
    let γ : Ordinal V :=
      Ordinal.wellOrderType
        (orderSumRel (IsOrdinal.memRelOn αo.val) αo.val (IsOrdinal.memRelOn βo.val) βo.val)
        (orderSumCarrier αo.val βo.val)
        (orderSum_isWellOrderOn
          (hR := IsOrdinal.wellOrderOn_memRelOn (α := αo.val))
          (hS := IsOrdinal.wellOrderOn_memRelOn (α := βo.val)))
    have hγ : γ.val = Ordinal.addValue αo βo := by
      symm
      simpa [γ] using Ordinal.addValue_eq_wellOrderTypeVal_orderSum_memRelOn αo βo
    rcases Ordinal.wellOrderType_isOrderIso
        (S := orderSumRel (IsOrdinal.memRelOn αo.val) αo.val (IsOrdinal.memRelOn βo.val) βo.val)
        (Y := orderSumCarrier αo.val βo.val)
        (hSwo := orderSum_isWellOrderOn
          (hR := IsOrdinal.wellOrderOn_memRelOn (α := αo.val))
          (hS := IsOrdinal.wellOrderOn_memRelOn (α := βo.val))) with ⟨f, hf⟩
    exact CardEQ.of_bijective <| by
      simpa [γ, hγ, αo, βo] using IsOrderIso.bijective hf
  exact eq_of_isCardinal_of_cardEQ hcardAdd.1 haddCard <|
    CardEQ.trans hcardAdd.2 (CardEQ.symm haddEQ)

lemma cardMul_eq_mulValue_of_mem_ω [V ⊧ₘ* 𝗭𝗙] {α β : V}
    (hαω : α ∈ (ω : V)) (hβω : β ∈ (ω : V)) :
    cardMul α β = Ordinal.mulValue ⟨α, IsOrdinal.of_mem hαω⟩ ⟨β, IsOrdinal.of_mem hβω⟩ := by
  let αo : Ordinal V := ⟨α, IsOrdinal.of_mem hαω⟩
  let βo : Ordinal V := ⟨β, IsOrdinal.of_mem hβω⟩
  letI : IsOrdinal αo.val := αo.ordinal
  letI : IsOrdinal βo.val := βo.ordinal
  have hcardMul := cardMul_spec_of_isOrdinal (V := V) αo.ordinal βo.ordinal
  have hmulω : Ordinal.mulValue αo βo ∈ (ω : V) :=
    Ordinal.mulValue_mem_ω (α := αo) (β := βo) hαω hβω
  have hmulCard : IsCardinal (Ordinal.mulValue αo βo) :=
    isCardinal_of_mem_ω (V := V) hmulω
  have hmulEQ : Ordinal.mulValue αo βo ≋ (α ×ˢ β) := by
    let γ : Ordinal V :=
      Ordinal.wellOrderType
        (orderProdRel (IsOrdinal.memRelOn αo.val) αo.val (IsOrdinal.memRelOn βo.val) βo.val)
        (αo.val ×ˢ βo.val)
        (orderProd_isWellOrderOn
          (hR := IsOrdinal.wellOrderOn_memRelOn (α := αo.val))
          (hS := IsOrdinal.wellOrderOn_memRelOn (α := βo.val)))
    have hγ : γ.val = Ordinal.mulValue αo βo := by
      symm
      simpa [γ] using Ordinal.mulValue_eq_wellOrderTypeVal_orderProd_memRelOn αo βo
    rcases Ordinal.wellOrderType_isOrderIso
        (S := orderProdRel (IsOrdinal.memRelOn αo.val) αo.val (IsOrdinal.memRelOn βo.val) βo.val)
        (Y := αo.val ×ˢ βo.val)
        (hSwo := orderProd_isWellOrderOn
          (hR := IsOrdinal.wellOrderOn_memRelOn (α := αo.val))
          (hS := IsOrdinal.wellOrderOn_memRelOn (α := βo.val))) with ⟨f, hf⟩
    exact CardEQ.of_bijective <| by
      simpa [γ, hγ, αo, βo] using IsOrderIso.bijective hf
  exact eq_of_isCardinal_of_cardEQ hcardMul.1 hmulCard <|
    CardEQ.trans hcardMul.2 (CardEQ.symm hmulEQ)

lemma card_eq_self_of_isCardinal {κ : V} (hκ : IsCardinal κ) : card κ = κ := by
  symm
  exact (card_eq_iff κ κ).2 <| Or.inl ⟨hκ, CardEQ.refl κ⟩

lemma cardLE_iff_subset_of_isCardinal [V ⊧ₘ* 𝗭𝗙] {κ ξ : V}
    (hκ : IsCardinal κ) (hξ : IsCardinal ξ) :
    κ ≤# ξ ↔ κ ⊆ ξ := by
  have hcardκ : card κ = κ := card_eq_self_of_isCardinal hκ
  have hcardξ : card ξ = ξ := card_eq_self_of_isCardinal hξ
  simpa [hcardκ, hcardξ] using
    (cardLE_iff_card_subset_card (X := κ) (Y := ξ)
      ⟨κ, hκ, CardEQ.refl κ⟩ ⟨ξ, hξ, CardEQ.refl ξ⟩)

lemma subset_card_of_isCardinal_of_subset [V ⊧ₘ* 𝗭𝗙] {κ α : V}
    (hκ : IsCardinal κ) (hα : IsOrdinal α) (hκα : κ ⊆ α) :
    κ ⊆ card α := by
  have hκαle : κ ≤# α := cardLE_of_subset hκα
  have hαcard : ∃ ξ, IsCardinal ξ ∧ ξ ≋ α :=
    exists_isCardinal_cardEQ_of_isOrdinal (V := V) hα
  have h : card κ ⊆ card α :=
    (cardLE_iff_card_subset_card (V := V) (X := κ) (Y := α)
      ⟨κ, hκ, CardEQ.refl κ⟩ hαcard).1 hκαle
  simpa [card_eq_self_of_isCardinal hκ] using h

lemma mem_of_card_mem_of_isCardinal [V ⊧ₘ* 𝗭𝗙] {κ α : V}
    (hκ : IsCardinal κ) (hα : IsOrdinal α) (hcardακ : card α ∈ κ) :
    α ∈ κ := by
  letI : IsOrdinal κ := hκ.1
  by_contra hακ
  rcases IsOrdinal.mem_trichotomy (α := α) (β := κ) with (hακ' | hEq | hκα)
  · exact hακ hακ'
  · have : κ ∈ κ := by
      simp [hEq, card_eq_self_of_isCardinal hκ] at hcardακ
    exact (mem_irrefl κ) this
  · have hκsubα : κ ⊆ α := hα.transitive _ hκα
    have hκsubcard : κ ⊆ card α :=
      subset_card_of_isCardinal_of_subset (V := V) hκ hα hκsubα
    have hcardsubκ : card α ⊆ κ := hκ.1.transitive _ hcardακ
    have hEq' : κ = card α := subset_antisymm hκsubcard hcardsubκ
    exact (mem_irrefl κ) (hEq' ▸ hcardακ)

lemma card_mem_of_mem_of_isCardinal [V ⊧ₘ* 𝗭𝗙] {μ κ : V}
    (hκ : IsCardinal κ) (hμ : IsOrdinal μ) (hμκ : μ ∈ κ) :
    card μ ∈ κ := by
  letI : IsOrdinal κ := hκ.1
  have hcardsub : card μ ⊆ μ := card_subset_of_isOrdinal (V := V) hμ
  have hcardμ : IsOrdinal (card μ) := (card_isCardinal_of_isOrdinal (V := V) hμ).1
  letI : IsOrdinal (card μ) := hcardμ
  rcases (IsOrdinal.subset_iff (α := card μ) (β := μ)).1 hcardsub with (hEq | hcardμμ)
  · exact hEq.symm ▸ hμκ
  · exact hκ.1.toIsTransitive.transitive _ hμκ _ hcardμμ

lemma ordinalPairZeroFstType_cardEQ_prod [V ⊧ₘ* 𝗭𝗙] {α : V}
    (hα : IsOrdinal α) :
    ordinalPairZeroFstType α ≋ (α ×ˢ α) := by
  rcases (ordinalPairInitialSegmentType_spec (V := V) ⟨0, α⟩ₖ).2 with ⟨f, hf⟩
  exact CardEQ.of_bijective <| by
    simpa [ordinalPairZeroFstType, ordinalPairInitialSegment_zero_fst_eq_prod (α := α) hα] using
      IsOrderIso.bijective hf

lemma ordinalPairZeroFstType_eq_self_of_isCardinal_of_ω_subset
    [V ⊧ₘ* 𝗭𝗙] {κ : V}
    (hκ : IsCardinal κ) (hωκ : (ω : V) ⊆ κ) :
    ordinalPairZeroFstType κ = κ := by
  let P : V → Prop := fun ξ ↦ IsCardinal ξ ∧ (ω : V) ⊆ ξ ∧ ordinalPairZeroFstType ξ ≠ ξ
  have hP : ℒₛₑₜ-predicate[V] P := by
    letI : ℒₛₑₜ-predicate[V] IsCardinal := IsCardinal.definable
    letI : ℒₛₑₜ-function₁[V] ordinalPairZeroFstType := ordinalPairZeroFstType.definable (V := V)
    change ℒₛₑₜ-predicate[V] (fun ξ ↦ IsCardinal ξ ∧ (ω : V) ⊆ ξ ∧ ordinalPairZeroFstType ξ ≠ ξ)
    definability
  by_contra hτκ
  have hEx : ∃ α : Ordinal V, P α := ⟨⟨κ, hκ.1⟩, hκ, hωκ, hτκ⟩
  rcases exists_minimal P hP hEx with ⟨κo, hκoP, hκleast⟩
  let κ : V := κo.val
  have hκcard : IsCardinal κ := by simpa [κ] using hκoP.1
  have hωκ : (ω : V) ⊆ κ := by simpa [κ] using hκoP.2.1
  have hτκ : ordinalPairZeroFstType κ ≠ κ := by simpa [κ] using hκoP.2.2
  letI : IsOrdinal (ordinalPairZeroFstType κ) := ordinalPairZeroFstType_isOrdinal (V := V) κ
  have hκsubτ : κ ⊆ ordinalPairZeroFstType κ := by
    simpa [κ] using subset_ordinalPairZeroFstType (V := V) κ hκcard.1
  have hκτ : κ ∈ ordinalPairZeroFstType κ := by
    rcases (IsOrdinal.subset_iff (α := κ) (β := ordinalPairZeroFstType κ)).1 hκsubτ with
      (hEq | hMem)
    · exact (hτκ hEq.symm).elim
    · exact hMem
  rcases exists_mem_prod_eq_ordinalPairInitialSegmentType_of_mem_ordinalPairZeroFstType
      (V := V) hκcard.1 hκτ with ⟨p, hpκprod, hκeqp⟩
  rcases mem_prod_iff.mp hpκprod with ⟨β, hβκ, γ, hγκ, rfl⟩
  have hβord : IsOrdinal β := hκcard.1.of_mem hβκ
  have hγord : IsOrdinal γ := hκcard.1.of_mem hγκ
  let ν : V := ordinalMax β γ
  have hνord : IsOrdinal ν := by
    simpa [ν] using ordinalMax_isOrdinal hβord hγord
  have hνκ : ν ∈ κ := by
    rcases IsOrdinal.subset_or_supset (α := β) (β := γ) with (hβγ | hγβ)
    · have hEq : ν = γ := by
        simpa [ν, ordinalMax] using (union_eq_iff_left.mpr hβγ : β ∪ γ = γ)
      simpa [hEq] using hγκ
    · have hEq : ν = β := by
        simpa [ν, ordinalMax] using (union_eq_iff_right.mpr hγβ : β ∪ γ = β)
      simpa [hEq] using hβκ
  let μ : V := succ ν
  have hμord : IsOrdinal μ := by
    simpa [μ] using IsOrdinal.succ (α := ν)
  have hμκ : μ ∈ κ := by
    have hμsubκ : μ ⊆ κ := by
      simpa [μ] using IsOrdinal.succ_subset_of_mem hνκ
    rcases (IsOrdinal.subset_iff (α := μ) (β := κ)).1 hμsubκ with (hEq | hMem)
    · exact (isLimitOrdinal_of_isCardinal_of_ω_subset hκcard hωκ).2.2 ⟨ν, hEq.symm⟩ |> False.elim
    · exact hMem
  have hβμ : β ∈ μ := by
    have hβsub : β ⊆ ν := by simp [ν, ordinalMax]
    rcases (IsOrdinal.subset_iff (α := β) (β := ν)).1 hβsub with (hEq | hβν)
    · exact mem_succ_iff.mpr (Or.inl (by simpa [μ] using hEq))
    · exact mem_succ_iff.mpr (Or.inr (by simpa [μ] using hβν))
  have hγμ : γ ∈ μ := by
    have hγsub : γ ⊆ ν := by simp [ν, ordinalMax]
    rcases (IsOrdinal.subset_iff (α := γ) (β := ν)).1 hγsub with (hEq | hγν)
    · exact mem_succ_iff.mpr (Or.inl (by simpa [μ] using hEq))
    · exact mem_succ_iff.mpr (Or.inr (by simpa [μ] using hγν))
  have hpμprod : ⟨β, γ⟩ₖ ∈ μ ×ˢ μ := by
    simpa [mem_prod_iff] using And.intro hβμ hγμ
  have hqμpair : IsOrdinalPair ⟨0, μ⟩ₖ := IsOrdinalPair.mk (by infer_instance) hμord
  have hpLTμ : OrdinalPairLT ⟨β, γ⟩ₖ ⟨0, μ⟩ₖ := by
    have hpμseg : ⟨β, γ⟩ₖ ∈ ordinalPairInitialSegment ⟨0, μ⟩ₖ := by
      simpa [ordinalPairInitialSegment_zero_fst_eq_prod (α := μ) hμord] using hpμprod
    exact (mem_ordinalPairInitialSegment_iff_of_isOrdinalPair hqμpair).1 hpμseg
  have htypepμ :
      ordinalPairInitialSegmentType ⟨β, γ⟩ₖ ∈ ordinalPairZeroFstType μ := by
    simpa [ordinalPairZeroFstType] using
      (ordinalPairInitialSegmentType_strictIncreasing (V := V) hpLTμ)
  let κμ : V := card μ
  have hκμcard : IsCardinal κμ := by
    simpa [κμ] using card_isCardinal_of_isOrdinal (V := V) hμord
  letI : IsOrdinal κμ := hκμcard.1
  have hκμμeq : κμ ≋ μ := by
    simpa [κμ] using card_cardEQ_of_isOrdinal (V := V) hμord
  have hκμκ : κμ ∈ κ := by
    simpa [κμ] using card_mem_of_mem_of_isCardinal (V := V) hκcard hμord hμκ
  have hτμprod : ordinalPairZeroFstType μ ≋ (μ ×ˢ μ) :=
    ordinalPairZeroFstType_cardEQ_prod (V := V) hμord
  have hprod : (μ ×ˢ μ) ≋ (κμ ×ˢ κμ) :=
    CardEQ.prod (V := V) (CardEQ.symm hκμμeq) (CardEQ.symm hκμμeq)
  have hτκμprod : ordinalPairZeroFstType κμ ≋ (κμ ×ˢ κμ) :=
    ordinalPairZeroFstType_cardEQ_prod (V := V) hκμcard.1
  have hτμτκμ : ordinalPairZeroFstType μ ≋ ordinalPairZeroFstType κμ := by
    exact CardEQ.trans hτμprod (CardEQ.trans hprod (CardEQ.symm hτκμprod))
  have hκμω_or_hωκμ : κμ ∈ (ω : V) ∨ (ω : V) ⊆ κμ := by
    rcases IsOrdinal.subset_or_supset (α := κμ) (β := (ω : V)) with (hκμωsub | hωκμ)
    · rcases (IsOrdinal.subset_iff (α := κμ) (β := (ω : V))).1 hκμωsub with (hEq | hκμω)
      · exact Or.inr (hEq.symm ▸ subset_refl (ω : V))
      · exact Or.inl hκμω
    · exact Or.inr hωκμ
  have hτμκ : ordinalPairZeroFstType μ ∈ κ := by
    rcases hκμω_or_hωκμ with (hκμω | hωκμ)
    · have hτκμω : ordinalPairZeroFstType κμ ∈ (ω : V) :=
        ordinalPairZeroFstType_mem_ω (V := V) hκμω
      have hτμω : ordinalPairZeroFstType μ ∈ (ω : V) :=
        mem_ω_of_isOrdinal_of_cardEQ_mem_ω (V := V)
          (ordinalPairZeroFstType_isOrdinal (V := V) μ) hτκμω hτμτκμ
      exact hωκ _ hτμω
    · have hτκμ : ordinalPairZeroFstType κμ = κμ := by
        by_cases hEq : ordinalPairZeroFstType κμ = κμ
        · exact hEq
        · have hκleκμ : κo ≤ ⟨κμ, hκμcard.1⟩ := by
            exact hκleast ⟨κμ, hκμcard.1⟩ ⟨hκμcard, hωκμ, hEq⟩
          have hκsubκμ : κ ⊆ κμ := by
            simpa [κ, Ordinal.le_def] using hκleκμ
          have hκμsubκ : κμ ⊆ κ := hκcard.1.transitive _ hκμκ
          have hEqκ : κ = κμ := subset_antisymm hκsubκμ hκμsubκ
          exact False.elim ((mem_irrefl κ) (hEqκ ▸ hκμκ))
      have hτμκμ : ordinalPairZeroFstType μ ≋ κμ := by
        simpa [hτκμ] using hτμτκμ
      have hcardτμ : card (ordinalPairZeroFstType μ) = κμ :=
        ((card_eq_iff (ordinalPairZeroFstType μ) κμ).2 <|
          Or.inl ⟨hκμcard, CardEQ.symm hτμκμ⟩).symm
      have hcardτμκ : card (ordinalPairZeroFstType μ) ∈ κ := by
        simpa [hcardτμ] using hκμκ
      exact mem_of_card_mem_of_isCardinal (V := V)
        hκcard (ordinalPairZeroFstType_isOrdinal (V := V) μ) hcardτμκ
  have hκτμ : κ ∈ ordinalPairZeroFstType μ := by
    simpa [hκeqp] using htypepμ
  have : κ ∈ κ := hκcard.1.toIsTransitive.transitive _ hτμκ _ hκτμ
  exact (mem_irrefl κ) this

lemma prod_cardEQ_self_of_isCardinal_of_ω_subset
    [V ⊧ₘ* 𝗭𝗙] {κ : V}
    (hκ : IsCardinal κ) (hωκ : (ω : V) ⊆ κ) :
    (κ ×ˢ κ) ≋ κ := by
  have hτprod : ordinalPairZeroFstType κ ≋ (κ ×ˢ κ) :=
    ordinalPairZeroFstType_cardEQ_prod (V := V) hκ.1
  have hτeq : ordinalPairZeroFstType κ = κ :=
    ordinalPairZeroFstType_eq_self_of_isCardinal_of_ω_subset (V := V) hκ hωκ
  simpa [hτeq] using CardEQ.symm hτprod

lemma cardAdd_comm_of_isCardinal [V ⊧ₘ* 𝗭𝗙] {κ μ : V}
    (hκ : IsCardinal κ) (hμ : IsCardinal μ) :
    cardAdd κ μ = cardAdd μ κ := by
  have hκμ := cardAdd_spec_of_isCardinal (V := V) hκ hμ
  have hμκ := cardAdd_spec_of_isCardinal (V := V) hμ hκ
  exact eq_of_isCardinal_of_cardEQ hκμ.1 hμκ.1 <|
    CardEQ.trans hκμ.2 <|
      CardEQ.trans (orderSumCarrier_cardEQ_comm (V := V) (X := κ) (Y := μ)) (CardEQ.symm hμκ.2)

lemma cardMul_comm_of_isCardinal [V ⊧ₘ* 𝗭𝗙] {κ μ : V}
    (hκ : IsCardinal κ) (hμ : IsCardinal μ) :
    cardMul κ μ = cardMul μ κ := by
  have hκμ := cardMul_spec_of_isCardinal (V := V) hκ hμ
  have hμκ := cardMul_spec_of_isCardinal (V := V) hμ hκ
  exact eq_of_isCardinal_of_cardEQ hκμ.1 hμκ.1 <|
    CardEQ.trans hκμ.2 <|
      CardEQ.trans prod_cardEQ_comm (CardEQ.symm hμκ.2)

lemma cardAdd_eq_self_of_isCardinal_of_ω_subset_of_subset
    [V ⊧ₘ* 𝗭𝗙] {κ μ : V}
    (hκ : IsCardinal κ) (hμ : IsCardinal μ)
    (hωκ : (ω : V) ⊆ κ) (hμκ : μ ⊆ κ) :
    cardAdd κ μ = κ := by
  have hAdd := cardAdd_spec_of_isCardinal (V := V) hκ hμ
  have hAddSub : orderSumCarrier κ μ ⊆ κ ×ˢ κ := by
    intro p hp
    rcases mem_orderSumCarrier_cases hp with (⟨x, hxκ, rfl⟩ | ⟨y, hyμ, rfl⟩)
    · simpa [mem_prod_iff] using And.intro hxκ (hωκ 0 zero_mem_ω)
    · have hyκ : y ∈ κ := hμκ _ hyμ
      simpa [mem_prod_iff] using And.intro hyκ (hωκ 1 one_mem_ω)
  have hUpper : cardAdd κ μ ≤# κ := by
    exact hAdd.2.le.trans <|
      (cardLE_of_subset hAddSub).trans (prod_cardEQ_self_of_isCardinal_of_ω_subset (V := V) hκ hωκ).le
  have hTagSub : (κ ×ˢ ({0} : V)) ⊆ orderSumCarrier κ μ := by
    intro p hp
    rcases mem_prod_iff.mp hp with ⟨x, hxκ, i, hi0, rfl⟩
    have hi : i = 0 := by simpa using hi0
    simp [mem_orderSumCarrier_iff, hi, hxκ]
  have hLower : κ ≤# cardAdd κ μ := by
    exact (CardEQ.tagProd (X := κ) (i := (0 : V))).le.trans <|
      (cardLE_of_subset hTagSub).trans hAdd.2.ge
  exact eq_of_isCardinal_of_cardEQ hAdd.1 hκ ⟨hUpper, hLower⟩

lemma cardMul_eq_self_of_isCardinal_of_ω_subset_of_subset_of_ne_zero
    [V ⊧ₘ* 𝗭𝗙] {κ μ : V}
    (hκ : IsCardinal κ) (hμ : IsCardinal μ)
    (hωκ : (ω : V) ⊆ κ) (hμκ : μ ⊆ κ)
    (hμ0 : μ ≠ (0 : V)) :
    cardMul κ μ = κ := by
  have hMul := cardMul_spec_of_isCardinal (V := V) hκ hμ
  have hMulSub : κ ×ˢ μ ⊆ κ ×ˢ κ :=
    prod_subset_prod_of_subset (by simp) hμκ
  have hUpper : cardMul κ μ ≤# κ := by
    exact hMul.2.le.trans <|
      (cardLE_of_subset hMulSub).trans (prod_cardEQ_self_of_isCardinal_of_ω_subset (V := V) hκ hωκ).le
  have hμne : μ ≠ ∅ := by simpa [zero_def] using hμ0
  have hμnonempty : IsNonempty μ := ne_empty_iff_isNonempty.mp hμne
  rcases hμnonempty.nonempty with ⟨y, hyμ⟩
  have hySub : ({y} : V) ⊆ μ := by
    intro z hz
    have hzEq : z = y := by simpa using hz
    simpa [hzEq] using hyμ
  have hTagSub : (κ ×ˢ ({y} : V)) ⊆ κ ×ˢ μ :=
    prod_subset_prod_of_subset (by simp) hySub
  have hLower : κ ≤# cardMul κ μ := by
    exact (CardEQ.tagProd (X := κ) (i := y)).le.trans <|
      (cardLE_of_subset hTagSub).trans hMul.2.ge
  exact eq_of_isCardinal_of_cardEQ hMul.1 hκ ⟨hUpper, hLower⟩

lemma cardAdd_eq_ordinalMax_of_isCardinal_of_ω_subset
    [V ⊧ₘ* 𝗭𝗙] {κ μ : V}
    (hκ : IsCardinal κ) (hμ : IsCardinal μ)
    (hω : (ω : V) ⊆ κ ∨ (ω : V) ⊆ μ) :
    cardAdd κ μ = ordinalMax κ μ := by
  letI : IsOrdinal κ := hκ.1
  letI : IsOrdinal μ := hμ.1
  rcases IsOrdinal.subset_or_supset (α := κ) (β := μ) with (hκμ | hμκ)
  · have hωμ : (ω : V) ⊆ μ := by
      rcases hω with (hωκ | hωμ)
      · exact subset_trans hωκ hκμ
      · exact hωμ
    calc
      cardAdd κ μ = cardAdd μ κ := cardAdd_comm_of_isCardinal (V := V) hκ hμ
      _ = μ := cardAdd_eq_self_of_isCardinal_of_ω_subset_of_subset (V := V) hμ hκ hωμ hκμ
      _ = ordinalMax κ μ := (union_eq_iff_left.mpr hκμ).symm
  · have hωκ : (ω : V) ⊆ κ := by
      rcases hω with (hωκ | hωμ)
      · exact hωκ
      · exact subset_trans hωμ hμκ
    calc
      cardAdd κ μ = κ :=
        cardAdd_eq_self_of_isCardinal_of_ω_subset_of_subset (V := V) hκ hμ hωκ hμκ
      _ = ordinalMax κ μ := (union_eq_iff_right.mpr hμκ).symm

lemma cardMul_eq_ordinalMax_of_isCardinal_of_ω_subset_of_ne_zero
    [V ⊧ₘ* 𝗭𝗙] {κ μ : V}
    (hκ : IsCardinal κ) (hμ : IsCardinal μ)
    (hω : (ω : V) ⊆ κ ∨ (ω : V) ⊆ μ)
    (hκ0 : κ ≠ (0 : V)) (hμ0 : μ ≠ (0 : V)) :
    cardMul κ μ = ordinalMax κ μ := by
  letI : IsOrdinal κ := hκ.1
  letI : IsOrdinal μ := hμ.1
  rcases IsOrdinal.subset_or_supset (α := κ) (β := μ) with (hκμ | hμκ)
  · have hωμ : (ω : V) ⊆ μ := by
      rcases hω with (hωκ | hωμ)
      · exact subset_trans hωκ hκμ
      · exact hωμ
    calc
      cardMul κ μ = cardMul μ κ := cardMul_comm_of_isCardinal (V := V) hκ hμ
      _ = μ :=
        cardMul_eq_self_of_isCardinal_of_ω_subset_of_subset_of_ne_zero
          (V := V) hμ hκ hωμ hκμ hκ0
      _ = ordinalMax κ μ := (union_eq_iff_left.mpr hκμ).symm
  · have hωκ : (ω : V) ⊆ κ := by
      rcases hω with (hωκ | hωμ)
      · exact hωκ
      · exact subset_trans hωμ hμκ
    calc
      cardMul κ μ = κ :=
        cardMul_eq_self_of_isCardinal_of_ω_subset_of_subset_of_ne_zero
          (V := V) hκ hμ hωκ hμκ hμ0
      _ = ordinalMax κ μ := (union_eq_iff_right.mpr hμκ).symm

lemma cardMul_mem_of_isCardinal_of_mem_of_ne_zero [V ⊧ₘ* 𝗭𝗙]
    {κ α lam : V}
    (hκ : IsCardinal κ) (hωκ : (ω : V) ⊆ κ)
    (hα : IsCardinal α) (hακ : α ∈ κ)
    (hlamκ : lam ∈ κ) (hα0 : α ≠ (0 : V)) (hlam0 : lam ≠ (0 : V)) :
    cardMul α lam ∈ κ := by
  have hlamord : IsOrdinal lam := hκ.1.of_mem hlamκ
  let μ : V := card lam
  have hμspec : IsCardinal μ ∧ μ ≋ lam := by
    simpa [μ] using
      (card_spec (exists_isCardinal_cardEQ_of_isOrdinal (V := V) hlamord))
  have hμcard : IsCardinal μ := hμspec.1
  have hμκ : μ ∈ κ := by
    simpa [μ] using card_mem_of_mem_of_isCardinal (V := V) hκ hlamord hlamκ
  have hEqMul : cardMul α lam = cardMul α μ := by
    have hLeft := cardMul_spec_of_isOrdinal (V := V) hα.1 hlamord
    have hRight := cardMul_spec_of_isCardinal (V := V) hα hμcard
    have hlamμ : lam ≋ μ := CardEQ.symm hμspec.2
    have hProdEq : (α ×ˢ lam) ≋ (α ×ˢ μ) :=
      CardEQ.prod (V := V) (CardEQ.refl α) hlamμ
    have hMulEq : cardMul α lam ≋ cardMul α μ :=
      CardEQ.trans hLeft.2 <| CardEQ.trans hProdEq (CardEQ.symm hRight.2)
    exact eq_of_isCardinal_of_cardEQ hLeft.1 hRight.1 hMulEq
  have hμ0 : μ ≠ (0 : V) := by
    intro hμeq0
    rcases ne_empty_iff_isNonempty.mp hlam0 with ⟨x, hxlam⟩
    rcases CardEQ.exists_bijective (V := V) hμspec.2 with ⟨e, he⟩
    have hxRange : x ∈ range e := by
      simpa [he.range_eq] using hxlam
    rcases mem_range_iff.mp hxRange with ⟨u, hue⟩
    have huμ : u ∈ μ := (mem_of_mem_functions he.mem_function hue).1
    have hu0 : u ∈ (0 : V) := by simpa [hμeq0] using huμ
    exact (not_mem_empty hu0).elim
  letI : IsOrdinal α := hα.1
  letI : IsOrdinal μ := hμcard.1
  rcases IsOrdinal.subset_or_supset (α := α) (β := μ) with (hαμ | hμα)
  · rcases mem_ω_or_ω_subset_of_isOrdinal (α := μ) with (hμω | hωμ)
    · have hμsubω : μ ⊆ (ω : V) := IsOrdinal.ω.transitive _ hμω
      have hαω : α ∈ (ω : V) := by
        have hαsubω : α ⊆ (ω : V) := subset_trans hαμ hμsubω
        have hαneω : α ≠ (ω : V) := by
          intro hEq
          have hωsubμ : (ω : V) ⊆ μ := by simpa [hEq] using hαμ
          have hμsubω : μ ⊆ (ω : V) := IsOrdinal.ω.transitive _ hμω
          have hωeqμ : (ω : V) = μ := subset_antisymm hωsubμ hμsubω
          have : (ω : V) ∈ (ω : V) := by simp [hωeqμ] at hμω
          exact False.elim ((mem_irrefl (ω : V)) this)
        exact mem_ω_of_subset_ω_of_ne_ω hαsubω hαneω
      have hMulω : cardMul α μ ∈ (ω : V) := by
        simpa [cardMul_eq_mulValue_of_mem_ω (V := V) hαω hμω] using
          (Ordinal.mulValue_mem_ω (α := ⟨α, hα.1⟩) (β := ⟨μ, hμcard.1⟩) hαω hμω)
      simpa [hEqMul] using hωκ _ hMulω
    · have hMulEq : cardMul α μ = μ := by
        calc
          cardMul α μ = cardMul μ α := cardMul_comm_of_isCardinal (V := V) hα hμcard
          _ = μ := cardMul_eq_self_of_isCardinal_of_ω_subset_of_subset_of_ne_zero
            (V := V) hμcard hα hωμ hαμ hα0
      simpa [hEqMul, hMulEq] using hμκ
  · rcases mem_ω_or_ω_subset_of_isOrdinal (α := α) with (hαω | hωα)
    · have hαsubω : α ⊆ (ω : V) := IsOrdinal.ω.transitive _ hαω
      have hμω : μ ∈ (ω : V) := by
        have hμsubω : μ ⊆ (ω : V) := subset_trans hμα hαsubω
        have hμneω : μ ≠ (ω : V) := by
          intro hEq
          have hωsubα : (ω : V) ⊆ α := by simpa [hEq] using hμα
          have hαsubω : α ⊆ (ω : V) := IsOrdinal.ω.transitive _ hαω
          have hωeqα : (ω : V) = α := subset_antisymm hωsubα hαsubω
          have : (ω : V) ∈ (ω : V) := by simp [hωeqα] at hαω
          exact False.elim ((mem_irrefl (ω : V)) this)
        exact mem_ω_of_subset_ω_of_ne_ω hμsubω hμneω
      have hMulω : cardMul α μ ∈ (ω : V) := by
        simpa [cardMul_eq_mulValue_of_mem_ω (V := V) hαω hμω] using
          (Ordinal.mulValue_mem_ω (α := ⟨α, hα.1⟩) (β := ⟨μ, hμcard.1⟩) hαω hμω)
      simpa [hEqMul] using hωκ _ hMulω
    · have hMulEq : cardMul α μ = α := by
        exact cardMul_eq_self_of_isCardinal_of_ω_subset_of_subset_of_ne_zero
          (V := V) hα hμcard hωα hμα hμ0
      simpa [hEqMul, hMulEq] using hακ

lemma coveringNumber_eq_cofinality_of_isCardinal_of_ω_subset [V ⊧ₘ* 𝗭𝗙] {κ : V}
    (hκ : IsCardinal κ) (hωκ : (ω : V) ⊆ κ) :
    coveringNumber κ = cofinality κ := by
  let α : V := coveringNumber κ
  have hκlim : IsLimitOrdinal κ := isLimitOrdinal_of_isCardinal_of_ω_subset hκ hωκ
  have hHasCof : HasCofinalFunction κ := hasCofinalFunction_of_isLimitOrdinal hκlim
  have hHasCover : HasSmallCoveringFunction κ :=
    hasSmallCoveringFunction_of_isCardinal_of_ω_subset (V := V) hκ hωκ
  have hαcard : IsCardinal α := by
    simpa [α] using coveringNumber_isCardinal (V := V) κ
  have hαsubcof : α ⊆ cofinality κ := by
    simpa [α] using
      coveringNumber_subset_cofinality_of_isCardinal_of_ω_subset (V := V) hκ hωκ
  have hcofsubκ : cofinality κ ⊆ κ := cofinality_subset_of_isLimitOrdinal hκlim
  have hαsubκ : α ⊆ κ := subset_trans hαsubcof hcofsubκ
  letI : IsOrdinal κ := hκ.1
  letI : IsOrdinal α := hαcard.1
  letI : IsOrdinal (cofinality κ) := cofinality_isOrdinal hHasCof
  rcases (IsOrdinal.subset_iff (α := α) (β := κ)).1 hαsubκ with (hEq | hακ)
  · have hRight : cofinality κ ⊆ α := by simpa [hEq] using hcofsubκ
    exact subset_antisymm hαsubcof hRight
  · rcases coveringNumber_hasFunction hHasCover with ⟨f, hf⟩
    have hfFun : f ∈ ℘ κ ^ α := hf.mem_function
    have hα0 : α ≠ (0 : V) := by
      intro hαeq0
      have hf0 : f ∈ ℘ κ ^ (0 : V) := by simpa [hαeq0] using hfFun
      have hdom : domain f = ∅ := by simpa using domain_eq_of_mem_function hf0
      have hrange : range f = ∅ := by
        apply subset_empty_iff_eq_empty.mp
        intro Y hY
        rcases mem_range_iff.mp hY with ⟨x, hx⟩
        have hxDom : x ∈ domain f := mem_domain_of_kpair_mem hx
        simp [hdom] at hxDom
      have hκ0 : κ = (0 : V) := by
        simpa [hrange, zero_def] using hf.2.2.symm
      have : (0 : V) ∈ (0 : V) := hκ0 ▸ hωκ 0 zero_mem_ω
      exact mem_irrefl 0 this
    let T : V → V → Prop := fun ξ η ↦
      ξ ∈ α ∧ η = Ordinal.wellOrderTypeValTotal (IsOrdinal.memRelOn (f ‘ ξ)) (f ‘ ξ)
    have hT : ℒₛₑₜ-relation[V] T := by
      letI : ℒₛₑₜ-function₂[V] value := value.definable
      letI : ℒₛₑₜ-function₁[V] IsOrdinal.memRelOn := IsOrdinal.memRelOn.definable
      letI : ℒₛₑₜ-function₂[V] Ordinal.wellOrderTypeValTotal := Ordinal.wellOrderTypeValTotal.definable (V := V)
      change ℒₛₑₜ-relation[V] (fun ξ η ↦
        ξ ∈ α ∧ η = Ordinal.wellOrderTypeValTotal (IsOrdinal.memRelOn (f ‘ ξ)) (f ‘ ξ))
      definability
    have hTfun : ∀ ξ : V, ξ ∈ α → ∃! η : V, T ξ η := by
      intro ξ hξα
      refine ⟨Ordinal.wellOrderTypeValTotal (IsOrdinal.memRelOn (f ‘ ξ)) (f ‘ ξ), ?_, ?_⟩
      · exact ⟨hξα, rfl⟩
      · intro η hη
        exact hη.2
    rcases replacement_graph_exists_on_of_definableRelation (V := V) α T hT hTfun with
      ⟨t, htFunc, htDom, htGraph⟩
    letI : IsFunction t := htFunc
    have htRangeSub : range t ⊆ κ := by
      intro η hηRange
      rcases mem_range_iff.mp hηRange with ⟨ξ, hξη⟩
      have hξα : ξ ∈ α := by
        simpa [htDom] using mem_domain_of_kpair_mem hξη
      have hηEq :
          η = Ordinal.wellOrderTypeValTotal (IsOrdinal.memRelOn (f ‘ ξ)) (f ‘ ξ) :=
        (htGraph ξ hξα η).1 hξη |>.2
      have hYpow : f ‘ ξ ∈ ℘ κ := by
        exact range_subset_of_mem_function hfFun _ (value_mem_range hfFun hξα)
      have hYsubκ : f ‘ ξ ⊆ κ := mem_power_iff.mp hYpow
      let hYwo : IsWellOrderOn (IsOrdinal.memRelOn (f ‘ ξ)) (f ‘ ξ) :=
        IsOrdinal.wellOrderOn_memRelOn_subset (α := κ) hYsubκ
      let τ : V := Ordinal.wellOrderTypeVal (IsOrdinal.memRelOn (f ‘ ξ)) (f ‘ ξ) hYwo
      have hτsubκ : τ ⊆ κ := by
        simpa [τ] using wellOrderTypeVal_memRelOn_subset_subset (α := κ) (X := f ‘ ξ) hYsubκ
      have hτY : τ ≋ f ‘ ξ := by
        rcases Ordinal.wellOrderType_isOrderIso
            (S := IsOrdinal.memRelOn (f ‘ ξ)) (Y := f ‘ ξ) (hSwo := hYwo) with ⟨e, he⟩
        exact CardEQ.of_bijective (IsOrderIso.bijective he)
      have hτne : τ ≠ κ := by
        intro hτeq
        exact (hf.2.1 _ (value_mem_range hfFun hξα)).2 (hτeq.symm ▸ hτY.le)
      have hτκ : τ ∈ κ := by
        letI : IsOrdinal τ := by
          simpa [τ] using
            (Ordinal.wellOrderTypeVal_spec (IsOrdinal.memRelOn (f ‘ ξ)) (f ‘ ξ) hYwo).1
        rcases (IsOrdinal.subset_iff (α := τ) (β := κ)).1 hτsubκ with (hEqτ | hMemτ)
        · exact False.elim (hτne hEqτ)
        · exact hMemτ
      simpa [hηEq, Ordinal.wellOrderTypeValTotal_of_wellOrderOn hYwo] using hτκ
    have htMem : t ∈ κ ^ α := by
      apply mem_function.intro
      · intro p hp
        rcases show ∃ ξ ∈ domain t, ∃ η ∈ range t, p = ⟨ξ, η⟩ₖ from by
            simpa [mem_prod_iff] using subset_prod_of_mem_function (IsFunction.mem_function t) _ hp with
          ⟨ξ, hξdom, η, hηRange, rfl⟩
        have hξα : ξ ∈ α := by simpa [htDom] using hξdom
        have hηκ : η ∈ κ := htRangeSub _ hηRange
        exact mem_prod_iff.mpr ⟨ξ, hξα, η, hηκ, rfl⟩
      · intro ξ hξα
        rcases hTfun ξ hξα with ⟨η, hη, hηuniq⟩
        refine ⟨η, (htGraph ξ hξα η).2 hη, ?_⟩
        intro η' hξη'
        exact hηuniq _ ((htGraph ξ hξα η').1 hξη')
    have htCof : IsCofinal (range t) κ := by
      refine ⟨range_subset_of_mem_function htMem, ?_⟩
      by_contra hne
      let lam : V := ⋃ˢ range t
      have hlamsubκ : lam ⊆ κ := by
        intro z hz
        rcases mem_sUnion_iff.mp hz with ⟨η, hηRange, hzη⟩
        have hηκ : η ∈ κ := htRangeSub _ hηRange
        exact hκ.1.toIsTransitive.transitive _ hηκ _ hzη
      have hlamκ : lam ∈ κ := by
        letI : IsOrdinal lam := IsOrdinal.sUnion fun η hηRange ↦ hκ.1.of_mem (htRangeSub _ hηRange)
        rcases (IsOrdinal.subset_iff (α := lam) (β := κ)).1 hlamsubκ with (hEqlam | hMemlam)
        · exact False.elim (hne hEqlam)
        · exact hMemlam
      let S : V → V → Prop := fun x p ↦
        ∃ ξ r : V,
          p = ⟨ξ, r⟩ₖ ∧
          ξ ∈ α ∧ x ∈ f ‘ ξ ∧
          (∀ ν : V, ν ∈ α → ν ∈ ξ → x ∉ f ‘ ν) ∧
          r = Ordinal.wellOrderTypeValTotal (IsOrdinal.memRelOn (f ‘ ξ ∩ x)) (f ‘ ξ ∩ x)
      have hS : ℒₛₑₜ-relation[V] S := by
        letI : ℒₛₑₜ-function₂[V] value := value.definable
        letI : ℒₛₑₜ-function₂[V] inter := inter.definable
        letI : ℒₛₑₜ-function₁[V] IsOrdinal.memRelOn := IsOrdinal.memRelOn.definable
        letI : ℒₛₑₜ-function₂[V] Ordinal.wellOrderTypeValTotal := Ordinal.wellOrderTypeValTotal.definable (V := V)
        change ℒₛₑₜ-relation[V] (fun x p ↦
          ∃ ξ r : V,
            p = ⟨ξ, r⟩ₖ ∧
            ξ ∈ α ∧ x ∈ f ‘ ξ ∧
            (∀ ν : V, ν ∈ α → ν ∈ ξ → x ∉ f ‘ ν) ∧
            r = Ordinal.wellOrderTypeValTotal (IsOrdinal.memRelOn (f ‘ ξ ∩ x)) (f ‘ ξ ∩ x))
        definability
      have hSfun : ∀ x : V, x ∈ κ → ∃! p : V, S x p := by
        intro x hxκ
        have hxUnion : x ∈ ⋃ˢ range f := by simpa [hf.2.2] using hxκ
        rcases mem_sUnion_iff.mp hxUnion with ⟨Y, hYRange, hxY⟩
        rcases mem_range_iff.mp hYRange with ⟨ξ₀, hξ₀Y⟩
        have hξ₀α : ξ₀ ∈ α := (mem_of_mem_functions hfFun hξ₀Y).1
        let Q : V → Prop := fun ξ ↦ ξ ∈ α ∧ x ∈ f ‘ ξ
        have hQ : ℒₛₑₜ-predicate[V] Q := by
          letI : ℒₛₑₜ-function₂[V] value := value.definable
          change ℒₛₑₜ-predicate[V] (fun ξ ↦ ξ ∈ α ∧ x ∈ f ‘ ξ)
          definability
        have hExQ : ∃ ξ : V, IsOrdinal ξ ∧ Q ξ := by
          refine ⟨ξ₀, hαcard.1.of_mem hξ₀α, hξ₀α, ?_⟩
          have hVal : f ‘ ξ₀ = Y := value_eq_of_kpair_mem hfFun hξ₀Y
          simpa [hVal] using hxY
        rcases exists_least_ordinal_of_exists (P := Q) hQ hExQ with ⟨ξ, hξord, hξQ, hξleast⟩
        let r : V := Ordinal.wellOrderTypeValTotal (IsOrdinal.memRelOn (f ‘ ξ ∩ x)) (f ‘ ξ ∩ x)
        refine ⟨⟨ξ, r⟩ₖ, ?_, ?_⟩
        · refine ⟨ξ, r, rfl, hξQ.1, hξQ.2, ?_, rfl⟩
          intro ν hνα hνξ hxν
          have hξsubν : ξ ⊆ ν := hξleast ν (hαcard.1.of_mem hνα) ⟨hνα, hxν⟩
          exact (mem_irrefl ν) (hξsubν _ hνξ)
        · intro p hp
          rcases hp with ⟨ξ', r', hpEq, hξ'α, hxξ', hleast', hr'Eq⟩
          have hξsubξ' : ξ ⊆ ξ' := hξleast ξ' (hαcard.1.of_mem hξ'α) ⟨hξ'α, hxξ'⟩
          letI : IsOrdinal ξ := hξord
          letI : IsOrdinal ξ' := hαcard.1.of_mem hξ'α
          have hξ'Eq : ξ' = ξ := by
            rcases IsOrdinal.mem_trichotomy (α := ξ) (β := ξ') with (hξξ' | hEq | hξ'ξ)
            · exact False.elim (hleast' ξ hξQ.1 hξξ' hξQ.2)
            · exact hEq.symm
            · exact False.elim ((mem_irrefl ξ') (hξsubξ' _ hξ'ξ))
          subst hξ'Eq
          simpa [r, hr'Eq] using hpEq
      rcases replacement_graph_exists_on_of_definableRelation (V := V) κ S hS hSfun with
        ⟨s, hsFunc, hsDom, hsGraph⟩
      letI : IsFunction s := hsFunc
      have hsRangeSub : range s ⊆ α ×ˢ lam := by
        intro p hpRange
        rcases mem_range_iff.mp hpRange with ⟨x, hxp⟩
        have hxκ : x ∈ κ := by
          simpa [hsDom] using mem_domain_of_kpair_mem hxp
        rcases (hsGraph x hxκ p).1 hxp with ⟨ξ, r, hpEq, hξα, hxξ, -, hrEq⟩
        subst hpEq
        have hYpow : f ‘ ξ ∈ ℘ κ := by
          exact range_subset_of_mem_function hfFun _ (value_mem_range hfFun hξα)
        have hYsubκ : f ‘ ξ ⊆ κ := mem_power_iff.mp hYpow
        have hrlam :
            r ∈ lam := by
          have hrτ :
              r ∈ Ordinal.wellOrderTypeValTotal (IsOrdinal.memRelOn (f ‘ ξ)) (f ‘ ξ) := by
            subst hrEq
            exact wellOrderTypeValTotal_memRelOn_inter_mem (V := V) (α := κ) (X := f ‘ ξ) hYsubκ hxξ
          have hτRange :
              Ordinal.wellOrderTypeValTotal (IsOrdinal.memRelOn (f ‘ ξ)) (f ‘ ξ) ∈ range t := by
            refine mem_range_iff.mpr ⟨ξ, ?_⟩
            rcases exists_of_mem_function htMem ξ hξα with ⟨η, -, hξη⟩
            have hηEq : η = Ordinal.wellOrderTypeValTotal (IsOrdinal.memRelOn (f ‘ ξ)) (f ‘ ξ) :=
              (htGraph ξ hξα η).1 hξη |>.2
            simpa [hηEq] using hξη
          exact mem_sUnion_iff.mpr ⟨_, hτRange, hrτ⟩
        simpa [mem_prod_iff] using And.intro hξα hrlam
      have hsMem : s ∈ (α ×ˢ lam) ^ κ := by
        apply mem_function.intro
        · intro p hp
          rcases show ∃ x ∈ domain s, ∃ q ∈ range s, p = ⟨x, q⟩ₖ from by
              simpa [mem_prod_iff] using subset_prod_of_mem_function (IsFunction.mem_function s) _ hp with
            ⟨x, hxdom, q, hqRange, rfl⟩
          have hxκ : x ∈ κ := by simpa [hsDom] using hxdom
          have hq : q ∈ α ×ˢ lam := hsRangeSub _ hqRange
          exact mem_prod_iff.mpr ⟨x, hxκ, q, hq, rfl⟩
        · intro x hxκ
          rcases hSfun x hxκ with ⟨p, hp, hpuniq⟩
          refine ⟨p, (hsGraph x hxκ p).2 hp, ?_⟩
          intro p' hxp'
          exact hpuniq _ ((hsGraph x hxκ p').1 hxp')
      have hsInj : Injective s := by
        intro x₁ x₂ p hx₁ hx₂
        have hx₁κ : x₁ ∈ κ := by simpa [hsDom] using mem_domain_of_kpair_mem hx₁
        have hx₂κ : x₂ ∈ κ := by simpa [hsDom] using mem_domain_of_kpair_mem hx₂
        rcases (hsGraph x₁ hx₁κ p).1 hx₁ with ⟨ξ₁, r₁, hp₁, hξ₁α, hx₁ξ, -, hr₁⟩
        rcases (hsGraph x₂ hx₂κ p).1 hx₂ with ⟨ξ₂, r₂, hp₂, hξ₂α, hx₂ξ, -, hr₂⟩
        have hpairs : ⟨ξ₁, r₁⟩ₖ = ⟨ξ₂, r₂⟩ₖ := by
          calc
            ⟨ξ₁, r₁⟩ₖ = p := hp₁.symm
            _ = ⟨ξ₂, r₂⟩ₖ := hp₂
        rcases kpair_inj hpairs with ⟨hξEq, hrEq⟩
        subst hξEq
        by_cases hEqx : x₁ = x₂
        · exact hEqx
        · letI : IsOrdinal x₁ := hκ.1.of_mem hx₁κ
          letI : IsOrdinal x₂ := hκ.1.of_mem hx₂κ
          rcases IsOrdinal.mem_trichotomy (α := x₁) (β := x₂) with (hx₁₂ | hxeq | hx₂₁)
          · exact False.elim <| by
              have hYpow : f ‘ ξ₁ ∈ ℘ κ := by
                exact range_subset_of_mem_function hfFun _ (value_mem_range hfFun hξ₁α)
              have hYsubκ : f ‘ ξ₁ ⊆ κ := mem_power_iff.mp hYpow
              have hlt : Ordinal.wellOrderTypeValTotal (IsOrdinal.memRelOn (f ‘ ξ₁ ∩ x₁)) (f ‘ ξ₁ ∩ x₁) ∈
                  Ordinal.wellOrderTypeValTotal (IsOrdinal.memRelOn (f ‘ ξ₁ ∩ x₂)) (f ‘ ξ₁ ∩ x₂) := by
                simpa [hr₁, hr₂, hrEq] using
                  wellOrderTypeValTotal_memRelOn_inter_strictIncreasing
                    (V := V) (α := κ) (X := f ‘ ξ₁) hYsubκ hx₁ξ hx₂ξ hx₁₂
              have h12 : r₁ ∈ r₂ := by simpa [hr₁, hr₂] using hlt
              have hself : r₁ ∈ r₁ := by simp [hrEq] at h12
              exact ((mem_irrefl r₁) hself).elim
          · exact (hEqx hxeq).elim
          · exact False.elim <| by
              have hYpow : f ‘ ξ₁ ∈ ℘ κ := by
                exact range_subset_of_mem_function hfFun _ (value_mem_range hfFun hξ₁α)
              have hYsubκ : f ‘ ξ₁ ⊆ κ := mem_power_iff.mp hYpow
              have hlt : Ordinal.wellOrderTypeValTotal (IsOrdinal.memRelOn (f ‘ ξ₁ ∩ x₂)) (f ‘ ξ₁ ∩ x₂) ∈
                  Ordinal.wellOrderTypeValTotal (IsOrdinal.memRelOn (f ‘ ξ₁ ∩ x₁)) (f ‘ ξ₁ ∩ x₁) := by
                simpa [hr₁, hr₂, hrEq] using
                  wellOrderTypeValTotal_memRelOn_inter_strictIncreasing
                    (V := V) (α := κ) (X := f ‘ ξ₁) hYsubκ hx₂ξ hx₁ξ hx₂₁
              have h21 : r₂ ∈ r₁ := by simpa [hr₁, hr₂] using hlt
              have hself : r₁ ∈ r₁ := by simp [hrEq] at h21
              exact ((mem_irrefl r₁) hself).elim
      have hκleProd : κ ≤# α ×ˢ lam := ⟨s, hsMem, hsInj⟩
      by_cases hlam0 : lam = (0 : V)
      · have h0card : IsCardinal (0 : V) := isCardinal_of_mem_ω (V := V) (by simp)
        have hle0 : κ ≤# (0 : V) := by
          simpa [hlam0, prod_empty, zero_def] using hκleProd
        have hκsub0 : κ ⊆ (0 : V) := (cardLE_iff_subset_of_isCardinal (V := V) hκ h0card).1 hle0
        exact (mem_irrefl 0) (hκsub0 0 (hωκ 0 zero_mem_ω))
      · have hMulκ : cardMul α lam ∈ κ := cardMul_mem_of_isCardinal_of_mem_of_ne_zero
          (V := V) hκ hωκ hαcard hακ hlamκ hα0 hlam0
        have hMulSubκ : cardMul α lam ⊆ κ := hκ.1.transitive _ hMulκ
        have hMulEq : cardMul α lam ≋ (α ×ˢ lam) :=
          cardMul_cardEQ_of_isOrdinal (V := V) hαcard.1 (hκ.1.of_mem hlamκ)
        have hκleMul : κ ≤# cardMul α lam := hκleProd.trans hMulEq.ge
        exact hκ.2 (cardMul α lam) hMulκ ⟨cardLE_of_subset hMulSubκ, hκleMul⟩
    have hcofsubα : cofinality κ ⊆ α := by
      rcases exists_isCofinalFunction_subset_of_mem_function_of_isCofinal
          (hβ := hαcard.1) (hα := hκlim) htMem htCof with
        ⟨γ, hγord, hγsubα, g, hg⟩
      exact subset_trans (cofinality_least hHasCof hγord ⟨g, hg⟩) hγsubα
    exact subset_antisymm hαsubcof hcofsubα

private lemma exists_mem_function_not_mem_range_of_mem_function_of_subset_of_isCardinal_of_ω_subset
    [V ⊧ₘ* 𝗭𝗙] {κ A F : V}
    (hκ : IsCardinal κ) (hωκ : (ω : V) ⊆ κ) (hAκ : A ⊆ κ)
    (hF : F ∈ (κ ^ cofinality κ) ^ A) :
    ∃ g ∈ κ ^ cofinality κ, g ∉ range F := by
  let δ : V := cofinality κ
  have hκlim : IsLimitOrdinal κ := isLimitOrdinal_of_isCardinal_of_ω_subset hκ hωκ
  have hHasCof : HasCofinalFunction κ := hasCofinalFunction_of_isLimitOrdinal hκlim
  have hδord : IsOrdinal δ := by
    simpa [δ] using cofinality_isOrdinal hHasCof
  letI : IsOrdinal δ := hδord
  rcases cofinality_hasFunction hHasCof with ⟨c, hc⟩
  have hcFun : c ∈ κ ^ δ := by
    simpa [δ] using hc.mem_function
  let D : V → V → Prop := fun ξ y ↦
    ξ ∈ δ ∧ y ∈ κ ∧
      (∀ β : V, β ∈ A → β ∈ c ‘ ξ → (F ‘ β) ‘ ξ ≠ y) ∧
      ∀ ν : V, IsOrdinal ν → ν ∈ κ →
        (∀ β : V, β ∈ A → β ∈ c ‘ ξ → (F ‘ β) ‘ ξ ≠ ν) → y ⊆ ν
  have hD : ℒₛₑₜ-relation[V] D := by
    letI : ℒₛₑₜ-function₂[V] value := value.definable
    change ℒₛₑₜ-relation[V] (fun ξ y ↦
      ξ ∈ δ ∧ y ∈ κ ∧
        (∀ β : V, β ∈ A → β ∈ c ‘ ξ → (F ‘ β) ‘ ξ ≠ y) ∧
        ∀ ν : V, IsOrdinal ν → ν ∈ κ →
          (∀ β : V, β ∈ A → β ∈ c ‘ ξ → (F ‘ β) ‘ ξ ≠ ν) → y ⊆ ν)
    definability
  have hDfun : ∀ ξ : V, ξ ∈ δ → ∃! y : V, D ξ y := by
    intro ξ hξδ
    have hcξκ : c ‘ ξ ∈ κ := hc.isCofinal.1 _ (value_mem_range hcFun hξδ)
    have hcξord : IsOrdinal (c ‘ ξ) := hκ.1.of_mem hcξκ
    let B : V := A ∩ c ‘ ξ
    let H : V → V := fun β ↦ (F ‘ β) ‘ ξ
    have hHdef : ℒₛₑₜ-function₁[V] H := by
      letI : ℒₛₑₜ-function₂[V] value := value.definable
      change ℒₛₑₜ-function₁[V] (fun β ↦ (F ‘ β) ‘ ξ)
      definability
    have hHmap : ∀ β ∈ B, H β ∈ κ := by
      intro β hβB
      have hβA : β ∈ A := (mem_inter_iff.mp hβB).1
      have hFβ : F ‘ β ∈ κ ^ δ :=
        range_subset_of_mem_function hF _ (value_mem_range hF hβA)
      exact range_subset_of_mem_function hFβ _ (value_mem_range hFβ hξδ)
    rcases graph_exists_mem_function_of_definableFunction B κ H hHdef hHmap with
      ⟨e, heFun, heGraph⟩
    have hRangeLe : range e ≤# c ‘ ξ :=
      range_cardLE_of_mem_function_of_subset_of_isOrdinal hcξord
        (fun β hβB ↦ (mem_inter_iff.mp hβB).2) heFun
    have hRangeSubκ : range e ⊆ κ := range_subset_of_mem_function heFun
    have hRangeNeκ : range e ≠ κ := by
      intro hEq
      have hκle : κ ≤# c ‘ ξ := by
        simpa [hEq] using hRangeLe
      have hcξle : c ‘ ξ ≤# κ := cardLE_of_subset (hκ.1.transitive _ hcξκ)
      exact (hκ.2 (c ‘ ξ) hcξκ ⟨hcξle, hκle⟩).elim
    let Q : V → Prop := fun y ↦
      y ∈ κ ∧ ∀ β : V, β ∈ A → β ∈ c ‘ ξ → (F ‘ β) ‘ ξ ≠ y
    have hQ : ℒₛₑₜ-predicate[V] Q := by
      letI : ℒₛₑₜ-function₂[V] value := value.definable
      change ℒₛₑₜ-predicate[V] (fun y ↦
        y ∈ κ ∧ ∀ β : V, β ∈ A → β ∈ c ‘ ξ → (F ‘ β) ‘ ξ ≠ y)
      definability
    have hExQ : ∃ y : V, IsOrdinal y ∧ Q y := by
      have hMiss : ∃ y, y ∈ κ ∧ y ∉ range e := by
        by_contra hNo
        apply hRangeNeκ
        apply subset_antisymm hRangeSubκ
        intro y hyκ
        by_contra hyNotRange
        exact hNo ⟨y, hyκ, hyNotRange⟩
      rcases hMiss with ⟨y, hyκ, hyNot⟩
      refine ⟨y, hκ.1.of_mem hyκ, hyκ, ?_⟩
      intro β hβA hβcξ hEq
      have hβB : β ∈ B := mem_inter_iff.mpr ⟨hβA, hβcξ⟩
      have hβy : ⟨β, y⟩ₖ ∈ e := by
        exact (heGraph β hβB y).2 (by simpa [H] using hEq.symm)
      exact hyNot (mem_range_iff.mpr ⟨β, hβy⟩)
    rcases exists_least_ordinal_of_exists (P := Q) hQ hExQ with
      ⟨y, hyord, hyQ, hyleast⟩
    refine ⟨y, ⟨hξδ, hyQ.1, hyQ.2, ?_⟩, ?_⟩
    · intro ν hνord hνκ hνQ
      exact hyleast ν hνord ⟨hνκ, hνQ⟩
    · intro y' hy'
      rcases hy' with ⟨-, hy'κ, hy'Q, hy'least⟩
      exact subset_antisymm
        (hy'least y hyord hyQ.1 hyQ.2)
        (hyleast y' (hκ.1.of_mem hy'κ) ⟨hy'κ, hy'Q⟩)
  rcases replacement_graph_exists_on_of_definableRelation (X := δ) D hD hDfun with
    ⟨g, hgFunc, hgDom, hgGraph⟩
  letI : IsFunction g := hgFunc
  have hgRangeSub : range g ⊆ κ := by
    intro y hyRange
    rcases mem_range_iff.mp hyRange with ⟨ξ, hξy⟩
    have hξδ : ξ ∈ δ := by
      simpa [hgDom] using mem_domain_of_kpair_mem hξy
    exact ((hgGraph ξ hξδ y).1 hξy).2.1
  have hgFun : g ∈ κ ^ δ := by
    apply mem_function.intro
    · intro p hp
      rcases show ∃ ξ ∈ domain g, ∃ y ∈ range g, p = ⟨ξ, y⟩ₖ from by
          simpa [mem_prod_iff] using subset_prod_of_mem_function (IsFunction.mem_function g) _ hp with
        ⟨ξ, hξDom, y, hyRange, rfl⟩
      have hξδ : ξ ∈ δ := by simpa [hgDom] using hξDom
      have hyκ : y ∈ κ := hgRangeSub _ hyRange
      exact mem_prod_iff.mpr ⟨ξ, hξδ, y, hyκ, rfl⟩
    · intro ξ hξδ
      rcases hDfun ξ hξδ with ⟨y, hy, hyuniq⟩
      refine ⟨y, (hgGraph ξ hξδ y).2 hy, ?_⟩
      intro y' hξy'
      exact hyuniq _ ((hgGraph ξ hξδ y').1 hξy')
  refine ⟨g, by simpa [δ] using hgFun, ?_⟩
  intro hgRange
  rcases mem_range_iff.mp hgRange with ⟨β, hβg⟩
  have hβA : β ∈ A := (mem_of_mem_functions hF hβg).1
  have hβκ : β ∈ κ := hAκ _ hβA
  have hβUnion : β ∈ ⋃ˢ range c := by
    rw [hc.isCofinal.2]
    exact hβκ
  rcases mem_sUnion_iff.mp hβUnion with ⟨u, huRange, hβu⟩
  rcases mem_range_iff.mp huRange with ⟨ξ, hξu⟩
  have hξδ : ξ ∈ δ := (mem_of_mem_functions hcFun hξu).1
  have huEq : c ‘ ξ = u := value_eq_of_kpair_mem hcFun hξu
  have hβcξ : β ∈ c ‘ ξ := by simpa [huEq] using hβu
  have hξDom : ξ ∈ domain g := by
    simpa [domain_eq_of_mem_function hgFun] using hξδ
  have hξpair : ⟨ξ, g ‘ ξ⟩ₖ ∈ g :=
    (IsFunction.value_eq_iff_kpair_mem (f := g) (x := ξ) (y := g ‘ ξ) hξDom).mp rfl
  rcases (hgGraph ξ hξδ (g ‘ ξ)).1 hξpair with ⟨-, -, hAvoid, -⟩
  have hFβg : F ‘ β = g := value_eq_of_kpair_mem hF hβg
  have hValEq : (F ‘ β) ‘ ξ = g ‘ ξ := by simp [hFβg]
  exact hAvoid β hβA hβcξ hValEq

lemma not_cardLE_power_cofinality_of_isCardinal_of_ω_subset [V ⊧ₘ* 𝗭𝗙] {κ : V}
    (hκ : IsCardinal κ) (hωκ : (ω : V) ⊆ κ) :
    ¬ κ ^ cofinality κ ≤# κ := by
  intro hPow
  rcases hPow with ⟨e, heFun, heInj⟩
  have hInvFun : inverse e ∈ (κ ^ cofinality κ) ^ range e :=
    inverse_mem_function_of_mem_function_of_injective heFun heInj
  rcases exists_mem_function_not_mem_range_of_mem_function_of_subset_of_isCardinal_of_ω_subset
      (hκ := hκ) (hωκ := hωκ) (hAκ := range_subset_of_mem_function heFun) hInvFun with
    ⟨g, hgFun, hgNot⟩
  have hgRange : g ∈ range (inverse e) := by
    simpa [range_inverse e, domain_eq_of_mem_function heFun] using hgFun
  exact hgNot hgRange

lemma cardLT_power_cofinality_of_isCardinal_of_ω_subset [V ⊧ₘ* 𝗭𝗙] {κ : V}
    (hκ : IsCardinal κ) (hωκ : (ω : V) ⊆ κ) :
    κ <# κ ^ cofinality κ := by
  let δ : V := cofinality κ
  have hκlim : IsLimitOrdinal κ := isLimitOrdinal_of_isCardinal_of_ω_subset hκ hωκ
  have hδlim : IsLimitOrdinal δ := by
    simpa [δ] using cofinality_isLimitOrdinal_of_isLimitOrdinal hκlim
  have hδnonempty : IsNonempty δ := by
    exact ne_empty_iff_isNonempty.mp (by simpa [δ, zero_def] using hδlim.2.1)
  letI : IsNonempty δ := hδnonempty
  refine ⟨?_, ?_⟩
  · simpa [δ] using (cardLE_power_of_nonempty_domain (V := V) (X := δ) (Y := κ))
  · simpa [δ] using not_cardLE_power_cofinality_of_isCardinal_of_ω_subset (V := V) hκ hωκ

lemma hartogs_least_cardinal_above_of_isCardinal [V ⊧ₘ* 𝗭𝗙] {κ : V}
    (hκ : IsCardinal κ) :
    IsCardinal (hartogs κ) ∧ κ ∈ hartogs κ ∧
      ∀ ξ : V, IsCardinal ξ → κ ∈ ξ → hartogs κ ⊆ ξ := by
  have hHartogsCard : IsCardinal (hartogs κ) := hartogs_isCardinal (V := V) κ
  have hκHartogs : κ ∈ hartogs κ := by
    letI : IsOrdinal κ := hκ.1
    letI : IsOrdinal (hartogs κ) := hartogs_isOrdinal (V := V) κ
    rcases IsOrdinal.mem_trichotomy (α := hartogs κ) (β := κ) with (hHartogsκ | hEq | hκHartogs)
    · exfalso
      exact
        (hartogs_not_cardLE (V := V) κ)
          (cardLE_of_subset (hκ.1.transitive _ hHartogsκ))
    · exfalso
      have hle : hartogs κ ≤# κ := by
        simp [hEq]
      exact (hartogs_not_cardLE (V := V) κ) hle
    · exact hκHartogs
  refine ⟨hHartogsCard, hκHartogs, ?_⟩
  intro ξ hξ hκξ
  have hξnleκ : ¬ ξ ≤# κ := by
    intro hξleκ
    have hξsubκ : ξ ⊆ κ := (cardLE_iff_subset_of_isCardinal (V := V) hξ hκ).1 hξleκ
    exact (mem_irrefl κ) (hξsubκ _ hκξ)
  exact hartogs_least (V := V) κ ξ hξ.1 hξnleκ

/--
Set-level infinite-cardinal sequence value obtained by specialized transfinite recursion:
base value `ω`, successor step `hartogs`, and limit step `⋃ˢ range`.
-/
noncomputable def alephValue [V ⊧ₘ* 𝗭𝗙] (α : V) : V :=
  IsOrdinal.transfiniteRecursionValueFn (IsOrdinal.SuccLimitRecursionStep (ω : V) hartogs) α

private instance alephStep_definable [V ⊧ₘ* 𝗭𝗙] :
    ℒₛₑₜ-function₁[V] (IsOrdinal.SuccLimitRecursionStep (ω : V) hartogs) := by
  exact IsOrdinal.succLimitRecursionStep_definable
    (ω : V) hartogs (hartogs.definable (V := V))

instance alephValue.definable [V ⊧ₘ* 𝗭𝗙] : ℒₛₑₜ-function₁[V] alephValue := by
  simpa [alephValue] using
    (IsOrdinal.transfiniteRecursionValueFn_definable
      (F := IsOrdinal.SuccLimitRecursionStep (ω : V) hartogs)
      (alephStep_definable (V := V)))

@[simp] lemma alephValue_zero [V ⊧ₘ* 𝗭𝗙] :
    alephValue (0 : V) = (ω : V) := by
  simpa [alephValue] using
    (IsOrdinal.succLimitRecursionStep_zero_transfiniteRecursionValueFn
      (a₀ := (ω : V)) (F := hartogs) (hartogs.definable (V := V)))

@[simp] lemma alephValue_succ [V ⊧ₘ* 𝗭𝗙] (β : V) (hβ : IsOrdinal β) :
    alephValue (succ β) = hartogs (alephValue β) := by
  simpa [alephValue] using
    (IsOrdinal.succLimitRecursionStep_successor_transfiniteRecursionValueFn
      (a₀ := (ω : V)) (F := hartogs) (hartogs.definable (V := V)) hβ)

lemma alephValue_isCardinal [V ⊧ₘ* 𝗭𝗙] {β : V} (hβ : IsOrdinal β) :
    IsCardinal (alephValue β) := by
  let P : V → Prop := fun γ ↦ IsCardinal (alephValue γ)
  have hP : ℒₛₑₜ-predicate[V] P := by
    letI : ℒₛₑₜ-function₁[V] alephValue := alephValue.definable (V := V)
    letI : ℒₛₑₜ-predicate[V] IsCardinal := IsCardinal.definable
    change ℒₛₑₜ-predicate[V] (fun γ ↦ IsCardinal (alephValue γ))
    definability
  have hMain : ∀ α : Ordinal V, P α := by
    refine transfinite_induction (P := P) hP ?_
    intro α ih
    by_cases hα0 : α = ⊥
    · subst hα0
      change IsCardinal (alephValue (0 : V))
      simpa using (isCardinal_ω (V := V) : IsCardinal (ω : V))
    · by_cases hs : ∃ δ : Ordinal V, α = δ.succ
      · rcases hs with ⟨δ, rfl⟩
        change IsCardinal (alephValue (succ δ.val))
        rw [alephValue_succ (V := V) δ.val δ.ordinal]
        exact hartogs_isCardinal (V := V) (alephValue δ.val)
      · let G : V → V := IsOrdinal.SuccLimitRecursionStep (ω : V) hartogs
        have hGdef : ℒₛₑₜ-function₁[V] G := by
          simpa [G] using
            (IsOrdinal.succLimitRecursionStep_definable
              (ω : V) hartogs (hartogs.definable (V := V)))
        let r : V := IsOrdinal.transfiniteRecursionValueFnReplacementGraph G hGdef α.val
        have hr :
            IsFunction r ∧
              domain r = α.val ∧
              ∀ ξ ∈ α.val, ∀ y, ⟨ξ, y⟩ₖ ∈ r ↔ y = IsOrdinal.transfiniteRecursionValueFn G ξ := by
          simpa [r] using
            (IsOrdinal.transfiniteRecursionValueFnReplacementGraph_spec
              (F := G) hGdef α.val)
        have hRangeCard : ∀ y ∈ range r, IsCardinal y := by
          intro y hyR
          rcases mem_range_iff.mp hyR with ⟨ξ, hξy⟩
          have hξd : ξ ∈ domain r := mem_domain_of_kpair_mem hξy
          have hξα : ξ ∈ α.val := by simpa [hr.2.1] using hξd
          have hξord : IsOrdinal ξ := IsOrdinal.of_mem hξα
          let ξo : Ordinal V := IsOrdinal.toOrdinal ξ
          have hξlt : ξo < α := Ordinal.lt_def.mpr (by simpa [ξo] using hξα)
          have hyEq : y = IsOrdinal.transfiniteRecursionValueFn G ξ :=
            (hr.2.2 ξ hξα y).1 hξy
          simpa [P, ξo, G, alephValue, hyEq] using ih ξo hξlt
        have hVal : alephValue α.val = ⋃ˢ range r := by
          have hRec : IsOrdinal.transfiniteRecursionValueFn G α.val = ⋃ˢ range r := by
            have hdomr : domain r = α.val := hr.2.1
            have hdomNe : domain r ≠ ∅ := by
              have hαne : α.val ≠ ∅ := by
                intro h
                apply hα0
                ext z
                simp [h, Ordinal.bot_val_eq]
              simpa [hdomr] using hαne
            have hdomNoSucc : ¬ ∃ ξ : V, domain r = succ ξ := by
              intro hs'
              rcases hs' with ⟨ξ, hξ⟩
              have hξord : IsOrdinal ξ := by
                have hξd : ξ ∈ domain r := by rw [hξ]; simp
                have hξα : ξ ∈ α.val := by simpa [hdomr] using hξd
                exact IsOrdinal.of_mem hξα
              let ξo : Ordinal V := IsOrdinal.toOrdinal ξ
              have hαeq : α.val = succ ξ := by simpa [hdomr] using hξ
              apply hs
              refine ⟨ξo, ?_⟩
              ext z
              simp [ξo, hαeq]
            have hEq :=
              IsOrdinal.transfiniteRecursionValueFn_eq_apply_replacementGraph_of_ordinal
                (F := G) hGdef α.ordinal
            rw [← hEq]
            simp [r, G, IsOrdinal.SuccLimitRecursionStep, hdomNe, hdomNoSucc]
          simpa [G, alephValue] using hRec
        simpa [P, hVal] using isCardinal_sUnion (V := V) (C := range r) hRangeCard
  exact hMain ⟨β, hβ⟩

lemma alephValue_isOrdinal [V ⊧ₘ* 𝗭𝗙] {β : V} (hβ : IsOrdinal β) :
    IsOrdinal (alephValue β) :=
  (alephValue_isCardinal (V := V) hβ).1

lemma alephValue_strictIncreasing [V ⊧ₘ* 𝗭𝗙] {β γ : V}
    (hγ : IsOrdinal γ) (hβγ : β ∈ γ) :
    alephValue β ∈ alephValue γ := by
  let P : V → Prop := fun ξ ↦ ∀ η, η ∈ ξ → alephValue η ∈ alephValue ξ
  have hP : ℒₛₑₜ-predicate[V] P := by
    letI : ℒₛₑₜ-function₁[V] alephValue := alephValue.definable (V := V)
    change ℒₛₑₜ-predicate[V] (fun ξ ↦ ∀ η, η ∈ ξ → alephValue η ∈ alephValue ξ)
    definability
  have hMain : ∀ α : Ordinal V, P α := by
    refine transfinite_induction (P := P) hP ?_
    intro α ih β hβα
    by_cases hα0 : α = ⊥
    · subst hα0
      simp [Ordinal.bot_val_eq] at hβα
    · by_cases hs : ∃ δ : Ordinal V, α = δ.succ
      · rcases hs with ⟨δ, rfl⟩
        have hδ : P δ := ih δ (by simp)
        have hδcard : IsCardinal (alephValue δ.val) :=
          alephValue_isCardinal (V := V) δ.ordinal
        have hStep := hartogs_least_cardinal_above_of_isCardinal (V := V) hδcard
        rcases mem_succ_iff.mp hβα with (rfl | hβδ)
        · simpa [alephValue_succ (V := V) δ.val δ.ordinal] using hStep.2.1
        · have hβδval : alephValue β ∈ alephValue δ.val := hδ β hβδ
          simpa [Ordinal.succ_val, alephValue_succ (V := V) δ.val δ.ordinal] using
            (hStep.1.1.toIsTransitive.transitive _ hStep.2.1 _ hβδval)
      · let G : V → V := IsOrdinal.SuccLimitRecursionStep (ω : V) hartogs
        have hGdef : ℒₛₑₜ-function₁[V] G := by
          simpa [G] using
            (IsOrdinal.succLimitRecursionStep_definable
              (ω : V) hartogs (hartogs.definable (V := V)))
        let r : V := IsOrdinal.transfiniteRecursionValueFnReplacementGraph G hGdef α.val
        have hr :
            IsFunction r ∧
              domain r = α.val ∧
              ∀ ξ ∈ α.val, ∀ y, ⟨ξ, y⟩ₖ ∈ r ↔ y = IsOrdinal.transfiniteRecursionValueFn G ξ := by
          simpa [r] using
            (IsOrdinal.transfiniteRecursionValueFnReplacementGraph_spec
              (F := G) hGdef α.val)
        have hVal : alephValue α.val = ⋃ˢ range r := by
          have hRec : IsOrdinal.transfiniteRecursionValueFn G α.val = ⋃ˢ range r := by
            have hdomr : domain r = α.val := hr.2.1
            have hdomNe : domain r ≠ ∅ := by
              have hαne : α.val ≠ ∅ := by
                intro h
                apply hα0
                ext z
                simp [h, Ordinal.bot_val_eq]
              simpa [hdomr] using hαne
            have hdomNoSucc : ¬ ∃ ξ : V, domain r = succ ξ := by
              intro hs'
              rcases hs' with ⟨ξ, hξ⟩
              have hξord : IsOrdinal ξ := by
                have hξd : ξ ∈ domain r := by rw [hξ]; simp
                have hξα : ξ ∈ α.val := by simpa [hdomr] using hξd
                exact IsOrdinal.of_mem hξα
              let ξo : Ordinal V := IsOrdinal.toOrdinal ξ
              have hαeq : α.val = succ ξ := by simpa [hdomr] using hξ
              apply hs
              refine ⟨ξo, ?_⟩
              simpa [Ordinal.succ_val, hαeq] using (Ordinal.val_toOrdinal α).symm
            have hEq :=
              IsOrdinal.transfiniteRecursionValueFn_eq_apply_replacementGraph_of_ordinal
                (F := G) hGdef α.ordinal
            rw [← hEq]
            simp [r, G, IsOrdinal.SuccLimitRecursionStep, hdomNe, hdomNoSucc]
          simpa [G, alephValue] using hRec
        have hβord : IsOrdinal β := α.ordinal.of_mem hβα
        let βo : Ordinal V := IsOrdinal.toOrdinal β
        have hsuccβsubα : succ β ⊆ α.val := IsOrdinal.succ_subset_of_mem hβα
        have hsuccβneα : succ β ≠ α.val := by
          intro hEq
          apply hs
          refine ⟨βo, ?_⟩
          ext z
          simp [βo, hEq]
        have hsuccβα : succ β ∈ α.val :=
          IsOrdinal.mem_of_ssubset (α := succ β) (β := α.val) ⟨hsuccβsubα, hsuccβneα⟩
        have hSuccPair : ⟨succ β, alephValue (succ β)⟩ₖ ∈ r := by
          refine (hr.2.2 (succ β) hsuccβα (alephValue (succ β))).2 ?_
          simp [G, alephValue]
        have hSuccRange : alephValue (succ β) ∈ range r := mem_range_iff.mpr ⟨succ β, hSuccPair⟩
        have hβSucc : alephValue β ∈ alephValue (succ β) := by
          rw [alephValue_succ (V := V) β hβord]
          exact
            (hartogs_least_cardinal_above_of_isCardinal
              (V := V) (alephValue_isCardinal (V := V) hβord)).2.1
        rw [hVal]
        exact mem_sUnion_iff.mpr ⟨alephValue (succ β), hSuccRange, hβSucc⟩
  exact hMain ⟨γ, hγ⟩ β hβγ

lemma alephValue_subset_self [V ⊧ₘ* 𝗭𝗙] {β : V} (hβ : IsOrdinal β) :
    β ⊆ alephValue β := by
  let F : V → V := alephValue
  have hFdef : ℒₛₑₜ-function₁[V] F := alephValue.definable (V := V)
  have hFstrict :
      ∀ ξ ζ : V, IsOrdinal ξ → IsOrdinal ζ → ξ ∈ ζ → F ξ ∈ F ζ := by
    intro ξ ζ hξ hζ hξζ
    exact alephValue_strictIncreasing (V := V) (hγ := hζ) hξζ
  have hFord : ∀ ξ : V, IsOrdinal ξ → IsOrdinal (F ξ) := by
    intro ξ hξ
    exact alephValue_isOrdinal (V := V) hξ
  simpa [F] using strictIncreasing_function_subset_value F hFdef hFstrict hFord β hβ

lemma alephValue_exists_max_stage_le [V ⊧ₘ* 𝗭𝗙] {κ : V}
    (hκ : IsOrdinal κ) (hωκ : (ω : V) ⊆ κ) :
    ∃ δ, δ ∈ succ (succ κ) ∧
      alephValue δ ⊆ κ ∧
      ∀ γ, γ ∈ succ (succ κ) → alephValue γ ⊆ κ → γ ⊆ δ := by
  let α : V := succ (succ κ)
  have hα : IsOrdinal α := IsOrdinal.succ
  have hstrict :
      ∀ β γ, β ∈ γ → γ ∈ α →
        IsOrdinal.transfiniteRecursionValueFn
            (IsOrdinal.SuccLimitRecursionStep (ω : V) hartogs) β ∈
          IsOrdinal.transfiniteRecursionValueFn
            (IsOrdinal.SuccLimitRecursionStep (ω : V) hartogs) γ := by
    intro β γ hβγ hγα
    exact alephValue_strictIncreasing (V := V) (hγ := IsOrdinal.of_mem hγα) hβγ
  have hValOrd :
      ∀ β, β ∈ α →
        IsOrdinal
          (IsOrdinal.transfiniteRecursionValueFn
            (IsOrdinal.SuccLimitRecursionStep (ω : V) hartogs) β) := by
    intro β hβα
    exact alephValue_isOrdinal (V := V) (IsOrdinal.of_mem hβα)
  have hself :
      ∀ β, β ∈ α →
        β ⊆
          IsOrdinal.transfiniteRecursionValueFn
            (IsOrdinal.SuccLimitRecursionStep (ω : V) hartogs) β := by
    intro β hβα
    exact alephValue_subset_self (V := V) (IsOrdinal.of_mem hβα)
  have hsuccκα : succ κ ∈ α := by
    simp [α]
  simpa [α, alephValue] using
    (IsOrdinal.succLimitRecursion_exists_max_stage_le_fn
      (a₀ := (ω : V)) (F := hartogs) (hFdef := hartogs.definable (V := V))
      (hα := hα) hstrict hValOrd hself hκ hωκ hsuccκα)

lemma exists_alephValue_eq_of_isCardinal_of_ω_subset [V ⊧ₘ* 𝗭𝗙] {κ : V}
    (hκ : IsCardinal κ) (hωκ : (ω : V) ⊆ κ) :
    ∃ α : Ordinal V, alephValue α.val = κ := by
  letI : IsOrdinal κ := hκ.1
  rcases alephValue_exists_max_stage_le (V := V) (κ := κ) hκ.1 hωκ with
    ⟨δ, hδα, hδle, hmax⟩
  have hδord : IsOrdinal δ := IsOrdinal.of_mem hδα
  have hδcard : IsCardinal (alephValue δ) := alephValue_isCardinal (V := V) hδord
  have hδsubκ : δ ⊆ κ := subset_trans (alephValue_subset_self (V := V) hδord) hδle
  by_cases hEq : alephValue δ = κ
  · exact ⟨⟨δ, hδord⟩, hEq⟩
  · have hValMemκ : alephValue δ ∈ κ := by
      letI : IsOrdinal (alephValue δ) := hδcard.1
      letI : IsOrdinal κ := hκ.1
      rcases (IsOrdinal.subset_iff (α := alephValue δ) (β := κ)).1 hδle with (hEq' | hMem')
      · exact (hEq hEq').elim
      · exact hMem'
    have hsuccδleκ : alephValue (succ δ) ⊆ κ := by
      rw [alephValue_succ (V := V) δ hδord]
      exact
        (hartogs_least_cardinal_above_of_isCardinal (V := V) hδcard).2.2
          κ hκ hValMemκ
    have hsuccδsubsuccκ : succ δ ⊆ succ κ := by
      intro t ht
      rcases mem_succ_iff.mp ht with (rfl | htδ)
      · exact mem_succ_iff.mpr ((IsOrdinal.subset_iff (α := t) (β := κ)).1 hδsubκ)
      · exact mem_succ_iff.mpr <| Or.inr (hδsubκ t htδ)
    have hsuccδα : succ δ ∈ succ (succ κ) := by
      letI : IsOrdinal δ := hδord
      letI : IsOrdinal (succ δ) := IsOrdinal.succ
      letI : IsOrdinal (succ κ) := IsOrdinal.succ
      simpa [mem_succ_iff] using
        (IsOrdinal.subset_iff (α := succ δ) (β := succ κ)).1 hsuccδsubsuccκ
    have hsuccδsubδ : succ δ ⊆ δ := hmax (succ δ) hsuccδα hsuccδleκ
    have : δ ∈ δ := hsuccδsubδ _ (by simp)
    exact (mem_irrefl δ this).elim

end LO.FirstOrder.SetTheory
