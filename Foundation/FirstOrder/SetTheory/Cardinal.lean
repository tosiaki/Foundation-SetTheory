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
