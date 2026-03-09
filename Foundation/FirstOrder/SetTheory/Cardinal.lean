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
