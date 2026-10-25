import Mathlib
import Submission.Obl.k4_sign_graph_generic_c1.AnalyticDerivatives
import Submission.Obl.k4_sign_graph_generic_c1.Hypersurface

noncomputable section

open Set Filter Module TopologicalSpace
open scoped Topology ContDiff

namespace Submission.Obl.k4_sign_graph_generic_c1

/-- A parametrized analytic patch, with an open finite-dimensional parameter domain. -/
structure AnalyticPatch (n : ℕ) where
  dim : ℕ
  domain : Set (Fin dim → ℝ)
  isOpen_domain : IsOpen domain
  toFun : (Fin dim → ℝ) → (Fin n → ℝ)
  analyticOnNhd_toFun : AnalyticOnNhd ℝ toFun domain

def AnalyticPatch.image {n : ℕ} (c : AnalyticPatch n) : Set (Fin n → ℝ) :=
  c.toFun '' c.domain

/-- The set is a countable union of images of analytic patches contained in it. -/
def HasAnalyticCover {n : ℕ} (S : Set (Fin n → ℝ)) : Prop :=
  ∃ C : Set (AnalyticPatch n), C.Countable ∧ S = ⋃ c ∈ C, c.image

namespace HasAnalyticCover

theorem of_isOpen {n : ℕ} {S : Set (Fin n → ℝ)} (hS : IsOpen S) : HasAnalyticCover S := by
  let c : AnalyticPatch n := ⟨n, S, hS, id, fun _ _ => analyticAt_id⟩
  refine ⟨{c}, (countable_singleton c), ?_⟩
  simp [AnalyticPatch.image, c]

theorem iUnion {n : ℕ} {ι : Type*} [Countable ι] {S : ι → Set (Fin n → ℝ)}
    (hS : ∀ i, HasAnalyticCover (S i)) : HasAnalyticCover (⋃ i, S i) := by
  classical
  choose C hC hcover using hS
  refine ⟨⋃ i, C i, countable_iUnion hC, ?_⟩
  ext x
  simp only [mem_iUnion, exists_prop]
  constructor
  · rintro ⟨i, hx⟩
    rw [hcover i] at hx
    have hx' : ∃ c, c ∈ C i ∧ x ∈ c.image := by
      simpa only [mem_iUnion, exists_prop] using hx
    obtain ⟨c, hc, hxc⟩ := hx'
    exact ⟨c, ⟨i, hc⟩, hxc⟩
  · rintro ⟨c, ⟨i, hci⟩, hxc⟩
    refine ⟨i, ?_⟩
    rw [hcover i]
    exact mem_iUnion.mpr ⟨c, mem_iUnion.mpr ⟨hci, hxc⟩⟩

theorem union {n : ℕ} {S T : Set (Fin n → ℝ)} (hS : HasAnalyticCover S)
    (hT : HasAnalyticCover T) : HasAnalyticCover (S ∪ T) := by
  obtain ⟨C, hC, hc⟩ := hS
  obtain ⟨D, hD, hd⟩ := hT
  refine ⟨C ∪ D, hC.union hD, ?_⟩
  rw [hc, hd, biUnion_union]

theorem image {m n : ℕ} {S U : Set (Fin m → ℝ)} {φ : (Fin m → ℝ) → (Fin n → ℝ)}
    (hS : HasAnalyticCover S) (hSU : S ⊆ U) (hφ : AnalyticOnNhd ℝ φ U) :
    HasAnalyticCover (φ '' S) := by
  classical
  obtain ⟨C, hC, hcover⟩ := hS
  let lift : C → AnalyticPatch n := fun c =>
    { dim := c.1.dim
      domain := c.1.domain
      isOpen_domain := c.1.isOpen_domain
      toFun := φ ∘ c.1.toFun
      analyticOnNhd_toFun := hφ.comp c.1.analyticOnNhd_toFun (by
        intro x hx
        apply hSU
        rw [hcover]
        exact mem_iUnion.mpr ⟨c.1, mem_iUnion.mpr ⟨c.2, ⟨x, hx, rfl⟩⟩⟩) }
  have : Countable C := hC.to_subtype
  refine ⟨range lift, countable_range lift, ?_⟩
  ext x
  constructor
  · rintro ⟨y, hy, heq⟩
    have hy' : ∃ c, c ∈ C ∧ y ∈ c.image := by
      rw [hcover] at hy
      simpa only [mem_iUnion, exists_prop] using hy
    obtain ⟨c, hc, z, hz, hzy⟩ := hy'
    apply mem_iUnion.mpr
    refine ⟨lift ⟨c, hc⟩, mem_iUnion.mpr ⟨⟨⟨c, hc⟩, rfl⟩, ?_⟩⟩
    refine ⟨z, hz, ?_⟩
    change φ (c.toFun z) = x
    rwa [hzy]
  · intro hx
    obtain ⟨c, hxc⟩ := mem_iUnion.mp hx
    obtain ⟨hc, hxc⟩ := mem_iUnion.mp hxc
    obtain ⟨c', rfl⟩ := hc
    obtain ⟨z, hz, heq⟩ := hxc
    refine ⟨c'.1.toFun z, ?_, heq⟩
    rw [hcover]
    exact mem_iUnion.mpr ⟨c'.1, mem_iUnion.mpr ⟨c'.2, ⟨z, hz, rfl⟩⟩⟩

end HasAnalyticCover


/-- A finite sign predicate on an open domain. -/
def signRegion {n m : ℕ} (U : Set (Fin n → ℝ)) (f : Fin m → (Fin n → ℝ) → ℝ)
    (B : Set (Fin m → SignType)) : Set (Fin n → ℝ) :=
  {x | x ∈ U ∧ (fun i => SignType.sign (f i x)) ∈ B}

/-- Away from a nonflat zero of one of the defining functions, a finite sign predicate is locally
constant, and hence its points are interior points. -/
theorem exists_nonflat_zero_of_not_mem_interior
    {n m : ℕ} {U : Set (Fin n → ℝ)} (hU : IsOpen U)
    {f : Fin m → (Fin n → ℝ) → ℝ} (hf : ∀ i, ContinuousOn (f i) U)
    {B : Set (Fin m → SignType)} {a : Fin n → ℝ}
    (ha : a ∈ signRegion U f B) (hnot : a ∉ interior (signRegion U f B)) :
    ∃ i, f i a = 0 ∧ ¬ f i =ᶠ[𝓝 a] 0 := by
  classical
  by_contra h
  push Not at h
  have hsign : ∀ᶠ x in 𝓝 a, ∀ i, SignType.sign (f i x) = SignType.sign (f i a) := by
    apply eventually_all.mpr
    intro i
    by_cases hi : f i a = 0
    · filter_upwards [h i hi] with x hx
      simp only [hx, Pi.zero_apply, hi]
    · have hc := (continuousAt_sign_of_ne_zero hi).comp ((hf i).continuousAt (hU.mem_nhds ha.1))
      have he := hc.preimage_mem_nhds
        ((isOpen_discrete {SignType.sign (f i a)}).mem_nhds (by simp))
      exact he
  apply hnot
  apply mem_interior_iff_mem_nhds.mpr
  filter_upwards [hsign, hU.mem_nhds ha.1] with x hx hxU
  refine ⟨hxU, ?_⟩
  have he : (fun i => SignType.sign (f i x)) = (fun i => SignType.sign (f i a)) := funext hx
  rw [he]
  exact ha.2


/-- Finite sign conditions of analytic functions have countably many analytic parametrizations.
This elementary dimension induction only needs regular hypersurface charts. -/
theorem hasAnalyticCover_signRegion (n : ℕ) :
    ∀ (m : ℕ) (U : Set (Fin n → ℝ)), IsOpen U →
    ∀ (f : Fin m → (Fin n → ℝ) → ℝ), (∀ i, AnalyticOnNhd ℝ (f i) U) →
    ∀ B : Set (Fin m → SignType), HasAnalyticCover (signRegion U f B) := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro m U hU f hf B
    let S := signRegion U f B
    let J := Fin m × (Σ k : ℕ, Fin k → Fin n)
    let q : J → (Fin n → ℝ) → ℝ := fun j => partialComponent (f j.1) j.2.1 j.2.2
    have hq : ∀ j, AnalyticOnNhd ℝ (q j) U := fun j =>
      analyticOnNhd_partialComponent (hf j.1) j.2.1 j.2.2
    let R : J → Set (Fin n → ℝ) := fun j =>
      {x | x ∈ U ∧ q j x = 0 ∧ fderiv ℝ (q j) x ≠ 0}
    have hpieces : ∀ j : J, ∃ T : Set (Fin n → ℝ),
        HasAnalyticCover T ∧ T ⊆ S ∧ S ∩ R j ⊆ T := by
      intro j
      have hcharts : ∀ a : R j,
          ∃ (d : ℕ) (_ : d < n) (W : Set (Fin d → ℝ)) (φ : (Fin d → ℝ) → (Fin n → ℝ))
            (V : Set (Fin n → ℝ)),
            IsOpen W ∧ AnalyticOnNhd ℝ φ W ∧ MapsTo φ W U ∧ IsOpen V ∧ a.1 ∈ V ∧
              ∀ x ∈ V, q j x = 0 → x ∈ φ '' W := by
        intro a
        exact exists_analytic_hypersurface_chart (hq j a.1 a.2.1) a.2.2.1 a.2.2.2
          (hU.mem_nhds a.2.1)
      choose d hd W φ V hWo hφ hmaps hVo haV hlocal using hcharts
      obtain ⟨A, hA, hAV⟩ := isOpen_iUnion_countable V hVo
      have : Countable A := hA.to_subtype
      let K : A → Set (Fin n → ℝ) := fun a =>
        φ a.1 '' signRegion (W a.1) (fun i => f i ∘ φ a.1) B
      have hK : ∀ a : A, HasAnalyticCover (K a) := by
        intro a
        have hpre := ih (d a.1) (hd a.1) m (W a.1) (hWo a.1)
          (fun i => f i ∘ φ a.1) (fun i => (hf i).comp (hφ a.1) (hmaps a.1)) B
        exact hpre.image (fun _ hx => hx.1) (hφ a.1)
      refine ⟨⋃ a : A, K a, HasAnalyticCover.iUnion hK, ?_, ?_⟩
      · intro x hx
        obtain ⟨a, hx⟩ := mem_iUnion.mp hx
        obtain ⟨y, hy, rfl⟩ := hx
        exact ⟨hmaps a.1 hy.1, hy.2⟩
      · intro x hx
        have hxV : x ∈ ⋃ a : R j, V a := mem_iUnion.mpr ⟨⟨x, hx.2⟩, haV ⟨x, hx.2⟩⟩
        rw [← hAV] at hxV
        obtain ⟨a, hxV⟩ := mem_iUnion.mp hxV
        obtain ⟨ha, hxV⟩ := mem_iUnion.mp hxV
        obtain ⟨y, hyW, hyx⟩ := hlocal a x hxV hx.2.2.1
        apply mem_iUnion.mpr
        refine ⟨⟨a, ha⟩, y, ⟨hyW, ?_⟩, hyx⟩
        have hsign := hx.1.2
        simpa only [Function.comp_def, hyx] using hsign
    choose T hTC hTS hRT using hpieces
    have hS : S = interior S ∪ ⋃ j : J, T j := by
      apply Subset.antisymm
      · intro x hx
        by_cases hxint : x ∈ interior S
        · exact Or.inl hxint
        · obtain ⟨i, hizero, hinonflat⟩ := exists_nonflat_zero_of_not_mem_interior hU
            (fun i => (hf i).continuousOn) hx hxint
          obtain ⟨k, v, hqzero, hqnonzero⟩ := exists_regular_partialComponent
            (hf i x hx.1) hizero hinonflat
          let j : J := (i, ⟨k, v⟩)
          apply Or.inr
          apply mem_iUnion.mpr
          exact ⟨j, hRT j ⟨hx, hx.1, hqzero, hqnonzero⟩⟩
      · rintro x (hx | hx)
        · exact interior_subset hx
        · obtain ⟨j, hj⟩ := mem_iUnion.mp hx
          exact hTS j hj
    change HasAnalyticCover S
    rw [hS]
    exact (HasAnalyticCover.of_isOpen isOpen_interior).union (HasAnalyticCover.iUnion hTC)

end Submission.Obl.k4_sign_graph_generic_c1
