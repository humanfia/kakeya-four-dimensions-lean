-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_c2_slope_normalization.BoundedSlope.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_c2_slope_normalization.Isometry

namespace WangZahlLot.Obl.wz_c2_slope_normalization

open Set Metric

theorem Assouad.mono_scale {d d' α C : ℝ} {B : Set ℝ}
    (h : Assouad d α C B) (hdd' : d ≤ d') : Assouad d' α C B :=
  fun r R a hdr hrR => h r R a (hdd'.trans hdr) hrR

theorem Assouad.neg_image {d α C : ℝ} {B : Set ℝ}
    (h : Assouad d α C B) : Assouad d α C ((fun x => -x) '' B) := by
  intro r R a hdr hrR
  obtain ⟨m, c, hc, hm⟩ := h r R (-a - R) hdr hrR
  refine ⟨m, (fun j => -c j), ?_, hm⟩
  rintro _ ⟨⟨v, hv, rfl⟩, hlo, hhi⟩
  have hvI : v ∈ Icc (-a - R) (-a - R + R) := ⟨by linarith, by linarith⟩
  obtain ⟨j, hj⟩ := mem_iUnion.mp (hc ⟨hv, hvI⟩)
  refine mem_iUnion.mpr ⟨j, ?_⟩
  simpa only [mem_closedBall, Real.dist_eq, neg_sub_neg, abs_sub_comm] using hj

/-- A nonzero scalar contraction preserves the original minimum scale and constant. -/
theorem Assouad.contract_image {d α C a : ℝ} {B : Set ℝ}
    (hd : 0 < d) (ha : a ≠ 0) (ha1 : |a| ≤ 1) (h : Assouad d α C B) :
    Assouad d α C ((fun x => a * x) '' B) := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp ha1
  rcases lt_or_gt_of_ne ha with hneg | hpos
  · have heq : ((fun x : ℝ => (-a) * x + 0) '' ((fun x => -x) '' B)) =
        (fun x => a * x) '' B := by
      rw [image_image]
      congr 1
      funext x
      ring
    have hscaled := h.neg_image.affine_image (a := -a) (b := 0) hd (neg_pos.mpr hneg)
    rw [heq] at hscaled
    exact hscaled.mono_scale (by nlinarith)
  · have hscaled := h.affine_image (a := a) (b := 0) hd hpos
    simp only [add_zero] at hscaled
    exact hscaled.mono_scale (by nlinarith)

/-- Exchange the first two coordinates, preserving the height coordinate. -/
noncomputable def swapXY : Space ≃ₗᵢ[ℝ] Space :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap (0 : Fin 3) 1)

theorem swapXY_zero (p : Space) : swapXY p 0 = p 1 := by
  simp [swapXY, Equiv.piCongrLeft'_apply]

theorem swapXY_one (p : Space) : swapXY p 1 = p 0 := by
  simp [swapXY, Equiv.piCongrLeft'_apply]

theorem swapXY_two (p : Space) : swapXY p 2 = p 2 := by
  rfl

/-- Swapping the horizontal coordinates replaces a nonzero slope by its reciprocal.
Each horizontal projected slice is contracted by that same reciprocal. -/
theorem projectedSlice_swapXY {f g : ℝ → ℝ} {z : ℝ}
    (hfn : f z ≠ 0) (hg : g z = (f z)⁻¹) (E : Set Space) :
    ProjectedSlice g (swapXY '' E) z =
      (fun u => (f z)⁻¹ * u) '' ProjectedSlice f E z := by
  ext u
  constructor
  · rintro ⟨_, ⟨p, hp, rfl⟩, he⟩
    have hz : p 2 = z := by simpa only [swapXY_two] using congrArg Prod.snd he
    have hu : p 1 + g z * p 0 = u := by
      simpa only [swapXY_zero, swapXY_one, swapXY_two, hz] using congrArg Prod.fst he
    refine ⟨p 0 + f z * p 1, ⟨p, hp, ?_⟩, ?_⟩
    · exact Prod.ext (by simp only [hz]) hz
    · rw [← hu, hg]
      field_simp
      ring
  · rintro ⟨v, ⟨p, hp, he⟩, rfl⟩
    have hz : p 2 = z := congrArg Prod.snd he
    have hu : p 0 + f z * p 1 = v := by simpa only [hz] using congrArg Prod.fst he
    refine ⟨swapXY p, ⟨p, hp, rfl⟩, ?_⟩
    apply Prod.ext
    · simp only [swapXY_zero, swapXY_one, swapXY_two, hz, hg]
      rw [← hu]
      field_simp
      ring
    · exact (swapXY_two p).trans hz

/-- Reciprocation is nonexpanding where the absolute value of the slope is at least one. -/
theorem reciprocal_lipschitzOn {f : ℝ → ℝ} {D : Set ℝ}
    (hf : LipschitzWith 1 f) (hlarge : ∀ z ∈ D, 1 ≤ |f z|) :
    LipschitzOnWith 1 (fun z => (f z)⁻¹) D := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have hxpos : 0 < |f x| := zero_lt_one.trans_le (hlarge x hx)
  have hypos : 0 < |f y| := zero_lt_one.trans_le (hlarge y hy)
  have hden : 1 ≤ |f x| * |f y| := by
    nlinarith [hlarge x hx, hlarge y hy]
  have hdist : dist ((f x)⁻¹) ((f y)⁻¹) ≤ dist (f x) (f y) := by
    rw [Real.dist_eq, inv_sub_inv (abs_pos.mp hxpos) (abs_pos.mp hypos), abs_div, abs_mul,
      Real.dist_eq, abs_sub_comm (f y) (f x)]
    exact div_le_self (abs_nonneg _) hden
  exact hdist.trans (hf.dist_le_mul x y)

/-- The additive size of the Lipschitz slope can be bounded by three using only an
orthogonal coordinate change. Density, volume, separated covers, and local grain
constants are preserved exactly. The extension outside the unit interval remains
globally 1-Lipschitz. -/
theorem bounded_slope_representative {σ η δ : ℝ} {n : ℕ}
    {x v : Fin n → Space} {Y : Fin n → Set Space} {f : ℝ → ℝ} {P : Space → Space}
    (hδ : 0 < δ) (hfamily : ExtremalFamily σ η δ n x v Y)
    (hf : LipschitzWith 1 f) (hgrains : Grains σ δ (δ ^ (-η)) v Y f P) :
    ∃ (e : Space ≃ₗᵢ[ℝ] Space) (g : ℝ → ℝ), LipschitzWith 1 g ∧
      (∀ z ∈ Icc (-1 : ℝ) 1, |g z| ≤ 3) ∧
      ExtremalFamily σ η δ n (fun i => e (x i)) (fun i => e (v i)) (fun i => e '' Y i) ∧
      Grains σ δ (δ ^ (-η)) (fun i => e (v i)) (fun i => e '' Y i) g
        (fun p => e (P (e.symm p))) := by
  have hdiff : ∀ z ∈ Icc (-1 : ℝ) 1, |f z - f 0| ≤ 1 := by
    intro z hz
    have hdist := hf.dist_le_mul z 0
    have habs : |z| ≤ 1 := abs_le.mpr hz
    simp only [Real.dist_eq, sub_zero, NNReal.coe_one, one_mul] at hdist
    exact hdist.trans habs
  by_cases hsmall : |f 0| ≤ 2
  · let e := LinearIsometryEquiv.refl ℝ Space
    refine ⟨e, f, hf, ?_, hfamily.isometry e, hgrains.isometry e ?_⟩
    · intro z hz
      calc |f z| = |(f z - f 0) + f 0| := by rw [sub_add_cancel]
        _ ≤ |f z - f 0| + |f 0| := abs_add_le _ _
        _ ≤ 3 := by linarith [hdiff z hz]
    · simpa [e] using hgrains.1
  · have hlarge : ∀ z ∈ Icc (-1 : ℝ) 1, 1 ≤ |f z| := by
      intro z hz
      have htri : |f 0| ≤ |f z - f 0| + |f z| := by
        calc |f 0| = |(f 0 - f z) + f z| := by rw [sub_add_cancel]
          _ ≤ |f 0 - f z| + |f z| := abs_add_le _ _
          _ = |f z - f 0| + |f z| := by rw [abs_sub_comm]
      have hzdist := hdiff z hz
      linarith
    obtain ⟨g, hg, hagree⟩ := (reciprocal_lipschitzOn hf hlarge).extend_real
    have hgunit : ∀ z ∈ Icc (-1 : ℝ) 1, |g z| ≤ 1 := by
      intro z hz
      rw [← hagree hz, abs_inv, ← one_div]
      exact (div_le_one (zero_lt_one.trans_le (hlarge z hz))).mpr (hlarge z hz)
    refine ⟨swapXY, g, hg, (fun z hz => (hgunit z hz).trans (by norm_num)),
      hfamily.isometry swapXY, hgrains.isometry swapXY ?_⟩
    intro z hz
    have hfn : f z ≠ 0 := abs_pos.mp (zero_lt_one.trans_le (hlarge z hz))
    rw [← image_iUnion, projectedSlice_swapXY hfn (hagree hz).symm]
    apply (hgrains.1 z hz).contract_image hδ (inv_ne_zero hfn)
    simpa only [hagree hz] using hgunit z hz

/-- The Lipschitz premise can always be arranged to have a uniformly bounded slope. -/
theorem LipschitzExamples.bounded_slope {σ : ℝ} (h : LipschitzExamples σ) :
    ∀ η d₀ : ℝ, 0 < η → 0 < d₀ → ∃ δ : ℝ, 0 < δ ∧ δ ≤ d₀ ∧ δ ≤ (1 / 100 : ℝ) ∧
      ∃ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
        ExtremalFamily σ η δ n x v Y ∧ ∃ (f : ℝ → ℝ) (P : Space → Space),
          LipschitzWith 1 f ∧ (∀ z ∈ Icc (-1 : ℝ) 1, |f z| ≤ 3) ∧
            Grains σ δ (δ ^ (-η)) v Y f P := by
  intro η d₀ hη hd₀
  obtain ⟨δ, hδ, hδd, hδmax, n, x, v, Y, hfamily, f, P, hf, hgrains⟩ := h η d₀ hη hd₀
  obtain ⟨e, g, hg, hgbound, hfamily', hgrains'⟩ :=
    bounded_slope_representative hδ hfamily hf hgrains
  exact ⟨δ, hδ, hδd, hδmax, n, (fun i => e (x i)), (fun i => e (v i)),
    (fun i => e '' Y i), hfamily', g, (fun p => e (P (e.symm p))), hg, hgbound, hgrains'⟩

end WangZahlLot.Obl.wz_c2_slope_normalization
