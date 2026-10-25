import Submission.Obl.k4_raw_localized_native_systems.C.VelocityPinning

/-
Adapted from this LOT tree, o178, session x0596, `PinningBins.lean` (commit ec5e1086),
renamed from `Submission.Obl.k4_unbounded_geometric_packet_reduction` into `Submission.Obl.k4_raw_localized_native_systems.C`.
-/

/-!
# Velocity bins forced by two transverse normal-velocity constraints

The Cramer center of two normal-velocity equations, the pinning of every
velocity satisfying both approximately, and the resulting `3 × 3` block of
velocity bins.  Used to list, from the terminal observation alone, the velocity
bins of a trajectory whose two chart labels have transverse normals.
-/

namespace Submission.Obl.k4_raw_localized_native_systems.C

noncomputable section

/-- The solution of `⟪n, v⟫ = a`, `⟪m, v⟫ = b` (Cramer's rule). -/
def cramer (n m : EuclideanSpace ℝ (Fin 2)) (a b : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![(a * m 1 - b * n 1) / cross2 n m, (b * n 0 - a * m 0) / cross2 n m]

theorem inner_cramer_left {n m : EuclideanSpace ℝ (Fin 2)} (h : cross2 n m ≠ 0) (a b : ℝ) :
    inner ℝ n (cramer n m a b) = a := by
  rw [inner_fin2]
  simp only [cramer]
  simp
  field_simp
  rw [cross2]; ring

theorem inner_cramer_right {n m : EuclideanSpace ℝ (Fin 2)} (h : cross2 n m ≠ 0) (a b : ℝ) :
    inner ℝ m (cramer n m a b) = b := by
  rw [inner_fin2]
  simp only [cramer]
  simp
  field_simp
  rw [cross2]; ring

theorem cross2_ne_zero_of_sep {n m : EuclideanSpace ℝ (Fin 2)} (hn : ‖n‖ = 1) (hm : ‖m‖ = 1)
    {θ : ℝ} (hθ : 0 < θ) (hsep : θ < min ‖n - m‖ ‖n + m‖) : cross2 n m ≠ 0 := by
  have := cross2_sq_lower hn hm hθ.le hsep
  intro h
  rw [h] at this
  nlinarith [sq_pos_of_pos hθ]

/-- **Pinning.**  A vector satisfying two transverse normal constraints is close to
the Cramer center. -/
theorem norm_sub_cramer_le {n m v : EuclideanSpace ℝ (Fin 2)} (hn : ‖n‖ = 1) (hm : ‖m‖ = 1)
    {θ a b ρ σ : ℝ} (hθ : 0 < θ) (hsep : θ < min ‖n - m‖ ‖n + m‖)
    (ha : |inner ℝ n v - a| ≤ ρ) (hb : |inner ℝ m v - b| ≤ σ) :
    ‖v - cramer n m a b‖ ≤ 4 * (ρ + σ) / θ := by
  have hc := cross2_ne_zero_of_sep hn hm hθ hsep
  apply norm_le_of_two_normals hn hm hθ hsep
  · rw [inner_sub_right, inner_cramer_left hc]; exact ha
  · rw [inner_sub_right, inner_cramer_right hc]; exact hb

/-- The velocity bin of a planar vector at width `w`. -/
def binOf (w : ℝ) (v : EuclideanSpace ℝ (Fin 2)) : Fin 2 → ℤ := fun j => ⌊v j / w⌋

/-- The `3 × 3` block of bins around a bin. -/
def nbhd (z : Fin 2 → ℤ) : Finset (Fin 2 → ℤ) :=
  ((Finset.Icc (-1 : ℤ) 1) ×ˢ (Finset.Icc (-1 : ℤ) 1)).image
    (fun e => ![z 0 + e.1, z 1 + e.2])

theorem card_nbhd_le (z : Fin 2 → ℤ) : (nbhd z).card ≤ 9 := by
  unfold nbhd
  refine (Finset.card_image_le).trans ?_
  simp

theorem floor_div_sub_mem {a b w : ℝ} (hw : 0 < w) (h : |a - b| ≤ w) :
    ⌊a / w⌋ - ⌊b / w⌋ ∈ Finset.Icc (-1 : ℤ) 1 := by
  rw [Finset.mem_Icc]
  have h' : |a / w - b / w| ≤ 1 := by
    rw [← sub_div, abs_div, abs_of_pos hw, div_le_one hw]; exact h
  rw [abs_le] at h'
  constructor
  · have : ⌊b / w⌋ ≤ ⌊a / w + 1⌋ := Int.floor_mono (by linarith)
    rw [Int.floor_add_one] at this
    linarith
  · have : ⌊a / w⌋ ≤ ⌊b / w + 1⌋ := Int.floor_mono (by linarith)
    rw [Int.floor_add_one] at this
    linarith

/-- A vector within `w` of a center has its bin in the `3 × 3` block of the center's bin. -/
theorem binOf_mem_nbhd {v c : EuclideanSpace ℝ (Fin 2)} {w : ℝ} (hw : 0 < w)
    (h : ‖v - c‖ ≤ w) : binOf w v ∈ nbhd (binOf w c) := by
  have h0 : |v 0 - c 0| ≤ w := by
    have := abs_coord_le_norm_fin2 (v - c) 0
    simp only [PiLp.sub_apply] at this
    linarith
  have h1 : |v 1 - c 1| ≤ w := by
    have := abs_coord_le_norm_fin2 (v - c) 1
    simp only [PiLp.sub_apply] at this
    linarith
  unfold nbhd
  rw [Finset.mem_image]
  refine ⟨(⌊v 0 / w⌋ - ⌊c 0 / w⌋, ⌊v 1 / w⌋ - ⌊c 1 / w⌋), ?_, ?_⟩
  · exact Finset.mem_product.2 ⟨floor_div_sub_mem hw h0, floor_div_sub_mem hw h1⟩
  · funext j
    fin_cases j <;> simp [binOf]

end

end Submission.Obl.k4_raw_localized_native_systems.C
